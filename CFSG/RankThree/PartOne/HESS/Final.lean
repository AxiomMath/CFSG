module

public import CFSG.RankThree.PartOne.HESS.Comm
public import CFSG.RankThree.PartOne.N143.JFactsOf

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)
open scoped commutatorElement

theorem two_step {G : Type} [Group G] {N : Type} (R : N → Set (Subgroup G))
    (cls : N → Subgroup G → Bool) (third : N → N → N)
    (hT : ∀ n, ∃ S ∈ R n, cls n S = true) (hF : ∀ n, ∃ S ∈ R n, cls n S = false)
    (hcomm : ∀ n m, n ≠ m → ∀ S ∈ R n, ∀ S' ∈ R m, cls n S ≠ cls m S' →
      ∀ a ∈ S, ∀ b ∈ S', a * b = b * a)
    (hnon : ∀ n m, n ≠ m → ∀ S ∈ R n, ∀ S' ∈ R m, cls n S = cls m S' →
      ∃ U ∈ R (third n m), cls (third n m) U ≠ cls n S ∧ ⁅S, S'⁆ = U ∧ U ≠ ⊥)
    (t x x' : N) (htx : t ≠ x) (htx' : t ≠ x') (hxx' : x ≠ x') (hz : third x x' ≠ t) : False := by
  obtain ⟨h, hR, hh⟩ := hT t
  obtain ⟨v, hv, hvc⟩ := hF x
  obtain ⟨v', hv', hvc'⟩ := hF x'
  have h1 : ∀ a ∈ v, ∀ b ∈ h, a * b = b * a := fun a ha b hb =>
    hcomm x t htx.symm v hv h hR (by rw [hvc, hh]; decide) a ha b hb
  have h2 : ∀ a ∈ v', ∀ b ∈ h, a * b = b * a := fun a ha b hb =>
    hcomm x' t htx'.symm v' hv' h hR (by rw [hvc', hh]; decide) a ha b hb
  obtain ⟨U, hU, hUc, hUe, hUne⟩ := hnon x x' hxx' v hv v' hv' (by rw [hvc, hvc'])
  have h3 : ∀ a ∈ U, ∀ b ∈ h, a * b = b * a := by
    have hle : ⁅v, v'⁆ ≤ Subgroup.centralizer (h : Set G) := by
      rw [Subgroup.commutator_le]
      intro g1 hg1 g2 hg2
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have c1 : Commute g1 y := (h1 g1 hg1 y hy)
      have c2 : Commute g2 y := (h2 g2 hg2 y hy)
      exact (((c1.mul_left c2).mul_left c1.inv_left).mul_left c2.inv_left).eq.symm
    intro a ha b hb
    have := hle (hUe ▸ ha)
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  have hcl : cls (third x x') U = cls t h := by
    rw [hh]
    have : cls (third x x') U ≠ cls x v := hUc
    rw [hvc] at this
    simpa using this
  obtain ⟨U', -, -, hUe', hUne'⟩ := hnon (third x x') t hz U hU h hR hcl
  apply hUne'
  rw [← hUe', eq_bot_iff, Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 (h3 g1 hg1 g2 hg2)

section Geometry

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A}

theorem HessSetup.third_mem (hS : HessSetup p A c L f P z) {x y : MulAut A}
    (hx : x ∈ reflectionSet p A) (hy : y ∈ reflectionSet p A) (hxy : x ≠ y) :
    x * y * x⁻¹ ∈ reflectionSet p A ∧ x * y * x⁻¹ ≠ x ∧ x * y * x⁻¹ ≠ y := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, X, hX, hxX⟩ := hx
    obtain ⟨w, -, hw, hxw⟩ := Sec12Three.mem_torusImage_iff.1 hxX
    have hmem := conj_mem_reflectionSet hS.prime hy hw
    have hcw : conjAut A w hw = x := hxw
    rwa [hcw] at hmem
  · intro h
    apply hxy
    have : x * y = x * x := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = x * x := by rw [h]
    exact (mul_left_cancel this).symm
  · intro h
    exact hS.ctx.hess x hx y hy hxy (by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h])

theorem HessSetup.exists_noncollinear (hS : HessSetup p A c L f P z) :
    ∃ t ∈ reflectionSet p A, ∃ x ∈ reflectionSet p A, ∃ x' ∈ reflectionSet p A,
      t ≠ x ∧ t ≠ x' ∧ x ≠ x' ∧ x * x' * x⁻¹ ≠ t := by
  obtain ⟨cL, hLg⟩ := hS.good L hS.ctx.facts13.inZeroStar
  obtain ⟨t₀, ht₀, -⟩ := hLg.exists_reflection
  have h2 : ∃ t ∈ reflectionSet p A, ∃ x ∈ reflectionSet p A, t ≠ x := by
    by_contra hno
    push Not at hno
    have hle : reflectionGroup p A ≤ Subgroup.zpowers t₀ := by
      refine (Subgroup.closure_le _).2 fun y hy => ?_
      rw [hno y hy t₀ ht₀]
      exact Subgroup.mem_zpowers t₀
    have h1 := Subgroup.card_le_of_le hle
    rw [hS.card, Nat.card_zpowers, ht₀.1.1] at h1
    omega
  obtain ⟨t, ht, x, hx, htx⟩ := h2
  refine ⟨t, ht, x, hx, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨J, hJ, htJ, hxJ⟩ := hS.pair t ht x hx (hS.ctx.hess t ht x hx htx)
  obtain ⟨cJ, hJg⟩ := hS.good J hJ
  obtain ⟨e⟩ := hJg.weyl
  have h6 : Nat.card (torusImage A J) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hsub : reflectionGroup p A ≤ torusImage A J := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    by_cases hyt : y = t
    · rw [hyt]; exact htJ
    by_cases hyx : y = x
    · rw [hyx]; exact hxJ
    have hxyt : x * y * x⁻¹ = t := hno y hy htx (fun h => hyt h.symm) (fun h => hyx h.symm)
    have : y = x⁻¹ * t * x := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * t * x := by rw [hxyt]
    rw [this]
    have hx' : x⁻¹ ∈ torusImage A J := (torusImage A J).inv_mem hxJ
    exact (torusImage A J).mul_mem ((torusImage A J).mul_mem hx' htJ) hxJ
  have h1 := Subgroup.card_le_of_le hsub
  rw [hS.card, h6] at h1
  omega

theorem HessSetup.false (hS : HessSetup p A c L f P z) : False := by
  classical
  obtain ⟨cls, hcls⟩ := hS.exists_classFn
  obtain ⟨t, ht, x, hx, x', hx', htx, htx', hxx', hz⟩ := hS.exists_noncollinear
  let N : Type := ↥(reflectionSet p A)
  let third : N → N → N := fun n m =>
    if h : n.1 ≠ m.1 then ⟨n.1 * m.1 * n.1⁻¹, (hS.third_mem n.2 m.2 h).1⟩ else n
  have hthird : ∀ n m : N, n.1 ≠ m.1 → (third n m).1 = n.1 * m.1 * n.1⁻¹ := by
    intro n m h
    simp [third, h]
  refine two_step (N := N) (fun n => RootSet A f p n.1) (fun n S => cls (n.1, S)) third
    (fun n => ?_) (fun n => ?_) ?_ ?_ ⟨t, ht⟩ ⟨x, hx⟩ ⟨x', hx'⟩ ?_ ?_ ?_ ?_
  · obtain ⟨S, hS', hc⟩ := (hcls.2.2 n.1 n.2).1
    exact ⟨S, hS', hc⟩
  · obtain ⟨S, hS', hc⟩ := (hcls.2.2 n.1 n.2).2
    exact ⟨S, hS', hc⟩
  · intro n m hnm S hSr S' hS'r hne
    exact (hS.comm_rule hcls n.2 m.2 (fun h => hnm (Subtype.ext h)) hSr hS'r).1 hne
  · intro n m hnm S hSr S' hS'r heq
    have hnm' : n.1 ≠ m.1 := fun h => hnm (Subtype.ext h)
    obtain ⟨U, hU, hUc, hUe, hUne⟩ := (hS.comm_rule hcls n.2 m.2 hnm' hSr hS'r).2 heq
    refine ⟨U, ?_, ?_, hUe, hUne⟩
    · show U ∈ RootSet A f p (third n m).1
      rw [hthird n m hnm']
      exact hU
    · show cls ((third n m).1, U) ≠ cls (n.1, S)
      rw [hthird n m hnm']
      exact hUc
  · intro h
    exact htx (congrArg Subtype.val h)
  · intro h
    exact htx' (congrArg Subtype.val h)
  · intro h
    exact hxx' (congrArg Subtype.val h)
  · intro h
    apply hz
    have := hthird ⟨x, hx⟩ ⟨x', hx'⟩ hxx'
    rw [← this]
    exact congrArg Subtype.val h

end Geometry

section Wiring

variable {G : Type} [Group G] [Finite G]

theorem mkSetup (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hpair : KF134Pair) {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} (hctx : HessCtx p A c L)
    {f : ℕ} (hf : p ∣ 2 ^ f - 1)
    (hm : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f) (h3 : 2 ^ f % 3 = 2) :
    ∃ (P : Subgroup (MulAut A)) (z : MulAut A), HessSetup p A c L f P z := by
  have hgood : ∀ J ∈ thetaCompZeroStarE p A, ∃ c' : G, JGood p A c' J := fun J hJm =>
    jGood_of_mem hRow1 h107 h109 h122 hctx hJm
  have hp : p.Prime := hctx.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p A := hctx.hyp.E_elem
  obtain ⟨cL, hLg⟩ := hgood L hctx.facts13.inZeroStar
  obtain ⟨s, hs, -⟩ := hLg.exists_reflection
  obtain ⟨hcard, P, z, hspec⟩ := hessianGeometry hctx.hyp.A_card (Sec12Three.five_le hctx.hyp)
    hctx.threeTransp hctx.facts13.irreducible ⟨s, hs⟩ hctx.hess
  have hKt1 := jLemmaKt1_holds hGA
  have hmodel : ∀ J ∈ thetaCompZeroStarE p A,
      StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f := by
    intro J hJ
    obtain ⟨cJ, hJg⟩ := hgood J hJ
    obtain ⟨fJ, -, hfJ, hmJ⟩ := hJg.model
    have hfe : fJ = f :=
      models_eq_all hKt1 hctx hpair hgood hJ hctx.facts13.inZeroStar hfJ hmJ hf hm
    subst hfe
    exact hmJ
  refine ⟨P, z, ?_⟩
  exact
    { ctx := hctx
      good := hgood
      model := hmodel
      f_dvd := hf
      f_odd := h3
      pair := fun t ht s hs hnc => hpair G p A c L A hctx.hyp hctx.facts12 hctx.facts13
        hctx.notFive (Or.inr ⟨rfl, hctx.allL3⟩) t ht s hs hnc
      spec := hspec
      card := hcard
      griess := hGA }

theorem node143CommB2_of_hess
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hpair : KF134Pair) : Node143CommB2 := by
  intro G _ _ p A c L E hyp h12 h13 hnotFive hEA hallL3 hthree hess hmodel hC3 x z hxL hx3 hz hxz
  subst hEA
  exfalso
  have hctx : HessCtx p E c L := ⟨hyp, h12, h13, hnotFive, hallL3, hthree, hess⟩
  obtain ⟨f, -, hf, hm, h2⟩ := hmodel
  obtain ⟨P, z', hS⟩ := mkSetup hGA hRow1 h107 h109 h122 hpair hctx hf hm h2
  exact hS.false

theorem node143CommB2Sup_of_hess
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hpair : KF134Pair) : Node143CommB2Sup :=
  Node143CommB2.toSup (node143CommB2_of_hess hGA hRow1 h107 h109 h122 hpair)

end Wiring

end CFSG.RankThree.PartOne.HESS
