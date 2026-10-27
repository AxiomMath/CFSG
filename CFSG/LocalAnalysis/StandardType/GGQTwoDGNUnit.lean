module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG1
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG2
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG3
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG4
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxModel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrBlock
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan
open CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem qTwoD_not_unitaryChart_four {p : ℕ} {B Bs L D J : Subgroup G} {x y : G}
    {X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hnbr : GGNbr p B x D J y X) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ψ : Su F 2 1 4 →* G} (hF : Nat.card F = 4)
    (hloc : GGNSLocalHyp p B Bs F 1 4 ψ) (hrange : ψ.range = X)
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) : False := by
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hloc.prime Nat.prime_three).mp
    (by simpa using hloc.dvd)
  subst hp3
  have hJX : J ≤ X := le_of_ggNbr hLB hcfg.1 hcfg.2.2
    (hPJ G 3 B x L D J hcfg.1 hcfg.2.2) hnbr
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hcfg hnbr hJX
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  obtain ⟨g, hg, hact⟩ := hdiag x hxBs
  have hcomp' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({x} : Set G)) := by
    simpa only [hrange] using hcomp
  obtain ⟨a, -, ha, ha4, hcent, -⟩ := exists_isComponent_block_iso
    (p := 3) (by simpa using hF) Nat.prime_three hloc.dvd hloc.ker hg hact hcomp'
  have ha4' : 4 ≤ a := ha4 rfl
  have hXcent : X ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hrange]
    exact hcent (by omega)
  have hcomm : ⁅X, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hXcent
  exact hnbr.2.2.2 (by rw [hcomm]; exact bot_le)

theorem isPerfect_su_two {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {n : ℕ} (hn : 4 ≤ n) : Group.IsPerfect (Su F 2 1 n) := by
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hq := (isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := 1) hF' (by omega) hnq).1.1
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedSU n (2 ^ 1) F) := hq
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr
      (SUid_eq_statedSU (F := F) (p := 2) (f := 1) hF' n)).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem mem_normalizer_range_of_acts {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {ψ : Su F 2 1 n →* G} {Bs : Subgroup G}
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) {b : G} (hb : b ∈ Bs) :
    b ∈ Subgroup.normalizer (ψ.range : Set G) := by
  have key : ∀ c ∈ Bs, ∀ z ∈ ψ.range, c * z * c⁻¹ ∈ ψ.range := by
    intro c hc z hz
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨g, -, -, hg⟩ := hdiag c hc
    obtain ⟨t, -, ht⟩ := hg s
    exact ⟨t, ht.symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key b hb z hz, fun hz => ?_⟩
  have h := key b⁻¹ (Bs.inv_mem hb) _ hz
  simpa [mul_assoc] using h

@[expose] noncomputable def qTwoNbrModelOfChart {B Bs L D J : Subgroup G} {x y : G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (ψ : Su F 2 1 n →* G)
    (hxBs : x ∈ Bs) (hJX : J ≤ ψ.range)
    (hcomp : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({x} : Set G)))
    (hF : Nat.card F = 4) (hn : 5 ≤ n) (hker : ψ.ker ≤ Subgroup.center (Su F 2 1 n))
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) :
    QTwoNbrModel 3 B Bs x L D J y ψ.range :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (Su F 2 1 n) := isPerfect_su_two hF (by omega)
  haveI : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  { hJK := hJX
    hcomp := hcomp
    hKperf := Group.isPerfect_def.mp inferInstance
    hxBs := hxBs
    hBsN := fun b hb => mem_normalizer_range_of_acts hdiag hb
    Delta := ⊥
    hDelta_le_K := bot_le
    hDelta_central := fun d hd k _ => by rw [Subgroup.mem_bot] at hd; subst hd; simp
    hDelta_pgroup := IsPGroup.of_card (n := 0) (by simp)
    Q := ↥(ψ.range ⊔ Bs)
    groupQ := inferInstance
    q := MonoidHom.id _
    hq_surj := Function.surjective_id
    hq_ker := by rw [MonoidHom.ker_id, Subgroup.bot_subgroupOf]
    F0 := F
    hcardF0 := hF
    d := n
    hd := hn
    ψ := ψ.codRestrict _ (fun s => Subgroup.mem_sup_left ⟨s, rfl⟩)
    hψ_ker := by
      intro s hs
      exact hker (by simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hs)
    Kbar := ((MonoidHom.id _).comp (Subgroup.inclusion le_sup_left)).range
    hKbar := rfl
    As := ((MonoidHom.id _).comp (Subgroup.inclusion le_sup_right)).range
    hAs := rfl
    hψ_range := by
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨⟨ψ s, ⟨s, rfl⟩⟩, rfl⟩
      · rintro ⟨⟨a, ha⟩, rfl⟩
        obtain ⟨s, rfl⟩ := ha
        exact ⟨s, rfl⟩
    hdiag := by
      rintro b' ⟨b, rfl⟩
      obtain ⟨g, hgd, hgu, hg⟩ := hdiag b b.2
      refine ⟨g, hgd, hgu, fun s => ?_⟩
      obtain ⟨t, ht, hbt⟩ := hg s
      exact ⟨t, ht, Subtype.ext hbt⟩
    Jbar := (((MonoidHom.id _).comp (Subgroup.inclusion le_sup_left)).comp
      (Subgroup.inclusion hJX)).range
    hJbar := rfl
    xbar := (MonoidHom.id _) ⟨x, (le_sup_right : Bs ≤ ψ.range ⊔ Bs) hxBs⟩
    hxbar := rfl
    CKbar := ((MonoidHom.id _).comp (Subgroup.inclusion
      (show ψ.range ⊓ Subgroup.centralizer ({x} : Set G) ≤ ψ.range ⊔ Bs from
        le_trans inf_le_left le_sup_left))).range
    hCKbar := rfl }

theorem qTwoD_gn_of_unitaryChart {p : ℕ} {B Bs L D J : Subgroup G} {x y : G} {X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hnbr : GGNbr p B x D J y X) {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {ψ : Su F 2 1 n →* G} (hF : Nat.card F = 4) (hloc : GGNSLocalHyp p B Bs F 1 n ψ)
    (hrange : ψ.range = X) (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ Bs) (hn : 5 ≤ n) :
    X ≤ ⨆ (g : G) (_ : g ∈ X) (_ : ∃ φ : MulAut ↥Bs,
        g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹),
      J.map (MulAut.conj g).toMonoidHom := by
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hloc.prime Nat.prime_three).mp
    (by simpa using hloc.dvd)
  subst hp3
  have hJX : J ≤ X := le_of_ggNbr hLB hcfg.1 hcfg.2.2 (hPJ G 3 B x L D J hcfg.1 hcfg.2.2) hnbr
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hcfg hnbr hJX
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  subst hrange
  have hM := qTwoNbrModelOfChart (B := B) (L := L) (D := D) (y := y) ψ hxBs hJX hcomp hF hn
    hloc.ker hdiag
  exact qTwoNbr_gen hM (qTwoNbr_comp_transport hM) (qTwoNbr_fourBlock hM)
    (qTwoNbr_normalTransport hcfg.2.1 hM)

end CFSG.StandardType.QTwo

end
