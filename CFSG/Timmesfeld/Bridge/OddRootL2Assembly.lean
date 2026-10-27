module

public import CFSG.Timmesfeld.Bridge.OddRootCompare
public import CFSG.Timmesfeld.Bridge.OddRootRigid
import CFSG.Timmesfeld.Bridge.OddTranspSimple
import CFSG.Timmesfeld.Bridge.RootSetsKernel
import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem eq_bot_of_normal_isPGroup (h : Hyp G D) {N : Subgroup G} (hN : N.Normal)
    (hNp : IsPGroup 2 N) : N = ⊥ := by
  have hle : N ≤ CFSG.pCore 2 G :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hNp
  rw [h.o2] at hle
  exact le_bot_iff.mp hle

private theorem exists_not_commute (h : Hyp G D) {d : G} (hd : d ∈ D) :
    ∃ x ∈ D, ¬ Commute d x := by
  obtain ⟨x, hx, hgt, hodd⟩ :=
    CFSG.Timmesfeld.exists_opposite h.setup.isClass
      (isRootInvolutionSet_of_isOddTransp h.setup.oddT)
      (fun N hN hNp => eq_bot_of_normal_isPGroup h hN hNp) hd
  refine ⟨x, hx, fun hc => ?_⟩
  have hne : d ≠ x := by
    rintro rfl
    rw [h.setup.oddT.mul_self_eq_one hd, orderOf_one] at hgt
    omega
  have h2 := h.setup.oddT.orderOf_mul_eq_two hd hx hne hc
  obtain ⟨k, hk⟩ := hodd
  rw [h2] at hk
  omega

private theorem Wof_le_Wof_of_not_commute
    (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x y : G} (hd : d ∈ D)
    (hx : x ∈ D) (hy : y ∈ D) (hdx : ¬ Commute d x) (hdy : ¬ Commute d y) :
    Wof D d x ≤ Wof D d y := by
  intro g hg
  by_contra hgy
  have hgE : g ∈ rootGroup D d := Wof_le_rootGroup d x hg
  have hpx : PSL2Pair D d y := hall d hd y hy hdy
  have hpx' : PSL2Pair D y d := hall y hy d hd (fun h' => hdy h'.symm)
  obtain ⟨e, he, z, hz, rfl⟩ := exists_rootSet_mul h hd hy hdy hpx hpx' hgE hgy
  have hzQ : z ∈ Qof D d x :=
    rootGroup_inf_le_Qof_of_not_commute h hall hd hy hx hdy hdx hz
  have hgQ : e * z ∈ Qof D d x := Wof_le_Qof d x hg
  have heQ : e ∈ Qof D d x := by
    have h1 : e * z * z⁻¹ ∈ Qof D d x := (Qof D d x).mul_mem hgQ ((Qof D d x).inv_mem hzQ)
    simpa using h1
  exact not_mem_Qof_of_mem_rootSet h.setup.oddT hx hdx he heQ

theorem Wof_eq {G : Type} [Group G]
    [Finite G] {D : Set G} (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x y : G} (hd : d ∈ D)
    (hx : x ∈ D) (hy : y ∈ D) (hdx : ¬ Commute d x) (hdy : ¬ Commute d y) :
    Wof D d x = Wof D d y :=
  le_antisymm (Wof_le_Wof_of_not_commute h hall hd hx hy hdx hdy)
    (Wof_le_Wof_of_not_commute h hall hd hy hx hdy hdx)

private theorem fixesOpposite_of_mem_Wof
    (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) {w : G} (hw : w ∈ Wof D d x) :
    FixesOpposite D d w := by
  refine ⟨Wof_le_rootGroup d x hw, ?_⟩
  intro c hc hdc _
  have hW : Wof D d x = Wof D d c := Wof_eq h hall hd hx hc hdx hdc
  have hwW : w ∈ Wof D d c := hW ▸ hw
  have hQ : Qof D d c = Qof D c d :=
    Qof_comm h hd hc hdc (hall d hd c hc hdc) (hall c hc d hd (fun h' => hdc h'.symm))
  have hwQ : w ∈ Qof D c d := by
    rw [← hQ]
    exact Wof_le_Qof d c hwW
  have hwN : w ∈ Subgroup.normalizer (rootSet D c) :=
    Qof_le_normalizer h hc hd (fun h' => hdc h'.symm)
      (hall c hc d hd (fun h' => hdc h'.symm)) hwQ
  exact (Subgroup.mem_set_normalizer_iff.mp hwN c).mp (mem_rootSet_self hc)

theorem Wof_eq_bot {G : Type}
    [Group G] [Finite G] {D : Set G} (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) : Wof D d x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hD : IsRootInvolutionSet D := isRootInvolutionSet_of_isOddTransp h.setup.oddT
  exact CFSG.Timmesfeld.eq_one_of_fixesOpposite h.setup.isClass hD
    (fun N hN hNp => eq_bot_of_normal_isPGroup h hN hNp) hd
    (fixesOpposite_of_mem_Wof h hall hd hx hdx hw)

theorem rootClosure_of_allPSL2
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) : RootClosure D := by
  intro d hd a ha b hb hab
  have hD : IsRootInvolutionSet D := isRootInvolutionSet_of_isOddTransp h.setup.oddT
  obtain ⟨x, hx, hdx⟩ := exists_not_commute h hd
  have hpx : PSL2Pair D d x := hall d hd x hx hdx
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  have hW : Wof D d x = ⊥ := Wof_eq_bot h hall hd hx hdx
  have hE : rootGroup D d = S := by
    rw [rootGroup_eq_sup h hd hx hdx hpx hC, hW, sup_bot_eq]
  have hmem : a * b ∈ S := by
    rw [← hE]
    exact (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ha)
      (rootSet_subset_rootGroup D d hb)
  exact hC.S_root (a * b) hmem (mul_ne_one_of_mem_rootSet hD hb hab)

private theorem eq_rootGroup_of_isPGroup
    (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) :
    ∀ P : Subgroup G, IsPGroup 2 P → rootGroup D d ≤ P →
      P ≤ rootGroup D d ⊔ rootGroup D x → P = rootGroup D d := by
  intro P hPp hEP hPX
  have hpx : PSL2Pair D d x := hall d hd x hx hdx
  obtain ⟨C, S, hC⟩ := exists_goodCompl h hd hx hdx hpx
  have hW : Wof D d x = ⊥ := Wof_eq_bot h hall hd hx hdx
  have hE : rootGroup D d = S := by
    rw [rootGroup_eq_sup h hd hx hdx hpx hC, hW, sup_bot_eq]
  have hQ : Qof D d x = ⊥ := by
    rw [Qof_eq_closure h hd hx hdx hpx hC, hW]
    simp
  have hCgen : C = rootGen D d x := by
    simpa [hQ] using hC.sup
  have hPC : P ≤ C := by
    rw [hCgen, rootGen_eq_rootGroup_sup h hd hx hdx hpx]
    exact hPX
  have hSP : S ≤ P := hE ▸ hEP
  have hPS : P = S := hC.S_sylow P hSP hPC hPp
  rw [← hE] at hPS
  exact hPS

theorem exists_SL2_of_allPSL2
    {G : Type} [Group G] [Finite G] {D : Set G} (h : Hyp G D)
    (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hdx : ¬ Commute d x) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (rootGroup D d) = 2 ^ n ∧
      ∃ φ : ↥(rootGroup D d ⊔ rootGroup D x) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        ((rootGroup D d).subgroupOf (rootGroup D d ⊔ rootGroup D x)).map φ.toMonoidHom =
            upperUnipotent (GaloisField 2 n) ∧
          ((rootGroup D x).subgroupOf (rootGroup D d ⊔ rootGroup D x)).map φ.toMonoidHom =
            lowerUnipotent (GaloisField 2 n) := by
  have hclass : ∃ d₀ : G, D = {g | IsConj d₀ g} := h.setup.isClass
  have hD : IsRootInvolutionSet D := isRootInvolutionSet_of_isOddTransp h.setup.oddT
  have hrc : RootClosure D := rootClosure_of_allPSL2 h hall
  have hodd : Odd (orderOf (d * x)) := h.setup.oddT.odd_of_not_commute hd hx hdx
  obtain ⟨v, hv, hvne, -⟩ := exists_rootSet_triple h.setup h.sq hd
  have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d := ⟨d, hd, v, hv, hvne⟩
  have hq : 4 ≤ Nat.card (rootGroup D d) := four_le_card_rootGroup hclass hD hrc hl hd
  have hsyl := eq_rootGroup_of_isPGroup h hall hd hx hdx
  have hrank : RankOneTransitive D d x :=
    rankOneTransitive_of_sylow hclass hD hrc hd hx hdx hodd hq hsyl
  have hM : MoufangPair D d x :=
    (moufangPair_iff_rankOneTransitive hclass hD hrc hd hx hdx hodd).mpr hrank
  exact exists_mulEquiv_SL2_of_moufang hclass hD hrc hd hx hdx hodd hM.1 hM.2 hq

end CFSG.Timmesfeld.Bridge.OddRoot
