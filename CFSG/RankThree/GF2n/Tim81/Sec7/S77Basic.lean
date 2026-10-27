module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S76
import CFSG.GroupTheory.ConjFixedParity
import CFSG.GroupTheory.Fitting.SimpleNormal
import CFSG.RankThree.GF2n.Tim81.Recog.GR
import CFSG.RankThree.GF2n.Tim81.Sec6.Basic
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

abbrev gammaStab (V : Subgroup G) : Subgroup G := CFSG.Timmesfeld.ARS.stabSet (gammaAt V)

abbrev gammaL (V : Subgroup G) : Subgroup G := ⨆ A ∈ gammaAt V, A

theorem omegaSet_conjSubgroup (V : Subgroup G) (g : G) :
    omegaSet (conjSubgroup g V) = omegaSet V := by
  ext U
  rw [omegaSet, omegaSet, Tim79a.mem_omegaOf, Tim79a.mem_omegaOf]
  simp only [Subgroup.mem_top, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y * g, by rw [conjSubgroup_conjSubgroup]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x * g⁻¹, ?_⟩
    rw [conjSubgroup_conjSubgroup, show (x * g⁻¹) * g = x by group]

theorem Hyp.gammaAt_conj (h : Hyp M V) {X : Subgroup G} (hX : X ∈ omegaSet V) (a : G) :
    gammaAt (conjSubgroup a X) = CFSG.Timmesfeld.ARS.conjSet (gammaAt X) a := by
  ext B
  rw [Hyp.mem_gammaAt_conj_iff h hX a]
  exact ⟨fun hB => (CFSG.Timmesfeld.ARS.mem_conjSet).mpr hB,
    fun hB => (CFSG.Timmesfeld.ARS.mem_conjSet).mp hB⟩

theorem Hyp.mem_gammaStab_iff_gammaAt_eq (h : Hyp M V) {x : G} :
    x ∈ gammaStab V ↔ gammaAt (conjSubgroup x V) = gammaAt V := by
  have hV : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  rw [gammaStab, CFSG.Timmesfeld.ARS.mem_stabSet, ← Hyp.gammaAt_conj h hV x]

theorem Sec6Hyp.mem_gammaStab_iff (hS : Sec6Hyp M V) (h75 : Sec7.Stmt75 V) {x : G} :
    x ∈ gammaStab V ↔ conjSubgroup x V ∈ gammaAt V := by
  constructor
  · intro hx
    exact CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet hx hS.mem_gammaAt_self
  · intro hx
    exact hS.sec5.toRootHyp.toHyp.mem_gammaStab_iff_gammaAt_eq.mpr (h75 _ hx)

theorem Hyp.M_le_gammaStab (h : Hyp M V) : M ≤ gammaStab V := by
  intro m hm
  refine h.mem_gammaStab_iff_gammaAt_eq.mpr ?_
  rw [mem_normalizer_iff_conjSubgroup_eq.mp (h.le_normalizer hm)]

theorem Sec6Hyp.normalizer_le_gammaStab (hS : Sec6Hyp M V) (h75 : Sec7.Stmt75 V)
    {A : Subgroup G} (hA : A ∈ gammaAt V) : Subgroup.normalizer (A : Set G) ≤ gammaStab V := by
  intro x hx
  have hAx : conjSubgroup x A = A := mem_normalizer_iff_conjSubgroup_eq.mp hx
  have h := Hyp.gammaAt_conj hS.sec5.toRootHyp.toHyp (gammaAt_subset_omegaSet V hA) x
  rw [hAx] at h
  rw [gammaStab, CFSG.Timmesfeld.ARS.mem_stabSet, ← h75 A hA]
  exact h.symm

theorem Sec6Hyp.gammaL_le_gammaStab (hS : Sec6Hyp M V) (h75 : Sec7.Stmt75 V) :
    gammaL V ≤ gammaStab V := by
  refine iSup₂_le fun A hA => ?_
  exact (Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G)).trans
    (hS.normalizer_le_gammaStab h75 hA)

theorem gammaStab_le_normalizer_gammaL (V : Subgroup G) :
    gammaStab V ≤ Subgroup.normalizer (gammaL V : Set G) :=
  CFSG.Timmesfeld.ARS.Sec5.stabSet_le_normalizer_gen (gammaAt V)

theorem Sec5Hyp.eq_of_Pc_le_normalizer (hS : Sec5Hyp M V) {E : Subgroup G}
    (hE : E ∈ omegaSet V) (hP : Pc M V ≤ Subgroup.normalizer (E : Set G)) : E = V := by
  have hH := hS.toRootHyp.toHyp
  obtain ⟨g, -, rfl⟩ := hE
  have hVE : V ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := hH.le_Pc.trans hP
  have hne : V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ := by
    intro hbot
    have hVbot : V = ⊥ := le_bot_iff.mp (le_inf le_rfl hVE |>.trans_eq hbot)
    exact hH.ne_bot hVbot
  have hcomm := Tim78.commute_of_isRootTypeTI hS.toRootHyp.rootType
    (g := 1) (h := g) (by rw [conjSubgroup_one]; exact hne)
  rw [conjSubgroup_one] at hcomm
  have hEcent : conjSubgroup g V ≤ Subgroup.centralizer (V : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hCV : Subgroup.centralizer (V : Set G) ≤ M := by
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH.ne_bot
    have hv : (v : G) ∈ V := v.2
    have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)).trans
      (hH.centralizer_le_M hv hv1')
  have hEM : conjSubgroup g V ≤ M := hEcent.trans hCV
  rcases hH.conj_le_Pc_or_inf_eq_bot hS.toRootHyp.rootType hEM with hPle | hbot
  · exact hS.toRootHyp.weaklyClosed_P.2 g hPle
  · have hPE : ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V ⊓ conjSubgroup g V :=
      le_inf
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEM.trans hH.le_normalizer_Pc))
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hP)
    have hPEbot : ⁅Pc M V, conjSubgroup g V⁆ = ⊥ := by
      refine le_bot_iff.mp (hPE.trans ?_)
      calc Pc M V ⊓ conjSubgroup g V ≤ inSubgroup (pCore 2) M ⊓ conjSubgroup g V :=
            inf_le_inf_right _ inf_le_left
        _ = ⊥ := by rw [inf_comm]; exact hbot
    have hEcentP : conjSubgroup g V ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [← Subgroup.commutator_comm] at hPEbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPEbot
    rw [hH.centralizer_Pc] at hEcentP
    exact Subgroup.eq_of_le_of_card_ge hEcentP (le_of_eq (card_conjSubgroup g V).symm)

theorem Sec6Hyp.odd_ncard_gammaAt (hS : Sec6Hyp M V) : Odd (gammaAt V).ncard := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hstab : ∀ x ∈ Pc M V, ∀ C ∈ gammaAt V,
      C.map (MulAut.conj x).toMonoidHom ∈ gammaAt V := by
    intro x hx C hC
    exact hS.sec5.toRootHyp.toHyp.conj_mem_gammaAt
      (hS.sec5.toRootHyp.toHyp.Pc_le_M hx) hC
  have hfix : {C ∈ gammaAt V | ∀ x ∈ Pc M V,
      C.map (MulAut.conj x).toMonoidHom = C} = {V} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hC, hfixC⟩
      exact hS.sec5.eq_of_Pc_le_normalizer (gammaAt_subset_omegaSet V hC)
        (fun x hx => mem_normalizer_iff_conjSubgroup_eq.mpr (hfixC x hx))
    · rintro rfl
      refine ⟨hS.mem_gammaAt_self, fun x hx => mem_normalizer_iff_conjSubgroup_eq.mp ?_⟩
      exact hS.sec5.toRootHyp.toHyp.le_normalizer
        (hS.sec5.toRootHyp.toHyp.Pc_le_M hx)
  have hmod := CFSG.GroupTheory.ncard_modEq_ncard_fixed (T := Pc M V) hP2 (𝒜 := gammaAt V) hstab
  rw [hfix, Set.ncard_singleton] at hmod
  rw [Nat.odd_iff]
  simpa [Nat.ModEq] using hmod

theorem Sec6Hyp.eq_bot_of_normal_of_inf_eq_bot (hS : Sec6Hyp M V) {N : Subgroup G}
    (hN : N.Normal) (hNV : N ⊓ V = ⊥) : N = ⊥ := by
  have hR := hS.sec5.toRootHyp
  by_contra hN1
  have hVF : V ≤ generalizedFitting G :=
    hS.normalClosure_eq hS.stmt60 ▸ Subgroup.subset_normalClosure
  have hVN : V ≤ N := hVF.trans (CFSG.GroupTheory.generalizedFitting_le_of_normal
    (hR.toHyp.isSimpleGroup_generalizedFitting hR.four_le_card).1 hN hN1)
  exact hR.toHyp.ne_bot (by rw [← hNV, inf_eq_right.mpr hVN])

theorem Sec6Hyp.Pc_le_m0Of_of_stmt74 (hS : Sec6Hyp M V) (h74 : Sec7.Stmt74 M V) :
    Pc M V ≤ m0Of M V := by
  obtain ⟨A, hA⟩ := hS.ne
  obtain ⟨B, hB, hAB⟩ := hS.exists_isL2Gen hA
  obtain ⟨g, hAg, hH⟩ := hA
  have h := (h74 A B g hAg ⟨g, hAg, hH⟩ hB hAB).2.2
  have hle : conjSubgroup g (Pc M V) ≤ conjSubgroup g (m0Of M V) := by
    rw [← h]
    exact le_sup_right
  have hle' : Pc M V ≤ conjSubgroup g⁻¹ (conjSubgroup g (m0Of M V)) :=
    conjSubgroup_le_iff.mp hle
  rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hle'

theorem Sec6Hyp.conj_m0Of_le_gammaL (hS : Sec6Hyp M V) {x : G}
    (hx : x = 1 ∨ conjSubgroup x V ∈ sigmaSet M V) :
    conjSubgroup x (m0Of M V) ≤ gammaL V := by
  rcases hx with rfl | hx
  · rw [conjSubgroup_one, m0Of]
    exact iSup₂_le fun U hU => le_iSup₂_of_le U (hS.sigmaSet_subset_gammaAt hU) le_rfl
  · rw [← m0Of_conjSubgroup x, m0Of]
    refine iSup₂_le fun U hU => ?_
    have hU' : U ∈ sigmaAt (conjSubgroup x V) := by
      rw [sigmaAt, (hS.sec5.root x).toHyp.normalizer_eq]
      exact hU
    exact le_iSup₂_of_le U ⟨conjSubgroup x V,
      (hS.sec5.toRootHyp.toHyp.sigmaAt_eq).symm ▸ hx, hU'⟩ le_rfl

theorem Sec6Hyp.cenOf_gammaL (hS : Sec6Hyp M V) (h74 : Sec7.Stmt74 M V) :
    cenOf (gammaL V) = ⊥ := by
  obtain ⟨A, hA⟩ := hS.ne
  obtain ⟨g, rfl, hH⟩ := hA
  have hA' : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hH⟩
  have hM0 : m0Of M V ≤ gammaL V := by
    have h := hS.conj_m0Of_le_gammaL (x := 1) (Or.inl rfl)
    rwa [conjSubgroup_one] at h
  have hP : Pc M V ≤ gammaL V := (hS.Pc_le_m0Of_of_stmt74 h74).trans hM0
  have hPg : conjSubgroup g (Pc M V) ≤ gammaL V :=
    (conjSubgroup_mono (hS.Pc_le_m0Of_of_stmt74 h74)).trans
      (hS.conj_m0Of_le_gammaL (Or.inr hA'))
  have hCV : cenOf (Pc M V) = V := hS.sec5.toRootHyp.toHyp.centralizer_Pc
  have hCg : cenOf (conjSubgroup g (Pc M V)) = conjSubgroup g V := by
    change Subgroup.centralizer (conjSubgroup g (Pc M V) : Set G) = conjSubgroup g V
    rw [centralizer_conjSubgroup_eq,
      show Subgroup.centralizer (Pc M V : Set G) = V from hCV]
  have hle : cenOf (gammaL V) ≤ cenOf (Pc M V) ⊓ cenOf (conjSubgroup g (Pc M V)) :=
    le_inf (Subgroup.centralizer_le hP) (Subgroup.centralizer_le hPg)
  rw [hCV, hCg] at hle
  have hbot : V ⊓ conjSubgroup g V = ⊥ :=
    inf_conjSubgroup_eq_bot_of_isTI hS.sec5.toRootHyp.toHyp.ti
      (ne_of_mem_sigmaSet hS.sec5.toRootHyp hA')
  exact le_antisymm (hle.trans_eq hbot) bot_le

theorem Sec6Hyp.Pc_le_pCore_gammaL (hS : Sec6Hyp M V) (h74 : Sec7.Stmt74 M V) :
    Pc M V ≤ inSubgroup (pCore 2) (gammaL V ⊓ Subgroup.normalizer (V : Set G)) := by
  have hH := hS.sec5.toRootHyp.toHyp
  have hM0 : m0Of M V ≤ gammaL V := by
    have h := hS.conj_m0Of_le_gammaL (x := 1) (Or.inl rfl)
    rwa [conjSubgroup_one] at h
  have hPL : Pc M V ≤ gammaL V := (hS.Pc_le_m0Of_of_stmt74 h74).trans hM0
  have hPN : Pc M V ≤ Subgroup.normalizer (V : Set G) := hH.Pc_le_M.trans hH.le_normalizer
  have hHle : gammaL V ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Pc M V : Set G) := by
    refine inf_le_right.trans ?_
    rw [hH.normalizer_eq]
    exact hH.le_normalizer_Pc
  exact le_inSubgroup_pCore (le_inf hPL hPN) hHle
    ((inSubgroup_pCore_two M).1.to_le inf_le_left)

theorem Sec7Hyp.two_le (hS : Sec7Hyp M V n f) : 2 ≤ f := by
  have h4 : 4 ≤ 2 ^ f := by
    rw [← hS.card_V]
    exact hS.sec5.toRootHyp.four_le_card
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)

theorem Sec7Hyp.isSUImage_gammaL (hS : Sec7Hyp M V n f) (h76U : Sec7.Stmt76U V n f) :
    IsSUImage (gammaL V) (gammaAt V) f (n + 2) hS.one_le (Nat.le_add_left 2 n) := by
  obtain ⟨Φ, hker, hrange, hmem⟩ := h76U hS.one_le
  exact ⟨Φ, hker.le, hrange, hmem⟩

theorem IsSUImage.nonempty {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (h : IsSUImage X Δ f m hf hm) : Δ.Nonempty := by
  obtain ⟨Φ, -, -, hclass⟩ := h
  refine ⟨(CFSG.Timmesfeld.ARS.conjSub ((CFSG.LieType.Universal.Unitary.rootDatum
    (CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf) m).rootGroup
    (CFSG.Timmesfeld.Transvection.unitaryLongRoot m hm)) 1).map Φ, ?_⟩
  exact (hclass _).mpr ⟨1, rfl⟩

theorem Sec7Hyp.yOf_le_gammaStab (hS : Sec7Hyp M V n f) (h73 : Sec7.Stmt73 M V n f)
    (h75 : Sec7.Stmt75 V) {A B : Subgroup G} {h : G} (hD : L2Datum M V A B h) :
    Sec7.yOf h ≤ gammaStab V := by
  intro y hy
  obtain ⟨h1, h2, -⟩ := h73 A B h hD
  obtain ⟨x, hxY0, hxy⟩ := h2 y hy
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
    have hxAB : x ∈ cenOf (A ⊔ B) := h1 hxY0
    have hx1 : x ∈ cenOf A :=
      Subgroup.centralizer_le (s := (A : Set G)) (t := ((A ⊔ B : Subgroup G) : Set G))
        (by intro z hz; exact Subgroup.mem_sup_left hz) hxAB
    exact Subgroup.centralizer_le_normalizer (A : Set G) hx1
  have hAω : A ∈ omegaSet V := sigmaSet_subset_omegaSet M V hD.memA
  have hmem : conjSubgroup x V ∈ sigmaAt A :=
    hS.sec5.conj_mem_sigmaAt hAω hxN (hS.sec5.self_mem_sigmaAt hD.memA)
  have hVxΓ : conjSubgroup x V ∈ gammaAt V := by
    have h' := hS.toSec6Hyp.sigmaAt_subset_gammaAt hAω hmem
    rwa [h75 A (hS.toSec6Hyp.sigmaSet_subset_gammaAt hD.memA)] at h'
  exact (hS.toSec6Hyp.mem_gammaStab_iff h75).mpr (by rwa [hxy])

theorem sylowRoots_le {K : Type} [Group K] (X₀ : Subgroup K) (Δ : Set (Subgroup K))
    (S : Sylow 2 ↥X₀) : sylowRoots X₀ Δ S ≤ X₀ := by
  unfold sylowRoots
  exact iSup₂_le fun A hA => hA.2.trans (Subgroup.map_subtype_le _)

theorem Sec7Hyp.exists_sylowRoots_of_commute (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h75 : Sec7.Stmt75 V) (h76U : Sec7.Stmt76U V n f) (hRTS : UnitaryRootTypeSylow)
    {E T : Subgroup G} (hE : E ∈ omegaSet V) (hT : T ∈ gammaAt V) (hTE : ⁅T, E⁆ = ⊥) :
    ∃ S : Sylow 2 ↥(gammaL V), E ≤ sylowRoots (gammaL V) (gammaAt V) S ∧
      T ≤ sylowRoots (gammaL V) (gammaAt V) S := by
  obtain ⟨x, -, rfl⟩ := hE
  have hA17 := hS.isSUImage_gammaL h76U
  have hA14 := hS.cenOf_gammaL h74
  have hEN : conjSubgroup x V ≤ Subgroup.normalizer (gammaL V : Set G) := by
    have h1 : conjSubgroup x V ≤ cenOf T := by
      have hET : ⁅conjSubgroup x V, T⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hET
    have h2 : cenOf T ≤ Subgroup.normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer (T : Set G)
    have h3 : Subgroup.normalizer (T : Set G) ≤ gammaStab V :=
      hS.toSec6Hyp.normalizer_le_gammaStab h75 hT
    exact h1.trans (h2.trans (h3.trans (gammaStab_le_normalizer_gammaL V)))
  have hEx : conjSubgroup x⁻¹ (conjSubgroup x V) ∈ gammaAt V := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    exact hS.toSec6Hyp.mem_gammaAt_self
  have hroot : Tim78.IsRootTypeTI (conjSubgroup x V) := (hS.sec5.root x).rootType
  exact hRTS G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have := hS.four_le; omega) hS.two_le hA17 hA14 (conjSubgroup x V) hEN
    ⟨x⁻¹, hEx⟩ hroot T hT hTE

theorem Sec7Hyp.Pc_le_normalizer_sylowRoots (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    (h76U : Sec7.Stmt76U V n f) (hSR : UnitarySylowRoots) {S : Sylow 2 ↥(gammaL V)}
    (hVS : V ≤ sylowRoots (gammaL V) (gammaAt V) S) :
    Pc M V ≤ Subgroup.normalizer (sylowRoots (gammaL V) (gammaAt V) S : Set G) := by
  have hA15 := hS.Pc_le_pCore_gammaL h74
  have hA17 := hS.isSUImage_gammaL h76U
  have h := hSR G (gammaL V) (gammaAt V) f (n + 2) hS.one_le
    (by have := hS.four_le; omega) hS.two_le hA17 S
  exact hA15.trans (h.2.2.2.1 V hS.toSec6Hyp.mem_gammaAt_self hVS)
