module

public import CFSG.Quasithin.Vol2.Ch11SecBG2Gen
public import CFSG.Quasithin.Vol2.Ch11SecB22Six
public import CFSG.Quasithin.Vol2.Ch11SecB24Claim
public import CFSG.Quasithin.Vol2.Ch11SecBG2Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem derivedG2WeakClosure_cent (hFG : FactsG2W) (hNF : NatFacts) (hFM : FactMParam)
    (hFO : FactOddCodim) (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt) (hN : FactNot4213)
    (hFR : FactRootInv) (hG2o : FactG2DerivedOrder) (h4213 : TmpL6_4_2_13)
    (h311 : Theorem311Stmt) (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12)
    (h664 : ASInputs.AS_E_6_6_four) (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (h1113 : Stmt11_1_3)
    (h1114 : Stmt11_1_4) (hyp : Hyp11 G T L I n) (hG2 : KindG2 L (fsuV T I) n)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {g : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) :
    conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  by_contra hnc
  have hV := isElemAbelian_fsuV hyp
  obtain ⟨V₁, V₂, V₃, hV₁, hV₂, hV₃, h12, h23, -, -, -⟩ := exists_isVi hNF h1102 hyp
  have hfl := flagG2_of hNF h331 h1102 hyp hV₁ hV₂ hV₃ hG2
  have hn := hfl.two_le
  have hVN : V ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans (T_le_normalizer_fsuV T I)
  have hs : E3.sParam hV = 2 * n := sParam_eq hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331
    h1102 h1103 hyp (Or.inl ⟨hG2, rfl⟩) hV
  have haS : autI hV A ∈ E3.aSet (2 * n) (autI hV ⊤) := by
    have := autI_mem_aSet_of_le hV (le_rfl : A ≤ conjSubgroup V g) hAN hnc
      (by rw [E3.mQuot_self, hs]; omega)
    rwa [E3.mQuot_self, Nat.sub_zero, hs] at this
  have hr : ((2 * n : ℕ) : ℕ∞) < E3.rParam V := by
    rcases rParam_cases hNF hFM hFO hFH hS44 hN hFR h4213 h311 h63 h612 h664 h614 h331 h1102
        h1103 h1104 h1114 hyp (Or.inl ⟨hG2, rfl⟩) hV₂ with h | ⟨hSL3, -⟩
    · exact h
    · exact (kind_not_SL3_G2 hG2o hn hSL3 hG2).elim
  obtain ⟨l, hl, hlines⟩ := hFG.offender G L V ⊤ T V₁ V₂ V₃ n hfl hC A hAN
    (E3.isElemAbelian_conjSubgroup hV g) haS
  have key : ∀ x, x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
      conjSubgroup V₂ x ≤ conjSubgroup V₃ l →
      conjSubgroup V₂ x ≤ A ∧ LOf L (conjSubgroup V₂ x) ≤ conjSubgroup L g := by
    rintro x ⟨hxL, hx1, hx2⟩
    obtain ⟨D, hDA, -, hDm, hCCD, hcomm⟩ := hlines x hxL hx1 hx2
    set ED := V ⊓ Subgroup.centralizer (D : Set G) with hEDdef
    have hEN : ED ≤ Subgroup.normalizer (A : Set G) := by
      by_contra hne
      have h1 := E3.e3_4_one (V := V) (B := D) (g := g) (le_inf hDA (hDA.trans hAN)) hne
      rw [hDm] at h1
      exact absurd (lt_of_lt_of_le hr h1) (lt_irrefl _)
    have hIA : conjSubgroup V₂ x ≤ A := by
      rw [← hcomm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hEN
    have hE'N : conjSubgroup ED g⁻¹ ≤ ⊤ ⊓ Subgroup.normalizer (V : Set G) := by
      refine le_inf le_top ?_
      have := E3.conjSubgroup_mono_left g⁻¹ hEN
      rwa [E3.conjSubgroup_normalizer, hAdef, E3.conjSubgroup_conj_inv] at this
    have hEDel : IsElemAbelian 2 ED := B2F.isElemAbelian_mono inf_le_left hV
    have hE'm : E3.mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup ED g⁻¹ : Set G)) = 2 * n := by
      have := E3.mQuot_conjSubgroup A (A ⊓ Subgroup.centralizer (ED : Set G)) g⁻¹
      rw [conjSubgroup_inf_centralizer, hAdef, E3.conjSubgroup_conj_inv, ← hAdef, hCCD,
        hDm] at this
      exact this
    obtain ⟨y, hyL, hy⟩ := hFG.rootLine G L V ⊤ T V₁ V₂ V₃ n hfl hC _ hE'N
      (E3.isElemAbelian_conjSubgroup hEDel g⁻¹) hE'm
    have hAE : ⁅A, ED⁆ = conjSubgroup V₂ (y * g) := by
      have h1 := congrArg (fun U => conjSubgroup U g) hy
      rwa [E3.conjSubgroup_commutator, E3.conjSubgroup_inv_conj, conjSubgroup_conjSubgroup,
        ← hAdef] at h1
    have hxy : conjSubgroup V₂ x = conjSubgroup V₂ (y * g) := by
      rw [← hcomm, Subgroup.commutator_comm, hAE]
    have hLx : LOf L (conjSubgroup V₂ x) = conjSubgroup (LOf L V₂) x := by
      have h1 := map_conj_lOf (L := L) V₂ (g := x⁻¹)
        (Subgroup.le_normalizer (L.inv_mem hxL))
      rw [map_conj_eq_conjSubgroup, map_conj_eq_conjSubgroup, inv_inv] at h1
      exact h1.symm
    obtain ⟨hcc, hnc'⟩ := isCComponent_conj_lOf h1113 hyp hV₂ x
    rw [hxy] at hcc hnc'
    have heq := eq_conj_lOf_of_isCComponent h1113 hyp hV₂ (y * g) hcc hnc'
    refine ⟨hIA, ?_⟩
    rw [hLx, heq, ← conjSubgroup_conjSubgroup]
    refine E3.conjSubgroup_mono_left g fun z hz => ?_
    rw [mem_conjSubgroup_iff] at hz
    have h1 : y * z * y⁻¹ ∈ L := (perfectCore_le _).trans inf_le_left hz
    have h2 := L.mul_mem (L.mul_mem (L.inv_mem hyL) h1) hyL
    simpa [mul_assoc] using h2
  have hY := eq_of_le_sup_centralizer h1102 hyp
    (P := fun x => x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
      conjSubgroup V₂ x ≤ conjSubgroup V₃ l) (W := fun x => conjSubgroup V₂ x)
    (fun x hx => by
      have := E3.conjSubgroup_mono_left x (IsVi.le_fsuV hV₂)
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (L_le_normalizer_fsuV hyp hx.1)] at this)
    (hFG.lineGen G L V ⊤ T V₁ V₂ V₃ n hfl l hl)
  have hLLg : L ≤ conjSubgroup L g := by
    have h1 : (⨆ (x : G) (_ : x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
        conjSubgroup V₂ x ≤ conjSubgroup V₃ l), LOf L (conjSubgroup V₂ x)) ≤ conjSubgroup L g :=
      iSup₂_le fun x hx => (key x hx).2
    rwa [hY] at h1
  have hgM : g ∈ Subgroup.normalizer (L : Set G) := by
    have heq : L = conjSubgroup L g :=
      Subgroup.eq_of_le_of_card_ge hLLg (by rw [E3.card_conjSubgroup])
    exact conjSubgroup_eq_iff_mem_normalizer.mp heq.symm
  have hIl := (key l ⟨hl, E3.conjSubgroup_mono_left l h12, E3.conjSubgroup_mono_left l h23⟩).1
  have hIV : conjSubgroup V₂ l ≤ V := by
    have := E3.conjSubgroup_mono_left l (IsVi.le_fsuV hV₂)
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (L_le_normalizer_fsuV hyp hl)] at this
  have hI1 : conjSubgroup V₂ l ≠ ⊥ := by
    intro h
    apply IsVi.ne_bot hyp hV₂ (by norm_num : 1 ≤ 2)
    have := E3.conjSubgroup_mono_left l⁻¹ (le_of_eq h)
    rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_bot, le_bot_iff] at this
  by_cases hgV : g ∈ Subgroup.normalizer (V : Set G)
  · apply hnc
    rw [hAdef, conjSubgroup_eq_iff_mem_normalizer.mpr hgV]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  · have hTI := ((h1103 G T L I n hyp).2.2.2.1).2 g hgM hgV
    apply hI1
    rw [eq_bot_iff, ← hTI]
    exact le_inf hIV hIl

end CFSG.Quasithin.Vol2.Ch11.SecB
