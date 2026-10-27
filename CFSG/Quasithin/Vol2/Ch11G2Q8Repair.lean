module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived22Rad
public import CFSG.Quasithin.Vol2.Ch11G2Q8Stmts
public import CFSG.Quasithin.Vol2.Ch11SecB22Six
public import CFSG.Quasithin.Vol2.Ch11SecB24Claim
public import CFSG.Quasithin.Vol2.Ch11SecBG2Gen
public import CFSG.Quasithin.Vol2.Ch11SecBG2Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isCComponent_conj_of {U K₀ : Subgroup G}
    (hC : quasithinIsCComponent K₀ (Subgroup.normalizer (U : Set G)))
    (hnc : ¬ K₀ ≤ Subgroup.centralizer (U : Set G)) (h : G) :
    quasithinIsCComponent (conjSubgroup K₀ h)
        (Subgroup.normalizer ((conjSubgroup U h : Subgroup G) : Set G)) ∧
      ¬ conjSubgroup K₀ h ≤ Subgroup.centralizer ((conjSubgroup U h : Subgroup G) : Set G) := by
  have h3 := isCComponent_map_equiv (MulAut.conj h⁻¹) hC
  rw [map_conj_normalizer, map_conj_eq_conjSubgroup, map_conj_eq_conjSubgroup, inv_inv] at h3
  refine ⟨h3, fun hle => hnc ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
  rwa [map_conj_centralizer, conjSubgroup_map_conj, conjSubgroup_map_conj] at this

omit [Finite G] in
theorem eq_conj_of_isCComponent {U K₀ : Subgroup G}
    (huniq : ∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.normalizer (U : Set G)) →
      ¬ K ≤ Subgroup.centralizer (U : Set G) → K = K₀) (h : G) {K : Subgroup G}
    (hK : quasithinIsCComponent K
      (Subgroup.normalizer ((conjSubgroup U h : Subgroup G) : Set G)))
    (hKc : ¬ K ≤ Subgroup.centralizer ((conjSubgroup U h : Subgroup G) : Set G)) :
    K = conjSubgroup K₀ h := by
  have h1 := isCComponent_map_equiv (MulAut.conj h) hK
  rw [map_conj_normalizer, conjSubgroup_map_conj] at h1
  have h2 : ¬ K.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (U : Set G) := by
    intro hle
    apply hKc
    have := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hle
    have hid : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id G := by
      ext y
      simp [mul_assoc]
    rwa [map_conj_centralizer, map_conj_eq_conjSubgroup U h⁻¹, inv_inv, Subgroup.map_map, hid,
      Subgroup.map_id] at this
  have h3 := huniq _ h1 h2
  rw [← h3, map_conj_eq_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel]
  ext x
  rw [mem_conjSubgroup_iff]
  simp

theorem derivedG2WeakClosureRad_of (hOff : FactG2OffenderRad) (hRL : FactG2RootLineRad)
    (hLG : FactG2LineGen) (hNF : NatFacts) (hFM : FactMParam) (hFO : FactOddCodim)
    (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt) (hN : FactNot4213) (hFR : FactRootInv)
    (hG2o : FactG2DerivedOrder) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1104 : Stmt11_0_4) (h1114 : Stmt11_1_4) (hR : Rad11_1_3) : DerivedG2WeakClosureRad := by
  intro G _ _ T L I n hyp hG2 hC g hAT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  by_contra hnc
  have hV := isElemAbelian_fsuV hyp
  obtain ⟨V₁, V₂, V₃, hV₁, hV₂, hV₃, h12, h23, -, -, -⟩ := exists_isVi hNF h1102 hyp
  have hfl := flagG2_of hNF h331 h1102 hyp hV₁ hV₂ hV₃ hG2
  have hn := hfl.two_le
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
  obtain ⟨hRc, hRnc, hRu⟩ := hR G T L I n V₂ hyp hG2 hC hV₂
  set A₂ := ⁅V₂, LOf L V₂⁆ with hA₂def
  obtain ⟨l, hl, hlines⟩ := hOff G L V ⊤ T V₁ V₂ V₃ n hfl hC A hAN
    (E3.isElemAbelian_conjSubgroup hV g) haS
  have hLx : ∀ x ∈ L, LOf L (conjSubgroup V₂ x) = conjSubgroup (LOf L V₂) x := by
    intro x hxL
    have h1 := map_conj_lOf (L := L) V₂ (g := x⁻¹) (Subgroup.le_normalizer (L.inv_mem hxL))
    rw [map_conj_eq_conjSubgroup, map_conj_eq_conjSubgroup, inv_inv] at h1
    exact h1.symm
  have hAx : ∀ x ∈ L, ⁅conjSubgroup V₂ x, LOf L (conjSubgroup V₂ x)⁆ = conjSubgroup A₂ x := by
    intro x hxL
    rw [hLx x hxL, hA₂def, E3.conjSubgroup_commutator]
  have key : ∀ x, x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
      conjSubgroup V₂ x ≤ conjSubgroup V₃ l →
      conjSubgroup A₂ x ≤ A ∧ LOf L (conjSubgroup V₂ x) ≤ conjSubgroup L g := by
    rintro x ⟨hxL, hx1, hx2⟩
    obtain ⟨D, hDA, -, hDm, hCCD, hcomm⟩ := hlines x hxL hx1 hx2
    rw [hAx x hxL] at hcomm
    set ED := V ⊓ Subgroup.centralizer (D : Set G) with hEDdef
    have hEN : ED ≤ Subgroup.normalizer (A : Set G) := by
      by_contra hne
      have h1 := E3.e3_4_one (V := V) (B := D) (g := g) (le_inf hDA (hDA.trans hAN)) hne
      rw [hDm] at h1
      exact absurd (lt_of_lt_of_le hr h1) (lt_irrefl _)
    have hIA : conjSubgroup A₂ x ≤ A := by
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
    obtain ⟨y, hyL, hy⟩ := hRL G L V ⊤ T V₁ V₂ V₃ n hfl hC _ hE'N
      (E3.isElemAbelian_conjSubgroup hEDel g⁻¹) hE'm
    rw [hAx y hyL] at hy
    have hAE : ⁅A, ED⁆ = conjSubgroup A₂ (y * g) := by
      have h1 := congrArg (fun U => conjSubgroup U g) hy
      rwa [E3.conjSubgroup_commutator, E3.conjSubgroup_inv_conj, conjSubgroup_conjSubgroup,
        ← hAdef] at h1
    have hxy : conjSubgroup A₂ x = conjSubgroup A₂ (y * g) := by
      rw [← hcomm, Subgroup.commutator_comm, hAE]
    obtain ⟨hcc, hnc'⟩ := isCComponent_conj_of hRc hRnc x
    rw [hxy] at hcc hnc'
    have heq := eq_conj_of_isCComponent hRu (y * g) hcc hnc'
    refine ⟨hIA, ?_⟩
    rw [hLx x hxL, heq, ← conjSubgroup_conjSubgroup]
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
    (hLG G L V ⊤ T V₁ V₂ V₃ n hfl l hl)
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
  have hA₂V₂ : A₂ ≤ V₂ := by
    rw [hA₂def, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp ((perfectCore_le _).trans inf_le_right)
  have hIV : conjSubgroup A₂ l ≤ V := by
    have := E3.conjSubgroup_mono_left l (hA₂V₂.trans (IsVi.le_fsuV hV₂))
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (L_le_normalizer_fsuV hyp hl)] at this
  have hA₂1 : A₂ ≠ ⊥ := by
    intro hb
    apply hRnc
    intro z _
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hb, Subgroup.coe_bot, Set.mem_singleton_iff] at hw
    rw [hw, one_mul, mul_one]
  have hI1 : conjSubgroup A₂ l ≠ ⊥ := by
    intro h
    apply hA₂1
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

end CFSG.Quasithin.Vol2.Ch11.G2Q8
