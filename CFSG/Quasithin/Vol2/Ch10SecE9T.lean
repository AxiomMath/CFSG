module

public import CFSG.Quasithin.Vol2.Ch10SecE9S
public import CFSG.Quasithin.Vol2.Ch10SecE9R

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def E9CoreSharp (T L P : Subgroup G) : Prop :=
  ∃ (K₁ : Subgroup G) (s : G) (p : ℕ), s ∈ T ∧
    K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) =
      K₁ ⊔ CFSG.conjugate K₁ s ∧
    p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
    Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)) ∧
    pCoreOf 2 (oTwoUpper P) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) ∧
    T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s) ≤ T1 T L ∧
    (∃ y ∈ K₁ ⊔ CFSG.conjugate K₁ s, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer (T1 T L : Set G) ∧ y ∉ oTwoUpper P) ∧
    (∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Nat.Coprime (orderOf n) 6 →
      n ∈ Subgroup.normalizer (oTwoUpper P : Set G)) ∧
    ∀ n ∈ Subgroup.normalizer (T1 T L : Set G),
      (∀ z ∈ K₁ ⊔ CFSG.conjugate K₁ s,
        n * z * n⁻¹ * z⁻¹ ∈ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) →
      n ∈ Subgroup.normalizer (oTwoUpper P : Set G)

@[expose] def Gap10_2_5E9PtSharp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I →
    (∀ y ∈ Subgroup.normalizer (T1 T L : Set G), y ∈ fsuM T L → orderOf y ≠ 3) →
    ∀ P P' : Subgroup G,
      IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P → IsMaxSubgroupIn (fsuL0 T L ⊔ T) P' → T ≤ P' →
      P ≠ P' → E9CoreSharp T L P → E9CoreSharp T L P' → False

variable [Finite G] {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ}
  {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem orderOf_ne_three_of_mem_fsuM (h1013 : Stmt10_1_3) (h : MaxCtx T L I t Ψ c)
    (h3 : Case10_1_1Three T L I) {y : G} (hyT : y ∈ Subgroup.normalizer (T1 T L : Set G))
    (hyM : y ∈ fsuM T L) : orderOf y ≠ 3 := by
  intro hy3
  have h1 := h1013 G T L I h.hyp 3 Nat.prime_three (by norm_num)
    (by rw [card_lbar h3.1]; norm_num)
  have hy : y ∈ oPrimeResidualOf 3 (fsuM T L) :=
    Subgroup.subset_closure ⟨hyM, 1, by rw [hy3, pow_one]⟩
  rw [h1] at hy
  exact E9.not_mem_sup_of_orderOf_three h hy3 hyT (Subgroup.mem_sup_left hy)

theorem core_facts (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    {K₁ : Subgroup G} {s : G} (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hbad : pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) :
    (p % 12 = 1 ∨ p % 12 = 11) ∧
    (∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Nat.Coprime (orderOf n) 6 →
      n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G)) ∧
    ∀ n ∈ Subgroup.normalizer (T1 T L : Set G),
      (∀ z ∈ K₁ ⊔ CFSG.conjugate K₁ s,
        n * z * n⁻¹ * z⁻¹ ∈ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) →
      n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := h.hyp.fsu.simple
  have hKl : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  obtain ⟨hXK, hG₀K, hS⟩ := inGzero_data h (A := A)
  have hH2 := pCoreOf_GA_ne_bot h311 h hD hA
  have hsG₀ : s ∈ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right hs)
  have hK₂ : CFSG.conjugate K₁ s ∈
      cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj s⁻¹) hK₁
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ hsG₀))] at h1
  have hne : K₁ ≠ CFSG.conjugate K₁ s := SecA.ne_conjugate hsn
  obtain ⟨e₂⟩ := nonempty_modO2_conjugate K₁ s
  have hc₁ := C10P34.center_eq_bot_of_mulEquiv e
  have hc₂ := C10P34.center_eq_bot_of_mulEquiv (e₂.trans e)
  obtain ⟨φ, hφ, hker, hφ₁, hφ₂⟩ := exists_pair_prod hKl h.h37 hH2 hK₁ hK₂ hne hc₁ hc₂
  rw [hK] at hXK hS hG₀K
  have hc : C10P34.PairCtx (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) K₁
      (CFSG.conjugate K₁ s) φ :=
    ⟨hK₁, hK₂, hne, fun L₁ L₂ h₁ h₂ hne' =>
      (Vol2Native.lemma_1_2_1_two hKl h.h37 hH2 h₁ h₂ hne').1, hG₀K, hφ, hker, hφ₁, hφ₂, hc₁, hc₂⟩
  have hp5 : 5 ≤ p := by
    have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK₁)
    exact C10P34.five_le_of_isPerfect (by rintro rfl; omega) e
  obtain ⟨P3, hP3X, hP3, hP33⟩ := exists_E9_le_XOf h hD
  have hXi := isXi_XOf h hD
  have hW := pCoreOf_sup_le h hD hXK hS
  have hTN := T1_normal h.h37 h.h38 h.hyp
  have hO : ∀ k : ↥(K₁ ⊔ CFSG.conjugate K₁ s),
      (k : G) ∈ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  refine ⟨E9.mod_twelve_of_pair hc hp5 h8 e (e₂.trans e) hXK hXi.1.symm
      (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1 hbad,
    fun n hnT hn6 => ?_, fun n hnT hn => ?_⟩
  · exact E9.mem_normalizer_of_coprime hc hp5 h8 e (e₂.trans e) hXK hXi.1.symm
      (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1 h.hyp.fsu.sylow.1
      (le_sup_right.trans le_sup_right) inf_le_left hTN hW (s := s⁻¹) (T.inv_mem hs) rfl hbad
      (Subgroup.mem_sup_left hnT) hnT hn6
  · have hnK := hc.normal (Subgroup.mem_sup_left hnT)
    refine E9.mem_normalizer_of_inner hc hp5 e (e₂.trans e) hXK hXi.1.symm
      (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1 hnK (a₁ := 1) (a₂ := 1)
      (fun z hz hz' => ?_) (Subgroup.one_mem _) (Subgroup.one_mem _)
    have h1 : φ ⟨n * z * n⁻¹, hz'⟩ * (φ ⟨z, hz⟩)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact hO _ (hn z hz)
    rw [mul_inv_eq_one] at h1
    rw [h1]
    simp

theorem e9CoreSharp_of_core (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    (hcore : E9Core T L (preIn Ψ (A.prod A) ⊔ T)) :
    E9CoreSharp T L (preIn Ψ (A.prod A) ⊔ T) := by
  obtain ⟨K₁, s, p, hs, hK₁, hsn, hK, hp, h8, ⟨e⟩, hbad, hST, hy⟩ := hcore
  obtain ⟨h12, hcop, hker⟩ := core_facts h311 h hD hA hs hK₁ hsn hK hp h8 e hbad
  exact ⟨K₁, s, p, hs, hK₁, hsn, hK, hp, by omega, ⟨e⟩, hbad, hST, hy, hcop, hker⟩

theorem e9CoreSharp_of_max (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) {P : Subgroup G} (hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P)
    (hTP : T ≤ P) (hcore : E9Core T L P) : E9CoreSharp T L P := by
  rcases maximal_classify h.h37 h.h38 h.hyp h.ht h.htn h.hC hP hTP with rfl | rfl
  · exact e9CoreSharp_of_core h311 h parData_a (Or.inl rfl) hcore
  · exact e9CoreSharp_of_core h311 h parData_b (Or.inr rfl) hcore

theorem exists_maxCtx (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    ∃ (t : G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ) (c : L32.Γ), MaxCtx T L I t Ψ c := by
  have hinner : T1Inner T L := fun s hs => by
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp h3.1 hinner ht htn
  exact ⟨t, Ψ, c, h37, h38, hyp, ht, htn, hC⟩

theorem oTwoUpper_sup_eq_fsuL0 (h : MaxCtx T L I t Ψ c) {P P' : Subgroup G}
    (hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P) (hTP : T ≤ P)
    (hP' : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P') (hTP' : T ≤ P') (hne : P ≠ P') :
    oTwoUpper P ⊔ oTwoUpper P' = fsuL0 T L := by
  rcases maximal_classify h.h37 h.h38 h.hyp h.ht h.htn h.hC hP hTP with rfl | rfl <;>
    rcases maximal_classify h.h37 h.h38 h.hyp h.ht h.htn h.hC hP' hTP' with rfl | rfl
  · exact absurd rfl hne
  · exact XOf_sup_eq h
  · rw [sup_comm]; exact XOf_sup_eq h
  · exact absurd rfl hne

theorem mem_fsuM_of_normalizes (h : MaxCtx T L I t Ψ c) {P P' : Subgroup G}
    (hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P) (hTP : T ≤ P)
    (hP' : IsMaxSubgroupIn (fsuL0 T L ⊔ T) P') (hTP' : T ≤ P') (hne : P ≠ P') {n : G}
    (hn : n ∈ Subgroup.normalizer (oTwoUpper P : Set G))
    (hn' : n ∈ Subgroup.normalizer (oTwoUpper P' : Set G)) : n ∈ fsuM T L := by
  show n ∈ Subgroup.normalizer (fsuL0 T L : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn hn' ⊢
  rw [← oTwoUpper_sup_eq_fsuL0 h hP hTP hP' hTP' hne, Subgroup.map_sup, hn, hn']

theorem gap10_2_5E9Pt_of_sharp (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h311 : Theorem311Stmt) (h1013 : Stmt10_1_3)
    (hsh : Gap10_2_5E9PtSharp) : Gap10_2_5E9Pt := by
  intro G _ _ T L I hyp h3 P P' hP hTP hP' hTP' hne hc hc'
  obtain ⟨t, Ψ, c, h⟩ := exists_maxCtx h37 h38 hyp h3
  exact hsh G T L I hyp h3 (fun y hyT hyM => orderOf_ne_three_of_mem_fsuM h1013 h h3 hyT hyM)
    P P' hP hTP hP' hTP' hne (e9CoreSharp_of_max h311 h hP hTP hc)
    (e9CoreSharp_of_max h311 h hP' hTP' hc')

end CFSG.Quasithin.Vol2.Ch10.SecB
