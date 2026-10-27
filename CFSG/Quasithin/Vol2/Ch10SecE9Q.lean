module

public import CFSG.Quasithin.Vol2.Ch10SecE9H
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2App

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def E9Core (T L P : Subgroup G) : Prop :=
  ∃ (K₁ : Subgroup G) (s : G) (p : ℕ), s ∈ T ∧
    K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) =
      K₁ ⊔ CFSG.conjugate K₁ s ∧
    p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)) ∧
    pCoreOf 2 (oTwoUpper P) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s) ∧
    T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s) ≤ T1 T L ∧
    ∃ y ∈ K₁ ⊔ CFSG.conjugate K₁ s, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer (T1 T L : Set G) ∧ y ∉ oTwoUpper P

variable [Finite G] {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ}
  {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem mem_normalizer_or_core (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    {K₁ : Subgroup G} {s : G} (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hbad : pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) {n : G}
    (hnT : n ∈ Subgroup.normalizer (T1 T L : Set G)) (hodd : Odd (orderOf n)) :
    n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) ∨ E9Core T L (preIn Ψ (A.prod A) ⊔ T) := by
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
  rcases E9.mem_normalizer_or_witness hc hp5 h8 e (e₂.trans e) hXK hXi.1.symm
      (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1 h.hyp.fsu.sylow.1
      (le_sup_right.trans le_sup_right) inf_le_left hTN hW (s := s⁻¹) (T.inv_mem hs) rfl hbad
      (Subgroup.mem_sup_left hnT) hnT hodd with hn | ⟨hST₁, y, hyK, hy3, hyT, hyX⟩
  · exact Or.inl hn
  · exact Or.inr ⟨K₁, s, p, hs, hK₁, hsn, hK, hp, h8, ⟨e⟩, hbad, hST₁, y, hyK, hy3, hyT, hyX⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
