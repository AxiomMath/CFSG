module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LL
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecB5EvL2App

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem normalizer_T1_le_XOf_L2p (h311 : Theorem311Stmt)
    (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    {K₁ : Subgroup G} {s : G} (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hE9 : p % 8 = 3 ∨ p % 8 = 5 →
      ¬ pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
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
    exact C10P34.five_le_of_isPerfect hp2 e
  obtain ⟨P3, hP3X, hP3, hP33⟩ := exists_E9_le_XOf h hD
  have hXi := isXi_XOf h hD
  have hW := pCoreOf_sup_le h hD hXK hS
  have hodd : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
      n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := fun n hn hno =>
    C10P34.mem_normalizer_of_odd_pair hc hp5 e (e₂.trans e) hXK hXi.1.symm
      (fun x hx => pow_three_mem h hD hx) hP3X hP3 hP33 hS hXi.2.1 inf_le_left hW
      (fun h8 => hc.pCoreOf_map_ne_bot (g := s⁻¹) (Subgroup.inv_mem _ hsG₀) rfl hXK
        (Subgroup.inv_mem _ (hXi.2.1 hs)) (hE9 h8))
      (Subgroup.mem_sup_left hn) hn hno
  have hTN := T1_normal h.h37 h.h38 h.hyp
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
    ⟨hTN, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow hTN⟩
  refine (C10P34.le_oTwoUpper_sup hTsyl).trans (sup_le ?_ hXi.2.1)
  exact (Subgroup.closure_le _).mpr fun n hn => hodd n hn.1 hn.2

end CFSG.Quasithin.Vol2.Ch10.SecB
