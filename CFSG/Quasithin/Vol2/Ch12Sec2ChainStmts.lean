module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def transvAxis {V : Type*} [CommGroup V] (A : Subgroup V) : Subgroup (MulAut V) where
  carrier := {c | (∀ a ∈ A, c a = a) ∧ ∀ v, c v * v⁻¹ ∈ A}
  one_mem' := ⟨fun _ _ => rfl, fun v => by simp [A.one_mem]⟩
  mul_mem' := by
    rintro c d ⟨hc₁, hc₂⟩ ⟨hd₁, hd₂⟩
    refine ⟨fun a ha => ?_, fun v => ?_⟩
    · rw [MulAut.mul_apply, hd₁ a ha, hc₁ a ha]
    · rw [MulAut.mul_apply, show c (d v) * v⁻¹ = (c (d v) * (d v)⁻¹) * (d v * v⁻¹) by group]
      exact A.mul_mem (hc₂ _) (hd₂ v)
  inv_mem' := by
    rintro c ⟨hc₁, hc₂⟩
    refine ⟨fun a ha => ?_, fun v => ?_⟩
    · have h1 := hc₁ a ha
      calc c⁻¹ a = c⁻¹ (c a) := by rw [h1]
        _ = a := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · have h1 := hc₂ (c⁻¹ v)
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h1
      have h2 := A.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at h2

@[expose] def Config12_2_24 {G : Type} [Group G] (T L V H P U I : Subgroup G) (h : G)
    (n p : ℕ) : Prop :=
  IsHStar T (Subgroup.normalizer (L : Set G)) H ∧ Group.IsSolvable ↥H ∧
    (n = 3 ∨ n = 4 ∨ n = 5) ∧ Nat.card V = 2 ^ n ∧
    T ≤ L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ∧ IsLnBlock L n ∧
    p.Prime ∧ p ≠ 2 ∧ P = Subgroup.zpowers h ∧ orderOf h = p ∧ h ∈ H ∧
    h ∉ Subgroup.normalizer (L : Set G) ∧
    I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
    U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
    IsElemAbelian 2 U ∧
    (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
    U ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
    (U ⊓ V).relIndex V = 2 ∧
    (∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)) ∧
    U ≤ pCoreOf 2 H ∧ U ⊓ V = pCoreOf 2 H ⊓ V ∧ oTwoUpper H = P ⊔ U ∧
    H ≤ Subgroup.normalizer (U : Set G) ∧ H ≤ Subgroup.normalizer (I : Set G) ∧
    I = P ⊔ U ⊔ V ∧ H = I ⊔ T ∧ ¬ I ≤ Subgroup.normalizer (L : Set G) ∧
    ⁅pCoreOf 2 (L ⊔ T), U⁆ ≤ U ⊓ V

@[expose] def Stmt12_2_24_config : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V →
      ∃ (H P U I : Subgroup G) (h : G) (n p : ℕ), Config12_2_24 T L V H P U I h n p

@[expose] def Stmt12_2_25_26_of_config : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Config12_2_24 T L V H P U I h n p →
      (Subgroup.normalizer (L : Set G) = L ∧ V = pCoreOf 2 L ∧ (n = 3 ∨ n = 4) ∧
        Nat.card (quasithinOmegaOneCenter T) = 2) ∧
      ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L

theorem stmt12_2_24_of_config (hc : Stmt12_2_24_config) : Stmt12_2_24 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  obtain ⟨-, -, hn, hV, -, hB, -⟩ := hC
  exact ⟨n, hn, hV, hB⟩

theorem stmt12_2_25_of_config (hc : Stmt12_2_24_config) (h2526 : Stmt12_2_25_26_of_config) :
    Stmt12_2_25 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  obtain ⟨⟨hML, hVO, hn, hZ⟩, -⟩ := h2526 G T L V H P U I h n p hH hE hC
  obtain ⟨-, -, -, hV, -⟩ := hC
  refine ⟨hML, hVO, ?_, hZ⟩
  rcases hn with rfl | rfl
  · exact Or.inl hV
  · exact Or.inr hV

theorem stmt12_2_26_of_config (hc : Stmt12_2_24_config) (h2526 : Stmt12_2_25_26_of_config) :
    Stmt12_2_26 := by
  intro G _ _ T L V hH hE
  obtain ⟨H, P, U, I, h, n, p, hC⟩ := hc G T L V hH hE
  exact (h2526 G T L V H P U I h n p hH hE hC).2

theorem stmt12_2_13_of_config (hc : Stmt12_2_24_config) (h2526 : Stmt12_2_25_26_of_config)
    (h27 : Stmt12_2_27) : Stmt12_2_13 :=
  stmt12_2_13_of_chain (stmt12_2_24_of_config hc) (stmt12_2_25_of_config hc h2526)
    (stmt12_2_26_of_config hc h2526) h27

end CFSG.Quasithin.H13
