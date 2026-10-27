module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Lin
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint.NativeSporadic

namespace Stellmacher.L3YC

namespace Row18

open CFSG.Sporadic.HS.Native (hsData)

theorem hs_overgroup_cases
    {Z : Subgroup (J hsData)} (hZ : hsCtx.S ≤ Z) :
    (Z = ⊤ ∧ Nat.card Z = 2 ^ 9 * 86625) ∨
      ∃ j < 5, Z = hsCtx.Y j ∧ Nat.card Z = #[1, 15, 21, 3, 3][j]! * 512 := by
  obtain ⟨j, hj, rfl⟩ := hs_complete Z hZ
  by_cases hj5 : j < 5
  · right
    have hm : memberOrTop 5 hsCtx.Y j = hsCtx.Y j := by simp [memberOrTop, hj5]
    exact ⟨j, hj5, hm, by rw [hm]; exact hs_member_card j hj5⟩
  · left
    have hm : memberOrTop 5 hsCtx.Y j = ⊤ := by simp [memberOrTop, hj5]
    rw [hm, Subgroup.card_top]
    exact ⟨rfl, hs_card⟩

theorem hs_ratio_two {j : ℕ} (hj : j < 5) (h : #[1, 15, 21, 3, 3][j]! * 512 = 10752) : j = 2 := by
  interval_cases j <;> simp_all

theorem hs_ratio_three {j : ℕ} (hj : j < 5) (h : #[1, 15, 21, 3, 3][j]! * 512 = 1536) :
    j = 3 ∨ j = 4 := by
  interval_cases j <;> simp_all

theorem hs_ratio_five {j : ℕ} (hj : j < 5) (h : ¬ 5 ∣ #[1, 15, 21, 3, 3][j]! * 512) :
    j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  interval_cases j <;> simp_all

theorem hs_J_overgroup_le
    {B P Z₁ Z₂ : Subgroup (J hsData)} (hB : hsCtx.S ≤ B)
    (hBc : Nat.card B = 10752) (h₁ : hsCtx.S ≤ Z₁) (h₁B : Z₁ ≤ B) (h₁c : Nat.card Z₁ = 1536)
    (h₂ : hsCtx.S ≤ Z₂) (h₂B : Z₂ ≤ B) (h₂c : Nat.card Z₂ = 1536) (hne : Z₁ ≠ Z₂)
    (hP : hsCtx.S ≤ P) (hP5 : ¬ 5 ∣ Nat.card P) : P ≤ B := by
  rcases hs_overgroup_cases hB with ⟨-, hc⟩ | ⟨jB, hjB, hBe, hBr⟩
  · rw [hBc] at hc; omega
  rw [hBc] at hBr
  have hjB2 := hs_ratio_two hjB hBr.symm
  rcases hs_overgroup_cases h₁ with ⟨-, hc⟩ | ⟨j₁, hj₁, h₁e, h₁r⟩
  · rw [h₁c] at hc; omega
  rw [h₁c] at h₁r
  rcases hs_overgroup_cases h₂ with ⟨-, hc⟩ | ⟨j₂, hj₂, h₂e, h₂r⟩
  · rw [h₂c] at hc; omega
  rw [h₂c] at h₂r
  rcases hs_overgroup_cases hP with ⟨-, hc⟩ | ⟨j, hj, hPe, hPr⟩
  · exfalso
    apply hP5
    rw [hc]
    exact ⟨2 ^ 9 * 17325, by norm_num⟩
  rw [hPr] at hP5
  have h1 := hs_ratio_three hj₁ h₁r.symm
  have h2 := hs_ratio_three hj₂ h₂r.symm
  have hj12 : j₁ ≠ j₂ := by
    rintro rfl
    exact hne (h₁e.trans h₂e.symm)
  rcases hs_ratio_five hj hP5 with rfl | hj2 | hj3 | hj4
  ·
    have hS : Nat.card hsCtx.S = 512 := hs_card_S
    have hPc : Nat.card P = 512 := by rw [hPr]; rfl
    have : hsCtx.S = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hS, hPc])
    rw [← this]
    exact hB
  · subst hj2
    rw [hPe, hBe, hjB2]
  · have : j = j₁ ∨ j = j₂ := by omega
    rcases this with rfl | rfl
    · rw [hPe, ← h₁e]; exact h₁B
    · rw [hPe, ← h₂e]; exact h₂B
  · have : j = j₁ ∨ j = j₂ := by omega
    rcases this with rfl | rfl
    · rw [hPe, ← h₁e]; exact h₁B
    · rw [hPe, ← h₂e]; exact h₂B

theorem exists_equiv_sylow {Γ X : Type} [Group Γ] [Finite Γ] [Group X] [Finite X] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) (e : X ≃* Γ) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem hs_overgroup_le
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* Carrier .HS)) {T B P Z₁ Z₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hB : T ≤ B) (hBc : Nat.card B = 10752) (h₁ : T ≤ Z₁) (h₁B : Z₁ ≤ B)
    (h₁c : Nat.card Z₁ = 1536) (h₂ : T ≤ Z₂) (h₂B : Z₂ ≤ B) (h₂c : Nat.card Z₂ = 1536)
    (hne : Z₁ ≠ Z₂) (hP : T ≤ P) (hP5 : ¬ 5 ∣ Nat.card P) : P ≤ B := by
  obtain ⟨e⟩ := hX
  obtain ⟨ψ, hψ⟩ := exists_equiv_sylow hs_S_sylow (e.trans (seedEquiv hs_facts.toBaseFacts)) hT
  have key : ∀ A : Subgroup X, T ≤ A → hsCtx.S ≤ A.map ψ.toMonoidHom := fun A hA =>
    hψ ▸ Subgroup.map_mono hA
  have hcard : ∀ A : Subgroup X, Nat.card (A.map ψ.toMonoidHom) = Nat.card A := fun A =>
    Subgroup.card_map_of_injective ψ.injective
  have := hs_J_overgroup_le (B := B.map ψ.toMonoidHom) (P := P.map ψ.toMonoidHom)
    (Z₁ := Z₁.map ψ.toMonoidHom) (Z₂ := Z₂.map ψ.toMonoidHom) (key _ hB) (by rw [hcard]; exact hBc)
    (key _ h₁) (Subgroup.map_mono h₁B) (by rw [hcard]; exact h₁c) (key _ h₂)
    (Subgroup.map_mono h₂B) (by rw [hcard]; exact h₂c)
    (fun h => hne (Subgroup.map_injective ψ.injective h)) (key _ hP) (by rw [hcard]; exact hP5)
  exact (Subgroup.map_le_map_iff_of_injective ψ.injective).mp this

section Ambient

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem card_subgroupOf_of_le {N A : Subgroup K} (h : A ≤ N) :
    Nat.card (A.subgroupOf N) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

omit [Finite K] in
theorem le_of_subgroupOf_le {N A A' : Subgroup K} (h : A ≤ N)
    (hle : A.subgroupOf N ≤ A'.subgroupOf N) : A ≤ A' := fun x hx => hle (show (⟨x, h hx⟩ : N) ∈
    A.subgroupOf N from hx)

theorem hs_overgroup_le_sub
    {N : Subgroup K} (hN : Nonempty (↥N ≃* Carrier .HS))
    {T B P Z₁ Z₂ : Subgroup K} (hT : IsSylowTwoOf T N) (hBN : B ≤ N) (hB : T ≤ B)
    (hBc : Nat.card B = 10752) (h₁ : T ≤ Z₁) (h₁B : Z₁ ≤ B) (h₁c : Nat.card Z₁ = 1536)
    (h₂ : T ≤ Z₂) (h₂B : Z₂ ≤ B) (h₂c : Nat.card Z₂ = 1536) (hne : Z₁ ≠ Z₂) (hP : T ≤ P)
    (hPN : P ≤ N) (hP5 : ¬ 5 ∣ Nat.card P) : P ≤ B := by
  have hTN : T ≤ N := hT.1
  have hT' : IsSylowTwoOf (T.subgroupOf N) (⊤ : Subgroup ↥N) :=
    K1.isSylowTwoOf_top_iff.mpr ⟨A4.isPGroup_subgroupOf_of_le hT.1 hT.2.1, hT.2.2⟩
  have hmono : ∀ {A A' : Subgroup K}, A ≤ A' → A.subgroupOf N ≤ A'.subgroupOf N :=
    fun h x hx => h hx
  have := hs_overgroup_le hN hT' (B := B.subgroupOf N) (P := P.subgroupOf N)
    (Z₁ := Z₁.subgroupOf N) (Z₂ := Z₂.subgroupOf N) (hmono hB)
    (by rw [card_subgroupOf_of_le hBN]; exact hBc) (hmono h₁) (hmono h₁B)
    (by rw [card_subgroupOf_of_le (h₁B.trans hBN)]; exact h₁c) (hmono h₂) (hmono h₂B)
    (by rw [card_subgroupOf_of_le (h₂B.trans hBN)]; exact h₂c)
    (fun h => hne (le_antisymm (le_of_subgroupOf_le (h₁B.trans hBN) h.le)
      (le_of_subgroupOf_le (h₂B.trans hBN) h.ge)))
    (hmono hP) (by rw [card_subgroupOf_of_le hPN]; exact hP5)
  exact le_of_subgroupOf_le hPN this

theorem hs_overgroup_le_of_psl32
    {N Lb T P : Subgroup K} (hN : Nonempty (↥N ≃* Carrier .HS))
    (hLN : Lb ≤ N) (hT : IsSylowTwoOf T N) (hTL : T ≤ Lb) (hLbc : Nat.card Lb = 10752)
    (ψ : ↥Lb →* SL32) (hψ : Function.Surjective ψ) (hTP : T ≤ P) (hPN : P ≤ N)
    (hP5 : ¬ 5 ∣ Nat.card P) : P ≤ Lb := by
  have hTLb : IsSylowTwoOf T Lb := B6.isSylowTwoOf_mono hT hTL hLN
  obtain ⟨Z₁, Z₂, h₁, h₂, hne, hi₁, hi₂⟩ := Row18.exists_two_overgroups ψ hψ
    (S := T.subgroupOf Lb) (A4.isPGroup_subgroupOf_of_le hTL hT.2.1) hTLb.2.2
  have hc : ∀ Z : Subgroup ↥Lb, Z.index = 7 → Nat.card Z = 1536 := fun Z hZ => by
    have := Subgroup.card_mul_index Z
    rw [hZ] at this
    have h : Nat.card ↥Lb = 10752 := hLbc
    omega
  have hTZ : ∀ Z : Subgroup ↥Lb, T.subgroupOf Lb ≤ Z → T ≤ Z.map Lb.subtype := fun Z hZ t ht =>
    ⟨⟨t, hTL ht⟩, hZ (show (⟨t, hTL ht⟩ : ↥Lb) ∈ T.subgroupOf Lb from ht), rfl⟩
  refine hs_overgroup_le_sub hN hT hLN hTL hLbc (Z₁ := Z₁.map Lb.subtype)
    (Z₂ := Z₂.map Lb.subtype) (hTZ _ h₁) (Subgroup.map_subtype_le _)
    (by rw [Subgroup.card_map_of_injective Lb.subtype_injective]; exact hc _ hi₁)
    (hTZ _ h₂) (Subgroup.map_subtype_le _)
    (by rw [Subgroup.card_map_of_injective Lb.subtype_injective]; exact hc _ hi₂)
    (fun h => hne (Subgroup.map_injective Lb.subtype_injective h)) hTP hPN hP5

end Ambient

end Row18

end Stellmacher.L3YC

end CFSG.Quasithin
