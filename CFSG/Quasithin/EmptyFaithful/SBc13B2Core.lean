module

public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc13

section Quot

variable {G : Type} [Group G]

theorem relIndex_pCoreOf (X : Subgroup G) :
    (pCoreOf 2 X).relIndex X = Nat.card (OTwoQuot X) := by
  have h : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [Subgroup.relIndex, h]
  rfl

theorem mem_normalizer_sup_of_mem_normalizer {B C : Subgroup G} {x : G}
    (hB : x ∈ Subgroup.normalizer (B : Set G)) (hC : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  have key : ∀ a : G, a ∈ Subgroup.normalizer (B : Set G) → a ∈ Subgroup.normalizer (C : Set G) →
      ∀ y ∈ B ⊔ C, a * y * a⁻¹ ∈ B ⊔ C := by
    intro a haB haC y hy
    rw [Subgroup.sup_eq_closure] at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact Subgroup.subset_closure (Or.inl ((Subgroup.mem_normalizer_iff.mp haB z).mp hz))
      · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.mp haC z).mp hz))
    | one => simp
    | mul u v _ _ ihu ihv => simpa [mul_assoc] using Subgroup.mul_mem _ ihu ihv
    | inv u _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key x hB hC y, fun hy => by
    simpa [mul_assoc] using key x⁻¹ (Subgroup.inv_mem _ hB) (Subgroup.inv_mem _ hC) _ hy⟩

theorem le_pCoreOf_or_le_sup {X D : Subgroup G} (hDX : D ≤ X)
    (hn : X ≤ Subgroup.normalizer (D : Set G)) (hs : IsSimpleGroup (OTwoQuot X)) :
    D ≤ pCoreOf 2 X ∨ X ≤ D ⊔ pCoreOf 2 X := by
  classical
  have hDn : (D.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hn
  let π : ↥X →* OTwoQuot X := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)
  have hI : ((D.subgroupOf X).map π).Normal :=
    Subgroup.Normal.map hDn π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf X).map π) with hbot | htop
  · left
    intro d hd
    have hmem : π ⟨d, hDX hd⟩ ∈ (D.subgroupOf X).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hd)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ⟨⟨d, hDX hd⟩, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩
  · right
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ (D.subgroupOf X).map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hmem
    have h1 : a⁻¹ * ⟨x, hx⟩ ∈ CFSG.Open.pCore 2 ↥X := QuotientGroup.eq.mp hax
    have e : x = (a : G) * ((a : G)⁻¹ * x) := by group
    rw [e]
    exact (D ⊔ pCoreOf 2 X).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
      (Subgroup.mem_sup_right ⟨a⁻¹ * ⟨x, hx⟩, h1, by simp⟩)

end Quot

section Core

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_proper_stab {A K₁ K₂ K' C : Subgroup G}
    (hK₁A : K₁ ≤ A) (hK'A : K' ≤ A) (hA : A ≤ K₁ ⊔ K₂)
    (hn₁ : A ≤ Subgroup.normalizer (K₁ : Set G)) (hn₂ : A ≤ Subgroup.normalizer (K₂ : Set G))
    (hCA : C ≤ A) (hK₂C : K₂ ≤ C) (hRC : pCoreOf 2 A ≤ C) (hK'C : K' ≤ C) (hK₁C : ¬ K₁ ≤ C)
    (hs₁ : IsSimpleGroup (OTwoQuot K₁)) (hs' : IsSimpleGroup (OTwoQuot K'))
    (hcard : Nat.card (OTwoQuot K') = Nat.card (OTwoQuot K₁)) (hperf : oTwoUpper K' = K') :
    K' ≤ K₂ := by
  classical
  set R : Subgroup G := pCoreOf 2 A with hR
  set N₀ : Subgroup G := K₂ ⊔ R with hN₀
  have hRA : R ≤ A := pCoreOf_le 2 A
  have hRn : A ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 A
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 A
  have hN₀n : A ≤ Subgroup.normalizer (N₀ : Set G) := fun x hx =>
    mem_normalizer_sup_of_mem_normalizer (hn₂ hx) (hRn hx)
  have hN₀C : N₀ ≤ C := sup_le hK₂C hRC
  have hN₀A : N₀ ≤ A := hN₀C.trans hCA
  have hK₂N₀ : K₂ ≤ N₀ := le_sup_left
  have hRN₀ : R ≤ N₀ := le_sup_right
  have hO₁R : pCoreOf 2 K₁ ≤ R :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₁).trans hK₁A)
      (hn₁.trans (normalizer_le_normalizer_pCoreOf 2 K₁)) (pCoreOf_isPGroup 2 K₁)
  have hn₁₀ : K₁ ≤ Subgroup.normalizer (N₀ : Set G) := fun x hx => hN₀n (hK₁A hx)
  have hK₁N : K₁ ≤ Subgroup.normalizer ((K₁ ⊓ N₀ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hn₁₀ hx⟩
  have h1 : K₁ ⊓ N₀ ≤ pCoreOf 2 K₁ := by
    rcases le_pCoreOf_or_le_sup inf_le_left hK₁N hs₁ with h | h
    · exact h
    · exfalso
      apply hK₁C
      have hle : (K₁ ⊓ N₀) ⊔ pCoreOf 2 K₁ ≤ N₀ := sup_le inf_le_right (hO₁R.trans hRN₀)
      exact fun x hx => hN₀C (hle (h hx))
  have h1' : K₁ ⊓ N₀ = pCoreOf 2 K₁ :=
    le_antisymm h1 (le_inf (pCoreOf_le 2 K₁) (hO₁R.trans hRN₀))
  have hAeq : K₁ ⊔ N₀ = A :=
    le_antisymm (sup_le hK₁A hN₀A) (hA.trans (sup_le_sup_left hK₂N₀ K₁))
  have hidx : N₀.relIndex A = Nat.card (OTwoQuot K₁) := by
    have h := C5.relIndex_inf_eq_of_le_normalizer hn₁₀
    rw [h1', relIndex_pCoreOf, hAeq] at h
    exact h.symm
  have hnpos : 0 < Nat.card (OTwoQuot K₁) := Nat.card_pos
  have hAC : ¬ A ≤ C := fun h => hK₁C (hK₁A.trans h)
  have hCne1 : C.relIndex A ≠ 1 := fun h => hAC (Subgroup.relIndex_eq_one.mp h)
  have hCne0 : C.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite (H := C.subgroupOf A)
  have hmul := Subgroup.relIndex_mul_relIndex N₀ C A hN₀C hCA
  have hlt : N₀.relIndex C < Nat.card (OTwoQuot K₁) := by
    have h2 : 2 ≤ C.relIndex A := by omega
    have h3 : N₀.relIndex C * 2 ≤ N₀.relIndex C * C.relIndex A := Nat.mul_le_mul_left _ h2
    omega
  have hn'₀ : K' ≤ Subgroup.normalizer (N₀ : Set G) := fun x hx => hN₀n (hK'A hx)
  have hK'N : K' ≤ Subgroup.normalizer ((K' ⊓ N₀ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hn'₀ hx⟩
  have hK'N₀ : K' ≤ N₀ := by
    rcases le_pCoreOf_or_le_sup inf_le_left hK'N hs' with h | h
    · exfalso
      have e1 := C5.relIndex_le_of_le_left h K'
      have e2 := C5.relIndex_inf_eq_of_le_normalizer hn'₀
      have e3 : N₀.relIndex (K' ⊔ N₀) ≤ N₀.relIndex C :=
        C5.relIndex_le_of_le le_sup_right (sup_le hK'C hN₀C)
      rw [relIndex_pCoreOf, hcard] at e1
      omega
    · have hO : oTwoUpper K' ≤ K' ⊓ N₀ :=
        Der6A.oTwoUpper_le_of_normal_sup inf_le_left
          ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hK'N)
          (pCoreOf_isPGroup 2 K') (pCoreOf_le 2 K') h
      rw [hperf] at hO
      exact hO.trans inf_le_right
  have hN₀N : K₂ ⊔ R ≤ Subgroup.normalizer (K₂ : Set G) :=
    sup_le Subgroup.le_normalizer (hRA.trans hn₂)
  have hO : oTwoUpper (K₂ ⊔ R) ≤ K₂ :=
    Der6A.oTwoUpper_le_of_normal_sup (H := K₂ ⊔ R) (N := K₂) (S := R) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hN₀N) hR2 le_sup_right
      le_rfl
  calc K' = oTwoUpper K' := hperf.symm
    _ ≤ oTwoUpper (K₂ ⊔ R) := oTwoUpper_mono hK'N₀
    _ ≤ K₂ := hO

end Core

section Conj

variable {G : Type} [Group G]

noncomputable def oTwoQuotConjSub (a : G) (X : Subgroup G) : OTwoQuot X ≃* OTwoQuot (conjSub a X) :=
  QuotientGroup.congr (CFSG.Open.pCore 2 ↥X) (CFSG.Open.pCore 2 ↥(conjSub a X))
    ((MulAut.conj a).subgroupMap X) (map_pCore_mulEquiv 2 _)

theorem nonempty_oTwoQuot_equiv_conjSub {Q : Type*} [Group Q] (a : G) {X : Subgroup G}
    (h : Nonempty (OTwoQuot X ≃* Q)) : Nonempty (OTwoQuot (conjSub a X) ≃* Q) :=
  h.elim fun φ => ⟨(oTwoQuotConjSub a X).symm.trans φ⟩

end Conj

end SBc13

end CFSG.Quasithin
