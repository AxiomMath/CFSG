module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AO2A
import CFSG.Quasithin.Background.E6TwentyTwo
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23ne_cent_le_of_mQuot_le {M V₀ V N₁ N₂ Y : Subgroup G}
    (hP : C23NePair M V₀ V N₁ N₂ Y) {U : Subgroup G} (hm : E3.mQuot V U ≤ 4) :
    centralizer (U : Set G) ≤ M := by
  have hWi := E6.mQuot_inf_left_le (V := V) (U := N₁) (U' := U) hP.elem.isPGroup hP.le₁
  have hWU : E3.mQuot N₁ (N₁ ⊓ U) ≤ 4 := hWi.trans hm
  have hsub := c23a_o2_mQuot_eq_rk_sub (V := N₁) (U := N₁ ⊓ U) inf_le_left
  have hfive : 5 ≤ rk ↥N₁ := by simpa only [mSub] using hP.rank_N₁.ge
  have hge1 : 1 ≤ rk ↥(N₁ ⊓ U) := by omega
  have hne : N₁ ⊓ U ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥(N₁ ⊓ U) = 0 := by rw [hbot]; exact rk_bot
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hwW : (a : G) ∈ N₁ := (Subgroup.mem_inf.1 a.2).1
  have hwU : (a : G) ∈ U := (Subgroup.mem_inf.1 a.2).2
  have hw1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwU)).trans
    (hP.cent (a : G) (Or.inl hwW) hw1)

theorem c23ne_inf_blocks_eq_bot {M V₀ V N₁ N₂ Y : Subgroup G} (hP : C23NePair M V₀ V N₁ N₂ Y)
    {A X : Subgroup G} (hA : ¬ A ≤ M) (hX : ∀ x ∈ X, ∀ a ∈ A, a * x = x * a) :
    X ⊓ N₁ = ⊥ ∧ X ⊓ N₂ = ⊥ := by
  have key : ∀ B : Subgroup G, (∀ w ∈ B, w ≠ 1 → centralizer ({w} : Set G) ≤ M) →
      X ⊓ B = ⊥ := by
    intro B hB
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    by_contra hw1
    obtain ⟨hwX, hwB⟩ := Subgroup.mem_inf.1 hw
    refine hA fun a ha => hB w hwB hw1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (hX w hwX a ha).symm
  exact ⟨key N₁ fun w hw hw1 => hP.cent w (Or.inl hw) hw1,
    key N₂ fun w hw hw1 => hP.cent w (Or.inr hw) hw1⟩

theorem c23ne_comm_mem_inf {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}
    (h : C23NeO2 M V₀ V N₁ N₂ Y g) {u y : G} (hu : u ∈ V ⊓ conjSubgroup M g)
    (hy : y ∈ conjSubgroup V g ⊓ M) : u * y * u⁻¹ * y⁻¹ ∈ V ⊓ conjSubgroup V g := by
  have huV : u ∈ V := (Subgroup.mem_inf.1 hu).1
  have huMg : u ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hu).2
  have hyVg : y ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hy).1
  have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).2
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hyN : y ∈ normalizer (V : Set G) := h.pair.norm hyM
    have hmem : y * u⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hyN u⁻¹).1 (V.inv_mem huV)
    have h2 : u * (y * u⁻¹ * y⁻¹) ∈ V := V.mul_mem huV hmem
    simpa only [mul_assoc] using h2
  · have huN : u ∈ normalizer (conjSubgroup V g : Set G) := h.pair'.norm huMg
    have hmem : u * y * u⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 huN y).1 hyVg
    exact (conjSubgroup V g).mul_mem hmem ((conjSubgroup V g).inv_mem hyVg)

theorem c23ne_mSub_le_three {M V₀ V N₁ N₂ Y : Subgroup G} (hP : C23NePair M V₀ V N₁ N₂ Y)
    {X : Subgroup G} (hXV : X ≤ V) (hX : X ⊓ N₁ = ⊥) : mSub X ≤ 3 := by
  have h1 := E6.mQuot_inf_left_le (V := V) (U := X) (U' := N₁) hP.elem.isPGroup hXV
  have h2 : E3.mQuot V N₁ = rk ↥V - rk ↥N₁ := c23a_o2_mQuot_eq_rk_sub hP.le₁
  have h3 : E3.mQuot X (X ⊓ N₁) = rk ↥X - rk ↥(X ⊓ N₁) :=
    c23a_o2_mQuot_eq_rk_sub inf_le_left
  have h4 : rk ↥(X ⊓ N₁) = 0 := by rw [hX]; exact rk_bot
  have h5 : rk ↥V = 8 := by simpa only [mSub] using hP.rank_V
  have h6 : rk ↥N₁ = 5 := by simpa only [mSub] using hP.rank_N₁
  simp only [mSub]
  omega

theorem c23ne_relIndex_le_card_of_orbit {U E : Subgroup G} {w : G}
    (hw : ∀ u ∈ U, u * w * u⁻¹ * w⁻¹ ∈ E) :
    (centralizer ({w} : Set G)).relIndex U ≤ Nat.card E := by
  classical
  let C : Subgroup G := centralizer ({w} : Set G)
  let φ : ↥U → ↥E := fun u => ⟨u.1 * w * u.1⁻¹ * w⁻¹, hw u.1 u.2⟩
  have hφ : ∀ a b : ↥U, QuotientGroup.leftRel (C.subgroupOf U) a b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    apply Subtype.ext
    have hv : a.1 * w * a.1⁻¹ = b.1 * w * b.1⁻¹ := by
      have hc : a.1⁻¹ * b.1 * w = w * (a.1⁻¹ * b.1) := by
        simpa using Subgroup.mem_centralizer_singleton_iff.mp hab
      have key : b.1 * w * b.1⁻¹ = a.1 * w * a.1⁻¹ := by
        calc b.1 * w * b.1⁻¹
            = a.1 * (a.1⁻¹ * b.1 * w) * b.1⁻¹ := by group
          _ = a.1 * (w * (a.1⁻¹ * b.1)) * b.1⁻¹ := by rw [hc]
          _ = a.1 * w * a.1⁻¹ := by group
      exact key.symm
    show a.1 * w * a.1⁻¹ * w⁻¹ = b.1 * w * b.1⁻¹ * w⁻¹
    rw [hv]
  let ψ : ↥U ⧸ (C.subgroupOf U) → ↥E := Quotient.lift φ hφ
  have hψ : Function.Injective ψ := by
    intro q q' hq
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective q'
    change φ a = φ b at hq
    apply Quotient.sound
    show QuotientGroup.leftRel (C.subgroupOf U) a b
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hv : a.1 * w * a.1⁻¹ = b.1 * w * b.1⁻¹ :=
      mul_right_cancel (Subtype.ext_iff.mp hq)
    have hc : b.1⁻¹ * a.1 ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcv : (b.1⁻¹ * a.1) * w * (b.1⁻¹ * a.1)⁻¹ = w := by
        have h := congrArg (fun x => b.1⁻¹ * x * b.1) hv
        have h1 : b.1⁻¹ * (a.1 * w * a.1⁻¹) * b.1 =
            (b.1⁻¹ * a.1) * w * (b.1⁻¹ * a.1)⁻¹ := by group
        have h2 : b.1⁻¹ * (b.1 * w * b.1⁻¹) * b.1 = w := by group
        rwa [h1, h2] at h
      calc (b.1⁻¹ * a.1) * w
          = ((b.1⁻¹ * a.1) * w * (b.1⁻¹ * a.1)⁻¹) * (b.1⁻¹ * a.1) := by group
        _ = w * (b.1⁻¹ * a.1) := by rw [hcv]
    have h : a.1⁻¹ * b.1 = (b.1⁻¹ * a.1)⁻¹ := by group
    change a.1⁻¹ * b.1 ∈ C
    rw [h]
    exact C.inv_mem hc
  show (C.subgroupOf U).index ≤ Nat.card E
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective ψ hψ

theorem c23ne_mQuot_le_two_of_orbit {U E : Subgroup G} {w : G} (hU : IsPGroup 2 U)
    (hE : Nat.card E ≤ 4) (hw : ∀ u ∈ U, u * w * u⁻¹ * w⁻¹ ∈ E) :
    E3.mQuot U (centralizer ({w} : Set G)) ≤ 2 := by
  have h1 := c23ne_relIndex_le_card_of_orbit hw
  rw [E3.relIndex_eq_two_pow hU] at h1
  have h2 : 2 ^ E3.mQuot U (centralizer ({w} : Set G)) ≤ 2 ^ 2 := by
    simpa using h1.trans hE
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem c23ne_exists_two_ne_one {A : Subgroup G} (h : 3 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hAn : Nat.card ↥A = (A : Set G).ncard := (Nat.card_coe_set_eq (A : Set G)).symm
  by_cases hex : ∃ a ∈ A, a ≠ 1
  · obtain ⟨a₀, ha₀, ha₁⟩ := hex
    have hsub : (A : Set G) ⊆ insert 1 {a₀} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx a₀ ha₀ hx1 ha₁)
    have hcard : (A : Set G).ncard ≤ 2 := by
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_insert_le (1 : G) ({a₀} : Set G)
      rw [Set.ncard_singleton] at h2
      omega
    omega
  · push_neg at hex
    have hsub : (A : Set G) ⊆ {1} := fun x hx => hex x hx
    have hcard : (A : Set G).ncard ≤ 1 := by
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_singleton] at h1
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
