module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Quot

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G] [Finite G] {X S Z Z₀ : Subgroup G}

@[expose] def pu4X1 (θ : ↥X →* Perm (Fin 5)) : Subgroup G :=
  ((Subgroup.centralizer ({swap 0 2} : Set (Perm (Fin 5)))).comap θ).map X.subtype

omit [Finite G] in
theorem mem_pu4X1 {θ : ↥X →* Perm (Fin 5)} {x : G} :
    x ∈ pu4X1 θ ↔ ∃ hx : x ∈ X, θ ⟨x, hx⟩ * swap 0 2 = swap 0 2 * θ ⟨x, hx⟩ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mp hy⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr hc, rfl⟩

omit [Finite G] in
theorem pu4X1_le {θ : ↥X →* Perm (Fin 5)} : pu4X1 θ ≤ X := fun _ hx => (mem_pu4X1.mp hx).1

theorem pResidualOf_mono {Y X : Subgroup G} (hYX : Y ≤ X) :
    pResidualOf 2 Y ≤ pResidualOf 2 X := by
  rw [← oTwoUpper_eq_pResidualOf, ← oTwoUpper_eq_pResidualOf]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X (hYX hx)
  exact ⟨k, hk⟩

theorem theta_residual_mem {θ : ↥X →* Perm (Fin 5)} {l : G} (hl : l ∈ pResidualOf 2 (pu4X1 θ)) :
    ∃ hlX : l ∈ X, θ ⟨l, hlX⟩ ∈ pu4A3 := by
  rw [← oTwoUpper_eq_pResidualOf] at hl
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxX, hc⟩ := mem_pu4X1.mp hx.1
    refine ⟨hxX, mem_pu4A3_of_odd hc hx.2 ?_⟩
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ orderOf x = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  | one =>
    exact ⟨X.one_mem, by
      have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
      rw [this, map_one]; exact one_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hxX, hx⟩ := hx
    obtain ⟨hyX, hy⟩ := hy
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    have : (⟨x * y, X.mul_mem hxX hyX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨y, hyX⟩ := rfl
    rw [this, map_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    obtain ⟨hxX, hx⟩ := hx
    refine ⟨X.inv_mem hxX, ?_⟩
    have : (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X) = (⟨x, hxX⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem hx

theorem pu4_orthogonal_detail (h : PushHyp X S Z) (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hZ₀ : Z₀ ≤ Z) (hO : IsOrthSec X Z₀ Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ∃ θ : ↥X →* Perm (Fin 5), Function.Surjective θ ∧
      (∀ (x : G) (hx : x ∈ X), θ ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X) ∧
      (S.subgroupOf X).map θ = S5Syl ∧ ((baum S).subgroupOf X).map θ = S5That ∧
      pResidualOf 2 (pu4X1 θ) ⊔ baum S ≤ X ∧
      IsSylowTwoOf (baum S) (pResidualOf 2 (pu4X1 θ) ⊔ baum S) ∧
      Nonempty (OTwoQuot (pResidualOf 2 (pu4X1 θ) ⊔ baum S) ≃* Perm (Fin 3)) ∧
      (pResidualOf 2 (pu4X1 θ) ⊔ baum S) ⊔ S = X := by
  obtain ⟨θ, hF⟩ := exists_orthFacts h hq hZ₀ hO
  have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A :=
    fun A hA hAQ => (offender_image h hF hA hAQ).2.2.1
  obtain ⟨-, hF4⟩ := centralizer_thompsonJ h hF hJ
  obtain ⟨-, hFW, hRcent⟩ := pu4_core h hJ hall hF4.le (exists_generated h hF hJ)
    (hF.relIndex_Z0.ge.trans (relIndex_le_of_le Z (centralizer_residual_le hF hZ₀)))
  set Q := pCoreOf 2 X with hQ
  set J := thompsonJ S with hJdef
  set W := omegaOneCenterOf J with hW
  set B := baum S with hB
  set X₁ := pu4X1 θ with hX₁
  set L' := pResidualOf 2 X₁ with hL'
  have hSX : S ≤ X := h.le_self
  have hQS : Q ≤ S := h.core_le
  have hQX : Q ≤ X := hQS.trans hSX
  have hBS : B ≤ S := inf_le_left
  have hBX : B ≤ X := hBS.trans hSX
  have hJS : J ≤ S := thompsonJ_le_self S
  have hJX : J ≤ X := hJS.trans hSX
  have hX₁X : X₁ ≤ X := pu4X1_le
  have hL'X₁ : L' ≤ X₁ := pResidualOf_le_self X₁
  have hL'X : L' ≤ X := hL'X₁.trans hX₁X
  have hJB : J ≤ B := by
    intro j hj
    refine ⟨hJS hj, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (omegaOneCenterOf_le_inf J hw).2 j hj)).symm
  have hθB : ∀ (s : G) (hs : s ∈ B), θ ⟨s, hBX hs⟩ ∈ S5That := fun s hs =>
    baum_image_le h hF hJ hFW (hBX hs) hs
  have hThatC : ∀ σ ∈ S5That, σ * swap 0 2 = swap 0 2 * σ := by
    intro σ hσ
    rw [mem_S5That_iff] at hσ
    revert σ; unfold S5ThatF; decide +kernel
  have hBX₁ : B ≤ X₁ := fun s hs =>
    mem_pu4X1.mpr ⟨hBX hs, hThatC _ (hθB s hs)⟩
  have hL'L : L' ≤ pResidualOf 2 X := pResidualOf_mono hX₁X
  have hL'Q_B : L' ⊓ Q ≤ B := by
    intro r hr
    refine ⟨hQS hr.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (hRcent r ⟨hL'L hr.1, hr.2⟩ w hw).symm
  have hL'B_Q : L' ⊓ B ≤ Q := by
    intro l hl
    obtain ⟨hlX, hlA⟩ := theta_residual_mem hl.1
    have h1 : θ ⟨l, hlX⟩ = 1 :=
      pu4A3_inf_That _ hlA (hθB l hl.2)
    exact (hF.ker l hlX).mp h1
  have hL'B : L' ⊓ B = L' ⊓ Q :=
    le_antisymm (fun x hx => ⟨hx.1, hL'B_Q hx⟩) (fun x hx => ⟨hx.1, hL'Q_B hx⟩)
  have hBn : B ≤ Subgroup.normalizer (L' : Set G) := hBX₁.trans (le_normalizer_pResidualOf X₁)
  have hsyl : IsSylowTwoOf B (L' ⊔ B) := by
    refine ⟨le_sup_right, h.sylow.2.1.to_le hBS, ?_⟩
    show ¬ 2 ∣ B.relIndex (L' ⊔ B)
    rw [relIndex_sup_eq_relIndex_inf hBn, hL'B, ← hF.card_map hL'X]
    have hle : (L'.subgroupOf X).map θ ≤ pu4A3 := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hl, hA⟩ := theta_residual_mem (Subgroup.mem_subgroupOf.mp hy)
      exact hA
    have hdvd : Nat.card ((L'.subgroupOf X).map θ) ∣ 3 := by
      rw [← card_pu4A3]; exact Subgroup.card_dvd_of_le hle
    intro h2
    have := h2.trans hdvd
    omega
  have hc : ∃ (u : G) (hu : u ∈ L' ⊔ B), θ ⟨u, (sup_le hL'X hBX) hu⟩ = pu4C := by
    obtain ⟨x, hx⟩ := hF.surj pu4C
    have hxX₁ : (x : G) ∈ X₁ := mem_pu4X1.mpr ⟨x.2, by
      rw [show (⟨(x : G), x.2⟩ : ↥X) = x from rfl, hx]
      unfold pu4C; decide +kernel⟩
    obtain ⟨l, hl, hlX, hθl⟩ := exists_mem_residual_of_odd hX₁X θ hxX₁ (σ := pu4C) hx
      (m := 3) (by decide) pu4C_pow_three
    exact ⟨l, Subgroup.mem_sup_left hl, hθl⟩
  have h02 : swap (0 : Fin 5) 2 ∈ S5That := by
    rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel
  have h13 : swap (1 : Fin 5) 3 ∈ S5That := by
    rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel
  have ht02 : ∃ (u : G) (hu : u ∈ L' ⊔ B), θ ⟨u, (sup_le hL'X hBX) hu⟩ = swap 0 2 := by
    obtain ⟨j, hj, hjJ, hjθ⟩ := exists_mem_thompsonJ h hF hJ h02
    exact ⟨j, Subgroup.mem_sup_right (hJB hjJ), hjθ⟩
  have ht13 : ∃ (u : G) (hu : u ∈ L' ⊔ B), θ ⟨u, (sup_le hL'X hBX) hu⟩ = swap 1 3 := by
    obtain ⟨j, hj, hjJ, hjθ⟩ := exists_mem_thompsonJ h hF hJ h13
    exact ⟨j, Subgroup.mem_sup_right (hJB hjJ), hjθ⟩
  have hBimg : (B.subgroupOf X).map θ = S5That := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hθB y.1 (Subgroup.mem_subgroupOf.mp hy)
    · rw [← image_thompsonJ h hF hJ]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hJB (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨θ, hF.surj, hF.ker, hF.map_S, hBimg, sup_le hL'X hBX, hsyl, ?_, ?_⟩
  · refine oTwoQuot_equiv_perm3 (sup_le hL'X hBX) θ ?_ ?_ hc ht13
    · intro x hx hθx
      have hxS : x ∈ S := hQS ((hF.ker x hx).mp hθx)
      obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨x, hxS⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro u hu
      exact (mem_pu4X1.mp (sup_le hL'X₁ hBX₁ hu)).2
  ·
    apply le_antisymm (sup_le (sup_le hL'X hBX) hSX)
    set H : Subgroup (Perm (Fin 5)) := (((L' ⊔ B) ⊔ S).subgroupOf X).map θ with hH
    have hmemH : ∀ (u : G) (hu : u ∈ (L' ⊔ B)) (σ : Perm (Fin 5)),
        θ ⟨u, (sup_le hL'X hBX) hu⟩ = σ → σ ∈ H := by
      intro u hu σ hσ
      exact ⟨⟨u, (sup_le hL'X hBX) hu⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hu), hσ⟩
    have hD : S5Syl ≤ H := by
      rw [← hF.map_S]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
    have htop : H = ⊤ := by
      obtain ⟨u1, hu1, hθ1⟩ := ht02
      obtain ⟨u2, hu2, hθ2⟩ := ht13
      obtain ⟨u3, hu3, hθ3⟩ := hc
      exact top_of_C_and_D H (hmemH _ hu1 _ hθ1) (hmemH _ hu2 _ hθ2) (hmemH _ hu3 _ hθ3) hD
    intro x hx
    have hxH : θ ⟨x, hx⟩ ∈ H := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hxH
    have hyU : (y : G) ∈ (L' ⊔ B) ⊔ S := Subgroup.mem_subgroupOf.mp hy
    have hq : (y : G)⁻¹ * x ∈ Q := by
      have hyx' : (y : G)⁻¹ * x ∈ X := X.mul_mem (X.inv_mem y.2) hx
      rw [← hF.ker _ hyx']
      have : (⟨(y : G)⁻¹ * x, hyx'⟩ : ↥X) = y⁻¹ * ⟨x, hx⟩ := rfl
      rw [this, map_mul, map_inv, hyx, inv_mul_cancel]
    have : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ hyU (Subgroup.mem_sup_right (hQS hq))

theorem pu4_orthogonal (h : PushHyp X S Z) (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hZ₀ : Z₀ ≤ Z) (hO : IsOrthSec X Z₀ Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ∃ U : Subgroup G, U ≤ X ∧ IsSylowTwoOf (baum S) U ∧
      Nonempty (OTwoQuot U ≃* Perm (Fin 3)) ∧ U ⊔ S = X := by
  obtain ⟨θ, -, -, -, -, hUX, hsyl, hquot, hUS⟩ := pu4_orthogonal_detail h hq hZ₀ hO hJ
  exact ⟨_, hUX, hsyl, hquot, hUS⟩

end CFSG.Quasithin.F53Push
