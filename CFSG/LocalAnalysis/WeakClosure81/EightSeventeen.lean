module

public import CFSG.LocalAnalysis.WeakClosure81.EightSeventeenAut
public import CFSG.LocalAnalysis.WeakClosure81.EightNVDerived
public import CFSG.LocalAnalysis.WeakClosure81.EightSeventeenCent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Sit

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.oTwoMod_eq_inf_centralizer_uGrp (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G)) :
    oTwoMod (cGrp H T) K = K ⊓ centralizer (uGrp V K : Set G) := by
  have hle : oTwoMod (cGrp H T) K ≤ K ⊓ centralizer (uGrp V K : Set G) :=
    le_inf oTwoMod_le_self (h.oTwoMod_le_centralizer_uGrp hNV)
  have hBK : K ⊓ centralizer (uGrp V K : Set G) ≤ K := inf_le_left
  have key : ∀ k ∈ K, ∀ b ∈ K ⊓ centralizer (uGrp V K : Set G),
      k * b * k⁻¹ ∈ K ⊓ centralizer (uGrp V K : Set G) := by
    intro k hk b hb
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk (Subgroup.mem_inf.mp hb).1) (K.inv_mem hk),
      ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : k⁻¹ * u * k ∈ uGrp V K := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V K (K.inv_mem hk)) u).mp
        hu
      simpa [uGrp] using this
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 _ hu'
    calc u * (k * b * k⁻¹) = k * ((k⁻¹ * u * k) * b) * k⁻¹ := by group
      _ = k * (b * (k⁻¹ * u * k)) * k⁻¹ := by rw [hc]
      _ = (k * b * k⁻¹) * u := by group
  have hBnorm : ((K ⊓ centralizer (uGrp V K : Set G)).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro b
    exact ⟨key k hk b, fun hb => by simpa [mul_assoc] using key k⁻¹ (K.inv_mem hk) _ hb⟩
  rcases h.kn1 _ hle hBK hBnorm with h1 | h1
  · exact h1.symm
  · exfalso
    have hKU : K ≤ centralizer (uGrp V K : Set G) := by
      intro k hk
      have : k ∈ K ⊓ centralizer (uGrp V K : Set G) := by rw [h1]; exact hk
      exact (Subgroup.mem_inf.mp this).2
    have hV1 : ∀ v ∈ V, v = 1 := fun v hv => h.eq_one_of_centralizes_K hv fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hKU hk) v (Sit813.V_le_uGrp hv)).symm
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hV1
    have h8 := h.card_V_eq_eight
    rw [hbot, Subgroup.card_bot] at h8
    omega

theorem Sit813.not_le_oTwoMod_of_isSylowIn (h : Sit813 V H T i A L K) {X : Subgroup G}
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G))) : ¬ X ≤ oTwoMod (cGrp H T) K := by
  intro hXN
  have hNP : oTwoMod (cGrp H T) K ≤ K ⊓ normalizer (V : Set G) := h.oTwoMod_le_inf
  have h1 : (oTwoMod (cGrp H T) K).relIndex (K ⊓ normalizer (V : Set G)) *
      (K ⊓ normalizer (V : Set G)).relIndex K = (oTwoMod (cGrp H T) K).relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ hNP inf_le_left
  rw [h.kn4, h.concl813.d_index] at h1
  have h12 : (oTwoMod (cGrp H T) K).relIndex (K ⊓ normalizer (V : Set G)) = 12 := by omega
  have h2 : X.relIndex (oTwoMod (cGrp H T) K) *
      (oTwoMod (cGrp H T) K).relIndex (K ⊓ normalizer (V : Set G)) =
      X.relIndex (K ⊓ normalizer (V : Set G)) := Subgroup.relIndex_mul_relIndex _ _ _ hXN hNP
  rw [h12] at h2
  exact hX.not_dvd_relIndex ⟨X.relIndex (oTwoMod (cGrp H T) K) * 4, by omega⟩

theorem Sit813.exists_section_card_mulAut (h : Sit813 V H T i A L K) :
    ∃ (Q : Type) (_ : Group Q) (φ : ↥K →* Q), Function.Surjective φ ∧
      (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoMod (cGrp H T) K) ∧ Nat.card (MulAut Q) = 120 := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hX⟩ := h.concl813.c_shape
  letI : Group X := hXgrp
  obtain ⟨e⟩ := CFSG.Quasithin.nonempty_equiv_alt5_of_isPSL_two_two_two (isL2_iff_isPSL.mp hX)
  refine ⟨X, hXgrp, φ, hφ, hker, ?_⟩
  rw [← CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five]
  exact Nat.card_congr (MulAut.congr e).toEquiv

theorem Sit813.eight_seventeen {X Y : Subgroup G} (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G))
    (hnat : IsNaturalSL2Module K (u1Grp V H T A K) (u1Grp V H T A K ⊓ centralizer (K : Set G)))
    (h4 : Nat.card (v1Grp V H T A K) = 4)
    (hKV : ∀ x ∈ V, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ u1Grp V H T A K)
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G)))
    (hY : IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G))) (hXY : X ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G)) :
    Y ≤ centralizer ((uGrp V K ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := by
  have hYV : Y ≤ normalizer (V : Set G) := hY.le.trans inf_le_right
  have hY3 : IsPGroup 3 ↥Y := hY.isPGroup
  have hXK : X ≤ K := hX.le.trans inf_le_left
  have hN := h.oTwoMod_eq_inf_centralizer_uGrp hNV
  have hYU : ∀ y ∈ Y, y ∈ normalizer (uGrp V K : Set G) := fun y hy =>
    mem_normalizer_conjClosure_of_mem_normalizers (hYV hy) (hYK hy)
  have key : ∀ y ∈ Y, ∀ n ∈ oTwoMod (cGrp H T) K, y * n * y⁻¹ ∈ oTwoMod (cGrp H T) K := by
    intro y hy n hn
    rw [hN] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hYK hy) n).mp
      (Subgroup.mem_inf.mp hn).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : y⁻¹ * u * y ∈ uGrp V K := by
      have := (Subgroup.mem_normalizer_iff.mp (hYU y⁻¹ (Y.inv_mem hy)) u).mp hu
      simpa [uGrp] using this
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 _ hu'
    calc u * (y * n * y⁻¹) = y * ((y⁻¹ * u * y) * n) * y⁻¹ := by group
      _ = y * (n * (y⁻¹ * u * y)) * y⁻¹ := by rw [hc]
      _ = (y * n * y⁻¹) * u := by group
  have hYN : Y ≤ normalizer (oTwoMod (cGrp H T) K : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    exact fun n => ⟨key y hy n, fun hn => by simpa [mul_assoc] using key y⁻¹ (Y.inv_mem hy) _ hn⟩
  obtain ⟨Q, hQgrp, φ, hφ, hker, hQ⟩ := h.exists_section_card_mulAut
  letI : Group Q := hQgrp
  have hXN : ¬ X ≤ oTwoMod (cGrp H T) K := h.not_le_oTwoMod_of_isSylowIn hX
  have hdec := exists_mul_trivial_on_section_of_card_mulAut φ hφ hker hQ h.kn3 hYK hYN hY3 hXY
    hXK hXN
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨x, hxX, hx⟩ := hdec y hy
  have hcY : x⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hXY hxX)) hy
  have hc3 : IsPGroup 3 ↥(Subgroup.zpowers (x⁻¹ * y)) :=
    hY3.to_le (Subgroup.zpowers_le.mpr hcY)
  have hcU : x⁻¹ * y ∈ centralizer (uGrp V K : Set G) :=
    h.mem_centralizer_uGrp_of_comm_mem_oTwoMod hNV hnat h4 hKV hc3 (hYV hcY) (hYK hcY) hx
  have h1 : z * (x⁻¹ * y) = (x⁻¹ * y) * z :=
    Subgroup.mem_centralizer_iff.mp hcU z (Subgroup.mem_inf.mp hz).1
  have h2 : x * z = z * x :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x (hXK hxX)
  calc z * y = (z * x) * (x⁻¹ * y) := by group
    _ = (x * z) * (x⁻¹ * y) := by rw [← h2]
    _ = x * (z * (x⁻¹ * y)) := by group
    _ = x * ((x⁻¹ * y) * z) := by rw [h1]
    _ = y * z := by group

theorem Sit813.eight_seventeen_of_in (hin : W3In814 G) {X Y : Subgroup G}
    (h : Sit813 V H T i A L K) (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G)))
    (hY : IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G))) (hXY : X ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G)) :
    Y ≤ centralizer ((uGrp V K ⊓ centralizer (K : Set G) : Subgroup G) : Set G) :=
  h.eight_seventeen (h.oTwoMod_le_centralizer_V hin) (h.eight_fourteen hin).1
    (h.eight_fourteen hin).2.2
    (h.comm_K_V_mem_u1Grp hin) hX hY hXY hYK

end Sit

end CFSG.LocalAnalysis.WeakClosure81

end
