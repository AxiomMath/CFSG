module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44d
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem K_le_L (h : FF84Sec4 b L B K b₁ b₂) : K ≤ L :=
  (h.hK.2.2.1 ▸ (le_sup_right : K ≤ Subgroup.zpowers b₁ ⊔ K) : K ≤ L ⊓ Cen b₁).trans inf_le_left

theorem K_le_cen_b₁ (h : FF84Sec4 b L B K b₁ b₂) : K ≤ Cen b₁ := h.hK.2.2.2.2

theorem K_le_cen_bb₁ (h : FF84Sec4 b L B K b₁ b₂) : K ≤ Cen (b * b₁) := by
  intro k hk
  have e1 : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.1
    (h.hyp.hLC (K_le_L h hk))
  have e2 : k * b₁ = b₁ * k := Subgroup.mem_centralizer_singleton_iff.1 (K_le_cen_b₁ h hk)
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc k * (b * b₁) = (k * b) * b₁ := by rw [mul_assoc]
    _ = (b * k) * b₁ := by rw [e1]
    _ = b * (k * b₁) := by rw [mul_assoc]
    _ = b * (b₁ * k) := by rw [e2]
    _ = (b * b₁) * k := by rw [mul_assoc]

theorem Z_K_sq (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) :
    ∀ z ∈ Subgroup.center ↥K, ((z : K) : G) ^ 2 = 1 := by
  obtain ⟨θ, hker, -, hsurj, hb₁θ, -⟩ := theta_model hA h
  obtain ⟨-, hKmod, hKsup, hKb₁K, hKcen⟩ := h.hK
  have hKle : K ≤ L ⊓ Cen b₁ := hKsup ▸ le_sup_right
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  let f : ↥L →* Perm (Fin 8) :=
    θ.comp (Subgroup.inclusion (fun x hx => Subgroup.le_normalizer hx))
  have hfker : ∀ x : ↥L, f x = 1 → (x : G) ∈ CenS L := fun x hx =>
    (hker ⟨x, Subgroup.le_normalizer x.2⟩).1 hx
  have hfb₁ : f ⟨b₁, hb₁L⟩ = a8c := hb₁θ
  have hlift : ∀ g₀ : Perm (Fin 8), sign g₀ = 1 → g₀ * a8c = a8c * g₀ →
      ∃ x : ↥L, f x = g₀ ∧ (x : G) ∈ Cen b₁ := by
    intro g₀ hg₀ hcomm
    obtain ⟨x, hx⟩ := hsurj g₀ (mem_alternatingGroup.2 hg₀)
    refine ⟨x, hx, ?_⟩
    have hc : f (x * ⟨b₁, hb₁L⟩ * x⁻¹ * ⟨b₁, hb₁L⟩⁻¹) = 1 := by
      have hx' : f x = g₀ := hx
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx', hfb₁]
      rw [hcomm]
      group
    set u : G := (x : G) * b₁ * (x : G)⁻¹ * b₁⁻¹ with hu
    have huc : u ∈ CenS L := hfker _ hc
    have huL : u ∈ L := mul_mem (mul_mem (mul_mem x.2 hb₁L) (inv_mem x.2)) (inv_mem hb₁L)
    have hu2 := Z_sq hA u huL huc
    have hub : u * b₁ = b₁ * u := (Subgroup.mem_centralizer_iff.1 huc b₁ hb₁L).symm
    have hu3 : u ^ 3 = 1 := by
      have hconj : ((x : G) * b₁ * (x : G)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hb3]; group
      have e1 : (x : G) * b₁ * (x : G)⁻¹ = u * b₁ := by rw [hu]; group
      rw [e1, (show Commute u b₁ from hub).mul_pow, hb3, mul_one] at hconj
      exact hconj
    have hu1 : u = 1 := by
      calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
        _ = 1 := by rw [hu3, hu2]; group
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc (x : G) * b₁ = ((x : G) * b₁ * (x : G)⁻¹ * b₁⁻¹) * (b₁ * x) := by group
      _ = b₁ * x := by rw [← hu, hu1, one_mul]
  intro z hz
  set zG : G := (z : G) with hzG
  have hzL : zG ∈ L := hKL z.2
  have hsub : L ⊓ Cen b₁ ≤ Subgroup.centralizer ({zG} : Set G) := by
    rw [← hKsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1
        (hKcen z.2)).symm
    · intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩))
  have hzcomm : ∀ x : ↥L, (x : G) ∈ Cen b₁ → x * ⟨zG, hzL⟩ = ⟨zG, hzL⟩ * x := by
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsub (Subgroup.mem_inf.2 ⟨x.2, hx⟩))
  have hfz : ∀ g₀ : Perm (Fin 8), (∃ x : ↥L, f x = g₀ ∧ (x : G) ∈ Cen b₁) →
      f ⟨zG, hzL⟩ * g₀ = g₀ * f ⟨zG, hzL⟩ := by
    rintro g₀ ⟨x, hx, hxc⟩
    rw [← hx, ← map_mul, ← map_mul, hzcomm x hxc |>.symm]
  have hb₁c : (⟨b₁, hb₁L⟩ : ↥L).1 ∈ Cen b₁ := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have h1 := hfz a8c ⟨⟨b₁, hb₁L⟩, hfb₁, hb₁c⟩
  have h2 := hfz a8d (hlift a8d a8d_sign (by
    unfold a8c a8d
    decide +kernel))
  have h3 := hfz (swap 4 5 * swap 5 6) (hlift _ sign_c456 (by decide +kernel))
  have h4 := hfz (swap 5 6 * swap 6 7) (hlift _ sign_c567 (by decide +kernel))
  have e4 : (b₁ ^ 2) ^ 2 = b₁ := by
    rw [← pow_mul]
    show b₁ ^ 4 = b₁
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hb3, one_mul]
  have hb₁K : ∀ w : G, w ∈ K → w = b₁ ^ 2 ∨ w = (b₁ ^ 2)⁻¹ → False := by
    intro w hw hwe
    have hb : b₁ ∈ K := by
      rcases hwe with rfl | rfl
      · rw [← e4]; exact pow_mem hw 2
      · have : b₁ ^ 2 ∈ K := by simpa using inv_mem hw
        rw [← e4]; exact pow_mem this 2
    have hb' : b₁ ∈ Subgroup.zpowers b₁ ⊓ K := Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers b₁, hb⟩
    rw [hKb₁K, Subgroup.mem_bot] at hb'
    exact b₁_ne_one h hb'
  rcases cen_a8c (f ⟨zG, hzL⟩) h1.symm.symm h2.symm.symm h3.symm.symm h4.symm.symm with
    hz1 | hz1 | hz1
  · exact Z_sq hA zG hzL (hfker _ hz1)
  · exfalso
    have hc : f (⟨zG, hzL⟩ * ⟨b₁, hb₁L⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hz1, hfb₁]; group
    set u : G := zG * b₁⁻¹ with hu
    have huc : u ∈ CenS L := hfker _ hc
    have huL : u ∈ L := mul_mem hzL (inv_mem hb₁L)
    have hu2 := Z_sq hA u huL huc
    have hub : u * b₁ = b₁ * u := (Subgroup.mem_centralizer_iff.1 huc b₁ hb₁L).symm
    have hz2 : zG ^ 2 = b₁ ^ 2 := by
      have e : zG = u * b₁ := by rw [hu]; group
      rw [e, (show Commute u b₁ from hub).mul_pow, hu2, one_mul]
    exact hb₁K (zG ^ 2) (pow_mem z.2 2) (Or.inl hz2)
  · exfalso
    have hc : f (⟨zG, hzL⟩ * ⟨b₁, hb₁L⟩) = 1 := by
      rw [map_mul, hz1, hfb₁]; group
    set u : G := zG * b₁ with hu
    have huc : u ∈ CenS L := hfker _ hc
    have huL : u ∈ L := mul_mem hzL hb₁L
    have hu2 := Z_sq hA u huL huc
    have hub : u * b₁⁻¹ = b₁⁻¹ * u := (Subgroup.mem_centralizer_iff.1 huc b₁⁻¹ (inv_mem hb₁L)).symm
    have hz2 : zG ^ 2 = (b₁ ^ 2)⁻¹ := by
      have e : zG = u * b₁⁻¹ := by rw [hu]; group
      rw [e, (show Commute u b₁⁻¹ from hub).mul_pow, hu2, one_mul]
      group
    exact hb₁K (zG ^ 2) (pow_mem z.2 2) (Or.inr hz2)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
