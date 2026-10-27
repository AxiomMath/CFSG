module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.CentralExtension

open Pointwise Subgroup

variable {E S : Type*} [Group E] [Group S]

theorem mem_doubleCoset_mul_of_stable {B N : Subgroup E} {D : Set E}
    (hD : D = {g | ∃ b₁ ∈ B, ∃ n ∈ N, ∃ b₂ ∈ B, g = b₁ * n * b₂}) {g b : E} (hg : g ∈ D)
    (hb : b ∈ B) : g * b ∈ D := by
  subst hD
  obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, rfl⟩ := hg
  exact ⟨b₁, hb₁, n, hn, b₂ * b, B.mul_mem hb₂ hb, by group⟩

theorem central_extension_faithful_bruhat_lift_splitting (π : E →* S)
    (hC : π.ker ≤ center E) {U H N B : Subgroup E} (hB : (B : Set E) = (U : Set E) * H)
    (hBinj : Set.InjOn π B) (hHN : (H.subgroupOf N).Normal) {ι : Type*} (s : ι → E)
    (hN : N = closure ((H : Set E) ∪ Set.range s)) (hs : ∀ i, s i ^ 2 ∈ H)
    (Xp Xm Ui : ι → Subgroup E) (hXp : ∀ i, Xp i ≤ U)
    (hfact : ∀ i, (B : Set E) = (Xp i : Set E) * (Ui i : Set E) * H)
    (hconj : ∀ i, ∀ u ∈ Ui i, (s i)⁻¹ * u * s i ∈ U)
    (hrew : ∀ i, ∀ x ∈ Xp i, x ≠ 1 → x * s i ∈ (Xm i : Set E) * H * (Xp i : Set E))
    (hsign : ∀ n ∈ N, ∀ i, (∀ x ∈ Xp i, n * x * n⁻¹ ∈ U) ∨ (∀ y ∈ Xm i, n * y * n⁻¹ ∈ U))
    (hBN : ∀ n ∈ N, π n ∈ B.map π → n ∈ H) (hS : B.map π ⊔ N.map π = ⊤) :
    Function.Bijective (π.domRestrict (B ⊔ N)) ∧
      (∃ e : π.ker × (B ⊔ N : Subgroup E) ≃* E, ∀ c g, e (c, g) = (c : E) * g) ∧
      ∃ σ : S →* E, π.comp σ = MonoidHom.id S := by
  have hUB : U ≤ B := fun u hu => by
    rw [← SetLike.mem_coe, hB]
    exact ⟨u, hu, 1, H.one_mem, mul_one u⟩
  have hHB : H ≤ B := fun h hh => by
    rw [← SetLike.mem_coe, hB]
    exact ⟨1, U.one_mem, h, hh, one_mul h⟩
  have hsN : ∀ i, s i ∈ N := fun i => hN ▸ subset_closure (Or.inr ⟨i, rfl⟩)
  have hHle : H ≤ N := fun h hh => hN ▸ subset_closure (Or.inl hh)
  have hconjH : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H := fun n hn h hh =>
    (normal_subgroupOf_iff hHle).1 hHN h n hh hn
  set D : Set E := {g | ∃ b₁ ∈ B, ∃ n ∈ N, ∃ b₂ ∈ B, g = b₁ * n * b₂} with hD
  have hD1 : (1 : E) ∈ D := ⟨1, B.one_mem, 1, N.one_mem, 1, B.one_mem, by group⟩
  have hDB : ∀ b ∈ B, ∀ g ∈ D, g * b ∈ D := fun b hb g hg =>
    mem_doubleCoset_mul_of_stable hD hg hb
  have hDs : ∀ i, ∀ g ∈ D, g * s i ∈ D := by
    intro i g hg
    obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, rfl⟩ := hg
    have hb₂' : b₂ ∈ (B : Set E) := hb₂
    rw [hfact i] at hb₂'
    obtain ⟨xu, ⟨x, hx, u, hu, rfl⟩, h, hh, rfl⟩ := hb₂'
    have hu' : (s i)⁻¹ * u * s i ∈ B := hUB (hconj i u hu)
    have hh' : (s i)⁻¹ * h * s i ∈ B := by
      have := hconjH _ (N.inv_mem (hsN i)) h hh
      rw [inv_inv] at this
      exact hHB this
    have htail : (s i)⁻¹ * u * s i * ((s i)⁻¹ * h * s i) ∈ B := B.mul_mem hu' hh'
    rcases hsign n hn i with hplus | hminus
    · refine ⟨b₁ * (n * x * n⁻¹), B.mul_mem hb₁ (hUB (hplus x hx)), n * s i,
        N.mul_mem hn (hsN i), _, htail, by group⟩
    · by_cases hx1 : x = 1
      · subst hx1
        exact ⟨b₁, hb₁, n * s i, N.mul_mem hn (hsN i), _, htail, by group⟩
      · obtain ⟨yh, ⟨y, hy, h₁, hh₁, rfl⟩, x', hx', hxs⟩ := hrew i x hx hx1
        refine ⟨b₁ * (n * y * n⁻¹) * (n * h₁ * n⁻¹),
          B.mul_mem (B.mul_mem hb₁ (hUB (hminus y hy))) (hHB (hconjH n hn h₁ hh₁)), n, hn,
          x' * ((s i)⁻¹ * u * s i * ((s i)⁻¹ * h * s i)), B.mul_mem (hUB (hXp i hx')) htail, ?_⟩
        have hxs' : x = y * h₁ * x' * (s i)⁻¹ := by
          rw [show y * h₁ * x' = x * s i from hxs]; group
        rw [hxs']
        group
  have hDsinv : ∀ i, ∀ g ∈ D, g * (s i)⁻¹ ∈ D := by
    intro i g hg
    have h := hDB _ (hHB (H.inv_mem (hs i))) _ (hDs i g hg)
    rwa [pow_two, mul_inv_rev, ← mul_assoc, mul_assoc g, mul_inv_cancel, mul_one] at h
  have hDN : ∀ n ∈ N, ∀ g ∈ D, g * n ∈ D := by
    intro n hn
    rw [hN] at hn
    induction hn using closure_induction'' with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact fun g hg => hDB x (hHB hx) g hg
      · exact hDs i
    | inv_mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact fun g hg => hDB x⁻¹ (hHB (H.inv_mem hx)) g hg
      · exact hDsinv i
    | one => exact fun g hg => by rwa [mul_one]
    | mul x y _ _ hx hy => exact fun g hg => by rw [← mul_assoc]; exact hy _ (hx g hg)
  have hDE : ∀ x ∈ B ⊔ N, ∀ g ∈ D, g * x ∈ D := by
    intro x hx
    rw [sup_eq_closure] at hx
    induction hx using closure_induction'' with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hDB x hx
      · exact hDN x hx
    | inv_mem x hx =>
      rcases hx with hx | hx
      · exact hDB x⁻¹ (B.inv_mem hx)
      · exact hDN x⁻¹ (N.inv_mem hx)
    | one => exact fun g hg => by rwa [mul_one]
    | mul x y _ _ hx hy => exact fun g hg => by rw [← mul_assoc]; exact hy _ (hx g hg)
  have hE₀D : ∀ x ∈ B ⊔ N, x ∈ D := fun x hx => by
    simpa using hDE x hx 1 hD1
  have hker : ∀ g ∈ B ⊔ N, π g = 1 → g = 1 := by
    intro g hg hπg
    obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, rfl⟩ := hE₀D g hg
    have hnB : π n ∈ B.map π := by
      refine ⟨b₁⁻¹ * b₂⁻¹, B.mul_mem (B.inv_mem hb₁) (B.inv_mem hb₂), ?_⟩
      simp only [map_mul] at hπg
      rw [map_mul, map_inv, map_inv]
      calc (π b₁)⁻¹ * (π b₂)⁻¹ = (π b₁)⁻¹ * (π b₁ * π n * π b₂) * (π b₂)⁻¹ := by
            rw [hπg]; group
        _ = π n := by group
    have hgB : b₁ * n * b₂ ∈ B := B.mul_mem (B.mul_mem hb₁ (hHB (hBN n hn hnB))) hb₂
    exact hBinj hgB B.one_mem (by rw [hπg, map_one])
  have hinj : Function.Injective (π.domRestrict (B ⊔ N)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hker g g.2 hg)
  have hsurj : Function.Surjective (π.domRestrict (B ⊔ N)) := by
    intro y
    have hy : y ∈ (B ⊔ N).map π := by rw [Subgroup.map_sup, hS]; exact mem_top y
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨⟨g, hg⟩, rfl⟩
  have hbij : Function.Bijective (π.domRestrict (B ⊔ N)) := ⟨hinj, hsurj⟩
  refine ⟨hbij, ?_, ?_⟩
  ·
    let f : π.ker × (B ⊔ N : Subgroup E) →* E :=
      MonoidHom.noncommCoprod π.ker.subtype (B ⊔ N).subtype fun c g =>
        (mem_center_iff.1 (hC c.2) g).symm
    have hf : ∀ c g, f (c, g) = (c : E) * g := fun c g => rfl
    have hfbij : Function.Bijective f := by
      refine ⟨?_, fun e => ?_⟩
      · rw [injective_iff_map_eq_one]
        rintro ⟨c, g⟩ h
        rw [hf] at h
        have hcg : (g : E) = (c : E)⁻¹ := eq_inv_of_mul_eq_one_right h
        have hg1 : (g : E) = 1 := by
          refine hker g g.2 ?_
          rw [hcg, map_inv, c.2, inv_one]
        have hc1 : (c : E) = 1 := by rw [hg1, mul_one] at h; exact h
        exact Prod.ext (Subtype.ext hc1) (Subtype.ext hg1)
      · obtain ⟨g, hg⟩ := hsurj (π e)
        have hc : e * (g : E)⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          change π e * (π.domRestrict (B ⊔ N) g)⁻¹ = 1
          rw [hg, mul_inv_cancel]
        exact ⟨(⟨_, hc⟩, g), by rw [hf]; group⟩
    exact ⟨MulEquiv.ofBijective f hfbij, hf⟩
  ·
    let ψ := MulEquiv.ofBijective (π.domRestrict (B ⊔ N)) hbij
    refine ⟨(B ⊔ N).subtype.comp ψ.symm.toMonoidHom, MonoidHom.ext fun y => ?_⟩
    change π.domRestrict (B ⊔ N) (ψ.symm y) = y
    exact ψ.apply_symm_apply y

end CFSG.RankThree.CentralExtension
