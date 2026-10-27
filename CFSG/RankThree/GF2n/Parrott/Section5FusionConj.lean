module

public import CFSG.RankThree.GF2n.Parrott.ActionV

public section

namespace CFSG.RankThree.GF2n.Parrott

open Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conj_inv_mul_comm {g x y : G} (h : x * (g * y * g⁻¹) = g * y * g⁻¹ * x) :
    g⁻¹ * x * g⁻¹⁻¹ * y = y * (g⁻¹ * x * g⁻¹⁻¹) :=
  calc g⁻¹ * x * g⁻¹⁻¹ * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * x) * g := by rw [h]
    _ = y * (g⁻¹ * x * g⁻¹⁻¹) := by group

private theorem card_J_inf_centralizer_conj_le {g y : G} (hg : g ∈ H z) :
    Nat.card ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)) ≤
      Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) := by
  have hHJ : H z ≤ normalizer (J z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
  refine card_le_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxJ, hxc⟩ := mem_inf.mp hx
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHJ ((H z).inv_mem hg)) x).mp hxJ,
    mem_centralizer_singleton_iff.mpr (conj_inv_mul_comm (mem_centralizer_singleton_iff.mp hxc))⟩

theorem forall_exists_conj_mem_ne_of_conj {g y : G} (hg : g ∈ H z)
    (hy : ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({g * y * g⁻¹} : Set G) →
      (∀ c ∈ H z ⊓ centralizer ({g * y * g⁻¹} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
      IsPGroup 2 B → g * y * g⁻¹ ∈ B → z ∉ B →
      Nat.card ↥(J z ⊓ centralizer ({g * y * g⁻¹} : Set G)) ≤ Nat.card B →
      ∃ c ∈ H z, c * (g * y * g⁻¹) * c⁻¹ ∈ B ∧ c * (g * y * g⁻¹) * c⁻¹ ≠ g * y * g⁻¹) :
    ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
      (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
      IsPGroup 2 B → y ∈ B → z ∉ B →
      Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
      ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  intro B hB hBn hB2 hyB hzB hcard
  have hgi : g⁻¹ ∈ H z := (H z).inv_mem hg
  have hconjH : ∀ {a c : G}, a ∈ H z → c ∈ H z → a * c * a⁻¹ ∈ H z := fun ha hc =>
    (H z).mul_mem ((H z).mul_mem ha hc) ((H z).inv_mem ha)
  have hconjC : ∀ {a c x : G}, c * x = x * c → (a * c * a⁻¹) * (a * x * a⁻¹) =
      (a * x * a⁻¹) * (a * c * a⁻¹) := fun {a c x} h =>
    calc a * c * a⁻¹ * (a * x * a⁻¹) = a * (c * x) * a⁻¹ := by group
      _ = a * (x * c) * a⁻¹ := by rw [h]
      _ = a * x * a⁻¹ * (a * c * a⁻¹) := by group
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hB' : B.map f ≤ H z ⊓ centralizer ({g * y * g⁻¹} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨hbH, hbc⟩ := mem_inf.mp (hB hb)
    exact mem_inf.mpr ⟨hconjH hg hbH, mem_centralizer_singleton_iff.mpr
      (hconjC (mem_centralizer_singleton_iff.mp hbc))⟩
  have hBn' : ∀ c ∈ H z ⊓ centralizer ({g * y * g⁻¹} : Set G), ∀ b ∈ B.map f,
      c * b * c⁻¹ ∈ B.map f := by
    rintro c hc _ ⟨b, hb, rfl⟩
    obtain ⟨hcH, hcc⟩ := mem_inf.mp hc
    have hc' : g⁻¹ * c * g⁻¹⁻¹ ∈ H z ⊓ centralizer ({y} : Set G) := by
      refine mem_inf.mpr ⟨hconjH hgi hcH, mem_centralizer_singleton_iff.mpr ?_⟩
      exact conj_inv_mul_comm (mem_centralizer_singleton_iff.mp hcc)
    refine mem_map.mpr ⟨_, hBn _ hc' b hb, ?_⟩
    show g * (g⁻¹ * c * g⁻¹⁻¹ * b * (g⁻¹ * c * g⁻¹⁻¹)⁻¹) * g⁻¹ = c * (g * b * g⁻¹) * c⁻¹
    group
  have hzB' : z ∉ B.map f := by
    rintro ⟨b, hb, hbz⟩
    have hgz : g * z = z * g := mem_centralizer_singleton_iff.mp hg
    have hbz' : g * b * g⁻¹ = z := hbz
    have h1 : g * b = z * g := by rw [← hbz']; group
    have : b = z := mul_left_cancel (h1.trans hgz.symm)
    exact hzB (this ▸ hb)
  obtain ⟨c, hcH, hcB, hcne⟩ := hy (B.map f) hB' hBn' (hB2.map f) (mem_map_of_mem f hyB) hzB'
    (((card_J_inf_centralizer_conj_le hg).trans hcard).trans_eq
      (card_map_of_injective (MulAut.conj g).injective).symm)
  obtain ⟨b, hb, hbeq⟩ := mem_map.mp hcB
  have hbeq' : g * b * g⁻¹ = c * (g * y * g⁻¹) * c⁻¹ := hbeq
  have hb' : g⁻¹ * c * g * y * (g⁻¹ * c * g)⁻¹ = b := by
    calc g⁻¹ * c * g * y * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * (g * y * g⁻¹) * c⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [hbeq']
      _ = b := by group
  refine ⟨g⁻¹ * c * g, (H z).mul_mem ((H z).mul_mem hgi hcH) hg, hb' ▸ hb, fun heq => hcne ?_⟩
  calc c * (g * y * g⁻¹) * c⁻¹ = g * (g⁻¹ * c * g * y * (g⁻¹ * c * g)⁻¹) * g⁻¹ := by group
    _ = g * y * g⁻¹ := by rw [heq]

end CFSG.RankThree.GF2n.Parrott
