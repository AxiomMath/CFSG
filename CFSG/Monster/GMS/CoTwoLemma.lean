module

public import CFSG.Monster.GMS.Leech.Count

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace LeechSystem

variable {G : Type*} [Group G] {w : G} (L : LeechSystem w)

def vecSpace (N : Subgroup G) : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {y | ∃ n ∈ leechQ w ⊓ N, L.vec n = y}
  zero_mem' := ⟨1, ⟨one_mem _, one_mem _⟩, L.vec_one⟩
  add_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p * q, mul_mem hp hq, L.vec_mul p hp.1 q hq.1⟩
  smul_mem' := by
    intro c y hy
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨1, ⟨one_mem _, one_mem _⟩, by simpa using L.vec_one⟩
    · simpa using hy

theorem mem_vecSpace {N : Subgroup G} {y : Fin 24 → ZMod 2} :
    y ∈ L.vecSpace N ↔ ∃ n ∈ leechQ w ⊓ N, L.vec n = y := Iff.rfl

include L

theorem vec_commutator {g q : G} (hg : g ∈ Subgroup.centralizer ({w} : Set G))
    (hq : q ∈ leechQ w) :
    ⁅g, q⁆ ∈ leechQ w ∧ L.vec ⁅g, q⁆ = co1Act (L.φ ⟨g, hg⟩) (L.vec q) + L.vec q := by
  have h1 : g * q * g⁻¹ ∈ leechQ w := L.conj_mem' hg hq
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hq)
  · rw [commutatorElement_def, L.vec_mul _ h1 _ (inv_mem hq), L.vec_inv hq, L.vec_conj' hg hq]

theorem commutator_eq_of_comm_span
    {D : Subgroup G}
    (hD : D ≤ Subgroup.centralizer ({w} : Set G)) {K : Subgroup Co1} (hK : L.image D = K)
    {S : Set (Fin 24 → ZMod 2)} (hS : ∀ y, y ∈ S ↔ y ∈ L.vecSpace D) (ha : ⁅K, K⁆ = K)
    (hb : ∀ X : Submodule (ZMod 2) (Fin 24 → ZMod 2), (∀ x ∈ X, x ∈ S) →
      (∀ A ∈ K, ∀ x ∈ X, co1Act A x ∈ X) → (∀ A ∈ K, ∀ y ∈ S, co1Act A y + y ∈ X) →
      ∀ y ∈ S, y ∈ X)
    (hc : ∃ y₁ ∈ S, ∃ y₂ ∈ S, bil₀ y₁ y₂ = 1) : ⁅D, D⁆ = D := by
  subst hK
  have hPD : ⁅D, D⁆ ≤ D := Subgroup.commutator_le.2 fun g hg h hh =>
    D.mul_mem (D.mul_mem (D.mul_mem hg hh) (D.inv_mem hg)) (D.inv_mem hh)
  have hPnorm : ∀ g ∈ D, ∀ p ∈ ⁅D, D⁆, g * p * g⁻¹ ∈ ⁅D, D⁆ := by
    intro g hg p hp
    have h1 : ⁅g, p⁆ ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator hg (hPD hp)
    have h2 : g * p * g⁻¹ = ⁅g, p⁆ * p := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem h1 hp
  let X : Submodule (ZMod 2) (Fin 24 → ZMod 2) := L.vecSpace ⁅D, D⁆
  have hXS : ∀ x ∈ X, x ∈ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hS _).2 ⟨p, ⟨hp.1, hPD hp.2⟩, rfl⟩
  have hXinv : ∀ A ∈ L.image D, ∀ x ∈ X, co1Act A x ∈ X := by
    intro A hA x hx
    obtain ⟨c, hcD, rfl⟩ := L.mem_image.1 hA
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨(c : G) * p * (c : G)⁻¹, ⟨L.conj_mem c hp.1, hPnorm _ hcD _ hp.2⟩, ?_⟩
    exact L.vec_conj c p hp.1
  have hXseed : ∀ A ∈ L.image D, ∀ y ∈ S, co1Act A y + y ∈ X := by
    intro A hA y hy
    obtain ⟨c, hcD, rfl⟩ := L.mem_image.1 hA
    obtain ⟨n, hn, rfl⟩ := (hS y).1 hy
    obtain ⟨hcQ, hcv⟩ := L.vec_commutator c.2 hn.1
    exact ⟨⁅(c : G), n⁆, ⟨hcQ, Subgroup.commutator_mem_commutator hcD hn.2⟩, hcv⟩
  have hmain := hb X hXS hXinv hXseed
  have hwP : w ∈ ⁅D, D⁆ := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hc
    obtain ⟨n₁, hn₁, rfl⟩ := (hS y₁).1 hy₁
    obtain ⟨n₂, hn₂, rfl⟩ := (hS y₂).1 hy₂
    rw [← (L.comm_eq_z_iff hn₁.1 hn₂.1).2 hy]
    exact Subgroup.commutator_mem_commutator hn₁.2 hn₂.2
  have hNP : ∀ n ∈ leechQ w ⊓ D, n ∈ ⁅D, D⁆ := by
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hmain _ ((hS _).2 ⟨n, hn, rfl⟩)
    rcases L.eq_or_eq_mul_z hn.1 hp.1 hpn.symm with h | h
    · rw [h]
      exact hp.2
    · rw [h]
      exact mul_mem hp.2 hwP
  have hKP : L.image D ≤ L.image ⁅D, D⁆ := by
    rw [← ha]
    refine Subgroup.commutator_le.2 fun A₁ hA₁ A₂ hA₂ => ?_
    obtain ⟨c₁, hc₁, rfl⟩ := L.mem_image.1 hA₁
    obtain ⟨c₂, hc₂, rfl⟩ := L.mem_image.1 hA₂
    exact L.mem_image.2 ⟨⁅c₁, c₂⁆, Subgroup.commutator_mem_commutator hc₁ hc₂,
      map_commutatorElement _ _ _⟩
  refine le_antisymm hPD fun d hd => ?_
  obtain ⟨c, hcP, hcd⟩ := L.mem_image.1 (hKP (L.mem_image.2 ⟨⟨d, hD hd⟩, hd, rfl⟩))
  have hker : (c : G)⁻¹ * d ∈ leechQ w := by
    refine (L.φ_ker (c⁻¹ * ⟨d, hD hd⟩)).1 ?_
    rw [map_mul, map_inv, hcd, inv_mul_cancel]
  have hmem := hNP _ ⟨hker, D.mul_mem (D.inv_mem (hPD hcP)) hd⟩
  have := mul_mem hcP hmem
  rwa [mul_inv_cancel_left] at this

theorem mem_vecSpace_centralizer_inf
    {ι : Type*} (s : ι → G) (hs : ∀ i, s i ∈ leechQ w)
    (y : Fin 24 → ZMod 2) :
    y ∈ L.vecSpace (Subgroup.centralizer ({w} : Set G) ⊓
      ⨅ i, Subgroup.centralizer ({s i} : Set G)) ↔ ∀ i, bil₀ y (L.vec (s i)) = 0 := by
  constructor
  · rintro ⟨n, hn, rfl⟩ i
    have h := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hn.2).2) i
    exact (L.comm_eq_one_iff hn.1 (hs i)).1
      (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 h))
  · intro h
    obtain ⟨q, hq, rfl⟩ := L.vec_surj y
    refine ⟨q, ⟨hq, Subgroup.mem_inf.2 ⟨L.mem_centralizer hq,
      Subgroup.mem_iInf.2 fun i => ?_⟩⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hq (hs i)).2 (h i)))

end LeechSystem

end CFSG.Monster.GMS
