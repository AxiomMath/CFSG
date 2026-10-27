module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 Subgroup
open scoped Pointwise

section Basic

variable {H : Type} [Group H] [Finite H]

theorem pgroup_comm_of_absyl {S0 : Subgroup H} (hS0 : IsSylowOf 3 S0 ⊤) (hc : IsMulCommutative S0)
    {S : Subgroup H} (hS : IsPGroup 3 S) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hp, hcop⟩ := hS0
  rw [Subgroup.relIndex_top_right] at hcop
  let S0s : Sylow 3 H := hp.toSylow ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S0s Q
  have hmem : ∀ x ∈ (Q : Subgroup H), ∃ s ∈ S0, x = g * s * g⁻¹ := by
    intro x hx
    rw [← hg, Sylow.smul_def] at hx
    have hx' : x ∈ (MulAut.conj g • (S0s : Subgroup H)) := hx
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, rfl⟩ := hx'
    exact ⟨s, hs, rfl⟩
  intro x hx y hy
  obtain ⟨s, hs, hxs⟩ := hmem x (hQ hx)
  obtain ⟨t, ht, hyt⟩ := hmem y (hQ hy)
  have hst : s * t = t * s := by
    have := hc.is_comm.comm (⟨s, hs⟩ : S0) ⟨t, ht⟩
    exact congrArg Subtype.val this
  rw [hxs, hyt]
  calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
    _ = g * (t * s) * g⁻¹ := by rw [hst]
    _ = _ := by group

theorem le_nor_of_stable {T P : Subgroup H} (h : ∀ a ∈ T, ∀ x ∈ P, a * x * a⁻¹ ∈ P) :
    T ≤ Nor P := by
  intro a ha
  rw [Nor, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h a ha x hx, fun hx => ?_⟩
  have := h a⁻¹ (T.inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem isElementaryAbelian_of_le {A T : Subgroup H} (hA : IsElementaryAbelian 3 ↥A) (hTA : T ≤ A) :
    IsElementaryAbelian 3 ↥T where
  is_comm := ⟨fun a b => by
    have h := hA.toIsMulCommutative.is_comm.comm (⟨a, hTA a.2⟩ : A) ⟨b, hTA b.2⟩
    have h' := congrArg (fun x : ↥A => (x : H)) h
    exact Subtype.ext h'⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := A) x (hTA x.2))

theorem card_sup_of_commute {P Q : Subgroup H} (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hd : P ⊓ Q = ⊥) : Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  let f : P × Q →* H := MonoidHom.noncommCoprod P.subtype Q.subtype fun x y => hc x x.2 y y.2
  have hrange : f.range = P ⊔ Q := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      exact (P ⊔ Q).mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right y.2)
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by show x * 1 = x; simp⟩
    · intro x hx
      exact ⟨(1, ⟨x, hx⟩), by show 1 * x = x; simp⟩
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : H) * y = 1 := hxy
    have h1 : (x : H) = (y : H)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have h2 : (x : H) ∈ P ⊓ Q := ⟨x.2, by rw [h1]; exact Q.inv_mem y.2⟩
    rw [hd, Subgroup.mem_bot] at h2
    have hx1 : x = 1 := Subtype.ext h2
    have hy1 : (y : H) = 1 := by rw [h1] at h2; simpa using h2
    rw [Subgroup.mem_bot]
    exact Prod.ext hx1 (Subtype.ext hy1)
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hrange] at h1
  rw [← h1, Nat.card_prod]

theorem exists_elemAb_compl {A Z : Subgroup H} (hA : IsElemAb 3 4 A) (hZA : Z ≤ A)
    (hZ : Nat.card Z = 9) : ∃ T : Subgroup H, T ≤ A ∧ IsElemAb 3 2 T ∧ T ⊓ Z = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hA.1
  obtain ⟨C', hC'⟩ := IsElementaryAbelian.exists_isCompl 3 ↥A (Z.subgroupOf A)
  set T : Subgroup H := C'.map A.subtype with hT
  have hTA : T ≤ A := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTZ : T ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxT, hxZ⟩
    obtain ⟨c, hc, rfl⟩ := hxT
    have h1 : c ∈ Z.subgroupOf A ⊓ C' := ⟨Subgroup.mem_subgroupOf.2 hxZ, hc⟩
    rw [hC'.1.eq_bot] at h1
    have : c = 1 := h1
    rw [show A.subtype c = 1 by rw [this]; exact map_one _]
    exact Subgroup.one_mem _
  have hcomm : ∀ x ∈ Z, ∀ y ∈ T, x * y = y * x := fun x hx y hy => by
    have := hA.1.toIsMulCommutative.is_comm.comm (⟨x, hZA hx⟩ : A) ⟨y, hTA hy⟩
    exact congrArg Subtype.val this
  have hsup : Z ⊔ T = A := by
    have h1 : (Z.subgroupOf A) ⊔ C' = ⊤ := hC'.2.eq_top
    have h2 := congrArg (Subgroup.map A.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZA, Subgroup.map_top,
      Subgroup.range_subtype] at h2
    exact h2
  have hcard : Nat.card A = Nat.card Z * Nat.card T := by
    rw [← hsup]; exact card_sup_of_commute hcomm (by rw [inf_comm]; exact hTZ)
  have h81 : Nat.card A = 3 ^ 4 := hA.2
  refine ⟨T, hTA, ⟨isElementaryAbelian_of_le hA.1 hTA, ?_⟩, hTZ⟩
  rw [hZ, h81] at hcard
  omega

end Basic

section Simple

theorem eq_one_of_central_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) {x : X} (hx : ∀ w : X, w * x = x * w) : x = 1 := by
  have := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hn).2
  have hmem : x ∈ center X := Subgroup.mem_center_iff.2 fun g => (hx g)
  rw [this] at hmem
  exact hmem

end Simple

end CFSG.RankThree.PartTwo.Sec21.FF79
