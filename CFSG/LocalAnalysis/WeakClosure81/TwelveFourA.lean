module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartanRel
public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartan

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section FourA

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_normalizer_le_sylow (S : Sylow 2 G) :
    pCoreOf 2 (normalizer (S : Set G)) ≤ (S : Subgroup G) := by
  have hP : IsPGroup 2 (pCoreOf 2 (normalizer (S : Set G))) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hN : pCoreOf 2 (normalizer (S : Set G)) ≤ normalizer (S : Set G) := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  exact le_sylow_of_le_normalizer hP hN

private theorem b12_TwelveFourA_card_ne_one (A : Subgroup G) {m : ℕ} (hA : Nat.card A = 2 ^ m) :
    Nat.card {x : ↥A // x ≠ 1} = 2 ^ m - 1 := by
  classical
  haveI hF : Fintype ↥A := Fintype.ofFinite _
  haveI hFs : Fintype {x : ↥A // x ≠ 1} := Fintype.ofFinite _
  have h1 : Fintype.card ↥A = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hA]
  have h2 : Fintype.card {x : ↥A // x ≠ 1} = 2 ^ m - 1 := by
    rw [Fintype.card_subtype_compl (p := fun y : ↥A => y = 1),
      Fintype.card_subtype_eq (1 : ↥A), h1]
  rwa [Nat.card_eq_fintype_card]

theorem exists_cartan_conj_inf_eq_bot {n m : ℕ}
    (hG : CFSG.Quasithin.IsPSL 2 2 n G) (S : Sylow 2 G) {t : G} (ht : t * t = 1)
    (htS : t ∉ normalizer (S : Set G)) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hm : 1 ≤ m) (hAcard : Nat.card A = 2 ^ m) (hnm : n = 2 * m) :
    ∃ b ∈ cartan (S : Subgroup G) t, ∀ a ∈ A, ∀ a' ∈ A, b * a' * b⁻¹ = a → a = 1 := by
  by_contra hcon
  push Not at hcon
  have hspec := rankOne_cartan_spec (Or.inl hG) S ht htS
  have hcardT : Nat.card (cartan (S : Subgroup G) t) = 2 ^ n - 1 := hspec.2.2.2.2.1
  choose! f hfA g hgA hfg hf1 using hcon
  have hg1 : ∀ b ∈ cartan (S : Subgroup G) t, g b ≠ 1 := by
    intro b hb h1
    apply hf1 b hb
    rw [← hfg b hb, h1]
    group
  let Φ : ↥(cartan (S : Subgroup G) t) → {x : ↥A // x ≠ 1} × {x : ↥A // x ≠ 1} :=
    fun b => (⟨⟨f b.1, hfA b.1 b.2⟩, fun h => hf1 b.1 b.2 (congrArg Subtype.val h)⟩,
      ⟨⟨g b.1, hgA b.1 b.2⟩, fun h => hg1 b.1 b.2 (congrArg Subtype.val h)⟩)
  have hinj : Function.Injective Φ := by
    intro b b' hbb
    have hf : f b.1 = f b'.1 := congrArg (fun p => ((p.1 : ↥A) : G)) hbb
    have hgg : g b.1 = g b'.1 := congrArg (fun p => ((p.2 : ↥A) : G)) hbb
    have hgS : g b.1 ∈ (S : Subgroup G) := hAS (hgA b.1 b.2)
    have hfS : f b.1 ∈ (S : Subgroup G) := hAS (hfA b.1 b.2)
    obtain ⟨x, hx, huniq⟩ := rankOne_psl_cartan_regular hG S ht htS hgS hfS (hg1 b.1 b.2)
      (hf1 b.1 b.2)
    have e1 : b = x := huniq b (hfg b.1 b.2)
    have e2 : b' = x := huniq b' (by
      have := hfg b'.1 b'.2
      rw [← hgg, ← hf] at this
      exact this)
    rw [e1, e2]
  have hle : Nat.card ↥(cartan (S : Subgroup G) t) ≤
      Nat.card ({x : ↥A // x ≠ 1} × {x : ↥A // x ≠ 1}) := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_prod, b12_TwelveFourA_card_ne_one A hAcard, hcardT, hnm, pow_mul'] at hle
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ m = y + 2 := ⟨2 ^ m - 2, by omega⟩
  rw [hy] at hle
  have h3 : ((y + 2) ^ 2 - 1) ≤ (y + 2 - 1) * (y + 2 - 1) := hle
  have h4 : (y + 2) ^ 2 = y * y + 4 * y + 4 := by ring
  rw [h4] at h3
  have h5 : y + 2 - 1 = y + 1 := by omega
  rw [h5] at h3
  have h6 : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by ring
  rw [h6] at h3
  generalize y * y = w at h3
  omega

private theorem b12_TwelveFourA_mul_injective {A C : Subgroup G} (hdisj : A ⊓ C = ⊥)
    {a a' c c' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hc : c ∈ C) (hc' : c' ∈ C)
    (h : a * c = a' * c') : a = a' ∧ c = c' := by
  have h2 : a'⁻¹ * a = c' * c⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
      _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have h3 : a'⁻¹ * a ∈ A ⊓ C :=
    ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ C.mul_mem hc' (C.inv_mem hc)⟩
  rw [hdisj] at h3
  have h4 : a'⁻¹ * a = 1 := h3
  have h5 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h4, mul_one]
  refine ⟨h5, ?_⟩
  rw [h5] at h
  exact mul_left_cancel h

private theorem b12_TwelveFourA_exists_mul {S A C : Subgroup G} (hAS : A ≤ S) (hCS : C ≤ S)
    (hdisj : A ⊓ C = ⊥) (hcard : Nat.card A * Nat.card C = Nat.card S) :
    ∀ s ∈ S, ∃ a ∈ A, ∃ c ∈ C, s = a * c := by
  let P : ↥A × ↥C → ↥S := fun p => ⟨p.1 * p.2, S.mul_mem (hAS p.1.2) (hCS p.2.2)⟩
  have hinj : Function.Injective P := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    have h1 : (a : G) * c = a' * c' := congrArg Subtype.val h
    obtain ⟨e1, e2⟩ := b12_TwelveFourA_mul_injective hdisj a.2 a'.2 c.2 c'.2 h1
    rw [Subtype.ext e1, Subtype.ext e2]
  have hbij : Function.Bijective P :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  intro s hs
  obtain ⟨⟨a, c⟩, hac⟩ := hbij.2 ⟨s, hs⟩
  exact ⟨a, a.2, c, c.2, (congrArg Subtype.val hac).symm⟩

private theorem b12_TwelveFourA_card_eq_mul {A C U : Subgroup G} (hAU : A ≤ U)
    (hdisj : A ⊓ C = ⊥) (hdec : ∀ u ∈ U, ∃ a ∈ A, ∃ c ∈ C, u = a * c) :
    Nat.card U = Nat.card A * Nat.card ↥(U ⊓ C) := by
  let P : ↥A × ↥(U ⊓ C) → ↥U := fun p =>
    ⟨p.1 * p.2, U.mul_mem (hAU p.1.2) p.2.2.1⟩
  have hinj : Function.Injective P := by
    rintro ⟨a, d⟩ ⟨a', d'⟩ h
    have h1 : (a : G) * d = a' * d' := congrArg Subtype.val h
    obtain ⟨e1, e2⟩ := b12_TwelveFourA_mul_injective hdisj a.2 a'.2 d.2.2 d'.2.2 h1
    rw [Subtype.ext e1, Subtype.ext e2]
  have hsurj : Function.Surjective P := by
    rintro ⟨u, hu⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec u hu
    have hcU : c ∈ U := by
      have : c = a⁻¹ * (a * c) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem (hAU ha)) hu
    exact ⟨(⟨a, ha⟩, ⟨c, hcU, hc⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective P ⟨hinj, hsurj⟩).symm

theorem twelveFour_exists_conj {n m : ℕ}
    (hG : CFSG.Quasithin.IsPSL 2 2 n G) (S : Sylow 2 G) {t : G} (ht : t * t = 1)
    (htS : t ∉ normalizer (S : Set G)) {A U : Subgroup G} (hAU : A ≤ U)
    (hUS : U ≤ (S : Subgroup G)) (hm : 1 ≤ m) (hAcard : Nat.card A = 2 ^ m)
    (hUcard : 2 ^ (m + 1) ≤ Nat.card U) (hnm : n = 2 * m) :
    ∃ b ∈ cartan (S : Subgroup G) t,
      (∀ s ∈ (S : Subgroup G), ∃ a ∈ A, ∃ c ∈ A.map (MulAut.conj b).toMonoidHom, s = a * c) ∧
      U ⊓ A.map (MulAut.conj b).toMonoidHom ≠ ⊥ ∧
      A.relIndex U < 2 ^ (m + 1) ∧
      (U ⊓ A.map (MulAut.conj b).toMonoidHom).relIndex U < 2 ^ (m + 1) := by
  have hAS : A ≤ (S : Subgroup G) := hAU.trans hUS
  obtain ⟨b, hbT, hb⟩ := exists_cartan_conj_inf_eq_bot hG S ht htS hAS hm hAcard hnm
  have hbN : b ∈ normalizer (S : Set G) := (rankOne_cartan_spec (Or.inl hG) S ht htS).1 hbT
  set C : Subgroup G := A.map (MulAut.conj b).toMonoidHom with hC
  have hCS : C ≤ (S : Subgroup G) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hbN a).mp (hAS ha)
  have hCcard : Nat.card C = 2 ^ m := by
    rw [hC, Subgroup.card_map_of_injective (MulAut.conj b).injective, hAcard]
  have hdisj : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, a', ha', rfl⟩
    exact hb _ hxA a' ha' rfl
  have hScard : Nat.card (S : Subgroup G) = 2 ^ n := (rankOne_psl_sylow_elemAbelian hG S).2
  have hprod : Nat.card A * Nat.card C = Nat.card (S : Subgroup G) := by
    rw [hAcard, hCcard, hScard, hnm, pow_mul', sq]
  have hSAC := b12_TwelveFourA_exists_mul hAS hCS hdisj hprod
  have hUcard' : Nat.card U = Nat.card A * Nat.card ↥(U ⊓ C) :=
    b12_TwelveFourA_card_eq_mul hAU hdisj (fun u hu => hSAC u (hUS hu))
  have hApos : 0 < Nat.card A := by rw [hAcard]; positivity
  have hDpos : 0 < Nat.card ↥(U ⊓ C) := Nat.card_pos
  have hD1 : U ⊓ C ≠ ⊥ := by
    intro hD
    have h1 : Nat.card ↥(U ⊓ C) = 1 := by rw [hD]; exact Subgroup.card_bot
    rw [h1, mul_one, hAcard] at hUcard'
    rw [hUcard', pow_succ] at hUcard
    have : 0 < 2 ^ m := by positivity
    omega
  refine ⟨b, hbT, hSAC, hD1, ?_, ?_⟩
  · have h := Subgroup.relIndex_mul_card (H := A) (K := U)
    rw [inf_eq_left.2 hAU, hUcard'] at h
    have h2 : A.relIndex U = Nat.card ↥(U ⊓ C) :=
      Nat.eq_of_mul_eq_mul_right hApos (by rw [h, mul_comm])
    rw [h2]
    calc Nat.card ↥(U ⊓ C) ≤ Nat.card C := Subgroup.card_le_of_le inf_le_right
      _ = 2 ^ m := hCcard
      _ < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · have h := Subgroup.relIndex_mul_card (H := U ⊓ C) (K := U)
    rw [inf_eq_left.2 inf_le_left, hUcard'] at h
    have h2 : (U ⊓ C).relIndex U = Nat.card A :=
      Nat.eq_of_mul_eq_mul_right hDpos h
    rw [h2, hAcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end FourA

end CFSG.LocalAnalysis.WeakClosure81
