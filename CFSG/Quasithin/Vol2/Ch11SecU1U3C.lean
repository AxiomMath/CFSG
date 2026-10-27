module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutBasic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Dick
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmNineZ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Alg
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.QuasithinUnique.Ch1 (transAut transAut_apply isInnerAut_of_transAut_mem_inner
  inner_of_sigma_id)
open CFSG.Quasithin.A312U3 (uniData)

variable {G : Type} [Group G] {L : Subgroup G} [L.Normal]

theorem mem_of_isInnerAut (hC : Subgroup.centralizer (L : Set G) = ⊥) {t : G}
    (h : CFSG.QuasithinUnique.Ch1.IsInnerAut (MulAut.conjNormal t : MulAut ↥L)) : t ∈ L := by
  obtain ⟨l, hl⟩ := h
  have hc : (l : G) * t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (hl ⟨y, hy⟩)
    rw [MulAut.conjNormal_apply] at h1
    push_cast at h1
    calc y * ((l : G) * t) = (l : G) * ((l : G)⁻¹ * y * l) * t := by group
      _ = (l : G) * (t * y * t⁻¹) * t := by rw [← h1]
      _ = (l : G) * t * y := by group
  rw [hC, Subgroup.mem_bot] at hc
  have h2 : t = (l : G)⁻¹ := eq_inv_of_mul_eq_one_right hc
  rw [h2]
  exact L.inv_mem l.2

variable {p : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p 1 F)

theorem exists_rep_bar (hp2 : p ≠ 2) (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (ψh : ↥L ≃* hypPSU h 1 1) {t : G} (htL : t ∉ L) (ht2 : orderOf t = 2) :
    ∃ x : semilinearSimilitudes h 1 1,
      semilinearAutHom h (le_refl 1) (le_refl 1) x = transAut ψh (MulAut.conjNormal t) ∧
        ∀ c, (x : SemiGL (HypIndex 1 1) F).right c = h.bar c := by
  set β : MulAut ↥L := MulAut.conjNormal t with hβ
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hβ2 : ∀ x, β (β x) = x := fun x => by
    rw [← MulAut.mul_apply, hβ, ← map_mul, htt, map_one, MulAut.one_apply]
  have hinner : ¬ CFSG.QuasithinUnique.Ch1.IsInnerAut β := fun hin =>
    htL (mem_of_isInnerAut hC hin)
  have hα1 : transAut ψh β ≠ 1 := fun h1 => hinner ⟨1, fun x => by
    have : β x = x := ψh.injective (by rw [← transAut_apply, h1, MulAut.one_apply])
    rw [this, inv_one, one_mul, mul_one]⟩
  have hord : orderOf (transAut ψh β) = 2 := orderOf_eq_prime
    (by rw [sq]; exact CFSG.QuasithinUnique.Ch1.transAut_mul_self ψh β hβ2) hα1
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, -⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp2 (le_refl 1) (le_refl 1)
      (by norm_num)).2.2.2 _ hord
  rcases hσ with rfl | hσ
  · exfalso
    have hin := inner_of_sigma_id h hA hx (hid rfl)
    rw [hΦ] at hin
    exact hinner (isInnerAut_of_transAut_mem_inner ψh β hin)
  · exact ⟨⟨_, hx⟩, hΦ, hσ⟩

theorem outer_pair (hp2 : p ≠ 2) (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (ψh : ↥L ≃* hypPSU h 1 1) {t₁ t₂ : G} (h1L : t₁ ∉ L) (h2L : t₂ ∉ L)
    (h1 : orderOf t₁ = 2) (h2 : orderOf t₂ = 2) (hc : t₁ * t₂ = t₂ * t₁) : t₁ * t₂ ∈ L := by
  by_contra h12L
  obtain ⟨x₁, hx₁, hσ₁⟩ := exists_rep_bar h hp2 hC ψh h1L h1
  obtain ⟨x₂, hx₂, hσ₂⟩ := exists_rep_bar h hp2 hC ψh h2L h2
  have h12 : orderOf (t₁ * t₂) = 2 := by
    refine orderOf_eq_prime ?_ fun h0 => h12L (h0 ▸ L.one_mem)
    have ht1 : t₁ * t₁ = 1 := by rw [← pow_two, ← h1, pow_orderOf_eq_one]
    have ht2 : t₂ * t₂ = 1 := by rw [← pow_two, ← h2, pow_orderOf_eq_one]
    rw [sq, show t₁ * t₂ * (t₁ * t₂) = (t₁ * t₁) * (t₂ * t₂) by
      rw [mul_assoc, ← mul_assoc t₂, ← hc]; group, ht1, ht2, one_mul]
  obtain ⟨x', hx', hσ'⟩ := exists_rep_bar h hp2 hC ψh h12L h12
  have hΦ : semilinearAutHom h (le_refl 1) (le_refl 1) (x₁ * x₂) =
      semilinearAutHom h (le_refl 1) (le_refl 1) x' := by
    rw [map_mul, hx₁, hx₂, hx']
    refine MulEquiv.ext fun y => ?_
    obtain ⟨y, rfl⟩ := ψh.surjective y
    rw [MulAut.mul_apply, transAut_apply, transAut_apply, transAut_apply, map_mul,
      MulAut.mul_apply]
  have hker : semilinearAutHom h (le_refl 1) (le_refl 1) (x₁ * x₂ * x'⁻¹) = 1 := by
    rw [map_mul, map_inv, hΦ, mul_inv_cancel]
  obtain ⟨hr, -⟩ := ((odd_unitary_automorphism_semilinear_representation h hp2 (le_refl 1)
    (le_refl 1) (by norm_num)).2.2.1 _).mp hker
  have e : (x₁ : SemiGL (HypIndex 1 1) F).right * (x₂ : SemiGL (HypIndex 1 1) F).right =
      (x' : SemiGL (HypIndex 1 1) F).right := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right] at hr
    exact mul_inv_eq_one.mp hr
  obtain ⟨c, hc'⟩ := h.exists_bar_ne
  apply hc'
  have e2 := congrArg (fun σ : F ≃+* F => σ c) e
  change (x₁ : SemiGL (HypIndex 1 1) F).right ((x₂ : SemiGL (HypIndex 1 1) F).right c) = _ at e2
  rw [hσ₁, hσ₂, hσ', h.bar_bar] at e2
  exact e2.symm

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
