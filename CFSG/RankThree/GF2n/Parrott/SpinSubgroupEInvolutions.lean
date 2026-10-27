module

public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupE
public import CFSG.RankThree.GF2n.Parrott.SpinFixedSConj
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}
variable {ψ : ↥(H z) →* A45} {κ : G → V}

private theorem eq_of_add_eq_zero_V' {v w : V} (h : v + w = 0) : v = w := by
  have h1 : -v = w := neg_eq_of_add_eq_zero_right h
  rw [← h1]
  exact (neg_eq_of_add_eq_zero_right (spinV_add_self v)).symm

theorem mem_spinFixE_of_involution_ut (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord ψ κ) {y : G}
    (hy : y ∈ H z) (hyy : y * y = 1) (hψ : ψ ⟨y, hy⟩ = uA * tA) : y ∈ spinFixE hκ := by
  have hz1 := z_ne_one_A h
  have hz2 := z_mul_self_A h
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  rw [mem_spinFixE_iff]
  refine ⟨hy, fun f hf => ?_⟩
  obtain ⟨x, hx⟩ := exists_range_rhoA_uA_mul_tA (κ f) hf.2
  obtain ⟨j, hj, hjx⟩ := hκ.surj x
  have hJn : y * j * y⁻¹ ∈ J z := (mem_normalizer_iff.mp (J_le_normalizer_A hy) j).mp hj
  have hcJ : y * j * y⁻¹ * j⁻¹ ∈ J z := mul_mem hJn (inv_mem hj)
  have hκc : κ (y * j * y⁻¹ * j⁻¹) = κ f := by
    rw [hκ.add _ hJn _ (inv_mem hj), hκ.act y hy j hj, hκ.kappa_inv hj, hψ, hjx]
    exact hx
  have hcF : y * j * y⁻¹ * j⁻¹ ∈ spinFixF hκ := ⟨hcJ, by rw [hκc]; exact hf.2⟩
  set c : G := y * j * y⁻¹ * j⁻¹ with hc
  have hcc : c * c = 1 := spinFixF_sq hκ hz1 hcF
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    have e1 : y * c * y⁻¹ = (y * y) * j * y⁻¹ * j⁻¹ * y⁻¹ := by simp only [hc]; group
    have e2 : c⁻¹ = j * y * j⁻¹ * y⁻¹ := by simp only [hc]; group
    rw [e1, e2, hyy, one_mul]
    rw [hyi]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  rw [hcinv] at hyc
  have hyc' : y * c = c * y := by
    rw [mul_inv_eq_iff_eq_mul] at hyc
    exact hyc
  rcases (hκ.kappa_eq_iff hf.1 hcJ).mp hκc with e | e
  · rw [e] at hyc'
    exact hyc'.symm
  · rw [e] at hyc'
    have h1 : (y * f) * z = (f * y) * z := by
      calc (y * f) * z = y * (f * z) := by rw [mul_assoc]
        _ = (f * z) * y := hyc'
        _ = f * (z * y) := by rw [mul_assoc]
        _ = f * (y * z) := by rw [← H_mul_z_comm hy]
        _ = (f * y) * z := by rw [mul_assoc]
    exact (mul_right_cancel h1).symm


@[expose] def spinFixT : AddSubgroup V where
  carrier := {v | SpinFixes tA v}
  zero_mem' := by
    show SpinFixes tA 0
    unfold SpinFixes
    rw [Matrix.mulVec_zero]
  add_mem' := fun {a b} ha hb => by
    have ha' : SpinFixes tA a := ha
    have hb' : SpinFixes tA b := hb
    show SpinFixes tA (a + b)
    unfold SpinFixes at ha' hb' ⊢
    rw [Matrix.mulVec_add, ha', hb']
  neg_mem' := fun {a} ha => by
    have ha' : SpinFixes tA a := ha
    show SpinFixes tA (-a)
    unfold SpinFixes at ha' ⊢
    rw [Matrix.mulVec_neg, ha']

theorem conj_mul_fixes' (hz2 : z * z = 1) {x j f : G} (hx : x ∈ H z) (hf : f ∈ J z)
    {a : ZMod 2} (hxf : x * f * x⁻¹ = if a = 0 then f else f * z)
    (hjf : j * f * j⁻¹ = if a = 0 then f else f * z) :
    (x * j) * f * (x * j)⁻¹ = f := by
  calc (x * j) * f * (x * j)⁻¹ = x * (j * f * j⁻¹) * x⁻¹ := by group
    _ = f := by
      rw [hjf]
      by_cases ha : a = 0
      · rw [if_pos ha] at hxf ⊢
        exact hxf
      · rw [if_neg ha] at hxf ⊢
        calc x * (f * z) * x⁻¹ = (x * f * x⁻¹) * (x * z * x⁻¹) := by group
          _ = (f * z) * z := by rw [hxf, show x * z * x⁻¹ = z by rw [H_mul_z_comm hx]; group]
          _ = f := by rw [mul_assoc, hz2, mul_one]

theorem exists_conj_mem_spinFixE_of_involution_t (h : Tim79a.ParrottHypA z)
    (hκ : IsSpinCoord ψ κ) (hE2 : IsElemAbelian 2 (spinFixE hκ)) {y : G} (hy : y ∈ H z)
    (hyy : y * y = 1) (hψ : ψ ⟨y, hy⟩ = tA) : ∃ x ∈ H z, x⁻¹ * y * x ∈ spinFixE hκ := by
  have hz1 := z_ne_one_A h
  have hz2 := z_mul_self_A h
  obtain ⟨e, he, heE, hψe⟩ := exists_spinFixE_over h hκ (tA_mem_S : tA ∈ sQA45)
  have hee : e * e = 1 := hE2.mul_self_eq_one heE
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  obtain ⟨ℓ, hadd, hspec⟩ := exists_action_functional hκ hz1 hz2 he spinFixT
    (fun u hu => by rw [hψe]; exact hu)
  have hj₁H : e⁻¹ * y ∈ H z := mul_mem (inv_mem he) hy
  have hj₁J : e⁻¹ * y ∈ J z := by
    rw [← hκ.eq_one_iff ⟨e⁻¹ * y, hj₁H⟩]
    have : (⟨e⁻¹ * y, hj₁H⟩ : ↥(H z)) = ⟨e, he⟩⁻¹ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_inv, hψe, hψ, inv_mul_cancel]
  obtain ⟨j₁, hj₁J, hyj⟩ : ∃ j₁ : G, j₁ ∈ J z ∧ y = e * j₁ := ⟨e⁻¹ * y, hj₁J, by group⟩
  have hJe : e * j₁ * e⁻¹ ∈ J z := (mem_normalizer_iff.mp (J_le_normalizer_A he) j₁).mp hj₁J
  have hprod : (e * j₁ * e⁻¹) * j₁ = 1 := by
    calc (e * j₁ * e⁻¹) * j₁ = (e * j₁) * (e * j₁) := by rw [hei]; group
      _ = y * y := by rw [← hyj]
      _ = 1 := hyy
  have hvC : SpinFixes tA (κ j₁) := by
    have h1 := hκ.add (e * j₁ * e⁻¹) hJe j₁ hj₁J
    rw [hprod, hκ.kappa_one, hκ.act e he j₁ hj₁J, hψe] at h1
    exact eq_of_add_eq_zero_V' h1.symm
  have hq : q (κ j₁) = ℓ (κ j₁) := by
    have h1 := hspec j₁ hj₁J hvC
    have h2 := hκ.sq j₁ hj₁J
    rw [h1] at hprod
    by_cases hℓ : ℓ (κ j₁) = 0
    · rw [if_pos hℓ] at hprod
      rw [hprod] at h2
      have : q (κ j₁) = 0 := by
        by_contra hqv
        rw [if_neg hqv] at h2
        exact hz1 h2.symm
      rw [this, hℓ]
    · rw [if_neg hℓ] at hprod
      have h3 : z * (j₁ * j₁) = 1 := by
        calc z * (j₁ * j₁) = (z * j₁) * j₁ := (mul_assoc z j₁ j₁).symm
          _ = (j₁ * z) * j₁ := by rw [← H_mul_z_comm (J_le_H hj₁J)]
          _ = 1 := hprod
      by_cases hqv : q (κ j₁) = 0
      · rw [if_pos hqv] at h2
        rw [h2, mul_one] at h3
        exact absurd h3 hz1
      · exact (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b) _ _ hqv hℓ
  have hW : ∀ u ∈ spinFixS, ℓ u = 0 := by
    intro u hu
    obtain ⟨f, hfJ, rfl⟩ := hκ.surj u
    have hf : f ∈ spinFixF hκ := ⟨hfJ, hu⟩
    have huU : κ f ∈ spinFixT := hu _ (tA_mem_S : tA ∈ sQA45)
    have h1 := hspec f hfJ huU
    have hfix : e * f * e⁻¹ = f := by
      have hc := ((mem_spinFixE_iff hκ e).mp heE).2 f hf
      rw [← hc]
      group
    rw [hfix] at h1
    by_contra hℓ
    rw [if_neg hℓ] at h1
    exact hz1 (mul_left_cancel (a := f) (by rw [mul_one]; exact h1)).symm
  obtain ⟨a, haS, ha⟩ := exists_conj_cover_of_fixes_tA ℓ (fun x hx x' hx' => hadd x hx x' hx')
    hW (κ j₁) hvC hq
  obtain ⟨x, hx⟩ := hκ.surjective a
  have hxH : (x : G) ∈ H z := x.2
  have hxa : ψ ⟨(x : G), hxH⟩ = a := hx
  refine ⟨x, hxH, ?_⟩
  rw [mem_spinFixE_iff]
  refine ⟨mul_mem (mul_mem (inv_mem hxH) hy) hxH, fun f hf => ?_⟩
  have hf'J : (x : G) * f * (x : G)⁻¹ ∈ J z :=
    (mem_normalizer_iff.mp (J_le_normalizer_A hxH) f).mp hf.1
  have hκf' : κ ((x : G) * f * (x : G)⁻¹) = ((rhoA a : GL8) : Mat8) *ᵥ κ f := by
    rw [hκ.act x hxH f hf.1, hxa]
  have hf'C : κ ((x : G) * f * (x : G)⁻¹) ∈ spinFixT := by
    rw [hκf']
    exact spinFixes_mulVec_of_conj (hf.2 _ haS)
  have h1 := hspec _ hf'J hf'C
  have h2 := J_conj_formula hκ hz2 hj₁J hf'J
  have hcov : ℓ (κ ((x : G) * f * (x : G)⁻¹)) = b (κ j₁) (κ ((x : G) * f * (x : G)⁻¹)) := by
    rw [hκf']
    exact ha _ hf.2
  rw [hcov] at h1
  have h3 := conj_mul_fixes' hz2 he hf'J h1 h2
  rw [← hyj] at h3
  have h4 : y * ((x : G) * f * (x : G)⁻¹) = ((x : G) * f * (x : G)⁻¹) * y := by
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  calc f * ((x : G)⁻¹ * y * (x : G))
      = (x : G)⁻¹ * (((x : G) * f * (x : G)⁻¹) * y) * (x : G) := by group
    _ = (x : G)⁻¹ * (y * ((x : G) * f * (x : G)⁻¹)) * (x : G) := by rw [h4]
    _ = ((x : G)⁻¹ * y * (x : G)) * f := by group

theorem isConj_tA_or_utA_of_involution {s : A45}
    (hs : s ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) : IsConj s tA ∨ IsConj s (uA * tA) := by
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hQn : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  rcases qa45_involution_classes s hord with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.mp h1
    have : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hc]
      exact hQn.conj_mem s hs c
    exact v_not_mem_Q this
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.mp h1
    have h2 : uA * vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hc]
      exact hQn.conj_mem s hs c
    have huQ : uA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := u_mem_Q
    have : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      have h3 := mul_mem (inv_mem huQ) h2
      rwa [inv_mul_cancel_left] at h3
    exact v_not_mem_Q this

section Meet

variable (D : QuotientData (z := z) (J_subgroupOf_normal z))

theorem exists_conj_mem_spinFixE_of_involution (h : Tim79a.ParrottHypA z)
    (hκ : IsSpinCoord (qH D) κ) (hE2 : IsElemAbelian 2 (spinFixE hκ)) {y : G} (hy : y ∈ H z)
    (hyy : y * y = 1) (hyJ : y ∉ J z) (hyc : y ∈ ⁅H z, H z⁆) :
    ∃ x ∈ H z, x * y * x⁻¹ ∈ spinFixE hκ := by
  have hyy' : (⟨y, hy⟩ * ⟨y, hy⟩ : ↥(H z)) = 1 := Subtype.ext hyy
  have hs2 : qH D ⟨y, hy⟩ * qH D ⟨y, hy⟩ = 1 := by rw [← map_mul, hyy', map_one]
  have hs1 : qH D ⟨y, hy⟩ ≠ 1 := fun h1 => hyJ ((hκ.eq_one_iff ⟨y, hy⟩).mp h1)
  have hsQ : qH D ⟨y, hy⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    obtain ⟨p, hp, hpy⟩ := commutator_le_map_P_H D hyc
    have hpe : p = ⟨y, hy⟩ := Subtype.ext hpy
    rw [hpe] at hp
    exact (mem_P_H_iff D _).mp hp
  rcases isConj_tA_or_utA_of_involution hsQ hs2 hs1 with h1 | h1
  · obtain ⟨c, hc⟩ := isConj_iff.mp h1
    obtain ⟨x₁, hx₁⟩ := hκ.surjective c
    have hy₁H : (x₁ : G) * y * (x₁ : G)⁻¹ ∈ H z := mul_mem (mul_mem x₁.2 hy) (inv_mem x₁.2)
    have hy₁y₁ : ((x₁ : G) * y * (x₁ : G)⁻¹) * ((x₁ : G) * y * (x₁ : G)⁻¹) = 1 := by
      calc ((x₁ : G) * y * (x₁ : G)⁻¹) * ((x₁ : G) * y * (x₁ : G)⁻¹)
          = (x₁ : G) * (y * y) * (x₁ : G)⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    have hψ₁ : qH D ⟨(x₁ : G) * y * (x₁ : G)⁻¹, hy₁H⟩ = tA := by
      have : (⟨(x₁ : G) * y * (x₁ : G)⁻¹, hy₁H⟩ : ↥(H z)) = x₁ * ⟨y, hy⟩ * x₁⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hx₁]
      exact hc
    obtain ⟨x, hxH, hxE⟩ := exists_conj_mem_spinFixE_of_involution_t h hκ hE2 hy₁H hy₁y₁ hψ₁
    refine ⟨x⁻¹ * (x₁ : G), mul_mem (inv_mem hxH) x₁.2, ?_⟩
    have : (x⁻¹ * (x₁ : G)) * y * (x⁻¹ * (x₁ : G))⁻¹ = x⁻¹ * ((x₁ : G) * y * (x₁ : G)⁻¹) * x := by
      group
    rw [this]
    exact hxE
  · obtain ⟨c, hc⟩ := isConj_iff.mp h1
    obtain ⟨x₁, hx₁⟩ := hκ.surjective c
    have hy₁H : (x₁ : G) * y * (x₁ : G)⁻¹ ∈ H z := mul_mem (mul_mem x₁.2 hy) (inv_mem x₁.2)
    have hy₁y₁ : ((x₁ : G) * y * (x₁ : G)⁻¹) * ((x₁ : G) * y * (x₁ : G)⁻¹) = 1 := by
      calc ((x₁ : G) * y * (x₁ : G)⁻¹) * ((x₁ : G) * y * (x₁ : G)⁻¹)
          = (x₁ : G) * (y * y) * (x₁ : G)⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    have hψ₁ : qH D ⟨(x₁ : G) * y * (x₁ : G)⁻¹, hy₁H⟩ = uA * tA := by
      have : (⟨(x₁ : G) * y * (x₁ : G)⁻¹, hy₁H⟩ : ↥(H z)) = x₁ * ⟨y, hy⟩ * x₁⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hx₁]
      exact hc
    exact ⟨x₁, x₁.2, mem_spinFixE_of_involution_ut h hκ hy₁H hy₁y₁ hψ₁⟩

end Meet

end CFSG.RankThree.GF2n.Parrott
