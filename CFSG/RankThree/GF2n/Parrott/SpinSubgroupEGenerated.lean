module

public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupE
public import CFSG.RankThree.GF2n.Parrott.SpinFixedSConj
public import CFSG.RankThree.GF2n.Parrott.SpinStabW0
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

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

variable {G : Type} [Group G] [Finite G] {z : G}
variable {κ : G → V}

section Generation

variable (D : QuotientData (z := z) (J_subgroupOf_normal z))

private theorem eq_of_add_eq_zero_V {v w : V} (h : v + w = 0) : v = w := by
  have h1 : -v = w := neg_eq_of_add_eq_zero_right h
  rw [← h1]
  exact (neg_eq_of_add_eq_zero_right (spinV_add_self v)).symm

theorem exists_j_conj_ne (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord (qH D) κ) {e : G}
    (he : e ∈ spinFixE hκ) (heJ : e ∉ J z) :
    ∃ j ∈ J z, j * e * j⁻¹ ≠ e ∧ j * e * j⁻¹ ≠ e * z := by
  have hz1 := z_ne_one_A h
  have heH : e ∈ H z := spinFixE_le_H hκ he
  have hs1 : qH D ⟨e, heH⟩ ≠ 1 := fun h1 => heJ ((hκ.eq_one_iff ⟨e, heH⟩).mp h1)
  have hmove : ∃ v : V, ((rhoA (qH D ⟨e, heH⟩) : GL8) : Mat8) *ᵥ v ≠ v := by
    by_contra hall
    have hall' : ∀ v : V, ((rhoA (qH D ⟨e, heH⟩) : GL8) : Mat8) *ᵥ v = v := fun v => by
      by_contra hv
      exact hall ⟨v, hv⟩
    apply hs1
    apply rhoA_injective
    rw [map_one]
    apply Units.ext
    ext i j
    have := congrFun (hall' (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  obtain ⟨v, hv⟩ := hmove
  obtain ⟨j, hj, hjv⟩ := hκ.surj v
  have hJn : e * j⁻¹ * e⁻¹ ∈ J z := (mem_normalizer_iff.mp (J_le_normalizer_A heH) j⁻¹).mp
    (inv_mem hj)
  have hd : j * e * j⁻¹ * e⁻¹ ∈ J z := by
    have : j * e * j⁻¹ * e⁻¹ = j * (e * j⁻¹ * e⁻¹) := by group
    rw [this]
    exact mul_mem hj hJn
  have hκd : κ (j * e * j⁻¹ * e⁻¹) ≠ 0 := by
    have : j * e * j⁻¹ * e⁻¹ = j * (e * j⁻¹ * e⁻¹) := by group
    rw [this, hκ.add j hj _ hJn, hκ.act e heH j⁻¹ (inv_mem hj), hκ.kappa_inv hj, hjv]
    intro h0
    exact hv (eq_of_add_eq_zero_V h0).symm
  refine ⟨j, hj, fun h1 => hκd ?_, fun h1 => hκd ?_⟩
  · rw [h1, mul_inv_cancel, hκ.kappa_one]
  · rw [h1, show e * z * e⁻¹ = z by rw [H_mul_z_comm heH]; group]
    exact (hκ.eq_zero_iff z (z_mem_J_A h)).mpr (Or.inr rfl)

theorem spinFixE_generated (h : Tim79a.ParrottHypA z) (hκ : IsSpinCoord (qH D) κ) {e : G}
    (he : e ∈ spinFixE hκ) (heJ : e ∉ J z) :
    Subgroup.closure ({z} ∪ {y : G | ∃ n ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z,
      y = n * e * n⁻¹}) = spinFixE hκ := by
  classical
  have hz1 := z_ne_one_A h
  have hz2 := z_mul_self_A h
  have heH : e ∈ H z := spinFixE_le_H hκ he
  set Y : Set G := {z} ∪ {y : G | ∃ n ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z,
      y = n * e * n⁻¹} with hY
  set C : Subgroup G := Subgroup.closure Y with hC
  have hzC : z ∈ C := Subgroup.subset_closure (Or.inl rfl)
  have hCE : C ≤ spinFixE hκ := by
    rw [hC, Subgroup.closure_le]
    rintro y (hy | ⟨n, hn, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hy]
      exact z_mem_spinFixE h hκ
    · exact (mem_normalizer_iff.mp (Subgroup.mem_inf.mp hn).1 e).mp he
  have hCnorm : ∀ n ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z, ∀ c ∈ C,
      n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨n', hn', rfl⟩
      · rw [Set.mem_singleton_iff.mp hy, H_mul_z_comm (Subgroup.mem_inf.mp hn).2]
        simpa using hzC
      · exact Subgroup.subset_closure (Or.inr ⟨n * n', mul_mem hn hn', by group⟩)
    | one => simp
    | mul a b _ _ ha hb =>
      have : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ha
  refine le_antisymm hCE ?_
  have hS : sQA45 ≤ (C.subgroupOf (H z)).map (qH D) := by
    have hs₀ : qH D ⟨e, heH⟩ ∈ sQA45 := qH_mem_sQA45_of_mem_spinFixE hκ heH he
    have hs₁ : qH D ⟨e, heH⟩ ≠ 1 := fun h1 => heJ ((hκ.eq_one_iff ⟨e, heH⟩).mp h1)
    refine (sQA45_le_closure_normalizer_conj _ hs₀ hs₁).trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n₀, hn₀⟩ := hκ.surjective a
    have hn₀N : (n₀ : G) ∈ Subgroup.normalizer (spinFixE hκ : Set G) :=
      (mem_normalizer_spinFixE_iff h hκ n₀.2).mpr (by
        have : qH D ⟨(n₀ : G), n₀.2⟩ = a := hn₀
        rw [this]
        exact ha)
    have hmemY : (n₀ : G) * e * (n₀ : G)⁻¹ ∈ C :=
      Subgroup.subset_closure (Or.inr ⟨n₀, Subgroup.mem_inf.mpr ⟨hn₀N, n₀.2⟩, rfl⟩)
    refine ⟨⟨(n₀ : G) * e * (n₀ : G)⁻¹, mul_mem (mul_mem n₀.2 heH) (inv_mem n₀.2)⟩,
      Subgroup.mem_subgroupOf.mpr hmemY, ?_⟩
    have h3 : (⟨(n₀ : G) * e * (n₀ : G)⁻¹, mul_mem (mul_mem n₀.2 heH) (inv_mem n₀.2)⟩ :
        ↥(H z)) = n₀ * ⟨e, heH⟩ * n₀⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv, hn₀]
  let Kc : AddSubgroup V :=
    { carrier := {v | ∃ d ∈ C ⊓ J z, κ d = v}
      zero_mem' := ⟨1, one_mem _, hκ.kappa_one⟩
      add_mem' := fun {a b} ha hb => by
        obtain ⟨d, hd, rfl⟩ := ha
        obtain ⟨d', hd', rfl⟩ := hb
        exact ⟨d * d', mul_mem hd hd', hκ.add d (Subgroup.mem_inf.mp hd).2 d'
          (Subgroup.mem_inf.mp hd').2⟩
      neg_mem' := fun {a} ha => by
        obtain ⟨d, hd, rfl⟩ := ha
        refine ⟨d⁻¹, inv_mem hd, ?_⟩
        rw [hκ.kappa_inv (Subgroup.mem_inf.mp hd).2]
        exact (neg_eq_of_add_eq_zero_right (spinV_add_self (κ d))).symm }
  have hKc : spinFixS ≤ Kc := by
    refine spinFixS_le_closure_commutators.trans ((AddSubgroup.closure_le _).mpr ?_)
    rintro _ ⟨s', hs', v, rfl⟩
    obtain ⟨y', hy', hψ⟩ := hS hs'
    obtain ⟨j, hj, hjv⟩ := hκ.surj v
    have hcC : y'.1 ∈ C := Subgroup.mem_subgroupOf.mp hy'
    have hjn : j ∈ Subgroup.normalizer (spinFixE hκ : Set G) ⊓ H z :=
      Subgroup.mem_inf.mpr ⟨J_le_normalizer_spinFixE h hκ hj, J_le_H hj⟩
    have h1 : j * y'.1 * j⁻¹ ∈ C := hCnorm j hjn _ hcC
    have hJn : y'.1 * j⁻¹ * y'.1⁻¹ ∈ J z :=
      (mem_normalizer_iff.mp (J_le_normalizer_A y'.2) j⁻¹).mp (inv_mem hj)
    have hd : j * (y'.1 * j⁻¹ * y'.1⁻¹) ∈ J z := mul_mem hj hJn
    have hdC : j * (y'.1 * j⁻¹ * y'.1⁻¹) ∈ C := by
      have : j * (y'.1 * j⁻¹ * y'.1⁻¹) = (j * y'.1 * j⁻¹) * y'.1⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem hcC)
    refine ⟨_, Subgroup.mem_inf.mpr ⟨hdC, hd⟩, ?_⟩
    rw [hκ.add j hj _ hJn, hκ.act y'.1 y'.2 j⁻¹ (inv_mem hj), hκ.kappa_inv hj, hjv]
    have : qH D ⟨y'.1, y'.2⟩ = s' := hψ
    rw [this, add_comm]
  have hF : spinFixF hκ ≤ C := by
    intro f hf
    obtain ⟨d, hd, hdf⟩ := hKc hf.2
    rcases (hκ.kappa_eq_iff (Subgroup.mem_inf.mp hd).2 hf.1).mp hdf.symm with e1 | e1
    · rw [e1]
      exact (Subgroup.mem_inf.mp hd).1
    · rw [e1]
      exact mul_mem (Subgroup.mem_inf.mp hd).1 hzC
  intro x hx
  have hxH : x ∈ H z := spinFixE_le_H hκ hx
  obtain ⟨y', hy', hψ⟩ := hS (qH_mem_sQA45_of_mem_spinFixE hκ hxH hx)
  have hcC : y'.1 ∈ C := Subgroup.mem_subgroupOf.mp hy'
  have hcJ : y'.1⁻¹ * x ∈ J z := by
    rw [← hκ.eq_one_iff ⟨y'.1⁻¹ * x, mul_mem (inv_mem y'.2) hxH⟩]
    have h3 : (⟨y'.1⁻¹ * x, mul_mem (inv_mem y'.2) hxH⟩ : ↥(H z)) = y'⁻¹ * ⟨x, hxH⟩ := rfl
    rw [h3, map_mul, map_inv, hψ, inv_mul_cancel]
  have hcE : y'.1⁻¹ * x ∈ spinFixE hκ := mul_mem (inv_mem (hCE hcC)) hx
  have hcF : y'.1⁻¹ * x ∈ spinFixF hκ := by
    rw [← spinFixE_inf_J hκ hz1]
    exact Subgroup.mem_inf.mpr ⟨hcE, hcJ⟩
  have : x = y'.1 * (y'.1⁻¹ * x) := by group
  rw [this]
  exact mul_mem hcC (hF hcF)

end Generation

end CFSG.RankThree.GF2n.Parrott
