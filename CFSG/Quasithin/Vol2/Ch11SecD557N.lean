module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by rw [mul_one]⟩
      mul_mem' := fun {x y} ⟨a, ha, b, hb, hx⟩ ⟨a', ha', b', hb', hy⟩ => by
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        rw [hx, hy, mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]
        group
      inv_mem' := fun {x} ⟨a, ha, b, hb, hx⟩ => by
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [hx, mul_inv_rev, hAB _ (A.inv_mem ha) _ (B.inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by rw [mul_one]⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem card_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * p.2, (A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h1 : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have h2 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
        calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
          _ = q.2 * (p.2 : G)⁻¹ := by rw [h1]; group
      have h3 : (q.1 : G)⁻¹ * p.1 ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem q.1.2) p.1.2, h2 ▸ B.mul_mem q.2.2 (B.inv_mem p.2.2)⟩
      rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (p.2 : G) = q.2 := by
        have := h1
        rw [← h3] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
    · obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hAB x.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hx.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

section Action

variable {U Z K : Subgroup G}

theorem normal_subgroupOf_of_le (hZU : Z ≤ U) (hUZ : U ≤ Subgroup.normalizer (Z : Set G)) :
    (Z.subgroupOf U).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hZU).mpr hUZ

theorem map_conjAct_subgroupOf (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (k : ↥K) :
    (Z.subgroupOf U).map ((conjAct U ⟨k, hKU k.2⟩ : MulAut ↥U) : ↥U →* ↥U) =
      Z.subgroupOf U := by
  ext ⟨w, hw⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxU⟩, hx, hxw⟩
    have h1 : (k : G) * x * (k : G)⁻¹ = w := by
      have h2 := congrArg Subtype.val hxw
      simp only [MonoidHom.coe_ofClass, conjAct_coe_apply] at h2
      exact h2
    rw [← h1]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ k.2) x).mp hx
  · intro hw'
    have hu : (k : G)⁻¹ * w * (k : G) ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hKU (K.inv_mem k.2)) w).mp hw
      simpa using this
    refine ⟨⟨(k : G)⁻¹ * w * k, hu⟩, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hKZ (K.inv_mem k.2)) w).mp hw'
      simpa using this
    · apply Subtype.ext
      simp only [MonoidHom.coe_ofClass, conjAct_coe_apply]
      group

variable [(Z.subgroupOf U).Normal]

noncomputable def quotAct (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) : ↥K →* MulAut (↥U ⧸ Z.subgroupOf U) where
  toFun k := QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U)
    (conjAct U ⟨k, hKU k.2⟩) (map_conjAct_subgroupOf hKU hKZ k)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [conjAct_coe_apply]
      simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      rw [conjAct_coe_apply, conjAct_coe_apply, conjAct_coe_apply, Subgroup.coe_mul]
      group

theorem quotAct_mk (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (k : ↥K) (u : ↥U) :
    quotAct hKU hKZ k (QuotientGroup.mk u) = QuotientGroup.mk (conjAct U ⟨k, hKU k.2⟩ u) :=
  QuotientGroup.congr_mk _ _ _ (map_conjAct_subgroupOf hKU hKZ k) u

theorem quotAct_eq_one_iff (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (k : ↥K) :
    quotAct hKU hKZ k = 1 ↔ ∀ u ∈ U, (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h1 u hu
    have h2 := congrArg (fun φ : MulAut (↥U ⧸ Z.subgroupOf U) =>
      φ (QuotientGroup.mk ⟨u, hu⟩)) h1
    simp only [quotAct_mk, MulAut.one_apply] at h2
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      conjAct_coe_apply] at h2
    have h3 := (Subgroup.mem_normalizer_iff.mp (hUZ hu) _).mp (Z.inv_mem h2)
    convert h3 using 1
    group
  · intro h1
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [quotAct_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv, conjAct_coe_apply]
      have h2 := Z.inv_mem (h1 w w.2)
      have h3 := (Subgroup.mem_normalizer_iff.mp (hUZ (U.inv_mem w.2)) _).mp h2
      convert h3 using 1
      group

end Action

end CFSG.Quasithin.Vol2.Ch11.SecD
