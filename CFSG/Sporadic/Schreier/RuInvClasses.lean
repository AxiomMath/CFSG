module

public import CFSG.Sporadic.Schreier.RuInvS
public import CFSG.Sporadic.Schreier.RuOuter

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem exists_conj_mem_ruS
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    ∃ g ∈ ruP, g * t * g⁻¹ ∈ ruS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : ruP := ⟨t, ht⟩
  have hp : IsPGroup 2 (Subgroup.zpowers t') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, pow_one]
    exact h2)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ruP Q ruSylow
  have hmem : MulAut.conj g • t' ∈ (ruSylow : Subgroup ruP) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers t'))
  rw [ruSylow_coe, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  exact ⟨g, g.2, by simpa [t'] using hmem⟩

theorem conj_ruZ_ncard
    {g : Equiv.Perm (Fin 4060)} : (fixSet (g * ruZ * g⁻¹)).ncard = 92 := by
  rw [ncard_fixSet_conj]
  exact ruFixSet_ncard

theorem conj_ruA0_ncard
    {g : Equiv.Perm (Fin 4060)} : (fixSet (g * ruA0 * g⁻¹)).ncard = 0 := by
  rw [ncard_fixSet_conj]
  exact fixSet_ruA0

theorem disjoint_ruZP_ruAP :
    Disjoint ruZP ruAP := by
  rw [Set.disjoint_left]
  rintro t ⟨g, -, rfl⟩ ⟨h, -, he⟩
  have h1 := conj_ruZ_ncard (g := g)
  rw [← he, conj_ruA0_ncard] at h1
  norm_num at h1

theorem ruA0_not_mem_ruZP :
    ruA0 ∉ ruZP := fun h =>
  Set.disjoint_left.1 disjoint_ruZP_ruAP h (self_mem_conjSet ruP ruA0)

theorem orderOf_of_mem_ruZP
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruZP) : orderOf t = 2 := by
  obtain ⟨g, -, rfl⟩ := ht
  rw [orderOf_conj', orderOf_ruZ]

theorem orderOf_of_mem_ruAP
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruAP) : orderOf t = 2 := by
  obtain ⟨g, -, rfl⟩ := ht
  rw [orderOf_conj', orderOf_ruA0]

theorem mem_ruP_of_mem_ruZP {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruZP) : t ∈ ruP := by
  obtain ⟨g, hg, rfl⟩ := ht
  exact ruP.mul_mem (ruP.mul_mem hg ruZ_mem) (ruP.inv_mem hg)

theorem mem_ruP_of_mem_ruAP {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruAP) : t ∈ ruP := by
  obtain ⟨g, hg, rfl⟩ := ht
  exact ruP.mul_mem (ruP.mul_mem hg ruA0_mem) (ruP.inv_mem hg)

theorem conj_inv_mem {H : Subgroup (Equiv.Perm (Fin 4060))} {x t g : Equiv.Perm (Fin 4060)}
    (hg : g ∈ H) (h : g * t * g⁻¹ ∈ conjSet H x) : t ∈ conjSet H x := by
  have := conj_mem_conjSet h (H.inv_mem hg)
  simpa [mul_assoc] using this

theorem ruInvolutions_eq :
    {t | t ∈ ruP ∧ orderOf t = 2} = ruZP ∪ ruAP := by
  ext t
  constructor
  · rintro ⟨ht, h2⟩
    obtain ⟨g, hg, hS⟩ := exists_conj_mem_ruS ht h2
    have hinv : g * t * g⁻¹ ∈ ruInvS := ⟨hS, by rw [orderOf_conj', h2]⟩
    rw [ruInvS_eq] at hinv
    rcases hinv with ((hz | h1) | h2') | h3
    · exact Or.inl (conj_inv_mem hg hz.2.2)
    all_goals
      right
      refine conj_inv_mem hg ?_
    · obtain ⟨s, hs, he⟩ := h1
      rw [← he, ← ruFusH_conj (by decide)]
      exact ⟨s * ruFusH 1, ruP.mul_mem (ruS_le hs) (ruFusH_mem 1), by group⟩
    · obtain ⟨s, hs, he⟩ := h2'
      rw [← he, ← ruFusH_conj (by decide)]
      exact ⟨s * ruFusH 2, ruP.mul_mem (ruS_le hs) (ruFusH_mem 2), by group⟩
    · obtain ⟨s, hs, he⟩ := h3
      rw [← he, ← ruFusH_conj (by decide)]
      exact ⟨s * ruFusH 3, ruP.mul_mem (ruS_le hs) (ruFusH_mem 3), by group⟩
  · rintro (h | h)
    · exact ⟨mem_ruP_of_mem_ruZP h, orderOf_of_mem_ruZP h⟩
    · exact ⟨mem_ruP_of_mem_ruAP h, orderOf_of_mem_ruAP h⟩

theorem ncard_ruZP :
    ruZP.ncard = 593775 := by
  show (conjSet ruP ruZ).ncard = 593775
  have h := ncard_conjSet_mul_card ruP ruZ
  rw [← ruC_eq_centralizer, card_ruC, card_ruP] at h
  have h' : (conjSet ruP ruZ).ncard * 245760 = 593775 * 245760 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

abbrev ruZ' : ruP := ⟨ruZ, ruZ_mem⟩

theorem ruZ'_mem_sylow :
    ruZ' ∈ (ruSylow : Subgroup ruP) := by
  rw [ruSylow_coe, Subgroup.mem_subgroupOf]
  exact ruZ_memS

theorem ruZ'_comm
    {s : ruP} (hs : s ∈ (ruSylow : Subgroup ruP)) : ruZ' * s = s * ruZ' := by
  rw [ruSylow_coe, Subgroup.mem_subgroupOf] at hs
  have hz : ruZ ∈ (Subgroup.center ruS).map ruS.subtype := by
    rw [center_ruS]
    exact Subgroup.mem_zpowers _
  obtain ⟨y, hy, hyz⟩ := hz
  have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨s, hs⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this hyz ⊢
  rw [← hyz]
  exact this.symm

theorem eq_ruZ'_of_central
    {y : ruP} (hy : y ∈ (ruSylow : Subgroup ruP))
    (hc : ∀ s ∈ (ruSylow : Subgroup ruP), y * s = s * y) (h1 : y ≠ 1) : y = ruZ' := by
  rw [ruSylow_coe] at hy hc
  have hcen : (y : ruP) ∈ ((Subgroup.center ruSP).map ruSP.subtype : Subgroup ruP) :=
    ⟨⟨y, hy⟩, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hc s s.2).symm, rfl⟩
  rw [ruSP_center, Subgroup.mem_subgroupOf, mem_zpowers_ruZ] at hcen
  rcases hcen with h | h
  · exact absurd (Subtype.ext h) h1
  · exact Subtype.ext h

theorem mulAut_ruZ'_mem
    (φ : MulAut ruP) : ((φ ruZ' : ruP) : Equiv.Perm (Fin 4060)) ∈ ruZP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ruP ruSylow (φ • ruSylow)
  have hφS : ∀ s, s ∈ ((φ • ruSylow : Sylow 2 ruP) : Subgroup ruP) ↔
      φ⁻¹ s ∈ (ruSylow : Subgroup ruP) := by
    intro s
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  have hgS : ∀ s, s ∈ ((φ • ruSylow : Sylow 2 ruP) : Subgroup ruP) ↔
      g⁻¹ * s * g ∈ (ruSylow : Subgroup ruP) := by
    intro s
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  set y : ruP := g⁻¹ * φ ruZ' * g with hy
  have hyS : y ∈ (ruSylow : Subgroup ruP) := (hgS _).1 ((hφS _).2 (by
    rw [MulAut.inv_apply_self]
    exact ruZ'_mem_sylow))
  have hyc : ∀ s ∈ (ruSylow : Subgroup ruP), y * s = s * y := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ ((φ • ruSylow : Sylow 2 ruP) : Subgroup ruP) :=
      (hgS _).2 (by simpa [mul_assoc] using hs)
    set u : ruP := φ⁻¹ (g * s * g⁻¹) with hu_def
    have hφu : φ u = g * s * g⁻¹ := by
      rw [hu_def]
      exact MulAut.apply_inv_self ruP φ (g * s * g⁻¹)
    have hc := ruZ'_comm ((hφS _).1 hs')
    have hc' : φ ruZ' * (g * s * g⁻¹) = (g * s * g⁻¹) * φ ruZ' := by
      calc φ ruZ' * (g * s * g⁻¹) = φ ruZ' * φ u := by rw [hφu]
        _ = φ (ruZ' * u) := (map_mul φ _ _).symm
        _ = φ (u * ruZ') := by rw [hc]
        _ = φ u * φ ruZ' := map_mul φ _ _
        _ = (g * s * g⁻¹) * φ ruZ' := by rw [hφu]
    rw [hy]
    calc g⁻¹ * φ ruZ' * g * s = g⁻¹ * (φ ruZ' * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * φ ruZ') * g := by rw [hc']
      _ = s * (g⁻¹ * φ ruZ' * g) := by group
  have hy1 : y ≠ 1 := by
    rw [hy]
    intro h
    have h' : φ ruZ' = 1 := by
      calc φ ruZ' = g * (g⁻¹ * φ ruZ' * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [map_eq_one_iff φ φ.injective] at h'
    exact ruZ_ne_one (congrArg Subtype.val h')
  have hyz := eq_ruZ'_of_central hyS hyc hy1
  refine ⟨g, g.2, ?_⟩
  have : φ ruZ' = g * ruZ' * g⁻¹ := by
    calc φ ruZ' = g * (g⁻¹ * φ ruZ' * g) * g⁻¹ := by group
      _ = g * ruZ' * g⁻¹ := by rw [← hy, hyz]
  rw [this]
  rfl

theorem mulAut_ruZP
    (φ : MulAut ruP) {t : ruP} (ht : (t : Equiv.Perm (Fin 4060)) ∈ ruZP) :
    ((φ t : ruP) : Equiv.Perm (Fin 4060)) ∈ ruZP := by
  obtain ⟨h, hh, he⟩ := ht
  have e : t = ⟨h, hh⟩ * ruZ' * (⟨h, hh⟩ : ruP)⁻¹ := Subtype.ext he.symm
  rw [e, map_mul, map_mul, map_inv]
  exact conj_mem_conjSet (mulAut_ruZ'_mem φ) (φ ⟨h, hh⟩).2

theorem mulAut_ruZP_iff
    (φ : MulAut ruP) (t : ruP) :
    ((φ t : ruP) : Equiv.Perm (Fin 4060)) ∈ ruZP ↔ (t : Equiv.Perm (Fin 4060)) ∈ ruZP := by
  refine ⟨fun h => ?_, mulAut_ruZP φ⟩
  have := mulAut_ruZP φ⁻¹ h
  rwa [MulAut.inv_apply_self] at this

theorem mulAut_ruAP_iff
    (φ : MulAut ruP) (t : ruP) :
    ((φ t : ruP) : Equiv.Perm (Fin 4060)) ∈ ruAP ↔ (t : Equiv.Perm (Fin 4060)) ∈ ruAP := by
  have key : ∀ u : ruP, (u : Equiv.Perm (Fin 4060)) ∈ ruAP ↔
      orderOf u = 2 ∧ (u : Equiv.Perm (Fin 4060)) ∉ ruZP := by
    intro u
    constructor
    · intro h
      exact ⟨by rw [← Subgroup.orderOf_coe]; exact orderOf_of_mem_ruAP h,
        fun hz => Set.disjoint_left.1 disjoint_ruZP_ruAP hz h⟩
    · rintro ⟨h2, hz⟩
      have hu : (u : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
        ⟨u.2, by rw [Subgroup.orderOf_coe]; exact h2⟩
      rw [ruInvolutions_eq] at hu
      exact hu.resolve_left hz
  rw [key, key, MulEquiv.orderOf_eq, mulAut_ruZP_iff]

theorem orderOf_eq_fourteen {G : Type*} [Monoid G] {x : G} (h14 : x ^ 14 = 1) (h7 : x ^ 7 ≠ 1)
    (h2 : x ^ 2 ≠ 1) : orderOf x = 14 := by
  have hd := orderOf_dvd_of_pow_eq_one h14
  have hmem : orderOf x ∈ Nat.divisors 14 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have e : Nat.divisors 14 = {1, 2, 7, 14} := by decide
  rw [e] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · rw [orderOf_eq_one_iff] at h
    exact absurd (by rw [h, one_pow]) h7
  · exact absurd (h ▸ pow_orderOf_eq_one x) h2
  · exact absurd (h ▸ pow_orderOf_eq_one x) h7
  · exact h

theorem ne_one_of_eqA {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : eqA 4060 t (idA 4060) = false) : g ≠ 1 := fun hg => by
  rw [(eqA_iff ht rep_idA).2 hg] at h
  exact Bool.false_ne_true h.symm

theorem ruSeed_relations :
    ruA0 ^ 2 = 1 ∧ ruA0 ≠ 1 ∧ ruA1 ^ 4 = 1 ∧ ruA1 ^ 2 ≠ 1 ∧ (ruA0 * ruA1) ^ 13 = 1 ∧
    orderOf (ruA0 * ruA1 ^ 2) = 14 ∧ (ruA0 * ruA1 * ruA0 * ruA1 ^ 2) ^ 29 = 1 ∧
    ruA0 * ruA1 ≠ ruA1 * ruA0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h2, h13, h14, h7, h2', h29, hab⟩ :=
    ruInv_check
  have hab2 : Rep 4060 ruAB2A (ruA0 * ruA1 ^ 2) := rep_compA rep_ruA0 (rep_powA rep_ruA1 2)
  refine ⟨by rw [pow_two]; exact ruA0_sq, ruA0_ne_one,
    eq_of_eqA (rep_powA rep_ruA1 4) rep_idA h4, ne_one_of_eqA (rep_powA rep_ruA1 2) h2,
    eq_of_eqA (rep_powA (rep_compA rep_ruA0 rep_ruA1) 13) rep_idA h13,
    orderOf_eq_fourteen (eq_of_eqA (rep_powA hab2 14) rep_idA h14)
      (ne_one_of_eqA (rep_powA hab2 7) h7) (ne_one_of_eqA (rep_powA hab2 2) h2'),
    eq_of_eqA (rep_powA (rep_compA (rep_compA (rep_compA rep_ruA0 rep_ruA1) rep_ruA0)
      (rep_powA rep_ruA1 2)) 29) rep_idA h29, fun h => ?_⟩
  rw [(eqA_iff (rep_compA rep_ruA0 rep_ruA1) (rep_compA rep_ruA1 rep_ruA0)).2 h] at hab
  exact Bool.false_ne_true hab.symm

theorem ruA1_sq_mem :
    ruA1 ^ 2 ∈ ruZP := by
  rw [pow_two]
  exact mem_ruZP_of_ruZWit (rep_compA rep_ruA1 rep_ruA1) ruInv_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem CTUC_Ru_two_involution_classes_and_seed_relations :
    (∃ T : Sylow 2 ruP, (T : Subgroup ruP) = ruS.subgroupOf ruP) ∧ Nat.card ruS = 16384 ∧
    ((Subgroup.center ruS).map ruS.subtype : Set (Equiv.Perm (Fin 4060))) = {1, ruZ} ∧
    orderOf ruZ = 2 ∧ orderOf ruA0 = 2 ∧
    {t | t ∈ ruP ∧ orderOf t = 2} = ruZP ∪ ruAP ∧ Disjoint ruZP ruAP ∧
    ruZP.ncard = 593775 ∧
    {t | t ∈ ruS ∧ orderOf t = 2}.ncard = 687 ∧
    {t | t ∈ ruS ∧ orderOf t = 2 ∧ t ∈ ruZP}.ncard = 495 ∧
    (∀ i ∈ [1, 2, 3], (conjSet ruS (ruFusX i)).ncard = 64 ∧
      Disjoint (conjSet ruS (ruFusX i)) ruZP ∧ ruFusH i * ruA0 * (ruFusH i)⁻¹ = ruFusX i) ∧
    (∀ i ∈ [1, 2, 3], ∀ j ∈ [1, 2, 3], i ≠ j →
      Disjoint (conjSet ruS (ruFusX i)) (conjSet ruS (ruFusX j))) ∧
    {t | t ∈ ruS ∧ orderOf t = 2} = {t | t ∈ ruS ∧ orderOf t = 2 ∧ t ∈ ruZP} ∪
      conjSet ruS (ruFusX 1) ∪ conjSet ruS (ruFusX 2) ∪ conjSet ruS (ruFusX 3) ∧
    ruA0 ∉ ruZP ∧ ruA1 ^ 2 ∈ ruZP ∧
    ruA0 ^ 2 = 1 ∧ ruA0 ≠ 1 ∧ ruA1 ^ 4 = 1 ∧ ruA1 ^ 2 ≠ 1 ∧ (ruA0 * ruA1) ^ 13 = 1 ∧
    orderOf (ruA0 * ruA1 ^ 2) = 14 ∧ (ruA0 * ruA1 * ruA0 * ruA1 ^ 2) ^ 29 = 1 ∧
    ∀ φ : MulAut ruP, ∀ t : ruP,
      (((φ t : ruP) : Equiv.Perm (Fin 4060)) ∈ ruZP ↔ (t : Equiv.Perm (Fin 4060)) ∈ ruZP) ∧
      (((φ t : ruP) : Equiv.Perm (Fin 4060)) ∈ ruAP ↔ (t : Equiv.Perm (Fin 4060)) ∈ ruAP) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := ruSeed_relations
  refine ⟨⟨ruSylow, rfl⟩, card_ruS, ?_, orderOf_ruZ, orderOf_ruA0, ruInvolutions_eq,
    disjoint_ruZP_ruAP, ncard_ruZP, ncard_ruInvS, ncard_ruInvSZ,
    fun i hi => ⟨ncard_ruXClass hi, ruXClass_disjoint_ZP hi, ruFusH_conj hi⟩,
    fun i hi j hj hij => ruXClass_disjoint hi hj hij, ruInvS_eq, ruA0_not_mem_ruZP, ruA1_sq_mem,
    s1, s2, s3, s4, s5, s6, s7, fun φ t => ⟨mulAut_ruZP_iff φ t, mulAut_ruAP_iff φ t⟩⟩
  rw [center_ruS]
  ext x
  rw [SetLike.mem_coe, mem_zpowers_ruZ]
  simp

end CFSG.Sporadic.RuSchreier
