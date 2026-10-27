module

public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.Quasithin.SteinbergBMTIPairCommutation

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nq_irreducible_TI_intersection_four_witness {T L M : Subgroup G} (h : QTNQ T L M)
    (hirr : ∀ W : Subgroup G, W ≤ qtnqU L M → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W = ⊥ ∨ W = qtnqU L M)
    (hTI : ∀ x : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) x = ⊥ ∨
      CFSG.conjugate (qtnqU L M) x = qtnqU L M)
    (g : G) (hAM : ¬ CFSG.conjugate (qtnqU L M) g ≤ M)
    (h4 : 4 ≤ Nat.card ↥(CFSG.conjugate (qtnqU L M) g ⊓ M)) :
    ∃ B : Subgroup G, B ≤ CFSG.conjugate (qtnqU L M) g ⊓ M ∧ CFSG.IsElementaryAbelian 2 B ∧
      Nat.card B = 4 ∧
      ∀ b ∈ B, (∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype) → b = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := qtnqU L M with hUdef
  set A := CFSG.conjugate U g with hAdef
  obtain ⟨-, hcharV, -, -, ⟨hU1, hUM, hUn, hUel⟩, -⟩ :=
    nonquasisimple_normalizer_internal_module_properties h
  have := hcharV
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := (isElementaryAbelian_iff.mp hUel).1
  have hU2 : ∀ a ∈ U, a ^ 2 = 1 := (isElementaryAbelian_iff.mp hUel).2
  have hUp : IsPGroup 2 U := CFSG.IsElementaryAbelian.isPGroup 2 U
  have hMN : M ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  have hNU : Subgroup.normalizer (U : Set G) = M :=
    h.max_two_local.2 _ ⟨U, hU1, hUp, rfl⟩ hMN
  have hAU : A ≠ U := fun he => hAM (he ▸ hUM)
  have hAel : CFSG.IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.map _
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := (isElementaryAbelian_iff.mp hAel).2
  have hRad : ∀ r ∈ (CFSG.solvableRadical ↥L).map L.subtype, ∀ u ∈ U, r * u = u * r := by
    intro r hr u hu
    rw [← h.centralizer_eq_radical] at hr
    have hUVc : U ≤ qtnqVc M := by
      rw [hUdef, qtnqU, Subgroup.commutator_le]
      intro v hv l hl
      have hl' : l ∈ Subgroup.normalizer (qtnqVc M : Set G) :=
        (Subgroup.le_normalizer.trans
          (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
            (primeReducedAggregate M 2))) (h.l_le hl)
      have h1 : l * v⁻¹ * l⁻¹ ∈ qtnqVc M :=
        (Subgroup.mem_normalizer_iff.mp hl' v⁻¹).mp ((qtnqVc M).inv_mem hv)
      rw [commutatorElement_def]
      have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
      rw [e]
      exact (qtnqVc M).mul_mem hv h1
    exact (mem_centralizer_iff.mp hr.2 u (hUVc hu)).symm
  have hfaith : ∀ b ∈ A ⊓ M, (∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype) →
      b = 1 := by
    intro b hb hbL
    by_contra hb1
    obtain ⟨hbA, hbM⟩ := hb
    have hbU : ∀ u ∈ U, b * u * b⁻¹ ∈ U := fun u hu =>
      (Subgroup.mem_normalizer_iff.mp (hMN hbM) u).mp hu
    have hb2 : b * b = 1 := by rw [← pow_two]; exact hA2 b hbA
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    set W : Subgroup G := U ⊓ Subgroup.centralizer {b} with hW
    have hWL : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
      intro l hl w hw
      obtain ⟨hwU, hwb⟩ := hw
      have hwb' : b * w = w * b := mem_centralizer_iff.mp hwb b rfl
      have hlU : l * w * l⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hMN (h.l_le hl)) w).mp hwU
      refine ⟨hlU, mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      have hs := hbL l⁻¹ (L.inv_mem hl)
      set s := ⁅l⁻¹, b⁆ with hsdef
      have hsw : s * w = w * s := hRad s hs w hwU
      have hbl : b * l = l * s * b := by
        rw [hsdef, commutatorElement_def]
        group
      calc b * (l * w * l⁻¹) = (b * l) * w * l⁻¹ := by group
        _ = l * s * (b * w) * l⁻¹ := by rw [hbl]; group
        _ = l * (s * w) * b * l⁻¹ := by rw [hwb']; group
        _ = l * (w * s) * b * l⁻¹ := by rw [hsw]
        _ = l * w * (s * b * l⁻¹) := by group
        _ = l * w * l⁻¹ * b := by
          have hbl' : s * b * l⁻¹ = l⁻¹ * b := by
            have := congrArg (fun x => l⁻¹ * x * l⁻¹) hbl
            rw [show l⁻¹ * (b * l) * l⁻¹ = l⁻¹ * b by group,
              show l⁻¹ * (l * s * b) * l⁻¹ = s * b * l⁻¹ by group] at this
            exact this.symm
          rw [hbl']
          group
    have hW1 : W ≠ ⊥ := by
      obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
      have hu1' : u ≠ 1 := fun e => hu1 (Subtype.ext e)
      by_cases hfix : b * u * b⁻¹ = u
      · intro hbot
        have : u ∈ W := ⟨hu, mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          calc b * u = b * u * b⁻¹ * b := by group
            _ = u * b := by rw [hfix]⟩
        rw [hbot, mem_bot] at this
        exact hu1' this
      · intro hbot
        set v := b * u * b⁻¹ with hv
        have hvU : v ∈ U := hbU u hu
        have hvv : b * v * b⁻¹ = u := by
          rw [hv, hbinv]
          calc b * (b * u * b) * b = (b * b) * u * (b * b) := by group
            _ = u := by rw [hb2]; group
        have hw : u * v ∈ W := by
          refine ⟨U.mul_mem hu hvU, mem_centralizer_iff.mpr fun y hy => ?_⟩
          rw [Set.mem_singleton_iff.mp hy]
          calc b * (u * v) = (b * u * b⁻¹) * (b * v * b⁻¹) * b := by group
            _ = v * u * b := by rw [← hv, hvv]
            _ = u * v * b := by rw [hUc v hvU u hu]
        rw [hbot, mem_bot] at hw
        apply hfix
        have h1 : v = u⁻¹ := (eq_inv_of_mul_eq_one_right hw)
        have h2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u hu)
        rw [h1, h2]
    have hWU : W = U := (hirr W inf_le_left hWL).resolve_left hW1
    have hbC : b ∈ Subgroup.centralizer (U : Set G) := by
      rw [mem_centralizer_iff]
      intro u hu
      have : u ∈ W := hWU ▸ hu
      exact (mem_centralizer_iff.mp this.2 b rfl).symm
    have hCA : A ⊓ Subgroup.centralizer (U : Set G) ≠ ⊥ := by
      intro hbot
      have : b ∈ A ⊓ Subgroup.centralizer (U : Set G) := ⟨hbA, hbC⟩
      rw [hbot, mem_bot] at this
      exact hb1 this
    have hcomm := (CFSG.Quasithin.SteinbergBM.nq_elementary_TI_pair_commutation hUel hTI hAU).1 hCA
    apply hAM
    have hAC : A ≤ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact Subgroup.le_centralizer_iff.mp hcomm
    rw [← hNU]
    exact hAC.trans (Subgroup.centralizer_le_normalizer _)
  have hD2 : IsPGroup 2 ↥(A ⊓ M) := hAel.isPGroup.to_le inf_le_left
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 := by
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  obtain ⟨B, hB, -, hBD⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) Nat.prime_two
    (n := 2) (H := ⊥) (L := A ⊓ M) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 hk2) bot_le
  refine ⟨B, hBD, isElementaryAbelian_of_le (hBD.trans inf_le_left) hAel, by rw [hB]; norm_num,
    fun b hb hbL => hfaith b (hBD hb) hbL⟩

end CFSG.Quasithin.H13.NQTerm
