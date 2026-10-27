module

public import CFSG.Quasithin.H13.NQCoreFourGroup
public import CFSG.Quasithin.H13.NQRigidBridge
public import CFSG.LieType.SteinbergBRUnitaryThreePerfect
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup
open scoped commutatorElement

theorem isSolvable_of_card_dvd_two_three {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (h : Nat.card H ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem isSolvable_mulAut_of_card_le_four {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V ≤ 4) : Group.IsSolvable (MulAut V) := by
  have hinj : Function.Injective (MulAut.toPerm V) := fun a b h =>
    MulEquiv.ext fun x => congrArg (fun f : Equiv.Perm V => f x) h
  have : Finite (MulAut V) := Finite.of_injective _ hinj
  refine isSolvable_of_card_dvd_two_three (a := 3) (b := 1) ?_
  have h1 : Nat.card (MulAut V) ∣ Nat.card (Equiv.Perm V) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_perm] at h1
  exact h1.trans ((Nat.factorial_dvd_factorial hV).trans (by decide))

theorem nq_original_TI_hyperplane_conjugates_centralize_internal_module
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) :
    ⁅qtnqU L M, L⁆ = qtnqU L M ∧ 8 ≤ Nat.card (qtnqU L M) ∧
      ∀ (g : G) (B₀ : Subgroup G), B₀ ≤ CFSG.conjugate (qtnqU L M) g ⊓ T →
        B₀.relIndex (CFSG.conjugate (qtnqU L M) g) ≤ 2 →
          ⁅qtnqU L M, CFSG.conjugate (qtnqU L M) g⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨hU1, -, -, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  set U : Subgroup G := qtnqU L M with hUdef
  have hUL : ⁅U, L⁆ = U := NQRigid.commutator_qtnqU_eq h
  have hMN : M ≤ normalizer (U : Set G) := NQRigid.le_normalizer_qtnqU h
  have hLM : L ≤ M := h.l_le
  have hTM : T ≤ M := h.t_le
  obtain ⟨hUc, hU2⟩ := SteinbergBM.elementaryAbelian_two_facts hUe
  have hUp : IsPGroup 2 ↥U := by
    have := hUe
    exact IsElementaryAbelian.isPGroup 2 ↥U
  have hU8 : 8 ≤ Nat.card U := by
    by_contra hlt
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hUp
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h1 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle : Nat.card U ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    have hsolv : Group.IsSolvable (MulAut ↥U) := isSolvable_mulAut_of_card_le_four hle
    let φ : ↥L →* MulAut ↥U := U.normalizerMonoidHom.comp (Subgroup.inclusion (hLM.trans hMN))
    have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp h.maximal_local.1.2.1
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    have hφperf : ⁅φ.range, φ.range⁆ = φ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have hφ : φ.range = ⊥ := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hφperf
    apply hU1
    rw [← hUL, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [mem_centralizer_iff]
    intro l hl
    have h1 : φ ⟨l, hl⟩ = 1 := by
      have h2 : φ ⟨l, hl⟩ ∈ φ.range := ⟨⟨l, hl⟩, rfl⟩
      rw [hφ, mem_bot] at h2
      exact h2
    have h3 : φ ⟨l, hl⟩ ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [h1]; rfl
    have h4 : l * u * l⁻¹ = u := congrArg Subtype.val h3
    calc l * u = l * u * l⁻¹ * l := by group
      _ = u * l := by rw [h4]
  refine ⟨hUL, hU8, fun g B₀ hB₀ hidx => ?_⟩
  set A : Subgroup G := CFSG.conjugate U g with hA
  rcases hTI g with hUA | hAU
  swap
  ·
    rw [show A = U from hAU, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact hUc y hy x hx
  by_contra hne
  have hAe : CFSG.IsElementaryAbelian 2 A := by
    have := hUe
    exact CFSG.IsElementaryAbelian.map _
  obtain ⟨hAc, hA2⟩ := SteinbergBM.elementaryAbelian_two_facts hAe
  have hATI := SteinbergBM.conjugate_TI hTI g
  have hcardA : Nat.card A = Nat.card U := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB₀A : B₀ ≤ A := fun x hx => (hB₀ hx).1
  have hB₀N : B₀ ≤ A ⊓ normalizer (U : Set G) := fun x hx =>
    ⟨(hB₀ hx).1, hMN (hTM (hB₀ hx).2)⟩
  have hcardB₀ : B₀.relIndex A * Nat.card B₀ = Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := B₀) (K := A)
    rwa [inf_eq_left.mpr hB₀A] at h1
  have hA2B₀ : Nat.card A ≤ 2 * Nat.card B₀ := by
    rw [← hcardB₀]
    exact Nat.mul_le_mul_right _ hidx
  have hB₀4 : 4 ≤ Nat.card B₀ := by omega
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B₀, b ≠ 1 := by
    by_contra hall
    have hbot : B₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      by_contra hx1
      exact hall ⟨x, hx, hx1⟩
    rw [hbot, card_bot] at hB₀4
    omega
  have hbA : b ∈ A := (hB₀ hb).1
  have hbN : b ∈ normalizer (U : Set G) := hMN (hTM (hB₀ hb).2)
  obtain ⟨f, hfU, hf1, hbf⟩ := SteinbergBM.exists_ne_one_commute hUc hU2 hU1 hbN (hA2 b hbA)
  have hfN : f ∈ normalizer (A : Set G) :=
    SteinbergBM.mem_normalizer_of_commute_of_TI hATI hbA hb1 hbf.symm
  have hC1 : U ⊓ normalizer (A : Set G) ≠ ⊥ := by
    intro hbot
    apply hf1
    have h1 : f ∈ U ⊓ normalizer (A : Set G) := ⟨hfU, hfN⟩
    rw [hbot, mem_bot] at h1
    exact h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hUp
  obtain ⟨-, -, -, -, -, -, -, hCeq, hClt⟩ :=
    SteinbergBM.equal_rank_elementary_TI_pair_mutual_normalizer_calculus hUe hAe hn
      (hcardA.trans hn) hUA hTI hATI hC1
  have hCU : U ⊓ normalizer (A : Set G) < U :=
    lt_of_le_of_ne inf_le_left fun heq => hne (hCeq heq).2
  obtain ⟨hBA, hcardCB, -, hCb, -⟩ := hClt hCU
  have hB₀B : B₀ ≤ A ⊓ normalizer (U : Set G) := hB₀N
  have hBAle : A ⊓ normalizer (U : Set G) ≤ A := inf_le_left
  have hcardB : (A ⊓ normalizer (U : Set G)).relIndex A * Nat.card (A ⊓ normalizer (U : Set G) :
      Subgroup G) = Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := A ⊓ normalizer (U : Set G)) (K := A)
    rwa [inf_eq_left.mpr hBAle] at h1
  have hrel1 : (A ⊓ normalizer (U : Set G)).relIndex A ≠ 1 := fun h1 =>
    (lt_iff_le_not_ge.mp hBA).2 (Subgroup.relIndex_eq_one.mp h1)
  have hrel0 : (A ⊓ normalizer (U : Set G)).relIndex A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcardB
    exact (Nat.card_pos (α := ↥A)).ne' hcardB.symm
  have hB₀Bc : Nat.card B₀ ≤ Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hB₀B
  have hBpos : 0 < Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) := Nat.card_pos
  have hrel2 : (A ⊓ normalizer (U : Set G)).relIndex A = 2 := by
    have h1 : (A ⊓ normalizer (U : Set G)).relIndex A *
        Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) ≤
          2 * Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) := by
      rw [hcardB]
      omega
    have h2 := Nat.le_of_mul_le_mul_right h1 hBpos
    omega
  have hcardAB : Nat.card A = 2 * Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) := by
    rw [← hcardB, hrel2]
  have hBB₀ : B₀ = A ⊓ normalizer (U : Set G) :=
    Subgroup.eq_of_le_of_card_ge hB₀B (by omega)
  have hcardU : Nat.card U = 2 * Nat.card (U ⊓ normalizer (A : Set G) : Subgroup G) := by
    rw [← hcardA, hcardAB, hcardCB]
  have hCrel : (U ⊓ normalizer (A : Set G)).relIndex U = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := U ⊓ normalizer (A : Set G)) (K := U)
    rw [inf_eq_left.mpr inf_le_left, hcardU] at h1
    have hCpos : 0 < Nat.card (U ⊓ normalizer (A : Set G) : Subgroup G) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hCpos h1
  have hBp : IsPGroup 2 ↥(A ⊓ normalizer (U : Set G)) := by
    have := hAe
    exact (IsElementaryAbelian.isPGroup 2 ↥A).to_le inf_le_left
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hBp
  have h4B : 2 ^ 2 ∣ Nat.card (A ⊓ normalizer (U : Set G) : Subgroup G) := by
    rw [hm]
    apply pow_dvd_pow
    by_contra hm2
    have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨D₁, hD₁⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4B
  set D₀ : Subgroup G := D₁.map (A ⊓ normalizer (U : Set G)).subtype with hD₀
  have hD₀B : D₀ ≤ A ⊓ normalizer (U : Set G) := map_subtype_le _
  have hD₀M : D₀ ≤ M := fun x hx => hTM ((hB₀ (hBB₀ ▸ hD₀B hx)).2)
  have hD₀e : CFSG.IsElementaryAbelian 2 D₀ := SteinbergBM.isElementaryAbelian_two_of
    (fun x hx y hy => hAc x (hD₀B hx).1 y (hD₀B hy).1) (fun x hx => hA2 x (hD₀B hx).1)
  have hD₀4 : Nat.card D₀ = 4 := by
    rw [hD₀, card_map_of_injective (subtype_injective _), hD₁]
    norm_num
  obtain ⟨c, hcD, hc1, hcL⟩ := configuration_four_group_obstruction h D₀ hD₀M hD₀e hD₀4
  have hcB : c ∈ A ⊓ normalizer (U : Set G) := hD₀B hcD
  have hCc : U ⊓ centralizer ({c} : Set G) = U ⊓ normalizer (A : Set G) := hCb c hcB hc1
  have hrad := NQBlock.inf_centralizer_qtnqU h
  have hcomm : ∀ l ∈ L, ⁅l, c⁆ ∈ centralizer (U : Set G) := fun l hl => by
    have h1 : ⁅l, c⁆ ∈ L ⊓ centralizer (U : Set G) := by
      rw [hrad]
      exact hcL l hl
    exact h1.2
  have hcN : c ∈ normalizer (U : Set G) := hcB.2
  have hnorm : ∀ l ∈ L, ∀ u ∈ U ⊓ centralizer ({c} : Set G),
      l * u * l⁻¹ ∈ U ⊓ centralizer ({c} : Set G) := by
    intro l hl u hu
    obtain ⟨huU, huc⟩ := mem_inf.mp hu
    have hcu : c * u = u * c := (mem_centralizer_singleton_iff.mp huc).symm
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hMN (hLM hl)) u).mp huU, ?_⟩
    rw [mem_centralizer_singleton_iff]
    set d := ⁅l⁻¹, c⁆ with hd
    have hdU : d ∈ centralizer (U : Set G) := hcomm l⁻¹ (L.inv_mem hl)
    have hdu : d * u = u * d := ((mem_centralizer_iff.mp hdU) u huU).symm
    have hlcl : l⁻¹ * c * l = d * c := by
      rw [hd, commutatorElement_def]
      group
    symm
    calc c * (l * u * l⁻¹) = l * (l⁻¹ * c * l) * u * l⁻¹ := by group
      _ = l * (d * c) * u * l⁻¹ := by rw [hlcl]
      _ = l * d * (c * u) * l⁻¹ := by group
      _ = l * d * (u * c) * l⁻¹ := by rw [hcu]
      _ = l * (d * u) * c * l⁻¹ := by group
      _ = l * (u * d) * c * l⁻¹ := by rw [hdu]
      _ = l * u * (d * c) * l⁻¹ := by group
      _ = l * u * (l⁻¹ * c * l) * l⁻¹ := by rw [hlcl]
      _ = l * u * l⁻¹ * c := by group
  set C : Subgroup G := U ⊓ normalizer (A : Set G) with hCdef
  have hCidx : (C.subgroupOf U).index = 2 := hCrel
  have hmem : ∀ l ∈ L, ∀ x ∈ U, (l * x * l⁻¹ ∈ C ↔ x ∈ C) := by
    intro l hl x hx
    rw [← hCc]
    constructor
    · intro h1
      have h2 := hnorm l⁻¹ (L.inv_mem hl) _ h1
      rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at h2
    · exact hnorm l hl x
  have hle : ⁅U, L⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlu : l * u * l⁻¹ ∈ U := (mem_normalizer_iff.mp (hMN (hLM hl)) u).mp hu
    have h1 := Subgroup.mul_mem_iff_of_index_two hCidx (a := ⟨u, hu⟩)
      (b := ⟨(l * u * l⁻¹)⁻¹, U.inv_mem hlu⟩)
    have h2 : ⁅u, l⁆ = u * (l * u * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    have h3 : u * (l * u * l⁻¹)⁻¹ ∈ C ↔ (u ∈ C ↔ (l * u * l⁻¹)⁻¹ ∈ C) := h1
    rw [h2, h3, inv_mem_iff, hmem l hl u hu]
  exact (lt_iff_le_not_ge.mp hCU).2 (hUL ▸ hle)

end CFSG.Quasithin.H13.NQCore
