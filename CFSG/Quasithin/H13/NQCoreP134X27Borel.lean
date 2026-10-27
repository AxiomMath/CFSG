module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Trans

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem OddConfig.false_of_comm_x27 {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (hcfg : OddConfig 3 L P T) (h27 : Nat.card P = 27)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup A) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hcfg.hyp.sqt) 3 Nat.prime_three (by norm_num)
  obtain ⟨E, hEP, hE, hE9⟩ := exists_elemAbelian_sq hcfg.exp (by rw [h27]; norm_num)
  obtain ⟨x, hxP, hxE⟩ : ∃ x ∈ P, x ∉ E := by
    by_contra hall
    push Not at hall
    have hle : Nat.card P ≤ Nat.card E := Subgroup.card_le_of_le hall
    rw [h27, hE9] at hle
    norm_num at hle
  exact false_of_commute' hrank hE hE9 hxE (hcfg.exp x hxP) fun a ha => hab a (hEP ha) x hxP

theorem false_of_borel_data_x27 {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (hcfg : OddConfig 3 L P T) (h27 : Nat.card P = 27) {C : Type} [Group C]
    (e₀ : C ≃* ↥L) {U B : Subgroup C} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hcont : ∀ H : Subgroup C, U ≤ H → Nat.card H = 27 * Nat.card U → H ≤ B)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite C := Finite.of_equiv L e₀.symm.toEquiv
  have hS := OddConfig.isSylowTwoOf_inf hcfg
  have hcardsub : ∀ {S : Subgroup A}, S ≤ L → Nat.card (S.subgroupOf L) = Nat.card S :=
    fun h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  obtain ⟨e, he⟩ := G2.exists_mulEquiv_map_sylow_eq e₀ (hUp.toSylow hUi)
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace he : U.map e.toMonoidHom = (T ⊓ L).subgroupOf L := he
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have he_surj : Function.Surjective e.toMonoidHom := e.surjective
  have hcardU' : Nat.card ((T ⊓ L).subgroupOf L) = Nat.card U := by
    rw [← he, Subgroup.card_map_of_injective he_inj]
  have hcomap : ∀ S : Subgroup L, Nat.card (S.comap e.toMonoidHom) = Nat.card S := by
    intro S
    rw [← Subgroup.card_map_of_injective he_inj,
      Subgroup.map_comap_eq_self_of_surjective he_surj]
  set PC := (P.subgroupOf L).comap e.toMonoidHom with hPC
  set HC := ((P ⊔ T ⊓ L).subgroupOf L).comap e.toMonoidHom with hHC
  have hPHC : PC ≤ HC := fun x hx => by
    change ((e x : L) : A) ∈ P ⊔ T ⊓ L
    exact le_sup_left (α := Subgroup A) hx
  have hPCcard : Nat.card PC = 27 := by
    rw [hPC, hcomap, hcardsub hcfg.le, h27]
  have hUHC : U ≤ HC := fun u hu => by
    have h1 : e u ∈ (T ⊓ L).subgroupOf L := he ▸ Subgroup.mem_map_of_mem e.toMonoidHom hu
    change ((e u : L) : A) ∈ P ⊔ T ⊓ L
    exact le_sup_right (α := Subgroup A) h1
  have hHCcard : Nat.card HC = 27 * Nat.card U := by
    rw [hHC, hcomap, hcardsub (OddConfig.sup_inf_le hcfg), OddConfig.card_sup_inf_x27 hcfg h27,
      ← hcardU', hcardsub (inf_le_right : T ⊓ L ≤ L)]
  have hHB : HC ≤ B := hcont HC hUHC hHCcard
  have hmemPC : ∀ x : L, (x : A) ∈ P → e.symm x ∈ PC := fun x hx => by
    change ((e (e.symm x) : L) : A) ∈ P
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have hdisj : Disjoint PC U := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hPCcard]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hUp
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  refine hcfg.false_of_comm_x27 h27 fun x hx y hy => ?_
  have hxC := hmemPC ⟨x, hcfg.le hx⟩ hx
  have hyC := hmemPC ⟨y, hcfg.le hy⟩ hy
  have h1 := Subgroup.disjoint_def.1 hdisj
    (PC.mul_mem (PC.mul_mem (PC.mul_mem hxC hyC) (PC.inv_mem hxC)) (PC.inv_mem hyC))
    (hcomm _ (hHB (hPHC hxC)) _ (hHB (hPHC hyC)))
  have h2 := congrArg e h1
  simp only [map_mul, map_inv, map_one, MulEquiv.apply_symm_apply] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem two_pow_add_one_ne_27 (n : ℕ) : 2 ^ n + 1 ≠ 3 ^ 3 := by
  intro h
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> norm_num at h
  · have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
    omega

end CFSG.Quasithin.H13.NQCore
