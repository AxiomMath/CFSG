module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEnds
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

@[expose] def f4ChiA : Fin 4 → Equiv.Perm (Fin 3) := ![Equiv.swap 0 1, Equiv.swap 1 2, 1, 1]

@[expose] def f4ChiB : Fin 4 → Equiv.Perm (Fin 3) := ![1, 1, Equiv.swap 0 1, Equiv.swap 1 2]

theorem f4ChiA_liftable : CoxeterMatrix.F₄.IsLiftable f4ChiA := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem f4ChiB_liftable : CoxeterMatrix.F₄.IsLiftable f4ChiB := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem f4Chi_eq_one_or (i : Fin 4) : f4ChiA i = 1 ∨ f4ChiB i = 1 := by
  fin_cases i <;> decide

theorem ggF4Ends_map_eq_one_of_braid {H Q : Type*} [Group H] [Group Q] (χ : H →* Q) {s t : H}
    (ht : t ^ 2 = 1) (hst : (s * t) ^ 3 = 1) (hs : χ s = 1) : χ t = 1 := by
  have h2 : χ t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have h3 : χ t ^ 3 = 1 := by
    have h := congrArg χ hst
    rwa [map_pow, map_mul, hs, one_mul, map_one] at h
  calc χ t = χ t ^ 3 * (χ t ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, one_mul]

theorem ggF4Ends_range_eq_top_of_swaps {H : Type*} [Group H] (χ : H →* Equiv.Perm (Fin 3)) {a b : H}
    (ha : χ a = Equiv.swap 0 1) (hb : χ b = Equiv.swap 1 2) : χ.range = ⊤ := by
  have ho2 : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have ho3 : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have h2 : 2 ∣ Nat.card χ.range := by
    have h := Subgroup.orderOf_dvd_natCard χ.range (⟨a, rfl⟩ : χ a ∈ χ.range)
    rwa [ha, ho2] at h
  have h3 : 3 ∣ Nat.card χ.range := by
    have h := Subgroup.orderOf_dvd_natCard χ.range (⟨a * b, rfl⟩ : χ (a * b) ∈ χ.range)
    rwa [map_mul, ha, hb, ho3] at h
  have h6 : 6 ∣ Nat.card χ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have htop : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hle : Nat.card χ.range ≤ 6 := htop ▸ Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card χ.range := Nat.card_pos
  apply Subgroup.eq_top_of_card_eq
  rw [htop]
  obtain ⟨k, hk⟩ := h6
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

section A3


theorem ggF4Ends_false_of_A3_join {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {AL AK : Subgroup (MulAut ↥Bs)} (hind : AL ⊔ AK ≤ ggInduced ⊤ Bs)
    (hW : GGWeylOfType p CoxeterMatrix.F₄ (AL ⊔ AK))
    (hAL : GGWeylOfType p (CoxeterMatrix.A 3) AL) (hAK : GGWeylReflectionGroup p AK)
    (h3 : ∃ a ∈ AL ⊓ AK, orderOf a = 3)
    (hfix : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ φ ∈ AK, φ b = b)
    (hfixA : ∀ b : ↥Bs, (∀ φ ∈ AL ⊔ AK, φ b = b) → b = 1) : False := by
  classical
  have hcardA : Nat.card ↥(AL ⊔ AK) = 1152 := ggF4Orig_card_weylOfType_F4 hW
  obtain ⟨e, he⟩ := hW
  have hWeyl : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
      (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    have h := Fintype.card_congr e'
    simp at h
  have hrefl := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT (AL ⊔ AK)
    hind (Fin 4) CoxeterMatrix.F₄ hWeyl hG2 e he
  let χA : ↥(AL ⊔ AK) →* Equiv.Perm (Fin 3) :=
    (CoxeterMatrix.F₄.toCoxeterSystem.lift ⟨f4ChiA, f4ChiA_liftable⟩).comp e.symm.toMonoidHom
  let χB : ↥(AL ⊔ AK) →* Equiv.Perm (Fin 3) :=
    (CoxeterMatrix.F₄.toCoxeterSystem.lift ⟨f4ChiB, f4ChiB_liftable⟩).comp e.symm.toMonoidHom
  have hχA : ∀ i, χA (e (CoxeterMatrix.F₄.simple i)) = f4ChiA i := by
    intro i
    simp only [χA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      ← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  have hχB : ∀ i, χB (e (CoxeterMatrix.F₄.simple i)) = f4ChiB i := by
    intro i
    simp only [χB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      ← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  have hclass : ∀ a : ↥(AL ⊔ AK), GGIsReflection p (a : MulAut ↥Bs) → χA a = 1 ∨ χB a = 1 := by
    intro a ha
    obtain ⟨i, g, rfl⟩ := hrefl a ha
    rcases f4Chi_eq_one_or i with hi | hi
    · left
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hχA, hi, mul_one,
        mul_inv_cancel]
    · right
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hχB, hi, mul_one,
        mul_inv_cancel]
  have hsurjA : χA.range = ⊤ := ggF4Ends_range_eq_top_of_swaps χA (hχA 0) (hχA 1)
  have hsurjB : χB.range = ⊤ := ggF4Ends_range_eq_top_of_swaps χB (hχB 2) (hχB 3)
  obtain ⟨eL, heL⟩ := hAL
  have hLA : AL ≤ AL ⊔ AK := le_sup_left
  let ρ : Fin 3 → ↥(AL ⊔ AK) := fun i =>
    Subgroup.inclusion hLA (eL ((CoxeterMatrix.A 3).simple i))
  have hρ : ∀ (i : Fin 3) (k : ℕ),
      ρ i ^ k = Subgroup.inclusion hLA (eL ((CoxeterMatrix.A 3).simple i ^ k)) := by
    intro i k
    simp only [ρ, map_pow]
  have hρsq : ∀ i, ρ i ^ 2 = 1 := by
    intro i
    rw [hρ, ← CoxeterMatrix.toCoxeterSystem_simple,
      (CoxeterMatrix.A 3).toCoxeterSystem.simple_sq i, map_one, map_one]
  have hbraid : ∀ i j : Fin 3, (CoxeterMatrix.A 3) i j = 3 → (ρ i * ρ j) ^ 3 = 1 := by
    intro i j hij
    have h := (CoxeterMatrix.A 3).toCoxeterSystem.simple_mul_simple_pow i j
    rw [hij, CoxeterMatrix.toCoxeterSystem_simple] at h
    simp only [ρ, ← map_mul, ← map_pow, h, map_one]
  have h01 : (CoxeterMatrix.A 3) 0 1 = 3 := by decide
  have h12 : (CoxeterMatrix.A 3) 1 2 = 3 := by decide
  have hkill : ∀ χ : ↥(AL ⊔ AK) →* Equiv.Perm (Fin 3), χ (ρ 0) = 1 →
      ∀ a : ↥(AL ⊔ AK), (a : MulAut ↥Bs) ∈ AL → χ a = 1 := by
    intro χ h0 a ha
    have h1 := ggF4Ends_map_eq_one_of_braid χ (hρsq 1) (hbraid 0 1 h01) h0
    have h2 := ggF4Ends_map_eq_one_of_braid χ (hρsq 2) (hbraid 1 2 h12) h1
    have hψ : χ.comp ((Subgroup.inclusion hLA).comp eL.toMonoidHom) = 1 := by
      apply (CoxeterMatrix.A 3).toCoxeterSystem.ext_simple
      intro i
      rw [CoxeterMatrix.toCoxeterSystem_simple, MonoidHom.one_apply]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hc := DFunLike.congr_fun hψ (eL.symm ⟨a, ha⟩)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.one_apply] at hc
    rwa [show Subgroup.inclusion hLA ⟨(a : MulAut ↥Bs), ha⟩ = a from Subtype.ext rfl] at hc
  obtain ⟨χ, hχL, hχtop⟩ : ∃ χ : ↥(AL ⊔ AK) →* Equiv.Perm (Fin 3),
      (∀ a : ↥(AL ⊔ AK), (a : MulAut ↥Bs) ∈ AL → χ a = 1) ∧ χ.range = ⊤ := by
    rcases hclass (ρ 0) (heL 0) with h | h
    · exact ⟨χA, hkill χA h, hsurjA⟩
    · exact ⟨χB, hkill χB h, hsurjB⟩
  let AL' : Subgroup ↥(AL ⊔ AK) := AL.subgroupOf (AL ⊔ AK)
  let AK' : Subgroup ↥(AL ⊔ AK) := AK.subgroupOf (AL ⊔ AK)
  have hsup : AL' ⊔ AK' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hmapL : AL'.map χ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro a ha
    exact hχL a (Subgroup.mem_subgroupOf.mp ha)
  have hmapK : AK'.map χ = ⊤ := by
    have h := congrArg (Subgroup.map χ) hsup
    rwa [Subgroup.map_sup, hmapL, bot_sup_eq, ← MonoidHom.range_eq_map, hχtop] at h
  let χK : ↥AK' →* Equiv.Perm (Fin 3) := χ.comp AK'.subtype
  have hrangeK : χK.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmapK]
  have hcardR : Nat.card χK.range = 6 := by
    rw [hrangeK, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨a, ⟨haL, haK⟩, ha3⟩ := h3
  let a' : ↥AK' := ⟨⟨a, Subgroup.mem_sup_right haK⟩, Subgroup.mem_subgroupOf.mpr haK⟩
  have ha'ker : a' ∈ χK.ker := hχL _ haL
  have hord : orderOf a' = 3 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact ha3
  have h3ker : 3 ∣ Nat.card χK.ker := by
    have h := Subgroup.orderOf_dvd_natCard χK.ker ha'ker
    rwa [hord] at h
  have hcardK' : Nat.card ↥AK' = Nat.card χK.ker * 6 := by
    rw [← hcardR, Subgroup.card_eq_card_quotient_mul_card_subgroup χK.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χK).toEquiv, mul_comm]
  have hcardK : Nat.card ↥AK = Nat.card ↥AK' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv).symm
  have h18 : 18 ∣ Nat.card ↥AK := by
    rw [hcardK, hcardK']
    obtain ⟨k, hk⟩ := h3ker
    exact ⟨k, by rw [hk]; ring⟩
  have hdvd : Nat.card ↥AK ∣ 1152 := hcardA ▸ Subgroup.card_dvd_of_le le_sup_right
  rcases ggF4Orig_type_cases hAK hdvd with ⟨n, hn1, hn3, hT⟩ | ⟨n, hn2, hn4, hT⟩ | hT | hT | hT
  · rw [ggWeylOfType_A_card hT] at h18
    interval_cases n <;> norm_num [Nat.factorial] at h18
  · obtain ⟨eK, -⟩ := hT
    have hc : Nat.card ↥AK = 2 ^ n * n.factorial := by
      rw [← Nat.card_congr eK.toEquiv]
      exact le_antisymm (card_coxeterB_le n) (SpFrame.card_coxeterB_ge n hn2)
    rw [hc] at h18
    interval_cases n <;> norm_num [Nat.factorial] at h18
  · obtain ⟨eK, -⟩ := hT
    have hc : Nat.card ↥AK = 2 ^ (4 - 1) * (4 : ℕ).factorial := by
      rw [← Nat.card_congr eK.toEquiv]
      exact OrthF3.card_coxeterD_eq 4 le_rfl
    rw [hc] at h18
    norm_num [Nat.factorial] at h18
  ·
    have hc : Nat.card ↥AK = 1152 := ggF4Orig_card_weylOfType_F4 hT
    have heq : AK = AL ⊔ AK :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardA, hc])
    obtain ⟨b, hb1, hb⟩ := hfix
    exact hb1 (hfixA b fun φ hφ => hb φ (heq ▸ hφ))
  · obtain ⟨eK, -⟩ := hT
    have hc : Nat.card ↥AK = 12 := by
      rw [← Nat.card_congr eK.toEquiv]
      exact l04fFRC_card_coxeterG2
    rw [hc] at h18
    norm_num at h18

theorem ggF4Ends_no_order_three_of_A3 (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ¬ ∃ a ∈ ggAutomizer L Bs ⊓ ggAutomizer K Bs, orderOf a = 3 := by
  intro h3
  have hR := hRC.1
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hNT : GGNoTransvection p Bs := hR.2.2.2.1
  have hind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    rw [← ggAutomizerJoin_singleton L Bs K]
    exact ggAutomizerJoin_le_ggInduced_top L {K}
  have hAK := GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR
    hRC.2.1 hNb
  have hyBs : y ∈ Bs := hR.1.2.1.1 hNb.1.2.1
  exact ggF4Ends_false_of_A3_join hp hp2 hBs hNT hind hWK hA3 hAK h3
    ⟨⟨y, hyBs⟩, fun h => hNb.1.2.2.1 (congrArg Subtype.val h), fun φ hφ =>
      ggAutomizer_apply_eq_of_le_centralizer (x := ⟨y, hyBs⟩) hNb.1.2.2.2.1 hφ⟩
    (fun b hb => GGSecFiveRestHyp.eq_one_of_fix_pair hTBF hWI hR hRC.2.1 hNb b hb)

end A3

end CFSG.StandardType

end
