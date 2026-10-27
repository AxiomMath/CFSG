module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 Equiv

section KP2

open CFSG.RankThree.PartTwo.KFacts.KP2

theorem mem_normalizer_of_le_of_normal_perm_seven {C V : Subgroup (Perm (Fin 7))} (hVC : V ≤ C)
    (hV : (V.subgroupOf C).Normal) {x : Perm (Fin 7)} (hx : x ∈ C) :
    x ∈ Subgroup.normalizer (V : Set (Perm (Fin 7))) := by
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have h := hV.conj_mem ⟨v, hVC hv⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem signal_eNine {b : Perm (Fin 7)} (hb : b ∈ eNine) (hb1 : b ≠ 1) :
    ∃ W : Subgroup (Perm (Fin 7)), ¬ 3 ∣ Nat.card W ∧
      Subgroup.centralizer ({b} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ≤
        Subgroup.normalizer (W : Set (Perm (Fin 7))) ∧
      ∀ U : Subgroup (Perm (Fin 7)), (∀ x ∈ U, x * b = b * x) → ¬ 3 ∣ Nat.card U →
        cOne ∈ Subgroup.normalizer (U : Set (Perm (Fin 7))) →
        cTwo ∈ Subgroup.normalizer (U : Set (Perm (Fin 7))) → U ≤ W := by
  obtain ⟨i, j, rfl⟩ := hb
  have hij : (i, j) ≠ (0, 0) := by
    rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hb1 (by decide +kernel)
  have hsq : ∀ x : Perm (Fin 7), x * eNineF i j = eNineF i j * x →
      x * eNineF i j ^ 2 = eNineF i j ^ 2 * x := fun x hx =>
    ((Commute.pow_right (show Commute x (eNineF i j) from hx) 2)).eq
  have hgen : ∀ {c : Perm (Fin 7)}, (eNineF i j = c ∨ eNineF i j ^ 2 = c) →
      ∀ x : Perm (Fin 7), x * eNineF i j = eNineF i j * x → x * c = c * x := by
    rintro c (rfl | rfl) x hx
    · exact hx
    · exact hsq x hx
  rcases eNineF_cases i j hij with h | h | h | h
  ·
    refine ⟨vOne, by rw [card_vOne]; norm_num, fun x hx => ?_, fun U hU hU3 _ h2 u hu =>
      mem_vOne_of_commute hU3 h2 hu (hgen h u (hU u hu))⟩
    have hxC : x ∈ centOne :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (hgen h x (Subgroup.mem_centralizer_singleton_iff.mp hx.1)), hx.2⟩
    exact mem_normalizer_of_le_of_normal_perm_seven vOne_le_centOne vOne_normal hxC
  ·
    refine ⟨vTwo, by rw [card_vTwo]; norm_num, fun x hx => ?_, fun U hU hU3 h1 _ u hu =>
      mem_vTwo_of_commute hU3 h1 hu (hgen h u (hU u hu))⟩
    have hxC : x ∈ centTwo :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (hgen h x (Subgroup.mem_centralizer_singleton_iff.mp hx.1)), hx.2⟩
    exact mem_normalizer_of_le_of_normal_perm_seven vTwo_le_centTwo vTwo_normal hxC
  ·
    refine ⟨⊥, by rw [Subgroup.card_bot]; norm_num, fun x _ => by
      rw [Subgroup.normalizer_eq_top ⊥]; trivial, fun U hU hU3 h1 _ u hu => ?_⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_commute_cOne_cTwo hU3 h1 hu (hgen h u (hU u hu))
  · refine ⟨⊥, by rw [Subgroup.card_bot]; norm_num, fun x _ => by
      rw [Subgroup.normalizer_eq_top ⊥]; trivial, fun U hU hU3 h1 _ u hu => ?_⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_commute_cOne_cTwo_sq hU3 h1 hu (hgen h u (hU u hu))

theorem ks142SignalA7 : KS142SignalA7 := by
  intro E hE hE9 b hbE hb1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hE'9 : Nat.card (eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
      card_eNine]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hE'p : IsPGroup 3 (eNine.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  have hEi : ¬ 3 ∣ E.index := by
    have h := E.index_mul_card
    rw [hE9, hcard] at h
    omega
  have hE'i : ¬ 3 ∣ (eNine.subgroupOf (alternatingGroup (Fin 7))).index := by
    have h := (eNine.subgroupOf (alternatingGroup (Fin 7))).index_mul_card
    rw [hE'9, hcard] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hEp.toSylow hEi)
    (hE'p.toSylow hE'i)
  have hmem : ∀ y : alternatingGroup (Fin 7), y ∈ eNine.subgroupOf (alternatingGroup (Fin 7)) →
      g⁻¹ * y * g ∈ E := by
    intro y hy
    have hy' : y ∈ ((g • hEp.toSylow hEi : Sylow 3 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [hg, IsPGroup.toSylow_coe]
      exact hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
    have : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [this, IsPGroup.toSylow_coe] at hy'
    exact hy'
  have hmem' : ∀ x : alternatingGroup (Fin 7), x ∈ E →
      g * x * g⁻¹ ∈ eNine.subgroupOf (alternatingGroup (Fin 7)) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ ((g • hEp.toSylow hEi : Sylow 3 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [this, IsPGroup.toSylow_coe]
      exact hx
    rw [hg, IsPGroup.toSylow_coe] at hx'
    exact hx'
  let ψ : alternatingGroup (Fin 7) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (MulAut.conj g).toMonoidHom
  have hψ : ∀ x : alternatingGroup (Fin 7),
      ψ x = ((g * x * g⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) := fun x => rfl
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp (MulAut.conj g).injective
  have hb' : ψ b ∈ eNine := Subgroup.mem_subgroupOf.mp (hmem' b hbE)
  have hb'1 : ψ b ≠ 1 := fun h => hb1 (hψinj (h.trans ψ.map_one.symm))
  obtain ⟨W', hW'3, hW'N, hW'le⟩ := signal_eNine hb' hb'1
  refine ⟨W'.comap ψ, fun h3 => hW'3 (h3.trans (Subgroup.card_comap_dvd_of_injective W' ψ hψinj)),
    ?_, ?_⟩
  ·
    intro x hx
    have hxc : ψ x ∈ Subgroup.centralizer ({ψ b} : Set (Perm (Fin 7))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hx]
    have hxA : ψ x ∈ alternatingGroup (Fin 7) := by
      rw [hψ]
      exact (g * x * g⁻¹).2
    exact Subgroup.le_normalizer_comap ψ (hW'N (Subgroup.mem_inf.mpr ⟨hxc, hxA⟩))
  ·
    intro U hU hU3 hEU
    have hU' : ∀ x ∈ U.map ψ, x * ψ b = ψ b * x := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hU hu)]
    have hU3' : ¬ 3 ∣ Nat.card (U.map ψ) := by
      rwa [Subgroup.card_map_of_injective hψinj]
    have hnorm : ∀ c ∈ eNine,
        c ∈ Subgroup.normalizer ((U.map ψ : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
      intro c hc
      have hyE : g⁻¹ * ⟨c, eNine_le_alternatingGroup hc⟩ * g ∈ E :=
        hmem _ (Subgroup.mem_subgroupOf.mpr hc)
      have hψy : ψ (g⁻¹ * ⟨c, eNine_le_alternatingGroup hc⟩ * g) = c := by
        rw [hψ]
        simp [mul_assoc]
      rw [← hψy]
      exact Subgroup.le_normalizer_map ψ ⟨_, hEU hyE, rfl⟩
    have hle := hW'le _ hU' hU3' (hnorm _ cOne_mem_eNine) (hnorm _ cTwo_mem_eNine)
    exact Subgroup.map_le_iff_le_comap.mp hle

end KP2

theorem step142A7_of' (h131 : Item131) (hspor : SporadicModels131) : Step142A7 :=
  step142A7_of h131 hspor ks142SignalA7

end CFSG.RankThree.PartTwo.Sec14
