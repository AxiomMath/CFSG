module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem card_barSub_eq_two_of_mem_omegaSet (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : Nat.card (barSub (kSub V H E) φ U) = 2 := by
  obtain ⟨k, hk, rfl⟩ := h.transitive U hU
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  rw [barSub_conjSubgroup (φ := φ) V ⟨k, hk⟩]
  exact (card_conjSubgroup' (φ ⟨k, hk⟩) (barSub (kSub V H E) φ V)).trans hV2


theorem mul_mem_iSub_of_card_barSub_eq_two (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) :
    ∀ U ∈ omegaSet V H E, ∀ u ∈ U, ∀ w ∈ U, u ∉ iSub V H E → w ∉ iSub V H E →
      u * w ∈ iSub V H E := by
  intro U hU u hu w hw huI hwI
  let K : Subgroup G := kSub V H E
  have hinf : U ⊓ iSub V H E = U ⊓ pCoreOf 2 K :=
    inf_iSub_eq_inf_J (J := pCoreOf 2 K) hU h.iSub_le h.pcore_le
  have huK : u ∈ K := le_kSub hU hu
  have hwK : w ∈ K := le_kSub hU hw
  have huJ : u ∉ pCoreOf 2 K := by
    intro huJ
    exact huI (hinf.symm ▸ (Subgroup.mem_inf.mpr ⟨hu, huJ⟩)).2
  have hwJ : w ∉ pCoreOf 2 K := by
    intro hwJ
    exact hwI (hinf.symm ▸ (Subgroup.mem_inf.mpr ⟨hw, hwJ⟩)).2
  have hne1u : φ ⟨u, huK⟩ ≠ 1 := fun h1 => huJ ((hφ.ker_iff ⟨u, huK⟩).mp h1)
  have hne1w : φ ⟨w, hwK⟩ ≠ 1 := fun h1 => hwJ ((hφ.ker_iff ⟨w, hwK⟩).mp h1)
  have hmemu : φ ⟨u, huK⟩ ∈ barSub K φ U := mem_barSub.mpr ⟨⟨u, huK⟩, hu, rfl⟩
  have hmemw : φ ⟨w, hwK⟩ ∈ barSub K φ U := mem_barSub.mpr ⟨⟨w, hwK⟩, hw, rfl⟩
  have hcard : Nat.card (barSub K φ U) = 2 :=
    card_barSub_eq_two_of_mem_omegaSet h hφ hV2 hU
  have hueqw : φ ⟨u, huK⟩ = φ ⟨w, hwK⟩ := by
    obtain ⟨z, _hz, hzuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(barSub K φ U))).mp hcard
    have h1 : (⟨φ ⟨u, huK⟩, hmemu⟩ : ↥(barSub K φ U)) = z :=
      hzuniq _ (fun h => hne1u (congrArg Subtype.val h))
    have h2 : (⟨φ ⟨w, hwK⟩, hmemw⟩ : ↥(barSub K φ U)) = z :=
      hzuniq _ (fun h => hne1w (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have huu : u * u = 1 :=
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) hu
  have hbaru2 : φ ⟨u, huK⟩ * φ ⟨u, huK⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨u, huK⟩ : ↥K) * ⟨u, huK⟩ = 1 := Subtype.ext (by simpa using huu)
    rw [h1, map_one]
  have hphiuw : φ ⟨u * w, K.mul_mem huK hwK⟩ = 1 := by
    have huw : (⟨u * w, K.mul_mem huK hwK⟩ : ↥K) = ⟨u, huK⟩ * ⟨w, hwK⟩ :=
      Subtype.ext rfl
    rw [huw, map_mul, ← hueqw, hbaru2]
  have huwJ : u * w ∈ pCoreOf 2 K :=
    (hφ.ker_iff ⟨u * w, K.mul_mem huK hwK⟩).mp hphiuw
  have hmem : u * w ∈ U ⊓ iSub V H E := by
    rw [hinf]
    exact ⟨U.mul_mem hu hw, huwJ⟩
  exact hmem.2

theorem mem_iSub_of_mem_normalizer_of_commutator_ne_bot (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) {U U' : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (hcomm : ⁅barSub (kSub V H E) φ U, barSub (kSub V H E) φ U'⁆ ≠ ⊥) :
    ∀ v ∈ U, v ∈ Subgroup.normalizer (U' : Set G) → v ∈ iSub V H E := by
  intro v hvU hvN
  by_contra hvI
  let K : Subgroup G := kSub V H E
  have hinf : U ⊓ iSub V H E = U ⊓ pCoreOf 2 K :=
    inf_iSub_eq_inf_J (J := pCoreOf 2 K) hU h.iSub_le h.pcore_le
  have hvK : v ∈ K := le_kSub hU hvU
  have hvJ : v ∉ pCoreOf 2 K := by
    intro hvJ
    exact hvI (hinf.symm ▸ (Subgroup.mem_inf.mpr ⟨hvU, hvJ⟩)).2
  have hne1v : φ ⟨v, hvK⟩ ≠ 1 := fun h1 => hvJ ((hφ.ker_iff ⟨v, hvK⟩).mp h1)
  have hcardU : Nat.card (barSub K φ U) = 2 :=
    card_barSub_eq_two_of_mem_omegaSet h hφ hV2 hU
  have hmemv : φ ⟨v, hvK⟩ ∈ barSub K φ U := mem_barSub.mpr ⟨⟨v, hvK⟩, hvU, rfl⟩
  obtain ⟨z, _hz, hzuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(barSub K φ U))).mp hcardU
  have hzv : (⟨φ ⟨v, hvK⟩, hmemv⟩ : ↥(barSub K φ U)) = z :=
    hzuniq _ (fun h => hne1v (congrArg Subtype.val h))
  have hzv_val : φ ⟨v, hvK⟩ = z.1 := congrArg Subtype.val hzv
  have hcardU' : Nat.card (barSub K φ U') = 2 :=
    card_barSub_eq_two_of_mem_omegaSet h hφ hV2 hU'
  obtain ⟨z', hz'ne, hz'uniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(barSub K φ U'))).mp hcardU'
  obtain ⟨u', hu'U', hφu'⟩ := mem_barSub.mp z'.2
  have hz'ne' : φ u' ≠ 1 := fun h => hz'ne (Subtype.ext (hφu'.symm.trans h))
  have hu'K : (u' : G) ∈ K := le_kSub hU' hu'U'
  have hK : v * (u' : G) * v⁻¹ ∈ K := K.mul_mem (K.mul_mem hvK hu'K) (K.inv_mem hvK)
  have hvin : v * (u' : G) * v⁻¹ ∈ U' :=
    (Subgroup.mem_set_normalizer_iff.mp hvN (u' : G)).mp hu'U'
  have hconj_eq : φ (⟨v * (u' : G) * v⁻¹, hK⟩ : ↥K)
      = φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹ := by
    rw [show (⟨v * (u' : G) * v⁻¹, hK⟩ : ↥K)
        = (⟨v, hvK⟩ : ↥K) * u' * (⟨v, hvK⟩ : ↥K)⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv]
  have hconj_mem : φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹ ∈ barSub K φ U' := by
    rw [← hconj_eq]
    exact mem_barSub.mpr ⟨⟨v * (u' : G) * v⁻¹, hK⟩, hvin, rfl⟩
  have hconj_eq_u' : φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹ = φ u' := by
    have hne : φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹ ≠ 1 := by
      intro h
      apply hz'ne'
      calc φ u' = (φ ⟨v, hvK⟩)⁻¹ * (φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹)
            * φ ⟨v, hvK⟩ := by group
        _ = (φ ⟨v, hvK⟩)⁻¹ * 1 * φ ⟨v, hvK⟩ := by rw [h]
        _ = 1 := by group
    have h1 : (⟨φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹, hconj_mem⟩ :
        ↥(barSub K φ U')) = z' :=
      hz'uniq _ (fun h => hne (congrArg Subtype.val h))
    exact (congrArg Subtype.val h1).trans hφu'.symm
  have hcommute : φ ⟨v, hvK⟩ * φ u' = φ u' * φ ⟨v, hvK⟩ := by
    calc φ ⟨v, hvK⟩ * φ u'
        = (φ ⟨v, hvK⟩ * φ u' * (φ ⟨v, hvK⟩)⁻¹) * φ ⟨v, hvK⟩ := by group
      _ = φ u' * φ ⟨v, hvK⟩ := by rw [hconj_eq_u']
  have hcommbot : ⁅barSub K φ U, barSub K φ U'⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    rcases eq_or_ne x 1 with hx1 | hx1
    · rw [hx1, one_mul, mul_one]
    rcases eq_or_ne y 1 with hy1 | hy1
    · rw [hy1, mul_one, one_mul]
    have hx_v : x = φ ⟨v, hvK⟩ := by
      have h1 : x = z.1 :=
        congrArg Subtype.val
          (hzuniq (⟨x, hx⟩ : ↥(barSub K φ U)) (fun h => hx1 (congrArg Subtype.val h)))
      exact h1.trans hzv_val.symm
    have hy_u' : y = φ u' := by
      have h1 : y = z'.1 :=
        congrArg Subtype.val
          (hz'uniq (⟨y, hy⟩ : ↥(barSub K φ U')) (fun h => hy1 (congrArg Subtype.val h)))
      exact h1.trans hφu'.symm
    rw [hx_v, hy_u']
    exact hcommute
  exact hcomm hcommbot

theorem sevenSevenCfg_of_barSub (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) (k₂ k₃ : ↥(kSub V H E))
    (h12 : IsPGroup 2 ↥(barSub (kSub V H E) φ V ⊔
      conjSubgroup (barSub (kSub V H E) φ V) (φ k₂)))
    (hne : conjSubgroup (barSub (kSub V H E) φ V) (φ k₂) ≠ barSub (kSub V H E) φ V)
    (h13 : ⁅barSub (kSub V H E) φ V, conjSubgroup (barSub (kSub V H E) φ V) (φ k₃)⁆ ≠ ⊥)
    (h23 : ⁅conjSubgroup (barSub (kSub V H E) φ V) (φ k₂),
      conjSubgroup (barSub (kSub V H E) φ V) (φ k₃)⁆ ≠ ⊥) :
    SevenSevenCfg V H E V (conjSubgroup V (k₂ : G)) (conjSubgroup V (k₃ : G)) := by
  have hk₂H : (k₂ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₂.2
  have hk₃H : (k₃ : G) ∈ H := kSub_le_of_forall_le h.omega_le k₃.2
  have hmem₂ : conjSubgroup V (k₂ : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hk₂H
  have hmem₃ : conjSubgroup V (k₃ : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hk₃H
  refine ⟨h.mem, hmem₂, hmem₃, mul_mem_iSub_of_card_barSub_eq_two h hφ hV2, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (isPGroup_barSub_sup_conj_iff h hφ k₂).mp h12
  · intro hEq
    exact hne (by rw [← barSub_conjSubgroup (φ := φ) V k₂, ← hEq])
  · exact mem_iSub_of_mem_normalizer_of_commutator_ne_bot h hφ hV2 h.mem hmem₃
      (by rw [barSub_conjSubgroup (φ := φ) V k₃]; exact h13)
  · exact mem_iSub_of_mem_normalizer_of_commutator_ne_bot h hφ hV2 hmem₂ hmem₃
      (by rw [barSub_conjSubgroup (φ := φ) V k₂, barSub_conjSubgroup (φ := φ) V k₃]
          exact h23)
  · refine mem_iSub_of_mem_normalizer_of_commutator_ne_bot h hφ hV2 hmem₃ h.mem ?_
    rw [Subgroup.commutator_comm, barSub_conjSubgroup (φ := φ) V k₃]
    exact h13
  · refine mem_iSub_of_mem_normalizer_of_commutator_ne_bot h hφ hV2 hmem₃ hmem₂ ?_
    rw [Subgroup.commutator_comm, barSub_conjSubgroup (φ := φ) V k₂,
      barSub_conjSubgroup (φ := φ) V k₃]
    exact h23

end CFSG.LocalAnalysis.WeakClosure81
