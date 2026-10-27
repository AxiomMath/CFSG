module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Gen

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2

theorem le_normalizer_of_forall_conj_mem {X : Type*} [Group X] [Finite X] {B K : Subgroup X}
    (h : ∀ b ∈ B, ∀ y ∈ K, b * y * b⁻¹ ∈ K) : B ≤ Subgroup.normalizer (K : Set X) :=
  fun b hb => Subgroup.mem_normalizer_fintype fun y hy => h b hb y hy

theorem support_card_vOneF_mul_vTwoF : ((vOneF 3 * vTwoF 3) ^ 4).support.card = 3 := by
  decide +kernel

theorem alternatingGroup_le_vOne_sup_vTwo : alternatingGroup (Fin 7) ≤ vOne ⊔ vTwo := by
  set H := vOne ⊔ vTwo with hH
  have h1 : ∀ m : Fin 4, vOneF m ∈ H := fun m => Subgroup.mem_sup_left ⟨m, rfl⟩
  have h2 : ∀ m : Fin 4, vTwoF m ∈ H := fun m => Subgroup.mem_sup_right ⟨m, rfl⟩
  have hpre : MulAction.IsPretransitive H (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base (6 : Fin 7)]
    intro x
    have hx : ∃ m : Fin 7, ([vTwoF 3, vTwoF 2, vTwoF 1, vOneF 3, vOneF 2, vOneF 1, 1] :
        List (Perm (Fin 7)))[m]! 6 = x := by
      revert x
      decide +kernel
    obtain ⟨m, hm⟩ := hx
    have hmem : ∀ m : Fin 7, ([vTwoF 3, vTwoF 2, vTwoF 1, vOneF 3, vOneF 2, vOneF 1, 1] :
        List (Perm (Fin 7)))[m]! ∈ H := by
      intro m
      fin_cases m
      exacts [h2 3, h2 2, h2 1, h1 3, h1 2, h1 1, one_mem H]
    exact ⟨⟨_, hmem m⟩, hm⟩
  have hprim : MulAction.IsPreprimitive H (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (card_support_eq_three_iff.mp support_card_vOneF_mul_vTwoF)
    (pow_mem (mul_mem (h1 3) (h2 3)) 4)

theorem eNineF_conj_vF : ∀ (i j : Fin 3) (m : Fin 4),
    (∃ n : Fin 4, eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF n) ∧
      (∃ n : Fin 4, eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF n) := by
  decide +kernel

theorem eNine_le_normalizer_vOne : eNine ≤ Subgroup.normalizer (vOne : Set (Perm (Fin 7))) :=
  le_normalizer_of_forall_conj_mem (by
    rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
    exact (eNineF_conj_vF i j m).1)

theorem eNine_le_normalizer_vTwo : eNine ≤ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) :=
  le_normalizer_of_forall_conj_mem (by
    rintro _ ⟨i, j, rfl⟩ _ ⟨m, rfl⟩
    exact (eNineF_conj_vF i j m).2)

theorem exists_sup_eq_top_of_card_nine {X : Type*} [Group X] [Finite X]
    (φ : X ≃* alternatingGroup (Fin 7)) {E : Subgroup X} (hE : Nat.card E = 9) :
    ∃ Q₁ Q₂ : Subgroup X, Q₁ ⊔ Q₂ = ⊤ ∧ Nat.card Q₁ = 4 ∧ Nat.card Q₂ = 4 ∧
      E ≤ Subgroup.normalizer (Q₁ : Set X) ∧ E ≤ Subgroup.normalizer (Q₂ : Set X) := by
  set ι : X →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιrange : ι.range = alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ y).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [hι]⟩
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine (E := E.map ι)
    (by rw [Subgroup.card_map_of_injective hιinj, hE])
  have hAconj : ∀ V : Subgroup (Perm (Fin 7)), V ≤ alternatingGroup (Fin 7) →
      V.map (MulAut.conj g⁻¹).toMonoidHom ≤ ι.range := by
    rintro V hV _ ⟨v, hv, rfl⟩
    rw [hιrange]
    change g⁻¹ * v * g⁻¹⁻¹ ∈ alternatingGroup (Fin 7)
    exact (Subgroup.Normal.conj_mem inferInstance v (hV hv) g⁻¹)
  have hV1 : vOne ≤ alternatingGroup (Fin 7) := vOne_le_centOne.trans inf_le_right
  have hV2 : vTwo ≤ alternatingGroup (Fin 7) := vTwo_le_centTwo.trans inf_le_right
  have hnorm : ∀ V : Subgroup (Perm (Fin 7)),
      eNine ≤ Subgroup.normalizer (V : Set (Perm (Fin 7))) →
      E ≤ Subgroup.normalizer
        (((V.map (MulAut.conj g⁻¹).toMonoidHom).comap ι : Subgroup X) : Set X) := by
    intro V hEV e he
    have he' : g * ι e * g⁻¹ ∈ eNine := by
      rw [← hg]
      exact ⟨ι e, ⟨e, he, rfl⟩, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨v, hv, hvy⟩ := hy
    have hvy' : v = g * ι y * g⁻¹ := by
      rw [show ι y = g⁻¹ * v * g⁻¹⁻¹ from hvy.symm]
      group
    have hmem : (g * ι e * g⁻¹) * v * (g * ι e * g⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hEV he') v).mp hv
    refine ⟨(g * ι e * g⁻¹) * v * (g * ι e * g⁻¹)⁻¹, hmem, ?_⟩
    change g⁻¹ * ((g * ι e * g⁻¹) * v * (g * ι e * g⁻¹)⁻¹) * g⁻¹⁻¹ = ι (e * y * e⁻¹)
    rw [hvy', map_mul, map_mul, map_inv]
    group
  refine ⟨(vOne.map (MulAut.conj g⁻¹).toMonoidHom).comap ι,
    (vTwo.map (MulAut.conj g⁻¹).toMonoidHom).comap ι, ?_, ?_, ?_,
    hnorm vOne eNine_le_normalizer_vOne, hnorm vTwo eNine_le_normalizer_vTwo⟩
  ·
    rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective hιinj, Subgroup.map_sup,
      Subgroup.map_comap_eq, Subgroup.map_comap_eq, inf_eq_right.mpr (hAconj vOne hV1),
      inf_eq_right.mpr (hAconj vTwo hV2), ← Subgroup.map_sup, ← MonoidHom.range_eq_map, hιrange]
    rintro x hx
    have hx' : g * x * g⁻¹ ∈ vOne ⊔ vTwo := alternatingGroup_le_vOne_sup_vTwo
      (Subgroup.Normal.conj_mem inferInstance x hx g)
    refine ⟨g * x * g⁻¹, hx', ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group
  · rw [← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq,
      inf_eq_right.mpr (hAconj vOne hV1),
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_vOne]
  · rw [← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq,
      inf_eq_right.mpr (hAconj vTwo hV2),
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_vTwo]

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have hz : x⁻¹ * y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := congrArg (fun σ : MulAut X => σ z) hxy
    simp only [MulAut.conj_apply] at h
    calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
      _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h]
      _ = x⁻¹ * y * z := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.mp hz)

theorem le_sSup_invariantPiSubgroups_of_a7 {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hA9 : Nat.card (Sec4.autThetaQuot A L) = 9)
    (hA7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  classical
  obtain ⟨φ⟩ := hA7
  set Ebar := Sec4.autThetaQuot A L with hEbar
  obtain ⟨-, hZ, hinner, -, -⟩ :=
    KFacts.KS14.a7_facts (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⟨φ⟩
  have hinj := conj_injective_of_center_eq_bot hZ
  have hEin : Ebar ≤ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
      MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range := by
    intro τ hτ
    have h9 : τ ^ 3 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := Ebar) (x := ⟨τ, hτ⟩)
      rw [hA9] at h
      exact congrArg Subtype.val h
    obtain ⟨x, hx⟩ := hinner τ ⟨2, h9⟩
    exact ⟨x, hx.symm⟩
  set E := Ebar.comap (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
      MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with hE
  have hEcard : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hE, Subgroup.map_comap_eq,
      inf_eq_right.mpr hEin, hA9]
  obtain ⟨Q₁, Q₂, htop, h4₁, h4₂, hN₁, hN₂⟩ := exists_sup_eq_top_of_card_nine φ hEcard
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have key : ∀ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card Q = 4 →
      E ≤ Subgroup.normalizer (Q : Set _) →
      (Q.comap (QuotientGroup.mk' _)).map L.subtype ∈ invariantPiSubgroups L A (piCompl 3) := by
    intro Q hQ4 hEQ
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [isPiSubgroup_piCompl_iff Nat.prime_three,
        Subgroup.card_map_of_injective L.subtype_injective]
      intro h3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hyQ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (y : ↥L) ∈ Q := y.2
      have hyo : orderOf (y : ↥L) = 3 := by rw [Subgroup.orderOf_coe, hy]
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (y : ↥L) = 1 := by
        have ho : orderOf (⟨_, hyQ⟩ : Q) ∣ Nat.gcd 3 4 := by
          refine Nat.dvd_gcd ?_ ?_
          · calc orderOf (⟨_, hyQ⟩ : Q)
                = orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (y : ↥L)) :=
                  Subgroup.orderOf_mk _ _
              _ ∣ orderOf (y : ↥L) := orderOf_map_dvd _ _
              _ = 3 := hyo
          · rw [← hQ4]
            exact orderOf_dvd_natCard _
        rw [show Nat.gcd 3 4 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at ho
        exact congrArg Subtype.val ho
      have hyθ : (y : ↥L) ∈ aschbacherSolvableCore 3 ↥L := (QuotientGroup.eq_one_iff _).mp h1
      have ho := orderOf_dvd_natCard (⟨(y : ↥L), hyθ⟩ : aschbacherSolvableCore 3 ↥L)
      rw [Subgroup.orderOf_mk, hyo] at ho
      exact hθ3 ho
    · refine le_normalizer_of_forall_conj_mem fun a ha y hy => ?_
      obtain ⟨l, hl, rfl⟩ := hy
      set τ := Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨a, hAL ha⟩) with hτ
      have hτE : τ ∈ Ebar := Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩
      obtain ⟨x, hx⟩ := hEin hτE
      have hxE : x ∈ E := by
        change MulAut.conj x ∈ Ebar
        rw [hx]
        exact hτE
      set l' := L.normalizerMonoidHom ⟨a, hAL ha⟩ l with hl'
      have hl'G : (l' : G) = a * (l : G) * a⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨a, hAL ha⟩ l
      have hπl' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l' =
          x * QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l * x⁻¹ := by
        have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l' =
            τ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l) :=
          (Sec4.thetaQuotMulAut_mk _ l).symm
        rw [h1, ← hx, MulAut.conj_apply]
      have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l' ∈ Q := by
        rw [hπl']
        exact (Subgroup.mem_normalizer_iff.mp (hEQ hxE) _).mp hl
      exact ⟨l', hmem, hl'G⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hgen : Q₁.comap π ⊔ Q₂.comap π = ⊤ := by
    have hmap : (Q₁.comap π ⊔ Q₂.comap π).map π = ⊤ := by
      rw [Subgroup.map_sup,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), htop]
    have h := Subgroup.comap_map_eq π (Q₁.comap π ⊔ Q₂.comap π)
    rw [hmap, Subgroup.comap_top] at h
    rw [h]
    exact (sup_eq_left.mpr ((Subgroup.ker_le_comap π Q₁).trans le_sup_left)).symm
  intro l hl
  have hl' : (⟨l, hl⟩ : ↥L) ∈ Q₁.comap π ⊔ Q₂.comap π := hgen ▸ Subgroup.mem_top _
  have hl'' : l ∈ (Q₁.comap π ⊔ Q₂.comap π).map L.subtype := ⟨_, hl', rfl⟩
  rw [Subgroup.map_sup] at hl''
  exact (sup_le (le_sSup (key Q₁ h4₁ hN₁)) (le_sSup (key Q₂ h4₂ hN₂))) hl''

theorem card_autThetaQuot_eq_nine {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) : Nat.card (Sec4.autThetaQuot A L) = 9 := by
  have h := card_inf_mul_card_autThetaQuot hD.le_normalizer
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  have heq : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hsc
  rw [heq, hD.card_zpowers, hD.card_eq] at h
  omega

theorem le_sSup_invariantPiSubgroups_of_sec13Data {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L)
    (hA7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) :=
  le_sSup_invariantPiSubgroups_of_a7 hD.le_normalizer (card_autThetaQuot_eq_nine hD) hA7

end Gen

end CFSG.RankThree.PartTwo.Sec17.Proof171Gen
