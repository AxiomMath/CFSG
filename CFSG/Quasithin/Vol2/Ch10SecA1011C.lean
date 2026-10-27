module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem isMulCommutative_of_le {A B : Subgroup G} (h : A ≤ B) [hB : IsMulCommutative ↥B] :
    IsMulCommutative ↥A :=
  ⟨⟨fun a b => Subtype.ext (by
    have := congrArg Subtype.val (hB.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩)
    exact this)⟩⟩

variable [Finite G] {T L I : Subgroup G}

theorem normalizer_le_normalizer_pCoreOf (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
  intro g hg
  rw [← conjugate_eq_self_iff, ← pCoreOf_conjugate, conjugate_eq_self_iff.mpr hg]

@[expose] def centQuot (T L : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ L ⊔ T1 T L ∧ ∀ l ∈ L, ⁅y, l⁆ ∈ pCoreOf 2 L}
  one_mem' := ⟨(L ⊔ T1 T L).one_mem, fun l _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨(L ⊔ T1 T L).mul_mem ha hb, fun l hl => ?_⟩
    have hLN : L ⊔ T1 T L ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer inf_le_right
    have hON : L ⊔ T1 T L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
      intro x hx
      exact normalizer_le_normalizer_pCoreOf L (hLN hx)
    have key : ⁅a * b, l⁆ = (a * ⁅b, l⁆ * a⁻¹) * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (pCoreOf 2 L).mul_mem ((Subgroup.mem_normalizer_iff.mp (hON ha) _).mp (hcb l hl))
      (hca l hl)
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨(L ⊔ T1 T L).inv_mem ha, fun l hl => ?_⟩
    have hLN : L ⊔ T1 T L ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer inf_le_right
    have key : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have hON : a⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      normalizer_le_normalizer_pCoreOf L ((Subgroup.normalizer _).inv_mem (hLN ha))
    exact (Subgroup.mem_normalizer_iff.mp hON _).mp ((pCoreOf 2 L).inv_mem (hca l hl))

theorem mem_pCoreOf_of_commutator_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {z : G} (hzL : z ∈ L)
    (hz : ∀ l ∈ L, ⁅z, l⁆ ∈ pCoreOf 2 L) : z ∈ pCoreOf 2 L := by
  have hzc : ((⟨z, hzL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hcomm : ((⁅(⟨z, hzL⟩ : ↥L), k⁆ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      (mk_eq_one_iff _).mpr (hz k k.2)
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      at hcomm
    exact hcomm.symm
  rw [center_quot_eq_bot h37 h38 hyp, Subgroup.mem_bot] at hzc
  exact (mk_eq_one_iff _).mp hzc

theorem le_normalizer_centQuot : L ⊔ T1 T L ≤ Subgroup.normalizer (centQuot T L : Set G) := by
  have hLN : L ⊔ T1 T L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have key : ∀ g ∈ L ⊔ T1 T L, ∀ y ∈ centQuot T L, g * y * g⁻¹ ∈ centQuot T L := by
    intro g hg y hy
    refine ⟨(L ⊔ T1 T L).mul_mem ((L ⊔ T1 T L).mul_mem hg hy.1) ((L ⊔ T1 T L).inv_mem hg),
      fun l hl => ?_⟩
    have hgl : g⁻¹ * l * g⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hLN hg)) l).mp hl
    have h1 := hy.2 _ hgl
    have heq : ⁅g * y * g⁻¹, l⁆ = g * ⁅y, g⁻¹ * l * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf L (hLN hg)) _).mp h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun h => ?_⟩
  have := key g⁻¹ ((L ⊔ T1 T L).inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem centQuot_le_pCoreOf
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) : centQuot T L ≤ pCoreOf 2 (L ⊔ T1 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun y hy => hy.1)
    le_normalizer_centQuot ?_
  rintro ⟨y, hy⟩
  have hyT : y ∈ ((T1 T L ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hy.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ inf_le_right] at hyT
  obtain ⟨t, ht, l, hl, rfl⟩ := hyT
  obtain ⟨k, hk⟩ := (hyp.fsu.sylow.1.to_le (inf_le_left : T1 T L ≤ T)) ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hLN : L ⊔ T1 T L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have : (L.subgroupOf (L ⊔ T1 T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLN
  have htL : t ∈ L ⊔ T1 T L := Subgroup.mem_sup_right ht
  have hlL : l ∈ L ⊔ T1 T L := Subgroup.mem_sup_left hl
  have hpowL : (t * l) ^ 2 ^ k ∈ L := by
    have h1 : (((⟨t, htL⟩ * ⟨l, hlL⟩ : ↥(L ⊔ T1 T L)) ^ 2 ^ k : ↥(L ⊔ T1 T L)) :
        ↥(L ⊔ T1 T L) ⧸ L.subgroupOf (L ⊔ T1 T L)) = 1 := by
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (⟨l, hlL⟩ : ↥(L ⊔ T1 T L))).mpr hl, mul_one,
        ← QuotientGroup.mk_pow, show (⟨t, htL⟩ : ↥(L ⊔ T1 T L)) ^ 2 ^ k = 1 from
          Subtype.ext (by simpa using hk'), QuotientGroup.mk_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hz : (t * l) ^ 2 ^ k ∈ pCoreOf 2 L :=
    mem_pCoreOf_of_commutator_mem h37 h38 hyp hpowL ((centQuot T L).pow_mem hy _).2
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hz⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : ((t * l) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  simpa [pow_add, pow_mul] using hj'

end CFSG.Quasithin.Vol2.Ch10.SecA
