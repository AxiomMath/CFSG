module

public import CFSG.Quasithin.Vol2.Ch10Reselect.GLemma
public import CFSG.Quasithin.Vol2.Ch10Reselect.ThreeSub
public import CFSG.Quasithin.Vol2.Ch10Reselect.CardGL
public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML
public import CFSG.Quasithin.Vol2.Ch10Reselect.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

private lemma conj_inv_mem_centralizer_aux {X : Subgroup G} {t z : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (hz : z ∈ Subgroup.centralizer (X : Set G)) :
    t⁻¹ * z * t ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro h hh
  have hh' : t * h * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp ht h).mp hh
  have hc := hz _ hh'
  calc h * (t⁻¹ * z * t) = t⁻¹ * ((t * h * t⁻¹) * z) * t := by group
    _ = t⁻¹ * (z * (t * h * t⁻¹)) * t := by rw [hc]
    _ = t⁻¹ * z * t * h := by group

theorem commutator_mem_Z_of_rElement [Finite K] (M : RModel T L I K) {r : ℕ} [Fact r.Prime]
    (hr : ¬ r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) {k : G} (hk : k ∈ fsuML T L)
    (hk0 : ∀ l ∈ L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) {j : ℕ}
    (hkord : k ^ (r ^ j) = 1) :
    ∀ u ∈ fsuUL T L I, ⁅k, u⁆ ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
  have hφ : actML M ⟨k, hk⟩ ∈ centralizerSL2 K := actML_mem_centralizerSL2 M ⟨k, hk⟩ hk0
  have hd1 : orderOf (actML M ⟨k, hk⟩) ∣ r ^ j := by
    refine (orderOf_map_dvd (actML M) ⟨k, hk⟩).trans ?_
    rw [← Subgroup.orderOf_coe ⟨k, hk⟩]
    exact orderOf_dvd_of_pow_eq_one hkord
  have hnd : ¬ r ∣ Nat.card (GL (Fin 2) K) :=
    not_dvd_card_GL_two_of_not_dvd_card_SL_two (Fact.out : Nat.Prime r) hr
  have hcop : Nat.Coprime (r ^ j) (Nat.card (GL (Fin 2) K)) :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime r)).mpr hnd)
  have hd2 : orderOf (actML M ⟨k, hk⟩) ∣ Nat.card (GL (Fin 2) K) :=
    orderOf_dvd_card_GL_two_of_mem_centralizerSL2 hφ
  have hone : orderOf (actML M ⟨k, hk⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have hact : M.actHom ⟨k, mem_acting_of_mem_fsuML hk⟩ = 1 := orderOf_eq_one_iff.mp hone
  have h := (UModel.actHom_eq_one_iff M ⟨k, mem_acting_of_mem_fsuML hk⟩).mp hact
  intro u hu
  rw [commutatorElement_def]
  exact h u hu

theorem mem_centralizer_of_trivial_on_U
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) [IsMulCommutative ↥(fsuVM T L I)] (hA : Concl326A T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {k : G} (hk : k ∈ fsuM T L)
    (hk0 : ∀ l ∈ fsuL0 T L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    (hU : ∀ u ∈ fsuUL T L I,
      ⁅k, u⁆ ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G))
    (hUt : ∀ u ∈ fsuUL T L I,
      ⁅t * k * t⁻¹, u⁆ ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :
    k ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have htM : t ∈ fsuM T L := le_fsuM T L ht
  have htA : t⁻¹ ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (Subgroup.normalizer (fsuVM T L I : Set G)).inv_mem (fsuM_le_normalizer_fsuVM T L I htM)
  have hkA : k ∈ Subgroup.normalizer (fsuVM T L I : Set G) := fsuM_le_normalizer_fsuVM T L I hk
  have hkC : k ∈ Subgroup.normalizer ((fsuVM T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :
      Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hkA, le_normalizer_centralizer (X := fsuM T L) (V := fsuL0 T L) le_rfl hk⟩
  have hUC : ∀ u ∈ fsuUL T L I, ⁅k, u⁆ ∈ fsuCVM T L I := fun u hu =>
    Subgroup.mem_inf.mpr ⟨fsuUL_le_fsuVM T L I (Subgroup.mem_inf.mp (hU u hu)).1,
      (Subgroup.mem_inf.mp (hU u hu)).2⟩
  have hU'C : ∀ u' ∈ CFSG.conjugate (fsuUL T L I) t, ⁅k, u'⁆ ∈ fsuCVM T L I := by
    intro u' hu'
    have hw : t * u' * t⁻¹ ∈ fsuUL T L I := mem_conjugate_iff.mp hu'
    obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.mp (hUt _ hw)
    have key : ⁅k, u'⁆ = t⁻¹ * ⁅t * k * t⁻¹, t * u' * t⁻¹⁆ * t := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [key]
    refine Subgroup.mem_inf.mpr ⟨?_, conj_inv_mem_centralizer_aux htM hzC⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp htA _).mp (fsuUL_le_fsuVM T L I hzU)
    rwa [inv_inv] at h1
  have hall := commutator_mem_of_sup_of_abelian (A := fsuVM T L I) (U := fsuUL T L I)
    (U' := CFSG.conjugate (fsuUL T L I) t) (C := fsuCVM T L I) (k := k) hkA hkC
    (fsuUL_le_fsuVM T L I) (conjugate_UL_le_fsuVM T L I htM) inf_le_left (hA t ht htn).1 hUC hU'C
  exact mem_centralizer_of_trivial_mod (A := fsuVM T L I) (L0 := fsuL0 T L) (C := fsuCVM T L I)
    (fsuL0_le_normalizer_fsuVM T L I) (fsuVM_eq_commutator hfsu) inf_le_left inf_le_right hk0 hall

end CFSG.Quasithin.Vol2.Ch10Reselect
