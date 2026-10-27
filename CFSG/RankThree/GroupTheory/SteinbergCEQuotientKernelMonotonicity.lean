module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers

variable {G : Type*} [Group G] {p : ℕ}

theorem conj_mem_inSubgroup_aschbacherSolvableCore {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ inSubgroup (aschbacherSolvableCore p) L) :
    g * x * g⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L := by
  obtain ⟨y, hy, rfl⟩ := hx
  set φ := L.normalizerMonoidHom ⟨g, hg⟩
  have h := Subgroup.characteristic_iff_map_eq.mp (aschbacherSolvableCore_characteristic p L) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← h]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hy
  · simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem exists_mul_of_eq_sup_core {L M : Subgroup G} (hML : M ≤ L)
    (hLM : L = M ⊔ inSubgroup (aschbacherSolvableCore p) L) {l : G} (hl : l ∈ L) :
    ∃ m ∈ M, ∃ n ∈ inSubgroup (aschbacherSolvableCore p) L, m * n = l := by
  have hNL : inSubgroup (aschbacherSolvableCore p) L ≤ L := Subgroup.map_subtype_le _
  have hθ : (inSubgroup (aschbacherSolvableCore p) L).subgroupOf L = aschbacherSolvableCore p L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have htop : (⊤ : Subgroup L) = M.subgroupOf L ⊔ aschbacherSolvableCore p L := by
    rw [← hθ, ← Subgroup.subgroupOf_sup hML hNL, ← hLM, Subgroup.subgroupOf_self]
  have hl' : (⟨l, hl⟩ : L) ∈ M.subgroupOf L ⊔ aschbacherSolvableCore p L :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp hl'
  exact ⟨m, hm, n, ⟨n, hn, rfl⟩, congrArg Subtype.val hmn⟩

theorem inf_core_le_core_of_eq_sup [Finite G] (hp : p.Prime) {L K : Subgroup G}
    (hLK : L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore p) L) :
    L ⊓ inSubgroup (aschbacherSolvableCore p) K ≤ inSubgroup (aschbacherSolvableCore p) L := by
  set θL := aschbacherSolvableCore p L
  set θK := inSubgroup (aschbacherSolvableCore p) K
  set T := L ⊓ θK
  have hTL : T ≤ L := inf_le_left
  have hNL : inSubgroup (aschbacherSolvableCore p) L ≤ L := Subgroup.map_subtype_le _
  set π := QuotientGroup.mk' θL
  set X := (T.subgroupOf L).map π
  have hθKeq : θK = thetaCoreOf p K := inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp K
  have hθKsol : Group.IsSolvable θK := hθKeq ▸ thetaCoreOf_solvable p hp K
  have hθKp : ¬ p ∣ Nat.card θK := hθKeq ▸ thetaCoreOf_prime_complement p hp K
  have hTsol : Group.IsSolvable (T.subgroupOf L) := by
    have : Group.IsSolvable T :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hTL).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hTL).injective
  have hTp : ¬ p ∣ Nat.card (T.subgroupOf L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv]
    exact fun h => hθKp (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hXnormal : X.Normal := by
    refine ⟨fun x hx y => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θL y
    obtain ⟨m, hm, n, hn, hmn⟩ := exists_mul_of_eq_sup_core inf_le_left hLK l.2
    have hnθ : (⟨n, hNL hn⟩ : L) ∈ θL := by
      obtain ⟨n', hn', hn'eq⟩ := id hn
      have : n' = ⟨n, hNL hn⟩ := Subtype.ext hn'eq
      rwa [← this]
    have hl : l = ⟨m, hm.1⟩ * ⟨n, hNL hn⟩ := Subtype.ext hmn.symm
    have hπn : π ⟨n, hNL hn⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hnθ
    have hπl : π l = π ⟨m, hm.1⟩ := by
      rw [hl, map_mul, hπn, mul_one]
    refine ⟨⟨m, hm.1⟩ * t * ⟨m, hm.1⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht ⊢
      refine ⟨L.mul_mem (L.mul_mem hm.1 ht.1) (L.inv_mem hm.1), ?_⟩
      exact conj_mem_inSubgroup_aschbacherSolvableCore (Subgroup.le_normalizer hm.2) ht.2
    · rw [hπl, map_mul, map_mul, map_inv]
  have hXsol : Group.IsSolvable X := Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  have hXp : ¬ p ∣ Nat.card X := fun h => hTp (h.trans (Subgroup.card_map_dvd _ π))
  obtain ⟨hθLsol, -, hθLp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hcore : aschbacherSolvableCore p (L ⧸ θL) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers (G := L) hp θL hθLsol hθLp).2.2.1
  have hX : X = ⊥ := le_bot_iff.mp (hcore ▸
    (solvable_prime_complement_core_characterization hp).2.2.2.1 X hXnormal hXsol hXp)
  intro t ht
  have hmem : π ⟨t, ht.1⟩ ∈ X := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ht)
  rw [hX, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

theorem solvable_prime_complement_supplement_quotient_kernel_monotonicity [Finite G]
    (hp : p.Prime) {A L K : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hLK : L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore p) L) :
    (thetaQuotientAction p hAK).ker ≤ (thetaQuotientAction p hAL).ker ∧
      thetaQuotientCentralizer p A K ≤ thetaQuotientCentralizer p A L := by
  have hker : (thetaQuotientAction p hAK).ker ≤ (thetaQuotientAction p hAL).ker := by
    intro a ha
    rw [mem_ker_thetaQuotientAction_iff] at ha ⊢
    intro l hl
    have haL : (a : G) ∈ Subgroup.normalizer (L : Set G) := hAL a.2
    obtain ⟨m, hm, n, hn, rfl⟩ := exists_mul_of_eq_sup_core inf_le_left hLK hl
    have hmL : m ∈ L := hm.1
    have h1 : (a : G) * m * (a : G)⁻¹ * m⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L := by
      refine inf_core_le_core_of_eq_sup hp hLK ⟨L.mul_mem ?_ (L.inv_mem hmL), ha m hm.2⟩
      exact (Subgroup.mem_normalizer_iff.mp haL m).mp hmL
    have h2 : (a : G) * n * (a : G)⁻¹ * n⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L :=
      Subgroup.mul_mem _ (conj_mem_inSubgroup_aschbacherSolvableCore haL hn)
        (Subgroup.inv_mem _ hn)
    have h3 := conj_mem_inSubgroup_aschbacherSolvableCore (Subgroup.le_normalizer hmL) h2
    have heq : (a : G) * (m * n) * (a : G)⁻¹ * (m * n)⁻¹ =
        ((a : G) * m * (a : G)⁻¹ * m⁻¹) * (m * ((a : G) * n * (a : G)⁻¹ * n⁻¹) * m⁻¹) := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ h1 h3
  refine ⟨hker, ?_⟩
  rw [thetaQuotientCentralizer_eq_map_ker p hAK, thetaQuotientCentralizer_eq_map_ker p hAL]
  exact Subgroup.map_mono hker

end CFSG.RankThree.GroupTheory
