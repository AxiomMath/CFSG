module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped Pointwise

variable {G : Type} [Group G]

theorem normal_subgroupOf_of_le_normalizer {Y N : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) : (N.subgroupOf Y).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.mp (hYN y.2) n).mp hn
  simpa using this

theorem eq_top_of_isPerfect_of_isSolvable_quotient {Y : Type*} [Group Y] [Finite Y]
    (hYp : Group.IsPerfect Y) (M : Subgroup Y) [M.Normal] (hs : Group.IsSolvable (Y ⧸ M)) :
    M = ⊤ := by
  haveI : Group.IsPerfect (Y ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  haveI := hs
  haveI := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := Y ⧸ M)
  rw [eq_top_iff]
  intro y _
  have h : (QuotientGroup.mk y : Y ⧸ M) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff y).mp h

variable [Finite G]

theorem le_of_le_normalizer_of_isQuasisimple {Y N Y0 : Subgroup G}
    (hYp : Group.IsPerfect Y) (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hY0Y : Y0 ≤ Y) (hY0N : Y0 ≤ N)
    (hY0 : ¬ Group.IsSolvable Y0) : Y ≤ N := by
  set θ : Subgroup Y := aschbacherSolvableCore 3 Y with hθ
  obtain ⟨hθs, hθc, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  haveI : θ.Characteristic := hθc
  set M : Subgroup Y := N.subgroupOf Y with hM
  haveI hMn : M.Normal := normal_subgroupOf_of_le_normalizer hYN
  set π := QuotientGroup.mk' θ with hπ
  have hMπ : (M.map π).Normal := hMn.map π (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hYq hMπ with htop | hcen
  ·
    have hsup : M ⊔ θ = ⊤ := by
      have h := Subgroup.comap_map_eq π M
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hsolv : Group.IsSolvable (↥Y ⧸ M) := by
      haveI := hθs
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' M).comp θ.subtype) ?_
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      have h1 : (M ⊔ θ).map (QuotientGroup.mk' M) = ⊤ := by
        rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
      exact h1
    have hMtop := eq_top_of_isPerfect_of_isSolvable_quotient hYp M hsolv
    have h2 : ∀ y : Y, (y : G) ∈ N := fun y => by
      have : y ∈ M := by rw [hMtop]; exact Subgroup.mem_top y
      exact Subgroup.mem_subgroupOf.mp this
    exact fun y hy => h2 ⟨y, hy⟩
  ·
    exfalso
    apply hY0
    set R : Subgroup Y := (Subgroup.center (↥Y ⧸ θ)).comap π with hR
    have hθR : θ ≤ R := by
      intro t ht
      rw [hR, Subgroup.mem_comap]
      have : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
      rw [this]
      exact Subgroup.one_mem _
    have hRs : Group.IsSolvable R := by
      haveI := hθs
      haveI : Group.IsSolvable (Subgroup.center (↥Y ⧸ θ)) := by
        exact Group.isSolvable_of_comm fun a b =>
          Subtype.ext ((Subgroup.mem_center_iff.mp b.2) a)
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθR)
        ((π.comp R.subtype).codRestrict (Subgroup.center (↥Y ⧸ θ)) fun r => r.2) ?_
      intro r hr
      rw [MonoidHom.mem_ker] at hr
      have hr' : π r = 1 := by
        exact congrArg Subtype.val hr
      exact ⟨⟨r, (QuotientGroup.eq_one_iff (r : Y)).mp hr'⟩, rfl⟩
    have hY0R : Y0.subgroupOf Y ≤ R := by
      intro y hy
      rw [hR, Subgroup.mem_comap]
      apply hcen
      exact ⟨y, Subgroup.mem_subgroupOf.mpr (hY0N (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
    haveI := hRs
    have h1 : Group.IsSolvable (Y0.subgroupOf Y) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hY0R)
        (Subgroup.inclusion_injective _)
    haveI := h1
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hY0Y).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hY0Y).surjective


theorem range_eq_bot_of_coprime {Q H : Type*} [Group Q] [Group H] [Finite Q]
    (hp : Group.IsPerfect Q) (hq : IsQuasisimple (Q ⧸ aschbacherSolvableCore 3 Q))
    (h3 : 3 ∣ Nat.card ((Q ⧸ aschbacherSolvableCore 3 Q) ⧸
      Subgroup.center (Q ⧸ aschbacherSolvableCore 3 Q)))
    (ψ : Q →* H) {S : Subgroup H} (hS : Nat.Coprime 3 (Nat.card S)) (hψS : ψ.range ≤ S) :
    ψ.range = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : Subgroup Q := aschbacherSolvableCore 3 Q with hθ
  obtain ⟨hθs, hθc, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  haveI : θ.Characteristic := hθc
  set K0 := ψ.ker with hK0
  obtain ⟨T⟩ : Nonempty (Sylow 3 Q) := inferInstance
  have hTK : (T : Subgroup Q) ≤ K0 := by
    have hTS : (T : Subgroup Q).map ψ ≤ S := by
      rintro _ ⟨t, -, rfl⟩
      exact hψS ⟨t, rfl⟩
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    have h1 : Nat.card ((T : Subgroup Q).map ψ) ∣ 3 ^ n := hn ▸ Subgroup.card_map_dvd (T : Subgroup Q) ψ
    have h2 : Nat.card ((T : Subgroup Q).map ψ) ∣ Nat.card S := Subgroup.card_dvd_of_le hTS
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have h4 : Nat.card ((T : Subgroup Q).map ψ) = 1 := by
      rcases m with _ | m
      · simpa using hm
      · exfalso
        rw [hm] at h2
        have : 3 ∣ Nat.card S := (dvd_pow_self 3 (Nat.succ_ne_zero m)).trans h2
        exact absurd (Nat.Coprime.eq_one_of_dvd hS this) (by norm_num)
    have h5 : (T : Subgroup Q).map ψ = ⊥ := Subgroup.eq_bot_of_card_eq _ h4
    rw [Subgroup.map_eq_bot_iff] at h5
    exact h5
  set π := QuotientGroup.mk' θ with hπ
  haveI : K0.Normal := MonoidHom.normal_ker ψ
  have hKπ : (K0.map π).Normal := (inferInstance : K0.Normal).map π (QuotientGroup.mk'_surjective θ)
  have htop : K0.map π = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKπ with h | h
    · exact h
    · exfalso
      set π' := (QuotientGroup.mk' (Subgroup.center (Q ⧸ θ))).comp π with hπ'
      have hπ's : Function.Surjective π' :=
        (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective θ)
      have hTk : (T : Subgroup Q) ≤ π'.ker := by
        intro t ht
        rw [MonoidHom.mem_ker, hπ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact h ⟨t, hTK ht, rfl⟩
      have hidx : π'.ker.index ∣ (T : Subgroup Q).index := Subgroup.index_dvd_of_le hTk
      have hidx' : π'.ker.index = Nat.card ((Q ⧸ θ) ⧸ Subgroup.center (Q ⧸ θ)) := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hπ's, Subgroup.card_top]
      rw [hidx'] at hidx
      exact T.not_dvd_index (h3.trans hidx)
  have hsup : K0 ⊔ θ = ⊤ := by
    have h := Subgroup.comap_map_eq π K0
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsolv : Group.IsSolvable (Q ⧸ K0) := by
    haveI := hθs
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' K0).comp θ.subtype) ?_
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : (K0 ⊔ θ).map (QuotientGroup.mk' K0) = ⊤ := by
      rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K0)]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hK0top := eq_top_of_isPerfect_of_isSolvable_quotient hp K0 hsolv
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  have : y ∈ K0 := by rw [hK0top]; exact Subgroup.mem_top _
  exact (MonoidHom.mem_ker.mp this)

theorem map_eq_bot_of_coprime {C H : Type*} [Group C] [Group H] [Finite C] {Y0 : Subgroup C}
    (hp : Group.IsPerfect Y0) (hq : IsQuasisimple (Y0 ⧸ aschbacherSolvableCore 3 Y0))
    (h3 : 3 ∣ Nat.card ((Y0 ⧸ aschbacherSolvableCore 3 Y0) ⧸
      Subgroup.center (Y0 ⧸ aschbacherSolvableCore 3 Y0)))
    (φ : C →* H) {S : Subgroup H} (hS : Nat.Coprime 3 (Nat.card S)) (hY0S : Y0.map φ ≤ S) :
    Y0.map φ = ⊥ := by
  have e : Y0.map φ = (φ.comp Y0.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e] at hY0S ⊢
  exact range_eq_bot_of_coprime hp hq h3 _ hS hY0S

section TypeLevel

variable {C : Type} [Group C] [Finite C]

theorem thetaComponents_sup_eq_or_commutator_le {K1 K2 : Subgroup C}
    (h1 : K1 ∈ thetaComponents 3 C) (h2 : K2 ∈ thetaComponents 3 C) :
    K1 ⊔ aschbacherSolvableCore 3 C = K2 ⊔ aschbacherSolvableCore 3 C ∨
      ⁅K1, K2⁆ ≤ aschbacherSolvableCore 3 C := by
  set ρ := QuotientGroup.mk' (aschbacherSolvableCore 3 C) with hρ
  have c1 := (CFSG.RankThree.theta_quotient_component_structure h1).2.1
  have c2 := (CFSG.RankThree.theta_quotient_component_structure h2).2.1
  rcases CFSG.LocalCores.distinct_components_commute c1 c2 with he | hc
  · left
    have := congrArg (Subgroup.comap ρ) he
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  · right
    have : (⁅K1, K2⁆).map ρ = ⊥ := by rw [Subgroup.map_commutator, hc]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
    exact this

theorem le_normalizer_of_normal_of_le {N H : Subgroup C} (hN : N.Normal) (hNH : N ≤ H) :
    N ≤ Subgroup.normalizer (H : Set C) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : t * h * t⁻¹ * h⁻¹ ∈ N := by
      have := hN.conj_mem _ (N.inv_mem ht) h
      have e : t * h * t⁻¹ * h⁻¹ = t * (h * t⁻¹ * h⁻¹) := by group
      rw [e]
      exact N.mul_mem ht this
    have e2 : t * h * t⁻¹ = (t * h * t⁻¹ * h⁻¹) * h := by group
    rw [e2]
    exact H.mul_mem (hNH this) hh
  · intro hh
    have : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ ∈ H := by
      have h1 : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ * (t * h * t⁻¹)⁻¹ ∈ N := by
        have := hN.conj_mem _ ht (t * h * t⁻¹)
        have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ * (t * h * t⁻¹)⁻¹ =
            t⁻¹ * ((t * h * t⁻¹) * t * (t * h * t⁻¹)⁻¹) := by group
        rw [e]
        exact N.mul_mem (N.inv_mem ht) this
      have e2 : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ =
          (t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ * (t * h * t⁻¹)⁻¹) * (t * h * t⁻¹) := by group
      rw [e2]
      exact H.mul_mem (hNH h1) hh
    simpa [mul_assoc] using this

theorem normalClosure_le_normalizer {K : Subgroup C} (hK : K ∈ thetaComponents 3 C) :
    Subgroup.normalClosure ((K ⊔ aschbacherSolvableCore 3 C : Subgroup C) : Set C) ≤
      Subgroup.normalizer ((K ⊔ aschbacherSolvableCore 3 C : Subgroup C) : Set C) := by
  set θ := aschbacherSolvableCore 3 C with hθ
  obtain ⟨-, hθc, -, -⟩ := solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  haveI : θ.Normal := by haveI := hθc; infer_instance
  have hθN : θ ≤ Subgroup.normalizer ((K ⊔ θ : Subgroup C) : Set C) :=
    le_normalizer_of_normal_of_le inferInstance le_sup_right
  have hconj : ∀ g : C, K.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((K ⊔ θ : Subgroup C) : Set C) := by
    intro g
    have hKg : K.map (MulAut.conj g).toMonoidHom ∈ thetaComponents 3 C :=
      map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj g) hK
    rcases thetaComponents_sup_eq_or_commutator_le hKg hK with he | hc
    · intro x hx
      have hx' : x ∈ K ⊔ θ := by rw [← he]; exact Subgroup.mem_sup_left hx
      exact Subgroup.le_normalizer hx'
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      have hmap : (K ⊔ θ).map (MulAut.conj x).toMonoidHom ≤ K ⊔ θ := by
        rw [Subgroup.map_sup, sup_le_iff]
        constructor
        · rintro _ ⟨k, hk, rfl⟩
          have hcomm : x * k * x⁻¹ * k⁻¹ ∈ θ := hc (Subgroup.commutator_mem_commutator hx hk)
          have e : (MulAut.conj x).toMonoidHom k = (x * k * x⁻¹ * k⁻¹) * k := by
            simp [MulAut.conj_apply]
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hk)
        · rintro _ ⟨t, ht, rfl⟩
          exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using
            (inferInstance : θ.Normal).conj_mem t ht x)
      have hmap' : (K ⊔ θ).map (MulAut.conj x⁻¹).toMonoidHom ≤ K ⊔ θ := by
        rw [Subgroup.map_sup, sup_le_iff]
        constructor
        · rintro _ ⟨k, hk, rfl⟩
          have hxi : x⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := Subgroup.inv_mem _ hx
          have hcomm : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ ∈ θ := hc (Subgroup.commutator_mem_commutator hxi hk)
          have e : (MulAut.conj x⁻¹).toMonoidHom k = (x⁻¹ * k * x⁻¹⁻¹ * k⁻¹) * k := by
            simp [MulAut.conj_apply]
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hk)
        · rintro _ ⟨t, ht, rfl⟩
          exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using
            (inferInstance : θ.Normal).conj_mem t ht x⁻¹)
      intro h
      constructor
      · intro hh
        exact hmap ⟨h, hh, by simp [MulAut.conj_apply]⟩
      · intro hh
        have hmem : h ∈ (K ⊔ θ).map (MulAut.conj x⁻¹).toMonoidHom :=
          ⟨x * h * x⁻¹, hh, by simp [MulAut.conj_apply, mul_assoc]⟩
        exact hmap' hmem
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro z hz
  obtain ⟨y, hy, hconjy⟩ := Group.mem_conjugatesOfSet_iff.mp hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconjy
  have hy' : y ∈ K ⊔ θ := hy
  have hmemc : g * y * g⁻¹ ∈ (K ⊔ θ).map (MulAut.conj g).toMonoidHom :=
    ⟨y, hy', by simp [MulAut.conj_apply]⟩
  rw [Subgroup.map_sup] at hmemc
  have hsup : K.map (MulAut.conj g).toMonoidHom ⊔ θ.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((K ⊔ θ : Subgroup C) : Set C) := by
    refine sup_le (hconj g) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hθN (by simpa [MulAut.conj_apply] using (inferInstance : θ.Normal).conj_mem t ht g)
  exact hsup hmemc


theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hq : IsQuasisimple (Q ⧸ aschbacherSolvableCore 3 Q)) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  obtain ⟨hp, hsimp, a, b, hab⟩ := hq
  haveI : Group.IsSolvable (Q ⧸ aschbacherSolvableCore 3 Q) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect (Q ⧸ aschbacherSolvableCore 3 Q) := hp
  haveI := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := Q ⧸ aschbacherSolvableCore 3 Q)
  apply hab
  have : Subsingleton ((Q ⧸ aschbacherSolvableCore 3 Q) ⧸
      Subgroup.center (Q ⧸ aschbacherSolvableCore 3 Q)) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [Subsingleton.elim x' y']
  exact Subsingleton.elim _ _

theorem le_sup_theta_of_le {K Y Y0 N L0 : Subgroup C} (hK : K ∈ thetaComponents 3 C)
    (hYp : Group.IsPerfect Y) (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y))
    (hY0p : Group.IsPerfect Y0) (hY0q : IsQuasisimple (Y0 ⧸ aschbacherSolvableCore 3 Y0))
    (hY03 : 3 ∣ Nat.card ((Y0 ⧸ aschbacherSolvableCore 3 Y0) ⧸
      Subgroup.center (Y0 ⧸ aschbacherSolvableCore 3 Y0)))
    (hY0Y : Y0 ≤ Y) (hL0K : L0 ≤ K) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hL0N : L0 ≤ Subgroup.normalizer (N : Set C)) (hY0NL : Y0 ≤ N ⊔ L0) :
    Y ≤ K ⊔ aschbacherSolvableCore 3 C := by
  set θ := aschbacherSolvableCore 3 C with hθ
  set Kθ := K ⊔ θ with hKθ
  set E := Subgroup.normalClosure (Kθ : Set C) with hE
  haveI hEn : E.Normal := Subgroup.normalClosure_normal
  have hKθE : Kθ ≤ E := Subgroup.le_normalClosure
  have hENm : E ≤ Subgroup.normalizer (Kθ : Set C) := normalClosure_le_normalizer hK
  have hY0s : ¬ Group.IsSolvable Y0 := not_isSolvable_of_isQuasisimple hY0q
  have hL0Kθ : L0 ≤ Kθ := hL0K.trans le_sup_left
  have hY0E : Y0 ≤ E := by
    have hmap := map_eq_bot_of_coprime hY0p hY0q hY03 (QuotientGroup.mk' E)
      (S := N.map (QuotientGroup.mk' E))
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N _) hN3) (by
        refine (Subgroup.map_mono hY0NL).trans ?_
        rw [Subgroup.map_sup]
        refine sup_le le_rfl ?_
        rw [(Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hL0Kθ.trans hKθE)]
        exact bot_le)
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  have hYE : Y ≤ E := le_of_le_normalizer_of_isQuasisimple hYp hYq
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hEn]; exact le_top) hY0Y hY0E hY0s
  set Nm := Subgroup.normalizer (Kθ : Set C) with hNm
  have hY0Nm : Y0 ≤ Nm := hY0E.trans hENm
  have hKθNm : Kθ ≤ Nm := Subgroup.le_normalizer
  haveI hKθn : (Kθ.subgroupOf Nm).Normal := Subgroup.normal_in_normalizer
  have hY0Kθ : Y0 ≤ Kθ := by
    set ψ : Y0 →* ↥Nm ⧸ Kθ.subgroupOf Nm :=
      (QuotientGroup.mk' (Kθ.subgroupOf Nm)).comp (Subgroup.inclusion hY0Nm) with hψ
    set S : Subgroup (↥Nm ⧸ Kθ.subgroupOf Nm) :=
      (N.subgroupOf Nm).map (QuotientGroup.mk' (Kθ.subgroupOf Nm)) with hS
    have hS3 : Nat.Coprime 3 (Nat.card S) := by
      refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
      refine Nat.Coprime.coprime_dvd_right ?_ hN3
      let f : ↥(N.subgroupOf Nm) →* ↥N :=
        { toFun := fun x => ⟨((x : Nm) : C), Subgroup.mem_subgroupOf.mp x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Subgroup.card_dvd_of_injective f fun x y hxy => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun z : ↥N => (z : C)) hxy
    have hrange : ψ.range ≤ S := by
      rintro _ ⟨y, rfl⟩
      have hyNL : (y : C) ∈ N ⊔ L0 := hY0NL y.2
      have hmul : (y : C) ∈ ((N : Set C) * (L0 : Set C)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left N L0 hL0N]; exact hyNL
      obtain ⟨n, hn, l, hl, hnl⟩ := hmul
      have hlNm : l ∈ Nm := hKθNm (hL0Kθ hl)
      have hnNm : n ∈ Nm := by
        have : n = (y : C) * l⁻¹ := by rw [← hnl]; group
        rw [this]; exact Nm.mul_mem (hY0Nm y.2) (Nm.inv_mem hlNm)
      refine ⟨⟨n, hnNm⟩, Subgroup.mem_subgroupOf.mpr hn, ?_⟩
      show (QuotientGroup.mk (⟨n, hnNm⟩ : Nm) : ↥Nm ⧸ Kθ.subgroupOf Nm) =
        QuotientGroup.mk (Subgroup.inclusion hY0Nm y)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((⟨n, hnNm⟩ : Nm)⁻¹ * Subgroup.inclusion hY0Nm y : Nm) : C) = l := by
        show n⁻¹ * (y : C) = l
        rw [← hnl]; group
      rw [e]
      exact hL0Kθ hl
    have hb := range_eq_bot_of_coprime hY0p hY0q hY03 ψ hS3 hrange
    intro y hy
    have h1 : ψ ⟨y, hy⟩ = 1 := by
      have : ψ ⟨y, hy⟩ ∈ ψ.range := ⟨⟨y, hy⟩, rfl⟩
      rw [hb] at this
      exact this
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  exact le_of_le_normalizer_of_isQuasisimple hYp hYq (hYE.trans hENm) hY0Y hY0Kθ hY0s

end TypeLevel


section Transport

noncomputable def thetaQuotEquiv {P Q : Type*} [Group P] [Group Q] [Finite P] (e : P ≃* Q) :
    P ⧸ aschbacherSolvableCore 3 P ≃* Q ⧸ aschbacherSolvableCore 3 Q :=
  QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)

theorem isPerfect_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : Group.IsPerfect P) : Group.IsPerfect Q :=
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem isQuasisimple_theta_of_mulEquiv {P Q : Type*} [Group P] [Group Q] [Finite P]
    (e : P ≃* Q) (h : IsQuasisimple (P ⧸ aschbacherSolvableCore 3 P)) :
    IsQuasisimple (Q ⧸ aschbacherSolvableCore 3 Q) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (thetaQuotEquiv e) h

theorem card_center_quot_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    Nat.card (P ⧸ Subgroup.center P) = Nat.card (Q ⧸ Subgroup.center Q) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

end Transport

variable [Finite G]

theorem le_sup_theta_centralizer {d : G} {K Yd YB N L0 : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d) (hYdC : Yd ≤ Subgroup.centralizer ({d} : Set G))
    (hYdp : Group.IsPerfect Yd) (hYdq : IsQuasisimple (Yd ⧸ aschbacherSolvableCore 3 Yd))
    (hYBp : Group.IsPerfect YB) (hYBq : IsQuasisimple (YB ⧸ aschbacherSolvableCore 3 YB))
    (hYB3 : 3 ∣ Nat.card ((YB ⧸ aschbacherSolvableCore 3 YB) ⧸
      Subgroup.center (YB ⧸ aschbacherSolvableCore 3 YB)))
    (hYBYd : YB ≤ Yd) (hL0K : L0 ≤ K) (hNC : N ≤ Subgroup.centralizer ({d} : Set G))
    (hN3 : Nat.Coprime 3 (Nat.card N)) (hL0N : L0 ≤ Subgroup.normalizer (N : Set G))
    (hYBNL : YB ≤ N ⊔ L0) :
    Yd ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  obtain ⟨hKC, hK'⟩ := (mem_thetaComponentsIn_iff (H := C)).mp
    ((thetaComponentsAt_eq_thetaComponentsIn d) ▸ hK)
  have hYBC : YB ≤ C := hYBYd.trans hYdC
  have hL0C : L0 ≤ C := hL0K.trans hKC
  set Y' := Yd.subgroupOf C
  set Y0' := YB.subgroupOf C
  set K' := K.subgroupOf C
  set N' := N.subgroupOf C
  set L0' := L0.subgroupOf C
  have eY := (Subgroup.subgroupOfEquivOfLe hYdC).symm
  have eB := (Subgroup.subgroupOfEquivOfLe hYBC).symm
  have hY'p : Group.IsPerfect Y' := isPerfect_of_mulEquiv eY hYdp
  have hY'q := isQuasisimple_theta_of_mulEquiv eY hYdq
  have hY0'p : Group.IsPerfect Y0' := isPerfect_of_mulEquiv eB hYBp
  have hY0'q := isQuasisimple_theta_of_mulEquiv eB hYBq
  have hY0'3 : 3 ∣ Nat.card ((Y0' ⧸ aschbacherSolvableCore 3 Y0') ⧸
      Subgroup.center (Y0' ⧸ aschbacherSolvableCore 3 Y0')) := by
    rwa [← card_center_quot_of_mulEquiv (thetaQuotEquiv eB)]
  have hY0'Y' : Y0' ≤ Y' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hYBYd (Subgroup.mem_subgroupOf.mp hx))
  have hL0'K' : L0' ≤ K' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hL0K (Subgroup.mem_subgroupOf.mp hx))
  have hN'3 : Nat.Coprime 3 (Nat.card N') := by
    have e := Subgroup.subgroupOfEquivOfLe hNC
    rw [Nat.card_congr e.toEquiv]
    exact hN3
  have hL0'N' : L0' ≤ Subgroup.normalizer (N' : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    show ((y : C) : G) ∈ N ↔ ((x * y * x⁻¹ : C) : G) ∈ N
    rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hL0N (Subgroup.mem_subgroupOf.mp hx)) y
  have hY0'NL : Y0' ≤ N' ⊔ L0' := by
    intro x hx
    have hxNL : (x : G) ∈ N ⊔ L0 := hYBNL (Subgroup.mem_subgroupOf.mp hx)
    have hmul : (x : G) ∈ ((N : Set G) * (L0 : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N L0 hL0N]; exact hxNL
    obtain ⟨n, hn, l, hl, hnl⟩ := hmul
    have hlC : l ∈ C := hL0C hl
    have hnC : n ∈ C := hNC hn
    have hx' : x = ⟨n, hnC⟩ * ⟨l, hlC⟩ := Subtype.ext hnl.symm
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hn))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hl))
  have key := le_sup_theta_of_le hK' hY'p hY'q hY0'p hY0'q hY0'3 hY0'Y' hL0'K' hN'3 hL0'N' hY0'NL
  intro y hy
  have hyC : y ∈ C := hYdC hy
  have hy' : (⟨y, hyC⟩ : C) ∈ K' ⊔ aschbacherSolvableCore 3 C :=
    key (Subgroup.mem_subgroupOf.mpr hy)
  have hmap : (K' ⊔ aschbacherSolvableCore 3 C).map C.subtype =
      K ⊔ inSubgroup (aschbacherSolvableCore 3) C := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKC]
    rfl
  rw [← hmap]
  exact ⟨⟨y, hyC⟩, hy', rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
