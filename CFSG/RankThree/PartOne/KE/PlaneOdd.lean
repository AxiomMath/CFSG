module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

theorem odd_card_sup_of_odd {G : Type*} [Group G] [Finite G] {N I : Subgroup G}
    (hI : I ≤ Subgroup.normalizer (N : Set G)) (hN : Odd (Nat.card N)) (hIo : Odd (Nat.card I)) :
    Odd (Nat.card ↥(N ⊔ I)) := by
  classical
  set W : Subgroup G := N ⊔ I with hW
  have hNW : N ≤ W := le_sup_left
  have hIW : I ≤ W := le_sup_right
  have hWnorm : W ≤ Subgroup.normalizer (N : Set G) :=
    sup_le Subgroup.le_normalizer hI
  have hnormal : (N.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).2
    hWnorm
  let f : I →* W ⧸ N.subgroupOf W :=
    (QuotientGroup.mk' (N.subgroupOf W)).comp (Subgroup.inclusion hIW)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    have hw : (w : G) ∈ ((N : Set G) * (I : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N I hI]
      exact w.2
    obtain ⟨n, hn, i, hi, hni⟩ := hw
    have hni' : n * i = (w : G) := hni
    refine ⟨⟨i, hi⟩, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hIW ⟨i, hi⟩) : W ⧸ N.subgroupOf W) =
      QuotientGroup.mk w
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : i⁻¹ * (n * i) ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (hI (inv_mem hi)) n).1 hn
      simpa [mul_assoc] using this
    have h2 : (((Subgroup.inclusion hIW ⟨i, hi⟩)⁻¹ * w : W) : G) = i⁻¹ * (n * i) := by
      rw [Subgroup.coe_mul, hni']
      rfl
    rw [h2]
    exact h1
  have hq : Nat.card (W ⧸ N.subgroupOf W) ∣ Nat.card I := Subgroup.card_dvd_of_surjective hfsurj
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf W)
  have hN' : Nat.card (N.subgroupOf W) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  rw [hcard, hN']
  exact (Odd.of_dvd_nat hIo hq).mul hN

theorem odd_card_commutator_of_odd_inner {C : Type*} [Group C] [Finite C]
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C))) {S A : Subgroup (MulAut C)}
    (hSA : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S)
    (hinn : Odd (Nat.card ↥(S ⊓ (MulAut.conj : C →* MulAut C).range))) :
    Odd (Nat.card ↥(⁅S, A⁆ : Subgroup (MulAut C))) := by
  classical
  set N : Subgroup (MulAut C) := ⁅S, A⁆ with hN
  have hNS : N ≤ S := Subgroup.commutator_le.2 fun s hs a ha => by
    have h := hSA a ha s⁻¹ (inv_mem hs)
    have e : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hs h
  set π : MulAut C →* Outer C := QuotientGroup.mk' (inner C) with hπ
  let φ : N →* Outer C := π.comp N.subtype
  have hrange : φ.range ≤ commutator (Outer C) := by
    have h1 : φ.range = N.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, hN, Subgroup.map_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hrodd : Odd (Nat.card φ.range) := by
    have hcomm : Odd (Nat.card (commutator (Outer C))) := Nat.not_even_iff_odd.1 fun h =>
      hout (even_iff_two_dvd.1 h)
    exact Odd.of_dvd_nat hcomm (Subgroup.card_dvd_of_le hrange)
  have hkodd : Odd (Nat.card φ.ker) := by
    refine Odd.of_dvd_nat hinn (Subgroup.card_dvd_of_injective
      (((N.subtype.comp φ.ker.subtype).codRestrict (S ⊓ (MulAut.conj : C →* MulAut C).range)
        fun x => ?_)) fun a b hab => ?_)
    · refine ⟨hNS x.1.2, ?_⟩
      have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff (N := inner C) (x.1 : MulAut C)).1 h
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(S ⊓ (MulAut.conj : C →* MulAut C).range) => (z : MulAut C)) hab
  have hcard : Nat.card φ.ker * φ.ker.index = Nat.card N := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker φ] at hcard
  rw [← hcard]
  exact hkodd.mul hrodd

theorem odd_card_inf_range_of_solvable {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hsolv : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal →
      Group.IsSolvable V → Odd (Nat.card V)) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range)) := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    rw [hD] at hd
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hYSD : S.comap Int ≤ D := by
    intro y hy
    have hyM : Int y ∈ M := hSM hy
    rw [hM] at hyM
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyM).2 (Int x) rfl
    rw [hD]
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hinj (by rw [map_mul, map_mul]; exact h1.symm))
  have hVnormal : ((S.comap Int).subgroupOf D).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    change Int ((d : C) * (v : C) * (d : C)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnorm _ (hIntD d d.2) _ hv⟩
  have hVsol : Group.IsSolvable ((S.comap Int).subgroupOf D) := by
    let f : ((S.comap Int).subgroupOf D) →* S :=
      ((Int.comp D.subtype).comp ((S.comap Int).subgroupOf D).subtype).codRestrict S
        fun v => Subgroup.mem_subgroupOf.1 v.2
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab)))
  have hodd : Odd (Nat.card ((S.comap Int).subgroupOf D)) := by
    rw [hD] at hVnormal hVsol ⊢
    exact hsolv _ hVnormal hVsol
  have e1 : Nat.card ((S.comap Int).subgroupOf D) = Nat.card (S.comap Int) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYSD).toEquiv
  have e2 : (S.comap Int).map Int = S ⊓ Int.range := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨z, hy, rfl⟩
  rw [← e2, Subgroup.card_map_of_injective hinj, ← e1]
  exact hodd

theorem conj_mem_commutator_of_mem_left {G : Type*} [Group G] {S A : Subgroup G} {s : G}
    (hs : s ∈ S) {y : G} (hy : y ∈ (⁅S, A⁆ : Subgroup G)) :
    s * y * s⁻¹ ∈ (⁅S, A⁆ : Subgroup G) := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨u, hu, a, ha, rfl⟩ := hz
    have e : s * ⁅u, a⁆ * s⁻¹ = ⁅s * u, a⁆ * ⁅s, a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hs hu) ha)
      (inv_mem (Subgroup.commutator_mem_commutator hs ha))
  | one => simp
  | mul y z _ _ hy hz =>
    have : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
    rw [this]
    exact mul_mem hy hz
  | inv y _ hy =>
    have : s * y⁻¹ * s⁻¹ = (s * y * s⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem le_normalizer_commutator_left {G : Type*} [Group G] (S A : Subgroup G) :
    S ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup G) : Set G) := fun s hs =>
  Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_commutator_of_mem_left hs hy,
    fun hy => by
      have := conj_mem_commutator_of_mem_left (inv_mem hs) hy
      simpa [mul_assoc] using this⟩

theorem native_plane_of_odd_kernels_abstract {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥)
    (hsolv : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V))
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range)
    (hactor : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : C →* MulAut C).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C)))))) :
    ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : C →* MulAut C).range →
            inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) = ⊥ ∧
              autPlaneProduct p B A t = ⊥) := by
  intro B hB A hAB hA hcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have htp : orderOf t = p := orderOf_eq_prime (hpow t htA) ht1
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
    obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
        B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
      ⟨_, rfl⟩
    have hAM : A ≤ M := by
      intro a ha
      rw [hM]
      refine Subgroup.mem_inf.2 ⟨hAB ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (mul_comm' (⟨_, htA⟩ : A) ⟨a, ha⟩)
    have hSM : S ≤ M := by
      rw [hS]
      exact Subgroup.map_subtype_le _
    have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
      intro m hm s hs
      rw [hS] at hs ⊢
      obtain ⟨s', hs', rfl⟩ := hs
      refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
      exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
    have hinn := odd_card_inf_range_of_solvable (B := B) hp hC hB (hsolv x hxp)
    rw [← hM, ← hS] at hinn
    have hN : Odd (Nat.card ↥(⁅S, A⁆ : Subgroup (MulAut C))) :=
      odd_card_commutator_of_odd_inner hout (fun a ha s hs => hSnorm a (hAM ha) s hs) hinn
    have hIS : autThetaT p B A ≤ S := by
      have := hthetaT_le (MulAut.conj x) htA ht1
      rwa [← hM, ← hS] at this
    have hI : Odd (Nat.card ↥(autThetaT p B A)) := by
      by_cases hnon : ∃ b ∈ A, b ∉ (MulAut.conj : C →* MulAut C).range
      · obtain ⟨b, hbA, hbn⟩ := hnon
        have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
        have hbp : orderOf b = p := orderOf_eq_prime (hpow b hbA) hb1
        have hθb := hcore B hB b (hAB hbA) hbn hbp
        have hle := hthetaT_le b hbA hb1
        rw [hθb] at hle
        have hbot : autThetaT p B A = ⊥ := le_bot_iff.1 hle
        rw [hbot, Subgroup.card_bot]
        exact odd_one
      · push Not at hnon
        obtain ⟨a, haA, ha1, haodd⟩ := hactor B hB A hAB hA hcard hnon
        exact Odd.of_dvd_nat haodd (Subgroup.card_dvd_of_le (hthetaT_le a haA ha1))
    have hplane : autPlaneProduct p B A (MulAut.conj x) = ⁅S, A⁆ ⊔ autThetaT p B A := by
      rw [autPlaneProduct, ← hM, ← hS]
    have hodd := odd_card_sup_of_odd ((hIS.trans (le_normalizer_commutator_left S A))) hN hI
    rw [hplane]
    exact ⟨hodd.not_two_dvd_nat, fun h => absurd ⟨x, rfl⟩ h⟩
  · have hθt := hcore B hB t (hAB htA) htn htp
    have hT : autThetaT p B A = ⊥ :=
      le_bot_iff.1 ((hthetaT_le t htA ht1).trans hθt.le)
    have hplane : autPlaneProduct p B A t = ⊥ := by
      rw [autPlaneProduct, hθt, Subgroup.commutator_bot_left, hT, sup_bot_eq]
    refine ⟨?_, fun _ => ⟨hθt, hplane⟩⟩
    rw [hplane, Subgroup.card_bot]
    omega

theorem planeLocalCoreOdd_of_odd_kernels_abstract {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥)
    (hsolv : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → Odd (Nat.card V))
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range)
    (hactor : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : C →* MulAut C).range →
        ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C)))))) :
    PlaneLocalCoreOdd p C := fun B hB A hAB hA hcard t htA ht1 =>
  (native_plane_of_odd_kernels_abstract hp hC hsolv hout hcore hactor B hB A hAB hA hcard t
    htA ht1).1

end CFSG.RankThree.PartOne.KE
