module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem isCyclic_sup_of_commute_of_coprime {G : Type*} [Group G] (U₁ U₂ : Subgroup G)
    [hU₁ : IsCyclic U₁] [hU₂ : IsCyclic U₂] (hc : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a)
    (hcop : (Nat.card U₁).Coprime (Nat.card U₂)) : IsCyclic ↥(U₁ ⊔ U₂) := by
  let φ : U₁ × U₂ →* G := MonoidHom.noncommCoprod U₁.subtype U₂.subtype
    (fun m n => hc m m.2 n n.2)
  have hprod : IsCyclic (U₁ × U₂) := Group.isCyclic_prod_iff.2 ⟨hU₁, hU₂, hcop⟩
  have hrange : φ.range = U₁ ⊔ U₂ :=
    (MonoidHom.noncommCoprod_range U₁.subtype U₂.subtype _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have hs : IsCyclic φ.range :=
    isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact (MulEquiv.subgroupCongr hrange).isCyclic.1 hs

theorem mem_zpowers_of_mem_inf_of_not_le {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {A R : Subgroup G} (hA : Nat.card A = p ^ 2) {t : G} (htA : t ∈ A) (htR : t ∈ R)
    (ht : orderOf t = p) (hnot : ¬ A ≤ R) {a : G} (haA : a ∈ A) (haR : a ∈ R) :
    a ∈ Subgroup.zpowers t := by
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact pow_ne_zero 2 hp.ne_zero)
  have hIA : A ⊓ R ≤ A := inf_le_left
  have hIfin : Finite ↥(A ⊓ R) :=
    Finite.of_injective (Subgroup.inclusion hIA) (Subgroup.inclusion_injective hIA)
  have hzI : Subgroup.zpowers t ≤ A ⊓ R := by
    rw [Subgroup.zpowers_le]
    exact ⟨htA, htR⟩
  have hzcard : Nat.card (Subgroup.zpowers t) = p := by rw [Nat.card_zpowers, ht]
  have h1 : p ∣ Nat.card ↥(A ⊓ R) := hzcard ▸ Subgroup.card_dvd_of_le hzI
  have h2 : Nat.card ↥(A ⊓ R) ∣ p ^ 2 := hA ▸ Subgroup.card_dvd_of_le hIA
  have hne : Nat.card ↥(A ⊓ R) ≠ p ^ 2 := by
    intro h
    apply hnot
    have : A ⊓ R = A := Subgroup.eq_of_le_of_card_ge hIA (by rw [h, hA])
    rw [← this]
    exact inf_le_right
  obtain ⟨k, hk, hkI⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hIp : Nat.card ↥(A ⊓ R) = p := by
    have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk2 with rfl | rfl | rfl
    · exfalso
      rw [hkI, pow_zero] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
    · simpa using hkI
    · exact absurd hkI hne
  have heq : Subgroup.zpowers t = A ⊓ R :=
    Subgroup.eq_of_le_of_card_ge hzI (by rw [hIp, hzcard])
  rw [heq]
  exact ⟨haA, haR⟩

variable {C : Type*} [Group C]

theorem isCyclic_ker_outerHom_of_solvable [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C} (hxp : orderOf x = p)
    (hsolv : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal →
      Group.IsSolvable V → IsCyclic V)
    {A : Subgroup (MulAut C)} [hA : IsElementaryAbelian p A] (hAB : A ≤ B)
    (hcard : Nat.card A = p ^ 2) (hnot : ¬ A ≤ (MulAut.conj : C →* MulAut C).range)
    (htA : (MulAut.conj x : MulAut C) ∈ A) :
    IsCyclic (outerHom (A ⊔ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))))).ker := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hM, ← hS]
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
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
  have hSp : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := M) hp).2.2.1
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
  have hVcyc : IsCyclic ((S.comap Int).subgroupOf D) := by
    rw [hD] at hVnormal hVsol ⊢
    exact hsolv _ hVnormal hVsol
  have hYScyc : IsCyclic (S.comap Int) :=
    (Subgroup.subgroupOfEquivOfLe hYSD).isCyclic.1 hVcyc
  have hYScard : Nat.card (S.comap Int) ∣ Nat.card S :=
    Subgroup.card_dvd_of_injective ((Int.comp (S.comap Int).subtype).codRestrict S fun y => y.2)
      fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  have hcop : (Nat.card (S.comap Int)).Coprime (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hxp]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hSp (h.trans hYScard)).symm
  have hUcyc : IsCyclic ↥(S.comap Int ⊔ Subgroup.zpowers x) := by
    have := hYScyc
    refine isCyclic_sup_of_commute_of_coprime _ _ (fun a ha b hb => ?_) hcop
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h1 : a * x = x * a := by
      have := hYSD ha
      rw [hD] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    exact ((Commute.zpow_right (show Commute a x from h1) k)).eq
  have hAnorm : A ≤ Subgroup.normalizer (S : Set (MulAut C)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSnorm a (hAM ha) s hs, fun hs => ?_⟩
    have h1 := hSnorm a⁻¹ (M.inv_mem (hAM ha)) _ hs
    have : a⁻¹ * (a * s * a⁻¹) * a⁻¹⁻¹ = s := by group
    rwa [this] at h1
  have hJmul : ((A ⊔ S : Subgroup (MulAut C)) : Set (MulAut C)) =
      (A : Set (MulAut C)) * (S : Set (MulAut C)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A S hAnorm
  have hYU : (A ⊔ S).comap Int ≤ S.comap Int ⊔ Subgroup.zpowers x := by
    intro y hy
    have hyJ : Int y ∈ ((A ⊔ S : Subgroup (MulAut C)) : Set (MulAut C)) := hy
    rw [hJmul] at hyJ
    obtain ⟨a, ha, s, hs, has⟩ := hyJ
    have hapow : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    have hspow : s ^ Nat.card S = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := S) (x := (⟨s, hs⟩ : S)))
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
    have has' : a * s = Int y := has
    obtain ⟨π, hπ⟩ : ∃ π : MulAut C →* Outer C, π = QuotientGroup.mk' (inner C) := ⟨_, rfl⟩
    have hπInt : ∀ u : C, π (Int u) = 1 := fun u => by
      rw [hπ]
      exact (QuotientGroup.eq_one_iff (N := inner C) _).2 ⟨u, rfl⟩
    have hπa : π a = (π s)⁻¹ := by
      have h1 : π a * π s = 1 := by rw [← map_mul, has', hπInt]
      exact eq_inv_of_mul_eq_one_left h1
    have hπap : (π a) ^ p = 1 := by rw [← map_pow, hapow, map_one]
    have hπaS : (π a) ^ Nat.card S = 1 := by
      rw [hπa, inv_pow, ← map_pow, hspow, map_one, inv_one]
    have hgcd : Nat.gcd p (Nat.card S) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hSp
    have hπa1 : π a = 1 := by
      have := pow_gcd_eq_one.2 ⟨hπap, hπaS⟩
      rwa [hgcd, pow_one] at this
    have haInn : a ∈ Int.range := by
      have h1 : (QuotientGroup.mk' (inner C)) a = 1 := by rw [← hπ]; exact hπa1
      exact (QuotientGroup.eq_one_iff (N := inner C) a).1 h1
    have haM : a ∈ Subgroup.zpowers (Int x) := by
      refine mem_zpowers_of_mem_inf_of_not_le hp (A := A) (R := Int.range) hcard htA
        ⟨x, rfl⟩ ?_ hnot ha haInn
      rw [orderOf_injective Int hinj x]
      exact hxp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 haM
    have hakx : a = Int (x ^ k) := by rw [map_zpow, hk]
    have hz : x ^ (-k) * y ∈ S.comap Int := by
      change Int (x ^ (-k) * y) ∈ S
      have hsa : s = a⁻¹ * Int y := by rw [← has]; group
      rw [map_mul, map_zpow, zpow_neg, ← map_zpow, ← hakx, ← hsa]
      exact hs
    have hy' : y = x ^ k * (x ^ (-k) * y) := by group
    rw [hy']
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x k))
      (Subgroup.mem_sup_left hz)
  have hYcyc : IsCyclic ((A ⊔ S).comap Int) := by
    have := hUcyc
    exact isCyclic_of_injective (Subgroup.inclusion hYU) (Subgroup.inclusion_injective hYU)
  let g0 : ((A ⊔ S).comap Int) →* ↥(A ⊔ S) :=
    (Int.comp ((A ⊔ S).comap Int).subtype).codRestrict (A ⊔ S) fun y => y.2
  let g : ((A ⊔ S).comap Int) →* (outerHom (A ⊔ S)).ker :=
    g0.codRestrict (outerHom (A ⊔ S)).ker fun y => (mem_ker_outerHom (g0 y)).2 ⟨y, rfl⟩
  refine isCyclic_of_surjective g ?_
  intro d
  obtain ⟨y, hy⟩ := (mem_ker_outerHom d.1).1 d.2
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change Int y ∈ A ⊔ S
    rw [hy]
    exact d.1.2
  · apply Subtype.ext
    apply Subtype.ext
    exact hy

theorem native_plane_of_solvable_cyclic_abstract [Finite C] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hC : Subgroup.center C = ⊥)
    (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q)
    (hcent : (∃ b : MulAut C, b ∉ (MulAut.conj : C →* MulAut C).range ∧ orderOf b = p) →
      ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
        V.Normal → Group.IsSolvable V → IsCyclic V)
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) :
    ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        ¬ A ≤ (MulAut.conj : C →* MulAut C).range ∧
        autThetaT p B A = ⊥ ∧
        ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : C →* MulAut C).range →
            inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) = ⊥ ∧
              autPlaneProduct p B A t = ⊥) := by
  intro B hB A hAB hA hcard
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hnot : ¬ A ≤ (MulAut.conj : C →* MulAut C).range :=
    not_le_range_conj_of_cyclic hp hC hcyc hpow hcard
  obtain ⟨b, hbA, hbn⟩ : ∃ b ∈ A, b ∉ (MulAut.conj : C →* MulAut C).range := by
    by_contra hcon
    refine hnot fun a ha => ?_
    by_contra h
    exact hcon ⟨a, ha, h⟩
  have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
  have hbp : orderOf b = p := orderOf_eq_prime (hpow b hbA) hb1
  have hθb := hcore B hB b (hAB hbA) hbn hbp
  have hθT : autThetaT p B A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    simp only [autThetaT, Subgroup.mem_iInf] at hy
    have h1 := hy b hbA hb1
    rw [hθb] at h1
    exact h1
  refine ⟨hnot, hθT, fun t htA ht1 => ?_⟩
  have htp : orderOf t = p := orderOf_eq_prime (hpow t htA) ht1
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
    obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
        B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
    have hAM : A ≤ M := by
      intro a ha
      rw [hM]
      refine Subgroup.mem_inf.2 ⟨hAB ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (mul_comm' (⟨_, htA⟩ : A) ⟨a, ha⟩)
    have hSM : inSubgroup (aschbacherSolvableCore p) M ≤ M := Subgroup.map_subtype_le _
    have hAodd : Odd (Nat.card A) := by
      rw [hcard]
      exact Odd.pow (hp.odd_of_ne_two (by omega))
    have hD := isCyclic_ker_outerHom_of_solvable hp hC hB hxp
      (hcent ⟨b, hbn, hbp⟩ x hxp) hAB hcard hnot htA
    have hAJ : A ≤ A ⊔ inSubgroup (aschbacherSolvableCore p) M := le_sup_left
    have hSJ : inSubgroup (aschbacherSolvableCore p) M ≤
        A ⊔ inSubgroup (aschbacherSolvableCore p) M := le_sup_right
    rw [← hM] at hD
    have hodd := odd_card_commutator_of_cyclic_ker hout
      (M := A ⊔ inSubgroup (aschbacherSolvableCore p) M) hSJ hAJ hAodd hD
    have hplane : autPlaneProduct p B A (MulAut.conj x) =
        ⁅inSubgroup (aschbacherSolvableCore p) M, A⁆ := by
      rw [autPlaneProduct, hθT, sup_bot_eq, hM]
    rw [hplane]
    exact ⟨hodd.not_two_dvd_nat, fun h => absurd ⟨x, rfl⟩ h⟩
  · have hθt := hcore B hB t (hAB htA) htn htp
    have hplane : autPlaneProduct p B A t = ⊥ := by
      rw [autPlaneProduct, hθt, Subgroup.commutator_bot_left, hθT, sup_bot_eq]
    refine ⟨?_, fun _ => ⟨hθt, hplane⟩⟩
    rw [hplane, Subgroup.card_bot]
    omega

theorem planeLocalCoreOdd_of_solvable_cyclic_abstract [Finite C] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hC : Subgroup.center C = ⊥)
    (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q)
    (hcent : (∃ b : MulAut C, b ∉ (MulAut.conj : C →* MulAut C).range ∧ orderOf b = p) →
      ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
        V.Normal → Group.IsSolvable V → IsCyclic V)
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) :
    PlaneLocalCoreOdd p C := fun B hB A hAB hA hcard t htA ht1 =>
  ((native_plane_of_solvable_cyclic_abstract hp hp3 hC hcyc hcent hout hcore B hB A hAB hA
    hcard).2.2 t htA ht1).1

end CFSG.RankThree.PartOne.KE
