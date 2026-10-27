module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_le_centralizer {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hKθ : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h9 : Nat.card (A ⊓ K : Subgroup G) = 9) {c : G} (hcA : c ∈ A) (hcK : c ∈ K) {n : G}
    (hnK : n ∈ K) (hnA : n ∈ Subgroup.normalizer (A : Set G)) {k : ℕ} (hn3 : n ^ 3 ^ k = 1)
    (hnc : n * c = c * n) (hnmove : ∃ x ∈ A, n * x * n⁻¹ ≠ x) :
    ∃ S : Sylow 3 K, (⟨c, hcK⟩ : K) ∈ (S : Subgroup K) ∧
      (S : Subgroup K) ≤ Subgroup.centralizer ({(⟨c, hcK⟩ : K)} : Set K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set c' : K := ⟨c, hcK⟩ with hc'
  set n' : K := ⟨n, hnK⟩ with hn'
  set E := (A ⊓ K).subgroupOf K with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hnE : Subgroup.zpowers n' ≤ Subgroup.normalizer (E : Set K) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : (x : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hnA _).mp hx'.1,
      K.mul_mem (K.mul_mem hnK hx'.2) (K.inv_mem hnK)⟩
  have hn'3 : n' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hn3)
  have hQ3 : IsPGroup 3 (Subgroup.zpowers n' ⊔ E : Subgroup K) :=
    (isPGroup_zpowers_of_pow hn'3).to_sup_of_normal_right' hE3 hnE
  set Q : Subgroup K := Subgroup.zpowers n' ⊔ E with hQ
  have hQC : Q ≤ Subgroup.centralizer ({c'} : Set K) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hnc
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      exact Subtype.ext (hcomm _ hxA c hcA)
  have hcQ : c' ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ⟨hcA, hcK⟩)
  have hnE' : n' ∉ E := by
    intro hnE'
    obtain ⟨x, hxA, hx⟩ := hnmove
    apply hx
    have hnA' : n ∈ A := (Subgroup.mem_subgroupOf.mp hnE').1
    rw [hcomm n hnA' x hxA, mul_inv_cancel_right]
  have hQ27 : 27 ≤ Nat.card Q := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ3
    have hEQ : E ≤ Q := le_sup_right
    have h9dvd : 9 ∣ 3 ^ j := hj ▸ hE9 ▸ Subgroup.card_dvd_of_le hEQ
    have hj2 : 2 ≤ j := by
      by_contra hlt
      push Not at hlt
      interval_cases j <;> norm_num at h9dvd
    have hj3 : j ≠ 2 := by
      rintro rfl
      apply hnE'
      have heq : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (by rw [hj, hE9]; norm_num)
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers n')
    rw [hj]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨S, hQS⟩ := hQ3.exists_le_sylow
  have hS27 : Nat.card (S : Subgroup K) ≤ 27 := by
    have hinj := injOn_mk_of_isPGroup Nat.prime_three S.isPGroup'
    have hcard : Nat.card ((S : Subgroup K).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) = Nat.card (S : Subgroup K) := by
      change Nat.card (↑((S : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) :
        Set (K ⧸ aschbacherSolvableCore 3 K)) = Nat.card ((S : Subgroup K) : Set K)
      rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    have hdvd : Nat.card (S : Subgroup K) ∣ 604800 := by
      rw [← hcard, ← KFacts.KS14.card_eq_of_j2 hKθ]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [hi] at hdvd ⊢
    by_contra hlt
    push Not at hlt
    have hi4 : 4 ≤ i := by
      by_contra h4
      push Not at h4
      interval_cases i <;> norm_num at hlt
    have h81 : 81 ∣ 604800 := by
      have : 3 ^ 4 ∣ 3 ^ i := Nat.pow_dvd_pow 3 hi4
      exact (show (81 : ℕ) = 3 ^ 4 by norm_num) ▸ this.trans hdvd
    norm_num at h81
  have hSQ : (S : Subgroup K) = Q :=
    (Subgroup.eq_of_le_of_card_ge hQS (by omega)).symm
  exact ⟨S, hSQ ▸ hcQ, hSQ ▸ hQC⟩

end Sylow

section ModTheta

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_forall_mem_theta (h415 : Sec4.Item4_15) {K L₀ : Subgroup G} {c : G}
    (hcK : c ∈ K) (hc1 : c ≠ 1)
    (hKθ : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hSyl : ∃ S : Sylow 3 K, (⟨c, hcK⟩ : K) ∈ (S : Subgroup K) ∧
      (S : Subgroup K) ≤ Subgroup.centralizer ({(⟨c, hcK⟩ : K)} : Set K))
    (hIL : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ≤ L₀)
    {y : G} (hyK : y ∈ K) (hyc : y * c = c * y) (hy3 : y ^ 3 = 1)
    (hy : ∀ i ∈ inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)),
      i⁻¹ * (y * i * y⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L₀) :
    y ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z : K := ⟨c, hcK⟩ with hz
  set y' : K := ⟨y, hyK⟩ with hy'
  have hz1 : z ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hJQ := Sec13.map_residual_centralizer_eq h415 hKθ hz1 hSyl
  obtain ⟨hz1', hzP⟩ := Sec13.bar_facts_of_central hz1 hSyl
  set N := aschbacherSolvableCore 3 K with hN
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set Cbar := Subgroup.centralizer ({π z} : Set (K ⧸ N)) with hCbar
  set I' := inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set K)) with hI'
  have hII' : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) =
      I'.map K.subtype := Sec13.residual_inf_centralizer_eq_map hcK
  have htop : perfectResidual ↥Cbar = ⊤ :=
    KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hKθ hz1' hzP
  have hCtc : Sec4.IsTripleCover ↥Cbar (alternatingGroup (Fin 6)) :=
    KFacts.KS14.j2_centralizer_isTripleCover h415 hKθ hz1' hzP
  have hCq : IsQuasisimple ↥Cbar :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (Sec14.j2_centralizer_residual_quasisimple h415 hKθ hz1' hzP)
  have hCθ : aschbacherSolvableCore 3 ↥Cbar = ⊥ :=
    Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hCq
      (IsPGroup.of_card (n := 1) (by rw [hCtc.1, pow_one]))
  let ρ : I' →* Cbar := (π.comp I'.subtype).codRestrict Cbar fun x =>
    hJQ ▸ Subgroup.mem_map_of_mem π x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  set N₁ : Subgroup I' :=
    (inSubgroup (aschbacherSolvableCore 3) L₀).comap (K.subtype.comp I'.subtype) with hN₁
  have hIG : ∀ x : I', ((x : K) : G) ∈ L₀ := fun x =>
    hIL (hII' ▸ Subgroup.mem_map_of_mem K.subtype x.2)
  have hN₁n : N₁.Normal := ⟨fun x hx g => by
    rw [hN₁, Subgroup.mem_comap] at hx ⊢
    simpa using Sec13.conj_mem_inSubgroup_theta (hIG g) hx⟩
  obtain ⟨hLs, -, hLp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L₀) Nat.prime_three
  have hN₁θ : ∀ u : N₁, (⟨(((u : I') : K) : G), hIG u⟩ : L₀) ∈ aschbacherSolvableCore 3 L₀ :=
    fun u => (Subgroup.mem_map_iff_mem L₀.subtype_injective).mp u.2
  let ι : N₁ →* aschbacherSolvableCore 3 L₀ :=
    (((K.subtype.comp I'.subtype).comp N₁.subtype).codRestrict L₀ fun u => hIG u).codRestrict
      _ hN₁θ
  have hι : Function.Injective ι := by
    intro u v huv
    have h1 : (((u : I') : K) : G) = (((v : I') : K) : G) := by
      have := congrArg (fun w : aschbacherSolvableCore 3 L₀ => ((w : L₀) : G)) huv
      exact this
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  have hN₁s : Group.IsSolvable N₁ := by
    have := hLs
    exact Group.isSolvable_of_isSolvable_injective hι
  have hN₁3 : ¬ 3 ∣ Nat.card N₁ := fun h3 =>
    hLp (h3.trans (Subgroup.card_dvd_of_injective ι hι))
  have hρN₁ : N₁.map ρ = ⊥ := by
    have hmax := (solvable_prime_complement_core_characterization (H := ↥Cbar)
      Nat.prime_three).2.2.2.1
    have hn : (N₁.map ρ).Normal := hN₁n.map ρ hρ
    have hs : Group.IsSolvable (N₁.map ρ) := by
      have := hN₁s
      exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective N₁)
    have hp : ¬ 3 ∣ Nat.card (N₁.map ρ) := fun h3 => hN₁3 (h3.trans (Subgroup.card_map_dvd _ ρ))
    have h := hmax _ hn hs hp
    rwa [hCθ, le_bot_iff] at h
  have hy'C : y' ∈ Subgroup.centralizer ({z} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hyc
  have hy'N : y' ∈ Subgroup.normalizer (I' : Set K) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ (Subgroup.le_normalizer hy'C)
  have hπy : π y' ∈ Cbar := by
    rw [hCbar, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hy'C]
  have hcomm : ∀ i' : I', π y' * π i' = π i' * π y' := by
    intro i'
    have hmem : (i' : K)⁻¹ * (y' * i' * y'⁻¹) ∈ I' :=
      I'.mul_mem (I'.inv_mem i'.2) ((Subgroup.mem_normalizer_iff.mp hy'N _).mp i'.2)
    have hθmem : (⟨_, hmem⟩ : I') ∈ N₁ := by
      rw [hN₁, Subgroup.mem_comap]
      have := hy _ (hII' ▸ Subgroup.mem_map_of_mem K.subtype i'.2)
      simpa [hy'] using this
    have h1 : ρ ⟨_, hmem⟩ = 1 := by
      have : ρ ⟨_, hmem⟩ ∈ N₁.map ρ := Subgroup.mem_map_of_mem ρ hθmem
      rwa [hρN₁, Subgroup.mem_bot] at this
    have h2 : π ((i' : K)⁻¹ * (y' * i' * y'⁻¹)) = 1 := congrArg Subtype.val h1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, inv_mul_eq_one] at h2
    calc π y' * π i' = (π y' * π i' * (π y')⁻¹) * π y' := by group
      _ = π i' * π y' := by rw [← h2]
  have hZ : (⟨π y', hπy⟩ : Cbar) ∈ Subgroup.center ↥Cbar := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    apply Subtype.ext
    exact (hcomm ⟨i, hi⟩).symm
  rw [KFacts.KS14.j2_center_centralizer h415 hKθ hz1' hzP, Subgroup.mem_subgroupOf] at hZ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hZ
  have hθ : y'⁻¹ * z ^ m ∈ N := by
    have hm' : π y' = π (z ^ m) := by rw [map_zpow]; exact hm.symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hm'
    exact QuotientGroup.eq.mp hm'
  obtain ⟨S, hzS, -⟩ := hSyl
  obtain ⟨j, hj⟩ := S.isPGroup' ⟨z, hzS⟩
  have hzj : z ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hy'3 : y' ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hy3)
  have hyz : Commute y' z := Subtype.ext hyc
  have h1 : (y'⁻¹ * z ^ m) ^ 3 ^ (1 + j) = 1 :=
    Sec13.pow_three_pow_mul_eq_one ((hyz.zpow_right m).inv_left) (by rw [inv_pow, hy'3, inv_one])
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzj, one_zpow])
  have h2 := Sec13.eq_one_of_pow_three_pow_of_not_dvd hθp hθ h1
  rw [inv_mul_eq_one] at h2
  have h3 : y = c ^ m := by simpa [hy', hz] using congrArg Subtype.val h2
  rw [h3]
  exact Subgroup.zpow_mem_zpowers c m

end ModTheta

end CFSG.RankThree.PartTwo.Sec12.Proof128
