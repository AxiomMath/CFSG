module

public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LieType.Ree.SuzukiTwoNormalFive
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open CFSG.RankThree.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThreeEvenClassification.Helpers (thetaCoreOf thetaCoreOf_le
  solvablePrimeComplementCore solvablePrimeComplementCore_properties
  thetaCoreOf_normal_intersection)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

@[expose] def SuzukiPrimeFieldCosetDescent : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ α : MulAut (suzukiGroup a K), orderOf α = p →
      α ∉ inner (suzukiGroup a K) →
      ∃ (σ : RingAut K) (h : suzukiGroup a K) (b : ℕ) (k : Type) (_ : Field k) (_ : Finite k),
        orderOf σ = p ∧ (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
        MulAut.conj h * α * (MulAut.conj h)⁻¹ = szFieldAut a K σ ∧
        Nonempty (↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃*
          suzukiGroup b k)

section Basic

variable {a : ℕ} {K : Type} [Field K]

theorem suzuki_center_eq_bot [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center (suzukiGroup a K) = ⊥ := by
  obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with
    h | h
  · exact h
  · have h1 := (suzuki_perfect ha hK).1
    rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
    exact absurd h1 bot_ne_top

theorem suzuki_conj_injective [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center (suzukiGroup a K) := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun α : MulAut (suzukiGroup a K) => α y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  rw [suzuki_center_eq_bot ha hK, Subgroup.mem_bot] at hgZ
  exact hgZ

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_mem_centralizer_iff {G : Type*} [Group G] (hinj : Function.Injective
    (MulAut.conj : G →* MulAut G)) (α : MulAut G) (g : G) :
    (MulAut.conj g : MulAut G) ∈ Subgroup.centralizer ({α} : Set (MulAut G)) ↔ α g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : α * MulAut.conj g * α⁻¹ = MulAut.conj g := by
      rw [show α * MulAut.conj g * α⁻¹ = MulAut.conj g * α * α⁻¹ by rw [h]]
      group
    rw [mulAut_mul_conj_mul_inv] at h1
    exact hinj h1
  · intro h
    have h1 := mulAut_mul_conj_mul_inv α g
    rw [h] at h1
    calc MulAut.conj g * α = α * MulAut.conj g * α⁻¹ * α := by rw [h1]
      _ = α * MulAut.conj g := by group

theorem eq_bot_of_normal_of_isSolvable {S : Type*} [Group S] [IsSimpleGroup S]
    (hperf : Group.IsPerfect S) {N : Subgroup S} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N = ⊥ := by
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hS : Group.IsSolvable S := by
      have := hs
      subst h
      exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := S)).toMonoidHom)
        (Subgroup.topEquiv (G := S)).surjective
    obtain ⟨n, hn⟩ := hS.solvable
    have htop : ∀ m, derivedSeries S m = ⊤ := by
      intro m
      induction m with
      | zero => exact derivedSeries_zero S
      | succ m ih => rw [derivedSeries_succ, ih]; exact hperf.1
    obtain ⟨x, hx⟩ := exists_ne (1 : S)
    have hx' : x ∈ derivedSeries S n := by rw [htop n]; exact Subgroup.mem_top x
    rw [hn, Subgroup.mem_bot] at hx'
    exact hx hx'

end Basic

section Plane

variable {a : ℕ} {K : Type} [Field K]

theorem suzuki_exists_inner_in_plane [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) {A : Subgroup (MulAut (suzukiGroup a K))} [IsElementaryAbelian p A]
    (hAcard : Nat.card A = p ^ 2) :
    ∃ y ∈ A, y ∈ inner (suzukiGroup a K) ∧ y ≠ 1 := by
  classical
  obtain ⟨-, -, -, -, hcyc, -, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  by_contra hcon
  push Not at hcon
  let q : ↥A →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' (inner (suzukiGroup a K))).comp A.subtype
  have hqinj : Function.Injective q := by
    rw [injective_iff_map_eq_one]
    intro y hy1
    have hyI : (y : MulAut (suzukiGroup a K)) ∈ inner (suzukiGroup a K) :=
      (QuotientGroup.eq_one_iff _).1 hy1
    by_contra hne
    exact hne (Subtype.ext (hcon y y.2 hyI))
  have : IsCyclic ↥A := isCyclic_of_injective q hqinj
  have h1 := IsCyclic.exponent_eq_card (α := ↥A)
  have h2 := IsElementaryAbelian.exponent_dvd_p p ↥A
  rw [h1, hAcard] at h2
  have h3 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos h2
  nlinarith [hp.two_le]

theorem solvablePrimeComplementCore_eq_bot_of_equiv_suzuki {M : Type*} [Group M] [Finite M]
    {p : ℕ} (hp : p.Prime) {b : ℕ} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) (hb : 1 ≤ b ∨ p = 5)
    (e : M ≃* suzukiGroup b k) : solvablePrimeComplementCore M p = ⊥ := by
  obtain ⟨hN, hNs, hNp⟩ := solvablePrimeComplementCore_properties M p hp
  set N := solvablePrimeComplementCore M p with hNdef
  have hNm : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hNcard : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e.injective
  have hNms : Group.IsSolvable (N.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (N.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have hbot : N.map e.toMonoidHom = ⊥ := by
    by_cases hb1 : 1 ≤ b
    · obtain ⟨hfin, hnt, hsimple⟩ := suzuki_simple hb1 hk
      exact eq_bot_of_normal_of_isSolvable (suzuki_perfect hb1 hk).2 hNm hNms
    · obtain rfl : b = 0 := by omega
      have hp5 : p = 5 := hb.resolve_left hb1
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      obtain ⟨-, P, -, -, -, hcore⟩ := suzuki_two_normal_five_complement_core_trivial hk2
      apply hcore _ hNm
      rw [hNcard]
      exact (Nat.Prime.coprime_iff_not_dvd (hp5 ▸ hp)).2 (hp5 ▸ hNp) |>.symm
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).1 hbot

theorem suzuki_theta_centralizer_odd_inner [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup (MulAut (suzukiGroup a K))) {g : suzukiGroup a K}
    (hg : orderOf (MulAut.conj g : MulAut (suzukiGroup a K)) = p) :
    ¬ 2 ∣ Nat.card (thetaCoreOf p (B ⊓ Subgroup.centralizer
      ({(MulAut.conj g : MulAut (suzukiGroup a K))} : Set (MulAut (suzukiGroup a K))))) := by
  have hinj := suzuki_conj_injective ha hK
  have hgo : orderOf g = p := by rw [← hg, orderOf_injective _ hinj g]
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hgo
    exact hp.one_lt.ne hgo
  obtain ⟨-, hodd⟩ := (Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 g hg1
    (hgo ▸ hp.odd_of_ne_two hp2)
  have hle : thetaCoreOf p (B ⊓ Subgroup.centralizer
      ({(MulAut.conj g : MulAut (suzukiGroup a K))} : Set (MulAut (suzukiGroup a K)))) ≤
      Subgroup.centralizer ({(MulAut.conj g : MulAut (suzukiGroup a K))} :
        Set (MulAut (suzukiGroup a K))) :=
    (thetaCoreOf_le p _).trans inf_le_right
  have hdvd := Subgroup.card_dvd_of_le hle
  intro h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))


theorem eq_five_of_prime_dvd_twenty {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ 20) :
    p = 5 := by
  have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | rfl | omega | (exfalso; revert hp; norm_num)

theorem map_conj_eq_self_of_mem {M : Type*} [Group M] {B : Subgroup M} {g : M} (hg : g ∈ B) :
    B.map (MulAut.conj g).toMonoidHom = B := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact B.mul_mem (B.mul_mem hg hz) (B.inv_mem hg)
  · intro hy
    refine ⟨g⁻¹ * y * g, B.mul_mem (B.mul_mem (B.inv_mem hg) hy) hg, ?_⟩
    group

theorem suzuki_theta_centralizer_odd_outer [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {B : Subgroup (MulAut (suzukiGroup a K))} (hB : inner (suzukiGroup a K) ≤ B)
    {A : Subgroup (MulAut (suzukiGroup a K))} [IsElementaryAbelian p A]
    (hAcard : Nat.card A = p ^ 2) {σ : RingAut K} (hσA : szFieldAut a K σ ∈ A)
    {b : ℕ} {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (eH : ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃* suzukiGroup b k) :
    ¬ 2 ∣ Nat.card (thetaCoreOf p (B ⊓ Subgroup.centralizer
      ({szFieldAut a K σ} : Set (MulAut (suzukiGroup a K))))) := by
  classical
  have hfin : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  set I : Subgroup (MulAut (suzukiGroup a K)) := inner (suzukiGroup a K) with hI
  set σh : MulAut (suzukiGroup a K) := szFieldAut a K σ with hσh
  set C : Subgroup (MulAut (suzukiGroup a K)) :=
    B ⊓ Subgroup.centralizer ({σh} : Set (MulAut (suzukiGroup a K))) with hC
  have hinj := suzuki_conj_injective ha hK
  obtain ⟨-, -, -, -, -, -, hOodd⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  set H : Subgroup (suzukiGroup a K) := σh.toMonoidHom.eqLocus (MonoidHom.id _) with hH
  set M : Subgroup (MulAut (suzukiGroup a K)) := I ⊓ C with hM
  have hmemM : ∀ g : (suzukiGroup a K), (MulAut.conj g : MulAut (suzukiGroup a K)) ∈ M ↔ g ∈ H := by
    intro g
    have h1 : (MulAut.conj g : MulAut (suzukiGroup a K)) ∈ I := ⟨g, rfl⟩
    have h2 : (MulAut.conj g : MulAut (suzukiGroup a K)) ∈ B := hB h1
    have h3 := conj_mem_centralizer_iff hinj σh g
    constructor
    · intro hg
      exact h3.1 hg.2.2
    · intro hg
      exact ⟨h1, h2, h3.2 hg⟩
  let ψ : H →* MulAut (suzukiGroup a K) :=
    (MulAut.conj : (suzukiGroup a K) →* MulAut (suzukiGroup a K)).comp H.subtype
  have hψinj : Function.Injective ψ := fun x y hxy => Subtype.ext (hinj hxy)
  have hψrange : ψ.range = M := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact (hmemM g).2 g.2
    · intro hy
      obtain ⟨g, rfl⟩ := hy.1
      exact ⟨⟨g, (hmemM g).1 hy⟩, rfl⟩
  let eM : M ≃* suzukiGroup b k :=
    ((MulEquiv.subgroupCongr hψrange.symm).trans (MonoidHom.ofInjective hψinj).symm).trans eH
  have hb : 1 ≤ b ∨ p = 5 := by
    by_cases hb1 : 1 ≤ b
    · exact Or.inl hb1
    · right
      obtain rfl : b = 0 := by omega
      obtain ⟨y, hyA, hyI, hy1⟩ := suzuki_exists_inner_in_plane ha hK hp hAcard (A := A)
      obtain ⟨g, rfl⟩ := hyI
      have hcomm : σh * MulAut.conj g = MulAut.conj g * σh :=
        SteinbergBY.mul_comm_of_isMulCommutative hσA hyA
      have hgH : g ∈ H := (conj_mem_centralizer_iff hinj σh g).1
        (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
      have hyp : (MulAut.conj g : MulAut (suzukiGroup a K)) ^ p = 1 :=
        elemPow_eq_one_of_isElementaryAbelian _ hyA
      have hgp : g ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
      have hg1 : g ≠ 1 := by
        rintro rfl
        exact hy1 (map_one _)
      have : Fact p.Prime := ⟨hp⟩
      have hgo : orderOf (⟨g, hgH⟩ : H) = p :=
        orderOf_eq_prime (Subtype.ext hgp) (fun h => hg1 (congrArg Subtype.val h))
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      have hcard : Nat.card H = 20 := by
        rw [Nat.card_congr eH.toEquiv]
        exact (suzuki_two_normal_five_complement_core_trivial hk2).1
      have hdvd : p ∣ 20 := hcard ▸ hgo ▸ orderOf_dvd_natCard _
      exact eq_five_of_prime_dvd_twenty hp hp3 hdvd
  have hθM : thetaCoreOf p M = ⊥ := by
    have h := solvablePrimeComplementCore_eq_bot_of_equiv_suzuki hp hk hb eM
    show (solvablePrimeComplementCore M p).map M.subtype = ⊥
    rw [h, Subgroup.map_bot]
  have hMnormal : (M.subgroupOf C).Normal := by
    have : (I.subgroupOf C).Normal := (inner_normal (suzukiGroup a K)).subgroupOf C
    rwa [hM, Subgroup.inf_subgroupOf_right]
  have hθ := thetaCoreOf_normal_intersection p hp M C inf_le_right hMnormal
  rw [hθM] at hθ
  have hθCle : thetaCoreOf p C ≤ C := thetaCoreOf_le p C
  have hker : ∀ r ∈ thetaCoreOf p C, r ∈ I → r = 1 := by
    intro r hrθ hrI
    have : r ∈ M ⊓ thetaCoreOf p C := ⟨⟨hrI, hθCle hrθ⟩, hrθ⟩
    rw [← hθ] at this
    exact Subgroup.mem_bot.1 this
  let q : ↥(thetaCoreOf p C) →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' I).comp (thetaCoreOf p C).subtype
  have hqinj : Function.Injective q := by
    rw [injective_iff_map_eq_one]
    intro r hr1
    exact Subtype.ext (hker r r.2 ((QuotientGroup.eq_one_iff _).1 hr1))
  have hdvd : Nat.card (thetaCoreOf p C) ∣ Nat.card (Outer (suzukiGroup a K)) :=
    Subgroup.card_dvd_of_injective q hqinj
  intro h2
  exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 (h2.trans hdvd))

theorem suzuki_theta_centralizer_odd_of_descent (hdesc : SuzukiPrimeFieldCosetDescent)
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {B : Subgroup (MulAut (suzukiGroup a K))}
    (hB : inner (suzukiGroup a K) ≤ B) {A : Subgroup (MulAut (suzukiGroup a K))}
    [IsElementaryAbelian p A] (hAcard : Nat.card A = p ^ 2) {x : MulAut (suzukiGroup a K)}
    (hxA : x ∈ A) (hx1 : x ≠ 1) :
    ¬ 2 ∣ Nat.card (thetaCoreOf p (B ⊓ Subgroup.centralizer
      ({x} : Set (MulAut (suzukiGroup a K))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hxp : orderOf x = p :=
    SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hxA hx1
  by_cases hxI : x ∈ inner (suzukiGroup a K)
  · obtain ⟨g, rfl⟩ := hxI
    exact suzuki_theta_centralizer_odd_inner ha hK hp (by omega) B hxp
  · obtain ⟨σ, h, b, k, _, _, hσ, hbp, hk, hconj, ⟨eH⟩⟩ :=
      hdesc a ha K hK p hp (by omega) x hxp hxI
    set φ : MulAut (MulAut (suzukiGroup a K)) := MulAut.conj (MulAut.conj h) with hφ
    have hφx : φ x = szFieldAut a K σ := by
      rw [hφ, MulAut.conj_apply]
      exact hconj
    have hhB : (MulAut.conj h : MulAut (suzukiGroup a K)) ∈ B := hB ⟨h, rfl⟩
    have hφB : B.map φ.toMonoidHom = B := map_conj_eq_self_of_mem hhB
    have : IsElementaryAbelian p (A.map φ.toMonoidHom) := IsElementaryAbelian.map φ.toMonoidHom
    have hA'card : Nat.card (A.map φ.toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective φ.injective, hAcard]
    have hσA' : szFieldAut a K σ ∈ A.map φ.toMonoidHom := ⟨x, hxA, hφx⟩
    have key := suzuki_theta_centralizer_odd_outer ha hK hp hp3 hB hA'card hσA' hk eH
    have hmap := map_inSubgroup_theta_centralizer_mulEquiv hp φ B x
    rw [hφB, hφx, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at hmap
    have hc : Nat.card (thetaCoreOf p (B ⊓ Subgroup.centralizer
        ({szFieldAut a K σ} : Set (MulAut (suzukiGroup a K))))) =
        Nat.card (thetaCoreOf p (B ⊓ Subgroup.centralizer
          ({x} : Set (MulAut (suzukiGroup a K))))) := by
      rw [← hmap, Subgroup.card_map_of_injective φ.injective]
    rw [← hc]
    exact key

theorem suzuki_planeLocalCoreOdd_of_descent (hdesc : SuzukiPrimeFieldCosetDescent)
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : PlaneLocalCoreOdd p (suzukiGroup a K) := by
  classical
  intro B hB A hAB hA hAcard t htA ht1
  have : IsElementaryAbelian p A := hA
  set S := inSubgroup (aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (suzukiGroup a K)))) with hS
  have hSodd : ¬ 2 ∣ Nat.card S := by
    rw [hS, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact suzuki_theta_centralizer_odd_of_descent hdesc ha hK hp hp3 hB hAcard htA ht1
  have hAC : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (suzukiGroup a K))) := by
    intro x hx
    exact Subgroup.mem_inf.2 ⟨hAB hx, Subgroup.mem_centralizer_singleton_iff.2
      (SteinbergBY.mul_comm_of_isMulCommutative hx htA)⟩
  have hAS : A ≤ Subgroup.normalizer (S : Set (MulAut (suzukiGroup a K))) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore
      p _ (Subgroup.le_normalizer (hAC hx))
  have hSA : ⁅S, A⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hAS
  have hIS : autThetaT p B A ≤ S := fun x hx => by
    simp only [autThetaT, Subgroup.mem_iInf] at hx
    exact hx t htA ht1
  have hle : autPlaneProduct p B A t ≤ S := sup_le hSA hIS
  intro h2
  exact hSodd (h2.trans (Subgroup.card_dvd_of_le hle))

end Plane

end CFSG.RankThree.PartOne.KE
