module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
import CFSG.RankThree.PartOne.S10.ComponentOrbitSemisimpleLocalRankWitness
import CFSG.RankThree.PartOne.S10.TransitiveSemisimpleOddKernel
import CFSG.RankThree.GroupTheory.SteinbergBKMinimalCoverPerfect
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartTwo.Setup
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.ComponentInitial.SmallGroupFacts
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartOne.SemisimpleSection

open CFSG CFSG.LocalCores Subgroup
open CFSG.Assembly (evenRank)
open CFSG.Assembly.RankThreeEven (localRank)

theorem card_sub_one_le_localRank_of_central_cover {K : Type} [Group K] [Finite K]
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {T : I → Type} [∀ i, Group (T i)] [∀ i, Finite (T i)] [∀ i, IsSimpleGroup (T i)]
    (hnonab : ∀ i, ∃ a b : T i, a * b ≠ b * a) (ψ : K →* ∀ i, T i)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center K) {q : ℕ} (hq : q.Prime)
    (h2q : ∀ i, 2 * q ∣ Nat.card (T i)) : Fintype.card I - 1 ≤ localRank q K := by
  classical
  let Kp : I → Subgroup K := fun i => (coordSubgroup T i).comap ψ
  have hKpn : ∀ i, (Kp i).Normal := fun i => (normal_coordSubgroup T i).comap ψ
  let g : ∀ i, ↥(Kp i) →* T i := fun i => (Pi.evalMonoidHom T i).comp (ψ.comp (Kp i).subtype)
  have hg_ker : ∀ i (x : Kp i), g i x = 1 → ψ x = 1 := by
    intro i x hx
    funext j
    by_cases hj : j = i
    · subst hj
      exact hx
    · exact (mem_coordSubgroup_iff T).mp x.2 j hj
  have hg_surj : ∀ i, Function.Surjective (g i) := by
    intro i t
    obtain ⟨k, hk⟩ := hψ (Pi.mulSingle i t)
    refine ⟨⟨k, ⟨t, hk.symm⟩⟩, ?_⟩
    simp [g, hk]
  have hg_central : ∀ i, (g i).ker ≤ center ↥(Kp i) := by
    intro i x hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hker (hg_ker i x hx)) y
  have hTq : ∀ i, IsQuasisimple (T i) := fun i => (isQuasisimple_of_isSimpleGroup (hnonab i)).1
  have hcomm := fun i => central_extension_derived_of_surjective (g i) (hg_surj i)
    (hg_central i) (hTq i).1
  let P : ∀ i, Subgroup ↥(Kp i) := fun i => commutator ↥(Kp i)
  let L : I → Subgroup K := fun i => (P i).map (Kp i).subtype
  have hPquasi : ∀ i, IsQuasisimple ↥(P i) := fun i =>
    quasisimple_central_extension_derived_of_surjective (g i) (hg_surj i) (hg_central i) (hTq i)
  have hLcomp : ∀ i, IsComponent (L i) := fun i =>
    ⟨isQuasisimple_of_mulEquiv ((P i).equivMapOfInjective _ (Kp i).subtype_injective) (hPquasi i),
      IsSubnormal.trans' (Normal.isSubnormal inferInstance) (hKpn i).isSubnormal⟩
  have hLmem : ∀ i, ∀ x ∈ L i, ψ x ∈ coordSubgroup T i := by
    rintro i _ ⟨y, -, rfl⟩
    exact y.2
  have hLsurj : ∀ i (t : T i), ∃ x ∈ L i, ψ x i = t := by
    intro i t
    obtain ⟨y, hy⟩ := (hcomm i).2.2 t
    exact ⟨((y : Kp i) : K), ⟨(y : Kp i), y.2, rfl⟩, hy⟩
  have hLinj : Function.Injective L := by
    intro i j hij
    by_contra hne
    obtain ⟨t, ht⟩ := exists_ne (1 : T i)
    obtain ⟨x, hxL, hxt⟩ := hLsurj i t
    have hxj : x ∈ L j := hij ▸ hxL
    have h1 := (mem_coordSubgroup_iff T).mp (hLmem j x hxj) i hne
    exact ht (hxt.symm.trans h1)
  have hLcard : ∀ i, Nat.card (L i ⧸ center ↥(L i)) = Nat.card (T i) := by
    intro i
    let f : ↥(P i) →* T i := (g i).comp (P i).subtype
    have hf : Function.Surjective f := (hcomm i).2.2
    have hfker : f.ker ≤ center ↥(P i) := by
      intro x hx
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact mem_center_iff.mp (hg_central i hx) (y : Kp i)
    have hcenter : center ↥(P i) = f.ker := by
      have h := comap_center_eq_of_perfect (hcomm i).2.1 f hf hfker
      rw [(isQuasisimple_of_isSimpleGroup (hnonab i)).2, MonoidHom.comap_bot] at h
      exact h.symm
    let e1 : ↥(P i) ⧸ center ↥(P i) ≃* T i :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    let e2 : ↥(P i) ≃* ↥(L i) := (P i).equivMapOfInjective _ (Kp i).subtype_injective
    let e3 : ↥(P i) ⧸ center ↥(P i) ≃* ↥(L i) ⧸ center ↥(L i) :=
      QuotientGroup.congr _ _ e2 (Subgroup.map_center_eq e2)
    exact (Nat.card_congr e3.symm.toEquiv).trans (Nat.card_congr e1.toEquiv)
  exact card_sub_one_le_localRank_of_component_family hq L hLcomp hLinj fun i => by
    rw [hLcard i]
    exact h2q i

theorem exists_odd_kernel_section {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : evenRank G ≤ m) (H : Subgroup G) {Γ : Type} [Group Γ] [Finite Γ] (π : H →* Γ)
    (hπ : Function.Surjective π) (S : Subgroup Γ) [S.Normal] (hSperf : Group.IsPerfect S)
    (hΓS : Group.IsSolvable (Γ ⧸ S)) :
    ∃ (J : Type) (_ : Group J) (_ : Finite J) (πJ : J →* Γ) (Kj : Subgroup J),
      Function.Surjective πJ ∧ Kj.Normal ∧ Group.IsPerfect Kj ∧ Kj.map πJ = S ∧
      Group.IsNilpotent ↥(πJ.comp Kj.subtype).ker ∧
      Odd (Nat.card ↥(πJ.comp Kj.subtype).ker) ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → localRank q J ≤ m := by
  classical
  obtain ⟨⟨U, hU, hmin⟩, hprops⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.minimal_section_cover_retains_perfect_normal_subgroup
      π hπ S hSperf hΓS
  obtain ⟨hNnil, hsyl, hPchar, hPperf, hPS, -, -, -⟩ := hprops U hU hmin
  set f : ↥U →* Γ := π.comp U.subtype with hf
  have hfs : Function.Surjective f := by
    intro γ
    have hγ : γ ∈ U.map π := hU ▸ mem_top γ
    obtain ⟨u, hu, rfl⟩ := hγ
    exact ⟨⟨u, hu⟩, rfl⟩
  set N : Subgroup ↥U := f.ker with hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R2⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  set R : Subgroup ↥U := (R2 : Subgroup ↥N).map N.subtype with hR
  have hRn : R.Normal := hsyl 2 R2
  have hRN : R ≤ N := map_subtype_le _
  have hRtwo : IsPGroup 2 R := R2.isPGroup'.map N.subtype
  let πJ : (↥U ⧸ R) →* Γ := QuotientGroup.lift R f fun x hx => hRN hx
  have hπJ : Function.Surjective πJ := by
    intro γ
    obtain ⟨u, hu⟩ := hfs γ
    exact ⟨(u : ↥U ⧸ R), hu⟩
  have hπJρ : πJ.comp (QuotientGroup.mk' R) = f := rfl
  set P : Subgroup ↥U := perfectResidual ↥U with hP
  have hPn : P.Normal := inferInstance
  have hρs : Function.Surjective (QuotientGroup.mk' R) := QuotientGroup.mk'_surjective R
  have hker : πJ.ker = N.map (QuotientGroup.mk' R) := by
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective R x
    simp only [MonoidHom.mem_ker, mem_map]
    constructor
    · intro h
      exact ⟨u, h, rfl⟩
    · rintro ⟨n, hn, hnu⟩
      rw [← hnu]
      exact hn
  have hNbarnil : Group.IsNilpotent ↥(N.map (QuotientGroup.mk' R)) := by
    have := hNnil
    exact Group.nilpotent_of_surjective ((QuotientGroup.mk' R).subgroupMap N)
      ((QuotientGroup.mk' R).subgroupMap_surjective N)
  have hNbarodd : Odd (Nat.card ↥(N.map (QuotientGroup.mk' R))) := by
    have hker' : ((QuotientGroup.mk' R).subgroupMap N).ker = (R2 : Subgroup ↥N) := by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk', hR]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    have e := QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' R).subgroupMap_surjective N)
    have hcard : Nat.card ↥(N.map (QuotientGroup.mk' R)) = (R2 : Subgroup ↥N).index := by
      rw [← hker']
      exact (Nat.card_congr e.toEquiv).symm
    rw [hcard]
    exact Nat.not_even_iff_odd.mp fun h => R2.not_dvd_index (even_iff_two_dvd.mp h)
  let c : ↥(πJ.comp (P.map (QuotientGroup.mk' R)).subtype).ker →*
      ↥(N.map (QuotientGroup.mk' R)) :=
    ((P.map (QuotientGroup.mk' R)).subtype.comp
      (πJ.comp (P.map (QuotientGroup.mk' R)).subtype).ker.subtype).codRestrict _ (fun x => by
        rw [← hker, MonoidHom.mem_ker]
        exact x.2)
  have hc : Function.Injective c := by
    intro a b h
    have h' := congrArg (fun x : ↥(N.map (QuotientGroup.mk' R)) => (x : ↥U ⧸ R)) h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨↥U ⧸ R, inferInstance, inferInstance, πJ, P.map (QuotientGroup.mk' R), hπJ,
    Subgroup.Normal.map hPn (QuotientGroup.mk' R) hρs, ?_, ?_, ?_, ?_, ?_⟩
  · have := hPperf
    exact Group.IsPerfect.map (QuotientGroup.mk' R)
  · rw [Subgroup.map_map, hπJρ]
    exact hPS
  · have := hNbarnil
    exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hc).symm
  · exact Odd.of_dvd_nat hNbarodd (Subgroup.card_dvd_of_injective c hc)
  · intro q hq hq2
    have hqR : ¬ q ∣ Nat.card R := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRtwo
      rw [hk]
      intro hdvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
    calc localRank q (↥U ⧸ R) ≤ localRank q ↥U :=
          CFSG.RankThree.Classical2.localRank_quotient_le hq hq2 R hqR
      _ ≤ localRank q ↥H := CFSG.RankThree.PartTwo.localRank_subgroup_le hq U
      _ ≤ localRank q G := CFSG.RankThree.PartTwo.localRank_subgroup_le hq H
      _ ≤ evenRank G := CFSG.RankThree.OddKernel.localRank_le_evenRank hq hq2
      _ ≤ m := hm

theorem isPerfect_pi {I : Type*} [Finite I] {T : I → Type*} [∀ i, Group (T i)]
    (h : ∀ i, Group.IsPerfect (T i)) : Group.IsPerfect (∀ i, T i) := by
  rw [Group.isPerfect_def, commutator_def]
  have htop : (⊤ : Subgroup (∀ i, T i)) = Subgroup.pi Set.univ fun _ => ⊤ :=
    (Subgroup.pi_top Set.univ).symm
  rw [htop, Subgroup.commutator_pi_pi_of_finite]
  have htop' : ∀ i, ⁅(⊤ : Subgroup (T i)), ⊤⁆ = ⊤ := fun i => by
    rw [← commutator_def]
    exact (h i).commutator_eq_top
  simp only [htop']

theorem exists_odd_prime_dvd_card_of_nonabelian_simple {S₀ : Type*} [Group S₀] [Finite S₀]
    [IsSimpleGroup S₀] (hnab : ∃ a b : S₀, a * b ≠ b * a) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card S₀ := by
  by_contra hno
  push Not at hno
  have hsolv : Group.IsSolvable S₀ := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hsub : (Nat.card S₀).primeFactors ⊆ {2} := fun p hp => by
      have hp' := Nat.mem_primeFactors.mp hp
      by_contra hne
      exact hno p hp'.1 (by simpa using hne) hp'.2.1
    exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (CFSG.LocalAnalysis.ComponentInitial.solvable_simple_abelian hsolv a b)

theorem natCard_eq_of_conjNormal_coord {Γ : Type*} [Group Γ] {S : Subgroup Γ} [S.Normal]
    {I : Type} [DecidableEq I] {T : I → Type} [∀ i, Group (T i)] (φ : S ≃* ∀ i, T i)
    {i j : I} (g : Γ)
    (hg : ∀ s : S, φ s ∈ coordSubgroup T i ↔ φ (MulAut.conjNormal g s) ∈ coordSubgroup T j) :
    Nat.card (T i) = Nat.card (T j) := by
  let e : ∀ k : I, {s : S // φ s ∈ coordSubgroup T k} ≃ ↥(coordSubgroup T k) := fun k =>
    φ.toEquiv.subtypeEquiv fun _ => Iff.rfl
  let e3 : {s : S // φ s ∈ coordSubgroup T i} ≃ {s : S // φ s ∈ coordSubgroup T j} :=
    (MulAut.conjNormal g).toEquiv.subtypeEquiv hg
  exact Nat.card_congr ((coordSubgroupEquiv T i).toEquiv.trans
    ((e i).symm.trans (e3.trans ((e j).trans (coordSubgroupEquiv T j).toEquiv.symm))))

end CFSG.RankThree.PartOne.SemisimpleSection

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores Subgroup SemisimpleSection
open CFSG.Assembly (evenRank)
open CFSG.Assembly.RankThreeEven (localRank)

theorem cyclic_semisimple_section_orbit_bound_of
    (h : TransitiveSemisimpleOddKernelCentralization) : CyclicSemisimpleSectionOrbitBound := by
  intro G _ _ m hm H Γ _ _ π hπ _ _ z _ S _ hSz I _ _ _ T _ _ _ hnonab heven φ htrans
  by_contra hlt
  have hd : m + 2 ≤ Fintype.card I := by omega
  have hTperf : ∀ i, Group.IsPerfect (T i) := fun i =>
    (isQuasisimple_of_isSimpleGroup (hnonab i)).1.1
  have hSperf : Group.IsPerfect S := by
    have := isPerfect_pi hTperf
    exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hΓS : Group.IsSolvable (Γ ⧸ S) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hgen : ∀ x : Γ ⧸ S, ∃ n : ℤ, x = (QuotientGroup.mk z : Γ ⧸ S) ^ n := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hg : g ∈ S ⊔ Subgroup.zpowers z := by
        rw [hSz]
        exact mem_top g
      obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine ⟨n, ?_⟩
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul,
        QuotientGroup.mk_zpow]
    obtain ⟨m, rfl⟩ := hgen a
    obtain ⟨n, rfl⟩ := hgen b
    exact (Commute.zpow_zpow_self _ m n).eq
  obtain ⟨J, _, _, πJ, Kj, hπJ, hKjn, hKjperf, hKjS, hCnil, hCodd, hrank⟩ :=
    exists_odd_kernel_section hm H π hπ S hSperf hΓS
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨q, hq, hq2, hqdvd⟩ := exists_odd_prime_dvd_card_of_nonabelian_simple (hnonab i₀)
  have hcard : ∀ j, Nat.card (T i₀) = Nat.card (T j) := by
    intro j
    obtain ⟨n, hn⟩ := htrans i₀ j
    exact natCard_eq_of_conjNormal_coord φ (z ^ n) hn
  have h2q : ∀ j, 2 * q ∣ Nat.card (T j) := by
    intro j
    have hq' : q ∣ Nat.card (T j) := (hcard j) ▸ hqdvd
    have h2 : 2 ∣ Nat.card (T j) := even_iff_two_dvd.mp (heven j)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm) h2 hq'
  let ψ0 : ↥Kj →* Γ := πJ.comp Kj.subtype
  have hψ0S : ∀ k : ↥Kj, ψ0 k ∈ S := fun k => hKjS ▸ mem_map_of_mem πJ k.2
  let ψ1 : ↥Kj →* S := ψ0.codRestrict S hψ0S
  have hψ1s : Function.Surjective ψ1 := by
    rintro ⟨s, hs⟩
    rw [← hKjS] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  let ψ : ↥Kj →* (∀ i, T i) := φ.toMonoidHom.comp ψ1
  have hψs : Function.Surjective ψ := φ.surjective.comp hψ1s
  have hψker : ψ.ker = ψ0.ker := by
    ext k
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hk
      have : ψ1 k = 1 := (map_eq_one_iff φ φ.injective).mp hk
      exact congrArg Subtype.val this
    · intro hk
      have : ψ1 k = 1 := Subtype.ext hk
      show φ (ψ1 k) = 1
      rw [this, map_one]
  let _ : MulDistribMulAction J ↥Kj :=
    MulDistribMulAction.compHom ↥Kj (MulAut.conjNormal : J →* MulAut ↥Kj)
  have hsmul : ∀ (a : J) (k : ↥Kj), ((a • k : ↥Kj) : J) = a * k * a⁻¹ := fun a k =>
    MulAut.conjNormal_apply a k
  have hψ0smul : ∀ (a : J) (k : ↥Kj), ψ0 (a • k) = πJ a * ψ0 k * (πJ a)⁻¹ := fun a k => by
    change πJ ((a • k : ↥Kj) : J) = _
    rw [hsmul, map_mul, map_mul, map_inv]
    rfl
  have hCinv : ∀ (a : J) (c : ↥Kj), c ∈ ψ.ker → a • c ∈ ψ.ker := by
    intro a c hc
    rw [hψker, MonoidHom.mem_ker] at hc ⊢
    rw [hψ0smul, hc, mul_one, mul_inv_cancel]
  have hCnil' : Group.IsNilpotent ↥ψ.ker := by
    rw [hψker]
    exact hCnil
  have hCodd' : Odd (Nat.card ↥ψ.ker) := by
    rw [hψker]
    exact hCodd
  have hrankK : evenRank ↥Kj ≤ m :=
    CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 =>
      (CFSG.RankThree.PartTwo.localRank_subgroup_le hr Kj).trans (hrank r hr hr2)
  obtain ⟨ū, hū⟩ := hπJ z
  let φ' : ↥Kj ⧸ ψ.ker ≃* (∀ i, T i) := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have hφ' : ∀ k : ↥Kj, φ' (k : ↥Kj ⧸ ψ.ker) = φ (ψ1 k) := fun k => rfl
  have htrans' : ∀ i j : I, ∃ a : J, ∀ k : ↥Kj,
      φ' (k : ↥Kj ⧸ ψ.ker) ∈ coordSubgroup T i ↔
        φ' ((a • k : ↥Kj) : ↥Kj ⧸ ψ.ker) ∈ coordSubgroup T j := by
    intro i j
    obtain ⟨n, hn⟩ := htrans i j
    refine ⟨ū ^ n, fun k => ?_⟩
    have h1 : ψ1 ((ū ^ n) • k) = MulAut.conjNormal (z ^ n) (ψ1 k) := by
      apply Subtype.ext
      change ψ0 ((ū ^ n) • k) = _
      rw [hψ0smul, map_pow, hū, MulAut.conjNormal_apply]
      rfl
    rw [hφ', hφ', h1]
    exact hn (ψ1 k)
  have hC : ψ.ker ≤ center ↥Kj :=
    h m ↥Kj hKjperf hrankK J ψ.ker hCinv hCnil' hCodd' I hd T hnonab heven φ' htrans'
  have hbound := card_sub_one_le_localRank_of_central_cover hnonab ψ hψs hC hq h2q
  have hKrank : localRank q ↥Kj ≤ m :=
    (CFSG.RankThree.PartTwo.localRank_subgroup_le hq Kj).trans (hrank q hq hq2)
  omega

theorem cyclic_semisimple_section_orbit_bound : CyclicSemisimpleSectionOrbitBound :=
  cyclic_semisimple_section_orbit_bound_of transitive_semisimple_odd_kernel_centralization

end CFSG.RankThree.PartOne
