module

public import CFSG.RankThree.PartTwo.Sec18.Item187F3NotCentral
public import CFSG.RankThree.PartTwo.Sec18.Item187F4Shape
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

section Helpers

variable {Γ Y : Type} [Group Γ] [Group Y]

private theorem f13_normalizer_map (f : Γ →* Y) (S : Subgroup Γ) (g : Γ)
    (hg : g ∈ Subgroup.normalizer (S : Set Γ)) :
    f g ∈ Subgroup.normalizer ((S.map f : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have h1 : g * t * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg t).mp ht
    have h2 : f g * f t * (f g)⁻¹ = f (g * t * g⁻¹) := by simp only [map_mul, map_inv]
    rw [h2]
    exact Subgroup.mem_map_of_mem f h1
  · intro hy
    obtain ⟨u, hu, hu'⟩ := hy
    have h1 : g⁻¹ * u * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg u).mp hu
    refine ⟨g⁻¹ * u * g, h1, ?_⟩
    simp only [map_mul, map_inv, hu']
    group

private theorem f13_mem_normalizer_subgroupOf {G : Type} [Group G] {K S : Subgroup G} {g : G}
    (hgK : g ∈ K) (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    (⟨g, hgK⟩ : K) ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  exact Subgroup.mem_normalizer_iff.mp hg (y : G)

private theorem f13_pRank_five_range {T V : Type} [Group T] [Finite T] [Group V] [Finite V]
    (φ : T →* V) (hker : ∀ t : T, φ t = 1 → ∃ n : ℕ, t ^ 2 ^ n = 1) :
    CFSG.pRank 5 ↥φ.range = CFSG.pRank 5 T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 5 ∣ Nat.card φ.rangeRestrict.ker := by
    have h2 : IsPGroup 2 φ.rangeRestrict.ker := by
      intro x
      have hx : φ x.1 = 1 := by
        have h := MonoidHom.mem_ker.mp x.2
        simpa using congrArg Subtype.val h
      obtain ⟨n, hn⟩ := hker x.1 hx
      exact ⟨n, Subtype.ext hn⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    intro h5
    rw [hn] at h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)
  have e := QuotientGroup.quotientKerEquivOfSurjective φ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective φ)
  rw [← CFSG.pRank_congr_of_mulEquiv e 5]
  exact CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd (by norm_num) _ hN

end Helpers

private theorem f13_le_normalizer_commutator {G : Type} [Group G] {K H L : Subgroup G}
    (hH : K ≤ Subgroup.normalizer (H : Set G)) (hL : K ≤ Subgroup.normalizer (L : Set G)) :
    K ≤ Subgroup.normalizer ((⁅H, L⁆ : Subgroup G) : Set G) := by
  intro k hk
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH hk)
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL hk)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, h1, h2]

private theorem f13_comm_mul_left {G : Type} [Group G] (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]; group

private theorem f13_commute_of_centralizer {G : Type} [Group G] {c d : G}
    (hd : d ∈ Subgroup.centralizer ({c} : Set G)) : Commute d c :=
  (Subgroup.mem_centralizer_iff.mp hd c (Set.mem_singleton c)).symm

private theorem f13_conj_zpowers {G : Type} [Group G] {c g : G} (hC : Commute g c) {h : G}
    (hh : h ∈ Subgroup.zpowers c) : g * h * g⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have e : g * c ^ n * g⁻¹ = c ^ n := by
    rw [(hC.zpow_right n).eq, mul_inv_cancel_right]
  rw [e]
  exact hh

private theorem f13_mem_normalizer_zpowers {G : Type} [Group G] {c g : G} (hC : Commute g c) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => f13_conj_zpowers hC hh, fun hh => ?_⟩
  have h2 := f13_conj_zpowers hC.inv_left hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at h2
  exact h2

private theorem f13_mem_sup_prod {G : Type} [Group G] {N S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ S) :
    ∃ n ∈ N, ∃ s ∈ S, x = n * s := by
  let T : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ s ∈ S, g = n * s}
      one_mem' := ⟨1, N.one_mem, 1, S.one_mem, (mul_one 1).symm⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨n1, hn1, s1, hs1, rfl⟩ := ha
        obtain ⟨n2, hn2, s2, hs2, rfl⟩ := hb
        refine ⟨n1 * (s1 * n2 * s1⁻¹),
          N.mul_mem hn1 ((Subgroup.mem_normalizer_iff.mp (hS hs1) n2).mp hn2), s1 * s2,
          S.mul_mem hs1 hs2, ?_⟩
        group
      inv_mem' := fun {a} ha => by
        obtain ⟨n, hn, s, hs, rfl⟩ := ha
        refine ⟨s⁻¹ * n⁻¹ * s, (Subgroup.mem_normalizer_iff''.mp (hS hs) n⁻¹).mp (N.inv_mem hn),
          s⁻¹, S.inv_mem hs, ?_⟩
        group }
  have hle : N ⊔ S ≤ T :=
    sup_le (fun n hn => ⟨n, hn, 1, S.one_mem, (mul_one n).symm⟩)
      (fun s hs => ⟨1, N.one_mem, s, hs, (one_mul s).symm⟩)
  exact hle hx

private theorem f13_commutator_le_left {G : Type} [Group G] {K L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (K : Set G)) : ⁅K, L⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun p hp z hz => ?_
  have hzp : z * p⁻¹ * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hL hz) p⁻¹).mp (K.inv_mem hp)
  have e : ⁅p, z⁆ = p * (z * p⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact K.mul_mem hp hzp

private theorem f13_comm_of_E27 {G : Type} [Group G] {A : Subgroup G}
    (hA : IsE27 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : Commute x y := by
  have h : (⟨x, hx⟩ : A) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hA.1.1.is_comm.comm _ _
  have h' : x * y = y * x := congrArg Subtype.val h
  exact h'

private theorem f13_commute_zpowers {G : Type} [Group G] {t c z : G} (ht : Commute t c)
    (hz : z ∈ Subgroup.zpowers c) : Commute t z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ht.zpow_right n

private theorem f13_comm_eq_one {G : Type} [Group G] {t z : G} (h : Commute t z) :
    ⁅t, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr h.eq

private theorem f13_mem_normalizer_of_inv {G : Type} [Group G] {W : Subgroup G} {g : G}
    (hg : ∀ y ∈ W, g * y * g⁻¹ ∈ W) (hg' : ∀ y ∈ W, g⁻¹ * y * g⁻¹⁻¹ ∈ W) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hg h hh, fun hh => ?_⟩
  have h2 := hg' _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h2

private theorem f13_conj_sup_mem {G : Type} [Group G] {K L W : Subgroup G} {g : G}
    (hK : K ≤ W.comap (MulAut.conj g).toMonoidHom)
    (hL : L ≤ W.comap (MulAut.conj g).toMonoidHom) :
    ∀ y ∈ K ⊔ L, g * y * g⁻¹ ∈ W :=
  fun y hy => sup_le hK hL hy

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.normal_pCoreOf_subgroupOf (hX : MinCex A M H c X) :
    ((CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c)).Normal := by
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hX.le_normalizer (Subgroup.mem_sup_left hcA)
  have hcQ : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hcX
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hsub : CFSG.Open.pCoreOf 2 X ≤ X ⊔ Subgroup.zpowers c :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans le_sup_left
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hsub]
  exact sup_le hXQ (Subgroup.zpowers_le.mpr hcQ)

private theorem f13_comm_quot {G : Type} [Group G] (N : Subgroup G) [N.Normal] (x y : G) :
    QuotientGroup.mk' N x * QuotientGroup.mk' N y = QuotientGroup.mk' N y * QuotientGroup.mk' N x ↔
      ⁅x, y⁆ ∈ N := by
  have h : QuotientGroup.mk' N ⁅x, y⁆ = ⁅QuotientGroup.mk' N x, QuotientGroup.mk' N y⁆ :=
    map_commutatorElement (QuotientGroup.mk' N) x y
  rw [← commutatorElement_eq_one_iff_mul_comm, ← h]
  exact QuotientGroup.eq_one_iff ⁅x, y⁆

private theorem f13_pow_eq_one_of_coe {G : Type} [Group G] {K : Subgroup G} {n : ℕ} (x : K)
    (h : (x : G) ^ n = 1) : x ^ n = 1 :=
  Subtype.ext (by simpa using h)

private theorem f13_comm_inv {G : Type} [Group G] (a b : G) : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by
  simp only [commutatorElement_def]; group

private theorem f13_shape81_abstract {Kg : Type} [Group Kg] [Finite Kg] {Y : Type} [Group Y]
    (N S0 P0 : Subgroup Kg) [N.Normal] [P0.Normal] (c0 : Kg) (ψ : Kg →* Y)
    (hS2 : ∀ x ∈ S0, ∃ n : ℕ, x ^ 2 ^ n = 1) (hN2 : ∀ t ∈ N, ∃ n : ℕ, t ^ 2 ^ n = 1)
    (hNS : N ≤ S0) (hNP : N ≤ P0) (hcS : c0 ∈ Subgroup.normalizer (S0 : Set Kg))
    (hc3 : c0 ^ 3 = 1) (hPpow : ∀ y ∈ P0, ∃ n : ℕ, y ^ 5 ^ n ∈ N)
    (hrank : CFSG.pRank 5 ↥P0 ≤ 2)
    (hMS : ∀ s ∈ S0, (∀ p ∈ P0, ⁅s, p⁆ ∈ N) → s ∈ N)
    (hMc : ¬ ∀ p ∈ P0, ∀ z ∈ Subgroup.zpowers c0, ⁅p, z⁆ ∈ N)
    (hψ : ∀ s ∈ S0, ψ s = 1 ↔ s ∈ N) :
    Shape81 (S0.map ψ) (ψ c0) := by
  haveI : Finite (Kg ⧸ N) := Quotient.finite _
  have hNψ : N ≤ ψ.ker := fun n hn => MonoidHom.mem_ker.mpr ((hψ n (hNS hn)).mpr hn)
  have hpsiq : ∀ x : Kg, QuotientGroup.lift N ψ hNψ (QuotientGroup.mk' N x) = ψ x :=
    fun x => rfl
  obtain ⟨cq, hcq⟩ : ∃ cq : Kg ⧸ N, cq = QuotientGroup.mk' N c0 := ⟨_, rfl⟩
  have hpsic : QuotientGroup.lift N ψ hNψ cq = ψ c0 := by rw [hcq, hpsiq]
  have hS2q : IsPGroup 2 ↥(S0.map (QuotientGroup.mk' N)) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := hS2 y hy
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hyx, ← map_pow, hn, map_one, OneMemClass.coe_one]
  have hP5q : IsPGroup 5 ↥(P0.map (QuotientGroup.mk' N)) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := hPpow y hy
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hyx, ← map_pow]
    rw [OneMemClass.coe_one]
    exact (QuotientGroup.eq_one_iff (y ^ 5 ^ n)).mpr hn
  haveI : (P0.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  have hrankq : CFSG.Open.pRank 5 (P0.map (QuotientGroup.mk' N)) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    have hrange : ((QuotientGroup.mk' N).comp P0.subtype).range =
        P0.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : ∀ t : ↥P0, ((QuotientGroup.mk' N).comp P0.subtype) t = 1 →
        ∃ n : ℕ, t ^ 2 ^ n = 1 := by
      intro t ht
      obtain ⟨n, hn⟩ := hN2 (t : Kg) ((QuotientGroup.eq_one_iff (t : Kg)).mp ht)
      exact ⟨n, f13_pow_eq_one_of_coe t hn⟩
    rw [← hrange, f13_pRank_five_range _ hker]
    exact hrank
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, φ, hφ⟩ := CFSG.RankThree.PartTwo.Sec16.Crit167.exists_rep (r := 5)
    (by norm_num) (P0.map (QuotientGroup.mk' N)) hP5q hrankq
  have hcpow : cq ^ 3 = 1 := by rw [hcq, ← map_pow, hc3, map_one]
  have hcop : Nat.Coprime (orderOf cq) 5 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcpow) (by norm_num)
  have hφc : φ cq ≠ 1 := by
    intro h1
    have hmem := hφ cq hcop h1
    apply hMc
    intro p hp z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzC : QuotientGroup.mk' N (c0 ^ n) ∈
        Subgroup.centralizer ((P0.map (QuotientGroup.mk' N) : Subgroup (Kg ⧸ N)) : Set (Kg ⧸ N)) := by
      rw [map_zpow, ← hcq]
      exact zpow_mem hmem n
    have hpP : QuotientGroup.mk' N p ∈ P0.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hp
    exact (f13_comm_quot N p (c0 ^ n)).mp (Subgroup.mem_centralizer_iff.mp hzC _ hpP)
  have hφS : ∀ g ∈ S0.map (QuotientGroup.mk' N), φ g = 1 → g = 1 := by
    intro g hg h1
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨n, hn⟩ := hS2 s hs
    have hdvd : orderOf (QuotientGroup.mk' N s) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hn, map_one])
    have hcop' : Nat.Coprime (orderOf (QuotientGroup.mk' N s)) 5 :=
      Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left n (by norm_num))
    have hmem := hφ _ hcop' h1
    have hsN : s ∈ N := by
      apply hMS s hs
      intro p hp
      have hpP : QuotientGroup.mk' N p ∈ P0.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hp
      rw [f13_comm_inv]
      exact N.inv_mem ((f13_comm_quot N p s).mp (Subgroup.mem_centralizer_iff.mp hmem _ hpP))
    exact (QuotientGroup.eq_one_iff s).mpr hsN
  have hc1 : cq ≠ 1 := fun h => hφc (by rw [h, map_one])
  have hc3q : orderOf cq = 3 := orderOf_eq_prime hcpow hc1
  have hcSq : cq ∈ Subgroup.normalizer
      ((S0.map (QuotientGroup.mk' N) : Subgroup (Kg ⧸ N)) : Set (Kg ⧸ N)) := by
    rw [hcq]; exact f13_normalizer_map (QuotientGroup.mk' N) S0 c0 hcS
  have hShape : Shape81 (S0.map (QuotientGroup.mk' N)) cq :=
    shape81_of_gl (S0.map (QuotientGroup.mk' N)) cq hS2q hc3q hcSq k hk φ hφc hφS
  have hmapS : ∀ x : ↥(S0.map (QuotientGroup.mk' N)),
      QuotientGroup.lift N ψ hNψ (x : Kg ⧸ N) ∈ S0.map ψ := by
    intro x
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp x.2
    rw [← hsx, hpsiq]
    exact Subgroup.mem_map_of_mem ψ hs
  let g' : ↥(S0.map (QuotientGroup.mk' N)) →* ↥(S0.map ψ) :=
    MonoidHom.codRestrict
      ((QuotientGroup.lift N ψ hNψ).comp (S0.map (QuotientGroup.mk' N)).subtype)
      (S0.map ψ) hmapS
  have hinj : Function.Injective g' := by
    refine (injective_iff_map_eq_one g').mpr fun x hx => ?_
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp x.2
    have h1 : QuotientGroup.lift N ψ hNψ (x : Kg ⧸ N) = 1 := congrArg Subtype.val hx
    rw [← hsx, hpsiq] at h1
    have hsN : s ∈ N := (hψ s hs).mp h1
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    rw [← hsx]
    exact (QuotientGroup.eq_one_iff s).mpr hsN
  have hsurj : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨QuotientGroup.mk' N s, Subgroup.mem_map_of_mem _ hs⟩, Subtype.ext rfl⟩
  let e : ↥(S0.map (QuotientGroup.mk' N)) ≃* ↥(S0.map ψ) :=
    MulEquiv.ofBijective g' ⟨hinj, hsurj⟩
  have he : ∀ s t : ↥(S0.map (QuotientGroup.mk' N)),
      cq * (s : Kg ⧸ N) * cq⁻¹ = (t : Kg ⧸ N) →
        ψ c0 * ((e s : ↥(S0.map ψ)) : Y) * (ψ c0)⁻¹ = ((e t : ↥(S0.map ψ)) : Y) := by
    intro s t hst
    have h1 := congrArg (⇑(QuotientGroup.lift N ψ hNψ)) hst
    simp only [map_mul, map_inv] at h1
    rw [hpsic] at h1
    exact h1
  exact Shape81.of_equiv hcSq (f13_normalizer_map ψ S0 c0 hcS) e he hShape

section Certified


theorem MinCex.shape81_map (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X)
    {Y : Type} [Group Y] (ψ : ↥(X ⊔ Subgroup.zpowers c) →* Y)
    (hψ : ∀ s : ↥(X ⊔ Subgroup.zpowers c),
      s ∈ (CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c) →
        (ψ s = 1 ↔ s ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c))) :
    Shape81 (((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c)).map ψ)
      (ψ ⟨c, Subgroup.mem_sup_right (Subgroup.mem_zpowers c)⟩) := by
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hX.le_normalizer (Subgroup.mem_sup_left hcA)
  have hcS : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) :=
    le_normalizer_pCoreOf hX.sec18H (Subgroup.mem_sup_left hcA)
  have hcK : c ∈ X ⊔ Subgroup.zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hXP : X ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoFive X)
  have hcP : c ∈ Subgroup.normalizer (oTwoFive X : Set G) :=
    normalizer_le_normalizer_oTwoFive X hcX
  have hPX : oTwoFive X ≤ X := oTwoFive_le X
  have hSX : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X := hX.pCoreOf_le
  have hQS : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
    MinCex.pCoreOf_le_S h186 hX
  have hQP : CFSG.Open.pCoreOf 2 X ≤ oTwoFive X := pCoreOf_le_oTwoFive X
  have hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 5 :=
    MinCex.card_primeFactors_subset h186 hX hsol h5
  have hPK : oTwoFive X ≤ X ⊔ Subgroup.zpowers c := hPX.trans le_sup_left
  have hKN : X ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    sup_le hXP (Subgroup.zpowers_le.mpr hcP)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc3G : c ^ 3 = 1 := by
    rw [← MinCex.orderOf_c h184 hX]
    exact pow_orderOf_eq_one c
  haveI hNn : ((CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c)).Normal :=
    MinCex.normal_pCoreOf_subgroupOf hX
  haveI hPn : ((oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKN
  have hS2 : ∀ x ∈ (CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c),
      ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
      ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
    exact ⟨n, f13_pow_eq_one_of_coe x (by simpa using congrArg Subtype.val hn)⟩
  have hN2 : ∀ t ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c),
      ∃ n : ℕ, t ^ 2 ^ n = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
      ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩
    exact ⟨n, f13_pow_eq_one_of_coe t (by simpa using congrArg Subtype.val hn)⟩
  have hNS : (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c) ≤
      (CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    intro t ht
    exact Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp ht))
  have hNP : (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c) ≤
      (oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    intro t ht
    exact Subgroup.mem_subgroupOf.mpr (hQP (Subgroup.mem_subgroupOf.mp ht))
  have hcS' := f13_mem_normalizer_subgroupOf hcK hcS
  have hc3' : (⟨c, hcK⟩ : ↥(X ⊔ Subgroup.zpowers c)) ^ 3 = 1 :=
    f13_pow_eq_one_of_coe _ hc3G
  have hPpow : ∀ y ∈ (oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c),
      ∃ n : ℕ, y ^ 5 ^ n ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    intro y hy
    obtain ⟨n, hn⟩ := exists_pow_mem_pCoreOf (Subgroup.mem_subgroupOf.mp hy)
    exact ⟨n, Subgroup.mem_subgroupOf.mpr (by rw [SubgroupClass.coe_pow]; exact hn)⟩
  have hrank : CFSG.pRank 5 ↥((oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c)) ≤ 2 := by
    have h1 : CFSG.pRank 5 ↥(oTwoFive X) ≤ CFSG.pRank 5 ↥X := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank 5 (oTwoFive X),
        CFSG.SectionRank.pRank_coe_eq_openPRank 5 X]
      exact CFSG.RankThreeEvenClassification.Helpers.pRank_mono 5 (by norm_num) (oTwoFive_le X)
    rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPK) 5]
    exact h1.trans (MinCex.pRank_five_le hX)
  have hMS : ∀ s ∈ (CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c),
      (∀ p ∈ (oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c),
        ⁅s, p⁆ ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c)) →
      s ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    intro s hs hcomm
    have hsS : (s : G) ∈ CFSG.Open.pCoreOf 2 (H ⊓ M) := Subgroup.mem_subgroupOf.mp hs
    have hcomm' : ∀ y ∈ oTwoFive X, ⁅(s : G), y⁆ ∈ CFSG.Open.pCoreOf 2 X := by
      intro y hy
      have hyK : y ∈ X ⊔ Subgroup.zpowers c := Subgroup.mem_sup_left (hPX hy)
      have h := Subgroup.mem_subgroupOf.mp (hcomm ⟨y, hyK⟩ (Subgroup.mem_subgroupOf.mpr hy))
      simpa [commutatorElement_def] using h
    exact Subgroup.mem_subgroupOf.mpr (MinCex.oTwoFive_inf_S hX (Subgroup.mem_inf.mpr
      ⟨mem_oTwoFive_of_commutator_mem hsol hπ (hSX hsS) hcomm', hsS⟩))
  have hMc : ¬ ∀ p ∈ (oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c),
      ∀ z ∈ Subgroup.zpowers (⟨c, hcK⟩ : ↥(X ⊔ Subgroup.zpowers c)),
        ⁅p, z⁆ ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    intro hall
    apply MinCex.not_commutator_oTwoFive_le h1812 h184 h186 hX hsol h5
    refine Subgroup.commutator_le.mpr fun g hg z hz => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzK : c ^ n ∈ X ⊔ Subgroup.zpowers c :=
      Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers c) n)
    have hz' : (⟨c ^ n, hzK⟩ : ↥(X ⊔ Subgroup.zpowers c)) ∈
        Subgroup.zpowers (⟨c, hcK⟩ : ↥(X ⊔ Subgroup.zpowers c)) :=
      Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simp)⟩
    have h := Subgroup.mem_subgroupOf.mp
      (hall ⟨g, hPK hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨c ^ n, hzK⟩ hz')
    simpa [commutatorElement_def] using h
  exact f13_shape81_abstract ((CFSG.Open.pCoreOf 2 X).subgroupOf (X ⊔ Subgroup.zpowers c))
    ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c))
    ((oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c)) ⟨c, hcK⟩ ψ hS2 hN2 hNS hNP hcS' hc3'
    hPpow hrank hMS hMc hψ

theorem MinCex.oTwoFive_le_commutator_sup (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X)
    (hcent : ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X) :
    oTwoFive X ≤ ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X := by
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hE27 : IsE27 A := isE27_of_mem_partTwoE hX.sec18H.mem_partTwoE
  have hAc : ∀ a ∈ A, Commute a c := fun a ha => f13_comm_of_E27 hE27 ha hcA
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    fun a ha => hX.le_normalizer (Subgroup.mem_sup_left ha)
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hAQ : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    fun a ha => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hAX ha)
  have hcQ : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := hAQ hcA
  have hQX : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hQS : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) := MinCex.pCoreOf_le_S h186 hX
  have hSX : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X := hX.pCoreOf_le
  have hPX : oTwoFive X ≤ X := oTwoFive_le X
  have hXP : X ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoFive X)
  have hAP : A ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    fun a ha => normalizer_le_normalizer_oTwoFive X (hAX ha)
  have hcP : c ∈ Subgroup.normalizer (oTwoFive X : Set G) := hAP hcA
  have hQP : CFSG.Open.pCoreOf 2 X ≤ oTwoFive X := pCoreOf_le_oTwoFive X
  have hsup : oTwoFive X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X :=
    MinCex.sup_oTwoFive_eq h186 hX hsol h5
  have hPS : oTwoFive X ⊓ CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ CFSG.Open.pCoreOf 2 X :=
    MinCex.oTwoFive_inf_S hX
  have hc3 : orderOf c = 3 := MinCex.orderOf_c h184 hX
  have hX3 : ¬ 3 ∣ Nat.card X := hX.not_three_dvd
  have hS3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    fun h => hX3 (h.trans (Subgroup.card_dvd_of_le hSX))
  have hSP : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    fun s hs => hXP (hSX hs)
  have hRS : (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 (H ⊓ M) :=
    inf_centralizer_sup_eq_of_commutator_le hc3 hS3 hQS hcQ hcent
  have hQS' : CFSG.Open.pCoreOf 2 X ⊔
      (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ Subgroup.centralizer ({c} : Set G)) =
      CFSG.Open.pCoreOf 2 (H ⊓ M) := by
    rw [sup_comm]; exact hRS
  have hSdec : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
      CFSG.Open.pCoreOf 2 X ⊔ (CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_of_eq hQS'.symm
  have hStQ : CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    fun t ht => hXQ (hSX (Subgroup.mem_inf.mp ht).1)
  have hSZ : ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ ≤
      ⁅CFSG.Open.pCoreOf 2 X, Subgroup.zpowers c⁆ := by
    refine Subgroup.commutator_le.mpr fun s hs z hz => ?_
    obtain ⟨q, hq, t, ht, rfl⟩ := f13_mem_sup_prod hStQ (hSdec hs)
    have ht1 : ⁅t, z⁆ = 1 :=
      f13_comm_eq_one (f13_commute_zpowers (f13_commute_of_centralizer (Subgroup.mem_inf.mp ht).2) hz)
    have e : ⁅q * t, z⁆ = ⁅q, z⁆ := by
      rw [f13_comm_mul_left, ht1]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hq hz
  have hQZ : ⁅CFSG.Open.pCoreOf 2 X, Subgroup.zpowers c⁆ ≤
      ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ :=
    Subgroup.commutator_mono hQS le_rfl
  have hK1 : X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    fun t ht => hXP (Subgroup.mem_inf.mp ht).1
  have hK2 : X ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    fun t ht => f13_mem_normalizer_zpowers (f13_commute_of_centralizer (Subgroup.mem_inf.mp ht).2)
  have hK3 : X ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    fun t ht => hXQ (Subgroup.mem_inf.mp ht).1
  have hCN : X ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
    rw [le_antisymm hSZ hQZ]
    exact f13_le_normalizer_commutator hK3 hK2
  have hCN' : X ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) :=
    hCN.trans (MinCex.normalizer_commutator_le h1812 h184 h186 hX)
  have hPZ : ⁅oTwoFive X, Subgroup.zpowers c⁆ ≤ oTwoFive X :=
    f13_commutator_le_left (Subgroup.zpowers_le.mpr hcP)
  have hWP : ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X ≤ oTwoFive X :=
    sup_le hPZ hQP
  have hWX : ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X ≤ X := hWP.trans hPX
  have hQN : ∀ x ∈ X, ∀ q ∈ CFSG.Open.pCoreOf 2 X, x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    fun x hx q hq => (Subgroup.mem_normalizer_iff.mp (hXQ hx) q).mp hq
  have hQconj : ∀ g ∈ CFSG.Open.pCoreOf 2 X, ∀ y ∈ ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔
      CFSG.Open.pCoreOf 2 X, g * y * g⁻¹ ∈ ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔
      CFSG.Open.pCoreOf 2 X := by
    intro g hg
    refine f13_conj_sup_mem ?_ ?_
    · refine Subgroup.commutator_le.mpr fun p hp z hz => ?_
      have hx : ⁅p, z⁆ ∈ oTwoFive X := hPZ (Subgroup.commutator_mem_commutator hp hz)
      have e : g * ⁅p, z⁆ * g⁻¹ = ⁅p, z⁆ * ((⁅p, z⁆⁻¹ * g * ⁅p, z⁆⁻¹⁻¹) * g⁻¹) := by
        group
      show g * ⁅p, z⁆ * g⁻¹ ∈ ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hp hz))
        (Subgroup.mem_sup_right (mul_mem (hQN _ (hPX (inv_mem hx)) g hg) (inv_mem hg)))
    · intro q hq
      show g * q * g⁻¹ ∈ ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X
      exact Subgroup.mem_sup_right (hQN g (hQX hg) q hq)
  have hQN_W : CFSG.Open.pCoreOf 2 X ≤ Subgroup.normalizer
      ((⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    fun q hq => f13_mem_normalizer_of_inv (hQconj q hq) (hQconj q⁻¹ (inv_mem hq))
  have hAPZ : A ≤ Subgroup.normalizer ((⁅oTwoFive X, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    f13_le_normalizer_commutator hAP (fun a ha => f13_mem_normalizer_zpowers (hAc a ha))
  have hAW : A ≤ Subgroup.normalizer
      ((⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    le_normalizer_sup hAPZ hAQ
  have hCW : X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer
      ((⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    le_normalizer_sup (f13_le_normalizer_commutator hK1 hK2) hK3
  have hSW : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ Subgroup.normalizer
      ((⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) := by
    intro s hs
    obtain ⟨q, hq, t, ht, rfl⟩ := f13_mem_sup_prod hStQ (hSdec hs)
    exact mul_mem (hQN_W hq)
      (hCW (Subgroup.mem_inf.mpr ⟨hSX (Subgroup.mem_inf.mp ht).1, (Subgroup.mem_inf.mp ht).2⟩))
  have hcW : c ∈ Subgroup.normalizer
      ((⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    hAW hcA
  have hWcomm : ⁅X, Subgroup.zpowers c⁆ ≤
      ⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X := by
    refine Subgroup.commutator_le.mpr fun x hx z hz => ?_
    have hx' : x ∈ oTwoFive X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
      rw [hsup]; exact hx
    obtain ⟨p, hp, s, hs, rfl⟩ := f13_mem_sup_prod hSP hx'
    have hsz : ⁅s, z⁆ ∈ CFSG.Open.pCoreOf 2 X :=
      hcent (Subgroup.commutator_mem_commutator hs hz)
    rw [f13_comm_mul_left]
    exact mul_mem (Subgroup.mem_sup_right (hQN p (hPX hp) _ hsz))
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hp hz))
  have hRW : (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X) = X :=
    inf_centralizer_sup_eq_of_commutator_le hc3 hX3 hWX hcW hWcomm
  have hWS : (⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X) ⊔
      CFSG.Open.pCoreOf 2 (H ⊓ M) = X := by
    by_contra hne
    have hWN := hX.le_of_sup_ne hWX (sup_le hAW hSW) hne
    apply hX.not_le
    rw [← hRW]
    exact sup_le hCN' hWN
  intro p hp
  have hp' : p ∈ (⁅oTwoFive X, Subgroup.zpowers c⁆ ⊔ CFSG.Open.pCoreOf 2 X) ⊔
      CFSG.Open.pCoreOf 2 (H ⊓ M) := by
    rw [hWS]; exact hPX hp
  obtain ⟨w, hw, s, hs, rfl⟩ := f13_mem_sup_prod hSW hp'
  have hsP : s ∈ oTwoFive X := by
    have h := mul_mem (inv_mem (hWP hw)) hp
    rwa [inv_mul_cancel_left] at h
  have hsQ : s ∈ CFSG.Open.pCoreOf 2 X := hPS (Subgroup.mem_inf.mpr ⟨hsP, hs⟩)
  exact mul_mem hw (Subgroup.mem_sup_right hsQ)

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
