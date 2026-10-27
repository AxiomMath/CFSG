module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
import CFSG.Open.BenderStronglyEmbedded
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Dihedral.BrauerSuzuki
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSolvable_normalizer_of_benderBorel {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (hB : fusionBenderBorel G q k) (Q : Sylow 2 G) :
    Group.IsSolvable (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
  obtain ⟨-, ⟨D, hDcyc, -, -, hsup⟩, -⟩ := hB Q
  have hDle : D ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := hsup ▸ le_sup_right
  let H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  let Qn : Subgroup H := (Q : Subgroup G).subgroupOf H
  have : Qn.Normal := Subgroup.normal_in_normalizer
  have : Group.IsSolvable Qn := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent Qn := (Q.isPGroup'.comap_subtype (K := H)).isNilpotent
    infer_instance
  have : IsCyclic D := hDcyc
  have : IsCyclic (H ⧸ Qn) := by
    refine isCyclic_of_surjective ((QuotientGroup.mk' Qn).comp (Subgroup.inclusion hDle)) ?_
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : (x : G) ∈ D ⊔ (Q : Subgroup G) := by
      rw [sup_comm, hsup]; exact x.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D (Q : Subgroup G) hDle]
      at hx
    obtain ⟨d, hd, q, hq, hdq⟩ := hx
    refine ⟨⟨d, hd⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hx' : (x : G) = d * q := hdq.symm
    have hq' : q ∈ (Q : Subgroup G) := hq
    simpa [hx'] using hq'
  have : Group.IsSolvable (H ⧸ Qn) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient Qn

theorem centralizer_le_normalizer_of_stronglyEmbedded {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} (hSE : fusionStronglyEmbedded (Subgroup.normalizer (Q : Set G)))
    {z : G} (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  by_contra hgn
  have hodd := hSE.2.2 g hgn
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hzQ
  have hmem : z ∈ Subgroup.normalizer (Q : Set G) ⊓
      (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    refine ⟨hzN, z, hzN, ?_⟩
    have hc : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z rfl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, hc, inv_mul_cancel_left]
  have h2 : 2 ∣ Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓
      (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g⁻¹).toMonoidHom) := by
    have := orderOf_dvd_natCard (⟨z, hmem⟩ : ↥(Subgroup.normalizer (Q : Set G) ⊓
      (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g⁻¹).toMonoidHom))
    rwa [Subgroup.orderOf_mk, hz] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem stronglyEmbedded_subgroupOf {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : fusionStronglyEmbedded E) (K : Subgroup G) (hK : ¬ K ≤ E)
    (heven : Even (Nat.card ↥(E ⊓ K))) : fusionStronglyEmbedded (E.subgroupOf K) := by
  refine ⟨fun h => hK (Subgroup.subgroupOf_eq_top.mp h), ?_, ?_⟩
  · have hcard : Nat.card ↥(E.subgroupOf K) = Nat.card ↥(E ⊓ K) := by
      rw [← Subgroup.subgroupOf_map_subtype E K]
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm
    rwa [hcard]
  · intro g hg
    have hgE : (g : G) ∉ E := hg
    have hodd := hE.2.2 (g : G) hgE
    set T := E.subgroupOf K ⊓ (E.subgroupOf K).map (MulAut.conj g⁻¹).toMonoidHom with hT
    have hle : T.map K.subtype ≤ E ⊓ E.map (MulAut.conj (g : G)⁻¹).toMonoidHom := by
      rintro _ ⟨t, ⟨htM, m, hm, rfl⟩, rfl⟩
      refine ⟨htM, (m : G), hm, ?_⟩
      simp
    have hdvd : Nat.card T ∣ Nat.card ↥(E ⊓ E.map (MulAut.conj (g : G)⁻¹).toMonoidHom) := by
      rw [← Subgroup.card_map_of_injective (K := T) K.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact hodd.of_dvd_nat hdvd

theorem eq_one_of_mem_odd_subgroup_of_pow_two_pow {H : Type*} [Group H] {N : Subgroup H}
    (hN : Odd (Nat.card N)) {c : H} (hcN : c ∈ N) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf c ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨c, hcN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hN.of_dvd_nat h2))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)

theorem centralizer_sup_eq_top_of_odd_normal {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N)) {z : H} (hz : orderOf z = 2)
    (hc : ∀ x : H, ⁅x, z⁆ ∈ N) :
    Subgroup.centralizer ({z} : Set H) ⊔ N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup H := N ⊔ Subgroup.zpowers z with hY
  have hzY : z ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hYn : Y.Normal := by
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : x * z * x⁻¹ ∈ Y := by
      have : x * z * x⁻¹ = ⁅x, z⁆ * z := by
        rw [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem_sup (hc x) (Subgroup.mem_zpowers z)
    have h2 : x * (n * z ^ k) * x⁻¹ = (x * n * x⁻¹) * (x * z * x⁻¹) ^ k := by
      rw [conj_zpow]; group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem ‹N.Normal› n hn x))
      (Subgroup.zpow_mem _ h1 k)
  let w : Y := ⟨z, hzY⟩
  have hw : orderOf w = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  obtain ⟨P0, hP0⟩ : ∃ P0 : Sylow 2 Y, Subgroup.zpowers w ≤ P0 := by
    refine IsPGroup.exists_le_sylow (IsPGroup.of_card (n := 1) ?_)
    rw [Nat.card_zpowers, hw, pow_one]
  have hfr := Sylow.normalizer_sup_eq_top P0
  have hzP : z ∈ (P0 : Subgroup Y).map Y.subtype := ⟨w, hP0 (Subgroup.mem_zpowers w), rfl⟩
  have hnorm : Subgroup.normalizer (((P0 : Subgroup Y).map Y.subtype : Subgroup H) : Set H) ≤
      Subgroup.centralizer ({z} : Set H) := by
    intro g hg
    have h1 : g * z * g⁻¹ ∈ (P0 : Subgroup Y).map Y.subtype :=
      (Subgroup.mem_normalizer_iff.mp hg z).mp hzP
    have h2 : ⁅g, z⁆ ∈ (P0 : Subgroup Y).map Y.subtype := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzP)
    have h3 : ⁅g, z⁆ = 1 := by
      obtain ⟨p, hp, hpc⟩ := h2
      obtain ⟨k, hk⟩ := P0.isPGroup' ⟨p, hp⟩
      refine eq_one_of_mem_odd_subgroup_of_pow_two_pow hN (hc g) (k := k) ?_
      rw [← hpc]
      have := congrArg (fun u : (P0 : Subgroup Y) => ((u : Y) : H)) hk
      simpa using this
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hzC : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
  refine top_le_iff.mp ?_
  calc (⊤ : Subgroup H)
      = Subgroup.normalizer (((P0 : Subgroup Y).map Y.subtype : Subgroup H) : Set H) ⊔ Y :=
        hfr.symm
    _ ≤ Subgroup.centralizer ({z} : Set H) ⊔ N :=
      sup_le (hnorm.trans le_sup_left) (sup_le le_sup_right (hzC.trans le_sup_left))

theorem isSolvable_of_centralizer_isSolvable {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : Odd (Nat.card N)) {z : K} (hz : orderOf z = 2)
    (hc : ∀ x : K, ⁅x, z⁆ ∈ N) (hC : Group.IsSolvable (Subgroup.centralizer ({z} : Set K))) :
    Group.IsSolvable K := by
  have hNs : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard N hN
  have hsup := centralizer_sup_eq_top_of_odd_normal N hN hz hc
  have hQ : Group.IsSolvable (K ⧸ N) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' N).comp (Subgroup.centralizer ({z} : Set K)).subtype) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ Subgroup.centralizer ({z} : Set K) ⊔ N := by rw [hsup]; trivial
    obtain ⟨c, hcC, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨c, hcC⟩, ?_⟩
    show (QuotientGroup.mk c : K ⧸ N) = QuotientGroup.mk (c * n)
    rw [QuotientGroup.eq]
    simpa using hn
  exact Group.isSolvable_of_subgroup_quotient N

theorem isSolvable_of_isCyclic_sylow_two {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (hP : IsCyclic P) : Group.IsSolvable K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hnormal, hodd, hindex, -⟩, -⟩ := cyclic_sylow_normal_odd_complement P hP
  have hs1 : Group.IsSolvable (pPrimeCore 2 K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : (pPrimeCore 2 K).Normal := hnormal
  have hs2 : Group.IsSolvable (K ⧸ pPrimeCore 2 K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hq : IsPGroup 2 (K ⧸ pPrimeCore 2 K) :=
      IsPGroup.of_card (n := n) (by rw [← Subgroup.index_eq_card, hindex, hn])
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (pPrimeCore 2 K)

theorem odd_card_oddCore_of_finite (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (oddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : oddCore H = pPrimeCore 2 H := by
    unfold oddCore pPrimeCore
    congr 1
    ext N
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem isSolvable_of_quaternion_sylow {K : Type*} [Group K] [Finite K]
    (hC : ∀ z : K, orderOf z = 2 → Group.IsSolvable (Subgroup.centralizer ({z} : Set K)))
    (P : Sylow 2 K) {r : ℕ} (hr : 3 ≤ r)
    (hquat : Nonempty ((P : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Group.IsSolvable K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPeven : 2 ∣ Nat.card (P : Subgroup K) := by
    obtain ⟨e⟩ := hquat
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    exact ⟨2 * 2 ^ (r - 2), by ring⟩
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' 2 hPeven
  have hz : orderOf (z0 : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz0
  have hcent := CFSG.BrauerSuzuki.brauer_suzuki r hr P hquat (z0 : K) z0.2 hz
  have hcomm : ∀ x : K, ⁅x, (z0 : K)⁆ ∈ oddCore K :=
    CFSG.BrauerSuzuki.Helpers.quotient_mk_mem_center_iff.mp hcent
  exact isSolvable_of_centralizer_isSolvable (oddCore K) (odd_card_oddCore_of_finite K) hz hcomm
    (hC _ hz)

theorem isSolvable_centralizer_of_involution {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (hB : fusionBenderBorel G q k) (K : Subgroup G) {z : K} (hz : orderOf z = 2) :
    Group.IsSolvable (Subgroup.centralizer ({z} : Set K)) := by
  have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 G, Subgroup.zpowers (z : G) ≤ Q := by
    refine IsPGroup.exists_le_sylow (IsPGroup.of_card (n := 1) ?_)
    rw [Nat.card_zpowers, hz', pow_one]
  have hzQ : (z : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
  have hcle := centralizer_le_normalizer_of_stronglyEmbedded (hB Q).1 hzQ hz'
  have := isSolvable_normalizer_of_benderBorel hB Q
  have hmem : ∀ c : Subgroup.centralizer ({z} : Set K),
      ((c : K) : G) ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro c
    apply hcle
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have := Subgroup.mem_centralizer_iff.mp c.2 z rfl
    exact congrArg (fun u : K => (u : G)) this
  let f : Subgroup.centralizer ({z} : Set K) →*
      Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    ((K.subtype).comp (Subgroup.centralizer ({z} : Set K)).subtype).codRestrict _ hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ((a : K) : G) = ((b : K) : G) :=
      congrArg (fun u : Subgroup.normalizer ((Q : Subgroup G) : Set G) => (u : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem isSolvable_of_sylow_cyclic_or_quaternion {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (hB : fusionBenderBorel G q k) (K : Subgroup G)
    (h : ∀ S : Sylow 2 K, IsCyclic (S : Subgroup K) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Group.IsSolvable K := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  rcases h P with hcyc | ⟨r, hr, hquat⟩
  · exact isSolvable_of_isCyclic_sylow_two P hcyc
  · exact isSolvable_of_quaternion_sylow
      (fun z hz => isSolvable_centralizer_of_involution hB K hz) P hr hquat

theorem even_card_of_simple_of_not_comm {S : Type*} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Even (Nat.card S) := by
  by_contra h
  have hodd : Odd (Nat.card S) := Nat.not_even_iff_odd.mp h
  obtain ⟨a, b, hab⟩ := hna
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard S hodd) a b)

theorem nonempty_mulEquiv_of_simple_section {X : Type*} [Group X] [Finite X]
    {M N L : Subgroup X} [M.Normal] [N.Normal] [L.Normal] [(M.subgroupOf N).Normal]
    (hMo : Odd (Nat.card M)) (hNo : Odd N.index)
    (hB : IsSimpleGroup (N ⧸ M.subgroupOf N))
    (hS : IsSimpleGroup (X ⧸ L)) (hna : ∃ a b : X ⧸ L, a * b ≠ b * a) :
    Nonempty ((X ⧸ L) ≃* (N ⧸ M.subgroupOf N)) := by
  have hev := even_card_of_simple_of_not_comm hS hna
  let π : X →* X ⧸ L := QuotientGroup.mk' L
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective L
  have hML : M ≤ L := by
    have hn : (M.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases hn.eq_bot_or_eq_top with h | h
    · simpa [π] using (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hd : Nat.card (M.map π) ∣ Nat.card M := Subgroup.card_map_dvd M π
      rw [h, Subgroup.card_top] at hd
      exact (Nat.not_even_iff_odd.mpr (hMo.of_dvd_nat hd)) hev
  have hNL : ¬ N ≤ L := by
    intro h
    have hd : L.index ∣ N.index := Subgroup.index_dvd_of_le h
    have h1 : Odd L.index := hNo.of_dvd_nat hd
    rw [Subgroup.index_eq_card] at h1
    exact (Nat.not_even_iff_odd.mpr h1) hev
  let φ : N →* X ⧸ L := π.comp N.subtype
  have hφker : φ.ker = L.subgroupOf N := by
    ext n
    simp [φ, π, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hφ : Function.Surjective φ := by
    have hn : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases hn.eq_bot_or_eq_top with h | h
    · exact absurd (by simpa [π] using (Subgroup.map_eq_bot_iff _).mp h) hNL
    · intro s
      have hs : s ∈ N.map π := h ▸ Subgroup.mem_top s
      obtain ⟨n, hn, rfl⟩ := hs
      exact ⟨⟨n, hn⟩, rfl⟩
  let ρ : N →* N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N)
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hMR : M.subgroupOf N ≤ L.subgroupOf N := fun n hn => hML hn
  have hR : ((L.subgroupOf N).map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρ
  rcases hR.eq_bot_or_eq_top with h | h
  · have hRM : L.subgroupOf N ≤ M.subgroupOf N := by
      have := (Subgroup.map_eq_bot_iff _).mp h
      simpa [ρ] using this
    have hker : φ.ker = M.subgroupOf N := by rw [hφker]; exact le_antisymm hRM hMR
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩
  · exfalso
    have h1 : L.subgroupOf N ⊔ ρ.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    have h2 : ρ.ker ≤ L.subgroupOf N := by
      rw [QuotientGroup.ker_mk']; exact hMR
    rw [sup_eq_left.mpr h2] at h1
    exact hNL (Subgroup.subgroupOf_eq_top.mp h1)

theorem isBenderGroup_of_simple_section
    {G : Type} [Group G] [Finite G] {q k : ℕ}
    (hB : CFSG.Open.fusionBenderBorel G q k) (K L : Subgroup G) (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] (hs : IsSimpleGroup (K ⧸ L.subgroupOf K))
    (hna : ∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) :
    CFSG.Open.fusionIsBenderGroup (K ⧸ L.subgroupOf K) := by
  have _hLK : L ≤ K := hLK
  have hKns : ¬ Group.IsSolvable K := by
    intro hKs
    obtain ⟨a, b, hab⟩ := hna
    have : Group.IsSolvable (K ⧸ L.subgroupOf K) := inferInstance
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
  have hKeven : 2 ∣ Nat.card K := by
    by_contra h
    exact hKns (CFSG.FeitThompson.isSolvable_of_odd_natCard K (Nat.odd_iff.mpr (by omega)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hKeven
  have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 G, Subgroup.zpowers (x : G) ≤ Q := by
    refine IsPGroup.exists_le_sylow (IsPGroup.of_card (n := 1) ?_)
    rw [Nat.card_zpowers, hx', pow_one]
  have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers _)
  have hxE : (x : G) ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hxQ
  have hKE : ¬ K ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro h
    have := isSolvable_normalizer_of_benderBorel hB Q
    exact hKns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h))
  have heven : Even (Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓ K)) := by
    let y : ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓ K) := ⟨(x : G), hxE, x.2⟩
    have hord : orderOf y = 2 := by rw [← Subgroup.orderOf_coe y]; exact hx'
    have := orderOf_dvd_natCard y
    rw [hord] at this
    exact even_iff_two_dvd.mpr this
  have hSE := stronglyEmbedded_subgroupOf (hB Q).1 K hKE heven
  rcases CFSG.Open.Open.bender_strongly_embedded K _ hSE with
    halt | ⟨M, N, hM, hN, hMN', -, hMo, hNo, hBN⟩
  · exact absurd (isSolvable_of_sylow_cyclic_or_quaternion hB K halt) hKns
  · have := hM
    have := hN
    have := hMN'
    have hsimple := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hBN
    obtain ⟨e⟩ := nonempty_mulEquiv_of_simple_section hMo hNo hsimple hs hna
    exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv e.symm hBN

end CFSG.SignalizerFunctorTheorem.CatalogBridge
