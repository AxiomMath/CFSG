module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Case811L4

variable {c : Counterexample4 G} (t : Case811L4 c)

private theorem toAdd_vA1_not_const :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd vA1 = fun _ => s := by
  rintro ⟨s, hs⟩
  have h0 : (1 : ZMod 3) = s := by simpa [vA1] using congrFun hs 0
  have h2 : (-1 : ZMod 3) = s := by simpa [vA1] using congrFun hs 2
  exact absurd (h0.trans h2.symm) (by decide)

private theorem toAdd_vA3_not_const :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd vA3 = fun _ => s := by
  rintro ⟨s, hs⟩
  have h0 : (1 : ZMod 3) = s := by simpa [vA3] using congrFun hs 0
  have h3 : (0 : ZMod 3) = s := by simpa [vA3] using congrFun hs 3
  exact absurd (h0.trans h3.symm) (by decide)

private theorem config_normalizer {v : Multiplicative (Fin 4 → ZMod 3)}
    (hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s)
    (hHM : ¬ Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G) ≤ c.S.M)
    (hrank : 2 ≤ CFSG.Open.pRank t.r
      (c.L ⊓ Subgroup.centralizer ({t.e v} : Set G))) :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.Config
      (c.toSec7Core4 t.mem_sigma) (Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G)) := by
  classical
  refine ⟨?_, hHM, ?_⟩
  ·
    intro htop
    have hXnormal : (Subgroup.zpowers (t.e v)).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact htop
    haveI : IsSimpleGroup G := c.standing.simple
    have hcardX : Nat.card (Subgroup.zpowers (t.e v)) = 3 := t.card_zpowers_e hv
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.zpowers (t.e v)) with hbot | htopX
    · have h1 : Nat.card (Subgroup.zpowers (t.e v)) = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    · have hG : Nat.card G = 3 := by
        rw [← Subgroup.card_top (G := G), ← htopX, hcardX]
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have hcyc : IsCyclic G := isCyclic_of_prime_card (p := 3) hG
      haveI : IsCyclic G := hcyc
      haveI : IsMulCommutative G := IsCyclic.isMulCommutative (α := G)
      obtain ⟨a, b, hab⟩ := c.standing.nonab
      exact hab (isMulCommutative_iff.mp inferInstance a b)
  ·
    have hle : c.L ⊓ Subgroup.centralizer ({t.e v} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G) ⊓ c.S.M := by
      exact le_inf ((inf_le_right : c.L ⊓ Subgroup.centralizer ({t.e v} : Set G) ≤
          Subgroup.centralizer ({t.e v} : Set G)).trans
          (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers (t.e v)))
        (inf_le_left.trans c.hyp81.1)
    have h5 := t.five_le
    exact hrank.trans (CFSG.SectionRank.pRank_mono (by omega) hle)

private theorem point_data (H : Subgroup G) {v : Multiplicative (Fin 4 → ZMod 3)}
    (hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd v = fun _ => s)
    (hH : H = Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G))
    (hHM : ¬ H ≤ c.S.M)
    (hrank : 2 ≤ CFSG.Open.pRank t.r (c.L ⊓ Subgroup.centralizer ({t.e v} : Set G)))
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedSolvable) :
    Odd (Nat.card (CFSG.pPrimeCore t.r ↥H)) ∧
      CFSG.pPrimeCore t.r ↥H ≤ (H ⊓ c.S.M).subgroupOf H ∧
      (IsSolvable ↥(((H ⊓ c.S.M).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pPrimeCore t.r ↥H))) ∨
        (t.r = 5 ∧
          (Nat.card ↥(((H ⊓ c.S.M).subgroupOf H).map
            (QuotientGroup.mk' (CFSG.pPrimeCore t.r ↥H)))).factorization 5 ≤ 2 ∧
          ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore t.r ↥H),
            Y ≤ ((H ⊓ c.S.M).subgroupOf H).map
              (QuotientGroup.mk' (CFSG.pPrimeCore t.r ↥H)) →
            ⁅Y, Y⁆ = Y → Nat.card ↥Y ≤ 3600)) := by
  subst hH
  have hconfig := t.config_normalizer hv hHM hrank
  have hodd : Odd (Nat.card (CFSG.pPrimeCore t.r
      ↥(Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G)))) :=
    (c.toSec7Core4 t.mem_sigma).odd_card_pPrimeCore_of_not_le
      hconfig.not_le hconfig.two_le_pRank
  have hOle : CFSG.pPrimeCore t.r ↥(Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G)) ≤
      (Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G) ⊓ c.S.M).subgroupOf
        (Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G)) := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
    exact (c.toSec7Core4 t.mem_sigma).pPrimeCore_le_of_not_le hconfig.not_le
      hconfig.two_le_pRank (Subgroup.mem_map_of_mem _ hx)
  have h5 := c.five_le_of_mem_sigma t.mem_sigma
  have hmain := (c.toSec7Core4 t.mem_sigma).solvable_or_of_stronglyEmbeddedSolvable h5
    c.three_not_mem_beta hconfig ((c.toSec7Core4 t.mem_sigma).step75 h5 hSE) hS
  exact ⟨hodd, hOle, hmain⟩

private theorem odd_normal_inf_map (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    (hodd : Odd (Nat.card O)) {K : Subgroup G} (hKH : K ≤ H) :
    Odd (Nat.card ↥(K ⊓ O.map H.subtype)) ∧
      ((K ⊓ O.map H.subtype).subgroupOf K).Normal := by
  have hsub : (O.map H.subtype).subgroupOf H = O := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)
  haveI : ((O.map H.subtype).subgroupOf H).Normal := by rw [hsub]; exact inferInstance
  have hnormal : ((K ⊓ O.map H.subtype).subgroupOf K).Normal := by
    have hinf := Subgroup.inf_subgroupOf_inf_normal_of_right (A := K) (B' := O.map H.subtype)
      (B := H)
    rwa [inf_eq_left.mpr hKH] at hinf
  have hodd' : Odd (Nat.card ↥(K ⊓ O.map H.subtype)) := by
    have hdvd : Nat.card ↥(K ⊓ O.map H.subtype) ∣ Nat.card ↥(O.map H.subtype) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  exact ⟨hodd', hnormal⟩

private theorem ker_comp_mk'_subgroupOf (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    (K : Subgroup ↥H) :
    ((QuotientGroup.mk' O).comp K.subtype).ker = O.subgroupOf K := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]

private theorem card_eq_card_map_mul_card (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    {P : Subgroup ↥H} (hOP : O ≤ P) :
    Nat.card ↥P = Nat.card ↥(P.map (QuotientGroup.mk' O)) * Nat.card ↥O := by
  have h1 : Nat.card ↥P = Nat.card (↥P ⧸ O.subgroupOf P) * Nat.card ↥(O.subgroupOf P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf P)
  rw [← CFSG.natCard_map_mk'_eq P O, CFSG.natCard_subgroupOf_eq O P hOP] at h1
  exact h1

private theorem subgroup_data (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    (hoddO : Odd (Nat.card O)) {v : Multiplicative (Fin 4 → ZMod 3)}
    (hH : H = Subgroup.normalizer (Subgroup.zpowers (t.e v) : Set G))
    {K : Subgroup G} (hKle : K ≤ c.L ⊓ Subgroup.centralizer ({t.e v} : Set G)) :
    K ≤ H ∧ K ≤ c.S.M ∧
      Odd (Nat.card ↥(K ⊓ O.map H.subtype)) ∧
      ((K ⊓ O.map H.subtype).subgroupOf K).Normal ∧
      ((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).ker =
        O.subgroupOf (K.subgroupOf H) ∧
      ((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range ≤
        ((H ⊓ c.S.M).subgroupOf H).map (QuotientGroup.mk' O) := by
  have hKH : K ≤ H := by
    rw [hH]
    exact (hKle.trans inf_le_right).trans
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers (t.e v))
  have hKM : K ≤ c.S.M := (hKle.trans inf_le_left).trans c.hyp81.1
  have hdata := odd_normal_inf_map H O hoddO hKH
  have hker := ker_comp_mk'_subgroupOf H O (K.subgroupOf H)
  have hKhM : K.subgroupOf H ≤ (H ⊓ c.S.M).subgroupOf H :=
    Subgroup.subgroupOf_mono H (le_inf hKH hKM)
  have hrange : ((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range ≤
      ((H ⊓ c.S.M).subgroupOf H).map (QuotientGroup.mk' O) := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) (hKhM x.2)
  exact ⟨hKH, hKM, hdata.1, hdata.2, hker, hrange⟩

private theorem perfect_image (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    (hoddO : Odd (Nat.card O)) {K : Subgroup G} (hKH : K ≤ H)
    (hKcomm : ⁅K, K⁆ = K)
    (hKodd : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥) :
    Nat.card ↥(((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range) = Nat.card ↥K ∧
      Group.IsPerfect ↥(((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range) := by
  let Kh : Subgroup ↥H := K.subgroupOf H
  let f : ↥Kh →* ↥H ⧸ O := (QuotientGroup.mk' O).comp Kh.subtype
  let Khat : Subgroup (↥H ⧸ O) := f.range
  have hdata := odd_normal_inf_map H O hoddO hKH
  have hN₀_bot : K ⊓ O.map H.subtype = ⊥ := hKodd _ inf_le_left hdata.2 hdata.1
  have hOsub_bot : O.subgroupOf Kh = ⊥ := by
    by_contra hne
    have h1 : (O.subgroupOf Kh).map Kh.subtype ≠ ⊥ := by
      intro h
      exact hne (Subgroup.map_injective Kh.subtype_injective
        (h.trans (Subgroup.map_bot Kh.subtype).symm))
    have h2 : ((O.subgroupOf Kh).map Kh.subtype).map H.subtype ≠ ⊥ := by
      intro h
      exact h1 (Subgroup.map_injective H.subtype_injective
        (h.trans (Subgroup.map_bot H.subtype).symm))
    have h3 : ((O.subgroupOf Kh).map Kh.subtype).map H.subtype ≤ K ⊓ O.map H.subtype := by
      refine le_inf ?_ ?_
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact z.2
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact Subgroup.mem_map_of_mem H.subtype hz
    rw [hN₀_bot] at h3
    exact h2 (le_antisymm h3 bot_le)
  have hker : f.ker = O.subgroupOf Kh := ker_comp_mk'_subgroupOf H O Kh
  have hcard : Nat.card ↥Khat = Nat.card ↥K := by
    have hinj : Function.Injective f.rangeRestrict := by
      rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_rangeRestrict, hker, hOsub_bot]
    have hcardKh : Nat.card ↥Khat = Nat.card ↥Kh := by
      have h := Nat.card_congr
        (Equiv.ofBijective f.rangeRestrict ⟨hinj, f.rangeRestrict_surjective⟩)
      exact h.symm
    have hcardK : Nat.card ↥Kh = Nat.card ↥K := by
      let e : ↥Kh ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
      exact Nat.card_congr e.toEquiv
    rw [hcardKh, hcardK]
  have hperf : Group.IsPerfect ↥Khat := by
    have hKperf : Group.IsPerfect ↥K := by
      refine ⟨?_⟩
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_subtype_commutator, hKcomm, Subgroup.map_top, Subgroup.range_subtype]
    have hKhperf : Group.IsPerfect ↥Kh := by
      refine ⟨?_⟩
      let e : ↥Kh ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
      have hmap : Subgroup.map e.toMonoidHom (commutator ↥Kh) = ⊤ := by
        rw [show commutator ↥Kh = ⁅(⊤ : Subgroup ↥Kh), ⊤⁆ from rfl,
          Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr e.surjective]
        exact hKperf.commutator_eq_top
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hmap, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
    haveI : Group.IsPerfect ↥Kh := hKhperf
    exact Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  exact ⟨hcard, hperf⟩

private theorem nonsolvable_image (H : Subgroup G) (O : Subgroup ↥H) [O.Normal]
    (hoddO : Odd (Nat.card O)) {K : Subgroup G} (hKH : K ≤ H)
    (hKnsolv : ¬ Group.IsSolvable ↥K)
    (hKcentral : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
      N ≤ Subgroup.centralizer (K : Set G)) :
    ¬ Group.IsSolvable ↥(((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range) := by
  let Kh : Subgroup ↥H := K.subgroupOf H
  let f : ↥Kh →* ↥H ⧸ O := (QuotientGroup.mk' O).comp Kh.subtype
  let Khat : Subgroup (↥H ⧸ O) := f.range
  have hdata := odd_normal_inf_map H O hoddO hKH
  have hN₀_central : K ⊓ O.map H.subtype ≤ Subgroup.centralizer (K : Set G) :=
    hKcentral _ inf_le_left hdata.2 hdata.1
  have hOsub_solv : Group.IsSolvable ↥(O.subgroupOf Kh) := by
    refine Group.isSolvable_of_comm ?_
    intro a b
    have haK : (((a.1 : ↥Kh) : ↥H) : G) ∈ K := a.1.2
    have hbN₀ : (((b.1 : ↥Kh) : ↥H) : G) ∈ K ⊓ O.map H.subtype := by
      refine ⟨b.1.2, ?_⟩
      exact Subgroup.mem_map_of_mem H.subtype b.2
    have hbC : (((b.1 : ↥Kh) : ↥H) : G) ∈ Subgroup.centralizer (K : Set G) :=
      hN₀_central hbN₀
    have hcomm := Subgroup.mem_centralizer_iff.mp hbC (((a.1 : ↥Kh) : ↥H) : G) haK
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    simpa using hcomm
  intro hKhat_solv
  haveI : Group.IsSolvable ↥(O.subgroupOf Kh) := hOsub_solv
  haveI : Group.IsSolvable ↥Khat := hKhat_solv
  have hker : f.ker = O.subgroupOf Kh := ker_comp_mk'_subgroupOf H O Kh
  have hker_le : f.rangeRestrict.ker ≤ (O.subgroupOf Kh).subtype.range := by
    rw [MonoidHom.ker_rangeRestrict, hker, Subgroup.range_subtype]
  have hKh_solv : Group.IsSolvable ↥Kh :=
    Group.isSolvable_of_ker_le_range (O.subgroupOf Kh).subtype f.rangeRestrict hker_le
  let e : ↥Kh ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  exact hKnsolv (Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective)

private theorem a3_arithmetic {H : Subgroup G} {O : Subgroup ↥H} [O.Normal]
    {Nbar : Subgroup (↥H ⧸ O)}
    (hle_subs : c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G) ≤ H ⊓ c.S.M)
    (hcard_HM : Nat.card ↥(H ⊓ c.S.M) = Nat.card ↥Nbar * Nat.card ↥O)
    (hcop5 : Nat.Coprime 5 (Nat.card ↥O))
    (h5 : t.r = 5)
    (hfacNbar : (Nat.card ↥Nbar).factorization 5 ≤ 2) : False := by
  have ha3A : t.a3 ∈ t.A := t.e_mem_A vA3
  have ha3M : t.a3 ∈ c.S.M := c.hyp81.1 (t.P_le_L (t.A_le ha3A))
  have ha3C : t.a3 ∈ Subgroup.centralizer ({t.a3} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem_a3 : t.a3 ∈ c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G) := ⟨ha3M, ha3C⟩
  have hnonempty : Nonempty ↥(c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G)) :=
    ⟨⟨t.a3, hmem_a3⟩⟩
  have hcard_ne : Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨hnonempty, inferInstance⟩
  have hfac3 : (Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G))).factorization 5 = 3 := by
    rw [← h5]
    exact t.factorization_a3
  have hdvd1 : 5 ^ 3 ∣ Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G)) :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hcard_ne).mpr (by omega)
  have hdvd_mul : 5 ^ 3 ∣ Nat.card ↥Nbar * Nat.card ↥O := by
    rw [← hcard_HM]
    exact hdvd1.trans (Subgroup.card_dvd_of_le hle_subs)
  have hcop : Nat.Coprime (5 ^ 3) (Nat.card ↥O) := hcop5.pow_left 3
  have hdvdNbar : 5 ^ 3 ∣ Nat.card ↥Nbar :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd_mul
  have hNbar_ne : Nat.card ↥Nbar ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨1, Nbar.one_mem⟩⟩, inferInstance⟩
  have h3le : 3 ≤ (Nat.card ↥Nbar).factorization 5 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hNbar_ne).mp hdvdNbar
  omega

theorem normalizer_a1_le
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedSolvable) :
    Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M := by
  classical
  by_contra hHM
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers t.a1 : Set G)
  let O : Subgroup ↥H := CFSG.pPrimeCore t.r ↥H
  let Nbar : Subgroup (↥H ⧸ O) := ((H ⊓ c.S.M).subgroupOf H).map (QuotientGroup.mk' O)
  obtain ⟨hoddO, -, hmain⟩ :=
    t.point_data H (v := vA1) toAdd_vA1_not_const rfl hHM t.two_le_pRank_a1 hSE hS
  obtain ⟨K, hKle, hKcomm, hKcard, hKodd⟩ := t.perfect_a1
  obtain ⟨hKH, -, -, -, -, hKhat_le⟩ :=
    t.subgroup_data H O hoddO (v := vA1) rfl hKle
  obtain ⟨hKhat_card, hKhatperf⟩ := perfect_image H O hoddO hKH hKcomm hKodd
  let Khat : Subgroup (↥H ⧸ O) := ((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range
  have hKhat_gt : 3600 < Nat.card ↥Khat := by
    rw [hKhat_card]
    exact hKcard
  haveI : Nontrivial ↥Khat := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have h1 : Nat.card ↥Khat = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hKhat_comm : ⁅Khat, Khat⁆ = Khat := by
    rw [← Subgroup.map_subtype_commutator Khat, hKhatperf.commutator_eq_top,
      Subgroup.map_top, Subgroup.range_subtype]
  rcases hmain with hsolv | hsecond
  · haveI : Group.IsSolvable ↥Nbar := hsolv
    have hKhat_solv : Group.IsSolvable ↥Khat :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hKhat_le) (Subgroup.inclusion_injective hKhat_le)
    exact (Group.IsPerfect.not_isSolvable ↥Khat) hKhat_solv
  · have hle := hsecond.2.2 Khat hKhat_le hKhat_comm
    exact (not_le_of_gt hKhat_gt) hle

theorem normalizer_a3_le
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedSolvable) :
    Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M := by
  classical
  by_contra hHM
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers t.a3 : Set G)
  let O : Subgroup ↥H := CFSG.pPrimeCore t.r ↥H
  let Nbar : Subgroup (↥H ⧸ O) := ((H ⊓ c.S.M).subgroupOf H).map (QuotientGroup.mk' O)
  obtain ⟨hoddO, hOle, hmain⟩ :=
    t.point_data H (v := vA3) toAdd_vA3_not_const rfl hHM t.two_le_pRank_a3 hSE hS
  obtain ⟨K, hKle, hKnsolv, hKcentral⟩ := t.nonsolvable_a3
  obtain ⟨hKH, -, -, -, -, hKhat_le⟩ :=
    t.subgroup_data H O hoddO (v := vA3) rfl hKle
  let Khat : Subgroup (↥H ⧸ O) := ((QuotientGroup.mk' O).comp (K.subgroupOf H).subtype).range
  have hKhat_nonsolv := nonsolvable_image H O hoddO hKH hKnsolv hKcentral
  have hNotSolvNbar : ¬ Group.IsSolvable ↥Nbar := by
    intro hs
    haveI : Group.IsSolvable ↥Nbar := hs
    exact hKhat_nonsolv (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hKhat_le) (Subgroup.inclusion_injective hKhat_le))
  have hsecond : t.r = 5 ∧ (Nat.card ↥Nbar).factorization 5 ≤ 2 := by
    rcases hmain with hs | hs
    · exact absurd hs hNotSolvNbar
    · exact ⟨hs.1, hs.2.1⟩
  have hle_subs : c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G) ≤ H ⊓ c.S.M := by
    refine le_inf ?_ inf_le_left
    change c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers t.a3 : Set G)
    exact (inf_le_right : c.S.M ⊓ Subgroup.centralizer ({t.a3} : Set G) ≤
      Subgroup.centralizer ({t.a3} : Set G)).trans
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers (t.a3))
  have hcard_HM : Nat.card ↥(H ⊓ c.S.M) = Nat.card ↥Nbar * Nat.card ↥O := by
    rw [← CFSG.natCard_subgroupOf_eq (H ⊓ c.S.M) H inf_le_left]
    exact card_eq_card_map_mul_card H O hOle
  have hcop5 : Nat.Coprime 5 (Nat.card ↥O) := by
    haveI : Fact t.r.Prime := ⟨t.mem_sigma.1.1⟩
    have h := CFSG.pPrimeCore_coprime_card (p := t.r) (G := ↥H)
    rw [hsecond.1] at h
    simpa [O, hsecond.1] using h
  exact a3_arithmetic t hle_subs hcard_HM hcop5 hsecond.1 hsecond.2

end Case811L4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
