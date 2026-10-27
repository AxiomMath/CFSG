module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmasB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer
public import CFSG.Mathlib.Arithmetic.TwoPowSubOneSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem exists_conj_of_conjSetOf_ne {M X : Subgroup G} (hXM : X ≤ M)
    (h : conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ M} ≠ conjSetOf M X) :
    ∃ g : G, g ∉ M ∧ X.map (MulAut.conj g).toMonoidHom ≤ M ∧
      X.map (MulAut.conj g).toMonoidHom ∉ conjSetOf M X := by
  classical
  have hsub : conjSetOf M X ⊆
      conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ M} := by
    rintro Y ⟨m, hm, rfl⟩
    refine ⟨⟨m, Subgroup.mem_top m, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hXM hx)) (M.inv_mem hm)
  obtain ⟨Y, ⟨⟨g, -, hYeq⟩, hYM⟩, hYnot⟩ :=
    Set.exists_of_ssubset (Set.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm h⟩)
  refine ⟨g, fun hgM => hYnot ⟨g, hgM, hYeq⟩, ?_, ?_⟩
  · rw [← hYeq]
    exact hYM
  · rw [← hYeq]
    exact hYnot

theorem card_barImage_of_prime {D : Data G} {Y : Subgroup G} {r : ℕ}
    (hYM : Y ≤ D.M) (hr : r.Prime) (hr2 : r ≠ 2) (hYcard : Nat.card Y = r) :
    Nat.card (barImage D.M Y) = r := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : IsPGroup 2 ↥(Y ⊓ pCoreOf 2 D.M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le inf_le_right
  obtain ⟨k, hk⟩ := hI2.exists_card_eq
  have hIr : Nat.card ↥(Y ⊓ pCoreOf 2 D.M) ∣ r := by
    rw [← hYcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hI1 : Nat.card ↥(Y ⊓ pCoreOf 2 D.M) = 1 := by
    rcases (Nat.dvd_prime hr).mp hIr with h1 | hr'
    · exact h1
    · exfalso
      have h2 : r ∣ 2 ^ k := by rw [← hk, hr']
      have h3 : r ∣ 2 := hr.dvd_of_dvd_pow h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3)
  have hIbot : Y ⊓ pCoreOf 2 D.M = ⊥ := Subgroup.card_eq_one.mp hI1
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  have hiff : ∀ x : ↥D.M, π x = 1 ↔ (x : G) ∈ pCoreOf 2 D.M := by
    intro x
    change QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x = 1 ↔ (x : G) ∈ pCoreOf 2 D.M
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥D.M) x).trans
      (Subgroup.mem_map_iff_mem D.M.subtype_injective).symm
  have hker : (Y.subgroupOf D.M) ⊓ π.ker =
      (Y ⊓ pCoreOf 2 D.M).subgroupOf D.M := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rw [hiff (x : ↥D.M)]
  have hcardker : Nat.card ↥((Y.subgroupOf D.M) ⊓ π.ker) = 1 := by
    rw [hker, hIbot]
    simp
  have hmap : (Y.subgroupOf D.M).map π = barImage D.M Y := rfl
  have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π (Y.subgroupOf D.M)
  rw [hcardker, Nat.mul_one] at h
  have hcardY : Nat.card ↥(Y.subgroupOf D.M) = r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv).trans hYcard
  rw [← hmap, ← h, hcardY]


theorem eq_seven_of_dvd_card_mulAut_L34 {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r)
    (hdvd : r ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7) : r = 7 := by
  have h2 : ¬ r ∣ 2 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
    omega
  have h3 : ¬ r ∣ 3 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
    omega
  have h5 : ¬ r ∣ 5 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 5)).mp h
    omega
  have h2p : ¬ r ∣ 2 ^ 8 := fun h => h2 (hr.dvd_of_dvd_pow h)
  have h3p : ¬ r ∣ 3 ^ 3 := fun h => h3 (hr.dvd_of_dvd_pow h)
  have hdvd' : r ∣ 2 ^ 8 * (3 ^ 3 * (5 * 7)) := by
    simpa [show 2 ^ 8 * 3 ^ 3 * 5 * 7 = 2 ^ 8 * (3 ^ 3 * (5 * 7)) by ring] using hdvd
  rcases hr.dvd_mul.mp hdvd' with h | h
  · exact absurd h h2p
  rcases hr.dvd_mul.mp h with h | h
  · exact absurd h h3p
  rcases hr.dvd_mul.mp h with h | h
  · exact absurd h h5
  exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_seven).mp h

theorem eq_seven_of_barImage_not_centralizes {D : Data G} {L Y : Subgroup G} {r : ℕ}
    (hL : L ∈ calC D.M) (hLn : (L.subgroupOf D.M).Normal) (hL3 : IsL3 (Bar2 L) 2)
    (hYM : Y ≤ D.M) (hr : r.Prime) (hr2 : r ≠ 2) (hYcard : Nat.card Y = r)
    (h7 : 7 ≤ r)
    (hcent : ¬ barImage D.M Y ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M))) :
    r = 7 := by
  classical
  have hLbar : (barImage D.M L).Normal := s13_barImage_normal hLn
  have htop : Subgroup.normalizer (barImage D.M L : Set (Bar2 D.M)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hYN : barImage D.M Y ≤
      Subgroup.normalizer (barImage D.M L : Set (Bar2 D.M)) := by
    rw [htop]
    exact le_top
  let ψ : ↥(barImage D.M Y) →*
      ↥(Subgroup.normalizer (barImage D.M L : Set (Bar2 D.M))) := Subgroup.inclusion hYN
  let φ : ↥(barImage D.M Y) →* MulAut ↥(barImage D.M L) :=
    (barImage D.M L).normalizerMonoidHom.comp ψ
  have hcardYbar : Nat.card ↥(barImage D.M Y) = r := card_barImage_of_prime hYM hr hr2 hYcard
  have hkerφ : φ.ker =
      (Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M))).subgroupOf (barImage D.M Y) := by
    ext x
    simp only [MonoidHom.mem_ker, φ, ψ, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    change (barImage D.M L).normalizerMonoidHom (Subgroup.inclusion hYN x) = 1 ↔
      (x : Bar2 D.M) ∈ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M))
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hnotker : φ.ker ≠ ⊤ := by
    intro htopker
    apply hcent
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥(barImage D.M Y)) ∈ φ.ker := by
      rw [htopker]
      exact Subgroup.mem_top _
    rwa [hkerφ, Subgroup.mem_subgroupOf] at hmem
  have hkerdvd : Nat.card ↥φ.ker ∣ r := by
    have h : Nat.card ↥φ.ker ∣ Nat.card ↥(barImage D.M Y) := by
      simpa using Subgroup.card_dvd_of_le
        (H := φ.ker) (K := (⊤ : Subgroup ↥(barImage D.M Y))) le_top
    rwa [hcardYbar] at h
  have hker1 : Nat.card ↥φ.ker = 1 := by
    rcases (Nat.dvd_prime hr).mp hkerdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq φ.ker (by rw [h, hcardYbar])) hnotker
  have hrange : Nat.card ↥φ.range = r := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker1, one_mul, hcardYbar] at h
    exact h
  have hdvdAut : r ∣ Nat.card (MulAut ↥(barImage D.M L)) := by
    rw [← hrange]
    exact Subgroup.card_subgroup_dvd_card φ.range
  obtain ⟨e⟩ := s13_bar_equiv hL
  have hcardAut : Nat.card (MulAut ↥(barImage D.M L)) =
      Nat.card (MulAut (Bar2 L)) :=
    Nat.card_congr (MulAut.congr e).toEquiv.symm
  rw [hcardAut, card_mulAut_bar_of_isL3 hL3] at hdvdAut
  exact eq_seven_of_dvd_card_mulAut_L34 hr h7 hdvdAut


theorem prime_dvd_two_pow_sub_one_eq_seven (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V)
    (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    {n r : ℕ} (hnodd : Odd n) (hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) : r = 7 := by
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := (s13_le_of_mem_calC hK).trans (Lp_le_M D p)
  have hKnorm : (K.subgroupOf D.M).Normal := (ctx.hyp54.2 K hKcalM).1
  have hKthin : F08.Thin8 K := by
    rcases hKshape with h | h
    · exact thin8_of_isL2 h
    · exact thin8_of_isSz h
  have hrBar : r ∣ Nat.card (Bar2 K) := by
    rcases hKshape with hL2 | hSz
    · rw [card_of_isL2 hL2]
      have hdvd : r ∣ 2 ^ (2 * n) - 1 := by
        have h1 : r ∣ (2 ^ n) ^ 2 - 1 :=
          hrdvd.trans (by
            simpa using Nat.pow_sub_one_dvd_pow_sub_one (2 ^ n)
              (show 1 ∣ 2 by norm_num))
        rwa [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; ring_nf] at h1
      exact hdvd.trans (dvd_mul_of_dvd_right (dvd_refl _) (2 ^ n))
    · exact dvd_card_bar2_of_isSz_sub_one hSz hrdvd
  obtain ⟨X, hXK, hXcard⟩ := s13_exists_subgroup_of_dvd_card_bar hr hrBar
  have hXM : X ≤ D.M := hXK.trans hKM
  have h7 : 7 ≤ r := s13_seven_le_of_dvd hnodd hr hrdvd
  have hr2 : r ≠ 2 := by omega
  have h55' := h55 K hKM hKnorm n hKshape n hnodd dvd_rfl r hr hrdvd X hXK hXcard
  obtain ⟨g, hgM, hYle, hYnot⟩ := exists_conj_of_conjSetOf_ne hXM h55'
  let Y : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  have hYeq : Y = X.map (MulAut.conj g).toMonoidHom := rfl
  have hYcard : Nat.card Y = r := by
    rw [hYeq, Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
  have hCX : Subgroup.centralizer (X : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (X : Set G)).trans
      (h3 K hKcalM hKthin X ⟨r, hr, hr2, hXcard, hXK⟩)
  have hcent : ¬ barImage D.M Y ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) :=
    barImage_not_le_centralizer_of_conj D ctx h59 h63 hr hr2 hYcard hYle hYeq hgM hCX
  exact eq_seven_of_barImage_not_centralizes ctx.memC (ctx.hyp54.2 L ctx.memC).1
    ctx.shapeL hYle hr hr2 hYcard h7 hcent


theorem eq_three_of_counter (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V)
    (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    {n : ℕ} (hnodd : Odd n) (hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n) :
    n = 3 := by
  have hn2 : 2 ≤ n := by
    rcases hKshape with h | h
    · exact s13_two_le_of_isL2 h
    · have := (s13_odd_three_le_of_isSz h).2
      omega
  exact CFSG.eq_three_of_forall_prime_dvd_two_pow_sub_one n hnodd hn2
    (fun r hr hrd => prime_dvd_two_pow_sub_one_eq_seven D ctx h3 h55 h59 h63
      hK hnodd hKshape hr hrd)

theorem card_barImage_eq_card_bar {D : Data G} {K : Subgroup G} (hK : K ∈ calC D.M) :
    Nat.card (barImage D.M K) = Nat.card (Bar2 K) := by
  obtain ⟨e⟩ := s13_bar_equiv hK
  exact (Nat.card_congr e.toEquiv).symm

theorem p_eq_three_of_isL2_three {D : Data G} {K : Subgroup G} {p : ℕ}
    (hK : K ∈ calC D.M) (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hL2 : IsL2 (Bar2 K) 3) (hdvd : p ∣ Nat.card (barImage D.M K)) : p = 3 := by
  have hcard : Nat.card (barImage D.M K) = 504 := by
    rw [card_barImage_eq_card_bar hK, card_of_isL2 hL2]
    norm_num
  rw [hcard] at hdvd
  have hdvd' : p ∣ 2 ^ 3 * (3 ^ 2 * 7) := by
    simpa [show (504 : ℕ) = 2 ^ 3 * (3 ^ 2 * 7) by norm_num] using hdvd
  rcases hp.dvd_mul.mp hdvd' with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h)) hp2
  rcases hp.dvd_mul.mp h with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h) hp7

theorem p_eq_five_or_thirteen_of_isSz_three
    {D : Data G} {K : Subgroup G} {p : ℕ}
    (hK : K ∈ calC D.M) (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hSz : IsSz (Bar2 K) 3) (hdvd : p ∣ Nat.card (barImage D.M K)) :
    p = 5 ∨ p = 13 := by
  have hcard : Nat.card (Bar2 K) = 29120 := by
    have h := CFSG.GH74.card_of_lieModel_twistedB2 (G := Bar2 K) hSz
    rw [h, CFSG.Open.ordSuzuki]
    norm_num
  have hcard' : Nat.card (barImage D.M K) = 29120 := by
    rw [card_barImage_eq_card_bar hK, hcard]
  rw [hcard'] at hdvd
  have hdvd' : p ∣ 2 ^ 6 * (5 * (7 * 13)) := by
    simpa [show (29120 : ℕ) = 2 ^ 6 * (5 * (7 * 13)) by norm_num] using hdvd
  rcases hp.dvd_mul.mp hdvd' with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h)) hp2
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h)
  rcases hp.dvd_mul.mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h) hp7
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h)


theorem opp_eq_self_of_calC {M L : Subgroup G} {p : ℕ} (hL : L ∈ calC M)
    (hsimple : IsSimpleGroup (Bar2 L)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card (Bar2 L)) : Opp p L = L := by
  have : Fact p.Prime := ⟨hp⟩
  let J : Subgroup G := Opp p L
  have hJL : J ≤ L := by
    change Opp p L ≤ L
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact (Subgroup.closure_le L).mpr fun _ hx => hx.1
  have hnorm : L ≤ normalizer (J : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p m L
    have hL' : CFSG.RankThree.PartOne.conjBy m L = L := by
      unfold CFSG.RankThree.PartOne.conjBy
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
    rw [hL'] at h
    simpa [J, Opp, CFSG.RankThree.PartOne.conjBy] using h.symm
  let N : Subgroup ↥L := J.subgroupOf L
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).2 hnorm
  let : N.Normal := hNnormal
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  let π : ↥L →* Bar2 L := QuotientGroup.mk' Q
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Subgroup.map_injective L.subtype_injective (by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hL.2.1])
  have hdvdL : p ∣ Nat.card ↥L :=
    hdvd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' p hdvdL
  have hgN : g ∈ N := by
    change g ∈ J.subgroupOf L
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨g.2, 1, by rw [Subgroup.orderOf_coe, hgord]; norm_num⟩
  have hNQ : N ⊔ Q = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
    · exfalso
      have hπg : π g = 1 := by
        have hmem : π g ∈ N.map π := Subgroup.mem_map_of_mem π hgN
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hgQ : g ∈ Q :=
        (QuotientGroup.eq_one_iff (N := Q) g).1 (by simpa [π] using hπg)
      obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
      have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hpk : p ∣ 2 ^ k := by
        have := orderOf_dvd_of_pow_eq_one hk'
        rwa [hgord] at this
      have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow hpk
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
    · apply top_le_iff.1
      intro y _
      have hmem : π y ∈ N.map π := by rw [htop]; exact Subgroup.mem_top (π y)
      obtain ⟨n, hn, hnπ⟩ := hmem
      have hndiff : n⁻¹ * y ∈ Q := by
        have hπ1 : π (n⁻¹ * y) = 1 := by rw [map_mul, map_inv, hnπ, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := Q) (n⁻¹ * y)).1 (by simpa [π] using hπ1)
      have hy : y = n * (n⁻¹ * y) := by group
      rw [hy]
      exact Subgroup.mul_mem_sup hn hndiff
  have hR : IsPGroup 2 (↥L ⧸ N) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ N ⊔ Q := hNQ ▸ Subgroup.mem_top z
    obtain ⟨n, hn, q, hq, hz'⟩ := Subgroup.mem_sup_of_normal_left.1 hz
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : ((n * q : ↥L) : ↥L ⧸ N) = (q : ↥L ⧸ N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
    rw [← hz']
    show (((n * q : ↥L) : ↥L ⧸ N)) ^ 2 ^ k = 1
    rw [h1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have : Group.IsNilpotent (↥L ⧸ N) := hR.isNilpotent
  have hle : (⊤ : Subgroup ↥L) ≤ N :=
    Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperf
  have hJtop : N = ⊤ := top_le_iff.1 hle
  have hLJ : L ≤ J := by
    intro y hy
    have hmemN : (⟨y, hy⟩ : ↥L) ∈ N := by rw [hJtop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf (H := J) (K := L)).1 (by simpa [N] using hmemN)
  show J = L
  exact le_antisymm hJL hLJ


omit [Finite G] in
private theorem eq_of_pair_eq_conjSetOf {M K₁ K₂ : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (K₁ : Set G))
    (h : ({K₁, K₂} : Set (Subgroup G)) =
      {N | ∃ m ∈ M, N = K₁.map (MulAut.conj m).toMonoidHom}) : K₂ = K₁ := by
  have hset : ({K₁, K₂} : Set (Subgroup G)) = {K₁} := by
    rw [h]
    ext N
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnorm hm))
    · intro hN
      exact ⟨1, M.one_mem, by
        rw [Set.mem_singleton_iff.mp hN]
        ext x
        simp⟩
  have hmem : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := by simp
  rw [hset] at hmem
  exact Set.mem_singleton_iff.mp hmem

theorem false_of_two_thin_components_17_61
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13)
    (h55 : R17_55At D V₀ V) (h8100 : F08.R8100R D)
    {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ∈ calC (Lp D p)) (hK₂ : K₂ ∈ calC (Lp D p))
    (hne : K₁ ≠ K₂) (hK₁neL : K₁ ≠ L) (hK₂neL : K₂ ≠ L)
    (hshape₁ : IsL2 (Bar2 K₁) 3 ∨ IsSz (Bar2 K₁) 3)
    (hshape₂ : IsL2 (Bar2 K₂) 3 ∨ IsSz (Bar2 K₂) 3) : False := by
  classical
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have hK₁calM : K₁ ∈ calC D.M := calC_of_calC_Lp D hK₁
  have hK₂calM : K₂ ∈ calC D.M := calC_of_calC_Lp D hK₂
  have hK₁M : K₁ ≤ D.M := s13_le_of_mem_calC hK₁calM
  have hK₂M : K₂ ≤ D.M := s13_le_of_mem_calC hK₂calM
  have hK₁n : (K₁.subgroupOf D.M).Normal := (ctx.hyp54.2 K₁ hK₁calM).1
  have hK₂n : (K₂.subgroupOf D.M).Normal := (ctx.hyp54.2 K₂ hK₂calM).1
  have hMnorm₁ : D.M ≤ Subgroup.normalizer (K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁M).mp hK₁n
  have hMnorm₂ : D.M ≤ Subgroup.normalizer (K₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂M).mp hK₂n
  have h7dvd₁ : 7 ∣ Nat.card (Bar2 K₁) := by
    rcases hshape₁ with hL2 | hSz
    · rw [card_of_isL2 hL2]; norm_num
    · rw [CFSG.GH74.card_of_lieModel_twistedB2 hSz, CFSG.Open.ordSuzuki]; norm_num
  obtain ⟨A, hAK₁, hAcard⟩ :=
    s13_exists_subgroup_of_dvd_card_bar (by norm_num : Nat.Prime 7) h7dvd₁
  have hAM : A ≤ D.M := hAK₁.trans hK₁M
  let X : Subgroup G := K₁ ⊔ K₂
  have hXset : (X : Set G) = (K₁ : Set G) * (K₂ : Set G) := by
    show ((K₁ ⊔ K₂ : Subgroup G) : Set G) = (K₁ : Set G) * (K₂ : Set G)
    exact Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂
      (calC_le_normalizer_of_ne hK₂calM hK₁calM hne.symm)
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : K₁.map (MulAut.conj m).toMonoidHom = K₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnorm₁ hm)
    have h2 : K₂.map (MulAut.conj m).toMonoidHom = K₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnorm₂ hm)
    show (K₁ ⊔ K₂).map (MulAut.conj m).toMonoidHom = K₁ ⊔ K₂
    rw [Subgroup.map_sup, h1, h2]
  let Lf : Fin 2 → Subgroup G := ![K₁, K₂]
  let nf : Fin 2 → ℕ := ![3, 3]
  have hH : F08.Hyp8100 D Lf nf 7 p A X := by
    refine ⟨?_, ?_, ?_, by norm_num, ?_, ctx.hyp54.1, hAcard, Or.inl hAK₁, hXset, hMX⟩
    · intro i
      fin_cases i
      · simpa [Lf] using hK₁calM
      · simpa [Lf] using hK₂calM
    · simpa [Lf] using hne
    · intro i
      fin_cases i
      · change IsL2 (Bar2 K₁) 3 ∨ IsSz (Bar2 K₁) 3
        exact hshape₁
      · change IsL2 (Bar2 K₂) 3 ∨ IsSz (Bar2 K₂) 3
        exact hshape₂
    · norm_num [nf]
  have h55K₁ : conjSetOf (⊤ : Subgroup G) A ∩ {Y : Subgroup G | Y ≤ D.M} ≠
      conjSetOf D.M A :=
    h55 K₁ hK₁M hK₁n 3 hshape₁ 3 (by norm_num) dvd_rfl 7 (by norm_num)
      (by norm_num : (7 : ℕ) ∣ 2 ^ 3 - 1) A hAK₁ hAcard
  have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent ctx.memC
  have hK₁comp : CFSG.IsComponent (barImage D.M K₁) := s13_barImage_isComponent hK₁calM
  have hK₂comp : CFSG.IsComponent (barImage D.M K₂) := s13_barImage_isComponent hK₂calM
  rcases h8100 Lf nf 7 p A X hH with hstr | h2 | h3 | h4
  ·
    exact h55K₁ (conjSetOf_eq_of_isStronglyPEmbedded hstr hAM hAcard)
  ·
    have hXopp : X = Opp 7 D.M := by
      simpa using (h2.2.2 (by norm_num)).1
    have hL3dvd : 7 ∣ Nat.card (Bar2 L) := by
      rw [card_bar_of_isL3 ctx.shapeL]; norm_num
    have hLsimple : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ctx.shapeL
    have hL7 : Opp 7 L = L :=
      opp_eq_self_of_calC ctx.memC hLsimple (by norm_num) (by norm_num) hL3dvd
    have hLleOpp : L ≤ Opp 7 D.M := by
      rw [← hL7]
      unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      exact Subgroup.closure_mono fun x hx =>
        ⟨s13_le_of_mem_calC ctx.memC hx.1, hx.2⟩
    have hLleX : L ≤ X := by
      rw [hXopp]
      exact hLleOpp
    have hK₁ne : barImage D.M K₁ ≠ barImage D.M L := fun h =>
      hK₁neL (barImage_injOn_calC hK₁calM ctx.memC h)
    have hK₂ne : barImage D.M K₂ ≠ barImage D.M L := fun h =>
      hK₂neL (barImage_injOn_calC hK₂calM ctx.memC h)
    have hK₁K₂ne : barImage D.M K₁ ≠ barImage D.M K₂ := fun h =>
      hne (barImage_injOn_calC hK₁calM hK₂calM h)
    have hinter : barImage D.M L ⊓ (barImage D.M K₁ ⊔ barImage D.M K₂) = ⊥ := by
      have h := s13_inf_iSup_eq_bot hns hLcomp {barImage D.M K₁, barImage D.M K₂}
        (by
          intro J hJ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
          rcases hJ with rfl | rfl
          · exact ⟨hK₁comp, hK₁ne⟩
          · exact ⟨hK₂comp, hK₂ne⟩)
      have hsup : (⨆ J ∈ ({barImage D.M K₁, barImage D.M K₂} :
          Finset (Subgroup (Bar2 D.M))), J) =
          barImage D.M K₁ ⊔ barImage D.M K₂ := by
        apply le_antisymm
        · refine iSup_le fun J => ?_
          refine iSup_le fun hJ => ?_
          rcases (by simpa using hJ) with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · exact sup_le (le_iSup₂_of_le _ (by simp) le_rfl)
            (le_iSup₂_of_le _ (by simp) le_rfl)
      rwa [hsup] at h
    have hLX : barImage D.M L ≤ barImage D.M K₁ ⊔ barImage D.M K₂ := by
      rw [← s13_barImage_sup hK₁M hK₂M]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map_of_mem _ (hLleX hx)
    have hbot : barImage D.M L = ⊥ := le_bot_iff.mp (hinter ▸ le_inf le_rfl hLX)
    have hcardL : Nat.card (barImage D.M L) = 20160 := by
      rw [card_barImage_eq_card_bar ctx.memC, card_bar_of_isL3 ctx.shapeL]
      norm_num
    rw [hbot] at hcardL
    norm_num at hcardL
  ·
    have h := h3.1
    change ({Lf 0, Lf 1} : Set (Subgroup G)) = {N | ∃ m ∈ D.M,
      N = (Lf 0).map (MulAut.conj m).toMonoidHom} at h
    simp only [Lf, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact hne (eq_of_pair_eq_conjSetOf hMnorm₁ h).symm
  ·
    have h := h4.1
    change ({Lf 0, Lf 1} : Set (Subgroup G)) = {N | ∃ m ∈ D.M,
      N = (Lf 0).map (MulAut.conj m).toMonoidHom} at h
    simp only [Lf, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact hne (eq_of_pair_eq_conjSetOf hMnorm₁ h).symm



end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
