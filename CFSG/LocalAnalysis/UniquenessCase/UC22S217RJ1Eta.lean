module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsSixInf
import CFSG.LocalAnalysis.UniquenessCase.UC22S217RJ1N
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Walter.J1Props.Extra
import CFSG.Mathlib.Arithmetic.TwoPowSubOneSeven
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217rj_mem_zpowers_of_commute {X : Type} [Group X] [Finite X] (hX : IsJ1 X)
    {x y : X} (hy : orderOf y = 7) (hxy : Commute x y) : x ∈ zpowers y := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcX : Nat.card X = 175560 := (kJ1_holds X hX).1
  obtain ⟨e⟩ := hX
  let f : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hcW : Nat.card CFSG.Open.walterJ1 = 175560 := by
    rw [← Nat.card_congr f.toEquiv, hcX]
  have hcy : Nat.card (zpowers (f y)) = 7 := by
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, hy]
  obtain ⟨P, hyP⟩ := (IsPGroup.of_card (n := 1) (by rw [hcy, pow_one]) :
    IsPGroup 7 (zpowers (f y))).exists_le_sylow
  have hPeq : zpowers (f y) = (P : Subgroup CFSG.Open.walterJ1) := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd : 7 ^ k ∣ 175560 := by
      rw [← hk, ← hcW]
      exact Subgroup.card_subgroup_dvd_card _
    have hk2 : k < 2 := by
      by_contra h
      exact uc22s217v_not_sq_dvd (by norm_num) (by norm_num)
        ((pow_dvd_pow 7 (by omega)).trans hdvd)
    have hle : 7 ≤ 7 ^ k :=
      calc 7 = Nat.card (zpowers (f y)) := hcy.symm
        _ ≤ Nat.card P := Subgroup.card_le_of_le hyP
        _ = 7 ^ k := hk
    refine Subgroup.eq_of_le_of_card_ge hyP ?_
    rw [hk, hcy]
    interval_cases k <;> simp_all
  have hmem : f x ∈ centralizer ((P : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1) := by
    rw [← hPeq, CFSG.Walter.J1Props.centralizer_zpowers_eq,
      Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy.eq]
  rw [CFSG.Walter.J1Props.centralizer_sylow_eq (Or.inl rfl) P, ← hPeq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  exact Subgroup.mem_zpowers_iff.2 ⟨k, f.injective (by rw [map_zpow, hk])⟩

theorem uc22s217rj_eq_seven {M L : Subgroup G} (hL : L ∈ calC M) (hJ1 : IsJ1 (Bar2 L))
    {b b₇ : G} (hb : b ∈ normalizer (L : Set G)) (hb₇ : b₇ ∈ normalizer (L : Set G))
    (hcomm : b * b₇ = b₇ * b) {r : ℕ} (hr : r.Prime) (hbr : orderOf b = r)
    (hb₇o : orderOf b₇ = 7) (hnb : ¬ CentralizesBar b L) (hnb₇ : ¬ CentralizesBar b₇ L) :
    r = 7 := by
  obtain ⟨-, hsimple, hinn⟩ := kJ1_holds (Bar2 L) hJ1
  haveI := hsimple
  have hZc : center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  have hinj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hac : a ∈ center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz : a * z * a⁻¹ = z := by
        simpa [MulAut.conj_apply] using DFunLike.congr_fun ha z
      calc z * a = a * z * a⁻¹ * a := by rw [hz]
        _ = a * z := by group
    rw [hZc] at hac
    exact Subgroup.mem_bot.1 hac
  have hne : ∀ m : ↥(normalizer (L : Set G)), ¬ CentralizesBar (m : G) L →
      UC6S846.rhoL L m ≠ 1 := by
    intro m hm h1
    refine hm ⟨m.2, fun l hl => (UC6S846.rhoL_fix_iff L m ⟨l, hl⟩).1 ?_⟩
    rw [h1, MulAut.one_apply]
  have hpow : ∀ (m : ↥(normalizer (L : Set G))) (z : Bar2 L) (k : ℕ),
      UC6S846.rhoL L m = MulAut.conj z → (m : G) ^ k = 1 → z ^ k = 1 := by
    intro m z k hz hk
    have hmk : m ^ k = 1 := Subtype.ext (by simpa using hk)
    apply hinj
    rw [map_pow, ← hz, ← map_pow, hmk, map_one, map_one]
  let m : ↥(normalizer (L : Set G)) := ⟨b, hb⟩
  let m₇ : ↥(normalizer (L : Set G)) := ⟨b₇, hb₇⟩
  obtain ⟨x, hx⟩ := hinn (UC6S846.rhoL L m)
  obtain ⟨y, hy⟩ := hinn (UC6S846.rhoL L m₇)
  have hx1 : x ≠ 1 := fun h => hne m hnb (by rw [hx, h, map_one])
  have hy1 : y ≠ 1 := fun h => hne m₇ hnb₇ (by rw [hy, h, map_one])
  have hxr : x ^ r = 1 := hpow m x r hx (by rw [← hbr]; exact pow_orderOf_eq_one b)
  have hy7 : y ^ 7 = 1 := hpow m₇ y 7 hy (by rw [← hb₇o]; exact pow_orderOf_eq_one b₇)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hxy : Commute x y := by
    show x * y = y * x
    apply hinj
    rw [map_mul, map_mul, ← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hcomm)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (uc22s217rj_mem_zpowers_of_commute hJ1 (orderOf_eq_prime hy7 hy1) hxy)
  have hx7 : (y ^ k) ^ 7 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy7, one_zpow]
  rw [← orderOf_eq_prime hxr hx1, orderOf_eq_prime hx7 hx1]

theorem uc22s217rj_n_eq_three (D : Data G) (Ch : Choice2011 G) (h5 : S21_5 D Ch)
    (h6 : S21_6Inf D Ch) (h8107 : F08.R8107 D) (h920 : PartOne.Section9.R920J1 D)
    (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnN : ¬ (L.subgroupOf D.M).Normal) (hJ1 : IsJ1 (Bar2 L)) : c.n = 3 := by
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hF : ∀ b ∈ c.B0, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf b = r → ¬ CentralizesBar b L := by
    intro b hb r hr hr2 hbr hcb
    refine uc22s217rj_false_of_commutator_le D Ch h8107 h920 hH c hL hnN hJ1 hb hr hr2 hbr ?_
    rw [Subgroup.commutator_le]
    intro g hg l hl
    rw [commutatorElement_def]
    exact (uc22p21d_centralizesBar_of_mem_zpowers hcb hg).2 l hl
  have hspor : ∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s := by
    haveI := (kJ1_holds _ hJ1).2.1
    obtain ⟨f⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (uc22p21k_center_eq_bot hL.2.2)
    obtain ⟨e⟩ := hJ1
    exact ⟨.J1, ⟨f.trans e⟩⟩
  rcases (h6 hH c₀ L hL hspor).2 with h3 | h7
  · exfalso
    obtain ⟨b, hb, r, hr, hr2, hr3, hbr⟩ := Ctx21.exists_mem_B0_orderOf_ne_three c hn3
    have hb3 : b ∈ CFSG.Quasithin.opResidual 3 c.B0 :=
      CFSG.Quasithin.mem_opResidual_of_coprime hb (by
        rw [hbr]
        exact (Nat.coprime_primes hr Nat.prime_three).2 hr3)
    exact uc22s217rj_false_of_commutator_le D Ch h8107 h920 hH c hL hnN hJ1 hb hr hr2 hbr
      ((Subgroup.commutator_mono (zpowers_le.2 hb3) le_rfl).trans h3)
  · obtain ⟨b₇, hb₇, hb₇o⟩ := uc22p22i_exists_elt_of_mem_piSet h7
    have hall : ∀ p : ℕ, p.Prime → p ∣ 2 ^ c.n - 1 → p = 7 := by
      intro p hp hpd
      obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet (B := c.B0) (r := p) (by
        rw [c.hpi]
        exact ⟨hp, hpd⟩)
      have hp2 : p ≠ 2 := by
        rintro rfl
        have h1 : 2 ∣ 2 ^ c.n := dvd_pow_self 2 (by omega)
        have h2 : 1 ≤ 2 ^ c.n := Nat.one_le_two_pow
        omega
      have hcomm : b * b₇ = b₇ * b :=
        congrArg Subtype.val (c.hB0.2.1.is_comm.comm (⟨b, hb⟩ : ↥c.B0) ⟨b₇, hb₇⟩)
      exact uc22s217rj_eq_seven hL hJ1 (h5 hH c₀ L hL hb) (h5 hH c₀ L hL hb₇) hcomm hp hbo
        hb₇o (hF b hb p hp hp2 hbo) (hF b₇ hb₇ 7 (by norm_num) (by norm_num) hb₇o)
    have hodd : Odd c.n := by
      rcases Nat.even_or_odd c.n with ⟨k, hk⟩ | h
      · have h3 : 3 ∣ 2 ^ c.n - 1 := by
          have h4 : 3 ∣ 4 ^ k - 1 := Nat.sub_one_dvd_pow_sub_one 4 k
          rwa [hk, ← two_mul, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact absurd (hall 3 Nat.prime_three h3) (by norm_num)
      · exact h
    exact CFSG.eq_three_of_forall_prime_dvd_two_pow_sub_one c.n hodd (by omega) hall

end CFSG.LocalAnalysis.UniquenessCase.UC22
