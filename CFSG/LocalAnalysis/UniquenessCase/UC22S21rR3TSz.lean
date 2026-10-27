module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Blueprint Subgroup
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_two_mul_lt_of_dvd {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : r.Prime)
    (hrq : r ∣ 2 ^ q - 1) : 2 * q < r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two (hq.odd_of_ne_two hq2) hrq
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h0
    have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).1 h0
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
  have hpow : (2 : ZMod r) ^ q = 1 := by
    have hsub : ((2 ^ q - 1 : ℕ) : ZMod r) = (2 : ZMod r) ^ q - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one, Nat.cast_pow]
      norm_num
    have hzero : ((2 ^ q - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrq
    exact sub_eq_zero.1 (by rw [← hsub, hzero])
  have hdq : orderOf (2 : ZMod r) ∣ q := orderOf_dvd_iff_pow_eq_one.2 hpow
  have hne1 : orderOf (2 : ZMod r) ≠ 1 := by
    intro h1
    have h21 : (2 : ZMod r) = 1 := by simpa using orderOf_eq_one_iff.1 h1
    have hsub : (2 : ZMod r) - 1 = 0 := by rw [h21]; ring
    have hcast : ((2 - 1 : ℕ) : ZMod r) = (2 : ZMod r) - 1 := by
      rw [Nat.cast_sub (by norm_num : (1 : ℕ) ≤ 2), Nat.cast_one]
      norm_num
    have h0 : ((2 - 1 : ℕ) : ZMod r) = 0 := by rw [hcast]; exact hsub
    rw [show 2 - 1 = 1 by norm_num] at h0
    exact hr.ne_one (Nat.dvd_one.1 ((ZMod.natCast_eq_zero_iff 1 r).1 h0))
  have hord : orderOf (2 : ZMod r) = q := by
    rcases (Nat.dvd_prime hq).1 hdq with h | h
    · exact absurd h hne1
    · exact h
  have hqr : q ∣ r - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one h2ne
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have h2 : 2 ∣ r - 1 := ⟨k, by omega⟩
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
  have h2q : 2 * q ∣ r - 1 := hcop.mul_dvd_of_dvd_of_dvd h2 hqr
  have hpos : 0 < r - 1 := by have := hr.two_le; omega
  have := Nat.le_of_dvd hpos h2q
  omega

private theorem uc22r3t_sz_aut_congr_not_inner {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {α : MulAut X} (hα : α ∉ (MulAut.conj : X →* MulAut X).range) :
    MulAut.congr e α ∉ (MulAut.conj : Y →* MulAut Y).range := by
  rintro ⟨y, hy⟩
  apply hα
  refine ⟨e.symm y, ?_⟩
  have h1 : MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  calc MulAut.conj (e.symm y) = (MulAut.congr e).symm (MulAut.conj y) := by
        rw [← h1, MulEquiv.symm_apply_apply]
    _ = (MulAut.congr e).symm (MulAut.congr e α) := by rw [hy]
    _ = α := MulEquiv.symm_apply_apply (MulAut.congr e) α

private theorem uc22r3t_szFieldAut_conj_fixed {a : ℕ} {K : Type} [Field K] {σ : RingAut K}
    {α : MulAut (suzukiGroup a K)} {h y : suzukiGroup a K}
    (hconj : MulAut.conj h * α * (MulAut.conj h)⁻¹ = szFieldAut a K σ) (hy : α y = y) :
    szFieldAut a K σ (h * y * h⁻¹) = h * y * h⁻¹ := by
  have h1 : (MulAut.conj h)⁻¹ (h * y * h⁻¹) = y := by
    rw [show (MulAut.conj h)⁻¹ = MulAut.conj h⁻¹ from
      (map_inv (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)) h).symm]
    rw [MulAut.conj_apply]
    group
  have hfix' := congrArg (fun f : MulAut (suzukiGroup a K) => f (h * y * h⁻¹)) hconj
  simp only [MulAut.mul_apply] at hfix'
  rw [h1, hy] at hfix'
  simp only [MulAut.conj_apply] at hfix'
  exact hfix'.symm

private theorem uc22r3t_sz_dvd_twenty {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] {q : ℕ} (hqeq : q = 2 * a + 1)
    (hKcard : Nat.card K = 2 ^ q) (hq : q.Prime) (hq2 : q ≠ 2)
    {α : MulAut (suzukiGroup a K)} (hαo : orderOf α = q)
    (hα : α ∉ (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range)
    {r : ℕ} (hr : r.Prime) {y : suzukiGroup a K} (hyo : orderOf y = r) (hfix : α y = y) :
    r ∣ 20 := by
  obtain ⟨σ, h, b, k, hk, hkf, -, hb, hkc, hconj, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K
      (by rw [hKcard, hqeq]) q hq hq2 α hαo hα
  letI : Field k := hk
  letI : Finite k := hkf
  set y' : suzukiGroup a K := h * y * h⁻¹ with hy'def
  have hy'fix : szFieldAut a K σ y' = y' := uc22r3t_szFieldAut_conj_fixed hconj hfix
  have hy'F : y' ∈ (szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _) := hy'fix
  have hordy' : orderOf y' = r := by
    rw [hy'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj h), hyo]
  have hordF : orderOf (⟨y', hy'F⟩ :
      ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _))) = r := by
    rw [← Subgroup.orderOf_coe (⟨y', hy'F⟩ :
      ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)))]
    exact hordy'
  have hdvd : r ∣ Nat.card (suzukiGroup b k) := by
    rw [← Nat.card_congr φ.toEquiv]
    have h := orderOf_dvd_natCard
      (⟨y', hy'F⟩ : ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id _)))
    rwa [hordF] at h
  have hb0 : b = 0 := by
    have h1 : (2 * b + 1) * q = 1 * q := by rw [hb, hqeq, one_mul]
    have h2 := Nat.mul_right_cancel hq.pos h1
    omega
  subst hb0
  have h20 : Nat.card (suzukiGroup 0 k) = 20 := by
    rw [CFSG.LieType.Ree.suzuki_order (by simpa using hkc)]
    norm_num
  rwa [h20] at hdvd

theorem uc22r3t_sz_fixed_false {X : Type} [Group X] [Finite X]
    {q : ℕ} (hX : IsSz X q) (hq : q.Prime) {α : MulAut X} (hαq : α ^ q = 1)
    (hα : α ∉ (MulAut.conj : X →* MulAut X).range) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr5 : r ≠ 5) {x : X} (hxo : orderOf x = r) (hfix : α x = x) : False := by
  obtain ⟨-, a, ha, K, hK, hKf, hqeq, hKcard, ⟨e⟩⟩ :=
    (CFSG.Blueprint.LieModel.suzukiModel hX).2
  letI : Field K := hK
  letI : Finite K := hKf
  have hq2 : q ≠ 2 := by omega
  have hαo : orderOf α = q := by
    have hd : orderOf α ∣ q := orderOf_dvd_iff_pow_eq_one.2 hαq
    rcases (Nat.dvd_prime hq).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) fun h1 => hα ⟨1, by rw [h1, map_one]⟩
    · exact h
  have hα'o : orderOf (MulAut.congr e α) = q := by rw [MulEquiv.orderOf_eq, hαo]
  have hα'x : MulAut.congr e α (e x) = e x := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfix]
  have hdvd : r ∣ 20 :=
    uc22r3t_sz_dvd_twenty ha hqeq hKcard hq hq2 hα'o
      (uc22r3t_sz_aut_congr_not_inner e hα) hr (by rw [MulEquiv.orderOf_eq e, hxo]) hα'x
  have h2 : r = 2 ∨ r = 5 := by
    have hd : r ∣ 2 ^ 2 * 5 := by rw [show 2 ^ 2 * 5 = 20 by norm_num]; exact hdvd
    rcases hr.dvd_mul.1 hd with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h'))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h')
  rcases h2 with rfl | rfl
  · exact hr2 rfl
  · exact hr5 rfl

theorem uc22r3t_theta_eq_one_of_mem_ne {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : L ≠ K) {k : G} (hk : k ∈ K)
    (hkn : k ∈ normalizer (L : Set G)) : inducedQuotInfAut L k hkn = 1 := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hKM : K ≤ M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hbar : ∀ a ∈ barImage M L, ∀ c ∈ barImage M K, a * c = c * a :=
    uc22p22l_barImage_commute hL hK hne
  have hL' : ∀ l : ↥L, ⁅k, (l : G)⁆ ∈ L := by
    intro l
    have h1 : k * (l : G) * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hkn l).1 l.2
    simpa [commutatorElement_def] using L.mul_mem h1 (L.inv_mem l.2)
  refine MulEquiv.ext fun z => ?_
  obtain ⟨l, rfl⟩ := piBarInf_surjective L z
  rw [inducedQuotInfAut_piBarInf, MulAut.one_apply]
  have hmem : (⟨⁅k, (l : G)⁆, hL' l⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    have hM : ⁅k, (l : G)⁆ ∈ pCoreOf 2 M := by
      have haL : uc22p21cPi M ⟨(l : G), hLM l.2⟩ ∈ barImage M L :=
        (uc22p21c_mem_barImage (P := L)).2 ⟨⟨(l : G), hLM l.2⟩, l.2, rfl⟩
      have haK : uc22p21cPi M ⟨k, hKM hk⟩ ∈ barImage M K :=
        (uc22p21c_mem_barImage (P := K)).2 ⟨⟨k, hKM hk⟩, hk, rfl⟩
      exact uc22p22u_commutator_mem_pCoreOf (X := M) (hKM hk) (hLM l.2)
        (hbar _ haL _ haK).symm
    have hle := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM (mem_inf.2 ⟨hL' l, hM⟩)
    obtain ⟨w, hw, hwG⟩ := Subgroup.mem_map.1 hle
    have hw' : w = (⟨⁅k, (l : G)⁆, hL' l⟩ : ↥L) := Subtype.ext hwG
    rwa [hw'] at hw
  have h1 : (⟨k * (l : G) * k⁻¹, (Subgroup.mem_normalizer_iff.1 hkn l).1 l.2⟩ : ↥L) =
      (⟨⁅k, (l : G)⁆, hL' l⟩ : ↥L) * l := by
    ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  have hzero : piBarInf L (⟨⁅k, (l : G)⁆, hL' l⟩ : ↥L) = 1 := by
    rw [← MonoidHom.mem_ker, piBarInf_ker hL.2.2]
    exact CFSG.pCore_le_solvableRadical 2 ↥L hmem
  rw [h1, map_mul, hzero, one_mul]

theorem uc22r3t_theta_eq_conj {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hln : l ∈ normalizer (L : Set G)) :
    inducedQuotInfAut L l hln = MulAut.conj (piBarInf L ⟨l, hl⟩) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨w, rfl⟩ := piBarInf_surjective L z
  rw [inducedQuotInfAut_piBarInf, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem uc22r3t_center_xbar_eq_bot {M L : Subgroup G} {q : ℕ} (hL : L ∈ calC M)
    (hSz : IsSz (Bar2 L) q) : center (BarInf L ⧸ center (BarInf L)) = ⊥ := by
  have hc : center (Bar2 L) = ⊥ := center_eq_bot_of_isSz hL.2.2 hSz
  have h1 := Subgroup.map_center_eq (quotCenterEquivBar2 hL.2.2 hc)
  rw [hc] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (quotCenterEquivBar2 hL.2.2 hc).injective).1 h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
