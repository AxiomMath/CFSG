module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralSylow
import CFSG.LocalAnalysis.StandardType.GGTriD4SchurHolds
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggWeylIrred_of_triD4Coords {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) {Ω : Subgroup G} (P : ℤ → ℤ → G) (hPΩ : ∀ i j, P i j ∈ Ω)
    (hΩP : ∀ y ∈ Ω, ∃ i j, P i j = y)
    (hmul : ∀ i j i' j', P i j * P i' j' = P (i + i') (j + j'))
    (hone : ∀ i j, P i j = 1 ↔ (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    {no nm : G} (hno : ∀ i j, no * P i j * no⁻¹ = P (j - i) j)
    (hnm : ∀ i j, nm * P i j * nm⁻¹ = P i (3 * i - j)) : GGWeylIrred Ω := by
  have hinvp : ∀ c : ℤ, ¬ (p : ℤ) ∣ c → ∃ d : ℤ, (p : ℤ) ∣ c * d - 1 := by
    intro c hc
    have hcop : IsCoprime (p : ℤ) c := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
      have : ¬ p ∣ c.natAbs := fun hd => hc (Int.natCast_dvd.mpr hd)
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨v, ⟨-u, by linear_combination huv⟩⟩
  have hP00 : P 0 0 = 1 := (hone 0 0).2 ⟨dvd_zero _, dvd_zero _⟩
  have hinv : ∀ i j, (P i j)⁻¹ = P (-i) (-j) := by
    intro i j
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, hmul, neg_add_cancel, neg_add_cancel, hP00]
  have hres : ∀ i j i' j', (p : ℤ) ∣ i - i' → (p : ℤ) ∣ j - j' → P i j = P i' j' := by
    intro i j i' j' hi hj
    have h1 : P i j * (P i' j')⁻¹ = 1 := by
      rw [hinv, hmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
      exact (hone _ _).2 ⟨hi, hj⟩
    exact mul_inv_eq_one.mp h1
  have hzpow : ∀ i j (m : ℤ), P i j ^ m = P (m * i) (m * j) := by
    intro i j m
    refine Int.induction_on m ?_ ?_ ?_
    · rw [zpow_zero, zero_mul, zero_mul, hP00]
    · intro k ih
      rw [zpow_add_one, ih, hmul]
      congr 1 <;> ring
    · intro k ih
      rw [zpow_sub_one, ih, hinv, hmul]
      congr 1 <;> ring
  have hnoN : no ∈ Subgroup.normalizer (Ω : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, j, rfl⟩ := hΩP h hh
      rw [hno]
      exact hPΩ _ _
    · intro hh
      obtain ⟨i, j, hij⟩ := hΩP _ hh
      have h2 : no * P (j - i) j * no⁻¹ = P i j := by
        rw [hno]
        congr 1
        ring
      have h3 : MulAut.conj no h = MulAut.conj no (P (j - i) j) := by
        rw [MulAut.conj_apply, MulAut.conj_apply, ← hij, h2]
      rw [(MulAut.conj no).injective h3]
      exact hPΩ _ _
  have hnmN : nm ∈ Subgroup.normalizer (Ω : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, j, rfl⟩ := hΩP h hh
      rw [hnm]
      exact hPΩ _ _
    · intro hh
      obtain ⟨i, j, hij⟩ := hΩP _ hh
      have h2 : nm * P i (3 * i - j) * nm⁻¹ = P i j := by
        rw [hnm]
        congr 1
        ring
      have h3 : MulAut.conj nm h = MulAut.conj nm (P i (3 * i - j)) := by
        rw [MulAut.conj_apply, MulAut.conj_apply, ← hij, h2]
      rw [(MulAut.conj nm).injective h3]
      exact hPΩ _ _
  intro E hEΩ hEinv
  rcases Subgroup.bot_or_exists_ne_one E with hbot | ⟨x, hxE, hx1⟩
  · exact Or.inl hbot
  right
  refine le_antisymm hEΩ ?_
  obtain ⟨i, j, rfl⟩ := hΩP x (hEΩ hxE)
  have hij : ¬ ((p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) := fun h => hx1 ((hone i j).2 h)
  have hcm : ∀ g ∈ Subgroup.normalizer (Ω : Set G), ∀ y ∈ E, g * y * g⁻¹ * y⁻¹ ∈ E :=
    fun g hg y hy => E.mul_mem (hEinv g hg y hy) (E.inv_mem hy)
  have hu : P (j - 2 * i) 0 ∈ E := by
    have h := hcm no hnoN _ hxE
    rwa [hno, hinv, hmul, show j - i + -i = j - 2 * i by ring, show j + -j = 0 by ring] at h
  have hv : P 0 (3 * i - 2 * j) ∈ E := by
    have h := hcm nm hnmN _ hxE
    rwa [hnm, hinv, hmul, show i + -i = 0 by ring,
      show 3 * i - j + -j = 3 * i - 2 * j by ring] at h
  have h3 : ¬ (p : ℤ) ∣ 3 := by
    intro h
    have h' : p ∣ 3 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  have hstep1 : P 1 0 ∈ E → P 0 1 ∈ E := by
    intro h10
    have h := hcm nm hnmN _ h10
    rw [hnm, hinv, hmul, show (1 : ℤ) + -1 = 0 by ring,
      show (3 : ℤ) * 1 - 0 + -0 = 3 by ring] at h
    obtain ⟨d, hd⟩ := hinvp 3 h3
    have h' := E.zpow_mem h d
    rwa [hzpow, hres (d * 0) (d * 3) 0 1 (by simp)
      (by rw [show d * 3 - 1 = 3 * d - 1 by ring]; exact hd)] at h'
  have hstep2 : P 0 1 ∈ E → P 1 0 ∈ E := by
    intro h01
    have h := hcm no hnoN _ h01
    rwa [hno, hinv, hmul, show (1 : ℤ) - 0 + -0 = 1 by ring,
      show (1 : ℤ) + -1 = 0 by ring] at h
  have hgen : P 1 0 ∈ E ∧ P 0 1 ∈ E := by
    by_cases hA : (p : ℤ) ∣ j - 2 * i
    · have hB : ¬ (p : ℤ) ∣ 3 * i - 2 * j := by
        intro hB
        apply hij
        have hi : (p : ℤ) ∣ i := by
          have h := dvd_add hB (dvd_mul_of_dvd_right hA 2)
          rw [show 3 * i - 2 * j + 2 * (j - 2 * i) = -i by ring] at h
          exact (dvd_neg).mp h
        refine ⟨hi, ?_⟩
        rw [show j = (j - 2 * i) + 2 * i by ring]
        exact dvd_add hA (dvd_mul_of_dvd_right hi 2)
      obtain ⟨d, hd⟩ := hinvp _ hB
      have h := E.zpow_mem hv d
      have h01 : P 0 1 ∈ E := by
        rwa [hzpow, hres (d * 0) (d * (3 * i - 2 * j)) 0 1 (by simp)
          (by rw [show d * (3 * i - 2 * j) - 1 = (3 * i - 2 * j) * d - 1 by ring]; exact hd)]
          at h
      exact ⟨hstep2 h01, h01⟩
    · obtain ⟨d, hd⟩ := hinvp _ hA
      have h := E.zpow_mem hu d
      have h10 : P 1 0 ∈ E := by
        rwa [hzpow, hres (d * (j - 2 * i)) (d * 0) 1 0
          (by rw [show d * (j - 2 * i) - 1 = (j - 2 * i) * d - 1 by ring]; exact hd)
          (by simp)] at h
      exact ⟨h10, hstep1 h10⟩
  obtain ⟨h10, h01⟩ := hgen
  intro y hy
  obtain ⟨a, b, rfl⟩ := hΩP y hy
  have e : P a b = P 1 0 ^ a * P 0 1 ^ b := by
    rw [hzpow, hzpow, hmul]
    congr 1 <;> ring
  rw [e]
  exact E.mul_mem (E.zpow_mem h10 a) (E.zpow_mem h01 b)

section Model


theorem ggSCWeylIrredTwoLU4_triD4Model {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) :
    GGSCWeylIrredTwoLU4 p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro E hE h2 _
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * n) hK3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ ^ 3 = 1 := TableBExcSmallRanks.sigma_pow_three_eq_one hK hσ
  obtain ⟨hconj, ⟨e, he⟩, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_split_prime_toral_Sylow Nat.prime_two hn K hK σ hσ hp
      (by omega) hpq
  have hTY : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := inf_le_right
  let ι : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.inclusion hTY).comp e.toMonoidHom
  have hιval : ∀ (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ),
      (ι (a, b) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ a * trialityMiddleTorus K σ b := fun a b => he a b
  have hιcoe : ∀ ab, (ι ab : ModGL TwistTag.D4.tag K) = (e ab : ModGL TwistTag.D4.tag K) :=
    fun _ => rfl
  have hιinj : Function.Injective ι := (Subgroup.inclusion_injective hTY).comp e.injective
  have hho1 : trialityOuterTorus K σ 1 = 1 := by
    have h1 := he 1 1
    rw [TableBExcSmallRanks.trialityMiddleTorus_one, mul_one] at h1
    rw [← h1]
    exact congrArg Subtype.val (map_one e)
  have hho : ∀ a : Kˣ, trialityOuterTorus K σ a = (ι (a, 1) : ModGL TwistTag.D4.tag K) :=
    fun a => by rw [hιval, TableBExcSmallRanks.trialityMiddleTorus_one, mul_one]
  have hhm : ∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityMiddleTorus K σ b = (ι (1, b) : ModGL TwistTag.D4.tag K) :=
    fun b => by rw [hιval, hho1, one_mul]
  set no : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨trialityOuterRep K,
    canonicalRep_orbitReflection_mem_graphFixedRootGroup (t := TwistTag.D4) (σ := σ.toRingHom)
      ⟨0, by decide⟩⟩
  set nm : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨trialityMiddleRep K,
    canonicalRep_orbitReflection_mem_graphFixedRootGroup (t := TwistTag.D4) (σ := σ.toRingHom)
      ⟨1, by decide⟩⟩
  have hconjMul : ∀ g x y : ModGL TwistTag.D4.tag K, g * (x * y) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by group
  have hnoι : ∀ (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ),
      no * ι (a, b) * no⁻¹ = ι (a⁻¹ * trialityFixedUnit K σ b, b) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιval]
    rw [hconjMul, trialityOuterRep_conj_outer, trialityOuterRep_conj_middle]
    simp only [hho, hhm, ← Subgroup.coe_mul, ← map_mul]
    congr 2
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  have hnmι : ∀ (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ),
      nm * ι (a, b) * nm⁻¹ = ι (a, trialityNorm σ hσ3 a * b⁻¹) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιval]
    rw [hconjMul, trialityMiddleRep_conj_outer hσ3, trialityMiddleRep_conj_middle]
    simp only [hho, hhm, ← Subgroup.coe_mul, ← map_mul]
    congr 2
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  have hpU : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hpq.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 3)
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpU
  have hζ₀q : ζ₀ ^ (2 ^ n - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hζ₀]; exact hpq)
  have hσζ₀ : σ (ζ₀ : K) = ζ₀ := by
    rw [hσ]
    have h1 : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    rw [h1, pow_succ, ← Units.val_pow_eq_pow_val, hζ₀q, Units.val_one, one_mul]
  have hζ₀k : (ζ₀ : K) ∈ trialityFixedField K σ.toRingHom := (mem_trialityFixedField).2 hσζ₀
  set ζ : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨ζ₀, hζ₀k⟩ (fun h => ζ₀.ne_zero (congrArg Subtype.val h))
  have hιζ : trialityFixedUnit K σ ζ = ζ₀ := Units.ext rfl
  have hfuinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hζord : orderOf ζ = p := by
    rw [← orderOf_injective (trialityFixedUnit K σ) hfuinj ζ, hιζ, hζ₀]
  have hNζ : trialityNorm σ hσ3 ζ₀ = ζ ^ 3 := by
    apply hfuinj
    apply Units.ext
    rw [coe_trialityNorm, map_pow, Units.val_pow_eq_pow_val, hιζ, hσζ₀, hσζ₀]
    ring
  set P : ℤ → ℤ → graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun i j => ι (ζ₀ ^ i, ζ ^ j)
  set Ω : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ((Subgroup.zpowers ζ₀).prod (Subgroup.zpowers ζ)).map ι with hΩdef
  have hPΩ : ∀ i j, P i j ∈ Ω := fun i j => Subgroup.mem_map_of_mem ι
    (Subgroup.mem_prod.mpr ⟨Subgroup.zpow_mem_zpowers ζ₀ i, Subgroup.zpow_mem_zpowers ζ j⟩)
  have hΩP : ∀ y ∈ Ω, ∃ i j, P i j = y := by
    intro y hy
    obtain ⟨ab, hab, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hab
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h2
    refine ⟨i, j, ?_⟩
    show ι (ζ₀ ^ i, ζ ^ j) = ι ab
    rw [hi, hj]
  have hmul : ∀ i j i' j', P i j * P i' j' = P (i + i') (j + j') := by
    intro i j i' j'
    show ι _ * ι _ = ι _
    rw [← map_mul, Prod.mk_mul_mk, ← zpow_add, ← zpow_add]
  have hone : ∀ i j, P i j = 1 ↔ (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j
    show ι _ = 1 ↔ _
    rw [map_eq_one_iff ι hιinj, Prod.mk_eq_one, ← orderOf_dvd_iff_zpow_eq_one,
      ← orderOf_dvd_iff_zpow_eq_one, hζ₀, hζord]
  have hnoP : ∀ i j, no * P i j * no⁻¹ = P (j - i) j := by
    intro i j
    show no * ι _ * no⁻¹ = ι _
    rw [hnoι, map_zpow, hιζ, ← zpow_neg, ← zpow_add, neg_add_eq_sub]
  have hnmP : ∀ i j, nm * P i j * nm⁻¹ = P i (3 * i - j) := by
    intro i j
    show nm * ι _ * nm⁻¹ = ι _
    rw [hnmι, map_zpow, hNζ, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add,
      ← sub_eq_add_neg]
    norm_num
  have hEp : IsPGroup p E := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 _ x.2)⟩
  obtain ⟨g, hg⟩ := hconj E hEp
  set E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    E.map (MulAut.conj g).toMonoidHom with hE'def
  have hE'Ω : E' ≤ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    have hxT := hg ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hxT
    obtain ⟨ab, hab⟩ := e.surjective ⟨_, hxT⟩
    have hxι : ι ab = (MulAut.conj g).toMonoidHom y :=
      Subtype.ext ((hιcoe ab).trans (congrArg Subtype.val hab))
    have hxp : ((MulAut.conj g).toMonoidHom y) ^ p = 1 := by
      rw [← map_pow, hE.2 y hy, map_one]
    rw [← hxι, ← map_pow, map_eq_one_iff ι hιinj] at hxp
    rw [← hxι]
    refine Subgroup.mem_map_of_mem ι (Subgroup.mem_prod.mpr ⟨?_, ?_⟩)
    · rw [(IsPrimitiveRoot.iff_orderOf.mpr hζ₀).zpowers_eq, mem_rootsOfUnity]
      exact congrArg Prod.fst hxp
    · rw [(IsPrimitiveRoot.iff_orderOf.mpr hζord).zpowers_eq, mem_rootsOfUnity]
      exact congrArg Prod.snd hxp
  have hcardΩ : Nat.card Ω ≤ p ^ 2 := by
    rw [hΩdef, Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hζ₀, hζord, sq]
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE'eq : E' = Ω :=
    Subgroup.eq_of_le_of_card_ge hE'Ω (by rw [hcardE']; exact hcardΩ.trans h2)
  have hirrE' : GGWeylIrred E' := by
    rw [hE'eq]
    exact ggWeylIrred_of_triD4Coords hp (by omega) P hPΩ hΩP hmul hone hnoP hnmP
  have hirr := ggWeylIrred_map (MulAut.conj g⁻¹) hirrE'
  have hback : E'.map (MulAut.conj g⁻¹).toMonoidHom = E := by
    rw [hE'def, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      MonoidHom.ext fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
    rw [hcomp, Subgroup.map_id]
  rwa [hback] at hirr

theorem ggSCWeylIrredTwoLU4_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n - 1) : GGSCWeylIrredTwoLU4 p (GGTriD4R n K) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  exact ggSCWeylIrredTwoLU4_of_mulEquiv e (ggSCWeylIrredTwoLU4_triD4Model hn hK σ hσ hp hp5 hpq)

theorem two_dvd_card_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) : 2 ∣ Nat.card (GGTriD4R n K) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨hC0, -, -⟩ := triality_both_orientations_exact_finite_order 2 n Nat.prime_two hn K hK
    1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  rw [Nat.card_congr e.toEquiv, hC0]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _) _

end Model

section Row


theorem ggCenterPrime_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (hs : IsSimpleGroup (GGTriD4R n K))
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) {p : ℕ} (hp : p.Prime) :
    GGCenterPrime p (GGTriD4R n K) := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have hkc : ψ.ker = Subgroup.center L' := TableBUR.ker_eq_center_of_surjective hψ hker hZ
  let θ : L' ⧸ Subgroup.center L' ≃* GGTriD4R n K :=
    (QuotientGroup.quotientMulEquivOfEq hkc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have h1 := ggTriD4SchurInput_holds n hn K hK hs L' hperf θ
  rw [h1, Subgroup.card_bot] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

theorem ggTorusNoLineTwo_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (hs : IsSimpleGroup (GGTriD4R n K))
    (hna : ∃ a b : GGTriD4R n K, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n - 1) : GGTorusNoLineTwo p (GGTriD4R n K) (GGTriD4ID n K) := by
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := by
    have := hs
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun h => ?_
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  exact ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp hZ
    (fun φ hφ _ => TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hφ)
    (ggCenterPrime_triD4 hn hK hs hZ hp) (ggSCWeylIrredTwoLU4_triD4 hn hK hp hp5 hpq)

theorem rowPlainTwo_triD4_recipe {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n - 1) :
    GGNbrWeylRowPlainTwo p 0 (GGTriD4R n K) (GGTriD4ID n K)
      (LargeEvenChevFieldImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
  ⟨fun g => conj_mem_chevIDImage _ g, TypeA.ggTorusLift_zero (two_dvd_card_triD4 hn hK),
    fun hs hna => ggTorusNoLineTwo_triD4 hn hK hs hna hp hp5 hpq⟩

theorem largeEvenLabelAll_rowPlainTwo_triD4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .triD4 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpq⟩ := h
  dsimp only at ht hpq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (fun K _ _ hK => rowPlainTwo_triD4_recipe hn hK hp hp5 hpq) hQ

end Row

end CFSG.StandardType

end
