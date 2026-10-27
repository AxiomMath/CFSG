module

public import CFSG.Quasithin.Background.C41PfF
import CFSG.Quasithin.EmptyFaithful.SzC4S8Nat
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace C41Pf

section Orders

theorem eight_dvd_card_of_isParabolic2 {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    {m : ℕ} (hP : IsParabolic2 L P) (hL : Nat.card ↥L = 2 ^ 3 * m) (hm : Odd m) :
    2 ^ 3 ∣ Nat.card ↥P := by
  obtain ⟨-, S, hS, hSP⟩ := hP
  have hSle : S ≤ P := fun s hs => hSP ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.2.1
  have h1 : S.relIndex L * Nat.card ↥(S ⊓ L) = Nat.card ↥L := Subgroup.relIndex_mul_card S L
  rw [inf_eq_left.mpr hS.1, hk, hL] at h1
  have hodd : Odd (S.relIndex L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.2.2)
  have hk1 : 2 ^ k ∣ 2 ^ 3 := by
    have h2 : 2 ^ k ∣ 2 ^ 3 * m := ⟨S.relIndex L, by rw [← h1]; ring⟩
    exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right h2
  have hk2 : 2 ^ 3 ∣ 2 ^ k := by
    have h2 : 2 ^ 3 ∣ S.relIndex L * 2 ^ k := ⟨m, h1⟩
    exact (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_left h2
  have hk3 : k = 3 := le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk1)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk2)
  rw [← hk3, ← hk]
  exact Subgroup.card_dvd_of_le hSle

theorem isSolvable_of_isParabolic2_168 {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hP : IsParabolic2 L P) (hne : P ≠ L) (hL : Nat.card ↥L = 168) : Group.IsSolvable ↥P := by
  have h8 := eight_dvd_card_of_isParabolic2 hP (m := 21) (by rw [hL]; norm_num) (by decide)
  have hdvd : Nat.card ↥P ∣ 168 := hL ▸ Subgroup.card_dvd_of_le hP.1
  have hlt : Nat.card ↥P ≠ 168 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hP.1 (by rw [hL, h]))
  obtain ⟨c, hc⟩ := h8
  rw [hc] at hdvd hlt
  have hc21 : c ∈ Nat.divisors 21 := by
    have h1 : 2 ^ 3 * c ∣ 2 ^ 3 * 21 := by norm_num at hdvd ⊢; exact hdvd
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1, by norm_num⟩
  have hdiv : Nat.divisors 21 = {1, 3, 7, 21} := by decide
  rw [hdiv] at hc21
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc21
  rcases hc21 with rfl | rfl | rfl | rfl
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 0) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hc]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hc]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 1) Nat.prime_two (by norm_num : (7 :
      ℕ).Prime) (by norm_num) (by rw [hc]; norm_num)
  · exact absurd rfl hlt

theorem isSolvable_of_isParabolic2_360 {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hP : IsParabolic2 L P) (hne : P ≠ L) (hL : Nat.card ↥L = 360) [IsSimpleGroup ↥L] :
    Group.IsSolvable ↥P := by
  have h8 := eight_dvd_card_of_isParabolic2 hP (m := 45) (by rw [hL]; norm_num) (by decide)
  have hdvd : Nat.card ↥P ∣ 360 := hL ▸ Subgroup.card_dvd_of_le hP.1
  have hidx : 6 ≤ (P.subgroupOf L).index := by
    by_contra hlt
    push Not at hlt
    have htop : P.subgroupOf L = ⊤ := by
      apply SmithC27.eq_top_of_not_dvd_factorial_index
      rw [hL]
      interval_cases h : (P.subgroupOf L).index <;> decide
    apply hne
    refine le_antisymm hP.1 fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact this
  have hcard : (P.subgroupOf L).index * Nat.card ↥P = 360 := by
    have h1 := Subgroup.relIndex_mul_card P L
    rw [inf_eq_left.mpr hP.1, hL] at h1
    exact h1
  obtain ⟨c, hc⟩ := h8
  rw [hc] at hdvd hcard
  have hc45 : c ∈ Nat.divisors 45 := by
    have h1 : 2 ^ 3 * c ∣ 2 ^ 3 * 45 := by norm_num at hdvd ⊢; exact hdvd
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1, by norm_num⟩
  have hdiv : Nat.divisors 45 = {1, 3, 5, 9, 15, 45} := by decide
  rw [hdiv] at hc45
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc45
  rcases hc45 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 0) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hc]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hc]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 1) Nat.prime_two (by norm_num : (5 :
      ℕ).Prime) (by norm_num) (by rw [hc]; norm_num)
  all_goals exfalso; omega

end Orders

variable {G : Type} [Group G] [Finite G]

section Core

theorem inf_centralizer_le_oTwoZIn {R K : Subgroup G}
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :
    K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤ oTwoZIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := pCoreOf 2 (K ⊔ R) with hA
  set Z := oTwoZIn K with hZ
  have hBA : K ⊔ R ≤ Subgroup.normalizer (A : Set G) := le_normalizer_pCoreOf 2 (K ⊔ R)
  have hZK : Z ≤ K := Subgroup.map_subtype_le _
  have hKA : K ⊓ A ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (le_sup_left.trans hBA)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hOZ : pCoreOf 2 K ≤ Z := by
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥K) w ∈ Subgroup.center _
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff w).mpr hw]
    exact Subgroup.one_mem _
  have hZA : Z ≤ Subgroup.normalizer (A : Set G) := hZK.trans (le_sup_left.trans hBA)
  rintro x ⟨hxK, hxC⟩
  have hx' : x ∈ ((A ⊔ Z : Subgroup G) : Set G) := h1.2.1 ⟨Subgroup.mem_sup_left hxK, hxC⟩
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A Z hZA] at hx'
  obtain ⟨a, ha, z, hz, rfl⟩ := hx'
  have haK : a ∈ K := by
    have := K.mul_mem hxK (K.inv_mem (hZK hz))
    simpa using this
  exact Z.mul_mem (hOZ (hKA ⟨haK, ha⟩)) hz

omit [Finite G] in
theorem map_oTwoZIn_eq_one {K : Subgroup G} {X : Type*} [Group X] (α : ↥K →* X)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hZ : Subgroup.center X = ⊥) {w : ↥K} (hw : (w : G) ∈ oTwoZIn K) : α w = 1 := by
  obtain ⟨w', hw', hww⟩ := hw
  have hw'' : w' = w := Subtype.ext hww
  subst hw''
  have hc : α w' ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k, rfl⟩ := hα x
    have h1 : ((k * w' : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = ((w' * k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact (Subgroup.mem_center_iff.mp hw' _)
    have h2 := QuotientGroup.eq.mp h1
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul] at h2
    have h3 : α k * α w' = α w' * α k := by
      calc α k * α w' = α k * α w' * ((α k * α w')⁻¹ * (α w' * α k)) := by rw [h2, mul_one]
        _ = α w' * α k := by group
    exact h3
  rw [hZ] at hc
  exact Subgroup.mem_bot.mp hc

omit [Finite G] in
theorem conjAct_eq_one_iff' {V : Subgroup G} (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  A4.conjAct_eq_one_iff

omit [Finite G] in
theorem nonempty_autOn_equiv {K V : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G))
    {X : Type*} [Group X] (α : ↥K →* X) (hα : Function.Surjective α)
    (hker : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (V : Set G)) :
    Nonempty (↥(autOn K V) ≃* X) := by
  let φ : ↥K →* ↥(autOn K V) :=
    ((conjAct V).comp (Subgroup.inclusion hKN)).codRestrict (autOn K V) fun k =>
      ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : φ.ker = α.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
    constructor
    · intro h
      have h' : conjAct V (Subgroup.inclusion hKN k) = 1 := congrArg Subtype.val h
      exact (conjAct_eq_one_iff' _).mp h'
    · intro h
      apply Subtype.ext
      exact (conjAct_eq_one_iff' (Subgroup.inclusion hKN k)).mpr h
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))⟩

theorem pCoreOf_le_centralizer {R K : Subgroup G} (hRN : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
  have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 K)
    exact sup_le (le_normalizer_pCoreOf 2 K) (hRN.trans (normalizer_le_normalizer_pCoreOf 2 K))
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (mem_centralizer_of_mem_omegaOneCenterOf hv (hle hq)).symm

theorem map_eq_one_iff_mem_centralizer {R K : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) {X : Type*} [Group X]
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hZ : Subgroup.center X = ⊥) (k : ↥K) :
    α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
  constructor
  · intro hk
    have hk' : k ∈ CFSG.pCore 2 ↥K := hker ▸ MonoidHom.mem_ker.mpr hk
    have hkO : (k : G) ∈ pCoreOf 2 K := by
      rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
      exact ⟨k, hk', rfl⟩
    exact pCoreOf_le_centralizer hRN hkO
  · intro hk
    exact map_oTwoZIn_eq_one α hα hker hZ (inf_centralizer_le_oTwoZIn h1 ⟨k.2, hk⟩)

omit [Finite G] in
theorem le_normalizer_omegaOneCenter (K R : Subgroup G) :
    K ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
  le_sup_left.trans ((le_normalizer_pCoreOf 2 (K ⊔ R)).trans
    (normalizer_le_normalizer_omegaOneCenterOf _))

end Core

section Cases

theorem eq_bot_of_alt_transposition {R M K P : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≤ 6) (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap)
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⊓
        Subgroup.centralizer (autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :
          Set (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))))
    (hPK : P ≤ K) (hPM : P ≤ M) (hPp : ⁅P, P⁆ = P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenter K R
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPK.trans hKN
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hRN htR
  have hcomm : ∀ (p : G) (hp : p ∈ P),
      (α ⟨p, hPK hp⟩ : Equiv.Perm (Fin n)) * σ = σ * (α ⟨p, hPK hp⟩ : Equiv.Perm (Fin n)) := by
    intro p hp
    have hpMK : conjAct V ⟨p, hPN hp⟩ ∈ autOn (M ⊓ K) V := ⟨⟨p, hPN hp⟩, ⟨hPM hp, hPK hp⟩, rfl⟩
    rw [hMK] at hpMK
    have htA : conjAct V ⟨t, htV⟩ ∈ autOn R V := ⟨⟨t, htV⟩, htR, rfl⟩
    have hc1 := Subgroup.mem_centralizer_iff.mp hpMK.2 _ htA
    have htpt : t * p * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK p).mp (hPK hp)
    have hxK : t * p * t⁻¹ * p⁻¹ ∈ K := K.mul_mem htpt (K.inv_mem (hPK hp))
    have hxN : t * p * t⁻¹ * p⁻¹ ∈ Subgroup.normalizer (V : Set G) := hKN hxK
    have hxC : t * p * t⁻¹ * p⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have e : (⟨t * p * t⁻¹ * p⁻¹, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G))) * ⟨p, hPN hp⟩ *
            (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ *
            (⟨p, hPN hp⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ := rfl
      refine (conjAct_eq_one_iff' ⟨t * p * t⁻¹ * p⁻¹, hxN⟩).mp ?_
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc1]
      group
    have h1' : α ⟨t * p * t⁻¹ * p⁻¹, hxK⟩ = 1 :=
      (map_eq_one_iff_mem_centralizer hRN h1 α hα hker hZ _).mpr hxC
    have h2 : α ⟨t * p * t⁻¹, htpt⟩ = α ⟨p, hPK hp⟩ := by
      have e : (⟨t * p * t⁻¹, htpt⟩ : ↥K) = ⟨t * p * t⁻¹ * p⁻¹, hxK⟩ * ⟨p, hPK hp⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, h1', one_mul]
    have h3 := hconj p (hPK hp) htpt
    rw [h2] at h3
    calc (α ⟨p, hPK hp⟩ : Equiv.Perm (Fin n)) * σ =
        σ * (α ⟨p, hPK hp⟩ : Equiv.Perm (Fin n)) * σ⁻¹ * σ := by rw [← h3]
      _ = σ * (α ⟨p, hPK hp⟩ : Equiv.Perm (Fin n)) := by group
  set Y : Subgroup (Equiv.Perm (Fin n)) :=
    ((P.subgroupOf K).map α).map (alternatingGroup (Fin n)).subtype with hY
  obtain ⟨a, b, hab, rfl⟩ := hσ
  have hYle : Y ≤ MulAction.stabilizer (Equiv.Perm (Fin n)) (({a, b} : Finset (Fin n)) :
      Set (Fin n)) := by
    rw [Finset.coe_insert, Finset.coe_singleton, ← SmithC27.centralizer_swap hab]
    rintro _ ⟨_, ⟨⟨p, hpK⟩, hp, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm p hp
  have hsolS : Group.IsSolvable ↥(MulAction.stabilizer (Equiv.Perm (Fin n))
      (({a, b} : Finset (Fin n)) : Set (Fin n))) := by
    have hcard := SmithC27.card_stabilizer_coe_finset (({a, b} : Finset (Fin n)))
    rw [Fintype.prod_bool] at hcard
    have ht : Fintype.card {x // decide (x ∈ ({a, b} : Finset (Fin n))) = true} = 2 := by
      simp only [decide_eq_true_eq]
      rw [Fintype.card_coe, Finset.card_pair hab]
    have hf : Fintype.card {x // decide (x ∈ ({a, b} : Finset (Fin n))) = false} = n - 2 := by
      simp only [decide_eq_false_iff_not]
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_pair hab, Fintype.card_fin]
    rw [ht, hf] at hcard
    interval_cases n
    · exact isSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 1) Nat.prime_two Nat.prime_three
        (by norm_num) (by rw [hcard]; decide)
    · exact isSolvable_of_card_eq_pow_mul_pow (a := 4) (b := 1) Nat.prime_two Nat.prime_three
        (by norm_num) (by rw [hcard]; decide)
  have hYs : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYle)
      (Subgroup.inclusion_injective hYle)
  have hYp : ⁅Y, Y⁆ = Y := by
    rw [hY, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_subgroupOf hPK hPK, hPp]
  have hY1 := eq_bot_of_perfect_of_isSolvable hYp hYs
  have hPO : P ≤ pCoreOf 2 K := by
    intro p hp
    have hmem : ((α ⟨p, hPK hp⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ Y :=
      ⟨_, ⟨⟨p, hPK hp⟩, hp, rfl⟩, rfl⟩
    rw [hY1, Subgroup.mem_bot] at hmem
    have h1' : α ⟨p, hPK hp⟩ = 1 := Subtype.ext hmem
    have hk' : (⟨p, hPK hp⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hker ▸ MonoidHom.mem_ker.mpr h1'
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    exact ⟨⟨p, hPK hp⟩, hk', rfl⟩
  have hPs : Group.IsSolvable ↥P := by
    have := ((pCoreOf_isPGroup 2 K).to_le hPO).isNilpotent
    infer_instance
  exact eq_bot_of_perfect_of_isSolvable hPp hPs

theorem isSolvable_of_c27A6 {R M K : Subgroup G} (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hK : IsAltBlockType K 6)
    (hmax : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) :
    Group.IsSolvable ↥(autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) := by
  obtain ⟨-, α, hα, hker, -⟩ := hK
  have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  obtain ⟨e⟩ := nonempty_autOn_equiv (le_normalizer_omegaOneCenter K R) α hα
    (map_eq_one_iff_mem_centralizer hRN h1 α hα hker hZ)
  have hcard : Nat.card ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) := e.isSimpleGroup
  exact isSolvable_of_isParabolic2_360 hmax.1 hmax.2.1 hcard

theorem card_statedSL_three_of_card_two {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168 :=
  CFSG.Quasithin.SzC4S8.card_statedSL_three_eq_168 hF

theorem isSolvable_of_c27SL3_two {K V M : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2)
    (e : ↥(autOn K V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)) :
    Group.IsSolvable ↥(autOn (M ⊓ K) V) := by
  have hcard : Nat.card ↥(autOn K V) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_three_of_card_two hF]
  exact isSolvable_of_isParabolic2_168 hmax.1 hmax.2.1 hcard

end Cases

end C41Pf

end CFSG.Quasithin
