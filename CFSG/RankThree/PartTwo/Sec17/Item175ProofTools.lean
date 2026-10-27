module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaSTransfer
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof175

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_or_eq_inv {c x : G} (hc : orderOf c = 3)
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c⁻¹ := by
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hmem : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h3 : ((orderOf c : ℕ) : ℤ) = 3 := by rw [hc]; norm_num
  have hm' : c ^ (m % 3) = x * c * x⁻¹ := by rw [← hm, ← h3, zpow_mod_orderOf]
  have hlt : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  have hge : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  set j := m % 3 with hj
  interval_cases j
  · exfalso
    apply hc1
    rw [zpow_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hm'
    exact hm'
  · left
    rw [zpow_one] at hm'
    exact hm'.symm
  · right
    rw [← hm', eq_inv_iff_mul_eq_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
      ← pow_succ, hc3]

omit [Finite G] in
theorem mem_centralizer_of_mem_normalizer {c x : G} (hc : orderOf c = 3)
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    x ∈ Subgroup.centralizer ({c} : Set G) := by
  have hx2 : x ^ 2 * c * (x ^ 2)⁻¹ = c := by
    rcases conj_eq_or_eq_inv hc hx with h1 | h1
    · calc x ^ 2 * c * (x ^ 2)⁻¹ = x * (x * c * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = c := by rw [h1, h1]
    · calc x ^ 2 * c * (x ^ 2)⁻¹ = x * (x * c * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * c⁻¹ * x⁻¹ := by rw [h1]
        _ = (x * c * x⁻¹)⁻¹ := by group
        _ = c := by rw [h1, inv_inv]
  have hx2C : x ^ 2 ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 2 * c = x ^ 2 * c * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = c * x ^ 2 := by rw [hx2]
  obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hxeq : x = (x ^ 2) ^ (t + 1) := by
    rw [← pow_mul, show 2 * (t + 1) = 3 ^ k + 1 by omega, pow_succ, hxk, one_mul]
  rw [hxeq]
  exact pow_mem hx2C _

theorem item175_of_sylow {A T : Subgroup G} {c : G} (hc : orderOf c = 3) (hA : IsE27 A)
    (hT : IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)))
    (hi : ∀ x ∈ T, x ^ 3 = 1 →
      ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), ℓ * x * ℓ⁻¹ ∈ A)
    (hii : ∀ E : Subgroup G, E ≤ T → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      c ∈ E → ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G),
        E.map (MulAut.conj ℓ).toMonoidHom = A) :
    Item175 A c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hΩ g hg
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
  set x := g * c * g⁻¹ with hxdef
  have hxH : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hg ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hx3 : x ^ 3 = 1 := by rw [hxdef, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    mem_centralizer_of_mem_normalizer hc hxH (k := 1) (by rw [pow_one]; exact hx3)
  have hx3' : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hx3 (fun h1 => by
      rw [hxdef, mul_inv_eq_one, mul_eq_left] at h1
      rw [h1, orderOf_one] at hc
      omega))
  obtain ⟨Q, hQ, hxQ⟩ := Item134SylowBarProof.exists_isSylowOf_le
    (Subgroup.zpowers_le.mpr hxC) hx3'
  obtain ⟨m, hmC, hQm⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hT hQ
  have hxT : m⁻¹ * x * m ∈ T := by
    have hxQ' : x ∈ T.map (MulAut.conj m).toMonoidHom := hQm ▸ hxQ (Subgroup.mem_zpowers x)
    obtain ⟨y, hy, hyx⟩ := hxQ'
    have : y = m⁻¹ * x * m := by
      rw [← hyx]
      simp [MulAut.conj_apply, mul_assoc]
    exact this ▸ hy
  have hxT3 : (m⁻¹ * x * m) ^ 3 = 1 := by
    rw [show m⁻¹ * x * m = m⁻¹ * x * m⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3, mul_one,
      mul_inv_cancel]
  obtain ⟨ℓ, hℓC, hℓA⟩ := hi _ hxT hxT3
  set k := ℓ * m⁻¹ * g with hkdef
  have hkc : k * c * k⁻¹ ∈ A := by
    have : k * c * k⁻¹ = ℓ * (m⁻¹ * x * m) * ℓ⁻¹ := by rw [hkdef, hxdef]; group
    rw [this]
    exact hℓA
  set E₀ := A.map (MulAut.conj k⁻¹).toMonoidHom with hE₀
  have hcE₀ : c ∈ E₀ := ⟨k * c * k⁻¹, hkc, by simp [mul_assoc]⟩
  have hE₀ab : CFSG.Assembly.IsElemAbelian 3 E₀ :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ A hA.1
  have hE₀C : E₀ ≤ Subgroup.centralizer ({c} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE₀ab.1.is_comm.comm ⟨e, he⟩ ⟨c, hcE₀⟩))
  have hE₀3 : IsPGroup 3 E₀ := hA.isPGroup.map _
  obtain ⟨Q', hQ', hE₀Q'⟩ := Item134SylowBarProof.exists_isSylowOf_le hE₀C hE₀3
  obtain ⟨m', hm'C, hQm'⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hT hQ'
  set E := E₀.map (MulAut.conj m'⁻¹).toMonoidHom with hEdef
  have hET : E ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ T.map (MulAut.conj m').toMonoidHom := hQm' ▸ hE₀Q' he
    obtain ⟨y, hy, hye⟩ := he'
    have : (MulAut.conj m'⁻¹).toMonoidHom e = y := by
      rw [← hye]
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hy
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E₀ hE₀ab
  have hE27 : Nat.card E = 27 := by
    rw [hEdef, hE₀, Subgroup.card_map_of_injective (MulAut.conj m'⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hA.2]
  have hcE : c ∈ E := by
    refine ⟨c, hcE₀, ?_⟩
    have hmc : m' * c = c * m' := Subgroup.mem_centralizer_singleton_iff.mp hm'C
    change m'⁻¹ * c * m'⁻¹⁻¹ = c
    rw [inv_inv, mul_assoc, ← hmc, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨ℓ', hℓ'C, hℓ'A⟩ := hii E hET hEab hE27 hcE
  set y := ℓ' * m'⁻¹ * k⁻¹ with hydef
  have hyA : A.map (MulAut.conj y).toMonoidHom = A := by
    rw [hydef, map_conj_mul, map_conj_mul, ← hE₀, ← hEdef, hℓ'A]
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_map_conj_eq' hyA
  have hyH : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have hmem : (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom ∈ omegaA A :=
      (map_conj_mem_omegaA_iff hyN).mpr (by rw [hΩ]; exact Set.mem_singleton _)
    rw [hΩ] at hmem
    exact mem_normalizer_of_map_conj_eq' hmem
  have hkH : k⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have : k⁻¹ = m' * ℓ'⁻¹ * y := by rw [hydef]; group
    rw [this]
    exact mul_mem (mul_mem (hCH hm'C) (inv_mem (hCH hℓ'C))) hyH
  have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have : g = m * ℓ⁻¹ * k⁻¹⁻¹ := by rw [inv_inv, hkdef]; group
    rw [this]
    exact mul_mem (mul_mem (hCH hmC) (inv_mem (hCH hℓC))) (inv_mem hkH)
  exact Late.map_conj_eq_of_mem_normalizer hgH

theorem sylow_facts_of_eq_omegaOneThree {A T : Subgroup G} {c : G} (hA : IsE27 A)
    (hAT : A = omegaOneThree T) :
    (∀ x ∈ T, x ^ 3 = 1 → ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), ℓ * x * ℓ⁻¹ ∈ A) ∧
    (∀ E : Subgroup G, E ≤ T → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → c ∈ E →
      ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), E.map (MulAut.conj ℓ).toMonoidHom = A) := by
  have hle : ∀ x ∈ T, x ^ 3 = 1 → x ∈ A := fun x hx hx3 => by
    rw [hAT]
    exact Subgroup.subset_closure ⟨hx, hx3⟩
  refine ⟨fun x hx hx3 => ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact hle x hx hx3⟩,
    fun E hET hE hE27 _ => ⟨1, one_mem _, ?_⟩⟩
  rw [map_conj_one]
  exact Subgroup.eq_of_le_of_card_ge (fun e he => hle e (hET he) (hE.2 e he))
    (by rw [hA.2, hE27])

section Decomposition

variable {L : Subgroup G}

theorem exists_inv_mul_mem_thetaQuotCentralizer_of_inner
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hinn : ∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), ∀ k : ℕ, σ ^ 3 ^ k = 1 →
      ∃ q, MulAut.conj q = σ)
    {S : Subgroup G} (hS : IsSylowOf 3 S L) {ρ : G}
    (hρL : ρ ∈ Subgroup.normalizer (L : Set G)) (hρS : ρ ∈ Subgroup.normalizer (S : Set G))
    {k : ℕ} (hρ : ρ ^ 3 ^ k = 1) :
    ∃ s ∈ S, s⁻¹ * ρ ∈ Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S', rfl⟩ := hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set ρ' : Subgroup.normalizer (L : Set G) := ⟨ρ, hρL⟩ with hρ'
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ρ') with hσ
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : ρ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hρ)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨q, hq⟩ := hinn σ k hσk
  have hσapp : ∀ x : ↥L, σ (π x) = π (L.normalizerMonoidHom ρ' x) := fun x => rfl
  have hqapp : ∀ y, q * y * q⁻¹ = σ y := fun y => by rw [← hq]; rfl
  have hρS' : ∀ x ∈ (S' : Subgroup ↥L), L.normalizerMonoidHom ρ' x ∈ (S' : Subgroup ↥L) := by
    intro x hx
    have h1 : ρ * (x : G) * ρ⁻¹ ∈ (S' : Subgroup ↥L).map L.subtype :=
      (Subgroup.mem_normalizer_iff.mp hρS x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = L.normalizerMonoidHom ρ' x := Subtype.ext hyx
    exact this ▸ hy
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S' : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  have hqN : q ∈ Subgroup.normalizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
      Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hqapp]
    rw [SetLike.mem_coe, hSb] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hσapp]
    exact Subgroup.mem_map_of_mem π (hρS' x hx)
  have hq3 : q ^ 3 ^ k = 1 := by
    have hc : q ^ 3 ^ k ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : MulAut.conj (q ^ 3 ^ k) = 1 := by rw [map_pow, hq, hσk]
      have h2 := congrArg (fun φ : MulAut _ => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * q ^ 3 ^ k = q ^ 3 ^ k * y * (q ^ 3 ^ k)⁻¹ * q ^ 3 ^ k := by rw [h2]
        _ = q ^ 3 ^ k * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hqS : q ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    have hdvd : orderOf q ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hq3
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hp : IsPGroup 3 (Subgroup.zpowers q) :=
      IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
    have hsup := hp.to_sup_of_normal_right' Sb.isPGroup' (Subgroup.zpowers_le.mpr hqN)
    have heq := Sb.3 hsup le_sup_right
    exact heq ▸ (le_sup_left : Subgroup.zpowers q ≤ _) (Subgroup.mem_zpowers q)
  rw [hSb] at hqS
  obtain ⟨s₁, hs₁, hs₁q⟩ := hqS
  refine ⟨(s₁ : G), ⟨s₁, hs₁, rfl⟩, ?_⟩
  have hs₁N : (s₁ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer s₁.2
  have hmemN : (s₁ : G)⁻¹ * ρ ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hs₁N) hρL
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hmemN, fun x => ?_⟩
  have heq : L.normalizerMonoidHom ⟨(s₁ : G)⁻¹ * ρ, hmemN⟩ x =
      s₁⁻¹ * L.normalizerMonoidHom ρ' x * s₁ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    show (s₁ : G)⁻¹ * ρ * (x : G) * ((s₁ : G)⁻¹ * ρ)⁻¹ = (s₁ : G)⁻¹ * (ρ * (x : G) * ρ⁻¹) * s₁
    group
  rw [heq, map_mul, map_mul, map_inv, ← hσapp, ← hqapp, hs₁q]
  group
  rfl

theorem exists_zpow_mul_of_pow_eq_one
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hinn : ∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), ∀ k : ℕ, σ ^ 3 ^ k = 1 →
      ∃ q, MulAut.conj q = σ)
    {A T : Subgroup G} {c : G} (hAF : A ∈ partTwoF G)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hT3 : IsPGroup 3 T) (hAT : A ≤ T)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowOf 3 (T ⊓ L) L) {x : G} (hxT : x ∈ T) (hx3 : x ^ 3 = 1) :
    ∃ k : ℤ, ∃ s ∈ T ⊓ L, s ^ 3 = 1 ∧ x = c ^ k * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Y := T ⊓ Sec4.thetaQuotCentralizer L with hYdef
  have hcA : c ∈ A := hAeq ▸ (le_sup_left : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hcL : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hy)).symm
  have hcY : c ∈ Y := ⟨hAT hcA, mem_thetaQuotCentralizer_of_commute hcL⟩
  set S' := (T ⊓ L).subgroupOf L with hS'
  have hS'3 : IsPGroup 3 S' := (hT3.to_le inf_le_left).comap_of_injective L.subtype
    L.subtype_injective
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hS'3
  have hYS : ∀ y ∈ Y, ∀ s ∈ T ⊓ L, y * s = s * y := by
    intro y hy s hs
    obtain ⟨hyN, hytriv⟩ := mem_thetaQuotCentralizer_iff.mp hy.2
    have hysT : y * s * y⁻¹ ∈ T := mul_mem (mul_mem hy.1 hs.1) (inv_mem hy.1)
    have hysL : y * s * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN s).mp hs.2
    have h1 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = L.normalizerMonoidHom ⟨y, hyN⟩ ⟨s, hs.2⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hyN⟩ ⟨s, hs.2⟩).symm
    have h2 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = ⟨s, hs.2⟩ := by
      refine hinj (show (⟨y * s * y⁻¹, hysL⟩ : ↥L) ∈ S' from ⟨hysT, hysL⟩)
        (show (⟨s, hs.2⟩ : ↥L) ∈ S' from hs) ?_
      rw [h1]
      exact hytriv ⟨s, hs.2⟩
    have h3 : y * s * y⁻¹ = s := congrArg Subtype.val h2
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h3]
  have hYL : ∀ e ∈ Y, e ∈ T ⊓ L → e = 1 := by
    intro e heY he
    obtain ⟨heN, hetriv⟩ := mem_thetaQuotCentralizer_iff.mp heY.2
    have hecen : π ⟨e, he.2⟩ ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        have h1 : L.normalizerMonoidHom ⟨e, heN⟩ x = ⟨e, he.2⟩ * x * ⟨e, he.2⟩⁻¹ :=
          Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)
        have h2 := hetriv x
        rw [h1, map_mul, map_mul, map_inv] at h2
        change π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x
        calc π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x * (π ⟨e, he.2⟩)⁻¹ * π ⟨e, he.2⟩ := by
              rw [h2]
          _ = π ⟨e, he.2⟩ * π x := by group
    rw [hZ, Subgroup.mem_bot] at hecen
    have he1 : (⟨e, he.2⟩ : ↥L) = 1 :=
      hinj (show (⟨e, he.2⟩ : ↥L) ∈ S' from he) (one_mem S') (by rw [hecen, map_one])
    exact congrArg Subtype.val he1
  have hAL : A ⊓ L ≤ T ⊓ L := inf_le_inf_right L hAT
  have hY3 : ∀ z ∈ Y, z ^ 3 = 1 → z ∈ Subgroup.zpowers c := by
    intro z hz hz3
    have hAz : A ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun e he => ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hTc hz.1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hYS z hz e (hAL he)).symm
    have hzA : z ∈ A := mem_of_mem_partTwoF hAF hz3 hAz
    have hcAL : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun e he => (hcL e he.2).symm
    rw [hAeq] at hzA
    obtain ⟨k, e, he, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcAL hzA
    have heY : e ∈ Y := by
      have : e = (c ^ k)⁻¹ * (c ^ k * e) := by group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hcY k)) hz
    rw [hYL e heY (hAL he), mul_one]
    exact zpow_mem (Subgroup.mem_zpowers c) k
  obtain ⟨n, hn⟩ := hT3 ⟨x, hxT⟩
  have hxn : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxS : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hxT))
      (Subgroup.zpowers_le.mpr (hTL hxT)) (Subgroup.mem_zpowers x)
  obtain ⟨s, hs, hsY⟩ :=
    exists_inv_mul_mem_thetaQuotCentralizer_of_inner hZ hinn hS (hTL hxT) hxS hxn
  have hγY : s⁻¹ * x ∈ Y :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hs).1) hxT, hsY⟩
  set γ := s⁻¹ * x with hγ
  have hxsγ : x = s * γ := by rw [hγ]; group
  have hsγ : γ * s = s * γ := hYS γ hγY s hs
  have hcube : s ^ 3 * γ ^ 3 = 1 := by
    have hc : Commute s γ := hsγ.symm
    rw [← hc.mul_pow, ← hxsγ, hx3]
  have hγ3 : γ ^ 3 = 1 := by
    have hmemL : γ ^ 3 ∈ T ⊓ L := by
      have : γ ^ 3 = (s ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hcube
      rw [this]
      exact inv_mem (pow_mem hs 3)
    exact hYL _ (pow_mem hγY 3) hmemL
  have hs3 : s ^ 3 = 1 := by rw [hγ3, mul_one] at hcube; exact hcube
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hY3 γ hγY hγ3)
  refine ⟨k, s, hs, hs3, ?_⟩
  rw [hxsγ, ← hk]
  exact ((Commute.zpow_left (hcL s hs.2) k).eq).symm

end Decomposition

omit [Finite G] in
theorem inf_le_of_exponent {A T L : Subgroup G} {c : G} (hAF : A ∈ partTwoF G)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAT : A ≤ T) (hc3 : c ^ 3 = 1)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hab : ∀ s ∈ T ⊓ L, ∀ t ∈ T ⊓ L, s * t = t * s) (hexp : ∀ s ∈ T ⊓ L, s ^ 3 = 1) :
    T ⊓ L ≤ A := by
  have hE : CFSG.Assembly.IsElemAbelian 3 (T ⊓ L) :=
    ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
  have hB := isElemAbelian_sup_zpowers hE hc3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLc he.2)
  have hAB : A ≤ (T ⊓ L) ⊔ Subgroup.zpowers c := by
    rw [hAeq]
    exact sup_le le_sup_right (le_sup_of_le_left (inf_le_inf_right L hAT))
  rw [← hAF.2.1 _ hB hAB]
  exact le_sup_left

theorem sylow_facts_of_inf_le {A T L : Subgroup G} {c : G} (hA : IsE27 A) (hcA : c ∈ A)
    (hdec : ∀ x ∈ T, x ^ 3 = 1 → ∃ k : ℤ, ∃ s ∈ T ⊓ L, s ^ 3 = 1 ∧ x = c ^ k * s)
    (hle : T ⊓ L ≤ A) :
    (∀ x ∈ T, x ^ 3 = 1 → ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), ℓ * x * ℓ⁻¹ ∈ A) ∧
    (∀ E : Subgroup G, E ≤ T → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → c ∈ E →
      ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), E.map (MulAut.conj ℓ).toMonoidHom = A) := by
  have hmem : ∀ x ∈ T, x ^ 3 = 1 → x ∈ A := fun x hx hx3 => by
    obtain ⟨k, s, hs, -, rfl⟩ := hdec x hx hx3
    exact mul_mem (zpow_mem hcA k) (hle hs)
  refine ⟨fun x hx hx3 => ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact hmem x hx hx3⟩,
    fun E hET hE hE27 _ => ⟨1, one_mem _, ?_⟩⟩
  rw [map_conj_one]
  exact Subgroup.eq_of_le_of_card_ge (fun e he => hmem e (hET he) (hE.2 e he))
    (by rw [hA.2, hE27])

theorem a7m22_facts (hA7 : KFacts.KS18A7M22) {L : Subgroup G}
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ ∧
      (∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), ∀ k : ℕ, σ ^ 3 ^ k = 1 →
        ∃ q, MulAut.conj q = σ) ∧
      ∀ S : Subgroup G, S ≤ L → IsPGroup 3 S →
        (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) ∧ ∀ s ∈ S, s ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hZ, hinn, hexp, hab⟩ := hA7 (↥L ⧸ aschbacherSolvableCore 3 ↥L) hL
  refine ⟨hZ, fun σ k hσ => ?_, fun S hSL hS3 => ?_⟩
  · obtain ⟨q, hq⟩ := hinn σ ⟨k, hσ⟩
    exact ⟨q, hq.symm⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set S' := S.subgroupOf L with hS'
  have hS'3 : IsPGroup 3 S' := hS3.comap_of_injective L.subtype L.subtype_injective
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hS'3
  have hcomm := hab (S'.map π) (hS'3.map π)
  refine ⟨fun s hs t ht => ?_, fun s hs => ?_⟩
  · have hs' : (⟨s, hSL hs⟩ : ↥L) ∈ S' := hs
    have ht' : (⟨t, hSL ht⟩ : ↥L) ∈ S' := ht
    have h1 : π (⟨s, hSL hs⟩ * ⟨t, hSL ht⟩) = π (⟨t, hSL ht⟩ * ⟨s, hSL hs⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨_, Subgroup.mem_map_of_mem π hs'⟩
        ⟨_, Subgroup.mem_map_of_mem π ht'⟩)
    exact congrArg Subtype.val (hinj (mul_mem hs' ht') (mul_mem ht' hs') h1)
  · have hs' : (⟨s, hSL hs⟩ : ↥L) ∈ S' := hs
    obtain ⟨n, hn⟩ := hS'3 ⟨_, hs'⟩
    have hn' : (⟨s, hSL hs⟩ : ↥L) ^ 3 ^ n = 1 := congrArg Subtype.val hn
    have h3 : π ⟨s, hSL hs⟩ ^ 3 = 1 := hexp _ ⟨n, by rw [← map_pow, hn', map_one]⟩
    have h1 : (⟨s, hSL hs⟩ : ↥L) ^ 3 = 1 :=
      hinj (pow_mem hs' 3) (one_mem S') (by rw [map_pow, h3, map_one])
    exact congrArg Subtype.val h1

theorem exponent_of_j2 (h415 : Sec4.Item4_15) {L S : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hS : IsSylowOf 3 S L) : Nat.card S = 27 ∧ ∀ s ∈ S, s ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hinj : Set.InjOn π ((Q : Subgroup ↥L) : Set ↥L) :=
    injOn_mk_of_isPGroup Nat.prime_three Q.isPGroup'
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Q.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (Q : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 _ hJ Sb _ rfl _ rfl
  refine ⟨?_, ?_⟩
  · rw [← hQ, Subgroup.card_map_of_injective L.subtype_injective, ← card_map_eq_of_injOn π hinj,
      ← hSb]
    exact hHeis.2.1
  · intro s hs
    rw [← hQ] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    have hqS : π q ∈ (Sb : Subgroup _) := hSb ▸ Subgroup.mem_map_of_mem π hq
    have h3 : (⟨π q, hqS⟩ : (Sb : Subgroup _)) ^ 3 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨π q, hqS⟩ : (Sb : Subgroup _))
      rwa [hHeis.2.2] at h
    have h3' : π q ^ 3 = 1 := congrArg Subtype.val h3
    have h1 : q ^ 3 = 1 := hinj (pow_mem hq 3) (one_mem _) (by rw [map_pow, h3', map_one])
    change ((q : ↥L) : G) ^ 3 = 1
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]

theorem sylow_facts_of_j2
    {A T L : Subgroup G} {c : G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hA : IsE27 A) (hAF : A ∈ partTwoF G) (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L) (hc : orderOf c = 3)
    (hT : IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G))) (hAT : A ≤ T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowOf 3 (T ⊓ L) L) :
    (∀ x ∈ T, x ^ 3 = 1 → ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), ℓ * x * ℓ⁻¹ ∈ A) ∧
    (∀ E : Subgroup G, E ≤ T → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → c ∈ E →
      ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), E.map (MulAut.conj ℓ).toMonoidHom = A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcA : c ∈ A := hAeq ▸ (le_sup_left : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨φJ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φJ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  have hinn : ∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), ∀ k : ℕ, σ ^ 3 ^ k = 1 →
      ∃ q, MulAut.conj q = σ := fun σ k hσ =>
    Item134SylowBarProof.mem_range_conj_of_pow_three_pow hJ σ hσ
  have hdec := fun x hx hx3 => exists_zpow_mul_of_pow_eq_one hZ hinn hAF hAeq hLc hT.isPGroup
    hAT hT.le hTL hS (x := x) hx hx3
  obtain ⟨h27, hexp⟩ := exponent_of_j2 h415 hJ hS
  have hzC : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hLc hy)
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hAle : A ≤ Subgroup.zpowers c ⊔ L := by
    rw [hAeq]
    exact sup_le_sup_left inf_le_right _
  have hcTL : c ∉ T ⊓ L := fun h => hcL h.2
  have hconj : ∀ E : Subgroup G, E ≤ Subgroup.zpowers c ⊔ L → c ∈ E → Nat.card E = 27 →
      ∃ ℓ ∈ Subgroup.centralizer ({c} : Set G), E.map (MulAut.conj ℓ).toMonoidHom = A := by
    intro E hE hcE hE27
    obtain ⟨g, hgL, hg⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot h415 hN3
      hJ hzC hcL hc3 hAle hE hcA hcE hA.2 hE27
    refine ⟨g, hLc hgL, ?_⟩
    rw [hg, conjugate, map_conj_map_conj, mul_inv_cancel, map_conj_one]
  refine ⟨fun x hx hx3 => ?_, fun E hET hE hE27 hcE => hconj E ?_ hcE hE27⟩
  · obtain ⟨k, s, hs, hs3, rfl⟩ := hdec x hx hx3
    by_cases hs1 : s = 1
    · refine ⟨1, one_mem _, ?_⟩
      rw [hs1, mul_one, one_mul, inv_one, mul_one]
      exact zpow_mem hcA k
    set X := T ⊓ L with hXdef
    have hX27 : Nat.card X = 27 := h27
    set s' : ↥X := ⟨s, hs⟩ with hs'def
    have hs'3 : Nat.card (Subgroup.zpowers s') = 3 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      refine orderOf_eq_prime (Subtype.ext (by simpa using hs3)) fun h => hs1 ?_
      exact congrArg Subtype.val h
    obtain ⟨K, hK9, hsK⟩ := Sylow.exists_subgroup_card_pow_succ (p := 3) (n := 1)
      (by rw [hX27]; norm_num) hs'3
    set F := K.map X.subtype with hFdef
    have hF9 : Nat.card F = 9 := by
      rw [hFdef, Subgroup.card_map_of_injective X.subtype_injective, hK9]
      norm_num
    have hFX : F ≤ X := Subgroup.map_subtype_le K
    have hsF : s ∈ F := ⟨s', hsK (Subgroup.mem_zpowers s'), rfl⟩
    obtain ⟨-, hE27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc3 hcTL hFX hF9 hexp
      fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hLc (hFX hy).2)).symm
    obtain ⟨ℓ, hℓC, hℓ⟩ := hconj (Subgroup.zpowers c ⊔ F)
      (sup_le le_sup_left (hFX.trans (inf_le_right.trans le_sup_right)))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) hE27
    refine ⟨ℓ, hℓC, ?_⟩
    rw [← hℓ]
    exact ⟨c ^ k * s, mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers c) k))
      (Subgroup.mem_sup_right hsF), rfl⟩
  · intro e he
    obtain ⟨k, s, hs, -, rfl⟩ := hdec e (hET he) (hE.2 e he)
    exact mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers c) k))
      (Subgroup.mem_sup_right hs.2)

end CFSG.RankThree.PartTwo.Sec17.Proof175
