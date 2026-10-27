module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4
import CFSG.RankThree.PartOne.AUTSL.FieldExt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RankBounds
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.Chevalley (graphFixedRootGroup graphFixedPosUnipotent graphFixedRootTorus
  trialityFixedField trialityTorusHom trialityTorusHom_injective_all
  trialityTorusHom_mem_graphFixedRootGroup trialityTorusHom_mem_graphFixedTorus fieldActorHom
  fieldActorHom_apply coe_fieldActor exists_rootDiagUnit_eq_of_mem_torusGroup rootDiagUnit_mul
  rootDiagUnit_one)
open CFSG.Quasithin.H13.Sec53F.TriD4 (borelAutData_d4 entry_rootDiagUnit d4_H_comm d4_H_le d4_sylow)

set_option linter.unusedSectionVars false

theorem uc22s218_d4_not_three_dvd {s : ℕ} (hs : Odd s) : ¬ 3 ∣ 2 ^ s - 1 := by
  obtain ⟨k, rfl⟩ := hs
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have h3 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [h2]
    omega
  generalize 2 ^ (2 * k + 1) = X at h3 ⊢
  omega

theorem uc22s218_d4_not_dvd_index {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hrq : r ∣ q - 1) (hq : 1 ≤ q) :
    ¬ r ∣ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1) * (q + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hq1 : (q : ZMod r) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) r).2 hrq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hq1]
  norm_num
  intro h
  have h12 : ((12 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h12
  have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases r <;> first | omega | exact absurd hr (by norm_num)

theorem uc22s218_d4_index_arith {q m idx N : ℕ} (hq : 1 < q) (hN : N = (q ^ 3 - 1) * (q - 1) * m)
    (hmul : N * idx = ordTrialityD4 q) :
    idx ∣ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1) * (q + 1) := by
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q := by omega
  have h6 : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have h : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h, h1]
    ring
  have h2' : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h, h2]
    ring
  have hA : 0 < q ^ 3 - 1 := by
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hB : 0 < q - 1 := by omega
  have key : (q ^ 3 - 1) * (q - 1) * (m * idx) =
      (q ^ 3 - 1) * (q - 1) * (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1) * (q + 1)) := by
    calc (q ^ 3 - 1) * (q - 1) * (m * idx) = ((q ^ 3 - 1) * (q - 1) * m) * idx := by ring
      _ = ordTrialityD4 q := by rw [← hN]; exact hmul
      _ = _ := by
        unfold ordTrialityD4
        rw [h6, h2']
        ring
  exact Dvd.intro_left m (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hA hB) key)

theorem uc22s218_d4_not_dvd_pow_three {n p : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ 2 ^ n - 1)
    (h2 : ¬ p ∣ 2 ^ (2 * n) + 2 ^ n + 1) : ¬ p ∣ 2 ^ (3 * n) - 1 := by
  have hfac : 2 ^ (3 * n) - 1 = (2 ^ n - 1) * (2 ^ (2 * n) + 2 ^ n + 1) := by
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
    have e2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e1, e2]
    generalize 2 ^ n = x at h ⊢
    have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ h
    zify [h, h3]
    ring
  rw [hfac]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact h1 h
  · exact h2 h


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "U₀" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
local notation "H₁" => graphFixedRootTorus TwistTag.D4 K σ.toRingHom
local notation "𝒰" => Subgroup.subgroupOf U₀ C₀
local notation "ℋ" => Subgroup.subgroupOf H₁ C₀
local notation "𝔽" => MonoidHom.range (fieldActorHom (t := TwistTag.D4) σ)

theorem uc22s218_d4_rootDiagUnit_pow {τ : CFSG.Blueprint.Chevalley.Tag} (b : Fin τ.rank → Kˣ)
    (m : ℕ) : rootDiagUnit τ b ^ m = rootDiagUnit τ (b ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ m ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]

theorem uc22s218_d4_exists_rootDiagUnit {h : ↥C₀} (hh : h ∈ ℋ) :
    ∃ l : Fin TwistTag.D4.tag.rank → Kˣ,
      (h : CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag l := by
  have hh' := Subgroup.mem_subgroupOf.1 hh
  exact exists_rootDiagUnit_eq_of_mem_torusGroup
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh').1).1

theorem uc22s218_d4_fieldAut_pow {φ : MulAut ↥C₀} (hφ : φ ∈ 𝔽) :
    ∃ j : ℕ, ∀ h ∈ ℋ, φ h = h ^ 2 ^ j := by
  obtain ⟨δ, rfl⟩ := hφ
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartOne.AUTSL.exists_ringEquiv_eq_pow_two δ
  refine ⟨j, fun h hh => ?_⟩
  obtain ⟨l, hl⟩ := uc22s218_d4_exists_rootDiagUnit σ hh
  have e1 : ∀ w : Kˣ, Units.map δ.toRingHom.toMonoidHom w = w ^ 2 ^ j := fun w => by
    ext
    simp [hj]
  apply Subtype.ext
  rw [fieldActorHom_apply, coe_fieldActor, Subgroup.coe_pow, hl, entry_rootDiagUnit,
    uc22s218_d4_rootDiagUnit_pow]
  exact congrArg _ (funext fun i => e1 (l i))

theorem uc22s218_d4_torus_pow {f : ℕ} (hK : Nat.card K = 2 ^ (3 * f)) {h : ↥C₀} (hh : h ∈ ℋ) :
    h ^ (2 ^ (3 * f) - 1) = 1 := by
  obtain ⟨l, hl⟩ := uc22s218_d4_exists_rootDiagUnit σ hh
  have hu : ∀ w : Kˣ, w ^ (2 ^ (3 * f) - 1) = 1 := fun w => by
    rw [← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  apply Subtype.ext
  rw [Subgroup.coe_pow, hl, uc22s218_d4_rootDiagUnit_pow,
    show l ^ (2 ^ (3 * f) - 1) = 1 from funext fun i => hu (l i), rootDiagUnit_one]
  rfl

theorem uc22s218_d4_exists_torusHom (hσ3 : σ ^ 3 = 1) :
    ∃ φ : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →* ↥C₀, Function.Injective φ ∧
      ∀ p, φ p ∈ ℋ := by
  refine ⟨(trialityTorusHom σ).codRestrict _ (trialityTorusHom_mem_graphFixedRootGroup hσ3),
    fun p q h => trialityTorusHom_injective_all hσ3 (congrArg Subtype.val h), fun p => ?_⟩
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
    ⟨trialityTorusHom_mem_graphFixedTorus hσ3 p, trialityTorusHom_mem_graphFixedRootGroup hσ3 p⟩)

theorem uc22s218_d4_exists_orderOf_torus {s f : ℕ} (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = 2 ^ (3 * f)) (hsf : s ∣ f) :
    ∃ d ∈ ℋ, orderOf d = 2 ^ s - 1 := by
  obtain ⟨φ, hφ, hmem⟩ := uc22s218_d4_exists_torusHom σ hσ3
  obtain ⟨t, ht⟩ := uc22p218c_exists_orderOf_units hK (Dvd.dvd.mul_left hsf 3)
  refine ⟨φ (t, 1), hmem _, ?_⟩
  rw [orderOf_injective φ hφ, Prod.orderOf, orderOf_one, Nat.lcm_one_right, ht]

theorem uc22s218_d4_exists_prime_orderOf_torus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = 2 ^ (3 * f)) (hℓK : ℓ ∣ 2 ^ (3 * f) - 1) :
    ∃ d ∈ ℋ, orderOf d = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨φ, hφ, hmem⟩ := uc22s218_d4_exists_torusHom σ hσ3
  have hℓK' : ℓ ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hℓK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ hℓK'
  refine ⟨φ (ζ, 1), hmem _, ?_⟩
  rw [orderOf_injective φ hφ, Prod.orderOf, orderOf_one, Nat.lcm_one_right, hζ]

theorem uc22s218_d4_fieldBorelData_model {f : ℕ} (hf : 1 ≤ f) (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    FieldBorelData f (2 ^ (3 * f) - 1) 𝒰 ℋ 𝔽 where
  borel := borelAutData_d4 σ hf hK hσ
  pow := fun _ hφ => uc22s218_d4_fieldAut_pow σ hφ
  exp := fun _ hh => uc22s218_d4_torus_pow σ (by rw [hK, ← pow_mul, mul_comm]) hh
  exists_d := fun _ hsf => uc22s218_d4_exists_orderOf_torus σ hσ3
    (by rw [hK, ← pow_mul, mul_comm]) hsf

theorem uc22s218_d4_model_elemAbelian {ℓ f : ℕ} (hℓ : ℓ.Prime) (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f)
    (hℓf : ℓ ∣ 2 ^ f - 1) :
    ∃ A : Subgroup ↥C₀, A ≤ ℋ ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨φ, hφ, hmem⟩ := uc22s218_d4_exists_torusHom σ hσ3
  have hℓK : ℓ ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, show (2 ^ f) ^ 3 = 2 ^ (3 * f) by rw [← pow_mul, mul_comm]]
    exact hℓf.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left 3 rfl))
  have hℓk : ℓ ∣ Nat.card (trialityFixedField K σ.toRingHom)ˣ := by
    rw [Nat.card_units, hk]
    exact hℓf
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ hℓK
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K σ.toRingHom)ˣ) ℓ
    hℓk
  let g : (↥(zpowers ζ) × ↥(zpowers ξ)) →* ↥C₀ :=
    φ.comp ((zpowers ζ).subtype.prodMap (zpowers ξ).subtype)
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 := hφ hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  have hpowζ : ∀ x : ↥(zpowers ζ), x ^ ℓ = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  have hpowξ : ∀ x : ↥(zpowers ξ), x ^ ℓ = 1 := fun x => by
    rw [← hξ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  refine ⟨(⊤ : Subgroup (↥(zpowers ζ) × ↥(zpowers ξ))).map g, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hmem _
  · exact CFSG.SectionRank.isElemAbelian_map
      ⟨inferInstance, fun x _ => Prod.ext (hpowζ x.1) (hpowξ x.2)⟩ g
  · rw [Subgroup.card_map_of_injective hg, Subgroup.card_top, Nat.card_prod, Nat.card_zpowers, hζ,
      Nat.card_zpowers, hξ, sq]

theorem uc22s218_d4_model_index_dvd {f : ℕ} (hf : 1 ≤ f) (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f) :
    (normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀)).index ∣
      (2 ^ f) ^ 12 * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 3 + 1) * (2 ^ f + 1) := by
  obtain ⟨φ, hφ, hmem⟩ := uc22s218_d4_exists_torusHom σ hσ3
  have hC : Nat.card ↥C₀ = ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom hσ
  have hmul := Subgroup.card_mul_index (normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀))
  rw [hC] at hmul
  have hHN : Nat.card ℋ ∣ Nat.card (normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀)) :=
    Subgroup.card_dvd_of_le (d4_H_le σ)
  have hrange : φ.range ≤ ℋ := by
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hT : Nat.card (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ∣ Nat.card ℋ :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm ▸ Subgroup.card_dvd_of_le hrange
  rw [Nat.card_prod, Nat.card_units, Nat.card_units, hK, hk] at hT
  obtain ⟨m, hm⟩ := hT.trans hHN
  exact uc22s218_d4_index_arith (Nat.one_lt_two_pow (by omega)) hm hmul

theorem uc22s218_d4_model_not_dvd_card_sylow {f r : ℕ} (hf : 1 ≤ f) (hσ3 : σ ^ 3 = 1)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrf : r ∣ 2 ^ f - 1) : ¬ r ∣ Nat.card (Sylow 2 ↥C₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have hU : IsSylowTwoOf 𝒰 ⊤ := d4_sylow σ
  have hidx : ¬ 2 ∣ Subgroup.index 𝒰 := by
    have h := hU.2.2
    rwa [show Subgroup.index (Subgroup.subgroupOf 𝒰 ⊤) = Subgroup.index 𝒰 from
      Subgroup.relIndex_top_right _] at h
  let P : Sylow 2 ↥C₀ := hU.2.1.toSylow hidx
  have hP : (P : Subgroup ↥C₀) = 𝒰 := IsPGroup.toSylow_coe hU.2.1 hidx
  rw [Sylow.card_eq_index_normalizer P]
  have hnorm : normalizer (P : Set ↥C₀) = normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀) := by
    rw [← hP]
    rfl
  rw [hnorm]
  intro hdvd
  exact uc22s218_d4_not_dvd_index hr hr2 hr3 hrf Nat.one_le_two_pow
    (hdvd.trans (uc22s218_d4_model_index_dvd σ hf hσ3 hK hσ hk))

end Model

section Rank

theorem uc22s218_d4_exists_model {Y : Type} [Group Y] {n : ℕ} (hY : Is3D4 Y n) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K),
      σ ^ 3 = 1 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧ Nat.card K = (2 ^ n) ^ 3 ∧
        Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n ∧
          Nonempty (Y ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hX := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨K, hF, hFin, hcp, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.TrialityCover.triality_model hX.1.2.1 hX.2
  exact ⟨hX.1.2.1, K, hF, hFin, hcp, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩

theorem uc22s218_d4_fieldBorel {Y : Type} [Group Y] {n : ℕ} (hY : Is3D4 Y n) :
    FieldBorel Y n (2 ^ (3 * n) - 1) := by
  obtain ⟨hn, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  exact FieldBorel.of_mulEquiv (Y := ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    ⟨_, _, _, uc22s218_d4_fieldBorelData_model σ hn hσ3 hK hσ⟩ e.symm

theorem uc22s218_d4_torus {Y : Type} [Group Y] {n : ℕ} (hY : Is3D4 Y n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ (3 * n) - 1 → ∃ y ∈ T, orderOf y = ℓ := by
  obtain ⟨hn, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  refine ⟨((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map e.symm.toMonoidHom, ?_,
    fun ℓ hℓ hℓn => ?_, fun ℓ hℓ hℓn => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, d4_H_comm σ x hx y hy]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_d4_model_elemAbelian σ hℓ hσ3 hK hk hℓn
    refine ⟨A.map e.symm.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]
  · obtain ⟨d, hdH, hdo⟩ := uc22s218_d4_exists_prime_orderOf_torus σ hℓ hσ3
      (by rw [hK, ← pow_mul, mul_comm]) hℓn
    exact ⟨e.symm d, ⟨d, hdH, rfl⟩, by rw [MulEquiv.orderOf_eq, hdo]⟩

theorem uc22s218_d4_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : Is3D4 Y n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) : ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨hn, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv Y e.toEquiv
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  exact uc22s218_d4_model_not_dvd_card_sylow σ hn hσ3 hK hσ hk hr
    (uc22p218c_ne_two_of_dvd hs.pos hrs) (fun h => uc22s218_d4_not_three_dvd hs (h ▸ hrs))
    (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))

end Rank

section RankTwo


theorem uc22s218_d4_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : Is3D4 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pRank_le_two_of_is3D4 hY hp hp2

theorem uc22s218_d4_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : Is3D4 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  refine le_antisymm (uc22s218_d4_pRank_le_two hY hr (uc22p218c_ne_two_of_dvd hs.pos hrs)) ?_
  obtain ⟨T, -, hT, -⟩ := uc22s218_d4_torus hY
  obtain ⟨A, -, hAe, hAc⟩ := hT r hr (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
  exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc

theorem torusFacts218_3D4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : Is3D4 Y n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ n - 1)
      (fun p => ¬ p ∣ 2 ^ n - 1 ∧ ¬ p ∣ 2 ^ (2 * n) + 2 ^ n + 1) :=
  torusFacts218_of_fieldBorel (E := 2 ^ (3 * n) - 1) (uc22s218_d4_fieldBorel hY)
    (fun _ hsn _ hrs => hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
    (fun hp _ hout => uc22s218_d4_not_dvd_pow_three hp hout.1 hout.2)
    (let ⟨T, hTc, hTE, _⟩ := uc22s218_d4_torus hY; ⟨T, hTc, hTE⟩)
    (fun hs hsn hr hrs => uc22s218_d4_pRank_eq_two hY hs hsn hr hrs)
    (fun hs hsn hr hrs => uc22s218_d4_not_dvd_card_sylow hY hs hsn hr hrs)
    (fun hp hp2 _ => uc22s218_d4_pRank_le_two hY hp hp2)

end RankTwo

end CFSG.LocalAnalysis.UniquenessCase.UC22
