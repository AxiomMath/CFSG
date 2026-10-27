module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
import CFSG.LieType.Chevalley.GraphFixedRootNormal
import CFSG.LieType.Steinberg.TwistedE6.Clause0
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime
import CFSG.LieType.Simplicity.Exceptional
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny in
theorem tableZ_cover
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (h3 : 3 ∣ 2 ^ n + 1)
    {R : Type} [Group R] (e : R ≃* ↥(twistedE6RootGroup K σ)) [Finite (HopfCover R)]
    (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R) :
    ∃ κ : HopfCover R →* ↥(TwistedE6.fixedGroup K σ.toRingHom),
      Function.Surjective κ ∧
      (∀ x, e6IsogenyFixed σ.toRingHom (κ x) =
        ((e (θ (QuotientGroup.mk x)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)) ∧
      ∀ x, x ∈ κ.ker ↔ x ∈ Subgroup.center (HopfCover R) ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card
      (k := K) (θ := σ.toRingHom) (q := 2 ^ n) hK hσ
  have hk4 : 4 ≤ Nat.card K := by
    rw [hK]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
  have hcomm : ⁅CFSG.Blueprint.twistedFixedGroup .E6 K σ.toRingHom,
      CFSG.Blueprint.twistedFixedGroup .E6 K σ.toRingHom⁆ = twistedE6RootGroup K σ := by
    refine le_antisymm
      (commutator_twistedFixedGroup_le (t := .E6) (σ := σ.toRingHom) σ.surjective) ?_
    haveI : Group.IsPerfect ↥(twistedE6RootGroup K σ) :=
      ⟨commutator_twistedE6RootGroup_eq_top (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ⟩
    rw [← Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect ↥(twistedE6RootGroup K σ))]
    exact Subgroup.commutator_mono (graphFixedRootGroup_le _ _ _) (graphFixedRootGroup_le _ _ _)
  haveI hC₀perf : Group.IsPerfect ↥(twistedE6RootGroup K σ) :=
    ⟨commutator_twistedE6RootGroup_eq_top (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ⟩
  haveI hRperf : Group.IsPerfect R :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI hUperf : Group.IsPerfect ↥(TwistedE6.fixedGroup K σ.toRingHom) :=
    CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card σ.toRingHom hθθ hk4
  haveI hHperf : Group.IsPerfect (HopfCover R) := hopfCover_isPerfect
  have hHcom : commutator (HopfCover R) = ⊤ := Group.IsPerfect.commutator_eq_top
  let τ := CFSG.LieType.Simplicity.twistedIsogeny σ.toRingHom hθθ hk4
  let π₁ : ↥(TwistedE6.fixedGroup K σ.toRingHom) →* ↥(twistedE6RootGroup K σ) :=
    (MulEquiv.subgroupCongr hcomm).toMonoidHom.comp τ
  have hπ₁coe : ∀ g, (π₁ g : ModGL TwistTag.E6.tag K) = e6IsogenyFixed σ.toRingHom g := by
    intro g
    change (((MulEquiv.subgroupCongr hcomm) (τ g) : ↥(twistedE6RootGroup K σ)) :
      ModGL TwistTag.E6.tag K) = e6IsogenyFixed σ.toRingHom g
    rw [MulEquiv.subgroupCongr_apply, CFSG.LieType.Simplicity.coe_twistedIsogeny,
      e6IsogenyFixed_apply]
  have hπ₁surj : Function.Surjective π₁ :=
    (MulEquiv.subgroupCongr hcomm).surjective.comp
      (CFSG.LieType.Simplicity.twistedIsogeny_surjective σ.toRingHom hθθ hk4)
  have hπ₁ker : π₁.ker = Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom) := by
    have h2 : π₁.ker = τ.ker := by
      ext x
      show (MulEquiv.subgroupCongr hcomm) (τ x) = 1 ↔ τ x = 1
      exact ⟨fun hx => (MulEquiv.subgroupCongr hcomm).injective (hx.trans (map_one _).symm),
        fun hx => by rw [hx, map_one]⟩
    rw [h2]
    exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center
      (θ := σ.toRingHom) hθθ hk4
  let p : ↥(TwistedE6.fixedGroup K σ.toRingHom) →* R := e.symm.toMonoidHom.comp π₁
  have hp : Function.Surjective p := e.symm.surjective.comp hπ₁surj
  have hpker : p.ker = Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom) := by
    have h1 : p.ker = π₁.ker := by
      ext x
      show e.symm (π₁ x) = 1 ↔ π₁ x = 1
      exact ⟨fun hx => e.symm.injective (hx.trans (map_one _).symm),
        fun hx => by rw [hx, map_one]⟩
    rw [h1, hπ₁ker]
  have hker : p.ker ≤ Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom) := le_of_eq hpker
  let κ₀ : HopfCover R →* ↥(TwistedE6.fixedGroup K σ.toRingHom) := hopfLift p hp hker
  have hκ₀ : ∀ x, p (κ₀ x) = hopfCoverMap R x := fun x =>
    DFunLike.congr_fun (comp_hopfLift p hp hker) x
  have hκ₀surj : Function.Surjective κ₀ := hopfLift_surjective p hp hker
  have hκ₀center : κ₀.ker ≤ Subgroup.center (HopfCover R) := by
    intro z hz
    apply hopfMultiplier_le_center
    rw [hopfMultiplier, MonoidHom.mem_ker, ← hκ₀ z, MonoidHom.mem_ker.mp hz, map_one]
  obtain ⟨-, -, θC, κ', lift, hκ'surj, hκ'ker, hκ'eq, hlift, hkg⟩ :=
    CFSG.StandardType.KGUniv.exists_universal_cover_lift hHcom θ
  have hκ'bij : Function.Bijective κ' :=
    ⟨(Finite.injective_iff_surjective (f := fun x => κ' x)).mpr hκ'surj, hκ'surj⟩
  let κ'bi : HopfCover R ≃* HopfCover R := MulEquiv.ofBijective κ' hκ'bij
  have hκ'bi : ∀ x, κ'bi x = κ' x := fun x => MulEquiv.ofBijective_apply κ' hκ'bij x
  let κ : HopfCover R →* ↥(TwistedE6.fixedGroup K σ.toRingHom) := κ₀.comp κ'bi.symm.toMonoidHom
  have hκeq : ∀ x, e6IsogenyFixed σ.toRingHom (κ x) =
      ((e (θ (QuotientGroup.mk x)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) := by
    intro x
    have hpx : p (κ x) = θ (QuotientGroup.mk x) := by
      have hy : κ' (κ'bi.symm x) = x := by
        rw [← hκ'bi (κ'bi.symm x), MulEquiv.apply_symm_apply]
      calc p (κ x) = hopfCoverMap R (κ'bi.symm x) := hκ₀ (κ'bi.symm x)
        _ = θ (QuotientGroup.mk (κ' (κ'bi.symm x))) := (hκ'eq (κ'bi.symm x)).symm
        _ = θ (QuotientGroup.mk x) := by rw [hy]
    calc e6IsogenyFixed σ.toRingHom (κ x)
        = ((π₁ (κ x) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) :=
          (hπ₁coe (κ x)).symm
      _ = ((e (p (κ x)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) := by
          rw [show p (κ x) = e.symm (π₁ (κ x)) from rfl, e.apply_symm_apply]
      _ = ((e (θ (QuotientGroup.mk x)) : ↥(twistedE6RootGroup K σ)) :
            ModGL TwistTag.E6.tag K) := by rw [hpx]
  refine ⟨κ, hκ₀surj.comp κ'bi.symm.surjective, hκeq, ?_⟩
  intro x
  constructor
  · intro hx
    have hy : κ'bi.symm x ∈ κ₀.ker := by
      change κ₀ (κ'bi.symm x) = 1
      exact hx
    refine ⟨?_, ?_⟩
    · have hyc : κ'bi.symm x ∈ Subgroup.center (HopfCover R) := hκ₀center hy
      rw [Subgroup.mem_center_iff] at hyc ⊢
      intro y
      obtain ⟨w, rfl⟩ := κ'bi.surjective y
      have hxeq : x = κ'bi (κ'bi.symm x) := (MulEquiv.apply_symm_apply κ'bi x).symm
      rw [hxeq]
      calc κ'bi w * κ'bi (κ'bi.symm x)
          = κ'bi (w * κ'bi.symm x) := (map_mul κ'bi _ _).symm
        _ = κ'bi (κ'bi.symm x * w) := by rw [hyc w]
        _ = κ'bi (κ'bi.symm x) * κ'bi w := map_mul κ'bi _ _
    · have hsplit : ∀ (E : Type) [Group E] [Finite E]
          (π : E →* ↥(TwistedE6.fixedGroup K σ.toRingHom)),
          Function.Surjective π → π.ker ≤ Subgroup.center E →
          Nat.Coprime 2 (Nat.card π.ker) →
          ∃ s : ↥(TwistedE6.fixedGroup K σ.toRingHom) →* E, ∀ h, π (s h) = h :=
        fun E _ _ π hπ hc hcop =>
          CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_coprime
            (k := K) (θ := σ.toRingHom) hθθ (p := 2) hπ hc hcop
      have hnoTorsion : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ z ∈ κ₀.ker, z ^ q = 1 → z = 1 := by
        intro q hq hq2
        exact CFSG.StandardType.StdSubRestU.noTorsion_ker_of_section
          (q := MonoidHom.id _) (hq := fun y => ⟨y, rfl⟩) (hsplit := hsplit)
          hq hq2 (fun z hz _ => by
            rw [MonoidHom.ker_id] at hz
            exact Subgroup.mem_bot.mp hz) hκ₀surj hκ₀center hHcom
      have hprime : ∀ d : ℕ, d.Prime → d ∣ orderOf (κ'bi.symm x) → d = 2 := by
        intro d hd hdvd
        by_contra hd2
        have hdpos : 0 < orderOf (κ'bi.symm x) := orderOf_pos _
        have hdivpos : 0 < orderOf (κ'bi.symm x) / d :=
          Nat.div_pos (Nat.le_of_dvd hdpos hdvd) hd.pos
        have hzord : orderOf ((κ'bi.symm x) ^ (orderOf (κ'bi.symm x) / d)) = d := by
          rw [orderOf_pow_of_dvd hdivpos.ne' (Nat.div_dvd_of_dvd hdvd),
            Nat.div_div_self hdvd (orderOf_pos _).ne']
        have hmem : (κ'bi.symm x) ^ (orderOf (κ'bi.symm x) / d) ∈ κ₀.ker :=
          κ₀.ker.pow_mem hy _
        have hp1 : ((κ'bi.symm x) ^ (orderOf (κ'bi.symm x) / d)) ^ d = 1 := by
          have := pow_orderOf_eq_one ((κ'bi.symm x) ^ (orderOf (κ'bi.symm x) / d))
          rwa [hzord] at this
        have h1 := hnoTorsion d hd hd2 _ hmem hp1
        rw [h1, orderOf_one] at hzord
        exact hd.ne_one hzord.symm
      have hpow : ∃ k, (κ'bi.symm x) ^ (2 ^ k) = 1 := by
        obtain ⟨k, hk⟩ : ∃ k, orderOf (κ'bi.symm x) = 2 ^ k :=
          ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) (orderOf_pos _).ne'
            (fun {d} hd hdvd => hprime d hd hdvd)⟩
        exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one _⟩
      obtain ⟨k, hk⟩ := hpow
      refine ⟨k, ?_⟩
      have hxeq : x = κ'bi (κ'bi.symm x) := (MulEquiv.apply_symm_apply κ'bi x).symm
      rw [hxeq, ← map_pow, hk, map_one]
  · rintro ⟨hxcent, k, hxk⟩
    have hmk : (QuotientGroup.mk x : HopfCover R ⧸ Subgroup.center (HopfCover R)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hxcent
    have hmem₁ : κ x ∈ π₁.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (π₁ (κ x) : ModGL TwistTag.E6.tag K) = 1
      rw [hπ₁coe (κ x), hκeq x, hmk, map_one, map_one]
      rfl
    have hmemc : κ x ∈ Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom) := by
      rw [← hπ₁ker]; exact hmem₁
    have hxk' : (κ x) ^ (2 ^ k) = 1 := by
      rw [← map_pow, hxk, map_one]
    have hdiv3 : orderOf (κ x) ∣ 3 := by
      have h1 : orderOf (κ x) ∣
          Nat.card (Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom)) := by
        simpa only [Subgroup.orderOf_mk] using
          orderOf_dvd_natCard (⟨κ x, hmemc⟩ : Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom))
      rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
        (k := K) (θ := σ.toRingHom) (q := 2 ^ n) hK hσ).1, Nat.gcd_eq_left h3] at h1
      exact h1
    have hdiv2 : orderOf (κ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk'
    have hcop : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
    have hone : orderOf (κ x) = 1 := by
      have hd : orderOf (κ x) ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hdiv3 hdiv2
      rw [hcop.gcd_eq_one] at hd
      exact Nat.dvd_one.mp hd
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    exact hone

end CFSG.StandardType.TablePThreeKG

end
