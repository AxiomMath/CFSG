module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Perp
public import CFSG.Quasithin.Background.SmithB42D4Inv
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Quasithin.Background.SmithB42D4Main
import CFSG.Quasithin.Background.SmithB42D4Gen
import CFSG.Quasithin.Background.SmithB42D4Weyl
import CFSG.Quasithin.Background.FixVLattice
import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.Background.RonanH143Main
public import CFSG.Quasithin.Background.RonanH154Vocab
public import CFSG.Quasithin.Background.RonanH155Vocab
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Quasithin.B42D4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4


section Torus

variable {K : Type} [Field K] {σ : K ≃+* K}

local notation "kk" => trialityFixedField K σ.toRingHom

theorem trialityTorusHom_fst (a : Kˣ) :
    trialityTorusHom σ (a, 1) = trialityOuterTorus K σ a := by
  rw [trialityTorusHom_apply, trialityMiddleTorus, map_one, torusElt_one, mul_one]

theorem trialityTorusHom_snd (b : kkˣ) :
    trialityTorusHom σ (1, b) = trialityMiddleTorus K σ b := by
  rw [trialityTorusHom_apply, trialityOuterTorus_eq]
  simp only [map_one, torusElt_one, one_mul]

theorem trialityTorusHom_eq_mul (a : Kˣ) (b : kkˣ) :
    trialityTorusHom σ (a, b) = trialityTorusHom σ (a, 1) * trialityTorusHom σ (1, b) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem nA_conj_trialityTorusHom (a : Kˣ) (b : kkˣ) :
    nA K * trialityTorusHom σ (a, b) * (nA K)⁻¹ =
      trialityTorusHom σ (a⁻¹ * trialityFixedUnit K σ b, b) := by
  rw [trialityTorusHom_eq_mul, conj_mul2, trialityTorusHom_fst, trialityTorusHom_snd]
  change trialityOuterRep K * _ * (trialityOuterRep K)⁻¹ *
    (trialityOuterRep K * _ * (trialityOuterRep K)⁻¹) = _
  rw [trialityOuterRep_conj_outer, trialityOuterRep_conj_middle, ← trialityTorusHom_fst,
    ← trialityTorusHom_fst, ← trialityTorusHom_snd, ← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]

theorem nB_conj_trialityTorusHom (hσ : σ ^ 3 = 1) (a : Kˣ) (b : kkˣ) :
    nB K * trialityTorusHom σ (a, b) * (nB K)⁻¹ =
      trialityTorusHom σ (a, trialityNorm σ hσ a * b⁻¹) := by
  rw [trialityTorusHom_eq_mul, conj_mul2, trialityTorusHom_fst, trialityTorusHom_snd]
  change trialityMiddleRep K * _ * (trialityMiddleRep K)⁻¹ *
    (trialityMiddleRep K * _ * (trialityMiddleRep K)⁻¹) = _
  rw [trialityMiddleRep_conj_outer hσ, trialityMiddleRep_conj_middle, ← trialityTorusHom_fst,
    ← trialityTorusHom_snd, ← trialityTorusHom_snd, ← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]

theorem trialityNorm_trialityFixedUnit (hσ : σ ^ 3 = 1) (b : kkˣ) :
    trialityNorm σ hσ (trialityFixedUnit K σ b) = b ^ 3 := by
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  refine hinj (Units.ext ?_)
  rw [coe_trialityNorm, map_pow, Units.val_pow_eq_pow_val]
  simp only [sigma_trialityFixedUnit]
  ring

end Torus

section Commute
variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

omit [CharP K 2] in
theorem orbitRankOneHom_range_le (a : Fin TwistTag.D4.foldedTag.rank) :
    (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range ≤ C₀ := by
  rw [orbitRankOneHom_range, graphFixedRootGroup_eq_iSup_orbitRankOneGroup σ.surjective]
  exact le_iSup (orbitRankOneGroup TwistTag.D4 K σ.toRingHom) a

theorem commute_of_mem_orbitRankOneHom_zero {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h₀ : d4CommB α d4E0 = true) (h₁ : d4CommB α d4E1 = true) (h₃ : d4CommB α d4E3 = true)
    (h₀' : d4CommB α (-d4E0) = true) (h₁' : d4CommB α (-d4E1) = true)
    (h₃' : d4CommB α (-d4E3) = true) (c : K) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩).range) :
    Commute (Xr α c) g := by
  rw [orbitRankOneHom_range] at hg
  refine Subgroup.closure_induction (p := fun g _ => Commute (Xr α c) g) ?_ ?_ ?_ ?_ hg
  · rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · dsimp only
      rw [orbitX_zero_eq, coe_ox₁_eq]
      exact commute_Xr_prod3 h₀ h₁ h₃ c _ _ _
    · dsimp only
      rw [orbitY_zero_eq, nx₁]
      exact commute_Xr_prod3 h₀' h₁' h₃' c _ _ _
  · exact Commute.one_right _
  · intro x y _ _ hx hy
    exact hx.mul_right hy
  · intro x _ hx
    exact hx.inv_right

end Commute

section Long

variable {f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "kk" => trialityFixedField K σ.toRingHom

include hK hσ in
theorem map_orbitRankOneHom_le_perpSub (hf : 1 ≤ f) {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (ψ : ↥C₀ →* MulAut V) (hψ : Function.Injective ψ)
    (hlong : ∀ x : ↥C₀, ConjC σ (x : ModGL TwistTag.D4.tag K) (Xr d4H 1) →
      (fixV (Subgroup.zpowers (ψ x))).index < 2 ^ (6 * f))
    {x : ↥C₀} (hx : ConjC σ (x : ModGL TwistTag.D4.tag K) (Xr d4H 1))
    (hc : ∀ g ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩).range,
      Commute (x : ModGL TwistTag.D4.tag K) g) :
    ((orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩).range.subgroupOf C₀).map ψ ≤
      perpSub (ψ x) := by
  have : CharP K 2 := charP_two_of_card hf hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  set R0 := orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ with hR0
  have hR0C : R0.range ≤ C₀ := orbitRankOneHom_range_le σ _
  have eM : ↥((R0.range.subgroupOf C₀).map ψ) ≃*
      SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :=
    ((Subgroup.equivMapOfInjective _ ψ hψ).symm.trans
      (Subgroup.subgroupOfEquivOfLe hR0C)).trans
      (MonoidHom.ofInjective (orbitRankOneHom_injective_D4 hσ3' _)).symm
  have hcardF : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) = 2 ^ (3 * f) := by
    rw [card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ c),
      show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide, ← pow_mul, mul_comm]
  refine le_perpSub_of_sl2 hV hcardF (by omega) eM ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hc g (Subgroup.mem_subgroupOf.1 hg)).eq.symm)
  · rw [show 2 * (3 * f) = 6 * f by ring]
    exact hlong x hx

omit
  [Finite K] in
theorem two_pow_six_mul_le_index_of_long {V : Type*} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} (φ : ↥L ≃* ↥C₀) {y : ↥L}
    (hy : ConjC σ ((φ y : C₀) : ModGL TwistTag.D4.tag K) (Xr d4H 1))
    (h : ∀ ψ : ↥C₀ →* MulAut V, Function.Injective ψ →
      (∀ x : ↥C₀, ConjC σ (x : ModGL TwistTag.D4.tag K) (Xr d4H 1) →
        (fixV (Subgroup.zpowers (ψ x))).index < 2 ^ (6 * f)) → False) :
    2 ^ (6 * f) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  set ψ : ↥C₀ →* MulAut V := L.subtype.comp φ.symm.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.symm.injective
  by_contra hlt
  push Not at hlt
  refine h ψ hψ fun x hx => ?_
  obtain ⟨g, hg, hgy⟩ := hy
  obtain ⟨g', hg', hgx⟩ := hx
  have e : x = ((⟨g', hg'⟩ : ↥C₀)⁻¹ * ⟨g, hg⟩) * φ y * ((⟨g', hg'⟩ : ↥C₀)⁻¹ * ⟨g, hg⟩)⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (x : ModGL TwistTag.D4.tag K) = g'⁻¹ * (g' * x * g'⁻¹) * g' := by group
      _ = g'⁻¹ * (g * (φ y : ModGL TwistTag.D4.tag K) * g⁻¹) * g' := by rw [hgx, hgy]
      _ = _ := by group
  rw [e, map_mul, map_mul, map_inv, FixVLat.index_fixV_zpowers_conj]
  show (fixV (Subgroup.zpowers ((φ.symm (φ y) : ↥L) : MulAut V))).index < _
  rw [MulEquiv.symm_apply_apply]
  exact hlt

include hK hσ in
theorem two_pow_six_mul_le_index_long (hf : 2 ≤ f) {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (φ : ↥L ≃* ↥C₀) {y : ↥L}
    (hy : ConjC σ ((φ y : C₀) : ModGL TwistTag.D4.tag K) (Xr d4H 1)) :
    2 ^ (6 * f) ≤ (fixV (Subgroup.zpowers (y : MulAut V))).index := by
  classical
  refine two_pow_six_mul_le_index_of_long σ φ hy fun ψ hψ hlong => ?_
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have hψconj : ∀ g x : ↥C₀, (fixV (Subgroup.zpowers (ψ (g * x * g⁻¹)))).index =
      (fixV (Subgroup.zpowers (ψ x))).index := fun g x => by
    rw [map_mul, map_mul, map_inv, FixVLat.index_fixV_zpowers_conj]
  have hHmem : ∀ c : K, σ c = c → Xr d4H c ∈ C₀ := fun c hc => Xr_H_mem_C0 σ hσ3 hc
  have hnW0 : ∀ c : K, nW0 K * Xr d4H c * (nW0 K)⁻¹ = Xr (-d4H) c := fun c => by
    rw [nW0_conj (by decide +kernel), w0_neg (by simp)]
  have hnHmem : ∀ c : K, σ c = c → Xr (-d4H) c ∈ C₀ := fun c hc => by
    rw [← hnW0]
    exact mul_mem (mul_mem (nW0_mem σ) (hHmem c hc)) (inv_mem (nW0_mem σ))
  have hHconj : ∀ c : K, σ c = c → c ≠ 0 → ConjC σ (Xr d4H c) (Xr d4H 1) :=
    fun c hc hc0 => H_conj_one σ hσ3 hc hc0
  have hnHconj : ∀ c : K, σ c = c → c ≠ 0 → ConjC σ (Xr (-d4H) c) (Xr d4H 1) :=
    fun c hc hc0 => ConjC.trans σ ⟨(nW0 K)⁻¹, inv_mem (nW0_mem σ), by rw [← hnW0]; group⟩
      (hHconj c hc hc0)
  set R0 := orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ with hR0
  set M : Subgroup (MulAut V) := (R0.range.subgroupOf C₀).map ψ with hMdef
  have hperp : ∀ x : ↥C₀, ConjC σ (x : ModGL TwistTag.D4.tag K) (Xr d4H 1) →
      (∀ g ∈ R0.range, Commute (x : ModGL TwistTag.D4.tag K) g) → M ≤ perpSub (ψ x) :=
    fun x hx hc => map_orbitRankOneHom_le_perpSub hK σ hσ (by omega) hV ψ hψ hlong hx hc
  have hcommH : ∀ c : K, ∀ g ∈ R0.range, Commute (Xr d4H c) g := fun c g hg =>
    commute_of_mem_orbitRankOneHom_zero σ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) c hg
  have hcommnH : ∀ c : K, ∀ g ∈ R0.range, Commute (Xr (-d4H) c) g := fun c g hg =>
    commute_of_mem_orbitRankOneHom_zero σ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) c hg
  have hPerpH : ∀ m ∈ M, ∀ (c : K) (hc : σ c = c), ψ ⟨Xr d4H c, hHmem c hc⟩ ∈ perpSub m := by
    intro m hm c hc
    by_cases hc0 : c = 0
    · subst hc0
      have e : (⟨Xr d4H 0, hHmem 0 hc⟩ : ↥C₀) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_one]; exact pinnedX_zero _ _ _)
      rw [e, map_one]
      exact (perpSub m).one_mem
    · have h := hperp ⟨Xr d4H c, hHmem c hc⟩ (hHconj c hc hc0) (hcommH c) hm
      exact mem_perpSub_comm.1 h
  have hPerpnH : ∀ m ∈ M, ∀ (c : K) (hc : σ c = c), ψ ⟨Xr (-d4H) c, hnHmem c hc⟩ ∈ perpSub m := by
    intro m hm c hc
    by_cases hc0 : c = 0
    · subst hc0
      have e : (⟨Xr (-d4H) 0, hnHmem 0 hc⟩ : ↥C₀) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_one]; exact pinnedX_zero _ _ _)
      rw [e, map_one]
      exact (perpSub m).one_mem
    · have h := hperp ⟨Xr (-d4H) c, hnHmem c hc⟩ (hnHconj c hc hc0) (hcommnH c) hm
      exact mem_perpSub_comm.1 h
  set g₁ : ModGL TwistTag.D4.tag K := nB K * nA K with hg₁
  have hconj₁ : ∀ x : ModGL TwistTag.D4.tag K,
      g₁ * x * g₁⁻¹ = nB K * (nA K * x * (nA K)⁻¹) * (nB K)⁻¹ := fun x => by
    rw [hg₁]
    group
  have hconjH : ∀ c : K, g₁ * Xr d4C c * g₁⁻¹ = Xr d4H c := fun c => by
    rw [hconj₁, nA_C, nB_P]
  have hconjnH : ∀ c : K, g₁ * Xr (-d4C) c * g₁⁻¹ = Xr (-d4H) c := fun c => by
    rw [hconj₁, nA_conj (by decide +kernel), smul_neg, rA_C, nB_conj (by decide +kernel), smul_neg,
      rB_P]
  set R1 := orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ with hR1
  have hfix1 : ∀ c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩, σ (c : K) = c := by
    intro c
    have h := (mem_orbitField (t := TwistTag.D4) (σ := σ.toRingHom)).1 c.2
    rw [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
    exact h
  set ι := (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hι
  have hR1P : ∀ m ∈ M, ∀ r ∈ R1.range, g₁ * r * g₁⁻¹ ∈ ((perpSub m).comap ψ).map ι := by
    intro m hm r hr
    have hle : R1.range ≤ (((perpSub m).comap ψ).map ι).comap (MulAut.conj g₁).toMonoidHom := by
      rw [hR1, orbitRankOneHom_range, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · dsimp only
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          orbitX_one_eq, hconjH]
        exact ⟨⟨Xr d4H c, hHmem c (hfix1 c)⟩, hPerpH m hm c (hfix1 c), rfl⟩
      · dsimp only
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          orbitY_one_eq, hconjnH]
        exact ⟨⟨Xr (-d4H) c, hnHmem c (hfix1 c)⟩, hPerpnH m hm c (hfix1 c), rfl⟩
    exact hle hr
  have hcardk : Nat.card kk = 2 ^ f := card_fixedField (by omega) hK σ hσ
  have hcardku : Nat.card kkˣ = 2 ^ f - 1 := by rw [Nat.card_units, hcardk]
  obtain ⟨b, hb1⟩ : ∃ b : kkˣ, b ≠ 1 := by
    have h1 : 1 < Nat.card kkˣ := by
      rw [hcardku]
      have : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
      omega
    have : Nontrivial kkˣ := Finite.one_lt_card_iff_nontrivial.1 h1
    exact exists_ne 1
  set fb : Kˣ := trialityFixedUnit K σ b with hfb
  set s : ↥C₀ := ⟨trialityTorusHom σ (fb, b ^ 2), torus_mem σ hσ3 _⟩ with hsdef
  set m₀ : ↥C₀ := ⟨trialityTorusHom σ (fb, 1), torus_mem σ hσ3 _⟩ with hm₀def
  have hs : (s : ModGL TwistTag.D4.tag K) = g₁ * trialityTorusHom σ (1, b) * g₁⁻¹ := by
    rw [hconj₁, nA_conj_trialityTorusHom, inv_one, one_mul, nB_conj_trialityTorusHom hσ3',
      trialityNorm_trialityFixedUnit]
    show trialityTorusHom σ (fb, b ^ 2) = trialityTorusHom σ (fb, b ^ 3 * b⁻¹)
    congr 2
    group
  have hTR1 : trialityTorusHom σ (1, b) ∈ R1.range := by
    rw [trialityTorusHom_eq_orbitH hσ3' 1 b]
    have e : trialityOuterParam hσ3' 1 = 1 := Units.ext rfl
    rw [e, orbitH_one', one_mul, ← orbitRankOneHom_HSL]
    exact ⟨_, rfl⟩
  have hm₀R0 : (m₀ : ModGL TwistTag.D4.tag K) ∈ R0.range := by
    show trialityTorusHom σ (fb, 1) ∈ R0.range
    rw [trialityTorusHom_eq_orbitH hσ3' fb 1]
    have e : trialityMiddleParam (σ := σ) 1 = 1 := Units.ext rfl
    rw [e, orbitH_one', mul_one, ← orbitRankOneHom_HSL]
    exact ⟨_, rfl⟩
  have hm₀M : ψ m₀ ∈ M := ⟨m₀, Subgroup.mem_subgroupOf.2 hm₀R0, rfl⟩
  have hsperp : ψ s ∈ perpSub (ψ m₀) := by
    obtain ⟨z, hz, hzs⟩ := hR1P (ψ m₀) hm₀M _ hTR1
    have e : z = s := Subtype.ext (hzs.trans hs.symm)
    rw [← e]
    exact hz
  have hsodd : Odd (orderOf (ψ s)) := by
    rw [orderOf_injective ψ hψ]
    have hbpow : b ^ (2 ^ f - 1) = 1 := by rw [← hcardku]; exact pow_card_eq_one'
    have hpow : s ^ (2 ^ f - 1) = 1 := by
      refine Subtype.ext ?_
      show trialityTorusHom σ (fb, b ^ 2) ^ (2 ^ f - 1) = 1
      rw [← map_pow, Prod.pow_mk, hfb, ← map_pow, hbpow, pow_right_comm, hbpow, one_pow, map_one]
      exact map_one _
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hpow)
  have hnB : (⟨nB K, nB_mem σ⟩ : ↥C₀) * s ^ 2 * (⟨nB K, nB_mem σ⟩ : ↥C₀)⁻¹ = s * m₀ := by
    refine Subtype.ext ?_
    show nB K * trialityTorusHom σ (fb, b ^ 2) ^ 2 * (nB K)⁻¹ =
      trialityTorusHom σ (fb, b ^ 2) * trialityTorusHom σ (fb, 1)
    calc nB K * trialityTorusHom σ (fb, b ^ 2) ^ 2 * (nB K)⁻¹
        = nB K * trialityTorusHom σ (trialityFixedUnit K σ (b ^ 2), (b ^ 2) ^ 2) * (nB K)⁻¹ := by
          rw [← map_pow, Prod.pow_mk, hfb, map_pow]
      _ = trialityTorusHom σ (trialityFixedUnit K σ (b ^ 2), b ^ 2) := by
          rw [nB_conj_trialityTorusHom hσ3', trialityNorm_trialityFixedUnit]
          exact congrArg (fun x => trialityTorusHom σ (trialityFixedUnit K σ (b ^ 2), x))
            (by group)
      _ = trialityTorusHom σ (fb, b ^ 2) * trialityTorusHom σ (fb, 1) := by
          rw [← map_mul, Prod.mk_mul_mk, mul_one, ← sq, hfb, ← map_pow]
  have hidx : (fixV (Subgroup.zpowers (ψ s))).index * (fixV (Subgroup.zpowers (ψ m₀))).index =
      (fixV (Subgroup.zpowers (ψ s))).index := by
    rw [← index_fixV_mul_of_mem_perpSub hV hsodd (mem_perpSub_comm.1 hsperp), ← map_mul, ← hnB,
      hψconj, map_pow, fixV_zpowers_sq_of_odd hsodd]
  have hone : (fixV (Subgroup.zpowers (ψ m₀))).index = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (hidx.trans (mul_one _).symm)
  have hψm₀ : ψ m₀ = 1 := eq_one_of_fixV_eq_top (Subgroup.index_eq_one.1 hone)
  have hm₀1 : m₀ = 1 := hψ (by rw [hψm₀, map_one])
  have hT : trialityTorusHom σ (fb, 1) = trialityTorusHom σ 1 := by
    rw [map_one]
    exact congrArg Subtype.val hm₀1
  have hfb1 : fb = 1 := congrArg Prod.fst (trialityTorusHom_injective hT)
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  exact hb1 (hinj (by rw [← hfb, hfb1, map_one]))

end Long

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
