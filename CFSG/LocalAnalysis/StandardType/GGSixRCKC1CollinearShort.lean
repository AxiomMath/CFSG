module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearExc
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer
public import CFSG.LieType.Universal.Unitary.RootGroupCard
public import CFSG.Timmesfeld.Transvection.PresSUHalf
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6Sc
import CFSG.Timmesfeld.Transvection.ModelRankSU
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePSU
import all CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.LieType.Ree CFSG.StandardType.LieKnownR2.Short
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.RankTwoOddLie (CenterPPrime)

theorem rckCollinearVia_of_mulEquiv_conj {M M' : LieUniversal} (τ : M.K ≃* M'.K)
    {β : Fin M.D.rank → ℤ} {γ : Fin M'.D.rank → ℤ} (w : M'.K)
    (hτ : (M.D.rootGroup β).map τ.toMonoidHom =
      (M'.D.rootGroup γ).map (MulAut.conj w).toMonoidHom)
    (h : RCKCollinearVia M' γ) : RCKCollinearVia M β := by
  intro X _ _ K R V hR hR2 r hr hr1 hrV hVK hV hV4 hconj
  obtain ⟨φ, hφrange, hφker, u, hRu⟩ := hR
  let φ' : M'.K →* X := φ.comp τ.symm.toMonoidHom
  let u' : M'.K := τ u * w
  have hφ'range : φ'.range = K := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show φ (τ.symm y) ∈ K
      rw [← hφrange]
      exact ⟨τ.symm y, rfl⟩
    · intro hx
      have hx' : x ∈ φ.range := by rwa [hφrange]
      obtain ⟨y, hy⟩ := hx'
      exact ⟨τ y, by simp [φ', hy]⟩
  have hφ'ker : φ'.ker ≤ Subgroup.center M'.K := by
    intro x hx
    have hx' : τ.symm x ∈ φ.ker := hx
    have hxcen : τ.symm x ∈ Subgroup.center M.K := hφker hx'
    have hxmap : x ∈ (Subgroup.center M.K).map (τ : M.K →* M'.K) :=
      Subgroup.mem_map.mpr ⟨τ.symm x, hxcen, by simp⟩
    rwa [Subgroup.map_center_eq τ] at hxmap
  have hcomp : φ'.comp ((MulAut.conj (τ u)).toMonoidHom.comp τ.toMonoidHom) =
      φ.comp (MulAut.conj u).toMonoidHom := by
    ext x
    show φ (τ.symm (τ u * τ x * (τ u)⁻¹)) = φ (u * x * u⁻¹)
    congr 1
    simp only [map_mul, map_inv]
    simp
  have hconjmul : (MulAut.conj (τ u * w)).toMonoidHom =
      (MulAut.conj (τ u)).toMonoidHom.comp (MulAut.conj w).toMonoidHom := by
    ext x
    change (τ u * w) * x * (τ u * w)⁻¹ = (τ u) * (w * x * w⁻¹) * (τ u)⁻¹
    group
  have hsub : ggRootSub M.D φ β u = ggRootSub M'.D φ' γ u' := by
    simp only [ggRootSub, φ', u']
    rw [hconjmul]
    rw [show (M'.D.rootGroup γ).map
        ((MulAut.conj (τ u)).toMonoidHom.comp (MulAut.conj w).toMonoidHom) =
        ((M'.D.rootGroup γ).map (MulAut.conj w).toMonoidHom).map
          (MulAut.conj (τ u)).toMonoidHom from (Subgroup.map_map ..).symm]
    rw [← hτ]
    simp only [Subgroup.map_map]
    rw [hcomp]
  refine h X K R V ⟨φ', hφ'range, hφ'ker, u', ?_⟩ hR2 r hr hr1 hrV hVK hV hV4 hconj
  rw [hRu, hsub]

theorem rckCollinearVia_of_card_ne_two {M : LieUniversal} [Finite M.K]
    (hZ : CenterPPrime M.K 2) {β : Fin M.D.rank → ℤ} (hX : IsPGroup 2 (M.D.rootGroup β))
    (hc : Nat.card (M.D.rootGroup β) ≠ 2) : RCKCollinearVia M β := by
  intro X _ _ K R V hR hR2 r hr hr1 hrV hVK hV hV4 hconj
  obtain ⟨φ, hφrange, hφker, u, hRu⟩ := hR
  let X' : Subgroup M.K := (M.D.rootGroup β).map (MulAut.conj u).toMonoidHom
  have hX' : IsPGroup 2 X' := hX.map (MulAut.conj u).toMonoidHom
  have hcardX' : Nat.card X' = Nat.card (M.D.rootGroup β) :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hcardmap : Nat.card (X'.map φ) = Nat.card X' :=
    CFSG.StandardType.GGOppRad.card_map_eq_of_isPGroup φ 2
      (fun z hz hz2 => hZ z (hφker hz) hz2) hX'
  have hcard : Nat.card R = 2 := hR2
  rw [hRu] at hcard
  change Nat.card (X'.map φ) = 2 at hcard
  rw [hcardmap, hcardX'] at hcard
  exact absurd hcard hc

theorem rckCollinearVia_F4_short
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .F4 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .F4 m g).D.roots) (hs : ¬ GGLongRoot (ggU .F4 m g).D β) :
    RCKCollinearVia (ggU .F4 m g) β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero g := ⟨by omega⟩
  have : CharP (GaloisField 2 g) ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 g) 2)
  let φ : (ggU .F4 m g).K ≃* (ggU .F4 m g).K :=
    ReeTag.F4.finiteExceptionalAut (GaloisField 2 g)
  obtain ⟨β', hβ', hXβ', -, hlong⟩ :=
    finiteExceptionalAut_F4_map_rootGroup (K := GaloisField 2 g) (β := β) hβ
  have hl' : GGLongRoot (ggU .F4 m g).D β' := hlong.mpr hs
  have h1 : (MulAut.conj (1 : (ggU .F4 m g).K)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  refine rckCollinearVia_of_mulEquiv_conj φ 1 ?_ (rckCollinearVia_F4_long hg hβ' hl')
  rw [h1, Subgroup.map_id]
  exact hXβ'

private theorem rckPSU_toStd_eq_weight_of_two_smul_mem {m : ℕ}
    {β : Fin (m / 2) → ℤ}
    (h2 : 2 • β ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.Unitary.isFiniteType_cartan m)
      (CFSG.LieType.Universal.Unitary.divisible m)) :
    ∃ i : Fin m, i ≠ Fin.rev i ∧
      CFSG.LieType.Universal.Unitary.toStd m β = CFSG.LieType.Universal.Unitary.weight m i := by
  have h2' : CFSG.LieType.Universal.Unitary.toStd m (2 • β) =
      2 • CFSG.LieType.Universal.Unitary.toStd m β :=
    CFSG.LieType.Universal.Unitary.SUExtras.toStd_nsmul_two β
  rw [CFSG.LieType.Universal.Unitary.roots_eq] at h2
  rcases h2 with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨-, i, hi, h⟩
  · exfalso
    obtain ⟨c, hc⟩ := CFSG.LieType.Universal.Unitary.SUExtras.exists_weight_ne_zero hi
    have hjc : CFSG.LieType.Universal.Unitary.weight m j c = 0 := by
      rw [CFSG.LieType.Universal.Unitary.SUExtras.weight_apply']
      by_cases h1 : j.val = c.val
      · exfalso
        exact hc.elim (fun hc1 => hij (Fin.ext (by omega)))
          (fun hc2 => hji (Fin.ext (by rw [Fin.val_rev]; omega)))
      · by_cases h2 : j.val + c.val + 1 = m
        · exfalso
          exact hc.elim (fun hc1 => hji (Fin.ext (by rw [Fin.val_rev]; omega)))
            (fun hc2 => hij (Fin.ext (by omega)))
        · rw [if_neg h1, if_neg h2]
    have hi1 : CFSG.LieType.Universal.Unitary.weight m i c = 1 ∨
        CFSG.LieType.Universal.Unitary.weight m i c = -1 := by
      rw [CFSG.LieType.Universal.Unitary.SUExtras.weight_apply']
      by_cases h1 : i.val = c.val
      · left; rw [if_pos h1]
      · by_cases h2 : i.val + c.val + 1 = m
        · right; rw [if_neg h1, if_pos h2]
        · exfalso
          exact hc.elim (fun hc1 => h1 hc1) (fun hc2 => h2 hc2)
    have hEq : (2 : ℤ) * CFSG.LieType.Universal.Unitary.toStd m β c =
        (CFSG.LieType.Universal.Unitary.weight m i -
          CFSG.LieType.Universal.Unitary.weight m j) c := by
      have := congrFun (h2'.symm.trans h) c
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rw [Pi.sub_apply, hjc, sub_zero] at hEq
    rcases hi1 with h1 | h1 <;> rw [h1] at hEq <;> omega
  · refine ⟨i, hi, ?_⟩
    funext a
    have heq : (2 : ℤ) • CFSG.LieType.Universal.Unitary.toStd m β =
        2 • CFSG.LieType.Universal.Unitary.weight m i := h2'.symm.trans h
    have := congrFun heq a
    simpa [Pi.smul_apply, smul_eq_mul] using this
  · exfalso
    obtain ⟨c, hc⟩ := CFSG.LieType.Universal.Unitary.SUExtras.exists_weight_ne_zero hi
    have hi1 : CFSG.LieType.Universal.Unitary.weight m i c = 1 ∨
        CFSG.LieType.Universal.Unitary.weight m i c = -1 := by
      rw [CFSG.LieType.Universal.Unitary.SUExtras.weight_apply']
      by_cases h1 : i.val = c.val
      · left; rw [if_pos h1]
      · by_cases h2 : i.val + c.val + 1 = m
        · right; rw [if_neg h1, if_pos h2]
        · exfalso
          exact hc.elim (fun hc1 => h1 hc1) (fun hc2 => h2 hc2)
    have hEq : (2 : ℤ) * CFSG.LieType.Universal.Unitary.toStd m β c =
        CFSG.LieType.Universal.Unitary.weight m i c := by
      have := congrFun (h2'.symm.trans h) c
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rcases hi1 with h1 | h1 <;> rw [h1] at hEq <;> omega

private theorem rckPSU_card_rootGroup_ne_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {g m : ℕ} (hg : 1 ≤ g) (hF : Nat.card F = (2 ^ g) ^ 2)
    {β : Fin (CFSG.LieType.Universal.Unitary.rootDatum hF m).rank → ℤ}
    (hβ : β ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots)
    (hs : ¬ GGLongRoot (CFSG.LieType.Universal.Unitary.rootDatum hF m) β) :
    Nat.card ((CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β) ≠ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcard
  have hσ : ∀ c, CFSG.LieType.BorelTits.unitaryInvolution F 2 g
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 g c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hFbig : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ g) ^ 2 := Nat.pow_le_pow_left h2g 2
  by_cases h2 : 2 • β ∉ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots
  · obtain ⟨A, B, hAB, hβrt⟩ :=
      CFSG.StandardType.ClassicalPosition.grcPSU_short_classification hF hβ hs h2
    let f : F → (CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β := fun c =>
      ⟨suElt (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) hσ A B c,
        CFSG.Timmesfeld.Transvection.Pres.suElt_mem hσ hAB hβrt c⟩
    have hf : Function.Injective f := by
      intro c d hcd
      have hval := congrArg Subtype.val hcd
      have hmat := congrArg (fun x : CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) m =>
        CFSG.LieType.Universal.Unitary.SUExtras.mat
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) m x
          (CFSG.Timmesfeld.Transvection.Pres.crd A)
          (CFSG.Timmesfeld.Transvection.Pres.crd (Sum.swap B))) hval
      simpa [f, CFSG.Timmesfeld.Transvection.mat_suElt_apply hσ hAB] using hmat
    have hle : Nat.card F ≤ Nat.card
        ((CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β) :=
      Nat.card_le_card_of_injective f hf
    omega
  · have h2mem : 2 • β ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots := by
      simpa using not_not.mp h2
    obtain ⟨a, ha, hβw⟩ := rckPSU_toStd_eq_weight_of_two_smul_mem h2mem
    have hodd : ¬ Even m := by
      intro he
      have hβ' : β ∈ CFSG.LieType.RootSystem.roots
          (CFSG.LieType.Universal.Unitary.isFiniteType_cartan m)
          (CFSG.LieType.Universal.Unitary.divisible m) := hβ
      rw [CFSG.LieType.Universal.Unitary.roots_eq] at hβ'
      rcases hβ' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨hodd, i, hi, h⟩
      · have hEq : CFSG.LieType.Universal.Unitary.weight m a =
            CFSG.LieType.Universal.Unitary.weight m i -
              CFSG.LieType.Universal.Unitary.weight m j := by
          rw [← hβw, h]
        exact CFSG.LieType.Universal.Unitary.SUExtras.weight_ne_weight_sub hij hi hj hji hEq
      · have hEq : CFSG.LieType.Universal.Unitary.weight m a =
            2 • CFSG.LieType.Universal.Unitary.weight m i := by
          rw [← hβw, h]
        exact CFSG.Timmesfeld.Transvection.ModelRank.weight_ne_two_smul_weight' hi hEq
      · exact hodd he
    let mid : Fin m := CFSG.LieType.Universal.Unitary.SUExtras.midIdx m hodd
    have hmid : Fin.rev mid = mid := CFSG.LieType.Universal.Unitary.SUExtras.rev_midIdx hodd
    have hik : a ≠ mid := by
      intro h
      have hzero : CFSG.LieType.Universal.Unitary.weight m a = 0 := by
        rw [h]
        exact CFSG.LieType.Universal.Unitary.SUExtras.weight_eq_zero_of_rev_eq hmid
      have hβzero : CFSG.LieType.Universal.Unitary.toStd m β = 0 := by rw [hβw, hzero]
      exact CFSG.LieType.Universal.Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ hβzero
    have hHle : CFSG.LieType.Universal.Unitary.heisenbergSubgroup
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) hσ ha hik hmid ≤
        (CFSG.LieType.Universal.Unitary.rootDatum hF m).rootGroup β :=
      CFSG.LieType.Universal.Unitary.SUExtras.heisenberg_le hσ ha hik hmid hβw.symm
    have hHcard : Nat.card (CFSG.LieType.Universal.Unitary.heisenbergSubgroup
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) hσ ha hik hmid) = (2 ^ g) ^ 3 :=
      CFSG.LieType.Universal.Unitary.card_heisenbergSubgroup hF ha hik hmid
    have h8 : 8 ≤ (2 ^ g) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 ^ g) ^ 3 := Nat.pow_le_pow_left h2g 3
    have hle2 : (2 ^ g) ^ 3 ≤ 2 := by
      rw [← hHcard]
      exact (Subgroup.card_le_of_le hHle).trans_eq hcard
    omega

theorem rckCollinearVia_PSU_short
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSU m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSU m g).D.roots) (hs : ¬ GGLongRoot (ggU .PSU m g).D β) :
    RCKCollinearVia (ggU .PSU m g) β := by
  have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
    card_galoisField_two_mul 2 g hg
  let M0 : LieUniversal :=
    ⟨CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m,
      CFSG.LieType.Universal.Unitary.rootDatum hF m⟩
  have e : ggU .PSU m g = M0 := by
    simp only [ggU, lieUniversal, hg, ↓reduceDIte, M0]
  suffices h : ∀ (M : LieUniversal), M = M0 →
      ∀ (β : Fin M.D.rank → ℤ), β ∈ M.D.roots → ¬ GGLongRoot M.D β →
      RCKCollinearVia M β by
    exact h (ggU .PSU m g) e β hβ hs
  intro M hM β hβ hs
  subst hM
  have hβ' : β ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF m).roots := hβ
  have hm : 1 ≤ m := by
    have hroots : β ∈ CFSG.LieType.RootSystem.roots
        (CFSG.LieType.Universal.Unitary.isFiniteType_cartan m)
        (CFSG.LieType.Universal.Unitary.divisible m) := hβ'
    rw [CFSG.LieType.Universal.Unitary.roots_eq] at hroots
    rcases hroots with ⟨i, j, -⟩ | ⟨i, -⟩ | ⟨-, i, -⟩
    · exact i.pos
    · exact i.pos
    · exact i.pos
  have : Finite M0.K := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : CenterPPrime M0.K 2 := rckGL2_centerPPrime_su hF hg hm
  have hX : IsPGroup 2 (M0.D.rootGroup β) := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF)
      (CFSG.LieType.Universal.Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ')
  have hc : Nat.card (M0.D.rootGroup β) ≠ 2 := rckPSU_card_rootGroup_ne_two hg hF hβ' hs
  exact rckCollinearVia_of_card_ne_two hZ hX hc

private theorem rckPOmega_short_card {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {γ : Fin (m - 1) → ℤ} {i : Fin (m - 1)}
    {s : Bool} (h : CFSG.LieType.Universal.Spin.toStdB (m - 1) γ =
      Pi.single i (CFSG.LieType.Universal.Spin.boolSign s)) (hK : 2 ≤ Nat.card K) :
    Nat.card (Spin.Twisted.minusRootGroup m hirr γ) ≠ 2 := by
  have hcard : Nat.card (Spin.Twisted.minusRootGroup m hirr γ) = Nat.card K ^ 2 := by
    rw [Spin.Twisted.minusRootGroup_eq_short m hirr i s h]
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (Spin.Twisted.twShortRoot_injective m hirr i s)).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  intro h2
  rw [hcard] at h2
  have hK2 : 4 ≤ Nat.card K ^ 2 := by nlinarith
  omega

private theorem rckPOmega_long_shape {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {γ : Fin (m - 1) → ℤ}
    (hγ : γ ∈ (Spin.Twisted.minusDatum m hirr).roots) {i j : Fin (m - 1)} (hij : i ≠ j)
    (s t : Bool) (h : CFSG.LieType.Universal.Spin.toStdB (m - 1) γ =
      Pi.single i (CFSG.LieType.Universal.Spin.boolSign s) +
        Pi.single j (CFSG.LieType.Universal.Spin.boolSign t)) :
    GGLongRoot (Spin.Twisted.minusDatum m hirr) γ := by
  have hm1 : 0 < m - 1 := by omega
  have hirrB : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
      (CFSG.LieType.Universal.Spin.cartanB (m - 1)) :=
    CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanB hm1
  have hdiv : (Spin.Twisted.minusDatum m hirr).divisible = ∅ := rfl
  obtain ⟨r, hr⟩ := CFSG.LieType.HighestRoot.exists_isHighestRoot
    (D := Spin.Twisted.minusDatum m hirr) hirrB hdiv hm1
  have hrL : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
      (Spin.Twisted.minusDatum m hirr) r := ⟨hr.mem_roots, hr.longest⟩
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (m - 1)) ∅ := by
    rwa [Spin.Twisted.minusDatum_roots] at hγ
  rcases hγ' with ⟨w, k, hγeq⟩ | ⟨w, k, hk, -⟩
  · have hsingle_long : ∃ (a b : Fin (m - 1)) (_ : a ≠ b) (s' t' : Bool),
        CFSG.LieType.Universal.Spin.toStdB (m - 1) (Pi.single k 1) =
          Pi.single a (CFSG.LieType.Universal.Spin.boolSign s') +
            Pi.single b (CFSG.LieType.Universal.Spin.boolSign t') := by
      have h' := CFSG.StandardType.RootCentOmega.exists_long_weylAction
        (m := m - 1) (w := w⁻¹) ⟨i, j, hij, s, t, h⟩
      rw [hγeq, CFSG.LieType.RootSystem.weylAction_inv_apply_apply] at h'
      exact h'
    have hk : k.val + 1 < m - 1 := by
      by_contra hk
      obtain ⟨a, b, hab, s', t', hst⟩ := hsingle_long
      have hs : CFSG.LieType.Universal.Spin.toStdB (m - 1) (Pi.single k 1) =
          Pi.single k (CFSG.LieType.Universal.Spin.boolSign true) :=
        Spin.Twisted.toStdB_single_of_not_lt' (n := m) (k := k) hk
      exact CFSG.LieType.Universal.Spin.single_ne_single_add_single hab
        (CFSG.LieType.Universal.Spin.boolSign_ne_zero s')
        (CFSG.LieType.Universal.Spin.boolSign_ne_zero t') (by simpa [hs] using hst)
    have hkL : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
        (Spin.Twisted.minusDatum m hirr) (Pi.single k 1) :=
      CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanB
        (m := m - 1) (by omega) rfl (Spin.Twisted.minusDatum m hirr).isFiniteType hk
    have hγL : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot
        (Spin.Twisted.minusDatum m hirr) γ := by
      rw [hγeq]
      exact hkL.map_weylAction w
    obtain ⟨w', hw'⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_of_isLongest
      (A := CFSG.LieType.Universal.Spin.cartanB (m - 1))
      (hA := CFSG.LieType.Universal.Spin.isFiniteType_cartanB (m - 1))
      (D := (Spin.Twisted.minusDatum m hirr).divisible)
      hirrB (fun i hi => by rw [hdiv] at hi; exact absurd hi (Set.notMem_empty i)) hrL hγL
    exact ⟨w', r, hr.mem_roots, hr.height_le, hw'.symm⟩
  · exact absurd hk (Set.notMem_empty k)

theorem rckCollinearVia_POmegaMinus_short
    {m g : ℕ} (hg : 1 ≤ g) (hm : 2 ≤ m) {β : Fin (ggU .POmegaMinus m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus m g).D.roots) (hs : ¬ GGLongRoot (ggU .POmegaMinus m g).D β) :
    RCKCollinearVia (ggU .POmegaMinus m g) β := by
  let M0 : LieUniversal :=
    ⟨spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
      Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)⟩
  have e : ggU .POmegaMinus m g = M0 := by
    simp only [ggU, lieUniversal, M0]
  have hK : 2 ≤ Nat.card (GaloisField 2 g) := by
    rw [GaloisField.card 2 g (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  suffices h : ∀ (M : LieUniversal), M = M0 →
      ∀ (β : Fin M.D.rank → ℤ), β ∈ M.D.roots → ¬ GGLongRoot M.D β →
      RCKCollinearVia M β by
    exact h (ggU .POmegaMinus m g) e β hβ hs
  intro M hM β hβ hs
  subst hM
  have hβ' : β ∈ (Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)).roots := hβ
  have hroots : β ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (m - 1)) ∅ := by
    rwa [Spin.Twisted.minusDatum_roots] at hβ'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : CenterPPrime M0.K 2 :=
    rckGL1_centerPPrime_ggU (t := .POmegaMinus) (by simp [GGPosTag]) hg (fun _ => hm)
  have : Finite M0.K :=
    rckXF_finite_ggU (t' := .POmegaMinus) (by simp [GGPosTag]) hg
  have hX : IsPGroup 2 (M0.D.rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_minusRootGroup (hirr := minusCoeffs_irr 2 g) hβ'
  have hc : Nat.card (M0.D.rootGroup β) ≠ 2 := by
    rcases Spin.Twisted.exists_toStdB_eq_of_mem_roots m hroots with
      ⟨i, j, hij, s, t, hst⟩ | ⟨i, s, hst⟩
    · exact absurd (rckPOmega_long_shape hm (minusCoeffs_irr 2 g) hβ' hij s t hst) hs
    · exact rckPOmega_short_card (minusCoeffs_irr 2 g) hst hK
  exact rckCollinearVia_of_card_ne_two hZ hX hc

theorem rckCollinearVia_POmegaMinus_two
    {g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaMinus 2 g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus 2 g).D.roots) :
    RCKCollinearVia (ggU .POmegaMinus 2 g) β := by
  let M0 : LieUniversal :=
    ⟨spinGroup (Spin.quadMinus 2 (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
      Spin.Twisted.minusDatum 2 (minusCoeffs_irr 2 g)⟩
  have e : ggU .POmegaMinus 2 g = M0 := by
    simp only [ggU, lieUniversal, M0]
  have hK : 2 ≤ Nat.card (GaloisField 2 g) := by
    rw [GaloisField.card 2 g (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  suffices h : ∀ (M : LieUniversal), M = M0 →
      ∀ (β : Fin M.D.rank → ℤ), β ∈ M.D.roots → RCKCollinearVia M β by
    exact h (ggU .POmegaMinus 2 g) e β hβ
  intro M hM β hβ
  subst hM
  have hβ' : β ∈ (Spin.Twisted.minusDatum 2 (minusCoeffs_irr 2 g)).roots := hβ
  have hroots : β ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB (2 - 1)) ∅ := by
    rwa [Spin.Twisted.minusDatum_roots] at hβ'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : CenterPPrime M0.K 2 :=
    rckGL1_centerPPrime_ggU (t := .POmegaMinus) (by simp [GGPosTag]) hg (fun _ => le_rfl)
  have : Finite M0.K :=
    rckXF_finite_ggU (t' := .POmegaMinus) (by simp [GGPosTag]) hg
  have hX : IsPGroup 2 (M0.D.rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_minusRootGroup (hirr := minusCoeffs_irr 2 g) hβ'
  have hc : Nat.card (M0.D.rootGroup β) ≠ 2 := by
    rcases Spin.Twisted.exists_toStdB_eq_of_mem_roots 2 hroots with
      ⟨i, j, hij, s, t, hst⟩ | ⟨i, s, hst⟩
    · exact absurd (show i = j from by fin_cases i; fin_cases j; rfl) hij
    · exact rckPOmega_short_card (minusCoeffs_irr 2 g) hst hK
  exact rckCollinearVia_of_card_ne_two hZ hX hc

private theorem rckTwE6X_injective
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    Function.Injective (rckTwE6X θ hθ) := by
  intro c d h
  have hv := congrArg (fun x : fixedGroup k θ =>
    (x : CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k)) h
  simp only [rckTwE6X, CFSG.LieType.Steinberg.TwistedE6.xPair_val] at hv
  exact (CFSG.LieType.Steinberg.TwistedE6.xm_mul_xm_rho_inj
    rckTwE6RootA_facts.1 rckTwE6RootA_facts.2.2.1 hv).1

private theorem rckTwE6_card_rootGroup_alpha
    {k : Type} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) :
    Nat.card ((twistedDatum k θ).rootGroup twE6Alpha) = Nat.card k := by
  let f : k → (twistedDatum k θ).rootGroup twE6Alpha := fun c =>
    ⟨rckTwE6X θ hθ c, (rckTwE6_mem_rootGroup_iff θ hθ _).mpr ⟨c, rfl⟩⟩
  have hf : Function.Injective f := by
    intro c d hcd
    exact rckTwE6X_injective θ hθ (congrArg Subtype.val hcd)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨c, hc⟩ := (rckTwE6_mem_rootGroup_iff θ hθ x).mp x.2
    exact ⟨c, Subtype.ext hc.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)).symm

private theorem rckTwE6_card_rootGroup_short
    {k : Type} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card k)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ (twistedDatum k θ).roots)
    (hs : ¬ GGLongRoot (twistedDatum k θ) β) :
    Nat.card ((twistedDatum k θ).rootGroup β) ≠ 2 := by
  obtain ⟨w, hw⟩ := twE6_exists_weyl_of_not_long θ hβ hs
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  obtain ⟨g, hg, -⟩ := exists_conj_ggRootSub_of_weylAction
    (D := twistedDatum k θ) hct (twE6_alpha_mem_roots θ) w hw 1
  have hg' : (twistedDatum k θ).rootGroup β =
      ((twistedDatum k θ).rootGroup twE6Alpha).map (MulAut.conj g).toMonoidHom := by
    have hc1 : MulAut.conj (1 : fixedGroup k θ) = 1 := by
      apply MulEquiv.ext
      intro x
      simp [MulAut.conj_apply]
    have h1 : (MulEquiv.toMonoidHom (1 : MulAut (fixedGroup k θ))) =
        MonoidHom.id (fixedGroup k θ) := by
      ext x
      rfl
    simpa only [ggRootSub, hc1, h1, Subgroup.map_id] using hg
  rw [hg', Subgroup.card_map_of_injective (MulAut.conj g).injective,
    rckTwE6_card_rootGroup_alpha θ hθ]
  omega

theorem rckCollinearVia_twistedE6_short
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .twistedE6 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .twistedE6 m g).D.roots) (hs : ¬ GGLongRoot (ggU .twistedE6 m g).D β) :
    RCKCollinearVia (ggU .twistedE6 m g) β := by
  let k := GaloisField 2 (2 * g)
  let θ : k →+* k := frobQ 2 g
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 g hg
  have hK : 4 ≤ Nat.card k := by
    dsimp [k]
    rw [card_galoisField_two_mul 2 g hg]
    have h2g : 2 ≤ 2 ^ g := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ g) ^ 2 := Nat.pow_le_pow_left h2g 2
  have hβ' : β ∈ (twistedDatum k θ).roots := hβ
  have hZ : CenterPPrime (ggU .twistedE6 m g).K 2 :=
    rckGL1_centerPPrime_ggU (t := .twistedE6) (by simp [GGPosTag]) hg (by simp)
  have : Finite (ggU .twistedE6 m g).K :=
    rckXF_finite_ggU (t' := .twistedE6) (by simp [GGPosTag]) hg
  have hX : IsPGroup 2 ((ggU .twistedE6 m g).D.rootGroup β) :=
    isPGroup_two_twistedRootGroup θ hβ'
  have hc : Nat.card ((ggU .twistedE6 m g).D.rootGroup β) ≠ 2 :=
    rckTwE6_card_rootGroup_short θ hθ hK hβ' hs
  exact rckCollinearVia_of_card_ne_two hZ hX hc

end CFSG.StandardType.RCKC1
