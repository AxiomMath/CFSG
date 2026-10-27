module

public import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open scoped Pointwise

namespace Res162Seven

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem normalizer_x_eq_of_main (h153 : Item153Main A (lB A)) (hn : Claim153Normal A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) :
    Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A)
      (Subgroup.normalizer (K : Set G))) : Set G) = Subgroup.normalizer (K : Set G) := by
  have hNX := Proof162.normalizer_le_normalizer_x h153 hK
  obtain ⟨M, hM⟩ := exists_mem_maximalTwoLocalsContaining hK.prop.2
  have hM' := hM
  rw [(h153 K hK).1] at hM'
  have hMeq : M = Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G) :=
    Set.mem_singleton_iff.mp hM'
  have hMmem : Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (K : Set G))) : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) := by
    rw [← hMeq]
    exact hM
  exact le_antisymm (hn K hK _ hMmem) hNX

theorem le_normalizer_of_isPLocal (h153 : Item153Main A (lB A)) (hn : Claim153Normal A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) {M : Subgroup G} (hM : IsPLocal 2 M)
    (hKM : K ≤ M) (hAM : A ≤ M) : M ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨M', hMM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hM
  exact hMM'.trans (hn K hK M' ⟨hM', fun x hx => hMM' (sup_le hKM hAM hx)⟩)

theorem inf_centralizer_pCoreOf_le (h153 : Item153Main A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) :
    K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ≤ CFSG.Open.pCoreOf 2 K := by
  have hF : generalizedFitting ↥K = CFSG.pCore 2 ↥K := (h153 K hK).2.2
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxc : (⟨x, hxK⟩ : ↥K) ∈
      Subgroup.centralizer (CFSG.generalizedFitting ↥K : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ CFSG.Open.pCoreOf 2 K := by
      rw [← Step163Alt.mem_pCore_two_iff y, ← hF]
      exact hy
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC (y : G) hy'
    exact Subtype.ext hcomm
  have hxG : (⟨x, hxK⟩ : ↥K) ∈ CFSG.generalizedFitting ↥K :=
    CFSG.centralizer_generalizedFitting_le ↥K hxc
  rw [hF] at hxG
  exact (Step163Alt.mem_pCore_two_iff ⟨x, hxK⟩).mp hxG

private noncomputable def pCoreQuotMulAut {H : Type*} [Group H] [Finite H] :
    MulAut H →* MulAut (H ⧸ CFSG.pCore 2 H) where
  toFun σ := QuotientGroup.congr _ _ σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem card_inf_eq_nine_of_a7 (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAmax : ∀ x : G, x ^ 3 = 1 → A ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A)
    {K : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {k : G}
    (hk : Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) = (Subgroup.zpowers k : Set G))
    (hk1 : k ≠ 1) :
    Nat.card (A ⊓ K : Subgroup G) = 9 ∧ k ∉ K ∧ (A ⊓ K) ⊔ Subgroup.zpowers k = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥A →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (pCoreQuotMulAut (H := ↥K)).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hAK))
  have hρapply : ∀ a : ↥A, ρ a =
      Step163Alt.conjQuotTwo K (hAK a.2) := by
    intro a
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [show ρ a = pCoreQuotMulAut (K.normalizerMonoidHom ⟨a, hAK a.2⟩) from rfl,
        Step163Alt.conjQuotTwo_mk]
      rfl
  have hkerSet : ∀ a : ↥A,
      (a : G) ∈ Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ↔ ρ a = 1 := by
    intro a
    constructor
    · intro ha
      ext z
      induction z using QuotientGroup.induction_on with
      | H x =>
        rw [hρapply a, Step163Alt.conjQuotTwo_mk, MulAut.one_apply,
          QuotientGroup.eq_iff_div_mem]
        have hmemK : a * (x : G) * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hAK a.2) (x : G)).mp x.2
        refine (Step163Alt.mem_pCore_two_iff
          ((⟨a * (x : G) * a⁻¹, hmemK⟩ : ↥K) / x)).mpr ?_
        simpa [div_eq_mul_inv] using ha.2 (x : G) x.2
    · intro ha
      refine ⟨a.2, fun x hx => ?_⟩
      have hmemK : a * x * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAK a.2) x).mp hx
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
            (⟨a * x * a⁻¹, hmemK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hx⟩ : ↥K) := by
        have h := congrArg (fun σ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
          σ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hx⟩ : ↥K))) ha
        rw [hρapply a] at h
        have h' : Step163Alt.conjQuotTwo K (hAK a.2)
            ((⟨x, hx⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
            ((⟨x, hx⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
          simpa only [QuotientGroup.mk'_apply, MulAut.one_apply] using h
        rw [Step163Alt.conjQuotTwo_mk] at h'
        simpa using h'
      have h2 : (⟨a * x * a⁻¹, hmemK⟩ : ↥K) / (⟨x, hx⟩ : ↥K) ∈
          CFSG.pCore 2 ↥K := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact h1
      have h3 := (Step163Alt.mem_pCore_two_iff
        ((⟨a * x * a⁻¹, hmemK⟩ : ↥K) / (⟨x, hx⟩ : ↥K))).mp h2
      simpa [div_eq_mul_inv] using h3
  have hkA : k ∈ A := by
    have : k ∈ Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) := by
      rw [hk]
      exact Subgroup.mem_zpowers k
    exact this.1
  have hk3 : k ^ 3 = 1 := hA.2 k hkA
  have hkorder : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hker : ρ.ker = (Subgroup.zpowers k).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hkerSet a, hk]
    exact Iff.rfl
  have hkercard : Nat.card ρ.ker = 3 := by
    rw [hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hkA)).toEquiv,
      Nat.card_zpowers, hkorder]
  have hR9 : Nat.card ρ.range = 9 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hA27, hkercard] at h1
    omega
  have hRcomm : ∀ σ ∈ ρ.range, ∀ τ ∈ ρ.range, σ * τ = τ * σ := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hA.1.is_comm.comm a b]
  obtain ⟨-, hZcenter, hinnerAut, -, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts
      (↥K ⧸ CFSG.pCore 2 ↥K) ⟨φ⟩
  let ι : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := MulAut.conj
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => σ z)
        (MonoidHom.mem_ker.mp hx)
      simp only [ι, MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * x = x * z * x⁻¹ * x := by rw [h1]
        _ = x * z := by group
    rw [hZcenter] at hxc
    exact hxc
  have hinner : ρ.range ≤ ι.range := by
    rintro _ ⟨a, rfl⟩
    have hσ3 : (ρ a) ^ 3 = 1 := by
      rw [hρapply a, Step163Alt.conjQuotTwo_pow_three K (hAK a.2) (hA.2 a a.2)]
    obtain ⟨x, hx⟩ := hinnerAut (ρ a) ⟨1, by simpa using hσ3⟩
    exact ⟨x, hx.symm⟩
  let DtilK : Subgroup ↥K :=
    ρ.range.comap (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
  let Dtil : Subgroup G := DtilK.map K.subtype
  have hDtilK : Dtil ≤ K := Subgroup.map_subtype_le _
  have hιconj : ∀ (σ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K))
      (z : ↥K ⧸ CFSG.pCore 2 ↥K),
      ι (σ z) = σ * ι z * σ⁻¹ := by
    intro σ z
    ext w
    simp only [ι, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hιeq_conj : ∀ (a : G) (ha : a ∈ A) (x : ↥K), x ∈ DtilK →
      (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
        (⟨a * (x : G) * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hAK ha) (x : G)).mp x.2⟩ : ↥K) =
      (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) x := by
    intro a ha x hx
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (⟨a * (x : G) * a⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hAK ha) (x : G)).mp x.2⟩ : ↥K) :
          ↥K ⧸ CFSG.pCore 2 ↥K) =
        ρ ⟨a, ha⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) := by
      rw [hρapply ⟨a, ha⟩]
      exact (Step163Alt.conjQuotTwo_mk K (hAK ha) x).symm
    change ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
      ⟨a * (x : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAK ha) (x : G)).mp x.2⟩) =
      ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)
    rw [h1, hιconj]
    have hσ : ρ ⟨a, ha⟩ ∈ ρ.range := ⟨⟨a, ha⟩, rfl⟩
    have hz : ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) ∈ ρ.range := hx
    calc ρ ⟨a, ha⟩ * ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) * (ρ ⟨a, ha⟩)⁻¹
        = ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) * ρ ⟨a, ha⟩ *
            (ρ ⟨a, ha⟩)⁻¹ := by rw [hRcomm _ hσ _ hz]
      _ = ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) := by group
  have hAD : A ≤ Subgroup.normalizer (Dtil : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemK : a * (xK : G) * a⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK ha) (xK : G)).mp xK.2
    have hnew : (⟨a * (xK : G) * a⁻¹, hmemK⟩ : ↥K) ∈ DtilK := by
      change (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
        ⟨a * (xK : G) * a⁻¹, hmemK⟩ ∈ ρ.range
      rw [hιeq_conj a ha xK hxK]
      exact hxK
    exact Subgroup.mem_map.mpr ⟨_, hnew, rfl⟩
  have hAtriv : ∀ (a : G) (ha : a ∈ A) (x : G) (hx : x ∈ Dtil),
      a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    intro a ha x hx
    obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemK : a * (xK : G) * a⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK ha) (xK : G)).mp xK.2
    have hquot : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (⟨a * (xK : G) * a⁻¹, hmemK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) xK :=
      hιinj (hιeq_conj a ha xK hxK)
    have h2 : (⟨a * (xK : G) * a⁻¹, hmemK⟩ : ↥K) / xK ∈
        CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_iff_div_mem]
      exact hquot
    have h3 := (Step163Alt.mem_pCore_two_iff
      ((⟨a * (xK : G) * a⁻¹, hmemK⟩ : ↥K) / xK)).mp h2
    simpa [div_eq_mul_inv] using h3
  let hD : ↥Dtil →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).comp (Subgroup.inclusion hDtilK)
  have hkerDle : hD.ker ≤ (CFSG.Open.pCoreOf 2 K).comap Dtil.subtype := by
    intro d hd
    rw [Subgroup.mem_comap]
    let x : ↥K := (Subgroup.inclusion hDtilK) d
    have h1 : ι ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)
        (x : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) = 1 := by
      simpa [x, hD] using hd
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
        (x : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      apply hιinj
      rw [h1, map_one]
    have h3 : x ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_one_iff x).mp h2
    exact (Step163Alt.mem_pCore_two_iff x).mp h3
  have hkerD : IsPGroup 2 hD.ker :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K).comap_of_injective
      Dtil.subtype Dtil.subtype_injective).to_le hkerDle
  have hrangeD : hD.range = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      obtain ⟨xK, hxK, hxd⟩ := Subgroup.mem_map.mp d.2
      have hxeq : (⟨d, hDtilK d.2⟩ : ↥K) = xK := Subtype.ext hxd.symm
      change (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) ⟨d, hDtilK d.2⟩ ∈
        ρ.range
      rw [hxeq]
      exact hxK
    · rintro r hr
      obtain ⟨z, hz⟩ := hinner hr
      obtain ⟨xK, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
      have hxK : xK ∈ DtilK := by
        change ι (QuotientGroup.mk' (CFSG.pCore 2 ↥K) xK) ∈ ρ.range
        rw [hz]
        exact hr
      let d : ↥Dtil := ⟨(xK : G), Subgroup.mem_map.mpr ⟨xK, hxK, rfl⟩⟩
      refine ⟨d, ?_⟩
      have hxeq : (⟨(xK : G), hDtilK d.2⟩ : ↥K) = xK := Subtype.ext rfl
      change (ι.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
        ⟨(xK : G), hDtilK d.2⟩ = r
      rw [hxeq]
      exact hz
  have hE : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun σ τ => Subtype.ext (hRcomm σ σ.2 τ τ.2)⟩⟩, fun σ hσ => ?_⟩
    obtain ⟨a, ha⟩ := hσ
    rw [← ha, ← map_pow, show a ^ 3 = 1 from Subtype.ext (hA.2 a a.2), map_one]
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  have hkercomp : ¬ 3 ∣ Nat.card hD.ker :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hkerD Nat.prime_three (by norm_num)
  let C : Subgroup G := Dtil ⊓ Subgroup.centralizer (A : Set G)
  let hC : ↥C →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    hD.comp (Subgroup.inclusion inf_le_left)
  have hCker : IsPGroup 2 hC.ker :=
    hkerD.comap_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have htrivD : ∀ (a : ↥A) (d : ↥Dtil),
      hD ⟨(a : G) * (d : G) * (a : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hAD a a.2 d d.2⟩ = hD d := by
    intro a d
    have hmemK : (a : G) * (d : G) * (a : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK a.2) (d : G)).mp (hDtilK d.2)
    have hquot : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (⟨(a : G) * (d : G) * (a : G)⁻¹, hmemK⟩ : ↥K) :
          ↥K ⧸ CFSG.pCore 2 ↥K) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hDtilK d.2⟩ := by
      change (((⟨(a : G) * (d : G) * (a : G)⁻¹, hmemK⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K)) =
        ((⟨d, hDtilK d.2⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
      rw [QuotientGroup.eq_iff_div_mem]
      refine (Step163Alt.mem_pCore_two_iff _).mpr ?_
      simpa [div_eq_mul_inv] using hAtriv (a : G) a.2 (d : G) d.2
    have hconjD : (a : G) * (d : G) * (a : G)⁻¹ ∈ Dtil :=
      (Subgroup.mem_normalizer_iff.mp (hAD a.2) (d : G)).mp d.2
    change ι ((QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        (⟨(a : G) * (d : G) * (a : G)⁻¹, hmemK⟩ : ↥K)) =
      ι ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (⟨d, hDtilK d.2⟩ : ↥K))
    rw [hquot]
  have hCrange : hC.range = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      change hD ⟨c, (Subgroup.mem_inf.mp c.2).1⟩ ∈ ρ.range
      rw [← hrangeD]
      exact ⟨⟨c, (Subgroup.mem_inf.mp c.2).1⟩, rfl⟩
    · rintro r hr
      have hrD : r ∈ hD.range := by rw [hrangeD]; exact hr
      obtain ⟨d, hd⟩ := hrD
      obtain ⟨c, hcC, hcEq⟩ :=
        exists_centralizer_with_same_image_of_trivial_quotient_action
          3 Nat.prime_three A Dtil hA3 hAD hD hkercomp htrivD d
      refine ⟨⟨c, ⟨c.2, hcC⟩⟩, ?_⟩
      change hD c = r
      exact hcEq.trans hd
  obtain ⟨S, hSC, hSE, hScard⟩ :=
    Step163Alt.exists_elemAbelian_lift (K := C) hC hCker (E := ρ.range) hE (by rw [hCrange])
  have hScard9 : Nat.card S = 9 := hScard.trans hR9
  have hSA : S ≤ A := by
    intro s hs
    refine hAmax s (hSE.2 s hs) ?_
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsc : s ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp (hSC hs)).2
    exact Subgroup.mem_centralizer_iff.mp hsc a ha
  have hSle : S ≤ A ⊓ K :=
    le_inf hSA ((hSC.trans inf_le_left).trans hDtilK)
  have h9le : 9 ≤ Nat.card (A ⊓ K : Subgroup G) :=
    hScard9 ▸ Subgroup.card_le_of_le hSle
  have hksec : k ∈ Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) := by
    rw [hk]
    exact Subgroup.mem_zpowers k
  have hknotK : k ∉ K := by
    intro hkK
    have hcent : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨k, hkK⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H y =>
        apply Eq.symm
        change ((⟨k, hkK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) *
            (y : ↥K ⧸ CFSG.pCore 2 ↥K) =
          (y : ↥K ⧸ CFSG.pCore 2 ↥K) *
            ((⟨k, hkK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          QuotientGroup.eq_iff_div_mem]
        refine (Step163Alt.mem_pCore_two_iff _).mpr ?_
        simpa [div_eq_mul_inv, mul_assoc] using hksec.2 (y : G) y.2
    rw [hZcenter, Subgroup.mem_bot] at hcent
    have hkθ : k ∈ CFSG.Open.pCoreOf 2 K := by
      have hmem : (⟨k, hkK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff (⟨k, hkK⟩ : ↥K)).mp hcent
      exact (Step163Alt.mem_pCore_two_iff (⟨k, hkK⟩ : ↥K)).mp hmem
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
      ⟨k, hkθ⟩
    have hm' : k ^ 2 ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    exact hk1 (Step163Alt.eq_one_of_two_three (m := m) (n := 1) hm'
      (by simpa using hk3))
  have hknotAK : k ∉ (A ⊓ K : Subgroup G) := fun h => hknotK h.2
  have hdisj' : Subgroup.zpowers k ⊓ (A ⊓ K : Subgroup G) = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers k ⊓ (A ⊓ K) : Subgroup G) ∣ 3 := by
      rw [← hkorder, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers k ⊓ (A ⊓ K : Subgroup G) = Subgroup.zpowers k :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [h3, Nat.card_zpowers, hkorder])
      have hk' : k ∈ Subgroup.zpowers k ⊓ (A ⊓ K : Subgroup G) := by
        rw [heq]
        exact Subgroup.mem_zpowers k
      exact hknotK hk'.2.2
  have hdisj : (A ⊓ K : Subgroup G) ⊓ Subgroup.zpowers k = ⊥ := by
    rw [inf_comm]
    exact hdisj'
  have hcommSup : ∀ x ∈ (A ⊓ K : Subgroup G), ∀ y ∈ Subgroup.zpowers k,
      x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx.1⟩
      ⟨y, Subgroup.zpowers_le.mpr hkA hy⟩)
  have hcard_sup : Nat.card ((A ⊓ K) ⊔ Subgroup.zpowers k : Subgroup G) =
      Nat.card (A ⊓ K : Subgroup G) * 3 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (L := A ⊓ K) (R := Subgroup.zpowers k) hcommSup).1
    rw [hdisj, Subgroup.card_bot, Nat.card_zpowers, hkorder, mul_one] at h
    exact h
  have hsup_le_A : ((A ⊓ K) ⊔ Subgroup.zpowers k : Subgroup G) ≤ A :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hkA)
  have hcard_le : Nat.card ((A ⊓ K) ⊔ Subgroup.zpowers k : Subgroup G) ≤ 27 := by
    have h := Subgroup.card_le_of_le hsup_le_A
    rwa [hA27] at h
  have hcard_inf_le : Nat.card (A ⊓ K : Subgroup G) ≤ 9 := by
    rw [hcard_sup] at hcard_le
    omega
  have hcard9 : Nat.card (A ⊓ K : Subgroup G) = 9 :=
    le_antisymm hcard_inf_le h9le
  have hsup_eq : (A ⊓ K) ⊔ Subgroup.zpowers k = A := by
    apply Subgroup.eq_of_le_of_card_ge hsup_le_A
    rw [hA27, hcard_sup, hcard9]
  exact ⟨hcard9, hknotK, hsup_eq⟩

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16
