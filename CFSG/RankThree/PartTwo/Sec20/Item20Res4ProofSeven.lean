module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofSeven
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenL
public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSix
import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofComm
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

noncomputable abbrev iTwenty {G : Type} [Group G] (M N : Subgroup G) (c : G) : Subgroup G :=
  normalClosureIn (kTwenty M c ⊓ N) c

noncomputable abbrev eTwenty {G : Type} [Group G] (M N : Subgroup G) (c : G) (T : Subgroup G) :
    Subgroup G :=
  ⁅zTwenty T, iTwenty M N c⁆

noncomputable abbrev fTwenty {G : Type} [Group G] (M N : Subgroup G) (c : G) (T : Subgroup G) :
    Subgroup G :=
  zTwenty T ⊓ eTwenty M N c T

@[expose] def Step207Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    eTwenty M N c T ≠ ⊥ → L ≤ Subgroup.centralizer (eTwenty M N c T : Set G) →
      ∃ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) ∧
        kTwenty M c ≤ (normalClosureIn (kTwenty M c ⊓
            Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹) ⊔ iTwenty M N c) ⊔
          CFSG.Open.pCoreOf 2 (kTwenty M c)

@[expose] def Step207YTheta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    eTwenty M N c T ≠ ⊥ → L ≤ Subgroup.centralizer (eTwenty M N c T : Set G) →
    ∀ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) →
        ⁅L, normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)⁆ ≤
          inSubgroup (CFSG.pPrimeCore 3)
            (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹))

namespace Res4

variable {G : Type} [Group G]

def commIn (M L : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ M ∧ ∀ l ∈ L, ⁅y, l⁆ ∈ M}
  one_mem' := ⟨M.one_mem, fun l _ => by rw [commutatorElement_one_left]; exact M.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hal⟩ ⟨hb, hbl⟩
    refine ⟨M.mul_mem ha hb, fun l hl => ?_⟩
    have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha (hbl l hl)) (M.inv_mem ha)) (hal l hl)
  inv_mem' := by
    rintro a ⟨ha, hal⟩
    refine ⟨M.inv_mem ha, fun l hl => ?_⟩
    have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.inv_mem ha) (M.inv_mem (hal l hl))) ha

theorem conj_mem_commIn {M L : Subgroup G} {w y : G} (hwM : w ∈ M)
    (hwL : w ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ commIn M L) :
    w * y * w⁻¹ ∈ commIn M L := by
  refine ⟨M.mul_mem (M.mul_mem hwM hy.1) (M.inv_mem hwM), fun l hl => ?_⟩
  have hl' : w⁻¹ * l * w ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwL) l).mp hl
    simpa using this
  have e : ⁅w * y * w⁻¹, l⁆ = w * ⁅y, w⁻¹ * l * w⁆ * w⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact M.mul_mem (M.mul_mem hwM (hy.2 _ hl')) (M.inv_mem hwM)

noncomputable def conjClosure (W Y : Subgroup G) : Subgroup G :=
  ⨆ (w : G) (_ : w ∈ W), Y.map (MulAut.conj w).toMonoidHom

theorem le_conjClosure (W Y : Subgroup G) : Y ≤ conjClosure W Y := by
  intro y hy
  have h : Y.map (MulAut.conj (1 : G)).toMonoidHom ≤ conjClosure W Y :=
    le_iSup₂_of_le (f := fun (w : G) (_ : w ∈ W) => Y.map (MulAut.conj w).toMonoidHom)
      (1 : G) W.one_mem le_rfl
  exact h ⟨y, hy, by simp⟩

theorem conjClosure_le {W Y X : Subgroup G}
    (h : ∀ w ∈ W, Y.map (MulAut.conj w).toMonoidHom ≤ X) : conjClosure W Y ≤ X :=
  iSup₂_le h

theorem le_normalizer_conjClosure [Finite G] (W Y : Subgroup G) :
    W ≤ Subgroup.normalizer (conjClosure W Y : Set G) := by
  intro w₀ hw₀
  apply mem_normalizer_of_map_conj_le
  rw [conjClosure, Subgroup.map_iSup]
  refine iSup_le fun w => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hw => ?_
  rw [Subgroup.map_map]
  have e : (MulAut.conj w₀).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj (w₀ * w)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  exact le_iSup₂_of_le (f := fun (w : G) (_ : w ∈ W) => Y.map (MulAut.conj w).toMonoidHom)
    (w₀ * w) (W.mul_mem hw₀ hw) le_rfl

theorem mem_map_conj_inv_iff {P : Subgroup G} {x y : G} :
    y ∈ P.map (MulAut.conj x⁻¹).toMonoidHom ↔ x * y * x⁻¹ ∈ P := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show x * (x⁻¹ * p * x⁻¹⁻¹) * x⁻¹ = p by group]
    exact hp
  · intro h
    refine ⟨x * y * x⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem le_normalizer_map_conj_inv {A P : Subgroup G} {x : G}
    (h : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (P : Set G)) :
    A ≤ Subgroup.normalizer ((P.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  intro a ha
  have hxa : x * a * x⁻¹ ∈ Subgroup.normalizer (P : Set G) := h ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_map_conj_inv_iff, mem_map_conj_inv_iff, Subgroup.mem_normalizer_iff.mp hxa]
  rw [show x * a * x⁻¹ * (x * y * x⁻¹) * (x * a * x⁻¹)⁻¹ = x * (a * y * a⁻¹) * x⁻¹ by group]

theorem eq_one_of_mem_of_isPGroup_two [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) {c : G}
    (hcP : c ∈ P) (hc3 : c ^ 3 = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
  have hk' : c ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf c ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem le_of_le_normalizer_of_coprime_three [Finite G] {A M R : Subgroup G}
    (h : Sec18Std G A M) (hR : Nat.Coprime 3 (Nat.card R))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : R ≤ M := by
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h27 := hA.2
    rw [hbot, Subgroup.card_bot] at h27
    omega
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three A R hA.1 hAne hAR hR
  rw [← hgen]
  refine iSup_le fun D => iSup_le fun hDA => iSup_le fun hD => ?_
  refine inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans ?_)
  refine (Source.normalizer_le_aschCore hA.1 hA.2 hDA
    (Source.card_eq_nine_of_index hA.2 hDA hD)).trans ?_
  rw [aschCore_eq_gamma_of_mem_partTwoE h.mem_partTwoE]
  exact h.mem_scriptM.2

end Res4

variable {G : Type} [Group G] [Finite G]

theorem not_mem_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (hc1 : c ≠ 1) : c ∉ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcL
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hsec : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    have : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
    rwa [← hT.centralizer_eq] at this
  obtain ⟨e⟩ := hLq
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := isSimpleGroup_projSL_three_galois_four
    exact e.isSimpleGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set c' : ↥L := ⟨c, hcL⟩ with hc'
  have hcen : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, q * π c' = π c' * q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    have h1 : c' * y * c'⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L :=
      (mem_pCore_iff_mem_pCoreOf_two _).mpr (hsec.2 y y.2)
    have h2 : π (c' * y * c'⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π y * π c' = (π c' * π y * (π c')⁻¹ * (π y)⁻¹)⁻¹ * (π c' * π y) := by group
      _ = π c' * π y := by rw [h2, inv_one, one_mul]
  have hN : (Subgroup.zpowers (π c')).Normal := by
    constructor
    intro z hz q
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hqc : Commute q (π c') := hcen q
    have hcomm : Commute q ((π c') ^ k) := hqc.zpow_right k
    rw [hcomm.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hπc3 : (π c') ^ 3 = 1 := by
    rw [← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (π c')) with hbot | htop
  ·
    have h1 : π c' = 1 := by
      have := Subgroup.mem_zpowers (π c')
      rwa [hbot, Subgroup.mem_bot] at this
    have h2 : c' ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : c ∈ CFSG.Open.pCoreOf 2 L := (mem_pCore_iff_mem_pCoreOf_two _).mp h2
    exact hc1 (Res4.eq_one_of_mem_of_isPGroup_two
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) h3 hc3)
  ·
    have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 := by
      rw [Nat.card_congr e.toEquiv, KFacts.L34.card_projSL]
    have hle : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ 3 := by
      rw [← Subgroup.card_top, ← htop, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hπc3)
    omega

theorem eq_zpowers_sup_inf_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hc1 : c ≠ 1) : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hAE := hT.mem_partTwoE.1
  have hc3 : c ^ 3 = 1 := hAE.2 c hcA
  have hA27 : Nat.card A = 27 := (isE27_of_mem_partTwoE hT.mem_partTwoE).2
  have hcL := not_mem_core hT hLq hc1
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hz : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hoc]
  have hinf : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ (A ⊓ L)) ∣ 3 :=
      hz ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ (A ⊓ L) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hz, h3])
      have : c ∈ Subgroup.zpowers c ⊓ (A ⊓ L) := by
        rw [heq]
        exact Subgroup.mem_zpowers c
      exact hcL this.2.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAE.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hcomm : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ A ⊓ L, a * b = b * a := fun a ha b hb =>
    hAc a (Subgroup.zpowers_le.mpr hcA ha) b hb.1
  have hcard := Sec3.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, hz, h9] at hcard
  exact (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
    (by rw [hcard, hA27])).symm

theorem step207K0Sub_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (hLM : ¬ L ≤ M) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (h3 : KIsL3 M c) (hTN : T ≤ N)
    (hCK : ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hLE : L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G))
    (hS : ∃ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) ∧
      kTwenty M c ≤ (normalClosureIn (kTwenty M c ⊓
          Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹) ⊔ iTwenty M N c) ⊔
        CFSG.Open.pCoreOf 2 (kTwenty M c))
    (hY : ∀ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) →
        ⁅L, normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)⁆ ≤
          inSubgroup (CFSG.pPrimeCore 3)
            (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)))
    {H : Subgroup G} (hH : H ∈ scriptHStar A M) (hL : L = inSubgroup perfectResidual H) :
    ∃ K₀ X : Subgroup G, K₀ ≤ kTwenty M c ∧
      kTwenty M c ≤ K₀ ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      X ≠ ⊤ ∧ H ≤ X ∧ K₀ ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hCK
    have h1 : kTwenty M (1 : G) = ⊥ := by
      rw [eq_bot_iff, kTwenty, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, -, rfl⟩
      simp
    rw [h1, bot_inf_eq]
    exact bot_le
  obtain ⟨x, hxK, hxB, hcx, hKK0⟩ := hS
  have hYL := hY x hxK hxB hcx
  set K := kTwenty M c with hKdef
  set I := iTwenty M N c with hIdef
  set F := fTwenty M N c T with hFdef
  set c' := x * c * x⁻¹ with hc'def
  set Y := normalClosureIn (Subgroup.centralizer (F : Set G)) c' with hYdef
  set K₀ := normalClosureIn (K ⊓ Subgroup.centralizer (F : Set G)) c' ⊔ I with hK₀def
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hAM : A ≤ M := le_of_hyp201 hT.toHyp201
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hxM : x ∈ M := hKM hxK
  have hc'K : c' ∈ K := K.mul_mem (K.mul_mem hxK hcK) (K.inv_mem hxK)
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hIK : I ≤ K := (normalClosureIn_le (show c ∈ K ⊓ N from ⟨hcK, hcN⟩)).trans inf_le_left
  have hK₀K : K₀ ≤ K :=
    sup_le ((normalClosureIn_le (show c' ∈ K ⊓ Subgroup.centralizer (F : Set G) from
      ⟨hc'K, hcx⟩)).trans inf_le_left) hIK
  have hCEF : Subgroup.centralizer (eTwenty M N c T : Set G) ≤
      Subgroup.centralizer (F : Set G) :=
    Subgroup.centralizer_le (fun z hz => hz.2)
  have hBF : A ⊓ L ≤ Subgroup.centralizer (F : Set G) := (inf_le_right.trans hLE).trans hCEF
  have hO3Y : inSubgroup (CFSG.pPrimeCore 3) Y ≤ M := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set P := inSubgroup (CFSG.pPrimeCore 3) Y with hPdef
    have hYN : Y ≤ Subgroup.normalizer (P : Set G) := Sec14.le_normalizer_pPrimeCoreOf 3 Y
    have hCN : Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (P : Set G) :=
      (le_normalizer_normalClosureIn _ c').trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 Y)
    have hc'Y : c' ∈ Y := self_mem_normalClosureIn _ c'
    have hB' : (A ⊓ L).map (MulAut.conj x).toMonoidHom = A ⊓ L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxB
    have hAx : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (P : Set G) := by
      rw [eq_zpowers_sup_inf_core hT hLq h9 hc1, Subgroup.map_sup,
        MonoidHom.map_zpowers, hB']
      exact sup_le (Subgroup.zpowers_le.mpr (hYN hc'Y)) (hBF.trans hCN)
    have hcop : Nat.Coprime 3 (Nat.card (P.map (MulAut.conj x⁻¹).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
      exact Sec14.coprime_card_pPrimeCoreOf 3 Y
    have hP' := Res4.le_of_le_normalizer_of_coprime_three (sec18Std_of_hyp201 hT.toHyp201)
      hcop (Res4.le_normalizer_map_conj_inv hAx)
    intro p hp
    have hp' : x⁻¹ * p * x⁻¹⁻¹ ∈ M := hP' ⟨p, hp, rfl⟩
    have e : p = x * (x⁻¹ * p * x⁻¹⁻¹) * x⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hxM hp') (M.inv_mem hxM)
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  obtain ⟨α, -, hαk⟩ := exists_hom_sl3_of_odd hn e
  have hq : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne']
    exact two_pow_mod_three_of_odd hn
  have hLI : L ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_normalClosureIn_of_hom_core hT hN hAL hO2L hTN hq α hαk
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hK₀C : K₀ ≤ Res4.commIn M L := by
    refine sup_le ?_ ?_
    · rw [normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, hm, rfl⟩
      have hmY : m * c' * m⁻¹ ∈ Y := Subgroup.subset_closure ⟨m, hm.2, rfl⟩
      refine ⟨hKM (K.mul_mem (K.mul_mem hm.1 hc'K) (K.inv_mem hm.1)), fun l hl => ?_⟩
      have h1 : ⁅m * c' * m⁻¹, l⁆ ∈ ⁅Y, L⁆ := Subgroup.commutator_mem_commutator hmY hl
      rw [Subgroup.commutator_comm] at h1
      exact hO3Y (hYL h1)
    · intro i hi
      refine ⟨hKM (hIK hi), fun l hl => ?_⟩
      have h1 : l * i⁻¹ * l⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hLI hl) _).mp (I.inv_mem hi)
      rw [commutatorElement_def, show i * l * i⁻¹ * l⁻¹ = i * (l * i⁻¹ * l⁻¹) by group]
      exact hKM (hIK (I.mul_mem hi h1))
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact Sec18.le_normalizer_inSubgroup_perfectResidual H
  set K₁ := Res4.conjClosure (H ⊓ M) K₀ with hK₁def
  have hK₁C : K₁ ≤ Res4.commIn M L := Res4.conjClosure_le fun w hw => by
    rintro _ ⟨y, hy, rfl⟩
    exact Res4.conj_mem_commIn hw.2 (hHL hw.1) (hK₀C hy)
  have hK₁K : K₁ ≤ K := Res4.conjClosure_le fun w hw => by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMK hw.2) y).mp (hK₀K hy)
  have hK₁M : K₁ ≤ M := hK₁K.trans hKM
  have hKK₁ : K ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K :=
    hKK0.trans (sup_le_sup_right (Res4.le_conjClosure (H ⊓ M) K₀) _)
  have hT₁M : ⁅K₁, L⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro y hy l hl
    exact (hK₁C hy).2 l hl
  refine ⟨K₁, Subgroup.normalizer ((K₁ ⊔ ⁅K₁, L⁆ : Subgroup G) : Set G), hK₁K, hKK₁, ?_, ?_, ?_⟩
  ·
    intro hX
    have hYn : (K₁ ⊔ ⁅K₁, L⁆).Normal := Subgroup.normalizer_eq_top_iff.mp hX
    have : IsSimpleGroup G := hT.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₁ ⊔ ⁅K₁, L⁆) with hbot | htop
    · have hK₁1 : K₁ = ⊥ := le_bot_iff.mp (hbot ▸ le_sup_left)
      rw [hK₁1, bot_sup_eq] at hKK₁
      exact hc1 (Res4.eq_one_of_mem_of_isPGroup_two
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) (hKK₁ hcK) hc3)
    · apply hLM
      have hMtop : M = ⊤ := top_le_iff.mp (htop ▸ sup_le hK₁M hT₁M)
      rw [hMtop]
      exact le_top
  ·
    have hHM : H ⊓ M ≤ Subgroup.normalizer ((K₁ ⊔ ⁅K₁, L⁆ : Subgroup G) : Set G) := by
      intro w hw
      exact Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨Res4.le_normalizer_conjClosure (H ⊓ M) K₀ hw,
          Res3.le_normalizer_commutator (Res4.le_normalizer_conjClosure (H ⊓ M) K₀)
            (inf_le_left.trans hHL) hw⟩
    have hLX : L ≤ Subgroup.normalizer ((K₁ ⊔ ⁅K₁, L⁆ : Subgroup G) : Set G) := by
      intro l hl
      refine Res4.mem_normalizer_sup_of (fun y hy => ?_)
        (Res3.le_normalizer_commutator_right K₁ L hl)
      have e1 : l * y * l⁻¹ = ⁅l, y⁆ * y := by
        rw [commutatorElement_def]
        group
      have h1 : ⁅l, y⁆ ∈ ⁅K₁, L⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hl hy
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
    have hHdef := (mem_scriptH_iff.mp (scriptHStar_subset A M hH)).2.1
    have hAH : A ≤ H := by
      rw [hHdef]
      exact le_sup_right.trans le_sup_left
    rw [hHdef, ← hL]
    refine sup_le (sup_le hLX ((le_inf hAH hAM).trans hHM)) ?_
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hHM
  ·
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.le_normalizer hk, by
        rw [Subgroup.commutator_comm]
        exact Res3.le_normalizer_commutator_right L K₁ hk⟩

section Certificates

theorem eq_zpowers_sup_inf_of_ctx20One (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20One G A M L N c T)
    (hc1 : c ≠ 1) : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
  eq_zpowers_sup_inf_core hT.toCtx20 (nonempty_quotient_of_hyp201One h184 hT.hyp201One)
    (card_inf_of_hyp201One h1812 h184 hT.hyp201One) hc1

theorem step207K0Sub_of_theta (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053) (hS : Step207Struct)
    (hY : Step207YTheta) : Step207K0Sub := by
  intro G _ _ A M L N c T hT hTN hCK hE hLE H hH hL
  have h := hT.hyp201One
  obtain ⟨H₀, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step207K0Sub_core hT.toCtx20 hN (le_normalizer_of_hyp201One h)
    (nonempty_quotient_of_hyp201One h184 h) (not_le_of_hyp201One h) (pCoreOf_le_of_hyp201One h)
    (card_inf_of_hyp201One h1812 h184 h)
    (h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT (h2051 G A M L N c T hT))) hTN hCK hLE
    (hS G A M L N c T hT hTN hCK hE hLE) (hY G A M L N c T hT hTN hCK hE hLE) hH hL

end Certificates

end CFSG.RankThree.PartTwo.Sec20
