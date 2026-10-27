module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import Certificates.Certificate13720
public import Certificates.Certificate1952
public import CFSG.LocalAnalysis.StandardType.GGOrdPToralE8Holds
import CFSG.LocalAnalysis.StandardType.GGOrdPToralE8FiveWeyl
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameDiag
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangRational
import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8Five
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralFive
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusDescent
import CFSG.RankThree.PartOne.KE.CTLangData
import CFSG.RankThree.PartOne.KE.SigmaUntwisted2

public section

namespace CFSG.StandardType.OrdPToralE8Five

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance ordPToralE8FiveFactFiveHolds : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem frameDiag_pow_eq {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 5 = 1) (m : ℕ)
    (x : Fin Tag.E8.rank → ZMod 5) :
    ExcFrames.frameDiag (τ := Tag.E8) ζ hζ x ^ m =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (m • x) := by
  induction m with
  | zero => rw [pow_zero, zero_nsmul, ExcFrames.frameDiag_zero]
  | succ m ih => rw [pow_succ, ih, ← ExcFrames.frameDiag_add, ← succ_nsmul]

theorem ggOrdPToralMax_adjointE8_five
    {K : Type} [Field K] [Finite K] [CharP K 2] (h5 : 5 ∣ Nat.card K * Nat.card K + 1) :
    GGOrdPToralMax (adjointGroup .E8 K) 5 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def 2 (f : ℕ) c
  have h2K : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 f.ne_zero
  have h5K : ¬ 5 ∣ Nat.card K := fun h => by
    have h1 : 5 ∣ Nat.card K * Nat.card K := Dvd.dvd.mul_right h _
    have h2 := (Nat.dvd_add_right h1).1 h5
    omega
  obtain ⟨g₀, hg₀C, hg₀⟩ := CFSG.RankThree.PartOne.KE.lang_conjugator Tag.E8 K (ℓ := 2)
    (f := (f : ℕ)) f.pos L NoOffRest.weylE8W
  have h5L : ¬ ringChar L ∣ 5 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨ζ, hζo⟩ := NoOffE8Five.exists_unit_orderOf_five_of_isAlgClosed (L := L) h5L
  have hζ : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hkey : ∀ x : ZMod 5, x * x + 1 = 0 → (-x) * (-x) = -1 ∧ x * (-x) = 1 := by decide
  have hqq : ((Nat.card K : ℕ) : ZMod 5) * ((Nat.card K : ℕ) : ZMod 5) + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 h5
    push_cast at h
    exact h
  obtain ⟨hlam, hqlam⟩ := hkey _ hqq
  set lam : ZMod 5 := -((Nat.card K : ℕ) : ZMod 5) with hlamdef
  obtain ⟨ι, hιinj, hιval⟩ := NoOffE8Five.exists_langTorsionHom hFr hζo hζ hqlam hg₀C hg₀
  obtain ⟨ι₂, hι₂inj, hcl⟩ :=
    NoOffE8Five.exists_conjClass_of_lang hFr h2K hζo hζ hlam hqlam h5 hg₀C hg₀
  have hdet : IsUnit (((Tag.E8).symmetrizedCartan.det : ℤ) : ZMod 5) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by norm_num)
  set n : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W with hn
  have hnC : n ∈ adjointGroup Tag.E8 L := canonicalRep_mem_adjointGroup _ L _
  set F : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hF
  have hFC : ∀ g ∈ adjointGroup Tag.E8 L, F g ∈ adjointGroup Tag.E8 L := fun g hg =>
    entrywiseFrobGL_mem 2 (f : ℕ) hg
  have hcardX : Nat.card ι.range = 5 ^ 4 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top]
    exact NoOffRest.card_eigE8 (by norm_num) hlam
  have hcardX₂ : Nat.card ι₂.range = 5 ^ 4 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hι₂inj, Subgroup.card_top]
    exact NoOffRest.card_eigE8 (by norm_num) hlam
  intro u hu
  set ub : ModGL Tag.E8 L := CFSG.RankThree.PartOne.KE.adjEmb Tag.E8 K L u with hub
  have hubF : F ub = ub := CFSG.RankThree.PartOne.KE.adjEmb_frobenius Fr hFr u
  have hubC : ub ∈ adjointGroup Tag.E8 L := CFSG.RankThree.PartOne.KE.adjEmb_mem u
  have hub5 : ub ^ 5 = 1 := by rw [hub, ← map_pow, hu, map_one]
  set t : ModGL Tag.E8 L := g₀⁻¹ * ub * g₀ with ht
  have htC : t ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem (inv_mem hg₀C) hubC) hg₀C
  have ht5 : t ^ 5 = 1 := by
    rw [ht, show g₀⁻¹ * ub * g₀ = g₀⁻¹ * ub * g₀⁻¹⁻¹ by rw [inv_inv], conj_pow, hub5, mul_one,
      mul_inv_cancel]
  have htS : n * F t * n⁻¹ = t := by
    have h1 : F g₀ = g₀ * n := hg₀
    rw [ht, map_mul, map_mul, map_inv, h1, hubF]
    group
  have hFt : F t = n⁻¹ * t * n :=
    calc F t = n⁻¹ * (n * F t * n⁻¹) * n := by group
      _ = n⁻¹ * t * n := by rw [htS]
  have hconjn : ∀ x : Fin Tag.E8.rank → ZMod 5,
      n * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ x * n⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (TableBExc.torusAct .E8 5 NoOffRest.weylE8W x) :=
    fun x => ExcFrames.canonicalRep_conj_frameDiag ζ hζ _ x
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.E8 5 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_five_of_chainBlock
      (fun _ hγ => CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E8 hγ)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.chainBlockToral_E8_four
  obtain ⟨g, hgC, hgT⟩ := ExcElemToral.exists_conj_mem_torusGroup_of_pow_eq_one hmon h5K htC ht5
  have hd5 : (g * t * g⁻¹) ^ 5 = 1 := by rw [conj_pow, ht5, mul_one, mul_inv_cancel]
  obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet (v := g * t * g⁻¹) ⟨hgT, hd5⟩
  have hFd : ∀ x : Fin Tag.E8.rank → ZMod 5, F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ x) =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (Nat.card K • x) := fun x => by
    rw [hF, ExcFrames.frameDiag, CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr,
      ← rootDiagUnit_pow, ← ExcFrames.frameDiag, frameDiag_pow_eq]
  have hiso : NoOffRest.bform .E8 5 s s = 0 := by
    set c₁ : ModGL Tag.E8 L := n * F g * n⁻¹ * g⁻¹ with hc₁
    have hc₁C : c₁ ∈ adjointGroup Tag.E8 L :=
      mul_mem (mul_mem (mul_mem hnC (hFC g hgC)) (inv_mem hnC)) (inv_mem hgC)
    have hconj : c₁ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * c₁⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          (Nat.card K • TableBExc.torusAct .E8 5 NoOffRest.weylE8W s) := by
      have h1 : n * F (g * t * g⁻¹) * n⁻¹ = c₁ * (g * t * g⁻¹) * c₁⁻¹ := by
        rw [hc₁, map_mul, map_mul, map_inv, hFt]
        group
      have hlin : TableBExc.torusAct .E8 5 NoOffRest.weylE8W (Nat.card K • s) =
          Nat.card K • TableBExc.torusAct .E8 5 NoOffRest.weylE8W s :=
        map_nsmul (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W) (Nat.card K) s
      calc c₁ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * c₁⁻¹ = c₁ * (g * t * g⁻¹) * c₁⁻¹ := by
            rw [hs]
        _ = n * F (g * t * g⁻¹) * n⁻¹ := h1.symm
        _ = n * F (ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s) * n⁻¹ := by rw [hs]
        _ = n * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (Nat.card K • s) * n⁻¹ := by rw [hFd]
        _ = _ := by rw [hconjn, hlin]
    obtain ⟨y, hy⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family Tag.E8 L
      (ι := Unit) (fun _ => TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord .E8 5 (Nat.card K • TableBExc.torusAct .E8 5 NoOffRest.weylE8W s)))
      (fun _ => TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 5 s)) hc₁C
      (fun _ => hconj)
    have hy' := hy ()
    change ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
        (Nat.card K • TableBExc.torusAct .E8 5 NoOffRest.weylE8W s) =
      canonicalRep (coxeterSystem Tag.E8) L y * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s *
        (canonicalRep (coxeterSystem Tag.E8) L y)⁻¹ at hy'
    rw [ExcFrames.canonicalRep_conj_frameDiag] at hy'
    have hys := ExcFrames.frameDiag_injective hζo hζ hdet hy'
    have hxs : TableBExc.torusAct .E8 5 (NoOffRest.weylE8W⁻¹ * y) s = Nat.card K • s := by
      rw [TableBExc.torusAct_mul, ← hys, ← NoOffRest.torusLin_apply, map_nsmul,
        NoOffRest.torusLin_apply, ← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
    have hb := NoOffRest.bform_torusAct (NoOffRest.weylE8W⁻¹ * y) s s
    have hm1 : ((Nat.card K : ℕ) : ZMod 5) * ((Nat.card K : ℕ) : ZMod 5) = -1 := by
      exact eq_neg_of_add_eq_zero_left hqq
    rw [hxs, ← Nat.cast_smul_eq_nsmul (ZMod 5), LinearMap.map_smul₂, map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, hm1] at hb
    have hkey2 : ∀ B : ZMod 5, -1 * B = B → B = 0 := by decide
    exact hkey2 _ hb
  obtain ⟨v, hv⟩ := exists_torusAct_mem_eigE8_of_bform_eq_zero hlam hiso
  set e : Fin Tag.E8.rank → ZMod 5 := TableBExc.torusAct .E8 5 v s with he
  set nv : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hnv
  have hnvC : nv ∈ adjointGroup Tag.E8 L := canonicalRep_mem_adjointGroup _ L _
  set d' : ModGL Tag.E8 L := ExcFrames.frameDiag (τ := Tag.E8) ζ hζ e with hd'
  set g' : ModGL Tag.E8 L := nv * g with hg'
  have hg'C : g' ∈ adjointGroup Tag.E8 L := mul_mem hnvC hgC
  have hg't : g' * t * g'⁻¹ = d' := by
    have hconjv : nv * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * nv⁻¹ = d' :=
      ExcFrames.canonicalRep_conj_frameDiag ζ hζ v s
    rw [← hconjv, hs, hg']
    group
  have hd'T := (NoOffE8Five.frameDiag_mem_twistedTorus_iff hFr hζo hζ hqlam e).2 hv
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorus] at hd'T
  have hd'S : n * F d' * n⁻¹ = d' := hd'T.2
  set a' : Fin Tag.E8.rank → Lˣ := TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 5 e)
    with ha'
  have hd'a : d' = rootDiagUnit Tag.E8 a' := rfl
  have ha'5 : ∀ i, a' i ^ 5 = 1 := fun i => by
    rw [ha', TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hlamval : ¬ 5 ∣ lam.val := by
    intro h
    have h0 : lam = 0 := by
      rw [← ZMod.natCast_zmod_val lam, (ZMod.natCast_eq_zero_iff _ _).2 h]
    rw [h0, mul_zero] at hlam
    exact absurd hlam (by decide)
  have hQ : n * rootDiagUnit Tag.E8 a' * n⁻¹ = rootDiagUnit Tag.E8 a' ^ lam.val := by
    have hFd' : F d' = d' ^ Nat.card K := by rw [hd', hFd, frameDiag_pow_eq]
    have h1 : (n * d' * n⁻¹) ^ Nat.card K = d' := by
      rw [conj_pow, ← hFd', hd'S]
    have h2 : (n * d' * n⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hd', ExcFrames.frameDiag_pow, mul_one, mul_inv_cancel]
    have h3 : (Nat.card K * lam.val) % 5 = 1 := by
      have : ((Nat.card K * lam.val : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact hqlam
      rw [ZMod.natCast_eq_natCast_iff'] at this
      exact this
    rw [← hd'a]
    calc n * d' * n⁻¹ = (n * d' * n⁻¹) ^ (Nat.card K * lam.val) := by
          rw [pow_eq_pow_mod (Nat.card K * lam.val) h2, h3, pow_one]
      _ = d' ^ lam.val := by rw [pow_mul, h1]
  have hLang := CFSG.HardMathSupport.Timmesfeld.Steinberg.toral_centralizer_Lang_E8_five 2 L
    (by norm_num) a' ha'5 (f : ℕ) f.pos hnC hlamval hQ
  set c : ModGL Tag.E8 L := (n * F g' * n⁻¹) * g'⁻¹ with hc
  have hcC : c ∈ toralCentralizer Tag.E8 L a' := by
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (mul_mem hnC (hFC g' hg'C)) (inv_mem hnC))
      (inv_mem hg'C), ?_⟩
    have h1 : c * d' * c⁻¹ = d' := by
      have h2 : n * F (g' * t * g'⁻¹) * n⁻¹ = c * (g' * t * g'⁻¹) * c⁻¹ := by
        rw [hc, map_mul, map_mul, map_inv, hFt]
        group
      rw [← hg't, ← h2, hg't, hd'S]
    rw [← hd'a]
    have hcomm : c * d' = d' * c :=
      calc c * d' = (c * d' * c⁻¹) * c := by group
        _ = d' * c := by rw [h1]
    calc d' * c * d'⁻¹ = c * d' * d'⁻¹ := by rw [hcomm]
      _ = c := by group
  obtain ⟨z, hzC, hz⟩ := hLang c⁻¹ (inv_mem hcC)
  obtain ⟨hzG, hzd⟩ := mem_toralCentralizer.1 hzC
  rw [← hd'a] at hzd
  rw [frobTwistGL_apply] at hz
  set u' : ModGL Tag.E8 L := z * g' with hu'
  have hu'C : u' ∈ adjointGroup Tag.E8 L := mul_mem hzG hg'C
  have hu'S : n * F u' * n⁻¹ = u' := by
    have h1 : n * F z * n⁻¹ = z * c⁻¹ := by
      have := congrArg (z * ·) hz
      simp only [mul_inv_cancel_left] at this
      exact this
    rw [hu', map_mul]
    calc n * (F z * F g') * n⁻¹ = (n * F z * n⁻¹) * (n * F g' * n⁻¹) := by group
      _ = z * c⁻¹ * (c * g') := by rw [h1, hc]; group
      _ = z * g' := by group
  have hu't : u' * t * u'⁻¹ = d' := by
    have hcz : d' * z = z * d' :=
      calc d' * z = (d' * z * d'⁻¹) * d' := by group
        _ = z * d' := by rw [hzd]
    have h1 : z * d' * z⁻¹ = d' :=
      calc z * d' * z⁻¹ = d' * z * z⁻¹ := by rw [hcz]
        _ = d' := by group
    rw [hu', ← h1, ← hg't]
    group
  set yb : ModGL Tag.E8 L := g₀ * u' * g₀⁻¹ with hyb
  have hybC : yb ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem hg₀C hu'C) (inv_mem hg₀C)
  have hybF : F yb = yb := by
    have h1 : F g₀ = g₀ * n := hg₀
    rw [hyb, map_mul, map_mul, map_inv, h1]
    calc g₀ * n * F u' * (g₀ * n)⁻¹ = g₀ * (n * F u' * n⁻¹) * g₀⁻¹ := by group
      _ = g₀ * u' * g₀⁻¹ := by rw [hu'S]
  obtain ⟨y₀, hy₀, hy₀y⟩ := CFSG.RankThree.PartOne.KE.qplus_frobenius_fixed_mem (Or.inr rfl)
    (K := K) Fr hFr hybC hybF
  set Y : adjointGroup Tag.E8 K := ⟨y₀, hy₀⟩ with hY
  have hYb : CFSG.RankThree.PartOne.KE.adjEmb Tag.E8 K L Y = yb := hy₀y
  have hYu : Y * u * Y⁻¹ = ι (Multiplicative.ofAdd ⟨e, hv⟩) := by
    apply CFSG.RankThree.PartOne.KE.adjEmb_injective (L := L)
    rw [hιval, NoOffE8Five.frameElt_apply, map_mul, map_mul, map_inv, hYb, ← hub, hyb]
    calc g₀ * u' * g₀⁻¹ * ub * (g₀ * u' * g₀⁻¹)⁻¹ = g₀ * (u' * t * u'⁻¹) * g₀⁻¹ := by
          rw [ht]; group
      _ = g₀ * d' * g₀⁻¹ := by rw [hu't]
  refine ⟨ι.range.map (MulAut.conj Y⁻¹).toMonoidHom,
    OrdPInnerExc.isElemAbelian_map _ (NoOffE8Five.isElemAbelian_range_of_module ι), ?_, ?_⟩
  · refine ⟨ι (Multiplicative.ofAdd ⟨e, hv⟩), ⟨_, rfl⟩, ?_⟩
    change Y⁻¹ * ι (Multiplicative.ofAdd ⟨e, hv⟩) * Y⁻¹⁻¹ = u
    rw [← hYu]
    group
  · intro A hA
    rw [Subgroup.card_map_of_injective (MulAut.conj Y⁻¹).injective, hcardX]
    by_cases h4 : 5 ^ 4 ≤ Nat.card A
    · obtain ⟨c₂, hc₂⟩ := hcl A hA h4
      rw [← hc₂, Subgroup.card_map_of_injective (MulAut.conj c₂).injective, hcardX₂]
    · omega

theorem ggOrdPToralE8FiveFour_holds :
    GGOrdPToralE8FiveFour := by
  intro f h1 h2 _
  have hf : f ≠ 0 := by
    rintro rfl
    exact h1 (by norm_num)
  refine ggOrdPToralMax_adjointE8_five ?_
  rw [GaloisField.card 2 f hf, ← Nat.modEq_zero_iff_dvd]
  have h0 : ¬ 5 ∣ 2 ^ f := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)) (by norm_num)
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hm : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by omega
  unfold Nat.ModEq
  rw [Nat.add_mod, Nat.mul_mod]
  rcases hm with hm | hm <;> rw [hm]

end CFSG.StandardType.OrdPToralE8Five

end
