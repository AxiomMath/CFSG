module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOneNineNarrow
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5Proof
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R913A5S
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5NHolds
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5L
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.GroupTheory.ThreeTranspositions.StrongSup
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def K_L35NoStrongFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 5 1 →
    ∀ N : Subgroup X, N ≠ ⊤ → ¬ IsStronglyPEmbedded 5 N

private theorem I9_eq_PPrimeCoreIn (H : Subgroup G) : I9 H = PPrimeCoreIn 3 H := rfl

private theorem not_le_M_of_hyp97 {D : Data G} {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) : ¬ L9 Y H ≤ D.M := by
  intro hLM
  exact hY.1.2.1.2.1 (by
    rw [eq_L9_sup_of_hyp91 hY.1]
    exact sup_le hLM inf_le_right)

private theorem five_dvd_card_inf_of_isAlt {D : Data G} {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5) :
    5 ∣ Nat.card ↥(L9 Y H ⊓ D.M) := by
  have h5bar : 5 ∣ Nat.card (Bar2 (Opp 3 Y)) := by
    rw [card_bar2_of_isAlt hA5]
    norm_num
  have h5X : 5 ∣ Nat.card (Opp 3 Y) :=
    h5bar.trans (Subgroup.card_dvd_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Opp 3 Y))))
  refine h5X.trans (Subgroup.card_dvd_of_le ?_)
  exact le_inf (opp_le_L9 Y H) ((opp_le_self 3 Y).trans hY.1.1.1)

private theorem subgroupOf_inf_I9_normal {Y H : Subgroup G} (hYH : Y ≤ H) :
    ((L9 Y H ⊓ I9 H).subgroupOf (L9 Y H)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  exact Subgroup.le_normalizer_inf Subgroup.le_normalizer
    ((L9_le_of_le hYH).trans (le_normalizer_I9 H))

private theorem eq_sup_I9_of_sup_eq_top {D : Data G} {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) {L B N : Subgroup G}
    (hL : L = L9 Y H) (hB : B = L9 Y H ⊓ D.M) (hN : N = L9 Y H ⊓ I9 H)
    (h : B.subgroupOf L ⊔ N.subgroupOf L = ⊤) :
    H = (H ⊓ D.M) ⊔ I9 H := by
  have hYH : Y ≤ H := hY.1.2.1.1
  have hLH : L9 Y H ≤ H := L9_le_of_le hYH
  have hBle : B ≤ H ⊓ D.M := by
    rw [hB]
    exact le_inf (inf_le_left.trans hLH) inf_le_right
  have hNle : N ≤ I9 H := by
    rw [hN]
    exact inf_le_right
  have hNnormal : (N.subgroupOf L).Normal := by
    rw [hN, hL]
    exact subgroupOf_inf_I9_normal hYH
  have hLle : L9 Y H ≤ B ⊔ N := by
    intro l hl
    have hmem : (⟨l, by rw [hL]; exact hl⟩ : ↥L) ∈ B.subgroupOf L ⊔ N.subgroupOf L := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨b, hb, n, hn, hbn⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := B.subgroupOf L) (t := N.subgroupOf L)
        (ht := hNnormal)).1 hmem
    have hbG : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
    have hnG : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
    have heq : l = (b : G) * (n : G) := by
      have hval := congrArg (Subtype.val (p := fun x => x ∈ L)) hbn
      exact hval.symm
    rw [heq]
    exact (B ⊔ N).mul_mem ((le_sup_left : B ≤ B ⊔ N) hbG) ((le_sup_right : N ≤ B ⊔ N) hnG)
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥H)))
  conv_lhs => rw [eq_L9_sup_of_hyp91 hY.1]
  exact sup_le (hLle.trans (sup_le (hBle.trans le_sup_left) (hNle.trans le_sup_right)))
    (le_sup_left : H ⊓ D.M ≤ (H ⊓ D.M) ⊔ I9 H)

private theorem eq_sup_I9_of_five_dvd {D : Data G} {Y H D₃ S : Subgroup G}
    (hsp : IsStronglyPEmbedded 5 D.M) (hY : Hyp97 D Y H D₃ S)
    (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5)
    (h5N : 5 ∣ Nat.card ↥(L9 Y H ⊓ I9 H)) :
    H = (H ⊓ D.M) ⊔ I9 H := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let L := L9 Y H
  let B := L ⊓ D.M
  let N := L ⊓ I9 H
  have hspB : IsStronglyPEmbedded 5 (B.subgroupOf L) := by
    have hdvd : 5 ∣ Nat.card ↥B := by simpa [B] using five_dvd_card_inf_of_isAlt hY hA5
    exact hsp.subgroupOf (by simpa [L] using not_le_M_of_hyp97 hY) hdvd
  obtain ⟨P, hPsyl, hPB⟩ := hspB.exists_isSylowOf_le
  have hPsyl' : IsSylowOf 5 P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hNnormal : (N.subgroupOf L).Normal := by
    change ((L9 Y H ⊓ I9 H).subgroupOf (L9 Y H)).Normal
    exact subgroupOf_inf_I9_normal hY.1.2.1.1
  have hPN : IsSylowOf 5 (P ⊓ N.subgroupOf L) (N.subgroupOf L) :=
    hPsyl'.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hPNe : P ⊓ N.subgroupOf L ≠ ⊥ := by
    intro hbot
    have hcard := hPN.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hdvd : 5 ∣ Nat.card ↥(N.subgroupOf L) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      simpa [N, L] using h5N
    have hfac : 1 ≤ (Nat.card ↥(N.subgroupOf L)).factorization 5 :=
      Nat.prime_five.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    have hge : 5 ≤ 5 ^ (Nat.card ↥(N.subgroupOf L)).factorization 5 := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 5) hfac
    omega
  have hUleB : P ⊓ N.subgroupOf L ≤ B.subgroupOf L := inf_le_left.trans hPB
  have hU5 : IsPGroup 5 ↥(P ⊓ N.subgroupOf L) := hPN.isPGroup
  have hNormU : normalizer (((P ⊓ N.subgroupOf L : Subgroup ↥L)) : Set ↥L) ≤ B.subgroupOf L :=
    hspB.normalizer_le hPNe hU5 hUleB
  obtain ⟨Q, hQ⟩ := hPN.exists_sylow_eq_subgroupOf
  have hmapQ : Subgroup.map (N.subgroupOf L).subtype (Q : Subgroup ↥(N.subgroupOf L)) =
      P ⊓ N.subgroupOf L := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN.le]
  have hfr := Sylow.normalizer_sup_eq_top (N := N.subgroupOf L) (P := Q)
  rw [hmapQ] at hfr
  have hBN : B.subgroupOf L ⊔ N.subgroupOf L = ⊤ := by
    rw [eq_top_iff, ← hfr]
    exact sup_le (hNormU.trans le_sup_left) le_sup_right
  exact eq_sup_I9_of_sup_eq_top hY rfl rfl rfl hBN

private theorem not_eq_sup_I9_of_lie {D : Data G} {Y H D₃ S : Subgroup G}
    (hY : Hyp97 D Y H D₃ S) (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5)
    (hLie : LieModel (Lbar9 Y H) .PSL 3 5 1) :
    H ≠ (H ⊓ D.M) ⊔ I9 H := by
  classical
  intro hEq
  set X : Subgroup G := Opp 3 Y with hX
  set L : Subgroup G := L9 Y H with hL
  set I : Subgroup G := I9 H with hI
  have hXH : X ≤ H := (opp_le_self 3 Y).trans hY.1.2.1.1
  have hXM : X ≤ D.M := (opp_le_self 3 Y).trans hY.1.1.1
  have hXHM : X ≤ H ⊓ D.M := le_inf hXH hXM
  have hXL : X ≤ L := opp_le_L9 Y H
  have hLI : L ≤ H := L9_le_of_le hY.1.2.1.1
  have hIH : I ≤ H := Subgroup.map_subtype_le _
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_I9 H
  have hHMX : H ⊓ D.M ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXHM).1 (r9R5_holds D Y H D₃ S hY).1
  have hA5' : IsAlt (Bar2 X) 5 := by simpa [hX] using hA5
  have hInorm : (I.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 hHI
  have hsupH : (⊤ : Subgroup ↥H) = (H ⊓ D.M).subgroupOf H ⊔ I.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hIH, ← hEq, Subgroup.subgroupOf_self]
  have hgen : ∀ h : ↥H, X.map (MulAut.conj (h : G)).toMonoidHom ≤ X ⊔ I := by
    intro h
    obtain ⟨a, ha, i, hi, hai⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := (H ⊓ D.M).subgroupOf H)
        (t := I.subgroupOf H) (ht := hInorm)).1 (by rw [← hsupH]; exact Subgroup.mem_top h)
    have haG : (a : G) ∈ H ⊓ D.M := Subgroup.mem_subgroupOf.1 ha
    have hiG : (i : G) ∈ I := Subgroup.mem_subgroupOf.1 hi
    have hh : (h : G) = (a : G) * (i : G) := by
      have := congrArg (Subtype.val (p := fun x => x ∈ H)) hai
      simpa using this.symm
    have haNormX : (a : G) ∈ normalizer (X : Set G) := hHMX haG
    have haNormI : (a : G) ∈ normalizer (I : Set G) := hHI haG.1
    have haNorm : (a : G) ∈ normalizer ((X ⊔ I : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup X I (mem_inf.2 ⟨haNormX, haNormI⟩)
    rintro _ ⟨x, hx, rfl⟩
    have hxH : x ∈ H := hXH hx
    have hiConj : (i : G) * x * (i : G)⁻¹ ∈ X ⊔ I := by
      have hmem : x * (i : G)⁻¹ * x⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.1 (hHI hxH) ((i : G)⁻¹)).1 (I.inv_mem hiG)
      have hmem' : (i : G) * (x * (i : G)⁻¹ * x⁻¹) ∈ I := I.mul_mem hiG hmem
      have heq : (i : G) * x * (i : G)⁻¹ =
          ((i : G) * (x * (i : G)⁻¹ * x⁻¹)) * x := by group
      rw [heq]
      exact (X ⊔ I).mul_mem ((le_sup_right : I ≤ X ⊔ I) hmem')
        ((le_sup_left : X ≤ X ⊔ I) hx)
    have hconj : (h : G) * x * (h : G)⁻¹ =
        (a : G) * ((i : G) * x * (i : G)⁻¹) * (a : G)⁻¹ := by
      rw [hh]; group
    show (MulAut.conj (h : G)) x ∈ X ⊔ I
    rw [MulAut.conj_apply, hconj]
    exact (Subgroup.mem_normalizer_iff.1 haNorm ((i : G) * x * (i : G)⁻¹)).1 hiConj
  have hLle : L ≤ X ⊔ I := by
    rw [hL]
    exact iSup_le hgen
  have hImg : img9 H L = img9 H X := by
    refine le_antisymm ?_ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hXL))
    intro y hy
    obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.1 hy
    have hlH : l ∈ X.subgroupOf H ⊔ I.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup hXH hIH]
      exact Subgroup.mem_subgroupOf.2 (hLle (Subgroup.mem_subgroupOf.1 hlL))
    obtain ⟨x, hx, i, hi, hxi⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := X.subgroupOf H) (t := I.subgroupOf H)
        (ht := hInorm)).1 hlH
    have hiK : i ∈ CFSG.pPrimeCore 3 ↥H :=
      (Subgroup.mem_map_iff_mem H.subtype_injective).1 (Subgroup.mem_subgroupOf.1 hi)
    have hπi : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) i = 1 :=
      (QuotientGroup.eq_one_iff i).2 hiK
    refine Subgroup.mem_map.2 ⟨x, hx, ?_⟩
    rw [← hxi, map_mul, hπi, mul_one]
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let ψ₀ : ↥X →* Hbar9 H := π.comp (Subgroup.inclusion hXH)
  have hψ₀range : ψ₀.range = img9 H X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let ψ : ↥X →* Lbar9 Y H := ψ₀.codRestrict (img9 H L) fun x => by
    rw [hImg, ← hψ₀range]
    exact ⟨x, rfl⟩
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : Hbar9 H) ∈ ψ₀.range := by
      rw [hψ₀range, ← hImg]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hψker : ψ.ker = (X ⊓ I).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx1 : (π (Subgroup.inclusion hXH x) : Hbar9 H) = 1 := by
        have := congrArg Subtype.val hx
        simpa [ψ, ψ₀] using this
      have hxK : Subgroup.inclusion hXH x ∈ CFSG.pPrimeCore 3 ↥H :=
        (QuotientGroup.eq_one_iff _).1 hx1
      exact ⟨x.2, (Subgroup.mem_map_iff_mem H.subtype_injective).2 hxK⟩
    · rintro ⟨hxX, hxI⟩
      apply Subtype.ext
      show ψ₀ x = 1
      have hxK : Subgroup.inclusion hXH x ∈ CFSG.pPrimeCore 3 ↥H :=
        (Subgroup.mem_map_iff_mem H.subtype_injective).1 hxI
      exact (QuotientGroup.eq_one_iff _).2 hxK
  have hKsub_normal : ((X ⊓ I).subgroupOf X).Normal := by
    rw [← hψker]
    exact MonoidHom.normal_ker ψ
  let e : (↥X ⧸ (X ⊓ I).subgroupOf X) ≃* Lbar9 Y H :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hKleR : (X ⊓ I).subgroupOf X ≤ (pCoreOf 2 X).subgroupOf X := by
    intro x hx
    refine Subgroup.mem_subgroupOf.2 (inf_I9_le_pCoreOf le_rfl ?_ hA5' hXH ?_)
    · exact (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).symm
    · exact Subgroup.mem_subgroupOf.1 hx
  have hs : IsSimpleGroup (Lbar9 Y H) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie)
  have hcardLb : Nat.card (Lbar9 Y H) = 372000 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie)
  let Rsub : Subgroup ↥X := (pCoreOf 2 X).subgroupOf X
  have hRsub_normal : Rsub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hRsub_2 : IsPGroup 2 Rsub :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_subtype
  let Rq : Subgroup (↥X ⧸ (X ⊓ I).subgroupOf X) :=
    Rsub.map (QuotientGroup.mk' ((X ⊓ I).subgroupOf X))
  have hRq_normal : Rq.Normal :=
    hRsub_normal.map (QuotientGroup.mk' ((X ⊓ I).subgroupOf X))
      (QuotientGroup.mk'_surjective _)
  have hRq_2 : IsPGroup 2 Rq := hRsub_2.map (QuotientGroup.mk' ((X ⊓ I).subgroupOf X))
  let Rbar : Subgroup (Lbar9 Y H) := Rq.map e.toMonoidHom
  have hRbar_normal : Rbar.Normal := hRq_normal.map e.toMonoidHom e.surjective
  have hRbar_2 : IsPGroup 2 Rbar := hRq_2.map e.toMonoidHom
  rcases hs.eq_bot_or_eq_top_of_normal Rbar with hbot | htop
  · have hRq_bot : Rq = ⊥ := by
      have hle : Rq ≤ e.toMonoidHom.ker := (Subgroup.map_eq_bot_iff Rq).1 hbot
      have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
      rw [hker] at hle
      exact le_bot_iff.1 hle
    have hRleK : Rsub ≤ (X ⊓ I).subgroupOf X := by
      have hle : Rsub ≤ (QuotientGroup.mk' ((X ⊓ I).subgroupOf X)).ker :=
        (Subgroup.map_eq_bot_iff Rsub).1 hRq_bot
      have hker : (QuotientGroup.mk' ((X ⊓ I).subgroupOf X)).ker = (X ⊓ I).subgroupOf X :=
        QuotientGroup.ker_mk' _
      rwa [hker] at hle
    have hRK : Rsub = (X ⊓ I).subgroupOf X := le_antisymm hRleK hKleR
    have hKcard : Nat.card (↥X ⧸ (X ⊓ I).subgroupOf X) = 60 := by
      rw [← hRK]
      exact (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
        (CFSG.openPCoreOf_subgroupOf 2 X)).toEquiv).trans (card_bar2_of_isAlt hA5')
    have hcardEq : Nat.card (Lbar9 Y H) = Nat.card (↥X ⧸ (X ⊓ I).subgroupOf X) :=
      Nat.card_congr e.toEquiv.symm
    rw [hcardEq, hKcard] at hcardLb
    norm_num at hcardLb
  · have h2top : IsPGroup 2 (⊤ : Subgroup (Lbar9 Y H)) := htop ▸ hRbar_2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2top
    rw [Subgroup.card_top, hcardLb] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (show 3 ∣ 372000 by norm_num)
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32

private theorem false_of_lie_of_strong {D : Data G} {Y H D₃ S : Subgroup G}
    (hK : K_L35NoStrongFive) (hsp : IsStronglyPEmbedded 5 D.M)
    (hY : Hyp97 D Y H D₃ S) (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5)
    (hLie : LieModel (Lbar9 Y H) .PSL 3 5 1) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hYH : Y ≤ H := hY.1.2.1.1
  have hspB : IsStronglyPEmbedded 5 ((L9 Y H ⊓ D.M).subgroupOf (L9 Y H)) :=
    hsp.subgroupOf (not_le_M_of_hyp97 hY) (five_dvd_card_inf_of_isAlt hY hA5)
  by_cases h5N : 5 ∣ Nat.card ↥(L9 Y H ⊓ I9 H)
  · exact (not_eq_sup_I9_of_lie hY hA5 hLie) (eq_sup_I9_of_five_dvd hsp hY hA5 h5N)
  · let L := L9 Y H
    let B := L ⊓ D.M
    let N := L ⊓ I9 H
    have hNnormal : (N.subgroupOf L).Normal := by
      change ((L9 Y H ⊓ I9 H).subgroupOf (L9 Y H)).Normal
      exact subgroupOf_inf_I9_normal hYH
    have h5Nsub : ¬ 5 ∣ Nat.card ↥(N.subgroupOf L) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      simpa [N, L] using h5N
    have hBN : B.subgroupOf L ⊔ N.subgroupOf L ≠ ⊤ := by
      intro htop
      exact not_eq_sup_I9_of_lie hY hA5 hLie
        (eq_sup_I9_of_sup_eq_top hY rfl rfl rfl htop)
    have hquot : IsStronglyPEmbedded 5
        (B.subgroupOf L |>.map (QuotientGroup.mk' (N.subgroupOf L))) :=
      CFSG.GroupTheory.ThreeTranspositions.isStronglyPEmbedded_map_mk_of_sup_ne_top
        Nat.prime_five hspB h5Nsub hBN
    obtain ⟨φ, hφ, hker⟩ := exists_surjective_Lbar9 hYH
    have hkerN : φ.ker = N.subgroupOf L := by
      ext l
      rw [MonoidHom.mem_ker, hker l, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
    have : (N.subgroupOf L).Normal := hNnormal
    let e : (↥L ⧸ N.subgroupOf L) ≃* Lbar9 Y H :=
      (QuotientGroup.quotientMulEquivOfEq hkerN.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
    let Bbar : Subgroup (Lbar9 Y H) :=
      ((B.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L))).map e.toMonoidHom
    have hBbar : IsStronglyPEmbedded 5 Bbar :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_map_mulEquiv e hquot
    have hBbar_ne : Bbar ≠ ⊤ := by
      intro htop
      apply hBN
      have hBq : (B.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) = ⊤ := by
        refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
        rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
        exact htop
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' (N.subgroupOf L) x ∈
          (B.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) := by
        rw [hBq]
        exact Subgroup.mem_top _
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 hx
      have hnb : (b : ↥L)⁻¹ * x ∈ N.subgroupOf L := QuotientGroup.eq.1 hbx
      have hxeq : x = (b : ↥L) * ((b : ↥L)⁻¹ * x) := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ ((le_sup_left : B.subgroupOf L ≤ B.subgroupOf L ⊔ N.subgroupOf L) hb)
        ((le_sup_right : N.subgroupOf L ≤ B.subgroupOf L ⊔ N.subgroupOf L) hnb)
    exact hK (Lbar9 Y H) hLie Bbar hBbar_ne hBbar

theorem r9_22sp5_of_K
    (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (hK : K_L35NoStrongFive) (D : Data G) (h92 : R92 D) (h640 : UC6.R6_40_1 D) :
    R9_22sp5 D := by
  classical
  intro hsp Y H D₃ S hY hR hA5
  have hKF : KFactShape92A5Normalizer := kFactShape92A5Normalizer_holds
  have hSH : IsSylowOf 2 S H := (r912A5_of_inputs D (r99_holds D) (r910_holds D)
      (r911_of h63 D h640) (r9R5_holds D) Y H D₃ S hY hA5 hR).1
  rcases r913A5S_holds hKF D h92 Y H D₃ S hY hA5 hSH with h | hLie
  · calc H = I9 H ⊔ (H ⊓ D.M) := h
      _ = (H ⊓ D.M) ⊔ PPrimeCoreIn 3 H := by rw [I9_eq_PPrimeCoreIn, sup_comm]
  · exact (false_of_lie_of_strong hK hsp hY hA5 hLie).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
