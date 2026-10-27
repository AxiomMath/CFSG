module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof15Res12b

omit [Finite G] in
theorem exists_surjective_of_eq_sup {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y) :
    ∃ f : ↥X →* ↥Y ⧸ CFSG.pCore 2 ↥Y, Function.Surjective f := by
  refine ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY), fun q => ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hXN : X ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
    hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hy : (y : G) ∈ ((X ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
    rw [← hY]
    exact y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _ hXN] at hy
  obtain ⟨x, hx, p, hp, hxp⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY hx⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hpY : p ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hp
  have he : (⟨x, hXY hx⟩ : ↥Y)⁻¹ * y = ⟨p, hpY⟩ := by
    apply Subtype.ext
    change x⁻¹ * (y : G) = p
    rw [← hxp]
    group
  rw [he]
  exact (mem_pCoreOf_iff1523 (⟨p, hpY⟩ : ↥Y)).mp hp

theorem exists_surjective_of_data1523Y4 {A L Y : Subgroup G} {d : G} (D : Data1523Y4 A L Y d) :
    (∃ (_ : Fact (Nat.Prime 7))
        (f : ↥(oPrimeResidualOf 3 (Y ⊓ k1523 A d)) →*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥(oPrimeResidualOf 3 (Y ⊓ k1523 A d)) →* alternatingGroup (Fin 7),
        Function.Surjective f := by
  have hXY : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ≤ Y :=
    (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  obtain ⟨f, hf⟩ := exists_surjective_of_eq_sup hXY D.eq_y
  rcases D.type_y with ⟨h7, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨h7, e.toMonoidHom.comp f, e.surjective.comp hf⟩
  · exact Or.inr ⟨e.toMonoidHom.comp f, e.surjective.comp hf⟩

theorem commutator_le_of_ks1523ONCent (hON : KS1523ONCent) {A L Y : Subgroup G} {d : G}
    (D : Data1523Y4 A L Y d) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer ((k1523 A d : Subgroup G) : Set G))
    (hXR : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R, k1523 A d⁆ ≤ CFSG.Open.pCoreOf 2 (k1523 A d) :=
  hON G (k1523 A d) (oPrimeResidualOf 3 (Y ⊓ k1523 A d)) R D.mem_k.2.2.2 D.type_k
    ((oPrimeResidualOf_le_self 3 _).trans inf_le_right) (exists_surjective_of_data1523Y4 D) hR2
    hRK hXR

end Proof15Res12b

open Proof15Res12b

theorem not_le_normalizer_of_data1523Y4 {A L Y : Subgroup G}
    {d : G} (D : Data1523Y4 A L Y d) : ¬ k1523 A d ≤ Subgroup.normalizer (Y : Set G) := by
  intro hKY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := k1523 A d with hKdef
  have hK4 : K ∈ scriptY4 A (lB A) := D.mem_k
  have hq : IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := hK4.2.2.2
  set N := CFSG.pCore 2 ↥K with hN
  set V := (Y ⊓ K).subgroupOf K with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    (Late.le_normalizer_inf hKY Subgroup.le_normalizer)
  have hVmap : (V.map (QuotientGroup.mk' N)).Normal := hVn.map _ (QuotientGroup.mk'_surjective N)
  set X := oPrimeResidualOf 3 (Y ⊓ K) with hX
  have hXK : X ≤ K := (oPrimeResidualOf_le_self 3 _).trans inf_le_right
  have hXY : X ≤ Y ⊓ K := oPrimeResidualOf_le_self 3 _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hVmap with htop | hcen
  ·
    have h11K : 11 ∣ Nat.card (↥K ⧸ N) := by
      rw [card_of_isTripleCover D.type_k]
      exact Dvd.dvd.mul_left eleven_dvd_card_ON 3
    have h11V : 11 ∣ Nat.card V := by
      have h1 := Subgroup.card_map_dvd V (QuotientGroup.mk' N)
      rw [htop, Subgroup.card_top] at h1
      exact h11K.trans h1
    have hVY : Nat.card V ∣ Nat.card Y := by
      rw [hV, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ K ≤ K)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hYc : Nat.card Y = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) * Nat.card (CFSG.pCore 2 ↥Y) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h11 : 11 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) * Nat.card (CFSG.pCore 2 ↥Y) :=
      hYc ▸ h11V.trans hVY
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 11)).mp h11 with h | h
    · exact not_eleven_dvd_of_type D.type_y h
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
        (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y))
      rw [hn] at h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((by norm_num : Nat.Prime 11).dvd_of_dvd_pow h)
      omega
  ·
    have hNs : Group.IsSolvable N := by
      have := (CFSG.pCore_isPGroup : IsPGroup 2 N).isNilpotent
      infer_instance
    have hKs : Group.IsSolvable ((Subgroup.center (↥K ⧸ N)).comap (QuotientGroup.mk' N)) :=
      isSolvable_comap_center N hNs
    have hVK : V ≤ (Subgroup.center (↥K ⧸ N)).comap (QuotientGroup.mk' N) :=
      fun x hx => hcen (Subgroup.mem_map_of_mem _ hx)
    have hXV : X.subgroupOf K ≤ V := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hXY (Subgroup.mem_subgroupOf.mp hx))
    have hXs : Group.IsSolvable (X.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hXV.trans hVK))
        (Subgroup.inclusion_injective _)
    have hXs' : Group.IsSolvable ↥X := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom) (MulEquiv.surjective _)
    have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 D.mem_x
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr (ne_bot_of_mem_scriptY4 D.mem_x)
    exact Group.IsPerfect.not_isSolvable ↥X hXs'

theorem rank3II_15_23_of_y4 {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) (h1514 : Item1514 A (lB A) c L)
    (h153 : Item153Main A (lB A)) (h149 : Item149 A (lB A)) (hON : KS1523ONCent)
    (h155 : Item155 A (lB A)) (hK : Step1523KY4 A c L) (hΔ : Step1523DeltaY4 A c L)
    (hZ : Step1523ZY4 A c L) : Item1523 A (lB A) L := by
  intro hJ Y hY
  by_cases hm : MeetsY4 A (lB A) L Y
  · exact conclusion1523_of_meets h1514 hJ hY hm
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, D⟩ := hK h hJ Y hY hm
  have hY0 : Y ∈ scriptY0 A (lB A) := hY.prop
  have hYF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y := (h153 Y hY).2.2
  set K := k1523 A d with hKdef
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  set X := oPrimeResidualOf 3 (Y ⊓ K) with hX
  set R := Q ⊓ Subgroup.centralizer ({d} : Set G) with hR
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hCd : Subgroup.centralizer ({d} : Set G) ∈ scriptY A :=
    centralizer_mem_scriptY h.toTheoremFourHyp.isSimpleGroup h.toTheoremFourHyp.nonabelian hAab
      D.mem_d D.ne_d
  have hCK : Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hCd
  have hKC : K ≤ Subgroup.centralizer ({d} : Set G) :=
    (oPrimeResidualOf_le_self 3 _).trans (delta_le _)
  have hXYK : X ≤ Y ⊓ K := oPrimeResidualOf_le_self 3 _
  have hXY : X ≤ Y := hXYK.trans inf_le_left
  have hXK : X ≤ K := hXYK.trans inf_le_right
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR2 : IsPGroup 2 R := hQ2.to_le inf_le_left
  have hRY : R ≤ Y := inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hRC : R ≤ Subgroup.centralizer ({d} : Set G) := inf_le_right
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY0.1.1.2
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hAab.is_comm.comm ⟨d, D.mem_d⟩ ⟨a, ha⟩)).symm
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf
      (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (hAC.trans Subgroup.le_normalizer)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    Late.le_normalizer_inf (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      ((hXK.trans hKC).trans Subgroup.le_normalizer)
  have hRK : ⁅R, K⁆ ≤ CFSG.Open.pCoreOf 2 K :=
    commutator_le_of_ks1523ONCent hON D hR2 (hRC.trans hCK) hXR
  by_cases hR1 : R = ⊥
  ·
    obtain ⟨c', Z, hc', hdc', hZY, hZQ, hZC⟩ := hZ h hJ Y hY hm d D hR1
    exact false_of_centralizer_le1523 h.toSec13Data.isElemAbelian hAY hYF
      (zpowers_mem_omegaA_iff.mp hc').1 hc'.2.1 D.mem_d D.ne_d hdc' hR1 hZY hZQ hZC
  ·
    apply not_le_normalizer_of_data1523Y4 D
    have hΔY : X ⊔ R = delta A (lB A) (X ⊔ R) := hΔ h hJ Y hY hm d D hR1 hRK
    have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
      have h1 : R ≤ Subgroup.normalizer ((Y ⊓ K : Subgroup G) : Set G) :=
        Late.le_normalizer_inf (hRY.trans Subgroup.le_normalizer) (hRC.trans hCK)
      exact le_normalizer_oPrimeResidualOf h1
    have hcop : Nat.Coprime 3 (Nat.card R) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hX3 : X = oPrimeResidualOf 3 X := D.mem_x.2.1
    have hO3 : oPrimeResidualOf 3 (X ⊔ R) = X := by
      rw [← oPrimeResidualOf_eq_of_le le_sup_left (fun x hx k hk =>
        mem_left_of_pow_prime_pow Nat.prime_three hRX hcop hx hk)]
      exact hX3.symm
    have hXRY : X ⊔ R ≤ Y := sup_le hXY hRY
    have hAXR : A ≤ Subgroup.normalizer ((X ⊔ R : Subgroup G) : Set G) :=
      le_normalizer_sup D.mem_x.1.2 hAR
    have hXRR : X ⊔ R ≤ Subgroup.normalizer (R : Set G) := sup_le hXR Subgroup.le_normalizer
    have hRO : R ≤ CFSG.Open.pCoreOf 2 (X ⊔ R) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hXRR hR2
    have hXR3 : X ⊔ R ∈ scriptY3 A (lB A) :=
      ⟨⟨⟨fun htop => hY0.1.1.1 (top_le_iff.mp (htop ▸ hXRY)), hAXR⟩,
        fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRO))⟩, hΔY⟩
    have hX4 : oPrimeResidualOf 3 (X ⊔ R) ∈ scriptY4 A (lB A) := by
      rw [hO3]
      exact D.mem_x
    have hXReq : X ⊔ R = oPrimeResidualOf 3 (X ⊔ R) ⊔ CFSG.Open.pCoreOf 2 (X ⊔ R) := by
      rw [hO3]
      exact le_antisymm (sup_le le_sup_left (hRO.trans le_sup_right))
        (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
    have hΓ : Y ∈ gam155 A (lB A) (X ⊔ R) (oPrimeResidualOf 3 (X ⊔ R)) := by
      refine ⟨hY, ?_, hXRY.trans Subgroup.le_normalizer⟩
      rw [hO3]
      exact hXY
    have hhyp : omg155 A (oPrimeResidualOf 3 (X ⊔ R)) ∨
        Y = oPrimeResidualOf 3 (X ⊔ R) ⊔ CFSG.Open.pCoreOf 2 Y := by
      right
      rw [hO3]
      exact D.eq_y
    have hK2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
    have hRK' : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
      (hRC.trans hCK).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    have hP2 : IsPGroup 2 ↥(R ⊔ CFSG.Open.pCoreOf 2 K) :=
      IsPGroup.to_sup_of_normal_right' hR2 hK2 hRK'
    have hP1 : R ⊔ CFSG.Open.pCoreOf 2 K ≠ ⊥ :=
      fun h0 => hR1 (le_bot_iff.mp (h0 ▸ le_sup_left))
    have hloc : IsPLocal 2
        (Subgroup.normalizer ((R ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G)) :=
      CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hP1
    have hKP : K ≤ Subgroup.normalizer ((R ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := by
      have h2 : R ⊔ CFSG.Open.pCoreOf 2 K = (R ⊔ ⁅R, K⁆) ⊔ CFSG.Open.pCoreOf 2 K := by
        rw [sup_assoc, sup_eq_right.mpr hRK]
      rw [h2]
      exact le_normalizer_sup (le_normalizer_sup_commutator R K)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    have hAP : A ≤ Subgroup.normalizer ((R ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
      le_normalizer_sup hAR
        (D.mem_k.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    have hXRP : X ⊔ R ≤
        Subgroup.normalizer ((R ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
      sup_le (hXK.trans hKP) (le_sup_left.trans Subgroup.le_normalizer)
    obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
    have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (X ⊔ R) : Subgroup G) : Set G) :=
      ⟨hM, fun x hx => hle (sup_le hAP hXRP hx)⟩
    have hΔM := (h155 (X ⊔ R) hXR3 hX4 hXReq).2 Y hΓ hhyp M hMm
    calc K = delta A (lB A) K := D.mem_k.2.2.1
      _ ≤ delta A (lB A) M := delta_mono (hKP.trans hle)
      _ ≤ Subgroup.normalizer (Y : Set G) := hΔM

theorem item1523R_of_y4 (h1514 : Item1514HJR)
    (h153 : Item153MainR) (h149 : Sec16.Item149S14) (hON : KS1523ONCent) (h155 : Item155HJR)
    (hK : Step1523KY4R) (hΔ : Step1523DeltaY4R) (hZ : Step1523ZY4R) : Item1523R :=
  fun G _ _ A c L hR hJ => rank3II_15_23_of_y4 hR (h1514 G A c L hR hJ) (h153 G A c L hR)
    (h149 G A c L hR.toSec14Std) hON (h155 G A c L hR hJ) (hK G A c L hR)
    (hΔ G A c L hR) (hZ G A c L hR) hJ

end CFSG.RankThree.PartTwo.Sec15
