module

public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.ConjOrderThree
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5SmallONan
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStrongEmb
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96C
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem isSylowOf_top_of_normalizer_le {P M : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hN : Subgroup.normalizer (P : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simpa using CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le
    (H := M) (M := ⊤) (T := P) (by simpa using hP) (by simpa using hN)

theorem exists_sylowOf_normalized_of_isPGroup_of_not_dvd_index {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    {K Q S : Subgroup G} (hQ : IsPGroup p Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf q S K) (hnot : ¬ p ∣ S.relIndex K) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q T K ∧
      Q ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let f : Q →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hQK)
  letI : MulAction Q (Sylow q K) := MulAction.compHom (Sylow q K) f
  haveI : Finite (Sylow q K) :=
    Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty (p := q) (G := K)))
  have hnotcard : ¬ p ∣ Nat.card (Sylow q K) := by
    obtain ⟨S₀, hS₀⟩ := hS.exists_sylow_eq_subgroupOf
    have hdvd : Nat.card (Sylow q K) ∣ S₀.index := Sylow.card_dvd_index S₀
    have hindex : S.relIndex K = S₀.index := by
      show (S.subgroupOf K).index = S₀.index
      rw [← hS₀]
    exact fun hp => hnot (by rw [hindex]; exact hp.trans hdvd)
  obtain ⟨T₀, hT₀fix⟩ :=
    hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q K) hnotcard
  let T : Subgroup G := (T₀ : Subgroup K).map K.subtype
  have hforward : ∀ a : Q, ∀ x ∈ T, (a : G) * x * (a : G)⁻¹ ∈ T := by
    intro a x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix : a • T₀ = T₀ := MulAction.mem_fixedPoints.mp hT₀fix a
    have hsm : (T₀ : Subgroup K).map
        (MulDistribMulAction.toMonoidHom (↥K) (f a)) = (T₀ : Subgroup K) := by
      have h := congrArg (fun S : Sylow q K => (S : Subgroup K)) hfix
      change (↑(f a • T₀) : Subgroup K) = (T₀ : Subgroup K) at h
      rwa [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
    have hmem : (f a) k ∈ (T₀ : Subgroup K) := by
      have h : (MulDistribMulAction.toMonoidHom (↥K) (f a)) k ∈
          (T₀ : Subgroup K).map (MulDistribMulAction.toMonoidHom (↥K) (f a)) :=
        Subgroup.mem_map_of_mem (MulDistribMulAction.toMonoidHom (↥K) (f a)) hk
      rwa [hsm] at h
    have hmemG : (((f a) k : K) : G) ∈ T := Subgroup.mem_map_of_mem K.subtype hmem
    have hcoe : (((f a) k : K) : G) = (a : G) * (k : G) * (a : G)⁻¹ := by
      change (((Subgroup.normalizerMonoidHom K) (Subgroup.inclusion hQK a)) k : G) =
        (a : G) * (k : G) * (a : G)⁻¹
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    change (a : G) * (k : G) * (a : G)⁻¹ ∈ T
    rwa [← hcoe]
  have hQnorm : Q ≤ Subgroup.normalizer (T : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward ⟨q, hq⟩ x
    · intro hx
      have h := hforward (⟨q, hq⟩ : Q)⁻¹ (q * x * q⁻¹) hx
      simpa [mul_assoc] using h
  exact ⟨T, ⟨T₀, rfl⟩, hQnorm⟩

theorem normalizer_sylow_le_M_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    Subgroup.normalizer (P : Set G) ≤ D.M := by
  classical
  have hQchar : ((P ⊓ c.L).subgroupOf P).Characteristic := by
    have hforward : ∀ (ψ : MulAut ↥P) (y : ↥P),
        y ∈ (P ⊓ c.L).subgroupOf P → ψ y ∈ (P ⊓ c.L).subgroupOf P := by
      intro ψ y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hy3G : (y : G) ^ 3 = 1 :=
        c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (y : G) hy
      have hy3 : y ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hy3G
      have hψ3 : ((ψ y : ↥P) : G) ^ 3 = 1 := by
        have h : (ψ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
        simpa using congrArg (fun z : ↥P => (z : G)) h
      exact Subgroup.mem_inf.mpr ⟨(ψ y).2,
        c.forall_pow_three_eq_one_mem_L_of_threeCover
          CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
          (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
          hON hP ((ψ y : ↥P) : G) (ψ y).2 hψ3⟩
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hforward φ y hy
    · intro hx
      exact ⟨φ.symm x, hforward φ.symm x hx, by simp⟩
  have hNPM : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) :=
    (CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic inf_le_left hQchar).trans
      (CFSG.LocalAnalysis.GLTheoremA.S9.L96.normalizer_le_normalizer_center (P ⊓ c.L))
  exact hNPM.trans hNZ

theorem isHatON_lbar_of_onan_wPH2 (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩

theorem map_zSub_le_center_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((zSub P c.L).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) ≤ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = (Q.subgroupOf c.L).map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hHat := isHatON_lbar_of_onan_wPH2 c hON
  have hcen :=
    (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).2.2.2
  rintro w ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hz
  have hzQ : (z : G) ∈ Q := hzZ.1
  have hzcent := hzZ.2
  have hzY : z ∈ Q.subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]; exact hzQ
  have hzS : π z ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hzY
  refine hcen (π z) hzS ?_
  intro s hs
  rw [hScoe] at hs
  obtain ⟨q, hqY, rfl⟩ := Subgroup.mem_map.mp hs
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hqY
  exact Subgroup.mem_centralizer_iff.mp hzcent (q : G) hqQ

theorem exists_seven_mem_centralizer_inf_L_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : 7 ∈ D.sig)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∃ y : G, y ∈ D.M ∧ orderOf y = 7 ∧ ∀ q ∈ P ⊓ c.L, y * q = q * y := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Z : Subgroup G := zSub P c.L
  let H : Subgroup G := Subgroup.normalizer (Z : Set G) ⊓ D.M
  have hHrank : 3 ≤ CFSG.Open.pRank 7 H := by
    simpa [H, Z] using c.three_le_pRank_normalizer_inf_of_onan hON hP h7
  have hHL : H ≤ Subgroup.normalizer (c.L : Set G) :=
    inf_le_right.trans c.le_normalizer_L
  let ψ := CFSG.GroupTheory.conjModPCore 2 c.L H hHL
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := 7) (by norm_num) c.L H hHL
  have hrange : CFSG.Open.pRank 7 ψ.range ≤ 2 := by
    haveI : Finite c.Lbar := by
      change Finite (↥c.L ⧸ CFSG.pCore 2 ↥c.L)
      infer_instance
    haveI : Fintype c.Lbar := Fintype.ofFinite c.Lbar
    haveI : Fintype (c.Lbar → c.Lbar) := inferInstance
    haveI : Finite (MulAut c.Lbar) :=
      Finite.of_injective (fun f : MulAut c.Lbar => (f : c.Lbar → c.Lbar))
        (fun f g h => MulEquiv.ext (fun x => congrFun h x))
    have h1 : CFSG.Open.pRank 7 ψ.range ≤
        CFSG.Open.pRank 7 (⊤ : Subgroup (MulAut c.Lbar)) :=
      CFSG.SectionRank.pRank_mono (G := MulAut c.Lbar) (p := 7) (by norm_num) le_top
    have h2' : CFSG.Open.pRank 7 (⊤ : Subgroup (MulAut c.Lbar)) ≤ 2 := by
      have h := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k5ONan_holds c.Lbar
        hON 7 (by norm_num) (by norm_num)
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h
    exact h1.trans h2'
  have hker : 1 ≤ CFSG.Open.pRank 7 (ψ.ker.map H.subtype) := by
    have hrank' : CFSG.Open.pRank 7 H ≤
        CFSG.Open.pRank 7 (ψ.ker.map H.subtype) + 2 := by
      simpa [ψ] using hrank.trans (Nat.add_le_add_left hrange _)
    omega
  obtain ⟨c0, hc0K, hc0ord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank (G := G) Nat.prime_seven hker
  let π := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  have hKsub : ψ.ker.map H.subtype ≤ π.ker.map D.M.subtype := by
    rw [CFSG.GroupTheory.map_ker_conjModPCore_mono (p := 2) (L := c.L)
      (M := D.M) (M' := H) inf_le_right c.le_normalizer_L hHL]
    exact inf_le_right
  have hc0pi : c0 ∈ π.ker.map D.M.subtype := hKsub hc0K
  obtain ⟨c0M, hc0ker, hc0eq⟩ := Subgroup.mem_map.mp hc0pi
  have hc0mem : c0 ∈ D.M := hc0eq ▸ c0M.2
  have hπc0 : π c0M = 1 := MonoidHom.mem_ker.mp hc0ker
  have hπc0' : π ⟨c0, hc0mem⟩ = 1 := by
    rw [show (⟨c0, hc0mem⟩ : ↥D.M) = c0M from Subtype.ext hc0eq.symm]
    exact hπc0
  let Q3 : Subgroup G := P ⊓ c.L
  let Nmap : Subgroup G := (CFSG.pCore 2 ↥c.L).map c.L.subtype
  let HL : Subgroup G := Q3 ⊔ Nmap
  have hHLleL : HL ≤ c.L :=
    sup_le inf_le_right (Subgroup.map_subtype_le _)
  have hQ3_3 : IsPGroup 3 Q3 := hP.isPGroup.to_le inf_le_left
  have hNmap2 : IsPGroup 2 Nmap := CFSG.pCore_isPGroup.map c.L.subtype
  have hdisj : Q3 ⊓ Nmap = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q3 Nmap hQ3_3 hNmap2).eq_bot
  have hQ3normN : Q3 ≤ Subgroup.normalizer (Nmap : Set G) := by
    intro q hq
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L
      (c.le_normalizer_L (c.hyp81.1 hq.2))
  have hcardHL : Nat.card HL = Nat.card Q3 * Nat.card Nmap := by
    have hsup : HL = Nmap ⊔ Q3 := by
      dsimp only [HL]
      exact sup_comm (a := Q3) (b := Nmap)
    rw [hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      Nmap Q3 hQ3normN (by rw [disjoint_iff, inf_comm]; exact hdisj), mul_comm]
  have hrel : Q3.relIndex HL = Nat.card Nmap := by
    have h := Subgroup.relIndex_mul_card Q3 HL
    rw [hcardHL, inf_eq_left.mpr le_sup_left, mul_comm (Nat.card Q3)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hnot7 : ¬ 7 ∣ Q3.relIndex HL := by
    rw [hrel]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hNmap2 Nat.prime_seven (by norm_num)
  have hnot3 : ¬ 3 ∣ Q3.relIndex HL := by
    rw [hrel]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hNmap2 Nat.prime_three (by norm_num)
  have hQ3syl : CFSG.ABGLocalTools.IsSylowOf 3 Q3 HL := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_sup_left, hQ3_3, hnot3⟩
  have hQ7 : IsPGroup 7 (Subgroup.zpowers c0) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc0ord, pow_one]
  have hc0N : c0 ∈ Subgroup.normalizer (Nmap : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L
      (c.le_normalizer_L hc0mem)
  have hc0comm :=
    (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M c.le_normalizer_L).mp hc0pi
  have hc0invcomm :=
    (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M c.le_normalizer_L).mp
      (Subgroup.inv_mem _ hc0pi)
  have hc0maple : HL.map (MulAut.conj c0).toMonoidHom ≤ HL := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have hhL : h ∈ c.L := hHLleL hh
    have hhQ : h ∈ Q3 ⊔ Nmap := hh
    have hc0hL : c0 * h * c0⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hc0mem) h).mp hhL
    have hdiff : (c0 * h * c0⁻¹) * h⁻¹ ∈ Nmap :=
      hc0comm.2 h hhL
    have hnormN : h ∈ Subgroup.normalizer (Nmap : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L
        (c.le_normalizer_L (c.hyp81.1 hhL))
    have hconjN : h⁻¹ * ((c0 * h * c0⁻¹) * h⁻¹) * h ∈ Nmap := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnormN)
        ((c0 * h * c0⁻¹) * h⁻¹)).mp hdiff
    have hprod : c0 * h * c0⁻¹ =
        h * (h⁻¹ * ((c0 * h * c0⁻¹) * h⁻¹) * h) := by group
    change c0 * h * c0⁻¹ ∈ HL
    rw [hprod]
    exact HL.mul_mem hh (Subgroup.mem_sup_right hconjN)
  have hc0invmaple : HL.map (MulAut.conj c0⁻¹).toMonoidHom ≤ HL := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have hhL : h ∈ c.L := hHLleL hh
    have hc0hL : c0⁻¹ * h * c0⁻¹⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L (D.M.inv_mem hc0mem)) h).mp hhL
    have hdiff : (c0⁻¹ * h * c0⁻¹⁻¹) * h⁻¹ ∈ Nmap :=
      hc0invcomm.2 h hhL
    have hnormN : h ∈ Subgroup.normalizer (Nmap : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L
        (c.le_normalizer_L (c.hyp81.1 hhL))
    have hconjN : h⁻¹ * ((c0⁻¹ * h * c0⁻¹⁻¹) * h⁻¹) * h ∈ Nmap := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnormN)
        ((c0⁻¹ * h * c0⁻¹⁻¹) * h⁻¹)).mp hdiff
    have hprod : c0⁻¹ * h * c0⁻¹⁻¹ =
        h * (h⁻¹ * ((c0⁻¹ * h * c0⁻¹⁻¹) * h⁻¹) * h) := by group
    change c0⁻¹ * h * c0⁻¹⁻¹ ∈ HL
    rw [hprod]
    exact HL.mul_mem hh (Subgroup.mem_sup_right hconjN)
  have hc0HL : c0 ∈ Subgroup.normalizer (HL : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm hc0maple ?_
    intro h hh
    have h' : c0⁻¹ * h * c0 ∈ HL := by
      have := hc0invmaple (Subgroup.mem_map_of_mem (MulAut.conj c0⁻¹).toMonoidHom hh)
      simpa [MulAut.conj_apply] using this
    exact Subgroup.mem_map.mpr ⟨c0⁻¹ * h * c0, h', by simp [MulAut.conj_apply]; group⟩
  have hQ7HL : Subgroup.zpowers c0 ≤ Subgroup.normalizer (HL : Set G) :=
    Subgroup.zpowers_le.mpr hc0HL
  obtain ⟨S, hSsyl, hc0S⟩ :=
    exists_sylowOf_normalized_of_isPGroup_of_not_dvd_index (p := 7) (q := 3)
      hQ7 hQ7HL hQ3syl hnot7
  obtain ⟨k, hkHL, hconj⟩ := hQ3syl.exists_mem_conj hSsyl
  have hS_eq : S = Q3.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      have h := (hconj x).mp hx
      exact ⟨k⁻¹ * x * k, h, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨q, hq, rfl⟩
      have h := (hconj (k * q * k⁻¹)).mpr ?_
      · simpa [MulAut.conj_apply] using h
      · simpa [MulAut.conj_apply, mul_assoc] using hq
  have hc0Scent : ∀ s ∈ S, c0 * s * c0⁻¹ = s := by
    intro s hs
    have hmemS : c0 * s * c0⁻¹ ∈ S := by
      have hc0Spow : c0 ∈ Subgroup.zpowers c0 := Subgroup.mem_zpowers c0
      exact (Subgroup.mem_normalizer_iff.mp (hc0S hc0Spow) s).mp hs
    have hsL : s ∈ c.L := hHLleL (hSsyl.le hs)
    have hc0sL : c0 * s * c0⁻¹ ∈ c.L := hHLleL (hSsyl.le hmemS)
    have hdiffS : (c0 * s * c0⁻¹) * s⁻¹ ∈ S :=
      S.mul_mem hmemS (S.inv_mem hs)
    have hdiffN : (c0 * s * c0⁻¹) * s⁻¹ ∈ Nmap :=
      hc0comm.2 s hsL
    have hbot : S ⊓ Nmap = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) S Nmap hSsyl.isPGroup hNmap2).eq_bot
    have hmemBot : (c0 * s * c0⁻¹) * s⁻¹ ∈ S ⊓ Nmap := Subgroup.mem_inf.mpr ⟨hdiffS, hdiffN⟩
    rw [hbot] at hmemBot
    have h1 : (c0 * s * c0⁻¹) * s⁻¹ = 1 := by simpa using hmemBot
    calc c0 * s * c0⁻¹ = ((c0 * s * c0⁻¹) * s⁻¹) * s := by group
      _ = s := by rw [h1, one_mul]
  refine ⟨k⁻¹ * c0 * k, ?_, ?_, ?_⟩
  · have hkL : k ∈ c.L := hHLleL hkHL
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem (c.hyp81.1 hkL)) hc0mem)
      (c.hyp81.1 hkL)
  · have hsem : SemiconjBy (k⁻¹) c0 (k⁻¹ * c0 * k) := by
      unfold SemiconjBy
      group
    rw [← SemiconjBy.orderOf_eq (k⁻¹) hsem, hc0ord]
  · intro q hq
    have hqS : k * q * k⁻¹ ∈ S := by
      rw [hS_eq]
      exact Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hq
    have hcent := hc0Scent (k * q * k⁻¹) hqS
    have hcent' : c0 * (k * q * k⁻¹) = (k * q * k⁻¹) * c0 := by
      calc c0 * (k * q * k⁻¹) = (c0 * (k * q * k⁻¹) * c0⁻¹) * c0 := by group
        _ = (k * q * k⁻¹) * c0 := by rw [hcent]
    calc (k⁻¹ * c0 * k) * q = k⁻¹ * (c0 * (k * q * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * q * k⁻¹) * c0) * k := by rw [hcent']
      _ = q * (k⁻¹ * c0 * k) := by group

abbrev centerPreimage_of_onan (c : Ctx82E3 D) : Subgroup G :=
  ((Subgroup.center c.Lbar).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))).map c.L.subtype

theorem zSub_conj_le_centerPreimage_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {g : G}
    (hg : g ∈ D.M) :
    (zSub P c.L).map (MulAut.conj g).toMonoidHom ≤ centerPreimage_of_onan c := by
  classical
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let πL : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let πM : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
  have hzPL : z ∈ P ⊓ c.L := (inf_le_left : zSub P c.L ≤ P ⊓ c.L) hz
  have hzL : z ∈ c.L := hzPL.2
  have hzcenter : πL ⟨z, hzL⟩ ∈ Subgroup.center c.Lbar := by
    have hzsub : ⟨z, hzL⟩ ∈ (zSub P c.L).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hz
    exact map_zSub_le_center_of_onan c hON hP (Subgroup.mem_map_of_mem πL hzsub)
  have hwL : g * z * g⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hg) z).mp hzL
  refine Subgroup.mem_map.mpr ⟨⟨g * z * g⁻¹, hwL⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
  have h : πL ⟨g * z * g⁻¹, hwL⟩ = πM ⟨g, hg⟩ (πL ⟨z, hzL⟩) :=
    (CFSG.GroupTheory.conjModPCore_mk 2 c.L D.M c.le_normalizer_L
      ⟨g, hg⟩ ⟨z, hzL⟩).symm
  rw [h]
  have hmap : (Subgroup.center c.Lbar).map (πM ⟨g, hg⟩).toMonoidHom =
      Subgroup.center c.Lbar := Subgroup.map_center_eq (πM ⟨g, hg⟩)
  rw [← hmap]
  exact Subgroup.mem_map_of_mem (πM ⟨g, hg⟩).toMonoidHom hzcenter

theorem inf_centerPreimage_sylow_le_zSub_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    centerPreimage_of_onan c ⊓ P ≤ zSub P c.L := by
  classical
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let πL : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  intro k hk
  obtain ⟨hkK, hkP⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨kL, hkcenter, hkLeq⟩ := Subgroup.mem_map.mp hkK
  have hkL : k ∈ c.L := hkLeq ▸ kL.2
  have hkPL : k ∈ P ⊓ c.L := Subgroup.mem_inf.mpr ⟨hkP, hkL⟩
  refine Subgroup.mem_inf.mpr ⟨hkPL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htL : t ∈ c.L := ht.2
  have hcommq : QuotientGroup.mk' N kL * QuotientGroup.mk' N ⟨t, htL⟩ =
      QuotientGroup.mk' N ⟨t, htL⟩ * QuotientGroup.mk' N kL :=
    (Subgroup.mem_center_iff.mp hkcenter (QuotientGroup.mk' N ⟨t, htL⟩)).symm
  have hclass : QuotientGroup.mk' N
      ⟨k * t * k⁻¹ * t⁻¹, c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hkL htL)
        (c.L.inv_mem hkL)) (c.L.inv_mem htL)⟩ = 1 := by
    change QuotientGroup.mk' N (⟨k, hkL⟩ * ⟨t, htL⟩ * ⟨k, hkL⟩⁻¹ *
      ⟨t, htL⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hkLeq' : QuotientGroup.mk' N ⟨k, hkL⟩ = QuotientGroup.mk' N kL := by
      exact congrArg (QuotientGroup.mk' N) (Subtype.ext hkLeq.symm)
    rw [hkLeq', hcommq]
    group
  have hcommN : k * t * k⁻¹ * t⁻¹ ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨k * t * k⁻¹ * t⁻¹, ?_⟩, ?_, rfl⟩
    · exact c.L.mul_mem (c.L.mul_mem (c.L.mul_mem hkL htL) (c.L.inv_mem hkL))
        (c.L.inv_mem htL)
    · exact (QuotientGroup.eq_one_iff _).mp hclass
  have hcommP : k * t * k⁻¹ * t⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hkP ht.1) (P.inv_mem hkP)) (P.inv_mem ht.1)
  have hbot : P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P
      ((CFSG.pCore 2 ↥c.L).map c.L.subtype) hP.isPGroup
      (CFSG.pCore_isPGroup.map c.L.subtype)).eq_bot
  have hmem : k * t * k⁻¹ * t⁻¹ ∈ P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype :=
    Subgroup.mem_inf.mpr ⟨hcommP, hcommN⟩
  rw [hbot] at hmem
  have h1 : k * t * k⁻¹ * t⁻¹ = 1 := by simpa using hmem
  have hkt : k * t = t * k := by
    calc k * t = (k * t * k⁻¹ * t⁻¹) * (t * k) := by group
      _ = t * k := by rw [h1, one_mul]
  exact hkt.symm

theorem centralizer_conj_eq_of_group {X : Type} [Group X] [Finite X] (g x : X) :
    Subgroup.centralizer ({MulAut.conj g x} : Set X) =
      (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom := by
  classical
  have hle : (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({MulAut.conj g x} : Set X) := by
    have := Subgroup.map_centralizer_le_centralizer_image ({x} : Set X)
      (MulAut.conj g).toMonoidHom
    simpa [Set.image_singleton] using this
  let φ : ↥(Subgroup.centralizer ({MulAut.conj g x} : Set X)) →
      ↥(Subgroup.centralizer ({x} : Set X)) := fun z =>
    ⟨(MulAut.conj g⁻¹) z, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz : (z : X) * (MulAut.conj g x) = (MulAut.conj g x) * z :=
        Subgroup.mem_centralizer_singleton_iff.mp z.2
      calc (MulAut.conj g⁻¹) z * x
          = (MulAut.conj g⁻¹) (z * MulAut.conj g x) := by
              rw [map_mul]
              congr 1
              simpa using ((MulAut.conj g).symm_apply_apply x).symm
        _ = (MulAut.conj g⁻¹) (MulAut.conj g x * z) := by rw [hz]
        _ = x * (MulAut.conj g⁻¹) z := by
              rw [map_mul]
              congr 1
              simpa using (MulAut.conj g).symm_apply_apply x⟩
  have hφinj : Function.Injective φ := fun a b h => by
    have h' : (MulAut.conj g⁻¹) (a : X) = (MulAut.conj g⁻¹) (b : X) :=
      Subtype.ext_iff.mp h
    have h'' := congrArg (fun w => (MulAut.conj g) w) h'
    simpa using h''
  have heq : (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({MulAut.conj g x} : Set X) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hcardmap : Nat.card ↥((Subgroup.centralizer ({x} : Set X)).map
        (MulAut.conj g).toMonoidHom) = Nat.card (Subgroup.centralizer ({x} : Set X)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv.symm
    rw [hcardmap]
    exact Nat.card_le_card_of_injective φ hφinj
  exact heq.symm

theorem zSub_conj_eq_of_le_of_onan (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    ∀ g : G, (zSub P c.L).map (MulAut.conj g).toMonoidHom ≤ P →
      (zSub P c.L).map (MulAut.conj g).toMonoidHom = zSub P c.L := by
  classical
  intro g hg
  let Z : Subgroup G := zSub P c.L
  change Z.map (MulAut.conj g).toMonoidHom = Z
  have h7mem : 7 ∈ D.sig := by rw [h7]; simp
  obtain ⟨y7, hy7M, hy7ord, hy7cent⟩ :=
    exists_seven_mem_centralizer_inf_L_of_onan c hON h7mem hP
  have hgPL : Z.map (MulAut.conj g).toMonoidHom ≤ P ⊓ c.L := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
    have hzPL : z ∈ P ⊓ c.L := (inf_le_left : Z ≤ P ⊓ c.L) hz
    have hwP : g * z * g⁻¹ ∈ P := hg (Subgroup.mem_map_of_mem _ hz)
    have hz3 : z ^ 3 = 1 :=
      c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP z hzPL
    have hw3 : (g * z * g⁻¹) ^ 3 = 1 := by
      have hcube : (g * z * g⁻¹) ^ 3 = g * z ^ 3 * g⁻¹ := by
        change (MulAut.conj g z) ^ 3 = MulAut.conj g (z ^ 3)
        rw [map_pow]
      rw [hcube, hz3, mul_one, mul_inv_cancel]
    exact Subgroup.mem_inf.mpr ⟨hwP,
      c.forall_pow_three_eq_one_mem_L_of_threeCover
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
        hON hP (g * z * g⁻¹) hwP hw3⟩
  have hy7norm : y7 ∈ Subgroup.normalizer ((Z.map (MulAut.conj g).toMonoidHom) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxPL : x ∈ P ⊓ c.L := hgPL hx
      have hcomm : y7 * x = x * y7 := hy7cent x hxPL
      show y7 * x * y7⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom
      rwa [show y7 * x * y7⁻¹ = x from by rw [hcomm]; group]
    · intro hx
      have hxPL : y7 * x * y7⁻¹ ∈ P ⊓ c.L := hgPL hx
      have hcomm : y7 * (y7 * x * y7⁻¹) = (y7 * x * y7⁻¹) * y7 :=
        hy7cent _ hxPL
      have hxeq : y7 * x * y7⁻¹ = x := by
        calc y7 * x * y7⁻¹ = y7⁻¹ * (y7 * (y7 * x * y7⁻¹)) := by group
          _ = y7⁻¹ * ((y7 * x * y7⁻¹) * y7) := by rw [hcomm]
          _ = x := by group
      rwa [hxeq] at hx
  have hy7Mg : y7 ∈ D.M.map (MulAut.conj g).toMonoidHom := by
    have hNle : Subgroup.normalizer ((Z.map (MulAut.conj g).toMonoidHom) : Set G) ≤
        D.M.map (MulAut.conj g).toMonoidHom := by
      rw [← Subgroup.map_normalizer_eq_of_bijective (H := Z)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective]
      exact Subgroup.map_mono hNZ
    exact hNle hy7norm
  have hgM : g ∈ D.M := by
    by_contra hgnot
    have hnot := (c.isStronglyPEmbedded_of_mem_sigma h7mem).not_dvd_card_inf_conj hgnot
    apply hnot
    have hy7inf : y7 ∈ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hy7M, hy7Mg⟩
    have h7dvd : 7 ∣ Nat.card (Subgroup.zpowers y7) := by
      rw [Nat.card_zpowers, hy7ord]
    exact h7dvd.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy7inf))
  have hZg_le_Z : Z.map (MulAut.conj g).toMonoidHom ≤ Z := by
    intro w hw
    have hwK : w ∈ centerPreimage_of_onan c :=
      zSub_conj_le_centerPreimage_of_onan c hON hP hgM hw
    have hwP : w ∈ P := hg hw
    exact inf_centerPreimage_sylow_le_zSub_of_onan c hON hP
      (Subgroup.mem_inf.mpr ⟨hwK, hwP⟩)
  have hcard : Nat.card ↥Z = 3 := c.card_inf_centralizer_of_onan hON hP
  have hcard' : Nat.card ↥(Z.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  exact Subgroup.eq_of_le_of_card_ge hZg_le_Z (by rw [hcard', hcard])

theorem exists_sylow_centralizer_of_gamma' (hK6 : K6ONanClasses) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    ∀ x ∈ P ⊓ c.L, orderOf x = 3 → x ∉ zSub P c.L →
      ∃ y ∈ P ⊓ c.L, orderOf y = 3 ∧ y ∉ zSub P c.L ∧
        CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ Subgroup.centralizer ({y} : Set G))
          (Subgroup.centralizer ({y} : Set G)) ∧
        (Subgroup.centralizer ({y} : Set G) ≤ D.M ↔
          Subgroup.centralizer ({x} : Set G) ≤ D.M) := by
  classical
  intro x hx hx3 hxZ
  let Z : Subgroup G := zSub P c.L
  have hxP : x ∈ P := hx.1
  have hxL : x ∈ c.L := hx.2
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hxCx : x ∈ Cx := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hQxCx3 : IsPGroup 3 ((P ⊓ Cx).subgroupOf Cx) :=
    (hP.isPGroup.to_le inf_le_left).comap_subtype
  obtain ⟨T₀, hT₀le⟩ := hQxCx3.exists_le_sylow
  let T : Subgroup G := (T₀ : Subgroup Cx).map Cx.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T Cx := ⟨T₀, rfl⟩
  have hQxT : P ⊓ Cx ≤ T := by
    intro w hw
    have hw' : (⟨w, hw.2⟩ : ↥Cx) ∈ (P ⊓ Cx).subgroupOf Cx :=
      Subgroup.mem_subgroupOf.mpr hw
    exact Subgroup.mem_map.mpr ⟨⟨w, hw.2⟩, hT₀le hw', rfl⟩
  have hNPleM : Subgroup.normalizer (P : Set G) ≤ D.M :=
    normalizer_sylow_le_M_of_onan c hON hP hNZ
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ :=
    isSylowOf_top_of_normalizer_le hP hNPleM
  have hPidx : ¬ 3 ∣ P.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hPtop).2.2
  let P₀ : Sylow 3 G := hPtop.isPGroup.toSylow hPidx
  have hP₀coe : (P₀ : Subgroup G) = P := hPtop.isPGroup.toSylow_coe hPidx
  obtain ⟨g, hgT⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow P₀ hTsyl.isPGroup
  have hgTP : T.map (MulAut.conj g).toMonoidHom ≤ P := by
    rwa [hP₀coe] at hgT
  let y : G := g * x * g⁻¹
  have hxT : x ∈ T :=
    hQxT (Subgroup.mem_inf.mpr ⟨hxP, hxCx⟩)
  have hyT : y ∈ T.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxT
  have hyP : y ∈ P := hgTP hyT
  have hy3 : orderOf y = 3 := by
    change orderOf ((MulAut.conj g) x) = 3
    rw [MulEquiv.orderOf_eq, hx3]
  have hy3pow : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hyPL : y ∈ P ⊓ c.L := by
    refine Subgroup.mem_inf.mpr ⟨hyP, ?_⟩
    exact c.forall_pow_three_eq_one_mem_L_of_threeCover
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
      hON hP y hyP hy3pow
  have hyL : y ∈ c.L := hyPL.2
  have hyZ : y ∉ Z := by
    intro hyZin
    have hZcard : Nat.card ↥Z = 3 := c.card_inf_centralizer_of_onan hON hP
    have hZeq : Z = Subgroup.zpowers y :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyZin) (by
        rw [Nat.card_zpowers, hy3, hZcard])).symm
    have hxmap : x ∈ Z.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨y, hyZin, ?_⟩
      have hyx : ((MulAut.conj g⁻¹).toMonoidHom) y = x := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show y = g * x * g⁻¹ from rfl]
        group
      exact hyx
    have hmaple : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
      rw [hZeq]
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hyx : (MulAut.conj g⁻¹) y = x := by
        rw [MulAut.conj_apply]
        rw [show y = g * x * g⁻¹ from rfl]
        group
      have hconj : (MulAut.conj g⁻¹) (y ^ k) = x ^ k := by
        calc (MulAut.conj g⁻¹) (y ^ k) = ((MulAut.conj g⁻¹) y) ^ k := by
              simpa using map_zpow ((MulAut.conj g⁻¹).toMonoidHom) y k
          _ = x ^ k := by rw [hyx]
      change (MulAut.conj g⁻¹) (y ^ k) ∈ P
      rw [hconj]
      exact P.zpow_mem hxP k
    have heq := zSub_conj_eq_of_le_of_onan c hON h7 hP hNZ g⁻¹ hmaple
    exact hxZ (heq ▸ hxmap)
  have hCxmap : Subgroup.centralizer ({y} : Set G) =
      Cx.map (MulAut.conj g).toMonoidHom := by
    rw [show y = MulAut.conj g x from rfl]
    exact centralizer_conj_eq_of_group g x
  have hTg_le_C : T.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({y} : Set G) := by
    rw [hCxmap]
    exact Subgroup.map_mono hTsyl.le
  have hTg_le : T.map (MulAut.conj g).toMonoidHom ≤
      P ⊓ Subgroup.centralizer ({y} : Set G) := le_inf hgTP hTg_le_C
  have hTg_syl : CFSG.ABGLocalTools.IsSylowOf 3
      (T.map (MulAut.conj g).toMonoidHom) (Subgroup.centralizer ({y} : Set G)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hTg_le_C ?_
    have hcardmap : Nat.card ↥(T.map (MulAut.conj g).toMonoidHom) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.equivMapOfInjective T (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv.symm
    rw [hcardmap, hTsyl.card_eq]
    congr 2
    have hcardCxmap : Nat.card ↥(Cx.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Cx :=
      Nat.card_congr (Subgroup.equivMapOfInjective Cx (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv.symm
    rw [hCxmap, hcardCxmap]
  have hCP_syl : CFSG.ABGLocalTools.IsSylowOf 3
      (P ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({y} : Set G)) := by
    have heq : P ⊓ Subgroup.centralizer ({y} : Set G) =
        T.map (MulAut.conj g).toMonoidHom :=
      hTg_syl.eq_of_le hTg_le inf_le_right (hP.isPGroup.to_inf_left)
    rw [heq]
    exact hTg_syl
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let πL : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  haveI : Finite c.Lbar := by
    change Finite (↥c.L ⧸ CFSG.pCore 2 ↥c.L)
    infer_instance
  let xL : ↥c.L := ⟨x, hxL⟩
  let yL : ↥c.L := ⟨y, hyL⟩
  have hxL3 : orderOf xL = 3 := by
    rw [← Subgroup.orderOf_coe xL]
    exact hx3
  have hyL3 : orderOf yL = 3 := by
    rw [← Subgroup.orderOf_coe yL]
    exact hy3
  have hxbar3 : orderOf (πL xL) = 3 := by
    have hdvd : orderOf (πL xL) ∣ 3 := by
      rw [← hxL3]
      exact orderOf_map_dvd πL xL
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hx1 : πL xL = 1 := orderOf_eq_one_iff.mp h1
      have hxN : x ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype :=
        Subgroup.mem_map.mpr ⟨xL, (QuotientGroup.eq_one_iff xL).mp hx1, rfl⟩
      have hbot : P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype = ⊥ :=
        (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P
          ((CFSG.pCore 2 ↥c.L).map c.L.subtype) hP.isPGroup
          (CFSG.pCore_isPGroup.map c.L.subtype)).eq_bot
      have : x ∈ P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype :=
        Subgroup.mem_inf.mpr ⟨hxP, hxN⟩
      rw [hbot] at this
      have hx1' : x = 1 := by simpa using this
      rw [hx1'] at hx3
      norm_num at hx3
    · exact h3
  have hybar3 : orderOf (πL yL) = 3 := by
    have hdvd : orderOf (πL yL) ∣ 3 := by
      rw [← hyL3]
      exact orderOf_map_dvd πL yL
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hy1 : πL yL = 1 := orderOf_eq_one_iff.mp h1
      have hyN : y ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype :=
        Subgroup.mem_map.mpr ⟨yL, (QuotientGroup.eq_one_iff yL).mp hy1, rfl⟩
      have hbot : P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype = ⊥ :=
        (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P
          ((CFSG.pCore 2 ↥c.L).map c.L.subtype) hP.isPGroup
          (CFSG.pCore_isPGroup.map c.L.subtype)).eq_bot
      have : y ∈ P ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype :=
        Subgroup.mem_inf.mpr ⟨hyP, hyN⟩
      rw [hbot] at this
      have hy1' : y = 1 := by simpa using this
      rw [hy1'] at hy3
      norm_num at hy3
    · exact h3
  have hxbarZ : πL xL ∉ Subgroup.center c.Lbar := by
    intro hxcenter
    have hxK : x ∈ centerPreimage_of_onan c :=
      Subgroup.mem_map.mpr ⟨xL, Subgroup.mem_comap.mpr hxcenter, rfl⟩
    exact hxZ (inf_centerPreimage_sylow_le_zSub_of_onan c hON hP
      (Subgroup.mem_inf.mpr ⟨hxK, hxP⟩))
  have hybarZ : πL yL ∉ Subgroup.center c.Lbar := by
    intro hycenter
    have hyK : y ∈ centerPreimage_of_onan c :=
      Subgroup.mem_map.mpr ⟨yL, Subgroup.mem_comap.mpr hycenter, rfl⟩
    exact hyZ (inf_centerPreimage_sylow_le_zSub_of_onan c hON hP
      (Subgroup.mem_inf.mpr ⟨hyK, hyP⟩))
  obtain ⟨gbar, hgbar⟩ := hK6 c.Lbar hON (πL xL) (πL yL)
    hxbar3 hxbarZ hybar3 hybarZ
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective N gbar
  have hlxL : πL (l * xL * l⁻¹) = πL yL := by
    rw [map_mul, map_mul, map_inv, hl, hgbar]
  have hcos : yL⁻¹ * (l * xL * l⁻¹) ∈ N := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change πL (yL⁻¹ * (l * xL * l⁻¹)) = 1
    rw [map_mul, map_inv, hlxL, inv_mul_cancel]
  have hlxL3 : orderOf (l * xL * l⁻¹) = 3 := by
    have hsem : SemiconjBy l xL (l * xL * l⁻¹) := by
      unfold SemiconjBy
      group
    rw [← SemiconjBy.orderOf_eq l hsem, hxL3]
  obtain ⟨j, hjN, hj⟩ :=
    CFSG.GroupTheory.exists_conj_of_order_three_of_mem_same_coset
      (M := ↥c.L) (J := N) CFSG.pCore_isPGroup hyL3 hlxL3 hcos
  let l' : ↥c.L := j * l
  have hl'eq : (l' : G) * x * (l' : G)⁻¹ = y := by
    change ((j * l : ↥c.L) : G) * x * ((j * l : ↥c.L) : G)⁻¹ = y
    have hj' : ((j * (l * xL * l⁻¹) * j⁻¹ : ↥c.L) : G) = y := by
      rw [hj]
    simpa [Subgroup.coe_mul, mul_assoc] using hj'
  have hl'M : (l' : G) ∈ D.M := c.hyp81.1 l'.2
  have hkey : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) ↔
      (l' : G) * z * (l' : G)⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hz
      rw [← hl'eq]
      calc ((l' : G) * z * (l' : G)⁻¹) * ((l' : G) * x * (l' : G)⁻¹) =
          (l' : G) * (z * x) * (l' : G)⁻¹ := by group
        _ = (l' : G) * (x * z) * (l' : G)⁻¹ := by rw [hz]
        _ = ((l' : G) * x * (l' : G)⁻¹) * ((l' : G) * z * (l' : G)⁻¹) := by group
    · intro hz
      have hz' := hz
      rw [← hl'eq] at hz'
      calc z * x = (l' : G)⁻¹ * (((l' : G) * z * (l' : G)⁻¹) *
          ((l' : G) * x * (l' : G)⁻¹)) * (l' : G) := by group
        _ = (l' : G)⁻¹ * (((l' : G) * x * (l' : G)⁻¹) *
          ((l' : G) * z * (l' : G)⁻¹)) * (l' : G) := by rw [hz']
        _ = x * z := by group
  refine ⟨y, hyPL, hy3, hyZ, hCP_syl, ?_⟩
  constructor
  · intro hle z hz
    have hz' : (l' : G) * z * (l' : G)⁻¹ ∈ D.M :=
      hle ((hkey z).mp hz)
    have hzM : z = (l' : G)⁻¹ * ((l' : G) * z * (l' : G)⁻¹) * (l' : G) := by group
    rw [hzM]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hl'M) hz') hl'M
  · intro hle z hz
    have hz' : (l' : G)⁻¹ * z * (l' : G) ∈
        Subgroup.centralizer ({x} : Set G) := by
      have := (hkey ((l' : G)⁻¹ * z * (l' : G))).mpr ?_
      · exact this
      · have hzz : (l' : G) * ((l' : G)⁻¹ * z * (l' : G)) * (l' : G)⁻¹ = z := by
          group
        rwa [hzz]
    have hzM : (l' : G)⁻¹ * z * (l' : G) ∈ D.M := hle hz'
    have hzM' : z = (l' : G) * ((l' : G)⁻¹ * z * (l' : G)) * (l' : G)⁻¹ := by group
    rw [hzM']
    exact D.M.mul_mem (D.M.mul_mem hl'M hzM) (D.M.inv_mem hl'M)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
