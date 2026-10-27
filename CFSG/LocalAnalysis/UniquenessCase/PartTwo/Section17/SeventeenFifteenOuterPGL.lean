module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.WeakClosure81.InFSqAlmostSimple
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
import CFSG.GroupTheory.PGL2Basic
import CFSG.LocalAnalysis.WeakClosure81.CFAutAlmostSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_centSection {L N : Subgroup G} (hLN : L ≤ N)
    (hN : (L.subgroupOf N).Normal) (h7 : IsL2Over17 (Bar2 L) 7)
    (hcentK : Subgroup.centralizer ((L.subgroupOf N).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) : Set (Bar2 N)) = ⊥) :
    CFSG.Open.pCoreOf 2 N = centSection N L (oTwoThreeIn L) := by
  rw [oTwoThreeIn_eq_pCoreOf h7]
  have hNnorm : N ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mp hN
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxN : x ∈ N := hyx ▸ y.2
    have hxNormL : x ∈ Subgroup.normalizer (L : Set G) := hNnorm hxN
    have hxNormB : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxNormL
    refine ⟨hxN, hxNormL, hxNormB, ?_⟩
    intro a ha
    have hxa : x * a * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxNormL a).mp ha
    have hcommL : x * a * x⁻¹ * a⁻¹ ∈ L := L.mul_mem hxa (L.inv_mem ha)
    have haN : a ∈ N := hLN ha
    have hNmem : x * a * x⁻¹ * a⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem hxN haN) (N.inv_mem hxN)) (N.inv_mem haN)
    have hx1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hxN⟩ = 1 :=
      (CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf ⟨x, hxN⟩).mpr hx
    have hcommN : x * a * x⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 N := by
      refine (CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf ⟨_, hNmem⟩).mp ?_
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) _ = 1
      have hdecomp : (⟨x * a * x⁻¹ * a⁻¹, hNmem⟩ : ↥N) =
          ⟨x, hxN⟩ * ⟨a, haN⟩ * ⟨x, hxN⟩⁻¹ * ⟨a, haN⟩⁻¹ := Subtype.ext rfl
      rw [hdecomp]
      simp only [map_mul, map_inv, hx1]
      group
    exact (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLN) ⟨hcommL, hcommN⟩
  · intro x hx
    obtain ⟨hxN, hxNormL, -, hxcent⟩ := hx
    have hxY : (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hxN⟩ ∈
        Subgroup.centralizer ((L.subgroupOf N).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) : Set (Bar2 N)) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro k hk
      obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp hk
      rw [← hlk]
      rw [← map_mul, ← map_mul]
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply (CFSG.mem_openPCoreOf_iff _).mp
      have hcommQ : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 N :=
        (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLN hNnorm)
          (hxcent (l : G) (Subgroup.mem_subgroupOf.mp hl))
      have hcoe : (((l * ⟨x, hxN⟩) / (⟨x, hxN⟩ * l) : ↥N) : G) =
          (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ := by
        rw [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_mul, div_eq_mul_inv]
        group
      rw [hcoe]
      exact (CFSG.Open.pCoreOf 2 N).inv_mem hcommQ
    have hxbot : (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hxN⟩ ∈
        (⊥ : Subgroup (Bar2 N)) := by
      have hxbot' := hxY
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) ⟨x, hxN⟩ ∈
        Subgroup.centralizer ((L.subgroupOf N).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) : Set (Bar2 N)) at hxbot'
      rw [hcentK] at hxbot'
      exact hxbot'
    exact (CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf ⟨x, hxN⟩).mp
      (Subgroup.mem_bot.mp hxbot)

theorem bar2_sup_data {L R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (h7 : IsL2Over17 (Bar2 L) 7) :
    Subgroup.centralizer ((L.subgroupOf (L ⊔ R)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ R))) : Set (Bar2 (L ⊔ R))) = ⊥ ∧
      (IsL2Over17 (Bar2 (L ⊔ R)) 7 ∨
        CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ R))) := by
  classical
  let N : Subgroup G := L ⊔ R
  have hLN : L ≤ N := le_sup_left
  have hRN' : R ≤ N := le_sup_right
  have hNnorm : N ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRN
  have hN : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNnorm
  have hsub : CFSG.Open.IsSubnormal L N :=
    CFSG.Open.IsSubnormal.step hLN hN (CFSG.Open.IsSubnormal.refl N)
  let K : Subgroup (Bar2 N) :=
    (L.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))
  have hKnormal : K.Normal :=
    Subgroup.Normal.map hN (QuotientGroup.mk' (CFSG.pCore 2 ↥N))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N))
  obtain ⟨eK, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_bar2Equiv hLN hsub
  have hKodd : IsL2Odd ↥K 7 :=
    CFSG.Blueprint.LieModel.of_mulEquiv eK (isL2Odd_seven_of_isL2Over17_seven h7)
  have hKcenter : Subgroup.center ↥K = ⊥ := by
    have hbarZ : Subgroup.center (Bar2 L) = ⊥ := by
      have hsc : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 7 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
          (isL2Odd_seven_of_isL2Over17_seven h7)
      obtain ⟨-, F, _, _, hFcard, ⟨eF⟩⟩ := hsc
      let e' : Bar2 L ≃* CFSG.GorensteinWalter.PSL2 F :=
        eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e'
        (CFSG.GorensteinWalter.psl2_center_eq_bot F)
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eK.symm hbarZ
  have htopN : L.subgroupOf N ⊔ R.subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hLN, Subgroup.map_subgroupOf_eq_of_le hRN']
  let g : ↥(R.subgroupOf N) →* Bar2 N ⧸ K :=
    (QuotientGroup.mk' K).comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp
      (R.subgroupOf N).subtype)
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) y'
    have hmem : n ∈ L.subgroupOf N ⊔ R.subgroupOf N := by
      rw [htopN]
      exact Subgroup.mem_top n
    obtain ⟨l, hl, r, hr, hlr⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨⟨r, hr⟩, ?_⟩
    change (QuotientGroup.mk' K) ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)) r) =
      (QuotientGroup.mk' K) ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)) n)
    rw [← hlr, map_mul, map_mul]
    have hl1 : (QuotientGroup.mk' K) ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)) l) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem _ hl)
    rw [hl1, one_mul]
  have hR2N : IsPGroup 2 (R.subgroupOf N) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRN').symm
  have hYquot2 : IsPGroup 2 (Bar2 N ⧸ K) := IsPGroup.of_surjective hR2N g hgsurj
  obtain ⟨nidx, hnidx⟩ := IsPGroup.iff_card.mp hYquot2
  have hKindex : ∃ n : ℕ, K.index = 2 ^ n := by
    refine ⟨nidx, ?_⟩
    rw [Subgroup.index_eq_card]
    exact hnidx
  have hCbot : Subgroup.centralizer (K : Set (Bar2 N)) ⊓ K = ⊥ := by
    rw [inf_comm]
    exact CFSG.GH74.Uniqueness.inf_centralizer_eq_bot_of_center K hKcenter
  have hcentK : Subgroup.centralizer (K : Set (Bar2 N)) =
      (Subgroup.center ↥K).map K.subtype := by
    rw [hKcenter, Subgroup.map_bot]
    let C : Subgroup (Bar2 N) := Subgroup.centralizer (K : Set (Bar2 N))
    have hCnormal : C.Normal := Subgroup.normal_centralizer
    let f : ↥C →* Bar2 N ⧸ K := (QuotientGroup.mk' K).comp C.subtype
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      apply le_bot_iff.mp
      intro x hx
      have hx1 : f x = 1 := hx
      have hxK : (x : Bar2 N) ∈ K :=
        (QuotientGroup.eq_one_iff (x : Bar2 N)).mp hx1
      have hxinf : (x : Bar2 N) ∈ C ⊓ K := ⟨x.2, hxK⟩
      rw [hCbot] at hxinf
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxinf))
    have hC2 : IsPGroup 2 C := IsPGroup.of_injective hYquot2 f hfinj
    have hCle : C ≤ CFSG.pCore 2 (Bar2 N) := le_sSup ⟨hCnormal, hC2⟩
    rw [show CFSG.pCore 2 (Bar2 N) = ⊥ from
      CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hCle
    exact le_bot_iff.mp hCle
  have hcentBot : Subgroup.centralizer (K : Set (Bar2 N)) = ⊥ := by
    rw [hcentK, hKcenter, Subgroup.map_bot]
  have hKLext : K = ⊤ ∨ CFSG.Quasithin.F6.IsPGL2 7 (Bar2 N) :=
    K_L27Extension (Bar2 N) K hKnormal hKodd hcentK hKindex
  refine ⟨?_, ?_⟩
  · simpa [K, N] using hcentBot
  · rcases hKLext with htop | hPGL
    · left
      have hYodd : IsL2Odd (Bar2 N) 7 :=
        CFSG.Blueprint.LieModel.of_mulEquiv
          ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv (G := Bar2 N))) hKodd
      exact ⟨7, 1, by norm_num, by norm_num, by norm_num, by norm_num, hYodd⟩
    · exact Or.inr hPGL

theorem isPGL2_mulAut_of_isL2Over17_seven {X : Type} [Group X]
    (h : IsL2Over17 X 7) : CFSG.Quasithin.F6.IsPGL2 7 (MulAut X) := by
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨eX⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel
      (isL2Odd_seven_of_isL2Over17_seven h) (by decide)
  have hF7 : Nat.card F = 7 := by rw [hFcard, pow_one]
  have hoddF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by norm_num, ⟨3, by norm_num⟩, le_rfl, by rw [hF7]; norm_num⟩
  have hcardF : 3 < Nat.card F := by rw [hF7]; norm_num
  let e : X ≃* CFSG.GorensteinWalter.PSL2 F :=
    eX.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  let eA : MulAut X ≃* MulAut (CFSG.GorensteinWalter.PSL2 F) := MulAut.congr e
  let eP : CFSG.GorensteinWalter.PGL2 F ≃* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
    MulEquiv.ofBijective _ (CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hF7 hoddF hcardF)
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  exact ⟨F, hF, hFfin, hF7,
    ⟨(eA.trans eP.symm).trans (QuotientGroup.quotientMulEquivOfEq hcs)⟩⟩

theorem card_mulAut_of_isL2Over17_seven {X : Type} [Group X]
    (h : IsL2Over17 X 7) : Nat.card (MulAut X) = 336 :=
  CFSG.GroupTheory.card_of_isPGL2_seven (isPGL2_mulAut_of_isL2Over17_seven h)

theorem gap17_15_autPGL2_of (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    Gap17_15_autPGL2 D V₀ V L r q hC := by
  intro h7 hYs hN
  classical
  let N : Subgroup G := L ⊔ D.T
  have hLN : L ≤ N := le_sup_left
  have hTN : D.T ≤ N := le_sup_right
  have hNnorm : N ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mp hN
  let K : Subgroup (Bar2 N) :=
    (L.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))
  have hdata := bar2_sup_data (L := L) (R := D.T) D.sylowM.isPGroup
    (le_trans hTN hNnorm) h7
  have hcentK : Subgroup.centralizer (K : Set (Bar2 N)) = ⊥ := by
    simpa [K, N] using hdata.1
  have hPGL : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 N) := by
    rcases hdata.2 with hL2 | hPGL
    · exact absurd (by simpa [N] using hL2) hYs
    · exact hPGL
  have hcentEq : CFSG.Open.pCoreOf 2 N = centSection N L (oTwoThreeIn L) :=
    pCoreOf_eq_centSection hLN hN h7 hcentK
  let φ : ↥(N ⊓ normalizer (L : Set G)) →* Bar2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion inf_le_left)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥N) y
    exact ⟨⟨n, Subgroup.mem_inf.mpr ⟨n.2, hNnorm n.2⟩⟩, rfl⟩
  have hφker : ∀ x : ↥(N ⊓ normalizer (L : Set G)),
      φ x = 1 ↔ (x : G) ∈ centSection N L (oTwoThreeIn L) := by
    intro x
    have hx : φ x = 1 ↔ ((Subgroup.inclusion inf_le_left x : ↥N) : G) ∈
        CFSG.Open.pCoreOf 2 N :=
      CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion inf_le_left x)
    rw [hx, hcentEq]
    rfl
  exact ⟨hPGL, Bar2 N, inferInstance, φ, hφsurj, hφker, hPGL⟩

theorem gap17_15_swapSplit_of (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    Gap17_15_swapSplit D V₀ V L r q hC := by
  intro h7 _
  have h := (bar2_sup_data (L := L) (R := NTL17 D L)
    (D.sylowM.isPGroup.to_le inf_le_left) inf_le_right h7).2
  simpa using h

theorem gap17_15_pairPGL2_of (h410 : W4Lem4_10) (D : Data G)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) :
    Gap17_15_pairPGL2 D V₀ V L r q hC := by
  intro hPGL
  exact CFSG.LocalAnalysis.WeakClosure81.inF_top_of_inFGroup 1
    (CFSG.LocalAnalysis.WeakClosure81.inFGroup_of_isPGL2_seven h410 (Bar2 (L ⊔ D.T)) hPGL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
