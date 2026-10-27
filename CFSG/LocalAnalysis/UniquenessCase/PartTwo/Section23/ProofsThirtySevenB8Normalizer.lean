module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsThirtySevenB8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineDecomp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNinePush
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerCartanCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenTorus
import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.BZeroCentralizerZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

theorem L_inf_centralizer_Z_eq (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.L ⊓ Subgroup.centralizer (D.Z : Set G) = D.T ⊓ c.L := by
  classical
  have hTZ : D.T ≤ Subgroup.centralizer (D.Z : Set G) := uc22main1_T_le_centralizer D
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ c.L) c.L :=
    (D.sylowG.of_le c.hL.1.1 le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  refine le_antisymm ?_ (le_inf inf_le_right (inf_le_left.trans hTZ))
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer (D.Z : Set G)
  let M : Subgroup G := c.L ⊓ Subgroup.centralizer (c.V : Set G)
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hMK : M ≤ K :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hZleV))
  have hM2 : IsPGroup 2 M := isPGroup_inf_centralizer_L D Ch h4 h23 h1930 c
  have hLV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    le_sup_left.trans (sup_le_normalizer_V D Ch c)
  have hLCV : c.L ≤ Subgroup.normalizer (Subgroup.centralizer (c.V : Set G) : Set G) :=
    hLV.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.V)
  have hLnormM : c.L ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf Subgroup.le_normalizer hLCV).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKnormM : K ≤ Subgroup.normalizer (M : Set G) := inf_le_left.trans hLnormM
  haveI : (M.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMK).mpr hKnormM
  have hM2' : IsPGroup 2 ↥(M.subgroupOf K) :=
    hM2.of_equiv (Subgroup.subgroupOfEquivOfLe hMK).symm
  have hquot : IsPGroup 2 (↥K ⧸ M.subgroupOf K) := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    refine ⟨1, ?_⟩
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      have hgsq : ((x : G) ^ 2) ∈ M :=
        sq_mem_inf_centralizer_V_of_mem_centralizer_Z D Ch h4 h23 h1930 c x.2.1 x.2.2
      have hx2 : x * x ∈ M.subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hgsq)
      rw [pow_one, pow_two, ← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff (x * x)).mpr hx2
  have hK2 : IsPGroup 2 ↥K := IsPGroup.of_subgroup_of_quotient hM2' hquot
  have hTK : D.T ⊓ c.L ≤ K := fun x hx => mem_inf.mpr ⟨hx.2, hTZ hx.1⟩
  have heq : K = D.T ⊓ c.L := hSyl.eq_of_le hTK inf_le_left hK2
  change K ≤ D.T ⊓ c.L
  rw [heq]

theorem sylowImage_L (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    ∃ S : Sylow 2 (Bar2 c.L),
      (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
        ((D.T ⊓ c.L).subgroupOf c.L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ c.L) c.L :=
    (D.sylowG.of_le c.hL.1.1 le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  let S : Sylow 2 (Bar2 c.L) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (QuotientGroup.mk'_surjective _) Q
  exact ⟨S, by rw [Sylow.coe_mapSurjective, hQ]⟩

theorem B0_le_borelOf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.B0 ≤ CFSG.Quasithin.borelOf c.L D.T := by
  have hN1 : c.L ⊓ Subgroup.centralizer (D.Z : Set G) = D.T ⊓ c.L :=
    L_inf_centralizer_Z_eq D Ch h4 h23 h1930 c
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    have h4c := h4 h1930 c
    simpa [h4c.1] using h4c.2.2
  have hB0L : c.B0 ≤ c.L := c.hB0.1.trans c.hL0L
  have hB0normZ : c.B0 ≤
      Subgroup.normalizer (Subgroup.centralizer (D.Z : Set G) : Set G) :=
    (c.hBM.trans hMZ).trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.Z)
  have hB0normTL : c.B0 ≤
      Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := by
    have h : c.B0 ≤ Subgroup.normalizer
        ((c.L ⊓ Subgroup.centralizer (D.Z : Set G) : Subgroup G) : Set G) :=
      (le_inf (fun b hb => Subgroup.le_normalizer (hB0L hb)) hB0normZ).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rwa [hN1] at h
  exact le_inf hB0L hB0normTL

theorem normalizer_TL_le_normalizer_T (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    CFSG.Quasithin.borelOf c.L D.T ≤
      Subgroup.normalizer (D.T : Set G) ⊓ D.M := by
  have hP1 := T_eq_sup_inf_centralizer D Ch h4 h23 h1930 c
  have hSylLT : CFSG.ABGLocalTools.IsSylowOf 2 D.T (c.L ⊔ D.T) :=
    (D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c).2 le_top).of_le le_sup_right
      (sup_le_N D Ch c)
  have hO2T : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylLT)
  have hcent : D.T ⊓ Subgroup.centralizer (c.V : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    (centTVLeO2LT_of D Ch h4 h23) h1930 c
  have hTeq : D.T = (D.T ⊓ c.L) ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := by
    refine le_antisymm ?_ (sup_le inf_le_left hO2T)
    calc D.T = (D.T ⊓ c.L) ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) := hP1
      _ ≤ (D.T ⊓ c.L) ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) := sup_le_sup_left hcent _
  have hB : CFSG.Quasithin.borelOf c.L D.T ≤
      Subgroup.normalizer ((D.T ⊓ c.L) ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Subgroup G) := by
    intro x hx
    have hxL : x ∈ c.L := hx.1
    have hxTL : x ∈ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := hx.2
    have hxLT : x ∈ Subgroup.normalizer ((c.L ⊔ D.T : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (show x ∈ c.L ⊔ D.T from mem_sup_left hxL)
    have hxO : x ∈ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Subgroup G) : Set G) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf
        (c.L ⊔ D.T)) hxLT
    exact (Subgroup.inf_normalizer_le_normalizer_sup _ _) ⟨hxTL, hxO⟩
  have hNT : CFSG.Quasithin.borelOf c.L D.T ≤ Subgroup.normalizer (D.T : Set G) := by
    intro x hx
    have hxA : x ∈ Subgroup.normalizer
        (((D.T ⊓ c.L) ⊔ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) : Subgroup G) : Set G) := hB hx
    rwa [hTeq]
  exact le_inf hNT (hNT.trans D.normalizer_le)

theorem normalizer_T_le_N {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) :
    Subgroup.normalizer (D.T : Set G) ≤ c.N := by
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    have h4c := h4 h1930 c
    simpa [h4c.1] using h4c.2.2
  have hJleT : InS3.thompsonJ D.T ≤ D.T := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.Quasithin.B6.thompsonJ_le D.T
  exact hPush h1930 c h3 D.T le_rfl Subgroup.le_normalizer
    ⟨1, D.T.one_mem, le_sup_left⟩ (c.V_le_T h4 h1930) hJleT
    (Subgroup.normalizer (D.T : Set G)) le_rfl
    (D.normalizer_le.trans hMZ)

end Ctx23L

theorem commutator_mem_inf_of_rhoL_inner {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) (hComm : KL2BorelComm)
    {k : ℕ} (hL2 : IsL2 (Bar2 K) k) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxT : x ∈ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G))
    (hinn : UC6S846.rhoL K ⟨x, hxK⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range)
    {d : G} (hd : d ∈ CFSG.Quasithin.borelOf K D.T) :
    x * d * x⁻¹ * d⁻¹ ∈ D.T ⊓ K := by
  classical
  obtain ⟨y, hy⟩ := hinn
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  have hO : CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := pCoreOf_le_inf_sylow hK hKn
  have hcomap := bar2_comap_map_subgroupOf hO
  have hSbar : (S : Subgroup (Bar2 K)) =
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.sylowBar2 K (D.T ⊓ K) := by
    rw [hS]
  have hxmap : (S : Subgroup (Bar2 K)).map (UC6S846.rhoL K ⟨x, hxK⟩).toMonoidHom =
      (S : Subgroup (Bar2 K)) := by
    rw [hSbar]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
      ⟨x, hxK⟩ hxT
  have hyS : y ∈ Subgroup.normalizer ((S : Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [hy] using hxmap
  have hdK : d ∈ K := CFSG.Quasithin.F1.borelOf_le K D.T hd
  have hdN : d ∈ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    CFSG.Quasithin.F1.borelOf_le_normalizer K D.T hd
  have hdKnorm : d ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hdK
  have hdmap : (S : Subgroup (Bar2 K)).map
      (UC6S846.rhoL K ⟨d, hdKnorm⟩).toMonoidHom = (S : Subgroup (Bar2 K)) := by
    rw [hSbar]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
      ⟨d, hdKnorm⟩ hdN
  have hdbarS : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩ ∈
      Subgroup.normalizer ((S : Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [UC6S846.rhoL_inner K d hdK] using hdmap
  have hcommS : y * (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩) * y⁻¹ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩)⁻¹ ∈ (S : Subgroup (Bar2 K)) :=
    hComm (Bar2 K) k hL2 S y hyS _ hdbarS
  have hfix : UC6S846.rhoL K ⟨x, hxK⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩)⁻¹ ∈
      (S : Subgroup (Bar2 K)) := by
    rw [← hy]
    simpa [MulAut.conj_apply] using hcommS
  have hfix' : UC6S846.rhoL K ⟨x, hxK⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d, hdK⟩)⁻¹ ∈
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ((D.T ⊓ K).subgroupOf K) := by
    rwa [← hS]
  exact commutator_mem_of_rhoL hcomap hxK hdK hfix'

private theorem borelOf_sz_conj_mem_T {D : Data G} (hSzAut : KSzTwoAut) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {m : ℕ}
    (hSz : IsSz (Bar2 K) m) :
    ∀ c ∈ CFSG.Quasithin.borelOf K D.T, ∀ t ∈ D.T, c * t * c⁻¹ ∈ D.T := by
  classical
  intro c hc t ht
  obtain ⟨hcK, hcTL⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨S, hS⟩ := sylowImage_isSylow hK hKn
  have hT2 : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowM
  have hO : CFSG.Open.pCoreOf 2 K ≤ D.T ⊓ K := pCoreOf_le_inf_sylow hK hKn
  have hcomap := bar2_comap_map_subgroupOf hO
  have hSbar : (S : Subgroup (Bar2 K)) =
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.sylowBar2 K (D.T ⊓ K) := by
    rw [hS]
  have htK : t ∈ Subgroup.normalizer (K : Set G) := T_le_normalizer_of_normal hK hKn ht
  have htTL : t ∈ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    T_le_normalizer_inf hK hKn ht
  have hθmap : Subgroup.map (UC6S846.rhoL K ⟨t, htK⟩).toMonoidHom
      (S : Subgroup (Bar2 K)) = (S : Subgroup (Bar2 K)) := by
    rw [hSbar]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2 ⟨t, htK⟩ htTL
  have hθS : ∀ x ∈ (S : Subgroup (Bar2 K)),
      UC6S846.rhoL K ⟨t, htK⟩ x ∈ (S : Subgroup (Bar2 K)) := by
    intro x hx
    rw [← hθmap]
    exact Subgroup.mem_map_of_mem (UC6S846.rhoL K ⟨t, htK⟩).toMonoidHom hx
  have hord : ∃ n : ℕ, orderOf (UC6S846.rhoL K ⟨t, htK⟩) = 2 ^ n :=
    exists_orderOf_eq_prime_pow_iff.mpr
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.exists_rhoL_pow_two_pow_eq_one
        hT2 ⟨t, htK⟩ ht)
  obtain ⟨s, hsS, hθ⟩ := hSzAut (Bar2 K) m hSz S _ hord hθS
  obtain ⟨y, hyS, hys⟩ := Subgroup.mem_map.mp (by rwa [hS] at hsS)
  have hyT : (y : G) ∈ D.T ⊓ K := Subgroup.mem_subgroupOf.mp hyS
  have hsbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y) ∈ (S : Subgroup (Bar2 K)) := by
    rwa [hys]
  have hθy : UC6S846.rhoL K ⟨t, htK⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y) := by
    rw [hθ, ← hys]
  have hcKnorm : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hcK
  have hcmap : (S : Subgroup (Bar2 K)).map
      (UC6S846.rhoL K ⟨c, hcKnorm⟩).toMonoidHom = (S : Subgroup (Bar2 K)) := by
    rw [hSbar]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
      ⟨c, hcKnorm⟩ hcTL
  have hcbarS : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩ ∈
      Subgroup.normalizer ((S : Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [UC6S846.rhoL_inner K c hcK] using hcmap
  have hcommS : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y)⁻¹ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩)⁻¹ ∈
      (S : Subgroup (Bar2 K)) := by
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩)⁻¹ ∈
        (S : Subgroup (Bar2 K)) :=
      (Subgroup.mem_normalizer_iff.mp hcbarS _).mp ((S : Subgroup (Bar2 K)).inv_mem hsbar)
    simpa [mul_assoc] using (S : Subgroup (Bar2 K)).mul_mem hsbar hmem
  have hfixS : UC6S846.rhoL K ⟨t, htK⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩)⁻¹ ∈
      (S : Subgroup (Bar2 K)) := by
    rw [hθy]
    simpa [MulAut.conj_apply, mul_assoc] using hcommS
  have hfix' : UC6S846.rhoL K ⟨t, htK⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨c, hcK⟩)⁻¹ ∈
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ((D.T ⊓ K).subgroupOf K) := by
    rwa [← hS]
  have hresult := commutator_mem_of_rhoL hcomap htK hcK hfix'
  have hinv : c * t * c⁻¹ * t⁻¹ ∈ D.T := by
    have h := D.T.inv_mem hresult.1
    rwa [show (t * c * t⁻¹ * c⁻¹)⁻¹ = c * t * c⁻¹ * t⁻¹ by group] at h
  have hct : c * t * c⁻¹ = (c * t * c⁻¹ * t⁻¹) * t := by group
  rw [hct]
  exact D.T.mul_mem hinv ht

theorem borelOf_le_normalizer_T_of_isSz {D : Data G} (hSzAut : KSzTwoAut) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {m : ℕ} (hSz : IsSz (Bar2 K) m) :
    CFSG.Quasithin.borelOf K D.T ≤ Subgroup.normalizer (D.T : Set G) := by
  intro c hc
  have hmain := borelOf_sz_conj_mem_T (D := D) hSzAut hK hKn hSz
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨hmain c hc t, ?_⟩
  intro hct
  have h := hmain c⁻¹ ((CFSG.Quasithin.borelOf K D.T).inv_mem hc) (c * t * c⁻¹) hct
  rwa [show c⁻¹ * (c * t * c⁻¹) * (c⁻¹)⁻¹ = t by group] at h

private theorem borelOf_mem_sylow_iff {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {S : Sylow 2 (Bar2 c.L)}
    (hS : (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      ((D.T ⊓ c.L).subgroupOf c.L))
    {x : G} (hxB : x ∈ CFSG.Quasithin.borelOf c.L D.T) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨x, hxB.1⟩ ∈ (S : Subgroup (Bar2 c.L)) ↔
      x ∈ D.T ⊓ c.L := by
  classical
  have hO2leTL : CFSG.pCore 2 ↥c.L ≤ (D.T ⊓ c.L).subgroupOf c.L := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr
      ⟨Ctx23L.pCoreOf_L_le_T D Ch c (Subgroup.mem_map_of_mem c.L.subtype hz), z.2⟩
  constructor
  · intro hq
    rw [hS] at hq
    obtain ⟨y, hy, hqy⟩ := Subgroup.mem_map.mp hq
    have hyTL : (y : G) ∈ D.T ⊓ c.L := Subgroup.mem_subgroupOf.mp hy
    have hdiv : (y / ⟨x, hxB.1⟩ : ↥c.L) ∈ CFSG.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_iff_div_mem]
      exact hqy
    have hxsub : (⟨x, hxB.1⟩ : ↥c.L) ∈ (D.T ⊓ c.L).subgroupOf c.L := by
      have hxeq : (⟨x, hxB.1⟩ : ↥c.L) = (y / ⟨x, hxB.1⟩)⁻¹ * y := by
        rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      rw [hxeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hO2leTL hdiv)) hy
    exact Subgroup.mem_subgroupOf.mp hxsub
  · intro hxTL
    rw [hS]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxTL)

theorem borelOf_mem_normalizer_sylow {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {S : Sylow 2 (Bar2 c.L)}
    (hS : (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      ((D.T ⊓ c.L).subgroupOf c.L))
    {x : G} (hxB : x ∈ CFSG.Quasithin.borelOf c.L D.T) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨x, hxB.1⟩ ∈
      Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) := by
  have hxL : x ∈ c.L := hxB.1
  have hxTL : x ∈ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := hxB.2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj (QuotientGroup.mk (⟨x, hxL⟩ : ↥c.L))).toMonoidHom
    (S : Subgroup (Bar2 c.L)) = (S : Subgroup (Bar2 c.L))
  rw [← UC6S846.rhoL_inner c.L x hxL, hS]
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
    (L := c.L) (U := D.T ⊓ c.L) ⟨x, Subgroup.le_normalizer hxL⟩ hxTL

private theorem index_pCore_subgroupOf_borelOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {n : ℕ} (hL2 : IsL2 (Bar2 c.L) n) (hCard : KL2BorelCard)
    {S : Sylow 2 (Bar2 c.L)}
    (hS : (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      ((D.T ⊓ c.L).subgroupOf c.L)) :
    ((CFSG.Open.pCoreOf 2 c.L).subgroupOf (CFSG.Quasithin.borelOf c.L D.T)).index =
      Nat.card (Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L))) := by
  classical
  let q : ↥c.L →* Bar2 c.L := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  let B : Subgroup G := CFSG.Quasithin.borelOf c.L D.T
  have hBleL : B ≤ c.L := CFSG.Quasithin.F1.borelOf_le c.L D.T
  let qB : ↥B →* Bar2 c.L := q.comp (Subgroup.inclusion hBleL)
  have hO2leTL : CFSG.Open.pCoreOf 2 c.L ≤ D.T ⊓ c.L :=
    le_inf (Ctx23L.pCoreOf_L_le_T D Ch c) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hker : qB.ker = (CFSG.Open.pCoreOf 2 c.L).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ((Subgroup.inclusion hBleL x : ↥c.L) : Bar2 c.L) = 1 ↔
      (x : G) ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype
    rw [QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem (f := c.L.subtype) c.L.subtype_injective
      (K := CFSG.pCore 2 ↥c.L) (x := Subgroup.inclusion hBleL x)).symm
  have hrange : qB.range = Subgroup.normalizer
      ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hxL : (x : G) ∈ c.L := hBleL x.2
      have hxTL : (x : G) ∈
          Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := x.2.2
      have hxmap : (S : Subgroup (Bar2 c.L)).map
          (UC6S846.rhoL c.L ⟨(x : G), Subgroup.le_normalizer hxL⟩).toMonoidHom =
          (S : Subgroup (Bar2 c.L)) := by
        rw [hS]
        exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_map_sylowBar2
          (L := c.L) (U := D.T ⊓ c.L) ⟨(x : G), Subgroup.le_normalizer hxL⟩ hxTL
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change Subgroup.map
        (MulAut.conj (QuotientGroup.mk (⟨(x : G), hxL⟩ : ↥c.L))).toMonoidHom
        (S : Subgroup (Bar2 c.L)) = (S : Subgroup (Bar2 c.L))
      rw [← UC6S846.rhoL_inner c.L (x : G) hxL]
      exact hxmap
    · intro hy
      obtain ⟨xL, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) y
      rw [hS] at hy
      have hxN : (xL : G) ∈
          Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) :=
        mem_normalizer_of_bar2_mem inf_le_right
          (bar2_comap_map_subgroupOf hO2leTL) hy
      have hxB : (xL : G) ∈ B := Subgroup.mem_inf.mpr ⟨xL.2, hxN⟩
      exact ⟨⟨(xL : G), hxB⟩, rfl⟩
  rw [Subgroup.index_eq_card, ← hker, ← hrange]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qB).toEquiv

private theorem relIndex_pCore_subgroupOf_borelOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {n : ℕ} (hL2 : IsL2 (Bar2 c.L) n) (hCard : KL2BorelCard)
    {S : Sylow 2 (Bar2 c.L)}
    (hS : (S : Subgroup (Bar2 c.L)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      ((D.T ⊓ c.L).subgroupOf c.L)) :
    ((CFSG.Open.pCoreOf 2 c.L).subgroupOf (CFSG.Quasithin.borelOf c.L D.T)).relIndex
        ((D.T ⊓ c.L).subgroupOf (CFSG.Quasithin.borelOf c.L D.T)) =
      Nat.card (S : Subgroup (Bar2 c.L)) := by
  classical
  let q : ↥c.L →* Bar2 c.L := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  let B : Subgroup G := CFSG.Quasithin.borelOf c.L D.T
  have hBleL : B ≤ c.L := CFSG.Quasithin.F1.borelOf_le c.L D.T
  have hTLB : D.T ⊓ c.L ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  let N0 : Subgroup ↥B := (D.T ⊓ c.L).subgroupOf B
  let qN : ↥N0 →* Bar2 c.L := q.comp ((Subgroup.inclusion hBleL).comp N0.subtype)
  have hO2leTL : CFSG.Open.pCoreOf 2 c.L ≤ D.T ⊓ c.L :=
    le_inf (Ctx23L.pCoreOf_L_le_T D Ch c) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hkerN : qN.ker = ((CFSG.Open.pCoreOf 2 c.L).subgroupOf B).subgroupOf N0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change ((Subgroup.inclusion hBleL x.1 : ↥c.L) : Bar2 c.L) = 1 ↔
      (x : G) ∈ (CFSG.pCore 2 ↥c.L).map c.L.subtype
    rw [QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem (f := c.L.subtype) c.L.subtype_injective
      (K := CFSG.pCore 2 ↥c.L) (x := Subgroup.inclusion hBleL x.1)).symm
  have hrangeN : qN.range = (S : Subgroup (Bar2 c.L)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hxTL : (x : G) ∈ D.T ⊓ c.L := Subgroup.mem_subgroupOf.mp x.2
      rw [hS]
      exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hxTL)
    · intro hy
      rw [hS] at hy
      obtain ⟨yL, hyL, rfl⟩ := Subgroup.mem_map.mp hy
      have hyTL : (yL : G) ∈ D.T ⊓ c.L := Subgroup.mem_subgroupOf.mp hyL
      have hyB : (yL : G) ∈ B := hTLB hyTL
      refine ⟨⟨⟨(yL : G), hyB⟩, Subgroup.mem_subgroupOf.mpr hyTL⟩, rfl⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hkerN, ← hrangeN]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qN).toEquiv

theorem Ctx23L.exists_cartan_L (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hCard : KL2BorelCard) (hComm : KL2BorelComm) :
    ∃ DL : Subgroup G, DL ≤ CFSG.Quasithin.borelOf c.L D.T ∧
      Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1 ∧ IsMulCommutative DL ∧
      (D.T ⊓ c.L) ⊓ DL = ⊥ ∧
      (D.T ⊓ c.L) ⊔ DL = CFSG.Quasithin.borelOf c.L D.T := by
  classical
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  obtain ⟨hV, hL2, -⟩ := h23 h1930 c
  obtain ⟨S, hS⟩ := sylowImage_L D Ch c
  let B : Subgroup G := CFSG.Quasithin.borelOf c.L D.T
  have hBleL : B ≤ c.L := CFSG.Quasithin.F1.borelOf_le c.L D.T
  have hTLB : D.T ⊓ c.L ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  let N0 : Subgroup ↥B := (D.T ⊓ c.L).subgroupOf B
  have hO2leTL : CFSG.Open.pCoreOf 2 c.L ≤ D.T ⊓ c.L :=
    le_inf (Ctx23L.pCoreOf_L_le_T D Ch c) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hcardS : Nat.card (S : Subgroup (Bar2 c.L)) = 2 ^ n ∧
      Nat.card (Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L))) =
        2 ^ n * (2 ^ n - 1) := hCard (Bar2 c.L) n hL2 S
  have hidxO := index_pCore_subgroupOf_borelOf (D := D) (Ch := Ch) c hL2 hCard hS
  have hrelO := relIndex_pCore_subgroupOf_borelOf (D := D) (Ch := Ch) c hL2 hCard hS
  have hO2leN0 : (CFSG.Open.pCoreOf 2 c.L).subgroupOf B ≤ N0 := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO2leTL (Subgroup.mem_subgroupOf.mp hx))
  have hN0index : N0.index = 2 ^ n - 1 := by
    have hmul := Subgroup.relIndex_mul_index (H := (CFSG.Open.pCoreOf 2 c.L).subgroupOf B)
      (K := N0) hO2leN0
    rw [hrelO, hidxO, hcardS.1, hcardS.2] at hmul
    exact Nat.mul_left_cancel (pow_pos (by norm_num) n) hmul
  have hn2 : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 hL2
  have hN0p : IsPGroup 2 ↥N0 := by
    have hTL2 : IsPGroup 2 ↥(D.T ⊓ c.L) :=
      IsPGroup.to_inf_left (p := 2) (H := D.T) (K := c.L)
        (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowM)
    exact hTL2.of_equiv (Subgroup.subgroupOfEquivOfLe hTLB).symm
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hodd : Odd (2 ^ n - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn0
  have hcop : Nat.Coprime (Nat.card N0) N0.index := by
    obtain ⟨k, hk⟩ := hN0p.exists_card_eq
    rw [hk, hN0index]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hN0normal : N0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTLB).mpr inf_le_right
  haveI : N0.Normal := hN0normal
  obtain ⟨A, hA⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hAcomm : A.IsComplement' N0 := Subgroup.isComplement'_comm.mp hA
  let DL : Subgroup G := A.map B.subtype
  have hDLleB : DL ≤ B := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hmapN0 : N0.map B.subtype = D.T ⊓ c.L := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTLB]
  have hcardDL : Nat.card DL = 2 ^ n - 1 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    have hAindex : Nat.card A = N0.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr hAcomm.QuotientMulEquiv.symm.toEquiv
    rw [hAindex, hN0index]
  have hdisj : A ⊓ N0 = ⊥ := disjoint_iff.mp hAcomm.disjoint
  have hinfDL : (D.T ⊓ c.L) ⊓ DL = ⊥ := by
    calc (D.T ⊓ c.L) ⊓ DL = (N0.map B.subtype) ⊓ (A.map B.subtype) := by rw [hmapN0]
      _ = (N0 ⊓ A).map B.subtype := by
        rw [Subgroup.map_inf_eq N0 A B.subtype B.subtype_injective]
      _ = (A ⊓ N0).map B.subtype := by rw [inf_comm]
      _ = ⊥ := by rw [hdisj, Subgroup.map_bot]
  have hsupDL : (D.T ⊓ c.L) ⊔ DL = B := by
    calc (D.T ⊓ c.L) ⊔ DL = (N0.map B.subtype) ⊔ (A.map B.subtype) := by rw [hmapN0]
      _ = (N0 ⊔ A).map B.subtype := by rw [Subgroup.map_sup]
      _ = (A ⊔ N0).map B.subtype := by rw [sup_comm]
      _ = (⊤ : Subgroup ↥B).map B.subtype := by rw [hAcomm.sup_eq_top]
      _ = B.subtype.range := Subgroup.map_top B.subtype
      _ = B := Subgroup.range_subtype B
  refine ⟨DL, hDLleB, hcardDL, ?_, hinfDL, hsupDL⟩
  refine IsMulCommutative.of_comm ?_
  intro a b
  apply Subtype.ext
  have haB : (a : G) ∈ B := hDLleB a.2
  have hbB : (b : G) ∈ B := hDLleB b.2
  have haN := borelOf_mem_normalizer_sylow (D := D) (Ch := Ch) c hS haB
  have hbN := borelOf_mem_normalizer_sylow (D := D) (Ch := Ch) c hS hbB
  have hcommN := hComm (Bar2 c.L) n hL2 S _ haN _ hbN
  have hcommB : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem haB hbB) (B.inv_mem haB)) (B.inv_mem hbB)
  have hsub : (⟨(a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹, hcommB.1⟩ : ↥c.L) =
      ⟨(a : G), haB.1⟩ * ⟨(b : G), hbB.1⟩ * ⟨(a : G), haB.1⟩⁻¹ *
        ⟨(b : G), hbB.1⟩⁻¹ := Subtype.ext rfl
  have hcommN' : QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
        (⟨(a : G), haB.1⟩ * ⟨(b : G), hbB.1⟩ * ⟨(a : G), haB.1⟩⁻¹ *
          ⟨(b : G), hbB.1⟩⁻¹) ∈ (S : Subgroup (Bar2 c.L)) := by
    simpa only [map_mul, map_inv] using hcommN
  have hmemTL : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ D.T ⊓ c.L :=
    (borelOf_mem_sylow_iff (D := D) (Ch := Ch) c hS hcommB).mp (by
      rw [hsub]
      exact hcommN')
  have hmemDL : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ DL :=
    DL.mul_mem (DL.mul_mem (DL.mul_mem a.2 b.2) (DL.inv_mem a.2)) (DL.inv_mem b.2)
  have hbot : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hinfDL]
    exact Subgroup.mem_inf.mpr ⟨hmemTL, hmemDL⟩
  have hone : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := Subgroup.mem_bot.mp hbot
  calc (a : G) * (b : G) =
        ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by group
    _ = (b : G) * (a : G) := by rw [hone, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
