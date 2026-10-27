module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJWreath
public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.Quasithin.EmptyFaithful.S151S5B
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quot

public section

namespace CFSG.Quasithin.LJ

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hs : IsSimpleGroup Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x

theorem pCoreOf_le_centralizer {X V : Subgroup G} (hV : IsTwoReducedIn X V) :
    pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
  refine hV.2.2.2 (pCoreOf 2 X) (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X) ?_
  intro d hd
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [this]
  exact Subgroup.one_mem _

theorem isQuasisimple_autI_of_simple {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X) (hsub : IsSubnormal L X)
    (hO2 : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G))
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.Open.IsQuasisimple ↥(autI hV L) := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLX.trans hXN
  have hsurj := L246C127.toAutI_surjective hV L hLN
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    hO2 (S151S5.pCoreOf_le_of_isSubnormal' hsub hx)
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hpcK : ∀ x : ↥L, π x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have h1 : x ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).mp hx
    exact hO2L ⟨x, by assumption, rfl⟩
  have hker : (L246C127.toAutI hV L hLN).ker = CFSG.pCore 2 ↥L := by
    rw [L246C127.toAutI_ker]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      have hKnorm : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (hLN.trans
          (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V))
      have hmn : (((Subgroup.centralizer (V : Set G)).subgroupOf L).map π).Normal :=
        hKnorm.map π hπs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((Subgroup.centralizer (V : Set G)).subgroupOf L).map π) with h | h
      · have hx' : π x ∈ ((Subgroup.centralizer (V : Set G)).subgroupOf L).map π :=
          ⟨x, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
        rw [h, Subgroup.mem_bot] at hx'
        exact (QuotientGroup.eq_one_iff x).mp hx'
      · exfalso
        apply hLV
        intro l hl
        have hmem : π ⟨l, hl⟩ ∈ ((Subgroup.centralizer (V : Set G)).subgroupOf L).map π :=
          h ▸ Subgroup.mem_top _
        obtain ⟨y, hy, hyl⟩ := hmem
        have h1 : π (y⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hyl, inv_mul_cancel]
        have h2 := hpcK _ h1
        have hyC : (y : G) ∈ Subgroup.centralizer (V : Set G) := Subgroup.mem_subgroupOf.mp hy
        have hl' : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
        rw [hl']
        exact (Subgroup.centralizer (V : Set G)).mul_mem hyC h2
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hpcK x ((QuotientGroup.eq_one_iff x).mpr hx)⟩
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autI hV L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact ⟨Group.isPerfect_def.mp hq'.1, hq'.2.1⟩


theorem thompsonJ_le_normalizer_of_ctx15120
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hchar : CharTwo L) :
    thompsonJ (s1516 T Z₁) ≤ Subgroup.normalizer (L : Set G) := by
  set S := s1516 T Z₁ with hSdef
  by_cases hSN : S ≤ Subgroup.normalizer (L : Set G)
  · exact (thompsonJ_le_self151 S).trans hSN
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hlocal := quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2
  have hSyl : IsSylowTwoOf S (L ⊔ S) := hlocal.2.1
  have hpcX : pCoreOf 2 (L ⊔ S) ≠ ⊥ := hlocal.2.2
  have hLX : L ∈ cComp (L ⊔ S) := cComp_of_isLocal hc.hL.mem.2
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hpcX hLX with
      hn | ⟨-, htypes⟩
    · exact absurd (le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)) hSN
    · exact Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  have hcenter := center_eq_bot_of_simple hc.hL.quasi hsimple
  have hz : ∀ x : ↥L ⧸ CFSG.pCore 2 ↥L, (∀ y, y * x = x * y) → x = 1 := fun x hx => by
    have : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.mem_center_iff.mpr hx
    rw [hcenter] at this
    exact Subgroup.mem_bot.mp this
  have hX : CharTwo (L ⊔ S) := S151S5.charTwo_sup_of_simple_comp hSyl.2.1
    (subnormal_of_mem_cComp hLX) (perfect_of_mem_cComp hLX) hchar hc.hL.quasi hz
  have hred := C1GN.isTwoReducedIn_VZ hX hSyl
  have hVe : IsElemAbelian 2 (VZ S (L ⊔ S)) := hred.2.2.1
  have hO2 := pCoreOf_le_centralizer hred
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hLnV : ¬ L ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := by
    intro hLV
    apply hc.hL.not_le
    intro x hx
    refine ⟨hLG hx, hq.centralizer_le_mc ?_⟩
    have hTV : quasithinOmegaOneCenter T ≤ VZ S (L ⊔ S) := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      have hzS : z ∈ S := ⟨hz.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hz.1.2 y (hZ₁T hy)⟩
      have hzZS : z ∈ quasithinOmegaOneCenter S :=
        Subgroup.subset_closure ⟨⟨hzS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_iff.mp hz.1.2 y (s1516_le T Z₁ hy)⟩, hz.2⟩
      exact le_conjClosure _ _ hzZS
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTV) (hLV hx)
  have hquasi := isQuasisimple_autI_of_simple hVe hred.2.1 le_sup_left
    (subnormal_of_mem_cComp hLX) hO2 hLnV hc.hL.quasi hsimple
  have hcomm : ∀ L' ∈ cComp (L ⊔ S), L' ≠ L →
      ⁅L, L'⁆ ≤ Subgroup.centralizer (VZ S (L ⊔ S) : Set G) := by
    intro L' hL' hne
    have := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 hpcX hLX hL' hne.symm
    exact this.1.trans (this.2.trans hO2)
  exact thompsonJ_le_normalizer_of_offenders hVe hred.1 hred.2.1 hSyl hLX hLnV hquasi hcomm

end CFSG.Quasithin.LJ
