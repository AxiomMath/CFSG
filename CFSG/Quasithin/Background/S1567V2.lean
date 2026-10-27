module

public import CFSG.Quasithin.Background.S1567V1
public import CFSG.Quasithin.Background.S1567W4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

@[expose] def Input15368PsiL3Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2))) →
    Nat.card ↥(⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆) ≤ 2 ^ 6

namespace S1567

section Loc

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem mem_normalizer_inf67 {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  have h1 := conjSubgroup_eq_iff_mem_normalizer.mpr hH
  have h2 := conjSubgroup_eq_iff_mem_normalizer.mpr hK
  exact conjSubgroup_eq_iff_mem_normalizer.mp
    (by rw [CFSG.QuasithinUnique.C5.conjSubgroup_inf, h1, h2])

theorem centralizer_V0_inf_G0_le_pCore (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) :
    G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) ≤
      pCoreOf 2 (G0_153 T Mc M E s) := by
  have hCT : G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) ≤ T := by
    intro x hx
    have hxV : x ∈ Subgroup.centralizer (VZ T M : Set G) :=
      Subgroup.centralizer_le (V_le_V0 (T := T) (Mc := Mc) (M := M) (E := E) (s := s)) hx.2
    have : x ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := r67.R_eq.symm ▸ hxV
    exact this.1
  have hCp : IsPGroup 2 ↥(G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) :=
    k.c.hyp.qtfe.sylow.1.to_le hCT
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hCp
  intro g hg
  exact mem_normalizer_inf67 (Subgroup.le_normalizer hg)
    (normalizer_le_normalizer_CE _ (V0_normal hg))

theorem VE67_le_V0 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) :
    VE67 T M E ≤ V0_153 T Mc M E s := by
  refine conjClosure_le fun g hg v hv => ?_
  have hG2 : G2_153 T E ≤ G0_153 T Mc M E s := le_sup_right
  have hXN : XE153 E ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ ((oTwoUpper_le _) hx)
  have hG2E : G2_153 T E ≤ Subgroup.normalizer (E : Set G) :=
    sup_le hXN (fun u hu => hu.2)
  have hG2N : G2_153 T E ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
    hG2E.trans r67.YE_normal
  have hYN : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) := fun y hy =>
    ((oTwoUpper_le _).trans inf_le_right) hy
  have hGE : Subgroup.normalizer (E : Set G) = G2_153 T E ⊔ YE153 Mc M E := by
    refine le_antisymm ?_ (sup_le hG2E hYN)
    rw [r67.GE_eq]
    exact sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  have hmem : g ∈ ((G2_153 T E ⊔ YE153 Mc M E : Subgroup G) : Set G) := hGE ▸ hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hG2N] at hmem
  obtain ⟨g₂, hg₂, y, hy, rfl⟩ := hmem
  have hyM : y ∈ M := ((oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))) hy
  have hyV : y * v * y⁻¹ ∈ V0_153 T Mc M E s :=
    V_le_V0 ((Subgroup.mem_normalizer_iff.mp (k.c.hyp.le_normalizer hyM) v).mp hv)
  have e : g₂ * y * v * (g₂ * y)⁻¹ = g₂ * (y * v * y⁻¹) * g₂⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (V0_normal (hG2 hg₂)) _).mp hyV

omit [Finite G] in
theorem oTwoUpper_le_oTwoUpper_of_le {X H : Subgroup G} (h : oTwoUpper X ≤ H) :
    oTwoUpper X ≤ oTwoUpper H :=
  (Subgroup.closure_le (oTwoUpper H)).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (h (mem_oTwoUpper_of_odd hx.1 hx.2)) hx.2

omit [Finite G] in
theorem XE_le_oTwoUpper_G0 : XE153 E ≤ oTwoUpper (G0_153 T Mc M E s) :=
  oTwoUpper_le_oTwoUpper_of_le ((le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right)

theorem YF_le_oTwoUpper_G0 : YF153 Mc M E s ≤ oTwoUpper (G0_153 T Mc M E s) := by
  have hY : YF153 Mc M E s =
      oTwoUpper (conjSubgroup (Y153 Mc M ⊓ Subgroup.normalizer (E : Set G)) s) :=
    (oTwoUpper_map (MulAut.conj s⁻¹).toMonoidHom _).symm
  have hle : YF153 Mc M E s ≤ G0_153 T Mc M E s :=
    (le_sup_left : YF153 Mc M E s ≤ G1_153 T Mc M E s).trans le_sup_left
  rw [hY] at hle ⊢
  exact oTwoUpper_le_oTwoUpper_of_le hle

theorem comm_V_YF (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    ⁅VZ T M, YF153 Mc M E s⁆ = VZ T M := by
  have hsM : s ∈ M := k.c.hyp.T_le (s_mem_T67 gl)
  have hV : conjSubgroup (VZ T M) s = VZ T M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (k.c.hyp.le_normalizer hsM)
  have h := CFSG.QuasithinUnique.C5.conjSubgroup_commutator (VZ T M) (YE153 Mc M E) s
  rw [k.r66.V_comm, hV] at h
  exact h.symm

theorem V_le_Q (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) :
    VZ T M ≤ ⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ := by
  calc VZ T M = ⁅VZ T M, YF153 Mc M E s⁆ := (comm_V_YF k gl).symm
    _ ≤ ⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ :=
      Subgroup.commutator_mono r68.V_le_pCore YF_le_oTwoUpper_G0

theorem V0_le_Q (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) :
    V0_153 T Mc M E s ≤ ⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ := by
  have hQN : G0_153 T Mc M E s ≤ Subgroup.normalizer
      ((⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ : Subgroup G) : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G) :=
      le_normalizer_pCoreOf 2 _ hg
    have h2 : g ∈ Subgroup.normalizer (oTwoUpper (G0_153 T Mc M E s) : Set G) :=
      le_normalizer_oTwoUpper _ hg
    refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
    rw [CFSG.QuasithinUnique.C5.conjSubgroup_commutator,
      conjSubgroup_eq_iff_mem_normalizer.mpr h1, conjSubgroup_eq_iff_mem_normalizer.mpr h2]
  refine conjClosure_le fun g hg v hv => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hQN hg) v).mp (V_le_Q k gl r68 hv)

theorem conjSubgroup_VE67_le_TE (k : Ctx67 G T Mc M V₁ V₂ E t) (gl : GoldLine153 T V₁ E s) :
    conjSubgroup (VE67 T M E) s ≤ TE153 T E := by
  have hsTE : s ∈ Subgroup.normalizer (TE153 T E : Set G) :=
    T_le_normalizer_TE k.r66 (s_mem_T67 gl)
  have h := CFSG.QuasithinUnique.C5.conjSubgroup_mono (VE67_le_TE k) s
  rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hsTE] at h

theorem conjSubgroup_VE67_le_pCore_G0 (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (hV0E : V0_153 T Mc M E s = VE67 T M E) :
    conjSubgroup (VE67 T M E) s ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
  intro a ha
  have haT : a ∈ TE153 T E := conjSubgroup_VE67_le_TE k gl ha
  have haG : a ∈ G0_153 T Mc M E s :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right haT)
  have hac : a ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [hV0E] at hv
    exact VE67_comm_conj_VE67 k gl v hv a ha
  exact centralizer_V0_inf_G0_le_pCore k r67 ⟨haG, hac⟩

end Loc

end S1567

theorem false_of_L32_of_loc {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hloc : Input15368PsiL3Loc)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (r50 : Res15350 T M) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2)))) : False := by
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, L, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  have hQ := hloc G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hL3
  have hVEV0 : VE67 T M E ≤ V0_153 T Mc M E s := S1567.VE67_le_V0 k r67
  have hV0Q := S1567.V0_le_Q k gl r68
  have h64 := S1567.sixtyFour_le_card_VE67 k r67
  have hV0c : Nat.card ↥(V0_153 T Mc M E s) ≤ 2 ^ 6 :=
    (Subgroup.card_le_of_le hV0Q).trans hQ
  have hV0E : V0_153 T Mc M E s = VE67 T M E :=
    (Subgroup.eq_of_le_of_card_ge hVEV0 (hV0c.trans h64)).symm
  have hQV0 : ⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ =
      V0_153 T Mc M E s :=
    (Subgroup.eq_of_le_of_card_ge hV0Q
      (hQ.trans (h64.trans (Subgroup.card_le_of_le hVEV0)))).symm
  have hQX : ⁅pCoreOf 2 (G0_153 T Mc M E s), XE153 E⁆ ≤ V0_153 T Mc M E s :=
    hQV0 ▸ Subgroup.commutator_mono le_rfl S1567.XE_le_oTwoUpper_G0
  refine S1567.false_of_VE_normalized h11 h113 k r67 gl ?_ ?_
  · intro y hy
    have h1 : y ∈ G0_153 T Mc M E s := Subgroup.mem_sup_left (Subgroup.mem_sup_left hy)
    have h2 := V0_normal h1
    rwa [hV0E] at h2
  · intro x hx a ha
    have haQ : a ∈ pCoreOf 2 (G0_153 T Mc M E s) :=
      S1567.conjSubgroup_VE67_le_pCore_G0 k r67 gl hV0E ha
    have h1 : ⁅x, a⁆ ∈ ⁅XE153 E, pCoreOf 2 (G0_153 T Mc M E s)⁆ :=
      Subgroup.commutator_mem_commutator hx haQ
    rw [Subgroup.commutator_comm] at h1
    have hcomm : ⁅x, a⁆ ∈ VE67 T M E := hV0E ▸ hQX h1
    rw [commutatorElement_def] at hcomm
    have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right ha)

theorem input15368PsiL3_of_loc (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hloc : Input15368PsiL3Loc) : Input15368PsiL3 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hL3
  exact (false_of_L32_of_loc h11 h113 hloc c r45 r46 r49 r50 L r66 r67 gl r68 hL3).elim

theorem stage1531InspectBCatNoTwo_of_inputs_loc (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h56 : AsB56) (hI1 : InspectListF618) (hNP : InspectRemainingNP)
    (hloc : Input15368PsiL3Loc) : Stage1531InspectBCatNoTwo :=
  stage1531InspectBCatNoTwo_of_inputs h113 h56 hI1 hNP (input15368PsiL3_of_loc h11 h113 hloc)

end CFSG.Quasithin
