module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueFrame
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRootPlane
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRootTwE6
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueSwap
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueUnitary
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFrame

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem glueZeroAux_card_of_frame {Bs : Subgroup G} {n : ℕ}
    (M : GGFrameModelData Bs n) : Nat.card ↥Bs = 3 ^ n := by
  calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := (Nat.card_congr Additive.toMul).symm
    _ = Nat.card (FEVec n) := Nat.card_congr M.ψ.toEquiv
    _ = 3 ^ n := by simp [FEVec, ZMod.card]

private theorem glueZeroAux_notMem_zpowers_of_plane {B : Subgroup G} {x z : G}
    {L D J : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, z}) : z ∉ Subgroup.zpowers x := by
  intro hz
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hDeq : D = Subgroup.zpowers x := by
    rw [hD, closure_pair_eq_sup, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hz)]
  have hcard : Nat.card D = 3 ^ 2 := hDJ.1.2.2.1
  rw [hDeq, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at hcard
  norm_num at hcard

private theorem glueZeroAux_eq_of_iso_twA6 {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twA, 6, 1⟩) : lab = ⟨.twA, 6, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem glueZeroAux_eq_of_iso_twA8 {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twA, 8, 1⟩) : lab = ⟨.twA, 8, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem glueZero_unitarySeven
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 6 ∧ lab.n = 1)) :
    B ≠ Bs ∧ ∃ (𝔐 : GGFrameModelData Bs 7) (z : G) (J₁ : Subgroup G) (k : ℕ),
      ggAutomizer L Bs ≤ 𝔐.A ∧ Nat.card ↥𝔐.A = 2903040 ∧
      (∀ φ : ↥𝔐.A, 𝔐.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) ∧
      𝔐.IsRoot z ∧ P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, k, 1⟩) ∧ (k = 4 ∨ k = 5) := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hThm : GGThmIHyp 3 B x L := hcfg.1
  have hBsstar : GGBstar 3 B Bs := hcfg.2.1
  have hBsE : IsElemAbelian 3 Bs := hBsstar.2.1
  have hBsB : B ≤ Bs := hBsstar.1
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBsB hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hR.1.tableB_facts.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  have hBne : B ≠ Bs := ne_bstar_of_unitarySeven hR hJ hm
  have hmark : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h =>
      ⟨Or.inl ⟨h.1, h.2.1⟩, h.2.2⟩) hm
  obtain ⟨_, 𝔐, hrest⟩ :=
    exists_frameModelData_E7 hTBF hWI hb1 hb1' hrig hR hW hq hJ hmark
  obtain ⟨hle, hcardA, hgen, hrefl, hv⟩ := hrest
  have hcardBs : Nat.card Bs = 3 ^ 7 := glueZeroAux_card_of_frame 𝔐
  have hM6 : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = ⟨.twA, 6, 1⟩) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
      obtain ⟨t, r, n⟩ := lab
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl) hm
  have hId : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hq
  have hIdLab : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 6, 1⟩) 3 Bs L :=
    CFSG.StandardType.E6QTwo.innerDiagOnLabel_of_marking hrig
      (fun lab lab' hiso h' => glueZeroAux_eq_of_iso_twA6 (h' ▸ hiso)) hId hM6
  obtain ⟨kL, F, hfield, hfin, θ, hSlab, hF, hk3, hTB, -⟩ :=
    P9_Wa_tbGroup_twA (S := fun _ lab => lab = ⟨.twA, 6, 1⟩) hBsE hcardBs (Or.inl rfl)
      hxBs hx1 hN hker hBsstar.2.2.2 (fun lab h => h ▸ ⟨rfl, rfl⟩) hIdLab
  have hkL : kL = 6 := by
    injection hSlab with _ h _
  subst hkL
  obtain ⟨hψ, hkerTB, hperf, hA, hAI, hrA, -, hSC⟩ := hTB
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    P9_U3a_exists_diagModel_of_card (m := 6 + 1) (r := 6) hF (by norm_num) (by norm_num)
      (by norm_num) hψ hkerTB hperf hA hAI hrA
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hζ : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  obtain ⟨u, z, J₁, k, hw, hmul, hconst, hsurj7, -, hzB, hshape, hP5, hlay, hmarkJ, -⟩ :=
    CFSG.StandardType.FrameRoute.UnitaryModel.exists_p5Out_of_unitaryModel
      (m := 6 + 1) (n := 7) hThm hBsstar hN hker hF
      (Or.inl ⟨rfl, rfl, hBne⟩) hcardBs hφs hφker hdiag hSC hζ
  have hzBs : z ∈ Bs := hBsB hzB
  have hzx : z ∉ Subgroup.zpowers x :=
    glueZeroAux_notMem_zpowers_of_plane hThm hP5.cfg.2.2 hP5.plane
  have hswap : ∀ a c : Fin 7, a ≠ c → ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      g ^ 2 = 1 ∧ ∀ b ∈ Bs, ∃ k : ZMod 3, ∀ i, u (g * b * g⁻¹) i =
        u b (Equiv.swap a c i) + k :=
    fun a c hac => exists_swap_of_unitaryModel hBsstar hxBs hLx hker hF (by norm_num)
      hφs hφker hζ hw (Or.inl (by norm_num)) hac
  have hroot : ∃ k₀ : ℕ, 𝔐.IsRoot (z * x ^ k₀) := by
    rcases hshape with ⟨-, hk5, j, c, hzc⟩ | ⟨hsecond, j, j', hjj', c, hzc⟩
    · exact GGFrameModelData.exists_isRoot_mul_pow_of_thirteen 𝔐 hle hrefl hLx hxBs hzBs
        hzx hv (thirteen_le_of_single hBsE hxBs hzBs hLx hmul hconst (hsurj7 rfl)
          ⟨c, hzc⟩ hswap)
    · have hk4 : k = 4 := by
        rcases hsecond with ⟨-, h⟩ | ⟨hm9, -⟩
        · exact h
        · omega
      obtain ⟨φ₀, hφ₀, hφ₀z⟩ :=
        exists_inv_of_single_sub_single hBsE hxBs hzBs hLx hmul hconst hjj'
          ⟨c, hzc⟩ (hswap j j' hjj')
      exact GGFrameModelData.exists_isRoot_mul_pow_of_inv 𝔐 hle hrefl hLx hxBs hzBs hzx
        hφ₀ hφ₀z
  obtain ⟨k₀, hroot⟩ := hroot
  have hk45 : k = 4 ∨ k = 5 := by
    rcases hshape with ⟨-, hk5, -⟩ | ⟨hsecond, -⟩
    · exact Or.inr hk5
    · rcases hsecond with ⟨-, hk4⟩ | ⟨hm9, -⟩
      · exact Or.inl hk4
      · omega
  have hP5' : P5Out B Bs x z L (Subgroup.closure {x, z * x ^ k₀}) J₁ := by
    rw [closure_pair_mul_pow x z k₀]
    exact hP5
  refine ⟨hBne, 𝔐, z * x ^ k₀, J₁, k, hle, hcardA, hgen, hroot,
    P5Out.of_closure_eq hP5' (closure_pair_mul_pow x z k₀), ?_, ?_, hk45⟩
  · rw [closure_pair_mul_pow x z k₀]
    exact hlay
  · exact hmarkJ

theorem glueZero_unitaryNine
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1)) :
    ∃ (𝔐 : GGFrameModelData Bs 8) (z : G) (J₁ : Subgroup G),
      ggAutomizer L Bs ≤ 𝔐.A ∧ Nat.card ↥𝔐.A = 696729600 ∧
      (∀ φ : ↥𝔐.A, 𝔐.ρ φ ∈ Submonoid.closure (Set.range (feS 8))) ∧
      𝔐.IsRoot z ∧ P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, 6, 1⟩) := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hThm : GGThmIHyp 3 B x L := hcfg.1
  have hBsstar : GGBstar 3 B Bs := hcfg.2.1
  have hBsE : IsElemAbelian 3 Bs := hBsstar.2.1
  have hBsB : B ≤ Bs := hBsstar.1
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBsB hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hR.1.tableB_facts.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  obtain ⟨_, 𝔐, hrest⟩ := exists_frameModelData_E8 hTBF hWI hb1 hb1' hR hW hq hJ
  obtain ⟨hle, hcardA, hgen, hrefl⟩ := hrest
  have hcardBs : Nat.card Bs = 3 ^ 8 := glueZeroAux_card_of_frame 𝔐
  have hM8 : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = ⟨.twA, 8, 1⟩) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
      obtain ⟨t, r, n⟩ := lab
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl) hm
  have hId : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hq
  have hIdLab : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 8, 1⟩) 3 Bs L :=
    CFSG.StandardType.E6QTwo.innerDiagOnLabel_of_marking hrig
      (fun lab lab' hiso h' => glueZeroAux_eq_of_iso_twA8 (h' ▸ hiso)) hId hM8
  obtain ⟨kL, F, hfield, hfin, θ, hSlab, hF, hk3, hTB, -⟩ :=
    P9_Wa_tbGroup_twA (S := fun _ lab => lab = ⟨.twA, 8, 1⟩) hBsE hcardBs (Or.inr rfl)
      hxBs hx1 hN hker hBsstar.2.2.2 (fun lab h => h ▸ ⟨rfl, rfl⟩) hIdLab
  have hkL : kL = 8 := by
    injection hSlab with _ h _
  subst hkL
  obtain ⟨hψ, hkerTB, hperf, hA, hAI, hrA, -, hSC⟩ := hTB
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    P9_U3a_exists_diagModel_of_card (m := 8 + 1) (r := 7) hF (by norm_num) (by norm_num)
      (by norm_num) hψ hkerTB hperf hA hAI hrA
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hζ : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  obtain ⟨u, z, J₁, k, hw, hmul, hconst, -, h9, hzB, hshape, hP5, hlay, hmarkJ, -⟩ :=
    CFSG.StandardType.FrameRoute.UnitaryModel.exists_p5Out_of_unitaryModel
      (m := 8 + 1) (n := 8) hThm hBsstar hN hker hF (Or.inr ⟨rfl, rfl⟩) hcardBs
      hφs hφker hdiag hSC hζ
  obtain ⟨hsum, hsurj9⟩ := h9 rfl
  have hzBs : z ∈ Bs := hBsB hzB
  have hzx : z ∉ Subgroup.zpowers x :=
    glueZeroAux_notMem_zpowers_of_plane hThm hP5.cfg.2.2 hP5.plane
  rcases hshape with ⟨hm7, -, -⟩ | ⟨hsecond, j, j', hjj', c, hzc⟩
  · omega
  have hk6 : k = 6 := by
    rcases hsecond with ⟨h7, -⟩ | ⟨-, h6⟩
    · omega
    · exact h6
  obtain ⟨φ₀, hφ₀, hφ₀z⟩ :=
    exists_inv_of_single_sub_single hBsE hxBs hzBs hLx hmul hconst hjj' ⟨c, hzc⟩
      (exists_swap_of_unitaryModel hBsstar hxBs hLx hker hF (by norm_num) hφs hφker hζ hw
        (Or.inr hsum) hjj')
  obtain ⟨k₀, hroot⟩ :=
    GGFrameModelData.exists_isRoot_mul_pow_of_inv 𝔐 hle hrefl hLx hxBs hzBs hzx hφ₀ hφ₀z
  have hP5' : P5Out B Bs x z L (Subgroup.closure {x, z * x ^ k₀}) J₁ := by
    rw [closure_pair_mul_pow x z k₀]
    exact hP5
  refine ⟨𝔐, z * x ^ k₀, J₁, hle, hcardA, hgen, hroot,
    P5Out.of_closure_eq hP5' (closure_pair_mul_pow x z k₀), ?_, ?_⟩
  · rw [closure_pair_mul_pow x z k₀]
    exact hlay
  · simpa [hk6] using hmarkJ

theorem glueZero_twE6
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twE6 ∧ lab.rank = 0 ∧ lab.n = 1))
    (hP5 : ∃ (z : G) (J₁ : Subgroup G) (lab : LargeEvenLabel) (u : G → NTPlane.X3),
      P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = lab) ∧
      ((B = Bs ∧ lab = ⟨.twD, 5, 1⟩) ∨ (B ≠ Bs ∧ lab = ⟨.twA, 5, 1⟩)) ∧
      z ∈ Bs ∧ (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
      (∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) ∧ (∀ v, ∃ b ∈ Bs, u b = v) ∧
      ((NTPlane.kerRoots (u z)).ncard = 30 ∨ (NTPlane.kerRoots (u z)).ncard = 40) ∧
      ∀ w : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6, ∃ m ∈ L,
        m ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b) :
    ∃ (𝔐 : GGFrameModelData Bs 7) (z : G) (J₁ : Subgroup G) (lab : LargeEvenLabel),
      ggAutomizer L Bs ≤ 𝔐.A ∧ Nat.card ↥𝔐.A = 2903040 ∧
      (∀ φ : ↥𝔐.A, 𝔐.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) ∧
      𝔐.IsRoot z ∧ P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = lab) ∧
      ((B = Bs ∧ lab = ⟨.twD, 5, 1⟩) ∨ (B ≠ Bs ∧ lab = ⟨.twA, 5, 1⟩)) := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hThm : GGThmIHyp 3 B x L := hcfg.1
  have hBsstar : GGBstar 3 B Bs := hcfg.2.1
  have hBsE : IsElemAbelian 3 Bs := hBsstar.2.1
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBsstar.1 hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hR.1.tableB_facts.2.2.2.1
  have hmark : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h =>
      ⟨Or.inr ⟨h.1, h.2.1⟩, h.2.2⟩) hm
  obtain ⟨_, 𝔐, hrest⟩ :=
    exists_frameModelData_E7 hTBF hWI hb1 hb1' hrig hR hW hq hJ hmark
  obtain ⟨hle, hcardA, hgen, hrefl, hv⟩ := hrest
  obtain ⟨z, J₁, lab, u, hP5out, hlay, hmarkJ, hdisj, hzBs, hadd, hu0, hsurj, hker, hW⟩ := hP5
  have hzx : z ∉ Subgroup.zpowers x :=
    glueZeroAux_notMem_zpowers_of_plane hThm hP5out.cfg.2.2 hP5out.plane
  have h13 : 13 ≤ ({φ | φ ∈ frameReflSet (ggAutomizer L Bs) ∧ φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩} :
      Set (MulAut ↥Bs)).ncard :=
    thirteen_le_of_kerRoots hBsE hxBs hzBs hLx hadd hu0 hsurj hker hW
  obtain ⟨k₀, hroot⟩ :=
    GGFrameModelData.exists_isRoot_mul_pow_of_thirteen 𝔐 hle hrefl hLx hxBs hzBs hzx hv h13
  have hP5' : P5Out B Bs x z L (Subgroup.closure {x, z * x ^ k₀}) J₁ := by
    rw [closure_pair_mul_pow x z k₀]
    exact hP5out
  refine ⟨𝔐, z * x ^ k₀, J₁, lab, hle, hcardA, hgen, hroot,
    P5Out.of_closure_eq hP5' (closure_pair_mul_pow x z k₀), ?_, hmarkJ, hdisj⟩
  rw [closure_pair_mul_pow x z k₀]
  exact hlay

end CFSG.StandardType.FrameRoute

end
