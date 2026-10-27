module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdent
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentH
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueNeBstar
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueOne
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueZero

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

private def glueSixAux_labP (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I _ =>
  LargeEvenInLambda2 lab ∧
    (lab.n = 1 → frameTagTabled lab.tag →
      ∀ r : ℕ, 6 ≤ r → frameTBRange lab r → GGTorusReflGenW 3 r R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A →
            (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
                (frameLabNum lab).1 (frameLabNum lab).2 ∧
              FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
            ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S) ∧
    (lab.n = 1 → ¬ frameTagTabled lab.tag →
      ∀ r : ℕ, 6 ≤ r → ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
        (A : Subgroup (MulAut L')), ¬ GGTorusTBGroup 3 r R I L' ψ A) ∧
    (lab.n = 1 → lab.tag = .twA → GGTorusLift 3 (ggUnitaryTorusRank 3 (lab.rank + 1)) R) ∧
    (lab.n = 1 → lab.tag = .E8 → GGTorusLift 3 7 R)

private theorem glueSixAux_labP_all
    (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (glueSixAux_labP lab) :=
  largeEvenLabelAll_and (largeEvenLabelAll_const hΛ)
    (largeEvenLabelAll_and
      (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htab => hb1.1 lab hΛ hn1 htab)
      (largeEvenLabelAll_and
        (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htab => hb1' lab hΛ hn1 htab)
        (largeEvenLabelAll_and
          (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htag =>
            largeEvenLabelAll_torusLift_twA hΛ htag Nat.prime_three (by rw [hn1]; norm_num))
          (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htag =>
            hb1.2 lab hΛ hn1 htag))))

omit [Finite G] in
private theorem glueSixAux_card {Bs : Subgroup G} {n : ℕ} (M : GGFrameModelData Bs n) :
    Nat.card Bs = 3 ^ n := by
  calc Nat.card Bs = Nat.card (Additive ↥Bs) := (Nat.card_congr Additive.toMul).symm
    _ = Nat.card (Fin n → ZMod 3) := Nat.card_congr M.ψ.toEquiv
    _ = 3 ^ n := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem glueSixAux_marking_of_tag {X : Type} [Group X]
    {t : LargeEvenLieTag} {r m : ℕ}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = t ∧ lab.rank = r ∧ lab.n = m)) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => lab = ⟨t, r, m⟩) := by
  refine largeEvenMarking_mono ?_ h
  intro lab R _ I F θ hp
  obtain ⟨ht, hr, hm⟩ := hp
  obtain ⟨t', r', m'⟩ := lab
  dsimp only at ht hr hm
  rw [ht, hr, hm]

omit [Finite G] in
private theorem glueSixAux_innerDiagOnLabel_of_marking {Bs K : Subgroup G} {p : ℕ}
    (hRig : GGLabelRigidInput) (h : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hM : LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab)) :
    GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs K := by
  obtain ⟨-, lab', hlab', hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hEq⟩ := largeEvenRawDatum_exists hraw
  have hEq' : lab' = lab := hEq
  subst lab'
  have hhas : GGHasLabel lab (K ⧸ Subgroup.center K) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  exact ggInnerDiagOn_relabel hRig h hlab' hhas

theorem subgroupOf_centralizer_normal_E7
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  obtain ⟨hp, hBsE, hxBs, hLx, -⟩ := hR.1.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  obtain ⟨𝒦, h𝒦, hne, e, he⟩ := hJ
  have hBs : Nat.card Bs = 3 ^ 7 :=
    card_bstar_of_weylAtJoin (Fintype.card_fin 7) exists_elemAbelian_two_coxeterE7
      hTBF hWI hR hW h𝒦 hne ⟨e, he⟩
  have hA : Nat.card (ggGamma L hN).range * 3 = Nat.card Bs :=
    card_range_ggGamma_mul_of hp hBsE hxBs hx1 hLx hS.2.2.2.2 hN
  have hA' : Nat.card (ggGamma L hN).range = 3 ^ 6 := by
    rw [hBs] at hA
    norm_num at hA ⊢
    omega
  have hE1 := largeEvenMarking_torusTBGroup_of_qTwo hR hq hN 6 hA'.ge
    (by rw [hA']; norm_num)
  have hE2 : LargeEvenMarking L (fun lab R _ I F θ =>
      (GGLabQTwo 3 lab ∧
        GGTorusTBGroup 3 6 R I L (ggQuotHom θ) (ggGamma L hN).range) ∧
      glueSixAux_labP lab R I F) := by
    refine largeEvenMarking_mono_labelAll (P' := glueSixAux_labP)
      (fun lab hΛ => glueSixAux_labP_all hb1 hb1' hΛ) ?_ hE1
    intro lab R _ I F θ _ hP hP'
    exact ⟨hP, hP'⟩
  obtain ⟨_, lab, hlab, hraw⟩ := hE2
  obtain ⟨R, _, I, F, -, -, θ, hPP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hP, hP'⟩ := hPP
  obtain ⟨hq2, hTB⟩ := hP
  obtain ⟨hΛ, hb1c, hb1'c, htw, htw8⟩ := hP'
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hΛ.1
    have h2 : lab.n < 2 := hq2
    omega
  have hrange : frameTBRange lab 6 :=
    frameTBRange_of_torusLift hR (Or.inl rfl) hBs hq.1 θ (htw hn1) (htw8 hn1)
  by_cases htab : frameTagTabled lab.tag
  · obtain ⟨-, hNum⟩ := hb1c hn1 htab 6 (by norm_num) hrange
    obtain ⟨-, S, hS3, hSnc⟩ := hNum L (ggQuotHom θ) (ggGamma L hN).range hTB
    refine subgroupOf_centralizer_normal_of_noncyclic hR
      ⟨S.map L.subtype, Subgroup.map_subtype_le S, hS3.map L.subtype, ?_⟩
    intro hcyc
    exact hSnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).injective)
  · exact absurd hTB
      (hb1'c hn1 htab 6 (by norm_num) L (ggQuotHom θ) (ggGamma L hN).range)

theorem exists_component_of_isRoot
    (hPU : GGPumpupInput) (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hrig : GGLabelRigidInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    {n : ℕ} (𝔐 : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hA : Nat.card ↥𝔐.A = if n = 7 then 2903040 else 696729600)
    (hgen : ∀ φ : ↥𝔐.A, 𝔐.ρ φ ∈ Submonoid.closure (Set.range (feS n)))
    (hHx : n = 7 → ∃ x' ∈ Bs, x' ≠ 1 ∧
      Nat.card (ggAutomizer (Subgroup.centralizer ({x'} : Set G)) Bs) ≤ 103680)
    {z : G} {J₁ : Subgroup G} {lab : LargeEvenLabel} (hz : 𝔐.IsRoot z)
    (hP5 : P5Out B Bs x z L (Subgroup.closure {x, z}) J₁) (hlab : GGFrameJTag lab)
    (hmJ : LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = lab)) :
    z ∈ B ∧ ∃ K : Subgroup G,
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)) ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z ∧
      ((n = 7 ∧
          GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K) ∨
        (n = 8 ∧ GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs K)) := by
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hzB : z ∈ B :=
    (facts_of_closure_pair hP5.cfg.1 hP5.cfg.2.2 hP5.plane).1
  have hBs : IsElemAbelian 3 Bs := hR.1.tableB_facts.2.1
  have hirr := GGFrameModelData.irreducible_of_isRoot 𝔐 hn hBs hz
  have hcard : Nat.card Bs = 3 ^ n := glueSixAux_card 𝔐
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨lab', hΛ', hhas', R, _, I, F, θ, hEq⟩ :=
    largeEvenMarking_exists_hasLabel hmJ
  have hJlab : ∃ j, GGFrameJTag j ∧ GGHasLabel j (J₁ ⧸ Subgroup.center J₁) := by
    refine ⟨lab, hlab, ?_⟩
    simpa [hEq] using hhas'
  obtain ⟨K, hKcomp, -, -, hBsK, hNK, hker, hinner⟩ :=
    glueOne hPU hO hTCJ hrig hP5 hcard hn4 hirr hJlab
  have hBmax : LargeEvenIsBmax 3 B := hS.1
  have hBBs : B ≤ Bs := hR.1.2.1.1
  have hNT : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hR.1.2.1.2.2.2
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := hKcomp.1
  have hlab12 := glueTwo 𝔐 hn hA hgen hBmax hBBs hBs hcard hNT hBstar hz hKz
    hBsK hNK hker hinner hHx
  refine ⟨hzB, K, hKcomp, hBsK, hker, ?_⟩
  rcases hlab12 with ⟨hn7, hD⟩ | hE7
  · exact Or.inl ⟨hn7, hD⟩
  · have hn8 : n = 8 := by
      rcases hn with h7 | h8
      · exfalso
        have h8' := (P10c_E7_eight hBs hcard (by omega) hz.1 hz.2.1 hBsK hker hBstar hE7).1
        omega
      · exact h8
    exact Or.inr ⟨hn8, hE7⟩

theorem fsPoint_unitarySeven
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 6 ∧ lab.n = 1)) :
    Nat.card Bs = 3 * Nat.card B ∧
      ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
        (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
        LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
  obtain ⟨hBne, 𝔐, z, J₁, k, -, hcardA, hgen, hz, hP5, -, hmarkJ₁, hk⟩ :=
    glueZero_unitarySeven hTBF hWI hb1 hb1' hrig hR hW hq hJ hm
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hBs : IsElemAbelian 3 Bs := hR.1.tableB_facts.2.1
  have hxBs : x ∈ Bs := hR.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcard7 : Nat.card Bs = 3 ^ 7 := glueSixAux_card 𝔐
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hR.1.tableB_facts.2.2.2.1
  have hNL : Subgroup.normalizer (Bs : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
      subgroupOf_centralizer_normal_E7 hTBF hWI hb1 hb1' hR hW hq hJ
    exact inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hLn)
  have hker := hR.1.bstar_inf_centralizer_L
  have hmA := glueSixAux_marking_of_tag hm
  have hLone := glueSixAux_innerDiagOnLabel_of_marking (p := 3) hrig hR.2.2.1.1 hmA
  have hL : GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.twA, 6, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩) 3 Bs L := by
    refine largeEvenMarking_mono ?_ hLone
    intro lab R _ I F θ h
    exact ⟨Or.inl h.1, h.2⟩
  have hHx : 7 = 7 → ∃ x' ∈ Bs, x' ≠ 1 ∧
      Nat.card (ggAutomizer (Subgroup.centralizer ({x'} : Set G)) Bs) ≤ 103680 := by
    intro _
    exact ⟨x, hxBs, hx1, card_automizer_centralizer_le_of_end hBs hcard7 hxBs hx1 hN hNL
      hker hR.1.2.1.2.2.2 hR.2.2.2.1 hL⟩
  have hlab : GGFrameJTag ⟨.twA, k, 1⟩ := by
    rcases hk with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  obtain ⟨hzB, K, hKcomp, hBsK, hkerK, hlabK⟩ :=
    exists_component_of_isRoot hPU hO hTCJ hrig hR 𝔐 (Or.inl rfl) hcardA hgen hHx hz
      hP5 hlab hmarkJ₁
  rcases hlabK with ⟨-, hD⟩ | ⟨h8, -⟩
  · have hBmax : LargeEvenIsBmax 3 B := hS.1
    have hBBs : B ≤ Bs := hR.1.2.1.1
    obtain ⟨-, -, -, hSStar, hKn, hmarkK⟩ :=
      sStar_normal_D6 hBmax hBBs hBs hcard7 hzB hz.2.1 hKcomp hBsK hkerK
        hR.1.2.1.2.2.2 hD
    exact ⟨card_bstar_eq_of_ne hR hBne, z, hzB, K, hSStar, hKn, hmarkK⟩
  · exact absurd h8 (by norm_num)

theorem fsPoint_twE6
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
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
    Nat.card Bs = 3 * Nat.card B ∧
      ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
        (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
        LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
  obtain ⟨𝔐, z, J₁, lab, -, hcardA, hgen, hz, hP5out, -, hmarkJ, hdisj⟩ :=
    glueZero_twE6 hTBF hWI hb1 hb1' hrig hR hW hq hJ hm hP5
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hBs : IsElemAbelian 3 Bs := hR.1.tableB_facts.2.1
  have hxBs : x ∈ Bs := hR.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcard7 : Nat.card Bs = 3 ^ 7 := glueSixAux_card 𝔐
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hR.1.tableB_facts.2.2.2.1
  have hNL : Subgroup.normalizer (Bs : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
      subgroupOf_centralizer_normal_E7 hTBF hWI hb1 hb1' hR hW hq hJ
    exact inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hLn)
  have hker := hR.1.bstar_inf_centralizer_L
  have hmE := glueSixAux_marking_of_tag hm
  have hLone := glueSixAux_innerDiagOnLabel_of_marking (p := 3) hrig hR.2.2.1.1 hmE
  have hL : GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.twA, 6, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩) 3 Bs L := by
    refine largeEvenMarking_mono ?_ hLone
    intro lab R _ I F θ h
    exact ⟨Or.inr h.1, h.2⟩
  have hHx : 7 = 7 → ∃ x' ∈ Bs, x' ≠ 1 ∧
      Nat.card (ggAutomizer (Subgroup.centralizer ({x'} : Set G)) Bs) ≤ 103680 := by
    intro _
    exact ⟨x, hxBs, hx1, card_automizer_centralizer_le_of_end hBs hcard7 hxBs hx1 hN hNL
      hker hR.1.2.1.2.2.2 hR.2.2.2.1 hL⟩
  have hlab : GGFrameJTag lab := by
    rcases hdisj with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inl rfl)
  obtain ⟨hzB, K, hKcomp, hBsK, hkerK, hlabK⟩ :=
    exists_component_of_isRoot hPU hO hTCJ hrig hR 𝔐 (Or.inl rfl) hcardA hgen hHx hz
      hP5out hlab hmarkJ
  rcases hlabK with ⟨-, hD⟩ | ⟨h8, -⟩
  · have hBmax : LargeEvenIsBmax 3 B := hS.1
    have hBBs : B ≤ Bs := hR.1.2.1.1
    have hBne : B ≠ Bs := by
      refine ne_bstar_of_isRoot_twoGroup hR.1.1 𝔐 (Or.inl rfl) hBs hz ?_
      intro T hT2 hTz hBsT
      exact twoGroup_le_centralizer_of_D6 hBmax hBBs hBs hcard7 hzB hz.2.1 hKcomp hBsK
        hkerK hR.1.2.1.2.2.2 hD hT2 hTz hBsT
    obtain ⟨-, -, -, hSStar, hKn, hmarkK⟩ :=
      sStar_normal_D6 hBmax hBBs hBs hcard7 hzB hz.2.1 hKcomp hBsK hkerK
        hR.1.2.1.2.2.2 hD
    exact ⟨card_bstar_eq_of_ne hR hBne, z, hzB, K, hSStar, hKn, hmarkK⟩
  · exact absurd h8 (by norm_num)

theorem fsPoint_unitaryNine
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1)) :
    Nat.card Bs = 3 * Nat.card B ∧
      ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
        (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
        LargeEvenMarking K (fun lab _ _ _ _ _ =>
          ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) := by
  obtain ⟨𝔐, z, J₁, -, hcardA, hgen, hz, hP5out, -, hmarkJ⟩ :=
    glueZero_unitaryNine hTBF hWI hb1 hb1' hrig hR hW hq hJ hm
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hBs : IsElemAbelian 3 Bs := hR.1.tableB_facts.2.1
  have hcard8 : Nat.card Bs = 3 ^ 8 := glueSixAux_card 𝔐
  have hlab : GGFrameJTag ⟨.twA, 6, 1⟩ := Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨hzB, K, hKcomp, hBsK, hkerK, hlabK⟩ :=
    exists_component_of_isRoot hPU hO hTCJ hrig hR 𝔐 (Or.inr rfl) hcardA hgen
      (fun h => absurd h (by norm_num)) hz hP5out hlab hmarkJ
  rcases hlabK with ⟨h7, -⟩ | ⟨-, hE7⟩
  · exact absurd h7 (by norm_num)
  · have hBmax : LargeEvenIsBmax 3 B := hS.1
    have hBBs : B ≤ Bs := hR.1.2.1.1
    have hBne : B ≠ Bs := by
      refine ne_bstar_of_isRoot_twoGroup hR.1.1 𝔐 (Or.inr rfl) hBs hz ?_
      intro T hT2 hTz hBsT
      exact twoGroup_le_centralizer_of_E7 hBmax hBBs hBs hcard8 (by norm_num) hzB hz.2.1
        hKcomp hBsK hkerK hR.1.2.1.2.2.2 hE7 hT2 hTz hBsT
    obtain ⟨-, -, -, -, -, hSStar, hKn, hmarkK⟩ :=
      sStar_normal_E7 hBmax hBBs hBs hcard8 (by norm_num) hzB hz.2.1 hKcomp hBsK hkerK
        hR.1.2.1.2.2.2 hE7
    refine ⟨card_bstar_eq_of_ne hR hBne, z, hzB, K, hSStar, hKn, ?_⟩
    refine largeEvenMarking_mono ?_ hmarkK
    intro lab R _ I F θ h
    exact ⟨Or.inr ⟨h.1, h.2.1⟩, h.2.2⟩

end CFSG.StandardType.FrameRoute

end
