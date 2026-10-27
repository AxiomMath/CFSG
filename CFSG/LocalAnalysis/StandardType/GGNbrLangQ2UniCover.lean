module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1JInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CoverData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGBstarAbelianPreimageJUniS1On (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d m : ℕ),
        (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5) → p ∣ 2 ^ m + 1 → ¬ (d = 3 ∧ m = 1) →
        ∀ (E : Type) [Field E] (hE : UnitaryFieldData 2 m E)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))),
          GGInnerDiagOnLab S p Bs L →
          IsMulCommutative
            ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
              (CFSG.HardMathSupport.C14Cl.uniConj hE d))

theorem GGBstarAbelianPreimageJUniS1On.mono {S T : ℕ → LargeEvenLabel → Prop}
    (hST : ∀ p lab, S p lab → T p lab) (h : GGBstarAbelianPreimageJUniS1On T) :
    GGBstarAbelianPreimageJUniS1On S := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ (GGInnerDiagOnLab.mono hST hlab)

theorem GGBstarAbelianPreimageJUniS1On.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGBstarAbelianPreimageJUniS1On S) (hT : GGBstarAbelianPreimageJUniS1On T) :
    GGBstarAbelianPreimageJUniS1On (fun p lab => S p lab ∨ T p lab) := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  rcases GGInnerDiagOnLab.elim_or hlab with h | h
  · exact hS G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ h
  · exact hT G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ h

@[expose] def Q2URLevelOn
    (Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop)
    (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p d m : ℕ) (lab : LargeEvenLabel), LargeEvenInLambda2 lab → S p lab → LargeEvenSplit p lab →
    ((p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5)) → p ∣ 2 ^ m + 1 → ¬ (d = 3 ∧ m = 1) →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) → Toral R A →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (E : Type) [Field E] (_ : UnitaryFieldData 2 m E),
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) →
          ∀ M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)),
            (∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J, (j' : R) = a j →
              α (QuotientGroup.mk j) = QuotientGroup.mk j') →
            Q2UnitaryLift M)

@[expose] def Q2URLevel (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  Q2URLevelOn (fun _ _ _ => True) S

@[expose] def Q2UConfigToral
    (Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop)
    (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
      S p lab → LargeEvenSplit p lab → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
        (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
        Toral R ((ggGamma L hN).range.map (ggInducedAut θ)))

theorem q2UConfigToral_true (S : ℕ → LargeEvenLabel → Prop) :
    Q2UConfigToral (fun _ _ _ => True) S := by
  intro G _ _ p B Bs x L D J hcfg P hP
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ _ _ => trivial⟩) hP

private theorem cuq2c_ggInducedAut_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ)
    (b : ↥Bs) : ggInducedAut θ (ggGamma L hN b) ∈ I := by
  obtain ⟨φ, hφI, hφ⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
  have hφ' : LargeEvenInduces θ (fun l l' : ↥L => l' = ggGamma L hN b l) φ := by
    intro l l' hl
    have h2 : (l' : G) = (((b : G)⁻¹))⁻¹ * (l : G) * ((b : G)⁻¹) := by
      rw [hl, ggGamma_coe]
      group
    exact hφ l l' h2
  have hEq : ggInducedAut θ (ggGamma L hN b) = φ := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact (hφ' l (ggGamma L hN b l) rfl).symm
  rw [hEq]
  exact hφI

private theorem cuq2c_isElemAbelian_range {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hE : IsElemAbelian p Bs) {L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hN).range := by
  haveI : IsMulCommutative ↥Bs := hE.1
  exact isElemAbelian_range
    (fun a b : ↥Bs => mul_comm' a b)
    (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2))
    (ggGamma L hN)

private theorem cuq2c_range_map_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ), a ∈ I := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
  rw [← hb]
  exact cuq2c_ggInducedAut_mem hN θ hact b

private theorem cuq2c_ggBsAut_apply_coe {G : Type} [Group G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (b : ↥Bs) (j : ↥J) :
    (((ggBsAut hN b) j : ↥J) : G) = (b : G) * (j : G) * (b : G)⁻¹ :=
  rfl

theorem ggBstarAbelianPreimageJUniS1On_of_rLevelToral
    {Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop}
    {S : ℕ → LargeEvenLabel → Prop} (hTor : Q2UConfigToral Toral S)
    (h : Q2URLevelOn Toral S) : GGBstarAbelianPreimageJUniS1On S := by
  intro G _ _ p B Bs x L D J hcfg _ hN d m hshape hpm hdm E _ hE θ hlab
  unfold Q2URLevelOn at h
  let Plab : LargeEvenMarkProp ↥L := fun lab _ _ I _ θ =>
    S p lab ∧ LargeEvenSplit p lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ
  have hlab' : LargeEvenMarking ↥L Plab := hlab
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hTor G p B Bs x L D J hcfg Plab hlab'
  obtain ⟨R, instR, I, F, hsimple, hnab, θL, hPlab, _⟩ := largeEvenRawDatum_exists hraw
  dsimp only [Plab] at hPlab
  obtain ⟨hS, hsplit, _, _⟩ := hPlab
  have hraw2 := (h p d m lab hΛ hS hsplit hshape hpm hdm) _ hraw
  obtain ⟨R', instR', I', F', hQ', hPred⟩ := largeEvenRawDatum_exists hraw2
  obtain ⟨hsimple', hnab', θL', hPlab', hQtor'⟩ := hQ'
  obtain ⟨hS', hsplit', hNL', hact'⟩ := hPlab'
  have htor' : Toral R' ((ggGamma L hNL').range.map (ggInducedAut θL')) :=
    hQtor' hS' hsplit' hNL' hact'
  obtain ⟨y, u, hyD, hyu, huord, hcomm, hJL, hJcomp⟩ := q1_fixed_component_data hcfg hNL'
  let π : ↥L →* R' := q2CoverMap θL'
  obtain ⟨hJ₀comp, ι, ι_mk⟩ := q2_cover_data hperf θL' u (J.subgroupOf L) hJcomp
  let J₀ : Subgroup R' := (J.subgroupOf L).map π
  let β : MulAut R' := ggInducedAut θL' u
  let A' : Subgroup (MulAut R') := (ggGamma L hNL').range.map (ggInducedAut θL')
  let φ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (centerQuotCongr φ).symm.trans ι
  let θ' : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)) :=
    e.symm.trans θ
  let M₀ : Subgroup (MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) :=
    ((ggBsAut hN).range.map (centerQuotAut ↥J)).map (MulAut.congr e).toMonoidHom
  have hcomm_all : ∀ (a : MulAut ↥L) (x : ↥L),
      π (a x) = ggInducedAut θL' a (π x) := by
    intro a x
    simpa [π, q2CoverMap] using (ggInducedAut_apply θL' a x).symm
  have hAb : IsElemAbelian p A' :=
    (cuq2c_isElemAbelian_range hcfg.2.1.2.1 hNL').map (ggInducedAut θL')
  have hAI : ∀ a ∈ A', a ∈ I' := cuq2c_range_map_mem hNL' θL' hact'
  have hu_range : u ∈ (ggGamma L hNL').range := ⟨y, hyu⟩
  have hβmem : β ∈ A' := Subgroup.mem_map.mpr ⟨u, hu_range, rfl⟩
  have hβord : orderOf β = p := by
    have hinj : Function.Injective (ggInducedAut θL') :=
      ggInducedAut_injective_of_perfect hperf θL'
    have h1 : orderOf (ggInducedAut θL' u) = orderOf u :=
      orderOf_injective (ggInducedAut θL') hinj u
    change orderOf (ggInducedAut θL' u) = p
    rw [h1, huord]
  have hAJ : ∀ a ∈ A', ∀ j ∈ J₀, a j ∈ J₀ := by
    intro a ha j hj
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
    rw [← hb]
    obtain ⟨j', hj', hjj'⟩ := Subgroup.mem_map.mp hj
    rw [← hjj']
    rw [← hcomm_all]
    refine Subgroup.mem_map.mpr ⟨ggGamma L hNL' b j', ?_, rfl⟩
    show ((ggGamma L hNL' b j' : ↥L) : G) ∈ J
    rw [ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hN b.2) (j' : G)).mp
      (Subgroup.mem_subgroupOf.mp hj')
  have hP0 : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) := ⟨θ'⟩
  have hMind : ∀ α ∈ M₀, ∃ a ∈ A', ∀ j j' : ↥J₀,
      (j' : R') = a j → α (QuotientGroup.mk j) = QuotientGroup.mk j' := by
    intro α hα
    obtain ⟨c, hc, hcα⟩ := Subgroup.mem_map.mp hα
    obtain ⟨d0, hd0, hd0c⟩ := Subgroup.mem_map.mp hc
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hd0
    rw [← hb] at hd0c
    refine ⟨ggInducedAut θL' (ggGamma L hNL' b),
      Subgroup.mem_map.mpr ⟨ggGamma L hNL' b, ⟨b, rfl⟩, rfl⟩, ?_⟩
    intro j j' hjj'
    obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp j.2
    let xJ : ↥(J.subgroupOf L) := ⟨x, hx⟩
    have hxJmem : ggGamma L hNL' b x ∈ J.subgroupOf L := by
      show ((ggGamma L hNL' b x : ↥L) : G) ∈ J
      rw [ggGamma_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hN b.2) (x : G)).mp
        (Subgroup.mem_subgroupOf.mp hx)
    have hιx : ι (QuotientGroup.mk xJ) = QuotientGroup.mk j := by
      rw [ι_mk]
      congr 1
      exact Subtype.ext hxj
    have hes : e.symm (QuotientGroup.mk j) = QuotientGroup.mk (φ xJ) := by
      dsimp only [e]
      rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, ← hιx,
        MulEquiv.symm_apply_apply, centerQuotCongr_mk]
    have he_mk : ∀ y : ↥J, e (QuotientGroup.mk y) = QuotientGroup.mk
        ⟨π (φ.symm y), Subgroup.mem_map_of_mem _ (φ.symm y).2⟩ := by
      intro y
      dsimp only [e]
      rw [MulEquiv.trans_apply, ← centerQuotCongr_symm, centerQuotCongr_mk, ι_mk]
    have hxx : φ ⟨ggGamma L hNL' b x, hxJmem⟩ = (ggBsAut hN b) (φ xJ) := by
      dsimp only [φ]
      apply Subtype.ext
      rw [Subgroup.subgroupOfEquivOfLe_apply_coe, cuq2c_ggBsAut_apply_coe,
        Subgroup.subgroupOfEquivOfLe_apply_coe]
      simp only [ggGamma_coe, Subgroup.coe_subgroupOf]
      rfl
    have hxx' : (⟨ggGamma L hNL' b x, hxJmem⟩ : ↥(J.subgroupOf L)) =
        φ.symm ((ggBsAut hN b) (φ xJ)) := by
      rw [← hxx, MulEquiv.symm_apply_apply]
    rw [← hcα, ← hd0c]
    change MulAut.congr e (centerQuotAut ↥J (ggBsAut hN b)) (QuotientGroup.mk j) =
      QuotientGroup.mk j'
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    rw [hes, centerQuotAut_mk, he_mk]
    congr 1
    apply Subtype.ext
    rw [← hxx']
    show π (ggGamma L hNL' b x) = (j' : R')
    rw [hcomm_all]
    rw [← hxj] at hjj'
    exact hjj'.symm
  have hLift : Q2UnitaryLift M₀ :=
    hPred A' hAb hAI htor' β hβmem hβord J₀ hJ₀comp hAJ E hE hP0 M₀ hMind
  have h3d : 3 ≤ d := by
    rcases hshape with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  have hcomm' := q2_commutative_of_unitaryLift hLift hE h3d hdm θ'
  have hcomp : (MulAut.congr θ').toMonoidHom.comp (MulAut.congr e).toMonoidHom
      = (MulAut.congr θ).toMonoidHom := by
    have heθ' : e.trans θ' = θ := by
      dsimp only [θ']
      ext x
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have h1 : (MulAut.congr e).trans (MulAut.congr θ') = MulAut.congr θ := by
      have h2 : (MulAut.congr e).trans (MulAut.congr θ') = MulAut.congr (e.trans θ') := by
        ext α
        rfl
      rw [h2, heθ']
    calc (MulAut.congr θ').toMonoidHom.comp (MulAut.congr e).toMonoidHom
        = ((MulAut.congr e).trans (MulAut.congr θ')).toMonoidHom := rfl
      _ = (MulAut.congr θ).toMonoidHom := by rw [h1]
  have hMeq : M₀.map (MulAut.congr θ').toMonoidHom
      = (ggBsAut hN).range.map (kgInducedAut θ) := by
    dsimp only [M₀]
    simp only [Subgroup.map_map]
    rw [← MonoidHom.comp_assoc, hcomp]
    rfl
  rw [hMeq] at hcomm'
  exact hcomm'

theorem ggBstarAbelianPreimageJUniS1On_of_rLevel {S : ℕ → LargeEvenLabel → Prop}
    (h : Q2URLevel S) : GGBstarAbelianPreimageJUniS1On S :=
  ggBstarAbelianPreimageJUniS1On_of_rLevelToral (Toral := fun _ _ _ => True)
    (q2UConfigToral_true S) h

end CFSG.StandardType
