module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenLinear
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCoord
public import CFSG.LocalAnalysis.StandardType.GGResCentBound

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTen_extract_of_coord (hLNC : GGLNoncyclicInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcoord : GGTenCoord Bs L K) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : Finite V)
      (ι : Additive ↥Bs ≃+ V), Module.finrank (ZMod 3) V = 10 ∧
        GGTenLinear ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)) := by
  classical
  subst hp3
  obtain ⟨V, iA, iM, iF, ι, ΛL, iFL, iDL, ML, CL, φL, hL, aL, φK, hK, aK, hdim, hcardL, hWM,
    hCL, hlinL, hreflL, hpairL, ⟨fL₀, hfL₀⟩, hclosL, hlinK, hreflK, hpairK, hclosK,
    ⟨a₀, ha₀, b₀, hb₀, hnonab⟩⟩ := hcoord
  letI := iA
  letI := iM
  letI := iF
  letI := iFL
  letI := iDL
  refine ⟨V, iA, iM, iF, ι, hdim, ?_⟩
  let rL : ΛL → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φL i)
  let rK : Fin 8 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φK i)
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let x' : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  have hmap_of_closure : ∀ {Λ : Type} (φ : Λ → MulAut ↥Bs),
      (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι)
        = Subgroup.closure (Set.range fun i => ggLin (p := 3) ι (φ i)) := by
    intro Λ φ
    rw [MonoidHom.map_closure]
    congr 1
    exact (Set.range_comp (ggLin (p := 3) ι) φ).symm
  have hmapL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range rL) := by
    rw [hclosL]
    exact hmap_of_closure φL
  have hmapK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range rK) := by
    rw [hclosK]
    exact hmap_of_closure φK
  let A : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)
  have hA' : A = Subgroup.closure (Set.range rL) ⊔ Subgroup.closure (Set.range rK) := by
    dsimp only [A]
    rw [Subgroup.map_sup, hmapL, hmapK]
  let eL : ↥(ggAutomizer L Bs) ≃* ↥(Subgroup.closure (Set.range rL)) :=
    (Subgroup.equivMapOfInjective (ggAutomizer L Bs) (ggLin (p := 3) ι)
      (ggLin_injective ι)).trans (MulEquiv.subgroupCongr hmapL)
  have hfL : ∀ i, ((fL₀.trans eL) (ML.simple i) : V ≃ₗ[ZMod 3] V) = rL i := by
    intro i
    rw [MulEquiv.trans_apply]
    change (((Subgroup.equivMapOfInjective (ggAutomizer L Bs) (ggLin (p := 3) ι)
      (ggLin_injective ι)).trans (MulEquiv.subgroupCongr hmapL)) (fL₀ (ML.simple i)) :
        V ≃ₗ[ZMod 3] V) = rL i
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply, hfL₀ i]
  have hrL : ∀ (i : ΛL) (v : V), rL i v = v - aL i v • hL i := fun i v => hlinL i v
  have hrK : ∀ (i : Fin 8) (v : V), rK i v = v - aK i v • hK i := fun i v => hlinK i v
  have hxne1 : (⟨x, hx⟩ : ↥Bs) ≠ 1 := by
    obtain ⟨t, -, -, htmove⟩ := ggIndep_moving_K hFixK hH hx
    intro h1
    exact htmove (by rw [h1, map_one])
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hxne1
    apply Additive.ofMul.injective
    apply ι.injective
    simpa [x'] using h0
  have hker : ∀ v : V, (∀ i : ΛL, aL i v = 0) →
      v ∈ Submodule.span (ZMod 3) ({x'} : Set V) :=
    ggIndep_fixL hFix hH hx hlinL hclosL
  have ht : ∃ t ∈ Subgroup.closure (Set.range rK), GGLinRefl t ∧ t x' ≠ x' := by
    obtain ⟨t, htK, htrefl, htmove⟩ := ggIndep_moving_K hFixK hH hx
    refine ⟨ggLin (p := 3) ι t, ?_, (ggRC_isReflection_iff_linRefl ι t).mp htrefl, ?_⟩
    · rw [← hmapK]
      exact Subgroup.mem_map.mpr ⟨t, htK, rfl⟩
    · intro hfix
      exact htmove ((ggLin_fix_iff ι t ⟨x, hx⟩).mpr (by simpa [x'] using hfix))
  have hnonabR : ∃ a ∈ Subgroup.closure (Set.range rL) ⊓ Subgroup.closure (Set.range rK),
      ∃ b ∈ Subgroup.closure (Set.range rL) ⊓ Subgroup.closure (Set.range rK), a * b ≠ b * a := by
    refine ⟨ggLin (p := 3) ι a₀, ⟨?_, ?_⟩, ggLin (p := 3) ι b₀, ⟨?_, ?_⟩, ?_⟩
    · rw [← hmapL]; exact Subgroup.mem_map.mpr ⟨a₀, ha₀.1, rfl⟩
    · rw [← hmapK]; exact Subgroup.mem_map.mpr ⟨a₀, ha₀.2, rfl⟩
    · rw [← hmapL]; exact Subgroup.mem_map.mpr ⟨b₀, hb₀.1, rfl⟩
    · rw [← hmapK]; exact Subgroup.mem_map.mpr ⟨b₀, hb₀.2, rfl⟩
    · intro h
      exact hnonab (ggLin_injective ι (by simpa only [map_mul] using h))
  have hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧
      ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    change g ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) at hg
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψtop : ψ ∈ ggAutomizer ⊤ Bs :=
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) hψA
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      rw [ggAutomizer_eq] at hψtop
      exact hψtop
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hLdat : GGResXDatum 3 Bs L :=
    ⟨ΛL, iFL, iDL, ML, CL, V, iA, iM, ι, φL, hL, aL, hWM, hCL, hlinL, hreflL, hpairL,
      ⟨fL₀, hfL₀⟩, hclosL⟩
  have hstabAA : Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      (3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) :=
    ggResCentBound_of_xDatum hLNC hFix hH hx hLdat
  have hcardL_A : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥(Subgroup.closure (Set.range rL)) := by
    rw [← hmapL]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (ggLin_injective ι)).toEquiv
  have hmapStab : ((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map (ggLin (p := 3) ι) =
      A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x' := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨ψ, ⟨hψA, hψs⟩, rfl⟩
      exact ⟨⟨ψ, hψA, rfl⟩, (ggLin_fix_iff ι ψ ⟨x, hx⟩).mp hψs⟩
    · rintro ⟨⟨ψ, hψA, rfl⟩, hs⟩
      exact ⟨ψ, ⟨hψA, (ggLin_fix_iff ι ψ ⟨x, hx⟩).mpr hs⟩, rfl⟩
  have hstabR : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x') ≤
      (3 - 1) * 6 * Nat.card ↥(Subgroup.closure (Set.range rL)) := by
    rw [← hmapStab]
    calc Nat.card ↥(((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
            MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)).map (ggLin (p := 3) ι))
        = Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
            MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (ggLin_injective ι)).toEquiv).symm
      _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hstabAA
      _ = (3 - 1) * 6 * Nat.card ↥(Subgroup.closure (Set.range rL)) := by rw [hcardL_A]
  exact ⟨ΛL, iFL, iDL, ML, CL, hL, aL, rL, hK, aK, rK, x', hcardL, hWM, hCL, hpairL, hrL,
    ⟨fL₀.trans eL, hfL⟩, hpairK, hrK, hx'0, hker, ht, hnonabR, hA', hnt, hstabR⟩

theorem ggTen_extract (hLNC : GGLNoncyclicInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum)
    (hJ2 : GGTBJTwoNodeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeNine p J K) (hyK : y ∈ K)
    (hcard : Nat.card ↥Bs = 3 ^ 10) (hLY : GGResLeviSideDatumLE3 p Bs L J)
    (hLn : ¬ GGResTwoNodeSideDatum p Bs L J) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : Finite V)
      (ι : Additive ↥Bs ≃+ V), Module.finrank (ZMod 3) V = 10 ∧
        GGTenLinear ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι)) :=
  ggTen_extract_of_coord hLNC hFix hFixK hp3 hH (ggTen_coord hD hJ2 hp3 hH hrow hyK hcard hLY hLn)

theorem ggTwoNodeTen_weyl
    (hKG : GGReflClassLargeInput') (hLNC : GGLNoncyclicInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum) (hJ2 : GGTBJTwoNodeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowTwoNodeNine p J K) (hyK : y ∈ K) (hcard : Nat.card ↥Bs = 3 ^ 10)
    (hLY : GGResLeviSideDatumLE3 p Bs L J) (hLn : ¬ GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp3 : p = 3 := by
    obtain ⟨labJ, labX, -, -, -, -, ⟨-, hp3, -⟩⟩ := hrow
    exact hp3
  obtain ⟨V, iA, iM, iF, ι, hdim, hlin⟩ :=
    ggTen_extract hLNC hFix hFixK hD hJ2 hp3 hH hrow hyK hcard hLY hLn
  letI := iA; letI := iM; letI := iF
  subst hp3
  exact ggRC_weylReflGroup_of_linWeyl ι _ (ggTen_linear hKG hdim _ hlin)

end CFSG.StandardType

end
