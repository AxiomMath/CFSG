module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSystems
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (UnitaryB2BlockStandardPair)
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_frobQ)
open CFSG.ClassicalInvolution.RouteD (IsTE6Chain)

@[expose] def GGF4QGeFourCfg {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) : Prop :=
  GGSecFiveRestHyp p B Bs x L D J ∧ GGSecFiveWeylCase' p B Bs x D J ∧
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L ∧ GGNbr p B x D J y K

inductive GGF4QGeFourRow
  | S1
  | S2

@[expose] def GGF4QGeFourRowHyp
    {G : Type} [Group G] (row : GGF4QGeFourRow) (f : ℕ) (L K : Subgroup G) : Prop :=
  match row with
  | .S1 => GGCentralImage .PSp 3 f L ∧ GGCentralImage .PSp 3 f K
  | .S2 => GGCentralImage .POmegaMinus 4 f L ∧
      (GGCentralImage .PSU 6 f K ∨ GGCentralImage .POmegaMinus 4 f K)

@[expose] def GGF4QGeFourBond
    {G : Type} [Group G] (row : GGF4QGeFourRow) (f : ℕ) (hf : 1 ≤ f) (U V : Subgroup G) : Prop :=
  match row with
  | .S1 => ∃ W, SymplecticBlockStandardPair (GaloisField 2 f) W U V
  | .S2 => ∃ W, UnitaryB2BlockStandardPair (frobQ 2 f) (frobQ_frobQ 2 f hf) W U V ∧ W ≤ U ⊔ V

@[expose] def GGF4QGeFourL1Input
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X : Subgroup G, (X = L ∨ X = K) → ∀ r ∈ ggAutomizer X Bs,
        r ∈ ggCoxRefl CoxeterMatrix.F₄ e → ggRankOnePerf Bs r = ggRankOneIn X Bs r

@[expose] def GGF4QGeFourRk1Input
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X : Subgroup G, (X = L ∨ X = K) → ∀ r ∈ ggAutomizer X Bs,
        r ∈ ggCoxRefl CoxeterMatrix.F₄ e →
          ∃ (F : Type) (_ : Field F) (_ : Finite F)
            (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
            Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
            (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
              ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
            (row = .S1 → Nat.card F = 2 ^ f) ∧
            (row = .S2 → Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f))

@[expose] def GGF4QGeFourGenInput
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X : Subgroup G, (X = L ∨ X = K) →
        X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl CoxeterMatrix.F₄ e},
          ggRankOneIn X Bs r

@[expose] def GGF4QGeFourOrbInput
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ i j : Fin 4, ∃ (w : CoxeterMatrix.F₄.Group) (X Y : Subgroup G), (X = L ∨ X = K) ∧
        (Y = L ∨ Y = K) ∧ (X = Y ∨ CoxeterMatrix.F₄ i j = 3) ∧
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs ∧
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs

@[expose] def GGF4QGeFourRk2Input
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f (hf : 2 ≤ f), p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X : Subgroup G, (X = L ∨ X = K) → ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4),
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
          (CoxeterMatrix.F₄ i j = 2 →
            ∀ a ∈ ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)),
            ∀ b ∈ ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)), a * b = b * a) ∧
          (CoxeterMatrix.F₄ i j = 3 →
            ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
              LinearBlockStandardPair F W
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)))) ∧
          (CoxeterMatrix.F₄ i j = 4 →
            GGF4QGeFourBond row f (by omega)
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹))) ∨
              GGF4QGeFourBond row f (by omega)
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)))
                (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹))))

@[expose] def GGF4QGeFourRk2CrossInput
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      ∀ X Y : Subgroup G, (X = L ∧ Y = K ∨ X = K ∧ Y = L) →
      ∀ (w : CoxeterMatrix.F₄.Group) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 →
        (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs →
        (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
            LinearBlockStandardPair F W
              (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
              (ggRankOneIn Y Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)))

@[expose] def GGF4QGeFourJoinInput
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGSecFiveRouteCfg p B Bs x L D J {K} →
    ∀ e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K → ggG0 p B x L D J = L ⊔ K

private theorem ggIsWeylMatrix_F₄ : GGIsWeylMatrix CoxeterMatrix.F₄ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))

private theorem f4_label_far : ∀ i j : Fin 4, i.val + 1 < j.val → CoxeterMatrix.F₄ i j = 2 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | decide | (exfalso; revert h; decide)

private theorem f4_label_single : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
    CoxeterMatrix.F₄ i j = 3 := by
  intro i j h h1
  fin_cases i <;> fin_cases j <;> first | decide | (exfalso; revert h h1; decide)

private theorem f4_label_rev : ∀ i j : Fin 4, CoxeterMatrix.F₄ (Fin.rev i) (Fin.rev j) =
    CoxeterMatrix.F₄ i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private theorem ggPres_conj_inv {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (w t : M.Group) :
    (↑(e w⁻¹) : MulAut ↥Bs) * ↑(e (w * t * w⁻¹)) * (↑(e w⁻¹))⁻¹ = (↑(e t) : MulAut ↥Bs) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

private theorem exists_conj_ggRankOnePerf {G : Type} [Group G] [Finite G] {Bs H : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer H Bs) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥A) (w : M.Group) :
    ∃ g : G, ∀ i : ι, (ggRankOnePerf Bs ↑(e (w * M.simple i * w⁻¹))).map
      (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs ↑(e (M.simple i)) := by
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (hA (e w⁻¹).2)
  exact ⟨g, fun i => by rw [ggRankOnePerf_map_conj hg, ggPres_conj_inv]⟩

private theorem GGF4QGeFourBond.map_conj
    {G : Type} [Group G] {row : GGF4QGeFourRow} {f : ℕ} {hf : 1 ≤ f} {U V : Subgroup G}
    (h : GGF4QGeFourBond row f hf U V) (g : G) :
    GGF4QGeFourBond row f hf (U.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom) := by
  cases row with
  | S1 =>
    obtain ⟨W, hW⟩ := h
    exact ⟨_, CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW _
      (MulAut.conj g).injective⟩
  | S2 =>
    obtain ⟨W, hW, hle⟩ := h
    refine ⟨_, CFSG.ClassicalInvolution.Models.TwistedPairs.TwistedB2Model.StandardPair.map hW _
      (MulAut.conj g).injective, ?_⟩
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hle

private theorem unitaryB2BlockStandardPair_card {E : Type} [Field E] {θ : E →+* E}
    {hθ : ∀ c, θ (θ c) = c} {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryB2BlockStandardPair θ hθ W U V) :
    Nat.card U = Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        ↥(CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField θ)) ∧
      Nat.card V = Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) := by
  obtain ⟨φ, -, -, hl, hs, hU, hV⟩ := h
  constructor
  · rw [← hU, ← MonoidHom.range_comp]
    exact Nat.card_congr (MonoidHom.ofInjective hl).toEquiv.symm
  · rw [← hV, ← MonoidHom.range_comp]
    exact Nat.card_congr (MonoidHom.ofInjective hs).toEquiv.symm

private theorem ggF4QGeFour_pairs
    {row : GGF4QGeFourRow} (hL1 : GGF4QGeFourL1Input row) (hOrb : GGF4QGeFourOrbInput row)
    (hRk2 : GGF4QGeFourRk2Input row) (hRk2c : GGF4QGeFourRk2CrossInput row)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp row f L K)
    (hf1 : 1 ≤ f) :
    (∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 2 →
      ∀ a ∈ ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i)),
      ∀ b ∈ ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple j)), a * b = b * a) ∧
    (∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 3 → ∀ (F : Type) [Field F] [Finite F],
      Nat.card ↥(ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i))) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) →
      ∃ W : Subgroup G, LinearBlockStandardPair F W
        (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i)))
        (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple j)))) ∧
    (GGF4QGeFourBond row f hf1 (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple 1)))
        (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple 2))) ∨
      GGF4QGeFourBond row f hf1 (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple 2)))
        (ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple 1)))) := by
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hL1' := hL1 G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  have hOrb' := hOrb G p B Bs x L D J y K hcfg e hpres f hf hp hrow
  have hRk2' := hRk2 G p B Bs x L D J y K hcfg e hpres f hf hp hrow
  have hRk2c' := hRk2c G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    obtain ⟨w, X, Y, hX, -, hXY, hi, hj⟩ := hOrb' i j
    rw [← hXY.resolve_right (by omega)] at hj
    have h1 := (hRk2' X hX w i j hi hj).1 hij
    rw [← hL1' X hX _ hi ⟨w, i, rfl⟩, ← hL1' X hX _ hj ⟨w, j, rfl⟩] at h1
    exact ggRankOnePerf_comm_of_conj_pair hAH e w i j h1 a ha b hb
  · intro i j hij F _ _ hcard
    obtain ⟨w, X, Y, hX, hY, -, hi, hj⟩ := hOrb' i j
    obtain ⟨F', _, _, W, -, hW⟩ : ∃ (F' : Type) (_ : Field F') (_ : Finite F') (W : Subgroup G),
        CharP F' 2 ∧ LinearBlockStandardPair F' W
          (ggRankOneIn X Bs ↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)))
          (ggRankOneIn Y Bs ↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹))) := by
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
      · exact (hRk2' _ (Or.inl rfl) w i j hi hj).2.1 hij
      · exact hRk2c' _ _ (Or.inl ⟨rfl, rfl⟩) w i j hij hi hj
      · exact hRk2c' _ _ (Or.inr ⟨rfl, rfl⟩) w i j hij hi hj
      · exact (hRk2' _ (Or.inr rfl) w i j hi hj).2.1 hij
    rw [← hL1' X hX _ hi ⟨w, i, rfl⟩, ← hL1' Y hY _ hj ⟨w, j, rfl⟩] at hW
    exact ggLinearBlockPair_of_conj_pair hAH e w i j hW hcard
  · obtain ⟨w, X, Y, hX, -, hXY, hi, hj⟩ := hOrb' 1 2
    rw [← hXY.resolve_right (by decide)] at hj
    have h4 := (hRk2' X hX w 1 2 hi hj).2.2 (by decide)
    rw [← hL1' X hX _ hi ⟨w, 1, rfl⟩, ← hL1' X hX _ hj ⟨w, 2, rfl⟩] at h4
    obtain ⟨g, hg⟩ := exists_conj_ggRankOnePerf hAH e w
    rcases h4 with h4 | h4
    · left
      have h5 := h4.map_conj g
      rwa [hg 1, hg 2] at h5
    · right
      have h5 := h4.map_conj g
      rwa [hg 1, hg 2] at h5

private theorem ggF4QGeFour_node
    {row : GGF4QGeFourRow} (hL1 : GGF4QGeFourL1Input row) (hRk1 : GGF4QGeFourRk1Input row)
    (hOrb : GGF4QGeFourOrbInput row)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp row f L K)
    (k : Fin 4) :
    (∃ n ∈ ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple k)),
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, (((↑(e (CoxeterMatrix.F₄.simple k)) : MulAut ↥Bs) b : ↥Bs) : G) =
        n * b * n⁻¹) ∧
    (∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card ↥(ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple k))) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      (row = .S1 → Nat.card F = 2 ^ f)) ∧
    ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple k)) ≤ L ⊔ K := by
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hL1' := hL1 G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  have hRk1' := hRk1 G p B Bs x L D J y K hcfg e hpres f hf hp hrow
  obtain ⟨w, X, _, hX, -, -, hk, -⟩ := hOrb G p B Bs x L D J y K hcfg e hpres f hf hp hrow k k
  have hL1k := hL1' X hX _ hk ⟨w, k, rfl⟩
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, ⟨n₀, hn₀, hn₀N, hn₀r⟩, hFc, -⟩ :=
    hRk1' X hX _ hk ⟨w, k, rfl⟩
  have hconj := ggRankOnePerf_conj_card_le (hAH (e w⁻¹).2)
    (↑(e (w * CoxeterMatrix.F₄.simple k * w⁻¹)) : MulAut ↥Bs)
  rw [ggPres_conj_inv] at hconj
  refine ⟨?_, ⟨F, hF, hFfin, ?_, hFc⟩, ?_⟩
  · rw [← hL1k] at hn₀
    obtain ⟨g, -, -, -, hnS, hnN, hnr⟩ := ggWeylElt_conj (hAH (e w⁻¹).2) hn₀ hn₀N hn₀r
    rw [ggPres_conj_inv] at hnS hnr
    exact ⟨_, hnS, hnN, hnr⟩
  · rw [hconj.1, hL1k, ← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  · refine hconj.2 ?_
    rw [hL1k]
    refine (ggRankOneIn_le X Bs _).trans ?_
    rcases hX with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right

private theorem ggF4QGeFour_iSup
    {row : GGF4QGeFourRow} (hL1 : GGF4QGeFourL1Input row) (hRk1 : GGF4QGeFourRk1Input row)
    (hGen : GGF4QGeFourGenInput row) (hOrb : GGF4QGeFourOrbInput row)
    (hJoin : GGF4QGeFourJoinInput row)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f) (hp : p ∣ 2 ^ f - 1) (hrow : GGF4QGeFourRowHyp row f L K) :
    ⨆ i : Fin 4, ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i)) = ggG0 p B x L D J := by
  have hL1' := hL1 G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow
  have hGen' := hGen G p B Bs x L D J y K hcfg e hpres f hf hp hrow
  have hnode := ggF4QGeFour_node hL1 hRk1 hOrb hcfg hRC e hpres hf hp hrow
  rw [hJoin G p B Bs x L D J y K hcfg hRC e hpres f hf hp hrow]
  apply le_antisymm
  · exact iSup_le fun i => (hnode i).2.2
  · refine sup_le ?_ ?_
    · exact ggLe_iSup_ggRankOnePerf_of_gen e (fun i => (hnode i).1) (hGen' L (Or.inl rfl))
        (hL1' L (Or.inl rfl))
    · exact ggLe_iSup_ggRankOnePerf_of_gen e (fun i => (hnode i).1) (hGen' K (Or.inr rfl))
        (hL1' K (Or.inr rfl))

private theorem ggF4QGeFour_sysF4_of {G : Type} [Group G] (f : ℕ) (S : Fin 4 → Subgroup G)
    (σ : Fin 4 → Fin 4) (hσ : ∀ i j, CoxeterMatrix.F₄ (σ i) (σ j) = CoxeterMatrix.F₄ i j)
    (hcomm : ∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hlin : ∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 3 → ∀ (F : Type) [Field F] [Finite F],
      Nat.card ↥(S i) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) →
        ∃ W : Subgroup G, LinearBlockStandardPair F W (S i) (S j))
    (hcard : ∀ i, Nat.card ↥(S i) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))
    (hbond : ∃ W, SymplecticBlockStandardPair (GaloisField 2 f) W (S (σ 1)) (S (σ 2))) :
    (∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ S (σ i), ∀ b ∈ S (σ j), a * b = b * a) ∧
    (∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (S (σ i)) (S (σ j))) ∧
    (∃ W, SymplecticBlockStandardPair (GaloisField 2 f) W (S (σ 1)) (S (σ 2))) := by
  refine ⟨fun i j hij => hcomm (σ i) (σ j) (by rw [hσ]; exact f4_label_far i j hij), ?_, hbond⟩
  intro i j hij hi1
  exact hlin (σ i) (σ j) (by rw [hσ]; exact f4_label_single i j hij hi1) _ (hcard (σ i))

private theorem ggF4QGeFour_isTE6Chain_of
    {G : Type} [Group G] (f : ℕ) (hf1 : 1 ≤ f) (S : Fin 4 → Subgroup G) (σ : Fin 4 → Fin 4)
    (hσ : ∀ i j, CoxeterMatrix.F₄ (σ i) (σ j) = CoxeterMatrix.F₄ i j)
    (hcomm : ∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hlin : ∀ i j : Fin 4, CoxeterMatrix.F₄ i j = 3 → ∀ (F : Type) [Field F] [Finite F],
      Nat.card ↥(S i) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) →
        ∃ W : Subgroup G, LinearBlockStandardPair F W (S i) (S j))
    (hbond : ∃ W, UnitaryB2BlockStandardPair (frobQ 2 f) (frobQ_frobQ 2 f hf1) W (S (σ 1))
      (S (σ 2)) ∧ W ≤ S (σ 1) ⊔ S (σ 2)) :
    IsTE6Chain 2 f hf1 (fun k => S (σ k)) := by
  obtain ⟨W, hW, hWle⟩ := hbond
  obtain ⟨hc1, hc2⟩ := unitaryB2BlockStandardPair_card hW
  have hc1' : Nat.card ↥(S (σ 1)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
    rw [hc1, ggSL2_card, ggSL2_card,
      CFSG.ClassicalInvolution.WeakCT.card_fixedField_frobQ 2 f hf1,
      GaloisField.card 2 f (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    exact hcomm (σ i) (σ j) (by rw [hσ]; exact f4_label_far i j hij) a ha b hb
  · obtain ⟨W', hW'⟩ := hlin (σ 1) (σ 0) (by rw [hσ]; decide) _ hc1'
    exact ⟨W', CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW'⟩
  · exact hlin (σ 2) (σ 3) (by rw [hσ]; decide) _ hc2
  · exact ⟨W, hW, hWle.trans le_sup_left⟩

theorem ggF4QGeFourSysF4Input_of_twins
    (hL1 : GGF4QGeFourL1Input .S1) (hRk1 : GGF4QGeFourRk1Input .S1)
    (hGen : GGF4QGeFourGenInput .S1) (hOrb : GGF4QGeFourOrbInput .S1)
    (hRk2 : GGF4QGeFourRk2Input .S1) (hRk2c : GGF4QGeFourRk2CrossInput .S1)
    (hJoin : GGF4QGeFourJoinInput .S1) :
    GGF4QGeFourSysF4Input := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  obtain ⟨e, he⟩ := hWK
  have hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e :=
    ⟨ggIsWeylMatrix_F₄, he⟩
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hrow : GGF4QGeFourRowHyp .S1 f L K := ⟨hL, hK⟩
  set S : Fin 4 → Subgroup G := fun i => ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i))
  obtain ⟨hcomm, hlin, hbond⟩ :=
    ggF4QGeFour_pairs hL1 hOrb hRk2 hRk2c hcfg hRC e hpres hf hp hrow (by omega)
  have hgen : ⨆ i, S i = ggG0 p B x L D J :=
    ggF4QGeFour_iSup hL1 hRk1 hGen hOrb hJoin hcfg hRC e hpres hf hp hrow
  have hcard : ∀ i, Nat.card ↥(S i) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
    intro i
    obtain ⟨F, _, _, hc, hF⟩ :=
      (ggF4QGeFour_node hL1 hRk1 hOrb hcfg hRC e hpres hf hp hrow i).2.1
    rw [hc, ggSL2_card, ggSL2_card, hF rfl, GaloisField.card 2 f (by omega)]
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hbond with hb | hb
  · obtain ⟨h1, h2, h3⟩ := ggF4QGeFour_sysF4_of f S id (fun _ _ => rfl) hcomm hlin hcard hb
    exact ⟨GaloisField 2 f, inferInstance, inferInstance, S, hF, h1, h2, h3, hgen⟩
  · obtain ⟨h1, h2, h3⟩ := ggF4QGeFour_sysF4_of f S Fin.rev f4_label_rev hcomm hlin hcard hb
    refine ⟨GaloisField 2 f, inferInstance, inferInstance, fun k => S (Fin.rev k), hF, h1, h2,
      h3, ?_⟩
    rw [← hgen]
    exact Equiv.iSup_comp (g := S) Fin.revPerm

theorem ggF4QGeFourSysTwE6Input_of_twins
    (hL1 : GGF4QGeFourL1Input .S2) (hRk1 : GGF4QGeFourRk1Input .S2)
    (hGen : GGF4QGeFourGenInput .S2) (hOrb : GGF4QGeFourOrbInput .S2)
    (hRk2 : GGF4QGeFourRk2Input .S2) (hRk2c : GGF4QGeFourRk2CrossInput .S2)
    (hJoin : GGF4QGeFourJoinInput .S2) :
    GGF4QGeFourSysTwE6Input := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  obtain ⟨e, he⟩ := hWK
  have hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e :=
    ⟨ggIsWeylMatrix_F₄, he⟩
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hrow : GGF4QGeFourRowHyp .S2 f L K := ⟨hL, hK⟩
  have hf1 : 1 ≤ f := by omega
  set S : Fin 4 → Subgroup G := fun i => ggRankOnePerf Bs ↑(e (CoxeterMatrix.F₄.simple i))
  obtain ⟨hcomm, hlin, hbond⟩ :=
    ggF4QGeFour_pairs hL1 hOrb hRk2 hRk2c hcfg hRC e hpres hf hp hrow hf1
  have hgen : ⨆ i, S i = ggG0 p B x L D J :=
    ggF4QGeFour_iSup hL1 hRk1 hGen hOrb hJoin hcfg hRC e hpres hf hp hrow
  rcases hbond with hb | hb
  · exact ⟨hf1, S, ggF4QGeFour_isTE6Chain_of f hf1 S id (fun _ _ => rfl) hcomm hlin hb, hgen⟩
  · refine ⟨hf1, fun k => S (Fin.rev k),
      ggF4QGeFour_isTE6Chain_of f hf1 S Fin.rev f4_label_rev hcomm hlin hb, ?_⟩
    rw [← hgen]
    exact Equiv.iSup_comp (g := S) Fin.revPerm

end CFSG.StandardType

end
