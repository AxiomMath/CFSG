module

public import CFSG.Quasithin.MS93.S5B512Stmt
public import CFSG.Quasithin.MS93.S5A56FStmt
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

section Defs

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def lamSel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (α' δ : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g x : (puAmalgam h.le).Universal, g ∈ stab _ (baseA _) ∧
    x ∈ puTrans h.le L (baseA _) ∧
    (((∀ l, ¬ S5.Case56 h q a δ l) ∧ S5.Concl55 h q α' δ g x) ∨
      (∃ l, S5.Case56 h q a δ l ∧ S5.Concl56 h q a α' l g x ∧ S l g x)) ∧
    (μ = g⁻¹ • δ ∨ μ = x⁻¹ • (g⁻¹ • δ))}

@[expose] def lamAllSel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (α' : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ ∧
    ¬ S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) ∧ μ ∈ lamSel h q a S α' δ}

@[expose] def lamAtSel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (γ γ' δ : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g : (puAmalgam h.le).Universal, g • γ = baseA _ ∧ g • geo _ γ γ' 1 = baseB _ ∧
    g • μ ∈ lamSel h q a S (g • γ') (g • δ)}

@[expose] def lamAllAtSel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (γ γ' : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g : (puAmalgam h.le).Universal, g • γ = baseA _ ∧ g • geo _ γ γ' 1 = baseB _ ∧
    g • μ ∈ lamAllSel h q a S (g • γ')}

@[expose] def IsLamStepSel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (γ γ' μ : Vtx (puAmalgam h.le)) : Prop :=
  IsCritical _ γ γ' ∧ μ ∈ lamAtSel h q a S γ γ' (geo _ γ γ' 2) ∧ IsCritical _ μ (geo _ γ γ' 2)

@[expose] def IsChain512Sel (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop)
    (α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)) : Prop :=
  geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _ ∧
    IsLamStepSel h q a S (geo _ (baseA (puAmalgam h.le)) α' 2) ν (baseA _) ∧
    geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν 2 = α' ∧
    IsCritical _ (baseA (puAmalgam h.le)) α' ∧
    μ₁ ∈ lamSel h q a S α' (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
    IsCritical _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
    IsLamStepSel h q a S μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) μ₂

@[expose] def Prod56 (h : PUHyp M T L) (k : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop) :
    Prop :=
  ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
    ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
      Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) →
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l) →
      ∃ g ∈ stab _ (baseA _), ∃ x ∈ puTrans h.le L (baseA _),
        S5.Concl56 h (2 ^ k) a α' l g x ∧ S l g x

end Defs

@[expose] def S512TwoF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k

@[expose] def S512ThreeF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

section Lemmas

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L} {q : ℕ}
  {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}
  {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}

theorem lamSel_subset {α' δ μ : Vtx (puAmalgam h.le)} (hμ : μ ∈ lamSel h q a S α' δ) :
    μ ∈ S5.lam h q a α' δ := by
  obtain ⟨g, x, hg, hx, hc, hμ⟩ := hμ
  exact ⟨g, x, hg, hx, hc.imp id fun ⟨l, hl, hc, _⟩ => ⟨l, hl, hc⟩, hμ⟩

theorem lamAllSel_subset {α' μ : Vtx (puAmalgam h.le)} (hμ : μ ∈ lamAllSel h q a S α') :
    μ ∈ S5.lamAll h q a α' := by
  obtain ⟨δ, hβδ, hδB, hμ⟩ := hμ
  exact ⟨δ, hβδ, hδB, lamSel_subset hμ⟩

theorem lamAtSel_subset {γ γ' δ μ : Vtx (puAmalgam h.le)} (hμ : μ ∈ lamAtSel h q a S γ γ' δ) :
    μ ∈ lamAt h q a γ γ' δ := by
  obtain ⟨g, h1, h2, h3⟩ := hμ
  exact ⟨g, h1, h2, lamSel_subset h3⟩

theorem lamAllAtSel_subset {γ γ' μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ lamAllAtSel h q a S γ γ') : μ ∈ lamAllAt h q a γ γ' := by
  obtain ⟨g, h1, h2, h3⟩ := hμ
  exact ⟨g, h1, h2, lamAllSel_subset h3⟩

theorem lamAllAtSel_smul (g : (puAmalgam h.le).Universal) {γ γ' μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ lamAllAtSel h q a S γ γ') : g • μ ∈ lamAllAtSel h q a S (g • γ) (g • γ') := by
  obtain ⟨g', h1, h2, h3⟩ := hμ
  refine ⟨g' * g⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_smul, h1]
  · rw [geo_smul, mul_smul, inv_smul_smul, h2]
  · rw [mul_smul, inv_smul_smul, mul_smul, inv_smul_smul]
    exact h3

theorem lamAtSel_smul (g : (puAmalgam h.le).Universal) {γ γ' δ μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ lamAtSel h q a S γ γ' δ) : g • μ ∈ lamAtSel h q a S (g • γ) (g • γ') (g • δ) := by
  obtain ⟨g', h1, h2, h3⟩ := hμ
  refine ⟨g' * g⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_smul, h1]
  · rw [geo_smul, mul_smul, inv_smul_smul, h2]
  · rw [mul_smul, inv_smul_smul, mul_smul, inv_smul_smul, mul_smul, inv_smul_smul]
    exact h3

theorem isLamStepSel_subset {γ γ' μ : Vtx (puAmalgam h.le)}
    (hs : IsLamStepSel h q a S γ γ' μ) : IsLamStep h q a γ γ' μ :=
  ⟨hs.1, lamAtSel_subset hs.2.1, hs.2.2⟩

theorem isLamStepSel_smul (g : (puAmalgam h.le).Universal) {γ γ' μ : Vtx (puAmalgam h.le)}
    (hs : IsLamStepSel h q a S γ γ' μ) : IsLamStepSel h q a S (g • γ) (g • γ') (g • μ) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨(isCritical_smul _ g _ _).2 h1, ?_, ?_⟩
  · rw [geo_smul]
    exact lamAtSel_smul g h2
  · rw [geo_smul]
    exact (isCritical_smul _ g _ _).2 h3

theorem isChain512Sel_subset {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hch : IsChain512Sel h q a S α' ν μ₁ μ₂) : IsChain512 h q a α' ν μ₁ μ₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hch
  exact ⟨h1, isLamStepSel_subset h2, h3, h4, lamSel_subset h5, h6, isLamStepSel_subset h7⟩

theorem exists_mem_stab_of_mem_lamSel {α' δ μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ lamSel h q a S α' δ) : ∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • δ := by
  obtain ⟨g, x, hg, hx, -, hμeq⟩ := hμ
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  rcases hμeq with rfl | rfl
  · exact ⟨g⁻¹, inv_mem hg, rfl⟩
  · exact ⟨x⁻¹ * g⁻¹, mul_mem (inv_mem hxst) (inv_mem hg), by rw [mul_smul]⟩

end Lemmas

section Prod

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L} {k : ℕ}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem prod56_top (h56 : S56) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) : Prod56 h k a (fun _ _ _ => True) := by
  intro α' hc hαβ l hl hTl hJl
  obtain ⟨g, hg, x, hx, hconc⟩ := h56 G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl hTl hJl
  exact ⟨g, hg, x, hx, hconc, trivial⟩

theorem prod56_opp (h56f : S5.S56f) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) : Prod56 h k a (S5.Opp56 h (2 ^ k) a) := by
  intro α' hc hαβ l hl hTl hJl
  obtain ⟨g, hg, x, hx, hconc⟩ := h56f G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl hTl hJl
  exact ⟨g, hg, x, hx, hconc.1.1, hconc.2⟩

end Prod

end S5B

end CFSG.Quasithin.MS93
