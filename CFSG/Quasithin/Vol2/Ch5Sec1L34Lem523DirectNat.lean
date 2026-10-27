module

public import CFSG.Quasithin.Vol2.Ch6NatSum
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

variable {G : Type} [Group G]

namespace NatL2Data

variable {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n)

@[expose] noncomputable def conjG (g : G) (hg : g ∈ L) : (Fin 2 → D.K) ≃+ (Fin 2 → D.K) :=
  D.conj ⟨g, D.le_normalizer hg⟩

@[expose] def SylowAdapted (S : Subgroup G) : Prop :=
  (∀ (g : G) (hg : g ∈ L), g ∈ S → ∃ b : D.K, ∀ w : Fin 2 → D.K,
      D.conjG g hg w = (unipSL b : Matrix.SpecialLinearGroup (Fin 2) D.K).1.mulVec w) ∧
  (∀ b : D.K, ∃ (g : G) (hg : g ∈ L), g ∈ S ∧ ∀ w : Fin 2 → D.K,
      D.conjG g hg w = (unipSL b : Matrix.SpecialLinearGroup (Fin 2) D.K).1.mulVec w)

end NatL2Data

theorem coe_specialLinearGroupEquivStatedSL_symm {F : Type} [Field F]
    (γ : ↥(Assembly.LowTwoRank.StatedSL 2 F)) :
    (((specialLinearGroupEquivStatedSL 2 F).symm γ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = ((γ : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
  conv_rhs => rw [← (specialLinearGroupEquivStatedSL 2 F).apply_symm_apply γ]
  rfl

theorem IsNatModCh5.exists_sylowAdapted {L W S : Subgroup G} [Finite G] {n : ℕ}
    (h : IsNatModCh5 L W n) (hS : IsSylowTwoOf S L) :
    ∃ D : NatL2Data L W n, D.SylowAdapted S := by
  obtain ⟨F, hF, hfin, hchar, hcard, ψ, Y, hY, hψ⟩ := h.exists_sylowCoord hS
  let e := specialLinearGroupEquivStatedSL 2 F
  let π : ↥(Assembly.LowTwoRank.StatedSL 2 F) →* ↥(autOn L W) :=
    ψ.symm.toMonoidHom.comp e.symm.toMonoidHom
  have hπ : ∀ γ : ↥(Assembly.LowTwoRank.StatedSL 2 F),
      ψ (π γ) = e.symm γ := fun γ => by
    simp [π]
  let D : NatL2Data L W n :=
    { K := F
      E := Y
      card := hcard
      π := π
      surj := by
        intro x
        refine ⟨e (ψ x), ?_⟩
        simp [π]
      le_normalizer := h.1
      inter := by
        intro γ v
        have := hY (π γ) v
        rw [hπ γ, coe_specialLinearGroupEquivStatedSL_symm] at this
        exact this }
  have hconj : ∀ (g : G) (hg : g ∈ L) (x : ↥(autOn L W)),
      (x : MulAut ↥W) = conjAct W ⟨g, D.le_normalizer hg⟩ →
      ∀ w : Fin 2 → F, D.conjG g hg w = (ψ x : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec w := by
    intro g hg x hx w
    obtain ⟨v, rfl⟩ : ∃ v : ↥W, Multiplicative.toAdd (Y v) = w :=
      ⟨Y.symm (Multiplicative.ofAdd w), by simp⟩
    show D.conj ⟨g, D.le_normalizer hg⟩ (Multiplicative.toAdd (Y v)) = _
    rw [NatL2Data.conj_apply]
    have e1 : conjAct W ⟨g, D.le_normalizer hg⟩ v = (x : MulAut ↥W) v := by rw [hx]
    rw [e1]
    exact hY x v
  refine ⟨D, ?_, ?_⟩
  · intro g hg hgS
    let x : ↥(autOn L W) := ⟨conjAct W ⟨g, D.le_normalizer hg⟩,
      mem_autOn_iff.mpr ⟨⟨g, D.le_normalizer hg⟩, hg, rfl⟩⟩
    have hxS : (x : MulAut ↥W) ∈ autOn S W :=
      mem_autOn_iff.mpr ⟨⟨g, D.le_normalizer hg⟩, hgS, rfl⟩
    obtain ⟨b, hb⟩ := (hψ x).mp hxS
    refine ⟨b, fun w => ?_⟩
    rw [hconj g hg x rfl w, hb]
  · intro b
    let y : ↥(autOn L W) := ψ.symm (unipSL b)
    have hyS : (y : MulAut ↥W) ∈ autOn S W := (hψ y).mpr ⟨b, by simp [y]⟩
    obtain ⟨g', hg'S, hg'y⟩ := mem_autOn_iff.mp hyS
    have hgL : (g' : G) ∈ L := hS.1 hg'S
    refine ⟨g', hgL, hg'S, fun w => ?_⟩
    rw [hconj g' hgL y hg'y.symm w]
    simp [y]

namespace NatL2Data

variable {L W V' : Subgroup G} {n : ℕ}

@[expose] noncomputable def trAut523 (Ψ : ↥W ≃* ↥V') (φ : MulAut ↥W) : MulAut ↥V' :=
  Ψ.symm.trans (φ.trans Ψ)

theorem trAut523_apply (Ψ : ↥W ≃* ↥V') (φ : MulAut ↥W) (v : ↥V') :
    trAut523 Ψ φ v = Ψ (φ (Ψ.symm v)) := rfl

@[expose] noncomputable def trAutHom (Ψ : ↥W ≃* ↥V') : MulAut ↥W →* MulAut ↥V' where
  toFun := trAut523 Ψ
  map_one' := by
    ext v
    simp [trAut523]
  map_mul' φ χ := by
    ext v
    simp [trAut523]

theorem trAut523_conjAct (Ψ : ↥W ≃* ↥V') {ℓ : G} (hW : ℓ ∈ Subgroup.normalizer (W : Set G))
    (hV : ℓ ∈ Subgroup.normalizer (V' : Set G))
    (hΨ : ∀ w : ↥W, Ψ (conjAct W ⟨ℓ, hW⟩ w) = conjAct V' ⟨ℓ, hV⟩ (Ψ w)) :
    trAut523 Ψ (conjAct W ⟨ℓ, hW⟩) = conjAct V' ⟨ℓ, hV⟩ := by
  ext v
  rw [trAut523_apply]
  have h := hΨ (Ψ.symm v)
  rw [MulEquiv.apply_symm_apply] at h
  exact congrArg Subtype.val h

noncomputable abbrev transport (D : NatL2Data L W n) (Ψ : ↥W ≃* ↥V')
    (hV' : L ≤ Subgroup.normalizer (V' : Set G))
    (hΨ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W),
      Ψ (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ w) = conjAct V' ⟨ℓ, hV' hℓ⟩ (Ψ w)) :
    NatL2Data L V' n :=
  { K := D.K
    E := Ψ.symm.trans D.E
    card := D.card
    π := MonoidHom.codRestrict ((trAutHom Ψ).comp (((autOn L W).subtype).comp D.π))
      (autOn L V') (by
        intro γ
        obtain ⟨m, hmL, hm⟩ := mem_autOn_iff.mp (D.π γ).2
        show trAut523 Ψ ((D.π γ : ↥(autOn L W)) : MulAut ↥W) ∈ autOn L V'
        rw [← hm, trAut523_conjAct Ψ (D.le_normalizer hmL) (hV' hmL) (hΨ m hmL)]
        exact mem_autOn_iff.mpr ⟨⟨m, hV' hmL⟩, hmL, rfl⟩)
    surj := by
      intro x'
      obtain ⟨m, hmL, hm⟩ := mem_autOn_iff.mp x'.2
      obtain ⟨γ, hγ⟩ := D.surj ⟨conjAct W ⟨m, D.le_normalizer hmL⟩,
        mem_autOn_iff.mpr ⟨⟨m, D.le_normalizer hmL⟩, hmL, rfl⟩⟩
      refine ⟨γ, Subtype.ext ?_⟩
      show trAut523 Ψ ((D.π γ : ↥(autOn L W)) : MulAut ↥W) = (x' : MulAut ↥V')
      rw [hγ]
      show trAut523 Ψ (conjAct W ⟨m, D.le_normalizer hmL⟩) = (x' : MulAut ↥V')
      rw [trAut523_conjAct Ψ (D.le_normalizer hmL) (hV' hmL) (hΨ m hmL)]
      exact hm
    le_normalizer := hV'
    inter := by
      intro γ v
      have h := D.inter γ (Ψ.symm v)
      change Multiplicative.toAdd (D.E (Ψ.symm (trAut523 Ψ ((D.π γ : ↥(autOn L W)) :
        MulAut ↥W) v))) = _
      rw [trAut523_apply, MulEquiv.symm_apply_apply]
      exact h }

theorem conjG_transport (D : NatL2Data L W n) (Ψ : ↥W ≃* ↥V')
    (hV' : L ≤ Subgroup.normalizer (V' : Set G))
    (hΨ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W),
      Ψ (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ w) = conjAct V' ⟨ℓ, hV' hℓ⟩ (Ψ w))
    (ℓ : G) (hℓ : ℓ ∈ L) (w : Fin 2 → D.K) :
    (D.transport Ψ hV' hΨ).conjG ℓ hℓ w = D.conjG ℓ hℓ w := by
  obtain ⟨v', rfl⟩ : ∃ v' : ↥V', Multiplicative.toAdd ((Ψ.symm.trans D.E) v') = w :=
    ⟨(Ψ.symm.trans D.E).symm (Multiplicative.ofAdd w), by simp⟩
  have h := hΨ ℓ hℓ (Ψ.symm v')
  rw [MulEquiv.apply_symm_apply] at h
  unfold NatL2Data.conjG
  rw [NatL2Data.conj_apply]
  have e2 : (Ψ.symm.trans D.E) v' = D.E (Ψ.symm v') := rfl
  rw [e2, NatL2Data.conj_apply]
  show Multiplicative.toAdd (D.E (Ψ.symm (conjAct V' ⟨ℓ, hV' hℓ⟩ v'))) =
    Multiplicative.toAdd (D.E (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ (Ψ.symm v')))
  rw [← h, MulEquiv.symm_apply_apply]

theorem sylowAdapted_transport (D : NatL2Data L W n) (Ψ : ↥W ≃* ↥V')
    (hV' : L ≤ Subgroup.normalizer (V' : Set G))
    (hΨ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W),
      Ψ (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ w) = conjAct V' ⟨ℓ, hV' hℓ⟩ (Ψ w))
    {S : Subgroup G} (hD : D.SylowAdapted S) : (D.transport Ψ hV' hΨ).SylowAdapted S := by
  obtain ⟨h1, h2⟩ := hD
  refine ⟨fun g hg hgS => ?_, fun b => ?_⟩
  · obtain ⟨b', hb'⟩ := h1 g hg hgS
    exact ⟨b', fun w => by rw [conjG_transport]; exact hb' w⟩
  · obtain ⟨g, hg, hgS, hb⟩ := h2 b
    exact ⟨g, hg, hgS, fun w => by rw [conjG_transport]; exact hb w⟩

theorem mem_centralizer_iff_line (D : NatL2Data L V' n) {S : Subgroup G} (hSL : S ≤ L)
    (hD : D.SylowAdapted S) (v : ↥V') :
    (v : G) ∈ Subgroup.centralizer (S : Set G) ↔
      ∃ a : D.K, Multiplicative.toAdd (D.E v) = ![a, 0] := by
  obtain ⟨h1, h2⟩ := hD
  constructor
  · intro hv
    obtain ⟨g₁, hg₁, hg₁S, hb₁⟩ := h2 1
    have hc := Subgroup.mem_centralizer_iff.mp hv g₁ hg₁S
    have hv' : conjAct V' ⟨g₁, D.le_normalizer hg₁⟩ v = v := by
      apply Subtype.ext
      rw [conjAct_apply_coe]
      calc g₁ * (v : G) * g₁⁻¹ = (v * g₁) * g₁⁻¹ := by rw [← hc]
        _ = v := by group
    have h := hb₁ (Multiplicative.toAdd (D.E v))
    unfold NatL2Data.conjG at h
    rw [NatL2Data.conj_apply, hv'] at h
    have hx0 := congrFun h 0
    refine ⟨Multiplicative.toAdd (D.E v) 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · simp [coe_unipSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx0 ⊢
      linear_combination hx0
  · rintro ⟨a, ha⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hgS
    have hgL := hSL hgS
    obtain ⟨b, hb⟩ := h1 g hgL hgS
    have hfix : D.conjG g hgL (Multiplicative.toAdd (D.E v)) = Multiplicative.toAdd (D.E v) := by
      rw [hb, ha]
      ext i
      fin_cases i <;> simp [coe_unipSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h2' : conjAct V' ⟨g, D.le_normalizer hgL⟩ v = v := by
      apply D.E.injective
      apply Multiplicative.toAdd.injective
      unfold NatL2Data.conjG at hfix
      rw [NatL2Data.conj_apply] at hfix
      exact hfix
    have h3 := congrArg (fun x : ↥V' => (x : G)) h2'
    simp only [conjAct_apply_coe] at h3
    calc g * (v : G) = (g * v * g⁻¹) * g := by group
      _ = v * g := by rw [h3]

noncomputable def scalMul (D : NatL2Data L W n) (c : D.K) (hc : c ≠ 0) : ↥W ≃* ↥W :=
  D.E.trans ((AddEquiv.toMultiplicative (LinearEquiv.smulOfNeZero D.K (Fin 2 → D.K) c hc).toAddEquiv).trans
    D.E.symm)

theorem scalMul_apply (D : NatL2Data L W n) (c : D.K) (hc : c ≠ 0) (w : ↥W) :
    Multiplicative.toAdd (D.E (scalMul D c hc w)) = c • Multiplicative.toAdd (D.E w) := by
  simp [scalMul]

theorem scalMul_conj (D : NatL2Data L W n) (c : D.K) (hc : c ≠ 0) (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W) :
    scalMul D c hc (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ w) =
      conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ (scalMul D c hc w) := by
  apply D.E.injective
  apply Multiplicative.toAdd.injective
  have hA : ∀ v : ↥W, Multiplicative.toAdd (D.E (conjAct W ⟨ℓ, D.le_normalizer hℓ⟩ v)) =
      D.conj ⟨ℓ, D.le_normalizer hℓ⟩ (Multiplicative.toAdd (D.E v)) :=
    fun v => (NatL2Data.conj_apply D _ v).symm
  have hR : ∀ x : Fin 2 → D.K, D.conj ⟨ℓ, D.le_normalizer hℓ⟩ x =
      (D.rho ⟨ℓ, hℓ⟩ : Matrix.SpecialLinearGroup (Fin 2) D.K).1.mulVec x :=
    fun x => D.conj_eq_rho ⟨ℓ, hℓ⟩ x
  rw [scalMul_apply, hA, hA, scalMul_apply, hR, hR, Matrix.mulVec_smul]

end NatL2Data


namespace NatL2Data

variable {L W V' : Subgroup G}

theorem irreducible_of_transport (Ψ : ↥W ≃* ↥V') (hWL : L ≤ Subgroup.normalizer (W : Set G))
    (hV' : L ≤ Subgroup.normalizer (V' : Set G))
    (hΨ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W),
      Ψ (conjAct W ⟨ℓ, hWL hℓ⟩ w) = conjAct V' ⟨ℓ, hV' hℓ⟩ (Ψ w))
    (hirr : ∀ X : Subgroup G, X ≤ W → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W) :
    ∀ X : Subgroup G, X ≤ V' → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = V' := by
  intro X hXV hLX
  let Y : Subgroup ↥W := (X.subgroupOf V').comap Ψ.toMonoidHom
  let Y' : Subgroup G := Y.map W.subtype
  have hmem : ∀ w : ↥W, (w : G) ∈ Y' ↔ ((Ψ w : ↥V') : G) ∈ X := by
    intro w
    constructor
    · rintro ⟨y, hy, hyw⟩
      have hyw' : y = w := Subtype.ext hyw
      subst hyw'
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hy)
    · intro h
      exact ⟨w, Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr h), rfl⟩
  have hY'W : Y' ≤ W := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hclaim : ∀ ℓ : G, ℓ ∈ L → ∀ x : G, x ∈ Y' → ℓ * x * ℓ⁻¹ ∈ Y' := by
    intro ℓ hℓ x hx
    obtain ⟨w, hwx⟩ : ∃ w : ↥W, (w : G) = x := by
      obtain ⟨y, _, hyx⟩ := hx
      exact ⟨y, hyx⟩
    subst hwx
    have hΨw : ((Ψ w : ↥V') : G) ∈ X := (hmem w).mp hx
    have hconj : ((conjAct W ⟨ℓ, hWL hℓ⟩ w : ↥W) : G) = ℓ * (w : G) * ℓ⁻¹ :=
      conjAct_apply_coe ⟨ℓ, hWL hℓ⟩ w
    rw [← hconj, hmem, hΨ ℓ hℓ w, conjAct_apply_coe ⟨ℓ, hV' hℓ⟩ (Ψ w)]
    exact (Subgroup.mem_normalizer_iff.mp (hLX hℓ) _).mp hΨw
  have hLY' : L ≤ Subgroup.normalizer (Y' : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hclaim ℓ hℓ x
    · intro hx
      have := hclaim ℓ⁻¹ (L.inv_mem hℓ) _ hx
      simpa [mul_assoc] using this
  rcases hirr Y' hY'W hLY' with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V' := hXV hx
    have hwY : (Ψ.symm ⟨x, hxV⟩ : G) ∈ Y' := (hmem _).mpr (by simpa using hx)
    rw [h, Subgroup.mem_bot] at hwY
    have hw : Ψ.symm ⟨x, hxV⟩ = 1 := Subtype.ext hwY
    have hx1 : x = ((Ψ (Ψ.symm ⟨x, hxV⟩) : ↥V') : G) := by simp
    rw [hw, map_one] at hx1
    rw [Subgroup.mem_bot, hx1]
    rfl
  · right
    apply le_antisymm hXV
    intro v hv
    have hwY : ((Ψ.symm ⟨v, hv⟩ : ↥W) : G) ∈ Y' := by
      rw [h]
      exact (Ψ.symm ⟨v, hv⟩).2
    have hΨw := (hmem _).mp hwY
    have hv' : ((Ψ (Ψ.symm ⟨v, hv⟩) : ↥V') : G) = v := by simp
    rwa [hv'] at hΨw

end NatL2Data

theorem exists_diag {L W₁ W₂ S : Subgroup G} {n : ℕ} (D₁ : NatL2Data L W₁ n)
    (D₂ : NatL2Data L W₂ n) (hSL : S ≤ L) (hD₁ : D₁.SylowAdapted S) (hD₂ : D₂.SylowAdapted S)
    (hsum : W₁ ⊓ W₂ = ⊥) (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a)
    (hker : ∀ ℓ ∈ L, ℓ ∈ Subgroup.centralizer (W₁ : Set G) ↔
      ℓ ∈ Subgroup.centralizer (W₂ : Set G))
    (hirr₁ : ∀ X : Subgroup G, X ≤ W₁ → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W₁)
    {z₁ z₂ : G} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂) (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1)
    (hC₁ : z₁ ∈ Subgroup.centralizer (S : Set G)) (hC₂ : z₂ ∈ Subgroup.centralizer (S : Set G)) :
    ∃ Γ : Subgroup G, z₁ * z₂ ∈ Γ ∧ Γ ≤ W₁ ⊔ W₂ ∧ L ≤ Subgroup.normalizer (Γ : Set G) ∧
      (∀ X : Subgroup G, X ≤ Γ → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Γ) ∧
      ∃ D : NatL2Data L Γ n, D.SylowAdapted S := by
  obtain ⟨φ₀, hφ₀⟩ := NatL2Data.exists_mulEquiv_ch6 D₁ D₂ hker
  have hcen : ∀ x : ↥W₁, (x : G) ∈ Subgroup.centralizer (S : Set G) →
      ((φ₀ x : ↥W₂) : G) ∈ Subgroup.centralizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have hxs : conjAct W₁ ⟨s, D₁.le_normalizer (hSL hs)⟩ x = x := by
      apply Subtype.ext
      rw [conjAct_apply_coe]
      have := hx s hs
      calc s * (x : G) * s⁻¹ = (x * s) * s⁻¹ := by rw [← this]
        _ = x := by group
    have h := hφ₀ ⟨s, hSL hs⟩ x
    rw [hxs] at h
    have h2 : s * ((φ₀ x : ↥W₂) : G) * s⁻¹ = ((φ₀ x : ↥W₂) : G) := by
      have := congrArg (fun y : ↥W₂ => (y : G)) h.symm
      simp only [conjAct_apply_coe] at this
      exact this
    calc s * ((φ₀ x : ↥W₂) : G) = (s * ((φ₀ x : ↥W₂) : G) * s⁻¹) * s := by group
      _ = ((φ₀ x : ↥W₂) : G) * s := by rw [h2]
  let z₁' : ↥W₁ := ⟨z₁, hz₁⟩
  let z₂' : ↥W₂ := ⟨z₂, hz₂⟩
  obtain ⟨a, ha⟩ := (NatL2Data.mem_centralizer_iff_line D₂ hSL hD₂ (φ₀ z₁')).mp (hcen z₁' hC₁)
  obtain ⟨a₂, ha₂⟩ := (NatL2Data.mem_centralizer_iff_line D₂ hSL hD₂ z₂').mp hC₂
  have ha0 : a ≠ 0 := by
    intro h0
    apply hz₁1
    have h1 : φ₀ z₁' = 1 := by
      apply D₂.E.injective
      apply Multiplicative.toAdd.injective
      rw [ha, h0]
      ext i
      fin_cases i <;> simp
    have := φ₀.injective (h1.trans (map_one φ₀).symm)
    exact congrArg Subtype.val this
  have ha20 : a₂ ≠ 0 := by
    intro h0
    apply hz₂1
    have h1 : z₂' = 1 := by
      apply D₂.E.injective
      apply Multiplicative.toAdd.injective
      rw [ha₂, h0]
      ext i
      fin_cases i <;> simp
    exact congrArg Subtype.val h1
  let cc : D₂.K := a₂ * a⁻¹
  have hcc : cc ≠ 0 := mul_ne_zero ha20 (inv_ne_zero ha0)
  let φ : ↥W₁ ≃* ↥W₂ := φ₀.trans (NatL2Data.scalMul D₂ cc hcc)
  have hφ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W₁),
      φ (conjAct W₁ ⟨ℓ, D₁.le_normalizer hℓ⟩ w) = conjAct W₂ ⟨ℓ, D₂.le_normalizer hℓ⟩ (φ w) := by
    intro ℓ hℓ w
    have h1 := hφ₀ ⟨ℓ, hℓ⟩ w
    show NatL2Data.scalMul D₂ cc hcc (φ₀ (conjAct W₁ ⟨ℓ, D₁.le_normalizer hℓ⟩ w)) = _
    rw [h1, NatL2Data.scalMul_conj D₂ cc hcc ℓ hℓ]
    rfl
  have hφz : φ z₁' = z₂' := by
    apply D₂.E.injective
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (D₂.E (NatL2Data.scalMul D₂ cc hcc (φ₀ z₁'))) = _
    rw [NatL2Data.scalMul_apply, ha, ha₂]
    have hcc' : cc * a = a₂ := by
      simp only [cc]
      rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    ext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul]
      simp [hcc']
    · simp
  let f : ↥W₁ →* G := MonoidHom.mk' (fun w => (w : G) * ((φ w : ↥W₂) : G)) (by
    intro w w'
    have hc := hcomm (w' : G) w'.2 ((φ w : ↥W₂) : G) (φ w).2
    simp only [map_mul, Subgroup.coe_mul]
    calc (w : G) * (w' : G) * (((φ w : ↥W₂) : G) * ((φ w' : ↥W₂) : G))
        = (w : G) * ((w' : G) * ((φ w : ↥W₂) : G)) * ((φ w' : ↥W₂) : G) := by group
      _ = (w : G) * (((φ w : ↥W₂) : G) * (w' : G)) * ((φ w' : ↥W₂) : G) := by rw [hc]
      _ = (w : G) * ((φ w : ↥W₂) : G) * ((w' : G) * ((φ w' : ↥W₂) : G)) := by group)
  have hf : ∀ w : ↥W₁, f w = (w : G) * ((φ w : ↥W₂) : G) := fun w => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [hf] at hw
    have h2 : (w : G) = ((φ w : ↥W₂) : G)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hmem : (w : G) ∈ W₁ ⊓ W₂ := ⟨w.2, by rw [h2]; exact W₂.inv_mem (φ w).2⟩
    rw [hsum, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hf_conj : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W₁),
      f (conjAct W₁ ⟨ℓ, D₁.le_normalizer hℓ⟩ w) = ℓ * f w * ℓ⁻¹ := by
    intro ℓ hℓ w
    rw [hf, hf, hφ ℓ hℓ w]
    simp only [conjAct_apply_coe]
    group
  have key : ∀ ℓ : G, ℓ ∈ L → ∀ x ∈ f.range, ℓ * x * ℓ⁻¹ ∈ f.range := by
    intro ℓ hℓ x hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨conjAct W₁ ⟨ℓ, D₁.le_normalizer hℓ⟩ w, hf_conj ℓ hℓ w⟩
  have hΓ : L ≤ Subgroup.normalizer (f.range : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key ℓ hℓ x
    · intro hx
      have h1 := key ℓ⁻¹ (L.inv_mem hℓ) _ hx
      have e : ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹⁻¹ = x := by group
      rw [e] at h1
      exact h1
  have hΨ : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (w : ↥W₁),
      (MonoidHom.ofInjective hfinj) (conjAct W₁ ⟨ℓ, D₁.le_normalizer hℓ⟩ w) =
        conjAct f.range ⟨ℓ, hΓ hℓ⟩ ((MonoidHom.ofInjective hfinj) w) := by
    intro ℓ hℓ w
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact hf_conj ℓ hℓ w
  refine ⟨f.range, ?_, ?_, hΓ, ?_, ?_⟩
  · refine ⟨z₁', ?_⟩
    show (z₁ : G) * ((φ z₁' : ↥W₂) : G) = z₁ * z₂
    rw [hφz]
  · rintro _ ⟨w, rfl⟩
    exact (W₁ ⊔ W₂).mul_mem (Subgroup.mem_sup_left w.2) (Subgroup.mem_sup_right (φ w).2)
  · intro X hXΓ hLX
    exact NatL2Data.irreducible_of_transport (MonoidHom.ofInjective hfinj) D₁.le_normalizer hΓ hΨ
      hirr₁ X hXΓ hLX
  · exact ⟨D₁.transport (MonoidHom.ofInjective hfinj) hΓ hΨ,
      NatL2Data.sylowAdapted_transport D₁ (MonoidHom.ofInjective hfinj) hΓ hΨ hD₁⟩

end CFSG.Quasithin.H13
