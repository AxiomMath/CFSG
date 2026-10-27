module

public import CFSG.Quasithin.Vol2.Ch9Sec4Fix
public import CFSG.Quasithin.Vol2.Ch9Lem942

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem centralizer_classify (h2 : n = 2) {m : G} (hm : m ∈ fsuM T L)
    (hU : 32 ≤ Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer ({m} : Set G))) :
    m ∈ Subgroup.centralizer (fsuV T I : Set G) ∨
      ∃ X₁ : Matrix (Fin 2) (Fin 2) K, X₁.det ≠ 0 ∧
        fsuV T I ⊓ Subgroup.centralizer ({m} : Set G) = inV e (Om4Pt.perpM X₁) ∧
        ∀ v ∈ fsuV T I, m * v * m⁻¹ * v⁻¹ ∈ inV e (Om4Pt.lineM X₁) := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set φ := bar e ⟨m, S.hMN hm⟩ with hφ
  have hmv : ∀ v ∈ fsuV T I, m * v * m⁻¹ ∈ fsuV T I := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.hMN hm) v).mp hv
  have hconj : ∀ (v : G) (hv : v ∈ fsuV T I), e ⟨m * v * m⁻¹, hmv v hv⟩ = φ (e ⟨v, hv⟩) :=
    fun v hv => S.e_conj_M e hm ⟨v, hv⟩ (hmv v hv)
  have hfix : ∀ (v : G) (hv : v ∈ fsuV T I),
      v ∈ Subgroup.centralizer ({m} : Set G) ↔ e ⟨v, hv⟩ ∈ Om4Pt.fixM φ := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff, Om4Pt.mem_fixM, ← hconj v hv]
    constructor
    · intro h
      congr 1
      apply Subtype.ext
      show m * v * m⁻¹ = v
      rw [← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val (e.injective h)
      have h1' : m * v * m⁻¹ = v := h1
      calc v * m = m * v * m⁻¹ * m := by rw [h1']
        _ = m * v := by group
  have hcard : 32 ≤ Nat.card (Om4Pt.fixM φ) := by
    refine hU.trans (Nat.card_le_card_of_injective
      (fun x : ↥(fsuV T I ⊓ Subgroup.centralizer ({m} : Set G)) =>
        (⟨e ⟨x, x.2.1⟩, (hfix x x.2.1).mp x.2.2⟩ : ↥(Om4Pt.fixM φ))) ?_)
    intro x y h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (congrArg (fun z : ↥(fsuV T I) => (z : G)) (e.injective h1))
  obtain ⟨A, B, τ, hform⟩ := hc.exists_form hm
  rcases Om4Pt.fix_classify hK4 A B τ hform hcard with h1 | ⟨X₁, hX₁, hfx, hcomm⟩
  · left
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h3 := hconj v hv
    rw [show φ = 1 from h1, MulAut.one_apply] at h3
    have h4 : m * v * m⁻¹ = v := congrArg Subtype.val (e.injective h3)
    calc v * m = m * v * m⁻¹ * m := by rw [h4]
      _ = m * v := by group
  · right
    refine ⟨X₁, hX₁, ?_, fun v hv => ?_⟩
    · ext v
      constructor
      · rintro ⟨hv, hvc⟩
        exact mem_inV.mpr ⟨hv, (hfx _).mp ((hfix v hv).mp hvc)⟩
      · intro hv
        obtain ⟨hvV, hvp⟩ := mem_inV.mp hv
        exact ⟨hvV, (hfix v hvV).mpr ((hfx _).mpr hvp)⟩
    · obtain ⟨c, hc'⟩ := hcomm (e ⟨v, hv⟩)
      have hmem : m * v * m⁻¹ * v⁻¹ ∈ fsuV T I :=
        (fsuV T I).mul_mem (hmv v hv) ((fsuV T I).inv_mem hv)
      refine mem_inV.mpr ⟨hmem, c, ?_⟩
      have e1 : (⟨m * v * m⁻¹ * v⁻¹, hmem⟩ : ↥(fsuV T I)) =
          ⟨m * v * m⁻¹, hmv v hv⟩ * (⟨v, hv⟩ : ↥(fsuV T I))⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_inv, hconj, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
      exact hc'

theorem three_lt_rParam (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four)
    (h612 : ASInputs.AS_E_6_12) (h1 : zQ T I = fsuV T I) (h2 : n = 2) :
    (3 : ℕ∞) < rParam (fsuV T I) := by
  classical
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hV2 : IsPGroup 2 ↥(fsuV T I) := S.isPGroup_fsuV
  have hVcard : Nat.card ↥(fsuV T I) = 256 := by
    rw [Nat.card_congr e.toEquiv, show Nat.card (Om4.VM K) = Nat.card (Fin 2 → Fin 2 → K) from rfl,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K), hK4]
    simp
  by_contra hle
  push Not at hle
  obtain ⟨U, hUV, hCU, hU3⟩ : ∃ U : Subgroup G, U ≤ fsuV T I ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      mQuot (fsuV T I) U ≤ 3 := by
    have hlt : rParam (fsuV T I) < 4 := lt_of_le_of_lt hle (by norm_num)
    unfold rParam at hlt
    obtain ⟨U, hU⟩ := iInf_lt_iff.mp hlt
    obtain ⟨⟨hUV, hCU⟩, hU2⟩ := iInf_lt_iff.mp hU
    have hm : mQuot (fsuV T I) U < 4 := by exact_mod_cast hU2
    exact ⟨U, hUV, hCU, by omega⟩
  have hUcard : 32 ≤ Nat.card U := by
    have h := card_eq_two_pow_mul hV2 hUV
    rw [hVcard] at h
    have h3 : 2 ^ mQuot (fsuV T I) U ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hU3
    nlinarith
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    omega
  have hr2 := S.two_le_rParam h37 h38 h39 h3228 hE610 h1
  have hCM : ¬ (fsuM T L ⊓ Subgroup.centralizer (U : Set G) =
      fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    intro heq
    have h3 := (h612 G T (fsuM T L) (fsuV T I) U (S.hypE61 h37 h38 h39 h3228) hU1 hUV heq
      (fun hle' => hCU (hle'.trans S.hMN))).2
    rw [h3] at hr2
    norm_num at hr2
  obtain ⟨m, ⟨hmM, hmU⟩, hmV⟩ : ∃ m ∈ fsuM T L ⊓ Subgroup.centralizer (U : Set G),
      m ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    by_contra hall
    push Not at hall
    exact hCM (le_antisymm (fun x hx => ⟨hx.1, hall x hx⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le hUV)))
  have hUC : U ≤ fsuV T I ⊓ Subgroup.centralizer ({m} : Set G) := fun u hu =>
    ⟨hUV hu, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hmU u hu)⟩
  rcases hc.centralizer_classify h2 hmM (hUcard.trans (Subgroup.card_le_of_le hUC)) with
    hmC | ⟨X₁, hX₁, hCm, -⟩
  · exact hmV hmC
  set X₂ := X₁ * !![(0 : K), 1; 1, 0] with hX₂
  have hX₁0 : X₁ ≠ 0 := fun h => hX₁ (by rw [h]; simp)
  have hX₂d : X₂.det ≠ 0 := by
    rw [hX₂, Matrix.det_mul, Matrix.det_fin_two_of]
    simpa using hX₁
  have hne : ∀ c : K, X₂ ≠ c • X₁ := by
    intro c h
    have h3 := congrArg (fun Y => X₁⁻¹ * Y) h
    simp only [hX₂, ← Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hX₁), Matrix.one_mul] at h3
    have h5 := congrFun₂ h3 0 1
    simp at h5
  have hX₂p : detPolarCh6 X₁ X₂ = 0 := by
    have h3 := Om4Pt.detPolar_mul_mul X₁ 1 1 !![(0 : K), 1; 1, 0]
    rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one] at h3
    rw [hX₂, h3]
    simp [detPolarCh6]
  have hX₁p : detPolarCh6 X₁ X₁ = 0 := by
    have h4 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [detPolarCh6]
    linear_combination (X₁ 0 0 * X₁ 1 1 + X₁ 0 1 * X₁ 1 0) * h4
  set U' : Subgroup (Om4.VM K) := (U.subgroupOf (fsuV T I)).map e.toMonoidHom with hU'
  have hU'card : Nat.card U' = Nat.card U := by
    rw [hU', Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  have hU'P : U' ≤ Om4Pt.perpM X₁ := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ inV e (Om4Pt.perpM X₁) := hCm ▸ hUC (Subgroup.mem_subgroupOf.mp hu)
    obtain ⟨hv, hp⟩ := mem_inV.mp hu'
    exact hp
  have hpoint : ∀ Y₁ : Matrix (Fin 2) (Fin 2) K, detPolarCh6 X₁ Y₁ = 0 → Y₁ ≠ 0 →
      ∃ w ∈ U, w ∈ inV e (Om4Pt.lineM Y₁) ∧ w ≠ 1 := by
    intro Y₁ hY hY0
    obtain ⟨c, hc0, hcU⟩ :=
      Om4Pt.exists_smul_mem_of_le_perpM hK4 hX₁0 hY hU'P (hU'card ▸ hUcard)
    obtain ⟨u, hu, hue⟩ := hcU
    have hue' : e u = Multiplicative.ofAdd (c • Y₁) := hue
    refine ⟨u, Subgroup.mem_subgroupOf.mp hu, mem_inV.mpr ⟨u.2, c, ?_⟩, ?_⟩
    · show Multiplicative.toAdd (e u) = c • Y₁
      rw [hue', toAdd_ofAdd]
    · intro h1
      have h3 : u = 1 := Subtype.ext h1
      rw [h3, map_one] at hue'
      have h4 : c • Y₁ = 0 := by
        have := congrArg Multiplicative.toAdd hue'
        rw [toAdd_ofAdd, toAdd_one] at this
        exact this.symm
      exact hY0 ((smul_eq_zero.mp h4).resolve_left hc0)
  obtain ⟨v, hvU, hvW, hv1⟩ := hpoint X₁ hX₁p hX₁0
  obtain ⟨u, huU, huW, hu1⟩ := hpoint X₂ hX₂p (fun h => hX₂d (by rw [h]; simp))
  apply hCU
  have hle := hc.centralizer_pair_le h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h2
    hX₁ hX₂d hne hvW hv1 huW hu1
  refine le_trans ?_ (hle.trans S.hMN)
  exact le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvU))
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU))

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
