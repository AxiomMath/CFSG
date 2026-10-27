module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.Timmesfeld.Transvection.ModelSUTransitive

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {F : Type} [Field F] {m : ℕ}

structure SUThetaFacts (σ : F ≃+* F) (a d : Fin m → F) (T : Subgroup (SU σ m)) : Prop where
  decomp : ∀ {x : SU σ m}, x ∈ uRad σ a →
    suMat σ m x *ᵥ d = d + radVec σ a d x + uForm σ d (suMat σ m x *ᵥ d) • a
  mem_perp : ∀ g : SU σ m, radVec σ a d g ∈ perpPair σ a d
  mul : ∀ {x y : SU σ m}, x ∈ uRad σ a → y ∈ uRad σ a →
    radVec σ a d (x * y) = radVec σ a d x + radVec σ a d y
  one : radVec σ a d 1 = 0
  inv : ∀ {x : SU σ m}, x ∈ uRad σ a → radVec σ a d x⁻¹ = - radVec σ a d x
  eq_zero_iff : ∀ {x : SU σ m}, x ∈ uRad σ a → (radVec σ a d x = 0 ↔ x ∈ T)
  exists_eq : ∀ {w : Fin m → F}, w ∈ perpPair σ a d → ∃ x ∈ uRad σ a, radVec σ a d x = w
  exists_eq_iso : ∀ {w : Fin m → F}, w ∈ perpPair σ a d → uForm σ w w = 0 →
    ∃ x ∈ uRad σ a, suMat σ m x *ᵥ d = d + w
  comm_mem : ∀ {x y : SU σ m}, x ∈ uRad σ a → y ∈ uRad σ a → ⁅x, y⁆ ∈ T
  conj : ∀ {g x : SU σ m} {μ : F}, suMat σ m g *ᵥ a = μ • a → x ∈ uRad σ a →
    radVec σ a d (g * x * g⁻¹) = σ μ • levAct σ a d g (radVec σ a d x)
  levAct_mul : ∀ {g g' : SU σ m}, g ∈ uLine σ a → g' ∈ uLine σ a → ∀ {w : Fin m → F},
    w ∈ perpPair σ a d → levAct σ a d (g * g') w = levAct σ a d g (levAct σ a d g' w)
  levAct_one : ∀ {w : Fin m → F}, w ∈ perpPair σ a d → levAct σ a d 1 w = w
  levAct_mem : ∀ {g : SU σ m}, g ∈ uLine σ a → ∀ {w : Fin m → F}, w ∈ perpPair σ a d →
    levAct σ a d g w ∈ perpPair σ a d
  levAct_add : ∀ (g : SU σ m) (w w' : Fin m → F),
    levAct σ a d g (w + w') = levAct σ a d g w + levAct σ a d g w'
  levAct_smul : ∀ (g : SU σ m) (c : F) (w : Fin m → F),
    levAct σ a d g (c • w) = c • levAct σ a d g w
  mem_uRad : ∀ {x : SU σ m}, suMat σ m x *ᵥ a = a →
    (∀ w : Fin m → F, w ∈ perpPair σ a d → levAct σ a d x w = w) → x ∈ uRad σ a
  transv_a : ∀ {v : Fin m → F} {c : F} {t : SU σ m}, v ∈ perpPair σ a d →
    suMat σ m t = uTrans σ v c → suMat σ m t *ᵥ a = a
  levAct_transv : ∀ {v : Fin m → F} {c : F} {t : SU σ m}, v ∈ perpPair σ a d →
    uForm σ v v = 0 → suMat σ m t = uTrans σ v c → ∀ {w : Fin m → F}, w ∈ perpPair σ a d →
      levAct σ a d t w = w + (c * uForm σ v w) • v

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem projPair_of_uForm_eq_zero {a d x : Fin m → F} (h : uForm σ a x = 0) :
    projPair σ a d x = x - uForm σ d x • a := by
  rw [projPair, h, zero_smul, sub_zero]

theorem radVec_mem (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (g : SU σ m) :
    radVec σ a d g ∈ perpPair σ a d :=
  projPair_mem hσ haa hdd had _

theorem suMat_mulVec_d_eq_radVec {a d : Fin m → F} (had : uForm σ a d = 1) {x : SU σ m}
    (hx : x ∈ uRad σ a) :
    suMat σ m x *ᵥ d = d + radVec σ a d x + uForm σ d (suMat σ m x *ᵥ d) • a := by
  have h1 : uForm σ a (suMat σ m x *ᵥ d) = 1 := by
    have h2 := uForm_mulVec σ x a d
    rw [hx.1, had] at h2
    exact h2
  rw [radVec, projPair, h1, one_smul]
  abel

theorem exists_suMat_mulVec_d_eq_radVec {a d : Fin m → F} (had : uForm σ a d = 1)
    {x : SU σ m} (hx : x ∈ uRad σ a) :
    ∃ c : F, suMat σ m x *ᵥ d = d + radVec σ a d x + c • a :=
  ⟨_, suMat_mulVec_d_eq_radVec had hx⟩

theorem radVec_eq_of_suMat_mulVec_eq (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g : SU σ m}
    {w : Fin m → F} (hw : w ∈ perpPair σ a d) {c : F}
    (h : suMat σ m g *ᵥ d = d + w + c • a) : radVec σ a d g = w := by
  rw [radVec, h, projPair_add_smul_a hσ haa had, projPair_add, projPair_d hdd had,
    projPair_of_mem hw, zero_add]

theorem radVec_mul_of_mem_uRad (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {x y : SU σ m}
    (hx : x ∈ uRad σ a) (hy : y ∈ uRad σ a) :
    radVec σ a d (x * y) = radVec σ a d x + radVec σ a d y := by
  obtain ⟨c₁, hc₁⟩ := exists_suMat_mulVec_d_eq_radVec had hy
  obtain ⟨c₂, hc₂⟩ := exists_suMat_mulVec_d_eq_radVec had hx
  obtain ⟨δ, hδ⟩ := hx.2 (radVec σ a d y) (radVec_mem hσ haa hdd had y).1
  refine radVec_eq_of_suMat_mulVec_eq hσ haa hdd had
    (add_mem (radVec_mem hσ haa hdd had x) (radVec_mem hσ haa hdd had y)) (c := c₂ + δ + c₁) ?_
  rw [map_mul, ← mulVec_mulVec, hc₁, mulVec_add, mulVec_add, mulVec_smul, hx.1, hδ, hc₂,
    add_smul, add_smul]
  abel

theorem radVec_one_eq_zero {a d : Fin m → F} (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) : radVec σ a d 1 = 0 := by
  rw [radVec, map_one, one_mulVec, projPair_d hdd had]

theorem radVec_inv_of_mem_uRad (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {x : SU σ m}
    (hx : x ∈ uRad σ a) : radVec σ a d x⁻¹ = - radVec σ a d x := by
  have h := radVec_mul_of_mem_uRad hσ haa hdd had hx (inv_mem hx)
  rw [mul_inv_cancel, radVec_one_eq_zero hdd had] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem radVec_eq_zero_iff_mem (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) {x : SU σ m} (hx : x ∈ uRad σ a) :
    radVec σ a d x = 0 ↔ x ∈ T := by
  have hda := uForm_swap_eq_one hσ had
  constructor
  · intro h0
    obtain ⟨μ, hμ⟩ : ∃ μ : F, suMat σ m x *ᵥ d = d + μ • a := by
      refine ⟨uForm σ d (suMat σ m x *ᵥ d), ?_⟩
      have h1 := suMat_mulVec_d_eq_radVec had hx
      rwa [h0, add_zero] at h1
    have htr0 : μ + σ μ = 0 := by
      have h1 := uForm_mulVec σ x d d
      rw [hμ, hdd] at h1
      simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hdd, haa,
        had, hda] at h1
      linear_combination h1
    have hmat : suMat σ m x = uTrans σ a μ := by
      refine Matrix.ext_iff_mulVec.2 fun v => ?_
      have hau : uForm σ a (v - uForm σ a v • d) = 0 := by
        rw [uForm_sub_right, uForm_smul_right, had, mul_one, sub_self]
      obtain ⟨c, hc⟩ := hx.2 _ hau
      have hc0 : c = 0 := by
        have h2 := uForm_mulVec σ x d (v - uForm σ a v • d)
        rw [hμ, hc] at h2
        simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hda,
          hau] at h2
        linear_combination h2
      have h3 : suMat σ m x *ᵥ v =
          suMat σ m x *ᵥ (v - uForm σ a v • d) + uForm σ a v • (suMat σ m x *ᵥ d) := by
        rw [← mulVec_smul, ← mulVec_add, sub_add_cancel]
      rw [h3, hc, hc0, hμ, uTrans_mulVec]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact (hT.1 x).2 ⟨μ, htr0, hmat⟩
  · intro hxT
    obtain ⟨c, -, hc⟩ := (hT.1 x).1 hxT
    rw [radVec, hc, uTrans_mulVec, had, mul_one, projPair_add_smul_a hσ haa had,
      projPair_d hdd had]

theorem exists_mem_uRad_mulVec_d_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d w : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) (hw : w ∈ perpPair σ a d) {μ : F}
    (hμ : μ + σ μ = uForm σ w w) :
    ∃ x ∈ uRad σ a, suMat σ m x *ᵥ d = d + w + μ • a := by
  obtain ⟨x, hx⟩ := exists_suMat_mulVec_eichler hσ haa hw.1 hμ
  have hwa : uForm σ w a = 0 := uForm_eq_zero_comm hσ hw.1
  have hwd : uForm σ w d = 0 := uForm_eq_zero_comm hσ hw.2
  refine ⟨x, ⟨?_, fun u hu => ⟨uForm σ w u, ?_⟩⟩, ?_⟩
  · rw [hx, haa, hwa, zero_smul, zero_smul, add_zero, add_zero]
  · rw [hx, hu, zero_smul, add_zero]
  · rw [hx, had, hwd, one_smul, zero_smul, add_zero, add_assoc]

theorem exists_mem_uRad_radVec_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d w : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (hw : w ∈ perpPair σ a d) :
    ∃ x ∈ uRad σ a, radVec σ a d x = w := by
  obtain ⟨μ, hμ⟩ := htr (uForm σ w w) (uForm_conj σ hσ w w)
  obtain ⟨x, hx, hxd⟩ := exists_mem_uRad_mulVec_d_eq hσ haa had hw hμ
  exact ⟨x, hx, radVec_eq_of_suMat_mulVec_eq hσ haa hdd had hw hxd⟩

theorem exists_mem_uRad_mulVec_d_eq_add [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d w : Fin m → F} (haa : uForm σ a a = 0) (had : uForm σ a d = 1)
    (hw : w ∈ perpPair σ a d) (hww : uForm σ w w = 0) :
    ∃ x ∈ uRad σ a, suMat σ m x *ᵥ d = d + w := by
  obtain ⟨x, hx, hxd⟩ := exists_mem_uRad_mulVec_d_eq hσ haa had hw (μ := 0)
    (by rw [map_zero, add_zero, hww])
  exact ⟨x, hx, by rw [hxd, zero_smul, add_zero]⟩

open scoped commutatorElement in
theorem commutatorElement_mem_of_mem_uRad (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) {x y : SU σ m} (hx : x ∈ uRad σ a)
    (hy : y ∈ uRad σ a) : ⁅x, y⁆ ∈ T := by
  have hxy : x * y ∈ uRad σ a := mul_mem hx hy
  have hxyx : x * y * x⁻¹ ∈ uRad σ a := mul_mem hxy (inv_mem hx)
  rw [commutatorElement_def]
  refine (radVec_eq_zero_iff_mem hσ haa hdd had hT (mul_mem hxyx (inv_mem hy))).1 ?_
  rw [radVec_mul_of_mem_uRad hσ haa hdd had hxyx (inv_mem hy),
    radVec_mul_of_mem_uRad hσ haa hdd had hxy (inv_mem hx),
    radVec_mul_of_mem_uRad hσ haa hdd had hx hy, radVec_inv_of_mem_uRad hσ haa hdd had hx,
    radVec_inv_of_mem_uRad hσ haa hdd had hy]
  abel

theorem radVec_conj_eq (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {g x : SU σ m} {μ : F}
    (hga : suMat σ m g *ᵥ a = μ • a) (hx : x ∈ uRad σ a) :
    radVec σ a d (g * x * g⁻¹) = σ μ • levAct σ a d g (radVec σ a d x) := by
  have hd' : uForm σ a (suMat σ m g⁻¹ *ᵥ d) = σ μ := by
    have h1 := uForm_mulVec σ g a (suMat σ m g⁻¹ *ᵥ d)
    rw [hga, suMat_mulVec_suMat_inv_mulVec, uForm_smul_left, had, mul_one] at h1
    exact h1.symm
  have hu₀ : uForm σ a (suMat σ m g⁻¹ *ᵥ d - σ μ • d) = 0 := by
    rw [uForm_sub_right, uForm_smul_right, had, mul_one, hd', sub_self]
  obtain ⟨c, hc⟩ := hx.2 _ hu₀
  obtain ⟨c₁, hc₁⟩ := exists_suMat_mulVec_d_eq_radVec had hx
  have h1 : suMat σ m x *ᵥ (suMat σ m g⁻¹ *ᵥ d) =
      suMat σ m g⁻¹ *ᵥ d + σ μ • radVec σ a d x + (σ μ * c₁ + c) • a := by
    have h2 : suMat σ m g⁻¹ *ᵥ d = σ μ • d + (suMat σ m g⁻¹ *ᵥ d - σ μ • d) :=
      (add_sub_cancel _ _).symm
    conv_lhs => rw [h2]
    rw [mulVec_add, mulVec_smul, hc, hc₁, smul_add, smul_add, smul_smul, add_smul]
    abel
  have h3 : suMat σ m (g * x * g⁻¹) *ᵥ d =
      d + σ μ • (suMat σ m g *ᵥ radVec σ a d x) + ((σ μ * c₁ + c) * μ) • a := by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, h1, mulVec_add, mulVec_add,
      mulVec_smul, mulVec_smul, suMat_mulVec_suMat_inv_mulVec, hga, smul_smul]
  conv_lhs => rw [radVec]
  rw [h3, projPair_add_smul_a hσ haa had, projPair_add, projPair_d hdd had, zero_add,
    projPair_smul]
  rfl

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem levAct_mem (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (g : SU σ m) (w : Fin m → F) :
    levAct σ a d g w ∈ perpPair σ a d :=
  projPair_mem hσ haa hdd had _

theorem levAct_add (a d : Fin m → F) (g : SU σ m) (w w' : Fin m → F) :
    levAct σ a d g (w + w') = levAct σ a d g w + levAct σ a d g w' := by
  rw [levAct, levAct, levAct, mulVec_add, projPair_add]

theorem levAct_smul (a d : Fin m → F) (g : SU σ m) (c : F) (w : Fin m → F) :
    levAct σ a d g (c • w) = c • levAct σ a d g w := by
  rw [levAct, levAct, mulVec_smul, projPair_smul]

theorem levAct_one_of_mem {a d w : Fin m → F} (hw : w ∈ perpPair σ a d) :
    levAct σ a d 1 w = w := by
  rw [levAct, map_one, one_mulVec, projPair_of_mem hw]

theorem uForm_mulVec_eq_zero_of_mem_uLine {a w : Fin m → F} {g : SU σ m}
    (hg : g ∈ uLine σ a) (hw : uForm σ a w = 0) : uForm σ a (suMat σ m g *ᵥ w) = 0 := by
  obtain ⟨μ, hμ, hga⟩ := hg
  have h1 := uForm_mulVec σ g a w
  rw [hga, uForm_smul_left, hw] at h1
  exact (mul_eq_zero.1 h1).resolve_left ((map_ne_zero σ).2 hμ)

theorem levAct_mul_of_mem_uLine (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) {g g' : SU σ m} (hg : g ∈ uLine σ a)
    (hg' : g' ∈ uLine σ a) {w : Fin m → F} (hw : w ∈ perpPair σ a d) :
    levAct σ a d (g * g') w = levAct σ a d g (levAct σ a d g' w) := by
  obtain ⟨μ, -, hμ⟩ := hg
  have h1 := uForm_mulVec_eq_zero_of_mem_uLine hg' hw.1
  have h3 : levAct σ a d g' w =
      suMat σ m g' *ᵥ w + (-uForm σ d (suMat σ m g' *ᵥ w)) • a := by
    rw [levAct, projPair_of_uForm_eq_zero h1, neg_smul, sub_eq_add_neg]
  show projPair σ a d (suMat σ m (g * g') *ᵥ w) =
    projPair σ a d (suMat σ m g *ᵥ levAct σ a d g' w)
  rw [h3, mulVec_add, mulVec_smul, hμ, smul_smul, projPair_add_smul_a hσ haa had, map_mul,
    mulVec_mulVec]

theorem mem_uRad_of_levAct_eq (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {x : SU σ m}
    (hxa : suMat σ m x *ᵥ a = a) (hx : ∀ w ∈ perpPair σ a d, levAct σ a d x w = w) :
    x ∈ uRad σ a := by
  refine ⟨hxa, fun u hu => ?_⟩
  have hw := projPair_mem hσ haa hdd had u
  have hpu : projPair σ a d u = u - uForm σ d u • a := projPair_of_uForm_eq_zero hu
  have h1 : uForm σ a (suMat σ m x *ᵥ projPair σ a d u) = 0 := by
    have h2 := uForm_mulVec σ x a (projPair σ a d u)
    rw [hxa, hw.1] at h2
    exact h2
  have h3 := hx _ hw
  rw [levAct, projPair_of_uForm_eq_zero (d := d) h1] at h3
  generalize uForm σ d (suMat σ m x *ᵥ projPair σ a d u) = e at h3
  have h5 := sub_eq_iff_eq_add.1 h3
  refine ⟨e, ?_⟩
  have h4 : suMat σ m x *ᵥ u = suMat σ m x *ᵥ projPair σ a d u + uForm σ d u • a := by
    rw [hpu, mulVec_sub, mulVec_smul, hxa, sub_add_cancel]
  rw [h4, h5, hpu]
  abel

theorem suMat_mulVec_a_eq_of_eq_uTrans (hσ : ∀ c, σ (σ c) = c) {a d v : Fin m → F}
    (hv : v ∈ perpPair σ a d) {c : F} {t : SU σ m} (ht : suMat σ m t = uTrans σ v c) :
    suMat σ m t *ᵥ a = a := by
  rw [ht, uTrans_mulVec, uForm_eq_zero_comm hσ hv.1, mul_zero, zero_smul, add_zero]

theorem levAct_eq_of_eq_uTrans {a d v : Fin m → F} (hv : v ∈ perpPair σ a d) {c : F}
    {t : SU σ m} (ht : suMat σ m t = uTrans σ v c) {w : Fin m → F}
    (hw : w ∈ perpPair σ a d) : levAct σ a d t w = w + (c * uForm σ v w) • v := by
  rw [levAct, ht, uTrans_mulVec, projPair_add, projPair_smul, projPair_of_mem hw,
    projPair_of_mem hv]

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suThetaFacts_holds [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) : SUThetaFacts σ a d T where
  decomp hx := suMat_mulVec_d_eq_radVec had hx
  mem_perp := radVec_mem hσ haa hdd had
  mul hx hy := radVec_mul_of_mem_uRad hσ haa hdd had hx hy
  one := radVec_one_eq_zero hdd had
  inv hx := radVec_inv_of_mem_uRad hσ haa hdd had hx
  eq_zero_iff hx := radVec_eq_zero_iff_mem hσ haa hdd had hT hx
  exists_eq hw := exists_mem_uRad_radVec_eq hσ htr haa hdd had hw
  exists_eq_iso hw hww := exists_mem_uRad_mulVec_d_eq_add hσ haa had hw hww
  comm_mem hx hy := commutatorElement_mem_of_mem_uRad hσ haa hdd had hT hx hy
  conj hga hx := radVec_conj_eq hσ haa hdd had hga hx
  levAct_mul hg hg' _ hw := levAct_mul_of_mem_uLine hσ haa had hg hg' hw
  levAct_one hw := levAct_one_of_mem hw
  levAct_mem {g} _ {w} _ := levAct_mem hσ haa hdd had g w
  levAct_add := levAct_add a d
  levAct_smul := levAct_smul a d
  mem_uRad hxa hx := mem_uRad_of_levAct_eq hσ haa hdd had hxa hx
  transv_a hv ht := suMat_mulVec_a_eq_of_eq_uTrans hσ hv ht
  levAct_transv hv _ ht _ hw := levAct_eq_of_eq_uTrans hv ht hw

end ModelRank

end CFSG.Timmesfeld.Transvection
