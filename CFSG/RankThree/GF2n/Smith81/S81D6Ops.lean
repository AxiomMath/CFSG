module

public import CFSG.RankThree.GF2n.Smith81.S81D6W

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

@[expose] def shiftW (γ : Fin (Tag.rank .E7) → ℤ) (a : Idx0) : Idx0 :=
  if h : shift γ (a : Fin e7Data.d) ∈ idx0 then ⟨shift γ (a : Fin e7Data.d), h⟩ else a

theorem shift_mem_idx0 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) {a : Fin e7Data.d}
    (ha : a ∈ idx0) (h : pr a γ = -1) : shift γ a ∈ idx0 := by
  rw [mem_idx0] at ha ⊢
  rw [pr_theta_shift_perp hγ h]
  exact ha

theorem shiftW_val {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) {a : Idx0}
    (h : pr (a : Fin e7Data.d) γ = -1) : ((shiftW γ a : Idx0) : Fin e7Data.d) = shift γ a := by
  unfold shiftW
  rw [dif_pos (shift_mem_idx0 hγ a.2 h)]

@[expose] def EWfun (γ : Fin (Tag.rank .E7) → ℤ) (w : W K) (b : Idx0) : K :=
  if pr (b : Fin e7Data.d) γ = 1 then w (shiftW (-γ) b) else 0

@[expose] def EW (K : Type) [Field K] (γ : Fin (Tag.rank .E7) → ℤ) : Module.End K (W K) where
  toFun w := Finsupp.equivFunOnFinite.symm (EWfun γ w)
  map_add' v w := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply, EWfun]
    split_ifs <;> simp
  map_smul' c v := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, EWfun]
    split_ifs <;> simp

theorem EW_apply (γ : Fin (Tag.rank .E7) → ℤ) (w : W K) (b : Idx0) :
    EW K γ w b = if pr (b : Fin e7Data.d) γ = 1 then w (shiftW (-γ) b) else 0 := by
  simp [EW, EWfun]

theorem emb_EW [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (w : W K) :
    emb K (EW K γ w) = e7Data.rootOp K γ (emb K w) := by
  have hγr : IsRoot .E7 γ := hγ.1
  have hnγ : -γ ∈ Perp := neg_mem_Perp hγ
  ext b
  rw [rootOp_apply hγr]
  by_cases hb : b ∈ idx0
  · obtain ⟨a, rfl⟩ : ∃ a : Idx0, (a : Fin e7Data.d) = b := ⟨⟨b, hb⟩, rfl⟩
    rw [emb_apply_coe, EW_apply]
    by_cases h1 : pr (a : Fin e7Data.d) γ = 1
    · rw [if_pos h1, if_pos h1]
      have h2 : pr (a : Fin e7Data.d) (-γ) = -1 := by rw [pr_neg, h1]
      have h4 := emb_apply_coe w (shiftW (-γ) a)
      rw [shiftW_val hnγ h2] at h4
      exact h4.symm
    · rw [if_neg h1, if_neg h1]
  · rw [emb_apply_of_not_mem _ hb]
    by_cases h1 : pr b γ = 1
    · rw [if_pos h1]
      have h2 : pr b (-γ) = -1 := by rw [pr_neg, h1]
      have h3 : shift (-γ) b ∉ idx0 := fun h => hb (by
        rw [mem_idx0] at h ⊢
        rw [← pr_theta_shift_perp hnγ h2]
        exact h)
      exact (emb_apply_of_not_mem w h3).symm
    · rw [if_neg h1]

theorem EW_mul_self [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) :
    EW K γ * EW K γ = 0 := by
  apply LinearMap.ext
  intro w
  apply emb_injective
  rw [Module.End.mul_apply, emb_EW hγ, emb_EW hγ, ← Module.End.mul_apply,
    e7Data_valid.rootOp_mul_self]
  simp

theorem EW_single [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (a : Idx0) :
    EW K γ (Finsupp.single a 1) =
      if pr (a : Fin e7Data.d) γ = -1 then Finsupp.single (shiftW γ a) 1 else 0 := by
  apply emb_injective
  rw [emb_EW hγ, emb_single, rootOp_single hγ.1]
  by_cases h : pr (a : Fin e7Data.d) γ = -1
  · rw [if_pos h, if_pos h, emb_single, shiftW_val hγ h]
  · rw [if_neg h, if_neg h]
    simp

theorem EW_mul_self_apply [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (w : W K) :
    EW K γ (EW K γ w) = 0 := by
  have h := LinearMap.congr_fun (EW_mul_self hγ) w
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h

@[expose] def xuWUnit [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K) :
    (Module.End K (W K))ˣ where
  val := 1 + c • EW K γ
  inv := 1 - c • EW K γ
  val_inv := by
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.smul_apply, map_sub, map_smul, EW_mul_self_apply hγ,
      smul_zero, sub_zero]
    abel_nf
  inv_val := by
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul, EW_mul_self_apply hγ,
      smul_zero, add_zero]
    abel_nf

theorem xuWUnit_val [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K) :
    (xuWUnit hγ c : Module.End K (W K)) = 1 + c • EW K γ := rfl

theorem xuWUnit_apply [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K) (w : W K) :
    (xuWUnit hγ c : Module.End K (W K)) w = w + c • EW K γ w := by
  rw [xuWUnit_val]
  simp

theorem xuWUnit_apply_coord [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K)
    (w : W K) (b : Idx0) :
    (xuWUnit hγ c : Module.End K (W K)) w b =
      w b + c * (if pr (b : Fin e7Data.d) γ = 1 then w (shiftW (-γ) b) else 0) := by
  rw [xuWUnit_apply, Finsupp.add_apply, Finsupp.smul_apply, EW_apply, smul_eq_mul]

theorem xuWUnit_induces [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K) :
    Induces (xuWUnit hγ c) (e7Data_valid.xu K γ c) := fun w => by
  rw [xuWUnit_apply, map_add, map_smul, emb_EW hγ, e7Data_valid.xu_apply]

theorem xuWUnit_mem_LamW [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K) :
    xuWUnit hγ c ∈ LamW K :=
  ⟨_, xu_mem_Lam hγ c, xuWUnit_induces hγ c⟩

@[expose] def restr (l : Module.End K (V K)) : Module.End K (W K) where
  toFun w := Finsupp.equivFunOnFinite.symm fun b : Idx0 => (l (emb K w)) (b : Fin e7Data.d)
  map_add' v w := by
    ext b
    simp
  map_smul' c v := by
    ext b
    simp

theorem emb_restr {l : Module.End K (V K)} (hl : ∀ w : W K, l (emb K w) ∈ V0 K) (w : W K) :
    emb K (restr l w) = l (emb K w) := by
  ext b
  by_cases hb : b ∈ idx0
  · rw [show emb K (restr l w) b = restr l w ⟨b, hb⟩ from emb_apply_coe _ ⟨b, hb⟩]
    simp [restr]
  · rw [emb_apply_of_not_mem _ hb]
    exact ((mem_V0.1 (hl w)) b hb).symm

theorem exists_induces [CharP K 2] {l : (Module.End K (V K))ˣ} (hl : l ∈ Lam K) :
    ∃ g : (Module.End K (W K))ˣ, Induces g l := by
  have h1 : ∀ w : W K, (l : Module.End K (V K)) (emb K w) ∈ V0 K := fun w =>
    Lam_stabilizes_V0 hl (emb_mem_V0 w)
  have h2 : ∀ w : W K, ((l⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) (emb K w) ∈ V0 K :=
    fun w => Lam_stabilizes_V0 (inv_mem hl) (emb_mem_V0 w)
  refine ⟨⟨restr (l : Module.End K (V K)), restr ((l⁻¹ : (Module.End K (V K))ˣ) :
    Module.End K (V K)), ?_, ?_⟩, fun w => emb_restr h1 w⟩
  · apply LinearMap.ext
    intro w
    apply emb_injective
    rw [Module.End.mul_apply, emb_restr h1, emb_restr h2, ← Module.End.mul_apply,
      ← Units.val_mul]
    simp
  · apply LinearMap.ext
    intro w
    apply emb_injective
    rw [Module.End.mul_apply, emb_restr h2, emb_restr h1, ← Module.End.mul_apply,
      ← Units.val_mul]
    simp

@[expose] def resV0 (K : Type) [Field K] [CharP K 2] : ↥(Lam K) →* (Module.End K (W K))ˣ where
  toFun l := Classical.choose (exists_induces l.2)
  map_one' := by
    apply Induces.unique (Classical.choose_spec (exists_induces (1 : ↥(Lam K)).2))
    exact induces_one
  map_mul' a b := by
    apply Induces.unique (Classical.choose_spec (exists_induces (a * b).2))
    exact (Classical.choose_spec (exists_induces a.2)).mul
      (Classical.choose_spec (exists_induces b.2))

theorem resV0_induces [CharP K 2] (l : ↥(Lam K)) : Induces (resV0 K l) (l : (Module.End K (V K))ˣ) :=
  Classical.choose_spec (exists_induces l.2)

theorem mem_LamW_iff [CharP K 2] {g : (Module.End K (W K))ˣ} :
    g ∈ LamW K ↔ ∃ l : ↥(Lam K), resV0 K l = g := by
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨⟨l, hl⟩, Induces.unique (resV0_induces ⟨l, hl⟩) h⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l, l.2, resV0_induces l⟩

theorem isRootEltW_iff [CharP K 2] {x : (Module.End K (W K))ˣ} :
    IsRootEltW x ↔ ∃ g ∈ LamW K, ∃ β : Fin (Tag.rank .E7) → ℤ, ∃ hβ : β ∈ Perp, ∃ c : K, c ≠ 0 ∧
      x = g * xuWUnit hβ c * g⁻¹ := by
  constructor
  · rintro ⟨l, hl, β, hβ, c, hc, h⟩
    obtain ⟨g, hg⟩ := exists_induces hl
    refine ⟨g, ⟨l, hl, hg⟩, β, hβ, c, hc, ?_⟩
    exact Induces.unique h ((hg.mul (xuWUnit_induces hβ c)).mul hg.inv)
  · rintro ⟨g, ⟨l, hl, hg⟩, β, hβ, c, hc, rfl⟩
    exact ⟨l, hl, β, hβ, c, hc, (hg.mul (xuWUnit_induces hβ c)).mul hg.inv⟩

end CFSG.RankThree.GF2n.Smith81.D6Spin
