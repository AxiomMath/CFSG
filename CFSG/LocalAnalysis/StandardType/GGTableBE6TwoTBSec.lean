module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBLin
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CorFourTwoMore TableBExc.E6Three E6TwoPilot

namespace E6TwoTB

@[expose] def SecEltAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R) (W : Set R), τ.range = E ∧
    (∀ (L' : Type) [Group L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' →
        ∃ σ : (Fin k → Multiplicative (ZMod p)) →* L', ψ.comp σ = τ) ∧
    (∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E) ∧
    (∀ E' : Subgroup R, E' ≤ E → (∀ w ∈ W, ∀ e ∈ E', w * e * w⁻¹ ∈ E') → E' = ⊥ ∨ E' = E) ∧
    (∃ w ∈ W, ∃ e ∈ E, w * e * w⁻¹ ≠ e) ∧
    ∀ F : R → R, (∀ e ∈ E, F e ∈ E) → (∀ e ∈ E, ∀ e' ∈ E, F (e * e') = F e * F e') →
      (∀ w ∈ W, ∀ e ∈ E, F (w * e * w⁻¹) = w * F e * w⁻¹) → ∃ c : ℕ, ∀ e ∈ E, F e = e ^ c

theorem SecEltAt.of_map {p : ℕ} {R R' : Type} [Group R] [Group R'] (φ : R ≃* R')
    {E : Subgroup R} (h : SecEltAt p (E.map φ.toMonoidHom)) : SecEltAt p E := by
  obtain ⟨k, τ, W, hτE, hsec, hWE, hirr, ⟨w₀, hw₀, e₀, he₀, hwe₀⟩, hschur⟩ := h
  have hmem : ∀ x : R, φ x ∈ E.map φ.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => φ.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hmem' : ∀ x : R', x ∈ E.map φ.toMonoidHom ↔ φ.symm x ∈ E := fun x => by
    rw [← hmem, MulEquiv.apply_symm_apply]
  refine ⟨k, φ.symm.toMonoidHom.comp τ, φ.symm '' W, ?_, fun L' _ ψ hψ hker => ?_, ?_,
    fun E' hE' hinv' => ?_, ?_, fun F hFE hFmul hFW => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : φ x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨σ, hσ⟩ := hsec L' (φ.toMonoidHom.comp ψ) (φ.surjective.comp hψ) (fun l hl =>
      hker (by simpa [MonoidHom.mem_ker] using hl))
    refine ⟨σ, MonoidHom.ext fun f => ?_⟩
    have h1 := DFunLike.congr_fun hσ f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    rw [← h1, MulEquiv.symm_apply_apply]
  · rintro _ ⟨w, hw, rfl⟩ x hx
    rw [← hmem]
    simpa using hWE w hw (φ x) ((hmem x).mpr hx)
  · have hle : E'.map φ.toMonoidHom ≤ E.map φ.toMonoidHom := Subgroup.map_mono hE'
    have hinv'' : ∀ w ∈ W, ∀ x ∈ E'.map φ.toMonoidHom, w * x * w⁻¹ ∈ E'.map φ.toMonoidHom := by
      rintro w hw _ ⟨y, hy, rfl⟩
      refine ⟨_, hinv' (φ.symm w) ⟨w, hw, rfl⟩ y hy, ?_⟩
      simp
    rcases hirr _ hle hinv'' with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : φ x ∈ E'.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact this ▸ Subgroup.one_mem _
    · right
      refine le_antisymm hE' fun x hx => ?_
      have : φ x ∈ E'.map φ.toMonoidHom := h1 ▸ (hmem x).mpr hx
      obtain ⟨y, hy, hyx⟩ := this
      exact φ.injective hyx ▸ hy
  · refine ⟨φ.symm w₀, ⟨w₀, hw₀, rfl⟩, φ.symm e₀, (hmem' e₀).mp he₀, fun heq => hwe₀ ?_⟩
    have h1 := congrArg φ heq
    simpa using h1
  · obtain ⟨c, hc⟩ := hschur (fun y => φ (F (φ.symm y)))
      (fun y hy => (hmem _).mpr (by simpa using hFE _ ((hmem' y).mp hy)))
      (fun y hy y' hy' => by
        rw [map_mul, hFmul _ ((hmem' y).mp hy) _ ((hmem' y').mp hy'), map_mul])
      (fun w hw y hy => by
        have h1 := hFW (φ.symm w) ⟨w, hw, rfl⟩ (φ.symm y) ((hmem' y).mp hy)
        simp only [map_mul, map_inv] at h1 ⊢
        rw [h1]
        simp)
    refine ⟨c, fun x hx => ?_⟩
    have h1 := hc (φ x) ((hmem x).mpr hx)
    simp only [MulEquiv.symm_apply_apply] at h1
    apply φ.injective
    rw [h1, map_pow]

section E6

variable {K : Type} [Field K] [CharP K 2]


theorem conj_nE6Two (h2 : (2 : K) = 0) (i : Fin 4) (v : V) :
    nE6Two i * torusE6Two h2 (.ofAdd v) * (nE6Two i)⁻¹ =
      torusE6Two (K := K) h2 (.ofAdd (Function.update v i (-(v i)))) := by
  rw [nE6Two_conj_torus h2 i v, sub_refl_eq_update]

theorem conj_tE6Two (h2 : (2 : K) = 0) (v : V) :
    tE6Two K * torusE6Two h2 (.ofAdd v) * (tE6Two K)⁻¹ = torusE6Two h2 (.ofAdd (mtFun v)) := by
  rw [torusE6Two_mtAut h2, mtAut_ofAdd]

theorem conj_sE6Two (h2 : (2 : K) = 0) (v : V) :
    sE6Two K * torusE6Two h2 (.ofAdd v) * (sE6Two K)⁻¹ = torusE6Two h2 (.ofAdd (msFun v)) := by
  rw [torusE6Two_msAut h2, msAut_ofAdd]

variable (K) in
@[expose] noncomputable def weylSet : Set (adjointGroup .E6 K) :=
  {w | (∃ i : Fin 4, w = nE6Two i) ∨ w = tE6Two K ∨ w = sE6Two K}

theorem weylSet_conj_mem (h2 : (2 : K) = 0) {w : adjointGroup .E6 K} (hw : w ∈ weylSet K)
    {e : adjointGroup .E6 K} (he : e ∈ (torusE6Two h2).range) :
    w * e * w⁻¹ ∈ (torusE6Two h2).range := by
  obtain ⟨v, rfl⟩ := he
  rw [← ofAdd_toAdd v]
  rcases hw with ⟨i, rfl⟩ | rfl | rfl
  · rw [conj_nE6Two]
    exact ⟨_, rfl⟩
  · rw [conj_tE6Two]
    exact ⟨_, rfl⟩
  · rw [conj_sE6Two]
    exact ⟨_, rfl⟩

theorem exists_section (h2 : (2 : K) = 0) {L' : Type} [Group L'] (ψ : L' →* adjointGroup .E6 K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') :
    ∃ σ : (Fin 4 → Multiplicative (ZMod 3)) →* L',
      ψ.comp σ = TableBF4.piTorus (torusE6Two h2) := by
  have hcomm : ∀ x ∈ (TableBF4.piTorus (torusE6Two h2)).range.comap ψ,
      ∀ y ∈ (TableBF4.piTorus (torusE6Two h2)).range.comap ψ, x * y = y * x := by
    rw [TableBF4.range_piTorus]
    exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker Nat.prime_three
      (by norm_num) (torusE6Two h2) reflFunE6Two reflFunE6Two_single nE6Two
      (nE6Two_conj_torus h2)
  have hinvb : ∀ i : Fin 4, ∃ w : adjointGroup .E6 K,
      w * TableBSymp.torusBasis (TableBF4.piTorus (torusE6Two h2)) i * w⁻¹ =
        (TableBSymp.torusBasis (TableBF4.piTorus (torusE6Two h2)) i)⁻¹ := by
    intro i
    refine ⟨nE6Two i, ?_⟩
    rw [TableBF4.torusBasis_piTorus, nE6Two_conj_torus h2 i, reflFunE6Two_single, ← map_inv,
      ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  exact TableBF4.exists_torus_section_of_comm hψ hker (by decide)
    (TableBF4.piTorus (torusE6Two h2)) hcomm hinvb

theorem torus_irreducible (h2 : (2 : K) = 0) {E' : Subgroup (adjointGroup .E6 K)}
    (hle : E' ≤ (torusE6Two h2).range)
    (hinv : ∀ w ∈ weylSet K, ∀ e ∈ E', w * e * w⁻¹ ∈ E') :
    E' = ⊥ ∨ E' = (torusE6Two h2).range := by
  let G : AddSubgroup V :=
    { carrier := {v | torusE6Two h2 (.ofAdd v) ∈ E'}
      zero_mem' := by
        show torusE6Two h2 (.ofAdd 0) ∈ E'
        rw [ofAdd_zero, map_one]
        exact E'.one_mem
      add_mem' := fun {a b} ha hb => by
        show torusE6Two h2 (.ofAdd (a + b)) ∈ E'
        rw [ofAdd_add, map_mul]
        exact E'.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        show torusE6Two h2 (.ofAdd (-a)) ∈ E'
        rw [ofAdd_neg, show torusE6Two h2 (.ofAdd a)⁻¹ = (torusE6Two h2 (.ofAdd a))⁻¹ from
          map_inv _ _]
        exact E'.inv_mem ha }
  have key : ∀ (w : adjointGroup .E6 K) (g : V → V), w ∈ weylSet K →
      (∀ v, w * torusE6Two h2 (.ofAdd v) * w⁻¹ = torusE6Two h2 (.ofAdd (g v))) →
      ∀ v ∈ G, g v ∈ G := by
    intro w g hw hg v hv
    have h1 := hinv w hw _ hv
    rw [hg v] at h1
    exact h1
  rcases eq_bot_or_eq_top_of_invariant G
    (fun i v hv => key _ (fun v => Function.update v i (-(v i))) (Or.inl ⟨i, rfl⟩)
      (conj_nE6Two h2 i) v hv)
    (fun v hv => key _ mtFun (Or.inr (Or.inl rfl)) (conj_tE6Two h2) v hv)
    (fun v hv => key _ msFun (Or.inr (Or.inr rfl)) (conj_sE6Two h2) v hv) with hG | hG
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨x, rfl⟩ := hle he
    have hx : Multiplicative.toAdd x ∈ G := by
      show torusE6Two h2 (.ofAdd (Multiplicative.toAdd x)) ∈ E'
      rw [ofAdd_toAdd]
      exact he
    rw [hG, AddSubgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    have hx1 : x = 1 := by rw [← ofAdd_toAdd x, hx, ofAdd_zero]
    rw [hx1, map_one]
  · right
    refine le_antisymm hle ?_
    rintro _ ⟨x, rfl⟩
    have hx : Multiplicative.toAdd x ∈ G := by
      rw [hG]
      exact AddSubgroup.mem_top _
    change torusE6Two h2 (.ofAdd (Multiplicative.toAdd x)) ∈ E' at hx
    rwa [ofAdd_toAdd] at hx

theorem torus_nontrivial (h2 : (2 : K) = 0) :
    ∃ w ∈ weylSet K, ∃ e ∈ (torusE6Two h2).range, w * e * w⁻¹ ≠ e := by
  refine ⟨nE6Two 0, Or.inl ⟨0, rfl⟩, torusE6Two h2 (.ofAdd (Pi.single 0 1)), ⟨_, rfl⟩,
    fun h => ?_⟩
  rw [conj_nE6Two] at h
  have h1 := congrFun (Multiplicative.ofAdd.injective (torusE6Two_injective h2 h)) 0
  revert h1
  decide

theorem torus_schur (h2 : (2 : K) = 0) (F : adjointGroup .E6 K → adjointGroup .E6 K)
    (hFE : ∀ e ∈ (torusE6Two h2).range, F e ∈ (torusE6Two h2).range)
    (hFmul : ∀ e ∈ (torusE6Two h2).range, ∀ e' ∈ (torusE6Two h2).range, F (e * e') = F e * F e')
    (hFW : ∀ w ∈ weylSet K, ∀ e ∈ (torusE6Two h2).range, F (w * e * w⁻¹) = w * F e * w⁻¹) :
    ∃ c : ℕ, ∀ e ∈ (torusE6Two h2).range, F e = e ^ c := by
  have hex : ∀ v : V, ∃ v' : V, torusE6Two h2 (.ofAdd v') = F (torusE6Two h2 (.ofAdd v)) := by
    intro v
    obtain ⟨x, hx⟩ := hFE _ ⟨.ofAdd v, rfl⟩
    exact ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx⟩
  choose f hf using hex
  have hinj := torusE6Two_injective (K := K) h2
  have hadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    apply Multiplicative.ofAdd.injective
    apply hinj
    rw [hf, ofAdd_add, map_mul, ofAdd_add, map_mul, hf, hf]
    exact hFmul _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
  have hcomm : ∀ (w : adjointGroup .E6 K) (g : V → V), w ∈ weylSet K →
      (∀ v, w * torusE6Two h2 (.ofAdd v) * w⁻¹ = torusE6Two h2 (.ofAdd (g v))) →
      ∀ v, f (g v) = g (f v) := by
    intro w g hw hg v
    apply Multiplicative.ofAdd.injective
    apply hinj
    rw [hf, ← hg v, hFW w hw _ ⟨_, rfl⟩, ← hf v, hg]
  obtain ⟨c, hc⟩ := exists_smul_of_commute f hadd
    (fun i v => hcomm _ (fun v => Function.update v i (-(v i))) (Or.inl ⟨i, rfl⟩)
      (conj_nE6Two h2 i) v)
    (hcomm _ mtFun (Or.inr (Or.inl rfl)) (conj_tE6Two h2))
    (hcomm _ msFun (Or.inr (Or.inr rfl)) (conj_sE6Two h2))
  refine ⟨c.val, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcv : c • Multiplicative.toAdd x = c.val • Multiplicative.toAdd x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [← ofAdd_toAdd x, ← hf, hc, hcv, torusE6Two_nsmul h2]

theorem secEltAt_torus (h2 : (2 : K) = 0) : SecEltAt 3 (torusE6Two h2).range :=
  ⟨4, TableBF4.piTorus (torusE6Two h2), weylSet K, TableBF4.range_piTorus _,
    fun L' _ ψ hψ hker => exists_section h2 ψ hψ hker,
    fun _ hw _ he => weylSet_conj_mem h2 hw he,
    fun _ hle hinv => torus_irreducible h2 hle hinv,
    torus_nontrivial h2,
    fun F hFE hFmul hFW => torus_schur h2 F hFE hFmul hFW⟩

variable [Finite K]

theorem ggTorusIrredSecElt_adjoint_E6_two (hK : Nat.card K = 2) :
    GGTorusIrredSecElt 3 4 (adjointGroup .E6 K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro E hE h4 _
  obtain ⟨c, hc⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE h4
  exact SecEltAt.of_map (MulAut.conj c) (by rw [hc]; exact secEltAt_torus h2)

theorem ggTorusIrred_E6_two (hK : Nat.card K = 2) :
    GGTorusIrred 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggTorusIrred_of_irredSecElt Nat.prime_three (recipeID_subset_inn_E6_two hK)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggTorusIrredSecElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggTorusIrredSecElt_adjoint_E6_two hK))

end E6

end E6TwoTB

end CFSG.StandardType
