module

public import CFSG.Quasithin.MS93.ASC134NC5Count

public section

namespace CFSG.Quasithin.MS93.AS

open Matrix
open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

variable {F : Type} [Field F]

@[expose] def swap12 [CharP F 2] : SL3 F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    rw [Matrix.det_fin_three]
    simp [CharTwo.neg_eq]⟩

theorem coe_swap12 [CharP F 2] :
    ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

theorem swap12_mulVec_e0 [CharP F 2] :
    ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  rw [coe_swap12]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swap12_inv [CharP F 2] : (swap12 : SL3 F)⁻¹ = swap12 := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  change ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((swap12 : SL3 F) :
    Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_swap12]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mem_qPt_of_swap12 [CharP F 2] {g : SL3 F} (hg : g ∈ (sStar : Subgroup (SL3 F)))
    (hw : swap12 * g * swap12⁻¹ ∈ (sStar : Subgroup (SL3 F))) :
    g ∈ (qPt : Subgroup (SL3 F)) := by
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hg
  obtain ⟨a', b', c', h⟩ := mem_sStar_iff.mp hw
  have hc : c = 0 := by
    have := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F) 2 1) h
    rw [swap12_inv] at this
    change (uniTri a' b' c' : Matrix (Fin 3) (Fin 3) F) 2 1 =
      (((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (uniTri a b c : Matrix (Fin 3) (Fin 3) F) *
        ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F)) 2 1 at this
    rw [coe_uniTri, coe_uniTri, coe_swap12] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this.symm
  exact mem_qPt_iff.mpr ⟨a, b, by rw [hc]⟩

theorem le_sStar_of_isPGroup [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {P : Subgroup (SL3 F)} (hP : IsPGroup 2 P) (hSP : (sStar : Subgroup (SL3 F)) ≤ P) :
    P ≤ sStar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)).is_maximal' hP hSP |>.le

theorem le_qPt_of_normalized [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Y : Subgroup (SL3 F)} (hY : IsPGroup 2 Y)
    (hYn : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : Y ≤ qPt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYS : Y ≤ sStar := by
    have hN : (sStar : Subgroup (SL3 F)) ≤ Subgroup.normalizer (Y : Set (SL3 F)) :=
      fun s hs => by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        refine ⟨fun hy => hYn s (sStar_mulVec_e0 hs) y hy, fun hy => ?_⟩
        have := hYn s⁻¹ (sStar_mulVec_e0 (inv_mem hs)) _ hy
        simpa [mul_assoc] using this
    have h2 : IsPGroup 2 ↥(Y ⊔ sStar) := hY.to_sup_of_normal_left' (isPGroup_sStar hF) hN
    exact le_sup_left.trans (le_sStar_of_isPGroup hF h2 le_sup_right)
  intro y hy
  exact mem_qPt_of_swap12 (hYS hy) (hYS (hYn swap12 swap12_mulVec_e0 y hy))

theorem mulVec_eq_of_mem_pt0 {g : SL3 F}
    (hg : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) {p : Fin 3 → F}
    (hp : p ∈ (pt0 : Submodule F (Fin 3 → F))) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p := by
  have hp' : p = p 0 • ![1, 0, 0] := by
    funext k
    fin_cases k
    · simp
    · simp [hp.1]
    · simp [hp.2]
  rw [hp', Matrix.mulVec_smul, hg]

theorem dg_dg (g h : SL3 F) (n : Fin 2 → Fin 3 → F) : dg g (dg h n) = dg (g * h) n := by
  funext i
  simp only [dg_apply]
  rw [sl3_mulVec_mul]

theorem dg_one (n : Fin 2 → Fin 3 → F) : dg (1 : SL3 F) n = n := by
  funext i
  simp only [dg_apply, sl3_one_mulVec]

theorem dg_add (g : SL3 F) (n m : Fin 2 → Fin 3 → F) : dg g (n + m) = dg g n + dg g m := by
  funext i
  simp only [dg_apply, Pi.add_apply, Matrix.mulVec_add]

theorem offender_eq_bot_of_equiv [Fintype F] [CharP F 2] {n₀ : ℕ} (hF : Fintype.card F = 2 ^ n₀)
    {X : Type*} [CommGroup X] (e : X ≃ (Fin 2 → Fin 3 → F)) (he : ∀ x y, e (x * y) = e x + e y)
    {B : Subgroup (MulAut X)} (hB : IsElemAbelian2 B)
    (hnorm : ∀ x ∈ B, ∀ g : SL3 F, ∃ h : SL3 F, ∀ v w : X, e w = dg g (e v) →
      e (x w) = dg h (e (x v)))
    (hpt : ∀ x ∈ B, ∀ g : SL3 F, (∀ v, e (x v) = dg g (e v)) → g ∈ qPt)
    (hoff : Nat.card X ≤ Nat.card B * Nat.card (fixV B)) : B = ⊥ := by
  classical
  let φ : MulAut X →* Equiv.Perm (Fin 2 → Fin 3 → F) :=
    { toFun := fun x => (e.symm.trans x.toEquiv).trans e
      map_one' := by ext n; simp
      map_mul' := fun x y => by ext n; simp }
  have hφ : ∀ x n, φ x n = e (x (e.symm n)) := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    ext v
    have := congrArg (fun f : Equiv.Perm _ => f (e v)) hxy
    simp only [hφ, Equiv.symm_apply_apply] at this
    exact e.injective this
  have hesymm : ∀ m₁ m₂, e.symm (m₁ + m₂) = e.symm m₁ * e.symm m₂ := fun m₁ m₂ => by
    apply e.injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmem : ∀ a ∈ B.map φ, ∃ x ∈ B, φ x = a := fun a ha => Subgroup.mem_map.mp ha
  have hbot : B.map φ = ⊥ := by
    refine offender_eq_bot hF (B.map φ) ?_ ?_ ?_ ?_ ?_ ?_
    · intro a ha m₁ m₂
      obtain ⟨x, -, rfl⟩ := hmem a ha
      rw [hφ, hφ, hφ, hesymm, map_mul, he]
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := hmem a ha
      obtain ⟨y, hy, rfl⟩ := hmem b hb
      rw [← map_mul, ← map_mul, hB.1 x hx y hy]
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := hmem a ha
      rw [← map_mul, ← pow_two, hB.2 x hx, map_one]
    · intro a ha g
      obtain ⟨x, hx, rfl⟩ := hmem a ha
      obtain ⟨h, hh⟩ := hnorm x hx g
      refine ⟨h, fun n => ?_⟩
      rw [hφ, hφ]
      exact hh (e.symm n) (e.symm (dg g n)) (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
    · intro a ha g hg
      obtain ⟨x, hx, rfl⟩ := hmem a ha
      refine hpt x hx g fun v => ?_
      have := hg (e v)
      rwa [hφ, Equiv.symm_apply_apply] at this
    · have hcardA : Nat.card (B.map φ) = Nat.card B := Subgroup.card_map_of_injective hφinj
      have hcardF : Nat.card ↥(fixP (B.map φ)) = Nat.card (fixV B) := by
        symm
        refine Nat.card_congr (e.subtypeEquiv fun v => ?_)
        constructor
        · intro hv a ha
          obtain ⟨x, hx, rfl⟩ := hmem a ha
          rw [hφ, Equiv.symm_apply_apply, hv x hx]
        · intro hv x hx
          have := hv (φ x) (Subgroup.mem_map_of_mem φ hx)
          rw [hφ, Equiv.symm_apply_apply] at this
          exact e.injective this
      rw [hcardA, hcardF, ← Nat.card_congr e]
      exact hoff
  rw [eq_bot_iff]
  intro x hx
  have : φ x ∈ B.map φ := Subgroup.mem_map_of_mem φ hx
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (hφinj (this.trans (map_one φ).symm))

variable {G : Type} [Group G]

theorem exists_standard_natural2 {L W T : Subgroup G} [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hW : IsSumOfNaturalModulesVia L W ⊥ α false 2) (hT : IsSylowTwoOf T L) :
    ∃ (α₁ : ↥L →* SL3 F) (b : ↥W → Fin 2 → Fin 3 → F), Function.Surjective α₁ ∧
      α₁.ker = α.ker ∧ (T.subgroupOf L).map α₁ = sStar ∧ Function.Bijective b ∧
      (∀ u v : ↥W, b (u * v) = b u + b v) ∧
      ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ → b v = dg (α₁ ℓ) (b u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  set e := specialLinearGroupEquivStatedSL 3 F with he
  set α₀ : ↥L →* SL3 F := e.symm.toMonoidHom.comp α with hα₀
  have hα₀s : Function.Surjective α₀ := e.symm.surjective.comp hα
  have hα₀ker : α₀.ker = α.ker := MonoidHom.ker_comp_of_injective α _ e.symm.injective
  have hcoe : ∀ ℓ : ↥L, (((α ℓ : StatedSL 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α₀ ℓ : SL3 F) : Matrix (Fin 3) (Fin 3) F) := fun ℓ => by
    rw [← specialLinearGroupEquivStatedSL_coe 3 F (α₀ ℓ)]
    simp [hα₀, he]
  have hT2 : IsPGroup 2 ↥(T.subgroupOf L) :=
    hT.2.1.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨γ, hγ⟩ := exists_map_conj_eq_sStar hF' (hT2.map α₀)
    (fun h2 => hT.2.2 (h2.trans (Subgroup.index_map_dvd _ hα₀s)))
  set α₁ : ↥L →* SL3 F := (MulAut.conj γ).toMonoidHom.comp α₀ with hα₁
  obtain ⟨-, -, β, hβs, hβk, hβeq⟩ := hW
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  set b : ↥W → Fin 2 → Fin 3 → F := fun w => dg γ (Multiplicative.toAdd (β w)) with hb
  refine ⟨α₁, b, (MulAut.conj γ).surjective.comp hα₀s, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hα₁, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj γ).injective, hα₀ker]
  · rw [hα₁, ← Subgroup.map_map, hγ]
  · intro u v huv
    apply hβinj
    apply Multiplicative.toAdd.injective
    have := congrArg (fun x => dg γ⁻¹ x) huv
    simp only [hb, dg_dg, inv_mul_cancel, dg_one] at this
    exact this
  · intro v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (dg γ⁻¹ v))
    refine ⟨u, ?_⟩
    simp only [hb, hu, toAdd_ofAdd, dg_dg, mul_inv_cancel, dg_one]
  · intro u v
    simp only [hb, map_mul, toAdd_mul, dg_add]
  · intro ℓ u v huv
    funext i
    have := hβeq ℓ u v huv i
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte] at this
    have hcomm : γ * α₀ ℓ = α₁ ℓ * γ := by
      simp only [hα₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    simp only [hb, dg_apply, this, hcoe]
    rw [← sl3_mulVec_mul, hcomm, sl3_mulVec_mul]

end CFSG.Quasithin.MS93.AS
