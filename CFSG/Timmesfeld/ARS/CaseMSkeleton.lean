module

public import CFSG.Timmesfeld.ARS.CaseBSkeleton
public import CFSG.Timmesfeld.ARS.CaseERootSys

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
open CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseM

theorem exists_hom_D [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {n : ℕ} (hn : 4 ≤ n)
    {A B : Fin n → Subgroup G} (hX : IsConfig R (edgeD n) A B) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : _ →* G,
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (-sroot k)).map Ψ =
          B k) ∧ Ψ.range = ⨆ k, (A k ⊔ B k) ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_D hn)
  have hn3 : 3 ≤ n := by omega
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  set H := ⨆ k, (A k ⊔ B k) with hH
  have hAH : ∀ k, A k ≤ H := fun k => le_sup_left.trans (le_iSup (fun k => A k ⊔ B k) k)
  have hBH : ∀ k, B k ≤ H := fun k => le_sup_right.trans (le_iSup (fun k => A k ⊔ B k) k)
  have hρH : ∀ k x, ρ k x ∈ H := by
    intro k x
    have hx : x ∈ upperUnipotent F ⊔ lowerUnipotent F := by
      rw [NaturalModule.upperUnipotent_sup_lowerUnipotent]
      trivial
    have hmem : ρ k x ∈ (upperUnipotent F ⊔ lowerUnipotent F).map (ρ k) := ⟨x, hx, rfl⟩
    rw [Subgroup.map_sup, (hρ k).2.1, (hρ k).2.2] at hmem
    exact sup_le (hAH k) (hBH k) hmem
  let ρ' : Fin n → SpecialLinearGroup (Fin 2) F →* H := fun k => (ρ k).codRestrict H (hρH k)
  have hcomp : ∀ k, H.subtype.comp (ρ' k) = ρ k := fun k => MonoidHom.ext fun _ => rfl
  have hρ' : ∀ k, (upperUnipotent F).map (ρ' k) = (A k).subgroupOf H ∧
      (lowerUnipotent F).map (ρ' k) = (B k).subgroupOf H := by
    intro k
    refine ⟨Subgroup.map_injective H.subtype_injective ?_,
      Subgroup.map_injective H.subtype_injective ?_⟩
    · rw [Subgroup.map_map, hcomp, Subgroup.map_subgroupOf_eq_of_le (hAH k)]
      exact (hρ k).2.1
    · rw [Subgroup.map_map, hcomp, Subgroup.map_subgroupOf_eq_of_le (hBH k)]
      exact (hρ k).2.2
  have hedge' : ∀ i j, edgeD n i j → ∃ ψ : SpecialLinearGroup (Fin 3) F →* H, ∀ c,
      ψ (tv 0 1 c) = ρ' i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ' i (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ' j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' j (tv 1 0 c) := by
    intro i j hij
    obtain ⟨ψ, hψ⟩ := hedge i j hij
    have hψH : ∀ x, ψ x ∈ H := CaseB.mem_of_tv_mem ψ (fun c => (hψ c).1 ▸ hρH i _)
      (fun c => (hψ c).2.1 ▸ hρH i _) (fun c => (hψ c).2.2.1 ▸ hρH j _)
      (fun c => (hψ c).2.2.2 ▸ hρH j _)
    exact ⟨ψ.codRestrict H hψH, fun c => ⟨Subtype.ext (hψ c).1, Subtype.ext (hψ c).2.1,
      Subtype.ext (hψ c).2.2.1, Subtype.ext (hψ c).2.2.2⟩⟩
  have hnonadj' : ∀ i j, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      Commuting ((A i).subgroupOf H) ((A j).subgroupOf H) ∧
      Commuting ((A i).subgroupOf H) ((B j).subgroupOf H) ∧
      Commuting ((B i).subgroupOf H) ((A j).subgroupOf H) ∧
      Commuting ((B i).subgroupOf H) ((B j).subgroupOf H) := by
    intro i j hij h1 h2
    obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    exact ⟨CaseB.commuting_subgroupOf c1, CaseB.commuting_subgroupOf c2,
      CaseB.commuting_subgroupOf c3, CaseB.commuting_subgroupOf c4⟩
  have hgen' : ⨆ k, ((A k).subgroupOf H ⊔ (B k).subgroupOf H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hk : ∀ k, ((A k).subgroupOf H ⊔ (B k).subgroupOf H).map H.subtype = A k ⊔ B k :=
      fun k => by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hAH k),
          Subgroup.map_subgroupOf_eq_of_le (hBH k)]
    rw [iSup_congr hk]
  have hnt' : ∃ k, ∃ a ∈ (A k).subgroupOf H, a ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
    exact ⟨⟨0, by omega⟩, ⟨a, hAH _ ha⟩, Subgroup.mem_subgroupOf.2 ha,
      fun e => ha1 (congrArg Subtype.val e)⟩
  obtain ⟨Ψ', hΨA, hΨB, hsurj, hker⟩ := exists_surjective_of_rho
    (D := Spin.plusDatum n F hn3)
    (CurtisTits.curtisTitsConclusion_spinPlus ⟨Nat.prime_two, hf, hn⟩ hF hn3)
    (leviConePresented_spinPlus F hn3) (simplyLacedLevis_spinPlus F hn3) hnonadj' ρ' hρ'
    hedge' hgen' hnt'
  refine ⟨f, hf, hcard, H.subtype.comp Ψ', fun k => ?_, fun k => ?_, ?_, ?_⟩
  · rw [← Subgroup.map_map]
    exact (congrArg (Subgroup.map H.subtype) (hΨA k)).trans
      (Subgroup.map_subgroupOf_eq_of_le (hAH k))
  · rw [← Subgroup.map_map]
    exact (congrArg (Subgroup.map H.subtype) (hΨB k)).trans
      (Subgroup.map_subgroupOf_eq_of_le (hBH k))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro x hx
    refine hker ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact H.subtype_injective (by rw [map_one]; exact hx)

theorem three_le_four : 3 ≤ 4 := by norm_num

theorem cartanForm_D4_add (u v : Fin 4 → ℤ) (a b : ℕ) :
    cartanForm (Spin.cartanD 4) (a • u + b • v) =
      (a : ℤ) ^ 2 * cartanForm (Spin.cartanD 4) u + (b : ℤ) ^ 2 * cartanForm (Spin.cartanD 4) v +
        2 * a * b * ∑ m, u m * coroot (Spin.cartanD 4) m v := by
  simp only [cartanForm, coroot_apply, Fin.sum_univ_four, Pi.add_apply, nsmul_eq_mul,
    Spin.cartanD, Matrix.of_apply]
  simp
  ring

theorem single_D4 (k : Fin 4) : (Pi.single k 1 : Fin 4 → ℤ) =
    ![if k = 0 then 1 else 0, if k = 1 then 1 else 0, if k = 2 then 1 else 0,
      if k = 3 then 1 else 0] := by
  ext j; fin_cases j <;> fin_cases k <;> rfl

abbrev rootB₁ : Fin 4 → ℤ := ![1, 1, 0, 0]

abbrev rootB₂ : Fin 4 → ℤ := ![1, 1, 1, 0]

abbrev rootB₃ : Fin 4 → ℤ := ![1, 1, 1, 1]

abbrev rootTheta : Fin 4 → ℤ := ![1, 2, 1, 1]

variable {F : Type} [Field F]

theorem mem_roots_B₁ : rootB₁ ∈ (Spin.plusDatum 4 F three_le_four).roots := by
  have e : (reflection (Spin.cartanD 4) (0 : Fin 4)) (Pi.single (1 : Fin 4) 1) = rootB₁ := by
    ext j; fin_cases j <;> simp [reflection_apply, Fin.sum_univ_four, Spin.cartanD]
  rw [← e]
  exact LevisExtras.reflection_mem_roots (D := Spin.plusDatum 4 F three_le_four) (0 : Fin 4)
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (1 : Fin 4))

theorem mem_roots_B₂ : rootB₂ ∈ (Spin.plusDatum 4 F three_le_four).roots := by
  have e : (reflection (Spin.cartanD 4) (2 : Fin 4)) rootB₁ = rootB₂ := by
    ext j; fin_cases j <;> simp [reflection_apply, Fin.sum_univ_four, Spin.cartanD]
  rw [← e]
  exact LevisExtras.reflection_mem_roots (D := Spin.plusDatum 4 F three_le_four) (2 : Fin 4)
    mem_roots_B₁

theorem mem_roots_B₃ : rootB₃ ∈ (Spin.plusDatum 4 F three_le_four).roots := by
  have e : (reflection (Spin.cartanD 4) (3 : Fin 4)) rootB₂ = rootB₃ := by
    ext j; fin_cases j <;> simp [reflection_apply, Fin.sum_univ_four, Spin.cartanD]
  rw [← e]
  exact LevisExtras.reflection_mem_roots (D := Spin.plusDatum 4 F three_le_four) (3 : Fin 4)
    mem_roots_B₂

theorem mem_roots_theta : rootTheta ∈ (Spin.plusDatum 4 F three_le_four).roots := by
  have e : (reflection (Spin.cartanD 4) (1 : Fin 4)) rootB₃ = rootTheta := by
    ext j; fin_cases j <;> simp [reflection_apply, Fin.sum_univ_four, Spin.cartanD]
  rw [← e]
  exact LevisExtras.reflection_mem_roots (D := Spin.plusDatum 4 F three_le_four) (1 : Fin 4)
    mem_roots_B₃

theorem commutator_x_D4 [CharP F 2] {α β : Fin 4 → ℤ}
    (hα : α ∈ (Spin.plusDatum 4 F three_le_four).roots)
    (hβ : β ∈ (Spin.plusDatum 4 F three_le_four).roots)
    (hαβ : α + β ∈ (Spin.plusDatum 4 F three_le_four).roots)
    (hq : ∀ a b : ℕ, cartanForm (Spin.cartanD 4) (a • α + b • β) =
      2 * (a : ℤ) ^ 2 + 2 * (b : ℤ) ^ 2 - 2 * a * b)
    (hq' : cartanForm (Spin.cartanD 4) (β - α) = 6) (c d : F) :
    ⁅SpinPlus.x 4 F three_le_four α c, SpinPlus.x 4 F three_le_four β d⁆ =
      SpinPlus.x 4 F three_le_four (α + β) (c * d) := by
  have hsymm : ∀ i j, Spin.cartanD 4 i j = Spin.cartanD 4 j i := fun i j => by
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan
    (Spin.plusDatum 4 F three_le_four).isFiniteType
    (Dv := (Spin.plusDatum 4 F three_le_four).divisible) rfl
  have hE := SpinPlus.chevalleyExtras three_le_four O SpinPlus.commC
    (SpinPlus.commutatorFormula three_le_four O)
  have hne : α + β ≠ 0 := fun h0 => by
    have := cartanForm_eq_two (Spin.isFiniteType_cartanD 4) hsymm hαβ
    rw [h0] at this
    simp [cartanForm] at this
  have hexp : ∀ a b : ℕ, 0 < a → 0 < b →
      a • α + b • β ∈ (Spin.plusDatum 4 F three_le_four).roots → a = 1 ∧ b = 1 := by
    intro a b ha hb hab
    have h2 := cartanForm_eq_two (Spin.isFiniteType_cartanD 4) hsymm hab
    rw [hq] at h2
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h4 : (a : ℤ) * b = 1 := by nlinarith [sq_nonneg ((a : ℤ) - b)]
    constructor <;> nlinarith
  have hβα : β - α ∉ (Spin.plusDatum 4 F three_le_four).roots := by
    intro h
    have h2 := cartanForm_eq_two (Spin.isFiniteType_cartanD 4) hsymm h
    rw [hq'] at h2
    exact absurd h2 (by norm_num)
  exact (LevisExtras.commutator_eq_of_charTwo hE
    (fun α _ β _ _ _ => SpinPlus.commC_natAbs α β (1, 1)) hα hβ hne hexp c d).1 hαβ hβα

theorem commutator_x_α₀_α₁ [CharP F 2] (c d : F) :
    ⁅SpinPlus.x 4 F three_le_four (Pi.single 0 1) c,
      SpinPlus.x 4 F three_le_four (Pi.single 1 1) d⁆ =
      SpinPlus.x 4 F three_le_four rootB₁ (c * d) := by
  have e : (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → ℤ) = rootB₁ := by
    rw [single_D4, single_D4]; ext j; fin_cases j <;> rfl
  rw [← e]
  refine commutator_x_D4 (α := Pi.single (0 : Fin 4) 1) (β := Pi.single (1 : Fin 4) 1)
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (0 : Fin 4))
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (1 : Fin 4))
    (e ▸ mem_roots_B₁) (fun a b => ?_) ?_ c d
  · rw [cartanForm_D4_add, single_D4, single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]
    ring
  · rw [single_D4, single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]

theorem commutator_x_β₁_α₂ [CharP F 2] (c d : F) :
    ⁅SpinPlus.x 4 F three_le_four rootB₁ c, SpinPlus.x 4 F three_le_four (Pi.single 2 1) d⁆ =
      SpinPlus.x 4 F three_le_four rootB₂ (c * d) := by
  have e : (rootB₁ + Pi.single 2 1 : Fin 4 → ℤ) = rootB₂ := by
    rw [single_D4]; ext j; fin_cases j <;> rfl
  rw [← e]
  refine commutator_x_D4 (α := rootB₁) (β := Pi.single (2 : Fin 4) 1) mem_roots_B₁
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (2 : Fin 4))
    (e ▸ mem_roots_B₂) (fun a b => ?_) ?_ c d
  · rw [cartanForm_D4_add, single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]
    ring
  · rw [single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]

theorem commutator_x_β₂_α₃ [CharP F 2] (c d : F) :
    ⁅SpinPlus.x 4 F three_le_four rootB₂ c, SpinPlus.x 4 F three_le_four (Pi.single 3 1) d⁆ =
      SpinPlus.x 4 F three_le_four rootB₃ (c * d) := by
  have e : (rootB₂ + Pi.single 3 1 : Fin 4 → ℤ) = rootB₃ := by
    rw [single_D4]; ext j; fin_cases j <;> rfl
  rw [← e]
  refine commutator_x_D4 (α := rootB₂) (β := Pi.single (3 : Fin 4) 1) mem_roots_B₂
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (3 : Fin 4))
    (e ▸ mem_roots_B₃) (fun a b => ?_) ?_ c d
  · rw [cartanForm_D4_add, single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]
    ring
  · rw [single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]

theorem commutator_x_β₃_α₁ [CharP F 2] (c d : F) :
    ⁅SpinPlus.x 4 F three_le_four rootB₃ c, SpinPlus.x 4 F three_le_four (Pi.single 1 1) d⁆ =
      SpinPlus.x 4 F three_le_four rootTheta (c * d) := by
  have e : (rootB₃ + Pi.single 1 1 : Fin 4 → ℤ) = rootTheta := by
    rw [single_D4]; ext j; fin_cases j <;> rfl
  rw [← e]
  refine commutator_x_D4 (α := rootB₃) (β := Pi.single (1 : Fin 4) 1) mem_roots_B₃
    (LevisExtras.single_mem_roots (D := Spin.plusDatum 4 F three_le_four) (1 : Fin 4))
    (e ▸ mem_roots_theta) (fun a b => ?_) ?_ c d
  · rw [cartanForm_D4_add, single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]
    ring
  · rw [single_D4]
    simp [cartanForm, coroot_apply, Fin.sum_univ_four, Spin.cartanD]

theorem commute_of_commute_legs [CharP F 2] {H : Type*} [Group H]
    (Ψ : ↥(spinGroup (Spin.quadPlus 4 F)) →* H) {z : H}
    (hleg : ∀ k : Fin 4, k ≠ 1 → ∀ c,
      Commute z (Ψ (SpinPlus.x 4 F three_le_four (Pi.single k 1) c)))
    (hE : ∀ c, ∃ d, z * Ψ (SpinPlus.x 4 F three_le_four (Pi.single 1 1) c) * z⁻¹ =
      Ψ (SpinPlus.x 4 F three_le_four (Pi.single 1 1) d))
    (hinj : Function.Injective fun c => Ψ (SpinPlus.x 4 F three_le_four rootB₁ c))
    (hinjθ : Function.Injective fun c => Ψ (SpinPlus.x 4 F three_le_four rootTheta c))
    (hθ : ∀ c, Commute z (Ψ (SpinPlus.x 4 F three_le_four rootTheta c))) (c : F) :
    Commute z (Ψ (SpinPlus.x 4 F three_le_four (Pi.single 1 1) c)) := by
  choose φ hφ using hE
  set x := SpinPlus.x 4 F three_le_four with hx
  have conj_comm : ∀ a b : H, z * ⁅a, b⁆ * z⁻¹ = ⁅z * a * z⁻¹, z * b * z⁻¹⁆ := fun a b =>
    (FrameSL3.commutatorElement_conj z a b).symm
  have fix : ∀ {g : H}, Commute z g → z * g * z⁻¹ = g := fun h => by
    rw [h.eq, mul_inv_cancel_right]
  have r1 : ∀ a b, Ψ (x rootB₁ (a * b)) = ⁅Ψ (x (Pi.single 0 1) a), Ψ (x (Pi.single 1 1) b)⁆ :=
    fun a b => by rw [← map_commutatorElement, commutator_x_α₀_α₁]
  have r2 : ∀ a b, Ψ (x rootB₂ (a * b)) = ⁅Ψ (x rootB₁ a), Ψ (x (Pi.single 2 1) b)⁆ :=
    fun a b => by rw [← map_commutatorElement, commutator_x_β₁_α₂]
  have r3 : ∀ a b, Ψ (x rootB₃ (a * b)) = ⁅Ψ (x rootB₂ a), Ψ (x (Pi.single 3 1) b)⁆ :=
    fun a b => by rw [← map_commutatorElement, commutator_x_β₂_α₃]
  have r4 : ∀ a b, Ψ (x rootTheta (a * b)) = ⁅Ψ (x rootB₃ a), Ψ (x (Pi.single 1 1) b)⁆ :=
    fun a b => by rw [← map_commutatorElement, commutator_x_β₃_α₁]
  have h1 : ∀ a b, z * Ψ (x rootB₁ (a * b)) * z⁻¹ = Ψ (x rootB₁ (a * φ b)) := by
    intro a b
    rw [r1, conj_comm, fix (hleg 0 (by decide) a), hφ, ← r1]
  set l := φ 1 with hl
  have hφl : ∀ b, φ b = b * l := by
    intro b
    have e1 := h1 1 b
    have e2 := h1 b 1
    rw [one_mul, one_mul] at e1
    rw [mul_one] at e2
    exact hinj (e1.symm.trans e2)
  have hB₁ : ∀ a, z * Ψ (x rootB₁ a) * z⁻¹ = Ψ (x rootB₁ (a * l)) := fun a => by
    simpa using h1 a 1
  have hB₂ : ∀ a, z * Ψ (x rootB₂ a) * z⁻¹ = Ψ (x rootB₂ (a * l)) := fun a => by
    have e := r2 a 1
    rw [mul_one] at e
    rw [e, conj_comm, hB₁, fix (hleg 2 (by decide) 1), ← r2, mul_one]
  have hB₃ : ∀ a, z * Ψ (x rootB₃ a) * z⁻¹ = Ψ (x rootB₃ (a * l)) := fun a => by
    have e := r3 a 1
    rw [mul_one] at e
    rw [e, conj_comm, hB₂, fix (hleg 3 (by decide) 1), ← r3, mul_one]
  have hθ1 : Ψ (x rootTheta 1) = Ψ (x rootTheta (l * l)) := by
    have e := r4 1 1
    rw [mul_one] at e
    calc Ψ (x rootTheta 1) = z * Ψ (x rootTheta 1) * z⁻¹ := (fix (hθ 1)).symm
      _ = Ψ (x rootTheta (l * l)) := by
        rw [e, conj_comm, hB₃, hφ, hφl, one_mul, ← r4]
  have hll : l * l = 1 := (hinjθ hθ1).symm
  have hl1 : l = 1 := by
    have h2 : (l + 1) * (l + 1) = 0 := by
      have e : (l + 1) * (l + 1) = (l * l + 1) + (l + l) := by ring
      rw [e, hll, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have h3 : l + 1 = 0 := mul_self_eq_zero.1 h2
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h3
  have hz : z * Ψ (x (Pi.single 1 1) c) * z⁻¹ = Ψ (x (Pi.single 1 1) c) := by
    rw [hφ, hφl, hl1, mul_one]
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  exact hz

end CaseM

end CFSG.Timmesfeld.ARS
