module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegProduct
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.PermDegBasic

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

universe u v

@[expose] def restrictHom {K : Type*} [Group K] {Ω : Type*} (f : K →* Equiv.Perm Ω)
    (p : Ω → Prop) (hp : ∀ k ω, p (f k ω) ↔ p ω) : K →* Equiv.Perm {ω // p ω} where
  toFun k := (f k).subtypePerm (hp k)
  map_one' := by
    ext ω
    simp
  map_mul' a b := by
    ext ω
    change (f (a * b)) ω = (f a) ((f b) ω)
    rw [map_mul]
    rfl

theorem restrictHom_apply_coe {K : Type*} [Group K] {Ω : Type*} (f : K →* Equiv.Perm Ω)
    (p : Ω → Prop) (hp : ∀ k ω, p (f k ω) ↔ p ω) (k : K) (ω : {ω // p ω}) :
    ((restrictHom f p hp k ω : {ω // p ω}) : Ω) = f k ω := rfl

variable {ι : Type u} [Fintype ι] {G : ι → Type v} [∀ i, Group (G i)] [∀ i, Finite (G i)]

@[expose] def ProperSubproducts (G : ι → Type v) [∀ i, Group (G i)] [∀ i, Finite (G i)] : Prop :=
  ∀ (p : ι → Prop) [DecidablePred p], (∃ i, p i) → (∃ i, ¬ p i) →
    ∑ i : {i // p i}, permDeg (G i) ≤ permDeg (∀ i : {i // p i}, G i)

section Split

variable [∀ i, IsSimpleGroup (G i)]

theorem sum_permDeg_le_of_split (hnc : ∀ i, ¬ IsMulCommutative (G i)) (ih : ProperSubproducts G)
    (N : Subgroup (∀ i, G i)) [N.Normal] (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    {X₁ X₂ : Type*} [Finite X₁] [Finite X₂]
    (φ₁ : (∀ i : {i // suppOf N i}, G i) →* Equiv.Perm X₁) (hφ₁ : Function.Injective φ₁)
    (φ₂ : (∀ i : {i // ¬ suppOf N i}, G i) →* Equiv.Perm X₂) (hφ₂ : Function.Injective φ₂)
    {P : ℕ} (hP : Nat.card X₁ + Nat.card X₂ ≤ P) : ∑ i, permDeg (G i) ≤ P := by
  classical
  have hN := eq_suppSubgroup_suppOf hnc N
  have h1 : ∃ i, suppOf N i := by
    by_contra h
    push Not at h
    refine hbot (eq_bot_iff.mpr fun x hx => ?_)
    rw [Subgroup.mem_bot]
    funext i
    by_contra hxi
    exact h i ⟨x, hx, hxi⟩
  have h2 : ∃ i, ¬ suppOf N i := by
    by_contra h
    push Not at h
    refine htop (eq_top_iff.mpr fun x _ => ?_)
    rw [hN]
    exact fun i hi => absurd (h i) hi
  have e1 := ih (suppOf N) h1 h2
  have e2 := ih (fun i => ¬ suppOf N i) h2 (by obtain ⟨i, hi⟩ := h1; exact ⟨i, not_not.mpr hi⟩)
  have e3 := permDeg_le_of_injective φ₁ hφ₁
  have e4 := permDeg_le_of_injective φ₂ hφ₂
  have e5 := Fintype.sum_subtype_add_sum_subtype (suppOf N) fun i => permDeg (G i)
  omega

theorem sum_permDeg_le_of_not_pretransitive (hnc : ∀ i, ¬ IsMulCommutative (G i))
    (ih : ProperSubproducts G) {Ω : Type*} [Finite Ω] [MulAction (∀ i, G i) Ω]
    (hfaith : ∀ q : ∀ i, G i, (∀ ω : Ω, q • ω = ω) → q = 1)
    (hΩ : Nat.card Ω ≤ permDeg (∀ i, G i))
    (hnt : ¬ MulAction.IsPretransitive (∀ i, G i) Ω) :
    ∑ i, permDeg (G i) ≤ Nat.card Ω := by
  classical
  rw [MulAction.isPretransitive_iff] at hnt
  push Not at hnt
  obtain ⟨a, b, hab⟩ := hnt
  let P : Ω → Prop := fun ω => ω ∈ MulAction.orbit (∀ i, G i) a
  have hPinv : ∀ (q : ∀ i, G i) (ω : Ω), P (q • ω) ↔ P ω := by
    intro q ω
    constructor
    · rintro ⟨g, hg⟩
      have hg' : g • a = q • ω := hg
      refine ⟨q⁻¹ * g, ?_⟩
      show (q⁻¹ * g) • a = ω
      rw [mul_smul, hg', inv_smul_smul]
    · rintro ⟨g, rfl⟩
      exact ⟨q * g, by show (q * g) • a = q • g • a; rw [mul_smul]⟩
  have hPb : ¬ P b := fun ⟨g, hg⟩ => hab g hg
  have hPa : P a := ⟨1, one_smul _ a⟩
  let N : Subgroup (∀ i, G i) := fixingSubgroup (∀ i, G i) {ω | P ω}
  have hmemN : ∀ q, q ∈ N ↔ ∀ ω, P ω → q • ω = ω := fun q => by
    simp [N, mem_fixingSubgroup_iff]
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hmemN] at hn ⊢
    intro ω hω
    have := hn (g⁻¹ • ω) ((hPinv g⁻¹ ω).mpr hω)
    rw [mul_smul, mul_smul, this, smul_inv_smul]⟩
  let f : (∀ i, G i) →* Equiv.Perm Ω := MulAction.toPermHom (∀ i, G i) Ω
  have hf : ∀ q ω, f q ω = q • ω := fun _ _ => rfl
  let ρ₁ := restrictHom f P (fun q ω => by rw [hf]; exact hPinv q ω)
  let ρ₂ := restrictHom f (fun ω => ¬ P ω) (fun q ω => by rw [hf]; exact (hPinv q ω).not)
  have hρ₁ : ∀ q, ρ₁ q = 1 → ∀ ω, P ω → q • ω = ω := fun q hq ω hω =>
    congrArg Subtype.val (Equiv.congr_fun hq ⟨ω, hω⟩)
  have hρ₂ : ∀ q, ρ₂ q = 1 → ∀ ω, ¬ P ω → q • ω = ω := fun q hq ω hω =>
    congrArg Subtype.val (Equiv.congr_fun hq ⟨ω, hω⟩)
  have hbot : N ≠ ⊥ := by
    intro hNbot
    have hinj : Function.Injective ρ₁ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro q hq
      rw [MonoidHom.mem_ker] at hq
      have : q ∈ N := (hmemN q).mpr (hρ₁ q hq)
      rwa [hNbot] at this
    have h1 := permDeg_le_of_injective ρ₁ hinj
    have h2 := Finite.card_subtype_lt (p := P) hPb
    omega
  have htop : N ≠ ⊤ := by
    intro hNtop
    have hinj : Function.Injective ρ₂ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro q hq
      rw [MonoidHom.mem_ker] at hq
      rw [Subgroup.mem_bot]
      refine hfaith q fun ω => ?_
      by_cases hω : P ω
      · exact (hmemN q).mp (hNtop ▸ Subgroup.mem_top q) ω hω
      · exact hρ₂ q hq ω hω
    have h1 := permDeg_le_of_injective ρ₂ hinj
    have h2 := Finite.card_subtype_lt (p := fun ω => ¬ P ω) (x := a) (not_not.mpr hPa)
    omega
  have hcard : Nat.card {ω // ¬ P ω} + Nat.card {ω // P ω} = Nat.card Ω := by
    rw [add_comm, ← Nat.card_sum, Nat.card_congr (Equiv.sumCompl P)]
  refine sum_permDeg_le_of_split hnc ih N hbot htop (ρ₂.comp (embSub G (suppOf N))) ?_
    (ρ₁.comp (embSub G (fun i => ¬ suppOf N i))) ?_ hcard.le
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_bot]
    have hq : embSub G (suppOf N) y = 1 := by
      refine hfaith _ fun ω => ?_
      by_cases hω : P ω
      · exact (hmemN _).mp (embSub_suppOf_mem hnc N y) ω hω
      · exact hρ₂ _ hy ω hω
    exact embSub_injective _ (hq.trans (map_one _).symm)
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_bot]
    exact eq_one_of_embSub_mem hnc N y ((hmemN _).mpr fun ω hω => hρ₁ _ hy ω hω)

theorem sum_permDeg_le_of_lt_stabilizer (hnc : ∀ i, ¬ IsMulCommutative (G i))
    (ih : ProperSubproducts G) {Ω : Type*} [Finite Ω] [MulAction (∀ i, G i) Ω]
    [MulAction.IsPretransitive (∀ i, G i) Ω]
    (hfaith : ∀ q : ∀ i, G i, (∀ ω : Ω, q • ω = ω) → q = 1)
    (hΩ : Nat.card Ω ≤ permDeg (∀ i, G i)) (a : Ω) {M : Subgroup (∀ i, G i)}
    (hlt : MulAction.stabilizer (∀ i, G i) a < M) (hMtop : M ≠ ⊤) :
    ∑ i, permDeg (G i) ≤ Nat.card Ω := by
  classical
  set M₀ := MulAction.stabilizer (∀ i, G i) a with hM₀
  have hΩpos : 0 < Nat.card Ω := Nat.card_pos_iff.mpr ⟨⟨a⟩, inferInstance⟩
  have hrel : M₀.relIndex M * M.index = Nat.card Ω := by
    rw [Subgroup.relIndex_mul_index hlt.le, hM₀, MulAction.index_stabilizer_of_transitive]
  have hMidx : 2 ≤ M.index := by
    have h0 : M.index ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hrel
      omega
    have h1 : M.index ≠ 1 := fun h => hMtop (Subgroup.index_eq_one.mp h)
    omega
  have hrelidx : 2 ≤ M₀.relIndex M := by
    have h0 : M₀.relIndex M ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hrel
      omega
    have h1 : M₀.relIndex M ≠ 1 := fun h => (not_le_of_gt hlt) (Subgroup.relIndex_eq_one.mp h)
    omega
  have hKM : M.normalCore ≤ M := M.normalCore_le
  have hKker : M.normalCore = (MulAction.toPermHom (∀ i, G i) ((∀ i, G i) ⧸ M)).ker :=
    M.normalCore_eq_ker
  have hKbot : M.normalCore ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (MulAction.toPermHom (∀ i, G i) ((∀ i, G i) ⧸ M)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← hKker]
      exact h
    have h1 := permDeg_le_of_injective _ hinj
    have h2 : Nat.card ((∀ i, G i) ⧸ M) = M.index := M.index_eq_card.symm
    nlinarith
  have hKtop : M.normalCore ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hKM))
  have hcard : Nat.card (M ⧸ M₀.subgroupOf M) + Nat.card ((∀ i, G i) ⧸ M) ≤ Nat.card Ω := by
    have e1 : Nat.card (M ⧸ M₀.subgroupOf M) = M₀.relIndex M :=
      (M₀.subgroupOf M).index_eq_card.symm
    have e2 : Nat.card ((∀ i, G i) ⧸ M) = M.index := M.index_eq_card.symm
    rw [e1, e2, ← hrel]
    nlinarith
  have hmem : ∀ y, embSub G (suppOf M.normalCore) y ∈ M := fun y =>
    hKM (embSub_suppOf_mem hnc M.normalCore y)
  refine sum_permDeg_le_of_split hnc ih M.normalCore hKbot hKtop
    ((MulAction.toPermHom M (M ⧸ M₀.subgroupOf M)).comp
      ((embSub G (suppOf M.normalCore)).codRestrict M hmem)) ?_
    ((MulAction.toPermHom (∀ i, G i) ((∀ i, G i) ⧸ M)).comp
      (embSub G (fun i => ¬ suppOf M.normalCore i))) ?_ hcard
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_bot]
    set k := embSub G (suppOf M.normalCore) y with hk
    have hkM : k ∈ M := hmem y
    have h1 : ∀ m : M, (m : ∀ i, G i)⁻¹ * k⁻¹ * m ∈ M₀ := by
      intro m
      have h2 : ((⟨k, hkM⟩ * m : M) : M ⧸ M₀.subgroupOf M) = (m : M ⧸ M₀.subgroupOf M) := by
        have := Equiv.congr_fun hy (m : M ⧸ M₀.subgroupOf M)
        exact this
      rw [QuotientGroup.eq] at h2
      have h3 : (((⟨k, hkM⟩ * m : M)⁻¹ * m : M) : ∀ i, G i) ∈ M₀ := h2
      simpa [mul_assoc] using h3
    have h4 : ∀ q : ∀ i, G i, q⁻¹ * k⁻¹ * q ∈ M₀ := by
      intro q
      obtain ⟨x, z, rfl⟩ := exists_eq_embSub_mul (suppOf M.normalCore) q
      have hxM : embSub G (suppOf M.normalCore) x ∈ M := hmem x
      have e1 : embSub G (suppOf M.normalCore) (x⁻¹ * y⁻¹ * x) =
          (embSub G (suppOf M.normalCore) x)⁻¹ * k⁻¹ * embSub G (suppOf M.normalCore) x := by
        simp [hk, map_mul, map_inv]
      have hcomm : Commute ((embSub G (suppOf M.normalCore) x)⁻¹ * k⁻¹ *
          embSub G (suppOf M.normalCore) x) (embSub G (fun i => ¬ suppOf M.normalCore i) z) := by
        rw [← e1]
        exact embSub_commute _ _ _
      have e : (embSub G (suppOf M.normalCore) x *
            embSub G (fun i => ¬ suppOf M.normalCore i) z)⁻¹ * k⁻¹ *
          (embSub G (suppOf M.normalCore) x * embSub G (fun i => ¬ suppOf M.normalCore i) z) =
          (embSub G (suppOf M.normalCore) x)⁻¹ * k⁻¹ * embSub G (suppOf M.normalCore) x := by
        calc _ = (embSub G (fun i => ¬ suppOf M.normalCore i) z)⁻¹ *
              ((embSub G (suppOf M.normalCore) x)⁻¹ * k⁻¹ * embSub G (suppOf M.normalCore) x) *
                embSub G (fun i => ¬ suppOf M.normalCore i) z := by group
          _ = _ := by rw [mul_assoc, hcomm.eq, inv_mul_cancel_left]
      rw [e]
      exact h1 ⟨_, hxM⟩
    have h5 : k⁻¹ = 1 := by
      refine hfaith _ fun ω => ?_
      obtain ⟨q, rfl⟩ := MulAction.exists_smul_eq (∀ i, G i) a ω
      have h6 := h4 q
      rw [hM₀, MulAction.mem_stabilizer_iff] at h6
      calc k⁻¹ • q • a = q • (q⁻¹ * k⁻¹ * q) • a := by
            simp only [mul_smul, smul_inv_smul]
        _ = q • a := by rw [h6]
    have h7 : k = 1 := inv_eq_one.mp h5
    exact embSub_injective _ (h7.trans (map_one _).symm)
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    rw [Subgroup.mem_bot]
    refine eq_one_of_embSub_mem hnc M.normalCore y ?_
    exact (SetLike.ext_iff.mp hKker _).mpr hy

end Split

end CFSG.SignalizerFunctorTheorem.McBride.Near
