module

public import CFSG.Sporadic.Co1Patterson.NativeSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS Matrix
open CFSG.Blueprint (NativeSporadic.Co1)

abbrev Vt : Type := ConjVert aNC

@[expose] noncomputable def vA : Vt := ⟨aNC, IsConj.refl _⟩

theorem smul_vA_eq_iff (g : NativeSporadic.Co1) :
    g • vA = vA ↔ g ∈ centralizer ({aNC} : Set NativeSporadic.Co1) :=
  smul_eq_self_iff g vA

theorem card_Vt :
    Nat.card Vt = 46621575 := by
  have horb : MulAction.orbit NativeSporadic.Co1 vA = Set.univ := by
    ext ⟨x, hx⟩
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, rfl⟩ := isConj_iff.1 hx
    exact ⟨g, Subtype.ext rfl⟩
  have hstab : MulAction.stabilizer NativeSporadic.Co1 vA =
      centralizer ({aNC} : Set NativeSporadic.Co1) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, smul_vA_eq_iff]
  have h1 := MulAction.index_stabilizer NativeSporadic.Co1 vA
  have h2 := (MulAction.stabilizer NativeSporadic.Co1 vA).card_mul_index
  rw [horb, Set.ncard_univ] at h1
  rw [h1, hstab, card_centralizer_aNC, CFSG.Sporadic.Co1.card_Co1] at h2
  omega

@[expose] def cOrb (v : Vt) : Set Vt :=
  {w | ∃ k ∈ centralizer ({aNC} : Set NativeSporadic.Co1), w = k • v}

theorem mem_cOrb_self (v : Vt) : v ∈ cOrb v := ⟨1, one_mem _, (one_smul _ v).symm⟩

theorem smul_mem_cOrb {v w : Vt} {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (hw : w ∈ cOrb v) :
    k • w ∈ cOrb v := by
  obtain ⟨k', hk', rfl⟩ := hw
  exact ⟨k * k', mul_mem hk hk', (mul_smul k k' v).symm⟩

@[expose] def orbRel (t u v : Vt) : Prop := ∃ g : NativeSporadic.Co1, g • vA = u ∧ g • t = v

theorem orbRel_smul {t u v : Vt} (g : NativeSporadic.Co1) (h : orbRel t u v) :
    orbRel t (g • u) (g • v) := by
  obtain ⟨g', h1, h2⟩ := h
  exact ⟨g * g', by rw [mul_smul, h1], by rw [mul_smul, h2]⟩

theorem orbRel_smul_iff_mem {t v : Vt} (x : NativeSporadic.Co1) :
    orbRel t (x • vA) v ↔ x⁻¹ • v ∈ cOrb t := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨x⁻¹ * g, (smul_vA_eq_iff _).1 ?_, by rw [mul_smul]⟩
    rw [mul_smul, hg, inv_smul_smul]
  · rintro ⟨k, hk, hv⟩
    refine ⟨x * k, ?_, ?_⟩
    · rw [mul_smul, (smul_vA_eq_iff k).2 hk]
    · rw [mul_smul, ← hv, smul_inv_smul]

@[expose] noncomputable def ordA (v : Vt) : ℕ := orderOf (aNC * (v : NativeSporadic.Co1))

@[expose] def inQa (v : Vt) : Prop := (v : NativeSporadic.Co1) ∈ twoAQNC

@[expose] def inQa2 (v : Vt) : Prop := (aNC * (v : NativeSporadic.Co1)) ^ 2 ∈ twoAQNC

@[expose] noncomputable def fixA (v : Vt) : ℕ :=
  {w : Fin 24 → ZMod 2 | matHom (aNC * (v : NativeSporadic.Co1)) *ᵥ w = w}.ncard

theorem mul_conj_of_comm {G : Type*} [Group G] {a k : G} (h : k * a = a * k) (x : G) :
    a * (k * x * k⁻¹) = k * (a * x) * k⁻¹ := by
  calc a * (k * x * k⁻¹) = (a * k) * x * k⁻¹ := by group
    _ = (k * a) * x * k⁻¹ := by rw [h]
    _ = k * (a * x) * k⁻¹ := by group

theorem aNC_mul_conj {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (x : NativeSporadic.Co1) :
    aNC * (k * x * k⁻¹) = k * (aNC * x) * k⁻¹ :=
  mul_conj_of_comm (mem_centralizer_singleton_iff.1 hk) x

theorem aNC_mul_smul {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (v : Vt) :
    aNC * (k • v).1 = k * (aNC * v.1) * k⁻¹ :=
  aNC_mul_conj hk v.1

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  rwa [MulAut.conj_apply] at this

theorem ordA_smul {k : NativeSporadic.Co1} (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1))
    (v : Vt) : ordA (k • v) = ordA v := by
  unfold ordA
  rw [aNC_mul_smul hk, orderOf_conj_eq]

theorem conj_mem_twoAQNC
    {k q : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (hq : q ∈ twoAQNC) :
    k * q * k⁻¹ ∈ twoAQNC := by
  rw [mem_twoAQNC_iff, map_mul, map_mul, map_inv]
  exact twoAQ_normal _ (mem_inf.2 ⟨nativeEmb_mem k, mem_centralizer_aNC_iff.1 hk⟩) _
    (mem_twoAQNC_iff.1 hq)

theorem mem_twoAQNC_conj_iff
    {k q : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) :
    k * q * k⁻¹ ∈ twoAQNC ↔ q ∈ twoAQNC := by
  refine ⟨fun h => ?_, conj_mem_twoAQNC hk⟩
  have := conj_mem_twoAQNC (inv_mem hk) h
  simpa [mul_assoc] using this

theorem inQa_smul
    {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (v : Vt) :
    inQa (k • v) ↔ inQa v := by
  unfold inQa
  rw [coe_smul_conjVert, mem_twoAQNC_conj_iff hk]

theorem inQa2_smul
    {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (v : Vt) :
    inQa2 (k • v) ↔ inQa2 v := by
  unfold inQa2
  rw [aNC_mul_smul hk, conj_pow, mem_twoAQNC_conj_iff hk]

theorem fix_conj_eq_image {A P Q : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) :
    {w : Fin 24 → ZMod 2 | (P * A * Q) *ᵥ w = w} = (fun w => P *ᵥ w) '' {w | A *ᵥ w = w} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hw
    refine ⟨Q *ᵥ w, ?_, ?_⟩
    · calc A *ᵥ (Q *ᵥ w) = (Q * P) *ᵥ (A *ᵥ (Q *ᵥ w)) := by rw [hQP, Matrix.one_mulVec]
        _ = Q *ᵥ ((P * A * Q) *ᵥ w) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = Q *ᵥ w := by rw [hw]
    · rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  · rintro ⟨u, hu, rfl⟩
    calc (P * A * Q) *ᵥ (P *ᵥ u) = P *ᵥ (A *ᵥ ((Q * P) *ᵥ u)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = P *ᵥ u := by rw [hQP, Matrix.one_mulVec, hu]

theorem ncard_fix_conj_gen {G : Type*} [Group G] (μ : G →* Matrix (Fin 24) (Fin 24) (ZMod 2))
    (g x : G) : {w : Fin 24 → ZMod 2 | μ (g * x * g⁻¹) *ᵥ w = w}.ncard =
      {w : Fin 24 → ZMod 2 | μ x *ᵥ w = w}.ncard := by
  have hg : μ g * μ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hg' : μ g⁻¹ * μ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, map_mul, fix_conj_eq_image hg hg']
  refine Set.ncard_image_of_injective _ fun u w h => ?_
  have := congrArg (fun z => μ g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec] using this

theorem ncard_fix_conj (g x : NativeSporadic.Co1) :
    {w : Fin 24 → ZMod 2 | matHom (g * x * g⁻¹) *ᵥ w = w}.ncard =
      {w : Fin 24 → ZMod 2 | matHom x *ᵥ w = w}.ncard :=
  ncard_fix_conj_gen matHom g x

theorem fixA_smul {k : NativeSporadic.Co1} (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1))
    (v : Vt) : fixA (k • v) = fixA v := by
  unfold fixA
  rw [aNC_mul_smul hk, ncard_fix_conj]

theorem card_le_of_double_count (R : Vt → Vt → Prop)
    (hR : ∀ k ∈ centralizer ({aNC} : Set NativeSporadic.Co1), ∀ u v, R u v → R (k • u) (k • v))
    (c₀ v₀ : Vt) {m n : ℕ} (hm : m ≤ {v | v ∈ cOrb v₀ ∧ R c₀ v}.ncard)
    (hn : {u | u ∈ cOrb c₀ ∧ R u v₀}.ncard ≤ n) :
    (cOrb c₀).ncard * m ≤ (cOrb v₀).ncard * n := by
  classical
  have hRinv : ∀ k ∈ centralizer ({aNC} : Set NativeSporadic.Co1), ∀ u v,
      R (k • u) (k • v) ↔ R u v := fun k hk u v =>
    ⟨fun h => by simpa using hR k⁻¹ (inv_mem hk) _ _ h, hR k hk u v⟩
  have hfin : ∀ S : Set Vt, S.Finite := fun S => Set.toFinite S
  set s := (hfin (cOrb c₀)).toFinset
  set t := (hfin (cOrb v₀)).toFinset
  have key := Finset.card_mul_le_card_mul (r := R) (s := s) (t := t) (m := m) (n := n)
    (fun c hc => ?_) (fun v hv => ?_)
  · rw [← Set.ncard_eq_toFinset_card _ (hfin _), ← Set.ncard_eq_toFinset_card _ (hfin _)] at key
    exact key
  · rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    refine hm.trans (le_of_eq ?_)
    rw [Finset.bipartiteAbove, ← Set.ncard_coe_finset, Finset.coe_filter]
    have : {v | v ∈ t ∧ R (k • c₀) v} = (k • ·) '' {v | v ∈ cOrb v₀ ∧ R c₀ v} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Set.mem_image, t]
      constructor
      · rintro ⟨hv, hR'⟩
        refine ⟨k⁻¹ • v, ⟨smul_mem_cOrb (inv_mem hk) hv, ?_⟩, smul_inv_smul _ _⟩
        rw [← hRinv k hk, smul_inv_smul]
        exact hR'
      · rintro ⟨w, ⟨hw, hR'⟩, rfl⟩
        exact ⟨smul_mem_cOrb hk hw, hR k hk _ _ hR'⟩
    rw [this, Set.ncard_image_of_injective _ (MulAction.injective k)]
  · rw [Set.Finite.mem_toFinset] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    refine le_trans (le_of_eq ?_) hn
    rw [Finset.bipartiteBelow, ← Set.ncard_coe_finset, Finset.coe_filter]
    have : {u | u ∈ s ∧ R u (k • v₀)} = (k • ·) '' {u | u ∈ cOrb c₀ ∧ R u v₀} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Set.mem_image, s]
      constructor
      · rintro ⟨hu, hR'⟩
        refine ⟨k⁻¹ • u, ⟨smul_mem_cOrb (inv_mem hk) hu, ?_⟩, smul_inv_smul _ _⟩
        rw [← hRinv k hk, smul_inv_smul]
        exact hR'
      · rintro ⟨w, ⟨hw, hR'⟩, rfl⟩
        exact ⟨smul_mem_cOrb hk hw, hR k hk _ _ hR'⟩
    rw [this, Set.ncard_image_of_injective _ (MulAction.injective k)]

end CFSG.Sporadic.Co1Patterson
