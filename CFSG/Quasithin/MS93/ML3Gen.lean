module

public import CFSG.Quasithin.MS93.ML3Basic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.MS93

open Matrix CFSG.Quasithin
open scoped commutatorElement

variable {F : Type} [Field F]

private theorem commutatorElement_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_generator_pow_succ [Finite F] :
    ∃ c : F, c ≠ 0 ∧ ∀ a : F, a ≠ 0 → ∃ k : ℕ, c ^ (k + 1) = a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨(g : F), g.ne_zero, fun a ha => ?_⟩
  have hmem : Units.mk0 a ha ∈ Submonoid.powers g :=
    (mem_powers_iff_mem_zpowers).mpr (hg _)
  obtain ⟨k, hk⟩ := hmem
  have hpos : 0 < orderOf g := orderOf_pos g
  refine ⟨k + orderOf g - 1, ?_⟩
  have hk' : (g : F) ^ k = a := by
    have := congrArg Units.val hk
    simpa using this
  rw [show k + orderOf g - 1 + 1 = k + orderOf g by omega, pow_add, hk',
    ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, mul_one]

theorem closure_rootElt_three_eq_top {c : F} (hc0 : c ≠ 0)
    (hc : ∀ a : F, a ≠ 0 → ∃ k : ℕ, c ^ (k + 1) = a) :
    Subgroup.closure {rootElt 0 2 c, rootElt 2 1 (1 : F), rootElt 1 0 (1 : F)} = ⊤ := by
  set H := Subgroup.closure {rootElt 0 2 c, rootElt 2 1 (1 : F), rootElt 1 0 (1 : F)} with hH
  have h02c : rootElt 0 2 c ∈ H := Subgroup.subset_closure (by simp)
  have h21 : rootElt 2 1 (1 : F) ∈ H := Subgroup.subset_closure (by simp)
  have h10 : rootElt 1 0 (1 : F) ∈ H := Subgroup.subset_closure (by simp)
  have comm : ∀ {i j l : Fin 3}, i ≠ j → j ≠ l → i ≠ l → ∀ a b : F,
      rootElt i j a ∈ H → rootElt j l b ∈ H → rootElt i l (a * b) ∈ H :=
    fun hij hjl hil a b ha hb => by
      rw [← rootElt_commutator hij hjl hil]
      exact commutatorElement_mem_of_mem ha hb
  have h20 : rootElt 2 0 (1 : F) ∈ H := by
    simpa using comm (by decide) (by decide) (by decide) 1 1 h21 h10
  have hk : ∀ k : ℕ, rootElt 2 1 (c ^ k) ∈ H ∧ rootElt 0 1 (c ^ (k + 1)) ∈ H := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simpa using h21, ?_⟩
      simpa using comm (by decide) (by decide) (by decide) c 1 h02c h21
    | succ k ih =>
      have h1 : rootElt 2 1 (c ^ (k + 1)) ∈ H := by
        simpa using comm (by decide) (by decide) (by decide) 1 (c ^ (k + 1)) h20 ih.2
      refine ⟨h1, ?_⟩
      have := comm (by decide) (by decide) (by decide) c (c ^ (k + 1)) h02c h1
      rwa [← pow_succ'] at this
  have hX21 : ∀ a : F, rootElt 2 1 a ∈ H := by
    intro a
    by_cases ha : a = 0
    · rw [ha, rootElt_zero]; exact H.one_mem
    · obtain ⟨k, rfl⟩ := hc a ha
      exact (hk (k + 1)).1
  have hX01 : ∀ a : F, rootElt 0 1 a ∈ H := by
    intro a
    by_cases ha : a = 0
    · rw [ha, rootElt_zero]; exact H.one_mem
    · obtain ⟨k, rfl⟩ := hc a ha
      exact (hk k).2
  have hX20 : ∀ a : F, rootElt 2 0 a ∈ H := fun a => by
    simpa using comm (by decide) (by decide) (by decide) a 1 (hX21 a) h10
  have h12c : rootElt 1 2 c ∈ H := by
    simpa using comm (by decide) (by decide) (by decide) 1 c h10 h02c
  have hX10 : ∀ a : F, rootElt 1 0 a ∈ H := fun a => by
    have := comm (by decide) (by decide) (by decide) c (c⁻¹ * a) h12c (hX20 _)
    rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at this
  have hX12 : ∀ a : F, rootElt 1 2 a ∈ H := fun a => by
    have := comm (by decide) (by decide) (by decide) (a * c⁻¹) c (hX10 _) h02c
    rwa [mul_assoc, inv_mul_cancel₀ hc0, mul_one] at this
  have hX02 : ∀ a : F, rootElt 0 2 a ∈ H := fun a => by
    simpa using comm (by decide) (by decide) (by decide) a 1 (hX01 a) (hX12 1)
  refine eq_top_of_rootElt_mem fun i j a hij => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact hX01 a
    | exact hX02 a
    | exact hX10 a
    | exact hX12 a
    | exact hX20 a
    | exact hX21 a

theorem ms11i [Finite F] {t : SL3 F} (ht : t ∈ rootGroup 0 2) (ht1 : t ≠ 1) :
    ∃ g₁ g₂ : SL3 F, Subgroup.closure {t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹} = ⊤ := by
  obtain ⟨a, rfl⟩ := ht
  have ha : a ≠ 0 := fun h => ht1 (by rw [h, rootElt_zero])
  obtain ⟨c, hc0, hc⟩ := exists_generator_pow_succ (F := F)
  obtain ⟨h₁, hh₁⟩ := exists_conj_rootElt_eq ha c hc0
  obtain ⟨d, hd⟩ := exists_conj_rootElt_eq ha 1 one_ne_zero
  have hcyc1 : cyc * rootElt 0 2 (1 : F) * cyc⁻¹ = rootElt 1 0 1 := cyc_conj_rootElt 0 2 1
  have hcyc2 : cyc * rootElt 1 0 (1 : F) * cyc⁻¹ = rootElt 2 1 1 := cyc_conj_rootElt 1 0 1
  set h₂ : SL3 F := cyc * cyc * d with hh₂
  set h₃ : SL3 F := cyc * d with hh₃
  have e₂ : h₂ * rootElt 0 2 a * h₂⁻¹ = rootElt 2 1 1 := by
    rw [hh₂, ← hcyc2, ← hcyc1, ← hd]
    group
  have e₃ : h₃ * rootElt 0 2 a * h₃⁻¹ = rootElt 1 0 1 := by
    rw [hh₃, ← hcyc1, ← hd]
    group
  refine ⟨h₁⁻¹ * h₂, h₁⁻¹ * h₃, ?_⟩
  set K' := Subgroup.closure {rootElt 0 2 a, (h₁⁻¹ * h₂) * rootElt 0 2 a * (h₁⁻¹ * h₂)⁻¹,
    (h₁⁻¹ * h₃) * rootElt 0 2 a * (h₁⁻¹ * h₃)⁻¹} with hK'
  have key : ∀ g : SL3 F, h₁ * (h₁⁻¹ * g * rootElt 0 2 a * (h₁⁻¹ * g)⁻¹) * h₁⁻¹ =
      g * rootElt 0 2 a * g⁻¹ := fun g => by group
  have hle : Subgroup.closure {rootElt 0 2 c, rootElt 2 1 (1 : F), rootElt 1 0 (1 : F)} ≤
      K'.map (MulAut.conj h₁).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact ⟨rootElt 0 2 a, Subgroup.subset_closure (by simp), by simpa using hh₁⟩
    · refine ⟨(h₁⁻¹ * h₂) * rootElt 0 2 a * (h₁⁻¹ * h₂)⁻¹, Subgroup.subset_closure (by simp), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [key, e₂]
    · refine ⟨(h₁⁻¹ * h₃) * rootElt 0 2 a * (h₁⁻¹ * h₃)⁻¹, Subgroup.subset_closure (by simp), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [key, e₃]
  rw [closure_rootElt_three_eq_top hc0 hc] at hle
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hle (Subgroup.mem_top ((MulAut.conj h₁) y))
  have hzy' : z = y := (MulAut.conj h₁).injective hzy
  rwa [← hzy']

theorem ms11i_of_surjective [Finite F] {K : Type*} [Group K] {α : K →* SL3 F}
    (hα : Function.Surjective α) {t : K} (ht : α t ∈ rootGroup 0 2) (ht1 : α t ≠ 1) :
    ∃ g₁ g₂ : K, Subgroup.closure {t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹} ⊔ α.ker = ⊤ := by
  obtain ⟨h₁, h₂, hgen⟩ := ms11i ht ht1
  obtain ⟨g₁, rfl⟩ := hα h₁
  obtain ⟨g₂, rfl⟩ := hα h₂
  refine ⟨g₁, g₂, ?_⟩
  rw [← Subgroup.comap_map_eq, MonoidHom.map_closure, eq_top_iff]
  intro y _
  rw [Subgroup.mem_comap]
  have himage : α '' {t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹} =
      {α t, α g₁ * α t * (α g₁)⁻¹, α g₂ * α t * (α g₂)⁻¹} := by
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [himage, hgen]
  exact Subgroup.mem_top _

section Module

open scoped Pointwise

variable {V : Type*} [CommGroup V]

theorem commV_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : commV X ≤ commV Y := by
  unfold commV
  refine Subgroup.closure_mono ?_
  rintro w ⟨x, hx, v, rfl⟩
  exact ⟨x, h hx, v, rfl⟩

theorem mem_commV_of_mem {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (v : V) :
    x v * v⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem commV_closure_eq_iSup (S : Set (MulAut V)) :
    commV (Subgroup.closure S) = ⨆ s ∈ S, commV (Subgroup.zpowers s) := by
  set D := ⨆ s ∈ S, commV (Subgroup.zpowers s) with hD
  refine le_antisymm ?_ (iSup₂_le fun s hs =>
    commV_mono ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure hs)))
  let T : Subgroup (MulAut V) :=
    { carrier := {y | ∀ v : V, y v * v⁻¹ ∈ D}
      mul_mem' := fun {y z} hy hz v => by
        have := D.mul_mem (hy (z v)) (hz v)
        simpa [MulAut.mul_apply, mul_assoc] using this
      one_mem' := fun v => by simp
      inv_mem' := fun {y} hy v => by
        have h := D.inv_mem (hy (y⁻¹ v))
        have h2 : y (y⁻¹ v) = v := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        rwa [h2, _root_.mul_inv_rev, inv_inv] at h }
  have hST : Subgroup.closure S ≤ T := by
    rw [Subgroup.closure_le]
    intro s hs v
    exact (le_iSup₂ (f := fun s (_ : s ∈ S) => commV (Subgroup.zpowers s)) s hs)
      (mem_commV_of_mem (Subgroup.mem_zpowers s) v)
  unfold commV
  rw [Subgroup.closure_le]
  rintro w ⟨y, hy, v, rfl⟩
  exact hST hy v

theorem card_commV_zpowers_conj [Finite V] (g x : MulAut V) :
    Nat.card (commV (Subgroup.zpowers (g * x * g⁻¹))) =
      Nat.card (commV (Subgroup.zpowers x)) := by
  have hmap : commV (Subgroup.zpowers (g * x * g⁻¹)) =
      (commV (Subgroup.zpowers x)).map g.toMonoidHom := by
    apply le_antisymm
    · unfold commV
      rw [Subgroup.closure_le]
      rintro w ⟨y, hy, v, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine ⟨(x ^ k) (g⁻¹ v) * (g⁻¹ v)⁻¹,
        Subgroup.subset_closure ⟨x ^ k, Subgroup.zpow_mem_zpowers x k, g⁻¹ v, rfl⟩, ?_⟩
      have hconj : (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ := by
        rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_zpow]
        rfl
      simp [hconj, MulAut.mul_apply]
    · rw [Subgroup.map_le_iff_le_comap]
      show Subgroup.closure _ ≤ _
      rw [Subgroup.closure_le]
      rintro w ⟨y, hy, v, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hconj : (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ := by
        rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_zpow]
        rfl
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have := mem_commV_of_mem (Subgroup.zpow_mem_zpowers (g * x * g⁻¹) k) (g v)
      rw [hconj] at this
      simpa [MulAut.mul_apply] using this
  rw [hmap, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]

theorem card_sup_le_mul [Finite V] (A B : Subgroup V) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have h : ((A ⊔ B : Subgroup V) : Set V) = (A : Set V) * (B : Set V) := Subgroup.mul_normal A B
  calc Nat.card ↥(A ⊔ B) = Nat.card ((A : Set V) * (B : Set V)) := by
        rw [← h]; rfl
    _ ≤ Nat.card (A : Set V) * Nat.card (B : Set V) := Set.natCard_mul_le
    _ = Nat.card A * Nat.card B := rfl

end Module

end CFSG.Quasithin.MS93
