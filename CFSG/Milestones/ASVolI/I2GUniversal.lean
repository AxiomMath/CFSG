module

public import CFSG.Milestones.ASVolI.I2
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.ASVolI

open CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section FreeModule

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

@[expose] def burnsideI23_shift (g : Γ) : (Γ → V) →* (Γ → V) where
  toFun f := fun h => f (g⁻¹ * h)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem burnsideI23_shift_apply (g : Γ) (f : Γ → V) (h : Γ) :
    burnsideI23_shift g f h = f (g⁻¹ * h) := rfl

theorem burnsideI23_shift_shift (g₁ g₂ : Γ) (f : Γ → V) :
    burnsideI23_shift g₁ (burnsideI23_shift g₂ f) = burnsideI23_shift (g₁ * g₂) f := by
  funext h
  simp [burnsideI23_shift_apply, mul_assoc]

theorem burnsideI23_shift_one (f : Γ → V) : burnsideI23_shift 1 f = f := by
  funext h
  simp [burnsideI23_shift_apply]

@[expose] def burnsideI23_comm (Λ : Subgroup Γ) (S : Subgroup (Γ → V)) : Subgroup (Γ → V) :=
  Subgroup.closure {y | ∃ l ∈ Λ, ∃ x ∈ S, y = burnsideI23_shift l x * x⁻¹}

theorem burnsideI23_comm_mem {Λ : Subgroup Γ} {S : Subgroup (Γ → V)} {l : Γ} (hl : l ∈ Λ)
    {x : Γ → V} (hx : x ∈ S) : burnsideI23_shift l x * x⁻¹ ∈ burnsideI23_comm Λ S :=
  Subgroup.subset_closure ⟨l, hl, x, hx, rfl⟩

theorem burnsideI23_comm_le {Λ : Subgroup Γ} {S : Subgroup (Γ → V)}
    (hS : ∀ l ∈ Λ, ∀ x ∈ S, burnsideI23_shift l x ∈ S) : burnsideI23_comm Λ S ≤ S := by
  rw [burnsideI23_comm, Subgroup.closure_le]
  rintro _ ⟨l, hl, x, hx, rfl⟩
  exact S.mul_mem (hS l hl x hx) (S.inv_mem hx)

theorem burnsideI23_comm_inv {Λ : Subgroup Γ} [Λ.Normal] {S : Subgroup (Γ → V)}
    (hS : ∀ g : Γ, ∀ x ∈ S, burnsideI23_shift g x ∈ S) :
    ∀ g : Γ, ∀ y ∈ burnsideI23_comm Λ S, burnsideI23_shift g y ∈ burnsideI23_comm Λ S := by
  intro g y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, x, hx, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨g * l * g⁻¹, ‹Λ.Normal›.conj_mem l hl g,
      burnsideI23_shift g x, hS g x hx, ?_⟩
    rw [map_mul, map_inv, burnsideI23_shift_shift, burnsideI23_shift_shift]
    simp [mul_assoc]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

@[expose] def burnsideI23_low (Λ : Subgroup Γ) : ℕ → Subgroup (Γ → V)
  | 0 => ⊤
  | k + 1 => burnsideI23_comm Λ (burnsideI23_low Λ k)

theorem burnsideI23_low_inv (Λ : Subgroup Γ) [Λ.Normal] (k : ℕ) :
    ∀ g : Γ, ∀ x ∈ burnsideI23_low (V := V) Λ k, burnsideI23_shift g x ∈ burnsideI23_low Λ k := by
  induction k with
  | zero => intro g x _; exact Subgroup.mem_top _
  | succ k ih => exact burnsideI23_comm_inv ih

theorem burnsideI23_low_succ_le (Λ : Subgroup Γ) [Λ.Normal] (k : ℕ) :
    burnsideI23_low (V := V) Λ (k + 1) ≤ burnsideI23_low Λ k :=
  burnsideI23_comm_le (fun l _ x hx => burnsideI23_low_inv Λ k l x hx)

theorem burnsideI23_low_antitone (Λ : Subgroup Γ) [Λ.Normal] :
    Antitone (burnsideI23_low (V := V) Λ) :=
  antitone_nat_of_succ_le (burnsideI23_low_succ_le Λ)

theorem burnsideI23_exists_stable [Finite Γ] [Finite V] (Λ : Subgroup Γ) [Λ.Normal] :
    ∃ k, burnsideI23_low (V := V) Λ (k + 1) = burnsideI23_low Λ k := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (burnsideI23_low (V := V) Λ)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨i, le_antisymm (burnsideI23_low_succ_le Λ i)
      (h ▸ burnsideI23_low_antitone Λ (Nat.succ_le_of_lt hlt))⟩
  · exact ⟨j, le_antisymm (burnsideI23_low_succ_le Λ j)
      (h.symm ▸ burnsideI23_low_antitone Λ (Nat.succ_le_of_lt hlt))⟩

@[expose] noncomputable def burnsideI23_core [Finite Γ] [Finite V] (Λ : Subgroup Γ) [Λ.Normal] :
    Subgroup (Γ → V) :=
  burnsideI23_low Λ (Classical.choose (burnsideI23_exists_stable (V := V) Λ))

theorem burnsideI23_comm_core [Finite Γ] [Finite V] (Λ : Subgroup Γ) [Λ.Normal] :
    burnsideI23_comm Λ (burnsideI23_core (V := V) Λ) = burnsideI23_core Λ :=
  Classical.choose_spec (burnsideI23_exists_stable (V := V) Λ)

theorem burnsideI23_core_inv [Finite Γ] [Finite V] (Λ : Subgroup Γ) [Λ.Normal] :
    ∀ g : Γ, ∀ x ∈ burnsideI23_core (V := V) Λ, burnsideI23_shift g x ∈ burnsideI23_core Λ :=
  burnsideI23_low_inv Λ _

theorem burnsideI23_exists_core_eq_low [Finite Γ] [Finite V] (Λ : Subgroup Γ) [Λ.Normal] :
    ∃ k, burnsideI23_core (V := V) Λ = burnsideI23_low Λ k := ⟨_, rfl⟩

end FreeModule

section Cover

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ] [Fintype Γ] [Finite V]

@[expose] def burnsideI23_aug (σ : Γ →* MulAut V) : (Γ → V) →* V where
  toFun f := ∏ h : Γ, σ h (f h)
  map_one' := by simp
  map_mul' f g := by simp [Finset.prod_mul_distrib]

theorem burnsideI23_aug_apply (σ : Γ →* MulAut V) (f : Γ → V) :
    burnsideI23_aug σ f = ∏ h : Γ, σ h (f h) := rfl

theorem burnsideI23_aug_shift (σ : Γ →* MulAut V) (g : Γ) (f : Γ → V) :
    burnsideI23_aug σ (burnsideI23_shift g f) = σ g (burnsideI23_aug σ f) := by
  rw [burnsideI23_aug_apply, burnsideI23_aug_apply, map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft g⁻¹) _ _ (fun h => ?_)
  simp only [burnsideI23_shift_apply, Equiv.coe_mulLeft]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem burnsideI23_aug_surjective (σ : Γ →* MulAut V) : Function.Surjective (burnsideI23_aug σ) := by
  classical
  intro v
  refine ⟨Pi.mulSingle 1 v, ?_⟩
  rw [burnsideI23_aug_apply, Finset.prod_eq_single (1 : Γ)]
  · simp
  · intro h _ hh
    simp [Pi.mulSingle_eq_of_ne hh]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (σ : Γ →* MulAut V) (Λ : Subgroup Γ) [Λ.Normal] (W0 : Subgroup V)

@[expose] noncomputable def burnsideI23_K0 : Subgroup (Γ → V) :=
  burnsideI23_core (V := V) Λ ⊓ W0.comap (burnsideI23_aug σ)

@[expose] noncomputable def burnsideI23_D : Subgroup (Γ → V) :=
  burnsideI23_comm Λ (burnsideI23_K0 σ Λ W0)

theorem burnsideI23_K0_inv (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) :
    ∀ g : Γ, ∀ x ∈ burnsideI23_K0 σ Λ W0, burnsideI23_shift g x ∈ burnsideI23_K0 σ Λ W0 := by
  intro g x hx
  refine ⟨burnsideI23_core_inv Λ g x hx.1, ?_⟩
  show burnsideI23_aug σ (burnsideI23_shift g x) ∈ W0
  rw [burnsideI23_aug_shift]
  exact hW0 g _ hx.2

theorem burnsideI23_D_inv (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) :
    ∀ g : Γ, ∀ y ∈ burnsideI23_D σ Λ W0, burnsideI23_shift g y ∈ burnsideI23_D σ Λ W0 :=
  burnsideI23_comm_inv (burnsideI23_K0_inv σ Λ W0 hW0)

theorem burnsideI23_aug_D (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w) :
    ∀ y ∈ burnsideI23_D σ Λ W0, burnsideI23_aug σ y = 1 := by
  have h : burnsideI23_D σ Λ W0 ≤ (burnsideI23_aug σ).ker := by
    rw [burnsideI23_D, burnsideI23_comm, Subgroup.closure_le]
    rintro _ ⟨l, hl, k, hk, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, burnsideI23_aug_shift,
      hW0 l hl _ hk.2, mul_inv_cancel]
  exact fun y hy => h hy

noncomputable abbrev burnsideI23_U : Type :=
  ↥(burnsideI23_core (V := V) Λ) ⧸
    (burnsideI23_D σ Λ W0).subgroupOf (burnsideI23_core (V := V) Λ)

end Cover

section Action

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ] [Fintype Γ] [Finite V]
  (σ : Γ →* MulAut V) (Λ : Subgroup Γ) [Λ.Normal] (W0 : Subgroup V)

@[expose] noncomputable def burnsideI23_actE (g : Γ) :
    ↥(burnsideI23_core (V := V) Λ) →* ↥(burnsideI23_core (V := V) Λ) where
  toFun x := ⟨burnsideI23_shift g (x : Γ → V), burnsideI23_core_inv (V := V) Λ g (x : Γ → V) x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem burnsideI23_actE_coe (g : Γ) (x : ↥(burnsideI23_core (V := V) Λ)) :
    ((burnsideI23_actE Λ g x : ↥(burnsideI23_core (V := V) Λ)) : Γ → V) =
      burnsideI23_shift g x := rfl

@[expose] noncomputable def burnsideI23_actU (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) (g : Γ) :
    burnsideI23_U σ Λ W0 →* burnsideI23_U σ Λ W0 :=
  QuotientGroup.map _ _ (burnsideI23_actE Λ g) (fun d hd => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, burnsideI23_actE_coe]
    exact burnsideI23_D_inv σ Λ W0 hW0 g _ (Subgroup.mem_subgroupOf.1 hd))

theorem burnsideI23_actU_mk (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) (g : Γ)
    (x : ↥(burnsideI23_core (V := V) Λ)) :
    burnsideI23_actU σ Λ W0 hW0 g (QuotientGroup.mk x) =
      QuotientGroup.mk (burnsideI23_actE Λ g x) := rfl

theorem burnsideI23_actU_mul (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) (g h : Γ)
    (u : burnsideI23_U σ Λ W0) :
    burnsideI23_actU σ Λ W0 hW0 (g * h) u =
      burnsideI23_actU σ Λ W0 hW0 g (burnsideI23_actU σ Λ W0 hW0 h u) := by
  induction u using QuotientGroup.induction_on with
  | H x => exact congrArg QuotientGroup.mk (Subtype.ext (burnsideI23_shift_shift g h (x : Γ → V)).symm)

theorem burnsideI23_actU_one (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0)
    (u : burnsideI23_U σ Λ W0) : burnsideI23_actU σ Λ W0 hW0 1 u = u := by
  induction u using QuotientGroup.induction_on with
  | H x => exact congrArg QuotientGroup.mk (Subtype.ext (burnsideI23_shift_one (x : Γ → V)))

@[expose] noncomputable def burnsideI23_rho (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) :
    Γ →* MulAut (burnsideI23_U σ Λ W0) where
  toFun g :=
    { toFun := burnsideI23_actU σ Λ W0 hW0 g
      invFun := burnsideI23_actU σ Λ W0 hW0 g⁻¹
      left_inv := fun u => by
        rw [← burnsideI23_actU_mul, inv_mul_cancel, burnsideI23_actU_one]
      right_inv := fun u => by
        rw [← burnsideI23_actU_mul, mul_inv_cancel, burnsideI23_actU_one]
      map_mul' := map_mul _ }
  map_one' := by
    ext u
    exact burnsideI23_actU_one σ Λ W0 hW0 u
  map_mul' g h := by
    ext u
    exact burnsideI23_actU_mul σ Λ W0 hW0 g h u

theorem burnsideI23_rho_apply (hW0 : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) (g : Γ)
    (u : burnsideI23_U σ Λ W0) :
    burnsideI23_rho σ Λ W0 hW0 g u = burnsideI23_actU σ Λ W0 hW0 g u := rfl

@[expose] noncomputable def burnsideI23_augE : ↥(burnsideI23_core (V := V) Λ) →* V where
  toFun x := burnsideI23_aug σ x
  map_one' := map_one _
  map_mul' x y := map_mul _ _ _

@[expose] noncomputable def burnsideI23_theta (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w) :
    burnsideI23_U σ Λ W0 →* V :=
  QuotientGroup.lift _ (burnsideI23_augE σ Λ)
    (fun d hd => by
      rw [Subgroup.mem_subgroupOf] at hd
      exact burnsideI23_aug_D σ Λ W0 hW0 _ hd)

theorem burnsideI23_theta_rho (hW0i : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0)
    (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w) (g : Γ) (u : burnsideI23_U σ Λ W0) :
    burnsideI23_theta σ Λ W0 hW0 (burnsideI23_rho σ Λ W0 hW0i g u) =
      σ g (burnsideI23_theta σ Λ W0 hW0 u) := by
  induction u using QuotientGroup.induction_on with
  | H x => exact burnsideI23_aug_shift σ g x

theorem burnsideI23_U_sq (u : burnsideI23_U σ Λ W0) (hV : ∀ v : V, v ^ 2 = 1) : u ^ 2 = 1 := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    apply Subtype.ext
    funext h
    exact hV _

theorem burnsideI23_map_aug_low (hcomm : Subgroup.closure
      {w : V | ∃ l ∈ Λ, ∃ v : V, w = σ l v * v⁻¹} = ⊤) (k : ℕ) :
    (burnsideI23_low (V := V) Λ k).map (burnsideI23_aug σ) = ⊤ := by
  induction k with
  | zero =>
    rw [burnsideI23_low, Subgroup.map_top, MonoidHom.range_eq_top]
    exact burnsideI23_aug_surjective σ
  | succ k ih =>
    rw [eq_top_iff, ← hcomm, Subgroup.closure_le]
    rintro _ ⟨l, hl, v, rfl⟩
    have hv : v ∈ (burnsideI23_low (V := V) Λ k).map (burnsideI23_aug σ) := by rw [ih]; trivial
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨burnsideI23_shift l x * x⁻¹, Subgroup.subset_closure ⟨l, hl, x, hx, rfl⟩, ?_⟩
    rw [map_mul, map_inv, burnsideI23_aug_shift]

end Action

section CoverProps

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ] [Fintype Γ] [Finite V]
  (σ : Γ →* MulAut V) (Λ : Subgroup Γ) [Λ.Normal] (W0 : Subgroup V)

theorem burnsideI23_theta_surjective
    (hcomm : Subgroup.closure {w : V | ∃ l ∈ Λ, ∃ v : V, w = σ l v * v⁻¹} = ⊤)
    (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w) :
    Function.Surjective (burnsideI23_theta σ Λ W0 hW0) := by
  intro v
  obtain ⟨k, hk⟩ := burnsideI23_exists_core_eq_low (V := V) Λ
  have hv : v ∈ (burnsideI23_core (V := V) Λ).map (burnsideI23_aug σ) := by
    rw [hk, burnsideI23_map_aug_low σ Λ hcomm k]
    trivial
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩

theorem burnsideI23_K_fix (hW0i : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0)
    (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w) :
    ∀ x ∈ Λ.map (burnsideI23_rho σ Λ W0 hW0i),
      ∀ u ∈ W0.comap (burnsideI23_theta σ Λ W0 hW0), x u = u := by
  rintro _ ⟨l, hl, rfl⟩ u hu
  induction u using QuotientGroup.induction_on with
  | H e =>
    rw [burnsideI23_rho_apply, burnsideI23_actU_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hK0 : (e : Γ → V) ∈ burnsideI23_K0 σ Λ W0 := ⟨e.2, hu⟩
    have h1 : (burnsideI23_shift l (e : Γ → V) * (e : Γ → V)⁻¹)⁻¹ ∈ burnsideI23_D σ Λ W0 :=
      Subgroup.inv_mem _ (burnsideI23_comm_mem hl hK0)
    have h2 : (((burnsideI23_actE Λ l e)⁻¹ * e : ↥(burnsideI23_core (V := V) Λ)) : Γ → V) =
        (burnsideI23_shift l (e : Γ → V) * (e : Γ → V)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, burnsideI23_actE_coe, mul_inv_rev, inv_inv]
      exact mul_comm _ _
    rw [h2]
    exact h1

open CFSG.Quasithin in
theorem burnsideI23_commV_top (hW0i : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0) :
    commV (Λ.map (burnsideI23_rho σ Λ W0 hW0i)) = ⊤ := by
  have hcore : ∀ y, y ∈ burnsideI23_comm Λ (burnsideI23_core (V := V) Λ) →
      y ∈ burnsideI23_core (V := V) Λ := by
    intro y hy
    rwa [burnsideI23_comm_core] at hy
  have key : ∀ y (hy : y ∈ burnsideI23_comm Λ (burnsideI23_core (V := V) Λ)),
      (QuotientGroup.mk ⟨y, hcore y hy⟩ : burnsideI23_U σ Λ W0) ∈
        commV (Λ.map (burnsideI23_rho σ Λ W0 hW0i)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hy
      have hx' : (x : Γ → V) ∈ burnsideI23_core (V := V) Λ := hx
      have h1 : (QuotientGroup.mk ⟨_, hcore _ (burnsideI23_comm_mem hl hx)⟩ :
          burnsideI23_U σ Λ W0) =
          burnsideI23_rho σ Λ W0 hW0i l (QuotientGroup.mk ⟨x, hx'⟩) *
            (QuotientGroup.mk ⟨x, hx'⟩)⁻¹ := by
        rw [burnsideI23_rho_apply, burnsideI23_actU_mk, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul]
        rfl
      rw [h1]
      exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ hl, _, rfl⟩
    | one =>
      have : (QuotientGroup.mk ⟨(1 : Γ → V), Subgroup.one_mem _⟩ : burnsideI23_U σ Λ W0) = 1 :=
        QuotientGroup.mk_one _
      rw [this]
      exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      have : (QuotientGroup.mk ⟨a * b, hcore _ (Subgroup.mul_mem _ ha hb)⟩ :
          burnsideI23_U σ Λ W0) =
          (QuotientGroup.mk ⟨a, hcore _ ha⟩) * (QuotientGroup.mk ⟨b, hcore _ hb⟩) :=
        rfl
      rw [this]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have : (QuotientGroup.mk ⟨a⁻¹, hcore _ (Subgroup.inv_mem _ ha)⟩ :
          burnsideI23_U σ Λ W0) = (QuotientGroup.mk ⟨a, hcore _ ha⟩)⁻¹ :=
        rfl
      rw [this]
      exact Subgroup.inv_mem _ iha
  rw [eq_top_iff]
  intro u _
  induction u using QuotientGroup.induction_on with
  | H e => exact key e.1 (by rw [burnsideI23_comm_core]; exact e.2)

end CoverProps

theorem burnsideI23_exists_lift {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C]
    (hA : ∀ a : A, a ^ 2 = 1) (hB : ∀ b : B, b ^ 2 = 1) (hC : ∀ c : C, c ^ 2 = 1)
    (p : B →* C) (hp : Function.Surjective p) (q : A →* C) :
    ∃ l : A →* B, ∀ a, p (l a) = q a := by
  have mod2 : ∀ {X : Type} [CommGroup X], (∀ x : X, x ^ 2 = 1) → Module (ZMod 2) (Additive X) :=
    fun {X} _ hX => AddCommGroup.zmodModule (fun a => by
      rw [two_nsmul]
      have h := hX (Additive.toMul a)
      rw [pow_two] at h
      exact congrArg Additive.ofMul h)
  letI : Module (ZMod 2) (Additive A) := mod2 hA
  letI : Module (ZMod 2) (Additive B) := mod2 hB
  letI : Module (ZMod 2) (Additive C) := mod2 hC
  let pl : Additive B →ₗ[ZMod 2] Additive C :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive p)
  let ql : Additive A →ₗ[ZMod 2] Additive C :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive q)
  have hpl : Function.Surjective pl := fun c => by
    obtain ⟨b, hb⟩ := hp (Additive.toMul c)
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property pl ql hpl
  refine ⟨MonoidHom.toAdditive.symm h.toAddMonoidHom, fun a => ?_⟩
  have := congrArg (fun f => Additive.toMul (f (Additive.ofMul a))) hh
  exact this

section Lift

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ] [Fintype Γ]

@[expose] noncomputable def burnsideI23_rep (Λ : Subgroup Γ) (h : Γ) : Γ :=
  (Quotient.mk (QuotientGroup.rightRel Λ) h).out

theorem burnsideI23_rep_mem (Λ : Subgroup Γ) (h : Γ) : h * (burnsideI23_rep Λ h)⁻¹ ∈ Λ :=
  QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel Λ) h)

theorem burnsideI23_rep_mul (Λ : Subgroup Γ) {l : Γ} (hl : l ∈ Λ) (h : Γ) :
    burnsideI23_rep Λ (l * h) = burnsideI23_rep Λ h := by
  unfold burnsideI23_rep
  congr 1
  exact Quotient.sound (QuotientGroup.rightRel_apply.2 (by simpa [mul_assoc] using Λ.inv_mem hl))

@[expose] noncomputable def burnsideI23_lh (Λ : Subgroup Γ) (h : Γ) : ↥Λ :=
  ⟨h * (burnsideI23_rep Λ h)⁻¹, burnsideI23_rep_mem Λ h⟩

theorem burnsideI23_lh_mul (Λ : Subgroup Γ) {l : Γ} (hl : l ∈ Λ) (h : Γ) :
    burnsideI23_lh Λ (l * h) = ⟨l, hl⟩ * burnsideI23_lh Λ h := by
  apply Subtype.ext
  show l * h * (burnsideI23_rep Λ (l * h))⁻¹ = l * (h * (burnsideI23_rep Λ h)⁻¹)
  rw [burnsideI23_rep_mul Λ hl, mul_assoc]

@[expose] noncomputable def burnsideI23_Fmap {V' : Type} [CommGroup V'] (σ : Γ →* MulAut V)
    (Λ : Subgroup Γ) (ρΛ : ↥Λ →* MulAut V') (lam : V →* V') : (Γ → V) →* V' where
  toFun φ := ∏ h : Γ, ρΛ (burnsideI23_lh Λ h) (lam (σ (burnsideI23_rep Λ h) (φ h)))
  map_one' := by simp
  map_mul' φ ψ := by simp [Finset.prod_mul_distrib]

theorem burnsideI23_Fmap_apply {V' : Type} [CommGroup V'] (σ : Γ →* MulAut V)
    (Λ : Subgroup Γ) (ρΛ : ↥Λ →* MulAut V') (lam : V →* V') (φ : Γ → V) :
    burnsideI23_Fmap σ Λ ρΛ lam φ =
      ∏ h : Γ, ρΛ (burnsideI23_lh Λ h) (lam (σ (burnsideI23_rep Λ h) (φ h))) := rfl

theorem burnsideI23_Fmap_shift {V' : Type} [CommGroup V'] (σ : Γ →* MulAut V)
    (Λ : Subgroup Γ) (ρΛ : ↥Λ →* MulAut V') (lam : V →* V') {l : Γ} (hl : l ∈ Λ) (φ : Γ → V) :
    burnsideI23_Fmap σ Λ ρΛ lam (burnsideI23_shift l φ) =
      ρΛ ⟨l, hl⟩ (burnsideI23_Fmap σ Λ ρΛ lam φ) := by
  rw [burnsideI23_Fmap_apply, burnsideI23_Fmap_apply, map_prod]
  symm
  refine Fintype.prod_equiv (Equiv.mulLeft l) _ _ (fun h => ?_)
  simp only [Equiv.coe_mulLeft, burnsideI23_shift_apply, inv_mul_cancel_left,
    burnsideI23_lh_mul Λ hl, burnsideI23_rep_mul Λ hl, map_mul, MulAut.mul_apply]

end Lift

section LiftProps

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ] [Fintype Γ] [Finite V]
  {V' : Type} [CommGroup V'] (σ : Γ →* MulAut V) (Λ : Subgroup Γ) [Λ.Normal] (W0 : Subgroup V)
  (ρΛ : ↥Λ →* MulAut V') (ψ'' : V' →* V ⧸ W0) (lam : V →* V')

theorem burnsideI23_psi_Fmap
    (hlam : ∀ v, ψ'' (lam v) = QuotientGroup.mk v)
    (hequiv : ∀ (l : ↥Λ) (v' : V') (v : V), ψ'' v' = QuotientGroup.mk v →
      ψ'' (ρΛ l v') = QuotientGroup.mk (σ l v)) (φ : Γ → V) :
    ψ'' (burnsideI23_Fmap σ Λ ρΛ lam φ) = QuotientGroup.mk (burnsideI23_aug σ φ) := by
  rw [burnsideI23_Fmap_apply, map_prod, burnsideI23_aug_apply]
  have h1 : (QuotientGroup.mk (∏ h : Γ, σ h (φ h)) : V ⧸ W0) =
      ∏ h : Γ, (QuotientGroup.mk (σ h (φ h)) : V ⧸ W0) :=
    map_prod (QuotientGroup.mk' W0) _ _
  rw [h1]
  refine Finset.prod_congr rfl (fun h _ => ?_)
  rw [hequiv _ _ _ (hlam _)]
  congr 1
  show σ (h * (burnsideI23_rep Λ h)⁻¹) (σ (burnsideI23_rep Λ h) (φ h)) = σ h (φ h)
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem burnsideI23_Fmap_D (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w)
    (hlam : ∀ v, ψ'' (lam v) = QuotientGroup.mk v)
    (hequiv : ∀ (l : ↥Λ) (v' : V') (v : V), ψ'' v' = QuotientGroup.mk v →
      ψ'' (ρΛ l v') = QuotientGroup.mk (σ l v))
    (hfix : ∀ w ∈ ψ''.ker, ∀ l : ↥Λ, ρΛ l w = w) :
    ∀ y ∈ burnsideI23_D σ Λ W0, burnsideI23_Fmap σ Λ ρΛ lam y = 1 := by
  have h : burnsideI23_D σ Λ W0 ≤ (burnsideI23_Fmap σ Λ ρΛ lam).ker := by
    rw [burnsideI23_D, burnsideI23_comm, Subgroup.closure_le]
    rintro _ ⟨l, hl, k, hk, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      burnsideI23_Fmap_shift σ Λ ρΛ lam hl]
    have hk0 : burnsideI23_Fmap σ Λ ρΛ lam k ∈ ψ''.ker := by
      rw [MonoidHom.mem_ker, burnsideI23_psi_Fmap σ Λ W0 ρΛ ψ'' lam hlam hequiv,
        QuotientGroup.eq_one_iff]
      exact hk.2
    rw [hfix _ hk0 ⟨l, hl⟩, mul_inv_cancel]
  exact fun y hy => h hy

theorem burnsideI23_Fmap_low
    (hlam : ∀ v, ψ'' (lam v) = QuotientGroup.mk v)
    (hequiv : ∀ (l : ↥Λ) (v' : V') (v : V), ψ'' v' = QuotientGroup.mk v →
      ψ'' (ρΛ l v') = QuotientGroup.mk (σ l v))
    (hsurj : Function.Surjective ψ'')
    (hfix : ∀ w ∈ ψ''.ker, ∀ l : ↥Λ, ρΛ l w = w)
    (hgen : Subgroup.closure {w : V' | ∃ (l : ↥Λ) (v : V'), w = ρΛ l v * v⁻¹} = ⊤) (k : ℕ) :
    (burnsideI23_low (V := V) Λ k).map (burnsideI23_Fmap σ Λ ρΛ lam) = ⊤ := by
  induction k with
  | zero =>
    rw [burnsideI23_low, Subgroup.map_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    have hsup : ∀ v' : V', v' ∈ (burnsideI23_Fmap σ Λ ρΛ lam).range ⊔ ψ''.ker := by
      intro v'
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ'' v')
      obtain ⟨φ, hφ⟩ := burnsideI23_aug_surjective σ v
      have h1 : ψ'' (burnsideI23_Fmap σ Λ ρΛ lam φ) = ψ'' v' := by
        rw [burnsideI23_psi_Fmap σ Λ W0 ρΛ ψ'' lam hlam hequiv, hφ, hv]
      have h2 : (burnsideI23_Fmap σ Λ ρΛ lam φ)⁻¹ * v' ∈ ψ''.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have : v' = burnsideI23_Fmap σ Λ ρΛ lam φ * ((burnsideI23_Fmap σ Λ ρΛ lam φ)⁻¹ * v') := by
        rw [mul_inv_cancel_left]
      rw [this]
      exact Subgroup.mul_mem_sup ⟨φ, rfl⟩ h2
    rintro _ ⟨l, v, rfl⟩
    obtain ⟨s, hs, w, hw, hv⟩ := Subgroup.mem_sup.1 (hsup v)
    obtain ⟨φ, rfl⟩ := hs
    have hl : (l : Γ) ∈ Λ := l.2
    have e1 : ρΛ l (burnsideI23_Fmap σ Λ ρΛ lam φ) =
        burnsideI23_Fmap σ Λ ρΛ lam (burnsideI23_shift (l : Γ) φ) :=
      (burnsideI23_Fmap_shift σ Λ ρΛ lam hl φ).symm
    rw [← hv, map_mul, hfix w hw l]
    have e2 : ρΛ l (burnsideI23_Fmap σ Λ ρΛ lam φ) * w *
        (burnsideI23_Fmap σ Λ ρΛ lam φ * w)⁻¹ =
        ρΛ l (burnsideI23_Fmap σ Λ ρΛ lam φ) * (burnsideI23_Fmap σ Λ ρΛ lam φ)⁻¹ := by
      group
    rw [e2, e1]
    exact Subgroup.mul_mem _ ⟨_, rfl⟩ (Subgroup.inv_mem _ ⟨_, rfl⟩)
  | succ k ih =>
    rw [burnsideI23_low, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨l, v, rfl⟩
    have hv : v ∈ (burnsideI23_low (V := V) Λ k).map (burnsideI23_Fmap σ Λ ρΛ lam) := by
      rw [ih]; trivial
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨burnsideI23_shift (l : Γ) x * x⁻¹, burnsideI23_comm_mem l.2 hx, ?_⟩
    rw [map_mul, map_inv, burnsideI23_Fmap_shift σ Λ ρΛ lam l.2]

end LiftProps

section Universal

open CFSG.ASVolI.ChIJK CFSG.Quasithin in
theorem burnsideI23_isUniversalCovering {V : Type} [CommGroup V] [Finite V] {Γ : Type} [Group Γ]
    [Fintype Γ] (σ : Γ →* MulAut V) (Λ : Subgroup Γ) [Λ.Normal] (W0 : Subgroup V)
    (hexp : ∀ v : V, v ^ 2 = 1) (hW0i : ∀ g : Γ, ∀ w ∈ W0, σ g w ∈ W0)
    (hW0 : ∀ l ∈ Λ, ∀ w ∈ W0, σ l w = w)
    (hcomm : Subgroup.closure {w : V | ∃ l ∈ Λ, ∃ v : V, w = σ l v * v⁻¹} = ⊤) :
    IsUniversalCovering (Λ.map (burnsideI23_rho σ Λ W0 hW0i))
      (W0.comap (burnsideI23_theta σ Λ W0 hW0)) := by
  refine ⟨fun u hu => mem_fixV.2 (fun x hx => burnsideI23_K_fix σ Λ W0 hW0i hW0 x hx u hu),
    burnsideI23_commV_top σ Λ W0 hW0i, ?_⟩
  intro V' _ _ ρ' W0' ψ' hexp' hfix' hgen' hsurj hker hequiv
  classical
  have hθs := burnsideI23_theta_surjective σ Λ W0 hcomm hW0
  let ι : burnsideI23_U σ Λ W0 ⧸ W0.comap (burnsideI23_theta σ Λ W0 hW0) →* V ⧸ W0 :=
    QuotientGroup.map _ W0 (burnsideI23_theta σ Λ W0 hW0) le_rfl
  have hι : ∀ u : burnsideI23_U σ Λ W0,
      ι (QuotientGroup.mk u) = QuotientGroup.mk (burnsideI23_theta σ Λ W0 hW0 u) := fun u => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [hι, hι, QuotientGroup.eq] at hab
        rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
        exact hab
  have hιsurj : Function.Surjective ι := by
    intro c
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨u, rfl⟩ := hθs v
    exact ⟨QuotientGroup.mk u, rfl⟩
  let ρΛ : ↥Λ →* MulAut V' := ρ'.comp ((burnsideI23_rho σ Λ W0 hW0i).subgroupMap Λ)
  have hρΛ : ∀ (l : ↥Λ) (v' : V'),
      ρΛ l v' = ρ' ⟨burnsideI23_rho σ Λ W0 hW0i l, Subgroup.mem_map_of_mem _ l.2⟩ v' := fun _ _ => rfl
  let ψ'' : V' →* V ⧸ W0 := ι.comp ψ'
  have hψ'' : ∀ v', ψ'' v' = ι (ψ' v') := fun _ => rfl
  have hψsurj : Function.Surjective ψ'' := fun c => by
    obtain ⟨x, hx⟩ := hιsurj c
    obtain ⟨v', hv'⟩ := hsurj x
    exact ⟨v', by rw [hψ'', hv', hx]⟩
  have hψker : ψ''.ker = W0' := by
    rw [← hker]
    ext v'
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ'', ← map_one ι]
    exact hιinj.eq_iff
  have hequivΛ : ∀ (l : ↥Λ) (v' : V') (v : V), ψ'' v' = QuotientGroup.mk v →
      ψ'' (ρΛ l v') = QuotientGroup.mk (σ l v) := by
    intro l v' v hv
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ψ' v')
    have h1 : QuotientGroup.mk (burnsideI23_theta σ Λ W0 hW0 u) = (QuotientGroup.mk v : V ⧸ W0) := by
      rw [← hι, hu, ← hψ'']
      exact hv
    have h2 := hequiv ⟨burnsideI23_rho σ Λ W0 hW0i l, Subgroup.mem_map_of_mem _ l.2⟩ v' u hu.symm
    rw [hρΛ, hψ'', h2, hι, burnsideI23_theta_rho σ Λ W0 hW0i hW0]
    rw [QuotientGroup.eq] at h1 ⊢
    have h3 := hW0i l _ h1
    rwa [map_mul, map_inv] at h3
  have hq : ∀ c : V ⧸ W0, c ^ 2 = 1 := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  obtain ⟨lam, hlam⟩ := burnsideI23_exists_lift hexp hexp' hq ψ'' hψsurj (QuotientGroup.mk' W0)
  have hlam' : ∀ v, ψ'' (lam v) = QuotientGroup.mk v := hlam
  have hfixΛ : ∀ w ∈ ψ''.ker, ∀ l : ↥Λ, ρΛ l w = w := by
    intro w hw l
    rw [hψker] at hw
    exact hfix' w hw _
  have hgenΛ : Subgroup.closure {w : V' | ∃ (l : ↥Λ) (v : V'), w = ρΛ l v * v⁻¹} = ⊤ := by
    rw [eq_top_iff, ← hgen', Subgroup.closure_le]
    rintro _ ⟨g, v, rfl⟩
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.1 g.2
    apply Subgroup.subset_closure
    refine ⟨⟨l, hl⟩, v, ?_⟩
    have : g = ⟨burnsideI23_rho σ Λ W0 hW0i l, Subgroup.mem_map_of_mem _ hl⟩ :=
      Subtype.ext hlg.symm
    rw [this, hρΛ]
  have hlow := burnsideI23_Fmap_low σ Λ W0 ρΛ ψ'' lam hlam' hequivΛ hψsurj hfixΛ hgenΛ
  have hD := burnsideI23_Fmap_D σ Λ W0 ρΛ ψ'' lam hW0 hlam' hequivΛ hfixΛ
  let FE : ↥(burnsideI23_core (V := V) Λ) →* V' :=
    { toFun := fun x => burnsideI23_Fmap σ Λ ρΛ lam x
      map_one' := map_one _
      map_mul' := fun x y => map_mul _ _ _ }
  let θ' : burnsideI23_U σ Λ W0 →* V' :=
    QuotientGroup.lift _ FE (fun d hd => by
      rw [Subgroup.mem_subgroupOf] at hd
      exact hD _ hd)
  have hθ'mk : ∀ x : ↥(burnsideI23_core (V := V) Λ),
      θ' (QuotientGroup.mk x) = burnsideI23_Fmap σ Λ ρΛ lam x := fun _ => rfl
  refine ⟨θ', ?_, ?_, ?_⟩
  · intro v'
    obtain ⟨k, hk⟩ := burnsideI23_exists_core_eq_low (V := V) Λ
    have hv : v' ∈ (burnsideI23_core (V := V) Λ).map (burnsideI23_Fmap σ Λ ρΛ lam) := by
      rw [hk, hlow k]; trivial
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩
  · intro g u
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.1 g.2
    have hg : g = ⟨burnsideI23_rho σ Λ W0 hW0i l, Subgroup.mem_map_of_mem _ hl⟩ :=
      Subtype.ext hlg.symm
    induction u using QuotientGroup.induction_on with
    | H e =>
      have h1 : ((g : MulAut (burnsideI23_U σ Λ W0)) (QuotientGroup.mk e)) =
          QuotientGroup.mk (burnsideI23_actE Λ l e) := by
        rw [← hlg]
        rfl
      rw [h1, hθ'mk, hθ'mk, hg, ← hρΛ ⟨l, hl⟩]
      exact burnsideI23_Fmap_shift σ Λ ρΛ lam hl e
  · intro u
    induction u using QuotientGroup.induction_on with
    | H e =>
      apply hιinj
      rw [hι, hθ'mk]
      show ψ'' _ = _
      rw [burnsideI23_psi_Fmap σ Λ W0 ρΛ ψ'' lam hlam' hequivΛ]
      rfl

end Universal

section GUniv

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
theorem burnsideI23_relUniversalLift {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) {W0 : Subgroup V}
    (hW0i : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤) :
    I23RelativeUniversalLift G L W0 := by
  haveI : Fintype ↥G := Fintype.ofFinite _
  haveI hN : (L.subgroupOf G).Normal := ⟨fun n hn h => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm h h.2 n hn⟩
  let σ : ↥G →* MulAut V := G.subtype
  have hσ : ∀ g : ↥G, σ g = (g : MulAut V) := fun _ => rfl
  have h1 : ∀ g : ↥G, ∀ w ∈ W0, σ g w ∈ W0 := fun g w hw => hW0i g g.2 w hw
  have h2 : ∀ l ∈ L.subgroupOf G, ∀ w ∈ W0, σ l w = w := fun l hl w hw =>
    mem_fixV.1 (hW0 hw) (l : MulAut V) (Subgroup.mem_subgroupOf.1 hl)
  have h3 : Subgroup.closure
      {w : V | ∃ l ∈ L.subgroupOf G, ∃ v : V, w = σ l v * v⁻¹} = ⊤ := by
    rw [← hcomm, commV]
    congr 1
    ext w
    constructor
    · rintro ⟨l, hl, v, rfl⟩
      exact ⟨(l : MulAut V), Subgroup.mem_subgroupOf.1 hl, v, rfl⟩
    · rintro ⟨x, hx, v, rfl⟩
      exact ⟨⟨x, hLG hx⟩, Subgroup.mem_subgroupOf.2 hx, v, rfl⟩
  have hU := burnsideI23_isUniversalCovering σ (L.subgroupOf G) W0 hV h1 h2 h3
  have hrange : ((burnsideI23_rho σ (L.subgroupOf G) W0 h1).comp
      (Subgroup.inclusion hLG)).range =
      (L.subgroupOf G).map (burnsideI23_rho σ (L.subgroupOf G) W0 h1) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLG l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩
  refine ⟨hLG, burnsideI23_U σ (L.subgroupOf G) W0, inferInstance, inferInstance,
    burnsideI23_rho σ (L.subgroupOf G) W0 h1,
    W0.comap (burnsideI23_theta σ (L.subgroupOf G) W0 h2),
    burnsideI23_theta σ (L.subgroupOf G) W0 h2, ?_, ?_, ?_, rfl, ?_⟩
  · exact fun u => burnsideI23_U_sq σ (L.subgroupOf G) W0 u hV
  · rw [hrange]
    exact hU
  · exact burnsideI23_theta_surjective σ (L.subgroupOf G) W0 h3 h2
  · intro g u
    exact burnsideI23_theta_rho σ (L.subgroupOf G) W0 h1 h2 g u

end GUniv

end CFSG.ASVolI
