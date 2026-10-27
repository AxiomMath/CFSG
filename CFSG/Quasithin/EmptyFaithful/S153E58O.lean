module

public import CFSG.Quasithin.EmptyFaithful.S153E58K

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E58

open S153E57

theorem realizesVia_mk_sub {V : Type*} [CommGroup V] {Γ : Type} [Group Γ] {A : Type} [CommGroup A]
    (act : Γ → A → A) (hact1 : ∀ γ, act γ 1 = 1) {H : Subgroup (MulAut V)} {U : Subgroup V}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (e : ↥U ≃* A)
    (he : ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (e u)) :
    (FFModel.mk Γ A act ⊤ ⊥).RealizesVia H U ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, hHU, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥U →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom)
    have hβ : ∀ u : ↥U,
        β u = ((Subgroup.topEquiv.symm (e u) : ↥(⊤ : Subgroup A)) :
          ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) := fun _ => rfl
    have hinj : ∀ a b : ↥(⊤ : Subgroup A), ((a : ↥(⊤ : Subgroup A) ⧸
        (⊥ : Subgroup A).subgroupOf ⊤) = b) → a = b := by
      intro a b h
      rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
      exact (inv_mul_eq_one.mp h)
    refine ⟨β, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨e.symm m, ?_⟩
      rw [hβ]
      congr 1
      exact Subtype.ext (by simp)
    · intro u
      rw [hβ, QuotientGroup.eq_one_iff, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        Subgroup.mem_bot]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        have hu1 : u = 1 := Subtype.ext h
        apply Subtype.ext
        simp [hu1]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (m : A)
      rw [he, ← hm']
      rfl

section Dual

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

@[expose] noncomputable def bvec (e : ↥W₁ ≃* V3) (i : Fin 3) : W :=
  ((e.symm (Multiplicative.ofAdd (fun j : Fin 3 => if i = j then (1 : ZMod 2) else 0)) : ↥W₁) : W)

theorem bvec_mem (e : ↥W₁ ≃* V3) (i : Fin 3) : bvec e i ∈ W₁ := (e.symm _).2

@[expose] noncomputable def dualCoord (bil : W → W → ZMod 2) (e : ↥W₁ ≃* V3) (u : W) : V3 :=
  Multiplicative.ofAdd (fun i => bil (bvec e i) u)

theorem toAdd_dualCoord (bil : W → W → ZMod 2) (e : ↥W₁ ≃* V3) (u : W) (i : Fin 3) :
    Multiplicative.toAdd (dualCoord bil e u) i = bil (bvec e i) u := rfl

theorem Setup58.dualCoord_mul (hS : Setup58 H K W₁ W₂ bil) (e : ↥W₁ ≃* V3) (u v : W) :
    dualCoord bil e (u * v) = dualCoord bil e u * dualCoord bil e v := by
  apply Multiplicative.toAdd.injective
  funext i
  show bil (bvec e i) (u * v) = bil (bvec e i) u + bil (bvec e i) v
  exact hS.bil_right _ _ _

theorem Setup58.dualCoord_one (hS : Setup58 H K W₁ W₂ bil) (e : ↥W₁ ≃* V3) :
    dualCoord bil e 1 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  exact hS.bil_one_right _

theorem Setup58.bil_eq_dot (hS : Setup58 H K W₁ W₂ bil) (e : ↥W₁ ≃* V3) (x : ↥W₁) (u : W) :
    bil x u = Multiplicative.toAdd (e x) ⬝ᵥ Multiplicative.toAdd (dualCoord bil e u) := by
  let L : (Fin 3 → ZMod 2) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun v => bil (e.symm (Multiplicative.ofAdd v) : W) u) (fun a b => by
      rw [show Multiplicative.ofAdd (a + b) = Multiplicative.ofAdd a * Multiplicative.ofAdd b from rfl,
        map_mul]
      exact hS.bil_left _ _ _)
  have h1 := LinearMap.pi_apply_eq_sum_univ (L.toZModLinearMap 2) (Multiplicative.toAdd (e x))
  have h2 : L (Multiplicative.toAdd (e x)) = bil x u := by
    show bil (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) : W) u = _
    simp
  have h3 : (L.toZModLinearMap 2) (Multiplicative.toAdd (e x)) = bil x u := h2
  rw [h3] at h1
  rw [h1, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  rfl

theorem Setup58.dualCoord_eq_one (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e)
    {u : W} (hu : u ∈ W₂) (h : dualCoord bil e u = 1) : u = 1 := by
  apply hS.eq_one_of_orth hT u hu
  intro x hx
  rw [hS.bil_eq_dot e ⟨x, hx⟩ u, h]
  simp

@[expose] noncomputable def Setup58.dualEquiv (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e) :
    ↥W₂ ≃* V3 :=
  have : Finite ↥W₂ := Nat.finite_of_card_ne_zero (by rw [hS.card₂]; omega)
  let f : ↥W₂ →* V3 :=
    { toFun := fun u => dualCoord bil e u
      map_one' := hS.dualCoord_one e
      map_mul' := fun a b => hS.dualCoord_mul e a b }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (hS.dualCoord_eq_one hT u.2 hu)
  have hcard : Nat.card V3 ≤ Nat.card ↥W₂ := by
    rw [hS.card₂]
    show Nat.card (Multiplicative (Fin 3 → ZMod 2)) ≤ 8
    simp [Nat.card_eq_fintype_card]
  MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)

theorem Setup58.dualEquiv_apply (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e)
    (u : ↥W₂) : hS.dualEquiv hT u = dualCoord bil e (u : W) := rfl

theorem Setup58.dualCoord_equivariant (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    {e : ↥W₁ ≃* V3}
    (he : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥W₁) (hu : (π γ : MulAut W) (u : W) ∈ W₁),
      e ⟨(π γ : MulAut W) (u : W), hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (e u))
    (γ : ↥(StatedSL 3 (ZMod 2))) (u : W) :
    dualCoord bil e ((π γ : MulAut W) u) = dualNatAct (StatedSL 3 (ZMod 2)) γ (dualCoord bil e u) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_dualCoord]
  have h1 : bil (bvec e i) ((π γ : MulAut W) u) = bil ((π γ⁻¹ : MulAut W) (bvec e i)) u := by
    have := hS.bil_inv_K (π γ⁻¹).2 (bvec e i) ((π γ : MulAut W) u)
    have e2 : (π γ⁻¹ : MulAut W) ((π γ : MulAut W) u) = u := by
      rw [map_inv]
      exact MulAut.inv_apply_self _ _ _
    rw [e2] at this
    exact this.symm
  have hmem : (π γ⁻¹ : MulAut W) (bvec e i) ∈ W₁ := hS.inv₁ _ (π γ⁻¹).2 _ (bvec_mem e i)
  have h2 := hS.bil_eq_dot e ⟨(π γ⁻¹ : MulAut W) (bvec e i), hmem⟩ u
  have h3 := he γ⁻¹ (e.symm (Multiplicative.ofAdd (fun j : Fin 3 => if i = j then (1 : ZMod 2) else 0)))
    hmem
  rw [h1]
  change bil (⟨(π γ⁻¹ : MulAut W) (bvec e i), hmem⟩ : ↥W₁) u = _
  rw [h2]
  have h4 : e ⟨(π γ⁻¹ : MulAut W) (bvec e i), hmem⟩ =
      natAct (StatedSL 3 (ZMod 2)) γ⁻¹ (Multiplicative.ofAdd (fun j : Fin 3 => if i = j then (1 : ZMod 2) else 0)) := by
    have := h3
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  rw [h4]
  simp only [natAct, dualNatAct, toAdd_ofAdd, dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.sum_ite_eq]

theorem Setup58.realizes_dual (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    (FFModel.dualNat (StatedSL 3 (ZMod 2))).RealizesVia K W₂ ⊥ π := by
  obtain ⟨e, hT, he⟩ := exists_coords_of_realizes hπ
  refine realizesVia_mk_sub (V := W) (Γ := ↥(StatedSL 3 (ZMod 2)))
    (A := Multiplicative (Fin 3 → ZMod 2)) (dualNatAct (StatedSL 3 (ZMod 2))) (fun γ => by
      unfold dualNatAct
      rw [show Multiplicative.toAdd (1 : Multiplicative (Fin 3 → ZMod 2)) = 0 from rfl,
        Matrix.mulVec_zero]
      rfl) π hπ.1 (fun h u hu => hS.inv₂ h h.2 u hu) (hS.dualEquiv hT)
    (fun γ u hu => hS.dualCoord_equivariant he γ (u : W))

end Dual

end S153E58

end CFSG.Quasithin
