module

public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.StandardType

open scoped commutatorElement

theorem ggComm_mul_central_left {G : Type*} [Group G] (a y z : G) (hz : z ∈ Subgroup.center G) :
    ⁅a * z, y⁆ = ⁅a, y⁆ := by
  have c : y * z = z * y := Subgroup.mem_center_iff.mp hz y
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z * y * (z⁻¹ * a⁻¹) * y⁻¹ = a * (z * y) * z⁻¹ * a⁻¹ * y⁻¹ := by group
    _ = a * (y * z) * z⁻¹ * a⁻¹ * y⁻¹ := by rw [c]
    _ = a * y * a⁻¹ * y⁻¹ := by group

theorem ggComm_mul_central {G : Type*} [Group G] (g₁ g₂ z₁ z₂ : G) (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) : ⁅g₁ * z₁, g₂ * z₂⁆ = ⁅g₁, g₂⁆ := by
  rw [ggComm_mul_central_left _ _ _ h₁, ← commutatorElement_inv,
    ggComm_mul_central_left _ _ _ h₂, commutatorElement_inv]

@[expose] def ggCore {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (K : Subgroup R) :
    Subgroup L' :=
  ⁅K.comap ψ, K.comap ψ⁆

theorem ggCore_def {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (K : Subgroup R) :
    ggCore ψ K = ⁅K.comap ψ, K.comap ψ⁆ := rfl

theorem ggPerfectCore {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (K : Subgroup R)
    (hK : ⁅K, K⁆ = K) :
    (ggCore ψ K).map ψ = K ∧ ⁅ggCore ψ K, ggCore ψ K⁆ = ggCore ψ K := by
  unfold ggCore
  have h1 : ⁅K.comap ψ, K.comap ψ⁆.map ψ = K := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hψ, hK]
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
      (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have key : ∀ m ∈ K.comap ψ, ∃ c ∈ ⁅K.comap ψ, K.comap ψ⁆, ∃ z ∈ Subgroup.center L',
        m = c * z := by
      intro m hm
      have hm' : ψ m ∈ ⁅K.comap ψ, K.comap ψ⁆.map ψ := by rw [h1]; exact hm
      obtain ⟨c, hc, hcm⟩ := hm'
      refine ⟨c, hc, c⁻¹ * m, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcm, inv_mul_cancel]
    obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := key g₁ hg₁
    obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := key g₂ hg₂
    rw [ggComm_mul_central _ _ _ _ hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator hc₁ hc₂

theorem ggSubfieldCore {L' R R₀ : Type} [Group L'] [Group R] [Group R₀] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (K : Subgroup R)
    (hK : ⁅K, K⁆ = K) (θ₀ : K ≃* R₀) :
    ∃ ψ'' : ggCore ψ K →* R₀,
      (∀ (l : ggCore ψ K) (hl : ψ l ∈ K), ψ'' l = θ₀ ⟨ψ l, hl⟩) ∧
      Function.Surjective ψ'' ∧ (∀ l, ψ'' l = 1 ↔ ψ l = 1) ∧
      ψ''.ker ≤ Subgroup.center (ggCore ψ K) ∧ commutator (ggCore ψ K) = ⊤ := by
  obtain ⟨hmap, hcomm⟩ := ggPerfectCore ψ hψ hker K hK
  have hmem : ∀ l : ggCore ψ K, ψ l ∈ K := fun l =>
    le_of_eq hmap (Subgroup.mem_map_of_mem ψ l.2)
  let g : ggCore ψ K →* K := (ψ.comp (ggCore ψ K).subtype).codRestrict K hmem
  let ψ'' : ggCore ψ K →* R₀ := θ₀.toMonoidHom.comp g
  have hval : ∀ (l : ggCore ψ K) (hl : ψ l ∈ K), ψ'' l = θ₀ ⟨ψ l, hl⟩ := by
    intro l hl
    exact congrArg θ₀ (Subtype.ext rfl)
  have hiff : ∀ l : ggCore ψ K, ψ'' l = 1 ↔ ψ l = 1 := by
    intro l
    have hgl : (g l : R) = ψ l := rfl
    constructor
    · intro h1
      have h2 : g l = 1 := by
        have h3 := congrArg (fun z => θ₀.symm z) h1
        simpa [ψ''] using h3
      have h4 : (g l : R) = 1 := by rw [h2]; rfl
      rwa [hgl] at h4
    · intro h1
      have h2 : g l = 1 := by
        rw [Subtype.ext_iff, hgl]
        simpa using h1
      show θ₀ (g l) = 1
      rw [h2, map_one]
  refine ⟨ψ'', hval, ?_, hiff, ?_, ?_⟩
  · intro y
    have hk : ((θ₀.symm y : K) : R) ∈ (ggCore ψ K).map ψ := by
      rw [hmap]
      exact (θ₀.symm y).2
    obtain ⟨l, hl, hlψ⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨l, hl⟩, ?_⟩
    have h3 : ψ'' ⟨l, hl⟩ = θ₀ (θ₀.symm y) := by
      rw [hval ⟨l, hl⟩ (by rw [hlψ]; exact (θ₀.symm y).2)]
      exact congrArg θ₀ (Subtype.ext hlψ)
    simpa using h3
  · intro l hl
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hcent : l.1 ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker]
      exact (hiff l).mp (MonoidHom.mem_ker.mp hl)
    exact Subgroup.mem_center_iff.mp hcent m.1
  · exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hcomm)

theorem ggCore_stab {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (K : Subgroup R)
    (a : MulAut L') (φ : MulAut R) (h : ∀ l, φ (ψ l) = ψ (a l)) (hφ : ∀ g ∈ K, φ g ∈ K) :
    ∀ l ∈ ggCore ψ K, a l ∈ ggCore ψ K := by
  intro l hl
  have hMmap : (K.comap ψ).map (a : L' →* L') ≤ K.comap ψ := by
    rintro _ ⟨m, hm, rfl⟩
    show ψ (a m) ∈ K
    rw [← h m]
    exact hφ (ψ m) hm
  have hle : (ggCore ψ K).map (a : L' →* L') ≤ ggCore ψ K := by
    rw [ggCore_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hMmap hMmap
  exact hle (Subgroup.mem_map_of_mem (a : L' →* L') hl)

theorem ggInduced_pow {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) {a : MulAut L'}
    {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l)) (n : ℕ) :
    ∀ l, (φ ^ n) (ψ l) = ψ ((a ^ n) l) := by
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
    intro l
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]

theorem ggFixes_core {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') (b : MulAut L') (x : MulAut R)
    (hbx : ∀ l, ψ (b l) = x (ψ l)) (M : Subgroup L') (hM : ∀ l ∈ M, x (ψ l) = ψ l) :
    ⁅M, M⁆ ≤ ggFixSub b := by
  have hz : ∀ g ∈ M, g⁻¹ * b g ∈ Subgroup.center L' := by
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbx, hM g hg, inv_mul_cancel]
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have e₁ : b g₁ = g₁ * (g₁⁻¹ * b g₁) := by group
  have e₂ : b g₂ = g₂ * (g₂⁻¹ * b g₂) := by group
  refine mem_ggFixSub.mpr ?_
  rw [map_commutatorElement, e₁, e₂]
  exact ggComm_mul_central _ _ _ _ (hz g₁ hg₁) (hz g₂ hg₂)

theorem ggAut_eq_one_of_induced_one {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (a : MulAut L')
    (h : ∀ l, ψ (a l) = ψ l) : a = 1 := by
  have h1 := ggFixes_core ψ hker a (1 : MulAut R) h ⊤ (fun l _ => rfl)
  have h2 : (⊤ : Subgroup L') ≤ ggFixSub a := by
    have e : (⊤ : Subgroup L') = ⁅(⊤ : Subgroup L'), ⊤⁆ := hperf.symm
    rw [e]
    exact h1
  ext l
  exact mem_ggFixSub.mp (h2 (Subgroup.mem_top l))

theorem ggAutRestrictHom {G : Type*} [Group G] (H : Subgroup G) (A₀ : Subgroup (MulAut G))
    (hstab : ∀ a ∈ A₀, ∀ l ∈ H, a l ∈ H) :
    ∃ res : A₀ →* MulAut H, ∀ (a : A₀) (l : H), ((res a l : H) : G) = (a : MulAut G) l := by
  let f : A₀ → MulAut H := fun a =>
    { toFun := fun l => ⟨(a : MulAut G) l, hstab a a.2 l l.2⟩
      invFun := fun l => ⟨((a⁻¹ : A₀) : MulAut G) l, hstab _ (a⁻¹ : A₀).2 l l.2⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp)
      map_mul' := fun l l' => Subtype.ext (map_mul _ _ _) }
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, fun a l => rfl⟩
  · ext l
    rfl
  · intro a a'
    ext l
    rfl

end CFSG.StandardType

end
