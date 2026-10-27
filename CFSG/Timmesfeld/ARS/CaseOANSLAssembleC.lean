module

public import CFSG.Timmesfeld.ARS.CaseOANSLAssemble
public import CFSG.Timmesfeld.ARS.CaseOANSLFrameC
public import CFSG.Timmesfeld.ARS.ExclNSFrames
public import CFSG.LieType.CurtisTits.Symplectic

public section

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open Matrix

namespace CFSG.Timmesfeld.ARS

namespace CaseOANSL

section SpRoots

variable {N : ℕ} {F₀ : Type} [Field F₀]

theorem sp_x_zero (γ : Fin N → ℤ) : Sp.x N F₀ γ 0 = 1 := by
  have h0 := sp_x_add (N := N) (F := F₀) γ 0 0
  rw [add_zero] at h0
  exact left_eq_mul.1 h0

theorem sp_x_pow (γ : Fin N → ℤ) (c : F₀) (k : ℕ) :
    Sp.x N F₀ γ c ^ k = Sp.x N F₀ γ (k * c) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sp_x_zero]
  | succ k ih => rw [pow_succ, ih, ← sp_x_add, Nat.cast_succ, add_mul, one_mul]

theorem mem_rootGroup_iff_sp {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅) {x : StatedSp N F₀} :
    x ∈ Symplectic.rootGroup N F₀ γ ↔ ∃ c, Sp.x N F₀ γ c = x :=
  (Sp.isParametrization γ hγ).1 x

theorem charP_two_of_isPGroup {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (h : IsPGroup 2 (Symplectic.rootGroup N F₀ γ)) : CharP F₀ 2 := by
  have hx : Sp.x N F₀ γ 1 ∈ Symplectic.rootGroup N F₀ γ :=
    (mem_rootGroup_iff_sp hγ).2 ⟨1, rfl⟩
  obtain ⟨k, hk⟩ := h ⟨_, hx⟩
  have hk' : Sp.x N F₀ γ ((2 ^ k : ℕ) * 1) = Sp.x N F₀ γ 0 := by
    rw [← sp_x_pow, sp_x_zero]
    simpa using congrArg Subtype.val hk
  have h2k := (Sp.isParametrization γ hγ).2.2 hk'
  rw [mul_one, Nat.cast_pow, Nat.cast_ofNat] at h2k
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h2k
  have h2 : (2 : F₀) = 0 := (pow_eq_zero_iff hk0).1 h2k
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)

theorem map_upper_eq_rootGroup {φ : SpecialLinearGroup (Fin 2) F₀ →* StatedSp N F₀} {i : Fin N}
    (hφU : ∀ c, φ (sl2Upper c) = Sp.x N F₀ (Pi.single i 1) c) :
    (upperUnipotent F₀).map φ = Symplectic.rootGroup N F₀ (Pi.single i 1) := by
  ext x
  rw [mem_rootGroup_iff_sp (mem_roots_single i)]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff F₀).1 hg
    exact ⟨t, (hφU t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨RankOne.upperElt F₀ t, (RankOne.mem_upperUnipotent_iff F₀).2 ⟨t, rfl⟩, hφU t⟩

theorem map_lower_eq_rootGroup {φ : SpecialLinearGroup (Fin 2) F₀ →* StatedSp N F₀} {i : Fin N}
    (hφL : ∀ c, φ (sl2Lower c) = Sp.x N F₀ (-Pi.single i 1) c) :
    (lowerUnipotent F₀).map φ = Symplectic.rootGroup N F₀ (-Pi.single i 1) := by
  ext x
  rw [mem_rootGroup_iff_sp ((RootSystem.ofCartan (isFiniteType_cartanC N) ∅).neg_mem _
    (mem_roots_single i))]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff F₀).1 hg
    exact ⟨t, (hφL t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨RankOne.lowerElt F₀ t, (RankOne.mem_lowerUnipotent_iff F₀).2 ⟨t, rfl⟩, hφL t⟩

theorem cartanC_end {i j : Fin N} (hij : i.val + 1 = j.val) (h : j.val + 1 = N) :
    cartanC N j i = -1 ∧ cartanC N i j = -2 := by
  simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem exists_weylAction_single_eq (hN : 1 ≤ N) :
    ∀ j (hj : j + 1 < N), ∃ w, (Pi.single (⟨j, by omega⟩ : Fin N) 1 : Fin N → ℤ) =
      weylAction (isFiniteType_cartanC N) w (Pi.single ⟨0, hN⟩ 1)
  | 0, _ => ⟨1, by simp⟩
  | j + 1, hj => by
    obtain ⟨w, hw⟩ := exists_weylAction_single_eq hN j (by omega)
    obtain ⟨-, -, r0s, r10, -, -⟩ := reflection_A2 (N := N) (p := ⟨j, by omega⟩)
      (q := ⟨j + 1, by omega⟩) rfl (by simp only; omega)
    refine ⟨(coxeterMatrix (isFiniteType_cartanC N)).toCoxeterSystem.simple ⟨j, by omega⟩ *
      (coxeterMatrix (isFiniteType_cartanC N)).toCoxeterSystem.simple ⟨j + 1, by omega⟩ * w, ?_⟩
    rw [weylAction_mul_apply, weylAction_mul_apply, ← hw, weylAction_simple, weylAction_simple,
      r10, r0s]

end SpRoots

section Cent

variable {G : Type} [Group G]

theorem conj_mem_centralizer {D : Subgroup G} {y g : G} (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hg : g ∈ Subgroup.centralizer (D : Set G)) :
    y * g * y⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro d hd
  have hd' : y⁻¹ * d * y ∈ D := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) d).1 hd
    simpa using this
  have := hg _ hd'
  calc d * (y * g * y⁻¹) = y * ((y⁻¹ * d * y) * g) * y⁻¹ := by group
    _ = y * (g * (y⁻¹ * d * y)) * y⁻¹ := by rw [this]
    _ = y * g * y⁻¹ * d := by group

theorem mem_centralizer_commutator {A₀ C : Subgroup G} {g : G}
    (h₀ : g ∈ Subgroup.centralizer (A₀ : Set G)) (hC : g ∈ Subgroup.centralizer (C : Set G)) :
    g ∈ Subgroup.centralizer ((⁅A₀, C⁆ : Subgroup G) : Set G) := by
  have hle : ⁅A₀, C⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha c hc
    have ha' : a ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h₀ a ha)
    have hc' : c ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hC c hc)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha' hc') (inv_mem ha')) (inv_mem hc')
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

end Cent

section LongRoot

variable {G : Type} [Group G] {k : ℕ} {F₀ : Type} [Field F₀]

theorem reflection_long (k : ℕ) :
    reflection (cartanC (k + 2)) ⟨k, by omega⟩
        (2 • Pi.single (⟨k, by omega⟩ : Fin (k + 2)) 1 + Pi.single ⟨k + 1, by omega⟩ 1) =
      Pi.single ⟨k + 1, by omega⟩ 1 := by
  obtain ⟨-, h2⟩ := cartanC_end (N := k + 2) (i := ⟨k, by omega⟩) (j := ⟨k + 1, by omega⟩) rfl rfl
  rw [map_add, map_nsmul, reflection_single_self (cartanC_self _), reflection_single', h2]
  module

theorem weylElement_conj_x [CharP F₀ 2] {N : ℕ} (i : Fin N) {β : Fin N → ℤ}
    (hβ : β ∈ RootSystem.roots (isFiniteType_cartanC N) ∅) (u : F₀) :
    weylElement (Sp.x N F₀) i 1 * Sp.x N F₀ β u * (weylElement (Sp.x N F₀) i 1)⁻¹ =
      Sp.x N F₀ (reflection (cartanC N) i β) u := by
  obtain ⟨ε, hε, hw⟩ := Sp.weyl (F := F₀) i hβ
  rw [hw 1 u, _root_.one_zpow, Units.val_one, mul_one]
  rcases hε with rfl | rfl
  · rw [Int.cast_one, one_mul]
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_mul]

theorem long_mem_centralizer [CharP F₀ 2] (hk : 1 ≤ k) (Θ : StatedSp (k + 2) F₀ →* G)
    {D : Subgroup G}
    (hnorm : ∀ β ∈ RootSystem.roots (isFiniteType_cartanC (k + 2)) ∅, β ⟨0, by omega⟩ = 0 →
      ∀ x ∈ Symplectic.rootGroup (k + 2) F₀ β, Θ x ∈ Subgroup.normalizer (D : Set G))
    (hc1 : ∀ c, Θ (Sp.x (k + 2) F₀ (Pi.single ⟨k, by omega⟩ 1) c) ∈
      Subgroup.centralizer (D : Set G))
    (hc2 : ∀ c, Θ (Sp.x (k + 2) F₀
      (Pi.single ⟨k, by omega⟩ 1 + Pi.single ⟨k + 1, by omega⟩ 1) c) ∈
        Subgroup.centralizer (D : Set G)) (c : F₀) :
    Θ (Sp.x (k + 2) F₀ (Pi.single ⟨k + 1, by omega⟩ 1) c) ∈ Subgroup.centralizer (D : Set G) ∧
      Θ (Sp.x (k + 2) F₀ (-Pi.single ⟨k + 1, by omega⟩ 1) c) ∈
        Subgroup.centralizer (D : Set G) := by
  have hroot : ∀ i : Fin (k + 2), (Pi.single i 1 : Fin (k + 2) → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanC (k + 2)) ∅ := mem_roots_single
  have hnroot : ∀ i : Fin (k + 2), (-Pi.single i 1 : Fin (k + 2) → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanC (k + 2)) ∅ := fun i =>
    (RootSystem.ofCartan (isFiniteType_cartanC (k + 2)) ∅).neg_mem _ (mem_roots_single i)
  have hsing : ∀ i : Fin (k + 2), i.val ≠ 0 →
      (Pi.single i 1 : Fin (k + 2) → ℤ) ⟨0, by omega⟩ = 0 := fun i hi =>
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ i.val from Ne.symm hi)) 1
  have hw : ∀ i : Fin (k + 2), i.val ≠ 0 →
      Θ (weylElement (Sp.x (k + 2) F₀) i 1) ∈ Subgroup.normalizer (D : Set G) := by
    intro i hi
    have h1 := hnorm _ (hroot i) (hsing i hi)
    have h2 := hnorm _ (hnroot i) (by rw [Pi.neg_apply, hsing i hi, neg_zero])
    rw [weylElement, map_mul, map_mul]
    exact mul_mem (mul_mem (h1 _ ((mem_rootGroup_iff_sp (hroot i)).2 ⟨_, rfl⟩))
      (h2 _ ((mem_rootGroup_iff_sp (hnroot i)).2 ⟨_, rfl⟩)))
      (h1 _ ((mem_rootGroup_iff_sp (hroot i)).2 ⟨_, rfl⟩))
  have hlong : ∀ t : F₀, Θ (Sp.x (k + 2) F₀ (2 • Pi.single ⟨k, by omega⟩ 1 +
      Pi.single ⟨k + 1, by omega⟩ 1) t) ∈ Subgroup.centralizer (D : Set G) := by
    intro t
    have hc := comm_B2 F₀ (N := k + 2) (i := ⟨k, by omega⟩) rfl 1 t
    rw [one_mul, one_pow, one_mul] at hc
    have e : Sp.x (k + 2) F₀ (2 • Pi.single ⟨k, by omega⟩ 1 + Pi.single ⟨k + 1, by omega⟩ 1) t =
        (Sp.x (k + 2) F₀ (Pi.single ⟨k, by omega⟩ 1 + Pi.single ⟨k + 1, by omega⟩ 1) t)⁻¹ *
          ⁅Sp.x (k + 2) F₀ (Pi.single ⟨k, by omega⟩ 1) 1,
            Sp.x (k + 2) F₀ (Pi.single ⟨k + 1, by omega⟩ 1) t⁆ := by
      rw [hc, inv_mul_cancel_left]
    have hy : Θ (Sp.x (k + 2) F₀ (Pi.single ⟨k + 1, by omega⟩ 1) t) ∈
        Subgroup.normalizer (D : Set G) :=
      hnorm _ (hroot _) (hsing _ (by simp)) _ ((mem_rootGroup_iff_sp (hroot _)).2 ⟨t, rfl⟩)
    rw [e, map_mul, map_inv, map_commutatorElement, commutatorElement_def]
    refine mul_mem (inv_mem (hc2 t)) ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc _ _ (Θ (Sp.x (k + 2) F₀ (Pi.single ⟨k + 1, _⟩ 1) t))⁻¹]
    exact mul_mem (hc1 1) (conj_mem_centralizer hy (inv_mem (hc1 1)))
  have hpos : ∀ t, Θ (Sp.x (k + 2) F₀ (Pi.single ⟨k + 1, by omega⟩ 1) t) ∈
      Subgroup.centralizer (D : Set G) := by
    intro t
    have e := weylElement_conj_x (F₀ := F₀) (⟨k, by omega⟩ : Fin (k + 2))
      (mem_roots_B2long (N := k + 2) (i := ⟨k, by omega⟩) rfl) t
    rw [reflection_long k] at e
    rw [← e, map_mul, map_mul, map_inv]
    exact conj_mem_centralizer (hw _ (by simp only; omega)) (hlong t)
  refine ⟨hpos c, ?_⟩
  have e := weylElement_conj_x (F₀ := F₀) (⟨k + 1, by omega⟩ : Fin (k + 2))
    (hroot ⟨k + 1, by omega⟩) c
  rw [reflection_single_self (cartanC_self _)] at e
  rw [← e, map_mul, map_mul, map_inv]
  exact conj_mem_centralizer (hw _ (by simp)) (hpos c)

end LongRoot

section SL2Lift

variable {G : Type} [Group G]

theorem map_upperUnipotent_ringEquiv {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    (upperUnipotent F).map (SpecialLinearGroup.map (e : F →+* F')) = upperUnipotent F' := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff F).1 hg'
    exact (RankOne.mem_upperUnipotent_iff F').2 ⟨e t, map_sl2Upper (e : F →+* F') t⟩
  · intro hg
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff F').1 hg
    refine ⟨RankOne.upperElt F (e.symm t), (RankOne.mem_upperUnipotent_iff F).2 ⟨_, rfl⟩, ?_⟩
    have := map_sl2Upper (e : F →+* F') (e.symm t)
    rw [RingEquiv.coe_toRingHom, e.apply_symm_apply] at this
    exact this

theorem map_lowerUnipotent_ringEquiv {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    (lowerUnipotent F).map (SpecialLinearGroup.map (e : F →+* F')) = lowerUnipotent F' := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff F).1 hg'
    exact (RankOne.mem_lowerUnipotent_iff F').2 ⟨e t, map_sl2Lower (e : F →+* F') t⟩
  · intro hg
    obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff F').1 hg
    refine ⟨RankOne.lowerElt F (e.symm t), (RankOne.mem_lowerUnipotent_iff F).2 ⟨_, rfl⟩, ?_⟩
    have := map_sl2Lower (e : F →+* F') (e.symm t)
    rw [RingEquiv.coe_toRingHom, e.apply_symm_apply] at this
    exact this

theorem map_injective_of_injective {F F' : Type} [Field F] [Field F'] {f : F →+* F'}
    (hf : Function.Injective f) : Function.Injective (SpecialLinearGroup.map (n := Fin 2) f) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun i j => hf ?_)
  have := congrArg (fun M : SpecialLinearGroup (Fin 2) F' => (M : Matrix (Fin 2) (Fin 2) F') i j)
    hgg'
  simpa [SpecialLinearGroup.map_apply_coe] using this

theorem range_eq_sup_of_map {F : Type} [Field F] {ρ : SpecialLinearGroup (Fin 2) F →* G}
    {X Y : Subgroup G} (hX : (upperUnipotent F).map ρ = X) (hY : (lowerUnipotent F).map ρ = Y) :
    ρ.range = X ⊔ Y := by
  rw [MonoidHom.range_eq_map, ← NaturalModule.upperUnipotent_sup_lowerUnipotent,
    Subgroup.map_sup, hX, hY]

theorem liftHom_eq_one_iff {Δ₁ : Set (Subgroup G)} (hZ : Subgroup.center ↥(gen Δ₁) = ⊥)
    {K : Type*} [Group K] (Ψ : K →* CompBar Δ₁) (k : K) : liftHom hZ Ψ k = 1 ↔ Ψ k = 1 := by
  constructor
  · intro h1
    have : (liftEquiv hZ) (Ψ k) = 1 := Subtype.ext h1
    simpa using this
  · intro h1
    simp [liftHom, h1]

end SL2Lift

section Main

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {Δ₁ Δ₂ : Set (Subgroup G)}

open ExclNS (memberRoots memberRoots_subset weylAction_mem_memberRoots neg_mem_memberRoots)

theorem output_of_frame_C (hset : CaseOASetting G R A A₀ Δ₁ Δ₂)
    (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
    (hCt : F.D.cartan = Symplectic.cartanC F.D.rank) : Output G R := by
  obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, -, hS₂⟩ := hset
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := center_gen_eq_bot h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F hS₂
  obtain ⟨P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩ := hS₂
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hc₁₂ := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  obtain ⟨hn, B, C, X₀, Y₀, -, hα₀O, hB, hC, hF', hBF', hX₀, hY₀, hXY₀, hX₀q, hY₀q, e0, e1,
    hstab⟩ := exists_frame_data h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F hP₂ hQ₂ hPQ₂ hgen₂
  have hnorm : ∀ β ∈ F.D.roots, β ⟨0, by omega⟩ = 0 → ∀ x ∈ F.D.rootGroup β,
      liftHom hZ F.Ψ x ∈ Subgroup.normalizer (B : Set G) ∧
        liftHom hZ F.Ψ x ∈ Subgroup.normalizer (C : Set G) := by
    intro β hβ hβ0 x hx
    obtain ⟨h1, h2'⟩ := hstab β hβ hβ0
    exact ⟨conjSub_eq_self_iff.1 (conjSub_liftHom_eq h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hZ F.Ψ hB
        (h1 ⟨x, hx, rfl⟩)),
      conjSub_eq_self_iff.1 (conjSub_liftHom_eq h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hZ F.Ψ hC
        (h2' ⟨x, hx, rfl⟩))⟩
  have hcent : ∀ β ∈ memberRoots F, β ⟨0, by omega⟩ = 0 → ∀ x ∈ F.D.rootGroup β,
      liftHom hZ F.Ψ x ∈ Subgroup.centralizer (B : Set G) ∧
        liftHom hZ F.Ψ x ∈ Subgroup.centralizer (C : Set G) := by
    intro β hβ hβ0 x hx
    obtain ⟨X, hX, hXq⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hβ
    obtain ⟨h1, h2'⟩ := hstab β (memberRoots_subset F hβ) hβ0
    exact ⟨Subgroup.mem_centralizer_iff.2 fun b hb => (commute_liftHom_of_mem h hA hAne hmax hA₀ h2
        hΔ₁ hΔ₂ hne hZ F.Ψ hB hX hXq h1 hx b hb).symm.eq,
      Subgroup.mem_centralizer_iff.2 fun b hb => (commute_liftHom_of_mem h hA hAne hmax hA₀ h2
        hΔ₁ hΔ₂ hne hZ F.Ψ hC hX hXq h2' hx b hb).symm.eq⟩
  have hMW : ∀ γ ∈ memberRoots F, ∀ w, weylAction F.D.isFiniteType w γ ∈ memberRoots F :=
    fun γ hγ w => weylAction_mem_memberRoots F hγ w
  have hMneg : ∀ γ ∈ memberRoots F, -γ ∈ memberRoots F := fun γ hγ => neg_mem_memberRoots F hγ
  generalize memberRoots F = M at hα₀O hcent hMW hMneg
  have hV₁A₀ : ∀ k, liftHom hZ F.Ψ k ∈ Subgroup.centralizer (A₀ : Set G) := fun k =>
    levi_le_centralizer_right A A₀ (gen_le_levi h hA hAne hA₀ hΔ₁ (liftHom_mem hZ F.Ψ k))
  have hsurj := F.surj
  clear hstab
  cases F with
  | mk K D nw T hct hext hdiv i₀ htype hpg Ψ _ hker _ _ _ hconc =>
  cases hconc with
  | minus n hirr =>
    have hn' : 3 ≤ n - 1 := hn
    exact absurd hCt (cartanB_ne_cartanC (m := n - 1) (by omega))
  | g2 K' => exact absurd hCt cartan_G2_ne_cartanC
  | twistedD4 f => exact absurd hCt cartan_G2_ne_cartanC
  | f4 K' => exact absurd hCt cartan_F4_ne_cartanC
  | twistedE6 f => exact absurd hCt cartan_F4_ne_cartanC
  | symplectic m F₀ =>
  have hm : 3 ≤ m := hn
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  set Θ : StatedSp (r + 2) F₀ →* G := liftHom hZ Ψ with hΘ
  have : CharP F₀ 2 := charP_two_of_isPGroup (mem_roots_single (⟨0, by omega⟩ : Fin (r + 2)))
    (hpg _ (mem_roots_single _))
  obtain ⟨φr, hφinj, hφU, hφL⟩ := Sp.rankOne (n := r + 2) (F := F₀) ⟨0, by omega⟩
  have hΘinj : Function.Injective (Θ.comp φr) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : Ψ (φr g) = 1 := (liftHom_eq_one_iff hZ Ψ (φr g)).1 hg
    exact Linear.eq_one_of_map_mem_center F₀ hφinj (hker hg')
  have hup : (upperUnipotent F₀).map (Θ.comp φr) = X₀ := by
    rw [← Subgroup.map_map, map_upper_eq_rootGroup hφU]
    exact map_liftHom hZ Ψ (le_gen hX₀) hX₀q
  have hlow : (lowerUnipotent F₀).map (Θ.comp φr) = Y₀ := by
    rw [← Subgroup.map_map, map_lower_eq_rootGroup hφL]
    exact map_liftHom hZ Ψ (le_gen hY₀) hY₀q
  obtain ⟨f, hf, hcard, -⟩ := hXY₀.exists_mulEquiv_SL2' hR (hl₁ hX₀).1.1
  have hF₀ : Nat.card F₀ = 2 ^ f := by
    rw [← RankOne.card_upperUnipotent, ← Subgroup.card_map_of_injective hΘinj, hup, hcard]
  have : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hF₀]; positivity)
  let _ : Fintype F₀ := Fintype.ofFinite F₀
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hGF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e : GaloisField 2 f ≃+* F₀ := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, hF₀])
  set ρX := (Θ.comp φr).comp (SpecialLinearGroup.map (e : GaloisField 2 f →+* F₀)) with hρX
  have hρXinj : Function.Injective ρX := hΘinj.comp (map_injective_of_injective e.injective)
  have hρXU : (upperUnipotent (GaloisField 2 f)).map ρX = X₀ := by
    rw [hρX, ← Subgroup.map_map, map_upperUnipotent_ringEquiv, hup]
  have hρXL : (lowerUnipotent (GaloisField 2 f)).map ρX = Y₀ := by
    rw [hρX, ← Subgroup.map_map, map_lowerUnipotent_ringEquiv, hlow]
  obtain ⟨ρ, hρ2, hρ, hedge⟩ := Linear.exists_chain hR hiso (m := 3)
    (A := ![P₂, B, X₀]) (B := ![Q₂, ⁅A₀, C⁆, Y₀])
    (fun i => by fin_cases i; exacts [(hl₂ hP₂).1.1, hB.1.1.1, (hl₁ hX₀).1.1])
    (fun i => by fin_cases i; exacts [(hl₂ hQ₂).1.1, hF'.1.1.1, (hl₁ hY₀).1.1])
    (fun i => by fin_cases i; exacts [hPQ₂, hBF', hXY₀])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [e0, e1])
    (k₀ := 2) hcard hρXinj hρXU hρXL
  obtain ⟨φ₀, hφ₀⟩ := hedge 0 1 rfl
  obtain ⟨φ₁, hφ₁⟩ := hedge 1 2 rfl
  have hρ0 : (ρ 0).range = P₂ ⊔ Q₂ := range_eq_sup_of_map (hρ 0).2.1 (hρ 0).2.2
  have hρ1 : (ρ 1).range = B ⊔ ⁅A₀, C⁆ := range_eq_sup_of_map (hρ 1).2.1 (hρ 1).2.2
  have hmemJ : ∀ j : Fin (r + 2), j.val + 1 < r + 2 → (Pi.single j 1 : Fin (r + 2) → ℤ) ∈ M := by
    intro j hj
    obtain ⟨w, hw⟩ := exists_weylAction_single_eq (N := r + 2) (by omega) j.val hj
    have := hMW _ hα₀O w
    have hj' : (Pi.single j 1 : Fin (r + 2) → ℤ) = weylAction (isFiniteType_cartanC (r + 2)) w
        (Pi.single ⟨0, by omega⟩ 1) := hw
    rw [hj']
    exact this
  have hmemS : (Pi.single (⟨r, by omega⟩ : Fin (r + 2)) 1 + Pi.single ⟨r + 1, by omega⟩ 1 :
      Fin (r + 2) → ℤ) ∈ M := by
    have e' : weylAction (isFiniteType_cartanC (r + 2))
        ((coxeterMatrix (isFiniteType_cartanC (r + 2))).toCoxeterSystem.simple ⟨r + 1, by omega⟩)
        (Pi.single ⟨r, by omega⟩ 1) =
          Pi.single ⟨r, by omega⟩ 1 + Pi.single ⟨r + 1, by omega⟩ 1 := by
      rw [weylAction_simple, reflection_single',
        (cartanC_end (N := r + 2) (i := ⟨r, by omega⟩) (j := ⟨r + 1, by omega⟩) rfl rfl).1]
      module
    have h1 := hMW _ (hmemJ ⟨r, by omega⟩ (by simp))
      ((coxeterMatrix (isFiniteType_cartanC (r + 2))).toCoxeterSystem.simple ⟨r + 1, by omega⟩)
    rw [← e']
    exact h1
  have hsing : ∀ j : Fin (r + 2), j.val ≠ 0 →
      (Pi.single j 1 : Fin (r + 2) → ℤ) ⟨0, by omega⟩ = 0 := fun j hj =>
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ j.val from Ne.symm hj)) 1
  have hroot : ∀ j : Fin (r + 2), (Pi.single j 1 : Fin (r + 2) → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanC (r + 2)) ∅ := mem_roots_single
  have hnroot : ∀ j : Fin (r + 2), (-Pi.single j 1 : Fin (r + 2) → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanC (r + 2)) ∅ := fun j =>
    (RootSystem.ofCartan (isFiniteType_cartanC (r + 2)) ∅).neg_mem _ (mem_roots_single j)
  have hcentJ : ∀ j : Fin (r + 2), j.val ≠ 0 → ∀ d : F₀,
      (Θ (Sp.x (r + 2) F₀ (Pi.single j 1) d) ∈ Subgroup.centralizer (B : Set G) ∧
        Θ (Sp.x (r + 2) F₀ (Pi.single j 1) d) ∈ Subgroup.centralizer (C : Set G)) ∧
      (Θ (Sp.x (r + 2) F₀ (-Pi.single j 1) d) ∈ Subgroup.centralizer (B : Set G) ∧
        Θ (Sp.x (r + 2) F₀ (-Pi.single j 1) d) ∈ Subgroup.centralizer (C : Set G)) := by
    intro j hj d
    by_cases hjl : j.val + 1 < r + 2
    · exact ⟨hcent _ (hmemJ j hjl) (hsing j hj) _ ((mem_rootGroup_iff_sp (hroot j)).2 ⟨d, rfl⟩),
        hcent _ (hMneg _ (hmemJ j hjl)) (neg_eq_zero.2 (hsing j hj)) _
          ((mem_rootGroup_iff_sp (hnroot j)).2 ⟨d, rfl⟩)⟩
    · have hjv := j.isLt
      obtain rfl : j = ⟨r + 1, Nat.lt_succ_self _⟩ := Fin.ext (show j.val = r + 1 by omega)
      have hc1 : ∀ c, Θ (Sp.x (r + 2) F₀ (Pi.single ⟨r, by omega⟩ 1) c) ∈
          Subgroup.centralizer (B : Set G) ∧ Θ (Sp.x (r + 2) F₀ (Pi.single ⟨r, by omega⟩ 1) c) ∈
            Subgroup.centralizer (C : Set G) := fun c =>
        hcent _ (hmemJ ⟨r, by omega⟩ (by simp)) (hsing ⟨r, by omega⟩ (show r ≠ 0 by omega)) _
          ((mem_rootGroup_iff_sp (hroot _)).2 ⟨c, rfl⟩)
      have hc2 : ∀ c, Θ (Sp.x (r + 2) F₀ (Pi.single ⟨r, by omega⟩ 1 +
          Pi.single ⟨r + 1, by omega⟩ 1) c) ∈ Subgroup.centralizer (B : Set G) ∧
            Θ (Sp.x (r + 2) F₀ (Pi.single ⟨r, by omega⟩ 1 + Pi.single ⟨r + 1, by omega⟩ 1) c) ∈
              Subgroup.centralizer (C : Set G) := fun c =>
        hcent _ hmemS (by
          show (Pi.single (⟨r, by omega⟩ : Fin (r + 2)) 1 + Pi.single ⟨r + 1, by omega⟩ 1 :
            Fin (r + 2) → ℤ) ⟨0, by omega⟩ = 0
          rw [Pi.add_apply, hsing ⟨r, by omega⟩ (show r ≠ 0 by omega),
            hsing ⟨r + 1, by omega⟩ (show r + 1 ≠ 0 by omega), add_zero]) _
          ((mem_rootGroup_iff_sp (mem_roots_B2sum (N := r + 2) (i := ⟨r, by omega⟩) rfl)).2
            ⟨c, rfl⟩)
      have hB' := long_mem_centralizer (k := r) (by omega) Θ (D := B)
        (fun β hβ hβ0 x hx => (hnorm β hβ hβ0 x hx).1) (fun c => (hc1 c).1)
        (fun c => (hc2 c).1) d
      have hC' := long_mem_centralizer (k := r) (by omega) Θ (D := C)
        (fun β hβ hβ0 x hx => (hnorm β hβ hβ0 x hx).2) (fun c => (hc1 c).2)
        (fun c => (hc2 c).2) d
      exact ⟨⟨hB'.1, hC'.1⟩, ⟨hB'.2, hC'.2⟩⟩
  have hg0 : ∀ g, ρ 0 g ∈ gen Δ₂ := fun g => by
    have : ρ 0 g ∈ (ρ 0).range := ⟨g, rfl⟩
    rw [hρ0] at this
    exact sup_le (le_gen hP₂) (le_gen hQ₂) this
  have key : ∀ g, ∀ y : G, y ∈ Subgroup.centralizer (B : Set G) →
      y ∈ Subgroup.centralizer (C : Set G) → y ∈ Subgroup.centralizer (A₀ : Set G) →
        Commute (ρ 1 g) y := by
    intro g y hyB hyC hyA
    have hle : B ⊔ ⁅A₀, C⁆ ≤ Subgroup.centralizer ({y} : Set G) :=
      sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyB b hb))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (mem_centralizer_commutator hyA hyC) z hz))
    have hg : ρ 1 g ∈ B ⊔ ⁅A₀, C⁆ := by
      rw [← hρ1]
      exact ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have H : FrameHyp (n := r + 1) Θ e φ₀ φ₁ (ρ 0) (ρ 1) :=
    { φ₀01 := fun c => (hφ₀ c).1
      φ₀10 := fun c => (hφ₀ c).2.1
      φ₀12 := fun c => (hφ₀ c).2.2.1
      φ₀21 := fun c => (hφ₀ c).2.2.2
      φ₁01 := fun c => (hφ₁ c).1
      φ₁10 := fun c => (hφ₁ c).2.1
      φ₁12 := fun c => by
        rw [(hφ₁ c).2.2.1, hρ2, hρX, MonoidHom.comp_apply, MonoidHom.comp_apply,
          LevisExtras.tv01_eq_sl2Upper, map_sl2Upper, hφU]
        rfl
      φ₁21 := fun c => by
        rw [(hφ₁ c).2.2.2, hρ2, hρX, MonoidHom.comp_apply, MonoidHom.comp_apply,
          LevisExtras.tv10_eq_sl2Lower, map_sl2Lower, hφL]
        rfl
      V := fun g b => (hc₁₂ (Θ b) (liftHom_mem hZ Ψ b) (ρ 0 g) (hg0 g)).symm
      E := fun j hj g d => ⟨key g _ (hcentJ j hj d).1.1 (hcentJ j hj d).1.2 (hV₁A₀ _),
        key g _ (hcentJ j hj d).2.1 (hcentJ j hj d).2.2 (hV₁A₀ _)⟩ }
  have htop : levi R A A₀ ⊔ B ⊔ ⁅A₀, C⁆ = ⊤ :=
    CaseOA.levi_sup_sup_eq_top h hA hAne hmax hA₀ hB hF'
  rw [CaseOA.levi_eq_sup h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne] at htop
  have hgen : (ρ 0).range ⊔ (ρ 1).range ⊔ Θ.range = ⊤ := by
    rw [hρ0, hρ1, range_liftHom hZ hsurj, ← hgen₂, eq_top_iff, ← htop]
    exact sup_le (sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_left.trans (le_sup_right.trans le_sup_left)))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))
  have hnt : ρ 0 (tv 0 1 1) ≠ 1 := by
    intro h1
    have h1' := (hρ 0).1 (h1.trans (map_one (ρ 0)).symm)
    rw [LevisExtras.tv01_eq_sl2Upper] at h1'
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) (GaloisField 2 f) =>
      (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1) h1'
    simp [sl2Upper] at this
  have hframe := (H.isCNFrame (by omega) hgen hnt).isCTFrame
  have hadm : StatedLieAdmissible .PSp (r + 1 + 3) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun e' => absurd (congrArg Prod.fst e') (by omega)⟩
  have hCT := CurtisTits.curtisTitsConclusion_symplectic (n := r + 1 + 3) (F := GaloisField 2 f)
    hadm hGF (by omega)
  have hL := leviConePresented_symplectic (r + 1 + 3) (GaloisField 2 f)
  refine Output.of_nonSimplyLaced
    (.inl ⟨r + 1 + 3, f, by omega, hf, hframe.lieModel hCT hL h.center⟩) ?_
  refine .inr (hframe.nslFrame hCT hL (Symplectic.isCTGroupDatum _ _)
    (Symplectic.steinbergExtras _ _) rfl (NSLType.symplecticDatum (by omega) _)
    (fun _ hγ => RankTwo.isPGroup_of_param Sp.isParametrization hγ)
    NSLFrameData.comm_symplecticDatum (hl₂ hP₂).1.1 ?_ ?_ hPQ₂)
  · have e' : oaPsi Θ e φ₀ φ₁ (a0 (r + 1)) = fun c => ρ 0 (tv 0 1 c) := funext H.v_a0
    refine Eq.symm ((RankTwo.range_phiOf Sp.isParametrization _ (mem_roots_single _)).trans ?_)
    show Set.range (oaPsi Θ e φ₀ φ₁ (a0 (r + 1))) = _
    rw [e', Linear.range_tv_upper, (hρ 0).2.1]
    rfl
  · have e' : oaPsi Θ e φ₀ φ₁ (-a0 (r + 1)) = fun c => ρ 0 (tv 1 0 c) := funext H.v_na0
    refine Eq.symm ((RankTwo.range_phiOf Sp.isParametrization _
      ((RootSystem.ofCartan (isFiniteType_cartanC (r + 1 + 3)) ∅).neg_mem _
        (mem_roots_single _))).trans ?_)
    show Set.range (oaPsi Θ e φ₀ φ₁ (-a0 (r + 1))) = _
    rw [e', Linear.range_tv_lower, (hρ 0).2.2]
    rfl

end Main

end CaseOANSL

end CFSG.Timmesfeld.ARS

