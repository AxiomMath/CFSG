module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Vec

variable {F : Type} [Field F] {m : ℕ}

@[expose] def GGVecEq (h h' : Fin m → Fˣ) : Prop :=
  ∀ k l, h k * (h' k)⁻¹ = h l * (h' l)⁻¹

theorem GGVecEq.refl (h : Fin m → Fˣ) : GGVecEq h h :=
  fun _ _ => by simp

theorem GGVecEq.trans {h h' h'' : Fin m → Fˣ} (e : GGVecEq h h') (e' : GGVecEq h' h'') :
    GGVecEq h h'' :=
  fun k l => by
    have h1 : (h k * (h' k)⁻¹) * (h' k * (h'' k)⁻¹) = h k * (h'' k)⁻¹ := by group
    have h2 : (h l * (h' l)⁻¹) * (h' l * (h'' l)⁻¹) = h l * (h'' l)⁻¹ := by group
    rw [← h1, ← h2, e k l, e' k l]

theorem ggVecEq_one_iff {h : Fin m → Fˣ} : GGVecEq h 1 ↔ ∀ k l, h k = h l := by
  constructor
  · intro e k l
    simpa using e k l
  · intro hconst k l
    simpa using hconst k l

theorem ggVecEq_iff_exists {h h' : Fin m → Fˣ} : GGVecEq h h' ↔ ∃ c : Fˣ, ∀ k, h k = c * h' k := by
  constructor
  · intro e
    by_cases hm : m = 0
    · subst hm
      exact ⟨1, fun k => Fin.elim0 k⟩
    · refine ⟨h ⟨0, Nat.pos_of_ne_zero hm⟩ * (h' ⟨0, Nat.pos_of_ne_zero hm⟩)⁻¹, fun k => ?_⟩
      have hk := e k ⟨0, Nat.pos_of_ne_zero hm⟩
      rw [← hk]
      group
  · rintro ⟨c, hc⟩ k l
    rw [hc k, hc l]
    group

@[expose] def diagAt (k : Fin m) (τ : Fˣ) : Fin m → Fˣ := Function.update 1 k τ

theorem diagAt_apply_self (k : Fin m) (τ : Fˣ) : diagAt k τ k = τ := by
  simp [diagAt]

theorem diagAt_apply_of_ne {k l : Fin m} (hl : l ≠ k) (τ : Fˣ) : diagAt k τ l = 1 := by
  simp [diagAt, Function.update_of_ne hl]

theorem diagAt_one (k : Fin m) : diagAt k (1 : Fˣ) = 1 := by
  funext l
  by_cases hl : l = k
  · subst hl; simp [diagAt]
  · simp [diagAt, Function.update_of_ne hl]

theorem diagAt_comp_perm (π : Equiv.Perm (Fin m)) (k : Fin m) (τ : Fˣ) :
    diagAt k τ ∘ π.symm = diagAt (π k) τ := by
  funext l
  simp only [Function.comp_apply, diagAt, Function.update_apply, Equiv.symm_apply_eq,
    Pi.one_apply]

theorem diagAt_succ_comp_succ {n : ℕ} (k : Fin n) (τ : Fˣ) :
    diagAt k.succ τ ∘ Fin.succ = diagAt k τ := by
  funext l
  simp only [Function.comp_apply, diagAt, Function.update_apply, Fin.succ_inj, Pi.one_apply]

theorem diagAt_castSucc_comp_castSucc {n : ℕ} (k : Fin n) (τ : Fˣ) :
    diagAt k.castSucc τ ∘ Fin.castSucc = diagAt k τ := by
  funext l
  simp only [Function.comp_apply, diagAt, Function.update_apply, Fin.castSucc_inj, Pi.one_apply]

theorem diagAt_zpow (k : Fin m) (τ : Fˣ) (e : ℤ) : diagAt k τ ^ e = diagAt k (τ ^ e) := by
  funext l
  by_cases hl : l = k
  · subst hl; simp [diagAt]
  · change (diagAt k τ l) ^ e = diagAt k (τ ^ e) l
    rw [diagAt_apply_of_ne hl, diagAt_apply_of_ne hl, _root_.one_zpow]

theorem ggVecEq_diagAt_one_iff (hm : 2 ≤ m) (k : Fin m) (τ : Fˣ) :
    GGVecEq (diagAt k τ) 1 ↔ τ = 1 := by
  constructor
  · intro e
    have hconst : ∀ a b : Fin m, diagAt k τ a = diagAt k τ b := ggVecEq_one_iff.mp e
    have hm1 : 1 < Fintype.card (Fin m) := by simpa using (by omega : 1 < m)
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card hm1 k
    have h := hconst k l
    rwa [diagAt_apply_self, diagAt_apply_of_ne hl] at h
  · rintro rfl
    rw [diagAt_one]
    exact GGVecEq.refl 1

end Vec

section ActsVec

variable {X : Type*} [Group X] {F : Type} [Field F] {m : ℕ}

@[expose] def GGActsVec (φ : SpecialLinearGroup (Fin m) F →* X) (g : X) (h : Fin m → Fˣ) : Prop :=
  ∀ s, g * φ s * g⁻¹ = φ (ggDiagConj h s)

theorem ggDiagConj_congr_of_vecEq {h h' : Fin m → Fˣ} (e : GGVecEq h h')
    (s : SpecialLinearGroup (Fin m) F) : ggDiagConj h s = ggDiagConj h' s := by
  obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp e
  have hfun : h = (fun _ => c) * h' := by
    funext k
    rw [Pi.mul_apply]
    exact hc k
  rw [hfun, ← ggDiagConj_ggDiagConj (fun _ => c) h' s,
    ggDiagConj_eq_self_of_const (t := (fun _ => c)) (fun _ _ => rfl)]

theorem GGActsVec.of_vecEq {φ : SpecialLinearGroup (Fin m) F →* X} {g : X} {h h' : Fin m → Fˣ}
    (a : GGActsVec φ g h) (e : GGVecEq h h') : GGActsVec φ g h' := by
  intro s
  rw [a s, ggDiagConj_congr_of_vecEq e s]

theorem GGActsVec.vecEq {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) {g : X}
    {h h' : Fin m → Fˣ} (a : GGActsVec φ g h) (a' : GGActsVec φ g h') : GGVecEq h h' :=
  ratio_eq_of_ggDiagConj hker (fun s => (a s).symm.trans (a' s))

theorem GGActsVec.mul {φ : SpecialLinearGroup (Fin m) F →* X} {g g' : X} {h h' : Fin m → Fˣ}
    (a : GGActsVec φ g h) (a' : GGActsVec φ g' h') : GGActsVec φ (g * g') (h * h') := by
  intro s
  calc (g * g') * φ s * (g * g')⁻¹ = g * (g' * φ s * g'⁻¹) * g⁻¹ := by group
    _ = g * φ (ggDiagConj h' s) * g⁻¹ := by rw [a' s]
    _ = φ (ggDiagConj h (ggDiagConj h' s)) := a (ggDiagConj h' s)
    _ = φ (ggDiagConj (h * h') s) := by rw [ggDiagConj_ggDiagConj]

theorem GGActsVec.inv {φ : SpecialLinearGroup (Fin m) F →* X} {g : X} {h : Fin m → Fˣ}
    (a : GGActsVec φ g h) : GGActsVec φ g⁻¹ h⁻¹ := by
  intro s
  have e := a (ggDiagConj h⁻¹ s)
  rw [ggDiagConj_ggDiagConj, mul_inv_cancel,
    ggDiagConj_eq_self_of_const (t := (1 : Fin m → Fˣ)) (fun _ _ => rfl)] at e
  rw [← e]
  group

theorem GGActsVec.zpow {φ : SpecialLinearGroup (Fin m) F →* X} {g : X} {h : Fin m → Fˣ}
    (a : GGActsVec φ g h) (k : ℤ) : GGActsVec φ (g ^ k) (h ^ k) := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | hk⟩
  · rw [zpow_natCast, zpow_natCast]
    exact GGActsDiag.pow a n
  · rw [hk]
    simp only [zpow_natCast, _root_.zpow_neg]
    exact GGActsVec.inv (GGActsDiag.pow a n)

theorem GGActsVec.one_of_commute {φ : SpecialLinearGroup (Fin m) F →* X} {g : X}
    (hc : ∀ s, g * φ s = φ s * g) : GGActsVec φ g 1 := by
  intro s
  rw [ggDiagConj_eq_self_of_const (t := (1 : Fin m → Fˣ)) (fun _ _ => rfl), hc s]
  group

theorem GGActsVec.commute_of_vecEq_one {φ : SpecialLinearGroup (Fin m) F →* X} {g : X}
    {h : Fin m → Fˣ} (a : GGActsVec φ g h) (e : GGVecEq h 1) : ∀ s, g * φ s = φ s * g := by
  intro s
  have hconst : ∀ k l, h k = h l := ggVecEq_one_iff.mp e
  have e1 := a s
  rw [ggDiagConj_eq_self_of_const hconst] at e1
  calc g * φ s = (g * φ s * g⁻¹) * g := by group
    _ = φ s * g := by rw [e1]

theorem GGActsVec.conj_perm (h2 : (2 : F) = 0) {φ : SpecialLinearGroup (Fin m) F →* X} {g : X}
    {h : Fin m → Fˣ} (a : GGActsVec φ g h) (π : Equiv.Perm (Fin m)) :
    GGActsVec φ (φ (slPerm h2 π) * g * (φ (slPerm h2 π))⁻¹) (h ∘ π.symm) := by
  intro s
  set P : SpecialLinearGroup (Fin m) F := slPerm h2 π with hP
  have hφs : φ s = φ P * φ (P⁻¹ * s * P) * (φ P)⁻¹ := by
    have h1 : P * (P⁻¹ * s * P) * P⁻¹ = s := by group
    calc φ s = φ (P * (P⁻¹ * s * P) * P⁻¹) := by rw [h1]
      _ = φ P * φ (P⁻¹ * s * P) * (φ P)⁻¹ := by rw [map_mul φ, map_mul φ, map_inv φ]
  calc (φ P * g * (φ P)⁻¹) * φ s * (φ P * g * (φ P)⁻¹)⁻¹
      = φ P * (g * φ (P⁻¹ * s * P) * g⁻¹) * (φ P)⁻¹ := by
        rw [hφs]
        group
    _ = φ P * φ (ggDiagConj h (P⁻¹ * s * P)) * (φ P)⁻¹ := by rw [a (P⁻¹ * s * P)]
    _ = φ (P * ggDiagConj h (P⁻¹ * s * P) * P⁻¹) := by
        rw [map_mul φ, map_mul φ, map_inv φ]
    _ = φ (ggDiagConj (h ∘ π.symm) (P * (P⁻¹ * s * P) * P⁻¹)) := by
        rw [hP, slPerm_mul_ggDiagConj h2 π h ((slPerm h2 π)⁻¹ * s * slPerm h2 π)]
    _ = φ (ggDiagConj (h ∘ π.symm) s) := by
        rw [show P * (P⁻¹ * s * P) * P⁻¹ = s by group]

theorem GGActsVec.block_compat {n : ℕ} {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)) {g : X}
    {h h' : Fin (n + 1) → Fˣ} (a₁ : GGActsVec φ₁ g h) (a₂ : GGActsVec φ₂ g h') :
    GGVecEq (h ∘ Fin.succ) (h' ∘ Fin.castSucc) := by
  have hθ : (φ₁.comp (slLowerBlockHom n F)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (injective_comp_slLowerBlockHom hker₁)]
    exact bot_le
  have hJ : ∀ g : SpecialLinearGroup (Fin n) F,
      (φ₁.comp (slLowerBlockHom n F)) (ggDiagConj (h ∘ Fin.succ) g) =
        (φ₁.comp (slLowerBlockHom n F)) (ggDiagConj (h' ∘ Fin.castSucc) g) := by
    intro g
    have e₁ := a₁ (slLowerBlockHom n F g)
    have e₂ := a₂ (slUpperBlockHom n F g)
    rw [ggDiagConj_slLowerBlockHom] at e₁
    rw [ggDiagConj_slUpperBlockHom] at e₂
    have hcx : ∀ x, φ₁ (slLowerBlockHom n F x) = φ₂ (slUpperBlockHom n F x) := fun x =>
      DFunLike.congr_fun hc x
    simp only [MonoidHom.comp_apply]
    rw [← e₁, hcx, e₂, ← hcx]
  exact ratio_eq_of_ggDiagConj hθ hJ

theorem slPerm_mem_normalizer_of_actsDiag (h2 : (2 : F) = 0) {p : ℕ} {Bs : Subgroup X}
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs) {n : ℕ}
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) (π : Equiv.Perm (Fin (n + 1))) :
    φ (slPerm h2 π) ∈ Subgroup.normalizer (Bs : Set X) := by
  have hmem : ∀ π : Equiv.Perm (Fin (n + 1)),
      π ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) →
      φ (slPerm h2 π) ∈ Subgroup.normalizer (Bs : Set X) := by
    intro π hπ
    induction hπ using Submonoid.closure_induction with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      rw [slPerm_swap_castSucc_succ]
      exact weylRep_mem_normalizer_of_actsDiag h2 hBp hBs hker hdiag i
    | one =>
      simp only [map_one]
      exact Subgroup.one_mem (Subgroup.normalizer (Bs : Set X))
    | mul x y hx hy ihx ihy =>
      simp only [map_mul]
      exact Subgroup.mul_mem (Subgroup.normalizer (Bs : Set X)) ihx ihy
  exact hmem π (by
    rw [show Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) = ⊤ from
      Equiv.Perm.mclosure_swap_castSucc_succ n]
    exact Submonoid.mem_top π)

end ActsVec

structure GGFarLifts {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]
    (φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X) (Bs : Subgroup X) : Prop where
  ker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)
  ker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)
  compat : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)
  diag₁ : ∀ c ∈ Bs, GGActsDiag φ₁ c
  diag₂ : ∀ c ∈ Bs, GGActsDiag φ₂ c

end CFSG.StandardType
