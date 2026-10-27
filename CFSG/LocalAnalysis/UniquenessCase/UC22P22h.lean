module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.Milestones.ASVolI.I1Cohomology
public import CFSG.Quasithin.Vol2.Ch6OrthIrred
public import CFSG.Milestones.ASVolI.K3Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

section Herm

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13
open scoped Matrix MatrixGroups

variable {F : Type} [Field F] [CharP F 2] {a : ℕ}

theorem uc22p22h_twist_mul (g h : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    twistActCh6 a (g * h) X = twistActCh6 a g (twistActCh6 a h X) := by
  simp only [twistActCh6, Matrix.SpecialLinearGroup.coe_mul, JonesParshall.frobPow_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem uc22p22h_twist_one (X : Matrix (Fin 2) (Fin 2) F) :
    twistActCh6 a (1 : SL(2, F)) X = X := by
  rw [twistActCh6, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, JonesParshall.frobPow_eq_map,
    map_one, Matrix.transpose_one, Matrix.mul_one]

theorem uc22p22h_twist_mem [Fintype F] (hF : Fintype.card F = 2 ^ (2 * a))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA a F) (g : SL(2, F)) :
    twistActCh6 a g X ∈ hermA a F :=
  twist_mem a (sig_sig hF) hX _

theorem uc22p22h_fixR [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA a F) :
    (∀ r ∈ B45L2.rootSub (⊤ : AddSubgroup F), twistActCh6 a r X = X) ↔
      (X 1 1 = 0 ∧ X 0 1 = 0) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  constructor
  · intro h
    have hsub : ∀ t : F, twistActCh6 a (uMat t) X - X = 0 := fun t => by
      rw [h (uMat t) ⟨t, trivial, rfl⟩, sub_self]
    have hA : ∀ t : F, !![sig a t * X 0 1 + t * sig a (X 0 1) + t * sig a t * X 1 1,
        t * X 1 1; sig a t * X 1 1, 0] = (0 : Matrix (Fin 2) (Fin 2) F) := fun t => by
      rw [← hAct_uMat_sub t hX]
      exact hsub t
    have e1 := congrFun (congrFun (hA 1) 0) 1
    have e2 := congrFun (congrFun (hA 1) 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, map_one, one_mul] at e1 e2
    have h11 : X 1 1 = 0 := e1
    have hσX : sig a (X 0 1) = X 0 1 := by
      have : X 0 1 + sig a (X 0 1) = 0 := by simpa [h11] using e2
      exact (CharTwo.add_eq_zero.mp this).symm
    obtain ⟨ω, hω⟩ : ∃ ω : F, ω ^ 2 ^ a ≠ ω := by
      have hF' : Nat.card F = 2 ^ (2 * a) := by rw [Nat.card_eq_fintype_card, hF]
      haveI : Finite F := inferInstance
      exact CFSG.ASVolI.burnsideK312_exists_notFixed ha hF'
    have e3 := congrFun (congrFun (hA ω) 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply] at e3
    have e3' : sig a ω * X 0 1 + ω * sig a (X 0 1) = 0 := by simpa [h11] using e3
    rw [hσX] at e3'
    have e4 : (sig a ω + ω) * X 0 1 = 0 := by linear_combination e3'
    refine ⟨h11, ?_⟩
    rcases mul_eq_zero.mp e4 with h0 | h0
    · exfalso
      apply hω
      rw [← sig_apply]
      exact CharTwo.add_eq_zero.mp h0
    · exact h0
  · rintro ⟨h11, h01⟩ r ⟨t, -, rfl⟩
    have h := hAct_uMat_sub t hX
    have h10 : X 1 0 = 0 := by rw [← hermA_apply hX 1 0, h01, map_zero]
    rw [h11, h01] at h
    simp only [map_zero, mul_zero, add_zero, zero_add] at h
    have : twistActCh6 a (uMat t) X - X = 0 := by
      rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    exact sub_eq_zero.mp this

theorem uc22p22h_card_fixR [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) F // X ∈ hermA a F ∧
      ∀ r ∈ B45L2.rootSub (⊤ : AddSubgroup F), twistActCh6 a r X = X} = 2 ^ a := by
  have hcard := B45L2.card_frob_fixed ha hF
  rw [← hcard]
  have key : ∀ X : {X : Matrix (Fin 2) (Fin 2) F // X ∈ hermA a F ∧
      ∀ r ∈ B45L2.rootSub (⊤ : AddSubgroup F), twistActCh6 a r X = X},
      X.1 1 1 = 0 ∧ X.1 0 1 = 0 ∧ X.1 1 0 = 0 := by
    intro X
    obtain ⟨h1, h2⟩ := (uc22p22h_fixR ha hF X.2.1).mp X.2.2
    exact ⟨h1, h2, by rw [← hermA_apply X.2.1 1 0, h2, map_zero]⟩
  have hmk : ∀ x : {x : F // x ^ 2 ^ a = x},
      (!![x.1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈ hermA a F := fun x =>
    mem_hermA_of fun i j => by
      fin_cases i <;> fin_cases j <;> simp [sig_apply, x.2]
  refine Nat.card_congr
    { toFun := fun X => ⟨X.1 0 0, by
        have := hermA_apply X.2.1 0 0
        rwa [sig_apply] at this⟩
      invFun := fun x => ⟨!![x.1, 0; 0, 0], hmk x,
        (uc22p22h_fixR ha hF (hmk x)).mpr ⟨by simp, by simp⟩⟩
      left_inv := fun X => ?_
      right_inv := fun x => ?_ }
  · obtain ⟨h11, h01, h10⟩ := key X
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h01, h10]
  · rfl

theorem uc22p22h_card_fixG [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    (x : SL(2, F)) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) F // X ∈ hermA a F ∧
      ∀ g ∈ (B45L2.rootSub (⊤ : AddSubgroup F)).map (MulAut.conj x).toMonoidHom,
        twistActCh6 a g X = X} = 2 ^ a := by
  rw [← uc22p22h_card_fixR ha hF]
  have hinvmul : ∀ (y : SL(2, F)) (Z : Matrix (Fin 2) (Fin 2) F),
      twistActCh6 a y⁻¹ (twistActCh6 a y Z) = Z := fun y Z => by
    rw [← uc22p22h_twist_mul, inv_mul_cancel, uc22p22h_twist_one]
  have hmulinv : ∀ (y : SL(2, F)) (Z : Matrix (Fin 2) (Fin 2) F),
      twistActCh6 a y (twistActCh6 a y⁻¹ Z) = Z := fun y Z => by
    rw [← uc22p22h_twist_mul, mul_inv_cancel, uc22p22h_twist_one]
  refine Nat.card_congr
    { toFun := fun X => ⟨twistActCh6 a x⁻¹ X.1, uc22p22h_twist_mem hF X.2.1 _, fun r hr => ?_⟩
      invFun := fun Y => ⟨twistActCh6 a x Y.1, uc22p22h_twist_mem hF Y.2.1 _, fun g hg => ?_⟩
      left_inv := fun X => Subtype.ext (hmulinv x X.1)
      right_inv := fun Y => Subtype.ext (hinvmul x Y.1) }
  · have h1 := X.2.2 (x * r * x⁻¹) ⟨r, hr, rfl⟩
    calc twistActCh6 a r (twistActCh6 a x⁻¹ X.1)
        = twistActCh6 a x⁻¹ (twistActCh6 a x (twistActCh6 a r (twistActCh6 a x⁻¹ X.1))) :=
          (hinvmul x _).symm
      _ = twistActCh6 a x⁻¹ (twistActCh6 a (x * r * x⁻¹) X.1) := by
          rw [uc22p22h_twist_mul, uc22p22h_twist_mul]
      _ = twistActCh6 a x⁻¹ X.1 := by rw [h1]
  · obtain ⟨r, hr, rfl⟩ := hg
    have h1 := Y.2.2 r hr
    show twistActCh6 a (x * r * x⁻¹) (twistActCh6 a x Y.1) = twistActCh6 a x Y.1
    rw [uc22p22h_twist_mul, uc22p22h_twist_mul, hinvmul, h1]

theorem uc22p22h_exists_U [Fintype F] {k : ℕ} (hF : Fintype.card F = 2 ^ (2 * k)) {L : Type}
    [Group L] (θ : L ≃* SL(2, F)) :
    ∃ U₀ : Subgroup L, Nat.card U₀ = 2 ^ (2 * k) ∧ IsPGroup 2 U₀ := by
  refine ⟨(B45L2.rootSub (⊤ : AddSubgroup F)).map θ.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective θ.symm.injective, CFSG.ASVolI.burnsideK312_card_rootSub,
      Nat.card_eq_fintype_card, hF]
  · rintro ⟨g, r, hr, rfl⟩
    obtain ⟨n, hn⟩ := CFSG.ASVolI.burnsideK312_isPGroup_rootSub (E := F) ⟨r, hr⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : r ^ 2 ^ n = 1 := congrArg Subtype.val hn
    show (θ.symm.toMonoidHom r) ^ 2 ^ n = 1
    rw [← map_pow, h1, map_one]

end Herm

section Pres

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13
open scoped Matrix MatrixGroups

variable {H : Type} [Group H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W) (L : Subgroup H)

theorem uc22p22h_pres {A : Submodule (ZMod 2) W} {k : ℕ}
    (hk : 1 ≤ k) (h : NatOmegaMinus4 ρ L A ⊥ k) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2), Fintype.card F = 2 ^ (2 * k) ∧
      ∃ (β : W →+ Matrix (Fin 2) (Fin 2) F) (θ : ↥L ≃* SL(2, F)),
        CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A ∧ (∀ x ∈ A, β x ∈ hermA k F) ∧ (∀ x ∈ A, β x = 0 → x = 0) ∧
        (∀ X ∈ hermA k F, ∃ x ∈ A, β x = X) ∧
        ∀ (l : ↥L) (x : W), x ∈ A → β (ρ l x) = twistActCh6 k (θ l) (β x) := by
  obtain ⟨K, _, _, hKcard, b, c, hbc, hinv, -, -, φ, ψ, -, hψinj, hψsurj, hψact⟩ := h
  haveI : CharP K 2 := uc22p22d_charP_two hk hKcard
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨F', _, _, ω, hrank, hω⟩ := CFSG.ASVolI.burnsideI16h_exists_quad_ext hbc
  haveI : Module.Finite K F' := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI : Finite F' := Module.finite_of_finite K
  letI : Fintype F' := Fintype.ofFinite F'
  haveI : CharP F' 2 := charP_of_injective_algebraMap (algebraMap K F').injective 2
  have hK : Fintype.card K = 2 ^ k := by rw [← Nat.card_eq_fintype_card, hKcard]
  let S : CFSG.ASVolI.burnsideI16h_Setup K F' := ⟨k, b, c, hk, hK, ω, hω, hbc, hrank⟩
  refine ⟨F', inferInstance, inferInstance, inferInstance, CFSG.ASVolI.burnsideI16h_hF S, ?_⟩
  refine ⟨(CFSG.ASVolI.burnsideI16h_H S).toAddMonoidHom.comp ψ,
    φ.trans (CFSG.ASVolI.burnsideI16h_θ S), hinv, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact CFSG.ASVolI.burnsideI16h_H_mem S (ψ x)
  · intro x hx h0
    have h1 : CFSG.ASVolI.burnsideI16h_H S (ψ x) = 0 := h0
    have h2 := CFSG.ASVolI.burnsideI16h_eps_H S (ψ x)
    rw [h1, map_zero] at h2
    have := hψinj x hx h2.symm
    exact Submodule.mem_bot _ |>.1 this
  · intro X hX
    obtain ⟨x, hx, hxX⟩ := hψsurj (CFSG.ASVolI.burnsideI16h_eps S X)
    exact ⟨x, hx, by
      change CFSG.ASVolI.burnsideI16h_H S (ψ x) = X
      rw [hxX]
      exact CFSG.ASVolI.burnsideI16h_H_eps S hX⟩
  · intro l x hx
    have hγ := hψact l x hx
    set γ := φ l with hγdef
    have h1 : CFSG.ASVolI.burnsideI16h_ΘEquiv S (CFSG.ASVolI.burnsideI16h_θ S γ) =
        CFSG.ASVolI.burnsideI16h_gammaEquiv S γ :=
      (CFSG.ASVolI.burnsideI16h_ΘEquiv S).apply_symm_apply _
    have h2 : CFSG.ASVolI.burnsideI16h_Θ S (CFSG.ASVolI.burnsideI16h_θ S γ) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv CFSG.ASVolI.burnsideI16h_OI K γ.1 :=
      congrArg Subtype.val h1
    have h3 : CFSG.ASVolI.burnsideI16h_L S (CFSG.ASVolI.burnsideI16h_θ S γ) (ψ x) =
        ψ (ρ l x) := by
      have := congrArg (fun f => f (ψ x)) h2
      simp only [CFSG.ASVolI.burnsideI16h_Θ_apply,
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] at this
      rw [this, hγ]
    change CFSG.ASVolI.burnsideI16h_H S (ψ (ρ l x)) = _
    rw [← h3, CFSG.ASVolI.burnsideI16h_H_L, CFSG.ASVolI.burnsideI16h_Tg_apply]
    rfl

theorem uc22p22h_irr {A : Submodule (ZMod 2) W} {k : ℕ} (hk : 1 ≤ k)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ (2 * k))
    (β : W →+ Matrix (Fin 2) (Fin 2) F) (θ : ↥L ≃* SL(2, F))
    (hmem : ∀ x ∈ A, β x ∈ hermA k F) (hinj : ∀ x ∈ A, β x = 0 → x = 0)
    (hact : ∀ (l : ↥L) (x : W), x ∈ A → β (ρ l x) = twistActCh6 k (θ l) (β x)) :
    ∀ C : Submodule (ZMod 2) W, C ≤ A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A := by
  intro C hCA hC
  by_cases hC0 : C = ⊥
  · exact Or.inl hC0
  refine Or.inr (le_antisymm hCA fun y hy => ?_)
  obtain ⟨x₀, hx₀C, hx₀0⟩ := (Submodule.ne_bot_iff C).1 hC0
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) F) := C.toAddSubgroup.map β
  have hSH : S ≤ hermA k F := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x (hCA hx)
  have hinv : ∀ g : SL(2, F), ∀ X ∈ S, twistActCh6 k g X ∈ S := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨ρ (θ.symm g : ↥L) x, hC _ (θ.symm g).2 x hx, ?_⟩
    rw [hact _ x (hCA hx), MulEquiv.apply_symm_apply]
  have hle := hermA_le_of_invariant_ch6 hF (by omega) S hSH hinv
    ⟨x₀, hx₀C, rfl⟩ (fun h => hx₀0 (hinj x₀ (hCA hx₀C) h))
  obtain ⟨z, hz, hzy⟩ := hle (hmem y hy)
  have : y - z = 0 := hinj (y - z) (A.sub_mem hy (hCA hz)) (by rw [map_sub, hzy, sub_self])
  rw [sub_eq_zero] at this
  rw [this]
  exact hz

theorem uc22p22h_card_fix {A : Submodule (ZMod 2) W} {k : ℕ} (hk : 1 ≤ k)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ (2 * k))
    (β : W →+ Matrix (Fin 2) (Fin 2) F) (θ : ↥L ≃* SL(2, F))
    (hmem : ∀ x ∈ A, β x ∈ hermA k F) (hinj : ∀ x ∈ A, β x = 0 → x = 0)
    (hsurj : ∀ X ∈ hermA k F, ∃ x ∈ A, β x = X)
    (hact : ∀ (l : ↥L) (x : W), x ∈ A → β (ρ l x) = twistActCh6 k (θ l) (β x))
    (hinvA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A)
    (U₀ : Subgroup ↥L) (hU₀card : Nat.card U₀ = 2 ^ (2 * k)) (hU₀ : IsPGroup 2 U₀) :
    Nat.card ↥(fixOn ρ (U₀.map L.subtype) A) = 2 ^ k := by
  classical
  set G : Subgroup SL(2, F) := U₀.map θ.toMonoidHom with hG
  have hGcard : Nat.card G = 2 ^ (2 * k) := by
    rw [hG, Subgroup.card_map_of_injective θ.injective, hU₀card]
  have hGp : IsPGroup 2 G := by
    rintro ⟨g, u, hu, rfl⟩
    obtain ⟨n, hn⟩ := hU₀ ⟨u, hu⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have h1 : u ^ 2 ^ n = 1 := congrArg Subtype.val hn
    show (θ.toMonoidHom u) ^ 2 ^ n = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨x, hx⟩ := CFSG.ASVolI.burnsideK312_sylow_conj (E := F) hGp
  have hFcard : Nat.card F = 2 ^ (2 * k) := by rw [Nat.card_eq_fintype_card, hF]
  have hRcard : Nat.card ((B45L2.rootSub (⊤ : AddSubgroup F)).map
      (MulAut.conj x).toMonoidHom) = 2 ^ (2 * k) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
      CFSG.ASVolI.burnsideK312_card_rootSub, hFcard]
  have hGeq : G = (B45L2.rootSub (⊤ : AddSubgroup F)).map (MulAut.conj x).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hx (by rw [hRcard, hGcard])
  have hbij : Nat.card ↥(fixOn ρ (U₀.map L.subtype) A) =
      Nat.card {X : Matrix (Fin 2) (Fin 2) F // X ∈ hermA k F ∧
        ∀ g ∈ G, twistActCh6 k g X = X} := by
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨β y.1, hmem y.1 (mem_fixOn.1 y.2).1, ?_⟩)
      ⟨?_, ?_⟩)
    · rintro g ⟨u, hu, rfl⟩
      have h1 := (mem_fixOn.1 y.2).2 (u : H) ⟨u, hu, rfl⟩
      show twistActCh6 k (θ u) (β y.1) = β y.1
      rw [← hact u y.1 (mem_fixOn.1 y.2).1, h1]
    · intro y y' hyy
      have hy := (mem_fixOn.1 y.2).1
      have hy' := (mem_fixOn.1 y'.2).1
      have h0 : β (y.1 - y'.1) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr (congrArg Subtype.val hyy)
      have := hinj _ (A.sub_mem hy hy') h0
      exact Subtype.ext (sub_eq_zero.mp this)
    · rintro ⟨X, hXH, hXG⟩
      obtain ⟨z, hz, hzX⟩ := hsurj X hXH
      refine ⟨⟨z, mem_fixOn.2 ⟨hz, ?_⟩⟩, Subtype.ext hzX⟩
      rintro _ ⟨u, hu, rfl⟩
      have h1 : β (ρ (u : H) z - z) = 0 := by
        rw [map_sub, hact u z hz, hzX]
        exact sub_eq_zero.mpr (hXG _ ⟨u, hu, rfl⟩)
      have := hinj _ (A.sub_mem (hinvA _ u.2 z hz) hz) h1
      exact sub_eq_zero.mp this
  rw [hbij, hGeq]
  exact uc22p22h_card_fixG hk hF x

end Pres

section Core

open CFSG.RankThree.FFModules

variable {H : Type} [Group H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

theorem uc22p22h_inv_inf {L : Subgroup H} {Y Z : Submodule (ZMod 2) W}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (Y ⊓ Z) :=
  fun a ha u hu => ⟨hY a ha u hu.1, hZ a ha u hu.2⟩

theorem uc22p22h_inv_sup {L : Subgroup H} {Y Z : Submodule (ZMod 2) W}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (Y ⊔ Z) := by
  intro a ha u hu
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add]
  exact Submodule.add_mem_sup (hY a ha y hy) (hZ a ha z hz)

theorem uc22p22h_inv_mono {L U : Subgroup H} (hUL : U ≤ L) {Y : Submodule (ZMod 2) W}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ U Y :=
  fun a ha u hu => hY a (hUL ha) u hu

theorem uc22p22h_card_fix_sup {U : Subgroup H} {Y₁ Y₂ : Submodule (ZMod 2) W}
    (hY₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ U Y₁) (hY₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ U Y₂) (hd : Y₁ ⊓ Y₂ = ⊥) :
    Nat.card ↥(fixOn ρ U (Y₁ ⊔ Y₂)) = Nat.card ↥(fixOn ρ U Y₁) * Nat.card ↥(fixOn ρ U Y₂) := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(fixOn ρ U Y₁) × ↥(fixOn ρ U Y₂) =>
      (⟨p.1.1 + p.2.1, mem_fixOn.2 ⟨Submodule.add_mem_sup (mem_fixOn.1 p.1.2).1
        (mem_fixOn.1 p.2.2).1, fun a ha => by
          rw [map_add, (mem_fixOn.1 p.1.2).2 a ha, (mem_fixOn.1 p.2.2).2 a ha]⟩⟩ :
        ↥(fixOn ρ U (Y₁ ⊔ Y₂)))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a + b = a' + b' := congrArg Subtype.val h
    have h2 : a - a' = b' - b := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm b' a']
      exact h1
    have hmem : a - a' ∈ Y₁ ⊓ Y₂ :=
      ⟨Y₁.sub_mem (mem_fixOn.1 ha).1 (mem_fixOn.1 ha').1, by
        rw [h2]
        exact Y₂.sub_mem (mem_fixOn.1 hb').1 (mem_fixOn.1 hb).1⟩
    rw [hd] at hmem
    have h3 : a = a' := sub_eq_zero.mp ((Submodule.mem_bot _).1 hmem)
    have h4 : b = b' := by
      rw [h3] at h1
      exact add_left_cancel h1
    subst h3
    subst h4
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨hzm, hzfix⟩ := mem_fixOn.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hzm
    have hfix : ∀ u ∈ U, ρ u a = a ∧ ρ u b = b := by
      intro u hu
      have h1 : ρ u a + ρ u b = a + b := by rw [← map_add]; exact hzfix u hu
      have h2 : ρ u a - a = b - ρ u b := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b a]
        exact h1
      have hmem : ρ u a - a ∈ Y₁ ⊓ Y₂ :=
        ⟨Y₁.sub_mem (hY₁ u hu a ha) ha, by
          rw [h2]
          exact Y₂.sub_mem hb (hY₂ u hu b hb)⟩
      rw [hd] at hmem
      have h3 : ρ u a = a := sub_eq_zero.mp ((Submodule.mem_bot _).1 hmem)
      refine ⟨h3, ?_⟩
      rw [h3] at h1
      exact add_left_cancel h1
    exact ⟨(⟨a, mem_fixOn.2 ⟨ha, fun u hu => (hfix u hu).1⟩⟩,
      ⟨b, mem_fixOn.2 ⟨hb, fun u hu => (hfix u hu).2⟩⟩), rfl⟩

theorem uc22p22h_core [Finite W] {L U : Subgroup H} (hUL : U ≤ L) {p : ℕ} (hp : p.Prime)
    {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {j : ℕ} (hcj : c ^ (p ^ j) = 1)
    (hY : ∀ Y : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y → Y ≠ ⊤ →
      ¬ Nat.card ↥(fixOn ρ U ⊤) ≡ Nat.card ↥(fixOn ρ U Y) [MOD p]) :
    ∀ x : W, ρ c x = x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcl : ∀ g ∈ Subgroup.centralizer (L : Set H), ∀ l ∈ L, ∀ x : W,
      ρ g (ρ l x) = ρ l (ρ g x) := by
    intro g hg l hl x
    have h1 : l * g = g * l := Subgroup.mem_centralizer_iff.1 hg l hl
    rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]
  have hcinv : c⁻¹ ∈ Subgroup.centralizer (L : Set H) := inv_mem hc
  let V₀ := ↥(fixOn ρ U ⊤)
  let mv : (g : H) → g ∈ Subgroup.centralizer (L : Set H) → V₀ → V₀ := fun g hg v =>
    ⟨ρ g v.1, mem_fixOn.2 ⟨Submodule.mem_top, fun a ha => by
      rw [← hcl g hg a (hUL ha) v.1, (mem_fixOn.1 v.2).2 a ha]⟩⟩
  let σ : Equiv.Perm V₀ :=
    { toFun := mv c hc
      invFun := mv c⁻¹ hcinv
      left_inv := fun v => Subtype.ext (by
        show ρ c⁻¹ (ρ c v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun v => Subtype.ext (by
        show ρ c (ρ c⁻¹ v.1) = v.1
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl) }
  have hform : ∀ (n : ℕ) (v : V₀), ((σ ^ n) v).1 = ρ (c ^ n) v.1 := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, map_mul, Module.End.mul_apply]
      rfl
  have hσ : σ ^ (p ^ j) = 1 := by
    ext v
    rw [hform, hcj, map_one]
    rfl
  have hPG : IsPGroup p (Subgroup.zpowers σ) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ,
      one_zpow]
    rfl
  let Y : Submodule (ZMod 2) W := LinearMap.ker (ρ c - LinearMap.id)
  have hYmem : ∀ x : W, x ∈ Y ↔ ρ c x = x := fun x => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hYinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := by
    intro a ha u hu
    rw [hYmem] at hu ⊢
    rw [hcl c hc a ha, hu]
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) V₀) =
      Nat.card ↥(fixOn ρ U Y) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, mem_fixOn.2 ⟨?_, (mem_fixOn.1 v.1.2).2⟩⟩
        invFun := fun x => ⟨⟨x.1, mem_fixOn.2 ⟨Submodule.mem_top, (mem_fixOn.1 x.2).2⟩⟩, ?_⟩
        left_inv := fun v => rfl
        right_inv := fun x => rfl }
    · have h1 := MulAction.mem_fixedPoints.1 v.2 ⟨σ, Subgroup.mem_zpowers σ⟩
      rw [hYmem]
      have h2 : σ v.1 = v.1 := h1
      exact congrArg Subtype.val h2
    · rw [MulAction.mem_fixedPoints]
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      show (σ ^ i) _ = _
      apply Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
      apply Subtype.ext
      exact (hYmem x.1).1 (mem_fixOn.1 x.2).1
  have hcongr := hPG.card_modEq_card_fixedPoints V₀
  rw [hfix] at hcongr
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hne
  have hYtop : Y ≠ ⊤ := fun h => hx ((hYmem x).1 (h ▸ Submodule.mem_top))
  exact hY Y hYinv hYtop hcongr

theorem uc22p22h_card_fix_bot (U : Subgroup H) : Nat.card ↥(fixOn ρ U ⊥) = 1 := by
  have : fixOn ρ U ⊥ = ⊥ := bot_inf_eq _
  rw [this]
  exact Nat.card_unique

theorem uc22p22h_classify [Finite W] {L U : Subgroup H} (hUL : U ≤ L)
    {A₁ A₂ : Submodule (ZMod 2) W}
    (hsup : A₁ ⊔ A₂ = ⊤) (hinf : A₁ ⊓ A₂ = ⊥)
    (hI₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A₁) (hI₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A₂)
    (hirr₂ : ∀ C : Submodule (ZMod 2) W, C ≤ A₂ → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A₂)
    (hirr₁ : ∀ C : Submodule (ZMod 2) W, C ≤ A₁ → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A₁)
    {q : ℕ} (hq : 0 < q) (hc₁ : Nat.card ↥(fixOn ρ U A₁) = q)
    (hc₂ : Nat.card ↥(fixOn ρ U A₂) = q) :
    Nat.card ↥(fixOn ρ U ⊤) = q * q ∧
    ∀ Y : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y → Y ≠ ⊤ →
      Nat.card ↥(fixOn ρ U Y) = 1 ∨ Nat.card ↥(fixOn ρ U Y) = q := by
  have hcard_top : Nat.card ↥(fixOn ρ U ⊤) = q * q := by
    rw [← hsup, uc22p22h_card_fix_sup ρ (uc22p22h_inv_mono ρ hUL hI₁)
      (uc22p22h_inv_mono ρ hUL hI₂) hinf, hc₁, hc₂]
  refine ⟨hcard_top, fun Y hY hne => ?_⟩
  rcases hirr₁ (Y ⊓ A₁) inf_le_right (uc22p22h_inv_inf ρ hY hI₁) with h1 | h1
  · have hZ := uc22p22h_inv_sup ρ hY hI₁
    rcases hirr₂ ((Y ⊔ A₁) ⊓ A₂) inf_le_right (uc22p22h_inv_inf ρ hZ hI₂) with h2 | h2
    · left
      have hZeq : Y ⊔ A₁ = A₁ := by
        have := sup_inf_assoc_of_le A₂ (le_sup_right : A₁ ≤ Y ⊔ A₁)
        rw [hsup, top_inf_eq, inf_comm A₂, h2, sup_bot_eq] at this
        exact this
      have hYle : Y ≤ A₁ := hZeq ▸ le_sup_left
      have hY0 : Y = ⊥ := by rw [← h1]; exact (inf_eq_left.2 hYle).symm
      rw [hY0]
      exact uc22p22h_card_fix_bot ρ U
    · right
      have hA₂le : A₂ ≤ Y ⊔ A₁ := inf_eq_right.1 h2
      have hZtop : Y ⊔ A₁ = ⊤ := top_unique (hsup ▸ sup_le le_sup_right hA₂le)
      have h3 := uc22p22h_card_fix_sup ρ (uc22p22h_inv_mono ρ hUL hY)
        (uc22p22h_inv_mono ρ hUL hI₁) h1
      rw [hZtop, hcard_top, hc₁] at h3
      exact Nat.eq_of_mul_eq_mul_right hq h3.symm
  · right
    have hA₁le : A₁ ≤ Y := inf_eq_right.1 h1
    rcases hirr₂ (Y ⊓ A₂) inf_le_right (uc22p22h_inv_inf ρ hY hI₂) with h2 | h2
    · have hYeq : Y = A₁ := by
        have := sup_inf_assoc_of_le A₂ hA₁le
        rw [hsup, top_inf_eq, inf_comm A₂ Y, h2, sup_bot_eq] at this
        exact this
      rw [hYeq, hc₁]
    · exfalso
      apply hne
      exact top_unique (hsup ▸ sup_le hA₁le (inf_eq_right.1 h2))

end Core

section Num

theorem uc22p22h_numerics {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : (2 : ℤ) ^ (2 * k) ≡ -1 [ZMOD (p : ℤ)]) :
    1 ≤ k ∧ ¬ (2 ^ k ≡ 1 [MOD p]) ∧ ¬ (2 ^ k * 2 ^ k ≡ 1 [MOD p]) ∧
      ¬ (2 ^ k * 2 ^ k ≡ 2 ^ k [MOD p]) := by
  have hnd := uc22p22g_not_dvd_pred hp hp2 hmod
  have hqq : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by rw [← pow_add, two_mul]
  have hcop : Nat.gcd p (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h3 : ¬ (2 ^ k * 2 ^ k ≡ 1 [MOD p]) := by
    intro h
    apply hnd
    rw [← hqq]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow.trans (le_of_eq hqq.symm))).1 h.symm
  have h2 : ¬ (2 ^ k ≡ 1 [MOD p]) := fun h => h3 (by simpa using h.mul h)
  refine ⟨?_, h2, h3, fun h => h2 ?_⟩
  · by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 : (p : ℤ) ∣ 2 := by
      have := (Int.modEq_iff_dvd.1 hmod)
      simpa using (dvd_neg.1 (by
        simpa [sub_eq_add_neg, show (-1 : ℤ) + -1 = -2 by norm_num] using this))
    have : p ∣ 2 := by exact_mod_cast h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  · exact Nat.ModEq.cancel_left_of_coprime hcop (by simpa using h)

end Num

theorem uc22p22h_centOmega4m_holds : uc22p22g_CentOmega4m := by
  intro H _ _ W _ _ _ ρ hρ L k p hp hp2 hmod hsum c hc j hcj
  obtain ⟨hk, hq1, hq2, hq3⟩ := uc22p22h_numerics hp hp2 hmod
  suffices h : ∀ x : W, ρ c x = x by
    apply hρ
    rw [map_one]
    exact LinearMap.ext fun x => h x
  rcases hsum with ⟨A, hA, hsup, hinf⟩ | ⟨A, hA, hsup, hinf⟩
  ·
    have hA0 : A 0 = ⊤ := by
      rw [← hsup]
      exact (iSup_unique (f := A)).symm
    obtain ⟨F, _, _, _, hF, β, θ, hinv, hmem, hinj, hsurj, hact⟩ :=
      uc22p22h_pres ρ L hk (hA 0).2.2
    have hirr := uc22p22h_irr ρ L hk hF β θ hmem hinj hact
    obtain ⟨U₀, hU₀card, hU₀p⟩ := uc22p22h_exists_U hF θ
    have hc₁ := uc22p22h_card_fix ρ L hk hF β θ hmem hinj hsurj hact hinv U₀ hU₀card hU₀p
    have hUL : U₀.map L.subtype ≤ L := fun x hx => by
      obtain ⟨u, -, rfl⟩ := hx
      exact u.2
    refine uc22p22h_core ρ hUL hp hc hcj fun Y hY hne => ?_
    rcases hirr Y (hA0 ▸ le_top) hY with h0 | h0
    · rw [h0, uc22p22h_card_fix_bot, ← hA0, hc₁]
      exact hq1
    · exact absurd (h0.trans hA0) hne
  ·
    have hsup' : A 0 ⊔ A 1 = ⊤ := by
      rw [← hsup]
      refine le_antisymm (sup_le (le_iSup A 0) (le_iSup A 1)) (iSup_le fun i => ?_)
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have hinf' : A 0 ⊓ A 1 = ⊥ := by
      refine le_bot_iff.1 ((inf_le_inf_left (A 0) ?_).trans (hinf 0))
      exact le_iSup₂_of_le (1 : Fin 2) (show (1 : Fin 2) ∈ {j : Fin 2 | j ≠ 0} from by decide)
        le_rfl
    obtain ⟨F₁, _, _, _, hF₁, β₁, θ₁, hinv₁, hmem₁, hinj₁, hsurj₁, hact₁⟩ :=
      uc22p22h_pres ρ L hk (hA 0).2.2
    obtain ⟨F₂, _, _, _, hF₂, β₂, θ₂, hinv₂, hmem₂, hinj₂, hsurj₂, hact₂⟩ :=
      uc22p22h_pres ρ L hk (hA 1).2.2
    have hirr₁ := uc22p22h_irr ρ L hk hF₁ β₁ θ₁ hmem₁ hinj₁ hact₁
    have hirr₂ := uc22p22h_irr ρ L hk hF₂ β₂ θ₂ hmem₂ hinj₂ hact₂
    obtain ⟨U₀, hU₀card, hU₀p⟩ := uc22p22h_exists_U hF₁ θ₁
    have hc₁ := uc22p22h_card_fix ρ L hk hF₁ β₁ θ₁ hmem₁ hinj₁ hsurj₁ hact₁ hinv₁ U₀ hU₀card hU₀p
    have hc₂ := uc22p22h_card_fix ρ L hk hF₂ β₂ θ₂ hmem₂ hinj₂ hsurj₂ hact₂ hinv₂ U₀ hU₀card hU₀p
    have hUL : U₀.map L.subtype ≤ L := fun x hx => by
      obtain ⟨u, -, rfl⟩ := hx
      exact u.2
    obtain ⟨hctop, hcls⟩ := uc22p22h_classify ρ hUL hsup' hinf' hinv₁ hinv₂ hirr₂ hirr₁
      (Nat.pos_of_ne_zero (pow_ne_zero k two_ne_zero)) hc₁ hc₂
    refine uc22p22h_core ρ hUL hp hc hcj fun Y hY hne => ?_
    rw [hctop]
    rcases hcls Y hY hne with h1 | h1
    · rw [h1]
      exact hq2
    · rw [h1]
      exact hq3

end CFSG.LocalAnalysis.UniquenessCase.UC22
