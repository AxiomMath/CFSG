module

public import CFSG.Quasithin.H13.KGLieTwist
public import CFSG.Quasithin.H13.KGLiePair
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.CGT.Timmesfeld75
open scoped Matrix

section TwBasic

variable {ι : Type} {F : Type} [Field F]

@[expose] def IsHerm (a : ℕ) (X : Matrix ι ι F) : Prop := (frobPow a X)ᵀ = X

@[expose] def twist [Fintype ι] (a : ℕ) (g X : Matrix ι ι F) : Matrix ι ι F :=
  g * X * (frobPow a g)ᵀ

theorem frobPow_eq_map [CharP F 2] (a : ℕ) (X : Matrix ι ι F) :
    frobPow a X = X.map (iterateFrobenius F 2 a) := rfl

theorem frobPow_mul [Fintype ι] [CharP F 2] (a : ℕ) (A B : Matrix ι ι F) :
    frobPow a (A * B) = frobPow a A * frobPow a B := by
  rw [frobPow_eq_map, frobPow_eq_map, frobPow_eq_map, Matrix.map_mul]

theorem frobPow_one [DecidableEq ι] (a : ℕ) : frobPow a (1 : Matrix ι ι F) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [frobPow, Matrix.one_apply, h]

theorem frobPow_add [CharP F 2] (a : ℕ) (A B : Matrix ι ι F) :
    frobPow a (A + B) = frobPow a A + frobPow a B := by
  rw [frobPow_eq_map, frobPow_eq_map, frobPow_eq_map, Matrix.map_add]
  exact map_add _

theorem frobPow_zero_mat (a : ℕ) : frobPow a (0 : Matrix ι ι F) = 0 := by
  ext i j
  simp [frobPow]

theorem frobPow_transpose (a : ℕ) (X : Matrix ι ι F) : frobPow a Xᵀ = (frobPow a X)ᵀ := rfl

theorem frobPow_frobPow [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (X : Matrix ι ι F) :
    frobPow a (frobPow a X) = X := by
  have : Fintype F := Fintype.ofFinite F
  ext i j
  simp only [frobPow, Matrix.map_apply]
  rw [← pow_mul, ← pow_add, ← two_mul, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem twist_mul [Fintype ι] [CharP F 2] (a : ℕ) (A B X : Matrix ι ι F) :
    twist a (A * B) X = twist a A (twist a B X) := by
  simp only [twist, frobPow_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem twist_one [Fintype ι] [DecidableEq ι] (a : ℕ) (X : Matrix ι ι F) : twist a 1 X = X := by
  rw [twist, frobPow_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem twist_add [Fintype ι] (a : ℕ) (g X Y : Matrix ι ι F) :
    twist a g (X + Y) = twist a g X + twist a g Y := by
  simp only [twist, Matrix.mul_add, Matrix.add_mul]

theorem twist_smul [Fintype ι] (a : ℕ) (g X : Matrix ι ι F) (k : F) :
    twist a g (k • X) = k • twist a g X := by
  simp only [twist, Matrix.mul_smul, Matrix.smul_mul]

theorem twist_zero [Fintype ι] (a : ℕ) (g : Matrix ι ι F) : twist a g 0 = 0 := by
  simp [twist]

theorem twist_sub [Fintype ι] (a : ℕ) (g X Y : Matrix ι ι F) :
    twist a g (X - Y) = twist a g X - twist a g Y := by
  simp only [twist, Matrix.mul_sub, Matrix.sub_mul]

theorem isHerm_twist [Fintype ι] [CharP F 2] [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    (g : Matrix ι ι F) {X : Matrix ι ι F} (hX : IsHerm a X) : IsHerm a (twist a g X) := by
  unfold IsHerm at hX ⊢
  rw [twist, frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow hF,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]

theorem isHerm_add [CharP F 2] {a : ℕ} {X Y : Matrix ι ι F} (hX : IsHerm a X) (hY : IsHerm a Y) :
    IsHerm a (X + Y) := by
  unfold IsHerm at hX hY ⊢
  rw [frobPow_add, Matrix.transpose_add, hX, hY]

theorem isHerm_smul [CharP F 2] {a : ℕ} {k : F} (hk : k ^ 2 ^ a = k) {X : Matrix ι ι F}
    (hX : IsHerm a X) : IsHerm a (k • X) := by
  unfold IsHerm at hX ⊢
  rw [frobPow_smul, hk, Matrix.transpose_smul, hX]

theorem isHerm_zero (a : ℕ) : IsHerm a (0 : Matrix ι ι F) := by
  unfold IsHerm
  rw [frobPow_zero_mat, Matrix.transpose_zero]

theorem isHerm_one [DecidableEq ι] (a : ℕ) : IsHerm a (1 : Matrix ι ι F) := by
  unfold IsHerm
  rw [frobPow_one, Matrix.transpose_one]

end TwBasic

section Sylow

variable {Γ' : Type*} [Group Γ'] [Finite Γ'] {L' : Type*} [Group L'] [Finite L']

omit [Finite Γ'] in
theorem exists_conj_mem_of_sylow (π : Γ' →* L') (hπ : Function.Surjective π) {U : Subgroup Γ'}
    (hU2 : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) {S : Subgroup L'} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : ∃ x : Γ', ∀ u ∈ U, π (x * u * x⁻¹) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU'2 : IsPGroup 2 (U.map π) := hU2.map π
  have hU'i : ¬ 2 ∣ (U.map π).index := fun h => hUi (h.trans (Subgroup.index_map_dvd U hπ))
  obtain ⟨l, hl⟩ := exists_conjSubgroup_eq_of_sylow (IsPGroup.toSylow hU'2 hU'i)
    (IsPGroup.toSylow hS2 hSi)
  obtain ⟨x, rfl⟩ := hπ l
  refine ⟨x, fun u hu => ?_⟩
  have h1 : π (x * u * x⁻¹) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (π x) (U.map π) := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, map_mul, map_mul, map_inv]
    rw [show (π x)⁻¹ * (π x * π u * (π x)⁻¹) * π x = π u by group]
    exact Subgroup.mem_map_of_mem π hu
  rw [IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at hl
  rw [hl] at h1
  exact h1

end Sylow

section Data

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [CharP F 2]

structure TwData (a : ℕ) (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (U : Subgroup ↥Γ)
    (T : Matrix ι ι F → Matrix ι ι F) : Prop where
  herm : ∀ X, IsHerm a X → IsHerm a (T X)
  add : ∀ X Y, IsHerm a X → IsHerm a Y → T (X + Y) = T X + T Y
  invol : ∀ X, IsHerm a X → T (T X) = X
  ne : ∃ X, IsHerm a X ∧ T X ≠ X
  card : Nat.card {Y : Matrix ι ι F // ∃ X, IsHerm a X ∧ T X - X = Y} ≤ 4
  comm : ∀ u ∈ U, ∀ X, IsHerm a X →
    T (twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X) =
      twist a (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T X)
  norm : ∀ γ : ↥Γ, ∃ γ' : ↥Γ, ∀ X, IsHerm a X →
    T (twist a ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T X)) =
      twist a ((γ' : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X
  smul : ∀ k : F, k ^ 2 ^ a = k → ∀ X, IsHerm a X → T (k • X) = k • T X

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_twData (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)} {v : MulAut V}
    (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) [Finite F] {a : ℕ}
    (hF : Nat.card F = 2 ^ (2 * a)) {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (U : Subgroup ↥Γ) (hU2 : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (h16 : a = 1 ∨ 16 < Nat.card ↥(hermSub a ι F))
    (hr : (FFModel.twistTensor a Γ).Realizes L ⊤ ⊥) :
    ∃ T : Matrix ι ι F → Matrix ι ι F, TwData a Γ U T := by
  classical
  obtain ⟨π, hπ⟩ := hr
  obtain ⟨e₀, he⟩ := exists_coordEquiv rfl hπ
  set e : V ≃* ↥(hermSub a ι F) := e₀ with he₀
  set M : V → Matrix ι ι F := fun w =>
    Multiplicative.toAdd ((e w : ↥(hermSub a ι F)) : Multiplicative (Matrix ι ι F)) with hM
  have hMherm : ∀ w, IsHerm a (M w) := fun w => (e w).2
  have hMmul : ∀ w w', M (w * w') = M w + M w' := by
    intro w w'
    simp only [hM, map_mul, Subgroup.coe_mul, toAdd_mul]
  have hM1 : M 1 = 0 := by
    have h3 := hMmul 1 1
    rw [mul_one] at h3
    exact add_eq_left.mp h3.symm
  have hMinv : ∀ w, M w⁻¹ = -M w := by
    intro w
    have h0 := hMmul w w⁻¹
    rw [mul_inv_cancel, hM1] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  have hMinj : Function.Injective M := by
    intro w w' h
    apply e.injective
    apply Subtype.ext
    exact Multiplicative.toAdd.injective h
  have hMact : ∀ (γ : ↥Γ) (w : V), M (((π γ : ↥L) : MulAut V) w) =
      twist a ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (M w) := by
    intro γ w
    exact congrArg Multiplicative.toAdd (he (γ : (FFModel.twistTensor a Γ).Gam) w)
  set Mi : Matrix ι ι F → V := fun X =>
    if hX : IsHerm a X then e.symm ⟨Multiplicative.ofAdd X, hX⟩ else 1 with hMi
  have hMMi : ∀ X, IsHerm a X → M (Mi X) = X := by
    intro X hX
    simp only [hMi, hM, hX, dite_true, MulEquiv.apply_symm_apply]
    rfl
  have hMiM : ∀ w, Mi (M w) = w := fun w => hMinj (hMMi _ (hMherm w))
  have hMi0 : Mi 0 = 1 := by rw [← hM1, hMiM]
  have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
  have hNorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have hgN : g ∈ normalizer (L : Set (MulAut V)) := by
      rw [hB4.2.1]
      exact le_normalizer_quasithinGenFitting G hg
    exact (mem_normalizer_iff.1 hgN l).1 hl
  obtain ⟨S, ⟨hSL, hS2, hSi⟩, hSv⟩ := hc.sylow
  have : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have : Finite ↥Γ := Subtype.finite
  obtain ⟨πΓ, hπΓ⟩ : ∃ πΓ : ↥Γ →* ↥L, ∀ γ : ↥Γ, πΓ γ = π γ := ⟨π, fun _ => rfl⟩
  have hπΓs : Function.Surjective πΓ := fun l => by
    obtain ⟨γ, hγ⟩ := hπ.1 l
    exact ⟨γ, (hπΓ γ).trans hγ⟩
  obtain ⟨x, hx⟩ := exists_conj_mem_of_sylow πΓ hπΓs hU2 hUi (S := S.subgroupOf L)
    (hS2.comap_of_injective L.subtype L.subtype_injective) hSi
  set px : MulAut V := ((πΓ x : ↥L) : MulAut V) with hpx
  set v' : MulAut V := px⁻¹ * v * px with hv'
  have hpxG : px ∈ G := hLG (πΓ x).2
  have hv'G : v' ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hpxG) hc.mem) hpxG
  have hv'v' : v' * v' = 1 := by
    rw [hv', show px⁻¹ * v * px * (px⁻¹ * v * px) = px⁻¹ * (v * v) * px by group, hc.sq]
    group
  have hv'inv : v'⁻¹ = v' := inv_eq_of_mul_eq_one_right hv'v'
  have hv'1 : v' ≠ 1 := by
    intro h1
    apply hc.ne_one
    calc v = px * v' * px⁻¹ := by rw [hv']; group
      _ = 1 := by rw [h1]; group
  have hv'U : ∀ u ∈ U, v' * ((π u : ↥L) : MulAut V) = ((π u : ↥L) : MulAut V) * v' := by
    intro u hu
    have h1' := hSv (hx u hu)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1'
    have h1 : ((πΓ (x * u * x⁻¹) : ↥L) : MulAut V) * v =
        v * ((πΓ (x * u * x⁻¹) : ↥L) : MulAut V) := h1'
    have h2 : ((πΓ (x * u * x⁻¹) : ↥L) : MulAut V) = px * ((π u : ↥L) : MulAut V) * px⁻¹ := by
      rw [map_mul, map_mul, map_inv, hπΓ u]
      rfl
    rw [h2] at h1
    calc v' * ((π u : ↥L) : MulAut V)
        = px⁻¹ * (v * (px * ((π u : ↥L) : MulAut V) * px⁻¹)) * px := by rw [hv']; group
      _ = px⁻¹ * ((px * ((π u : ↥L) : MulAut V) * px⁻¹) * v) * px := by rw [← h1]
      _ = ((π u : ↥L) : MulAut V) * v' := by rw [hv']; group
  have hrk : (commHom v).ker.index ≤ 4 := by
    rw [← fixV_zpowers_eq_ker]
    exact index_le_four_of_rkIdx hV2 hc.rank
  have hker : (commHom v').ker = (commHom v).ker.map px⁻¹.toMonoidHom := by
    ext w
    rw [mem_ker_commHom, Subgroup.mem_map]
    constructor
    · intro hw
      refine ⟨px w, ?_, ?_⟩
      · rw [mem_ker_commHom]
        have := congrArg px hw
        simp only [hv', MulAut.mul_apply, MulAut.apply_inv_self] at this
        exact this
      · show px⁻¹ (px w) = w
        exact MulAut.inv_apply_self _ px w
    · rintro ⟨w', hw', rfl⟩
      rw [mem_ker_commHom] at hw'
      show v' (px⁻¹ w') = px⁻¹ w'
      simp only [hv', MulAut.mul_apply, MulAut.apply_inv_self, hw']
  have hrk' : (commHom v').ker.index ≤ 4 := by
    rw [hker, Subgroup.index_map_of_bijective px⁻¹.bijective]
    exact hrk
  set T : Matrix ι ι F → Matrix ι ι F := fun X => if IsHerm a X then M (v' (Mi X)) else X
    with hT
  have hTM : ∀ w, T (M w) = M (v' w) := by
    intro w
    simp only [hT, hMherm w, ite_true, hMiM]
  have hTherm : ∀ X, IsHerm a X → T X = M (v' (Mi X)) := fun X hX => by
    simp only [hT, hX, ite_true]
  have hT0 : T 0 = 0 := by
    rw [hTherm 0 (isHerm_zero a), hMi0, map_one, hM1]
  refine ⟨T, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro X hX
    rw [hTherm X hX]
    exact hMherm _
  · intro X Y hX hY
    obtain ⟨w, rfl⟩ : ∃ w, M w = X := ⟨Mi X, hMMi X hX⟩
    obtain ⟨w', rfl⟩ : ∃ w', M w' = Y := ⟨Mi Y, hMMi Y hY⟩
    rw [← hMmul, hTM, hTM, hTM, map_mul, hMmul]
  · intro X hX
    obtain ⟨w, rfl⟩ : ∃ w, M w = X := ⟨Mi X, hMMi X hX⟩
    rw [hTM, hTM]
    congr 1
    have := congrArg (fun g : MulAut V => g w) hv'v'
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  · obtain ⟨w, hw⟩ : ∃ w, v' w ≠ w := by
      by_contra hne
      push Not at hne
      exact hv'1 (MulEquiv.ext hne)
    refine ⟨M w, hMherm w, ?_⟩
    rw [hTM]
    exact fun h => hw (hMinj h)
  ·
    have hsurj : Function.Surjective (fun z : ↥(commHom v').range =>
        (⟨M (z : V), by
          obtain ⟨w, hw⟩ := z.2
          refine ⟨M w, hMherm w, ?_⟩
          rw [hTM, ← hw]
          show M (v' w) - M w = M (v' w * w⁻¹)
          rw [hMmul, hMinv, sub_eq_add_neg]⟩ :
          {Y : Matrix ι ι F // ∃ X, IsHerm a X ∧ T X - X = Y})) := by
      rintro ⟨Y, X, hX, rfl⟩
      obtain ⟨w, rfl⟩ : ∃ w, M w = X := ⟨Mi X, hMMi X hX⟩
      refine ⟨⟨v' w * w⁻¹, w, rfl⟩, ?_⟩
      apply Subtype.ext
      show M (v' w * w⁻¹) = T (M w) - M w
      rw [hTM, hMmul, hMinv, sub_eq_add_neg]
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [← Subgroup.index_ker] at h1
    exact h1.trans hrk'
  · intro u hu X hX
    obtain ⟨w, rfl⟩ : ∃ w, M w = X := ⟨Mi X, hMMi X hX⟩
    rw [← hMact u w, hTM, hTM, ← hMact u (v' w)]
    congr 1
    have := congrArg (fun g : MulAut V => g w) (hv'U u hu)
    simpa only [MulAut.mul_apply] using this
  · intro γ
    have hm : v' * ((π γ : ↥L) : MulAut V) * v'⁻¹ ∈ L := hNorm v' hv'G _ (π γ).2
    obtain ⟨γ', hγ'⟩ := hπ.1 ⟨_, hm⟩
    refine ⟨γ', fun X hX => ?_⟩
    obtain ⟨w, rfl⟩ : ∃ w, M w = X := ⟨Mi X, hMMi X hX⟩
    rw [hTM, ← hMact γ (v' w), hTM, ← hMact (γ' : ↥Γ) w]
    congr 1
    have h1 : ((π γ' : ↥L) : MulAut V) = v' * ((π γ : ↥L) : MulAut V) * v'⁻¹ :=
      congrArg Subtype.val hγ'
    rw [h1, hv'inv]
    rfl
  ·
    intro k hk X hX
    by_cases hk0 : k = 0
    · subst hk0
      rw [zero_smul, zero_smul, hT0]
    rcases h16 with ha1 | h16
    ·
      subst ha1
      have hk1 : k = 1 := by
        have : k * (k - 1) = 0 := by linear_combination hk
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk0)
      rw [hk1, one_smul, one_smul]
    ·
      have hkk : ∀ X : Matrix ι ι F, IsHerm a X → IsHerm a (k • X) := fun X hX =>
        isHerm_smul hk hX
      have hk' : k⁻¹ ^ 2 ^ a = k⁻¹ := by rw [inv_pow, hk]
      have hmul' : ∀ w w', Mi (k • M (w * w')) = Mi (k • M w) * Mi (k • M w') := by
        intro w w'
        apply hMinj
        have e1 : M (Mi (k • M (w * w'))) = k • M w + k • M w' := by
          rw [hMMi _ (hkk _ (hMherm _)), hMmul, smul_add]
        have e2 : M (Mi (k • M w) * Mi (k • M w')) = k • M w + k • M w' := by
          rw [hMmul, hMMi _ (hkk _ (hMherm _)), hMMi _ (hkk _ (hMherm _))]
        rw [e1, e2]
      set mk : MulAut V :=
        { toFun := fun w => Mi (k • M w)
          invFun := fun w => Mi (k⁻¹ • M w)
          left_inv := fun w => by
            show Mi (k⁻¹ • M (Mi (k • M w))) = w
            rw [hMMi _ (hkk _ (hMherm w)), smul_smul, inv_mul_cancel₀ hk0, one_smul, hMiM]
          right_inv := fun w => by
            show Mi (k • M (Mi (k⁻¹ • M w))) = w
            rw [hMMi _ (isHerm_smul hk' (hMherm w)), smul_smul, mul_inv_cancel₀ hk0, one_smul,
              hMiM]
          map_mul' := hmul' } with hmk
      have hMmk : ∀ w, M (mk w) = k • M w := fun w => hMMi _ (hkk _ (hMherm w))
      have hmkL : ∀ l ∈ L, mk * l = l * mk := by
        intro l hl
        obtain ⟨γ, hγ⟩ := hπΓs ⟨l, hl⟩
        have hl' : l = ((π γ : ↥L) : MulAut V) := by rw [← hπΓ γ, hγ]
        rw [hl']
        ext w
        apply hMinj
        simp only [MulAut.mul_apply]
        rw [hMmk, hMact, hMact, hMmk, twist_smul]
      have hvL : ∀ l ∈ L, v'⁻¹ * l * v' ∈ L := by
        intro l hl
        have := hNorm v'⁻¹ (G.inv_mem hv'G) l hl
        simpa using this
      have hV : 16 < Nat.card V := by
        rw [Nat.card_congr e.toEquiv]
        exact h16
      have hcomm := comm_of_scalar hB4.2.2.2 hvL hrk' hV hmkL
      have h1 : Mi (k • X) = mk (Mi X) := by
        apply hMinj
        rw [hMMi _ (hkk X hX), hMmk, hMMi X hX]
      rw [hTherm _ (hkk X hX), hTherm X hX, h1]
      have := congrArg (fun g : MulAut V => g (Mi X)) hcomm
      simp only [MulAut.mul_apply] at this
      rw [this, hMmk]

end Data

end CFSG.Quasithin.H13.KGLie
