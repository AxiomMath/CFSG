module

public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsForms
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem tfmo_repr_smul_basis {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (c : ZMod p)
    (i j : Fin n) : (b.repr (c • b i)) j = if j = i then c else 0 := by
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg (Ne.symm h), smul_zero, if_neg h]

private theorem tfmo_pairUnit_self {n : ℕ} {i j : Fin n} (_hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c i = c := by
  rw [pairUnit, if_pos rfl]

private theorem tfmo_pairUnit_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c j = c⁻¹ := by
  rw [pairUnit, if_neg (Ne.symm hij), if_pos rfl]

private theorem tfmo_pairUnit_ne {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (c : (ZMod p)ˣ) : pairUnit p i j c k = 1 := by
  rw [pairUnit, if_neg hki, if_neg hkj]

private theorem tfmo_pairUnit_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p j i c = pairUnit p i j c⁻¹ := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [tfmo_pairUnit_other (Ne.symm hij) c, tfmo_pairUnit_self hij c⁻¹]
  · by_cases hkj : k = j
    · subst hkj
      rw [tfmo_pairUnit_self (Ne.symm hij) c, tfmo_pairUnit_other hij c⁻¹, inv_inv]
    · rw [tfmo_pairUnit_ne hkj hki c, tfmo_pairUnit_ne hki hkj c⁻¹]

private theorem tfmo_pairUnit_mul_comp_swap {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a c : (ZMod p)ˣ) :
    pairUnit p i j a * (pairUnit p i j c ∘ Equiv.swap i j) = pairUnit p i j (a * c⁻¹) := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [Pi.mul_apply, Function.comp_apply, Equiv.swap_apply_left, tfmo_pairUnit_self hij a,
      tfmo_pairUnit_other hij c, tfmo_pairUnit_self hij (a * c⁻¹)]
  · by_cases hkj : k = j
    · subst hkj
      rw [Pi.mul_apply, Function.comp_apply, Equiv.swap_apply_right, tfmo_pairUnit_other hij a,
        tfmo_pairUnit_self hij c, tfmo_pairUnit_other hij (a * c⁻¹)]
      exact mul_comm _ _
    · rw [Pi.mul_apply, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj,
        tfmo_pairUnit_ne hki hkj a, tfmo_pairUnit_ne hki hkj c, one_mul,
        tfmo_pairUnit_ne hki hkj (a * c⁻¹)]

private theorem tfmo_twist_apply_left {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j : Fin n} (hij : i ≠ j) (a : (ZMod p)ˣ) :
    (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) (b i) =
      (a⁻¹ : ZMod p) • b j := by
  rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_left, diagMap_apply_basis,
    tfmo_pairUnit_other hij a, Units.val_inv_eq_inv_val]

private theorem tfmo_twist_apply_right {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j : Fin n} (hij : i ≠ j) (a : (ZMod p)ˣ) :
    (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) (b j) =
      (a : ZMod p) • b i := by
  rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_right, diagMap_apply_basis,
    tfmo_pairUnit_self hij a]

private theorem tfmo_twist_apply_of_ne {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (a : (ZMod p)ˣ) :
    (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) (b k) = b k := by
  rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne hki hkj,
    diagMap_apply_basis, tfmo_pairUnit_ne hki hkj a, Units.val_one, one_smul]

private theorem tfmo_pairUnit_neg_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    pairUnit p i j (-1) =
      (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) *
        (fun k => if k = j then (-1 : (ZMod p)ˣ) else 1) := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [tfmo_pairUnit_self hij (-1), Pi.mul_apply, if_pos rfl, if_neg hij, mul_one]
  · by_cases hkj : k = j
    · subst hkj
      rw [tfmo_pairUnit_other hij (-1), Pi.mul_apply, if_neg (Ne.symm hij), if_pos rfl,
        one_mul, inv_neg, inv_one]
    · rw [tfmo_pairUnit_ne hki hkj (-1), Pi.mul_apply, if_neg hki, if_neg hkj, mul_one]

theorem diagMap_mul_permMap_inj {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {d d' : Fin n → (ZMod p)ˣ} {σ σ' : Equiv.Perm (Fin n)}
    (h : diagMap p b d * permMap p b σ = diagMap p b d' * permMap p b σ') : d = d' ∧ σ = σ' := by
  have hval : ∀ k, (d (σ k) : ZMod p) = if σ k = σ' k then (d' (σ' k) : ZMod p) else 0 := by
    intro k
    have hk : (d (σ k) : ZMod p) • b (σ k) = (d' (σ' k) : ZMod p) • b (σ' k) := by
      have h1 := congrArg (fun g : V ≃ₗ[ZMod p] V => g (b k)) h
      simpa only [LinearEquiv.mul_apply, diagMap_apply_basis, permMap_apply_basis] using h1
    have h2 := congrArg (fun w : V => b.repr w (σ k)) hk
    simpa only [tfmo_repr_smul_basis, if_true] using h2
  have hσ : σ = σ' := by
    refine Equiv.ext fun k => ?_
    by_contra hne
    have h0 := hval k
    rw [if_neg hne] at h0
    exact (d (σ k)).ne_zero h0
  subst hσ
  refine ⟨?_, rfl⟩
  funext j
  obtain ⟨k, hk⟩ := σ.surjective j
  rw [← hk]
  exact Units.ext (by simpa using hval k)

theorem twist_swap_symm {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j)
    (c : (ZMod p)ˣ) :
    diagMap p b (pairUnit p j i c) * permMap p b (Equiv.swap j i) =
      diagMap p b (pairUnit p i j c⁻¹) * permMap p b (Equiv.swap i j) := by
  rw [tfmo_pairUnit_swap hij c, Equiv.swap_comm j i]

theorem twist_mul_twist_eq {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hij : i ≠ j) (a c : (ZMod p)ˣ) :
    diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p i j c) * permMap p b (Equiv.swap i j)) =
      diagMap p b (pairUnit p i j (a * c⁻¹)) := by
  have hperm : permMap p b (Equiv.swap i j) * permMap p b (Equiv.swap i j) = 1 := by
    rw [permMap_mul, Equiv.swap_mul_self, permMap_one]
  have hconj : permMap p b (Equiv.swap i j) * diagMap p b (pairUnit p i j c) *
      (permMap p b (Equiv.swap i j))⁻¹ = diagMap p b (pairUnit p i j c ∘ Equiv.swap i j) := by
    rw [permMap_mul_diagMap_mul_inv, Equiv.symm_swap]
  calc diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p i j c) * permMap p b (Equiv.swap i j))
      = diagMap p b (pairUnit p i j a) *
          (permMap p b (Equiv.swap i j) * diagMap p b (pairUnit p i j c) *
            (permMap p b (Equiv.swap i j))⁻¹) *
          (permMap p b (Equiv.swap i j) * permMap p b (Equiv.swap i j)) := by group
    _ = diagMap p b (pairUnit p i j a) *
          diagMap p b (pairUnit p i j c ∘ Equiv.swap i j) * 1 := by rw [hconj, hperm]
    _ = diagMap p b (pairUnit p i j a) *
          diagMap p b (pairUnit p i j c ∘ Equiv.swap i j) := by rw [mul_one]
    _ = diagMap p b (pairUnit p i j a * (pairUnit p i j c ∘ Equiv.swap i j)) := by
          rw [diagMap_mul]
    _ = diagMap p b (pairUnit p i j (a * c⁻¹)) := by
          rw [tfmo_pairUnit_mul_comp_swap hij]

private theorem tfmo_perm_pow_three {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {τ : Equiv.Perm (Fin n)} (hτ : τ ^ 3 = 1) (d : Fin n → (ZMod p)ˣ) :
    (diagMap p b d * permMap p b τ) ^ 3 =
      diagMap p b (fun l => d l * d (τ l) * d (τ (τ l))) := by
  refine b.ext' fun l => ?_
  have hτl : τ (τ (τ l)) = l := by
    have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hτ) l
    simpa [pow_three, Equiv.Perm.mul_apply] using this
  rw [pow_three]
  simp only [LinearEquiv.mul_apply, diagMap_apply_basis, permMap_apply_basis, map_smul,
    smul_smul]
  rw [hτl]
  congr 1
  simp only [Units.val_mul]
  ring

private theorem tfmo_swap_mul_swap_vals {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) i = j ∧
      (Equiv.swap i j * Equiv.swap j k) j = k ∧
      (Equiv.swap i j * Equiv.swap j k) k = i := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik,
      Equiv.swap_apply_left]
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]

private theorem tfmo_orbit_e_vals {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a c : (ZMod p)ˣ) :
    (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm)) i = a * c ∧
      (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm)) j = a⁻¹ ∧
      (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm)) k = c⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · show pairUnit p i j a i * pairUnit p j k c (Equiv.swap i j i) = a * c
    rw [Equiv.swap_apply_left, tfmo_pairUnit_self hij a, tfmo_pairUnit_self hjk c]
  · show pairUnit p i j a j * pairUnit p j k c (Equiv.swap i j j) = a⁻¹
    rw [Equiv.swap_apply_right, tfmo_pairUnit_other hij a, tfmo_pairUnit_ne hij hik c, mul_one]
  · show pairUnit p i j a k * pairUnit p j k c (Equiv.swap i j k) = c⁻¹
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
      tfmo_pairUnit_ne (Ne.symm hik) (Ne.symm hjk) a, tfmo_pairUnit_other hjk c, one_mul]

private theorem tfmo_three_orbit_eq_one {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a c : (ZMod p)ˣ) :
    (fun l => (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm)) l *
        (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm))
          ((Equiv.swap i j * Equiv.swap j k) l) *
        (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm))
          ((Equiv.swap i j * Equiv.swap j k)
            ((Equiv.swap i j * Equiv.swap j k) l))) = 1 := by
  obtain ⟨hτi, hτj, hτk⟩ := tfmo_swap_mul_swap_vals hij hjk hik
  obtain ⟨hei, hej, hek⟩ := tfmo_orbit_e_vals hij hjk hik a c
  funext l
  by_cases hli : l = i
  · subst hli
    rw [hτi, hτj, hei, hej, hek]
    simp [mul_assoc]
  · by_cases hlj : l = j
    · subst hlj
      rw [hτj, hτk, hej, hek, hei]
      simp [mul_comm, mul_assoc]
    · by_cases hlk : l = k
      · subst hlk
        rw [hτk, hτi, hek, hei, hej]
        simp [mul_comm, mul_assoc]
      · have hτl : (Equiv.swap i j * Equiv.swap j k) l = l := by
          simp only [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hlj hlk, Equiv.swap_apply_of_ne_of_ne hli hlj]
        have hel : pairUnit p i j a l * pairUnit p j k c ((Equiv.swap i j) l) = 1 := by
          simp only [Equiv.swap_apply_of_ne_of_ne hli hlj, pairUnit]
          simp [hli, hlj, hlk]
        simp [hτl, hel]

theorem twist_mul_twist_pow_three {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a c : (ZMod p)ˣ) :
    (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p j k c) * permMap p b (Equiv.swap j k))) ^ 3 = 1 := by
  have hτ3 : (Equiv.swap i j * Equiv.swap j k) ^ 3 = 1 := by
    rw [show Equiv.swap i j = Equiv.swap j i from Equiv.swap_comm i j,
      ← Equiv.Perm.IsThreeCycle.orderOf
        (Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hij) hjk hik)]
    exact pow_orderOf_eq_one _
  have hxy : (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) *
      (diagMap p b (pairUnit p j k c) * permMap p b (Equiv.swap j k)) =
      diagMap p b (pairUnit p i j a * (pairUnit p j k c ∘ (Equiv.swap i j).symm)) *
        permMap p b (Equiv.swap i j * Equiv.swap j k) := by
    rw [mul_diagMap_permMap]
  rw [hxy, tfmo_perm_pow_three b hτ3 _,
    tfmo_three_orbit_eq_one hij hjk hik a c, diagMap_one]

theorem orderOf_diagMap_pairUnit {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hij : i ≠ j) (u : (ZMod p)ˣ) : orderOf (diagMap p b (pairUnit p i j u)) = orderOf u := by
  let φ : (ZMod p)ˣ →* (V ≃ₗ[ZMod p] V) :=
    { toFun := fun u => diagMap p b (pairUnit p i j u)
      map_one' := by rw [pairUnit_one, diagMap_one]
      map_mul' := fun u v => by rw [pairUnit_mul, diagMap_mul] }
  have hinj : Function.Injective φ := by
    intro u v huv
    have h : diagMap p b (pairUnit p i j u) (b i) = diagMap p b (pairUnit p i j v) (b i) :=
      congrArg (fun g : V ≃ₗ[ZMod p] V => g (b i)) huv
    rw [diagMap_apply_basis, tfmo_pairUnit_self hij u, diagMap_apply_basis,
      tfmo_pairUnit_self hij v] at h
    have h2 := congrArg (fun w : V => b.repr w i) h
    simp only [tfmo_repr_smul_basis, if_true] at h2
    exact Units.ext h2
  exact orderOf_injective φ hinj u

private theorem tfmo_twist_disjoint_vals {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (a c : (ZMod p)ˣ)
    (g : V ≃ₗ[ZMod p] V)
    (hg : g = (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) *
      (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))) :
    g (b i) = (a⁻¹ : ZMod p) • b j ∧ g (b j) = (a : ZMod p) • b i ∧
      g (b k) = (c⁻¹ : ZMod p) • b l ∧ g (b l) = (c : ZMod p) • b k ∧
      (∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ l → g (b m) = b m) := by
  subst hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, tfmo_twist_apply_of_ne b hik hil c,
      tfmo_twist_apply_left b hij a]
  · rw [LinearEquiv.mul_apply, tfmo_twist_apply_of_ne b hjk hjl c,
      tfmo_twist_apply_right b hij a]
  · rw [LinearEquiv.mul_apply, tfmo_twist_apply_left b hkl c, map_smul,
      tfmo_twist_apply_of_ne (k := l) b (Ne.symm hil) (Ne.symm hjl) a]
  · rw [LinearEquiv.mul_apply, tfmo_twist_apply_right b hkl c, map_smul,
      tfmo_twist_apply_of_ne b (Ne.symm hik) (Ne.symm hjk) a]
  · intro m hmi hmj hmk hml
    rw [LinearEquiv.mul_apply, tfmo_twist_apply_of_ne b hmk hml c,
      tfmo_twist_apply_of_ne b hmi hmj a]

private theorem tfmo_twist_disjoint_sq_eq_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (a c : (ZMod p)ˣ) :
    ((diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) *
      (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))) ^ 2 = 1 := by
  let g : V ≃ₗ[ZMod p] V := (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)) *
      (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))
  obtain ⟨hgi, hgj, hgk, hgl, hgfix⟩ :=
    tfmo_twist_disjoint_vals b hij hkl hik hil hjk hjl a c g rfl
  change g ^ 2 = 1
  rw [pow_two]
  refine b.ext' fun m => ?_
  rw [LinearEquiv.mul_apply]
  change g (g (b m)) = b m
  by_cases hmi : m = i
  · rw [hmi, hgi, map_smul, hgj, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_smul]
  · by_cases hmj : m = j
    · rw [hmj, hgj, map_smul, hgi, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, one_smul]
    · by_cases hmk : m = k
      · rw [hmk, hgk, map_smul, hgl, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_smul]
      · by_cases hml : m = l
        · rw [hml, hgl, map_smul, hgk, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
            mul_inv_cancel, Units.val_one, one_smul]
        · simp [hgfix m hmi hmj hmk hml]

theorem orderOf_twist_mul_twist {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (a c : (ZMod p)ˣ) :
    orderOf (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))) ≤ 3 ∨
      orderOf (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))) = orderOf (a * c⁻¹) ∨
      orderOf (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) *
        (diagMap p b (pairUnit p k l c) * permMap p b (Equiv.swap k l))) = orderOf (a * c) := by
  rcases em ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) with hsame | hsame
  · rcases hsame with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · subst hk; subst hl
      exact Or.inr (Or.inl (by
        rw [twist_mul_twist_eq b hij a c, orderOf_diagMap_pairUnit b hij (a * c⁻¹)]))
    · subst hk; subst hl
      exact Or.inr (Or.inr (by
        rw [twist_swap_symm b hij c, twist_mul_twist_eq b hij a c⁻¹,
          orderOf_diagMap_pairUnit b hij (a * (c⁻¹)⁻¹), inv_inv]))
  · by_cases hdisj : i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l
    · exact Or.inl (le_trans (orderOf_le_of_pow_eq_one (by norm_num)
        (tfmo_twist_disjoint_sq_eq_one b hij hkl hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2
          a c)) (by norm_num))
    · have hcase : i = k ∨ i = l ∨ j = k ∨ j = l := by
        by_contra hc
        exact hdisj
          ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr (Or.inl h)),
            fun h => hc (Or.inr (Or.inr (Or.inl h))),
            fun h => hc (Or.inr (Or.inr (Or.inr h)))⟩
      rcases hcase with h | h | h | h
      · subst h
        have hjl : j ≠ l := fun h => hsame (Or.inl ⟨rfl, h.symm⟩)
        refine Or.inl (orderOf_le_of_pow_eq_one (by norm_num) ?_)
        rw [twist_swap_symm b (Ne.symm hij) a]
        exact twist_mul_twist_pow_three b (Ne.symm hij) hkl hjl a⁻¹ c
      · subst h
        have hjk : j ≠ k := fun h => hsame (Or.inr ⟨h.symm, rfl⟩)
        refine Or.inl (orderOf_le_of_pow_eq_one (by norm_num) ?_)
        rw [twist_swap_symm b (Ne.symm hij) a, twist_swap_symm b (Ne.symm hkl) c]
        exact twist_mul_twist_pow_three b (Ne.symm hij) (Ne.symm hkl) hjk a⁻¹ c⁻¹
      · subst h
        have hil : i ≠ l := fun h => hsame (Or.inr ⟨rfl, h.symm⟩)
        exact Or.inl (orderOf_le_of_pow_eq_one (by norm_num)
          (twist_mul_twist_pow_three b hij hkl hil a c))
      · subst h
        have hik : i ≠ k := fun h => hsame (Or.inl ⟨h.symm, rfl⟩)
        refine Or.inl (orderOf_le_of_pow_eq_one (by norm_num) ?_)
        rw [twist_swap_symm b (Ne.symm hkl) c]
        exact twist_mul_twist_pow_three b hij (Ne.symm hkl) hik a c⁻¹

theorem signChange_mem_g2mmn {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i₀ i₁ : Fin n)
    (ζ : (ZMod p)ˣ) (k : Fin n) :
    diagMap p b (fun j => if j = k then -1 else 1) ∈ g2mmn p b i₀ i₁ ζ := by
  classical
  by_cases hk : k = i₀
  · subst hk
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · have hgen : diagMap p b (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈
        g2mmn p b i₀ i₁ ζ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hperm : permMap p b (Equiv.swap i₀ k) ∈ g2mmn p b i₀ i₁ ζ :=
      Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    have hconj : permMap p b (Equiv.swap i₀ k) *
        diagMap p b (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) *
        (permMap p b (Equiv.swap i₀ k))⁻¹ =
        diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
      rw [permMap_mul_diagMap_mul_inv, Equiv.symm_swap]
      congr 1
      funext x
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)

private theorem tfmo_sign_not_mem_gmmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (k : Fin n) :
    diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∉ gmmn p b i₀ i₁ ζ := by
  intro hS
  obtain ⟨d, σ, _hd, hprod, hform⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn b hi hS
  have hform' : diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      permMap p b 1 = diagMap p b d * permMap p b σ := by
    rw [permMap_one, mul_one]; exact hform
  obtain ⟨hd_eq, -⟩ := diagMap_mul_permMap_inj b hform'
  have hprod_sign : (∏ j : Fin n, (if j = k then (-1 : (ZMod p)ˣ) else 1)) = -1 := by
    rw [Fintype.prod_eq_mul_prod_compl k]
    have h1 : ∏ j ∈ ({k}ᶜ : Finset (Fin n)),
        (if j = k then (-1 : (ZMod p)ˣ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      exact if_neg hj
    rw [h1, mul_one]; simp
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by
      have h1 : (-1 : ZMod p) = 1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
      calc (2 : ZMod p) = 1 + 1 := by ring
        _ = -1 + 1 := congrArg (fun x : ZMod p => x + 1) h1.symm
        _ = 0 := by ring
    exact ZMod.prime_ne_zero p 2 hp h2
  rw [← hd_eq] at hprod
  rw [hprod_sign] at hprod
  exact hne hprod

private theorem tfmo_exists_twist_of_isRefl_mem_gmmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {x : V ≃ₗ[ZMod p] V} (hx : x ∈ gmmn p b i₀ i₁ ζ) (hxr : IsRefl p x) :
    ∃ i j : Fin n, i ≠ j ∧ ∃ a ∈ Subgroup.zpowers ζ,
      x = diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) := by
  obtain ⟨d, σ, hd, _hprod, hxform⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn b hi hx
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, x (b i) = c i • b (σ i) := by
    refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => ?_⟩
    rw [hxform, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  rcases eq_sign_or_eq_twist_of_isRefl hp b hxr hmon with ⟨k, hk⟩ | ⟨i, j, hij, c, hc⟩
  · exact (tfmo_sign_not_mem_gmmn hp b hi k (hk ▸ hx)).elim
  · obtain ⟨hd_eq, hσ_eq⟩ := diagMap_mul_permMap_inj b (hxform.symm.trans hc)
    refine ⟨i, j, hij, c, ?_, hc⟩
    have hmem : c ∈ Subgroup.zpowers ζ := by
      have h := hd (σ i)
      rw [hd_eq, hσ_eq, Equiv.swap_apply_left] at h
      rw [show pairUnit p i j c j = c⁻¹ by simp [pairUnit, Ne.symm hij]] at h
      simpa using Subgroup.inv_mem _ h
    exact hmem

theorem orderOf_mul_le_three_or_dvd_of_mem_gmmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {x y : V ≃ₗ[ZMod p] V} (hx : x ∈ gmmn p b i₀ i₁ ζ) (hy : y ∈ gmmn p b i₀ i₁ ζ)
    (hxr : IsRefl p x) (hyr : IsRefl p y) :
    orderOf (x * y) ≤ 3 ∨ orderOf (x * y) ∣ orderOf ζ := by
  obtain ⟨i, j, hij, a, ha, rfl⟩ := tfmo_exists_twist_of_isRefl_mem_gmmn hp b hi ζ hx hxr
  obtain ⟨k, l, hkl, c, hc, rfl⟩ := tfmo_exists_twist_of_isRefl_mem_gmmn hp b hi ζ hy hyr
  rcases orderOf_twist_mul_twist b hij hkl a c with h | h | h
  · exact Or.inl h
  · exact Or.inr (by
      rw [h]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hc)))
  · exact Or.inr (by
      rw [h]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.mul_mem _ ha hc))

private theorem tfmo_pow_lcm_eq_one_of_mem_closure {ζ u : (ZMod p)ˣ}
    (hu : u ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) :
    u ^ Nat.lcm 2 (orderOf ζ) = 1 := by
  have hζ : ζ ^ Nat.lcm 2 (orderOf ζ) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right 2 (orderOf ζ))
  have hneg : (-1 : (ZMod p)ˣ) ^ Nat.lcm 2 (orderOf ζ) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    exact Even.neg_one_pow (even_iff_two_dvd.mpr (Nat.dvd_lcm_left 2 (orderOf ζ)))
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | rfl
      · exact hζ
      · exact hneg
  | one => rw [one_pow]
  | mul x y _ _ hx hy => rw [mul_pow, hx, hy, one_mul]
  | inv x _ hx => rw [inv_pow, hx, inv_one]

private theorem tfmo_exists_sign_or_twist_of_isRefl_mem_g2mmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {x : V ≃ₗ[ZMod p] V} (hx : x ∈ g2mmn p b i₀ i₁ ζ) (hxr : IsRefl p x) :
    (∃ k, x = diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1)) ∨
      ∃ i j : Fin n, i ≠ j ∧ ∃ a ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ),
        x = diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j) := by
  obtain ⟨d, σ, hd, _hprod, hxform⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn b hi hx
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, x (b i) = c i • b (σ i) := by
    refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => ?_⟩
    rw [hxform, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  rcases eq_sign_or_eq_twist_of_isRefl hp b hxr hmon with ⟨k, hk⟩ | ⟨i, j, hij, c, hc⟩
  · exact Or.inl ⟨k, hk⟩
  · obtain ⟨hd_eq, hσ_eq⟩ := diagMap_mul_permMap_inj b (hxform.symm.trans hc)
    refine Or.inr ⟨i, j, hij, c, ?_, hc⟩
    have h := hd (σ i)
    rw [hd_eq, hσ_eq, Equiv.swap_apply_left] at h
    rw [show pairUnit p i j c j = c⁻¹ by simp [pairUnit, Ne.symm hij]] at h
    simpa using Subgroup.inv_mem _ h

private theorem tfmo_sign_apply_of_ne {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {k m : Fin n} (hm : m ≠ k) :
    diagMap p b (fun l => if l = k then (-1 : (ZMod p)ˣ) else 1) (b m) = b m := by
  rw [diagMap_apply_basis, if_neg hm, Units.val_one, one_smul]

private theorem tfmo_sign_apply_self {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    diagMap p b (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) (b k) = -b k := by
  rw [diagMap_apply_basis, if_pos rfl]; simp

private theorem tfmo_diagMap_pow {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (m : ℕ) : (diagMap p b d) ^ m = diagMap p b (d ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, diagMap_one]
  | succ m ih => rw [pow_succ, ih, diagMap_mul, pow_succ]

private theorem tfmo_diagMap_pow_eq_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (d : Fin n → (ZMod p)ˣ) (m : ℕ) (hd : ∀ k, (d k) ^ m = 1) :
    (diagMap p b d) ^ m = 1 := by
  rw [tfmo_diagMap_pow]
  have h : d ^ m = 1 := by funext k; exact hd k
  rw [h, diagMap_one]

private theorem tfmo_sign_mul_sign_pow_two {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (k l : Fin n) :
    (diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p b (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1)) ^ 2 = 1 := by
  rw [diagMap_mul]
  apply tfmo_diagMap_pow_eq_one
  intro m
  rw [Pi.mul_apply, mul_pow]
  rw [show (if m = k then (-1 : (ZMod p)ˣ) else 1) ^ 2 = 1 by
    by_cases h : m = k <;> simp [h]]
  rw [show (if m = l then (-1 : (ZMod p)ˣ) else 1) ^ 2 = 1 by
    by_cases h : m = l <;> simp [h]]
  rw [mul_one]

private theorem tfmo_sign_twist_pow_two_of_notmem {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a : (ZMod p)ˣ) :
    (diagMap p b (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j))) ^ 2 = 1 := by
  let s : V ≃ₗ[ZMod p] V := diagMap p b (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1)
  let t : V ≃ₗ[ZMod p] V := diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)
  have hgi : (s * t) (b i) = (a⁻¹ : ZMod p) • b j := by
    rw [LinearEquiv.mul_apply,
      show t (b i) = (a⁻¹ : ZMod p) • b j from tfmo_twist_apply_left b hij a,
      map_smul, show s (b j) = b j from tfmo_sign_apply_of_ne b (Ne.symm hkj)]
  have hgj : (s * t) (b j) = (a : ZMod p) • b i := by
    rw [LinearEquiv.mul_apply,
      show t (b j) = (a : ZMod p) • b i from tfmo_twist_apply_right b hij a,
      map_smul, show s (b i) = b i from tfmo_sign_apply_of_ne b (Ne.symm hki)]
  have hgk : (s * t) (b k) = -b k := by
    rw [LinearEquiv.mul_apply, show t (b k) = b k from tfmo_twist_apply_of_ne b hki hkj a,
      show s (b k) = -b k from tfmo_sign_apply_self b k]
  have hgfix : ∀ l, l ≠ i → l ≠ j → l ≠ k → (s * t) (b l) = b l := by
    intro l hli hlj hlk
    rw [LinearEquiv.mul_apply, show t (b l) = b l from tfmo_twist_apply_of_ne b hli hlj a,
      show s (b l) = b l from tfmo_sign_apply_of_ne b hlk]
  change (s * t) ^ 2 = 1
  rw [pow_two]
  refine b.ext' fun l => ?_
  rw [LinearEquiv.mul_apply]
  change (s * t) ((s * t) (b l)) = b l
  by_cases hli : l = i
  · rw [hli, hgi, map_smul, hgj, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_smul]
  · by_cases hlj : l = j
    · rw [hlj, hgj, map_smul, hgi, smul_smul, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, one_smul]
    · by_cases hlk : l = k
      · rw [hlk, hgk, map_neg, hgk, neg_neg]
      · simp [hgfix l hli hlj hlk]

private theorem tfmo_sign_twist_pow_four_of_mem {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i j : Fin n} (hij : i ≠ j) (a : (ZMod p)ˣ) :
    (diagMap p b (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j))) ^ 4 = 1 := by
  let s : V ≃ₗ[ZMod p] V := diagMap p b (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1)
  let t : V ≃ₗ[ZMod p] V := diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)
  let g : V ≃ₗ[ZMod p] V := s * t
  have hpi : g (b i) = (a⁻¹ : ZMod p) • b j := by
    change (s * t) (b i) = _
    rw [LinearEquiv.mul_apply,
      show t (b i) = (a⁻¹ : ZMod p) • b j from tfmo_twist_apply_left b hij a,
      map_smul, show s (b j) = b j from tfmo_sign_apply_of_ne b (Ne.symm hij)]
  have hpj : g (b j) = -((a : ZMod p) • b i) := by
    change (s * t) (b j) = _
    rw [LinearEquiv.mul_apply,
      show t (b j) = (a : ZMod p) • b i from tfmo_twist_apply_right b hij a,
      map_smul, show s (b i) = -b i from tfmo_sign_apply_self b i, smul_neg]
  have hpfix : ∀ l, l ≠ i → l ≠ j → g (b l) = b l := by
    intro l hli hlj
    change (s * t) (b l) = _
    rw [LinearEquiv.mul_apply, show t (b l) = b l from tfmo_twist_apply_of_ne b hli hlj a,
      show s (b l) = b l from tfmo_sign_apply_of_ne b hli]
  have hqi : (g ^ 2) (b i) = -b i := by
    rw [pow_two, LinearEquiv.mul_apply, hpi, map_smul, hpj, smul_neg, smul_smul,
      ← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hqj : (g ^ 2) (b j) = -b j := by
    rw [pow_two, LinearEquiv.mul_apply, hpj, map_neg, map_smul, hpi, smul_smul,
      ← Units.val_inv_eq_inv_val, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hqfix : ∀ l, l ≠ i → l ≠ j → (g ^ 2) (b l) = b l := by
    intro l hli hlj
    rw [pow_two, LinearEquiv.mul_apply, hpfix l hli hlj, hpfix l hli hlj]
  have hsquare : (g ^ 2) ^ 2 = 1 := by
    rw [pow_two]
    refine b.ext' fun l => ?_
    rw [LinearEquiv.mul_apply]
    change (g ^ 2) ((g ^ 2) (b l)) = b l
    by_cases hli : l = i
    · rw [hli, hqi, map_neg, hqi, neg_neg]
    · by_cases hlj : l = j
      · rw [hlj, hqj, map_neg, hqj, neg_neg]
      · simp [hqfix l hli hlj]
  change g ^ 4 = 1
  rw [show g ^ 4 = (g ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]]
  exact hsquare

private theorem tfmo_orderOf_sign_mul_twist_le_four {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (k : Fin n) {i j : Fin n} (hij : i ≠ j) (a : (ZMod p)ˣ) :
    orderOf (diagMap p b (fun l => if l = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j))) ≤ 4 := by
  by_cases hki : k = i
  · subst hki
    exact orderOf_le_of_pow_eq_one (by norm_num) (tfmo_sign_twist_pow_four_of_mem b hij a)
  · by_cases hkj : k = j
    · subst hkj
      rw [twist_swap_symm b (Ne.symm hij) a]
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (tfmo_sign_twist_pow_four_of_mem b (Ne.symm hij) a⁻¹)
    · exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
        (tfmo_sign_twist_pow_two_of_notmem b hij hki hkj a)) (by norm_num)

theorem orderOf_mul_le_four_or_dvd_of_mem_g2mmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {x y : V ≃ₗ[ZMod p] V} (hx : x ∈ g2mmn p b i₀ i₁ ζ) (hy : y ∈ g2mmn p b i₀ i₁ ζ)
    (hxr : IsRefl p x) (hyr : IsRefl p y) :
    orderOf (x * y) ≤ 4 ∨ orderOf (x * y) ∣ Nat.lcm 2 (orderOf ζ) := by
  rcases tfmo_exists_sign_or_twist_of_isRefl_mem_g2mmn hp b hi ζ hx hxr with
    ⟨k, rfl⟩ | ⟨i, j, hij, a, ha, rfl⟩
  · rcases tfmo_exists_sign_or_twist_of_isRefl_mem_g2mmn hp b hi ζ hy hyr with
      ⟨l, rfl⟩ | ⟨k', l', hkl, c, hc, rfl⟩
    · exact Or.inl (le_trans (orderOf_le_of_pow_eq_one (by norm_num)
        (tfmo_sign_mul_sign_pow_two b k l)) (by norm_num))
    · exact Or.inl (tfmo_orderOf_sign_mul_twist_le_four b k hkl c)
  · rcases tfmo_exists_sign_or_twist_of_isRefl_mem_g2mmn hp b hi ζ hy hyr with
      ⟨l, rfl⟩ | ⟨k, l, hkl, c, hc, rfl⟩
    · let s : V ≃ₗ[ZMod p] V := diagMap p b (fun m => if m = l then (-1 : (ZMod p)ˣ) else 1)
      let t : V ≃ₗ[ZMod p] V := diagMap p b (pairUnit p i j a) * permMap p b (Equiv.swap i j)
      have hconj : SemiconjBy s (t * s) (s * t) := by
        change s * (t * s) = (s * t) * s
        group
      change orderOf (t * s) ≤ 4 ∨ orderOf (t * s) ∣ Nat.lcm 2 (orderOf ζ)
      rw [SemiconjBy.orderOf_eq s hconj]
      exact Or.inl (tfmo_orderOf_sign_mul_twist_le_four b l hij a)
    · rcases orderOf_twist_mul_twist b hij hkl a c with h | h | h
      · exact Or.inl (le_trans h (by norm_num))
      · refine Or.inr (by
          rw [h]
          exact orderOf_dvd_of_pow_eq_one
            (tfmo_pow_lcm_eq_one_of_mem_closure (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hc))))
      · refine Or.inr (by
          rw [h]
          exact orderOf_dvd_of_pow_eq_one
            (tfmo_pow_lcm_eq_one_of_mem_closure (Subgroup.mul_mem _ ha hc)))

theorem exists_pair_orderOf_eq_of_gmmn (_hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    ∃ x ∈ gmmn p b i₀ i₁ ζ, ∃ y ∈ gmmn p b i₀ i₁ ζ, IsRefl p x ∧ IsRefl p y ∧
      orderOf (x * y) = orderOf ζ := by
  refine ⟨permMap p b (Equiv.swap i₀ i₁),
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _)),
    diagMap p b (pairUnit p i₀ i₁ ζ) * permMap p b (Equiv.swap i₀ i₁),
    Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self _))),
    isRefl_permMap_swap b hi, isRefl_diagMap_mul_permMap_swap b hi ζ, ?_⟩
  have htwist : permMap p b (Equiv.swap i₀ i₁) *
      (diagMap p b (pairUnit p i₀ i₁ ζ) * permMap p b (Equiv.swap i₀ i₁)) =
      diagMap p b (pairUnit p i₀ i₁ ζ⁻¹) := by
    have h := twist_mul_twist_eq (p := p) b hi (1 : (ZMod p)ˣ) ζ
    rwa [pairUnit_one, diagMap_one, one_mul, one_mul] at h
  rw [htwist, orderOf_diagMap_pairUnit b hi ζ⁻¹, orderOf_inv]

theorem exists_pair_orderOf_eq_lcm_of_g2mmn (hp : p ≠ 2) {n : ℕ}
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    ∃ x ∈ g2mmn p b i₀ i₁ ζ, ∃ y ∈ g2mmn p b i₀ i₁ ζ, IsRefl p x ∧ IsRefl p y ∧
      orderOf (x * y) = Nat.lcm 2 (orderOf ζ) := by
  have hneg : orderOf (-1 : (ZMod p)ˣ) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; simp
    · intro h
      have h2 : (2 : ZMod p) = 0 := by
        have h1 : (-1 : ZMod p) = 1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
        calc (2 : ZMod p) = 1 + 1 := by ring
          _ = -1 + 1 := congrArg (fun x : ZMod p => x + 1) h1.symm
          _ = 0 := by ring
      exact ZMod.prime_ne_zero p 2 hp h2
  have hηexists : ∃ η ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ),
      orderOf η = Nat.lcm 2 (orderOf ζ) := by
    by_cases hd : 2 ∣ orderOf ζ
    · refine ⟨ζ, Subgroup.subset_closure (Or.inl rfl), ?_⟩
      exact (Nat.dvd_antisymm (Nat.lcm_dvd hd dvd_rfl) (Nat.dvd_lcm_right 2 _)).symm
    · refine ⟨-ζ, ?_, ?_⟩
      · rw [show (-ζ : (ZMod p)ˣ) = (-1) * ζ by rw [neg_mul, one_mul]]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
          (Subgroup.subset_closure (Or.inl rfl))
      · have hcop : Nat.Coprime 2 (orderOf ζ) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd
        have hcop' : (orderOf (-1 : (ZMod p)ˣ)).Coprime (orderOf ζ) := by
          rw [hneg]; exact hcop
        have hηeq : (-ζ : (ZMod p)ˣ) = (-1) * ζ := by rw [neg_mul, one_mul]
        rw [hηeq,
          (Commute.all (-1 : (ZMod p)ˣ) ζ).orderOf_mul_eq_mul_orderOf_of_coprime hcop', hneg,
          Nat.Coprime.lcm_eq_mul hcop]
  obtain ⟨η, hηmem, hηord⟩ := hηexists
  refine ⟨permMap p b (Equiv.swap i₀ i₁),
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _)),
    diagMap p b (pairUnit p i₀ i₁ η) * permMap p b (Equiv.swap i₀ i₁),
    Subgroup.mul_mem _ (diagMap_pairUnit_mem_g2mmn b hi hi hηmem)
      (Subgroup.subset_closure (Or.inl (Set.mem_range_self _))),
    isRefl_permMap_swap b hi, isRefl_diagMap_mul_permMap_swap b hi η, ?_⟩
  have htwist : permMap p b (Equiv.swap i₀ i₁) *
      (diagMap p b (pairUnit p i₀ i₁ η) * permMap p b (Equiv.swap i₀ i₁)) =
      diagMap p b (pairUnit p i₀ i₁ η⁻¹) := by
    have h := twist_mul_twist_eq (p := p) b hi (1 : (ZMod p)ˣ) η
    rwa [pairUnit_one, diagMap_one, one_mul, one_mul] at h
  rw [htwist, orderOf_diagMap_pairUnit b hi η⁻¹, orderOf_inv, hηord]

theorem gmmn_neg_one_le_g2mmn {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) : gmmn p b i₀ i₁ (-1) ≤ g2mmn p b i₀ i₁ ζ := by
  rw [gmmn, Subgroup.closure_le]
  intro x hx
  rcases hx with ⟨σ, rfl⟩ | hx
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [tfmo_pairUnit_neg_one hi, ← diagMap_mul]
    exact Subgroup.mul_mem _ (signChange_mem_g2mmn b i₀ i₁ ζ i₀)
      (signChange_mem_g2mmn b i₀ i₁ ζ i₁)

private def tfmo_signClosure {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure (Set.range (permMap p b) ∪ Set.range (fun k : Fin n =>
    diagMap p b (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1)))

private theorem tfmo_g2mmn_le_signClosure {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) :
    g2mmn p b i₀ i₁ ζ ≤ tfmo_signClosure b := by
  have hcases : ζ = 1 ∨ ζ = -1 := by
    have hζ' : (ζ : ZMod p) * (ζ : ZMod p) = 1 := by
      rw [← Units.val_mul, hζ, Units.val_one]
    rcases mul_self_eq_one_iff.mp hζ' with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  rw [g2mmn, tfmo_signClosure, Subgroup.closure_le]
  intro x hx
  rcases hx with ⟨σ, rfl⟩ | hx
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (Or.inr (Set.mem_range_self i₀))
    · rcases hcases with h1 | h1
      · rw [h1, pairUnit_one, diagMap_one]; exact Subgroup.one_mem _
      · rw [h1, tfmo_pairUnit_neg_one hi, ← diagMap_mul]
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (Or.inr (Set.mem_range_self i₀)))
          (Subgroup.subset_closure (Or.inr (Set.mem_range_self i₁)))

private theorem tfmo_signClosure_le_g2mmn {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    tfmo_signClosure b ≤ g2mmn p b i₀ i₁ ζ := by
  rw [tfmo_signClosure, Subgroup.closure_le]
  intro x hx
  rcases hx with ⟨σ, rfl⟩ | ⟨k, rfl⟩
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  · exact signChange_mem_g2mmn b i₀ i₁ ζ k

theorem g2mmn_eq_g2mmn_of_mul_self_eq_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i₀ i₁ j₀ j₁ : Fin n} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) :
    g2mmn p b i₀ i₁ ζ = g2mmn p b j₀ j₁ 1 := by
  have h1 : g2mmn p b i₀ i₁ ζ ≤ tfmo_signClosure b := tfmo_g2mmn_le_signClosure b hi hζ
  have h2 : tfmo_signClosure b ≤ g2mmn p b i₀ i₁ ζ := tfmo_signClosure_le_g2mmn b i₀ i₁ ζ
  have h3 : g2mmn p b j₀ j₁ 1 ≤ tfmo_signClosure b :=
    tfmo_g2mmn_le_signClosure b hj (one_mul (1 : (ZMod p)ˣ))
  have h4 : tfmo_signClosure b ≤ g2mmn p b j₀ j₁ 1 := tfmo_signClosure_le_g2mmn b j₀ j₁ 1
  exact le_antisymm (h1.trans h4) (h3.trans h2)

private theorem tfmo_exists_ne_pair {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  by_contra h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ ({i, j} : Finset (Fin n)) := by
    intro k _
    by_contra hk
    exact h ⟨k, fun hki => hk (Finset.mem_insert.mpr (Or.inl hki)),
      fun hkj => hk (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hkj)))⟩
  have hcard : n ≤ ({i, j} : Finset (Fin n)).card := by
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_univ, Fintype.card_fin] at hh
  have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
    calc ({i, j} : Finset (Fin n)).card
        = (insert i ({j} : Finset (Fin n))).card := rfl
      _ ≤ (({j} : Finset (Fin n)).card + 1) := Finset.card_insert_le i _
      _ = 2 := by simp
  omega

theorem bilin_eq_zero_of_gmmn_le {n : ℕ} (hn : 3 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    {B : LinearMap.BilinForm (ZMod p) V}
    (hB : ∀ g ∈ gmmn p b i₀ i₁ ζ, ∀ u v, B (g u) (g v) = B u v) : B = 0 := by
  have hζ1 : ζ ≠ 1 := fun h1 => hζ (by rw [h1, mul_one])
  have hζ2 : (ζ : ZMod p) * (ζ : ZMod p) ≠ 1 := by
    intro h
    exact hζ (Units.ext (by simpa [Units.val_mul] using h))
  have hζ1' : (ζ : ZMod p) ≠ 1 := fun h => hζ1 (Units.ext h)
  refine LinearMap.BilinForm.ext_basis b fun x y => ?_
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨k, hkx, -⟩ := tfmo_exists_ne_pair hn x x
    have hg : diagMap p b (pairUnit p x k ζ) ∈ gmmn p b i₀ i₁ ζ :=
      diagMap_pairUnit_mem_gmmn (i₀ := i₀) (i₁ := i₁) (ζ := ζ) (k := x) (k₀ := k)
        (c := ζ) b hi (Ne.symm hkx) (Subgroup.mem_zpowers ζ)
    have hgx : (diagMap p b (pairUnit p x k ζ)) (b x) = (ζ : ZMod p) • b x := by
      rw [diagMap_apply_basis, tfmo_pairUnit_self (Ne.symm hkx) ζ]
    have h := hB (diagMap p b (pairUnit p x k ζ)) hg (b x) (b x)
    rw [hgx, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, ← mul_assoc] at h
    have h0 : (1 - (ζ : ZMod p) * (ζ : ZMod p)) * B (b x) (b x) = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hζ2))
  · obtain ⟨k, hkx, hky⟩ := tfmo_exists_ne_pair hn x y
    have hg : diagMap p b (pairUnit p x k ζ) ∈ gmmn p b i₀ i₁ ζ :=
      diagMap_pairUnit_mem_gmmn (i₀ := i₀) (i₁ := i₁) (ζ := ζ) (k := x) (k₀ := k)
        (c := ζ) b hi (Ne.symm hkx) (Subgroup.mem_zpowers ζ)
    have hgx : (diagMap p b (pairUnit p x k ζ)) (b x) = (ζ : ZMod p) • b x := by
      rw [diagMap_apply_basis, tfmo_pairUnit_self (Ne.symm hkx) ζ]
    have hgy : (diagMap p b (pairUnit p x k ζ)) (b y) = b y := by
      rw [diagMap_apply_basis, tfmo_pairUnit_ne (Ne.symm hxy) (Ne.symm hky) ζ,
        Units.val_one, one_smul]
    have h := hB (diagMap p b (pairUnit p x k ζ)) hg (b x) (b y)
    rw [hgx, hgy, LinearMap.BilinForm.smul_left] at h
    have h0 : (1 - (ζ : ZMod p)) * B (b x) (b y) = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hζ1'))

theorem two_mul_finrank_le_of_bilin_eq_zero [Module.Finite (ZMod p) V]
    {B : LinearMap.BilinForm (ZMod p) V} (hB : B.Nondegenerate) (S : Submodule (ZMod p) V)
    (hS : ∀ u ∈ S, ∀ v ∈ S, B u v = 0) :
    2 * Module.finrank (ZMod p) S ≤ Module.finrank (ZMod p) V := by
  let φ : S →ₗ[ZMod p] Module.Dual (ZMod p) V :=
    (B.toDual hB).toLinearMap.comp S.subtype
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h' : B.toDual hB (u : V) = B.toDual hB (v : V) := huv
    exact Subtype.ext ((B.toDual hB).injective h')
  have hrange : LinearMap.range φ ≤ S.dualAnnihilator := by
    rintro f ⟨u, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    simpa [LinearMap.BilinForm.toDual_def] using hS u u.2 v hv
  have hle : Module.finrank (ZMod p) S ≤ Module.finrank (ZMod p) S.dualAnnihilator := by
    rw [← LinearMap.finrank_range_of_inj hφinj]
    exact Submodule.finrank_mono hrange
  have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  omega

theorem false_of_gmmn_le_of_isIsom {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] {Y : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ} (hn : 3 ≤ n)
    (g : Module.Basis (Fin n) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin n} (hj : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hY : gmmn p g j₀ j₁ ζ ≤ movedGroup Y) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hQY : ∀ y ∈ Y, IsIsom p Q y)
    (hdim : Module.finrank (ZMod p) U < 2 * n) : False := by
  let VY := HardMathSupport.Kantor79.commutatorSpace Y
  let B : LinearMap.BilinForm (ZMod p) VY :=
    LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) VY
  have hpolar : ∀ y ∈ Y, ∀ u v : U, QuadraticMap.polarBilin Q (y u) (y v) =
      QuadraticMap.polarBilin Q u v := by
    intro y hy u v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQY y hy, hQY y hy, hQY y hy]
  have hBinv : ∀ h ∈ gmmn p g j₀ j₁ ζ, ∀ u v : VY, B (h u) (h v) = B u v := by
    intro h hh u v
    have hhY : h ∈ movedGroup Y := hY hh
    obtain ⟨y, rfl⟩ := hhY
    simp only [B, LinearMap.BilinForm.restrict_apply, restrictHom_apply]
    exact hpolar y.1 y.2 (u : U) (v : U)
  have hB0 : B = 0 := bilin_eq_zero_of_gmmn_le hn g hj hζ hBinv
  have hS : ∀ u ∈ VY, ∀ v ∈ VY, QuadraticMap.polarBilin Q u v = 0 := by
    intro u hu v hv
    have h := congrArg (fun B' : LinearMap.BilinForm (ZMod p) VY => B' ⟨u, hu⟩ ⟨v, hv⟩) hB0
    simpa [B, LinearMap.BilinForm.restrict_apply] using h
  have hle := two_mul_finrank_le_of_bilin_eq_zero (p := p) hQ VY hS
  have hfin : Module.finrank (ZMod p) VY = n := by
    rw [Module.finrank_eq_card_basis g, Fintype.card_fin]
  rw [hfin] at hle
  omega

theorem card_dvd_two_pow_mul_factorial_of_three (hp3 : p = 3) {n : ℕ} (hn : 2 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : J = gmmn p b i₀ i₁ ζ ∨ J = g2mmn p b i₀ i₁ ζ) :
    Nat.card J ∣ 2 ^ n * n.factorial := by
  subst hp3
  have hζdvd : orderOf ζ ∣ 2 := by
    have hcard : Fintype.card (ZMod 3)ˣ = 2 := by
      rw [ZMod.card_units_eq_totient]; decide
    rw [← hcard]
    exact orderOf_dvd_card
  have hn1 : 1 ≤ n := by omega
  rcases hJ with rfl | rfl
  · rw [card_gmmn hn b hi ζ]
    exact dvd_trans (Nat.mul_dvd_mul_right (pow_dvd_pow_of_dvd hζdvd (n - 1)) _)
      (Nat.mul_dvd_mul_right (pow_dvd_pow 2 (Nat.sub_le n 1)) _)
  · rw [card_g2mmn (by decide : (3 : ℕ) ≠ 2) hn b hi ζ]
    have hlcm : Nat.lcm 2 (orderOf ζ) = 2 :=
      Nat.dvd_antisymm (Nat.lcm_dvd dvd_rfl hζdvd) (Nat.dvd_lcm_left 2 (orderOf ζ))
    rw [hlcm]
    have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn1]
    simp [hpow]

theorem two_mul_add_one_le_of_three_pow_dvd {n k : ℕ} (hn : 1 ≤ n)
    (h : 3 ^ k ∣ 2 ^ n * n.factorial) : 2 * k + 1 ≤ n := by
  have hcop : Nat.Coprime (3 ^ k) (2 ^ n) :=
    Nat.Coprime.pow k n (by decide : Nat.Coprime 3 2)
  have hnf : 3 ^ k ∣ n.factorial := hcop.dvd_of_dvd_mul_left h
  have hk : k ≤ padicValNat 3 n.factorial :=
    (padicValNat_dvd_iff_le (p := 3) (n := k) (Nat.factorial_ne_zero n)).mp hnf
  have hleg : (3 - 1) * padicValNat 3 n.factorial < n :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := 3) (by omega)
  omega

private theorem tfmo_basisDiagForm_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    basisDiagForm b 1 = basisSumSq b := by
  ext v
  rw [basisSumSq_apply]
  simp only [basisDiagForm, QuadraticMap.comp_apply, QuadraticMap.weightedSumSquares_apply,
    Pi.one_apply, one_smul]
  apply Fintype.sum_congr
  intro m
  change b.equivFun v m * b.equivFun v m = b.repr v m * b.repr v m
  have h : b.equivFun v m = b.repr v m := congrFun (Module.Basis.equivFun_apply b v) m
  rw [h]

private theorem tfmo_polar_basisSumSq {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (u v : V) :
    QuadraticMap.polar (basisSumSq b) u v = 2 * ∑ i, (b.repr u i) * (b.repr v i) := by
  rw [QuadraticMap.polar, basisSumSq_apply, basisSumSq_apply, basisSumSq_apply]
  have hrepr : ∀ i, b.repr (u + v) i = b.repr u i + b.repr v i := by
    intro i; rw [map_add, Finsupp.add_apply]
  simp only [hrepr]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem tfmo_polar_basisDiagForm_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (u v : V) :
    QuadraticMap.polar (basisDiagForm b 1) u v = 2 * ∑ i, (b.repr u i) * (b.repr v i) := by
  rw [tfmo_basisDiagForm_one]
  exact tfmo_polar_basisSumSq b u v

private theorem tfmo_exists_perm_dot_eq_zero_three :
    ∀ x : Fin 4 → ZMod 3, ∑ i, x i ^ 2 ≠ 0 → (∃ i, x i = 0) →
      ∃ σ : Equiv.Perm (Fin 4), ∑ i, x i * x (σ i) = 0 := by
  decide +kernel

private theorem tfmo_sum_neg_pair_eq_zero_three :
    ∀ x : Fin 4 → ZMod 3, (∀ i, x i ≠ 0) → ∀ i₀ i₁ : Fin 4, i₀ ≠ i₁ →
      ∑ i, x i * (if i = i₀ ∨ i = i₁ then -x i else x i) = 0 := by
  decide +kernel

theorem exists_mem_gmmn_polar_eq_zero (hp3 : p = 3) (b : Module.Basis (Fin 4) (ZMod p) V)
    {i₀ i₁ : Fin 4} (hi : i₀ ≠ i₁) {w : V} (hw : basisDiagForm b 1 w ≠ 0) :
    ∃ g ∈ gmmn p b i₀ i₁ (-1), QuadraticMap.polar (basisDiagForm b 1) w (g w) = 0 := by
  subst hp3
  let x : Fin 4 → ZMod 3 := fun i => b.repr w i
  have hxsum : ∑ i, x i ^ 2 ≠ 0 := by
    intro h0
    apply hw
    rw [tfmo_basisDiagForm_one, basisSumSq_apply]
    simpa [x, pow_two] using h0
  by_cases hzero : ∃ i, x i = 0
  · obtain ⟨i, hi0⟩ := hzero
    obtain ⟨σ, hσ⟩ := tfmo_exists_perm_dot_eq_zero_three x hxsum ⟨i, hi0⟩
    refine ⟨permMap 3 b σ⁻¹, Subgroup.subset_closure (Or.inl (Set.mem_range_self _)), ?_⟩
    have hcoord : ∀ m, b.repr ((permMap 3 b σ⁻¹) w) m = x (σ m) := by
      intro m
      rw [repr_permMap]
      change b.repr w (σ m) = x (σ m)
      rfl
    rw [tfmo_polar_basisDiagForm_one,
      Finset.sum_congr rfl (fun m _ => by rw [hcoord m]), hσ, mul_zero]
  · have hall : ∀ i, x i ≠ 0 := fun i hi0 => hzero ⟨i, hi0⟩
    have hfun : pairUnit 3 i₀ i₁ (-1) =
        (fun m => if m = i₀ ∨ m = i₁ then (-1 : (ZMod 3)ˣ) else 1) := by
      funext m
      by_cases hm₀ : m = i₀
      · subst hm₀
        rw [tfmo_pairUnit_self hi (-1), if_pos (Or.inl rfl)]
      · by_cases hm₁ : m = i₁
        · subst hm₁
          rw [tfmo_pairUnit_other hi (-1), if_pos (Or.inr rfl), inv_neg, inv_one]
        · rw [tfmo_pairUnit_ne hm₀ hm₁ (-1), if_neg (fun h => h.elim hm₀ hm₁)]
    refine ⟨diagMap 3 b (pairUnit 3 i₀ i₁ (-1)),
      Subgroup.subset_closure (Or.inr rfl), ?_⟩
    have hcoord : ∀ m, b.repr ((diagMap 3 b (pairUnit 3 i₀ i₁ (-1))) w) m =
        (if m = i₀ ∨ m = i₁ then -x m else x m) := by
      intro m
      rw [repr_diagMap, hfun]
      dsimp only
      by_cases hm : m = i₀ ∨ m = i₁
      · rw [if_pos hm, if_pos hm]; simp [x]
      · rw [if_neg hm, if_neg hm]; simp [x]
    rw [tfmo_polar_basisDiagForm_one,
      Finset.sum_congr rfl (fun m _ => by rw [hcoord m]),
      tfmo_sum_neg_pair_eq_zero_three x hall i₀ i₁ hi, mul_zero]

end CFSG.StandardType.ZS.TableFacts

end
