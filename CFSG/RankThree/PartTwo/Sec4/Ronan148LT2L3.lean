module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SNoCQ
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.N143.HeisenbergThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.Open (StatedSL StatedSU)
open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.DFT
open scoped commutatorElement

section Comm

variable {G : Type} [Group G]

theorem commutatorElement_mul_of_central {x a b : G} (ha : ⁅a, x⁆ ∈ Subgroup.center G)
    (hb : ⁅b, x⁆ ∈ Subgroup.center G) : ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
  have hzb := Subgroup.mem_center_iff.mp hb
  have hza := Subgroup.mem_center_iff.mp ha
  calc ⁅a * b, x⁆ = a * (b * x * b⁻¹ * x⁻¹) * x * a⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * ⁅b, x⁆ * x * a⁻¹ * x⁻¹ := by rw [commutatorElement_def]
    _ = ⁅b, x⁆ * (a * x * a⁻¹ * x⁻¹) := by rw [hzb a]; group
    _ = ⁅b, x⁆ * ⁅a, x⁆ := by rw [commutatorElement_def a x]
    _ = ⁅a, x⁆ * ⁅b, x⁆ := hza ⁅b, x⁆

@[expose] def commHom (M : Subgroup G) (x : G) (hM : ∀ h ∈ M, ⁅h, x⁆ ∈ Subgroup.center G) :
    M →* Subgroup.center G where
  toFun h := ⟨⁅(h : G), x⁆, hM h h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (commutatorElement_mul_of_central (hM a a.2) (hM b b.2))

theorem commutator_le_centralizer (M : Subgroup G) (x : G)
    (hM : ∀ h ∈ M, ⁅h, x⁆ ∈ Subgroup.center G) : ⁅M, M⁆ ≤ Subgroup.centralizer {x} := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : commHom M x hM ⁅(⟨a, ha⟩ : M), (⟨b, hb⟩ : M)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hM b hb) ⁅a, x⁆
  have h2 : ⁅⁅a, b⁆, x⁆ = 1 := congrArg Subtype.val h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2)

theorem commutator_le_map_ker {N : Subgroup G} {A : Type} [CommGroup A] (f : N →* A)
    {L : Subgroup G} (hL : L ≤ N) : ⁅L, L⁆ ≤ f.ker.map N.subtype := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨⁅(⟨a, hL ha⟩ : N), (⟨b, hL hb⟩ : N)⁆, ?_, rfl⟩
  change f ⁅(⟨a, hL ha⟩ : N), (⟨b, hL hb⟩ : N)⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end Comm

section PGL

variable {n : Type} [Fintype n] [DecidableEq n] {F : Type} [Field F]

theorem perfect_le_map_centralizer {M : Subgroup (ProjGenLinGroup n F)} (hM : ⁅M, M⁆ = M)
    {x : GL n F} (hMx : M ≤ Subgroup.centralizer {ProjGenLinGroup.mk x}) :
    ⁅M.comap ProjGenLinGroup.mk, M.comap ProjGenLinGroup.mk⁆ ≤ Subgroup.centralizer {x} ∧
      (⁅M.comap ProjGenLinGroup.mk, M.comap ProjGenLinGroup.mk⁆).map ProjGenLinGroup.mk = M := by
  refine ⟨commutator_le_centralizer _ x fun h hh => ?_, ?_⟩
  · rw [← ProjGenLinGroup.mk_eq_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hMx hh)
  · rw [Subgroup.map_commutator,
      Subgroup.map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective, hM]

theorem commutator_le_ker_det (L : Subgroup (GL n F)) :
    ⁅L, L⁆ ≤ (GeneralLinearGroup.det : GL n F →* Fˣ).ker := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end PGL

section GL3

variable {F : Type} [Field F]

theorem circulant_of_commute {h : Matrix (Fin 3) (Fin 3) F}
    (hc : h * permMat3 = permMat3 * h) :
    h = !![h 0 0, h 0 1, h 0 2; h 0 2, h 0 0, h 0 1; h 0 1, h 0 2, h 0 0] := by
  have e : ∀ i j, (h * (permMat3 : Matrix (Fin 3) (Fin 3) F)) i j =
      ((permMat3 : Matrix (Fin 3) (Fin 3) F) * h) i j := fun i j => by rw [hc]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [permMat3, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem commute_of_commute_permMat3 {h h' : Matrix (Fin 3) (Fin 3) F}
    (hc : h * permMat3 = permMat3 * h) (hc' : h' * permMat3 = permMat3 * h') :
    h * h' = h' * h := by
  rw [circulant_of_commute hc, circulant_of_commute hc']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem commute_of_commute_conj_permGL3 {g h h' : GL (Fin 3) F}
    (hc : h * (g * permGL3 * g⁻¹) = (g * permGL3 * g⁻¹) * h)
    (hc' : h' * (g * permGL3 * g⁻¹) = (g * permGL3 * g⁻¹) * h') : h * h' = h' * h := by
  have key : ∀ k : GL (Fin 3) F, k * (g * permGL3 * g⁻¹) = (g * permGL3 * g⁻¹) * k →
      (g⁻¹ * k * g) * permGL3 = permGL3 * (g⁻¹ * k * g) := by
    intro k hk
    calc (g⁻¹ * k * g) * permGL3 = g⁻¹ * (k * (g * permGL3 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * permGL3 * g⁻¹) * k) * g := by rw [hk]
      _ = permGL3 * (g⁻¹ * k * g) := by group
  have h1 := key h hc
  have h2 := key h' hc'
  have coe : ∀ k : GL (Fin 3) F, (g⁻¹ * k * g) * permGL3 = permGL3 * (g⁻¹ * k * g) →
      ((g⁻¹ * k * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * permMat3 =
        permMat3 * ((g⁻¹ * k * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro k hk
    have := congrArg (fun m : GL (Fin 3) F => (m : Matrix (Fin 3) (Fin 3) F)) hk
    simp only [Units.val_mul (g⁻¹ * k * g) permGL3, Units.val_mul permGL3 (g⁻¹ * k * g),
      coe_permGL3] at this
    exact this
  have h3 : (g⁻¹ * h * g) * (g⁻¹ * h' * g) = (g⁻¹ * h' * g) * (g⁻¹ * h * g) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_commute_permMat3 (coe h h1) (coe h' h2)
  calc h * h' = g * ((g⁻¹ * h * g) * (g⁻¹ * h' * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * h' * g) * (g⁻¹ * h * g)) * g⁻¹ := by rw [h3]
    _ = h' * h := by group

theorem diagGL_mul_permGL3_eq_conj (t : Fin 3 → Fˣ) (ht : t 0 * t 1 * t 2 = 1) :
    TauCeti.diagGL t * permGL3 =
      TauCeti.diagGL ![1, t 1, t 1 * t 2] * permGL3 * (TauCeti.diagGL ![1, t 1, t 1 * t 2])⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, permGL3_mul_diagGL, ← mul_assoc, ← map_mul]
  congr 2
  funext i
  fin_cases i
  · show t 0 * (t 1 * t 2) = 1
    rw [← mul_assoc, ht]
  · show t 1 * 1 = t 1
    rw [mul_one]
  · show t 2 * t 1 = t 1 * t 2
    rw [mul_comm]

theorem entry_eq_zero_of_commute {d : Fin 3 → Fˣ} {h : GL (Fin 3) F}
    (hc : h * TauCeti.diagGL d = TauCeti.diagGL d * h) {k l : Fin 3} (hkl : d l ≠ d k) :
    (h : Matrix (Fin 3) (Fin 3) F) k l = 0 := by
  have e := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) k l) hc
  simp only [Units.val_mul, TauCeti.diagGL_coe, mul_diagonal, diagonal_mul] at e
  have hne : ((d l : Fˣ) : F) - d k ≠ 0 := sub_ne_zero.mpr fun h => hkl (Units.ext h)
  have : (h : Matrix (Fin 3) (Fin 3) F) k l * (((d l : Fˣ) : F) - d k) = 0 := by
    linear_combination e
  exact (mul_eq_zero.mp this).resolve_right hne

theorem mul_apply_diag_of_row {h h' : Matrix (Fin 3) (Fin 3) F} {k : Fin 3}
    (hr : ∀ l, l ≠ k → h k l = 0) : (h * h') k k = h k k * h' k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro l _ hl
    rw [hr l hl, zero_mul]
  · simp

@[expose] noncomputable def entryHom (d : Fin 3 → Fˣ) (k : Fin 3) (hk : ∀ l, l ≠ k → d l ≠ d k) :
    Subgroup.centralizer {TauCeti.diagGL d} →* Fˣ where
  toFun h :=
    { val := (h : GL (Fin 3) F) k k
      inv := ((h : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) k k
      val_inv := by
        have hr : ∀ l, l ≠ k → ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k l = 0 :=
          fun l hl => entry_eq_zero_of_commute
            (Subgroup.mem_centralizer_singleton_iff.mp h.2) (hk l hl)
        rw [← mul_apply_diag_of_row hr, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          one_apply_eq]
      inv_val := by
        have hr : ∀ l, l ≠ k →
            ((((h : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k l = 0 :=
          fun l hl => entry_eq_zero_of_commute
            (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ h.2)) (hk l hl)
        rw [← mul_apply_diag_of_row hr, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_apply_eq] }
  map_one' := Units.ext (by simp)
  map_mul' a b := by
    apply Units.ext
    have hr : ∀ l, l ≠ k → ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k l = 0 :=
      fun l hl => entry_eq_zero_of_commute
        (Subgroup.mem_centralizer_singleton_iff.mp a.2) (hk l hl)
    change (((a : GL (Fin 3) F) * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k k = _
    rw [Units.val_mul, mul_apply_diag_of_row hr]
    rfl

theorem coe_entryHom (d : Fin 3 → Fˣ) (k : Fin 3) (hk : ∀ l, l ≠ k → d l ≠ d k)
    (h : Subgroup.centralizer {TauCeti.diagGL d}) :
    ((entryHom d k hk h : Fˣ) : F) = (h : GL (Fin 3) F) k k := rfl

end GL3

section False

variable {F : Type} [Field F]

theorem false_of_perfect_cyclic {M : Subgroup (ProjGenLinGroup (Fin 3) F)} (hM : ⁅M, M⁆ = M)
    {g : GL (Fin 3) F}
    (hMx : M ≤ Subgroup.centralizer {ProjGenLinGroup.mk (g * permGL3 * g⁻¹)})
    (hx : ProjGenLinGroup.mk (g * permGL3 * g⁻¹) ∈ M)
    (hne : ProjGenLinGroup.mk (g * permGL3 * g⁻¹) ≠ 1) : False := by
  obtain ⟨hL, hLM⟩ := perfect_le_map_centralizer hM hMx
  apply hne
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    rw [← hLM]
    rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    rw [← map_mul, ← map_mul, commute_of_commute_conj_permGL3
      (Subgroup.mem_centralizer_singleton_iff.mp (hL hl))
      (Subgroup.mem_centralizer_singleton_iff.mp (hL hl'))]
  have hbot : ⁅M, M⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a ha b hb
  rw [hM] at hbot
  rw [hbot] at hx
  exact hx

theorem false_of_perfect_diag {M : Subgroup (ProjGenLinGroup (Fin 3) F)} (hM : ⁅M, M⁆ = M)
    {d : Fin 3 → Fˣ}
    (hMx : M ≤ Subgroup.centralizer {ProjGenLinGroup.mk (TauCeti.diagGL d)})
    (hx : ProjGenLinGroup.mk (TauCeti.diagGL d) ∈ M) (hdet : d 0 * d 1 * d 2 = 1)
    (h3 : ∀ i j, d i ^ 3 = d j ^ 3) (hne : ¬ (d 0 = d 1 ∧ d 1 = d 2)) : False := by
  obtain ⟨hL, hLM⟩ := perfect_le_map_centralizer hM hMx
  set L := ⁅M.comap ProjGenLinGroup.mk, M.comap ProjGenLinGroup.mk⁆ with hLdef
  have hLL : (⁅L, L⁆).map ProjGenLinGroup.mk = M := by
    rw [Subgroup.map_commutator, hLM, hM]
  rw [← hLL] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hyx.symm
  have hdety : GeneralLinearGroup.det y = 1 := commutator_le_ker_det L hy
  rw [← hu, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdety
  have hdetd : GeneralLinearGroup.det (TauCeti.diagGL d) = d 0 * d 1 * d 2 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_three]
    simp
  rw [hdetd, hdet, one_mul] at hdety
  have key : ∀ k : Fin 3, (∀ l, l ≠ k → d l ≠ d k) → d k * u = 1 := by
    intro k hk
    have hyk := commutator_le_map_ker (entryHom d k hk) hL hy
    obtain ⟨z, hz, rfl⟩ := hyk
    have hz' : entryHom d k hk z = 1 := hz
    apply Units.ext
    have hzk := congrArg (fun v : Fˣ => (v : F)) hz'
    simp only [coe_entryHom, Units.val_one] at hzk
    rw [Units.val_mul, Units.val_one, ← hzk]
    change _ = ((Subgroup.subtype _ z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k k
    rw [← hu, Units.val_mul, TauCeti.diagGL_coe]
    simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hcube : ∀ a b : Fˣ, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b := by
    intro a b h2 h3'
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = b ^ 3 * (b ^ 2)⁻¹ := by rw [h3', h2]
      _ = b := by group
  have fin3 : ∀ P : Fin 3 → Prop, P 0 → P 1 → P 2 → ∀ l, P l := by
    intro P h0 h1 h2 l
    fin_cases l
    · exact h0
    · exact h1
    · exact h2
  have two : ∀ i j k : Fin 3, i ≠ k → d i = d j → (∀ l, l ≠ k → d l ≠ d k) →
      d i * d j * d k = 1 → False := by
    intro i j k hik hij hk hprod
    have hprod' : d i ^ 2 * d k = 1 := by rw [sq, ← hprod, ← hij]
    have hku := key k hk
    have hu' : u = (d k)⁻¹ := eq_inv_of_mul_eq_one_right hku
    have hk3 : d k ^ 3 = 1 := by
      rw [hu', inv_pow] at hdety
      exact inv_eq_one.mp hdety
    have hi2 : d i ^ 2 = d k ^ 2 := by
      have : d i ^ 2 = (d k)⁻¹ := eq_inv_of_mul_eq_one_left hprod'
      rw [this]
      calc (d k)⁻¹ = d k ^ 3 * (d k)⁻¹ := by rw [hk3, one_mul]
        _ = d k ^ 2 := by group
    exact hk i hik (hcube _ _ hi2 (h3 i k))
  by_cases h01 : d 0 = d 1
  · have h12 : d 1 ≠ d 2 := fun h => hne ⟨h01, h⟩
    exact two 0 1 2 (by decide) h01
      (fin3 (fun l => l ≠ 2 → d l ≠ d 2) (fun _ => h01 ▸ h12) (fun _ => h12)
        (fun h => absurd rfl h)) hdet
  · by_cases h02 : d 0 = d 2
    · exact two 0 2 1 (by decide) h02
        (fin3 (fun l => l ≠ 1 → d l ≠ d 1) (fun _ => h01) (fun h => absurd rfl h)
          (fun _ h => h01 (h02.trans h))) (by rw [mul_right_comm]; exact hdet)
    · by_cases h12 : d 1 = d 2
      · exact two 1 2 0 (by decide) h12
          (fin3 (fun l => l ≠ 0 → d l ≠ d 0) (fun h => absurd rfl h)
            (fun _ h => h01 h.symm) (fun _ h => h02 h.symm))
          (by rw [mul_comm, ← mul_assoc]; exact hdet)
      ·
        have k0 := key 0 (fin3 (fun l => l ≠ 0 → d l ≠ d 0) (fun h => absurd rfl h)
          (fun _ h => h01 h.symm) (fun _ h => h02 h.symm))
        have k1 := key 1 (fin3 (fun l => l ≠ 1 → d l ≠ d 1) (fun _ => h01)
          (fun h => absurd rfl h) (fun _ h => h12 h.symm))
        exact h01 (mul_right_cancel (k0.trans k1.symm))

end False

section Torus3

variable {F : Type} [Field F]

@[expose] def vec3 : Fˣ × Fˣ →* (Fin 3 → Fˣ) where
  toFun x := ![x.1, x.2, (x.1 * x.2)⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem vec3_prod (x : Fˣ × Fˣ) : vec3 x 0 * vec3 x 1 * vec3 x 2 = 1 := by
  change x.1 * x.2 * (x.1 * x.2)⁻¹ = 1
  rw [mul_inv_cancel]

variable {N : ℕ} [NeZero N]

@[expose] def rotL : ZMod N × ZMod N →+ ZMod N × ZMod N where
  toFun v := (-(v.1 + v.2), v.1)
  map_zero' := by simp
  map_add' v w := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add]
      abel
    · simp

theorem rotL_ne [Fact (1 < N)] : ∃ v : ZMod N × ZMod N, rotL v ≠ v :=
  ⟨(1, 0), fun h => one_ne_zero (congrArg Prod.snd h)⟩

variable {ζ : Fˣ} (hζ : ζ ^ N = 1)

@[expose] noncomputable def τ3 : Multiplicative (ZMod N × ZMod N) →* GL (Fin 3) F :=
  TauCeti.diagGL.comp (vec3.comp ((MonoidHom.prodMap (expHom ζ hζ) (expHom ζ hζ)).comp
    (MulEquiv.prodMultiplicative (ZMod N) (ZMod N)).toMonoidHom))

theorem τ3_apply (v : ZMod N × ZMod N) :
    τ3 hζ (.ofAdd v) = TauCeti.diagGL (vec3 (expHom ζ hζ (.ofAdd v.1), expHom ζ hζ (.ofAdd v.2))) :=
  rfl

theorem τ3_injective (hζo : orderOf ζ = N) : Function.Injective (τ3 hζ) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective y
  rw [τ3_apply, τ3_apply] at hxy
  have h := TauCeti.diagGL_injective hxy
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have e0 := Multiplicative.ofAdd.injective (expHom_injective hζ hζo h0)
  have e1 := Multiplicative.ofAdd.injective (expHom_injective hζ hζo h1)
  rw [Prod.ext e0 e1]

theorem permGL3_τ3 (v : ZMod N × ZMod N) :
    permGL3 * τ3 hζ (.ofAdd v) = τ3 hζ (.ofAdd (rotL v)) * permGL3 := by
  rw [τ3_apply, τ3_apply, permGL3_mul_diagGL]
  congr 2
  funext i
  fin_cases i
  · change (expHom ζ hζ (.ofAdd v.1) * expHom ζ hζ (.ofAdd v.2))⁻¹ =
      expHom ζ hζ (.ofAdd (-(v.1 + v.2)))
    rw [ofAdd_neg, map_inv, ofAdd_add, map_mul]
  · rfl
  · change expHom ζ hζ (.ofAdd v.2) =
      (expHom ζ hζ (.ofAdd (-(v.1 + v.2))) * expHom ζ hζ (.ofAdd v.1))⁻¹
    rw [ofAdd_neg, map_inv, ofAdd_add, map_mul]
    group

end Torus3

section Main

variable {F : Type} [Field F] [Finite F] {H : Subgroup (GL (Fin 3) F)}

theorem exists_conj_mem_of_sylow {X : Type} [Group X] [Finite X] (P₀ : Sylow 3 X) {h : X}
    (h9 : h ^ 9 = 1) : ∃ g : X, g⁻¹ * h * g ∈ (P₀ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers h) := by
    have hd : Nat.card (Subgroup.zpowers h) ∣ 3 ^ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (by norm_num [h9])
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    exact IsPGroup.of_card hm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₀ Q
  refine ⟨g, ?_⟩
  have hhQ : h ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers h)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hhQ
  convert hhQ using 1
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem NoCQAt.of_inv {S : Type} [Group S] [Finite S] {s : S} (h : NoCQAt s⁻¹) : NoCQAt s := by
  intro K hsK hKC hKq hT
  refine h K (K.inv_mem hsK) (fun k hk => ?_) hKq hT
  have := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc : Commute k s := this
  exact hc.inv_right.eq

@[expose] noncomputable def piH (H : Subgroup (GL (Fin 3) F)) : H →* projImage H :=
  ProjGenLinGroup.mk.subgroupMap H

theorem piH_surjective : Function.Surjective (piH H) := MonoidHom.subgroupMap_surjective _ _

theorem noCQAt_of_pgl {x : H}
    (hfalse : ∀ M : Subgroup (ProjGenLinGroup (Fin 3) F), ⁅M, M⁆ = M →
      M ≤ Subgroup.centralizer {ProjGenLinGroup.mk (x : GL (Fin 3) F)} →
      ProjGenLinGroup.mk (x : GL (Fin 3) F) ∈ M → False) :
    NoCQAt (piH H x) := by
  intro K hxK hKC hKq _
  haveI : Group.IsPerfect K := hKq.1
  have hKK : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
  refine hfalse (K.map (projImage H).subtype) (by rw [← Subgroup.map_commutator, hKK])
    ?_ ⟨_, hxK, rfl⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  exact congrArg Subtype.val this

theorem noCQ425_projImage_three (hH : H ≤ StatedSL 3 F) {a k : ℕ} {ζ : Fˣ}
    (hζo : orderOf ζ = 3 ^ (a + 1))
    (hT : ∀ t : Fin 3 → Fˣ, (∀ i, t i ^ (3 ^ (a + 1)) = 1) → t 0 * t 1 * t 2 = 1 →
      TauCeti.diagGL t ∈ H)
    (hw : permGL3 ∈ H) (hcard : Nat.card H = 3 ^ (2 * (a + 1) + 1) * k) (hk : ¬ 3 ∣ k) :
    NoCQ425 (projImage H) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (1 < 3 ^ (a + 1)) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  have hζ : ζ ^ (3 ^ (a + 1)) = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hmem : ∀ v, τ3 hζ v ∈ H := by
    intro v
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [τ3_apply]
    refine hT _ (fun i => ?_) (vec3_prod _)
    have hpow : ∀ c : ZMod (3 ^ (a + 1)), expHom ζ hζ (.ofAdd c) ^ (3 ^ (a + 1)) = 1 := by
      intro c
      rw [expHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    fin_cases i
    · exact hpow _
    · exact hpow _
    · change ((expHom ζ hζ (.ofAdd u.1) * expHom ζ hζ (.ofAdd u.2))⁻¹) ^ (3 ^ (a + 1)) = 1
      rw [inv_pow, mul_pow, hpow, hpow, one_mul, inv_one]
  let τ : Multiplicative (ZMod (3 ^ (a + 1)) × ZMod (3 ^ (a + 1))) →* H :=
    (τ3 hζ).codRestrict H hmem
  have hτ : Function.Injective τ := fun x y h => τ3_injective hζ hζo (congrArg Subtype.val h)
  let w : H := ⟨permGL3, hw⟩
  have hw3 : w ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact permGL3_pow_three)
  have hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rotL v)) * w := fun v =>
    Subtype.ext (permGL3_τ3 hζ v)
  have hV : Nat.card (ZMod (3 ^ (a + 1)) × ZMod (3 ^ (a + 1))) = 3 ^ (2 * (a + 1)) := by
    rw [Nat.card_prod, Nat.card_zmod]
    ring
  obtain ⟨P₀, hP₀⟩ := exists_sylow_torusExt hτ hw3 hwτ rotL_ne hV hcard hk
  have hker : ∀ z : H, piH H z = 1 → z ^ 3 = 1 := by
    intro z hz
    have h1 : ProjGenLinGroup.mk (z : GL (Fin 3) F) = 1 := congrArg Subtype.val hz
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have hdet : GeneralLinearGroup.det (z : GL (Fin 3) F) = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply, Units.val_one]
                    exact CFSG.Open.StatedAPI.det_of_mem_statedSL (hH z.2))
    rw [← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hdet, map_one]
    rfl
  refine noCQ425_of_at fun s hs3 => ?_
  obtain ⟨h, rfl⟩ := piH_surjective s
  have hs31 : piH H h ^ 3 = 1 := by
    have := pow_orderOf_eq_one (piH H h)
    rwa [hs3] at this
  have h9 : h ^ 9 = 1 := by
    have := hker (h ^ 3) (by rw [map_pow, hs31])
    rw [← pow_mul] at this
    exact this
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow P₀ h9
  rw [hP₀] at hg
  obtain ⟨v, j, hvj⟩ := hg
  refine NoCQAt.of_mulEquiv (MulAut.conj (piH H g)⁻¹) ?_
  have hconj : (MulAut.conj (piH H g)⁻¹) (piH H h) = piH H (g⁻¹ * h * g) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, inv_inv]
  rw [hconj, hvj]
  have hord : ∀ y : H, piH H y = (MulAut.conj (piH H g)⁻¹) (piH H h) →
      piH H y ^ 3 = 1 ∧ piH H y ≠ 1 := by
    intro y hy
    rw [hy, ← map_pow, hs31, map_one]
    refine ⟨rfl, fun h1 => ?_⟩
    rw [map_eq_one_iff _ (MulAut.conj _).injective] at h1
    rw [h1, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have hxy := hord (τ (.ofAdd v) * w ^ j) (by rw [hconj, hvj])
  have hwj : w ^ j = w ^ (j % 3) := pow_eq_pow_mod j hw3
  rw [hwj] at hxy ⊢
  have hx3 := hxy.1
  have hx1 := hxy.2
  set d : Fin 3 → Fˣ := vec3 (expHom ζ hζ (.ofAdd v.1),
    expHom ζ hζ (.ofAdd v.2)) with hd
  have hτv : ((τ (.ofAdd v) : H) : GL (Fin 3) F) = TauCeti.diagGL d := τ3_apply hζ v
  have hdprod : d 0 * d 1 * d 2 = 1 := vec3_prod _
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with hj | hj | hj
  ·
    rw [hj, pow_zero, mul_one] at hx3 hx1 ⊢
    refine noCQAt_of_pgl fun M hM hMx hxM => false_of_perfect_diag hM (hτv ▸ hMx) (hτv ▸ hxM)
      hdprod ?_ ?_
    ·
      have h1 : ProjGenLinGroup.mk ((τ (.ofAdd v) : H) : GL (Fin 3) F) ^ 3 = 1 :=
        congrArg Subtype.val hx3
      rw [← map_pow, hτv, ProjGenLinGroup.mk_eq_one,
        GeneralLinearGroup.center_eq_range_scalar] at h1
      obtain ⟨c, hc⟩ := h1
      have hdc : ∀ i, d i ^ 3 = c := by
        intro i
        have := congrArg (fun m : GL (Fin 3) F => (m : Matrix (Fin 3) (Fin 3) F) i i) hc
        simp only [GeneralLinearGroup.scalar, Units.val_pow_eq_pow_val, TauCeti.diagGL_coe,
          diagonal_pow] at this
        apply Units.ext
        simpa [Matrix.diagonal_apply, Matrix.scalar] using this.symm
      intro i j
      rw [hdc i, hdc j]
    ·
      rintro ⟨h01, h12⟩
      apply hx1
      apply Subtype.ext
      change ProjGenLinGroup.mk ((τ (.ofAdd v) : H) : GL (Fin 3) F) = 1
      rw [hτv, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨d 0, ?_⟩
      apply Units.ext
      rw [TauCeti.diagGL_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, h01, h12]
  ·
    rw [hj, pow_one] at hx3 hx1 ⊢
    have hconjx : ((τ (.ofAdd v) * w : H) : GL (Fin 3) F) =
        TauCeti.diagGL ![1, d 1, d 1 * d 2] * permGL3 *
          (TauCeti.diagGL ![1, d 1, d 1 * d 2])⁻¹ := by
      rw [Subgroup.coe_mul, hτv]
      exact diagGL_mul_permGL3_eq_conj d hdprod
    refine noCQAt_of_pgl fun M hM hMx hxM => false_of_perfect_cyclic hM (hconjx ▸ hMx)
      (hconjx ▸ hxM) ?_
    rw [← hconjx]
    intro h1
    exact hx1 (Subtype.ext h1)
  ·
    rw [hj] at hx3 hx1 ⊢
    refine NoCQAt.of_inv ?_
    have hinv : (τ (.ofAdd v) * w ^ 2)⁻¹ = τ (.ofAdd (rotL (-v))) * w := by
      rw [_root_.mul_inv_rev, ← hwτ, ← map_inv, ← ofAdd_neg]
      have : (w ^ 2)⁻¹ = w := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ]
        exact hw3
      rw [this]
    rw [← map_inv, hinv]
    set d' : Fin 3 → Fˣ := vec3 (expHom ζ hζ (.ofAdd (rotL (-v)).1),
      expHom ζ hζ (.ofAdd (rotL (-v)).2)) with hd'
    have hτv' : ((τ (.ofAdd (rotL (-v))) : H) : GL (Fin 3) F) = TauCeti.diagGL d' :=
      τ3_apply hζ _
    have hconjx : ((τ (.ofAdd (rotL (-v))) * w : H) : GL (Fin 3) F) =
        TauCeti.diagGL ![1, d' 1, d' 1 * d' 2] * permGL3 *
          (TauCeti.diagGL ![1, d' 1, d' 1 * d' 2])⁻¹ := by
      rw [Subgroup.coe_mul, hτv']
      exact diagGL_mul_permGL3_eq_conj d' (vec3_prod _)
    refine noCQAt_of_pgl fun M hM hMx hxM => false_of_perfect_cyclic hM (hconjx ▸ hMx)
      (hconjx ▸ hxM) ?_
    rw [← hconjx]
    intro h1
    apply hx1
    have h2 : piH H (τ (.ofAdd (rotL (-v))) * w) = 1 := Subtype.ext h1
    rw [← hinv, map_inv, inv_eq_one] at h2
    exact h2

end Main

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
