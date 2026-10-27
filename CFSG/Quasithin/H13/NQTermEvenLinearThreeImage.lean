module

public import CFSG.Quasithin.H13.NQTermPerfectSmallFamily
public import CFSG.Quasithin.SteinbergBQReducibleTwoNormalizers

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.SteinbergCC (frattiniQuotConj)
open scoped MatrixGroups

section TwoElements

variable {k : Type*} [Field k]

theorem exists_lift_pow_two_pow {m : ℕ} (y : LinearFlag.projectiveSL 3 k) (hy : y ^ 2 ^ m = 1) :
    ∃ s : SL(3, k), LinearFlag.proj 3 k s = y ∧ s ^ 2 ^ m = 1 := by
  obtain ⟨s₀, rfl⟩ := LinearFlag.proj_surjective 3 k y
  have h1 : s₀ ^ 2 ^ m ∈ LinearFlag.scalars 3 k := by
    rw [← LinearFlag.proj_eq_one_iff, map_pow]
    exact hy
  have h3 : (s₀ ^ 2 ^ m) ^ 3 = 1 := SteinbergBQ.pow_three_eq_one_of_mem_scalars h1
  have h4 : (2 ^ m) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  obtain ⟨c, hc⟩ : 3 ∣ 1 + 2 * (2 ^ m) ^ 2 := Nat.dvd_of_mod_eq_zero (by omega)
  refine ⟨s₀ ^ (1 + 2 * (2 ^ m) ^ 2), ?_, ?_⟩
  · rw [map_pow, pow_add, pow_one, show 2 * (2 ^ m) ^ 2 = 2 ^ m * (2 * 2 ^ m) by ring, pow_mul,
      hy, one_pow, mul_one]
  · rw [← pow_mul, hc, show 3 * c * 2 ^ m = 2 ^ m * 3 * c by ring, pow_mul, pow_mul, h3, one_pow]

theorem mul_comm_of_proj_conj_eq {m : ℕ} {s : SL(3, k)} (hs : s ^ 2 ^ m = 1) (d : SL(3, k))
    (hd : LinearFlag.proj 3 k (d * s * d⁻¹) = LinearFlag.proj 3 k s) : d * s = s * d := by
  have hz : s⁻¹ * (d * s * d⁻¹) ∈ LinearFlag.scalars 3 k := by
    rw [← LinearFlag.proj_eq_proj_iff]
    exact hd.symm
  set z := s⁻¹ * (d * s * d⁻¹) with hzdef
  have hzc : Commute s z :=
    (Subgroup.mem_center_iff.mp (LinearFlag.scalars_le_center 3 k hz) s)
  have hz3 : z ^ 3 = 1 := SteinbergBQ.pow_three_eq_one_of_mem_scalars hz
  have hdsd : d * s * d⁻¹ = s * z := by rw [hzdef, mul_inv_cancel_left]
  have hzn : z ^ 2 ^ m = 1 := by
    have h1 : (d * s * d⁻¹) ^ 2 ^ m = 1 := by rw [conj_pow, hs, mul_one, mul_inv_cancel]
    rw [hdsd, hzc.mul_pow, hs, one_mul] at h1
    exact h1
  have hcop : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  have hz1 : z = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hzn, hz3⟩
    rwa [hcop, pow_one] at h1
  rw [hz1, mul_one] at hdsd
  exact mul_inv_eq_iff_eq_mul.mp hdsd

theorem exists_offDiag_ne_zero_of_pow_two_pow [CharP k 2] {m : ℕ} {s : SL(3, k)}
    (hs : s ^ 2 ^ m = 1) (hs1 : s ≠ 1) :
    ∃ r t : Fin 3, r ≠ t ∧ (s : Matrix (Fin 3) (Fin 3) k) r t ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  apply hs1
  set M := (s : Matrix (Fin 3) (Fin 3) k) with hM
  have hdiag : M = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hno i j hij
  have hpow : M ^ 2 ^ m = 1 := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, hs, Matrix.SpecialLinearGroup.coe_one]
  rw [hdiag, Matrix.diagonal_pow, ← Matrix.diagonal_one] at hpow
  have hent : ∀ i, M i i = 1 := by
    intro i
    have h1 : M i i ^ 2 ^ m = 1 := congrFun (Matrix.diagonal_injective hpow) i
    have h2 : (M i i - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, h1, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m two_ne_zero)).mp h2)
  apply Subtype.ext
  change M = 1
  rw [hdiag, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hent i

theorem val_eq_of_planeElem_mul_comm {p : ℕ} [NeZero p] {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    (v : SteinbergBQ.sumZeroPlane p) {s : SL(3, k)}
    (hc : SteinbergBQ.planeElem ζ hζ.pow_eq_one v * s = s * SteinbergBQ.planeElem ζ hζ.pow_eq_one v)
    {r t : Fin 3} (hrt : (s : Matrix (Fin 3) (Fin 3) k) r t ≠ 0) :
    (v : Fin 3 → ZMod p) r = (v : Fin 3 → ZMod p) t := by
  have h1 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) r t) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, SteinbergBQ.coe_planeElem, SteinbergBQ.diagPow,
    Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
  apply SteinbergBQ.pow_val_injective hζ
  rw [mul_comm] at h1
  exact mul_left_cancel₀ hrt h1

end TwoElements

theorem sumZeroPlane_ext_of_ne {p : ℕ} {v w : SteinbergBQ.sumZeroPlane p} {r t : Fin 3}
    (hrt : r ≠ t) (h1 : (v : Fin 3 → ZMod p) r = (w : Fin 3 → ZMod p) r)
    (h2 : (v : Fin 3 → ZMod p) t = (w : Fin 3 → ZMod p) t) : v = w := by
  have hv : (v : Fin 3 → ZMod p) 0 + (v : Fin 3 → ZMod p) 1 + (v : Fin 3 → ZMod p) 2 = 0 := v.2
  have hw : (w : Fin 3 → ZMod p) 0 + (w : Fin 3 → ZMod p) 1 + (w : Fin 3 → ZMod p) 2 = 0 := w.2
  apply Subtype.ext
  funext i
  fin_cases r <;> fin_cases t <;> simp at hrt <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at h1 h2 ⊢ <;>
    first
    | exact h1
    | exact h2
    | linear_combination hv - hw - h1 - h2

@[expose] def coordLine {G : Type*} [Group G] {p : ℕ}
    (e : G →* Multiplicative (SteinbergBQ.sumZeroPlane p)) (r t : Fin 3) : Subgroup G where
  carrier := {x | ((Multiplicative.toAdd (e x) : SteinbergBQ.sumZeroPlane p) : Fin 3 → ZMod p) r =
    ((Multiplicative.toAdd (e x) : SteinbergBQ.sumZeroPlane p) : Fin 3 → ZMod p) t}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul, Submodule.coe_add, Pi.add_apply] at hx hy ⊢
    rw [hx, hy]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, map_inv, toAdd_inv, Submodule.coe_neg, Pi.neg_apply] at hx ⊢
    rw [hx]

theorem mem_coordLine {G : Type*} [Group G] {p : ℕ}
    {e : G →* Multiplicative (SteinbergBQ.sumZeroPlane p)} {r t : Fin 3} {x : G} :
    x ∈ coordLine e r t ↔
      ((Multiplicative.toAdd (e x) : SteinbergBQ.sumZeroPlane p) : Fin 3 → ZMod p) r =
        ((Multiplicative.toAdd (e x) : SteinbergBQ.sumZeroPlane p) : Fin 3 → ZMod p) t :=
  Iff.rfl

theorem coordLine_comm {G : Type*} [Group G] {p : ℕ}
    (e : G →* Multiplicative (SteinbergBQ.sumZeroPlane p)) (r t : Fin 3) :
    coordLine e r t = coordLine e t r := by
  ext x
  rw [mem_coordLine, mem_coordLine]
  exact eq_comm

theorem card_coordLine_le {G : Type*} [Group G] {p : ℕ} [NeZero p]
    {e : G →* Multiplicative (SteinbergBQ.sumZeroPlane p)} (he : Function.Injective e)
    {r t : Fin 3} (hrt : r ≠ t) : Nat.card (coordLine e r t) ≤ p := by
  have hinj : Function.Injective fun x : coordLine e r t =>
      ((Multiplicative.toAdd (e x) : SteinbergBQ.sumZeroPlane p) : Fin 3 → ZMod p) r := by
    intro x y hxy
    apply Subtype.ext
    apply he
    apply Multiplicative.toAdd.injective
    refine sumZeroPlane_ext_of_ne hrt hxy ?_
    rw [← mem_coordLine.mp x.2, ← mem_coordLine.mp y.2]
    exact hxy
  calc Nat.card (coordLine e r t) ≤ Nat.card (ZMod p) := Nat.card_le_card_of_injective _ hinj
    _ = p := Nat.card_zmod p

open CFSG.Quasithin.SteinbergBQ in
theorem original_perfect_plane_excludes_central_even_linear_three_image {L : Type*} [Group L]
    [Finite L] (hL : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup L} [X.Normal] (hA1 : CFSG.pCore 2 X ≠ ⊥)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : L, ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (k : Type*) [Field k] [Finite k] [CharP k 2] :
    ¬ ∃ f : X →* LinearFlag.projectiveSL 3 k, IsPGroup 2 f.ker ∧ f.ker ≤ center X := by
  classical
  rintro ⟨f, hf2, hfZ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set A₀ := CFSG.pCore 2 X with hA₀
  have hA₀p : IsPGroup 2 A₀ := CFSG.pCore_isPGroup
  have hpow : ∀ x : X ⧸ A₀, x ^ p = 1 := fun x => hexp ▸ Monoid.pow_exponent_eq_one x
  have hXp : IsPGroup p (X ⧸ A₀) := fun x => ⟨1, by rw [pow_one]; exact hpow x⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p X) := inferInstance
  set P₁ : Subgroup X := (P₀ : Subgroup X) with hP₁
  have hbij := sylow_bijective_coreQuot hp2 hXp P₀
  set e₀ : P₁ ≃* X ⧸ A₀ := MulEquiv.ofBijective _ hbij with he₀
  have hPpow : ∀ u : P₁, u ^ p = 1 := fun u => e₀.injective (by rw [map_pow, hpow, map_one])
  have hPnc : ¬ IsCyclic P₁ := by
    intro hc
    have : IsCyclic (X ⧸ A₀) := isCyclic_of_surjective e₀ e₀.surjective
    have h1 := IsCyclic.exponent_eq_card (α := X ⧸ A₀)
    rw [hexp] at h1
    have h2 : Nat.card ((X ⧸ A₀) ⧸ frattini (X ⧸ A₀)) ≤ Nat.card (X ⧸ A₀) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [hW, ← h1] at h2
    nlinarith [hp.two_le]
  set θ := f.comp P₁.subtype with hθ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 P₁ f.ker P₀.isPGroup' hf2
    have h2 : (u : X) ∈ P₁ ⊓ f.ker := Subgroup.mem_inf.mpr ⟨u.2, hu⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  set PS := θ.range with hPS
  let ePS : P₁ ≃* PS := MonoidHom.ofInjective hθinj
  have hPSnc : ¬ IsCyclic PS := fun hc => hPnc (isCyclic_of_surjective ePS.symm ePS.symm.surjective)
  have hPSexp : ∀ x ∈ PS, x ^ p = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_pow, hPpow, map_one]
  have hk2 : ringChar k ≠ p := by
    rw [ringChar.eq k 2]
    exact fun h => hp2 h.symm
  obtain ⟨-, hPSe, hPSc, ζ, hζ, g, hg, hπinj, -, -⟩ :=
    noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers
      hp5 hk2 PS hPSnc hPSexp
  have hPc : Nat.card P₁ = p ^ 2 := by rw [Nat.card_congr ePS.toEquiv, hPSc]
  have : IsMulCommutative P₁ := ⟨⟨fun x y => ePS.injective (by
    rw [map_mul, map_mul]
    exact hPSe.toIsMulCommutative.is_comm.comm _ _)⟩⟩
  have hPe : CFSG.IsElementaryAbelian p P₁ := ⟨Monoid.exponent_dvd_of_forall_pow_eq_one hPpow⟩
  set ψ := (LinearFlag.proj 3 k).comp (SteinbergBQ.planeHom ζ hζ.pow_eq_one) with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : (⟨SteinbergBQ.planeHom ζ hζ.pow_eq_one a, ⟨a, rfl⟩⟩ :
        SteinbergBQ.diagPlane p ζ hζ.pow_eq_one) = ⟨SteinbergBQ.planeHom ζ hζ.pow_eq_one b,
          ⟨b, rfl⟩⟩ := hπinj hab
    have h2 := SteinbergBQ.planeElem_injective hζ (congrArg Subtype.val h1)
    exact Multiplicative.toAdd.injective h2
  set f' := (LinearFlag.conjAut 3 k g).toMonoidHom.comp f with hf'
  set θ' := f'.comp P₁.subtype with hθ'
  have hθ'inj : Function.Injective θ' := fun a b hab =>
    hθinj ((LinearFlag.conjAut 3 k g).injective hab)
  have hex : ∀ u : P₁, ∃ v, ψ v = θ' u := by
    intro u
    have h1 : θ' u ∈ PS.map (LinearFlag.conjAut 3 k g).toMonoidHom := ⟨θ u, ⟨u, rfl⟩, rfl⟩
    rw [hg] at h1
    obtain ⟨d, ⟨v, rfl⟩, hdv⟩ := h1
    exact ⟨v, hdv⟩
  choose ev hev using hex
  let e : P₁ →* Multiplicative (SteinbergBQ.sumZeroPlane p) :=
    { toFun := ev
      map_one' := hψinj (by rw [hev, map_one, map_one])
      map_mul' := fun u w => hψinj (by rw [map_mul, hev, hev, hev, map_mul]) }
  have heinj : Function.Injective e := fun u w h => hθ'inj (by
    rw [← hev, ← hev]
    exact congrArg ψ h)
  set Rsub : Fin 3 → Subgroup X := fun i =>
    (coordLine e (![1, 0, 0] i) (![2, 2, 1] i)).map P₁.subtype with hRsub
  have hRsub : ∀ r t : Fin 3, r ≠ t → ∃ i, (coordLine e r t).map P₁.subtype = Rsub i := by
    intro r t hrt
    fin_cases r <;> fin_cases t <;> simp at hrt
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, by rw [hRsub]; simp only; rw [coordLine_comm]; rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, by rw [hRsub]; simp only; rw [coordLine_comm]; rfl⟩
    · exact ⟨0, by rw [hRsub]; simp only; rw [coordLine_comm]; rfl⟩
  refine false_of_small_centralizer_family hL hp hp2 hA1 hX2 hXp hW hirr P₀ hPe hPc
    (Set.range Rsub) (Set.finite_range _) ?_ ?_
  · calc (Set.range Rsub).ncard ≤ (Set.univ : Set (Fin 3)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ ≤ 4 := by rw [Set.ncard_univ, Nat.card_fin]; norm_num
  intro a ha ha1 hac
  obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ A₀ ⊓ centralizer {a}, w ∉ center X := by
    by_contra hne
    push Not at hne
    exact hac fun x hx => hne x hx
  obtain ⟨hwA, hwc⟩ := Subgroup.mem_inf.mp hw
  have hwa : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
  have hfw : f' w ≠ 1 := by
    intro h
    apply hwZ
    apply hfZ
    rw [MonoidHom.mem_ker]
    exact (MulEquiv.map_eq_one_iff (LinearFlag.conjAut 3 k g)).mp h
  obtain ⟨m, hm⟩ := hA₀p ⟨w, hwA⟩
  have hwm : w ^ 2 ^ m = 1 := by
    have h1 := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow] at h1
  obtain ⟨s, hs, hsm⟩ := exists_lift_pow_two_pow (f' w) (by rw [← map_pow, hwm, map_one])
  have hs1 : s ≠ 1 := fun h => hfw (by rw [← hs, h, map_one])
  set u : P₁ := ⟨a, ha⟩ with hu
  set d := SteinbergBQ.planeElem ζ hζ.pow_eq_one (Multiplicative.toAdd (e u)) with hd
  have hdproj : LinearFlag.proj 3 k d = f' a := hev u
  have hds : d * s = s * d := by
    refine mul_comm_of_proj_conj_eq hsm d ?_
    have hcomm : f' a * f' w = f' w * f' a := by rw [← map_mul, ← map_mul, hwa]
    rw [map_mul, map_mul, map_inv, hdproj, hs, hcomm, mul_inv_cancel_right]
  obtain ⟨r, t, hrt, hst⟩ := exists_offDiag_ne_zero_of_pow_two_pow hsm hs1
  have hrt' := val_eq_of_planeElem_mul_comm hζ (Multiplicative.toAdd (e u)) hds hst
  have hau : u ∈ coordLine e r t := hrt'
  have hle : zpowers a ≤ (coordLine e r t).map P₁.subtype :=
    Subgroup.zpowers_le.mpr ⟨u, hau, rfl⟩
  have hcard : Nat.card ((coordLine e r t).map P₁.subtype) ≤ Nat.card (zpowers a) := by
    rw [Subgroup.card_map_of_injective P₁.subtype_injective, Nat.card_zpowers,
      orderOf_eq_prime (by simpa using congrArg Subtype.val (hPpow u)) ha1]
    exact card_coordLine_le heinj hrt
  obtain ⟨i, hi⟩ := hRsub r t hrt
  exact ⟨i, (hi.symm.trans (Subgroup.eq_of_le_of_card_ge hle hcard).symm)⟩

end CFSG.Quasithin.H13.NQTerm
