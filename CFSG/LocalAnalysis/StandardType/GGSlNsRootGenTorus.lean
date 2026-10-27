module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB
  Multiplicative

section Coord

variable {s p : ℕ} [Fact p.Prime]

theorem swapMap_swapMap (i j : Fin s) (t : Fin s → ZMod p) :
    swapMap i j (swapMap i j t) = t := by
  funext m
  simp only [swapMap, Function.comp_apply, Equiv.swap_apply_self]

theorem negMap_negMap (i : Fin s) (t : Fin s → ZMod p) :
    negMap i (negMap i t) = t := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [negMap, Function.update_apply]
  · simp [negMap, Function.update_of_ne hm]

theorem swapMap_surjective (i j : Fin s) : Function.Surjective (swapMap (p := p) i j) :=
  fun t => ⟨swapMap i j t, swapMap_swapMap i j t⟩

theorem negMap_surjective (i : Fin s) : Function.Surjective (negMap (p := p) i) :=
  fun t => ⟨negMap i t, negMap_negMap i t⟩

theorem swapMap_eq_self_iff {i j : Fin s} {t : Fin s → ZMod p} :
    swapMap i j t = t ↔ t i = t j := by
  constructor
  · intro h
    have h1 := congrFun h i
    rw [swapMap, Function.comp_apply, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext m
    show t (Equiv.swap i j m) = t m
    by_cases hmi : m = i
    · subst hmi
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hmj : m = j
      · subst hmj
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]

theorem negMap_eq_self_iff (hp2 : p ≠ 2) {i : Fin s} {t : Fin s → ZMod p} :
    negMap i t = t ↔ t i = 0 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rw [negMap, Function.update_eq_self_iff]
  constructor
  · intro h
    exact (ZMod.add_self_eq_zero_iff_eq_zero hpodd).mp (neg_eq_iff_add_eq_zero.mp h)
  · intro h
    rw [h]
    exact neg_zero

theorem card_fixed_swapMap {i j : Fin s} (hij : i ≠ j) :
    Nat.card {t // swapMap (p := p) i j t = t} * p = p ^ s := by
  let f : (Fin s → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun t => t i - t j) fun t u => by
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single i c, ?_⟩
    simp [f, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
  have hiff : ∀ t, t ∈ f.ker ↔ swapMap i j t = t := by
    intro t
    rw [AddMonoidHom.mem_ker, swapMap_eq_self_iff]
    constructor
    · intro h
      exact sub_eq_zero.mp (by simpa [f] using h)
    · intro h
      simpa [f] using sub_eq_zero.mpr h
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsurj (f := f)
  have hcard' : Nat.card ↥f.ker * p = Nat.card (Fin s → ZMod p) := by
    simpa [Nat.card_zmod] using hcard
  have hker : Nat.card ↥f.ker = Nat.card {t // swapMap i j t = t} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← hker, hcard', Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_fixed_negMap (hp2 : p ≠ 2) (i : Fin s) :
    Nat.card {t // negMap (p := p) i t = t} * p = p ^ s := by
  let f : (Fin s → ZMod p) →+ ZMod p :=
    Pi.evalAddMonoidHom (fun _ : Fin s => ZMod p) i
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single i c, ?_⟩
    simp [f, Pi.single_eq_same]
  have hiff : ∀ t, t ∈ f.ker ↔ negMap i t = t := by
    intro t
    rw [AddMonoidHom.mem_ker, negMap_eq_self_iff hp2]
    constructor
    · intro h
      simpa [f] using h
    · intro h
      simpa [f] using h
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsurj (f := f)
  have hcard' : Nat.card ↥f.ker * p = Nat.card (Fin s → ZMod p) := by
    simpa [Nat.card_zmod] using hcard
  have hker : Nat.card ↥f.ker = Nat.card {t // negMap i t = t} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← hker, hcard', Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem swapMap_single (i j m : Fin s) (c : ZMod p) :
    swapMap i j (Pi.single m c) = Pi.single (Equiv.swap i j m) c := by
  funext x
  by_cases hx : x = Equiv.swap i j m
  · subst hx
    rw [swapMap, Function.comp_apply, Equiv.swap_apply_self, Pi.single_eq_same,
      Pi.single_eq_same]
  · have hx' : Equiv.swap i j x ≠ m := by
      intro h
      apply hx
      calc x = Equiv.swap i j (Equiv.swap i j x) := (Equiv.swap_apply_self i j x).symm
        _ = Equiv.swap i j m := by rw [h]
    rw [swapMap, Function.comp_apply, Pi.single_eq_of_ne hx', Pi.single_eq_of_ne hx]

theorem pair_eq_of_swapMap_eq {i j k l : Fin s} (hij : i ≠ j) (hkl : k ≠ l)
    (h : swapMap (p := p) i j = swapMap k l) : ({i, j} : Finset (Fin s)) = {k, l} := by
  have hsingle : ∀ m : Fin s,
      (Pi.single (Equiv.swap i j m) (1 : ZMod p) : Fin s → ZMod p) =
        (Pi.single (Equiv.swap k l m) (1 : ZMod p) : Fin s → ZMod p) := by
    intro m
    have h1 := congrFun h ((Pi.single m (1 : ZMod p) : Fin s → ZMod p))
    simpa [swapMap_single] using h1
  have hind : ∀ m, Equiv.swap i j m = Equiv.swap k l m := by
    intro m
    by_contra hne
    have h1 := congrFun (hsingle m) (Equiv.swap i j m)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
    exact one_ne_zero h1
  have hswap : Equiv.swap i j = Equiv.swap k l := Equiv.ext hind
  have hsupp := congrArg Equiv.Perm.support hswap
  rwa [Equiv.Perm.support_swap hij, Equiv.Perm.support_swap hkl] at hsupp

theorem swapMap_ne_negMap {i j : Fin s} (hij : i ≠ j) (m : Fin s) :
    swapMap (p := p) i j ≠ negMap m := by
  intro h
  have h1 := congrFun (congrFun h (Pi.single i 1)) j
  rw [swapMap, Function.comp_apply, Equiv.swap_apply_right, Pi.single_eq_same] at h1
  rw [negMap] at h1
  by_cases hm : j = m
  · subst hm
    rw [Function.update_apply, if_pos rfl, Pi.single_eq_of_ne (Ne.symm hij)] at h1
    have h2 : (1 : ZMod p) = 0 := h1.trans (neg_zero : (-(0 : ZMod p)) = 0)
    exact (Fact.out : p.Prime).not_dvd_one
      ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h2))
  · rw [Function.update_of_ne hm, Pi.single_eq_of_ne (Ne.symm hij)] at h1
    exact one_ne_zero h1

theorem eq_of_negMap_eq (hp2 : p ≠ 2) {m m' : Fin s} (h : negMap (p := p) m = negMap m') :
    m = m' := by
  by_contra hne
  have h1 := congrFun (congrFun h (Pi.single m 1)) m
  rw [negMap, Function.update_apply, if_pos rfl] at h1
  rw [negMap, Function.update_of_ne hne] at h1
  rw [Pi.single_eq_same] at h1
  have hp2' : 2 < p := by
    have hle := (Fact.out : p.Prime).two_le
    omega
  haveI : Fact (2 < p) := ⟨hp2'⟩
  exact (CharP.neg_one_ne_one (ZMod p) p) h1

end Coord

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}
  [Fact p.Prime] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1} {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin n) K →* L'}
  {A : Subgroup (MulAut L')}

private theorem torusSL_pow_p (a : Multiplicative (Fin s → ZMod p)) :
    torusSL ε hC hCp a ^ p = 1 := by
  simpa [torusSL] using
    CoordSL.frameHom_pow_p (ψ := MonoidHom.id (SpecialLinearGroup (Fin n) K))
      (A₀ := 1) (ε := ε) (C := rootMat g) (hC := hC) hCp a

theorem injective_conj_torusSL
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1)) :
    Function.Injective fun t : Multiplicative (Fin s → ZMod p) =>
      MulAut.conj (φ (torusSL ε hC hCp t)) := by
  let ψ : SpecialLinearGroup (Fin n) K →* MulAut L' := MulAut.conj.comp φ
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : MulAut.conj (φ x) = 1 := by simpa [ψ] using hx
    apply hφc x
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : MulAut.conj (φ x) y = y := by rw [hx1]; rfl
    rw [MulAut.conj_apply] at h1
    calc y * φ x = (φ x * y * (φ x)⁻¹) * φ x := by rw [h1]
      _ = φ x * y := by group
  have hinj := CoordSL.frameHom_injective (ψ := ψ) (A₀ := 1) (ε := ε)
    (C := rootMat g) (hC := hC) hCp hker (CoordSL.rootPB_dim_pos g) hunit
  have hfun : (fun t => CoordSL.frameHom ψ 1 ε hC hCp t) =
      fun t => MulAut.conj (φ (torusSL ε hC hCp t)) := by
    funext t
    rw [show t = ofAdd (toAdd t) from (ofAdd_toAdd t).symm]
    rw [CoordSL.frameHom_apply, torusSL, CoordSL.frameHom_apply]
    simp [ψ, MulAut.conj_apply]
  change Function.Injective (fun t => CoordSL.frameHom ψ 1 ε hC hCp t) at hinj
  rw [hfun] at hinj
  exact hinj

@[expose] noncomputable def torusFun (hCp : rootMat g ^ p = 1)
    (hM : IsBlockTorusModel φ ε hC A) (t : Multiplicative (Fin s → ZMod p)) : MulAut L' :=
  MulAut.conj (φ (torusSL ε hC hCp t))

theorem torusFun_mem (hCp : rootMat g ^ p = 1)
    (hM : IsBlockTorusModel φ ε hC A) (t : Multiplicative (Fin s → ZMod p)) :
    torusFun hCp hM t ∈ A := by
  have h : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (toAdd t)))) ∈ A :=
    (hM.mem_iff hCp).mpr ⟨toAdd t, rfl⟩
  convert h using 1
  rw [torusFun, ofAdd_toAdd]

@[expose] noncomputable def torusHom (hCp : rootMat g ^ p = 1)
    (hM : IsBlockTorusModel φ ε hC A) : Multiplicative (Fin s → ZMod p) →* A where
  toFun t := ⟨torusFun hCp hM t, torusFun_mem hCp hM t⟩
  map_one' := by
    apply Subtype.ext
    change torusFun hCp hM 1 = 1
    rw [torusFun, map_one (torusSL ε hC hCp), map_one φ, map_one (MulAut.conj)]
  map_mul' t u := by
    apply Subtype.ext
    change torusFun hCp hM (t * u) = torusFun hCp hM t * torusFun hCp hM u
    rw [torusFun, torusFun, torusFun, map_mul (torusSL ε hC hCp) t u, map_mul φ,
      map_mul (MulAut.conj)]

@[expose] noncomputable def torusEquiv (hCp : rootMat g ^ p = 1) (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1)) :
    Multiplicative (Fin s → ZMod p) ≃* A :=
  MulEquiv.ofBijective (torusHom (ε := ε) (hC := hC) hCp hM)
    ⟨fun a b h => by
      have h' : torusFun hCp hM a = torusFun hCp hM b :=
        congrArg (fun x : A => (x : MulAut L')) h
      change MulAut.conj (φ (torusSL ε hC hCp a)) =
        MulAut.conj (φ (torusSL ε hC hCp b)) at h'
      exact injective_conj_torusSL (ε := ε) (hC := hC) (hCp := hCp) hφc hunit h',
     fun a => by
      obtain ⟨t, ht⟩ := (hM.mem_iff hCp).mp a.2
      refine ⟨ofAdd t, Subtype.ext ?_⟩
      change torusFun hCp hM (ofAdd t) = (a : MulAut L')
      rw [torusFun]
      exact ht.symm⟩

theorem coe_torusEquiv (hCp : rootMat g ^ p = 1) (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    (t : Multiplicative (Fin s → ZMod p)) :
    ((torusEquiv hCp hM hφc hunit t : A) : MulAut L') =
      MulAut.conj (φ (torusSL ε hC hCp t)) := by
  change ((torusHom (ε := ε) (hC := hC) hCp hM t : A) : MulAut L') =
    MulAut.conj (φ (torusSL ε hC hCp t))
  rfl

theorem IsBlockTorusModel.card_eq (hCp : rootMat g ^ p = 1) (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1)) :
    Nat.card A = p ^ s := by
  rw [← Nat.card_congr (torusEquiv hCp hM hφc hunit).toEquiv,
    Nat.card_congr Multiplicative.toAdd]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

variable {w : SpecialLinearGroup (Fin n) K} {f : (Fin s → ZMod p) → (Fin s → ZMod p)}

theorem ggTorusWeylElt_of_conj (hM : IsBlockTorusModel φ ε hC A)
    (hw : ∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t))) :
    GGTorusWeylElt p A (φ w) := by
  intro a ha
  obtain ⟨t, rfl⟩ := (hM.mem_iff hCp).mp ha
  set c : L' := φ (torusSL ε hC hCp (ofAdd (f t))) *
    (φ (torusSL ε hC hCp (ofAdd t)))⁻¹ with hc
  have hkey : φ w * (MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) (φ w))⁻¹ = c := by
    rw [hc, MulAut.conj_apply]
    calc φ w * (φ (torusSL ε hC hCp (ofAdd t)) * φ w *
          (φ (torusSL ε hC hCp (ofAdd t)))⁻¹)⁻¹
        = φ w * φ (torusSL ε hC hCp (ofAdd t)) * (φ w)⁻¹ *
            (φ (torusSL ε hC hCp (ofAdd t)))⁻¹ := by group
      _ = φ (w * torusSL ε hC hCp (ofAdd t) * w⁻¹) *
            (φ (torusSL ε hC hCp (ofAdd t)))⁻¹ := by
              simp only [← map_mul, ← map_inv]
      _ = φ (torusSL ε hC hCp (ofAdd (f t))) *
            (φ (torusSL ε hC hCp (ofAdd t)))⁻¹ := by rw [hw t]
  refine ⟨?_, ?_⟩
  · rw [hkey, hc]
    have harg : (torusSL ε hC hCp (ofAdd (f t)) *
        (torusSL ε hC hCp (ofAdd t))⁻¹) ^ p = 1 := by
      rw [← map_inv, ← map_mul]
      exact torusSL_pow_p _
    rw [← map_inv, ← map_mul, ← map_pow, harg, map_one]
  · intro a' ha'
    obtain ⟨u, rfl⟩ := (hM.mem_iff hCp).mp ha'
    have hcomm : φ (torusSL ε hC hCp (ofAdd u)) * c =
        c * φ (torusSL ε hC hCp (ofAdd u)) := by
      rw [hc]
      simp only [← map_mul, ← map_inv]
      rw [mul_comm]
    rw [hkey, MulAut.conj_apply, hcomm]
    group

theorem conj_mem_normalizer_of_conj (hM : IsBlockTorusModel φ ε hC A)
    (hw : ∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t)))
    (hf : Function.Surjective f) :
    MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨t, rfl⟩ := (hM.mem_iff hCp).mp hb
    obtain ⟨u, rfl⟩ := hf t
    refine (hM.mem_iff hCp).mpr ⟨f (f u), ?_⟩
    simp only [← map_mul, ← map_inv, hw (f u)]
  · intro hb
    obtain ⟨t, ht⟩ := (hM.mem_iff hCp).mp hb
    obtain ⟨u, rfl⟩ := hf t
    refine (hM.mem_iff hCp).mpr ⟨u, ?_⟩
    calc b = (MulAut.conj (φ w))⁻¹ * (MulAut.conj (φ w) * b *
          (MulAut.conj (φ w))⁻¹) * MulAut.conj (φ w) := by group
      _ = (MulAut.conj (φ w))⁻¹ *
            MulAut.conj (φ (torusSL ε hC hCp (ofAdd (f u)))) *
            MulAut.conj (φ w) := by rw [ht]
      _ = MulAut.conj (φ (torusSL ε hC hCp (ofAdd u))) := by
            simp only [← map_mul, ← map_inv]
            rw [show w⁻¹ * torusSL ε hC hCp (ofAdd (f u)) * w =
                torusSL ε hC hCp (ofAdd u) from by
              rw [← hw u]
              group]

theorem ggConjAut_torusEquiv (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    (hw : ∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t)))
    (hn : MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L'))) (t : Fin s → ZMod p) :
    ggConjAut A hn (torusEquiv hCp hM hφc hunit (ofAdd t)) =
      torusEquiv hCp hM hφc hunit (ofAdd (f t)) := by
  refine Subtype.ext ?_
  rw [ggConjAut_apply, coe_torusEquiv, coe_torusEquiv]
  simp only [← map_mul, ← map_inv, hw t]

theorem commute_conj_iff_of_conj
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    (hw : ∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t)))
    (t : Fin s → ZMod p) :
    MulAut.conj (φ w) * MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) =
        MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) * MulAut.conj (φ w) ↔ f t = t := by
  have hAB : MulAut.conj (φ w) * MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) =
      MulAut.conj (φ (torusSL ε hC hCp (ofAdd (f t)))) * MulAut.conj (φ w) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul, ← hw t]
    group
  constructor
  · intro h
    have h' : MulAut.conj (φ (torusSL ε hC hCp (ofAdd (f t)))) * MulAut.conj (φ w) =
        MulAut.conj (φ (torusSL ε hC hCp (ofAdd t))) * MulAut.conj (φ w) := by
      rw [← hAB]
      exact h
    exact ofAdd.injective (injective_conj_torusSL (ε := ε) (hC := hC) (hCp := hCp)
      hφc hunit (mul_right_cancel h'))
  · intro h
    rw [hAB, h]

theorem isReflection_of_conj (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    (hw : ∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t)))
    (hn : MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hf2 : ∀ t, f (f t) = t) (hfix : Nat.card {t // f t = t} * p = p ^ s) :
    GGIsReflection p (ggConjAut A hn) := by
  let e := torusEquiv hCp hM hφc hunit
  have he : ∀ t : Fin s → ZMod p,
      ggConjAut A hn (e (ofAdd t)) = e (ofAdd (f t)) :=
    fun t => ggConjAut_torusEquiv hM hφc hunit hw hn t
  constructor
  · refine MulEquiv.ext fun b => ?_
    obtain ⟨t, rfl⟩ := e.surjective b
    obtain ⟨u, hu⟩ : ∃ u, t = ofAdd u := ⟨toAdd t, (ofAdd_toAdd t).symm⟩
    rw [hu, pow_two, MulAut.mul_apply, he u, he (f u), hf2 u]
    rfl
  · have hiff : ∀ u : Multiplicative (Fin s → ZMod p),
        ggConjAut A hn (e u) = e u ↔ f (toAdd u) = toAdd u := by
      intro u
      have hu : u = ofAdd (toAdd u) := (ofAdd_toAdd u).symm
      conv_lhs => rw [hu]
      rw [he (toAdd u)]
      constructor
      · intro h
        exact ofAdd.injective (e.injective h)
      · intro h
        rw [h]
    have hcard : Nat.card {b : ↥A // ggConjAut A hn b = b} =
        Nat.card {t : Fin s → ZMod p // f t = t} := by
      have hsub : {u : Multiplicative (Fin s → ZMod p) //
          ggConjAut A hn (e u) = e u} ≃ {b : ↥A // ggConjAut A hn b = b} :=
        Equiv.subtypeEquiv e.toEquiv (fun _ => Iff.rfl)
      have hofAdd : {t : Fin s → ZMod p // f t = t} ≃
          {u : Multiplicative (Fin s → ZMod p) // f (toAdd u) = toAdd u} :=
        Equiv.subtypeEquiv Multiplicative.ofAdd (fun t => by rw [toAdd_ofAdd])
      rw [← Nat.card_congr hsub, Nat.card_congr (Equiv.subtypeEquivRight hiff),
        ← Nat.card_congr hofAdd]
    rw [hcard]
    exact hfix.trans (hM.card_eq hCp hφc hunit).symm

theorem eq_of_ggConjAut_eq (hM : IsBlockTorusModel φ ε hC A)
    (hφc : ∀ x, φ x ∈ Subgroup.center L' → x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1))
    {w₁ w₂ : SpecialLinearGroup (Fin n) K} {f₁ f₂ : (Fin s → ZMod p) → (Fin s → ZMod p)}
    (hw₁ : ∀ t, w₁ * torusSL ε hC hCp (ofAdd t) * w₁⁻¹ = torusSL ε hC hCp (ofAdd (f₁ t)))
    (hw₂ : ∀ t, w₂ * torusSL ε hC hCp (ofAdd t) * w₂⁻¹ = torusSL ε hC hCp (ofAdd (f₂ t)))
    (hn₁ : MulAut.conj (φ w₁) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hn₂ : MulAut.conj (φ w₂) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (h : ggConjAut A hn₁ = ggConjAut A hn₂) : f₁ = f₂ := by
  funext t
  let e := torusEquiv hCp hM hφc hunit
  have h1 := ggConjAut_torusEquiv hM hφc hunit hw₁ hn₁ t
  have h2 := ggConjAut_torusEquiv hM hφc hunit hw₂ hn₂ t
  have h3 : e (ofAdd (f₁ t)) = e (ofAdd (f₂ t)) := by
    rw [← h1, ← h2, h]
  exact ofAdd.injective (e.injective h3)


end CFSG.StandardType.SlNsRootGen

end

