module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusLabel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusMoved
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeightsAlg
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusInvol
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis
  CFSG.StandardType

open scoped BigOperators

@[expose] def OmqPlusSevenRoots {n : ℕ} (hn : 3 ≤ n) : Prop :=
  ∀ {m : ℕ}, 3 ≤ m → ∀ {a b : Fin n}, a ≠ b → ∀ {δ δ' : ℤ}, (δ = 1 ∨ δ = -1) →
    (δ' = 1 ∨ δ' = -1) → ∀ {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}, SpIsSign s →
    ∏ c, s c = 1 →
    ((π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) →
    ∃ u : Fin 7 → Fin n → ZMod m, Function.Injective u ∧
      (∀ i, ∃ (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ), SpIsSign s' ∧ ∏ c, s' c = 1 ∧
        omqSignedAct π' s' (Pi.single a (δ : ZMod m) + Pi.single b (δ' : ZMod m)) = u i) ∧
      ∀ i l, u i ≠ omqSignedAct π s (u l)

theorem omqPlusSevenRoots_of_five {n : ℕ} (hn : 5 ≤ n) :
    OmqPlusSevenRoots (by omega : 3 ≤ n) :=
  by
    intro m hm3 a b hab δ δ' hδ hδ' π s hs _ hx
    exact omq_exists_seven_orbit_roots hn hm3 hab hδ hδ' hs hx

private theorem c2slomqk1_finrank_range_conj {G k V : Type*} [Group G] [Field k]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (g y : G) :
    Module.finrank k (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

private lemma c2slomqk1_exists_ne_of_wt_ne {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] {m : ℕ} (hm : m = Nat.card Fˣ) (hodd : Odd m) {k : Type}
    [Field k] (ι : F →+* k) {ν ν' : Fin n → ZMod m} (hne : ν ≠ ν') :
    ∃ h ∈ (omPlusCurtisDatum n F hn).H, omqPlusWt ι ν h ≠ omqPlusWt ι ν' h := by
  by_contra h
  exact hne (omq_omPlus_wt_injective hn hm hodd ι (fun g hg =>
    not_not.mp (fun hg' => h ⟨g, hg, hg'⟩)))

private theorem c2slomqk1_transport {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ} (hm : m = Nat.card Fˣ) {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] (ι : F →+* k) {σ : Representation k (spinGroup (quadPlus n F)) V}
    {ν : Fin n → ZMod m} {w : V} (hw : w ≠ 0)
    (hwt : ∀ h ∈ (omPlusCurtisDatum n F hn).H, σ h w = omqPlusWt ι ν h • w)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s) (hs : SpIsSign s) :
    σ ((omPlusCurtisDatum n F hn).nW x) w ≠ 0 ∧
      ∀ h ∈ (omPlusCurtisDatum n F hn).H,
        σ h (σ ((omPlusCurtisDatum n F hn).nW x) w) =
          omqPlusWt ι (omqSignedAct π s ν) h •
            σ ((omPlusCurtisDatum n F hn).nW x) w := by
  have hne : σ ((omPlusCurtisDatum n F hn).nW x) w ≠ 0 := by
    intro h0
    apply hw
    have h1 := congrArg (fun v => σ ((omPlusCurtisDatum n F hn).nW x)⁻¹ v) h0
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h1
  refine ⟨hne, fun h hh => ?_⟩
  have hc := omq_omPlus_wt_conj hn hm ι hxr hs ν hh
  calc σ h (σ ((omPlusCurtisDatum n F hn).nW x) w)
      = σ (h * (omPlusCurtisDatum n F hn).nW x) w := by
        rw [map_mul, Module.End.mul_apply]
    _ = σ ((omPlusCurtisDatum n F hn).nW x *
          (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h * (omPlusCurtisDatum n F hn).nW x)) w := by
        rw [show h * (omPlusCurtisDatum n F hn).nW x =
          (omPlusCurtisDatum n F hn).nW x *
            (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h * (omPlusCurtisDatum n F hn).nW x)
            from by group]
    _ = σ ((omPlusCurtisDatum n F hn).nW x)
          (σ (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h *
            (omPlusCurtisDatum n F hn).nW x) w) := by
        rw [map_mul, Module.End.mul_apply]
    _ = σ ((omPlusCurtisDatum n F hn).nW x)
          (omqPlusWt ι ν (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h *
            (omPlusCurtisDatum n F hn).nW x) • w) := by rw [hwt _ hc.1]
    _ = omqPlusWt ι ν (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h *
          (omPlusCurtisDatum n F hn).nW x) • σ ((omPlusCurtisDatum n F hn).nW x) w := by
        rw [map_smul]
    _ = omqPlusWt ι (omqSignedAct π s ν) h • σ ((omPlusCurtisDatum n F hn).nW x) w := by
        rw [hc.2]

private lemma c2slomqk1_neg_toStdD_single_eq {n m : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (-(fun x => (((toStdD n (Pi.single i 1)) x : ℤ) : ZMod m))) =
      Pi.single (rootIdxD n i) ((-1 : ℤ) : ZMod m) +
        Pi.single (rootIdxD' n i) (((-boolSign (rootSignD n i) : ℤ)) : ZMod m) := by
  funext x
  rw [Pi.neg_apply, toStdD_single_eq hn i, Pi.add_apply, Pi.single_apply, Pi.single_apply,
    Pi.add_apply, Pi.single_apply, Pi.single_apply]
  by_cases hx : x = rootIdxD n i
  · subst hx
    simp [rootIdxD_ne n hn i]
  · by_cases hx' : x = rootIdxD' n i
    · subst hx'
      simp [hx, (rootIdxD_ne n hn i).symm]
    · simp [hx, hx']

theorem omq_omPlus_kappa_one_rank (h1 : OmqPlusWeightVector) (h2 : OmqRankFromWeights) {n : ℕ}
    (hn : 3 ≤ n) (hseven : OmqPlusSevenRoots hn) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : 4 ≤ Nat.card F)
    {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ι : F →+* k) {σ : Representation k (spinGroup (quadPlus n F)) V} (hσ : IsSimpleRep σ)
    {y : V} {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F (by omega)).IsCurtisType σ y χ μ)
    (hχ1 : ∀ h ∈ (omPlusCurtisDatum n F (by omega)).H, χ h = 1)
    {g : spinGroup (quadPlus n F)} (hg2 : g * g = 1) (hσg : σ g ≠ 1) :
    7 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let m : ℕ := Nat.card Fˣ
  have hm : m = Nat.card Fˣ := rfl
  have hcard_units : m = Nat.card F - 1 := by rw [hm, Nat.card_units]
  have hmodd : Odd m := by
    rw [hcard_units]
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨f, -, hcard⟩ := FiniteField.card F 2
    have heven : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact even_two.pow_of_ne_zero (f.pos).ne'
    exact Nat.Even.sub_odd (n := 1) (by have := Nat.card_pos (α := F); omega) heven ⟨0, rfl⟩
  have hm3 : 3 ≤ m := by rw [hcard_units]; omega
  let D := omPlusCurtisDatum n F hn3
  obtain ⟨i, hi⟩ := omq_omPlus_exists_separating hn3 hσ ht hσg
  let ν₀ : Fin n → ZMod m := fun b => ((toStdD n (Pi.single i 1) b : ℤ) : ZMod m)
  let ν : Fin n → ZMod m := -ν₀
  have hchi : ∀ a : Fˣ, χ (torusD F hn3 i a) = ι (a : F) ^ m := by
    intro a
    have hmem : torusD F hn3 i a ∈ D.H := by
      rw [omPlusCurtisDatum_H (hn := hn3)]
      exact Subgroup.mem_iSup_of_mem i ⟨a, rfl⟩
    have hχa : χ (torusD F hn3 i a) = 1 := hχ1 _ (by simpa [D] using hmem)
    have h1u : a ^ m = 1 := by rw [hm, pow_card_eq_one']
    have hPa : (a : F) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1u, Units.val_one]
    rw [hχa, ← map_pow, hPa, map_one]
  obtain ⟨w, hwne, hwv⟩ := h1 hn3 ι hσ ht i hi (c := m) (j := 1)
    (by omega) (le_of_eq hm) hchi (by rw [Nat.choose_one_right]; exact hmodd)
  have hwt : ∀ h ∈ D.H, σ h w = omqPlusWt ι ν h • w := by
    intro h hh
    have hχh : χ h = 1 := hχ1 h (by simpa [D] using hh)
    have hneg := omq_omPlus_wt_neg hn3 hm ι ν₀ hh
    calc σ h w = (χ h * (omqPlusWt ι ν₀ h)⁻¹ ^ 1) • w := hwv h (by simpa [D] using hh)
      _ = (omqPlusWt ι ν₀ h)⁻¹ • w := by rw [hχh, one_mul, pow_one]
      _ = omqPlusWt ι ν h • w := by rw [show ν = -ν₀ from rfl, hneg]
  have hg1 : g ≠ 1 := fun h => hσg (by rw [h, map_one])
  obtain ⟨g', π, s, hs, hprod, hshape, hg⟩ := exists_conj_spinMatrix_eq_spMonoPerm hn3 hg2 hg1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_spinMatrix_eq (K := F) hn3
    (g := g' * g * g'⁻¹) hs hprod hg
  have glue : ∀ (a b : Fin n) (δ δ' : ℤ), a ≠ b → (δ = 1 ∨ δ = -1) →
      (δ' = 1 ∨ δ' = -1) → ν = Pi.single a (δ : ZMod m) + Pi.single b (δ' : ZMod m) →
      7 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
    intro a b δ δ' hab hδ hδ' hν
    obtain ⟨u, hinj, horb, hmove⟩ :=
      hseven hm3 hab hδ hδ' hs hprod hshape
    have hdata : ∀ l : Fin 7, ∃ (x : (coxeterMatrix (isFiniteType_cartanD n)).Group)
        (π' : Equiv.Perm (Fin n)) (s' : Fin n → ℤ),
        SpIsSign s' ∧ (∏ c, s' c = 1) ∧ OmRealizes n x π' s' ∧
          omqSignedAct π' s' ν = u l := by
      intro l
      obtain ⟨π', s', hs', hprod', hact⟩ := horb l
      obtain ⟨x', hx'r⟩ := exists_omRealizes_of_even (n := n) hn2 π' hs' hprod'
      exact ⟨x', π', s', hs', hprod', hx'r, by rw [hν]; exact hact⟩
    choose xf πf sf hdata' using hdata
    have hsf : ∀ l, SpIsSign (sf l) := fun l => (hdata' l).1
    have hxf : ∀ l, OmRealizes n (xf l) (πf l) (sf l) := fun l => (hdata' l).2.2.1
    have hwf : ∀ l, omqSignedAct (πf l) (sf l) ν = u l := fun l => (hdata' l).2.2.2
    let wl : Fin 7 → V := fun l => σ (D.nW (xf l)) w
    have hwl_ne : ∀ l, wl l ≠ 0 := fun l =>
      (c2slomqk1_transport hn3 hm ι hwne hwt (hxf l) (hsf l)).1
    have hwl_wt : ∀ l, ∀ h ∈ D.H, σ h (wl l) = omqPlusWt ι (u l) h • wl l := by
      intro l h hh
      have h2l := (c2slomqk1_transport hn3 hm ι hwne hwt (hxf l) (hsf l)).2 h hh
      rwa [hwf l] at h2l
    have hdistinct : ∀ l l', l ≠ l' →
        ∃ h ∈ D.H, omqPlusWt ι (u l) h ≠ omqPlusWt ι (u l') h :=
      fun l l' hll' => c2slomqk1_exists_ne_of_wt_ne hn3 hm hmodd ι (fun h => hll' (hinj h))
    have hnorm : ∀ h ∈ D.H, (D.nW x)⁻¹ * h * (D.nW x) ∈ D.H := fun h hh =>
      (omq_omPlus_wt_conj hn3 hm ι hxr hs (0 : Fin n → ZMod m) hh).1
    have hmove' : ∀ l l', ∃ h ∈ D.H,
        omqPlusWt ι (u l) ((D.nW x)⁻¹ * h * (D.nW x)) ≠ omqPlusWt ι (u l') h := by
      intro l l'
      have hne : omqSignedAct π s (u l) ≠ u l' := (hmove l' l).symm
      obtain ⟨h, hh, hval⟩ := c2slomqk1_exists_ne_of_wt_ne hn3 hm hmodd ι hne
      refine ⟨h, hh, ?_⟩
      have hc := omq_omPlus_wt_conj hn3 hm ι hxr hs (u l) hh
      rw [hc.2]
      exact hval
    have hrank := h2 σ D.H (D.nW x) hnorm 7 (fun l => omqPlusWt ι (u l)) wl
      hwl_ne hwl_wt hdistinct hmove'
    rw [hxw] at hrank
    rw [c2slomqk1_finrank_range_conj σ g' g] at hrank
    exact hrank
  exact glue (rootIdxD n i) (rootIdxD' n i) (-1) (-boolSign (rootSignD n i))
    (rootIdxD_ne n hn2 i) (Or.inr rfl)
    (by rcases boolSign_eq_one_or_eq_neg_one (rootSignD n i) with h | h <;> rw [h] <;> simp)
    (c2slomqk1_neg_toStdD_single_eq (n := n) (m := m) hn2 i)

end CFSG.LocalAnalysis.WeakClosure81
