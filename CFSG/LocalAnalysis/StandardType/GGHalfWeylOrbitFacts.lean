module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGSpFrameOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

private theorem eq_or_inv_of_card_three {H : Type*} [Group H] (hH : Nat.card H = 3)
    {u u' : H} (hu : u ≠ 1) (hu' : u' ≠ 1) : u' = u ∨ u' = u⁻¹ := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hu3 : orderOf u = 3 := by
    have h1 : orderOf u ∣ 3 := hH ▸ orderOf_dvd_natCard u
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu
    · exact h
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hu3, hH]
  have hmem : u' ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top u'
  rw [mem_zpowers_iff_mem_range_orderOf, hu3] at hmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hmem
  have hk3 : k < 3 := Finset.mem_range.1 hk
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exact absurd (pow_zero u) hu'
  · exact Or.inl (pow_one u)
  · refine Or.inr ?_
    have h3 : u ^ 3 = 1 := hu3 ▸ pow_orderOf_eq_one u
    exact eq_inv_of_mul_eq_one_right (by simpa [← pow_succ'] using h3)

private theorem zmod3_eq_or_inv (u u' : Multiplicative (ZMod 3)) (hu : u ≠ 1) (hu' : u' ≠ 1) :
    u' = u ∨ u' = u⁻¹ := by
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact eq_or_inv_of_card_three hcard hu hu'

private theorem update_mulSingle_self {n : ℕ} {M : Type*} [One M] (i : Fin n) (a b : M) :
    Function.update (Pi.mulSingle i a : Fin n → M) i b = Pi.mulSingle i b := by
  funext t
  by_cases ht : t = i
  · subst ht; simp
  · simp [Function.update_of_ne ht, Pi.mulSingle_eq_of_ne ht]

private theorem exists_mulSingle_of_pairwise {n : ℕ} {M : Type*} [Group M] {v : Fin n → M}
    (hv : v ≠ 1) (h : ∀ i j : Fin n, i ≠ j → v i = 1 ∨ v j = 1) :
    ∃ i : Fin n, ∃ u : M, u ≠ 1 ∧ v = Pi.mulSingle i u := by
  classical
  have hex : ∃ i, v i ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hv (funext fun i => by simpa using hc i)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, v i, hi, ?_⟩
  funext t
  by_cases ht : t = i
  · subst ht; simp
  · have hne : i ≠ t := fun hh => ht hh.symm
    rcases h i t hne with h1 | h1
    · exact absurd h1 hi
    · simp [Pi.mulSingle_eq_of_ne ht, h1]

private theorem mem_orbit_of_frame_perm {G : Type} [Group G] {Bs : Subgroup G} {k : ℕ}
    {A : Subgroup (MulAut ↥Bs)}
    {Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs}
    (hΦ : ∀ h ∈ SpJoin.spSignedGroup (k + 1) 3, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a))
    {x y : G} {hx : x ∈ Bs} {hy : y ∈ Bs}
    {v w : Fin (k + 1) → Multiplicative (ZMod 3)}
    (hv : Φ v = (⟨x, hx⟩ : ↥Bs)) (hw : Φ w = (⟨y, hy⟩ : ↥Bs))
    {h : Equiv.Perm (Fin (k + 1) → Multiplicative (ZMod 3))}
    (hh : h ∈ SpJoin.spSignedGroup (k + 1) 3) (hval : h w = v) :
    x ∈ GGHalfOrbit A y hy := by
  obtain ⟨ψ, hψ, hψval⟩ := hΦ h hh
  refine ⟨ψ, hψ, ?_⟩
  have h1 : ψ (⟨y, hy⟩ : ↥Bs) = (⟨x, hx⟩ : ↥Bs) := by
    rw [← hw, hψval w, hval, hv]
  exact congrArg (fun z : ↥Bs => (z : G)) h1

theorem weyl_orbit_facts {G : Type} [Group G] [Finite G] {k : ℕ}
    {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs) (hk : 3 ≤ k) (hcard : Nat.card Bs = 3 ^ (k + 1))
    {X Y : Subgroup G} {x y : G} (hx : x ∈ Bs) (hy : y ∈ Bs) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxX : x ∈ Subgroup.centralizer (X : Set G)) (hyY : y ∈ Subgroup.centralizer (Y : Set G))
    (hAX : 2 ^ k * k.factorial ≤ Nat.card (ggAutomizer X Bs))
    (hAY : 2 ^ k * k.factorial ≤ Nat.card (ggAutomizer Y Bs))
    (hW : GGWeylOfType 3 (CoxeterMatrix.B (k + 1)) (ggAutomizer X Bs ⊔ ggAutomizer Y Bs)) :
    Set.ncard (GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) y hy) ≤ 2 * k + 2 ∧
    Set.ncard (GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) x hx) ≤ 2 * k + 2 ∧
    x ∈ GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) y hy ∧
    y ∈ GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) x hx := by
  classical
  have hfixX : ∀ ψ ∈ ggAutomizer X Bs, ((ψ ⟨x, hx⟩ : ↥Bs) : G) = x :=
    SpJoin.ggAutomizer_fixes_of_mem_centralizer hx hxX
  have hfixY : ∀ ψ ∈ ggAutomizer Y Bs, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y :=
    SpJoin.ggAutomizer_fixes_of_mem_centralizer hy hyY
  have horbY : Set.ncard (GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) y hy) ≤ 2 * k + 2 := by
    have h := SpJoin.ncard_automizer_orbit_le (n := k) (p := 3)
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) (H := ggAutomizer Y Bs)
      hW le_sup_right hy hfixY hAY
    simpa only [GGHalfOrbit] using h
  have horbX : Set.ncard (GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) x hx) ≤ 2 * k + 2 := by
    have h := SpJoin.ncard_automizer_orbit_le (n := k) (p := 3)
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) (H := ggAutomizer X Bs)
      hW le_sup_left hx hfixX hAX
    simpa only [GGHalfOrbit] using h
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl (p := 3) (m := k) Nat.prime_three
    (by norm_num) hBs (by omega) hcard hW
  let v : Fin (k + 1) → Multiplicative (ZMod 3) := Φ.symm ⟨x, hx⟩
  let w : Fin (k + 1) → Multiplicative (ZMod 3) := Φ.symm ⟨y, hy⟩
  have hv : v ≠ 1 := by
    intro hv1
    have h1 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      have hΦv : Φ v = (⟨x, hx⟩ : ↥Bs) := Φ.apply_symm_apply ⟨x, hx⟩
      rw [hv1, map_one] at hΦv
      exact hΦv.symm
    exact hx1 (Subtype.ext_iff.mp h1)
  have hw : w ≠ 1 := by
    intro hw1
    have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have hΦw : Φ w = (⟨y, hy⟩ : ↥Bs) := Φ.apply_symm_apply ⟨y, hy⟩
      rw [hw1, map_one] at hΦw
      exact hΦw.symm
    exact hy1 (Subtype.ext_iff.mp h1)
  have hpairv : ∀ i j : Fin (k + 1), i ≠ j → v i = 1 ∨ v j = 1 := by
    intro i j hij
    exact SpFrame.coord_eq_one_of_fixed (p := 3) (m := k) Nat.prime_three (by norm_num) hk
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) hW Φ hΦ
      (H := ggAutomizer X Bs) le_sup_left hx hfixX hAX hij
  have hpairw : ∀ i j : Fin (k + 1), i ≠ j → w i = 1 ∨ w j = 1 := by
    intro i j hij
    exact SpFrame.coord_eq_one_of_fixed (p := 3) (m := k) Nat.prime_three (by norm_num) hk
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) hW Φ hΦ
      (H := ggAutomizer Y Bs) le_sup_right hy hfixY hAY hij
  obtain ⟨i, u, hu, hv_eq⟩ := exists_mulSingle_of_pairwise hv hpairv
  obtain ⟨j, u', hu', hw_eq⟩ := exists_mulSingle_of_pairwise hw hpairw
  have key : ∃ h ∈ SpJoin.spSignedGroup (k + 1) 3, h w = v := by
    rcases zmod3_eq_or_inv u u' hu hu' with hcase | hcase
    · obtain ⟨h, hh, hhval⟩ :=
        SpJoin.exists_mem_spSignedGroup_mulSingle (n := k + 1) (p := 3) j i u'
      exact ⟨h, hh, by rw [hw_eq, hv_eq, hhval, hcase]⟩
    · obtain ⟨h₁, hh₁, hh₁val⟩ :=
        SpJoin.exists_mem_spSignedGroup_mulSingle (n := k + 1) (p := 3) j i u'
      have hcase' : u'⁻¹ = u := by rw [hcase]; exact inv_inv u
      have hstep : SpJoin.coordInv (k + 1) 3 i (Pi.mulSingle i u') = Pi.mulSingle i u := by
        rw [SpJoin.coordInv_apply, Pi.mulSingle_eq_same, update_mulSingle_self]
        exact congrArg (fun x => Pi.mulSingle i x) hcase'
      refine ⟨SpJoin.coordInv (k + 1) 3 i * h₁,
        Subgroup.mul_mem _ (SpJoin.coordInv_mem_spSignedGroup i) hh₁, ?_⟩
      rw [hw_eq, hv_eq, Equiv.Perm.mul_apply, hh₁val, hstep]
  obtain ⟨h, hh, hval⟩ := key
  have hx_orbit : x ∈ GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) y hy :=
    mem_orbit_of_frame_perm (x := x) (y := y) (hx := hx) (hy := hy) (v := v) (w := w)
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) (Φ := Φ)
      hΦ (Φ.apply_symm_apply ⟨x, hx⟩) (Φ.apply_symm_apply ⟨y, hy⟩) hh hval
  have hy_orbit : y ∈ GGHalfOrbit (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) x hx := by
    have hval' : h⁻¹ v = w := by
      rw [← hval]
      exact Equiv.symm_apply_apply h w
    exact mem_orbit_of_frame_perm (x := y) (y := x) (hx := hy) (hy := hx) (v := w) (w := v)
      (A := ggAutomizer X Bs ⊔ ggAutomizer Y Bs) (Φ := Φ)
      hΦ (Φ.apply_symm_apply ⟨y, hy⟩) (Φ.apply_symm_apply ⟨x, hx⟩)
      (Subgroup.inv_mem _ hh) hval'
  exact ⟨horbY, horbX, hx_orbit, hy_orbit⟩

end GGHalf

end CFSG.StandardType

end
