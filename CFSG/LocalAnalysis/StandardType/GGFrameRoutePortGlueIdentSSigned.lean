module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ChoiceTwo

variable {G : Type} [Group G] {Bs : Subgroup G}

private lemma sgnZ_xor (a b : Bool) (x : ZMod 3) :
    sgnZ a (sgnZ b x) = sgnZ (Bool.xor a b) x := by
  cases a <;> cases b <;> simp [sgnZ, Bool.xor]

private lemma sgnZ_one_injective (b c : Bool)
    (h : sgnZ b (1 : ZMod 3) = sgnZ c 1) : b = c := by
  cases b <;> cases c <;> simp only [sgnZ] at h ⊢ <;> try rfl
  all_goals exact absurd h (by decide)

private lemma moveExp_single (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool) (j : Fin 6) :
    moveExp π η (Pi.single j (1 : ZMod 3)) =
      Pi.single (π.symm j) (sgnZ (η (π.symm j)) 1) := by
  funext i
  rw [moveExp_apply, Pi.single_apply, Pi.single_apply]
  by_cases hi : i = π.symm j
  · subst hi
    simp
  · have hπi : π i ≠ j := by
      intro h
      apply hi
      rw [← h, Equiv.symm_apply_apply]
    simp [hi, hπi, sgnZ_zero]

private lemma moveExp_injective :
    Function.Injective (fun p : Equiv.Perm (Fin 6) × (Fin 6 → Bool) =>
      moveExp p.1 p.2) := by
  rintro ⟨π, η⟩ ⟨π', η'⟩ h
  have hfun : moveExp π η = moveExp π' η' := h
  have hπsymm : π.symm = π'.symm := by
    apply Equiv.ext
    intro j
    have h1 := congrFun hfun (Pi.single j (1 : ZMod 3))
    rw [moveExp_single, moveExp_single] at h1
    have hne : sgnZ (η (π.symm j)) (1 : ZMod 3) ≠ 0 := by
      intro h0
      rw [sgnZ_eq_zero_iff] at h0
      exact one_ne_zero h0
    have h2 := congrFun h1 (π.symm j)
    rw [Pi.single_eq_same] at h2
    by_cases hij : π.symm j = π'.symm j
    · exact hij
    · rw [Pi.single_eq_of_ne hij] at h2
      exact absurd h2 hne
  have hπ : π = π' := by
    rw [← Equiv.symm_symm π, ← Equiv.symm_symm π', hπsymm]
  have hη : η = η' := by
    funext i
    have h1 := congrFun hfun (Pi.single (π i) (1 : ZMod 3))
    rw [moveExp_single, moveExp_single] at h1
    have hπ'i : π'.symm (π i) = i := by rw [← hπ]; simp
    rw [hπ'i, Equiv.symm_apply_apply] at h1
    have h2 := congrFun h1 i
    rw [Pi.single_eq_same, Pi.single_eq_same] at h2
    exact sgnZ_one_injective (η i) (η' i) h2
  rw [hπ, hη]

private lemma moveExp_comp (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool)
    (π' : Equiv.Perm (Fin 6)) (η' : Fin 6 → Bool) (v : Fin 6 → ZMod 3) :
    moveExp π η (moveExp π' η' v) =
      moveExp (π' * π) (fun i => Bool.xor (η i) (η' (π i))) v := by
  funext i
  simp only [moveExp_apply, sgnZ_xor, Equiv.Perm.mul_apply]

private def pairMul (p q : Equiv.Perm (Fin 6) × (Fin 6 → Bool)) :
    Equiv.Perm (Fin 6) × (Fin 6 → Bool) :=
  (q.1 * p.1, fun i => Bool.xor (p.2 i) (q.2 (p.1 i)))

private lemma signedPerm_closure_eq_top {H : Type} [Group H] [Finite H]
    (σ : H ≃ Equiv.Perm (Fin 6) × (Fin 6 → Bool))
    (hσ_mul : ∀ φ ψ : H, σ (φ * ψ) = pairMul (σ φ) (σ ψ))
    (hσ_one : σ 1 = (1, fun _ => false)) :
    Subgroup.closure ({h : H | ∃ i, h = σ.symm (1, fun j => decide (j = i))} ∪
      {h : H | ∃ i j, i ≠ j ∧ h = σ.symm (Equiv.swap i j, fun _ => false)}) = ⊤ := by
  let Gen : Set H :=
    {h : H | ∃ i, h = σ.symm (1, fun j => decide (j = i))} ∪
      {h : H | ∃ i j, i ≠ j ∧ h = σ.symm (Equiv.swap i j, fun _ => false)}
  let W : Subgroup H := Subgroup.closure Gen
  have hlift_mul : ∀ p q : Equiv.Perm (Fin 6) × (Fin 6 → Bool),
      σ.symm (pairMul p q) = σ.symm p * σ.symm q := by
    intro p q
    apply σ.injective
    rw [hσ_mul]
    simp
  have hη_gen : ∀ η : Fin 6 → Bool, σ.symm (1, η) ∈ W := by
    intro η
    let S : Finset (Fin 6) := Finset.univ.filter (fun i => η i = true)
    have hη : η = fun i => decide (i ∈ S) := by
      funext i
      by_cases hi : η i = true
      · simp [S, hi]
      · have hif : η i = false := by cases h : η i <;> simp_all
        simp [S, hif]
    rw [hη]
    induction S using Finset.induction_on with
    | empty =>
      have h2 : σ.symm (1, (fun _ => false : Fin 6 → Bool)) = (1 : H) := by
        rw [← hσ_one, Equiv.symm_apply_apply]
      have h1 : ((1 : Equiv.Perm (Fin 6)), (fun i : Fin 6 => decide (i ∈ (∅ : Finset (Fin 6))))) =
          ((1 : Equiv.Perm (Fin 6)), (fun _ : Fin 6 => false)) := by
        apply Prod.ext
        · simp
        · funext i
          simp
      rw [h1, h2]
      exact W.one_mem
    | insert a s ha ih =>
      have h1 : ((1 : Equiv.Perm (Fin 6)), (fun i : Fin 6 => decide (i ∈ insert a s))) =
          pairMul ((1 : Equiv.Perm (Fin 6)), (fun i : Fin 6 => decide (i = a)))
            ((1 : Equiv.Perm (Fin 6)), (fun i : Fin 6 => decide (i ∈ s))) := by
        apply Prod.ext
        · simp [pairMul]
        · funext i
          simp only [pairMul, Bool.xor, Finset.mem_insert]
          by_cases hi : i = a
          · subst hi
            simp [ha]
          · simp [hi]
            rfl
      rw [h1, hlift_mul]
      exact W.mul_mem (Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)) ih
  have hπ_gen : ∀ π : Equiv.Perm (Fin 6), σ.symm (π, fun _ => false) ∈ W := by
    intro π
    refine Equiv.Perm.swap_induction_on π ?_ ?_
    · have h2 : σ.symm (1, (fun _ => false : Fin 6 → Bool)) = (1 : H) := by
        rw [← hσ_one, Equiv.symm_apply_apply]
      rw [h2]
      exact W.one_mem
    · intro f x y hxy ih
      have h1 : ((Equiv.swap x y * f : Equiv.Perm (Fin 6)), (fun _ : Fin 6 => false)) =
          pairMul ((f : Equiv.Perm (Fin 6)), (fun _ : Fin 6 => false))
            ((Equiv.swap x y : Equiv.Perm (Fin 6)), (fun _ : Fin 6 => false)) := by
        simp [pairMul]
      rw [h1, hlift_mul]
      exact W.mul_mem ih (Subgroup.subset_closure (Or.inr ⟨x, y, hxy, rfl⟩))
  have hgen_all : ∀ p : Equiv.Perm (Fin 6) × (Fin 6 → Bool), σ.symm p ∈ W := by
    intro p
    have hp : p = pairMul ((1 : Equiv.Perm (Fin 6)), p.2) (p.1, (fun _ : Fin 6 => false)) := by
      simp [pairMul]
    rw [hp, hlift_mul]
    exact W.mul_mem (hη_gen p.2) (hπ_gen p.1)
  rw [Subgroup.eq_top_iff']
  intro φ
  rw [← Equiv.symm_apply_apply σ φ]
  exact hgen_all (σ φ)

private def displacementHom {G : Type} [Group G] {Bs : Subgroup G}
    (hcomm : IsMulCommutative ↥Bs) (φ : MulAut ↥Bs) : ↥Bs →* ↥Bs where
  toFun b := b⁻¹ * φ b
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := hcomm.is_comm.comm b⁻¹ a⁻¹
    rw [h1]
    have h2 : φ a * b⁻¹ = b⁻¹ * φ a := hcomm.is_comm.comm (φ a) b⁻¹
    calc
      a⁻¹ * b⁻¹ * (φ a * φ b) = a⁻¹ * (b⁻¹ * φ a) * φ b := by group
      _ = a⁻¹ * (φ a * b⁻¹) * φ b := by rw [← h2]
      _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by group

private lemma signedB6At_u_inv {A : Type} [AddCommGroup A] {u : G → A} [Finite G]
    {z : G}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z) (b : ↥Bs) :
    u ((b⁻¹ : ↥Bs) : G) = -u (b : G) := by
  have hu1 : u 1 = 0 := (hker 1 Bs.one_mem).mpr (Subgroup.one_mem _)
  have h := hadd (b : G) b.2 ((b⁻¹ : ↥Bs) : G) b⁻¹.2
  rw [show (b : G) * ((b⁻¹ : ↥Bs) : G) = 1 by simp, hu1] at h
  rw [eq_comm] at h
  have h' : u ((b⁻¹ : ↥Bs) : G) + u (b : G) = 0 := by rw [add_comm]; exact h
  exact eq_neg_of_add_eq_zero_left h'

private lemma signedB6At_card_Bs [Finite G] (hBs : IsElemAbelian 3 Bs) {z : G} (hzBs : z ∈ Bs)
    (hz1 : z ≠ 1) {u : G → Fin 6 → ZMod 3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z)
    (hsurj : ∀ v : Fin 6 → ZMod 3, ∃ b ∈ Bs, u b = v) :
    Nat.card ↥Bs = 3 ^ 7 := by
  let uBs : ↥Bs →* Multiplicative (Fin 6 → ZMod 3) :=
    { toFun := fun b => Multiplicative.ofAdd (u b)
      map_one' := by
        apply Multiplicative.toAdd.injective
        change u 1 = 0
        exact (hker 1 Bs.one_mem).mpr (Subgroup.one_mem _)
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        change u (a * b) = u a + u b
        exact hadd a a.2 b b.2 }
  have hcard_mul : Nat.card ↥(MonoidHom.ker uBs) * Nat.card ↥(MonoidHom.range uBs) =
      Nat.card ↥Bs := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker uBs)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange uBs).toEquiv] at h
    rw [Nat.mul_comm] at h
    exact h.symm
  have hker_eq : MonoidHom.ker uBs = Subgroup.zpowers (⟨z, hzBs⟩ : ↥Bs) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    · intro h
      have h0 : u b = 0 := by
        change Multiplicative.toAdd (uBs b) = 0
        rw [h]
        rfl
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hker b b.2).mp h0)
      exact ⟨k, by apply Subtype.ext; simpa using hk⟩
    · rintro ⟨k, hk⟩
      rw [← hk]
      have hz0 : uBs (⟨z, hzBs⟩ : ↥Bs) = 1 := by
        apply Multiplicative.toAdd.injective
        change u z = 0
        exact (hker z hzBs).mpr (Subgroup.mem_zpowers z)
      rw [map_zpow, hz0]
      exact one_zpow k
  have hker_card : Nat.card ↥(MonoidHom.ker uBs) = 3 := by
    rw [hker_eq, Nat.card_zpowers]
    have hz3 : (⟨z, hzBs⟩ : ↥Bs) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hBs.2 z hzBs
    have hz1' : (⟨z, hzBs⟩ : ↥Bs) ≠ 1 := by
      intro h
      exact hz1 (by simpa [Subtype.ext_iff] using h)
    have hdvd : orderOf (⟨z, hzBs⟩ : ↥Bs) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1'
    · exact h
  have hrange_top : MonoidHom.range uBs = ⊤ := by
    rw [eq_top_iff]
    intro v hv
    obtain ⟨b, hb, hbuv⟩ := hsurj (Multiplicative.toAdd v)
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    change u b = Multiplicative.toAdd v
    exact hbuv
  rw [← hcard_mul, hker_card, hrange_top]
  have htop_card : Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 6 → ZMod 3))) =
      Nat.card (Fin 6 → ZMod 3) := by
    rw [Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (Fin 6 → ZMod 3))).toEquiv]
    rfl
  rw [htop_card, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private lemma signedB6At_u_inj_on_E [Finite G] (hBs : IsElemAbelian 3 Bs)
    {z : G} (hzBs : z ∈ Bs) {u : G → Fin 6 → ZMod 3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z)
    {h : MulAut ↥Bs} (hwz : h ⟨z, hzBs⟩ = ⟨z, hzBs⟩) (h2 : h ^ 2 = 1)
    {x y : ↥Bs} (hx : h x = x⁻¹) (hy : h y = y⁻¹) (huv : u x = u y) : x = y := by
  have h2b : ∀ b : ↥Bs, h (h b) = b := by
    intro b
    rw [← MulAut.mul_apply, ← pow_two, h2, MulAut.one_apply]
  let c : ↥Bs := x⁻¹ * y
  have hc_E : h c = c⁻¹ := by
    change h (x⁻¹ * y) = (x⁻¹ * y)⁻¹
    simp only [map_mul, map_inv, hx, hy, mul_inv_rev, inv_inv]
    exact (hBs.1.is_comm.comm x y⁻¹)
  have hx_inv' : u ((↑x)⁻¹) = -u (↑x) := by
    rw [← Subgroup.coe_inv]
    exact signedB6At_u_inv hadd hker x
  have hc_ker : u c = 0 := by
    change u (((x⁻¹ * y : ↥Bs) : G)) = 0
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hadd (x⁻¹) x⁻¹.2 y y.2, hx_inv', huv]
    abel
  have hc_zp : c ∈ Subgroup.zpowers (⟨z, hzBs⟩ : ↥Bs) := by
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hker c c.2).mp hc_ker)
    exact ⟨k, by apply Subtype.ext; simpa using hk⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_zp
  have hc_fix : h c = c := by
    rw [← hk, map_zpow, hwz]
  have hc_eq : c = c⁻¹ := hc_fix.symm.trans hc_E
  have hc2 : c ^ 2 = 1 := by
    have h : c * c⁻¹ = 1 := mul_inv_cancel c
    rw [← hc_eq] at h
    rwa [pow_two]
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    exact hBs.2 c c.2
  have hc1 : c = 1 := by
    have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have hdvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h1 : orderOf c = 1 := by
      have h : orderOf c ∣ Nat.gcd 2 3 := Nat.dvd_gcd hdvd2 hdvd3
      rw [show Nat.gcd 2 3 = 1 by norm_num] at h
      exact Nat.dvd_one.mp h
    exact orderOf_eq_one_iff.mp h1
  have hc1' : x⁻¹ * y = 1 := hc1
  have h := congrArg (fun w => x * w) hc1'
  simpa [mul_assoc] using h.symm

private lemma card_E_sgn [Finite G] (hBs : IsElemAbelian 3 Bs)
    {z : G} (hzBs : z ∈ Bs) {u : G → Fin 6 → ZMod 3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z)
    {h : MulAut ↥Bs} (hwz : h ⟨z, hzBs⟩ = ⟨z, hzBs⟩) (h2 : h ^ 2 = 1)
    {i : Fin 6} (hpair : ∀ x : ↥Bs, u (h x) = moveExp 1 (fun j => decide (j = i)) (u x)) :
    Nat.card {x : ↥Bs | h x = x⁻¹} ≤ 3 := by
  let E : Set ↥Bs := {x | h x = x⁻¹}
  have hsupp : ∀ x ∈ E, ∀ k : Fin 6, k ≠ i → u x k = 0 := by
    intro x hx k hk
    have h1 : u (h x) k = -u x k := by
      rw [hx, signedB6At_u_inv hadd hker x]
      rfl
    have h2 : u (h x) k = u x k := by
      rw [hpair x]
      simp [moveExp_apply, sgnZ, hk]
    rw [h1] at h2
    have h3 : (2 : ZMod 3) * u x k = 0 := by
      rw [show (2 : ZMod 3) * u x k = u x k + u x k by ring]
      exact (eq_neg_iff_add_eq_zero).mp h2.symm
    exact (mul_eq_zero.mp h3).resolve_left (by decide)
  have hinj : Function.Injective (fun x : E => u x.1 i) := by
    intro x y hxy
    apply Subtype.ext
    apply signedB6At_u_inj_on_E hBs hzBs hadd hker hwz h2 x.2 y.2
    funext k
    by_cases hk : k = i
    · subst hk; exact hxy
    · rw [hsupp x.1 x.2 k hk, hsupp y.1 y.2 k hk]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

private lemma card_E_swap [Finite G] (hBs : IsElemAbelian 3 Bs)
    {z : G} (hzBs : z ∈ Bs) {u : G → Fin 6 → ZMod 3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z)
    {h : MulAut ↥Bs} (hwz : h ⟨z, hzBs⟩ = ⟨z, hzBs⟩) (h2 : h ^ 2 = 1)
    {i j : Fin 6} (hij : i ≠ j)
    (hpair : ∀ x : ↥Bs, u (h x) = moveExp (Equiv.swap i j) (fun _ => false) (u x)) :
    Nat.card {x : ↥Bs | h x = x⁻¹} ≤ 3 := by
  let E : Set ↥Bs := {x | h x = x⁻¹}
  have hsupp : ∀ x ∈ E, ∀ k : Fin 6, k ≠ i → k ≠ j → u x k = 0 := by
    intro x hx k hki hkj
    have h1 : u (h x) k = -u x k := by
      rw [hx, signedB6At_u_inv hadd hker x]
      rfl
    have h2 : u (h x) k = u x k := by
      rw [hpair x]
      simp [moveExp_apply, sgnZ, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [h1] at h2
    have h3 : (2 : ZMod 3) * u x k = 0 := by
      rw [show (2 : ZMod 3) * u x k = u x k + u x k by ring]
      exact (eq_neg_iff_add_eq_zero).mp h2.symm
    exact (mul_eq_zero.mp h3).resolve_left (by decide)
  have hrel : ∀ x ∈ E, u x j = -u x i := by
    intro x hx
    have h1 : u (h x) i = -u x i := by
      rw [hx, signedB6At_u_inv hadd hker x]
      rfl
    have h2 : u (h x) i = u x j := by
      rw [hpair x]
      simp [moveExp_apply, sgnZ]
    rw [h2] at h1
    exact h1
  have hinj : Function.Injective (fun x : E => u x.1 i) := by
    intro x y hxy
    apply Subtype.ext
    apply signedB6At_u_inj_on_E hBs hzBs hadd hker hwz h2 x.2 y.2
    funext k
    by_cases hki : k = i
    · subst hki; exact hxy
    · by_cases hkj : k = j
      · subst hkj
        rw [hrel x x.2, hrel y y.2]
        exact congrArg Neg.neg hxy
      · rw [hsupp x.1 x.2 k hki hkj, hsupp y.1 y.2 k hki hkj]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

private lemma card_range_displacement_eq_three [Finite G] (hBs : IsElemAbelian 3 Bs)
    {h : MulAut ↥Bs} (h2 : h ^ 2 = 1) (hne : h ≠ 1)
    (hcardBs : Nat.card ↥Bs = 3 ^ 7)
    (hE_card : Nat.card {x : ↥Bs | h x = x⁻¹} ≤ 3) :
    Nat.card ↥(MonoidHom.range (displacementHom hBs.1 h)) = 3 := by
  let d := displacementHom hBs.1 h
  have hd_ne_bot : MonoidHom.range d ≠ ⊥ := by
    intro hbot
    apply hne
    have hd : d = 1 := (MonoidHom.range_eq_bot_iff).mp hbot
    ext b
    have : d b = 1 := by rw [hd]; rfl
    have h' := congrArg (fun x => b * x) this
    simpa [d, displacementHom] using h'
  have hrange_le_E : (MonoidHom.range d : Set ↥Bs) ⊆ {x : ↥Bs | h x = x⁻¹} := by
    rintro x ⟨b, rfl⟩
    change h (b⁻¹ * h b) = (b⁻¹ * h b)⁻¹
    have h2b : h (h b) = b := by
      rw [← MulAut.mul_apply, ← pow_two, h2, MulAut.one_apply]
    simp only [map_mul, map_inv, h2b, inv_inv, mul_inv_rev]
  have hrange_card_le : Nat.card ↥(MonoidHom.range d) ≤ 3 := by
    have hle : Nat.card ↥(MonoidHom.range d) ≤ Nat.card {x : ↥Bs | h x = x⁻¹} :=
      Nat.card_mono (Set.toFinite _) hrange_le_E
    exact le_trans hle hE_card
  have hrange_dvd : Nat.card ↥(MonoidHom.range d) ∣ 3 ^ 7 := by
    rw [← hcardBs]
    exact Subgroup.card_subgroup_dvd_card _
  have hrange_ne_one : Nat.card ↥(MonoidHom.range d) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    exact hd_ne_bot h1
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hrange_dvd
  have hk1 : k ≤ 1 := by
    by_contra hk'
    have hk2 : 2 ≤ k := by omega
    have hpow : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    rw [hk] at hrange_card_le
    norm_num at hpow
    omega
  interval_cases k
  · rw [hk] at hrange_ne_one
    norm_num at hrange_ne_one
  · rw [hk]
    norm_num

private lemma ggAutomizer_fixes_z [Finite G] {z : G} (hzBs : z ∈ Bs)
    {h : MulAut ↥Bs} (hh : h ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) :
    h ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
  obtain ⟨g, hgC, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hh
  have hgz : g * z * g⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp hgC z (by simp)
    rw [← h]; group
  exact Subtype.ext ((hφg ⟨z, hzBs⟩).trans hgz)

private lemma displacementHom_ker {G : Type} [Group G] {Bs : Subgroup G}
    (hcomm : IsMulCommutative ↥Bs) (φ : MulAut ↥Bs) (b : ↥Bs) :
    b ∈ (displacementHom hcomm φ).ker ↔ φ b = b := by
  rw [MonoidHom.mem_ker]
  change b⁻¹ * φ b = 1 ↔ φ b = b
  constructor
  · intro h
    have := congrArg (fun x => b * x) h
    simpa using this
  · intro h
    rw [h]
    exact inv_mul_cancel b

private lemma card_fix_mul_three [Finite G] {Bs : Subgroup G} (hcomm : IsMulCommutative ↥Bs)
    (φ : MulAut ↥Bs)
    (hcard_range : Nat.card ↥(MonoidHom.range (displacementHom hcomm φ)) = 3) :
    Nat.card {b : ↥Bs // φ b = b} * 3 = Nat.card ↥Bs := by
  let d := displacementHom hcomm φ
  have hcard_mul : Nat.card ↥(MonoidHom.ker d) * Nat.card ↥(MonoidHom.range d) = Nat.card ↥Bs := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker d)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv] at h
    rw [Nat.mul_comm] at h
    exact h.symm
  have hcard_ker : Nat.card ↥(MonoidHom.ker d) = Nat.card {b : ↥Bs // φ b = b} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro b
    exact displacementHom_ker hcomm φ b
  calc
    Nat.card {b : ↥Bs // φ b = b} * 3 = Nat.card ↥(MonoidHom.ker d) * 3 := by rw [hcard_ker]
    _ = Nat.card ↥(MonoidHom.ker d) * Nat.card ↥(MonoidHom.range d) := by rw [hcard_range]
    _ = Nat.card ↥Bs := hcard_mul

theorem eq_one_of_mem_ggAutomizer_of_forall_eq {A : Type} [AddCommGroup A] [Finite G]
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) {z : G} (hzBs : z ∈ Bs)
    (hz1 : z ≠ 1) {u : G → A} (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs)
    (htriv : ∀ b : ↥Bs, u ((φ b : ↥Bs) : G) = u (b : G)) : φ = 1 := by
  by_contra hφne
  obtain ⟨g, hgC, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgz : g * z * g⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp hgC z (by simp)
    rw [← h]; group
  have hφz : φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ :=
    Subtype.ext ((hφg ⟨z, hzBs⟩).trans hgz)
  let z' : ↥Bs := ⟨z, hzBs⟩
  have hφz' : φ z' = z' := hφz
  have hz3 : z' ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBs.2 z hzBs
  have hz'1 : z' ≠ 1 := by
    intro h
    exact hz1 (by simpa [z'] using h)
  have horder : orderOf z' = 3 := by
    have hdvd : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'1
    · exact h
  have hcard_zp : Nat.card ↥(Subgroup.zpowers z') = 3 := by
    rw [Nat.card_zpowers, horder]
  have hu1 : u 1 = 0 := (hker 1 Bs.one_mem).mpr (Subgroup.one_mem _)
  let d : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * φ b
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := hBs.1.is_comm.comm b⁻¹ a⁻¹
        rw [h1]
        have h2 : φ a * b⁻¹ = b⁻¹ * φ a := hBs.1.is_comm.comm (φ a) b⁻¹
        calc
          a⁻¹ * b⁻¹ * (φ a * φ b) = a⁻¹ * (b⁻¹ * φ a) * φ b := by group
          _ = a⁻¹ * (φ a * b⁻¹) * φ b := by rw [← h2]
          _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by group }
  have hu_inv : ∀ b : ↥Bs, u ((b⁻¹ : ↥Bs) : G) = -u (b : G) := by
    intro b
    have h := hadd (b : G) b.2 ((b⁻¹ : ↥Bs) : G) b⁻¹.2
    rw [show (b : G) * ((b⁻¹ : ↥Bs) : G) = 1 by simp, hu1] at h
    rw [eq_comm] at h
    have h' : u ((b⁻¹ : ↥Bs) : G) + u (b : G) = 0 := by rw [add_comm]; exact h
    exact eq_neg_of_add_eq_zero_left h'
  have hd_mem_zp : ∀ b : ↥Bs, d b ∈ Subgroup.zpowers z' := by
    intro b
    have hu_d : u ((d b : ↥Bs) : G) = 0 := by
      have h := hadd ((b⁻¹ : ↥Bs) : G) b⁻¹.2 ((φ b : ↥Bs) : G) (φ b).2
      rw [hu_inv b, htriv b] at h
      have hd : ((d b : ↥Bs) : G) = ((b⁻¹ : ↥Bs) : G) * ((φ b : ↥Bs) : G) := rfl
      rw [hd, h]
      abel
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hker ((d b : ↥Bs) : G) (d b).2).mp hu_d)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simpa using hk
  have hcard_ker : Nat.card ↥(MonoidHom.ker d) = Nat.card {b : ↥Bs // φ b = b} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro b
    rw [MonoidHom.mem_ker]
    dsimp [d]
    constructor
    · intro h
      have h' := congrArg (fun x : ↥Bs => b * x) h
      simpa using h'
    · intro h
      rw [h, inv_mul_cancel]
  have hrange_le : MonoidHom.range d ≤ Subgroup.zpowers z' := by
    rintro x ⟨b, rfl⟩
    exact hd_mem_zp b
  have hcard_range : Nat.card ↥(MonoidHom.range d) = 3 := by
    have hdvd : Nat.card ↥(MonoidHom.range d) ∣ 3 := by
      rw [← hcard_zp]
      exact Subgroup.card_dvd_of_le hrange_le
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exfalso
      rw [Subgroup.card_eq_one] at h
      rw [MonoidHom.range_eq_bot_iff] at h
      apply hφne
      ext b
      have hb : d b = 1 := by rw [h]; rfl
      have h' := congrArg (fun x : ↥Bs => b * x) hb
      simpa [d] using h'
    · exact h
  have hcard_mul : Nat.card ↥(MonoidHom.ker d) * Nat.card ↥(MonoidHom.range d) = Nat.card ↥Bs := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker d)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv] at h
    rw [Nat.mul_comm] at h
    exact h.symm
  have hfix : Nat.card {b : ↥Bs // φ b = b} * 3 = Nat.card ↥Bs := by
    rw [← hcard_ker, ← hcard_range]
    exact hcard_mul
  have hfix_zp : ∀ x ∈ Subgroup.zpowers z', φ x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, hφz']
  have htrans : GGIsTransvection 3 φ := by
    refine ⟨hfix, fun b => ?_⟩
    simpa [d] using hfix_zp (d b) (hd_mem_zp b)
  have hφ_ind : φ ∈ ggInduced ⊤ Bs := by
    have h2 : φ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ
    rw [ggAutomizer_eq] at h2
    exact h2
  exact hNT φ hφ_ind htrans

private lemma signedB6At_pairEquiv [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1)
    {u : G → Fin 6 → ZMod 3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hker : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z)
    (hsurj : ∀ v : Fin 6 → ZMod 3, ∃ b ∈ Bs, u b = v)
    (h4 : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∃ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
        ∀ b ∈ Bs, u (g * b * g⁻¹) = moveExp π η (u b))
    (h5 : ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
      ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ b ∈ Bs, u (g * b * g⁻¹) = moveExp π η (u b)) :
    ∃ σ : ↥(ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) ≃
        Equiv.Perm (Fin 6) × (Fin 6 → Bool),
      ∀ (φ : ↥(ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs)) (b : ↥Bs),
        u ((φ.1 b : ↥Bs) : G) = moveExp (σ φ).1 (σ φ).2 (u b) := by
  let Hz : Subgroup (MulAut ↥Bs) := ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs
  have hpair : ∀ φ : ↥Hz, ∃ p : Equiv.Perm (Fin 6) × (Fin 6 → Bool),
      ∀ b : ↥Bs, u ((φ.1 b : ↥Bs) : G) = moveExp p.1 p.2 (u b) := by
    intro φ
    have hφmem : φ.1 ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := φ.2
    obtain ⟨g, hgC, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφmem
    have hg : g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
      ⟨hgN, hgC⟩
    obtain ⟨π, η, hπη⟩ := h4 g hg
    refine ⟨(π, η), fun b => ?_⟩
    have h1 := hπη (b : G) b.2
    have h2 : ((φ.1 b : ↥Bs) : G) = g * (b : G) * g⁻¹ := hφg b
    rw [h2]
    exact h1
  let σ : ↥Hz → Equiv.Perm (Fin 6) × (Fin 6 → Bool) := fun φ => Classical.choose (hpair φ)
  have hσ : ∀ φ : ↥Hz, ∀ b : ↥Bs,
      u ((φ.1 b : ↥Bs) : G) = moveExp (σ φ).1 (σ φ).2 (u b) :=
    fun φ => Classical.choose_spec (hpair φ)
  have hσ_inj : Function.Injective σ := by
    intro φ ψ hφψ
    have hcomp : ∀ v : Fin 6 → ZMod 3,
        moveExp (σ (ψ⁻¹)).1 (σ (ψ⁻¹)).2 (moveExp (σ ψ).1 (σ ψ).2 v) = v := by
      intro v
      obtain ⟨b, hb, hbuv⟩ := hsurj v
      rw [← hbuv]
      have h1 : u ((ψ.1 ⟨b, hb⟩ : ↥Bs) : G) =
          moveExp (σ ψ).1 (σ ψ).2 (u (⟨b, hb⟩ : ↥Bs)) := hσ ψ ⟨b, hb⟩
      have h2 : u (((ψ⁻¹).1 (ψ.1 ⟨b, hb⟩) : ↥Bs) : G) =
          moveExp (σ (ψ⁻¹)).1 (σ (ψ⁻¹)).2 (u ((ψ.1 ⟨b, hb⟩ : ↥Bs) : G)) :=
        hσ (ψ⁻¹) (ψ.1 ⟨b, hb⟩)
      have h3 : ((ψ⁻¹).1 (ψ.1 ⟨b, hb⟩) : ↥Bs) = ⟨b, hb⟩ := by simp
      rw [h1] at h2
      rw [h3] at h2
      exact h2.symm
    have hu : ∀ b : ↥Bs, u ((((ψ⁻¹ * φ).1) b : ↥Bs) : G) = u (b : G) := by
      intro b
      have h1 : ((ψ⁻¹ * φ).1 b : ↥Bs) = (ψ⁻¹).1 (φ.1 b) := rfl
      rw [h1]
      have h2 := hσ (ψ⁻¹) (φ.1 b)
      have h3 := hσ φ b
      rw [h3] at h2
      rw [hφψ] at h2
      rw [hcomp (u b)] at h2
      exact h2
    have hψφ : (ψ⁻¹ * φ).1 ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := (ψ⁻¹ * φ).2
    have h1 : (ψ⁻¹ * φ).1 = 1 :=
      eq_one_of_mem_ggAutomizer_of_forall_eq hBs hNT hzBs hz1 hadd hker hψφ hu
    have h2 : ψ⁻¹ * φ = 1 := Subtype.ext h1
    calc
      φ = ψ * (ψ⁻¹ * φ) := by group
      _ = ψ * 1 := by rw [h2]
      _ = ψ := mul_one ψ
  have hσ_surj : Function.Surjective σ := by
    intro p
    obtain ⟨g, hg, hgact⟩ := h5 p.1 p.2
    have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := hg.1
    have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := hg.2
    let φ : ↥Hz := ⟨ggConjAut Bs hgN, ggConjAut_mem_ggAutomizer hgC hgN⟩
    refine ⟨φ, ?_⟩
    apply moveExp_injective
    funext v
    obtain ⟨b, hb, hbuv⟩ := hsurj v
    rw [← hbuv]
    have h1 : u ((φ.1 ⟨b, hb⟩ : ↥Bs) : G) =
        moveExp (σ φ).1 (σ φ).2 (u (⟨b, hb⟩ : ↥Bs)) := hσ φ ⟨b, hb⟩
    have h2 : ((φ.1 ⟨b, hb⟩ : ↥Bs) : G) = g * b * g⁻¹ :=
      ggConjAut_apply Bs hgN ⟨b, hb⟩
    rw [h2] at h1
    have h3 := hgact b hb
    rw [h3] at h1
    exact h1.symm
  exact ⟨Equiv.ofBijective σ ⟨hσ_inj, hσ_surj⟩, hσ⟩

theorem card_ggAutomizer_centralizer_of_signedB6At [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1)
    (hsgn : GGSignedB6At Bs z) :
    Nat.card (ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) = 46080 := by
  obtain ⟨u, hadd, hker, hsurj, h4, h5⟩ := hsgn
  obtain ⟨σ, hσ⟩ := signedB6At_pairEquiv hBs hNT hzBs hz1 hadd hker hsurj h4 h5
  have hcard : Nat.card (ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) =
      Nat.card (Equiv.Perm (Fin 6) × (Fin 6 → Bool)) :=
    Nat.card_congr σ
  rw [hcard, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fun]
  norm_num

theorem exists_reflection_not_mem_of_signedB6At [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1)
    (hsgn : GGSignedB6At Bs z) {K : Subgroup (MulAut ↥Bs)}
    (hK : K ≤ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs) (hKc : Nat.card K = 23040) :
    ∃ h ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs,
      h ∉ K ∧ GGIsReflection 3 h ∧ ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
  have hsgn' : GGSignedB6At Bs z := hsgn
  obtain ⟨u, hadd, hker, hsurj, h4, h5⟩ := hsgn
  let Hz : Subgroup (MulAut ↥Bs) := ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs
  obtain ⟨σ, hσ⟩ := signedB6At_pairEquiv hBs hNT hzBs hz1 hadd hker hsurj h4 h5
  let lift : Equiv.Perm (Fin 6) × (Fin 6 → Bool) → ↥Hz := σ.symm
  have hσ_lift : ∀ p, σ (lift p) = p := fun p => σ.apply_symm_apply p
  have hσ_mul : ∀ φ ψ : ↥Hz,
      σ (φ * ψ) = pairMul (σ φ) (σ ψ) := by
    intro φ ψ
    apply moveExp_injective
    funext v
    obtain ⟨b, hb, hbuv⟩ := hsurj v
    rw [← hbuv]
    have h1 : u (((φ * ψ).1 ⟨b, hb⟩ : ↥Bs) : G) =
        moveExp (σ (φ * ψ)).1 (σ (φ * ψ)).2 (u (⟨b, hb⟩ : ↥Bs)) := hσ (φ * ψ) ⟨b, hb⟩
    have h2 : u (((φ * ψ).1 ⟨b, hb⟩ : ↥Bs) : G) =
        moveExp (σ φ).1 (σ φ).2 (moveExp (σ ψ).1 (σ ψ).2 (u (⟨b, hb⟩ : ↥Bs))) := by
      rw [show ((φ * ψ).1 ⟨b, hb⟩ : ↥Bs) = φ.1 (ψ.1 ⟨b, hb⟩) from rfl]
      rw [hσ φ (ψ.1 ⟨b, hb⟩), hσ ψ ⟨b, hb⟩]
    rw [moveExp_comp] at h2
    exact h1.symm.trans h2
  have hlift_mul : ∀ p q : Equiv.Perm (Fin 6) × (Fin 6 → Bool),
      lift (pairMul p q) = lift p * lift q := by
    intro p q
    apply σ.injective
    rw [σ.apply_symm_apply, hσ_mul, σ.apply_symm_apply, σ.apply_symm_apply]
  have hσ_one : σ (1 : ↥Hz) = (1, fun _ => false) := by
    apply moveExp_injective
    funext v
    obtain ⟨b, hb, hbuv⟩ := hsurj v
    rw [← hbuv]
    have h1 : u (((1 : ↥Hz).1 ⟨b, hb⟩ : ↥Bs) : G) =
        moveExp (σ (1 : ↥Hz)).1 (σ (1 : ↥Hz)).2 (u (⟨b, hb⟩ : ↥Bs)) := hσ 1 ⟨b, hb⟩
    have h2 : ((1 : ↥Hz).1 ⟨b, hb⟩ : ↥Bs) = ⟨b, hb⟩ := rfl
    rw [h2] at h1
    have h3 : moveExp 1 (fun _ => false) (u (⟨b, hb⟩ : ↥Bs)) = u (⟨b, hb⟩ : ↥Bs) := by
      funext i
      simp [moveExp_apply, sgnZ]
    change moveExp (σ (1 : ↥Hz)).1 (σ (1 : ↥Hz)).2 (u (⟨b, hb⟩ : ↥Bs)) =
      moveExp 1 (fun _ => false) (u (⟨b, hb⟩ : ↥Bs))
    rw [h3]
    exact h1.symm
  have hlift_one : lift (1, fun _ => false) = 1 := by
    apply σ.injective
    change σ (lift (1, fun _ => false)) = σ (1 : ↥Hz)
    rw [σ.apply_symm_apply, hσ_one]
  have hcardHz : Nat.card ↥Hz = 46080 :=
    card_ggAutomizer_centralizer_of_signedB6At hBs hNT hzBs hz1 hsgn'
  have hcardK_sub : Nat.card ↥(K.subgroupOf Hz) = 23040 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv]
    exact hKc
  have hindex : (K.subgroupOf Hz).index = 2 := by
    have h := Subgroup.card_mul_index (K.subgroupOf Hz)
    rw [hcardK_sub, hcardHz] at h
    omega
  have hNormal : (K.subgroupOf Hz).Normal := Subgroup.normal_of_index_eq_two hindex
  have hconj : ∀ h ∈ Hz, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    have hk' : (⟨k, hK hk⟩ : ↥Hz) ∈ K.subgroupOf Hz := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have hconj' := hNormal.conj_mem ⟨k, hK hk⟩ hk' ⟨h, hh⟩
    rw [Subgroup.mem_subgroupOf] at hconj'
    simpa using hconj'
  let Gen : Set ↥Hz :=
    {h | ∃ i, h = lift (1, fun j => decide (j = i))} ∪
      {h | ∃ i j, i ≠ j ∧ h = lift (Equiv.swap i j, fun _ => false)}
  let W : Subgroup ↥Hz := Subgroup.closure Gen
  have hW_top : W = ⊤ := by
    have h := signedPerm_closure_eq_top σ hσ_mul hσ_one
    simpa [W, Gen, lift] using h
  have hgen_le : (∀ g ∈ Gen, g.1 ∈ K) → Hz ≤ K := by
    intro hgen
    have hGenK : Gen ⊆ (K.subgroupOf Hz : Set ↥Hz) := fun g hg => by
      change g.1 ∈ K
      exact hgen g hg
    have hWle : W ≤ K.subgroupOf Hz := (Subgroup.closure_le (K.subgroupOf Hz)).mpr hGenK
    have htop : (⊤ : Subgroup ↥Hz) ≤ K.subgroupOf Hz := hW_top ▸ hWle
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥Hz) ∈ K.subgroupOf Hz := htop (Subgroup.mem_top _)
    rwa [Subgroup.mem_subgroupOf] at hx'
  have hgen_out : ∃ g ∈ Gen, g.1 ∉ K := by
    by_contra h
    have hgen : ∀ g ∈ Gen, g.1 ∈ K := by
      intro g hg
      by_contra hgK
      exact h ⟨g, hg, hgK⟩
    have hHzleK : Hz ≤ K := hgen_le hgen
    have hcard_le : Nat.card ↥Hz ≤ Nat.card ↥K := Subgroup.card_le_of_le hHzleK
    rw [hcardHz, hKc] at hcard_le
    omega
  obtain ⟨g, hgGen, hgK⟩ := hgen_out
  let h : MulAut ↥Bs := g.1
  have hhHz : h ∈ Hz := g.2
  have hhK : h ∉ K := hgK
  have hhne : h ≠ 1 := by
    intro h1
    exact hhK (h1 ▸ K.one_mem)
  have hsq : h ^ 2 = 1 := by
    have hg2 : g * g = 1 := by
      have h1 : σ (g * g) = (1, fun _ => false) := by
        rw [hσ_mul]
        rcases hgGen with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
        · rw [σ.apply_symm_apply]
          apply Prod.ext
          · simp [pairMul]
          · funext k
            simp [pairMul, Bool.xor]
            rfl
        · rw [σ.apply_symm_apply]
          apply Prod.ext
          · simp [pairMul, Equiv.swap_mul_self]
          · funext k
            simp [pairMul]
      rw [← show σ (1 : ↥Hz) = (1, fun _ => false) from hσ_one] at h1
      exact σ.injective h1
    have hval : g.1 * g.1 = 1 := by
      have := congrArg Subtype.val hg2
      simpa using this
    rw [pow_two]
    exact hval
  have hfix : Nat.card {b : ↥Bs // h b = b} * 3 = Nat.card ↥Bs := by
    have hcardBs : Nat.card ↥Bs = 3 ^ 7 :=
      signedB6At_card_Bs hBs hzBs hz1 hadd hker hsurj
    have hwz : h ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := ggAutomizer_fixes_z hzBs hhHz
    rcases hgGen with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have hpair : ∀ x : ↥Bs, u (h x) = moveExp 1 (fun k => decide (k = i)) (u x) := by
        intro x
        change u (((lift (1, fun k => decide (k = i))).1 x : ↥Bs) : G) =
          moveExp 1 (fun k => decide (k = i)) (u x)
        rw [hσ]
        rw [σ.apply_symm_apply]
      have hE_card := card_E_sgn hBs hzBs hadd hker hwz hsq hpair
      have hrange := card_range_displacement_eq_three hBs hsq hhne hcardBs hE_card
      exact card_fix_mul_three hBs.1 h hrange
    · have hpair : ∀ x : ↥Bs, u (h x) = moveExp (Equiv.swap i j) (fun _ => false) (u x) := by
        intro x
        change u (((lift (Equiv.swap i j, fun _ => false)).1 x : ↥Bs) : G) =
          moveExp (Equiv.swap i j) (fun _ => false) (u x)
        rw [hσ]
        rw [σ.apply_symm_apply]
      have hE_card := card_E_swap hBs hzBs hadd hker hwz hsq hij hpair
      have hrange := card_range_displacement_eq_three hBs hsq hhne hcardBs hE_card
      exact card_fix_mul_three hBs.1 h hrange
  exact ⟨h, hhHz, hhK, ⟨hsq, hfix⟩, hconj h hhHz⟩

end CFSG.StandardType.FrameRoute

end
