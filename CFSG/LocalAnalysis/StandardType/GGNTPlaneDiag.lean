module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases

public section

namespace CFSG.StandardType.NTPlane

@[expose] def cycConjDiag {G : Type*} [Group G] (y r : G) : G :=
  r * (y * r * y⁻¹) * (y ^ 2 * r * (y ^ 2)⁻¹)

private theorem comm_first_third {G : Type*} [Group G] {y : G} (hy3 : y ^ 3 = 1) {R : Subgroup G}
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (y * s * y⁻¹)) {r s : G} (hr : r ∈ R) (hs : s ∈ R) :
    Commute r (y ^ 2 * s * (y ^ 2)⁻¹) := by
  have hy : y ^ 2 = y⁻¹ := by
    have : y ^ 2 * y = 1 := by rw [← pow_succ, hy3]
    exact eq_inv_of_mul_eq_one_left this
  have h : Commute (y * r * y⁻¹) s := (hcomm s hs r hr).symm
  have h2 := Commute.map h (MulAut.conj y⁻¹).toMonoidHom
  have e1 : (MulAut.conj y⁻¹).toMonoidHom (y * r * y⁻¹) = r := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have e2 : (MulAut.conj y⁻¹).toMonoidHom s = y⁻¹ * s * y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [e1, e2] at h2
  rw [hy]
  simpa only [inv_inv] using h2

private theorem comm_second_third {G : Type*} [Group G] {y : G} (hy3 : y ^ 3 = 1) {R : Subgroup G}
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (y * s * y⁻¹)) {r s : G} (hr : r ∈ R) (hs : s ∈ R) :
    Commute (y * r * y⁻¹) (y ^ 2 * s * (y ^ 2)⁻¹) := by
  have h := Commute.map (hcomm r hr s hs) (MulAut.conj y).toMonoidHom
  have e1 : (MulAut.conj y).toMonoidHom r = y * r * y⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e2 : (MulAut.conj y).toMonoidHom (y * s * y⁻¹) = y ^ 2 * s * (y ^ 2)⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two, mul_inv_rev]; group
  rw [e1, e2] at h
  exact h

theorem cycConjDiag_mul {G : Type*} [Group G] (y : G) (R : Subgroup G) (hy3 : y ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (y * s * y⁻¹)) {r s : G} (hr : r ∈ R) (hs : s ∈ R) :
    cycConjDiag y (r * s) = cycConjDiag y r * cycConjDiag y s := by
  have e : cycConjDiag y (r * s) = (r * s) * ((y * r * y⁻¹) * (y * s * y⁻¹)) *
      ((y ^ 2 * r * (y ^ 2)⁻¹) * (y ^ 2 * s * (y ^ 2)⁻¹)) := by
    unfold cycConjDiag; group
  rw [e]
  unfold cycConjDiag
  have h1 : Commute s (y * r * y⁻¹) := hcomm s hs r hr
  have h2 : Commute s (y ^ 2 * r * (y ^ 2)⁻¹) := comm_first_third hy3 hcomm hs hr
  have h3 : Commute (y * s * y⁻¹) (y ^ 2 * r * (y ^ 2)⁻¹) := comm_second_third hy3 hcomm hs hr
  generalize y * r * y⁻¹ = r2 at *
  generalize y * s * y⁻¹ = s2 at *
  generalize y ^ 2 * r * (y ^ 2)⁻¹ = r3 at *
  generalize y ^ 2 * s * (y ^ 2)⁻¹ = s3 at *
  calc r * s * (r2 * s2) * (r3 * s3) = r * (s * r2) * (s2 * r3) * s3 := by group
    _ = r * (r2 * s) * (r3 * s2) * s3 := by rw [h1.eq, h3.eq]
    _ = r * r2 * (s * r3) * s2 * s3 := by group
    _ = r * r2 * (r3 * s) * s2 * s3 := by rw [h2.eq]
    _ = r * r2 * r3 * (s * s2 * s3) := by group

theorem cycConjDiag_conj {G : Type*} [Group G] (y : G) (R : Subgroup G) (hy3 : y ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (y * s * y⁻¹)) {r : G} (hr : r ∈ R) :
    y * cycConjDiag y r * y⁻¹ = cycConjDiag y r := by
  have e : y * cycConjDiag y r * y⁻¹ = (y * r * y⁻¹) * (y ^ 2 * r * (y ^ 2)⁻¹) *
      (y ^ 3 * r * (y ^ 3)⁻¹) := by
    unfold cycConjDiag; group
  rw [e, hy3]
  have h1 : Commute r (y * r * y⁻¹) := hcomm r hr r hr
  have h2 : Commute r (y ^ 2 * r * (y ^ 2)⁻¹) := comm_first_third hy3 hcomm hr hr
  unfold cycConjDiag
  generalize y * r * y⁻¹ = r2 at *
  generalize y ^ 2 * r * (y ^ 2)⁻¹ = r3 at *
  calc r2 * r3 * (1 * r * 1⁻¹) = r2 * (r3 * r) := by group
    _ = r2 * (r * r3) := by rw [h2.eq]
    _ = (r2 * r) * r3 := by group
    _ = (r * r2) * r3 := by rw [h1.eq]
    _ = r * r2 * r3 := rfl

theorem eq_cycConjDiag_mul_of_commute {G : Type*} [Group G] (y : G)
    (R Z : Subgroup G) (hy3 : y ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, Commute r (y * s * y⁻¹))
    (hZc : ∀ z ∈ Z, ∀ r ∈ R,
      Commute z r ∧ Commute z (y * r * y⁻¹) ∧ Commute z (y ^ 2 * r * (y ^ 2)⁻¹))
    (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z)
    (hov : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ r₃ ∈ R,
      r₁ * (y * r₂ * y⁻¹) * (y ^ 2 * r₃ * (y ^ 2)⁻¹) = 1 →
        r₁ ∈ Z ∧ y * r₂ * y⁻¹ ∈ Z ∧ y ^ 2 * r₃ * (y ^ 2)⁻¹ ∈ Z)
    {g : G} (hg : ∃ a ∈ R, ∃ b ∈ R, ∃ c ∈ R,
      g = a * (y * b * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹))
    (hgy : y * g * y⁻¹ = g) :
    ∃ a ∈ R, ∃ z ∈ Z, g = cycConjDiag y a * z := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hg
  have hcP : Commute c (y * a * y⁻¹) := hcomm c hc a ha
  have hcC' : Commute c (y ^ 2 * b * (y ^ 2)⁻¹) := comm_first_third hy3 hcomm hc hb
  have haP : Commute a (y * a * y⁻¹) := hcomm a ha a ha
  have haC' : Commute a (y ^ 2 * b * (y ^ 2)⁻¹) := comm_first_third hy3 hcomm ha hb
  have hPC' : Commute (y * a * y⁻¹) (y ^ 2 * b * (y ^ 2)⁻¹) :=
    comm_second_third hy3 hcomm ha hb
  have hBC' : Commute (y * b * y⁻¹) (y ^ 2 * b * (y ^ 2)⁻¹) :=
    comm_second_third hy3 hcomm hb hb
  have hE1 : (y * a * y⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹) * c =
      a * (y * b * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹) := by
    have e : y * (a * (y * b * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹)) * y⁻¹ =
        (y * a * y⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹) * (y ^ 3 * c * (y ^ 3)⁻¹) := by group
    rw [e, hy3] at hgy
    simpa using hgy
  have hrel : (c⁻¹ * a) * (y * (a⁻¹ * b) * y⁻¹) * (y ^ 2 * (b⁻¹ * c) * (y ^ 2)⁻¹) = 1 := by
    have e1 : y * (a⁻¹ * b) * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹) := by group
    have e2 : y ^ 2 * (b⁻¹ * c) * (y ^ 2)⁻¹ =
        (y ^ 2 * b * (y ^ 2)⁻¹)⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹) := by group
    rw [e1, e2]
    generalize y * a * y⁻¹ = P at *
    generalize y * b * y⁻¹ = B at *
    generalize y ^ 2 * b * (y ^ 2)⁻¹ = C' at *
    generalize y ^ 2 * c * (y ^ 2)⁻¹ = C at *
    have hMa : Commute a (P * C') := haP.mul_right haC'
    have hMc : Commute c (P * C') := hcP.mul_right hcC'
    have hMX : P * C' * (P⁻¹ * B * (C'⁻¹ * C)) = B * C := by
      calc P * C' * (P⁻¹ * B * (C'⁻¹ * C)) = (P * C' * P⁻¹) * B * C'⁻¹ * C := by group
        _ = C' * B * C'⁻¹ * C := by rw [hPC'.mul_inv_cancel]
        _ = B * C := by rw [hBC'.symm.mul_inv_cancel]
    have hBC : B * C = a⁻¹ * (P * C' * c) := by
      rw [hE1]; group
    have hX : P⁻¹ * B * (C'⁻¹ * C) = (P * C')⁻¹ * (a⁻¹ * (P * C' * c)) := by
      rw [← hBC, ← hMX]; group
    calc c⁻¹ * a * (P⁻¹ * B) * (C'⁻¹ * C) = c⁻¹ * a * (P⁻¹ * B * (C'⁻¹ * C)) := by group
      _ = c⁻¹ * a * ((P * C')⁻¹ * (a⁻¹ * (P * C' * c))) := by rw [hX]
      _ = c⁻¹ * (a * (P * C')⁻¹ * a⁻¹) * (P * C') * c := by group
      _ = c⁻¹ * (P * C')⁻¹ * (P * C') * c := by rw [hMa.inv_right.mul_inv_cancel]
      _ = 1 := by group
  obtain ⟨-, hE, hF⟩ := hov _ (R.mul_mem (R.inv_mem hc) ha) _ (R.mul_mem (R.inv_mem ha) hb) _
    (R.mul_mem (R.inv_mem hb) hc) hrel
  have hyE : y * (y * (a⁻¹ * b) * y⁻¹) * y⁻¹ ∈ Z := hyZ _ hE
  refine ⟨a, ha, (y * (a⁻¹ * b) * y⁻¹) * ((y * (y * (a⁻¹ * b) * y⁻¹) * y⁻¹) *
    (y ^ 2 * (b⁻¹ * c) * (y ^ 2)⁻¹)), ?_, ?_⟩
  · exact Z.mul_mem hE (Z.mul_mem hyE hF)
  · have hxu : Commute ((y ^ 2 * a * (y ^ 2)⁻¹)⁻¹) (y * (a⁻¹ * b) * y⁻¹) :=
      ((hZc _ hE a ha).2.2).inv_right.symm
    have h1 : (cycConjDiag y a)⁻¹ * (a * (y * b * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹)) =
        (y ^ 2 * a * (y ^ 2)⁻¹)⁻¹ * (y * (a⁻¹ * b) * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹) := by
      unfold cycConjDiag; group
    have h2 : (y ^ 2 * a * (y ^ 2)⁻¹)⁻¹ * (y * (a⁻¹ * b) * y⁻¹) * (y ^ 2 * c * (y ^ 2)⁻¹) =
        (y * (a⁻¹ * b) * y⁻¹) * ((y ^ 2 * a * (y ^ 2)⁻¹)⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹)) := by
      rw [hxu.eq, mul_assoc]
    have h3 : (y ^ 2 * a * (y ^ 2)⁻¹)⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹) =
        (y * (y * (a⁻¹ * b) * y⁻¹) * y⁻¹) * (y ^ 2 * (b⁻¹ * c) * (y ^ 2)⁻¹) := by
      simp only [pow_two, mul_inv_rev]; group
    rw [h3] at h2
    have h4 := h1.trans h2
    exact inv_mul_eq_iff_eq_mul.mp h4

theorem exists_equiv_finRotate {α : Type*} [Fintype α] (hcard : Fintype.card α = 3)
    (σ : Equiv.Perm α) (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) :
    ∃ e : Fin 3 ≃ α, ∀ k : Fin 3, σ (e k) = e (finRotate 3 k) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, σ i₀ ≠ i₀ := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have h3i : σ (σ (σ i₀)) = i₀ := by
    have := congrArg (fun f : Equiv.Perm α => f i₀) hσ3
    simpa [pow_succ, pow_two] using this
  have h20 : i₀ ≠ σ (σ i₀) := by
    intro h
    have h' : σ i₀ = σ (σ (σ i₀)) := congrArg σ h
    rw [h3i] at h'
    exact hi₀ h'
  have h2 : σ i₀ ≠ σ (σ i₀) := fun h => hi₀ (σ.injective h).symm
  let f : Fin 3 → α := ![i₀, σ i₀, σ (σ i₀)]
  have hf0 : f 0 = i₀ := rfl
  have hf1 : f 1 = σ i₀ := rfl
  have hf2 : f 2 = σ (σ i₀) := rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, by rw [Fintype.card_fin]; exact hcard.symm⟩
  refine ⟨Equiv.ofBijective f hfbij, ?_⟩
  have hr0 : finRotate 3 0 = 1 := by decide
  have hr1 : finRotate 3 1 = 2 := by decide
  have hr2 : finRotate 3 2 = 0 := by decide
  intro k
  fin_cases k <;> simp [f, hr0, hr1, hr2, h3i]

theorem exists_eq_cycConjDiag_mul_of_fixed {G : Type*} [Group G] (n : G) (hn3 : n ^ 3 = 1)
    {R : Fin 3 → Subgroup G}
    (hcomm : ∀ k l : Fin 3, k ≠ l → ∀ x ∈ R k, ∀ z ∈ R l, Commute x z)
    (hconj : ∀ k : Fin 3, (R k).map (MulAut.conj n).toMonoidHom = R (finRotate 3 k))
    {g : G} (hgE : g ∈ ⨆ k : Fin 3, R k) (hgn : n * g * n⁻¹ = g) :
    ∃ a ∈ R 0, ∃ z ∈ (⨆ k : Fin 3, R k) ⊓
        Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G),
      g = cycConjDiag n a * z := by
  have hr0 : finRotate 3 0 = 1 := by decide
  have hr1 : finRotate 3 1 = 2 := by decide
  have hr2 : finRotate 3 2 = 0 := by decide
  have hrot_ne : ∀ j : Fin 3, finRotate 3 j ≠ j := by intro j; fin_cases j <;> decide
  have hrot_ne' : ∀ j : Fin 3, finRotate 3 (finRotate 3 j) ≠ j := by
    intro j; fin_cases j <;> decide
  have hE : (⨆ k : Fin 3, R k) = R 0 ⊔ R 1 ⊔ R 2 := by
    refine le_antisymm (iSup_le ?_) (sup_le (sup_le ?_ ?_) ?_)
    · intro k; fin_cases k
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact le_iSup (fun k : Fin 3 => R k) 0
    · exact le_iSup (fun k : Fin 3 => R k) 1
    · exact le_iSup (fun k : Fin 3 => R k) 2
  have hR0E : R 0 ≤ (⨆ k : Fin 3, R k) := le_iSup (fun k : Fin 3 => R k) 0
  have hR1E : R 1 ≤ (⨆ k : Fin 3, R k) := le_iSup (fun k : Fin 3 => R k) 1
  have hR2E : R 2 ≤ (⨆ k : Fin 3, R k) := le_iSup (fun k : Fin 3 => R k) 2
  have hshift : ∀ (k : Fin 3) {r : G}, r ∈ R k → n * r * n⁻¹ ∈ R (finRotate 3 k) := by
    intro k r hr
    have h1 : n * r * n⁻¹ ∈ (R k).map (MulAut.conj n).toMonoidHom :=
      ⟨r, hr, by simp [MulAut.conj_apply]⟩
    rwa [hconj k] at h1
  have hnE : (⨆ k : Fin 3, R k).map (MulAut.conj n).toMonoidHom = ⨆ k : Fin 3, R k := by
    rw [hE, Subgroup.map_sup, Subgroup.map_sup, hconj 0, hconj 1, hconj 2, hr0, hr1, hr2]
    ac_rfl
  have hrot_ne2 : ∀ j : Fin 3, finRotate 3 j ≠ finRotate 3 (finRotate 3 j) :=
    fun j h => hrot_ne j ((finRotate 3).injective h).symm
  have hcent_pair : ∀ {k l : Fin 3}, k ≠ l → R k ≤ Subgroup.centralizer (R l : Set G) := by
    intro k l hkl x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm k l hkl x hx y hy).symm.eq
  have hdecomp : ∀ {H K : Subgroup G}, H ≤ Subgroup.centralizer (K : Set G) →
      ∀ x ∈ (H ⊔ K : Subgroup G), ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
    intro H K hHK x hx
    have hN : H ≤ Subgroup.normalizer K :=
      hHK.trans (Subgroup.centralizer_le_normalizer (K : Set G))
    have hx' : x ∈ (↑(H ⊔ K) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H K hN] at hx'
    exact Set.mem_mul.mp hx'
  have hcent_of : ∀ (j : Fin 3) (z : G), z ∈ R j →
      z ∈ (R (finRotate 3 j) ⊔ R (finRotate 3 (finRotate 3 j)) : Subgroup G) →
      ∀ x ∈ (⨆ k : Fin 3, R k), Commute x z := by
    intro j z hzj hzother x hx
    refine Subgroup.iSup_induction (fun k : Fin 3 => R k) (C := fun y => Commute y z)
      hx ?_ ?_ ?_
    · intro k y hy
      by_cases hkj : k = j
      · rw [hkj] at hy
        obtain ⟨z1, hz1, z2, hz2, hzz⟩ :=
          hdecomp (hcent_pair (k := finRotate 3 j) (l := finRotate 3 (finRotate 3 j))
            (hrot_ne2 j)) z hzother
        rw [← hzz]
        exact ((hcomm _ j (hrot_ne j) z1 hz1 y hy).symm).mul_right
          ((hcomm _ j (hrot_ne' j) z2 hz2 y hy).symm)
      · exact (hcomm j k (Ne.symm hkj) z hzj y hy).symm
    · exact Commute.one_left z
    · intro a b ha hb; exact ha.mul_left hb
  have hZc : ∀ z ∈ (⨆ k : Fin 3, R k) ⊓
      Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G), ∀ r ∈ R 0,
      Commute z r ∧ Commute z (n * r * n⁻¹) ∧ Commute z (n ^ 2 * r * (n ^ 2)⁻¹) := by
    intro z hz r hr
    obtain ⟨hzE, hzc⟩ := Subgroup.mem_inf.mp hz
    have hnr : n * r * n⁻¹ ∈ R 1 := by
      have := hshift 0 hr; rwa [hr0] at this
    have hn2r : n ^ 2 * r * (n ^ 2)⁻¹ ∈ R 2 := by
      have h1 : n * (n * r * n⁻¹) * n⁻¹ ∈ R (finRotate 3 1) := hshift 1 hnr
      rw [hr1] at h1
      have he : n ^ 2 * r * (n ^ 2)⁻¹ = n * (n * r * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      rwa [he]
    refine ⟨(Subgroup.mem_centralizer_iff.mp hzc r (hR0E hr)).symm,
      (Subgroup.mem_centralizer_iff.mp hzc _ (hR1E hnr)).symm,
      (Subgroup.mem_centralizer_iff.mp hzc _ (hR2E hn2r)).symm⟩
  have hyZ : ∀ z ∈ (⨆ k : Fin 3, R k) ⊓
      Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G),
      n * z * n⁻¹ ∈ (⨆ k : Fin 3, R k) ⊓
        Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G) := by
    intro z hz
    obtain ⟨hzE, hzc⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : (MulAut.conj n) z ∈ (⨆ k : Fin 3, R k).map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hzE
      have h2 : (MulAut.conj n) z ∈ ⨆ k : Fin 3, R k := by rwa [hnE] at h1
      simpa [MulAut.conj_apply] using h2
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxn : n⁻¹ * x * n ∈ ⨆ k : Fin 3, R k := by
        have h1 : x ∈ (⨆ k : Fin 3, R k).map (MulAut.conj n).toMonoidHom := by
          rw [hnE]; exact hx
        rw [Subgroup.mem_map] at h1
        obtain ⟨u, hu, hueq⟩ := h1
        have hueq' : n * u * n⁻¹ = x := by simpa [MulAut.conj_apply] using hueq
        have : u = n⁻¹ * x * n := by
          calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
            _ = n⁻¹ * x * n := by rw [hueq']
        rwa [this] at hu
      have hzxn : Commute z (n⁻¹ * x * n) :=
        (Subgroup.mem_centralizer_iff.mp hzc _ hxn).symm
      have h3 : Commute (n * z * n⁻¹) x := by
        have h := hzxn.map (MulAut.conj n).toMonoidHom
        have e1 : (MulAut.conj n).toMonoidHom z = n * z * n⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e2 : (MulAut.conj n).toMonoidHom (n⁻¹ * x * n) = x := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
        rwa [e1, e2] at h
      exact h3.symm
  have hov : ∀ r₁ ∈ R 0, ∀ r₂ ∈ R 0, ∀ r₃ ∈ R 0,
      r₁ * (n * r₂ * n⁻¹) * (n ^ 2 * r₃ * (n ^ 2)⁻¹) = 1 →
        r₁ ∈ (⨆ k : Fin 3, R k) ⊓ Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G) ∧
        n * r₂ * n⁻¹ ∈ (⨆ k : Fin 3, R k) ⊓
          Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G) ∧
        n ^ 2 * r₃ * (n ^ 2)⁻¹ ∈ (⨆ k : Fin 3, R k) ⊓
          Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G) := by
    intro r1 hm1 r2 hm2 r3 hm3 hrel
    have hnr2 : n * r2 * n⁻¹ ∈ R 1 := by
      have := hshift 0 hm2; rwa [hr0] at this
    have hn2r3 : n ^ 2 * r3 * (n ^ 2)⁻¹ ∈ R 2 := by
      have h1 : n * (n * r3 * n⁻¹) * n⁻¹ ∈ R (finRotate 3 1) := hshift 1 (by
        have := hshift 0 hm3; rwa [hr0] at this)
      rw [hr1] at h1
      have he : n ^ 2 * r3 * (n ^ 2)⁻¹ = n * (n * r3 * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      rwa [he]
    have hrel' : r1 * ((n * r2 * n⁻¹) * (n ^ 2 * r3 * (n ^ 2)⁻¹)) = 1 := by
      rw [mul_assoc] at hrel; exact hrel
    have e1 : r1 = ((n * r2 * n⁻¹) * (n ^ 2 * r3 * (n ^ 2)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_left hrel'
    have hX : (n * r2 * n⁻¹) * (n ^ 2 * r3 * (n ^ 2)⁻¹) = r1⁻¹ := by rw [e1, inv_inv]
    have e2 : n * r2 * n⁻¹ = r1⁻¹ * (n ^ 2 * r3 * (n ^ 2)⁻¹)⁻¹ := by rw [← hX]; group
    have e3 : n ^ 2 * r3 * (n ^ 2)⁻¹ = (r1 * (n * r2 * n⁻¹))⁻¹ := by
      have h3 : r1 * (n * r2 * n⁻¹) = (n ^ 2 * r3 * (n ^ 2)⁻¹)⁻¹ :=
        mul_eq_one_iff_eq_inv.mp hrel
      rw [h3, inv_inv]
    refine ⟨Subgroup.mem_inf.mpr ⟨hR0E hm1, ?_⟩, Subgroup.mem_inf.mpr ⟨hR1E hnr2, ?_⟩,
      Subgroup.mem_inf.mpr ⟨hR2E hn2r3, ?_⟩⟩
    · have hzo : r1 ∈ (R (finRotate 3 0) ⊔ R (finRotate 3 (finRotate 3 0)) : Subgroup G) := by
        rw [e1, hr0, hr1]
        exact Subgroup.inv_mem (R 1 ⊔ R 2) ((R 1 ⊔ R 2).mul_mem
          (Subgroup.mem_sup_left hnr2) (Subgroup.mem_sup_right hn2r3))
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent_of 0 r1 hm1 hzo x hx).eq
    · have hzo : n * r2 * n⁻¹ ∈
          (R (finRotate 3 1) ⊔ R (finRotate 3 (finRotate 3 1)) : Subgroup G) := by
        rw [e2, hr1, hr2]
        exact (R 2 ⊔ R 0).mul_mem
          (Subgroup.mem_sup_right ((R 0).inv_mem hm1))
          (Subgroup.mem_sup_left ((R 2).inv_mem hn2r3))
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent_of 1 _ hnr2 hzo x hx).eq
    · have hzo : n ^ 2 * r3 * (n ^ 2)⁻¹ ∈
          (R (finRotate 3 2) ⊔ R (finRotate 3 (finRotate 3 2)) : Subgroup G) := by
        rw [e3, hr2, hr0]
        exact Subgroup.inv_mem (R 0 ⊔ R 1) ((R 0 ⊔ R 1).mul_mem
          (Subgroup.mem_sup_left hm1) (Subgroup.mem_sup_right hnr2))
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent_of 2 _ hn2r3 hzo x hx).eq
  rw [hE] at hgE
  have hsup02 : R 0 ⊔ R 1 ≤ Subgroup.centralizer (R 2 : Set G) :=
    sup_le (hcent_pair (k := 0) (l := 2) (by decide))
      (hcent_pair (k := 1) (l := 2) (by decide))
  obtain ⟨x, hx, u2, hu2, hxu2⟩ := hdecomp hsup02 g hgE
  obtain ⟨u0, hu0, u1, hu1, hu01⟩ := hdecomp (hcent_pair (k := 0) (l := 1) (by decide)) x hx
  have hg : g = u0 * u1 * u2 := by rw [← hxu2, ← hu01]
  have hb : ∃ b ∈ R 0, n * b * n⁻¹ = u1 := by
    have h1 : u1 ∈ (R 0).map (MulAut.conj n).toMonoidHom := by rw [hconj 0, hr0]; exact hu1
    rw [Subgroup.mem_map] at h1
    obtain ⟨b, hb, hbb⟩ := h1
    exact ⟨b, hb, by simpa [MulAut.conj_apply] using hbb⟩
  obtain ⟨b, hb, hb1⟩ := hb
  have hv : ∃ v ∈ R 1, n * v * n⁻¹ = u2 := by
    have h1 : u2 ∈ (R 1).map (MulAut.conj n).toMonoidHom := by rw [hconj 1, hr1]; exact hu2
    rw [Subgroup.mem_map] at h1
    obtain ⟨v, hv, hvv⟩ := h1
    exact ⟨v, hv, by simpa [MulAut.conj_apply] using hvv⟩
  obtain ⟨v, hv, hv1⟩ := hv
  have hc : ∃ c ∈ R 0, n * c * n⁻¹ = v := by
    have h1 : v ∈ (R 0).map (MulAut.conj n).toMonoidHom := by rw [hconj 0, hr0]; exact hv
    rw [Subgroup.mem_map] at h1
    obtain ⟨c, hc, hcc⟩ := h1
    exact ⟨c, hc, by simpa [MulAut.conj_apply] using hcc⟩
  obtain ⟨c, hc, hc1⟩ := hc
  have hu2' : u2 = n ^ 2 * c * (n ^ 2)⁻¹ := by rw [← hv1, ← hc1, pow_two]; group
  obtain ⟨a, ha, z, hz, hgaz⟩ :=
    eq_cycConjDiag_mul_of_commute n (R 0) ((⨆ k : Fin 3, R k) ⊓
      Subgroup.centralizer (↑(⨆ k : Fin 3, R k) : Set G)) hn3
      (fun r hr s hs => hcomm 0 1 (by decide) r hr (n * s * n⁻¹)
        (by have := hshift 0 hs; rwa [hr0] at this))
      hZc hyZ hov (⟨u0, hu0, b, hb, c, hc, by rw [hg, ← hb1, hu2']⟩) hgn
  exact ⟨a, ha, z, hz, hgaz⟩

end CFSG.StandardType.NTPlane

end
