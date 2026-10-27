module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.Q1327T.GlueWeyl
public import CFSG.RankThree.PartOne.Q1327C.BBase

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327C

variable {G : Type} [Group G]

theorem eq_inv_of_central_involution {X F : Subgroup G} (hcomm : ∀ a b : F, a * b = b * a)
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F X B → B = ⊥ ∨ B = F)
    {z : MulAut F} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : ∀ g ∈ torusImage F X, g * z = z * g) : ∀ e : F, z e = e⁻¹ := by
  let B : Subgroup F :=
    { carrier := {e | z e = e}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
        rw [ha] }
  have hBinv : ∀ g ∈ torusImage F X, ∀ b ∈ B, g b ∈ B := by
    intro g hg b hb
    have h1 := congrArg (fun m : MulAut F => m b) (hcen g hg)
    simp only [MulAut.mul_apply] at h1
    have hb' : z b = b := hb
    show z (g b) = g b
    rw [← h1, hb']
  have hB : B = ⊥ := by
    by_contra hne
    have htop := eq_top_of_torusImage_invariant hirr hBinv hne
    apply hz1
    refine MulEquiv.ext fun e => ?_
    have : e ∈ B := htop ▸ Subgroup.mem_top e
    exact this
  intro e
  have hzz : z (z e) = e := by
    have := congrArg (fun m : MulAut F => m e) hz2
    simpa [MulAut.mul_apply] using this
  have hmem : e * z e ∈ B := by
    show z (e * z e) = e * z e
    rw [map_mul, hzz, hcomm]
  rw [hB, Subgroup.mem_bot] at hmem
  exact eq_inv_of_mul_eq_one_right hmem

theorem exists_pow_prod_of_independent {M : Type} [CommGroup M] [Finite M] {p : ℕ}
    [Fact p.Prime] (hcard : Nat.card M = p ^ 3) (e : Fin 3 → M)
    (hind : ∀ a b c : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c = 1 →
      (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) :
    ∀ x : M, ∃ a b c : ℕ, x = e 0 ^ a * e 1 ^ b * e 2 ^ c := by
  classical
  let g : Fin p × Fin p × Fin p → M := fun x =>
    e 0 ^ (x.1 : ℕ) * e 1 ^ (x.2.1 : ℕ) * e 2 ^ (x.2.2 : ℕ)
  have hdvd : ∀ a a' : Fin p, (p : ℤ) ∣ ((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ) → a = a' := by
    intro a a' h
    have h0 : ((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h
      have h1 := a.2
      have h2 := a'.2
      rw [abs_lt]
      constructor <;> omega
    exact Fin.ext (by omega)
  have hg : Function.Injective g := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h1 : e 0 ^ (((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ)) * e 1 ^ (((b : ℕ) : ℤ) - ((b' : ℕ) : ℤ)) *
        e 2 ^ (((c : ℕ) : ℤ) - ((c' : ℕ) : ℤ)) = 1 := by
      calc e 0 ^ (((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ)) * e 1 ^ (((b : ℕ) : ℤ) - ((b' : ℕ) : ℤ)) *
            e 2 ^ (((c : ℕ) : ℤ) - ((c' : ℕ) : ℤ)) = g (a, b, c) / g (a', b', c') := by
            simp only [g, zpow_sub, zpow_natCast, div_eq_mul_inv, mul_inv]
            ac_rfl
        _ = 1 := div_eq_one.2 h
    obtain ⟨d1, d2, d3⟩ := hind _ _ _ h1
    rw [hdvd a a' d1, hdvd b b' d2, hdvd c c' d3]
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_prod, Nat.card_prod, Nat.card_fin]
    exact (by ring : p ^ 3 = p * (p * p)).le)
  intro x
  obtain ⟨⟨a, b, c⟩, hx⟩ := hbij.2 x
  exact ⟨a, b, c, hx.symm⟩

variable [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem false_of_signed_permM (h : Q1327.T123Base p X A₀ F)
    (hneg : ∀ φ ∈ torusImage F X, ∃ f : F, φ f ≠ f⁻¹)
    (e w : Fin 3 → ↥X ⧸ Subgroup.center ↥X)
    (heE : ∀ j, e j ∈ bar X F)
    (hind : ∀ a b c : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c = 1 →
      (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c)
    (hwN : ∀ i, w i ∈ Subgroup.normalizer ((bar X F : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X)))
    (hwe : ∀ i j, w i * e j * (w i)⁻¹ = if i = j then (e j)⁻¹ else e j) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  let E : Subgroup (↥X ⧸ Subgroup.center ↥X) := bar X F
  have hne : ∀ i j : Fin 3, i ≠ j → w i * e j * (w i)⁻¹ = e j := fun i j hij => by
    rw [hwe i j]
    simp [hij]
  have heq : ∀ i : Fin 3, w i * e i * (w i)⁻¹ = (e i)⁻¹ := fun i => by
    rw [hwe i i]
    simp
  have hci : ∀ (i : Fin 3) (x : ↥X ⧸ Subgroup.center ↥X),
      w i * x⁻¹ * (w i)⁻¹ = (w i * x * (w i)⁻¹)⁻¹ := fun i x => by group
  set y : ↥X ⧸ Subgroup.center ↥X := w 0 * w 1 * w 2 with hy
  have hyN : y ∈ Subgroup.normalizer ((E : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X)) := mul_mem (mul_mem (hwN 0) (hwN 1)) (hwN 2)
  have hshape : ∀ k, y * e k * y⁻¹ =
      w 0 * (w 1 * (w 2 * e k * (w 2)⁻¹) * (w 1)⁻¹) * (w 0)⁻¹ := fun k => by
    simp only [hy, mul_inv_rev, mul_assoc]
  have hyk : ∀ k, y * e k * y⁻¹ = (e k)⁻¹ := by
    intro k
    rw [hshape k]
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
    · rw [hne 2 0 (by decide), hne 1 0 (by decide), heq 0]
    · rw [hne 2 1 (by decide), heq 1, hci 0, hne 0 1 (by decide)]
    · rw [heq 2, hci 1, hne 1 2 (by decide), hci 0, hne 0 2 (by decide)]
  let ψ : F ≃* E := barF_equiv h
  let α : MulAut E := E.normalizerMonoidHom ⟨y, hyN⟩
  have hαW : α ∈ torusWeyl E := ⟨⟨y, hyN⟩, rfl⟩
  obtain ⟨φ, hφ, hφα⟩ := torusWeyl_bar_le_B h hαW
  let ē : Fin 3 → E := fun j => ⟨e j, heE j⟩
  have hαk : ∀ k, α (ē k) = (ē k)⁻¹ := fun k => Subtype.ext (hyk k)
  have hcommE : ∀ a b : E, a * b = b * a := fun a b => by
    have hF := h.F_elem.is_comm.comm
    have := hF (ψ.symm a) (ψ.symm b)
    simpa using congrArg ψ this
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcommE }
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (barF_exp h x x.2)
  have hindE : ∀ a b c : ℤ, ē 0 ^ a * ē 1 ^ b * ē 2 ^ c = 1 →
      (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c := fun a b c hh => hind a b c (by
    have := congrArg Subtype.val hh
    simpa [ē] using this)
  have hαE : ∀ x : E, α x = x⁻¹ := by
    intro x
    obtain ⟨a, b, c, rfl⟩ := exists_pow_prod_of_independent (barF_card h) ē hindE x
    simp only [map_mul, map_pow, hαk, mul_inv, inv_pow]
  obtain ⟨f, hf⟩ := hneg φ hφ
  apply hf
  apply ψ.injective
  have h1 : ψ (φ f) = α (ψ f) := by
    rw [← hφα]
    show ψ (φ f) = (MulAut.congr ψ φ) (ψ f)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h1, hαE, map_inv]

end CFSG.RankThree.PartOne.Q1327T
