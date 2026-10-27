module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem mem_normalizer_of_conj_le {M : Type} [Group M] [Finite M] {S : Subgroup M} {w : M}
    (h : ∀ s ∈ S, w * s * w⁻¹ ∈ S) : w ∈ Subgroup.normalizer (S : Set M) := by
  let φ : S → S := fun s => ⟨w * s * w⁻¹, h s s.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hs : Function.Surjective φ := Finite.injective_iff_surjective.1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    obtain ⟨s, hs'⟩ := hs ⟨w * x * w⁻¹, hx⟩
    have := congrArg Subtype.val hs'
    simp only [φ, mul_left_inj, mul_right_inj] at this
    rw [← this]
    exact s.2

theorem conj_lam_torus_single (i k : Fin 3) (a : Kˣ) :
    lam i sl2W * (torusHom (Pi.mulSingle k a) : StatedSp 3 K) * (lam i sl2W)⁻¹ =
      torusHom (Pi.mulSingle k (if k = i then a⁻¹ else a)) := by
  rw [← lam_sl2Diag, ← lam_sl2Diag]
  by_cases hki : k = i
  · subst hki
    have hite : (if k = k then a⁻¹ else a) = a⁻¹ := by simp
    rw [hite, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [sl2W_mul_sl2Diag, mul_assoc, mul_inv_cancel, mul_one]
  · have hite : (if k = i then a⁻¹ else a) = a := by simp [hki]
    rw [hite]
    rw [(commute_lam_lam (Ne.symm hki) sl2W (sl2Diag a)).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_rho_torus_single {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) (a : Kˣ) :
    rho i j hij sl2W * (torusHom (Pi.mulSingle k a) : StatedSp 3 K) * (rho i j hij sl2W)⁻¹ =
      torusHom (Pi.mulSingle (Equiv.swap i j k) a) := by
  rw [← lam_sl2Diag, ← lam_sl2Diag]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    have := DFunLike.congr_fun (conj_rho_sl2W_comp_lam_fst (k := K) hij) (sl2Diag a)
    simpa [MulAut.conj_apply] using this
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right]
    have := DFunLike.congr_fun (conj_rho_sl2W_comp_lam_snd (k := K) hij) (sl2Diag a)
    simpa [MulAut.conj_apply] using this
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
      (commute_rho_lam hij hki hkj sl2W (sl2Diag a)).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_lam_torus (i : Fin 3) (t : Fin 3 → Kˣ) :
    lam i sl2W * (torusHom t : StatedSp 3 K) * (lam i sl2W)⁻¹ =
      torusHom (fun k => if k = i then (t k)⁻¹ else t k) := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext m
    fin_cases m <;> simp
  have h2 : (fun k => if k = i then (t k)⁻¹ else t k) =
      Pi.mulSingle 0 (if (0 : Fin 3) = i then (t 0)⁻¹ else t 0) *
        Pi.mulSingle 1 (if (1 : Fin 3) = i then (t 1)⁻¹ else t 1) *
          Pi.mulSingle 2 (if (2 : Fin 3) = i then (t 2)⁻¹ else t 2) := by
    funext m
    fin_cases m <;> simp
  rw [h2]
  conv_lhs => rw [ht]
  simp only [map_mul]
  rw [show ∀ A B C W : StatedSp 3 K, W * (A * B * C) * W⁻¹ = (W * A * W⁻¹) * (W * B * W⁻¹) *
      (W * C * W⁻¹) from fun A B C W => by group]
  rw [conj_lam_torus_single, conj_lam_torus_single, conj_lam_torus_single]

theorem conj_rho01_torus (h01 : (0 : Fin 3) ≠ 1) (t : Fin 3 → Kˣ) :
    rho 0 1 h01 sl2W * (torusHom t : StatedSp 3 K) * (rho 0 1 h01 sl2W)⁻¹ =
      torusHom ![t 1, t 0, t 2] := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext m
    fin_cases m <;> simp
  have h2 : (![t 1, t 0, t 2] : Fin 3 → Kˣ) =
      Pi.mulSingle 1 (t 0) * Pi.mulSingle 0 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext m
    fin_cases m <;> simp
  rw [h2]
  conv_lhs => rw [ht]
  simp only [map_mul]
  rw [show ∀ A B C W : StatedSp 3 K, W * (A * B * C) * W⁻¹ = (W * A * W⁻¹) * (W * B * W⁻¹) *
      (W * C * W⁻¹) from fun A B C W => by group]
  rw [conj_rho_torus_single h01, conj_rho_torus_single h01, conj_rho_torus_single h01]
  have s0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  have s1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
  have s2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
  rw [s0, s1, s2]

theorem conj_lam_e (i j : Fin 3) (ζ : Kˣ) :
    lam i sl2W * (torusHom (Pi.mulSingle j ζ) : StatedSp 3 K) * (lam i sl2W)⁻¹ =
      if i = j then (torusHom (Pi.mulSingle j ζ))⁻¹ else torusHom (Pi.mulSingle j ζ) := by
  rw [conj_lam_torus_single]
  by_cases hij : i = j
  · subst hij
    simp [← map_inv, Pi.mulSingle_inv]
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

theorem conj_rho01_e0 (h01 : (0 : Fin 3) ≠ 1) (ζ : Kˣ) :
    rho 0 1 h01 sl2W * (torusHom (Pi.mulSingle 0 ζ) : StatedSp 3 K) * (rho 0 1 h01 sl2W)⁻¹ =
      torusHom (Pi.mulSingle 1 ζ) := by
  rw [conj_rho_torus_single]
  have s0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  rw [s0]

theorem conj_rho01_e1 (h01 : (0 : Fin 3) ≠ 1) (ζ : Kˣ) :
    rho 0 1 h01 sl2W * (torusHom (Pi.mulSingle 1 ζ) : StatedSp 3 K) * (rho 0 1 h01 sl2W)⁻¹ =
      torusHom (Pi.mulSingle 0 ζ) := by
  rw [conj_rho_torus_single]
  have s1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
  rw [s1]

theorem conj_rho01_e2 (h01 : (0 : Fin 3) ≠ 1) (ζ : Kˣ) :
    rho 0 1 h01 sl2W * (torusHom (Pi.mulSingle 2 ζ) : StatedSp 3 K) * (rho 0 1 h01 sl2W)⁻¹ =
      torusHom (Pi.mulSingle 2 ζ) := by
  rw [conj_rho_torus_single]
  have s2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
  rw [s2]

end CFSG.RankThree.PartOne.Q1327C
