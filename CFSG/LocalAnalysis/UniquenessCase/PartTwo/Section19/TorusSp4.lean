module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

private theorem tcsp_prime_ne {n r : ℕ} (hodd : Odd n) (hr : r.Prime) (hdvd : r ∣ 2 ^ n - 1) :
    r ≠ 2 ∧ r ≠ 3 := by
  have h3 : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hodd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  constructor <;> rintro rfl <;> omega

private theorem tcsp_not_dvd {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ m) :
    ¬ r ∣ (m + 1) ^ 4 * (m + 2) ^ 2 * ((m + 1) ^ 2 + 1) := by
  have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  intro h
  rcases hr.dvd_mul.mp h with h | h
  · rcases hr.dvd_mul.mp h with h | h
    · exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp (hr.dvd_of_dvd_pow h)))
    · exact h2 ((Nat.dvd_add_right hdvd).mp (hr.dvd_of_dvd_pow h))
  · rw [show (m + 1) ^ 2 + 1 = m * (m + 2) + 2 by ring] at h
    exact h2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left hdvd _)).mp h)

section Model

variable {K : Type} [Field K]

private theorem tcsp_entry_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → K}
    {M : Matrix ι ι K} (h : Matrix.diagonal d * M = M * Matrix.diagonal d) {x y : ι}
    (hxy : d x ≠ d y) : M x y = 0 := by
  have h' := congrFun (congrFun h x) y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h'
  have h'' : (d x - d y) * M x y = 0 := by linear_combination h'
  exact (mul_eq_zero.mp h'').resolve_left (sub_ne_zero.mpr hxy)

private theorem tcsp_eq_one_of_eq_inv [CharP K 2] {u : Kˣ} (h : u = u⁻¹) : u = 1 := by
  have h2 : (u : K) ^ 2 = 1 := by
    have h' : u ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel u
    rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  have h20 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ((u : K) - 1) ^ 2 = 0 := by linear_combination h2 + (1 - (u : K)) * h20
  exact Units.val_eq_one.mp (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

private theorem tcsp_diag_injective [CharP K 2] {t : Fin 2 → Kˣ} (h0 : t 0 ≠ 1) (h1 : t 1 ≠ 1)
    (h01 : t 0 ≠ t 1) (h01' : t 0 ≠ (t 1)⁻¹) :
    Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) := by
  have h00 : t 0 ≠ (t 0)⁻¹ := fun h => h0 (tcsp_eq_one_of_eq_inv h)
  have h11 : t 1 ≠ (t 1)⁻¹ := fun h => h1 (tcsp_eq_one_of_eq_inv h)
  have h10' : t 1 ≠ (t 0)⁻¹ := fun h => h01' (by rw [h, inv_inv])
  have hU : Function.Injective (Sum.elim t fun i => (t i)⁻¹ : Fin 2 ⊕ Fin 2 → Kˣ) := by
    rintro (a | a) (b | b) h <;> fin_cases a <;> fin_cases b <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.zero_eta, Fin.isValue, Fin.mk_one,
        inv_inj] at h <;>
      first
        | rfl
        | exact absurd h h01 | exact absurd h.symm h01
        | exact absurd h h00 | exact absurd h.symm h00
        | exact absurd h h11 | exact absurd h.symm h11
        | exact absurd h h01' | exact absurd h.symm h01'
        | exact absurd h h10' | exact absurd h.symm h10'
  have hc : (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) =
      Units.val ∘ (Sum.elim t fun i => (t i)⁻¹ : Fin 2 ⊕ Fin 2 → Kˣ) := by
    funext x
    rcases x with x | x <;> rfl
  rw [hc]
  exact Units.val_injective.comp hU

private theorem tcsp_mem_torus_of_commute {t : Fin 2 → Kˣ}
    (hinj : Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)))
    {y : StatedSp 2 K} (hy : y * torusHom t = torusHom t * y) : y ∈ torus 2 K := by
  have hcomm : Matrix.diagonal (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) *
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        Matrix.diagonal (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) := by
    have h := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hy
    simp only [coe_mul_statedSp, coe_torusHom] at h
    exact h.symm
  have hdiag : ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.diagonal fun x =>
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x x := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact tcsp_entry_eq_zero hcomm (hinj.ne hab)
  have hsp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp y.2
  have hprod : ∀ i,
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          (Sum.inl i) (Sum.inl i) *
        ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun hsp (Sum.inl i)) (Sum.inr i)
    rw [hdiag, Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa using h
  refine ⟨fun i => Units.mkOfMulEqOne _ _ (hprod i), statedSp_ext ?_⟩
  rw [coe_torusHom]
  refine (congrArg Matrix.diagonal ?_).trans hdiag.symm
  funext x
  rcases x with i | i <;> rfl

private theorem tcsp_centralizer_eq_torus {t : Fin 2 → Kˣ}
    (hinj : Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K))) :
    centralizer ({torusHom t} : Set (StatedSp 2 K)) = torus 2 K := by
  apply le_antisymm
  · intro y hy
    rw [mem_centralizer_singleton_iff] at hy
    exact tcsp_mem_torus_of_commute hinj hy
  · rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mul_comm]

private theorem tcsp_torusHom_eq_lam (t : Fin 2 → Kˣ) :
    torusHom t = lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)) := by
  rw [lam_sl2Diag, lam_sl2Diag, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem tcsp_commute_lam_zero {t : Fin 2 → Kˣ} (h : t 0 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : Commute (torusHom t) (lam 0 g) := by
  rw [tcsp_torusHom_eq_lam, h, map_one, map_one, one_mul]
  exact commute_lam_lam (by decide) _ _

private theorem tcsp_commute_lam_one {t : Fin 2 → Kˣ} (h : t 1 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : Commute (torusHom t) (lam 1 g) := by
  rw [tcsp_torusHom_eq_lam, h, map_one, map_one, mul_one]
  exact commute_lam_lam (by decide) _ _

private theorem tcsp_rho_injective :
    Function.Injective (rho (k := K) (0 : Fin 2) 1 (by decide)) := by
  intro g h hgh
  have hm := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hgh
  simp only [coe_rho'] at hm
  have h1 := (Matrix.fromBlocks_inj.mp hm).1
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  have h2 := congrFun (congrFun h1 a) b
  fin_cases a <;> fin_cases b <;> simpa [pairMat] using h2

private theorem tcsp_commute_rho {t : Fin 2 → Kˣ} (h : t 0 = t 1)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (torusHom t) (rho 0 1 (by decide) g) := by
  have ht : t = fun _ => t 0 := by
    funext i
    fin_cases i
    · rfl
    · exact h.symm
  rw [ht]
  simp only [torusHom, rho, MonoidHom.comp_apply]
  refine Commute.map ?_ leviSp
  show _ * _ = _ * _
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem tcsp_conj_lam_one_sl2W (t : Fin 2 → Kˣ) :
    lam (r := 2) 1 sl2W * torusHom t * (lam (r := 2) 1 sl2W)⁻¹ =
      lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)⁻¹) := by
  set s : StatedSp 2 K := lam 1 sl2W with hs
  have hc : s * lam 0 (sl2Diag (t 0)) = lam 0 (sl2Diag (t 0)) * s :=
    (commute_lam_lam (by decide) _ _).eq
  rw [tcsp_torusHom_eq_lam, ← sl2W_conj_sl2Diag, map_mul, map_mul, map_inv, ← hs]
  calc s * (lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1))) * s⁻¹
      = (s * lam 0 (sl2Diag (t 0))) * lam 1 (sl2Diag (t 1)) * s⁻¹ := by
        simp only [mul_assoc]
    _ = (lam 0 (sl2Diag (t 0)) * s) * lam 1 (sl2Diag (t 1)) * s⁻¹ := by
        rw [hc]
    _ = lam 0 (sl2Diag (t 0)) * (s * lam 1 (sl2Diag (t 1)) * s⁻¹) := by
        simp only [mul_assoc]

private theorem tcsp_commute_conj {G : Type*} [Group G] {c x y : G}
    (h : Commute (c * x * c⁻¹) y) : Commute x (c⁻¹ * y * c) := by
  show x * (c⁻¹ * y * c) = c⁻¹ * y * c * x
  calc x * (c⁻¹ * y * c) = c⁻¹ * ((c * x * c⁻¹) * y) * c := by group
    _ = c⁻¹ * (y * (c * x * c⁻¹)) * c := by rw [h.eq]
    _ = c⁻¹ * y * c * x := by group

private theorem tcsp_commute_rho_conj {t : Fin 2 → Kˣ} (h : t 0 = (t 1)⁻¹)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (torusHom t)
      (((MulAut.conj (lam (r := 2) 1 sl2W)⁻¹).toMonoidHom.comp (rho 0 1 (by decide))) g) := by
  have hconj : lam (r := 2) 1 sl2W * torusHom t * (lam (r := 2) 1 sl2W)⁻¹ =
      torusHom fun _ => t 0 := by
    rw [tcsp_conj_lam_one_sl2W, ← h, tcsp_torusHom_eq_lam]
  have hc : Commute (lam (r := 2) 1 sl2W * torusHom t * (lam (r := 2) 1 sl2W)⁻¹)
      (rho 0 1 (by decide) g) := by
    rw [hconj]
    exact tcsp_commute_rho (t := fun _ => t 0) rfl g
  show Commute (torusHom t)
    ((lam (r := 2) 1 sl2W)⁻¹ * rho 0 1 _ g * ((lam (r := 2) 1 sl2W)⁻¹)⁻¹)
  rw [inv_inv]
  exact tcsp_commute_conj hc

private theorem tcsp_torus_dichotomy [CharP K 2] (t : Fin 2 → Kˣ) :
    centralizer ({torusHom t} : Set (StatedSp 2 K)) = torus 2 K ∨
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K, Function.Injective φ ∧
        ∀ g, Commute (torusHom t) (φ g) := by
  by_cases h0 : t 0 = 1
  · exact Or.inr ⟨lam 0, lam_injective 0, tcsp_commute_lam_zero h0⟩
  by_cases h1 : t 1 = 1
  · exact Or.inr ⟨lam 1, lam_injective 1, tcsp_commute_lam_one h1⟩
  by_cases h01 : t 0 = t 1
  · exact Or.inr ⟨rho 0 1 (by decide), tcsp_rho_injective, tcsp_commute_rho h01⟩
  by_cases h01' : t 0 = (t 1)⁻¹
  · exact Or.inr ⟨(MulAut.conj (lam (r := 2) 1 sl2W)⁻¹).toMonoidHom.comp (rho 0 1 (by decide)),
      (MulAut.conj _).injective.comp tcsp_rho_injective, tcsp_commute_rho_conj h01'⟩
  exact Or.inl (tcsp_centralizer_eq_torus (tcsp_diag_injective h0 h1 h01 h01'))

private theorem tcsp_card_torus [Finite K] : Nat.card (torus 2 K) = (Nat.card K - 1) ^ 2 := by
  show Nat.card (torusHom (r := 2) (k := K)).range = _
  rw [← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (r := 2) (k := K))).toEquiv,
    Nat.card_fun, Nat.card_units, Nat.card_fin]

private theorem tcsp_exists_regular [Finite K] [CharP K 2] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrd : r ∣ Nat.card K - 1) :
    ∃ y : StatedSp 2 K, centralizer ({y} : Set (StatedSp 2 K)) = torus 2 K ∧ y ^ r = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hpow : ∀ k : ℕ, ζ ^ k = 1 ↔ r ∣ k := fun k => by rw [← hζ, orderOf_dvd_iff_pow_eq_one]
  have hζ1 : ζ ≠ 1 := fun h => hr.one_lt.ne' (by rw [← hζ, h, orderOf_one])
  have hζ2 : ζ ^ 2 ≠ 1 := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp ((hpow 2).mp h))
  have hζ3 : ζ ^ 3 ≠ 1 := fun h =>
    hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp ((hpow 3).mp h))
  refine ⟨torusHom ![ζ, ζ ^ 2], tcsp_centralizer_eq_torus (tcsp_diag_injective ?_ ?_ ?_ ?_), ?_⟩
  · simpa using hζ1
  · simpa using hζ2
  · show ζ ≠ ζ ^ 2
    intro h
    apply hζ1
    have h' : ζ * 1 = ζ * ζ := by rw [mul_one, ← sq]; exact h
    exact (mul_left_cancel h').symm
  · show ζ ≠ (ζ ^ 2)⁻¹
    intro h
    apply hζ3
    calc ζ ^ 3 = ζ * ζ ^ 2 := by group
      _ = (ζ ^ 2)⁻¹ * ζ ^ 2 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  · have hζr : ζ ^ r = 1 := (hpow r).mpr dvd_rfl
    have ht : (![ζ, ζ ^ 2] : Fin 2 → Kˣ) ^ r = 1 := by
      funext i
      fin_cases i
      · exact hζr
      · show (ζ ^ 2) ^ r = 1
        rw [← pow_mul, mul_comm, pow_mul, hζr, one_pow]
    rw [← map_pow, ht, map_one]

private theorem tcsp_not_dvd_index [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card K - 1) {T : Subgroup (StatedSp 2 K)}
    (hT : Nat.card T = (Nat.card K - 1) * (Nat.card K - 1)) : ¬ r ∣ T.index := by
  have hcard := T.card_mul_index
  rw [hT, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two] at hcard
  obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
    have := Nat.card_pos (α := K)
    omega⟩
  have hm0 : 0 < m * m := by
    have h := Nat.card_pos (α := T)
    rwa [hT, hm, Nat.add_sub_cancel] at h
  rw [hm, Nat.add_sub_cancel] at hcard hrd
  have h2 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    rw [show (m + 1) ^ 2 = m * (m + 2) + 1 by ring, Nat.add_sub_cancel]
  have h4 : (m + 1) ^ 4 - 1 = m * (m + 2) * ((m + 1) ^ 2 + 1) := by
    rw [show (m + 1) ^ 4 = m * (m + 2) * ((m + 1) ^ 2 + 1) + 1 by ring, Nat.add_sub_cancel]
  rw [h2, h4] at hcard
  have hidx : T.index = (m + 1) ^ 4 * (m + 2) ^ 2 * ((m + 1) ^ 2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hm0
    rw [hcard]
    ring
  rw [hidx]
  exact tcsp_not_dvd hr hr2 hrd

private theorem tcsp_exists_sylow_le [Finite K] {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrd : r ∣ Nat.card K - 1) {T : Subgroup (StatedSp 2 K)}
    (hT : Nat.card T = (Nat.card K - 1) * (Nat.card K - 1)) :
    ∃ Q : Sylow r (StatedSp 2 K), (Q : Subgroup (StatedSp 2 K)) ≤ T := by
  obtain ⟨P⟩ : Nonempty (Sylow r T) := inferInstance
  have hidx : ¬ r ∣ ((P : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases hr.out.dvd_mul.mp h with h | h
    · exact P.not_dvd_index h
    · exact tcsp_not_dvd_index hr.out hr2 hrd hT h
  exact ⟨(P.isPGroup'.map T.subtype).toSylow hidx, Subgroup.map_subtype_le _⟩

end Model

theorem exists_conj_eq_torus_of_isZModSq_sp4 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (hodd : Odd n) {T : Subgroup (StatedSp 2 K)}
    (hT : IsZModSq T n) :
    ∃ g : StatedSp 2 K, T = (torus 2 K).map (MulAut.conj g).toMonoidHom := by
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  obtain ⟨hr2, hr3⟩ := tcsp_prime_ne hodd hr hrd
  have : Fact r.Prime := ⟨hr⟩
  rw [← hK] at hrd
  have hTcard : Nat.card T = (Nat.card K - 1) * (Nat.card K - 1) := by
    rw [card_eq_of_isZModSq hT, hK]
  obtain ⟨y, hyC, hyr⟩ := tcsp_exists_regular hr hr2 hr3 hrd
  obtain ⟨Q, hQT⟩ := tcsp_exists_sylow_le hr2 hrd hTcard
  have hyp : IsPGroup r (zpowers y) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hyr)
  obtain ⟨Q', hQ'⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 K) Q' Q
  have hgy : g * y * g⁻¹ ∈ T := by
    apply hQT
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q' : Subgroup (StatedSp 2 K))
      (hQ' (mem_zpowers y))
  have := isMulCommutative_of_isZModSq hT
  refine ⟨g, Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) ?_⟩
  · have hcomm : g * y * g⁻¹ * z = z * (g * y * g⁻¹) := Subgroup.le_centralizer T hz _ hgy
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, ← hyC, mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * z) * g := by rw [hcomm]
      _ = y * (g⁻¹ * z * g) := by group
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      tcsp_card_torus, hTcard]
    exact (sq _).le

private theorem tcsp_map_centralizer {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact h
  · intro h
    have h' := congrArg e.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h'

theorem k_19_25_torusCent_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hX : IsSp4 X n) {T : Subgroup X} (hT : IsZModSq T n) {x : X} (hxT : x ∈ T) :
    centralizer ({x} : Set X) = T ∨ ∃ Y : Subgroup X, Y ≤ centralizer ({x} : Set X) ∧
      ∃ (Z : Subgroup ↥Y) (_ : Z.Normal), IsL2 (↥Y ⧸ Z) n := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.exists_mulEquiv_statedSp_of_lieModel hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  obtain ⟨eT⟩ := hT
  obtain ⟨g, hg⟩ := exists_conj_eq_torus_of_isZModSq_sp4 hK hn hodd (T := T.map e.toMonoidHom)
    ⟨(T.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eT⟩
  let E : StatedSp 2 K ≃* X := (MulAut.conj g).trans e.symm
  have hTE : ∀ z, z ∈ T ↔ E.symm z ∈ torus 2 K := by
    intro z
    show z ∈ T ↔ (MulAut.conj g).symm (e z) ∈ torus 2 K
    rw [← Subgroup.mem_map_equiv, ← hg, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  obtain ⟨t, ht⟩ := (hTE x).mp hxT
  have hxE : E (torusHom t) = x := by rw [ht, MulEquiv.apply_symm_apply]
  rcases tcsp_torus_dichotomy t with hC | ⟨φ, hφ, hcomm⟩
  · left
    rw [← hxE, ← tcsp_map_centralizer, hC]
    ext z
    rw [Subgroup.mem_map_equiv, hTE]
  · right
    refine ⟨(E.toMonoidHom.comp φ).range, ?_, ⊥, inferInstance, ?_⟩
    · rintro _ ⟨h, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hxE]
      exact ((hcomm h).symm.map E).eq
    · exact CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.isL2_of_mulEquiv_sl2 (by omega) hK
        (QuotientGroup.quotientBot.trans
          (MonoidHom.ofInjective (f := E.toMonoidHom.comp φ) (E.injective.comp hφ)).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
