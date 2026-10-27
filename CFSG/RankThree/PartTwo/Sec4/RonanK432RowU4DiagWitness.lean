module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4DiagMono
public import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardAbs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432.U4Diag

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {p f : ℕ} {K : Type} [Field K]

theorem mem_idUnitary {h : UnitaryFieldData p f K} {g : GL (Fin 4) K} :
    g ∈ primeFormUnitary h (idGram K 4) ↔
      ((g : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
  rw [mem_primeFormUnitary]
  simp [idGram]

theorem exists_witness_of_scalar_cube {h : UnitaryFieldData p f K} {ω : K}
    (hω2 : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) (hmq : 3 ∣ p ^ f + 1)
    {x : GL (Fin 4) K} (hx : x ∈ unitarySU p f K 4) {c : Kˣ}
    (hc : x ^ 3 = GeneralLinearGroup.scalar (Fin 4) c)
    (hns : ∀ c' : Kˣ, x ≠ GeneralLinearGroup.scalar (Fin 4) c') :
    ∃ t ∈ unitarySU p f K 4,
      Matrix.ProjGenLinGroup.mk t * Matrix.ProjGenLinGroup.mk x *
            (Matrix.ProjGenLinGroup.mk t)⁻¹ * Matrix.ProjGenLinGroup.mk x =
          Matrix.ProjGenLinGroup.mk x *
            (Matrix.ProjGenLinGroup.mk t * Matrix.ProjGenLinGroup.mk x *
              (Matrix.ProjGenLinGroup.mk t)⁻¹) ∧
        Matrix.ProjGenLinGroup.mk t * Matrix.ProjGenLinGroup.mk x *
            (Matrix.ProjGenLinGroup.mk t)⁻¹ ∉
          Subgroup.zpowers (Matrix.ProjGenLinGroup.mk x) := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 4) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  have hω : IsPrimitiveRoot ω 3 := isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  obtain ⟨hdetx, hunx⟩ := (mem_unitarySU_iff h).mp hx
  have hxU : x ∈ primeFormUnitary h (idGram K 4) := mem_idUnitary.mpr hunx
  have hsSU : GeneralLinearGroup.scalar (Fin 4) c ∈ unitarySU p f K 4 := hc ▸ pow_mem hx 3
  obtain ⟨hdets, huns⟩ := (mem_unitarySU_iff h).mp hsSU
  have hsU : GeneralLinearGroup.scalar (Fin 4) c ∈ primeFormUnitary h (idGram K 4) :=
    mem_idUnitary.mpr huns
  have hc4 : (c : K) ^ 4 = 1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using hdets
  obtain ⟨x', hx'⟩ : ∃ y : GL (Fin 4) K, y = GeneralLinearGroup.scalar (Fin 4) c * x := ⟨_, rfl⟩
  have hx'U : x' ∈ primeFormUnitary h (idGram K 4) := by
    rw [hx']
    exact mul_mem hsU hxU
  have hcomm_sx : Commute (GeneralLinearGroup.scalar (Fin 4) c) x := (commute_scalar c x).symm
  have hcu : c ^ 3 * c = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, ← pow_succ]
    exact hc4
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', hcomm_sx.mul_pow, hc, ← map_pow, ← map_mul, hcu, map_one]
  have hdetx' : (x' : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [hx', Units.val_mul, Matrix.det_mul, hdets, hdetx, one_mul]
  let X : primeFormUnitary h (idGram K 4) := ⟨x', hx'U⟩
  have hX3 : X ^ 3 = 1 := Subtype.ext (by simpa using hx'3)
  let G : Subgroup (primeFormUnitary h (idGram K 4)) := Subgroup.zpowers X
  have hcommG : ∀ y ∈ G, ∀ z ∈ G, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl X).zpow_zpow i j).eq
  have hpowG : ∀ y ∈ G, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hX3, _root_.one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hω hmq G hcommG
    hpowG
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 4) K, g = (P : GL (Fin 4) K) := ⟨_, rfl⟩
  have hgU : g ∈ primeFormUnitary h (idGram K 4) := by
    rw [hg]
    exact P.2
  obtain ⟨D, hD_def⟩ : ∃ D : GL (Fin 4) K, D = g⁻¹ * x' * g := ⟨_, rfl⟩
  have hDdiag : (D : Matrix (Fin 4) (Fin 4) K).IsDiag := by
    have := hP X (Subgroup.mem_zpowers X)
    rw [hD_def, hg]
    exact this
  have hD3 : D ^ 3 = 1 := by
    have e := conj_pow (a := g⁻¹) (b := x') (i := 3)
    rw [inv_inv, ← hD_def, hx'3, mul_one, inv_mul_cancel] at e
    exact e
  obtain ⟨d, hdiag⟩ : ∃ d : Fin 4 → K, (D : Matrix (Fin 4) (Fin 4) K) = diagonal d :=
    ⟨fun l => (D : Matrix (Fin 4) (Fin 4) K) l l, hDdiag.diagonal_diag.symm⟩
  have hd3 : ∀ l, d l ^ 3 = 1 := by
    intro l
    have hm : (D : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hD3, Units.val_one]
    rw [hdiag, Matrix.diagonal_pow] at hm
    have := congrFun (congrFun hm l) l
    simpa [Matrix.diagonal_apply_eq] using this
  choose a ha using fun l => exists_zmod_three_pow_eq hω2 (hd3 l)
  have hdpsi : ∀ l, d l = psi ω (a l) := fun l => (ha l).symm
  have hdetD : (D : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    have e : GeneralLinearGroup.det D = GeneralLinearGroup.det x' := by
      rw [hD_def, map_mul, map_mul, map_inv]
      simp [mul_comm, mul_assoc, mul_left_comm]
    have h1 := congrArg (fun u : Kˣ => (u : K)) e
    simp only [GeneralLinearGroup.val_det_apply] at h1
    rw [h1, hdetx']
  have hsum : ∑ l, a l = 0 := by
    have hprod : (D : Matrix (Fin 4) (Fin 4) K).det = psi ω (∑ l, a l) := by
      rw [hdiag, Matrix.det_diagonal, ← psi_prod hω Finset.univ a]
      exact Finset.prod_congr rfl (fun l _ => hdpsi l)
    rw [hprod] at hdetD
    exact (psi_eq_one_iff hω _).mp hdetD
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hns c⁻¹
    have hd1 : ∀ l, d l = 1 := fun l => by
      rw [hdpsi l]
      simp [ha0, psi_zero]
    have hD1 : D = 1 := by
      apply Units.ext
      rw [hdiag, Units.val_one]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hd1]
      · simp [Matrix.diagonal_apply_ne _ hij, hij]
    have hx'1 : x' = 1 := by
      calc x' = g * (g⁻¹ * x' * g) * g⁻¹ := by group
        _ = 1 := by rw [← hD_def, hD1]; group
    have hsx1 : GeneralLinearGroup.scalar (Fin 4) c * x = 1 := hx'.symm.trans hx'1
    exact (eq_inv_of_mul_eq_one_right hsx1).trans (map_inv (GeneralLinearGroup.scalar (Fin 4)) c).symm
  obtain ⟨i, j, hij, hsw⟩ := exists_swap_of_ne_zero a ha0 hsum
  have hσ : ∀ r : Fin 4, Equiv.swap i j (Equiv.swap i j r) = r := fun r => Equiv.swap_apply_self i j r
  obtain ⟨ε, hεdef⟩ : ∃ ε : Fin 4 → K, ε = fun c' => if c' = j then -1 else 1 := ⟨_, rfl⟩
  have hε : ∀ c', ε c' * ε c' = 1 := by
    intro c'
    rw [hεdef]
    by_cases hc' : c' = j <;> simp [hc']
  have hfε : ∀ c', h.bar (ε c') = ε c' := by
    intro c'
    rw [hεdef]
    by_cases hc' : c' = j <;> simp [hc']
  obtain ⟨S, hSdef⟩ : ∃ S : GL (Fin 4) K, S = monoUnit (Equiv.swap i j) hσ ε hε := ⟨_, rfl⟩
  have hSval : (S : Matrix (Fin 4) (Fin 4) K) = mono (Equiv.swap i j) ε := by
    rw [hSdef, monoUnit_val]
  have hSinv : ((S⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (mono (Equiv.swap i j) ε)ᵀ := by
    rw [hSdef, monoUnit_inv_val]
  have hSdet : (S : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [hSval, det_mono _ hσ, Equiv.Perm.sign_swap hij, hεdef]
    simp [Finset.prod_ite_eq']
  have hSU : S ∈ primeFormUnitary h (idGram K 4) := by
    rw [mem_idUnitary, hSval, map_mono h.bar (Equiv.swap i j) ε hfε,
      transpose_mono_mul_mono (Equiv.swap i j) hσ ε hε]
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin 4) K, t = g * S * g⁻¹ := ⟨_, rfl⟩
  have htU : t ∈ primeFormUnitary h (idGram K 4) := by
    rw [ht]
    exact mul_mem (mul_mem hgU hSU) (inv_mem hgU)
  have hgdet : (g : Matrix (Fin 4) (Fin 4) K).det * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det
      = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have htdet : (t : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [ht, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hSdet, mul_one]
    exact hgdet
  have htL : t ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).mpr ⟨htdet, mem_idUnitary.mp htU⟩
  have hSDS : ((S * D * S⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun r => d (Equiv.swap i j r)) := by
    rw [Units.val_mul, Units.val_mul, hSval, hSinv, hdiag,
      mono_mul_diagonal_mul_transpose (Equiv.swap i j) hσ ε d hε]
  have hcommD : (S * D * S⁻¹) * D = D * (S * D * S⁻¹) := by
    apply Units.ext
    have e1 : (((S * D * S⁻¹) * D : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal (fun r => d (Equiv.swap i j r)) * diagonal d := by
      rw [Units.val_mul, hSDS, hdiag]
    have e2 : ((D * (S * D * S⁻¹) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal d * diagonal (fun r => d (Equiv.swap i j r)) := by
      rw [Units.val_mul, hSDS, hdiag]
    rw [e1, e2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    exact mul_comm _ _
  have hx'eq : x' = g * D * g⁻¹ := by
    rw [hD_def]
    group
  have hcommGL : t * x' * t⁻¹ * x' = x' * (t * x' * t⁻¹) := by
    have e1 : t * x' * t⁻¹ * x' = g * ((S * D * S⁻¹) * D) * g⁻¹ := by
      rw [ht, hx'eq]
      group
    have e2 : x' * (t * x' * t⁻¹) = g * (D * (S * D * S⁻¹)) * g⁻¹ := by
      rw [ht, hx'eq]
      group
    rw [e1, e2, hcommD]
  have hmx : Matrix.ProjGenLinGroup.mk x = Matrix.ProjGenLinGroup.mk x' := by
    rw [hx', map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  refine ⟨t, htL, ?_, ?_⟩
  · rw [hmx]
    have := congrArg Matrix.ProjGenLinGroup.mk hcommGL
    simpa only [map_mul, map_inv] using this
  · rw [hmx]
    intro hmem
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    have hn' : Matrix.ProjGenLinGroup.mk (x' ^ n) = Matrix.ProjGenLinGroup.mk (t * x' * t⁻¹) := by
      rw [map_pow, hn]
      simp only [map_mul, map_inv]
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn'
    have hcs : GeneralLinearGroup.scalar (Fin 4) u * g = g * GeneralLinearGroup.scalar (Fin 4) u :=
      (commute_scalar u g).eq.symm
    have hDn : D ^ n * GeneralLinearGroup.scalar (Fin 4) u = S * D * S⁻¹ := by
      have e1 : D ^ n = g⁻¹ * x' ^ n * g := by
        rw [hD_def]
        have := conj_pow (a := g⁻¹) (b := x') (i := n)
        rw [inv_inv] at this
        exact this
      have e2 : g⁻¹ * (x' ^ n * GeneralLinearGroup.scalar (Fin 4) u) * g =
          D ^ n * GeneralLinearGroup.scalar (Fin 4) u := by
        rw [e1]
        calc g⁻¹ * (x' ^ n * GeneralLinearGroup.scalar (Fin 4) u) * g
            = g⁻¹ * x' ^ n * (GeneralLinearGroup.scalar (Fin 4) u * g) := by group
          _ = g⁻¹ * x' ^ n * (g * GeneralLinearGroup.scalar (Fin 4) u) := by rw [hcs]
          _ = g⁻¹ * x' ^ n * g * GeneralLinearGroup.scalar (Fin 4) u := by group
      have e3 : g⁻¹ * (t * x' * t⁻¹) * g = S * D * S⁻¹ := by
        rw [ht, hD_def]
        group
      rw [← e2, hu, e3]
    have hmat : ((D ^ n * GeneralLinearGroup.scalar (Fin 4) u : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = diagonal (fun r => d (Equiv.swap i j r)) := by
      rw [← hSDS, hDn]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hdiag, Matrix.diagonal_pow,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at hmat
    have hr : ∀ r, psi ω (a (Equiv.swap i j r)) = (u : K) * psi ω (a r) ^ n := by
      intro r
      have e := congrFun (Matrix.diagonal_injective hmat) r
      rw [← hdpsi (Equiv.swap i j r), ← hdpsi r, ← e, mul_comm, Pi.pow_apply]
    obtain ⟨l, l', hne⟩ := hsw (n : ZMod 3)
    exact hne (sub_const_of_psi_eq hω (Equiv.swap i j) a n (u : K) hr l l')

end CFSG.RankThree.PartTwo.Sec4.RonanK432.U4Diag

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.PGLModel (projImage)

theorem listRow_projSU_four_of_dvd_succ {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h3 : 3 ∣ p ^ f + 1) : ListRow (projSU 4 p f) := by
  classical
  have h := unitaryFieldData_galoisField p f hf
  haveI : Finite (GaloisField p (2 * f)) := h.finite
  haveI : CharP (GaloisField p (2 * f)) p := h.charP
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 4) (GaloisField p (2 * f))) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 4) (GaloisField p (2 * f)) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  have h3K : (3 : GaloisField p (2 * f)) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := by
      have h0' : ((3 : ℕ) : GaloisField p (2 * f)) = 0 := by exact_mod_cast h0
      exact (CharP.cast_eq_zero_iff (GaloisField p (2 * f)) p 3).mp h0'
    have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd
    subst hp
    have h30 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    exact absurd ((Nat.dvd_add_right h30).mp h3) (by norm_num)
  have hcard : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have hdvdU : 3 ∣ Nat.card (GaloisField p (2 * f))ˣ := by
    rw [Nat.card_units, hcard]
    have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    have hsq : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      obtain ⟨r, hr⟩ : ∃ r, p ^ f = r + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [hsq]
    exact Dvd.dvd.mul_right h3 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g3, hg3⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p (2 * f))ˣ) 3 hdvdU
  have hω3 : (g3 : GaloisField p (2 * f)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg3, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (g3 : GaloisField p (2 * f)) ≠ 1 := by
    intro h1
    have hg1 : g3 = 1 := Units.ext h1
    rw [hg1, orderOf_one] at hg3
    exact absurd hg3 (by norm_num)
  have hω2 : (g3 : GaloisField p (2 * f)) ^ 2 + (g3 : GaloisField p (2 * f)) + 1 = 0 := by
    have h1 : ((g3 : GaloisField p (2 * f)) - 1) *
        ((g3 : GaloisField p (2 * f)) ^ 2 + (g3 : GaloisField p (2 * f)) + 1) = 0 := by
      linear_combination hω3
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hω1
    · exact h2
  have hL : ListRow (projImage (CFSG.Open.StatedSU 4 (p ^ f) (GaloisField p (2 * f)))) := by
    refine L3Hard.listRow_map_of_witness
      (Matrix.ProjGenLinGroup.mk : GL (Fin 4) (GaloisField p (2 * f)) →* _)
      (CFSG.Open.StatedSU 4 (p ^ f) (GaloisField p (2 * f))) ?_
    intro x hx ho
    have hx3 : Matrix.ProjGenLinGroup.mk (x ^ 3) = 1 := by
      rw [map_pow]
      have := pow_orderOf_eq_one (Matrix.ProjGenLinGroup.mk x)
      rwa [ho] at this
    obtain ⟨c, hc⟩ : ∃ c : (GaloisField p (2 * f))ˣ,
        Matrix.GeneralLinearGroup.scalar (Fin 4) c = x ^ 3 := by
      have hmem := Matrix.ProjGenLinGroup.mk_eq_one.mp hx3
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
      exact hmem
    have hns : ∀ c' : (GaloisField p (2 * f))ˣ, x ≠ Matrix.GeneralLinearGroup.scalar (Fin 4) c' := by
      intro c' hxc
      have h1 : Matrix.ProjGenLinGroup.mk x = 1 := by
        rw [hxc, Matrix.ProjGenLinGroup.mk_scalar]
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    exact U4Diag.exists_witness_of_scalar_cube (h := h) hω2 h3K h3 hx hc.symm hns
  exact ListRow.of_mulEquiv (MulEquiv.subgroupCongr (CFSG.PGLModel.projImage_statedSU 4 p f)) hL

theorem rowOf_four_SU_of_mod_two :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → RowOf (projSU 4 p 1) := by
  intro p _ hp hp2 S _ _ _ _ ⟨e⟩
  have h3 : 3 ∣ p ^ 1 + 1 := by
    rw [pow_one]
    omega
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSU_four_of_dvd_succ (p := p) (f := 1) le_rfl h3, outerRow_projSU_four_prime⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

end
