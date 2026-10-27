module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUCore
public import CFSG.GroupTheory.OddOrderClosureIdempotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4PSU

open Matrix CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)
open scoped commutatorElement

variable {n : ℕ}

theorem permSU_mul_rev (σ τ : Equiv.Perm (Fin n)) :
    permSU hK (σ * τ) = permSU hK τ * permSU hK σ :=
  eq_of_coe_eq (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_permSU, coe_permSU, coe_permSU,
      Matrix.permMatrix_mul])

theorem permSU_one' : permSU hK (1 : Equiv.Perm (Fin n)) = 1 :=
  eq_of_coe_eq (by rw [coe_permSU, Subgroup.coe_one, Units.val_one, Matrix.permMatrix_one])

theorem permSU_inv' (σ : Equiv.Perm (Fin n)) : (permSU hK σ)⁻¹ = permSU hK σ⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← permSU_mul_rev, mul_inv_cancel, permSU_one']

theorem permSU_pow' (c : Equiv.Perm (Fin n)) (m : ℕ) : permSU hK (c ^ m) = permSU hK c ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, permSU_one']
  | succ m ih => rw [pow_succ, permSU_mul_rev, ih, pow_succ']

theorem permSU_conj_swap (ρ : Equiv.Perm (Fin n)) (u w : Fin n) :
    permSU hK ρ⁻¹ * permSU hK (Equiv.swap u w) * (permSU hK ρ⁻¹)⁻¹ =
      permSU hK (Equiv.swap (ρ u) (ρ w)) := by
  rw [permSU_inv', inv_inv, ← permSU_mul_rev, ← permSU_mul_rev, ← mul_assoc,
    ← Equiv.swap_apply_apply]

theorem permSU_pow_three_of_isThreeCycle {c : Equiv.Perm (Fin n)} (hc : c.IsThreeCycle) :
    permSU hK c ^ 3 = 1 := by
  have h3 : c ^ 3 = 1 := by
    rw [← hc.orderOf]
    exact pow_orderOf_eq_one c
  rw [← permSU_pow', h3, permSU_one']

theorem dSU_pow_three {k l : Fin n} (hkl : k ≠ l) : dSU hkl ^ 3 = 1 := by
  apply eq_of_coe_eq
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_dSU, diagonal_pow, Subgroup.coe_one,
    Units.val_one, ← diagonal_one]
  congr 1
  funext a
  obtain ⟨-, -, h1k, h1l, h1o⟩ := diagKL_spec hkl
  rw [Pi.pow_apply]
  by_cases hak : a = k
  · rw [hak, h1k, omega_cube]
  · by_cases hal : a = l
    · rw [hal, h1l, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_cube, one_pow]
    · rw [h1o a hak hal, one_pow]

theorem conj_mem_commutator_commutator {G : Type*} [Group G] {H : Subgroup G} {g x : G}
    (hg : g ∈ H) (hx : x ∈ ⁅⁅H, H⁆, ⁅H, H⁆⁆) : g * x * g⁻¹ ∈ ⁅⁅H, H⁆, ⁅H, H⁆⁆ := by
  have hN := Subgroup.normalizer_commutator_ge_left H H hg
  have key : ⁅⁅H, H⁆, ⁅H, H⁆⁆ ≤ (⁅⁅H, H⁆, ⁅H, H⁆⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hN a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp hN b).mp hb)
    rw [Subgroup.mem_comap]
    simpa [commutatorElement_def, mul_assoc] using this
  exact key hx

section Swaps

variable {i j : Fin n} (hij : i ≠ j)

theorem swap_fix {k l : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) : Equiv.swap k l i = i ∧ Equiv.swap k l j = j :=
  ⟨Equiv.swap_apply_of_ne_of_ne (ne_left_of_mem_compl hk).symm (ne_left_of_mem_compl hl).symm,
    Equiv.swap_apply_of_ne_of_ne (ne_right_of_mem_compl hk).symm (ne_right_of_mem_compl hl).symm⟩

theorem permSU_swap_mem_centralizer {k l : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) :
    permSU hK (Equiv.swap k l) ∈ Subgroup.centralizer {tvTransSU hK hij} :=
  unitaryBlock_le_centralizer_tvTransSU hK hij
    (permSU_mem_unitaryBlock (swap_fix hk hl).1 (swap_fix hk hl).2)

theorem dSU_mem_centralizer {k l : Fin n} (hkl : k ≠ l) (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) :
    dSU hkl ∈ Subgroup.centralizer {tvTransSU hK hij} :=
  unitaryBlock_le_centralizer_tvTransSU hK hij (dSU_mem_unitaryBlock hkl hk hl)

theorem permSU_swap_mem_commutator (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {k l : Fin n}
    (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) :
    permSU hK (Equiv.swap k l) ∈
      ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆ := by
  obtain ⟨u, hu, w, hw, huw, hmem⟩ := exists_swap_mem_commutator hij hJ
  have hρ₁i : Equiv.swap u k i = i := (swap_fix hu hk).1
  have hρ₁j : Equiv.swap u k j = j := (swap_fix hu hk).2
  have hw' : Equiv.swap u k w ∈ ({i, j}ᶜ : Finset (Fin n)) := perm_mem_compl hρ₁i hρ₁j hw
  have hwk : Equiv.swap u k w ≠ k := by
    intro h
    apply huw
    apply (Equiv.swap u k).injective
    rw [h, Equiv.swap_apply_left]
  have hρi : (Equiv.swap (Equiv.swap u k w) l * Equiv.swap u k) i = i := by
    rw [Equiv.Perm.mul_apply, hρ₁i, (swap_fix hw' hl).1]
  have hρj : (Equiv.swap (Equiv.swap u k w) l * Equiv.swap u k) j = j := by
    rw [Equiv.Perm.mul_apply, hρ₁j, (swap_fix hw' hl).2]
  have hρu : (Equiv.swap (Equiv.swap u k w) l * Equiv.swap u k) u = k := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hwk.symm hkl]
  have hρw : (Equiv.swap (Equiv.swap u k w) l * Equiv.swap u k) w = l := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hρC : permSU hK (Equiv.swap (Equiv.swap u k w) l * Equiv.swap u k)⁻¹ ∈
      Subgroup.centralizer {tvTransSU hK hij} := by
    refine unitaryBlock_le_centralizer_tvTransSU hK hij (permSU_mem_unitaryBlock ?_ ?_)
    · rw [Equiv.Perm.inv_eq_iff_eq, hρi]
    · rw [Equiv.Perm.inv_eq_iff_eq, hρj]
  have := (Subgroup.mem_normalizer_iff.1
    (Subgroup.normalizer_commutator_ge_left _ _ hρC) _).1 hmem
  rwa [permSU_conj_swap, hρu, hρw] at this

end Swaps

section Second

variable {i j : Fin n} (hij : i ≠ j)

theorem commutator_dSU_permSU_swap {k l : Fin n} (hkl : k ≠ l) :
    ⁅dSU hkl, permSU hK (Equiv.swap k l)⁆ = dSU hkl.symm := by
  apply commutatorElement_eq_of_mul_eq
  apply eq_of_coe_eq
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
    Units.val_mul, coe_dSU, coe_dSU, coe_permSU]
  have hPd : ∀ (σ : Equiv.Perm (Fin n)) (d : Fin n → K),
      σ.permMatrix K * diagonal d = diagonal (d ∘ σ) * σ.permMatrix K := by
    intro σ d
    ext a b
    rw [mul_diagonal, diagonal_mul]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, Function.comp_apply]
    split_ifs with hab
    · rw [hab, one_mul, mul_one]
    · rw [zero_mul, mul_zero]
  rw [hPd, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2
  funext a
  obtain ⟨-, -, h1k, h1l, h1o⟩ := diagKL_spec hkl
  obtain ⟨-, -, h2l, h2k, h2o⟩ := diagKL_spec hkl.symm
  simp only [Function.comp_apply]
  by_cases hak : a = k
  · rw [hak, Equiv.swap_apply_left, h1k, h2k, h1l, ← pow_add,
      show 2 + 2 = 3 + 1 from rfl, pow_succ, omega_cube, one_mul]
  · by_cases hal : a = l
    · rw [hal, Equiv.swap_apply_right, h1l, h2l, h1k, sq]
    · rw [Equiv.swap_apply_of_ne_of_ne hak hal, h1o a hak hal, h2o a hal hak, one_mul]

theorem dSU_mem_commutator {k l : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) :
    dSU hkl ∈
      ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆ := by
  have h : ⁅dSU hkl.symm, permSU hK (Equiv.swap l k)⁆ = dSU hkl :=
    commutator_dSU_permSU_swap hkl.symm
  rw [← h]
  exact Subgroup.commutator_mem_commutator (dSU_mem_centralizer hij hkl.symm hl hk)
    (permSU_swap_mem_centralizer hij hl hk)

theorem dSU_mem_commutator_commutator (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {k l : Fin n}
    (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) :
    dSU hkl ∈
      ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆ := by
  have h : ⁅dSU hkl.symm, permSU hK (Equiv.swap l k)⁆ = dSU hkl :=
    commutator_dSU_permSU_swap hkl.symm
  rw [← h]
  exact Subgroup.commutator_mem_commutator (dSU_mem_commutator hij hl hk hkl.symm)
    (permSU_swap_mem_commutator hij hJ hl hk hkl.symm)

theorem commutator_permSU_swap_swap {k l p : Fin n} (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) :
    ⁅permSU hK (Equiv.swap k l), permSU hK (Equiv.swap k p)⁆ =
      permSU hK (Equiv.swap k l * Equiv.swap k p) := by
  apply commutatorElement_eq_of_mul_eq
  rw [← permSU_mul_rev, ← permSU_mul_rev, ← permSU_mul_rev]
  congr 1
  have h3 := (Equiv.Perm.isThreeCycle_swap_mul_swap_same hkl hkp hlp).orderOf
  have hpow : (Equiv.swap k l * Equiv.swap k p) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  have hsq : (Equiv.swap k l * Equiv.swap k p) * (Equiv.swap k l * Equiv.swap k p) =
      (Equiv.swap k l * Equiv.swap k p)⁻¹ := by
    rw [← sq]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hpow
  rw [hsq, _root_.mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

theorem permSU_threeCycle_mem_commutator_commutator (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    {k l p : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (hl : l ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hp : p ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) :
    permSU hK (Equiv.swap k l * Equiv.swap k p) ∈
      ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆ := by
  rw [← commutator_permSU_swap_swap hkl hkp hlp]
  exact Subgroup.commutator_mem_commutator (permSU_swap_mem_commutator hij hJ hk hl hkl)
    (permSU_swap_mem_commutator hij hJ hk hp hkp)

end Second

section Core

variable {i j : Fin n} (hij : i ≠ j)

@[expose] noncomputable def coreW : Subgroup (unitarySU 2 1 K n) :=
  CFSG.GroupTheory.oddOrderClosure
    ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
      ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆

theorem coreW_le :
    coreW hij ≤
      ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆ :=
  CFSG.GroupTheory.oddOrderClosure_le _

theorem oddOrderClosure_coreW : CFSG.GroupTheory.oddOrderClosure (coreW hij) = coreW hij :=
  CFSG.GroupTheory.oddOrderClosure_oddOrderClosure _

theorem mem_coreW_of_pow_three {x : unitarySU 2 1 K n}
    (hx : x ∈
      ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆)
    (hx3 : x ^ 3 = 1) : x ∈ coreW hij :=
  CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd hx
    (Odd.of_dvd_nat ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one hx3))

theorem dSU_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {k l : Fin n}
    (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) :
    dSU hkl ∈ coreW hij :=
  mem_coreW_of_pow_three hij (dSU_mem_commutator_commutator hij hJ hk hl hkl) (dSU_pow_three hkl)

theorem permSU_threeCycle_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {k l p : Fin n}
    (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (hl : l ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hp : p ∈ ({i, j}ᶜ : Finset (Fin n))) (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) :
    permSU hK (Equiv.swap k l * Equiv.swap k p) ∈ coreW hij :=
  mem_coreW_of_pow_three hij
    (permSU_threeCycle_mem_commutator_commutator hij hJ hk hl hp hkl hkp hlp)
    (permSU_pow_three_of_isThreeCycle (Equiv.Perm.isThreeCycle_swap_mul_swap_same hkl hkp hlp))

theorem commutator_mem_coreW {d g : unitarySU 2 1 K n}
    (hd : d ∈
      ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
        ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆)
    (hd3 : d ^ 3 = 1) (hg : g ∈ Subgroup.centralizer {tvTransSU hK hij}) :
    ⁅d, g⁆ ∈ coreW hij := by
  have e : ⁅d, g⁆ = d * (g * d⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  refine mul_mem (mem_coreW_of_pow_three hij hd hd3) (mem_coreW_of_pow_three hij
    (conj_mem_commutator_commutator hg (inv_mem hd)) ?_)
  rw [conj_pow, inv_pow, hd3, inv_one, mul_one, mul_inv_cancel]

theorem exists_tvESU_single_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {k : Fin n}
    (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) (c : K) :
    ∃ (s : K) (hcs : TvAdm hK i j (Pi.single k c) s),
      tvESU hK hij (Pi.single k c) s hcs ∈ coreW hij := by
  obtain ⟨l, hl, hlk⟩ := Finset.exists_mem_ne (by omega : 1 < ({i, j}ᶜ : Finset (Fin n)).card) k
  have hkl : k ≠ l := fun h => hlk h.symm
  obtain ⟨-, -, hdk, -, -⟩ := diagKL_spec hkl
  have hmB : dSU hkl ∈ unitaryBlock hK ({i, j}ᶜ : Finset (Fin n)) := dSU_mem_unitaryBlock hkl hk hl
  have hω1 : ω + 1 ≠ 0 := by
    rw [← omega_sq]
    exact pow_ne_zero 2 omega_ne_zero
  set y : Fin n → K := Pi.single k (c * (ω + 1)⁻¹) with hy
  obtain ⟨s₁, hs₁⟩ := exists_add_bar_eq hK (bar_norm hK (c * (ω + 1)⁻¹))
  have hys := tvAdm_single hK hk hs₁
  obtain ⟨hys', hconj⟩ := conj_tvESU hK hij hmB hys
  have hxy : ((dSU hkl : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y + y = Pi.single k c := by
    ext a
    rw [Pi.add_apply, coe_dSU, mulVec_diagonal, hy, Pi.single_apply, Pi.single_apply]
    split_ifs with hak
    · rw [hak, hdk]
      field_simp
    · rw [mul_zero, add_zero]
  have P := hys'.mul hK hys.bar
  rw [hxy] at P
  refine ⟨_, P, ?_⟩
  have e : ⁅dSU hkl, tvESU hK hij y s₁ hys⁆ = tvESU hK hij (Pi.single k c) _ P := by
    rw [commutatorElement_def, hconj, tvESU_inv, tvESU_mul]
    exact tvESU_congr hK hij hxy rfl _ _
  rw [← e]
  exact commutator_mem_coreW hij (dSU_mem_commutator_commutator hij hJ hk hl hkl)
    (dSU_pow_three hkl) (tvRadical_le_centralizer hK hij (tvESU_mem_tvRadical hK hij hys))

theorem exists_tvESU_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {x : Fin n → K}
    (hxi : x i = 0) (hxj : x j = 0) :
    ∃ (s : K) (hxs : TvAdm hK i j x s), tvESU hK hij x s hxs ∈ coreW hij := by
  have hsum : x = ∑ k ∈ ({i, j}ᶜ : Finset (Fin n)), Pi.single k (x k) := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with ha
    · rfl
    · rcases eq_or_eq_or_mem_compl i j a with h' | h' | h'
      · rw [h', hxi]
      · rw [h', hxj]
      · exact absurd h' ha
  have key := Finset.sum_induction (s := ({i, j}ᶜ : Finset (Fin n)))
    (fun k => Pi.single k (x k))
    (fun y => y i = 0 ∧ y j = 0 ∧
      ∃ (s : K) (hys : TvAdm hK i j y s), tvESU hK hij y s hys ∈ coreW hij)
    (fun a b ha hb => by
      obtain ⟨-, -, s, hs, hsD⟩ := ha
      obtain ⟨-, -, s', hs', hs'D⟩ := hb
      refine ⟨(hs.mul hK hs').1, (hs.mul hK hs').2.1, _, hs.mul hK hs', ?_⟩
      rw [← tvESU_mul hK hij hs hs']
      exact mul_mem hsD hs'D)
    ⟨rfl, rfl, 0, TvAdm.zero_zero hK, by rw [tvESU_zero_zero]; exact one_mem _⟩
    (fun k hk => by
      obtain ⟨s, hs, hsD⟩ := exists_tvESU_single_mem_coreW hij hJ hk (x k)
      exact ⟨hs.1, hs.2.1, s, hs, hsD⟩)
  rw [← hsum] at key
  exact key.2.2

theorem eq_zero_or_eq_one_of_tvAdm_zero {t : K} (ht : TvAdm hK i j 0 t) : t = 0 ∨ t = 1 := by
  have h1 := ht.2.2
  rw [tvBar_zero, zero_dotProduct, bar_apply_K] at h1
  have h2 : t * (t + 1) = 0 := by
    rw [mul_add, mul_one, ← sq]
    rw [add_comm] at h1
    exact h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact Or.inl h
  · right
    have := (CharTwo.add_eq_zero (R := K)).1 h
    exact this

theorem tvTransSU_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) :
    tvTransSU hK hij ∈ coreW hij := by
  obtain ⟨k, hk⟩ : ({i, j}ᶜ : Finset (Fin n)).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨s, hs, hsW⟩ := exists_tvESU_single_mem_coreW hij hJ hk 1
  have e : tvESU hK hij (Pi.single k 1) s hs * tvESU hK hij (Pi.single k 1) s hs =
      tvTransSU hK hij := by
    rw [tvESU_mul, tvTransSU]
    refine tvESU_congr hK hij ?_ ?_ _ _
    · ext a
      exact CharTwo.add_self_eq_zero _
    · rw [CharTwo.add_self_eq_zero, zero_add, tvBar_single, single_dotProduct, Pi.single_eq_same,
        map_one, one_mul]
  rw [← e]
  exact mul_mem hsW hsW

theorem tvESU_zero_mem_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) {t : K}
    (ht : TvAdm hK i j 0 t) : tvESU hK hij 0 t ht ∈ coreW hij := by
  rcases eq_zero_or_eq_one_of_tvAdm_zero ht with rfl | rfl
  · rw [tvESU_zero_zero]
    exact one_mem _
  · exact tvTransSU_mem_coreW hij hJ

theorem tvRadical_le_coreW (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) :
    tvRadical hK hij ≤ coreW hij := by
  intro r hr
  obtain ⟨x, s, hxs, rfl⟩ := exists_eq_tvESU_of_mem_tvRadical hK hij hr
  obtain ⟨s', hxs', hW⟩ := exists_tvESU_mem_coreW hij hJ hxs.1 hxs.2.1
  have ht : TvAdm hK i j 0 (s' + s) := by
    refine ⟨rfl, rfl, ?_⟩
    rw [tvBar_zero, zero_dotProduct, map_add]
    linear_combination hxs'.2.2 + hxs.2.2 + (tvBar hK x ⬝ᵥ x) * CharTwo.two_eq_zero (R := K)
  have e : tvESU hK hij x s hxs = tvESU hK hij x s' hxs' * tvESU hK hij 0 (s' + s) ht := by
    rw [tvESU_mul]
    refine tvESU_congr hK hij (by rw [add_zero]) ?_ _ _
    rw [dotProduct_zero, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [e]
  exact mul_mem hW (tvESU_zero_mem_coreW hij hJ ht)

end Core

end CFSG.RankThree.GF2n.Stroth78.Sec4PSU
