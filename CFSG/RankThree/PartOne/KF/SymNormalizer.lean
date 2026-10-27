module

public import CFSG.RankThree.PartOne.KF.SymTorus
public import Certificates.Certificate4951

public section

namespace CFSG.RankThree.PartOne.KFU

open Equiv

theorem perm_three_conj : ∀ t₁ t₂ : Perm (Fin 3),
    (t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1 ∧ t₁ * t₂ ≠ 1) →
      ∃ π : Perm (Fin 3), π * swap 0 1 * π⁻¹ = t₁ ∧ π * swap 1 2 * π⁻¹ = t₂ := by
  decide

theorem perm_four_conj_two : ∀ t₁ t₂ : Perm (Fin 4),
    (t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ ≠ 1 ∧ (t₁ * t₂) ^ 3 = 1 ∧ t₁ * t₂ ≠ 1) →
      ∃ π : Perm (Fin 4), π * swap 0 1 * π⁻¹ = t₁ ∧ π * swap 1 2 * π⁻¹ = t₂ :=
  Certificates.certificate4951.1

theorem perm_four_conj_three : ∀ t : Perm (Fin 4),
    (t * t = 1 ∧ t ≠ 1 ∧ (swap 1 2 * t) ^ 3 = 1 ∧ swap 1 2 * t ≠ 1 ∧ (swap 0 1 * t) ^ 2 = 1 ∧
      swap 0 1 * t ≠ 1) → t = swap 2 3 := by
  decide

theorem perm_three_aut_inner (α : Perm (Fin 3) →* Perm (Fin 3)) (hα : Function.Injective α) :
    ∃ π : Perm (Fin 3), ∀ σ, α σ = π * σ * π⁻¹ := by
  have hne : ∀ x : Perm (Fin 3), x ≠ 1 → α x ≠ 1 := fun x hx h =>
    hx (hα (by rw [h, map_one]))
  have h1 : swap (0 : Fin 3) 1 * swap 0 1 = 1 := by decide
  have h2 : swap (1 : Fin 3) 2 * swap 1 2 = 1 := by decide
  have h3 : (swap (0 : Fin 3) 1 * swap 1 2) ^ 3 = 1 := by decide
  obtain ⟨π, hπ1, hπ2⟩ := perm_three_conj (α (swap 0 1)) (α (swap 1 2))
    ⟨by rw [← map_mul, h1, map_one], hne _ (by decide), by rw [← map_mul, h2, map_one],
      hne _ (by decide), by rw [← map_mul, ← map_pow, h3, map_one],
      by rw [← map_mul]; exact hne _ (by decide)⟩
  refine ⟨π, fun σ => ?_⟩
  have hgen := MonoidHom.eqOn_closureM (f := α) (g := (MulAut.conj π).toMonoidHom)
    (s := Set.range fun i : Fin 2 => swap i.castSucc i.succ) (by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hπ1.symm
      · exact hπ2.symm)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ 2] at hgen
  exact hgen (Submonoid.mem_top σ)

theorem perm_four_aut_inner (α : Perm (Fin 4) →* Perm (Fin 4)) (hα : Function.Injective α) :
    ∃ π : Perm (Fin 4), ∀ σ, α σ = π * σ * π⁻¹ := by
  have hne : ∀ x : Perm (Fin 4), x ≠ 1 → α x ≠ 1 := fun x hx h =>
    hx (hα (by rw [h, map_one]))
  have h1 : swap (0 : Fin 4) 1 * swap 0 1 = 1 := by decide
  have h2 : swap (1 : Fin 4) 2 * swap 1 2 = 1 := by decide
  have h3 : swap (2 : Fin 4) 3 * swap 2 3 = 1 := by decide
  have h12 : (swap (0 : Fin 4) 1 * swap 1 2) ^ 3 = 1 := by decide
  have h23 : (swap (1 : Fin 4) 2 * swap 2 3) ^ 3 = 1 := by decide
  have h13 : (swap (0 : Fin 4) 1 * swap 2 3) ^ 2 = 1 := by decide
  obtain ⟨π, hπ1, hπ2⟩ := perm_four_conj_two (α (swap 0 1)) (α (swap 1 2))
    ⟨by rw [← map_mul, h1, map_one], hne _ (by decide), by rw [← map_mul, h2, map_one],
      hne _ (by decide), by rw [← map_mul, ← map_pow, h12, map_one],
      by rw [← map_mul]; exact hne _ (by decide)⟩
  have hc1 : MulAut.conj π⁻¹ (α (swap 0 1)) = swap 0 1 := by
    rw [← hπ1, MulAut.conj_apply]; group
  have hc2 : MulAut.conj π⁻¹ (α (swap 1 2)) = swap 1 2 := by
    rw [← hπ2, MulAut.conj_apply]; group
  have hcα : ∀ x y : Perm (Fin 4), MulAut.conj π⁻¹ (α x) * MulAut.conj π⁻¹ (α y) =
      MulAut.conj π⁻¹ (α (x * y)) := fun x y => by rw [← map_mul, ← map_mul]
  have hcpow : ∀ (x : Perm (Fin 4)) (k : ℕ), (MulAut.conj π⁻¹ (α x)) ^ k =
      MulAut.conj π⁻¹ (α (x ^ k)) := fun x k => by rw [← map_pow, ← map_pow]
  have hc3 : MulAut.conj π⁻¹ (α (swap 2 3)) = swap 2 3 := by
    apply perm_four_conj_three
    have hcne : ∀ x : Perm (Fin 4), x ≠ 1 → MulAut.conj π⁻¹ (α x) ≠ 1 := fun x hx h =>
      hne x hx ((MulEquiv.map_eq_one_iff (MulAut.conj π⁻¹)).mp h)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcα, h3, map_one, map_one]
    · exact hcne _ (by decide)
    · rw [← hc2, hcα, hcpow, h23, map_one, map_one]
    · rw [← hc2, hcα]
      exact hcne _ (by decide)
    · rw [← hc1, hcα, hcpow, h13, map_one, map_one]
    · rw [← hc1, hcα]
      exact hcne _ (by decide)
  have hπ3 : α (swap 2 3) = π * swap 2 3 * π⁻¹ := by
    have h := hc3
    rw [MulAut.conj_apply, inv_inv] at h
    calc α (swap 2 3) = π * (π⁻¹ * α (swap 2 3) * π) * π⁻¹ := by group
      _ = π * swap 2 3 * π⁻¹ := by rw [h]
  refine ⟨π, fun σ => ?_⟩
  have hgen := MonoidHom.eqOn_closureM (f := α) (g := (MulAut.conj π).toMonoidHom)
    (s := Set.range fun i : Fin 3 => swap i.castSucc i.succ) (by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hπ1.symm
      · exact hπ2.symm
      · exact hπ3)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ 3] at hgen
  exact hgen (Submonoid.mem_top σ)

theorem perm_five_conj_two : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    (swap a b * swap c d) ^ 3 = 1 → swap a b * swap c d ≠ 1 →
      ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d :=
  Certificates.certificate4951.2.1

theorem perm_five_conj_three : ∀ a b c d e f : Fin 5,
    (a ≠ b ∧ c ≠ d ∧ e ≠ f ∧ (swap a b * swap c d) ^ 3 = 1 ∧ swap a b * swap c d ≠ 1 ∧
    (swap c d * swap e f) ^ 3 = 1 ∧ swap c d * swap e f ≠ 1 ∧
    (swap a b * swap e f) ^ 2 = 1 ∧ swap a b * swap e f ≠ 1) →
      ∃ π : Perm (Fin 5), π * swap 0 1 * π⁻¹ = swap a b ∧ π * swap 1 2 * π⁻¹ = swap c d ∧
        π * swap 2 3 * π⁻¹ = swap e f :=
  Certificates.certificate4951.2.2.1

theorem perm_five_conj_four : ∀ (π : Perm (Fin 5)) (g h : Fin 5),
    (g ≠ h ∧ (π * swap 2 3 * π⁻¹ * swap g h) ^ 3 = 1 ∧ π * swap 2 3 * π⁻¹ * swap g h ≠ 1 ∧
    (π * swap 0 1 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 0 1 * π⁻¹ * swap g h ≠ 1 ∧
    (π * swap 1 2 * π⁻¹ * swap g h) ^ 2 = 1 ∧ π * swap 1 2 * π⁻¹ * swap g h ≠ 1) →
      swap g h = π * swap 3 4 * π⁻¹ :=
  Certificates.certificate4951.2.2.2.1

theorem perm_five_aut_inner (α : Perm (Fin 5) →* Perm (Fin 5)) (hα : Function.Injective α)
    (htrans : ∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5, c ≠ d ∧ α (swap a b) = swap c d) :
    ∃ π : Perm (Fin 5), ∀ σ, α σ = π * σ * π⁻¹ := by
  have hne : ∀ x : Perm (Fin 5), x ≠ 1 → α x ≠ 1 := fun x hx h => hx (hα (by rw [h, map_one]))
  obtain ⟨a, b, hab, h1⟩ := htrans 0 1 (by decide)
  obtain ⟨c, d, hcd, h2⟩ := htrans 1 2 (by decide)
  obtain ⟨e, f, hef, h3⟩ := htrans 2 3 (by decide)
  obtain ⟨g, h, hgh, h4⟩ := htrans 3 4 (by decide)
  have r12 : (swap a b * swap c d) ^ 3 = 1 := by
    rw [← h1, ← h2, ← map_mul, ← map_pow,
      show (swap (0 : Fin 5) 1 * swap 1 2) ^ 3 = 1 by decide, map_one]
  have n12 : swap a b * swap c d ≠ 1 := by
    rw [← h1, ← h2, ← map_mul]
    exact hne _ (by decide)
  have r23 : (swap c d * swap e f) ^ 3 = 1 := by
    rw [← h2, ← h3, ← map_mul, ← map_pow,
      show (swap (1 : Fin 5) 2 * swap 2 3) ^ 3 = 1 by decide, map_one]
  have n23 : swap c d * swap e f ≠ 1 := by
    rw [← h2, ← h3, ← map_mul]
    exact hne _ (by decide)
  have r13 : (swap a b * swap e f) ^ 2 = 1 := by
    rw [← h1, ← h3, ← map_mul, ← map_pow,
      show (swap (0 : Fin 5) 1 * swap 2 3) ^ 2 = 1 by decide, map_one]
  have n13 : swap a b * swap e f ≠ 1 := by
    rw [← h1, ← h3, ← map_mul]
    exact hne _ (by decide)
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := perm_five_conj_three a b c d e f
    ⟨hab, hcd, hef, r12, n12, r23, n23, r13, n13⟩
  have r34 : (swap e f * swap g h) ^ 3 = 1 := by
    rw [← h3, ← h4, ← map_mul, ← map_pow,
      show (swap (2 : Fin 5) 3 * swap 3 4) ^ 3 = 1 by decide, map_one]
  have n34 : swap e f * swap g h ≠ 1 := by
    rw [← h3, ← h4, ← map_mul]
    exact hne _ (by decide)
  have r14 : (swap a b * swap g h) ^ 2 = 1 := by
    rw [← h1, ← h4, ← map_mul, ← map_pow,
      show (swap (0 : Fin 5) 1 * swap 3 4) ^ 2 = 1 by decide, map_one]
  have n14 : swap a b * swap g h ≠ 1 := by
    rw [← h1, ← h4, ← map_mul]
    exact hne _ (by decide)
  have r24 : (swap c d * swap g h) ^ 2 = 1 := by
    rw [← h2, ← h4, ← map_mul, ← map_pow,
      show (swap (1 : Fin 5) 2 * swap 3 4) ^ 2 = 1 by decide, map_one]
  have n24 : swap c d * swap g h ≠ 1 := by
    rw [← h2, ← h4, ← map_mul]
    exact hne _ (by decide)
  have hπ4 := perm_five_conj_four π g h ⟨hgh, by rw [hπ3]; exact r34, by rw [hπ3]; exact n34,
    by rw [hπ1]; exact r14, by rw [hπ1]; exact n14, by rw [hπ2]; exact r24,
    by rw [hπ2]; exact n24⟩
  refine ⟨π, fun σ => ?_⟩
  have hgen := MonoidHom.eqOn_closureM (f := α) (g := (MulAut.conj π).toMonoidHom)
    (s := Set.range fun i : Fin 4 => swap i.castSucc i.succ) (by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact h1.trans hπ1.symm
      · exact h2.trans hπ2.symm
      · exact h3.trans hπ3.symm
      · exact h4.trans hπ4)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ 4] at hgen
  exact hgen (Submonoid.mem_top σ)

theorem perm_five_cycle : ∀ π : Perm (Fin 5), π ^ 5 = 1 → π = 1 ∨
    ∃ a, π a ≠ a ∧ π (π a) ≠ a ∧ π (π (π a)) ≠ a :=
  Certificates.certificate4951.2.2.2.2

section Main

variable {n p : ℕ} {K : Type} [Field K]

theorem symAct_swap_torusEltV {i j : Fin n} (hij : i ≠ j) (u : rootsOfUnity p K) :
    symAct p K (swap i j) (torusEltV p hij u) = (torusEltV p hij u)⁻¹ := by
  apply Subtype.ext
  funext k
  rw [coe_symAct, coe_torusEltV]
  show torusElt i j (u : Kˣ) ((swap i j).symm k) = (torusElt i j (u : Kˣ) k)⁻¹
  rw [Equiv.symm_swap]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, torusElt_apply_right hij, torusElt_apply_left hij]
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, torusElt_apply_left hij, torusElt_apply_right hij, inv_inv]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, torusElt_apply_other hki hkj, inv_one]

theorem exists_eq_torusEltV_of_swap_inv (hp : p.Prime) (hp2 : p ≠ 2) {i j : Fin n} (hij : i ≠ j)
    (x : torusVec p n K) (h : symAct p K (swap i j) x = x⁻¹) :
    ∃ u : rootsOfUnity p K, x = torusEltV p hij u := by
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hother : ∀ k, k ≠ i → k ≠ j → (x : Fin n → Kˣ) k = 1 := by
    intro k hki hkj
    have h1 := congrFun (congrArg Subtype.val h) k
    rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj] at h1
    have h1' : (x : Fin n → Kˣ) k = ((x : Fin n → Kˣ) k)⁻¹ := h1
    have h2 : (x : Fin n → Kˣ) k ^ 2 = 1 := by
      rw [sq]
      calc (x : Fin n → Kˣ) k * (x : Fin n → Kˣ) k
          = (x : Fin n → Kˣ) k * ((x : Fin n → Kˣ) k)⁻¹ := by rw [← h1']
        _ = 1 := mul_inv_cancel _
    have h4 := pow_gcd_eq_one.mpr ⟨x.2.1 k, h2⟩
    rwa [hcop, pow_one] at h4
  have hi : (x : Fin n → Kˣ) j = ((x : Fin n → Kˣ) i)⁻¹ := by
    have h1 := congrFun (congrArg Subtype.val h) i
    rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_left] at h1
    exact h1
  refine ⟨⟨(x : Fin n → Kˣ) i, (mem_rootsOfUnity p _).mpr (x.2.1 i)⟩, ?_⟩
  apply Subtype.ext
  funext k
  rw [coe_torusEltV]
  by_cases hki : k = i
  · subst hki
    rw [torusElt_apply_left hij]
  · by_cases hkj : k = j
    · subst hkj
      rw [torusElt_apply_right hij, hi]
    · rw [torusElt_apply_other hki hkj, hother k hki hkj]

theorem exists_unit_pow_eq [NeZero p] {ζ v : Kˣ} (hζ : IsPrimitiveRoot ζ p) (hv : v ^ p = 1) :
    ∃ m : ℕ, ζ ^ m = v := by
  obtain ⟨m, -, hm⟩ := (IsPrimitiveRoot.coe_units_iff.mpr hζ).eq_pow_of_pow_eq_one
    (ξ := (v : K)) (by rw [← Units.val_pow_eq_pow_val, hv, Units.val_one])
  exact ⟨m, Units.ext (by rw [Units.val_pow_eq_pow_val, hm])⟩

theorem exists_pow_of_commutes (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (φ' : MulAut (torusVec p n K))
    (hcomm : ∀ σ : Perm (Fin n), φ' * symAut p K σ = symAut p K σ * φ') :
    ∃ e : ℕ, ∀ d : torusVec p n K, φ' d = d ^ e := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := ⟨1, by omega⟩
  have hij : i₀ ≠ j₀ := fun h => by simpa [i₀, j₀] using congrArg Fin.val h
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ.pow_eq_one⟩
  let d₀ : torusVec p n K := torusEltV p hij z
  have h2 : symAct p K (swap i₀ j₀) (φ' d₀) = (φ' d₀)⁻¹ := by
    have h := congrArg (fun m : MulAut (torusVec p n K) => m d₀) (hcomm (swap i₀ j₀))
    simp only [MulAut.mul_apply, symAut_apply, d₀, symAct_swap_torusEltV, map_inv] at h
    exact h.symm
  obtain ⟨u, hu⟩ := exists_eq_torusEltV_of_swap_inv hp hp2 hij (φ' d₀) h2
  obtain ⟨e, he⟩ := exists_unit_pow_eq hζ (v := (u : Kˣ)) ((mem_rootsOfUnity p _).mp u.2)
  have hu' : u = z ^ e := Subtype.ext he.symm
  have hφd₀ : φ' d₀ = d₀ ^ e := by rw [hu, hu', map_pow]
  have hpair : ∀ (k l : Fin n) (hkl : k ≠ l) (v : rootsOfUnity p K),
      φ' (torusEltV p hkl v) = (torusEltV p hkl v) ^ e := by
    intro k l hkl v
    obtain ⟨τ, rfl, rfl⟩ := exists_perm_pair hij hkl
    obtain ⟨m, hm⟩ := exists_unit_pow_eq hζ (v := (v : Kˣ)) ((mem_rootsOfUnity p _).mp v.2)
    have hv : v = z ^ m := Subtype.ext hm.symm
    have hτ : torusEltV p hkl z = symAct p K τ d₀ := (symAct_torusEltV τ hij z).symm
    have hc : φ' (symAct p K τ d₀) = symAct p K τ (φ' d₀) := by
      have h := congrArg (fun m : MulAut (torusVec p n K) => m d₀) (hcomm τ)
      simpa only [MulAut.mul_apply, symAut_apply] using h
    have hg : φ' (torusEltV p hkl z) = (torusEltV p hkl z) ^ e := by
      rw [hτ, hc, hφd₀, map_pow]
    rw [hv, map_pow, map_pow, hg, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨e, fun d => ?_⟩
  have hd : d ∈ torusSpan p n K := by rw [torusSpan_eq_top]; trivial
  unfold torusSpan at hd
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, u, rfl⟩ := hx
    exact hpair i j hij u
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_pow]
  | inv x _ hx => rw [map_inv, hx, inv_pow]

theorem iter_pow_apply (π : Perm (Fin n)) (e : ℕ) (φ φ' : MulAut (torusVec p n K))
    (hφ : φ = symAut p K π * φ') (hφ' : ∀ d, φ' d = d ^ e) (k : ℕ) (d : torusVec p n K) :
    (φ ^ k) d = (symAct p K (π ^ k) d) ^ (e ^ k) := by
  induction k generalizing d with
  | zero => simp [symAct_one]
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hφ, MulAut.mul_apply, hφ', symAut_apply, map_pow,
      map_pow, ← symAct_mul, ← pow_mul, ← pow_succ', ← pow_succ]

theorem exists_symAut_of_symNormalizer [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Perm (Fin n) →* Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (torusVec p n K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ σ : Perm (Fin n), ∃ τ : Perm (Fin n), φ * symAut p K σ * φ⁻¹ = symAut p K τ) :
    ∃ π : Perm (Fin n), π ^ p = 1 ∧ φ = symAut p K π := by
  classical
  have hinj := symAut_injective (n := n) (K := K) hp hp2 hζ
  choose α hα using hnorm
  let αh : Perm (Fin n) →* Perm (Fin n) :=
    { toFun := α
      map_one' := hinj (by rw [← hα 1, map_one, mul_one, mul_inv_cancel])
      map_mul' := fun σ τ => hinj (by
        rw [map_mul (symAut p K) (α σ) (α τ), ← hα σ, ← hα τ, ← hα (σ * τ), map_mul]
        group) }
  have hαinj : Function.Injective αh := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply hinj
    have h1 := hα σ
    have h2 : α σ = 1 := hσ
    rw [h2, map_one] at h1
    rw [map_one]
    calc symAut p K σ = φ⁻¹ * (φ * symAut p K σ * φ⁻¹) * φ := by group
      _ = 1 := by rw [h1]; group
  have hαtrans : ∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧
      α (Equiv.swap a b) = Equiv.swap c d := by
    intro a b hab
    have hsw1 : Equiv.swap a b * Equiv.swap a b = 1 := Equiv.swap_mul_self a b
    have hτ1 : α (Equiv.swap a b) * α (Equiv.swap a b) = 1 := by
      have : αh (Equiv.swap a b * Equiv.swap a b) = 1 := by rw [hsw1, map_one]
      rw [map_mul] at this
      exact this
    have hτne : α (Equiv.swap a b) ≠ 1 := by
      intro h
      have : αh (Equiv.swap a b) = αh 1 := by rw [map_one]; exact h
      have := hαinj this
      have h2 := congrArg (fun τ : Perm (Fin n) => τ a) this
      simp [Equiv.swap_apply_left] at h2
      exact hab h2.symm
    have hmoved : movedSub p K (α (Equiv.swap a b)) = (movedSub p K (Equiv.swap a b)).map
        φ.toMonoidHom := by
      unfold movedSub
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        refine ⟨symAct p K (Equiv.swap a b) (φ.symm d) * (φ.symm d)⁻¹, ⟨φ.symm d, rfl⟩, ?_⟩
        have h1 := congrArg (fun m : MulAut (torusVec p n K) => m d) (hα (Equiv.swap a b))
        simp only [MulAut.mul_apply, MulAut.inv_apply, symAut_apply] at h1
        show φ (symAct p K (Equiv.swap a b) (φ.symm d) * (φ.symm d)⁻¹) = _
        rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
        have h2 : φ (symAct p K (Equiv.swap a b) (φ.symm d)) =
            symAct p K (α (Equiv.swap a b)) d := by
          rw [← h1]
        rw [h2]
      · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
        refine ⟨φ d, ?_⟩
        have h1 := congrArg (fun m : MulAut (torusVec p n K) => m (φ d)) (hα (Equiv.swap a b))
        simp only [MulAut.mul_apply, MulAut.inv_apply, symAut_apply, MulEquiv.symm_apply_apply]
          at h1
        show symAct p K (α (Equiv.swap a b)) (φ d) * (φ d)⁻¹ =
          φ (symAct p K (Equiv.swap a b) d * d⁻¹)
        rw [map_mul, map_inv, ← h1]
    have hcardτ : Nat.card (movedSub p K (α (Equiv.swap a b))) = p := by
      rw [hmoved, Subgroup.card_map_of_injective φ.injective]
      exact card_movedSub_swap hp hp2 hζ hab
    rcases involution_cases _ hτ1 hτne with ⟨c, d, hcd, h⟩ | ⟨a', b', c', d', hab', hac', hada,
        hbc', hbd', hcd', h1, h2, h3, h4⟩
    · exact ⟨c, d, hcd, h⟩
    · exact absurd hcardτ (card_movedSub_ne_prime_of_double_swap hp hp2 hζ _ hab' hac' hbc' hcd'
        h1 h2 h3 h4)
  obtain ⟨π, hπ⟩ := hinner αh hαinj hαtrans
  set φ' : MulAut (torusVec p n K) := (symAut p K π)⁻¹ * φ with hφ'def
  have hφdef : φ = symAut p K π * φ' := by rw [hφ'def, mul_inv_cancel_left]
  have hcomm : ∀ σ, φ' * symAut p K σ = symAut p K σ * φ' := by
    intro σ
    have h1 := hα σ
    have h2 : α σ = π * σ * π⁻¹ := hπ σ
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc (symAut p K π)⁻¹ * φ * symAut p K σ
        = (symAut p K π)⁻¹ * (φ * symAut p K σ * φ⁻¹) * φ := by group
      _ = (symAut p K π)⁻¹ * (symAut p K π * symAut p K σ * (symAut p K π)⁻¹) * φ := by rw [h1]
      _ = symAut p K σ * ((symAut p K π)⁻¹ * φ) := by group
  obtain ⟨e, he⟩ := exists_pow_of_commutes hp hp2 (by omega) hζ φ' hcomm
  have hiter := iter_pow_apply π e φ φ' hφdef he
  obtain ⟨ζ, hζ'⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ'.pow_eq_one⟩
  have hζ1 : ζ ≠ 1 := hζ'.ne_one hp.one_lt
  have hπp : π ^ p = 1 := by
    have hρ : ∀ d : torusVec p n K, (symAct p K (π ^ p) d) ^ (e ^ p) = d := fun d => by
      have := hiter p d
      rw [hφ, MulAut.one_apply] at this
      exact this.symm
    have key : ∀ i j : Fin n, i ≠ j → (π ^ p) i = i ∨ (π ^ p) j = i := by
      intro i j hij
      by_contra hcon
      push Not at hcon
      have h1 := hρ (torusEltV p hij z)
      rw [symAct_torusEltV] at h1
      have h2 := congrFun (congrArg Subtype.val h1) i
      rw [Subgroup.coe_pow, Pi.pow_apply, coe_torusEltV, coe_torusEltV,
        torusElt_apply_other (Ne.symm hcon.1) (Ne.symm hcon.2), torusElt_apply_left hij,
        one_pow] at h2
      exact hζ1 h2.symm
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, (π ^ p) i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨j₁, j₂, hj₁, hj₂, hj12⟩ : ∃ j₁ j₂ : Fin n, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ := by
      by_cases ha : i.val = 0
      · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
          fun h => by simp [Fin.ext_iff] at h; omega, by simp [Fin.ext_iff]⟩
      · by_cases hb : i.val = 1
        · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
            fun h => by simp [Fin.ext_iff] at h; omega, by simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
            fun h => by simp [Fin.ext_iff] at h; omega, by simp [Fin.ext_iff]⟩
    have e1 := (key i j₁ hj₁.symm).resolve_left hi
    have e2 := (key i j₂ hj₂.symm).resolve_left hi
    exact hj12 ((π ^ p).injective (e1.trans e2.symm))
  have hdp : ∀ d : torusVec p n K, d ^ p = 1 := fun d => Subtype.ext (funext fun i => d.2.1 i)
  have hep : ∀ d : torusVec p n K, d ^ (e ^ p) = d := fun d => by
    have := hiter p d
    rw [hφ, MulAut.one_apply, hπp, symAct_one] at this
    exact this.symm
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j : Fin n, i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have h2 := congrFun (congrArg Subtype.val (hep (torusEltV p hij₀ z))) i₀
  rw [Subgroup.coe_pow, Pi.pow_apply, coe_torusEltV, torusElt_apply_left hij₀] at h2
  have h2' : ζ ^ (e ^ p) = ζ := h2
  have hpos : 1 ≤ e ^ p := by
    by_contra h
    have h0 : e ^ p = 0 := by omega
    rw [h0, pow_zero] at h2'
    exact hζ1 h2'.symm
  have hdvd : p ∣ e ^ p - 1 := by
    rw [← hζ'.pow_eq_one_iff_dvd]
    have h3 : ζ ^ (e ^ p - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, h2', one_mul]
    exact mul_right_cancel h3
  have hmod : 1 ≡ e ^ p [MOD p] := (Nat.modEq_iff_dvd' hpos).mpr hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : ((e : ℕ) : ZMod p) = 1 := by
    have h4 : ((1 : ℕ) : ZMod p) = ((e ^ p : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h4
    exact h4.symm
  have hmod1 : e ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hz1, Nat.cast_one])
  have hemod : e % p = 1 := by
    have h5 : e % p = 1 % p := hmod1
    rw [h5]
    exact Nat.mod_eq_of_lt hp.one_lt
  have hφ'1 : φ' = 1 := MulEquiv.ext fun d => by
    rw [he, pow_eq_pow_mod e (hdp d), hemod, pow_one]
    rfl
  refine ⟨π, hπp, ?_⟩
  rw [hφdef, hφ'1, mul_one]

theorem eq_one_of_symNormalizer [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hpn : ∀ π : Perm (Fin n), π ^ p = 1 → π = 1) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Perm (Fin n) →* Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (torusVec p n K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ σ : Perm (Fin n), ∃ τ : Perm (Fin n), φ * symAut p K σ * φ⁻¹ = symAut p K τ) :
    φ = 1 := by
  obtain ⟨π, hπ, rfl⟩ := exists_symAut_of_symNormalizer hp hp2 hn hζ hinner φ hφ hnorm
  rw [hpn π hπ, map_one]

end Main

end CFSG.RankThree.PartOne.KFU
