module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot
public import CFSG.RankThree.PartOne.CTP.LinearEdge
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTraceField

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.BenderSuzuki.MatrixGroups

section Basic

variable {F : Type} [Field F]

@[expose] def u2 (a : F) : SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a

@[expose] def l2 (b : F) : SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) b

theorem u2_coe (a : F) : (u2 a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u2, SpecialLinearGroup.transvection_coe]

theorem l2_coe (b : F) : (l2 b : Matrix (Fin 2) (Fin 2) F) = !![1, 0; b, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l2, SpecialLinearGroup.transvection_coe]

theorem u2_add (a b : F) : u2 (a + b) = u2 a * u2 b :=
  SpecialLinearGroup.transvection_add _ a b

theorem u2_zero : u2 (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _

theorem u2_injective : Function.Injective (u2 : F → SpecialLinearGroup (Fin 2) F) :=
  SpecialLinearGroup.transvection_injective (show (0 : Fin 2) ≠ 1 by decide)

theorem l2_zero : l2 (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _

theorem l2_add (a b : F) : l2 (a + b) = l2 a * l2 b :=
  SpecialLinearGroup.transvection_add _ a b

variable [CharP F 2]

theorem u2_mul_self (a : F) : u2 a * u2 a = 1 := by
  rw [← u2_add, CharTwo.add_self_eq_zero, u2_zero]

theorem l2_mul_self (b : F) : l2 b * l2 b = 1 := by
  rw [← l2_add, CharTwo.add_self_eq_zero, l2_zero]

omit [CharP F 2] in
theorem u2_mul_l2_ne {a b : F} (hab : a * b ≠ 0) : u2 a * l2 b ≠ l2 b * u2 a := by
  intro h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [u2_coe, l2_coe, Matrix.mul_apply, Fin.sum_univ_two] at h1
  exact hab (by rcases h1 with h | h <;> simp [h])

omit [CharP F 2] in
theorem coe_u2_mul_l2 (a b : F) :
    ((u2 a * l2 b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1 + a * b, a; b, 1] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem trace_u2_mul_l2 (a b : F) :
    Matrix.trace ((u2 a * l2 b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      a * b := by
  rw [coe_u2_mul_l2, Matrix.trace_fin_two]
  simp
  linear_combination (1 : F) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem trace_u2_mul_l2_mul_u2 (x y b : F) :
    Matrix.trace ((u2 y * l2 b * u2 (x + y) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = x * b := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (b * y + 1) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem trace_pair (x y b : F) :
    Matrix.trace ((u2 x * l2 b * (u2 y * l2 b * u2 (x + y)) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = y ^ 2 * b ^ 2 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (b ^ 2 * x * y + 2 * b * x + 2 * b * y + 1) *
    (CharTwo.two_eq_zero : (2 : F) = 0)

end Basic

section Subgroups

variable {F : Type} [Field F]

@[expose] def mkPSL (F : Type) [Field F] : SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))

theorem mkPSL_injective [CharP F 2] : Function.Injective (mkPSL F) := by
  rw [← MonoidHom.ker_eq_bot_iff, mkPSL, QuotientGroup.ker_mk', center_sl2_eq_bot]

@[expose] def rootHom (k : Subfield F) (a₁ a₂ : F) :
    Multiplicative (k × k) →* SpecialLinearGroup (Fin 2) F where
  toFun c := u2 ((c.toAdd.1 : F) * a₁ + (c.toAdd.2 : F) * a₂)
  map_one' := by simp [u2_zero]
  map_mul' c d := by
    rw [← u2_add]
    congr 1
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Subfield.coe_add]
    ring

theorem rootHom_injective {k : Subfield F} {a₁ a₂ : F} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ / a₁ ∉ k) :
    Function.Injective (rootHom k a₁ a₂) := by
  intro c d hcd
  have h := u2_injective hcd
  have hc2 : (c.toAdd.2 : F) = d.toAdd.2 := by
    by_contra hne
    apply ha₂
    have hne' : (d.toAdd.2 : F) - c.toAdd.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have : a₂ / a₁ = ((c.toAdd.1 - d.toAdd.1 : k) : F) / ((d.toAdd.2 - c.toAdd.2 : k) : F) := by
      push_cast
      field_simp
      linear_combination -h
    rw [this]
    exact k.div_mem (c.toAdd.1 - d.toAdd.1).2 (d.toAdd.2 - c.toAdd.2).2
  have hc1 : (c.toAdd.1 : F) = d.toAdd.1 := by
    rw [hc2] at h
    have : ((c.toAdd.1 : F) - d.toAdd.1) * a₁ = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 ha₁
  exact Multiplicative.toAdd.injective (Prod.ext (Subtype.ext hc1) (Subtype.ext hc2))

theorem card_sq_dvd_card {k : Subfield F} {a₁ a₂ : F} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ / a₁ ∉ k)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c₁ ∈ k, ∀ c₂ ∈ k, u2 (c₁ * a₁ + c₂ * a₂) ∈ M) :
    Nat.card k * Nat.card k ∣ Nat.card M := by
  have hle : (rootHom k a₁ a₂).range ≤ M := by
    rintro _ ⟨c, rfl⟩
    exact hu _ c.toAdd.1.2 _ c.toAdd.2.2
  have hcard : Nat.card (rootHom k a₁ a₂).range = Nat.card k * Nat.card k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (rootHom_injective ha₁ ha₂)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem exists_card_eq_two_pow (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem mem_subfield_of_sq_mem [Finite F] [CharP F 2] (S : Subfield F) {z : F}
    (hz : z ^ 2 ∈ S) : z ∈ S := by
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  have : Fintype F := Fintype.ofFinite F
  have hq : z ^ (2 ^ f) = z := by
    have := FiniteField.pow_card z
    rwa [← Nat.card_eq_fintype_card, hF] at this
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have h : z = (z ^ 2) ^ (2 ^ g) := by
    rw [← pow_mul, ← pow_succ']
    exact hq.symm
  rw [h]
  exact S.pow_mem hz _

theorem mem_of_sq_eq_one_of_sup {G : Type*} [Group G] {N C : Subgroup G} [N.Normal]
    (hdisj : Disjoint N C) (hsup : N ⊔ C = ⊤) (hCodd : Odd (Nat.card C)) {g : G}
    (hg : g ^ 2 = 1) : g ∈ N := by
  have hg' : g ∈ N ⊔ C := hsup ▸ Subgroup.mem_top g
  obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
  have hnc : n * (c * n * c) = 1 := by
    have h1 : n * c * (n * c) = 1 := by simpa [pow_two] using hg
    simpa [mul_assoc] using h1
  have hc2 : c ^ 2 ∈ N := by
    have h2 : c ^ 2 = (c * n * c⁻¹)⁻¹ * n⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hnc, pow_two]
      group
    rw [h2]
    exact N.mul_mem (N.inv_mem (Subgroup.Normal.conj_mem inferInstance n hn c)) (N.inv_mem hn)
  have hc2' : c ^ 2 = 1 := Subgroup.disjoint_def.mp hdisj hc2 (C.pow_mem hc 2)
  have hord : orderOf c = 1 := by
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2'
    have h2 : orderOf c ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by simpa [Nat.not_even_iff_odd] using hCodd.not_two_dvd_nat)
  rw [orderOf_eq_one_iff.mp hord, mul_one]
  exact hn

end Subgroups

section Dickson


open CFSG.Glauberman.Dickson

theorem witness_eq_top {F : Type} [Field F] [Finite F] [CharP F 2] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hK : Nat.card F = Nat.card k ^ d) {a₁ a₂ b₀ : F} (ha₁ : a₁ ≠ 0)
    (ha₂ : a₂ / a₁ ∉ k) (hb₀ : b₀ ≠ 0) {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c₁ ∈ k, ∀ c₂ ∈ k, u2 (c₁ * a₁ + c₂ * a₂) ∈ M) (hl : l2 b₀ ∈ M) {m : ℕ}
    (W : SubfieldConjugacyWitness 2 m (M.map (mkPSL F))) : W.K = ⊤ := by
  have key : ∀ x y : F, u2 x ∈ M → u2 y ∈ M → x ≠ 0 → (y / x) ^ 2 ∈ W.K := by
    intro x y hx hy hx0
    have hAM : u2 x * l2 b₀ ∈ M := M.mul_mem hx hl
    have hBM : u2 y * l2 b₀ * u2 (x + y) ∈ M :=
      M.mul_mem (M.mul_mem hy hl) (by rw [u2_add]; exact M.mul_mem hx hy)
    have hxb : x * b₀ ≠ 0 := mul_ne_zero hx0 hb₀
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F (u2 x * l2 b₀), Subgroup.mem_map_of_mem _ hAM⟩
      ⟨mkPSL F (u2 y * l2 b₀ * u2 (x + y)), Subgroup.mem_map_of_mem _ hBM⟩
      (u2 x * l2 b₀) (u2 y * l2 b₀ * u2 (x + y)) rfl rfl
      (by rw [trace_u2_mul_l2]; exact hxb)
      (by rw [trace_u2_mul_l2_mul_u2]; exact hxb)
    rw [trace_pair, trace_u2_mul_l2, trace_u2_mul_l2_mul_u2] at h
    have : y ^ 2 * b₀ ^ 2 / (x * b₀ * (x * b₀)) = (y / x) ^ 2 := by
      field_simp
    rwa [this] at h
  have hu1 : ∀ c ∈ k, u2 (c * a₁) ∈ M := fun c hc => by
    simpa using hu c hc 0 k.zero_mem
  have hkW : k ≤ W.K := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]
      exact W.K.zero_mem
    · have h := key a₁ (c * a₁) (by simpa using hu1 1 k.one_mem) (hu1 c hc) ha₁
      have hc' : c * a₁ / a₁ = c := by field_simp
      rw [hc'] at h
      exact mem_subfield_of_sq_mem W.K h
  have h2 : a₂ / a₁ ∈ W.K := by
    refine mem_subfield_of_sq_mem W.K (key a₁ a₂ (by simpa using hu1 1 k.one_mem) ?_ ha₁)
    simpa using hu 0 k.zero_mem 1 k.one_mem
  rcases subfield_eq_or_eq_top hkW hd hK with h | h
  · exact absurd (h ▸ h2) ha₂
  · exact h

theorem alternating_four_involutions_comm :
    ∀ a b : alternatingGroup (Fin 4), a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a := by
  decide +kernel

theorem sl2_eq_top_of_root_groups {F : Type} [Field F] [Finite F] [CharP F 2] {k : Subfield F}
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card F = Nat.card k ^ d) {a₁ a₂ b₀ : F}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ / a₁ ∉ k) (hb₀ : b₀ ≠ 0)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c₁ ∈ k, ∀ c₂ ∈ k, u2 (c₁ * a₁ + c₂ * a₂) ∈ M) (hl : l2 b₀ ∈ M) : M = ⊤ := by
  classical
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  obtain ⟨m₀, hm₀1, hk⟩ := exists_card_eq_two_pow k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := mkPSL_injective (F := F)
  have hxM : u2 a₁ ∈ M := by simpa using hu 1 k.one_mem 0 k.zero_mem
  have hHcard : Nat.card (M.map (mkPSL F)) = Nat.card M := Subgroup.card_map_of_injective hinj
  have hdodd : Odd d := hd.odd_of_ne_two hd2
  have hfm : f = m₀ * d := by
    have h : 2 ^ f = 2 ^ (m₀ * d) := by rw [← hF, hK, hk, ← pow_mul]
    exact Nat.pow_right_injective (le_refl 2) h
  have h4 : 4 ∣ Nat.card M := by
    have h1 := card_sq_dvd_card ha₁ ha₂ hu
    have h2 : 2 ∣ Nat.card k := by
      rw [hk]
      exact dvd_pow_self 2 (by omega)
    exact (Nat.mul_dvd_mul h2 h2).trans h1
  have hFodd : Odd (2 ^ f - 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rcases h1 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hFodd' : Odd (2 ^ f + 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hFodd.not_two_dvd_nat)
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  let x : H := ⟨mkPSL F (u2 a₁), Subgroup.mem_map_of_mem _ hxM⟩
  let y : H := ⟨mkPSL F (l2 b₀), Subgroup.mem_map_of_mem _ hl⟩
  have hxy : x * y ≠ y * x := by
    intro h
    have h' := congrArg Subtype.val h
    apply u2_mul_l2_ne (mul_ne_zero ha₁ hb₀)
    apply hinj
    rw [map_mul, map_mul]
    exact h'
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simp [x, pow_two, ← map_mul, u2_mul_self]
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simp [y, pow_two, ← map_mul, l2_mul_self]
  have hcomm : ∀ {z : ℕ}, z ∣ 2 ^ f - 1 ∨ z ∣ 2 ^ f + 1 → Odd z := fun {z} hz =>
    hz.elim (fun h => Odd.of_dvd_nat hFodd h) (fun h => Odd.of_dvd_nat hFodd' h)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := 2) (f := f) hF
      H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  ·
    have hzodd : Odd z := by
      simp only [hF, hg, Nat.div_one] at hz
      exact hcomm hz
    have h42 : 4 ∣ 2 * z := by rw [← hcard, hHcard]; exact h4
    obtain ⟨c, hc⟩ := hzodd
    omega
  · exact absurd (by
      have := alternating_four_involutions_comm (e x) (e y) (by rw [← map_pow, hx2, map_one])
        (by rw [← map_pow, hy2, map_one])
      exact e.injective (by rw [map_mul, map_mul]; exact this)) hxy
  · exfalso
    have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  ·
    exfalso
    rcases h5 with h5 | h5
    · omega
    · have hf_even : Even f := by
        by_contra hf
        rw [Nat.not_even_iff_odd] at hf
        obtain ⟨j, hj⟩ := hf
        have h1 : 2 ^ (2 * f) % 5 = 4 := by
          rw [hj, show 2 * (2 * j + 1) = 4 * j + 2 by ring, pow_add, pow_mul]
          norm_num [Nat.mul_mod, Nat.pow_mod]
        have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
        omega
      have hm_even : Even m₀ := by
        have : Even (m₀ * d) := hfm ▸ hf_even
        rcases Nat.even_mul.mp this with h | h
        · exact h
        · exact absurd h (Nat.not_even_iff_odd.mpr hdodd)
      have hm2 : 2 ≤ m₀ := by
        obtain ⟨c, hc⟩ := hm_even
        omega
      have h16 : 16 ∣ Nat.card M := by
        have h1 := card_sq_dvd_card ha₁ ha₂ hu
        refine (?_ : 16 ∣ Nat.card k * Nat.card k).trans h1
        rw [hk, ← pow_add]
        exact (pow_dvd_pow 2 (by omega : 4 ≤ m₀ + m₀) : 2 ^ 4 ∣ _)
      have h60 : Nat.card M = 60 := by
        rw [← hHcard, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Fintype.card_fin]
        decide
      rw [h60] at h16
      omega
  ·
    exfalso
    have htodd : Odd t :=
      Odd.of_dvd_nat hFodd (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have := hN
    have hxN : x ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hx2
    have hyN : y ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hy2
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxy (congrArg Subtype.val hcN)
  ·
    have hWK : W.K = ⊤ := witness_eq_top hd hK ha₁ ha₂ hb₀ hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have e2 : GaloisField 2 m ≃+* F := by
      have := Fintype.ofFinite (GaloisField 2 m)
      have := Fintype.ofFinite F
      exact FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card 2 m hm0, hmf'])
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      rw [Nat.card_congr eP.toEquiv]
      exact Nat.card_congr (h826_pslEquiv e2).toEquiv
    have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcardH
    refine eq_top_iff.2 fun g _ => ?_
    have hg' : mkPSL F g ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨g', hg'M, hgg'⟩ := Subgroup.mem_map.mp hg'
    rwa [← hinj hgg']
  ·
    exfalso
    have hWK : W.K = ⊤ := witness_eq_top hd hK ha₁ ha₂ hb₀ hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have := Nat.le_of_dvd (by omega) hmf
    omega

end Dickson

end CFSG.RankThree.PartOne.CTP
