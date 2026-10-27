module

public import CFSG.RankThree.PartOne.KFOUT3.KtySUCls
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix

section Rho

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} [NeZero n]

@[expose] def rhoMatHom (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix (Fin n) (Fin n) K where
  toFun A := rhoMat n σ (A : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact rhoMat_one hc σ
  map_mul' A B := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact (rhoMat_mul hn hc σ _ _).symm

@[expose] noncomputable def rhoGL (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin n) K :=
  (rhoMatHom hn hc σ).toHomUnits

omit [Finite K] [CharP K 2] in
theorem rhoGL_val (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((rhoGL hn hc σ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      rhoMat n σ (A : Matrix (Fin 2) (Fin 2) K) := rfl

omit [Finite K] in
theorem rhoGL_mem_SU (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x)
    (h4 : 4 ≤ Nat.card K) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    rhoGL hn hc σ A ∈ SU σ n := by
  refine mem_SU.mpr ⟨?_, ?_⟩
  · have hperf : Group.IsPerfect (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
      Group.IsPerfect.top_iff.mpr (KCRootAxis.sl2_isPerfect h4)
    have hle := perfect_le_ker ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).comp
      (rhoGL hn hc σ)) hperf (Subgroup.mem_top A)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hle
    have := congrArg Units.val hle
    simpa using this
  · rw [rhoGL_val]
    exact rhoMat_gram hn hc σ hσ _ (by
      have := A.2
      rw [Matrix.det_fin_two] at this
      exact this)

end Rho

section Big

variable {K : Type} [Field K] {n : ℕ} [NeZero n]

theorem K1 (hc : D8Comb n) (σ : K ≃+* K) {a : Kˣ} (ha1 : a ≠ 1)
    (ha2 : a⁻¹ ≠ a) {m : GL (Fin n) K} (hmSU : m ∈ SU σ n)
    (hcomm : m * diagU (dvecN n a a) = diagU (dvecN n a a) * m)
    (h00 : (m : Matrix (Fin n) (Fin n) K) 0 0 = 1) (h01 : (m : Matrix (Fin n) (Fin n) K) 0 1 = 0)
    (h10 : (m : Matrix (Fin n) (Fin n) K) 1 0 = 0) (h11 : (m : Matrix (Fin n) (Fin n) K) 1 1 = 1) :
    m = 1 := by
  classical
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  have hcM : M * Matrix.diagonal (fun i => (dvecN n a a i : K)) =
      Matrix.diagonal (fun i => (dvecN n a a i : K)) * M := by
    have := congrArg Units.val hcomm
    simpa [diagU_val] using this
  have hv : ∀ i j, gp n i ≠ gp n j → M i j = 0 := fun i j h => vanish_aa ha1 ha2 hcM h
  obtain ⟨hdet, hgram⟩ := mem_SU.mp hmSU
  have h01' : (0 : Fin n) ≠ 1 := hc.one_ne_zero.symm
  have h10' : ¬ (1 : Fin n) = 0 := Ne.symm h01'
  have hrow0 : ∀ j, M 0 j = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : gp n j = 0
    · rcases (gp_eq_zero_iff hc).mp hj with h | h
      · subst h; simpa using h00
      · subst h; simpa [h10'] using h01
    · have hj0 : ¬ j = 0 := fun h => hj (by rw [h]; exact gp_zero)
      simpa [hj0] using hv 0 j (by rw [gp_zero]; exact Ne.symm hj)
  have hrow1 : ∀ j, M 1 j = if j = 1 then 1 else 0 := by
    intro j
    by_cases hj : gp n j = 0
    · rcases (gp_eq_zero_iff hc).mp hj with h | h
      · subst h; simpa [h01'] using h10
      · subst h; simpa using h11
    · have hj1 : ¬ j = 1 := fun h => hj (by rw [h]; exact gp_one hc)
      simpa [hj1] using hv 1 j (by rw [gp_one hc]; exact Ne.symm hj)
  have hgram' : ∀ i₀ s : Fin n, ∑ k, σ (M k i₀) * M (Fin.rev k) s =
      if s = Fin.rev i₀ then 1 else 0 := by
    intro i₀ s
    have h1 := congrFun (congrFun hgram i₀) s
    rw [gram_apply] at h1
    rw [h1]
    simp [antidiag]
  have hcol : ∀ i₀ : Fin n, gp n i₀ = 0 → ∀ k, k ≠ 0 → k ≠ 1 → M k i₀ = 0 := by
    intro i₀ hi₀ k hk0 hk1
    apply hv
    rw [hi₀]
    intro h
    rcases (gp_eq_zero_iff hc).mp h with h | h
    · exact hk0 h
    · exact hk1 h
  have hrevrow0 : ∀ s, M (Fin.rev 0) s = if s = Fin.rev 0 then 1 else 0 := by
    intro s
    have := hgram' 0 s
    rw [sum_eq_pair h01' (fun k hk0 hk1 => by rw [hcol 0 gp_zero k hk0 hk1, map_zero, zero_mul])] at this
    simpa [h00, h10] using this
  have hrevrow1 : ∀ s, M (Fin.rev 1) s = if s = Fin.rev 1 then 1 else 0 := by
    intro s
    have := hgram' 1 s
    rw [sum_eq_pair h01' (fun k hk0 hk1 => by rw [hcol 1 (gp_one hc) k hk0 hk1, map_zero, zero_mul])] at this
    simpa [h01, h11] using this
  have hoff : ∀ i j : Fin n, i ≠ j → M i j = 0 := by
    intro i j hij
    rcases index_kinds i with h | h | h | h | h
    · subst h; simpa [Ne.symm hij] using hrow0 j
    · subst h; simpa [Ne.symm hij] using hrow1 j
    · subst h; simpa [Ne.symm hij] using hrevrow1 j
    · subst h; simpa [Ne.symm hij] using hrevrow0 j
    · by_cases hj : gp n j = 2
      · exact absurd (cls_injective hc (by rw [h, gp_eq_two_iff.mp hj])) hij
      · exact hv i j (by rw [gp_middle h]; exact Ne.symm hj)
  have hdd_ne : ∀ i : Fin n, d8Cls n i ≠ 4 → M i i = 1 := by
    intro i hi
    rcases index_kinds i with h | h | h | h | h
    · subst h; exact h00
    · subst h; exact h11
    · subst h; simpa using hrevrow1 (Fin.rev 1)
    · subst h; simpa using hrevrow0 (Fin.rev 0)
    · exact absurd h hi
  have hMdiag : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact hoff i j hij
  have hdet' : ∏ i, M i i = 1 := by
    rw [← Matrix.det_diagonal, ← hMdiag]; exact hdet
  have hdd : ∀ i, M i i = 1 := by
    intro i
    by_cases hi : d8Cls n i = 4
    · rw [← hdet', Finset.prod_eq_single i]
      · intro k _ hk
        exact hdd_ne k (fun h4 => hk (cls_injective hc (by rw [h4, hi])))
      · simp
    · exact hdd_ne i hi
  apply Units.ext
  show M = 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hdd]
  · simp [hij, hoff i j hij]

theorem rho_comm [CharP K 2] [Finite K] (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) (a : Kˣ)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    rhoGL hn hc σ A * diagU (dvecN n a a) = diagU (dvecN n a a) * rhoGL hn hc σ A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, rhoGL_val, diagU_val]
  ext i j
  simp only [rhoMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, dvecN]
  exact rhoEnt_comm_aa σ _ a _ _

@[expose] def eA (n : ℕ) [NeZero n] : Fin 2 → Fin n := ![0, 1]

theorem eA_injective (hc : D8Comb n) : Function.Injective (eA n) := by
  intro x y h
  have h01 : (0 : Fin n) ≠ 1 := hc.one_ne_zero.symm
  fin_cases x <;> fin_cases y <;> simp_all [eA]

theorem mem_range_eA {j : Fin n} : j ∈ Set.range (eA n) ↔ j = 0 ∨ j = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

@[expose] def centA (n : ℕ) [NeZero n] (a : Kˣ) : Subgroup (GL (Fin n) K) :=
  Subgroup.centralizer ({diagU (dvecN n a a)} : Set (GL (Fin n) K))

theorem mem_centA {a : Kˣ} {x : GL (Fin n) K} :
    x ∈ centA n a ↔ x * diagU (dvecN n a a) = diagU (dvecN n a a) * x := by
  unfold centA
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h _ (Set.mem_singleton _)).symm
  · intro h w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact h.symm

theorem centA_vanish (hc : D8Comb n) {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) :
    ∀ m ∈ centA n a, ∀ b j, j ∉ Set.range (eA n) →
      ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (eA n b) j = 0 := by
  intro m hm b j hj
  apply vanish_aa ha1 ha2 (comm_matrix (mem_centA.mp hm))
  rw [mem_range_eA] at hj
  have hj' : gp n j ≠ 0 := fun h => hj ((gp_eq_zero_iff hc).mp h)
  fin_cases b
  · show gp n 0 ≠ gp n j
    rw [gp_zero]; exact Ne.symm hj'
  · show gp n 1 ≠ gp n j
    rw [gp_one hc]; exact Ne.symm hj'

@[expose] noncomputable def betaA (hc : D8Comb n) {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) :
    ↥(centA n a) →* GL (Fin 2) K :=
  blkHom (eA n) (eA_injective hc) (centA n a) (centA_vanish hc ha1 ha2)

variable [Finite K] [CharP K 2]

theorem rhoGL_mem_centA (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) (a : Kˣ)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) : rhoGL hn hc σ A ∈ centA n a :=
  mem_centA.mpr (rho_comm hn hc σ a A)

theorem betaA_rho (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) {a : Kˣ} (ha1 : a ≠ 1)
    (ha2 : a⁻¹ ≠ a) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    betaA hc ha1 ha2 ⟨rhoGL hn hc σ A, rhoGL_mem_centA hn hc σ a A⟩ =
      Matrix.SpecialLinearGroup.toGL A := by
  apply Units.ext
  rw [betaA, blkHom_val]
  ext b c
  have h01 : (0 : Fin n) ≠ 1 := hc.one_ne_zero.symm
  fin_cases b <;> fin_cases c <;>
    simp [eA, rhoGL_val, rhoMat, cls_zero, cls_one hc, rhoEnt]

omit [Finite K] [CharP K 2] in
theorem det_toGL (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL A) = 1 := by
  apply Units.ext
  simp

theorem conj_rho_mem (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x)
    (h4 : 4 ≤ Nat.card K) {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) {x : GL (Fin n) K}
    (hxSU : x ∈ SU σ n) (hx : x * diagU (dvecN n a a) = diagU (dvecN n a a) * x)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ A' : Matrix.SpecialLinearGroup (Fin 2) K,
      x * rhoGL hn hc σ A * x⁻¹ = rhoGL hn hc σ A' := by
  have hxC : x ∈ centA n a := mem_centA.mpr hx
  have hρC := rhoGL_mem_centA hn hc σ a
  have hρSU := rhoGL_mem_SU hn hc σ hσ h4
  set m : GL (Fin n) K := x * rhoGL hn hc σ A * x⁻¹ with hm
  have hmC : m ∈ centA n a := (centA n a).mul_mem ((centA n a).mul_mem hxC (hρC A))
    ((centA n a).inv_mem hxC)
  have hmSU : m ∈ SU σ n := (SU σ n).mul_mem ((SU σ n).mul_mem hxSU (hρSU A))
    ((SU σ n).inv_mem hxSU)
  let β := betaA hc ha1 ha2
  have hβm : β ⟨m, hmC⟩ = β ⟨x, hxC⟩ * Matrix.SpecialLinearGroup.toGL A * (β ⟨x, hxC⟩)⁻¹ := by
    have : (⟨m, hmC⟩ : ↥(centA n a)) =
        ⟨x, hxC⟩ * ⟨rhoGL hn hc σ A, hρC A⟩ * ⟨x, hxC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, betaA_rho hn hc σ ha1 ha2]
  have hdet : Matrix.GeneralLinearGroup.det (β ⟨m, hmC⟩) = 1 := by
    rw [hβm, map_mul, map_mul, map_inv, det_toGL, mul_one, mul_inv_cancel]
  let A' : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨((β ⟨m, hmC⟩ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
      have := congrArg Units.val hdet
      simpa using this⟩
  have hA' : Matrix.SpecialLinearGroup.toGL A' = β ⟨m, hmC⟩ := Units.ext rfl
  refine ⟨A', ?_⟩
  set m' : GL (Fin n) K := (rhoGL hn hc σ A')⁻¹ * m with hm'
  have hm'C : m' ∈ centA n a := (centA n a).mul_mem ((centA n a).inv_mem (hρC A')) hmC
  have hm'SU : m' ∈ SU σ n := (SU σ n).mul_mem ((SU σ n).inv_mem (hρSU A')) hmSU
  have hβm' : β ⟨m', hm'C⟩ = 1 := by
    have : (⟨m', hm'C⟩ : ↥(centA n a)) =
        ⟨rhoGL hn hc σ A', hρC A'⟩⁻¹ * ⟨m, hmC⟩ := rfl
    rw [this, map_mul, map_inv, betaA_rho hn hc σ ha1 ha2, hA', inv_mul_cancel]
  have hent : ∀ b c : Fin 2, ((m' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (eA n b) (eA n c) =
      (1 : Matrix (Fin 2) (Fin 2) K) b c := by
    intro b c
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
      hβm') b) c
    simpa [β, betaA, blkHom_val] using this
  have h01 : (0 : Fin n) ≠ 1 := hc.one_ne_zero.symm
  have hm'1 : m' = 1 := by
    refine K1 hc σ ha1 ha2 hm'SU (mem_centA.mp hm'C) ?_ ?_ ?_ ?_
    · simpa [eA] using hent 0 0
    · simpa [eA] using hent 0 1
    · simpa [eA] using hent 1 0
    · simpa [eA] using hent 1 1
  have : (rhoGL hn hc σ A')⁻¹ * m = 1 := hm'1
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem card_sl2 (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

omit [Finite K] [CharP K 2] in
theorem rhoMat_eA (hc : D8Comb n) (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) (b c : Fin 2) :
    rhoMat n σ A (eA n b) (eA n c) = A b c := by
  have h01 : (0 : Fin n) ≠ 1 := hc.one_ne_zero.symm
  fin_cases b <;> fin_cases c <;> simp [eA, rhoMat, cls_zero, cls_one hc, rhoEnt]

@[expose] noncomputable def rhoSU (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (hσ : ∀ x, σ (σ x) = x) (h4 : 4 ≤ Nat.card K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* ↥(SU σ n) :=
  (rhoGL hn hc σ).codRestrict (SU σ n) (rhoGL_mem_SU hn hc σ hσ h4)

omit [Finite K] in
theorem rhoSU_injective (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (hσ : ∀ x, σ (σ x) = x) (h4 : 4 ≤ Nat.card K) :
    Function.Injective (rhoSU hn hc σ hσ h4) := by
  intro A B h
  apply Subtype.ext
  ext b c
  have := congrArg (fun g : ↥(SU σ n) => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (eA n b) (eA n c)) h
  simpa [rhoSU, rhoGL_val, rhoMat_eA hc] using this

theorem big_su (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x)
    (h4 : 4 ≤ Nat.card K) {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card K * (Nat.card K ^ 2 - 1)) (hu : diagU (dvecN n a a) ∈ SU σ n) :
    ∃ S₀ : Subgroup ↥(SU σ n), Group.IsPerfect S₀ ∧ IsSimpleGroup S₀ ∧
      (∃ s ∈ S₀, orderOf s = p) ∧
      (∀ s ∈ S₀, (⟨diagU (dvecN n a a), hu⟩ : ↥(SU σ n)) * s =
        s * ⟨diagU (dvecN n a a), hu⟩) ∧
      (∀ x : ↥(SU σ n), (⟨diagU (dvecN n a a), hu⟩ : ↥(SU σ n)) * x =
        x * ⟨diagU (dvecN n a a), hu⟩ → ∀ s ∈ S₀, x * s * x⁻¹ ∈ S₀) ∧
      Nat.card S₀ = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := KCRootAxis.sl2_isSimpleGroup h4
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := KCRootAxis.sl2_isPerfect h4
  have hinj := rhoSU_injective hn hc σ hσ h4
  let ρ := rhoSU hn hc σ hσ h4
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* ρ.range := MonoidHom.ofInjective hinj
  have hcard : Nat.card ρ.range = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, card_sl2]
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨ρ.range, Group.IsPerfect.range ρ, e.symm.isSimpleGroup, ?_, ?_, ?_, hcard⟩
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ hpd)
    exact ⟨(x : ↥(SU σ n)), x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  · rintro _ ⟨A, rfl⟩
    exact Subtype.ext (rho_comm hn hc σ a A).symm
  · intro x hx s hs
    obtain ⟨A, rfl⟩ := hs
    obtain ⟨A', hA'⟩ := conj_rho_mem hn hc σ hσ h4 ha1 ha2 x.2 (congrArg Subtype.val hx).symm A
    exact ⟨A', Subtype.ext hA'.symm⟩

end Big

end CFSG.RankThree.PartOne.KFOUT3
