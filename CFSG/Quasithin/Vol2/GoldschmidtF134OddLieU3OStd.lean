module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OModel

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} {p : ℕ}

theorem diagHom_pow' (d : Fin 3 → Kˣ) (n : ℕ) : diagHom 3 d ^ n = diagHom 3 (d ^ n) :=
  (map_pow _ _ _).symm

theorem pow_eq_pow_iff {ζ : Kˣ} (hζ : orderOf ζ = p) {m n : ℕ} :
    ζ ^ m = ζ ^ n ↔ (m : ZMod p) = n := by
  rw [pow_eq_pow_iff_modEq, hζ, ZMod.natCast_eq_natCast_iff]

theorem pow_eq_one_iff' {ζ : Kˣ} (hζ : orderOf ζ = p) {n : ℕ} :
    ζ ^ n = 1 ↔ (n : ZMod p) = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, hζ, ZMod.natCast_eq_zero_iff]

@[expose] noncomputable def dd (ζ : Kˣ) (a b : ℕ) : GL (Fin 3) K :=
  diagHom 3 ![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹]

section Dd

variable {ζ : Kˣ}

theorem dd_pow (n a b : ℕ) : dd ζ a b ^ n = dd ζ (n * a) (n * b) := by
  unfold dd
  rw [diagHom_pow']
  congr 1
  funext i
  fin_cases i
  · show (ζ ^ a) ^ n = ζ ^ (n * a)
    rw [← pow_mul, mul_comm]
  · show (ζ ^ b) ^ n = ζ ^ (n * b)
    rw [← pow_mul, mul_comm]
  · show ((ζ ^ a * ζ ^ b)⁻¹) ^ n = (ζ ^ (n * a) * ζ ^ (n * b))⁻¹
    rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm a n, mul_comm b n]

theorem dd_congr (hζ : orderOf ζ = p) {a a' b b' : ℕ} (ha : (a : ZMod p) = a')
    (hb : (b : ZMod p) = b') : dd ζ a b = dd ζ a' b' := by
  have h1 : ζ ^ a = ζ ^ a' := (pow_eq_pow_iff hζ).2 ha
  have h2 : ζ ^ b = ζ ^ b' := (pow_eq_pow_iff hζ).2 hb
  unfold dd
  rw [h1, h2]

theorem dd_zero : dd (K := K) ζ 0 0 = 1 := by
  unfold dd
  rw [← map_one (diagHom (K := K) 3)]
  congr 1
  funext i
  fin_cases i <;> simp

theorem dd_pow_p (hζ : orderOf ζ = p) (a b : ℕ) : dd ζ a b ^ p = 1 := by
  rw [dd_pow, ← dd_zero (ζ := ζ)]
  exact dd_congr hζ (by simp) (by simp)

theorem dd_mem_torus3 (hζM : ζ ∈ M) (a b : ℕ) : dd ζ a b ∈ torus3 M := by
  refine (mem_torus3 M).2 ⟨![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹], fun i => ?_, ?_, rfl⟩
  · fin_cases i
    · exact M.pow_mem hζM _
    · exact M.pow_mem hζM _
    · exact M.inv_mem (M.mul_mem (M.pow_mem hζM _) (M.pow_mem hζM _))
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [mul_inv_cancel]

theorem dd_mem_omegaP (hζM : ζ ∈ M) (hζ : orderOf ζ = p) (a b : ℕ) :
    dd ζ a b ∈ omegaP p M :=
  ⟨dd_mem_torus3 hζM a b, dd_pow_p hζ a b⟩

theorem exists_dd_of_mem_omegaP [hp : Fact p.Prime] (hζ : orderOf ζ = p) {y : GL (Fin 3) K}
    (hy : y ∈ omegaP p M) : ∃ a b : ℕ, a < p ∧ b < p ∧ y = dd ζ a b := by
  have hprim : IsPrimitiveRoot ζ p := hζ ▸ IsPrimitiveRoot.orderOf ζ
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨hyT, hyp⟩ := hy
  obtain ⟨d, -, hd, rfl⟩ := (mem_torus3 M).1 hyT
  rw [diagHom_pow'] at hyp
  have hdp : d ^ p = 1 := diagHom_injective 3 (hyp.trans (map_one _).symm)
  have hroot : ∀ i, ∃ k < p, ζ ^ k = d i := fun i => by
    apply hprim.eq_pow_of_mem_rootsOfUnity
    rw [mem_rootsOfUnity]
    exact congrFun hdp i
  obtain ⟨k0, hk0, e0⟩ := hroot 0
  obtain ⟨k1, hk1, e1⟩ := hroot 1
  refine ⟨k0, k1, hk0, hk1, ?_⟩
  unfold dd
  congr 1
  funext i
  fin_cases i
  · exact e0.symm
  · exact e1.symm
  · show d 2 = (ζ ^ k0 * ζ ^ k1)⁻¹
    rw [e0, e1]
    exact eq_inv_of_mul_eq_one_right hd

end Dd

namespace PModel

variable (h : PModel p H M)
include h

theorem exists_orderP [Finite K] [Fact p.Prime] : ∃ ζ : Kˣ, ζ ∈ M ∧ orderOf ζ = p := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) p h.dvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

@[expose] noncomputable def ddH {ζ : Kˣ} (hζM : ζ ∈ M) (a b : ℕ) : H :=
  ⟨dd ζ a b, torus3_le M h.mono (dd_mem_torus3 hζM a b)⟩

theorem coe_ddH {ζ : Kˣ} (hζM : ζ ∈ M) (a b : ℕ) :
    ((h.ddH hζM a b : H) : GL (Fin 3) K) = dd ζ a b :=
  rfl

theorem ddH_pow_p {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = p) (a b : ℕ) :
    h.ddH hζM a b ^ p = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, coe_ddH, dd_pow_p hζ, Subgroup.coe_one])

theorem ddH_pow {ζ : Kˣ} (hζM : ζ ∈ M) (n a b : ℕ) :
    h.ddH hζM a b ^ n = h.ddH hζM (n * a) (n * b) :=
  Subtype.ext (by rw [Subgroup.coe_pow, coe_ddH, coe_ddH, dd_pow])

theorem ddH_congr {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = p) {a a' b b' : ℕ}
    (ha : (a : ZMod p) = a') (hb : (b : ZMod p) = b') : h.ddH hζM a b = h.ddH hζM a' b' :=
  Subtype.ext (dd_congr hζ ha hb)

theorem card_pstd_le [Finite K] [Fact p.Prime] : Nat.card (pstd p H M) ≤ p ^ 2 := by
  obtain ⟨ζ, hζM, hζ⟩ := h.exists_orderP
  let F : Fin p × Fin p → pstd p H M := fun ab =>
    ⟨proj H (h.ddH hζM ab.1 ab.2), mem_pstd.2 ⟨_, dd_mem_omegaP hζM hζ _ _, rfl⟩⟩
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, rfl⟩ := mem_pstd.1 hx
    obtain ⟨a, b, ha, hb, hab⟩ := exists_dd_of_mem_omegaP hζ ht
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext ?_⟩
    show proj H (h.ddH hζM a b) = proj H t
    congr 1
    exact Subtype.ext hab.symm
  calc Nat.card (pstd p H M) ≤ Nat.card (Fin p × Fin p) := Nat.card_le_card_of_surjective F hF
    _ = p ^ 2 := by simp [sq]

omit h in
theorem comm_pstd {x y : StatedProj H} (hx : x ∈ pstd p H M) (hy : y ∈ pstd p H M) :
    x * y = y * x := by
  obtain ⟨t, ht, rfl⟩ := mem_pstd.1 hx
  obtain ⟨t', ht', rfl⟩ := mem_pstd.1 hy
  have : t * t' = t' * t := Subtype.ext (torus3_comm M ht.1 ht'.1)
  rw [← map_mul, ← map_mul, this]

theorem comm_of_exp [Finite K] [Fact p.Prime] (hp3 : p ≠ 3) {P : Subgroup (StatedProj H)}
    (hexp : ∀ x ∈ P, x ^ p = 1) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have hP : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨g, hg⟩ := h.exists_conj_le_pstd hp3 hP hexp
  intro a ha b hb
  have := comm_pstd (hg a ha) (hg b hb)
  have h2 : g⁻¹ * (a * b) * g = g⁻¹ * (b * a) * g := by
    calc g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := this
      _ = g⁻¹ * (b * a) * g := by group
  simpa using h2

theorem exists_map_eq_pstd [Finite K] [Fact p.Prime] (hp3 : p ≠ 3) {P : Subgroup (StatedProj H)}
    (hP : Nat.card P = p ^ 2) (hexp : ∀ x ∈ P, x ^ p = 1) :
    ∃ φ : StatedProj H ≃* StatedProj H, P.map φ.toMonoidHom = pstd p H M := by
  have hp0 : p ^ 2 ≠ 0 := pow_ne_zero 2 (Fact.out : p.Prime).ne_zero
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact hp0)
  have hP' : IsPGroup p P := IsPGroup.iff_card.2 ⟨2, by rw [hP]⟩
  obtain ⟨g, hg⟩ := h.exists_conj_le_pstd hp3 hP' hexp
  refine ⟨MulAut.conj g⁻¹, ?_⟩
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ pstd p H M := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hg x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP]
  exact h.card_pstd_le

end PModel

end CFSG.Quasithin.H13.NQCore.U3O
