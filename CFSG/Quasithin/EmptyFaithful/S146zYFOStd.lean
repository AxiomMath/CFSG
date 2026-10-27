module

public import CFSG.Quasithin.EmptyFaithful.S146zYFOModel

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

theorem diagHom_pow' (d : Fin 3 → Kˣ) (n : ℕ) : diagHom 3 d ^ n = diagHom 3 (d ^ n) :=
  (map_pow _ _ _).symm

theorem pow_eq_pow_iff_mod {ζ : Kˣ} (hζ : orderOf ζ = 5) {m n : ℕ} :
    ζ ^ m = ζ ^ n ↔ m % 5 = n % 5 := by
  rw [pow_eq_pow_iff_modEq, hζ]
  rfl

@[expose] noncomputable def dd (ζ : Kˣ) (a b : ℕ) : GL (Fin 3) K :=
  diagHom 3 ![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))]

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
  · show (ζ ^ (4 * (a + b))) ^ n = ζ ^ (4 * (n * a + n * b))
    rw [← pow_mul]
    congr 1
    ring

theorem dd_congr (hζ : orderOf ζ = 5) {a a' b b' : ℕ} (ha : a % 5 = a' % 5) (hb : b % 5 = b' % 5) :
    dd ζ a b = dd ζ a' b' := by
  unfold dd
  congr 1
  funext i
  fin_cases i
  · exact (pow_eq_pow_iff_mod hζ).2 ha
  · exact (pow_eq_pow_iff_mod hζ).2 hb
  · exact (pow_eq_pow_iff_mod hζ).2 (by omega)

theorem dd_pow_five (hζ : orderOf ζ = 5) (a b : ℕ) : dd ζ a b ^ 5 = 1 := by
  rw [dd_pow]
  have h0 : dd ζ 0 0 = 1 := by
    unfold dd
    rw [← map_one (diagHom (K := K) 3)]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [← h0]
  exact dd_congr hζ (by omega) (by omega)

theorem dd_mem_torus3 (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (a b : ℕ) : dd ζ a b ∈ torus3 M := by
  have hζ5 : ζ ^ 5 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine (mem_torus3 M).2 ⟨![ζ ^ a, ζ ^ b, ζ ^ (4 * (a + b))], fun i => ?_, ?_, rfl⟩
  · fin_cases i <;> exact M.pow_mem hζM _
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [← pow_add, ← pow_add, show a + b + 4 * (a + b) = 5 * (a + b) by ring, pow_mul, hζ5,
      one_pow]

theorem dd_mem_omega5 (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (a b : ℕ) : dd ζ a b ∈ omega5 M :=
  ⟨dd_mem_torus3 hζM hζ a b, dd_pow_five hζ a b⟩

theorem exists_dd_of_mem_omega5 (hζ : orderOf ζ = 5) {y : GL (Fin 3) K} (hy : y ∈ omega5 M) :
    ∃ a b : ℕ, a < 5 ∧ b < 5 ∧ y = dd ζ a b := by
  have hprim : IsPrimitiveRoot ζ 5 := hζ ▸ IsPrimitiveRoot.orderOf ζ
  obtain ⟨hyT, hy5⟩ := hy
  obtain ⟨d, -, hd, rfl⟩ := (mem_torus3 M).1 hyT
  rw [diagHom_pow'] at hy5
  have hd5 : d ^ 5 = 1 := diagHom_injective 3 (hy5.trans (map_one _).symm)
  have hroot : ∀ i, ∃ k < 5, ζ ^ k = d i := fun i => by
    apply hprim.eq_pow_of_mem_rootsOfUnity
    rw [mem_rootsOfUnity]
    exact congrFun hd5 i
  obtain ⟨k0, hk0, e0⟩ := hroot 0
  obtain ⟨k1, hk1, e1⟩ := hroot 1
  obtain ⟨k2, hk2, e2⟩ := hroot 2
  have hprod : ζ ^ (k0 + k1 + k2) = 1 := by rw [pow_add, pow_add, e0, e1, e2]; exact hd
  have hdvd : 5 ∣ k0 + k1 + k2 := hζ ▸ orderOf_dvd_of_pow_eq_one hprod
  refine ⟨k0, k1, hk0, hk1, ?_⟩
  unfold dd
  congr 1
  funext i
  fin_cases i
  · exact e0.symm
  · exact e1.symm
  · show d 2 = ζ ^ (4 * (k0 + k1))
    rw [← e2]
    exact (pow_eq_pow_iff_mod hζ).2 (by omega)

end Dd

namespace FiveModel

variable (h : FiveModel H M)
include h

theorem exists_orderFive [Finite K] : ∃ ζ : Kˣ, ζ ∈ M ∧ orderOf ζ = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 5 h.five
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

@[expose] noncomputable def ddH {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (a b : ℕ) : H :=
  ⟨dd ζ a b, torus3_le M h.mono (dd_mem_torus3 hζM hζ a b)⟩

theorem coe_ddH {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (a b : ℕ) :
    ((h.ddH hζM hζ a b : H) : GL (Fin 3) K) = dd ζ a b :=
  rfl

theorem ddH_pow_five {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (a b : ℕ) :
    h.ddH hζM hζ a b ^ 5 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, coe_ddH, dd_pow_five hζ, Subgroup.coe_one])

theorem ddH_pow {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) (n a b : ℕ) :
    h.ddH hζM hζ a b ^ n = h.ddH hζM hζ (n * a) (n * b) :=
  Subtype.ext (by rw [Subgroup.coe_pow, coe_ddH, coe_ddH, dd_pow])

theorem ddH_congr {ζ : Kˣ} (hζM : ζ ∈ M) (hζ : orderOf ζ = 5) {a a' b b' : ℕ}
    (ha : a % 5 = a' % 5) (hb : b % 5 = b' % 5) : h.ddH hζM hζ a b = h.ddH hζM hζ a' b' :=
  Subtype.ext (dd_congr hζ ha hb)

theorem card_pstd_le [Finite K] : Nat.card (pstd H M) ≤ 25 := by
  obtain ⟨ζ, hζM, hζ⟩ := h.exists_orderFive
  let F : Fin 5 × Fin 5 → pstd H M := fun ab =>
    ⟨proj H (h.ddH hζM hζ ab.1 ab.2),
      mem_pstd.2 ⟨_, dd_mem_omega5 hζM hζ _ _, rfl⟩⟩
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, rfl⟩ := mem_pstd.1 hx
    obtain ⟨a, b, ha, hb, hab⟩ := exists_dd_of_mem_omega5 hζ ht
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext ?_⟩
    show proj H (h.ddH hζM hζ a b) = proj H t
    congr 1
    exact Subtype.ext hab.symm
  calc Nat.card (pstd H M) ≤ Nat.card (Fin 5 × Fin 5) := Nat.card_le_card_of_surjective F hF
    _ = 25 := by simp

theorem exists_map_eq_pstd [Finite K] {P : Subgroup (StatedProj H)} (hP : Nat.card P = 25)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) :
    ∃ φ : StatedProj H ≃* StatedProj H, P.map φ.toMonoidHom = pstd H M := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hP5 : IsPGroup 5 P := IsPGroup.iff_card.2 ⟨2, by rw [hP]; norm_num⟩
  obtain ⟨g, hg⟩ := h.exists_conj_le_pstd hP5 hexp
  refine ⟨MulAut.conj g⁻¹, ?_⟩
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ pstd H M := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hg x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP]
  exact h.card_pstd_le

end FiveModel

end FiveOdd

end CFSG.Quasithin.S146zY
