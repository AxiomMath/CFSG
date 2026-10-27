module

public import CFSG.Quasithin.Background.SmithD321Sz
public import CFSG.Quasithin.Background.SmithD321Main
public import CFSG.Quasithin.Background.SmithD310UCaseI
public import CFSG.Quasithin.Background.SmithD36TSec
public import CFSG.Quasithin.Background.SmithD37ClsSz
public import CFSG.Quasithin.Background.SmithD321Fac
public import CFSG.Quasithin.Background.SmithD321Three

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.SmithD39Two
open scoped Pointwise Matrix commutatorElement

section Arith

theorem card_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz n X) :
    Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]

theorem odd_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz n X) : Odd n ∧ 3 ≤ n := by
  obtain ⟨-, a, ha, K, _, _, rfl, -, -⟩ := h
  exact ⟨⟨a, rfl⟩, by omega⟩

theorem five_dvd_card_of_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsSz n X) : 5 ∣ Nat.card X := by
  obtain ⟨⟨a, rfl⟩, -⟩ := odd_of_isSz h
  rw [card_of_isSz h]
  apply Dvd.dvd.mul_left
  have h16 : (16 : ℕ) ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have e : ((2 : ℕ) ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [e]
  omega

theorem dvd_card_of_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsSz n X) {p : ℕ} (hp : p ∣ 2 ^ n - 1) : p ∣ Nat.card X := by
  rw [card_of_isSz h]
  exact (hp.mul_left _).mul_right _

theorem exists_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  have hodd : Odd (2 ^ n - 1) := by
    rw [Nat.odd_sub (by omega)]
    simp [Nat.even_pow, show n ≠ 0 by omega]
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpd)

end Arith

section Models

theorem exists_five_GL45 {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∃ g : GL (Fin n) (ZMod 2), g ^ 5 = 1 ∧ g ≠ 1 := by
  rcases hn with rfl | rfl
  · refine ⟨⟨!![0,0,0,1; 1,0,0,1; 0,1,0,1; 0,0,1,1], !![1,1,0,0; 1,0,1,0; 1,0,0,1; 1,0,0,0],
      by decide, by decide⟩, ?_, ?_⟩
    · apply Units.ext
      decide
    · intro h
      have h' := congrArg Units.val h
      revert h'
      decide
  · refine ⟨⟨!![0,0,0,1,0; 1,0,0,1,0; 0,1,0,1,0; 0,0,1,1,0; 0,0,0,0,1],
      !![1,1,0,0,0; 1,0,1,0,0; 1,0,0,1,0; 1,0,0,0,0; 0,0,0,0,1], by decide, by decide⟩, ?_, ?_⟩
    · apply Units.ext
      decide
    · intro h
      have h' := congrArg Units.val h
      revert h'
      decide

theorem exists_pow_five_of_binaryNaturalSL45 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {n : ℕ} (hn : n = 4 ∨ n = 5) (h : BinaryNaturalSL L ⊤ ⊥ n 1) :
    ∃ y ∈ L, y ^ 5 = 1 ∧ y ≠ 1 := by
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL h
  have := charP_two_of_card hK
  obtain ⟨ι, hι⟩ := exists_hom_statedSL n K
  obtain ⟨g, hg5, hg1⟩ := exists_five_GL45 hn
  refine ⟨(e (ι g) : MulAut V), (e (ι g)).2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hg5, map_one, map_one]
    rfl
  · intro h1
    apply hg1
    apply hι
    apply e.injective
    rw [map_one, map_one]
    exact Subtype.ext h1

theorem exists_pow_prime_of_binaryNaturalSL3 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {m : ℕ} (h : BinaryNaturalSL L ⊤ ⊥ 3 m) {θ : MulAut V} (hθ : ∀ l ∈ L, θ * l = l * θ)
    {p : ℕ} (hp : p.Prime) (hθp : θ ^ p = 1) (hθ1 : θ ≠ 1) : ∃ y ∈ L, y ^ p = 1 ∧ y ≠ 1 := by
  classical
  obtain ⟨K, _, _, -, e, hR⟩ := exists_equiv_of_binaryNaturalSL h
  obtain ⟨E, hE⟩ := SmithD310U.exists_coord hR
  let f : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := fun v => Multiplicative.toAdd (E (θ (E.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun x y => by rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul] }
  have hfE : ∀ u : V, f (Multiplicative.toAdd (E u)) = Multiplicative.toAdd (E (θ u)) := by
    intro u
    simp [f]
  have hsurjE : ∀ v : Fin 3 → K, ∃ u, Multiplicative.toAdd (E u) = v :=
    fun v => ⟨E.symm (Multiplicative.ofAdd v), by simp⟩
  have hcomm : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
      f (v + Pi.single i (c * v j)) = f v + Pi.single i (c * f v j) := by
    intro i j hij c v
    obtain ⟨u, rfl⟩ := hsurjE v
    set γ := specialLinearGroupEquivStatedSL 3 K (SmithD310U.tv i j hij c) with hγ
    have hγv : ∀ w : Fin 3 → K, ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
        w + Pi.single i (c * w j) := by
      intro w
      rw [hγ, specialLinearGroupEquivStatedSL_coe, SmithD310U.tv_mulVec]
    have h1 : θ ((e.toMonoidHom γ : MulAut V) u) = (e.toMonoidHom γ : MulAut V) (θ u) := by
      have := hθ _ (e γ).2
      exact congrArg (fun φ : MulAut V => φ u) this
    rw [← hγv, ← hE, hfE, h1, hE, hfE, hγv]
  obtain ⟨l, hl⟩ := SmithD310U.exists_smul_of_comm f hcomm
  have hpow : ∀ k : ℕ, ∀ u : V,
      Multiplicative.toAdd (E ((θ ^ k) u)) = l ^ k • Multiplicative.toAdd (E u) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, ih, ← hfE, hl, smul_smul, pow_succ]
  set e0 : V := E.symm (Multiplicative.ofAdd (Pi.single 0 1)) with he0
  have he0' : Multiplicative.toAdd (E e0) = Pi.single 0 1 := by simp [he0]
  have hlp : l ^ p = 1 := by
    have h1 := hpow p e0
    rw [hθp, MulAut.one_apply, he0'] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hθ1
    refine MulEquiv.ext fun u => E.injective (Multiplicative.toAdd.injective ?_)
    rw [← hfE, hl, one_smul]
    rfl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlp
    exact zero_ne_one hlp
  set μ : Kˣ := Units.mk0 l hl0 with hμ
  have hμp : μ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hμ, Units.val_mk0, hlp,
    Units.val_one])
  have hμ1 : μ ≠ 1 := fun h1 => hl1 (by simpa [hμ] using congrArg Units.val h1)
  set d : Fin 3 → Kˣ := ![μ, μ⁻¹, 1] with hd
  have hdS : diagHom K d ∈ StatedSL 3 K := by
    apply Subgroup.subset_closure
    show (Matrix.diagonal fun i => (d i : K)).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hd]
  set δ : ↥(StatedSL 3 K) := ⟨diagHom K d, hdS⟩ with hδ
  have hδp : δ ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hδ, ← map_pow, Subgroup.coe_one]
    have hdp : d ^ p = 1 := by
      funext i
      fin_cases i <;> simp [hd, inv_pow, hμp]
    rw [hdp, map_one]
  have hδ1 : δ ≠ 1 := by
    intro h1
    have h2 : diagHom K d = diagHom K 1 := by
      rw [map_one]
      exact congrArg Subtype.val h1
    have h3 := congrFun (diagHom_injective h2) 0
    exact hμ1 (by simpa [hd] using h3)
  refine ⟨(e δ : MulAut V), (e δ).2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hδp, map_one]
    rfl
  · intro h1
    apply hδ1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h1

end Models

section Offender

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_offender_of_ratio_half (hV : ∀ v : V, v ^ 2 = 1) {X B : Subgroup (MulAut V)}
    (hBX : B ≤ X) (hB : IsElemAbelian2 B) (hpos : 0 < rk ↥B)
    (hr : 2 * rkIdx (fixV B) ≤ rk ↥B) :
    (∃ F : Subgroup (MulAut V), IsFFStarOffender X F) ∧
      qOf X ≤ ((1 / 2 : ℚ) : WithTop ℚ) ∧
      (2 * rkIdx (fixV B) < rk ↥B → qOf X < ((1 / 2 : ℚ) : WithTop ℚ)) := by
  classical
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 b b.2)⟩
  have hcard : ∀ C : Subgroup (MulAut V), C ≤ B →
      Nat.card ↥C * Nat.card ↥(fixV C) = 2 ^ (rk ↥C + rk ↥(fixV C)) := by
    intro C hC
    rw [card_eq_two_pow_of_isPGroup (hBp.to_le hC), card_eq_two_pow hV (fixV C), pow_add]
  have hidx : ∀ C : Subgroup (MulAut V), rk ↥(fixV C) + rkIdx (fixV C) = rk V :=
    fun C => rk_add_rkIdx (fixV C)
  have : Nonempty {C : Subgroup (MulAut V) // C ≤ B} := ⟨⟨⊥, bot_le⟩⟩
  obtain ⟨⟨E, hEB⟩, hEmax⟩ := Finite.exists_max
    (fun C : {C : Subgroup (MulAut V) // C ≤ B} => Nat.card ↥C.1 * Nat.card ↥(fixV C.1))
  have hEmax' : ∀ C : Subgroup (MulAut V), C ≤ B →
      rk ↥C + rk ↥(fixV C) ≤ rk ↥E + rk ↥(fixV E) := by
    intro C hC
    have h1 := hEmax ⟨C, hC⟩
    simp only at h1
    rw [hcard C hC, hcard E hEB] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have hBE := hEmax' B le_rfl
  have hBidx := hidx B
  have hEidx := hidx E
  have hrkE : rk ↥E ≤ rk ↥B := rk_mono hEB
  have hEne : E ≠ ⊥ := by
    intro hE
    have hfixbot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rw [hE, rk_bot, hfixbot, rk_top] at hBE
    omega
  have hEoff : IsFFStarOffender X E := by
    refine ⟨hEB.trans hBX, hEne, ⟨fun a ha b hb => hB.1 a (hEB ha) b (hEB hb),
      fun a ha => hB.2 a (hEB ha)⟩, fun C hC => ?_⟩
    exact hEmax ⟨C, hC.trans hEB⟩
  obtain ⟨F, hFE, hFoff, hFq, hFcard, -, -⟩ := exists_quadratic_offender_le hV hEoff
  have hFB : F ≤ B := hFE.trans hEB
  have hFrk : rk ↥F + rk ↥(fixV F) = rk ↥E + rk ↥(fixV E) := by
    rw [hcard F hFB, hcard E hEB] at hFcard
    exact Nat.pow_right_injective le_rfl hFcard
  have hFidx := hidx F
  have hrkF : rk ↥F ≤ rk ↥E := rk_mono hFE
  have hFpos : 0 < rk ↥F := by
    rcases Nat.eq_zero_or_pos (rk ↥F) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup (hBp.to_le hFB)).1 h) hFoff.2.1
    · exact h
  have hA2 : IsA2 X F := ⟨hFoff.1, hFoff.2.1, hFoff.2.2.1⟩
  have hqF : qOf X ≤ ((rAV F : ℚ) : WithTop ℚ) :=
    kq_le_iff.2 ⟨F, hA2, (isQuadratic_iff_commSeries_two F).1 hFq, le_rfl⟩
  have hFq' : (0 : ℚ) < (rk ↥F : ℚ) := by exact_mod_cast hFpos
  refine ⟨⟨F, hFoff⟩, hqF.trans (WithTop.coe_le_coe.2 ?_), fun hlt => ?_⟩
  · have h2 : 2 * rkIdx (fixV F) ≤ rk ↥F := by omega
    unfold rAV
    rw [div_le_iff₀ hFq']
    have : (2 * rkIdx (fixV F) : ℚ) ≤ (rk ↥F : ℚ) := by exact_mod_cast h2
    linarith
  · have h2 : 2 * rkIdx (fixV F) < rk ↥F := by omega
    refine hqF.trans_lt (WithTop.coe_lt_coe.2 ?_)
    unfold rAV
    rw [div_lt_iff₀ hFq']
    have : (2 * rkIdx (fixV F) : ℚ) < (rk ↥F : ℚ) := by exact_mod_cast h2
    linarith

theorem case2_or_case9 {G L A : Subgroup (MulAut V)} (h : B42Conclusion G L A)
    (hq : qOf G ≤ ((1 / 2 : ℚ) : WithTop ℚ)) :
    (qOf G = ((1 / 2 : ℚ) : WithTop ℚ) ∧ ∃ m, BinaryNaturalSL L ⊤ ⊥ 3 m) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ BinaryNaturalSL L ⊤ ⊥ n 1 := by
  have key : ∀ c : ℚ, qOf G = (c : WithTop ℚ) → c ≤ 1 / 2 := fun c hc => by
    rw [hc] at hq
    exact WithTop.coe_le_coe.1 hq
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨-, -, -, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, hBN, h1⟩ := h
    exact Or.inl ⟨h1, hBN⟩
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, h1⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, -, h1, -⟩ := h
    have := key _ h1; norm_num at this
  · obtain ⟨-, n, hn, hBN, -⟩ := h
    exact Or.inr ⟨n, hn, hBN⟩
  · obtain ⟨-, ⟨-, -, -, h1⟩ | ⟨-, -, h1⟩⟩ := h
    · have := key _ h1; norm_num at this
    · have := key _ h1; norm_num at this
  · obtain ⟨-, -, -, h1, -⟩ := h
    have := key _ h1; norm_num at this

end Offender

section Clif

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q] [Finite Q]
  {K A : Subgroup Γ}

theorem exists_irr_half [Finite Γ] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) {Y : Subgroup Q} (hY : XMod.IsIrr ↥(K ⊔ A) Y)
    (hKY : ∃ k ∈ K, ∃ y ∈ Y, k • y ≠ y) (hAY : ∃ a ∈ A, ∃ y ∈ Y, a • y ≠ y)
    (hr : 2 * nB A Y ≤ rk ↥A - rk ↥(A ⊓ fixingSubgroup Γ (Y : Set Q))) :
    ∃ J : Subgroup Q, J ≤ Y ∧ XMod.IsIrr ↥K J ∧ XMod.commOf ↥K J = J ∧
      rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q)) < rk ↥(stabIn A J) ∧
      2 * nB (stabIn A J) J ≤
        rk ↥(stabIn A J) - rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q)) ∧
      (2 * nB A Y < rk ↥A - rk ↥(A ⊓ fixingSubgroup Γ (Y : Set Q)) →
        2 * nB (stabIn A J) J <
          rk ↥(stabIn A J) - rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q))) ∧
      (2 * nB (stabIn A J) J =
          rk ↥(stabIn A J) - rk ↥(stabIn A J ⊓ fixingSubgroup Γ (J : Set Q)) → J = Y) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set Γ) := fun x hx => mem_normalizer_of_conj hAK hx
  have hNA := normalizes_of_conj (Q := Q) hAK
  have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA2 x x.2)⟩
  have hYK : XMod.IsInv ↥K Y := fun k y hy => hY.1 ⟨k, le_sup_left (α := Subgroup Γ) k.2⟩ y hy
  have hYA : ∀ a ∈ A, ∀ y ∈ Y, a • y ∈ Y := fun a ha y hy =>
    hY.1 ⟨a, le_sup_right (α := Subgroup Γ) ha⟩ y hy
  have hYirr : ∀ J : Subgroup Q, J ≤ Y → XMod.IsInv ↥K J → (∀ a ∈ A, ∀ y ∈ J, a • y ∈ J) →
      J = ⊥ ∨ J = Y := by
    intro J hJY hJK hJA
    have hJinv : XMod.IsInv ↥(K ⊔ A) J := fun g y hy =>
      smul_mem_of_mem_sup (A := K) (Λ := A) (fun k hk y hy => hJK ⟨k, hk⟩ y hy) hJA g.2 y hy
    exact hY.2.2 J hJinv bot_le hJY
  have hCYK : Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) = ⊥ := by
    rcases hYirr (Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q)) inf_le_left
      (fun k y hy => ⟨hYK k y hy.1, trivial, fun k' => by
        change (k' : Γ) • (k : Γ) • y = (k : Γ) • y
        have h1 : (k : Γ) • y = y := hy.2.2 k
        rw [h1]
        exact hy.2.2 k'⟩)
      (fun a ha y hy => ⟨hYA a ha y hy.1, trivial, fun k => by
        change (k : Γ) • a • y = a • y
        have h1 : (a⁻¹ * k * a) • y = y := hy.2.2 ⟨a⁻¹ * k * a, by
          have := hAK a⁻¹ (A.inv_mem ha) k k.2
          rwa [inv_inv] at this⟩
        have h2 : (k : Γ) • a • y = a • ((a⁻¹ * k * a) • y) := by
          rw [smul_smul, smul_smul]
          congr 1
          group
        rw [h2, h1]⟩) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk, y, hy, hky⟩ := hKY
      have : y ∈ Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) := by rw [h]; exact hy
      exact hky (this.2.2 ⟨k, hk⟩)
  have hYne : Y ≠ ⊥ := by
    intro h
    obtain ⟨k, -, y, hy, hky⟩ := hKY
    rw [h, Subgroup.mem_bot] at hy
    rw [hy, smul_one] at hky
    exact hky rfl
  obtain ⟨J₀, hJ₀Y, hJ₀⟩ := exists_isIrr_le hYK hYne
  obtain ⟨J, hJle, hJ, -, hhc⟩ := XMod.exists_isHomComp_of_isIrr hQ hNA hAp hJ₀
  have hhom : ∀ t ∈ A, XMod.Iso ↥K (t • J) J → t • J = J := fun t ht hiso =>
    (XMod.forall_iso_smul_eq_iff_isHomComp hNA hJ).2 hhc ⟨t, ht⟩ hiso
  have hJY : J ≤ Y := by
    refine hJle.trans (iSup_le fun t => ?_)
    intro q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    have h1 := hYA _ t.2 _ (hJ₀Y hq)
    change (t : Γ) • ((t : Γ)⁻¹ • q) ∈ Y at h1
    rwa [smul_inv_smul] at h1
  have horb : orbSum A J = Y := by
    have hle : orbSum A J ≤ Y := by
      refine iSup_le fun t => ?_
      intro q hq
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
      have h1 := hYA _ t.2 _ (hJY hq)
      rwa [smul_inv_smul] at h1
    rcases hYirr _ hle (isInv_orbSum hAN hJ.1) (fun a ha q hq => smul_mem_orbSum ha hq) with
      h | h
    · exfalso
      have := le_orbSum A J
      rw [h] at this
      exact hJ.2.1.ne' (le_bot_iff.1 this)
    · exact h
  have hcomm : XMod.commOf ↥K J = J := by
    rcases hJ.2.2 _ (XMod.isInv_commOf J) bot_le (XMod.commOf_le_of_isInv hJ.1) with h | h
    · exfalso
      have h1 : J ≤ Y ⊓ XMod.fixed ↥K (⊤ : Subgroup Q) :=
        le_inf hJY (XMod.commOf_eq_bot_iff.1 h)
      rw [hCYK] at h1
      exact hJ.2.1.ne' (le_bot_iff.1 h1)
    · exact h
  set A₀ := stabIn A J with hA₀
  have hcent : A ⊓ fixingSubgroup Γ (Y : Set Q) = A₀ ⊓ fixingSubgroup Γ (J : Set Q) := by
    apply le_antisymm
    · rintro a ⟨ha, hfix⟩
      have hfix' := (mem_fixingSubgroup_iff Γ).1 hfix
      refine ⟨⟨ha, ?_⟩, (mem_fixingSubgroup_iff Γ).2 fun y hy => hfix' y (hJY hy)⟩
      show a • J = J
      ext q
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hq
        have h1 := hfix' _ (hJY hq)
        rw [smul_inv_smul] at h1
        rw [h1]
        exact hq
      · intro hq
        rw [inv_smul_eq_iff.2 (hfix' q (hJY hq)).symm]
        exact hq
    · rintro a ⟨⟨ha, -⟩, hfix⟩
      have hfix' := (mem_fixingSubgroup_iff Γ).1 hfix
      refine ⟨ha, (mem_fixingSubgroup_iff Γ).2 fun y hy => ?_⟩
      rw [← horb] at hy
      have hle : orbSum A J ≤ XMod.fixed ↥(Subgroup.zpowers a) (⊤ : Subgroup Q) := by
        refine iSup_le fun t => ?_
        intro q hq
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
        refine mem_fixed_zpowers_iff.2 ?_
        have h1 := hfix' _ hq
        calc a • q = a • ((t : Γ) • ((t : Γ)⁻¹ • q)) := by rw [smul_inv_smul]
          _ = (t : Γ) • (a • ((t : Γ)⁻¹ • q)) := by rw [smul_smul, hAc a ha t t.2, mul_smul]
          _ = q := by rw [h1, smul_inv_smul]
      exact mem_fixed_zpowers_iff.1 (hle hy)
  obtain ⟨hrkY, hnB⟩ := nB_orbit hAK hAc hA2 hJ hhom
  rw [horb, ← hA₀] at hrkY hnB
  rw [hcent] at hr
  have hv : 0 < rk ↥J := by
    rcases Nat.eq_zero_or_pos (rk ↥J) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hJ.2.1.ne'
    · exact h
  have hc : rk ↥(A₀ ⊓ fixingSubgroup Γ (J : Set Q)) ≤ rk ↥A₀ := rk_mono inf_le_left
  have hA₀le : rk ↥A₀ ≤ rk ↥A := rk_mono inf_le_left
  have hpow : rk ↥A - rk ↥A₀ < 2 ^ (rk ↥A - rk ↥A₀) := Nat.lt_two_pow_self
  have h2 : (rk ↥A - rk ↥A₀) + rk ↥J ≤ 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J := by
    have h3 : (rk ↥A - rk ↥A₀ + 1) * rk ↥J ≤ 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J :=
      Nat.mul_le_mul_right _ hpow
    have h4 : rk ↥A - rk ↥A₀ ≤ (rk ↥A - rk ↥A₀) * rk ↥J := Nat.le_mul_of_pos_right _ hv
    nlinarith
  generalize 2 ^ (rk ↥A - rk ↥A₀) * rk ↥J = P at h2 hnB hrkY
  have hAp' : IsPGroup 2 ↥(A ⊓ fixingSubgroup Γ (Y : Set Q)) := hAp.to_le inf_le_left
  refine ⟨J, hJY, hJ, hcomm, ?_, by rw [← hA₀]; omega, fun hlt => ?_, fun heq => ?_⟩
  · rw [← hA₀]
    by_contra hle
    have hj : rk ↥A = rk ↥A₀ := by omega
    apply hAY.elim
    intro a ⟨ha, y, hy, hay⟩
    have hfull : A ⊓ fixingSubgroup Γ (Y : Set Q) = A := by
      refine (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)
      rw [card_eq_two_pow_of_isPGroup hAp, card_eq_two_pow_of_isPGroup hAp', hcent]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have : a ∈ A ⊓ fixingSubgroup Γ (Y : Set Q) := by rw [hfull]; exact ha
    exact hay ((mem_fixingSubgroup_iff Γ).1 this.2 y hy)
  · rw [hcent] at hlt
    rw [← hA₀]
    omega
  · rw [← hA₀] at heq
    have hP : P = rk ↥J := by omega
    refine Subgroup.eq_of_le_of_card_ge hJY ?_
    rw [card_eq_two_pow hQ Y, card_eq_two_pow hQ J, hrkY, hP]

end Clif

section Sections

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem rkIdx_fixV_autSec_add_le {A : Subgroup (MulAut Q)} {X U : Subgroup Q} (hUX : U ≤ X) :
    rkIdx (fixV (autSec A X U)) + (rk ↥U - rk ↥(U ⊓ fixV A)) ≤ rk ↥X - rk ↥(X ⊓ fixV A) := by
  classical
  set J : Subgroup Q := X ⊓ fixV A with hJ
  set ρ : ↥X →* Sec X U := QuotientGroup.mk' (U.subgroupOf X) with hρ
  set J' : Subgroup ↥X := J.subgroupOf X with hJ'
  have himg : J'.map ρ ≤ fixV (autSec A X U) := by
    rintro _ ⟨v, hv, rfl⟩
    show (QuotientGroup.mk v : Sec X U) ∈ fixV (autQuot (autSub A X) (U.subgroupOf X))
    rw [mk_mem_fixV_autQuot]
    intro g hg _
    obtain ⟨g', hg'A, rfl⟩ := mem_autSub.mp hg
    rw [Subgroup.mem_subgroupOf]
    have hvJ : (v : Q) ∈ J := hv
    have h1 : (g' : MulAut Q) (v : Q) = v := hvJ.2 _ hg'A
    have h3 : (((resHom X g' v * v⁻¹ : ↥X)) : Q) = (g' : MulAut Q) (v : Q) * (v : Q)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [h3, h1, mul_inv_cancel]
    exact U.one_mem
  have hkerρ : J' ⊓ ρ.ker = (U ⊓ fixV A).subgroupOf X := by
    ext v
    simp only [hρ, hJ', hJ, Subgroup.mem_inf, Subgroup.mem_subgroupOf, QuotientGroup.ker_mk']
    tauto
  have hrkmap : ∀ (K : Subgroup ↥X), rk ↥(K.map ρ) + rk ↥(K ⊓ ρ.ker) = rk ↥K := by
    intro K
    have h1 := B1More.card_map_mul_card_inf_ker K ρ
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  have e1 := hrkmap J'
  have e1' : rk ↥J' = rk ↥J := by
    unfold rk
    rw [hJ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ≤ X)).toEquiv]
  have e1'' : rk ↥(J' ⊓ ρ.ker) = rk ↥(U ⊓ fixV A) := by
    unfold rk
    rw [hkerρ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hUX)).toEquiv]
  have e2 : rk (Sec X U) + rk ↥U = rk ↥X := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_sec_mul hUX]
  have e3 : rk ↥(fixV (autSec A X U)) + rkIdx (fixV (autSec A X U)) = rk (Sec X U) :=
    rk_add_rkIdx (fixV (autSec A X U))
  have e4 : rk ↥(J'.map ρ) ≤ rk ↥(fixV (autSec A X U)) := rk_mono himg
  have e5 : rk ↥(U ⊓ fixV A) ≤ rk ↥U := rk_mono inf_le_left
  have e6 : rk ↥J ≤ rk ↥X := rk_mono inf_le_left
  omega

theorem rk_sub_rk_inf_le_rkIdx (A : Subgroup (MulAut Q)) (X : Subgroup Q) :
    rk ↥X - rk ↥(X ⊓ fixV A) ≤ rkIdx (fixV A) := by
  have h1 := rk_sup_add_rk_inf X (fixV A)
  have h2 : rk ↥(X ⊔ fixV A) ≤ rk ↥(⊤ : Subgroup Q) := rk_mono le_top
  rw [rk_top] at h2
  have h3 := rk_add_rkIdx (fixV A)
  omega

theorem commV_le_of_rk_eq (hQ : ∀ q : Q, q ^ 2 = 1) {A : Subgroup (MulAut Q)} {X : Subgroup Q}
    (hXA : ∀ a ∈ A, ∀ x ∈ X, a x ∈ X) (h : rk ↥X - rk ↥(X ⊓ fixV A) = rkIdx (fixV A)) :
    commV A ≤ X := by
  have h1 := rk_sup_add_rk_inf X (fixV A)
  have h3 := rk_add_rkIdx (fixV A)
  have h4 : rk ↥(X ⊓ fixV A) ≤ rk ↥X := rk_mono inf_le_left
  have htop : X ⊔ fixV A = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    have hcard : Nat.card (⊤ : Subgroup Q) ≤ Nat.card ↥(X ⊔ fixV A) := by
      rw [card_eq_two_pow hQ, card_eq_two_pow hQ, rk_top]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Subgroup.eq_of_le_of_card_ge le_top hcard]
    trivial
  rw [commV_eq_commSub, commSub, Subgroup.closure_le]
  rintro _ ⟨a, ha, w, -, rfl⟩
  have hw : w ∈ X ⊔ fixV A := by rw [htop]; trivial
  obtain ⟨x, hx, f, hf, rfl⟩ := Subgroup.mem_sup.1 hw
  have hfa : a f = f := hf a ha
  have e : a (x * f) * (x * f)⁻¹ = a x * x⁻¹ := by
    rw [map_mul, hfa, mul_inv_rev]
    group
  rw [e]
  exact X.mul_mem (hXA a ha x hx) (X.inv_mem hx)

end Sections

section Core

variable {Q : Type} [CommGroup Q]

private noncomputable def coreIn (H : Subgroup (MulAut Q)) (F : Subgroup Q) : Subgroup Q :=
  ⨅ h : ↥H, F.comap (h : MulAut Q).toMonoidHom

private theorem mem_coreIn {H : Subgroup (MulAut Q)} {F : Subgroup Q} {w : Q} :
    w ∈ coreIn H F ↔ ∀ h ∈ H, h w ∈ F := by
  simp only [coreIn, Subgroup.mem_iInf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

private theorem coreIn_le {H : Subgroup (MulAut Q)} {F : Subgroup Q} : coreIn H F ≤ F :=
  fun w hw => by simpa using mem_coreIn.1 hw 1 H.one_mem

private theorem smul_mem_coreIn {H : Subgroup (MulAut Q)} {F : Subgroup Q} :
    ∀ g ∈ H, ∀ w ∈ coreIn H F, g w ∈ coreIn H F := by
  intro g hg w hw
  refine mem_coreIn.2 fun h hh => ?_
  have := mem_coreIn.1 hw _ (H.mul_mem hh hg)
  rwa [MulAut.mul_apply] at this

private theorem le_coreIn {H : Subgroup (MulAut Q)} {F T : Subgroup Q}
    (hT : ∀ h ∈ H, ∀ w ∈ T, h w ∈ T) (hTF : T ≤ F) : T ≤ coreIn H F :=
  fun w hw => mem_coreIn.2 fun h hh => hTF (hT h hh w hw)

private noncomputable def closureIn (H : Subgroup (MulAut Q)) (S : Subgroup Q) : Subgroup Q :=
  sInf {T | S ≤ T ∧ ∀ h ∈ H, ∀ w ∈ T, h w ∈ T}

private theorem le_closureIn {H : Subgroup (MulAut Q)} {S : Subgroup Q} : S ≤ closureIn H S :=
  le_sInf fun _ hT => hT.1

private theorem closureIn_le {H : Subgroup (MulAut Q)} {S T : Subgroup Q} (hST : S ≤ T)
    (hT : ∀ h ∈ H, ∀ w ∈ T, h w ∈ T) : closureIn H S ≤ T :=
  sInf_le ⟨hST, hT⟩

private theorem smul_mem_closureIn {H : Subgroup (MulAut Q)} {S : Subgroup Q} :
    ∀ g ∈ H, ∀ w ∈ closureIn H S, g w ∈ closureIn H S := by
  intro g hg w hw
  rw [closureIn, Subgroup.mem_sInf] at hw ⊢
  exact fun T hT => hT.2 g hg w (hw T hT)

private theorem commute_sup {K A : Subgroup (MulAut Q)} {φ : MulAut Q}
    (hK : ∀ k ∈ K, φ * k = k * φ) (hA : ∀ a ∈ A, φ * a = a * φ) :
    ∀ g ∈ K ⊔ A, φ * g = g * φ := by
  have h : K ⊔ A ≤ Subgroup.centralizer {φ} := by
    refine sup_le (fun k hk => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hK k hk).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hA a ha).symm
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h hg)).symm

private theorem map_closureIn {H : Subgroup (MulAut Q)} {S : Subgroup Q} {ψ : MulAut Q}
    (hψ : ∀ g ∈ H, ψ * g = g * ψ) (hS : ∀ w ∈ S, ψ w ∈ S) :
    ∀ w ∈ closureIn H S, ψ w ∈ closureIn H S := by
  intro w hw
  have hle : closureIn H S ≤ (closureIn H S).comap ψ.toMonoidHom := by
    refine closureIn_le (fun x hx => le_closureIn (hS x hx)) (fun g hg x hx => ?_)
    rw [Subgroup.mem_comap] at hx ⊢
    have : ψ.toMonoidHom (g x) = g (ψ.toMonoidHom x) := by
      show ψ (g x) = g (ψ x)
      rw [← MulAut.mul_apply, hψ g hg, MulAut.mul_apply]
    rw [this]
    exact smul_mem_closureIn g hg _ hx
  exact hle hw

private theorem map_coreIn {H : Subgroup (MulAut Q)} {F : Subgroup Q} {ψ : MulAut Q}
    (hψ : ∀ g ∈ H, ψ * g = g * ψ) (hF : ∀ w ∈ F, ψ w ∈ F) :
    ∀ w ∈ coreIn H F, ψ w ∈ coreIn H F := by
  intro w hw
  refine mem_coreIn.2 fun h hh => ?_
  have : h (ψ w) = ψ (h w) := by rw [← MulAut.mul_apply, ← hψ h hh, MulAut.mul_apply]
  rw [this]
  exact hF _ (mem_coreIn.1 hw h hh)

end Core

section LemmaG

variable {Q : Type} [CommGroup Q] [Finite Q]

omit [Finite Q] in
private theorem smul_mem_sup' {H : Subgroup (MulAut Q)} {T U : Subgroup Q}
    (hT : ∀ g ∈ H, ∀ w ∈ T, g w ∈ T) (hU : ∀ g ∈ H, ∀ w ∈ U, g w ∈ U) :
    ∀ g ∈ H, ∀ w ∈ T ⊔ U, g w ∈ T ⊔ U := by
  intro g hg w hw
  obtain ⟨y, hy, u, hu, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hT g hg y hy) (hU g hg u hu)

private theorem not_commSub_le_inf {K A : Subgroup (MulAut Q)} (hK : CFSG.IsQuasisimple ↥K)
    (hAN : A ≤ Subgroup.normalizer (K : Set (MulAut Q))) (hA1 : A ≠ ⊥)
    (hAf : A ⊓ Subgroup.centralizer (K : Set (MulAut Q)) = ⊥) :
    ¬ commSub (closureIn (K ⊔ A) (commV A)) K ≤
      closureIn (K ⊔ A) (commV A) ⊓ coreIn (K ⊔ A) (fixV A) := by
  set H := K ⊔ A with hH
  set N := closureIn H (commV A) with hN
  set D := coreIn H (fixV A) with hD
  have hKperf : ⁅K, K⁆ = K := by
    have : Group.IsPerfect ↥K := hK.1
    exact Subgroup.commutator_eq_self
  intro hle
  have hKnt : ¬ commSub ⊤ K ≤ ⊥ := by
    intro h
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
    obtain ⟨k, hk1⟩ := exists_ne (1 : ↥K)
    apply hk1
    apply Subtype.ext
    refine MulEquiv.ext fun w => ?_
    have := h (Subgroup.subset_closure ⟨k, k.2, w, trivial, rfl⟩)
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  have hHbot : H ≤ stabSub (⊥ : Subgroup Q) :=
    B1.le_stabSub_of_invariant fun g _ w hw => by
      rw [Subgroup.mem_bot] at hw ⊢
      rw [hw, map_one]
  have hHtop : H ≤ stabSub (⊤ : Subgroup Q) :=
    B1.le_stabSub_of_invariant fun _ _ _ _ => trivial
  obtain ⟨U, X, -, hUX, -, hHU, hHX, hKXU, hirr⟩ :=
    SmithD310U.exists_chief_section_le hKperf bot_le hHbot hHtop hKnt
  have hKX : K ≤ stabSub X := le_sup_left.trans hHX
  have hKU : K ≤ stabSub U := le_sup_left.trans hHU
  have hAX : A ≤ stabSub X := le_sup_right.trans hHX
  have hAU : A ≤ stabSub U := le_sup_right.trans hHU
  have hKc : ¬ K ≤ centSec X U := by
    intro h
    apply hKXU
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, w, hw, rfl⟩
    exact (h hk).2 w hw
  have hAcent := SmithD310U.le_centralizer_of_centSec hK hKX hKU hAN hKc
  obtain ⟨a, ha, hac⟩ : ∃ a ∈ A, a ∉ centSec X U := by
    by_contra h
    push Not at h
    apply hA1
    rw [eq_bot_iff]
    intro b hb
    have : b ∈ A ⊓ Subgroup.centralizer (K : Set (MulAut Q)) := ⟨hb, hAcent ⟨hb, h b hb⟩⟩
    rwa [hAf] at this
  obtain ⟨x, hx, hxU⟩ : ∃ x ∈ X, a x * x⁻¹ ∉ U := by
    by_contra h
    push Not at h
    exact hac ⟨hAX ha, h⟩
  have hNinv : ∀ g ∈ H, ∀ w ∈ N, g w ∈ N := smul_mem_closureIn
  have hDinv : ∀ g ∈ H, ∀ w ∈ D, g w ∈ D := smul_mem_coreIn
  have hXinv : ∀ g ∈ H, ∀ w ∈ X, g w ∈ X := fun g hg w hw => (hHX hg w).2 hw
  have hUinv : ∀ g ∈ H, ∀ w ∈ U, g w ∈ U := fun g hg w hw => (hHU hg w).2 hw
  have hinf : ∀ {T T' : Subgroup Q}, (∀ g ∈ H, ∀ w ∈ T, g w ∈ T) →
      (∀ g ∈ H, ∀ w ∈ T', g w ∈ T') → ∀ g ∈ H, ∀ w ∈ T ⊓ T', g w ∈ T ⊓ T' :=
    fun hT hT' g hg w hw => ⟨hT g hg w hw.1, hT' g hg w hw.2⟩
  have hNX : (N ⊓ X) ⊔ U = X := by
    rcases hirr ((N ⊓ X) ⊔ U)
        (B1.le_stabSub_of_invariant (smul_mem_sup' (hinf hNinv hXinv) hUinv)) le_sup_right
        (sup_le inf_le_right hUX) with h | h
    · exfalso
      apply hxU
      rw [← h]
      refine Subgroup.mem_sup_left ⟨le_closureIn ?_, X.mul_mem ((hAX ha x).2 hx) (X.inv_mem hx)⟩
      rw [commV_eq_commSub]
      exact Subgroup.subset_closure ⟨a, ha, x, trivial, rfl⟩
    · exact h
  have hDX : D ⊓ X ≤ U := by
    rcases hirr ((D ⊓ X) ⊔ U)
        (B1.le_stabSub_of_invariant (smul_mem_sup' (hinf hDinv hXinv) hUinv)) le_sup_right
        (sup_le inf_le_right hUX) with h | h
    · rw [← h]
      exact le_sup_left
    · exfalso
      apply hxU
      have hx' : x ∈ (D ⊓ X) ⊔ U := by rw [h]; exact hx
      obtain ⟨d, hd, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx'
      have hda : a d = d := coreIn_le hd.1 a ha
      have e : a (d * u) * (d * u)⁻¹ = a u * u⁻¹ := by
        rw [map_mul, hda, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rw [e]
      exact U.mul_mem ((hAU ha u).2 hu) (U.inv_mem hu)
  apply hKXU
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, w, hw, rfl⟩
  rw [← hNX] at hw
  obtain ⟨y, hy, u, hu, rfl⟩ := Subgroup.mem_sup.1 hw
  have e : k (y * u) * (y * u)⁻¹ = (k y * y⁻¹) * (k u * u⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [e]
  refine U.mul_mem ?_ (U.mul_mem ((hKU hk u).2 hu) (U.inv_mem hu))
  have h1 : k y * y⁻¹ ∈ N ⊓ D := hle (Subgroup.subset_closure ⟨k, hk, y, hy.1, rfl⟩)
  have h2 : k y * y⁻¹ ∈ X := X.mul_mem ((hKX hk y).2 hy.2) (X.inv_mem hy.2)
  exact hDX ⟨h1.2, h2⟩

theorem false_of_two_mul_rkIdx_le (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hQ : ∀ q : Q, q ^ 2 = 1) {K A : Subgroup (MulAut Q)}
    (hH : IsQuotientOfSQTKTC ↥(K ⊔ A)) (hK : CFSG.IsQuasisimple ↥K)
    (hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hAf : A ⊓ Subgroup.centralizer (K : Set (MulAut Q)) = ⊥)
    (hr : 2 * rkIdx (fixV A) ≤ rk ↥A)
    (h5 : ∀ x ∈ K, ∀ k : ℕ, x ^ (5 ^ k) = 1 → x = 1)
    (hφ : 2 * rkIdx (fixV A) = rk ↥A → ∃ φ : MulAut Q, ∃ p : ℕ, p.Prime ∧ φ ^ p = 1 ∧
      (∀ q, φ q = q → q = 1) ∧ (∀ k ∈ K, φ * k = k * φ) ∧ (∀ a ∈ A, φ * a = a * φ) ∧
      ∀ x ∈ K, ∀ k : ℕ, x ^ (p ^ k) = 1 → x = 1) :
    False := by
  classical
  set H := K ⊔ A with hHdef
  have hAN : A ≤ Subgroup.normalizer (K : Set (MulAut Q)) :=
    fun a ha => mem_normalizer_of_conj hAK ha
  have hKperf : ⁅K, K⁆ = K := by
    have : Group.IsPerfect ↥K := hK.1
    exact Subgroup.commutator_eq_self
  set N := closureIn H (commV A) with hN
  set D := coreIn H (fixV A) with hD
  have hNinv : ∀ g ∈ H, ∀ w ∈ N, g w ∈ N := smul_mem_closureIn
  have hDinv : ∀ g ∈ H, ∀ w ∈ D, g w ∈ D := smul_mem_coreIn
  obtain ⟨U, X, hNDU, hUX, hXN, hHU, hHX, hKXU, hirr⟩ :=
    SmithD310U.exists_chief_section_le hKperf inf_le_left
      (B1.le_stabSub_of_invariant fun g hg w hw => ⟨hNinv g hg w hw.1, hDinv g hg w hw.2⟩)
      (B1.le_stabSub_of_invariant hNinv) (not_commSub_le_inf hK hAN hA1 hAf)
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hKX : K ≤ stabSub X := hKH.trans hHX
  have hKU : K ≤ stabSub U := hKH.trans hHU
  have hAX : A ≤ stabSub X := hAH.trans hHX
  have hXinv : ∀ g ∈ H, ∀ w ∈ X, g w ∈ X := fun g hg w hw => (hHX hg w).2 hw
  have hUinv : ∀ g ∈ H, ∀ w ∈ U, g w ∈ U := fun g hg w hw => (hHU hg w).2 hw
  have hUX' : U < X := by
    refine lt_of_le_of_ne hUX fun h => hKXU ?_
    rw [h]
    exact commSub_le_of_invariant fun x hx w hw => (hKX hx w).2 hw
  have hKc : ¬ K ≤ centSec X U := by
    intro h
    apply hKXU
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, w, hw, rfl⟩
    exact (h hk).2 w hw
  have hAcent := SmithD310U.le_centralizer_of_centSec hK hKX hKU hAN hKc
  have hAcs : A ⊓ centSec X U = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ A ⊓ Subgroup.centralizer (K : Set (MulAut Q)) := ⟨ha.1, hAcent ha⟩
    rwa [hAf] at this
  set φs := B5.secHom H hHX hHU with hφs
  let _iH : MulDistribMulAction ↥H (Sec X U) := MulDistribMulAction.compHom (Sec X U) φs
  have hact : ∀ (h : ↥H) (q : Sec X U), h • q = φs h q := fun _ _ => rfl
  have hQs : ∀ q : Sec X U, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hQ (x : Q))
      rw [this, QuotientGroup.mk_one]
  set K' := K.subgroupOf H with hK'
  set A' := A.subgroupOf H with hA'
  have hφH : ∀ h : ↥H, φs h ∈ autSec H X U := fun h => by
    rw [← B5.range_secHom H hHX hHU]
    exact ⟨h, rfl⟩
  have hK'q : CFSG.IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hK
  have hAK' : ∀ a ∈ A', ∀ x ∈ K', a * x * a⁻¹ ∈ K' := fun a ha x hx =>
    hAK _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hx)
  have hAc' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hAe.1 _ ha _ hb)
  have hA2' : ∀ a ∈ A', a ^ 2 = 1 := fun a ha => Subtype.ext (by simpa using hAe.2 _ ha)
  have htop : K' ⊔ A' = ⊤ := by
    rw [hK', hA', ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hirrS : XMod.IsIrrSec ↥(autSec H X U) (⊥ : Subgroup (Sec X U)) ⊤ :=
    B5.isIrrSec_autSec hUX' (fun J hJ hUJ hJX => hirr J (B1.le_stabSub_of_invariant hJ) hUJ hJX)
      hHX hHU
  have hirrT : XMod.IsIrr ↥(autSec H X U) (⊤ : Subgroup (Sec X U)) :=
    ⟨XMod.isInv_top, hirrS.1, fun J hJ _ _ => hirrS.2 J hJ bot_le le_top⟩
  have hY' : XMod.IsIrr ↥(K' ⊔ A') (⊤ : Subgroup (Sec X U)) := by
    refine isIrr_of_surj (Λ' := ↥(K' ⊔ A')) (Λ := ↥(autSec H X U))
      (fun x => ⟨φs (x : ↥H), hφH x⟩) ?_ (fun x q => rfl) hirrT
    rintro ⟨y, hy⟩
    rw [← B5.range_secHom H hHX hHU] at hy
    obtain ⟨h, rfl⟩ := hy
    exact ⟨⟨h, by rw [htop]; trivial⟩, rfl⟩
  have htriv : ∀ h : ↥H, (∀ y ∈ (⊤ : Subgroup (Sec X U)), h • y = y) →
      (h : MulAut Q) ∈ centSec X U := by
    intro h hhY
    have h2 : h ∈ φs.ker := by
      rw [MonoidHom.mem_ker]
      exact MulEquiv.ext fun r => hhY r trivial
    exact (B5.mem_ker_secHom H hHX hHU h).1 h2
  have hKY' : ∃ x ∈ K', ∃ y ∈ (⊤ : Subgroup (Sec X U)), x • y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact hKc fun x hx => htriv ⟨x, hKH hx⟩ (hcon _ hx)
  have hAY' : ∃ a ∈ A', ∃ y ∈ (⊤ : Subgroup (Sec X U)), a • y ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hA1
    rw [eq_bot_iff, ← hAcs]
    intro a ha
    exact ⟨ha, htriv ⟨a, hAH ha⟩ (hcon _ ha)⟩
  have hfixeq : XMod.fixed ↥A' (⊤ : Subgroup (Sec X U)) =
      XMod.fixed ↥(autSec A X U) (⊤ : Subgroup (Sec X U)) := by
    have hmap := B5.map_secHom_eq_autSec H hHX hHU hAH
    ext q
    constructor
    · intro hq
      refine ⟨trivial, fun p => ?_⟩
      have hp : (p : MulAut (Sec X U)) ∈ (A.subgroupOf H).map φs := by
        rw [hmap]
        exact p.2
      obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 hp
      have h1 := hq.2 ⟨a, ha⟩
      show (p : MulAut (Sec X U)) q = q
      rw [← hpa]
      exact h1
    · intro hq
      refine ⟨trivial, fun a => ?_⟩
      have hmem : φs a ∈ autSec A X U := by
        rw [← hmap]
        exact ⟨a, a.2, rfl⟩
      exact hq.2 ⟨φs a, hmem⟩
  have hnB : nB A' (⊤ : Subgroup (Sec X U)) = rkIdx (fixV (autSec A X U)) := by
    rw [← SmithD310U.nB_top_eq_rkIdx]
    unfold nB
    rw [hfixeq]
  have hrkA' : rk ↥A' = rk ↥A := by
    unfold rk
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
  have hrk0 : rk ↥(A' ⊓ fixingSubgroup ↥H ((⊤ : Subgroup (Sec X U)) : Set (Sec X U))) = 0 := by
    have hbot : A' ⊓ fixingSubgroup ↥H ((⊤ : Subgroup (Sec X U)) : Set (Sec X U)) = ⊥ := by
      rw [eq_bot_iff]
      rintro h ⟨hA, hfx⟩
      have : (h : MulAut Q) ∈ A ⊓ centSec X U :=
        ⟨hA, htriv h fun y hy => (mem_fixingSubgroup_iff ↥H).1 hfx y hy⟩
      rw [hAcs] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    rw [hbot, rk_bot]
  have hsec := rkIdx_fixV_autSec_add_le (A := A) hUX
  have hmono := rk_sub_rk_inf_le_rkIdx A X
  have hr' : 2 * nB A' (⊤ : Subgroup (Sec X U)) ≤
      rk ↥A' - rk ↥(A' ⊓ fixingSubgroup ↥H ((⊤ : Subgroup (Sec X U)) : Set (Sec X U))) := by
    rw [hnB, hrkA', hrk0]
    omega
  obtain ⟨J, -, hJ, hJc, hpos, hrat, hstrict, heqJ⟩ :=
    exists_irr_half (Γ := ↥H) hQs hAK' hAc' hA2' hY' hKY' hAY' hr'
  set A₀ := stabIn A' J with hA₀
  have hstab : ∀ a ∈ A₀, a • J = J := fun a ha => (mem_stabIn.1 ha).2
  have hA₀A : A₀ ≤ A' := inf_le_left
  have hAK₀ : ∀ a ∈ A₀, ∀ k ∈ K', a * k * a⁻¹ ∈ K' := fun a ha => hAK' a (hA₀A ha)
  have hA2₀ : ∀ a ∈ A₀, a ^ 2 = 1 := fun a ha => hA2' a (hA₀A ha)
  have hJK : ∀ k ∈ K', ∀ j ∈ J, k • j ∈ J := fun k hk j hj => hJ.1 ⟨k, hk⟩ j hj
  have hJA₀ : ∀ a ∈ A₀, ∀ j ∈ J, a • j ∈ J := by
    intro a ha j hj
    rw [← hstab a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hj
  have hJKA : ∀ g ∈ K' ⊔ A₀, ∀ j ∈ J, g • j ∈ J := fun g hg j hj =>
    smul_mem_of_mem_sup (A := K') (Λ := A₀) hJK hJA₀ hg j hj
  have hB4 := b4Hyp_resJ hA21 hH hQs hK'q hAK₀ hA2₀ hJ hJc hJK hJKA
  have hJ2 : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQs j)
  have hAbX : (resJ A₀ J hJA₀).range ≤ (resJ (K' ⊔ A₀) J hJKA).range :=
    range_resJ_mono le_sup_right
  have hAbel : IsElemAbelian2 (resJ A₀ J hJA₀).range :=
    isElemAbelian2_range_resJ (fun a ha b hb => hAc' a (hA₀A ha) b (hA₀A hb)) hA2₀ hJA₀
  have hrkAb := rk_range_resJ (S := A₀) (J := J) (hS := hJA₀)
  have hfixAb := rk_fixV_range_resJ (S := A₀) (J := J) (hS := hJA₀)
  have hidx := rk_add_rkIdx (fixV (resJ A₀ J hJA₀).range)
  have hJle : rk ↥(J ⊓ XMod.fixed ↥A₀ (⊤ : Subgroup (Sec X U))) ≤ rk ↥J := rk_mono inf_le_left
  have hpos' : 0 < rk ↥(resJ A₀ J hJA₀).range := by omega
  have hratio : 2 * rkIdx (fixV (resJ A₀ J hJA₀).range) ≤ rk ↥(resJ A₀ J hJA₀).range := by
    unfold nB at hrat
    omega
  obtain ⟨⟨F, hF⟩, hqle, hqlt⟩ := exists_offender_of_ratio_half hJ2 hAbX hAbel hpos' hratio
  have hconcl := hB42 ↥J hJ2 _ _ hB4 F hF
  let f : ↥K →* MulAut ↥J :=
    (resJ K' J hJK).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom
  have hfrange : ∀ y ∈ (resJ K' J hJK).range, ∃ k : ↥K, f k = y := by
    rintro _ ⟨k, rfl⟩
    refine ⟨Subgroup.subgroupOfEquivOfLe hKH k, ?_⟩
    simp [f]
  have hlift : ∀ {p : ℕ}, p.Prime → (∀ x ∈ K, ∀ k : ℕ, x ^ (p ^ k) = 1 → x = 1) →
      ∀ y ∈ (resJ K' J hJK).range, y ^ p = 1 → y = 1 := by
    intro p hp hpK y hy hyp
    obtain ⟨k, hk⟩ := hfrange y hy
    obtain ⟨c, m, hcm, hfc⟩ := exists_pElement_lift f hp hk hyp
    have h1 : ((k ^ c : ↥K) : MulAut Q) = 1 :=
      hpK _ (k ^ c).2 m (by rw [← Subgroup.coe_pow, hcm, Subgroup.coe_one])
    have h2 : k ^ c = 1 := Subtype.ext h1
    rw [← hfc, h2, map_one]
  rcases case2_or_case9 hconcl hqle with ⟨hq2, m, hm⟩ | ⟨n, hn, hBN⟩
  ·
    have hnlt : ¬ 2 * rkIdx (fixV (resJ A₀ J hJA₀).range) < rk ↥(resJ A₀ J hJA₀).range := by
      intro h
      have h1 := hqlt h
      rw [hq2] at h1
      exact lt_irrefl _ h1
    have heq₀ : 2 * nB A₀ J = rk ↥A₀ - rk ↥(A₀ ⊓ fixingSubgroup ↥H (J : Set (Sec X U))) := by
      unfold nB at hrat ⊢
      omega
    have hJtop : J = ⊤ := heqJ heq₀
    have heqY : 2 * nB A' (⊤ : Subgroup (Sec X U)) =
        rk ↥A' - rk ↥(A' ⊓ fixingSubgroup ↥H ((⊤ : Subgroup (Sec X U)) : Set (Sec X U))) := by
      by_contra hne
      have h1 := hstrict (lt_of_le_of_ne hr' hne)
      omega
    rw [hnB, hrkA', hrk0] at heqY
    have hE : 2 * rkIdx (fixV A) = rk ↥A := by omega
    have hU0 : rk ↥(U ⊓ fixV A) = rk ↥U := by
      have := rk_mono (inf_le_left : U ⊓ fixV A ≤ U)
      omega
    have hX0 : rk ↥X - rk ↥(X ⊓ fixV A) = rkIdx (fixV A) := by omega
    have hUA : U ≤ fixV A := by
      have hcard : Nat.card ↥U ≤ Nat.card ↥(U ⊓ fixV A) := by
        rw [card_eq_two_pow hQ, card_eq_two_pow hQ, hU0]
      rw [← Subgroup.eq_of_le_of_card_ge (inf_le_left : U ⊓ fixV A ≤ U) hcard]
      exact inf_le_right
    have hXA : commV A ≤ X := commV_le_of_rk_eq hQ (fun a ha x hx => (hAX ha x).2 hx) hX0
    have hXeq : X = N := le_antisymm hXN (closureIn_le hXA hXinv)
    have hUeq : U = N ⊓ D := le_antisymm (le_inf (hUX.trans hXN) (le_coreIn hUinv hUA)) hNDU
    obtain ⟨φ, p, hp, hφp, hφfp, hφK, hφA, hpK⟩ := hφ hE
    have hinvK : ∀ k ∈ K, φ⁻¹ * k = k * φ⁻¹ := fun k hk => by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hφK k hk, mul_assoc, mul_inv_cancel, mul_one]
    have hinvA : ∀ a ∈ A, φ⁻¹ * a = a * φ⁻¹ := fun a ha => by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hφA a ha, mul_assoc, mul_inv_cancel, mul_one]
    have hpres : ∀ ψ : MulAut Q, (∀ k ∈ K, ψ * k = k * ψ) → (∀ a ∈ A, ψ * a = a * ψ) →
        (∀ w ∈ N, ψ w ∈ N) ∧ (∀ w ∈ D, ψ w ∈ D) := by
      intro ψ hψK hψA
      have hψH := commute_sup hψK hψA
      have hcA : ∀ a ∈ A, ∀ w : Q, ψ (a w) = a (ψ w) := fun a ha w => by
        rw [← MulAut.mul_apply, hψA a ha, MulAut.mul_apply]
      refine ⟨map_closureIn hψH fun w hw => ?_, map_coreIn hψH fun w hw a ha => ?_⟩
      · rw [commV_eq_commSub, commSub] at hw ⊢
        have hle : Subgroup.closure {c | ∃ x ∈ A, ∃ w ∈ (⊤ : Subgroup Q), x w * w⁻¹ = c} ≤
            (Subgroup.closure {c | ∃ x ∈ A, ∃ w ∈ (⊤ : Subgroup Q), x w * w⁻¹ = c}).comap
              ψ.toMonoidHom := by
          rw [Subgroup.closure_le]
          rintro _ ⟨x, hx, v, -, rfl⟩
          refine Subgroup.subset_closure ⟨x, hx, ψ v, trivial, ?_⟩
          show x (ψ v) * (ψ v)⁻¹ = ψ (x v * v⁻¹)
          rw [map_mul, map_inv, hcA x hx]
        exact hle hw
      · rw [← hcA a ha, hw a ha]
    obtain ⟨hφN, hφD⟩ := hpres φ hφK hφA
    obtain ⟨hφN', hφD'⟩ := hpres φ⁻¹ hinvK hinvA
    have hφX : φ ∈ stabSub X := by
      rw [hXeq]
      exact mem_stabSub_of_inv hφN hφN'
    have hφU : φ ∈ stabSub U := by
      rw [hUeq]
      exact mem_stabSub_of_inv (fun w hw => ⟨hφN w hw.1, hφD w hw.2⟩)
        (fun w hw => ⟨hφN' w hw.1, hφD' w hw.2⟩)
    have hzX : Subgroup.zpowers φ ≤ stabSub X := (Subgroup.zpowers_le).2 hφX
    have hzU : Subgroup.zpowers φ ≤ stabSub U := (Subgroup.zpowers_le).2 hφU
    set φb := B5.secHom (Subgroup.zpowers φ) hzX hzU ⟨φ, Subgroup.mem_zpowers φ⟩ with hφb
    have hφH := commute_sup hφK hφA
    have hφbH : ∀ h : ↥H, φb * φs h = φs h * φb := by
      intro h
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H w =>
        show φb (φs h (QuotientGroup.mk w)) = φs h (φb (QuotientGroup.mk w))
        rw [hφb, hφs, B5.secHom_mk, B5.secHom_mk, B5.secHom_mk, B5.secHom_mk]
        congr 1
        apply Subtype.ext
        show φ ((h : MulAut Q) (w : Q)) = (h : MulAut Q) (φ (w : Q))
        rw [← MulAut.mul_apply, hφH h h.2, MulAut.mul_apply]
    have hφbp : φb ^ p = 1 := by
      rw [hφb, ← map_pow]
      have : (⟨φ, Subgroup.mem_zpowers φ⟩ : ↥(Subgroup.zpowers φ)) ^ p = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, hφp, Subgroup.coe_one])
      rw [this, map_one]
    have hφb1 : φb ≠ 1 := by
      intro h1
      have hker : (⟨φ, Subgroup.mem_zpowers φ⟩ : ↥(Subgroup.zpowers φ)) ∈
          (B5.secHom (Subgroup.zpowers φ) hzX hzU).ker := by
        rw [MonoidHom.mem_ker]
        exact h1
      rw [B5.mem_ker_secHom] at hker
      let δ : Q →* Q :=
        { toFun := fun q => φ q * q⁻¹
          map_one' := by simp
          map_mul' := fun a b => by
            rw [map_mul, mul_inv]
            ac_rfl }
      have hδinj : Function.Injective δ := by
        rw [injective_iff_map_eq_one]
        intro q hq
        exact hφfp q (mul_inv_eq_one.1 hq)
      have hδN : X.map δ ≤ U := by
        rintro _ ⟨w, hw, rfl⟩
        exact hker.2 w hw
      have hcard : Nat.card ↥X ≤ Nat.card ↥U := by
        rw [← Subgroup.card_map_of_injective hδinj]
        exact Subgroup.card_le_of_le hδN
      exact hUX'.ne (Subgroup.eq_of_le_of_card_ge hUX hcard)
    have hJall : ∀ q : Sec X U, q ∈ J := fun q => by rw [hJtop]; trivial
    let θ : MulAut ↥J :=
      { toFun := fun j => ⟨φb j, hJall _⟩
        invFun := fun j => ⟨φb⁻¹ j, hJall _⟩
        left_inv := fun j => Subtype.ext (by simp)
        right_inv := fun j => Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    have hθ : ∀ j : ↥J, ((θ j : ↥J) : Sec X U) = φb j := fun _ => rfl
    have hθpow : ∀ k : ℕ, ∀ j : ↥J, (((θ ^ k) j : ↥J) : Sec X U) = (φb ^ k) j := by
      intro k
      induction k with
      | zero => intro j; rfl
      | succ k ih =>
        intro j
        rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply, hθ]
    have hθcomm : ∀ l ∈ (resJ K' J hJK).range, θ * l = l * θ := by
      rintro _ ⟨k, rfl⟩
      refine MulEquiv.ext fun j => Subtype.ext ?_
      show φb (φs (k : ↥H) j) = φs (k : ↥H) (φb j)
      rw [← MulAut.mul_apply, hφbH, MulAut.mul_apply]
    have hθp : θ ^ p = 1 :=
      MulEquiv.ext fun j => Subtype.ext (by rw [hθpow, hφbp]; rfl)
    have hθ1 : θ ≠ 1 := by
      intro h1
      apply hφb1
      refine MulEquiv.ext fun q => ?_
      have := congrArg (fun t : MulAut ↥J => ((t ⟨q, hJall q⟩ : ↥J) : Sec X U)) h1
      exact this
    obtain ⟨y, hyL, hyp, hy1⟩ := exists_pow_prime_of_binaryNaturalSL3 hm hθcomm hp hθp hθ1
    exact hy1 (hlift hp hpK y hyL hyp)
  · obtain ⟨y, hyL, hy5, hy1⟩ := exists_pow_five_of_binaryNaturalSL45 hn hBN
    exact hy1 (hlift Nat.prime_five h5 y hyL hy5)

end LemmaG

section Mult

variable {R : Type*} [Ring R] {I : Type*} [AddCommGroup I] [Module R I]

theorem exists_mult_pi [Finite I] [IsSimpleModule R I] {d : ℕ}
    (hd : Nat.card I = Nat.card (Module.End R I) ^ d) (c : ℕ) :
    ∃ X : AddSubgroup (Fin c → I),
      (∀ f : (Fin c → I) →ₗ[R] (Fin c → I), ∀ x ∈ X, f x ∈ X) ∧
      (∀ S : Set ((Fin c → I) →ₗ[R] (Fin c → I)),
        Nat.card {y : Fin c → I // ∀ f ∈ S, f y = y} =
          Nat.card {x : X // ∀ f ∈ S, f x = x} ^ d) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (Module.End R I) - 1 →
        ∃ φ : (Fin c → I) →ₗ[R] (Fin c → I),
          (∀ f : (Fin c → I) →ₗ[R] (Fin c → I), ∀ y, φ (f y) = f (φ y)) ∧
          (∀ x ∈ X, φ x ∈ X) ∧ (∀ y, (φ ^ p) y = y) ∧ ∀ y, φ y = y → y = 0 := by
  classical
  set D := Module.End R I with hD
  have : Finite D := Finite.of_injective (fun f : D => (f : I → I))
    (fun f g h => LinearMap.ext (congrFun h))
  have : Fintype D := Fintype.ofFinite D
  have : Fintype I := Fintype.ofFinite I
  have hDc : ∀ a b : D, a * b = b * a := fun a b => mul_comm a b
  have : Module.Finite D I := Module.Finite.of_finite
  set b := Module.Free.chooseBasis D I with hb
  set ι := Module.Free.ChooseBasisIndex D I with hι
  have hcardι : Fintype.card ι = d := by
    have h1 : Fintype.card I = Fintype.card D ^ Module.finrank D I := Module.card_eq_pow_finrank
    rw [Module.finrank_eq_card_chooseBasisIndex] at h1
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hd] at h1
    have hD2 : 1 < Nat.card D := by
      have : Nontrivial D := inferInstance
      exact Finite.one_lt_card
    exact (Nat.pow_right_injective hD2 h1).symm
  set crdE : I ≃ (ι → D) := b.repr.toEquiv.trans Finsupp.equivFunOnFinite with hcrdE
  have crd_add : ∀ v w : I, crdE (v + w) = crdE v + crdE w := fun v w => by
    funext i
    simp [hcrdE]
  have crd_smul : ∀ (a : D) (v : I), crdE (a v) = fun i => a * crdE v i := fun a v => by
    funext i
    simp only [hcrdE, Equiv.trans_apply, LinearEquiv.coe_toEquiv, Finsupp.equivFunOnFinite_apply]
    rw [← Module.End.smul_def, b.repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have crd_zero : crdE 0 = 0 := by
    funext i
    simp [hcrdE]
  have crd_neg : ∀ v : I, crdE (-v) = -crdE v := fun v => by
    funext i
    simp [hcrdE]
  let ent : ((Fin c → I) →ₗ[R] (Fin c → I)) → Fin c → Fin c → D := fun f j k =>
    (LinearMap.proj j) ∘ₗ f ∘ₗ (LinearMap.single R (fun _ => I) k)
  have hent : ∀ f (y : Fin c → I) j, f y j = ∑ k, ent f j k (y k) := by
    intro f y j
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum, Finset.sum_apply]
    rfl
  have hcrdf : ∀ f (y : Fin c → I) j i, crdE (f y j) i = ∑ k, ent f j k * crdE (y k) i := by
    intro f y j i
    rw [hent f y j]
    have hsum : ∀ (s : Finset (Fin c)) (g : Fin c → I),
        crdE (∑ k ∈ s, g k) i = ∑ k ∈ s, crdE (g k) i := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp [crd_zero]
      | insert a s ha ih => rw [Finset.sum_insert ha, crd_add, Pi.add_apply, ih,
          Finset.sum_insert ha]
    rw [hsum]
    exact Finset.sum_congr rfl fun k _ => congrFun (crd_smul (ent f j k) (y k)) i
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hd
      have : Nontrivial I := IsSimpleModule.nontrivial R I
      have h1 := Finite.one_lt_card (α := I)
      omega
    · exact h0
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcardι]
    exact hd0
  obtain ⟨i₀⟩ := this
  let X : AddSubgroup (Fin c → I) :=
    { carrier := {y | ∀ k, ∀ i, i ≠ i₀ → crdE (y k) i = 0}
      add_mem' := fun {a b} ha hb k i hi => by
        rw [Pi.add_apply, crd_add, Pi.add_apply, ha k i hi, hb k i hi, add_zero]
      zero_mem' := fun k i _ => by rw [Pi.zero_apply, crd_zero, Pi.zero_apply]
      neg_mem' := fun {a} ha k i hi => by
        rw [Pi.neg_apply, crd_neg, Pi.neg_apply, ha k i hi, neg_zero] }
  have hmemX : ∀ y, y ∈ X ↔ ∀ k, ∀ i, i ≠ i₀ → crdE (y k) i = 0 := fun y => Iff.rfl
  have hfix : ∀ (S : Set ((Fin c → I) →ₗ[R] (Fin c → I))) (y : Fin c → I),
      (∀ f ∈ S, f y = y) ↔ ∀ i, ∀ f ∈ S, ∀ j, ∑ k, ent f j k * crdE (y k) i = crdE (y j) i := by
    intro S y
    constructor
    · intro h i f hf j
      rw [← hcrdf, h f hf]
    · intro h f hf
      funext j
      apply crdE.injective
      funext i
      rw [hcrdf]
      exact h i f hf j
  refine ⟨X, ?_, ?_, ?_⟩
  · intro f x hx j i hi
    rw [hcrdf]
    exact Finset.sum_eq_zero fun k _ => by rw [(hmemX x).1 hx k i hi, mul_zero]
  · intro S
    set P : (Fin c → D) → Prop := fun u => ∀ f ∈ S, ∀ j, ∑ k, ent f j k * u k = u j with hP
    let E : (Fin c → I) ≃ (ι → Fin c → D) :=
      (Equiv.piCongrRight fun _ => crdE).trans (Equiv.piComm _)
    have hE : ∀ y i k, E y i k = crdE (y k) i := fun _ _ _ => rfl
    have e1 : {y : Fin c → I // ∀ f ∈ S, f y = y} ≃ {w : ι → Fin c → D // ∀ i, P (w i)} :=
      Equiv.subtypeEquiv E fun y => by
        rw [hfix]
        rfl
    have h1 : Nat.card {y : Fin c → I // ∀ f ∈ S, f y = y} = Nat.card {u // P u} ^ d := by
      rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi)), Nat.card_fun,
        Nat.card_eq_fintype_card (α := ι), hcardι]
    have e2 : {x : X // ∀ f ∈ S, f x = x} ≃ {u // P u} :=
      { toFun := fun x => ⟨fun k => crdE (x.1.1 k) i₀,
          fun f hf j => ((hfix S x.1.1).1 x.2) i₀ f hf j⟩
        invFun := fun u => ⟨⟨fun k => crdE.symm (Pi.single i₀ (u.1 k)), fun k i hi => by
            rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hi]⟩, by
          refine (hfix S _).2 fun i f hf j => ?_
          simp only [Equiv.apply_symm_apply]
          by_cases hi : i = i₀
          · subst hi
            simp only [Pi.single_eq_same]
            exact u.2 f hf j
          · simp only [Pi.single_eq_of_ne hi, mul_zero, Finset.sum_const_zero]⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          funext k
          apply crdE.injective
          rw [Equiv.apply_symm_apply]
          funext i
          by_cases hi : i = i₀
          · subst hi
            rw [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne hi, (hmemX x.1.1).1 x.1.2 k i hi]
        right_inv := fun u => by
          apply Subtype.ext
          funext k
          show crdE (crdE.symm (Pi.single i₀ (u.1 k))) i₀ = u.1 k
          rw [Equiv.apply_symm_apply, Pi.single_eq_same] }
    rw [h1, Nat.card_congr e2]
  · intro p hp hpD
    have : Fact p.Prime := ⟨hp⟩
    have hpu : p ∣ Fintype.card Dˣ := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
      exact hpD
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card p hpu
    let φ : (Fin c → I) →ₗ[R] (Fin c → I) :=
      LinearMap.pi fun k => (l : D) ∘ₗ LinearMap.proj k
    have hφ : ∀ y k, φ y k = (l : D) (y k) := fun _ _ => rfl
    have hφpow : ∀ n : ℕ, ∀ y k, (φ ^ n) y k = ((l : D) ^ n) (y k) := by
      intro n
      induction n with
      | zero => intro y k; rfl
      | succ n ih =>
        intro y k
        rw [pow_succ', Module.End.mul_apply, hφ, ih, pow_succ', Module.End.mul_apply]
    have hl1 : l ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hl
      exact hp.one_lt.ne' hl.symm
    have hcφ : ∀ y k i, crdE (φ y k) i = (l : D) * crdE (y k) i := fun y k i => by
      rw [hφ, crd_smul]
    refine ⟨φ, fun f y => ?_, fun x hx k i hi => ?_, fun y => ?_, fun y hy => ?_⟩
    · funext j
      apply crdE.injective
      funext i
      rw [hcφ, hcrdf, hcrdf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcφ, ← mul_assoc, ← mul_assoc, hDc (l : D)]
    · rw [hcφ, (hmemX x).1 hx k i hi, mul_zero]
    · funext k
      have hlp : l ^ p = 1 := by
        rw [← hl]
        exact pow_orderOf_eq_one l
      rw [hφpow, ← Units.val_pow_eq_pow_val, hlp, Units.val_one]
      rfl
    · funext k
      have h1 : ((l : D) - 1) (y k) = 0 := by
        rw [LinearMap.sub_apply, ← hφ, hy, Module.End.one_apply, sub_self]
      have h2 : (l : D) - 1 ≠ 0 := by
        intro h
        apply hl1
        exact Units.ext (sub_eq_zero.1 h)
      have h3 : ((l : D) - 1)⁻¹ * ((l : D) - 1) = 1 := inv_mul_cancel₀ h2
      calc y k = (((l : D) - 1)⁻¹ * ((l : D) - 1)) (y k) := by rw [h3]; rfl
        _ = 0 := by rw [Module.End.mul_apply, h1, map_zero]

end Mult

section MultQ

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

open CFSG.Quasithin.SmithD39Two CFSG.Quasithin.SmithD391

theorem smul_mem_isoComp {Λ : Subgroup Γ} {J : Subgroup Q} {g : Γ}
    (hg : ∀ l ∈ Λ, l * g = g * l) : ∀ q ∈ isoComp ↥Λ J, g • q ∈ isoComp ↥Λ J := by
  have hg' : ∀ l ∈ Λ, g * l = l * g := fun l hl => (hg l hl).symm
  have hle : isoComp ↥Λ J ≤ (isoComp ↥Λ J).comap (MulDistribMulAction.toMonoidHom Q g) := by
    refine iSup_le fun J' => ?_
    intro q hq
    rw [Subgroup.mem_comap]
    have hirr : XMod.IsIrr ↥Λ (g • (J' : Subgroup Q)) := isIrr_smul_of_comm J'.2.1 hg'
    have hiso : XMod.Iso ↥Λ (g • (J' : Subgroup Q)) J :=
      XMod.Iso.trans (iso_smul_of_comm J'.2.1.1 hg') J'.2.2
    exact le_isoComp hirr hiso (Subgroup.smul_mem_pointwise_smul _ _ _ hq)
  exact fun q hq => hle hq

theorem exists_mult_sub [Finite Q] {Λ : Subgroup Γ} {J : Subgroup Q} (hJ : XMod.IsIrr ↥Λ J)
    {d : ℕ} (hd : Nat.card ↥J =
      Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hJ.1)) ^ d) :
    ∃ X : Subgroup Q, X ≤ isoComp ↥Λ J ∧
      (∀ g : Γ, (∀ l ∈ Λ, l * g = g * l) → ∀ x ∈ X, g • x ∈ X) ∧
      (∀ P : Subgroup Γ, (∀ g ∈ P, ∀ l ∈ Λ, l * g = g * l) →
        Nat.card ↥(isoComp ↥Λ J ⊓ XMod.fixed ↥P ⊤) = Nat.card ↥(X ⊓ XMod.fixed ↥P ⊤) ^ d) ∧
      ∀ p : ℕ, p.Prime →
        p ∣ Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hJ.1)) - 1 →
        ∃ φ : MulAut ↥X, φ ^ p = 1 ∧ (∀ x, φ x = x → x = 1) ∧
          ∀ g : Γ, (∀ l ∈ Λ, l * g = g * l) → ∀ x y : ↥X, (y : Q) = g • (x : Q) →
            ((φ y : ↥X) : Q) = g • ((φ x : ↥X) : Q) := by
  classical
  set R := ↥(XMod.opRing ↥Λ Q) with hR
  set T := isoComp ↥Λ J with hTdef
  have hT : XMod.IsInv ↥Λ T := isInv_isoComp J
  set Ym := XMod.toSubmod hT with hYm
  set Im := XMod.toSubmod hJ.1 with hIm
  have : IsSimpleModule R ↥Im := (XMod.isIrr_iff hJ.1).1 hJ
  have : IsSemisimpleModule R ↥Ym := isSemisimpleModule_toSubmod hJ hT le_rfl
  have hiso : IsIsotypicOfType R ↥Ym ↥Im := isIsotypicOfType_toSubmod hJ hT le_rfl
  have : Module.Finite R ↥Ym := Module.Finite.of_finite
  obtain ⟨c, ⟨e⟩⟩ := hiso.linearEquiv_fun
  have hd' : Nat.card ↥Im = Nat.card (Module.End R ↥Im) ^ d := by
    rw [card_toSubmod hJ.1]
    exact hd
  obtain ⟨X₀, hX₀f, hX₀c, hX₀φ⟩ := exists_mult_pi hd' c
  let ρ : ∀ g : Γ, (∀ l ∈ Λ, l * g = g * l) → (↥Ym →ₗ[R] ↥Ym) := fun g hg =>
    { toFun := fun a => ⟨Additive.ofMul (g • Additive.toMul a.1),
        smul_mem_isoComp (Λ := Λ) (J := J) hg (Additive.toMul a.1) a.2⟩
      map_add' := fun a b => Subtype.ext (by
        show Additive.ofMul (g • Additive.toMul (a.1 + b.1)) =
          Additive.ofMul (g • Additive.toMul a.1) + Additive.ofMul (g • Additive.toMul b.1)
        rw [toMul_add, smul_mul', ofMul_mul])
      map_smul' := fun r a => Subtype.ext (by
        show Additive.ofMul (g • Additive.toMul ((r : AddMonoid.End (Additive Q)) a.1)) =
          (r : AddMonoid.End (Additive Q)) (Additive.ofMul (g • Additive.toMul a.1))
        rw [opRing_apply_ofMul_smul hg r.2, ofMul_toMul]) }
  have hρ : ∀ g hg (a : ↥Ym), ((ρ g hg a : ↥Ym) : Additive Q) =
      Additive.ofMul (g • Additive.toMul (a : Additive Q)) := fun _ _ _ => rfl
  let F : ∀ g : Γ, (∀ l ∈ Λ, l * g = g * l) → ((Fin c → ↥Im) →ₗ[R] (Fin c → ↥Im)) :=
    fun g hg => e.toLinearMap ∘ₗ ρ g hg ∘ₗ e.symm.toLinearMap
  have hF : ∀ g hg (a : ↥Ym), F g hg (e a) = e (ρ g hg a) := fun g hg a => by
    simp [F]
  let X : Subgroup Q :=
    { carrier := {q | ∃ hq : q ∈ T, e ⟨Additive.ofMul q, hq⟩ ∈ X₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨T.mul_mem ha hb, ?_⟩
        have : (⟨Additive.ofMul (a * b), T.mul_mem ha hb⟩ : ↥Ym) =
            ⟨Additive.ofMul a, ha⟩ + ⟨Additive.ofMul b, hb⟩ := rfl
        rw [this, map_add]
        exact X₀.add_mem ha' hb'
      one_mem' := ⟨T.one_mem, by
        have : (⟨Additive.ofMul 1, T.one_mem⟩ : ↥Ym) = 0 := rfl
        rw [this, map_zero]
        exact X₀.zero_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨T.inv_mem ha, ?_⟩
        have : (⟨Additive.ofMul a⁻¹, T.inv_mem ha⟩ : ↥Ym) = -⟨Additive.ofMul a, ha⟩ := rfl
        rw [this, map_neg]
        exact X₀.neg_mem ha' }
  have hmemX : ∀ q, q ∈ X ↔ ∃ hq : q ∈ T, e ⟨Additive.ofMul q, hq⟩ ∈ X₀ := fun _ => Iff.rfl
  have hfixP : ∀ (P : Subgroup Γ) (hP : ∀ g ∈ P, ∀ l ∈ Λ, l * g = g * l) (a : ↥Ym),
      Additive.toMul a.1 ∈ XMod.fixed ↥P ⊤ ↔ ∀ f ∈ Set.range (fun g : ↥P => F g (hP g g.2)),
        f (e a) = e a := by
    intro P hP a
    constructor
    · rintro ⟨-, hfx⟩ _ ⟨g, rfl⟩
      rw [hF g (hP g g.2)]
      congr 1
      apply Subtype.ext
      rw [hρ g (hP g g.2)]
      exact congrArg Additive.ofMul (hfx g)
    · intro h
      refine ⟨trivial, fun g => ?_⟩
      have h1 := h _ ⟨g, rfl⟩
      rw [hF g (hP g g.2)] at h1
      have h2 := congrArg Subtype.val (e.injective h1)
      rw [hρ g (hP g g.2)] at h2
      exact Additive.ofMul.injective h2
  refine ⟨X, fun q hq => hq.1, fun g hg x hx => ?_, fun P hP => ?_, fun p hp hpD => ?_⟩
  · obtain ⟨hxT, hxX⟩ := hx
    refine ⟨smul_mem_isoComp hg x hxT, ?_⟩
    have h1 := hX₀f (F g hg) _ hxX
    rw [hF g hg] at h1
    exact h1
  · set S := Set.range (fun g : ↥P => F g (hP g g.2)) with hS
    have e1 : ↥(T ⊓ XMod.fixed ↥P ⊤) ≃ {z : Fin c → ↥Im // ∀ f ∈ S, f z = z} :=
      { toFun := fun q => ⟨e ⟨Additive.ofMul q.1, q.2.1⟩,
          (hfixP P hP ⟨Additive.ofMul q.1, q.2.1⟩).1 q.2.2⟩
        invFun := fun z => ⟨Additive.toMul (e.symm z.1).1, (e.symm z.1).2,
          (hfixP P hP (e.symm z.1)).2 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩
        left_inv := fun q => Subtype.ext (by
          show Additive.toMul (e.symm (e ⟨Additive.ofMul q.1, q.2.1⟩)).1 = q.1
          rw [LinearEquiv.symm_apply_apply]
          rfl)
        right_inv := fun z => Subtype.ext (LinearEquiv.apply_symm_apply e z.1) }
    have e2 : ↥(X ⊓ XMod.fixed ↥P ⊤) ≃ {x : X₀ // ∀ f ∈ S, f x = x} :=
      { toFun := fun q => ⟨⟨e ⟨Additive.ofMul q.1, q.2.1.1⟩, q.2.1.2⟩,
          (hfixP P hP ⟨Additive.ofMul q.1, q.2.1.1⟩).1 q.2.2⟩
        invFun := fun z => ⟨Additive.toMul (e.symm z.1.1).1, ⟨(e.symm z.1.1).2, by
            show e (e.symm z.1.1) ∈ X₀
            rw [LinearEquiv.apply_symm_apply]
            exact z.1.2⟩,
          (hfixP P hP (e.symm z.1.1)).2 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩
        left_inv := fun q => Subtype.ext (by
          show Additive.toMul (e.symm (e ⟨Additive.ofMul q.1, q.2.1.1⟩)).1 = q.1
          rw [LinearEquiv.symm_apply_apply]
          rfl)
        right_inv := fun z => Subtype.ext (Subtype.ext (LinearEquiv.apply_symm_apply e z.1.1)) }
    rw [Nat.card_congr e1, Nat.card_congr e2]
    exact hX₀c S
  · obtain ⟨φ₀, hφ₀f, hφ₀X, hφ₀p, hφ₀fp⟩ := hX₀φ p hp hpD
    have hinj₀ : Function.Injective φ₀ := by
      intro a b hab
      obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
      have ha := hφ₀p a
      have hb := hφ₀p b
      rw [hk, pow_succ, Module.End.mul_apply] at ha hb
      rw [← ha, ← hb, hab]
    let toY : ↥X → ↥Ym := fun x => ⟨Additive.ofMul (x : Q), x.2.1⟩
    have hmapX : ∀ x : ↥X, Additive.toMul (e.symm (φ₀ (e (toY x)))).1 ∈ X := by
      intro x
      refine ⟨(e.symm _).2, ?_⟩
      show e (e.symm (φ₀ (e (toY x)))) ∈ X₀
      rw [LinearEquiv.apply_symm_apply]
      exact hφ₀X _ x.2.2
    have htoY_mul : ∀ x y : ↥X, toY (x * y) = toY x + toY y := fun _ _ => rfl
    have htoY_one : toY 1 = 0 := rfl
    obtain ⟨φX, hφXY⟩ : ∃ φX : ↥X →* ↥X, ∀ x, toY (φX x) = e.symm (φ₀ (e (toY x))) :=
      ⟨{ toFun := fun x => ⟨_, hmapX x⟩
         map_one' := Subtype.ext (by
           show Additive.toMul (e.symm (φ₀ (e (toY 1)))).1 = 1
           rw [htoY_one, LinearEquiv.map_zero, LinearMap.map_zero, LinearEquiv.map_zero]
           rfl)
         map_mul' := fun x y => Subtype.ext (by
           show Additive.toMul (e.symm (φ₀ (e (toY (x * y))))).1 =
             Additive.toMul (e.symm (φ₀ (e (toY x)))).1 *
               Additive.toMul (e.symm (φ₀ (e (toY y)))).1
           rw [htoY_mul, LinearEquiv.map_add, LinearMap.map_add, LinearEquiv.map_add]
           rfl) }, fun x => Subtype.ext rfl⟩
    have htoY_inj : Function.Injective toY := fun x y h =>
      Subtype.ext (Additive.ofMul.injective (congrArg (fun a : ↥Ym => (a : Additive Q)) h))
    have hinjX : Function.Injective φX := by
      intro x y hxy
      have h1 : toY (φX x) = toY (φX y) := by rw [hxy]
      rw [hφXY, hφXY] at h1
      exact htoY_inj (e.injective (hinj₀ (e.symm.injective h1)))
    obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥X, ∀ x, φ x = φX x :=
      ⟨MulEquiv.ofBijective φX ⟨hinjX, Finite.injective_iff_surjective.1 hinjX⟩, fun _ => rfl⟩
    have hpow : ∀ k : ℕ, ∀ x : ↥X, toY ((φ ^ k) x) = e.symm ((φ₀ ^ k) (e (toY x))) := by
      intro k
      induction k with
      | zero =>
        intro x
        rw [pow_zero, pow_zero, MulAut.one_apply, Module.End.one_apply,
          LinearEquiv.symm_apply_apply]
      | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, hφ, hφXY, ih, LinearEquiv.apply_symm_apply, pow_succ',
          Module.End.mul_apply]
    refine ⟨φ, MulEquiv.ext fun x => htoY_inj ?_, fun x hx => ?_, fun g hg x y hxy => ?_⟩
    · rw [hpow, hφ₀p, LinearEquiv.symm_apply_apply, MulAut.one_apply]
    · have h1 : toY (φ x) = toY x := by rw [hx]
      rw [hφ, hφXY] at h1
      have h2 : φ₀ (e (toY x)) = e (toY x) := by
        have := congrArg e h1
        rwa [LinearEquiv.apply_symm_apply] at this
      have h3 := hφ₀fp _ h2
      have h4 : toY x = 0 := by
        rw [← e.symm.map_zero, ← h3, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (Additive.ofMul.injective
        (congrArg (fun a : ↥Ym => (a : Additive Q)) h4))
    · have h1 : toY y = ρ g hg (toY x) := Subtype.ext (by
        show Additive.ofMul (y : Q) = Additive.ofMul (g • (x : Q))
        rw [hxy])
      have h2 : e (toY (φ y)) = e (ρ g hg (toY (φ x))) := by
        rw [← hF g hg, hφ, hφ, hφXY, hφXY, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, h1, ← hF g hg, hφ₀f]
      have h3 := congrArg (fun a : ↥Ym => (a : Additive Q)) (e.injective h2)
      rw [hρ g hg] at h3
      exact Additive.ofMul.injective h3

end MultQ

section EndCard

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem card_end_eq [Finite Q] {Λ : Subgroup Γ} {I : Subgroup Q} (hI : XMod.IsInv ↥Λ I) :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI)) =
      Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} := by
  classical
  have : Finite (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI)) :=
    Finite.of_injective (fun f => (f : ↥(XMod.toSubmod hI) → ↥(XMod.toSubmod hI)))
      (fun f g h => LinearMap.ext (congrFun h))
  refine le_antisymm (card_end_le hI) ?_
  have key : ∀ θ : ↥I →* ↥I, IsEqv Λ (I.subtype.comp θ) → ∀ f ∈ XMod.opRing ↥Λ Q, ∀ x : ↥I,
      ∃ (hx : Additive.toMul (f (Additive.ofMul (x : Q))) ∈ I)
        (hy : Additive.toMul (f (Additive.ofMul ((θ x : ↥I) : Q))) ∈ I),
        θ ⟨Additive.toMul (f (Additive.ofMul (x : Q))), hx⟩ =
          ⟨Additive.toMul (f (Additive.ofMul ((θ x : ↥I) : Q))), hy⟩ := by
    intro θ hθ f hf
    induction hf using Subring.closure_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      intro x
      have hx : (a : Γ) • (x : Q) ∈ I := hI a _ x.2
      have hy : (a : Γ) • ((θ x : ↥I) : Q) ∈ I := hI a _ (θ x).2
      exact ⟨hx, hy, Subtype.ext (hθ a x ⟨(a : Γ) • (x : Q), hx⟩ rfl)⟩
    | zero =>
      intro x
      exact ⟨I.one_mem, I.one_mem, Subtype.ext (congrArg Subtype.val (map_one θ))⟩
    | one =>
      intro x
      exact ⟨x.2, (θ x).2, rfl⟩
    | add f g _ _ hf hg =>
      intro x
      obtain ⟨hxf, hyf, hf'⟩ := hf x
      obtain ⟨hxg, hyg, hg'⟩ := hg x
      refine ⟨I.mul_mem hxf hxg, I.mul_mem hyf hyg, ?_⟩
      have h1 := map_mul θ ⟨_, hxf⟩ ⟨_, hxg⟩
      rw [hf', hg'] at h1
      exact h1
    | neg f _ hf =>
      intro x
      obtain ⟨hxf, hyf, hf'⟩ := hf x
      refine ⟨I.inv_mem hxf, I.inv_mem hyf, ?_⟩
      have h1 := map_inv θ ⟨_, hxf⟩
      rw [hf'] at h1
      exact h1
    | mul f g _ _ hf hg =>
      intro x
      obtain ⟨hxg, hyg, hg'⟩ := hg x
      obtain ⟨hxf, hyf, hf'⟩ := hf ⟨_, hxg⟩
      have e : ((θ ⟨_, hxg⟩ : ↥I) : Q) = Additive.toMul (g (Additive.ofMul ((θ x : ↥I) : Q))) :=
        congrArg Subtype.val hg'
      refine ⟨hxf, ?_, ?_⟩
      · change Additive.toMul (f (Additive.ofMul (Additive.toMul
          (g (Additive.ofMul ((θ x : ↥I) : Q)))))) ∈ I
        rw [← e]
        exact hyf
      · apply Subtype.ext
        have h1 := congrArg Subtype.val hf'
        change ((θ ⟨_, hxf⟩ : ↥I) : Q) = _
        rw [h1]
        change _ = Additive.toMul (f (Additive.ofMul (Additive.toMul
          (g (Additive.ofMul ((θ x : ↥I) : Q))))))
        rw [← e]
  let F : {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} →
      Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI) := fun θ =>
    { toFun := fun p => ⟨Additive.ofMul ((θ.1 ⟨Additive.toMul p.1, p.2⟩ : ↥I) : Q), (θ.1 _).2⟩
      map_add' := fun p p' => by
        apply Subtype.ext
        have h1 := map_mul θ.1 ⟨Additive.toMul p.1, p.2⟩ ⟨Additive.toMul p'.1, p'.2⟩
        exact congrArg (fun z : ↥I => Additive.ofMul (z : Q)) h1
      map_smul' := fun r p => by
        apply Subtype.ext
        obtain ⟨hx, hy, he⟩ := key θ.1 θ.2 r.1 r.2 ⟨Additive.toMul p.1, p.2⟩
        exact congrArg (fun z : ↥I => Additive.ofMul (z : Q)) he }
  refine Nat.card_le_card_of_injective F fun θ θ' h => Subtype.ext (MonoidHom.ext fun x => ?_)
  have h1 := congrArg (fun φ : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI) =>
    ((φ ⟨Additive.ofMul (x : Q), x.2⟩ : ↥(XMod.toSubmod hI)) : Additive Q)) h
  exact Subtype.ext (Additive.ofMul.injective h1)

theorem card_end_congr [Finite Q] {Λ : Subgroup Γ} {I J : Subgroup Q} (hI : XMod.IsInv ↥Λ I)
    (hJ : XMod.IsInv ↥Λ J) (hiso : XMod.Iso ↥Λ I J) :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI)) =
      Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hJ)) := by
  obtain ⟨e⟩ := XMod.nonempty_linearEquiv_of_iso hI hJ hiso
  exact Nat.card_congr
    { toFun := fun f => e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
      invFun := fun f => e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap
      left_inv := fun f => by ext; simp
      right_inv := fun f => by ext; simp }

theorem card_eqv_le_smul {Λ : Subgroup Γ} {I : Subgroup Q} {g : Γ}
    (hg : ∀ l ∈ Λ, g⁻¹ * l * g ∈ Λ) [Finite Q] :
    Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} ≤
      Nat.card {θ : ↥(g • I) →* ↥(g • I) // IsEqv Λ ((g • I).subtype.comp θ)} := by
  classical
  have : Finite (↥(g • I) →* ↥(g • I)) := Finite.of_injective
    (fun θ : ↥(g • I) →* ↥(g • I) => (θ : ↥(g • I) → ↥(g • I))) DFunLike.coe_injective
  have hin : ∀ y : ↥(g • I), g⁻¹ • (y : Q) ∈ I := fun y =>
    (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 y.2
  have hout : ∀ x : ↥I, g • (x : Q) ∈ g • I := fun x => Subgroup.smul_mem_pointwise_smul _ _ _ x.2
  let F : {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} →
      {θ : ↥(g • I) →* ↥(g • I) // IsEqv Λ ((g • I).subtype.comp θ)} := fun θ =>
    ⟨{ toFun := fun y => ⟨g • ((θ.1 ⟨g⁻¹ • (y : Q), hin y⟩ : ↥I) : Q), hout _⟩
       map_one' := Subtype.ext (by
         show g • ((θ.1 ⟨g⁻¹ • (1 : Q), _⟩ : ↥I) : Q) = 1
         have : (⟨g⁻¹ • (1 : Q), hin 1⟩ : ↥I) = 1 := Subtype.ext (smul_one _)
         rw [this, map_one]
         exact smul_one _)
       map_mul' := fun y y' => Subtype.ext (by
         show g • ((θ.1 ⟨g⁻¹ • ((y : Q) * y'), _⟩ : ↥I) : Q) =
           g • ((θ.1 ⟨g⁻¹ • (y : Q), _⟩ : ↥I) : Q) * g • ((θ.1 ⟨g⁻¹ • (y' : Q), _⟩ : ↥I) : Q)
         have : (⟨g⁻¹ • ((y : Q) * y'), hin (y * y')⟩ : ↥I) =
             ⟨g⁻¹ • (y : Q), hin y⟩ * ⟨g⁻¹ • (y' : Q), hin y'⟩ := Subtype.ext (smul_mul' _ _ _)
         rw [this, map_mul, Subgroup.coe_mul, smul_mul']) }, fun l y y' hyy' => by
      show g • ((θ.1 ⟨g⁻¹ • (y' : Q), _⟩ : ↥I) : Q) =
        (l : Γ) • g • ((θ.1 ⟨g⁻¹ • (y : Q), _⟩ : ↥I) : Q)
      have hl : g⁻¹ * l * g ∈ Λ := hg l l.2
      have h1 : (g⁻¹ * l * g) • (g⁻¹ • (y : Q)) = g⁻¹ • (y' : Q) := by
        rw [← hyy', smul_smul, smul_smul]
        congr 1
        group
      have h2 := θ.2 ⟨_, hl⟩ ⟨g⁻¹ • (y : Q), hin y⟩ ⟨g⁻¹ • (y' : Q), hin y'⟩ h1
      change ((θ.1 ⟨g⁻¹ • (y' : Q), _⟩ : ↥I) : Q) =
        (g⁻¹ * l * g) • ((θ.1 ⟨g⁻¹ • (y : Q), _⟩ : ↥I) : Q) at h2
      rw [h2, smul_smul, smul_smul]
      congr 1
      group⟩
  refine Nat.card_le_card_of_injective F fun θ θ' h => Subtype.ext (MonoidHom.ext fun x => ?_)
  have h1 := congrArg (fun φ : {θ : ↥(g • I) →* ↥(g • I) // IsEqv Λ ((g • I).subtype.comp θ)} =>
    ((φ.1 ⟨g • (x : Q), hout x⟩ : ↥(g • I)) : Q)) h
  have hx : (⟨g⁻¹ • (g • (x : Q)), hin ⟨g • (x : Q), hout x⟩⟩ : ↥I) = x :=
    Subtype.ext (inv_smul_smul g (x : Q))
  change g • ((θ.1 ⟨g⁻¹ • (g • (x : Q)), _⟩ : ↥I) : Q) =
    g • ((θ'.1 ⟨g⁻¹ • (g • (x : Q)), _⟩ : ↥I) : Q) at h1
  rw [hx] at h1
  exact Subtype.ext (MulAction.injective g h1)

end EndCard

section Helpers

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

private theorem le_of_forall_isIrr_le {ι : Type*} {S : ι → Subgroup Q}
    (hS : ∀ i, XMod.IsIrr A (S i))
    {X F : Subgroup Q} (hX : XMod.IsInv A X) (hXS : X ≤ ⨆ i, S i) (hF : XMod.IsInv A F)
    (h : ∀ J ≤ X, XMod.IsIrr A J → J ≤ F) : X ≤ F := by
  classical
  have hinv : ∀ i, XMod.IsInv A (S i) := fun i => (hS i).1
  set m : Submodule ↥(XMod.opRing A Q) (Additive Q) := ⨆ i, XMod.toSubmod (hinv i) with hm
  have : IsSemisimpleModule ↥(XMod.opRing A Q) ↥m := by
    have h1 := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
      (s := Set.univ) (p := fun i => XMod.toSubmod (hinv i)) (fun i _ => by
        have := (XMod.isIrr_iff (hinv i)).1 (hS i)
        infer_instance)
    have h2 : (⨆ i ∈ Set.univ, XMod.toSubmod (hinv i)) = m := by
      rw [hm]
      exact iSup_congr fun i => iSup_pos (Set.mem_univ i)
    rw [h2] at h1
    exact h1
  have hXm : XMod.toSubmod hX ≤ m := by
    rw [hm, ← XMod.toSubmod_iSup hinv]
    exact XMod.toSubmod_le_iff.2 hXS
  set N := (XMod.toSubmod hX).comap m.subtype with hN
  have key : N ≤ (XMod.toSubmod hF).comap m.subtype := by
    rw [← IsSemisimpleModule.sSup_simples_le N]
    refine sSup_le ?_
    rintro n ⟨hns, hnN⟩
    set s := n.map m.subtype with hs
    have hss : IsSimpleModule ↥(XMod.opRing A Q) ↥s :=
      IsSimpleModule.congr (M := ↥s) (N := ↥n)
        (Submodule.equivMapOfInjective m.subtype m.injective_subtype n).symm
    have hJinv := XMod.isInv_ofSubmod s
    have hJs : XMod.toSubmod hJinv = s := Submodule.ext fun _ => Iff.rfl
    have hJirr : XMod.IsIrr A (XMod.ofSubmod s) := (XMod.isIrr_iff hJinv).2 (by rw [hJs]; exact hss)
    have hJX : XMod.ofSubmod s ≤ X := by
      intro q hq
      have hq' : Additive.ofMul q ∈ s := hq
      obtain ⟨y, hy, hyq⟩ := Submodule.mem_map.1 hq'
      have h1 : y ∈ N := hnN hy
      rw [hN, Submodule.mem_comap] at h1
      have h2 : Additive.ofMul q ∈ XMod.toSubmod hX := by rw [← hyq]; exact h1
      exact h2
    have hJF := h _ hJX hJirr
    intro y hy
    rw [Submodule.mem_comap]
    have h3 : m.subtype y ∈ s := Submodule.mem_map_of_mem hy
    exact hJF h3
  intro x hx
  have hxm : Additive.ofMul x ∈ m := hXm hx
  have h4 : (⟨Additive.ofMul x, hxm⟩ : ↥m) ∈ N := by
    rw [hN, Submodule.mem_comap]
    exact hx
  exact key h4

end Helpers

section Helpers2

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem fixed_sup (P P' : Subgroup Γ) :
    XMod.fixed ↥(P ⊔ P') (⊤ : Subgroup Q) =
      XMod.fixed ↥P (⊤ : Subgroup Q) ⊓ XMod.fixed ↥P' (⊤ : Subgroup Q) := by
  ext q
  constructor
  · intro hq
    exact ⟨⟨trivial, fun x => hq.2 ⟨x, le_sup_left (α := Subgroup Γ) x.2⟩⟩,
      ⟨trivial, fun x => hq.2 ⟨x, le_sup_right (α := Subgroup Γ) x.2⟩⟩⟩
  · rintro ⟨h1, h2⟩
    have hle : P ⊔ P' ≤ MulAction.stabilizer Γ q :=
      sup_le (fun x hx => h1.2 ⟨x, hx⟩) (fun x hx => h2.2 ⟨x, hx⟩)
    exact ⟨trivial, fun x => hle x.2⟩

theorem eq_one_of_pow_of_mem_range {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    {p : ℕ} (hp : p.Prime) (hG : ∀ g : G, ∀ k : ℕ, g ^ (p ^ k) = 1 → g = 1) :
    ∀ h ∈ f.range, ∀ k : ℕ, h ^ (p ^ k) = 1 → h = 1 := by
  intro h hh k
  induction k generalizing h with
  | zero => intro hk; simpa using hk
  | succ k ih =>
    intro hk
    obtain ⟨g, rfl⟩ := hh
    have h1 : (f g ^ (p ^ k)) ^ p = 1 := by rw [← pow_mul, ← pow_succ]; exact hk
    obtain ⟨c, m, hcm, hfc⟩ := exists_pElement_lift f hp (g := g ^ (p ^ k)) (map_pow f g _) h1
    have h2 := hG _ m hcm
    have h3 : f g ^ (p ^ k) = 1 := by rw [← hfc, h2, map_one]
    exact ih (f g) ⟨g, rfl⟩ h3

theorem commute_of_comm_fix {K : Subgroup Γ} (hK : CFSG.IsQuasisimple ↥K) {S : Subgroup Q}
    (hKS : ∀ k ∈ K, ∀ s ∈ S, k • s ∈ S) (hnt : ∃ k ∈ K, ∃ s ∈ S, k • s ≠ s) {a : Γ}
    (haK : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hfix : ∀ k ∈ K, ∀ s ∈ S, ⁅a, k⁆ • s = s) :
    ∀ k ∈ K, a * k = k * a := by
  have hperf : ⁅K, K⁆ = K := by
    have : Group.IsPerfect ↥K := hK.1
    exact Subgroup.commutator_eq_self
  set Z := K ⊓ fixingSubgroup Γ (S : Set Q) with hZ
  have hN : (Z.subgroupOf K).Normal := by
    refine ⟨fun z hz k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    refine ⟨K.mul_mem (K.mul_mem k.2 hz.1) (K.inv_mem k.2), (mem_fixingSubgroup_iff Γ).2 ?_⟩
    intro s hs
    have h1 : (k : Γ)⁻¹ • s ∈ S := hKS _ (K.inv_mem k.2) s hs
    have h2 := (mem_fixingSubgroup_iff Γ).1 hz.2 _ h1
    show ((k : Γ) * z * (k : Γ)⁻¹) • s = s
    rw [mul_smul, mul_smul, h2, smul_inv_smul]
  have hZc : ∀ z ∈ Z, ∀ l ∈ K, z * l = l * z := by
    intro z hz l hl
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hN with h | h
    · exfalso
      obtain ⟨k, hk, s, hs, hks⟩ := hnt
      have : (⟨k, hk⟩ : ↥K) ∈ Z.subgroupOf K := by rw [h]; trivial
      exact hks ((mem_fixingSubgroup_iff Γ).1 (Subgroup.mem_subgroupOf.1 this).2 s hs)
    · have := Subgroup.mem_center_iff.1 (h (show (⟨z, hz.1⟩ : ↥K) ∈ Z.subgroupOf K from hz))
        ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm
  refine B5.commute_of_comm_central hperf haK hZc fun l hl => ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact K.mul_mem (haK l hl) (K.inv_mem hl)
  · exact (mem_fixingSubgroup_iff Γ).2 (hfix l hl)

private theorem isQuotientOfSQTKTC_of_surjective {X Y : Type*} [Group X] [Group Y]
    (hX : IsQuotientOfSQTKTC X) (f : X →* Y) (hf : Function.Surjective f) :
    IsQuotientOfSQTKTC Y := by
  obtain ⟨S, _, _, h1, h2, φ, hφ⟩ := hX
  exact ⟨S, inferInstance, inferInstance, h1, h2, f.comp φ, hf.comp hφ⟩

end Helpers2

namespace D321Sit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

private noncomputable def secIso (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    ↥L ≃* ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
  have : IsSimpleGroup ↥L := hS.hsimp
  have hN : D36Norm M Mp T L V t := ⟨hS.hD, hlt, hS.htT, hS.htn, hS.hMp, hVt⟩
  (autSubEquivOfFaithful (insp5a_le_stabSub hN.std.hyp) (d36t_faithful_V hN)).trans
    (B5.secEquiv (autSub L V) (InternalSec.le_stabSub_top _) (d36t_qsec hL38 hN).stabKC
      (d36t_qsec hL38 hN).faithful)

theorem cls2F_sec
    (hA21 : AsA21SQTKSection) (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ)) {n : ℕ} (hSz : IsSz n ↥L) :
    SmithD37.endCard (autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) = 2 ^ n ∧
      Nat.card (Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V)) = 2 ^ (4 * n) := by
  classical
  have : IsSimpleGroup ↥L := hS.hsimp
  have hN : D36Norm M Mp T L V t := ⟨hS.hD, hlt, hS.htT, hS.htn, hS.hMp, hVt⟩
  set C₀ := (V ⊓ fixV Mp).subgroupOf V with hC₀
  have hQs := d36t_qsec hL38 hN
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hS.exp])
  have hb4 := hQs.b4Hyp hexp (d36t_sqtk hA21 hN)
  have hexpS := sec_sq_eq_one_d36t hexp (⊤ : Subgroup ↥V) C₀
  have hq : qhatOf (autSec (autSub (Mp ⊔ T) V) ⊤ C₀) ≤ ((2 : ℚ) : WithTop ℚ) :=
    (hQs.qhatOf_autSec_le hexp).trans hqV
  obtain ⟨E, hEA2, hEc, hEr⟩ := kq_le_iff.1 hq
  have hEp : IsPGroup 2 ↥E := hEA2.isElemAbelian2.isPGroup
  have hErk : 0 < rk ↥E := by
    rcases Nat.eq_zero_or_pos (rk ↥E) with h | h
    · exact absurd ((rk_eq_zero_iff_of_isPGroup hEp).1 h) hEA2.ne_bot
    · exact h
  have hidx : rkIdx (fixV E) ≤ 2 * rk ↥E := by
    have hEq : (0 : ℚ) < (rk ↥E : ℚ) := by exact_mod_cast hErk
    have h1 : (rkIdx (fixV E) : ℚ) / (rk ↥E : ℚ) ≤ 2 := hEr
    rw [div_le_iff₀ hEq] at h1
    exact_mod_cast h1
  have hoff : Nat.card (Sec (⊤ : Subgroup ↥V) C₀) ≤ Nat.card ↥E ^ 2 * Nat.card ↥(fixV E) := by
    have hcS : Nat.card (Sec (⊤ : Subgroup ↥V) C₀) = 2 ^ rk (Sec (⊤ : Subgroup ↥V) C₀) := by
      rw [← Subgroup.card_top, card_eq_two_pow hexpS ⊤, rk_top]
    rw [hcS, card_eq_two_pow_of_isPGroup hEp, card_eq_two_pow hexpS (fixV E), ← pow_mul,
      ← pow_add]
    have h1 := rk_add_rkIdx (fixV E)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA38 : A38Types ↥(autSec (autSub L V) ⊤ C₀) := by
    obtain ⟨h2, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hSz
    exact Or.inr (Or.inl ⟨n, h2, a, ha, K, inferInstance, inferInstance, hn, hK,
      ⟨(secIso hL38 hS hlt hVt).symm.trans e⟩⟩)
  have hSz' : IsSz n ↥(autSec (autSub L V) ⊤ C₀) := by
    obtain ⟨h2, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hSz
    exact ⟨h2, a, ha, K, inferInstance, inferInstance, hn, hK,
      ⟨(secIso hL38 hS hlt hVt).symm.trans e⟩⟩
  have hcls : SmithD37.Cls2F (autSec (autSub (Mp ⊔ T) V) ⊤ C₀) (autSec (autSub L V) ⊤ C₀) E :=
    ⟨hexpS, hb4, hA38, hEA2, hEc, hoff⟩
  obtain ⟨hend, hcard, -, -⟩ := SmithD37.cls2F_sz hcls hSz'
  exact ⟨hend, hcard⟩

private theorem secIso_mk (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (l : ↥L) (v : ↥V)
    (hlv : (l : MulAut W) (v : W) ∈ V) :
    ((secIso hL38 hS hlt hVt l : ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V))) :
        MulAut (Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V)))
      (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩) =
        QuotientGroup.mk ⟨⟨(l : MulAut W) v, hlv⟩, Subgroup.mem_top _⟩ :=
  rfl

theorem card_tildeV
    (hA21 : AsA21SQTKSection) (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ)) {n : ℕ} (hSz : IsSz n ↥L) :
    letI := qAct hS.hD.hyp.Mp_normal
    Nat.card ↥(tilde Mp ⊤ V) = 2 ^ (4 * n) ∧
      Nat.card {θ : ↥(tilde Mp ⊤ V) →* ↥(tilde Mp ⊤ V) //
        IsEqv (Mp.subgroupOf M) ((tilde Mp ⊤ V).subtype.comp θ)} = 2 ^ n := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨hend, hcard⟩ := hS.cls2F_sec hA21 hL38 hlt hVt hqV hSz
  set C₀ := (V ⊓ fixV Mp).subgroupOf V with hC₀
  set Vt := tilde Mp ⊤ V with hVtdef
  have hC₀map : C₀.map (Subgroup.topEquiv (G := ↥V)).symm.toMonoidHom =
      C₀.subgroupOf (⊤ : Subgroup ↥V) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(x : ↥V), hx, rfl⟩
  let ψ : ↥Vt ≃* Sec (⊤ : Subgroup ↥V) C₀ :=
    (tildeEquiv (Mp := Mp) V).trans
      (QuotientGroup.congr C₀ (C₀.subgroupOf ⊤) Subgroup.topEquiv.symm hC₀map)
  have hψ : ∀ v : ↥V, ψ ⟨QuotientGroup.mk (v : W), ⟨v, v.2, rfl⟩⟩ =
      QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩ := by
    intro v
    show QuotientGroup.congr C₀ (C₀.subgroupOf ⊤) Subgroup.topEquiv.symm hC₀map
      (tildeEquiv (Mp := Mp) V ⟨QuotientGroup.mk (v : W), ⟨v, v.2, rfl⟩⟩) = _
    rw [tildeEquiv_mk]
    rfl
  have hψ' : ∀ (w : W) (hw : w ∈ V) (hq : QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) w ∈ Vt),
      ψ ⟨QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) w, hq⟩ =
        QuotientGroup.mk ⟨⟨w, hw⟩, Subgroup.mem_top _⟩ := fun w hw _ => hψ ⟨w, hw⟩
  refine ⟨by rw [Nat.card_congr ψ.toEquiv, hcard], ?_⟩
  rw [← hend]
  have hLV : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V := fun l hl v hv => hS.Mp_inv_V l (hS.L_le_Mp hl) v hv
  have hLVt : ∀ (l : ↥L) (q : ↥Vt), (⟨(l : MulAut W), hS.L_le l.2⟩ : ↥M) •
      ((q : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) ∈ Vt := by
    rintro l ⟨_, w, hw, rfl⟩
    exact ⟨(l : MulAut W) w, hLV l l.2 w hw, rfl⟩
  have hint : ∀ (l : ↥L) (q : ↥Vt), ψ ⟨(⟨(l : MulAut W), hS.L_le l.2⟩ : ↥M) •
      ((q : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)), hLVt l q⟩ =
      ((secIso hL38 hS hlt hVt l : ↥(autSec (autSub L V) ⊤ C₀)) :
        MulAut (Sec (⊤ : Subgroup ↥V) C₀)) (ψ q) := by
    rintro l ⟨_, w, hw, rfl⟩
    refine (hψ' ((l : MulAut W) w) (hLV l l.2 w hw) _).trans
      ((secIso_mk hL38 hS hlt hVt l ⟨w, hw⟩ (hLV l l.2 w hw)).symm.trans ?_)
    exact congrArg _ (hψ' w hw _).symm
  have hint' : ∀ (l : ↥L) (s : Sec (⊤ : Subgroup ↥V) C₀),
      (((ψ.symm (((secIso hL38 hS hlt hVt l : ↥(autSec (autSub L V) ⊤ C₀)) :
        MulAut (Sec (⊤ : Subgroup ↥V) C₀)) s)) : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
        (⟨(l : MulAut W), hS.L_le l.2⟩ : ↥M) •
          ((ψ.symm s : ↥Vt) : W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    intro l s
    have h1 := hint l (ψ.symm s)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, MulEquiv.symm_apply_apply]
  have hLt : ∀ x : ↥M, (x : MulAut W) ∈ conjAutSub t L → ∀ q ∈ Vt, x • q = q := by
    intro x hx q hq
    exact (XMod.mem_fixed.1 (hS.tildeU_le_fixed hVt (hS.tildeV_le_tildeU hVt hq))).2 ⟨x, hx⟩
  have hΛ : ∀ lam : ↥(Mp.subgroupOf M), ∃ a : ↥L, ∀ q ∈ Vt,
      (lam : ↥M) • q = (⟨(a : MulAut W), hS.L_le a.2⟩ : ↥M) • q := by
    intro lam
    obtain ⟨a, ha, b, hb, hab⟩ := hS.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 lam.2)
    refine ⟨⟨a, ha⟩, fun q hq => ?_⟩
    have hbM : b ∈ M := hS.Lt_le hb
    have h1 : (lam : ↥M) = ⟨a, hS.L_le ha⟩ * ⟨b, hbM⟩ := Subtype.ext hab
    rw [h1, mul_smul, hLt ⟨b, hbM⟩ hb q hq]
  have hLmem : ∀ a : ↥L, (⟨(a : MulAut W), hS.L_le a.2⟩ : ↥M) ∈ Mp.subgroupOf M :=
    fun a => Subgroup.mem_subgroupOf.2 (hS.L_le_Mp a.2)
  refine Nat.card_congr
    { toFun := fun θ => ⟨(ψ.toMonoidHom.comp θ.1).comp ψ.symm.toMonoidHom, ?_⟩
      invFun := fun φ => ⟨(ψ.symm.toMonoidHom.comp φ.1).comp ψ.toMonoidHom, ?_⟩
      left_inv := fun θ => Subtype.ext (MonoidHom.ext fun q => by simp)
      right_inv := fun φ => Subtype.ext (MonoidHom.ext fun s => by simp) }
  · intro l' hl' s
    obtain ⟨l, hl⟩ := (secIso hL38 hS hlt hVt).surjective ⟨l', hl'⟩
    have hl'' : l' = ((secIso hL38 hS hlt hVt l : ↥(autSec (autSub L V) ⊤ C₀)) :
        MulAut (Sec (⊤ : Subgroup ↥V) C₀)) := by rw [hl]
    rw [hl'']
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    have h1 := θ.2 ⟨_, hLmem l⟩ (ψ.symm s) ⟨_, hLVt l (ψ.symm s)⟩ rfl
    have h2 : ψ.symm ((secIso hL38 hS hlt hVt l : MulAut _) s) = ⟨_, hLVt l (ψ.symm s)⟩ :=
      Subtype.ext (hint' l s)
    rw [h2]
    have h3 : θ.1 ⟨_, hLVt l (ψ.symm s)⟩ = ⟨_, hLVt l (θ.1 (ψ.symm s))⟩ := Subtype.ext h1
    rw [h3, hint]
  · intro lam v w hvw
    obtain ⟨a, ha⟩ := hΛ lam
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      Subgroup.coe_subtype]
    have hw : w = ⟨_, hLVt a v⟩ := Subtype.ext (by rw [← hvw, ha _ v.2])
    rw [hw, hint, φ.2 _ (secIso hL38 hS hlt hVt a).2, hint', ← ha _ (ψ.symm _).2]

theorem card_end_of_isIrr
    (hA21 : AsA21SQTKSection) (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ)) {n : ℕ} (hSz : IsSz n ↥L)
    {J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hJ : letI := qAct hS.hD.hyp.Mp_normal; XMod.IsIrr ↥(Mp.subgroupOf M) J) :
    letI := qAct hS.hD.hyp.Mp_normal
    Nat.card (Module.End ↥(XMod.opRing ↥(Mp.subgroupOf M) (W ⧸ modFix Mp (⊤ : Subgroup W)))
        ↥(XMod.toSubmod hJ.1)) = 2 ^ n ∧ Nat.card ↥J = 2 ^ (4 * n) := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨hcV, heV⟩ := hS.card_tildeV hA21 hL38 hlt hVt hqV hSz
  have hN := normalizes_whole (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (Mp.subgroupOf M)
    hS.Λ_normal
  have hirrg : ∀ g : ↥M, XMod.IsIrr ↥(Mp.subgroupOf M) (g • tilde Mp ⊤ V) :=
    fun g => isIrr_smul hN g hS.irr
  have hJle : J ≤ ⨆ g : ↥M, g • tilde Mp ⊤ V := by
    rw [hS.gen]
    exact le_top
  obtain ⟨g, hiso⟩ := exists_iso_of_le_iSup hirrg hJ hJle
  have hconj : ∀ l ∈ Mp.subgroupOf M, g⁻¹ * l * g ∈ Mp.subgroupOf M := fun l hl => by
    have := hS.Λ_normal g⁻¹ l hl
    rwa [inv_inv] at this
  have hconj' : ∀ l ∈ Mp.subgroupOf M, g⁻¹⁻¹ * l * g⁻¹ ∈ Mp.subgroupOf M := fun l hl => by
    rw [inv_inv]
    exact hS.Λ_normal g l hl
  have h1 := card_eqv_le_smul (Λ := Mp.subgroupOf M) (I := tilde Mp ⊤ V) hconj
  have h2 := card_eqv_le_smul (Λ := Mp.subgroupOf M) (I := g • tilde Mp ⊤ V) hconj'
  rw [smul_smul, inv_mul_cancel, one_smul] at h2
  refine ⟨?_, ?_⟩
  · rw [card_end_congr hJ.1 (hirrg g).1 hiso, card_end_eq, ← heV]
    exact le_antisymm h2 h1
  · obtain ⟨φ, -⟩ := hiso
    rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr (XMod.smulEquiv g (tilde Mp ⊤ V)).toEquiv, hcV]

theorem le_centralizer_of_quasi
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hL38 : D3L38) (hS : D321Sit M Mp T L V t A r)
    (hlt : V < orbSup T V) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ)) {n : ℕ} (hSz : IsSz n ↥L)
    (hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)))
    {K₀ : Subgroup (MulAut W)} (hKq : CFSG.IsQuasisimple ↥K₀)
    (hKC : K₀ ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hAK : ∀ a ∈ A, ∀ k ∈ K₀, a * k * a⁻¹ ∈ K₀) :
    A ≤ Subgroup.centralizer (K₀ : Set (MulAut W)) := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  by_contra hcon
  set B₁ := A ⊓ Subgroup.centralizer (K₀ : Set (MulAut W)) with hB₁def
  have hKM : K₀ ≤ M := hKC.trans inf_le_left
  have hAM : A ≤ M := hS.A_le
  have hB₁A : B₁ ≤ A := inf_le_left
  have hB₁M : B₁ ≤ M := hB₁A.trans hAM
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hS.elemAb.1
  have hAp : IsPGroup 2 ↥A := hS.isPGroup
  have hB₁p : IsPGroup 2 ↥B₁ := hAp.to_le hB₁A
  have hKMp : ∀ k ∈ K₀, ∀ x ∈ Mp, k * x = x * k := fun k hk x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hKC hk).2) x hx).symm
  have hAMp : ∀ a ∈ A, ∀ x ∈ Mp, a * x = x * a := fun a ha x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hAC ha)) x hx).symm
  have hB₁K : ∀ b ∈ B₁, ∀ k ∈ K₀, b * k = k * b := fun b hb k hk =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) k hk).symm
  set S₀ := XMod.fixed ↥(B₁.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    with hS₀
  have hKS₀ : ∃ k, ∃ hk : k ∈ K₀, ∃ q ∈ S₀, (⟨k, hKM hk⟩ : ↥M) • q ≠ q := by
    by_contra h
    push Not at h
    apply not_isPGroup_two_of_isQuasisimple hKq
    intro x
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hxa : (x : MulAut W) ^ (2 ^ a) ∈ K₀ := K₀.pow_mem x.2 _
    have hy1 : (x : MulAut W) ^ (2 ^ a) = 1 := by
      refine SmithD39Two.eq_one_of_fix_fixed hS.hD.hyp.Mp_normal hS.exp hS.commV_eq_top hB₁M hB₁p
        (hKM hxa) (hKMp _ hxa) hm ?_ (fun e he => (hB₁K e he _ hxa).symm) (h _ hxa)
      rw [← pow_mul, ← hord, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow]; exact hy1)⟩
  have hN := normalizes_whole (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (Mp.subgroupOf M)
    hS.Λ_normal
  have hirrg : ∀ g : ↥M, XMod.IsIrr ↥(Mp.subgroupOf M) (g • tilde Mp ⊤ V) :=
    fun g => isIrr_smul hN g hS.irr
  have hcen : ∀ (P : Subgroup (MulAut W)), (∀ x ∈ P, ∀ y ∈ Mp, x * y = y * x) →
      ∀ g ∈ P.subgroupOf M, ∀ l ∈ Mp.subgroupOf M, l * g = g * l :=
    fun P hP g hg l hl => Subtype.ext (hP _ hg _ hl).symm
  have hB₁c := hcen B₁ fun x hx y hy => hAMp x (hB₁A hx) y hy
  have hAc' := hcen A hAMp
  have hKc' := hcen K₀ hKMp
  have hS₀inv : XMod.IsInv ↥(Mp.subgroupOf M) S₀ :=
    SmithD310U.isInv_fixed_of_comm fun b hb l hl => (hB₁c b hb l hl).symm
  obtain ⟨J, hJS₀, hJ, k₀, hk₀, q₀, hq₀, hkq₀⟩ : ∃ J ≤ S₀, XMod.IsIrr ↥(Mp.subgroupOf M) J ∧
      ∃ k, ∃ hk : k ∈ K₀, ∃ q ∈ J, (⟨k, hKM hk⟩ : ↥M) • q ≠ q := by
    by_contra h
    push Not at h
    obtain ⟨k, hk, q, hq, hkq⟩ := hKS₀
    set kM : ↥M := ⟨k, hKM hk⟩ with hkM
    have hFinv : XMod.IsInv ↥(Mp.subgroupOf M)
        (XMod.fixed ↥(Subgroup.zpowers kM) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))) := by
      refine SmithD310U.isInv_fixed_of_comm fun e he l hl => ?_
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact (Commute.zpow_left (hKc' kM hk l hl).symm z)
    have hle := le_of_forall_isIrr_le hirrg hS₀inv (by rw [hS.gen]; exact le_top) hFinv
      (fun J' hJ' hJ'irr p hp => SmithD39Two.mem_fixed_zpowers_iff.2 (h J' hJ' hJ'irr k hk p hp))
    exact hkq (SmithD39Two.mem_fixed_zpowers_iff.1 (hle hq))
  obtain ⟨hJend, hJcard⟩ := hS.card_end_of_isIrr hA21 hL38 hlt hVt hqV hSz hJ
  have hd : Nat.card ↥J = Nat.card (Module.End ↥(XMod.opRing ↥(Mp.subgroupOf M)
      (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod hJ.1)) ^ 4 := by
    rw [hJend, hJcard, ← pow_mul, mul_comm]
  obtain ⟨X₁, hX₁Y, hX₁inv, hX₁cnt, hX₁φ⟩ := exists_mult_sub hJ hd
  set Y := isoComp ↥(Mp.subgroupOf M) J with hY
  set S := X₁ ⊓ S₀ with hSdef
  have hfixA : XMod.fixed ↥(A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤ S₀ :=
    SmithD39Two.fixed_anti fun x hx => Subgroup.mem_subgroupOf.2 (hB₁A hx)
  have hrk4 : ∀ (P : Subgroup ↥M), (∀ g ∈ P, ∀ l ∈ Mp.subgroupOf M, l * g = g * l) →
      rk ↥(Y ⊓ XMod.fixed ↥P (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))) =
        4 * rk ↥(X₁ ⊓ XMod.fixed ↥P (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))) := by
    intro P hP
    unfold rk
    rw [hX₁cnt P hP, padicValNat.pow]
  have hr1 : rk ↥(Y ⊓ S₀) = 4 * rk ↥S := hrk4 _ hB₁c
  have hr2 := hrk4 _ hAc'
  have hSA : S ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤ = X₁ ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤ := by
    rw [hSdef, inf_assoc, inf_eq_right.2 hfixA]
  have hYA : (Y ⊓ S₀) ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤ = Y ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤ := by
    rw [inf_assoc, inf_eq_right.2 hfixA]
  have hnS : 4 * nB (A.subgroupOf M) S = nB (A.subgroupOf M) (Y ⊓ S₀) := by
    have h1 : rk ↥(X₁ ⊓ XMod.fixed ↥(A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp ⊤))) ≤
        rk ↥S := rk_mono (inf_le_inf_left _ hfixA)
    unfold nB
    rw [hSA, hYA, hr1, hr2]
    omega
  have hmono : nB (A.subgroupOf M) (Y ⊓ S₀) ≤ nB (A.subgroupOf M) S₀ := nB_mono _ inf_le_right
  have hKB₁c : ∀ g ∈ K₀.subgroupOf M ⊔ B₁.subgroupOf M, ∀ l ∈ Mp.subgroupOf M,
      l * g = g * l := by
    intro g hg l hl
    have hle : K₀.subgroupOf M ⊔ B₁.subgroupOf M ≤ Subgroup.centralizer {l} := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hKc' x hx l hl).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hB₁c x hx l hl).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hKS : ∃ k, ∃ hk : k ∈ K₀, ∃ s ∈ S, (⟨k, hKM hk⟩ : ↥M) • s ≠ s := by
    by_contra h
    push Not at h
    have h1 : X₁ ⊓ XMod.fixed ↥(K₀.subgroupOf M ⊔ B₁.subgroupOf M) ⊤ = X₁ ⊓ S₀ := by
      rw [fixed_sup]
      ext q
      constructor
      · rintro ⟨hq, -, hq'⟩
        exact ⟨hq, hq'⟩
      · rintro ⟨hq, hq'⟩
        refine ⟨hq, ⟨trivial, fun k => ?_⟩, hq'⟩
        exact h _ k.2 q ⟨hq, hq'⟩
    have h2 : Y ⊓ XMod.fixed ↥(K₀.subgroupOf M ⊔ B₁.subgroupOf M) ⊤ = Y ⊓ S₀ := by
      have hle : Y ⊓ XMod.fixed ↥(K₀.subgroupOf M ⊔ B₁.subgroupOf M) ⊤ ≤ Y ⊓ S₀ :=
        inf_le_inf_left _ (SmithD39Two.fixed_anti le_sup_right)
      refine le_antisymm hle (Subgroup.eq_of_le_of_card_ge hle ?_).ge
      rw [hX₁cnt _ hKB₁c, hX₁cnt _ hB₁c, h1]
    have hq₀Y : q₀ ∈ Y ⊓ S₀ := ⟨le_isoComp hJ (XMod.Iso.refl J) hq₀, hJS₀ hq₀⟩
    rw [← h2, fixed_sup] at hq₀Y
    exact hkq₀ (hq₀Y.2.1.2 ⟨⟨k₀, hKM hk₀⟩, hk₀⟩)
  have hS₀g : ∀ g : ↥M, (∀ b ∈ B₁, (g : MulAut W) * b = b * g) → ∀ s ∈ S₀, g • s ∈ S₀ := by
    intro g hg s hs
    refine ⟨trivial, fun b => ?_⟩
    have hbg : (b : ↥M) * g = g * (b : ↥M) :=
      Subtype.ext (hg _ (Subgroup.mem_subgroupOf.1 b.2)).symm
    show (b : ↥M) • g • s = g • s
    rw [smul_smul, hbg, mul_smul]
    exact congrArg (g • ·) ((XMod.mem_fixed.1 hs).2 b)
  have hSK : ∀ k ∈ K₀.subgroupOf M, ∀ s ∈ S, k • s ∈ S := fun k hk s hs =>
    ⟨hX₁inv k (hKc' k hk) s hs.1, hS₀g k (fun b hb => (hB₁K b hb _ hk).symm) s hs.2⟩
  have hSA : ∀ a ∈ A.subgroupOf M, ∀ s ∈ S, a • s ∈ S := fun a ha s hs =>
    ⟨hX₁inv a (hAc' a ha) s hs.1, hS₀g a (fun b hb => hAc _ ha _ (hB₁A hb)) s hs.2⟩
  have hK'q : CFSG.IsQuasisimple ↥(K₀.subgroupOf M) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKM).symm hKq
  have hntS : ∃ k ∈ K₀.subgroupOf M, ∃ s ∈ S, k • s ≠ s := by
    obtain ⟨k, hk, s, hs, hks⟩ := hKS
    exact ⟨⟨k, hKM hk⟩, hk, s, hs, hks⟩
  have hAK' : ∀ a ∈ A.subgroupOf M, ∀ k ∈ K₀.subgroupOf M, a * k * a⁻¹ ∈ K₀.subgroupOf M :=
    fun a ha k hk => hAK _ ha _ hk
  have htrick : ∀ a ∈ A.subgroupOf M, (∀ k ∈ K₀.subgroupOf M, ∀ s ∈ S, ⁅a, k⁆ • s = s) →
      (a : MulAut W) ∈ B₁ := by
    intro a ha hfix
    have h1 := commute_of_comm_fix hK'q hSK hntS (hAK' a ha) hfix
    refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    exact (congrArg Subtype.val (h1 ⟨k, hKM hk⟩ hk)).symm
  have hfixS : ∀ a ∈ A.subgroupOf M, (∀ s ∈ S, a • s = s) → (a : MulAut W) ∈ B₁ := by
    intro a ha hfix
    refine htrick a ha fun k hk s hs => ?_
    have hk' : k⁻¹ • s ∈ S := hSK _ ((K₀.subgroupOf M).inv_mem hk) s hs
    have h1 : a⁻¹ • (k⁻¹ • s) = k⁻¹ • s := by
      rw [inv_smul_eq_iff]
      exact (hfix _ hk').symm
    rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, h1, smul_inv_smul, hfix s hs]
  have hAnot : ¬ ∀ a ∈ A.subgroupOf M, ∀ s ∈ S, a • s = s := by
    intro h
    apply hcon
    intro a ha
    exact (hfixS ⟨a, hAM ha⟩ ha (h _ ha)).2
  have hS₀top : B₁ = ⊥ → S₀ = ⊤ := by
    intro hB₁0
    rw [eq_top_iff]
    intro q _
    refine ⟨trivial, fun b => ?_⟩
    have key : ∀ x : MulAut W, x ∈ B₁ → x = 1 := fun x hx => by
      rw [hB₁0, Subgroup.mem_bot] at hx
      exact hx
    have : (b : ↥M) = 1 := Subtype.ext (key _ (Subgroup.mem_subgroupOf.1 b.2))
    show (b : ↥M) • q = q
    rw [this, one_smul]
  have hD7 : 4 * nB (A.subgroupOf M) S ≤ 2 * (rk ↥A - rk ↥B₁) ∧
      (B₁ ≠ ⊥ → 4 * nB (A.subgroupOf M) S < 2 * (rk ↥A - rk ↥B₁)) := by
    by_cases hB₁0 : B₁ = ⊥
    · have h1 := hS.nB_le
      rw [← hS₀top hB₁0] at h1
      have h2 : rk ↥B₁ = 0 := by rw [hB₁0, rk_bot]
      exact ⟨by omega, fun h => absurd hB₁0 h⟩
    · by_cases hUA : fixV B₁ ≤ fixV A
      · exfalso
        apply hAnot
        intro a ha s hs
        have hs₀ : s ∈ S₀ := hs.2
        rw [hS₀, ← SmithD39Two.map_fixV_eq_fixed hS.hD.hyp.Mp_normal hB₁M
          (fun b hb x hx => hAMp b (hB₁A hb) x hx) hS.commOf_eq] at hs₀
        obtain ⟨w, hw, rfl⟩ := hs₀
        show QuotientGroup.mk ((a : MulAut W) w) = QuotientGroup.mk w
        exact congrArg QuotientGroup.mk ((mem_fixV.1 (hUA hw)) _ ha)
      · have h1 := SmithD39Two.nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ hB₁A hB₁0 hUA hB₁M
          (fun b hb x hx => hAMp b (hB₁A hb) x hx) hS.commOf_eq
        rw [← hS₀] at h1
        exact ⟨by omega, fun _ => by omega⟩
  set ρK := resJ (K₀.subgroupOf M) S hSK with hρK
  set ρA := resJ (A.subgroupOf M) S hSA with hρA
  have hSH : ∀ h ∈ (K₀ ⊔ A).subgroupOf M, ∀ s ∈ S, h • s ∈ S := by
    intro h hh s hs
    rw [Subgroup.subgroupOf_sup hKM hAM] at hh
    exact smul_mem_of_mem_sup hSK hSA hh s hs
  set ρH := resJ ((K₀ ⊔ A).subgroupOf M) S hSH with hρH
  have hQS : ∀ q : ↥S, q ^ 2 = 1 := fun q => Subtype.ext (by simpa using hS.quot_sq q)
  have hrangeH : IsQuotientOfSQTKTC ↥ρH.range :=
    isQuotientOfSQTKTC_of_surjective
      (SmithD39Two.isQuotientOfSQTKTC_subgroup hS.hD.hyp.qsqtk ((K₀ ⊔ A).subgroupOf M))
      ρH.rangeRestrict ρH.rangeRestrict_surjective
  have hKAle : ρK.range ⊔ ρA.range ≤ ρH.range :=
    sup_le (range_resJ_mono fun x hx => Subgroup.mem_subgroupOf.2
        ((le_sup_left : K₀ ≤ K₀ ⊔ A) (Subgroup.mem_subgroupOf.1 hx)))
      (range_resJ_mono fun x hx => Subgroup.mem_subgroupOf.2
        ((le_sup_right : A ≤ K₀ ⊔ A) (Subgroup.mem_subgroupOf.1 hx)))
  have hH : IsQuotientOfSQTKTC ↥(ρK.range ⊔ ρA.range) :=
    SmithD39Two.isQuotientOfSQTKTC_of_le hrangeH hKAle
  have hKbar : CFSG.IsQuasisimple ↥ρK.range := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hK'q ρK.rangeRestrict_surjective ?_
    obtain ⟨k, hk, s, hs, hks⟩ := hntS
    refine ⟨⟨k, hk⟩, fun h1 => hks ?_⟩
    have := congrArg (fun φ : ↥ρK.range =>
      (((φ : MulAut ↥S) ⟨s, hs⟩ : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W))) h1
    exact this
  have hAKbar : ∀ a ∈ ρA.range, ∀ k ∈ ρK.range, a * k * a⁻¹ ∈ ρK.range := by
    rintro _ ⟨a, rfl⟩ _ ⟨k, rfl⟩
    refine ⟨⟨(a : ↥M) * k * (a : ↥M)⁻¹, hAK' _ a.2 _ k.2⟩, ?_⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ((a : ↥M) * k * (a : ↥M)⁻¹) • (x : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      (((ρA a * ρK k * (ρA a)⁻¹) x : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W))
    rw [MulAut.mul_apply, MulAut.mul_apply, resJ_apply, resJ_apply, mul_smul, mul_smul]
    congr 2
  have hAebar : IsElemAbelian2 ρA.range :=
    isElemAbelian2_range_resJ (fun a ha b hb => Subtype.ext (hAc _ ha _ hb))
      (fun a ha => Subtype.ext (by simpa using hS.elemAb.2 _ ha)) hSA
  have hA1bar : ρA.range ≠ ⊥ := by
    intro h
    apply hAnot
    intro a ha s hs
    have h1 : ρA ⟨a, ha⟩ = 1 := by
      have hmem : ρA ⟨a, ha⟩ ∈ ρA.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    exact congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W))) h1
  have hAfbar : ρA.range ⊓ Subgroup.centralizer (ρK.range : Set (MulAut ↥S)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hac⟩
    have hB : ((a : ↥M) : MulAut W) ∈ B₁ := htrick a a.2 fun k hk s hs => by
      have h1 := Subgroup.mem_centralizer_iff.1 hac (ρK ⟨k, hk⟩) ⟨_, rfl⟩
      have hx : (a : ↥M)⁻¹ • k⁻¹ • s ∈ S :=
        hSA _ ((A.subgroupOf M).inv_mem a.2) _ (hSK _ ((K₀.subgroupOf M).inv_mem hk) s hs)
      have h2 : k • (a : ↥M) • ((a : ↥M)⁻¹ • k⁻¹ • s) =
          (a : ↥M) • k • ((a : ↥M)⁻¹ • k⁻¹ • s) :=
        congrArg (fun φ : MulAut ↥S => ((φ ⟨_, hx⟩ : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W))) h1
      rw [smul_inv_smul, smul_inv_smul] at h2
      rw [commutatorElement_def, mul_smul, mul_smul, mul_smul]
      exact h2.symm
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show (a : ↥M) • (x : W ⧸ modFix Mp (⊤ : Subgroup W)) = x
    exact (XMod.mem_fixed.1 x.2.2).2 ⟨a, hB⟩
  have hrank : rk ↥ρA.range = rk ↥A - rk ↥B₁ := by
    have h1 : rk ↥ρA.range + rk ↥(A.subgroupOf M ⊓
        fixingSubgroup ↥M (S : Set (W ⧸ modFix Mp (⊤ : Subgroup W)))) = rk ↥(A.subgroupOf M) :=
      rk_range_resJ (S := A.subgroupOf M) (J := S) (hS := hSA)
    have h2 : A.subgroupOf M ⊓ fixingSubgroup ↥M (S : Set (W ⧸ modFix Mp (⊤ : Subgroup W))) =
        B₁.subgroupOf M := by
      ext a
      constructor
      · rintro ⟨ha, hfx⟩
        exact hfixS a ha fun s hs => (mem_fixingSubgroup_iff ↥M).1 hfx s hs
      · intro hb
        exact ⟨hB₁A hb, (mem_fixingSubgroup_iff ↥M).2 fun s hs => (XMod.mem_fixed.1 hs.2).2 ⟨a, hb⟩⟩
    rw [h2] at h1
    have h3 : rk ↥(A.subgroupOf M) = rk ↥A := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    have h4 : rk ↥(B₁.subgroupOf M) = rk ↥B₁ := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁M).toEquiv]
    omega
  have hnBS : nB (A.subgroupOf M) S = rkIdx (fixV ρA.range) := nB_eq_rkIdx_fixV hSA
  have hr : 2 * rkIdx (fixV ρA.range) ≤ rk ↥ρA.range := by
    rw [← hnBS, hrank]
    have := hD7.1
    omega
  have hpK : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥L →
      ∀ x ∈ ρK.range, ∀ k : ℕ, x ^ (p ^ k) = 1 → x = 1 := by
    intro p hp hp2 hpL
    refine eq_one_of_pow_of_mem_range ρK hp fun g k hg => ?_
    have h1 : ((g : ↥M) : MulAut W) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      hKC (Subgroup.mem_subgroupOf.1 g.2)
    have h2 : ((g : ↥M) : MulAut W) ^ (p ^ k) = 1 := by
      have := congrArg (fun x : ↥(K₀.subgroupOf M) => ((x : ↥M) : MulAut W)) hg
      simpa using this
    exact Subtype.ext (Subtype.ext (hS.eq_one_of_pow_prime_pow hp hp2 hpL h1 h2))
  have h5 := hpK 5 Nat.prime_five (by norm_num) (five_dvd_card_of_isSz hSz)
  refine false_of_two_mul_rkIdx_le hA21 hB42 hQS hH hKbar hAKbar hAebar hA1bar hAfbar hr h5 ?_
  intro heq
  have hB₁0 : B₁ = ⊥ := by
    by_contra hne
    have h1 := hD7.2 hne
    rw [← hnBS, hrank] at heq
    omega
  have hSX : S = X₁ := by rw [hSdef, hS₀top hB₁0, inf_top_eq]
  obtain ⟨-, hn3⟩ := odd_of_isSz hSz
  obtain ⟨p, hp, hp2, hpd⟩ := exists_prime_dvd_two_pow_sub_one (show 2 ≤ n by omega)
  have hpD : p ∣ Nat.card (Module.End ↥(XMod.opRing ↥(Mp.subgroupOf M)
      (W ⧸ modFix Mp (⊤ : Subgroup W))) ↥(XMod.toSubmod hJ.1)) - 1 := by
    rw [hJend]
    exact hpd
  obtain ⟨φ, hφp, hφfp, hφc⟩ := hX₁φ p hp hpD
  set e : ↥S ≃* ↥X₁ := MulEquiv.subgroupCongr hSX with he
  set ψ : MulAut ↥S := (e.trans φ).trans e.symm with hψdef
  have hψ : ∀ s : ↥S, ((ψ s : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      ((φ (e s) : ↥X₁) : W ⧸ modFix Mp (⊤ : Subgroup W)) := fun _ => rfl
  have hψpow : ∀ k : ℕ, ∀ s : ↥S, (((ψ ^ k) s : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      (((φ ^ k) (e s) : ↥X₁) : W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ', MulAut.mul_apply, hψ, pow_succ', MulAut.mul_apply]
      congr 2
      apply Subtype.ext
      exact ih s
  have hcomm : ∀ (g : ↥M), (∀ l ∈ Mp.subgroupOf M, l * g = g * l) →
      ∀ (hg : ∀ s ∈ S, g • s ∈ S) (s : ↥S),
        ((ψ ⟨g • (s : W ⧸ modFix Mp (⊤ : Subgroup W)), hg s s.2⟩ : ↥S) :
          W ⧸ modFix Mp (⊤ : Subgroup W)) = g • ((ψ s : ↥S) : W ⧸ modFix Mp (⊤ : Subgroup W)) := by
    intro g hgΛ hg s
    rw [hψ, hψ]
    exact hφc g hgΛ (e s) (e ⟨_, hg s s.2⟩) rfl
  refine ⟨ψ, p, hp, MulEquiv.ext fun s => Subtype.ext ?_, fun x hx => ?_, ?_, ?_,
    hpK p hp hp2 (dvd_card_of_isSz hSz hpd)⟩
  · rw [hψpow, hφp]
    rfl
  · have h1 : φ (e x) = e x := Subtype.ext (by
      have := congrArg (fun y : ↥S => (y : W ⧸ modFix Mp (⊤ : Subgroup W))) hx
      rw [hψ] at this
      exact this)
    have h2 := hφfp _ h1
    exact e.injective (h2.trans (map_one e).symm)
  · rintro _ ⟨k, rfl⟩
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact hcomm (k : ↥M) (hKc' k k.2) (fun s hs => hSK _ k.2 s hs) s
  · rintro _ ⟨a, rfl⟩
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact hcomm (a : ↥M) (hAc' a a.2) (fun s hs => hSA _ a.2 s hs) s

end D321Sit

section Diagonal

theorem exists_odd_not_mem_center {Y : Type*} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y) :
    ∃ x : Y, Odd (orderOf x) ∧ x ∉ Subgroup.center Y := by
  classical
  by_contra h
  push Not at h
  obtain ⟨-, hsimp, a, b, hab⟩ := hY
  have h2 : IsPGroup 2 (Y ⧸ Subgroup.center Y) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨k, ?_⟩
    have hg : g ^ (2 ^ k) ∈ Subgroup.center Y := by
      refine h _ (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_))
      rw [← pow_mul, ← hord, pow_orderOf_eq_one]
    show (QuotientGroup.mk g : Y ⧸ Subgroup.center Y) ^ (2 ^ k) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (Y ⧸ Subgroup.center Y) := IsPGroup.isNilpotent h2
  have hcomm : ∀ x y : Y ⧸ Subgroup.center Y, x * y = y * x :=
    IsSimpleGroup.comm_iff_isSolvable.2 inferInstance
  exact hab (hcomm a b)

variable {G : Type*} [Group G]

private def twoDiag (K : Subgroup G) (a : G)
    (hc : ∀ x ∈ K, ∀ y ∈ K, x * (a * y * a⁻¹) = (a * y * a⁻¹) * x) : ↥K →* G where
  toFun k := (k : G) * (a * k * a⁻¹)
  map_one' := by simp
  map_mul' k l := by
    simp only [Subgroup.coe_mul]
    have h1 := hc l l.2 k k.2
    calc (k : G) * l * (a * (k * l) * a⁻¹) = k * (l * (a * k * a⁻¹)) * (a * l * a⁻¹) := by group
      _ = k * ((a * k * a⁻¹) * l) * (a * l * a⁻¹) := by rw [h1]
      _ = (k : G) * (a * k * a⁻¹) * (l * (a * l * a⁻¹)) := by group

end Diagonal

namespace D321Sit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem le_normalizer_of_comm (hS : D321Sit M Mp T L V t A r)
    (hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hV2 : letI := qAct hS.hD.hyp.Mp_normal; 2 < rk ↥(tilde Mp ⊤ V))
    (hNAL : ∀ K₀ : Subgroup (MulAut W), CFSG.IsQuasisimple ↥K₀ →
      K₀ ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) →
      (∀ a ∈ A, ∀ k ∈ K₀, a * k * a⁻¹ ∈ K₀) → A ≤ Subgroup.centralizer (K₀ : Set (MulAut W)))
    {K : Subgroup (MulAut W)} (hKq : CFSG.IsQuasisimple ↥K)
    (hKC : K ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hcomm : ∀ b ∈ A, b ∉ Subgroup.normalizer (K : Set (MulAut W)) →
      ∀ x ∈ K, ∀ y ∈ K, x * (b * y * b⁻¹) = (b * y * b⁻¹) * x) :
    A ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  classical
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hCdef
  have hAM : A ≤ M := hS.A_le
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hS.elemAb.1
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact hS.elemAb.2 a ha
  have hAinv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hA2 a ha)
  have hconjC : ∀ c ∈ A, ∀ k ∈ C, c * k * c⁻¹ ∈ C := by
    intro c hc k hk
    refine ⟨M.mul_mem (M.mul_mem (hAM hc) hk.1) (M.inv_mem (hAM hc)), ?_⟩
    show c * k * c⁻¹ ∈ Subgroup.centralizer (Mp : Set (MulAut W))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : Commute y c := (Subgroup.mem_centralizer_iff.1 (hAC hc)) y hy
    have h2 : Commute y k := (Subgroup.mem_centralizer_iff.1 hk.2) y hy
    exact ((h1.mul_right h2).mul_right h1.inv_right).eq
  suffices key : ∀ d : ℕ, ∀ K : Subgroup (MulAut W),
      Nat.card ↥A - Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set (MulAut W))) = d →
      CFSG.IsQuasisimple ↥K → K ≤ C → (∀ b ∈ A, b ∉ Subgroup.normalizer (K : Set (MulAut W)) →
        ∀ x ∈ K, ∀ y ∈ K, x * (b * y * b⁻¹) = (b * y * b⁻¹) * x) →
      A ≤ Subgroup.normalizer (K : Set (MulAut W)) from key _ K rfl hKq hKC hcomm
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih => ?_
  intro K hd hKq hKC hcomm
  by_contra hAN
  obtain ⟨a, ha, haN⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut W)) := by
    by_contra h
    push Not at h
    exact hAN h
  have hca := hcomm a ha haN
  obtain ⟨x₀, hx₀odd, hx₀c⟩ := exists_odd_not_mem_center hKq
  have hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
    by_contra h
    push Not at h
    apply hx₀c
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h _ g.2 _ x₀.2)
  set δ := twoDiag K a hca with hδ
  set K' := δ.range with hK'
  have hδ' : ∀ k : ↥K, δ k = (k : MulAut W) * (a * k * a⁻¹) := fun _ => rfl
  have hconjδ : ∀ c ∈ A, ∀ (hcN : c ∈ Subgroup.normalizer (K : Set (MulAut W))) (k : ↥K),
      c * δ k * c⁻¹ = δ ⟨c * k * c⁻¹, ((Subgroup.mem_normalizer_iff.1 hcN) k).1 k.2⟩ := by
    intro c hc hcN k
    rw [hδ', hδ']
    have hac : a * c = c * a := hAc a ha c hc
    calc c * ((k : MulAut W) * (a * k * a⁻¹)) * c⁻¹ =
        (c * k * c⁻¹) * ((c * a) * k * (c * a)⁻¹) := by group
      _ = (c * k * c⁻¹) * ((a * c) * k * (a * c)⁻¹) := by rw [hac]
      _ = (c * k * c⁻¹) * (a * (c * k * c⁻¹) * a⁻¹) := by group
  have haδ : ∀ k : ↥K, a * δ k * a⁻¹ = δ k := by
    intro k
    rw [hδ']
    have h1 := hca k k.2 k k.2
    have ha1 : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, hA2 a ha, inv_one]
    calc a * ((k : MulAut W) * (a * k * a⁻¹)) * a⁻¹ =
        (a * k * a⁻¹) * ((a * a) * k * (a⁻¹ * a⁻¹)) := by group
      _ = (a * k * a⁻¹) * k := by rw [hA2 a ha, ha1]; group
      _ = k * (a * k * a⁻¹) := h1.symm
  have hN1 : ∀ c ∈ A, c ∈ Subgroup.normalizer (K : Set (MulAut W)) →
      c ∈ Subgroup.normalizer (K' : Set (MulAut W)) := by
    intro c hc hcN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, (hconjδ c hc hcN k).symm⟩
    · rintro ⟨k, hk⟩
      have hc' : c⁻¹ ∈ Subgroup.normalizer (K : Set (MulAut W)) := Subgroup.inv_mem _ hcN
      refine ⟨⟨c⁻¹ * k * c⁻¹⁻¹, ((Subgroup.mem_normalizer_iff.1 hc') k).1 k.2⟩, ?_⟩
      rw [← hconjδ c⁻¹ (A.inv_mem hc) hc' k, hk]
      group
  have haN' : a ∈ Subgroup.normalizer (K' : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (haδ k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc δ k = a⁻¹ * (a * δ k * a⁻¹) * a := by group
        _ = a⁻¹ * δ k * a := by rw [haδ k]
        _ = z := by rw [hk]; group
  have hNK' : ∀ c ∈ A, (c ∈ Subgroup.normalizer (K : Set (MulAut W)) ∨
      a * c ∈ Subgroup.normalizer (K : Set (MulAut W))) →
      c ∈ Subgroup.normalizer (K' : Set (MulAut W)) := by
    intro c hc hcases
    rcases hcases with h | h
    · exact hN1 c hc h
    · have e : c = a * (a * c) := by rw [← mul_assoc, hA2 a ha, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ haN' (hN1 _ (A.mul_mem ha hc) h)
  have hcomm' : ∀ b ∈ A, b ∉ Subgroup.normalizer (K' : Set (MulAut W)) →
      ∀ x ∈ K', ∀ y ∈ K', x * (b * y * b⁻¹) = (b * y * b⁻¹) * x := by
    intro b hb hbN x hx y hy
    have hbK : b ∉ Subgroup.normalizer (K : Set (MulAut W)) := fun h => hbN (hNK' b hb (Or.inl h))
    have habK : a * b ∉ Subgroup.normalizer (K : Set (MulAut W)) := fun h =>
      hbN (hNK' b hb (Or.inr h))
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hab : a * b = b * a := hAc a ha b hb
    have e1 : b * δ l * b⁻¹ = (b * l * b⁻¹) * ((a * b) * l * (a * b)⁻¹) := by
      rw [hδ', hab]
      group
    rw [e1, hδ']
    have c1 : Commute (k : MulAut W) (b * l * b⁻¹) := hcomm b hb hbK k k.2 l l.2
    have c2 : Commute (k : MulAut W) ((a * b) * l * (a * b)⁻¹) :=
      hcomm (a * b) (A.mul_mem ha hb) habK k k.2 l l.2
    have ha1 : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, hA2 a ha, inv_one]
    have e2 : b * l * b⁻¹ = a * ((a * b) * l * (a * b)⁻¹) * a⁻¹ := by
      calc b * l * b⁻¹ = (a * a) * b * l * b⁻¹ * (a⁻¹ * a⁻¹) := by rw [hA2 a ha, ha1]; group
        _ = a * ((a * b) * l * (a * b)⁻¹) * a⁻¹ := by group
    have e3 : (a * b) * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ := by group
    have conj : ∀ {u v : MulAut W}, Commute u v → Commute (a * u * a⁻¹) (a * v * a⁻¹) := by
      intro u v huv
      have := huv.map (MulAut.conj a).toMonoidHom
      simpa [MulAut.conj_apply] using this
    have c3 : Commute (a * k * a⁻¹) (b * l * b⁻¹) := by
      rw [e2]
      exact conj c2
    have c4 : Commute (a * k * a⁻¹) ((a * b) * l * (a * b)⁻¹) := by
      rw [e3]
      exact conj c1
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  have hle : A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      A ⊓ Subgroup.normalizer (K' : Set (MulAut W)) :=
    fun c hc => ⟨hc.1, hNK' c hc.1 (Or.inl hc.2)⟩
  have haK' : a ∈ A ⊓ Subgroup.normalizer (K' : Set (MulAut W)) := ⟨ha, haN'⟩
  have hlt : Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set (MulAut W))) <
      Nat.card ↥(A ⊓ Subgroup.normalizer (K' : Set (MulAut W))) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h => ?_
    have heq := Subgroup.eq_of_le_of_card_ge hle h.ge
    rw [← heq] at haK'
    exact haN haK'.2
  have hcardA : Nat.card ↥(A ⊓ Subgroup.normalizer (K' : Set (MulAut W))) ≤ Nat.card ↥A :=
    Subgroup.card_le_of_le inf_le_left
  have hK'q : CFSG.IsQuasisimple ↥K' := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hKq δ.rangeRestrict_surjective ?_
    by_contra h
    push Not at h
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    apply hxy
    have hx1 : (x : MulAut W) * (a * x * a⁻¹) = 1 := congrArg Subtype.val (h ⟨x, hx⟩)
    have hxe : x = (a * x * a⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx1
    have hc : Commute y (a * x * a⁻¹) := hca y hy x hx
    have hc' : Commute y x := by
      have := hc.inv_right
      rwa [← hxe] at this
    exact hc'.eq.symm
  have hK'C : K' ≤ C := by
    rintro _ ⟨k, rfl⟩
    rw [hδ']
    exact C.mul_mem (hKC k.2) (hconjC a ha k (hKC k.2))
  have hAN' := ih _ (by omega) K' rfl hK'q hK'C hcomm'
  have hAC' := hNAL K' hK'q hK'C fun c hc z hz =>
    ((Subgroup.mem_normalizer_iff.1 (hAN' hc)) z).1 hz
  have hcδ : ∀ c ∈ A, ∀ k : ↥K, c * δ k * c⁻¹ = δ k := by
    intro c hc k
    have h1 : δ k * c = c * δ k := (Subgroup.mem_centralizer_iff.1 (hAC' hc)) (δ k) ⟨k, rfl⟩
    rw [← h1]
    group
  set B' := A ⊓ Subgroup.normalizer (K : Set (MulAut W)) with hB'
  have hsplit : ∀ c ∈ A, c ∈ B' ∨ a⁻¹ * c ∈ B' := by
    intro c hc
    by_contra h
    push Not at h
    have hcK : c ∉ Subgroup.normalizer (K : Set (MulAut W)) := fun h' => h.1 ⟨hc, h'⟩
    have hacK : a * c ∉ Subgroup.normalizer (K : Set (MulAut W)) := fun h' =>
      h.2 ⟨A.mul_mem (A.inv_mem ha) hc, by rw [hAinv a ha]; exact h'⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    apply hxy
    have hac : a * c = c * a := hAc a ha c hc
    have e1 : c * δ ⟨x, hx⟩ * c⁻¹ = (c * x * c⁻¹) * ((a * c) * x * (a * c)⁻¹) := by
      rw [hδ', hac]
      group
    have cy1 : Commute y (c * x * c⁻¹) := hcomm c hc hcK y hy x hx
    have cy2 : Commute y ((a * c) * x * (a * c)⁻¹) := hcomm (a * c) (A.mul_mem ha hc) hacK y hy x hx
    have cyδ : Commute y (δ ⟨x, hx⟩) := by
      rw [← hcδ c hc ⟨x, hx⟩, e1]
      exact cy1.mul_right cy2
    have cya : Commute y (a * x * a⁻¹) := hca y hy x hx
    have ex : (x : MulAut W) = δ ⟨x, hx⟩ * (a * x * a⁻¹)⁻¹ := by
      rw [hδ']
      group
    have cyx : Commute y x := by
      have := cyδ.mul_right cya.inv_right
      rwa [← ex] at this
    exact cyx.eq.symm
  have hB'A : B' ≤ A := inf_le_left
  have hrk := SmithD310U.rk_eq_add_one_of_split hB'A ha (fun h => haN h.2) hsplit
  have hperf : ⁅K, K⁆ = K := by
    have : Group.IsPerfect ↥K := hKq.1
    exact Subgroup.commutator_eq_self
  have hB'K : ∀ b ∈ B', ∀ k ∈ K, b * k = k * b := by
    intro b hb
    have hbN : ∀ l ∈ K, b * l * b⁻¹ ∈ K := fun l hl =>
      ((Subgroup.mem_normalizer_iff.1 hb.2) l).1 hl
    refine B5.commute_of_comm_central hperf hbN (Z := Subgroup.centralizer (K : Set (MulAut W)))
      (fun z hz l hl => ((Subgroup.mem_centralizer_iff.1 hz) l hl).symm) fun l hl => ?_
    set u := b * l * b⁻¹ with hu
    have huK : u ∈ K := hbN l hl
    have hδuv : δ ⟨u, huK⟩ = δ ⟨l, hl⟩ := by
      rw [← hconjδ b hb.1 hb.2 ⟨l, hl⟩]
      exact hcδ b hb.1 ⟨l, hl⟩
    rw [hδ', hδ'] at hδuv
    have hlu : l * u⁻¹ ∈ K := K.mul_mem hl (K.inv_mem huK)
    have h1 : l⁻¹ * u = a * (l * u⁻¹) * a⁻¹ := by
      calc l⁻¹ * u = l⁻¹ * (u * (a * u * a⁻¹)) * (a * u * a⁻¹)⁻¹ := by group
        _ = l⁻¹ * (l * (a * l * a⁻¹)) * (a * u * a⁻¹)⁻¹ := by rw [hδuv]
        _ = a * (l * u⁻¹) * a⁻¹ := by group
    have h2 : Commute l (a * (l * u⁻¹) * a⁻¹) := hca l hl _ hlu
    have hz : u * l⁻¹ = a * (l * u⁻¹) * a⁻¹ := by
      calc u * l⁻¹ = l * (l⁻¹ * u) * l⁻¹ := by group
        _ = l * (a * (l * u⁻¹) * a⁻¹) * l⁻¹ := by rw [h1]
        _ = a * (l * u⁻¹) * a⁻¹ := by rw [h2.eq]; group
    rw [commutatorElement_def, show b * l * b⁻¹ * l⁻¹ = u * l⁻¹ from rfl, hz,
      Subgroup.mem_centralizer_iff]
    intro y hy
    exact hca y hy _ hlu
  have hB'Ka : ∀ b ∈ B', ∀ k ∈ K, Commute b (a * k * a⁻¹) := by
    intro b hb k hk
    have h1 : Commute b a := (hAc b hb.1 a ha)
    have h2 : Commute b k := hB'K b hb k hk
    exact (h1.mul_right h2).mul_right h1.inv_right
  have hGL := hS.fix_fixed_of_rk_lt hAC hB'A (by omega)
  set xx : MulAut W := (x₀ : MulAut W) with hxx
  set w : MulAut W := a * xx * a⁻¹ with hw
  set y : MulAut W := xx * w⁻¹ with hy
  have hxw : Commute xx w := hca xx x₀.2 xx x₀.2
  have hyC : y ∈ C := C.mul_mem (hKC x₀.2) (C.inv_mem (hconjC a ha _ (hKC x₀.2)))
  have hxm : xx ^ orderOf x₀ = 1 := by
    rw [hxx, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hwm : w ^ orderOf x₀ = 1 := by
    rw [hw, conj_pow, hxm]
    group
  have hym : y ^ orderOf x₀ = 1 := by
    rw [hy, hxw.inv_right.mul_pow, hxm, inv_pow, hwm, inv_one, one_mul]
  have hyB : ∀ e ∈ B', Commute y e := by
    intro e he
    have h1 : Commute xx e := (hB'K e he xx x₀.2).symm
    have h2 : Commute w e := (hB'Ka e he xx x₀.2).symm
    exact h1.mul_left h2.inv_left
  have ha1 : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, hA2 a ha, inv_one]
  have hay : a * y * a⁻¹ = y⁻¹ := by
    rw [hy, hw, mul_inv_rev, inv_inv]
    calc a * (xx * (a * xx⁻¹ * a⁻¹)) * a⁻¹ = a * xx * a⁻¹ * ((a * a) * xx⁻¹ * (a⁻¹ * a⁻¹)) := by
          group
      _ = a * xx * a⁻¹ * xx⁻¹ := by rw [hA2 a ha, ha1]; group
  let _i := qAct hS.hD.hyp.Mp_normal
  have hB'M : B' ≤ M := hB'A.trans hAM
  set yM : ↥M := ⟨y, hyC.1⟩ with hyM
  set aM : ↥M := ⟨a, hAM ha⟩ with haM
  have hayM : aM * yM * aM⁻¹ = yM⁻¹ := Subtype.ext hay
  have hy2fix : ∀ q ∈ XMod.fixed ↥(B'.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))), (yM * yM) • q = q := by
    intro q hq
    have hyq : yM • q ∈ XMod.fixed ↥(B'.subgroupOf M)
        (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
      refine XMod.mem_fixed.2 ⟨trivial, fun e => ?_⟩
      have he : (e : ↥M) * yM = yM * (e : ↥M) :=
        Subtype.ext ((hyB _ (Subgroup.mem_subgroupOf.1 e.2)).symm.eq)
      show (e : ↥M) • yM • q = yM • q
      rw [smul_smul, he, mul_smul]
      exact congrArg (yM • ·) ((XMod.mem_fixed.1 hq).2 e)
    have h1 : aM • (yM • q) = yM • q := hGL aM ha _ hyq
    have h2 : aM⁻¹ • q = q := hGL aM⁻¹ ((A.subgroupOf M).inv_mem ha) q hq
    have h3 : yM⁻¹ • q = yM • q := by
      rw [← hayM, mul_smul, mul_smul, h2, h1]
    rw [mul_smul, ← h3, smul_inv_smul]
  have hyN : ∀ x ∈ Mp, y * y * x = x * (y * y) := by
    intro x hx
    have h1 : Commute x y := (Subgroup.mem_centralizer_iff.1 hyC.2) x hx
    exact ((h1.mul_right h1).symm).eq
  have hyy : (y * y) ^ orderOf x₀ = 1 := by
    rw [(Commute.refl y).mul_pow, hym, one_mul]
  have hy2 := SmithD39Two.eq_one_of_fix_fixed hS.hD.hyp.Mp_normal hS.exp hS.commV_eq_top hB'M
    (hS.isPGroup.to_le hB'A) (M.mul_mem hyC.1 hyC.1) hyN hx₀odd hyy
    (fun e he => (((hyB e he).mul_left (hyB e he))).eq) hy2fix
  have hy1 : y = 1 := by
    obtain ⟨j, hj⟩ := hx₀odd
    have h1 : y ^ orderOf x₀ = (y * y) ^ j * y := by
      rw [hj, pow_succ, pow_mul, sq]
    rw [hym, hy2, one_pow, one_mul] at h1
    exact h1.symm
  apply hx₀c
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hxw' : xx = w := by
    have := hy1
    rw [hy, mul_inv_eq_one] at this
    exact this
  show (g : MulAut W) * xx = xx * g
  rw [hxw']
  exact hca g g.2 x₀ x₀.2

end D321Sit

theorem szStep_holds
    (hSzA : H13.SzTwoAutInnerFact) (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38) : SzStep := by
  intro W _ _ M Mp T L V t A r hS hlt hc hU n hSz
  have hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v := hc.1
  have hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have key : ∀ U : Subgroup W, U = V → qhatOf (autSub (Mp ⊔ T) U) ≤ ((2 : ℚ) : WithTop ℚ) →
        qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
      rintro U rfl h
      exact h
    exact key _ hU hc.2.2.1
  obtain ⟨hVc, -⟩ := hS.card_tildeV hA21 hL38 hlt hVt hqV hSz
  obtain ⟨-, hn3⟩ := odd_of_isSz hSz
  have hVrk4 : (letI := qAct hS.hD.hyp.Mp_normal; rk ↥(tilde Mp ⊤ V)) = 4 * n := by
    let _i := qAct hS.hD.hyp.Mp_normal
    unfold rk
    rw [hVc, padicValNat.prime_pow]
  refine hS.false_of_sz_of_comp hSzA hB45 hF hA21 h38 hA23 hSzF hVt hSz (by rw [hVrk4]; omega) ?_
  intro hAC K hK hKq hKC _
  have hNAL : ∀ K₀ : Subgroup (MulAut W), CFSG.IsQuasisimple ↥K₀ →
      K₀ ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) →
      (∀ a ∈ A, ∀ k ∈ K₀, a * k * a⁻¹ ∈ K₀) →
      A ≤ Subgroup.centralizer (K₀ : Set (MulAut W)) := fun K₀ hK₀q hK₀C hAK₀ =>
    hS.le_centralizer_of_quasi hA21 hB42 hL38 hlt hVt hqV hSz hAC hK₀q hK₀C hAK₀
  have hcomm : ∀ b ∈ A, b ∉ Subgroup.normalizer (K : Set (MulAut W)) →
      ∀ x ∈ K, ∀ y ∈ K, x * (b * y * b⁻¹) = (b * y * b⁻¹) * x := by
    intro b hb hbN x hx y hy
    have hKb : conjAutSub b K ∈ cComp M := conjAutSub_mem_cComp hK (hS.A_le hb)
    have hKbq : CFSG.IsQuasisimple ↥(conjAutSub b K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective K (MulAut.conj b).toMonoidHom (MulAut.conj b).injective) hKq
    have hne : K ≠ conjAutSub b K := fun h =>
      hbN (mem_normalizer_iff_conjAutSub.2 h.symm)
    exact SmithD310U.commute_of_mem_cComp hK hKq hKb hKbq hne x hx _ (conj_mem_conjAutSub b hy)
  have hAN := hS.le_normalizer_of_comm hAC (by rw [hVrk4]; omega) hNAL hKq hKC hcomm
  exact hNAL K hKq hKC fun a ha k hk => ((Subgroup.mem_normalizer_iff.1 (hAN ha)) k).1 hk

end CFSG.Quasithin.SmithD321
