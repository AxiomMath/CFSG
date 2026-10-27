module

public import CFSG.Quasithin.Vol2.Ch6NatSemi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ}

namespace NatL2Data

variable (D : NatL2Data L V n)

theorem toAdd_E_conj (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    Multiplicative.toAdd (D.E (conjAct V g v)) = D.conj g (Multiplicative.toAdd (D.E v)) :=
  (D.conj_apply g v).symm

theorem mem_centralizer_of_conj_eq (g : Subgroup.normalizer (V : Set G))
    (hg : ∀ w, D.conj g w = w) : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := D.toAdd_E_conj g ⟨v, hv⟩
  rw [hg] at h1
  have h2 : conjAct V g ⟨v, hv⟩ = ⟨v, hv⟩ :=
    D.E.injective (Multiplicative.toAdd.injective h1)
  have h3 := congrArg Subtype.val h2
  rw [conjAct_apply_coe] at h3
  calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * g := by rw [h3]
    _ = g * v := by group

theorem conj_eq_of_mem_centralizer (g : Subgroup.normalizer (V : Set G))
    (hg : (g : G) ∈ Subgroup.centralizer (V : Set G)) (w : Fin 2 → D.K) : D.conj g w = w := by
  obtain ⟨v, rfl⟩ : ∃ v : ↥V, Multiplicative.toAdd (D.E v) = w :=
    ⟨D.E.symm (Multiplicative.ofAdd w), by simp⟩
  rw [← D.toAdd_E_conj]
  congr 2
  apply Subtype.ext
  rw [conjAct_apply_coe]
  have := Subgroup.mem_centralizer_iff.mp hg v v.2
  calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [this]
    _ = v := by group

theorem exists_conj_eq_smul (m : Subgroup.normalizer (V : Set G))
    (hm : ∀ g ∈ L, (m : G) * g * (m : G)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    ∃ c : D.K, ∀ w, D.conj m w = c • w := by
  apply exists_eq_smul_of_commute
  intro A w
  obtain ⟨g, hgL, hg⟩ := D.exists_mem_of_matrix A
  rw [← hg, ← hg, ← D.conj_mul, ← D.conj_mul]
  have hc : ((m * g * m⁻¹ * g⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    simpa using hm g hgL
  have e : m * g = (m * g * m⁻¹ * g⁻¹) * (g * m) := by group
  rw [e, D.conj_mul, D.conj_eq_of_mem_centralizer _ hc]

end NatL2Data

theorem sl2X_one_mulVec {K : Type} [Field K] :
    (sl2X (1 : K) : Matrix (Fin 2) (Fin 2) K).mulVec ![0, 1] = ![1, 1] := by
  funext i; fin_cases i <;> simp [sl2X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem IsNatModCh5.not_le_centralizer (h : IsNatModCh5 L V n) :
    ¬ L ≤ Subgroup.centralizer (V : Set G) := by
  intro hL
  let D := h.data
  obtain ⟨g, hgL, hg⟩ := D.exists_mem_of_matrix (sl2X 1)
  have h1 := hg ![0, 1]
  rw [D.conj_eq_of_mem_centralizer g (hL hgL), sl2X_one_mulVec] at h1
  have := congrFun h1 0
  simp at this

theorem IsNatModCh5.commutator_eq (h : IsNatModCh5 L V n) : ⁅V, L⁆ = V := by
  have hLV := h.1
  have hle : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have : l * v⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact V.mul_mem hv this
  have hN : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hmap : (⁅V, L⁆).map (MulAut.conj l).toMonoidHom = ⁅V, L⁆ := by
      rw [Subgroup.map_commutator]
      congr 1
      · ext y
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv
        · intro hy
          refine ⟨l⁻¹ * y * l, ?_, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLV hl)) y).mp hy
          simpa using this
      · ext y
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl)
        · intro hy
          exact ⟨l⁻¹ * y * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hy) hl, by group⟩
    constructor
    · intro hx
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := by
        have := congrArg (fun z => l⁻¹ * z * l) hyx
        simpa [mul_assoc] using this
      rw [← this]; exact hy
  rcases h.irreducible ⁅V, L⁆ hle hN with h0 | h0
  · exfalso
    apply h.not_le_centralizer
    rw [Subgroup.commutator_comm] at h0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
  · exact h0

namespace NatL2Data

variable (D : NatL2Data L V n)

theorem conj_pow (m : Subgroup.normalizer (V : Set G)) (k : ℕ) (w : Fin 2 → D.K) :
    D.conj (m ^ k) w = (D.conj m)^[k] w := by
  induction k generalizing w with
  | zero =>
    rw [pow_zero, Function.iterate_zero, id_eq]
    change Additive.ofMul (D.E (conjAct V 1 (D.E.symm (Additive.toMul w)))) = w
    rw [map_one, MulAut.one_apply, MulEquiv.apply_symm_apply]
    rfl
  | succ k ih => rw [pow_succ, D.conj_mul, ih, Function.iterate_succ_apply]

end NatL2Data

theorem IsNatModCh5.mem_centralizer_of_pow (h : IsNatModCh5 L V n)
    (m : Subgroup.normalizer (V : Set G))
    (hm : ∀ g ∈ L, (m : G) * g * (m : G)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G)) (k : ℕ)
    (hk : (m : G) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)) :
    (m : G) ∈ Subgroup.centralizer (V : Set G) := by
  classical
  let D := h.data
  obtain ⟨c, hc⟩ := D.exists_conj_eq_smul m hm
  have hiter : ∀ j : ℕ, ∀ w, (D.conj m)^[j] w = c ^ j • w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih => intro w; rw [Function.iterate_succ_apply', ih, hc, smul_smul, pow_succ']
  have hfix : ∀ w, D.conj (m ^ 2 ^ k) w = w :=
    D.conj_eq_of_mem_centralizer (m ^ 2 ^ k) (by simpa using hk)
  have hpow : c ^ 2 ^ k = 1 := by
    have h1 := hfix ![1, 0]
    rw [D.conj_pow, hiter] at h1
    have := congrFun h1 0
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero k two_ne_zero)] at hpow
    exact zero_ne_one hpow
  have hc1 : c = 1 := by
    have := Fintype.ofFinite D.K
    let u : D.Kˣ := Units.mk0 c hc0
    have hu : u ^ 2 ^ k = 1 := Units.ext (by simpa [u] using hpow)
    have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu
    have h2 : orderOf u ∣ Fintype.card D.Kˣ := orderOf_dvd_card
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, D.card] at h2
    have hodd : Odd (2 ^ n - 1) := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rcases Nat.even_or_odd (2 ^ n - 1) with he | ho
      · exfalso
        have hn : n ≠ 0 := by
          rintro rfl
          have : Nat.card D.K = 1 := by simpa using D.card
          exact (Finite.one_lt_card (α := D.K)).ne' this
        have h2n : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, hn⟩)
        have : Even (2 ^ n - 1 + 1) := by rw [Nat.sub_add_cancel this]; exact h2n
        exact (Nat.even_add_one.mp this) he
      · exact ho
    have hcop : Nat.Coprime (2 ^ k) (2 ^ n - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have hord : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have := orderOf_eq_one_iff.mp hord
    have := congrArg Units.val this
    simpa [u] using this
  apply D.mem_centralizer_of_conj_eq
  intro w
  rw [hc, hc1, one_smul]

theorem IsNatModCh5.le_centralizer_of_normal_two (h : IsNatModCh5 L V n) [Finite G]
    {P : Subgroup G} (hPL : P ≤ L) (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hP2 : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)) :
    P ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := h.1
  let D := h.data
  let Pbar : Subgroup (MulAut ↥V) := autOn P V
  have hPbar : IsPGroup 2 ↥Pbar := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgP, rfl⟩ := mem_autOn_iff.mp hφ
    obtain ⟨k, hk⟩ := hP2 g hgP
    refine ⟨k, Subtype.ext ?_⟩
    show (conjAct V g) ^ 2 ^ k = 1
    rw [← map_pow]
    refine MulEquiv.ext fun v => Subtype.ext ?_
    have hc := Subgroup.mem_centralizer_iff.mp hk (v : G) v.2
    rw [MulAut.one_apply, conjAct_apply_coe]
    simp only [Subgroup.coe_pow]
    calc (g : G) ^ 2 ^ k * (v : G) * ((g : G) ^ 2 ^ k)⁻¹ =
          (v : G) * (g : G) ^ 2 ^ k * ((g : G) ^ 2 ^ k)⁻¹ := by rw [hc]
      _ = (v : G) := by group
  have hcard : 2 ∣ Nat.card ↥V := by
    rw [Nat.card_congr D.E.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_fin]
    have h2 : 2 ∣ Nat.card D.K := by
      rw [D.card]
      have hn : n ≠ 0 := by
        rintro rfl
        have : Nat.card D.K = 1 := by simpa using D.card
        exact (Finite.one_lt_card (α := D.K)).ne' this
      exact dvd_pow_self 2 hn
    exact h2.trans (Dvd.intro _ (by ring))
  have h1fix : (1 : ↥V) ∈ MulAction.fixedPoints ↥Pbar ↥V := fun φ => map_one (φ : MulAut ↥V)
  obtain ⟨b, hb, hb1⟩ := hPbar.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥V hcard h1fix
  let W : Subgroup G := V ⊓ Subgroup.centralizer (P : Set G)
  have hWV : W ≤ V := inf_le_left
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hLV hl) x
    have h2 := Subgroup.mem_normalizer_iff.mp
      (F7.normalizer_le_normalizer_centralizer P (hLP hl)) x
    simp only [W, Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  have hbW : ((b : ↥V) : G) ∈ W := by
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := hLV (hPL hg)
    have := hb ⟨conjAct V ⟨g, hgN⟩, mem_autOn_iff.mpr ⟨⟨g, hgN⟩, hg, rfl⟩⟩
    have h3 : ((conjAct V ⟨g, hgN⟩ b : ↥V) : G) = (b : G) := congrArg Subtype.val this
    rw [conjAct_apply_coe] at h3
    calc g * (b : G) = (g * (b : G) * g⁻¹) * g := by group
      _ = (b : G) * g := by rw [h3]
  rcases h.irreducible W hWV hLW with h0 | h0
  · exfalso
    apply hb1
    have : ((b : ↥V) : G) ∈ (⊥ : Subgroup G) := h0 ▸ hbW
    rw [Subgroup.mem_bot] at this
    exact (Subtype.ext this).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ W := h0 ▸ hv
    exact (Subgroup.mem_centralizer_iff.mp hvW.2 x hx).symm

theorem IsNatModCh5.isTwoReducedIn (h : IsNatModCh5 L V n) [Finite G] {X : Subgroup G}
    (hLX : L ≤ X) (hVX : V ≤ X) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 V) : IsTwoReducedIn X V := by
  refine ⟨hVX, hXV, hV, fun Dn hDX hXD hD2 => ?_⟩
  have hDL : Dn ⊓ L ≤ Subgroup.centralizer (V : Set G) := by
    refine h.le_centralizer_of_normal_two inf_le_right ?_ fun x hx => hD2 x hx.1
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hXD (hLX hl)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  intro d hd
  have hdN : d ∈ Subgroup.normalizer (V : Set G) := hXV (hDX hd)
  have hcomm : ∀ g ∈ L, d * g * d⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg
    refine hDL ⟨?_, ?_⟩
    · have : g * d⁻¹ * g⁻¹ ∈ Dn :=
        (Subgroup.mem_normalizer_iff.mp (hXD (hLX hg)) d⁻¹).mp (Dn.inv_mem hd)
      have e : d * g * d⁻¹ * g⁻¹ = d * (g * d⁻¹ * g⁻¹) := by group
      rw [e]
      exact Dn.mul_mem hd this
    · have : d * g * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hXL (hDX hd)) g).mp hg
      exact L.mul_mem this (L.inv_mem hg)
  obtain ⟨k, hk⟩ := hD2 d hd
  exact h.mem_centralizer_of_pow ⟨d, hdN⟩ hcomm k hk

theorem IsNatModCh5.card_eq (h : IsNatModCh5 L V n) : Nat.card V = 2 ^ n * 2 ^ n := by
  let D := h.data
  rw [Nat.card_congr D.E.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
    D.card, pow_two]

namespace NatL2Data

variable (D : NatL2Data L V n)

@[expose] noncomputable def fixedEquiv (m : Subgroup.normalizer (V : Set G)) :
    ↥(V ⊓ Subgroup.centralizer ({(m : G)} : Set G)) ≃ {w : Fin 2 → D.K // D.conj m w = w} where
  toFun v := ⟨Multiplicative.toAdd (D.E ⟨v, v.2.1⟩), by
    rw [← D.toAdd_E_conj]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp v.2.2 (m : G) rfl
    calc (m : G) * v * (m : G)⁻¹ = v * m * (m : G)⁻¹ := by rw [this]
      _ = v := by group⟩
  invFun w := ⟨(D.E.symm (Multiplicative.ofAdd w.1) : G), by
    refine Subgroup.mem_inf.mpr ⟨(D.E.symm (Multiplicative.ofAdd w.1)).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro x rfl
    have hw := w.2
    have h1 : D.conj m (Multiplicative.toAdd (D.E (D.E.symm (Multiplicative.ofAdd w.1)))) =
        Multiplicative.toAdd (D.E (D.E.symm (Multiplicative.ofAdd w.1))) := by
      simpa using hw
    rw [D.conj_apply] at h1
    have h2 := congrArg Subtype.val (D.E.injective (Multiplicative.toAdd.injective h1))
    rw [conjAct_apply_coe] at h2
    calc (m : G) * (D.E.symm (Multiplicative.ofAdd w.1) : G) =
        ((m : G) * (D.E.symm (Multiplicative.ofAdd w.1) : G) * (m : G)⁻¹) * m := by group
      _ = (D.E.symm (Multiplicative.ofAdd w.1) : G) * m := by rw [h2]⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

include D in
theorem card_fixed_le_two_pow (m : Subgroup.normalizer (V : Set G))
    (hmL : (m : G) ∈ Subgroup.normalizer (L : Set G))
    (hm : (m : G) ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({(m : G)} : Set G)) ≤ 2 ^ n := by
  rw [Nat.card_congr (D.fixedEquiv m), ← D.card]
  obtain ⟨σ, hσ⟩ := D.exists_semilinear m hmL
  refine CFSG.Quasithin.H13.card_fixed_le_semilinear (D.conj m) σ hσ ?_
  by_contra hcon
  push Not at hcon
  exact hm (D.mem_centralizer_of_conj_eq m hcon)

end NatL2Data

end CFSG.Quasithin.H13
