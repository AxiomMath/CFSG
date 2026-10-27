module

public import CFSG.Walter.ReeOrder.WardLocal.Main
public import CFSG.Walter.ReeOrder.WardLocal.CentP
public import CFSG.Walter.ReeOrder.WardLocal.Trans

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G]

omit [Group G] in
theorem conj_eq_smul {G : Type} [Group G] {A A' : Subgroup G} {g : G}
    (h : ∀ x, x ∈ A' ↔ g⁻¹ * x * g ∈ A) : A' = MulAut.conj g • A := by
  ext x; rw [h, mem_conj_smul_iff]

theorem conj_mem_zpowers {g R x : G} (hx : x ∈ Subgroup.zpowers R) :
    g⁻¹ * x * g ∈ Subgroup.zpowers (g⁻¹ * R * g) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [show g⁻¹ * R * g = MulAut.conj g⁻¹ R by simp, ← map_zpow]
  simp

variable [Finite G]

theorem ward_two_three
    (h : ReeTypeHyp G) (P : Sylow 3 G) :
    let Pg : Subgroup G := P
    let Z : Subgroup G := (Subgroup.center Pg).map Pg.subtype
    Nat.card Pg = h.q ^ 3 ∧
    (∀ g : G, Pg ⊓ (MulAut.conj g • Pg) = ⊥ ∨ Pg ⊓ (MulAut.conj g • Pg) = Pg) ∧
    IsElementaryAbelian 3 Z ∧ Nat.card Z = h.q ∧
    ∃ P₁ W : Subgroup G,
      P₁ ≤ Pg ∧ Pg ≤ Subgroup.normalizer (P₁ : Set G) ∧ IsElementaryAbelian 3 P₁ ∧
      Nat.card P₁ = h.q ^ 2 ∧ Z ≤ P₁ ∧
      (∀ x ∈ P₁, x ∉ Z → Pg ⊓ Subgroup.centralizer ({x} : Set G) = P₁) ∧
      IsCyclic W ∧ Nat.card W = h.q - 1 ∧ Pg ⊓ W = ⊥ ∧
      Subgroup.normalizer (Pg : Set G) = Pg ⊔ W ∧
      (∀ t ∈ W, orderOf t = 2 →
        Pg ⊓ Subgroup.centralizer ({t} : Set G) = P₁ ⊓ Subgroup.centralizer ({t} : Set G) ∧
        IsElementaryAbelian 3 (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ∧
        Nat.card (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = h.q ∧
        Pg ⊓ Subgroup.centralizer ({t} : Set G) ⊓ Z = ⊥) ∧
      ∀ R ∈ W, orderOf R = (h.q - 1) / 2 → ∀ R'' ∈ Subgroup.zpowers R, R'' ≠ 1 →
        Pg ⊓ Subgroup.centralizer ({R''} : Set G) = ⊥ := by
  intro Pg Z
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨⟨k, hk, hq⟩, hG⟩ := ward_order h
  have : CharP h.F 3 := ree_charP_three h hq
  obtain ⟨S, D, B, P₀, hP1P, hPc, hPn, hN1c⟩ := exists_data h hq hG
  obtain ⟨g, hQ⟩ := exists_conj_of_sylow hq hG hPc P
  have hK := h.card_F
  have hcT := B.hcT hq hK hG
  have hA := B.card_AA hq hK hG
  have hC1 : ∀ x : G, Odd (orderOf x) → 3 ∣ orderOf x →
      Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * h.q ^ 3 :=
    fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3
  have hZ0 := zcen_eq_CC hq hK hcT hG hA hP1P hPc hPn
  have hN0 := normalizer_eq_NN1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c
  have hq3 : 3 ≤ h.q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hZmem : ∀ z, z ∈ Z ↔ g⁻¹ * z * g ∈ CC S hq hK hcT hG := fun z => by
    rw [← hZ0]; exact mem_zcen_conj hQ
  have hCC1 : ∀ {x}, x ∈ CC S hq hK hcT hG → x ∈ PP1 S := fun hx => hx.1
  set P₁ : Subgroup G := MulAut.conj g • PP1 S with hP₁
  set W : Subgroup G := MulAut.conj g • WW S with hW
  have hP₁mem : ∀ x, x ∈ P₁ ↔ g⁻¹ * x * g ∈ PP1 S := fun x => mem_conj_smul_iff
  have hWmem : ∀ x, x ∈ W ↔ g⁻¹ * x * g ∈ WW S := fun x => mem_conj_smul_iff
  have hconj_mul : ∀ x y : G, g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := fun x y => by
    group
  have hconj_inj : ∀ x y : G, g⁻¹ * x * g = g⁻¹ * y * g → x = y := fun x y hxy => by
    have := congrArg (fun t => g * t * g⁻¹) hxy
    simpa [mul_assoc] using this
  have hconj_one : ∀ x : G, g⁻¹ * x * g = 1 ↔ x = 1 := fun x =>
    ⟨fun h1 => hconj_inj x 1 (by rw [h1]; group), fun h1 => by rw [h1]; group⟩
  have hconj_pow : ∀ x : G, ∀ n : ℕ, g⁻¹ * x ^ n * g = (g⁻¹ * x * g) ^ n := fun x n => by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, ← map_pow]
    simp
  have helem : ∀ {A A' : Subgroup G}, (∀ x, x ∈ A' ↔ g⁻¹ * x * g ∈ A) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 3 = 1) → IsElementaryAbelian 3 A' := by
    intro A A' hAA' hcomm hpow
    refine isElementaryAbelian_three (fun x hx y hy => ?_) (fun x hx => ?_)
    · apply hconj_inj
      rw [hconj_mul, hconj_mul]
      exact hcomm _ ((hAA' x).mp hx) _ ((hAA' y).mp hy)
    · rw [← hconj_one, hconj_pow]
      exact hpow _ ((hAA' x).mp hx)
  refine ⟨card_sylow3 hq hG P, B.inf_conj hq hK hG hP1P hPc hPn hN1c hQ, ?_, ?_, P₁, W,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact helem hZmem (fun x hx y hy => PP1_comm hq hK hcT hG (hCC1 hx) (hCC1 hy))
      (fun x hx => PP1_pow_three hq hK hcT hG (hCC1 hx))
  ·
    rw [conj_eq_smul hZmem, card_conj_smul, card_CC hq hK hcT hG hA]
  ·
    intro x hx
    rw [hQ]; exact hP1P ((hP₁mem x).mp hx)
  ·
    intro p hp
    have hp0 : g⁻¹ * p * g ∈ Subgroup.normalizer (P₀ : Set G) :=
      Subgroup.le_normalizer ((hQ p).mp hp)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hP₁mem, hP₁mem, hconj_mul, hconj_mul,
      show g⁻¹ * p⁻¹ * g = (g⁻¹ * p * g)⁻¹ by group]
    constructor
    · intro hy
      exact conj_mem_PP1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c hp0 hy
    · intro hy
      have := conj_mem_PP1 hq hK hcT hG hA hC1 hP1P hPc hPn hN1c (Subgroup.inv_mem _ hp0) hy
      simpa [mul_assoc] using this
  ·
    exact helem hP₁mem (fun x hx y hy => PP1_comm hq hK hcT hG hx hy)
      (fun x hx => PP1_pow_three hq hK hcT hG hx)
  ·
    rw [card_conj_smul, card_PP1 hq hK hcT hG]
  ·
    intro z hz
    rw [hP₁mem]; exact hCC1 ((hZmem z).mp hz)
  ·
    intro x hx hxZ
    have hx0 := (hP₁mem x).mp hx
    have hxZ0 : g⁻¹ * x * g ∉ zcen P₀ := by
      rw [hZ0]; exact fun h' => hxZ ((hZmem x).mpr h')
    have heq := B.inf_centralizer_PP1 hq hK hG hP1P hPc hPn hx0 hxZ0
    ext y
    rw [hP₁mem, ← heq, Subgroup.mem_inf, Subgroup.mem_inf, hQ, mem_centralizer_conj (g := g)]
  ·
    have : IsCyclic (WW S) := by rw [WW]; infer_instance
    exact isCyclic_of_surjective (Subgroup.equivSMul (MulAut.conj g) (WW S)).toMonoidHom
      (MulEquiv.surjective _)
  ·
    rw [card_conj_smul, card_WW hq hK]
  ·
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
      rw [card_sylow3 hq hG P, card_conj_smul, card_WW hq hK]; exact coprime_q3 hq))
  ·
    symm
    refine sup_eq_normalizer ?_ ?_ ?_
    · intro w hw
      rw [Block.mem_normalizer_Q hQ]
      exact WW_le_normalizer hq hK hcT hG hA hC1 hP1P hPc hPn hN1c ((hWmem w).mp hw)
    · rw [card_sylow3 hq hG P, card_conj_smul, card_WW hq hK]; exact coprime_q3 hq
    · rw [B.card_normalizer_Q_eq hq hK hG hP1P hPc hPn hN1c hQ, card_sylow3 hq hG P,
        card_conj_smul, card_WW hq hK]
  ·
    intro t ht ht2
    have ht0 := (hWmem t).mp ht
    have htJ : g⁻¹ * t * g = S.J := by
      have h2 : (g⁻¹ * t * g) ^ 2 = 1 := by
        rw [← hconj_pow, ← ht2, pow_orderOf_eq_one]; group
      rcases WW_sq_eq_one hq hK ht0 h2 with h1 | h1
      · exfalso
        rw [hconj_one] at h1
        rw [h1, orderOf_one] at ht2
        omega
      · exact h1
    have hF0 : P₀ ⊓ Subgroup.centralizer ({S.J} : Set G) = FF S :=
      inf_centralizer_J hq hK hcT hP1P hPc
    have hF1 : PP1 S ⊓ Subgroup.centralizer ({S.J} : Set G) = FF S := by
      apply le_antisymm
      · intro x hx
        exact mem_FF_of_PP1_comm_J hq hK hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
      · intro x hx
        exact ⟨FF_le_PP1 hq hcT hx, Subgroup.mem_centralizer_singleton_iff.mpr (FF_comm_J hx)⟩
    have hmemP : ∀ y, y ∈ Pg ⊓ Subgroup.centralizer ({t} : Set G) ↔ g⁻¹ * y * g ∈ FF S := by
      intro y
      rw [← hF0, Subgroup.mem_inf, Subgroup.mem_inf, hQ, mem_centralizer_conj (g := g), htJ]
    have hmemP₁ : ∀ y, y ∈ P₁ ⊓ Subgroup.centralizer ({t} : Set G) ↔ g⁻¹ * y * g ∈ FF S := by
      intro y
      rw [← hF1, Subgroup.mem_inf, Subgroup.mem_inf, hP₁mem, mem_centralizer_conj (g := g), htJ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext y; rw [hmemP, hmemP₁]
    · exact helem hmemP (fun x hx y hy => FF_comm hx hy) (fun x hx => FF_pow_three hx)
    · rw [conj_eq_smul hmemP, card_conj_smul, card_FF, hK]
    · rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_bot, ← hconj_one]
      exact CC_inf_FF hq hK hcT hG ((hZmem y).mp hy2) ((hmemP y).mp hy1)
  ·
    intro R hR hRo R'' hR'' hR''1
    have hR0 := (hWmem R).mp hR
    obtain ⟨k', hk', hodd⟩ := Block.q_half hq
    have hRodd : Odd (orderOf (g⁻¹ * R * g)) := by
      rw [orderOf_conj', hRo, show (h.q - 1) / 2 = k' by omega]; exact hodd
    have hRR : g⁻¹ * R * g ∈ RR S := mem_RR_of_mem_WW hR0 hRodd
    have hR''0 : g⁻¹ * R'' * g ∈ RR S :=
      (Subgroup.zpowers_le.mpr hRR) (conj_mem_zpowers hR'')
    have hbot := inf_centralizer_RR hq hK hPc hR''0 (fun h1 => hR''1 ((hconj_one R'').mp h1))
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    have : g⁻¹ * y * g ∈ P₀ ⊓ Subgroup.centralizer ({g⁻¹ * R'' * g} : Set G) :=
      ⟨(hQ y).mp hy1, (mem_centralizer_conj (g := g)).mp hy2⟩
    rw [hbot, Subgroup.mem_bot, hconj_one] at this
    rw [Subgroup.mem_bot]; exact this

theorem ward_five
    (h : ReeTypeHyp G) (P : Sylow 3 G) :
    FaithfulSMul G (G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
    MulAction.IsMultiplyPretransitive G (G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G)) 2 ∧
    (∀ a b c : G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G), a ≠ b → a ≠ c → b ≠ c →
      Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
        MulAction.stabilizer G c : Subgroup G) ≤ 2) ∧
    ∃ a b c : G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
        MulAction.stabilizer G c : Subgroup G) = 2 := by
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨⟨k, hk, hq⟩, hG⟩ := ward_order h
  have : CharP h.F 3 := ree_charP_three h hq
  obtain ⟨S, D, B, P₀, hP1P, hPc, hPn, hN1c⟩ := exists_data h hq hG
  obtain ⟨g, hQ⟩ := exists_conj_of_sylow hq hG hPc P
  have hK := h.card_F
  exact ⟨B.faithfulSMul hq hK hG hP1P hPc hPn hN1c hQ,
    B.isMultiplyPretransitive hq hK hG hP1P hPc hPn hN1c hQ,
    B.card_stabilizer_three_le hq hK hG hP1P hPc hPn hN1c hQ,
    B.exists_card_stabilizer_three_eq hq hK hG hP1P hPc hPn hN1c hQ⟩

theorem ward_doubly_transitive_sylow
    (h : ReeTypeHyp G) :
    MulAction.IsMultiplyPretransitive G (Sylow 3 G) 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h2 := (ward_five h P).2.1
  rw [MulAction.is_two_pretransitive_iff] at h2 ⊢
  intro A B C D hAB hCD
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G P A
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G P B
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq G P C
  obtain ⟨d, rfl⟩ := MulAction.exists_smul_eq G P D
  have hcoset : ∀ x y : G, x • P ≠ y • P →
      (x : G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G)) ≠ y := by
    intro x y hxy hc
    apply hxy
    have hmem : (x⁻¹ * y) • P = P :=
      (Sylow.smul_eq_iff_mem_normalizer (P := P)).mpr (QuotientGroup.eq.mp hc)
    calc x • P = x • ((x⁻¹ * y) • P) := by rw [hmem]
      _ = y • P := by rw [smul_smul, mul_inv_cancel_left]
  obtain ⟨g, hga, hgb⟩ := h2 (hcoset a b hAB) (hcoset c d hCD)
  have hmove : ∀ x y : G, g • (x : G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G)) = y →
      g • x • P = y • P := by
    intro x y hxy
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hxy
    have hxy' : ((g * x)⁻¹ * y) • P = P := (Sylow.smul_eq_iff_mem_normalizer (P := P)).mpr hxy
    calc g • x • P = (g * x) • P := by rw [smul_smul]
      _ = (g * x) • (((g * x)⁻¹ * y) • P) := by rw [hxy']
      _ = y • P := by rw [smul_smul, mul_inv_cancel_left]
  exact ⟨g, hmove a c hga, hmove b d hgb⟩

end CFSG.Walter.WardLocal
