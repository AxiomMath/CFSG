module

public import CFSG.Walter.ReeOrder.WardLocal.Class3
public import CFSG.Walter.ReeOrder.WardLocal.Statements

public section

open scoped BigOperators Classical MatrixGroups Pointwise commutatorElement

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

section General

variable {G : Type} [Group G]

theorem map_commutator_subtype (H : Subgroup G) : (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem conj_smul_commutator (g : G) (A B : Subgroup G) :
    MulAut.conj g • ⁅A, B⁆ = ⁅MulAut.conj g • A, MulAut.conj g • B⁆ := by
  simp only [Subgroup.pointwise_smul_def]
  exact Subgroup.map_commutator A B _

theorem conj_smul_zpowers (g x : G) :
    MulAut.conj g • Subgroup.zpowers x = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [Subgroup.pointwise_smul_def]
  exact MonoidHom.map_zpowers _ x

theorem mem_upperCentralSeries_two {H : Subgroup G} {x : G} :
    x ∈ (Subgroup.upperCentralSeries H 2).map H.subtype ↔
      x ∈ H ∧ ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ (Subgroup.center H).map H.subtype := by
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨u.2, fun y hy => ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff] at hu
    have := hu ⟨y, hy⟩
    rw [Subgroup.upperCentralSeries_one] at this
    exact Subgroup.mem_map.mpr ⟨_, this, rfl⟩
  · rintro ⟨hx, h⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    obtain ⟨c, hc, hce⟩ := h y y.2
    have : ⁅(⟨x, hx⟩ : H), y⁆ = c := Subtype.ext hce.symm
    rw [this]; exact hc

theorem nilpotencyClass_eq_three {H : Type*} [Group H] [Group.IsNilpotent H]
    (h3 : Subgroup.upperCentralSeries H 3 = ⊤) (h2 : Subgroup.upperCentralSeries H 2 ≠ ⊤) :
    Group.nilpotencyClass H = 3 := by
  have hle := Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp h3
  have hnot : ¬ Group.nilpotencyClass H ≤ 2 := fun h =>
    h2 (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h)
  omega

end General

variable {G : Type} [Group G] [Finite G]

theorem ward_two
    (h : ReeTypeHyp G) (P : Sylow 3 G) :
    let Pg : Subgroup G := P
    let Z : Subgroup G := (Subgroup.center Pg).map Pg.subtype
    let P₁ : Subgroup G := (commutator Pg).map Pg.subtype
    Nat.card Pg = h.q ^ 3 ∧
    (∀ g : G, Pg ⊓ (MulAut.conj g • Pg) = ⊥ ∨ Pg ⊓ (MulAut.conj g • Pg) = Pg) ∧
    IsElementaryAbelian 3 Z ∧ Nat.card Z = h.q ∧
    Group.nilpotencyClass Pg = 3 ∧
    P₁ = ⁅Pg, Pg⁆ ∧ P₁ = (frattini Pg).map Pg.subtype ∧
    P₁ = (Subgroup.upperCentralSeries Pg 2).map Pg.subtype ∧
    P₁ = Subgroup.closure {x : G | x ∈ Pg ∧ x ^ 3 = 1} ∧
    ⁅P₁, Pg⁆ = Z ∧
    Pg ≤ Subgroup.normalizer (P₁ : Set G) ∧ IsElementaryAbelian 3 P₁ ∧
    Nat.card P₁ = h.q ^ 2 ∧ Z ≤ P₁ ∧
    (∀ x ∈ P₁, x ∉ Z → Pg ⊓ Subgroup.centralizer ({x} : Set G) = P₁) ∧
    (∀ x ∈ Pg, x ∉ P₁ → orderOf x = 9 ∧
      Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ Z ∧
      Pg ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ Z) ∧
    (fun x : G => x ^ 3) '' {x : G | x ∈ Pg ∧ x ∉ P₁} = {z : G | z ∈ Z ∧ z ≠ 1} ∧
    ∃ W : Subgroup G, IsCyclic W ∧ Nat.card W = h.q - 1 ∧ Pg ⊓ W = ⊥ ∧
      Subgroup.normalizer (Pg : Set G) = Pg ⊔ W ∧
      (∀ t ∈ W, orderOf t = 2 →
        Pg ⊓ Subgroup.centralizer ({t} : Set G) = P₁ ⊓ Subgroup.centralizer ({t} : Set G) ∧
        IsElementaryAbelian 3 (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ∧
        Nat.card (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = h.q ∧
        Z ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ ∧
        P₁ = Z ⊔ (Pg ⊓ Subgroup.centralizer ({t} : Set G))) ∧
      ∀ R ∈ W, orderOf R = (h.q - 1) / 2 → ∀ R'' ∈ Subgroup.zpowers R, R'' ≠ 1 →
        Pg ⊓ Subgroup.centralizer ({R''} : Set G) = ⊥ := by
  intro Pg Z P₁
  let _ : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  have hm : h.q = 3 * (3 ^ k) ^ 2 := by rw [hq, ← pow_mul, ← pow_succ']; ring_nf
  have hZ0 := zcen_eq_CC hq hK hcT hG hA hP1P hPc hPn
  have hq27 : 27 ≤ h.q := S.q_ge
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
  have hconj_comm : ∀ x y : G, g⁻¹ * (x * y * x⁻¹ * y⁻¹) * g =
      (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g)⁻¹ := fun x y => by group
  have hback : ∀ x : G, g⁻¹ * (g * x * g⁻¹) * g = x := fun x => by group
  have hZmem : ∀ z, z ∈ Z ↔ g⁻¹ * z * g ∈ zcen P₀ := fun z => mem_zcen_conj hQ
  have hPg : Pg = MulAut.conj g • P₀ := conj_eq_smul hQ
  have hZsmul : Z = MulAut.conj g • zcen P₀ := conj_eq_smul hZmem
  have hP₁ : P₁ = MulAut.conj g • PP1 S := by
    show (commutator Pg).map Pg.subtype = _
    rw [map_commutator_subtype, hPg, ← conj_smul_commutator,
      B.commutator_eq_PP1 hq hK hG hP1P hPc hPn hN1c hm]
  have hP₁mem : ∀ x, x ∈ P₁ ↔ g⁻¹ * x * g ∈ PP1 S := fun x => by
    rw [hP₁]; exact mem_conj_smul_iff
  have hP₁le : P₁ ≤ Pg := fun x hx => (hQ x).mpr (hP1P ((hP₁mem x).mp hx))
  have hZle : Z ≤ Pg := fun z hz => (hQ z).mpr (mem_zcen.mp ((hZmem z).mp hz)).1
  have h6 : P₁ = ⁅Pg, Pg⁆ := map_commutator_subtype Pg
  have h10 : ⁅P₁, Pg⁆ = Z := by
    rw [hZsmul, hP₁, hPg, ← conj_smul_commutator,
      B.commutator_PP1_eq_zcen hq hK hG hP1P hPc hPn]
  have hout : ∀ x ∈ Pg, x ∉ P₁ → g⁻¹ * x * g ∈ P₀ ∧ g⁻¹ * x * g ∉ PP1 S := fun x hx hxP1 =>
    ⟨(hQ x).mp hx, fun h' => hxP1 ((hP₁mem x).mpr h')⟩
  have hcube_ne : ∀ x ∈ Pg, x ∉ P₁ → x ^ 3 ≠ 1 := fun x hx hxP1 h3 => by
    obtain ⟨hx0, hx0P1⟩ := hout x hx hxP1
    apply B.cube_ne_one_outer hq hK hG hP1P hPc hPn hN1c hm hx0 hx0P1
    rw [← hconj_pow, h3]; group
  have h8 : P₁ = (Subgroup.upperCentralSeries Pg 2).map Pg.subtype := by
    ext x
    rw [mem_upperCentralSeries_two]
    constructor
    · intro hx
      refine ⟨hP₁le hx, fun y hy => ?_⟩
      have := Subgroup.commutator_mem_commutator hx hy
      rw [h10] at this
      exact this
    · rintro ⟨hx, hxc⟩
      by_contra hxP1
      obtain ⟨hx0, hx0P1⟩ := hout x hx hxP1
      obtain ⟨g₀, hg₀, hg₀x⟩ :=
        B.exists_comm_not_mem_zcen hq hK hG hP1P hPc hPn hN1c hm hx0 hx0P1
      have hy : g * g₀ * g⁻¹ ∈ Pg := (hQ _).mpr (by rw [hback]; exact hg₀)
      have h1 := (hZmem _).mp (hxc _ hy)
      rw [hconj_comm, hback] at h1
      apply hg₀x
      have := (zcen P₀).inv_mem h1
      rwa [show ((g⁻¹ * x * g) * g₀ * (g⁻¹ * x * g)⁻¹ * g₀⁻¹)⁻¹ =
        g₀ * (g⁻¹ * x * g) * g₀⁻¹ * (g⁻¹ * x * g)⁻¹ by group] at this
  have hPp : IsPGroup 3 Pg := IsPGroup.of_card (n := 3 * (2 * k + 1))
    (by rw [card_sylow3 hq hG P, hq, ← pow_mul, mul_comm])
  have hP₁ne : P₁ ≠ Pg := by
    intro heq
    have h1 : Nat.card P₁ = h.q ^ 2 := by rw [hP₁, card_conj_smul, card_PP1 hq hK hcT hG]
    rw [heq, card_sylow3 hq hG P] at h1
    have : h.q ^ 2 < h.q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  refine ⟨card_sylow3 hq hG P, B.inf_conj hq hK hG hP1P hPc hPn hN1c hQ, ?_, ?_, ?_, h6, ?_, h8,
    ?_, h10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine isElementaryAbelian_three (fun x hx y hy => (mem_zcen.mp hx).2 y (hZle hy))
      (fun x hx => ?_)
    rw [← hconj_one, hconj_pow]
    exact PP1_pow_three hq hK hcT hG (B.zcen_le_PP1 hq hK hG hP1P hPc hPn ((hZmem x).mp hx))
  ·
    rw [hZsmul, card_conj_smul, B.card_zcen hq hK hG hP1P hPc hPn]
  ·
    have : Group.IsNilpotent Pg := hPp.isNilpotent
    apply nilpotencyClass_eq_three
    · rw [eq_top_iff]
      intro u _
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro v
      rw [← Subgroup.mem_map_iff_mem Pg.subtype_injective, ← h8, h6]
      exact Subgroup.commutator_mem_commutator u.2 v.2
    · intro htop
      apply hP₁ne
      rw [h8, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  ·
    have : Fact (IsPGroup 3 Pg) := ⟨hPp⟩
    rw [frattini_eq_closure_commutator_union_powers (p := 3), MonoidHom.map_closure,
      Set.image_union]
    apply le_antisymm
    · intro x hx
      exact Subgroup.subset_closure (Or.inl hx)
    · rw [Subgroup.closure_le]
      rintro _ (⟨c, hc, rfl⟩ | ⟨y, ⟨u, rfl⟩, rfl⟩)
      · exact ⟨c, hc, rfl⟩
      · show Pg.subtype (u ^ 3) ∈ (P₁ : Set G)
        refine (hP₁mem _).mpr ?_
        show g⁻¹ * (u : G) ^ 3 * g ∈ PP1 S
        rw [hconj_pow]
        exact B.cube_mem_PP1 hq hK hG hP1P hPc hPn hN1c ((hQ u).mp u.2)
  ·
    apply le_antisymm
    · intro x hx
      refine Subgroup.subset_closure ⟨hP₁le hx, ?_⟩
      rw [← hconj_one, hconj_pow]
      exact PP1_pow_three hq hK hcT hG ((hP₁mem x).mp hx)
    · rw [Subgroup.closure_le]
      rintro x ⟨hx, hx3⟩
      by_contra hxP1
      exact hcube_ne x hx hxP1 hx3
  ·
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcm : ∀ a ∈ Pg, ∀ b ∈ Pg, a * b * a⁻¹ * b⁻¹ ∈ P₁ := fun a ha b hb => by
      rw [h6]; exact Subgroup.commutator_mem_commutator ha hb
    constructor
    · intro hy
      have e : p * y * p⁻¹ = (p * y * p⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact P₁.mul_mem (hcm p hp y (hP₁le hy)) hy
    · intro hy
      have hyP : y ∈ Pg := by
        have e : y = p⁻¹ * (p * y * p⁻¹) * p := by group
        rw [e]
        exact Pg.mul_mem (Pg.mul_mem (Pg.inv_mem hp) (hP₁le hy)) hp
      have e : y = (y * p * y⁻¹ * p⁻¹) * (p * y * p⁻¹) := by group
      rw [e]
      exact P₁.mul_mem (hcm y hyP p hp) hy
  ·
    refine isElementaryAbelian_three (fun x hx y hy => ?_) (fun x hx => ?_)
    · apply hconj_inj
      rw [hconj_mul, hconj_mul]
      exact PP1_comm hq hK hcT hG ((hP₁mem x).mp hx) ((hP₁mem y).mp hy)
    · rw [← hconj_one, hconj_pow]
      exact PP1_pow_three hq hK hcT hG ((hP₁mem x).mp hx)
  ·
    rw [hP₁, card_conj_smul, card_PP1 hq hK hcT hG]
  ·
    intro z hz
    rw [hP₁mem]
    exact B.zcen_le_PP1 hq hK hG hP1P hPc hPn ((hZmem z).mp hz)
  ·
    intro x hx hxZ
    have hx0 := (hP₁mem x).mp hx
    have hxZ0 : g⁻¹ * x * g ∉ zcen P₀ := fun h' => hxZ ((hZmem x).mpr h')
    have heq := B.inf_centralizer_PP1 hq hK hG hP1P hPc hPn hx0 hxZ0
    ext y
    rw [hP₁mem, ← heq, Subgroup.mem_inf, Subgroup.mem_inf, hQ, mem_centralizer_conj (g := g)]
  ·
    intro x hx hxP1
    obtain ⟨hx0, hx0P1⟩ := hout x hx hxP1
    have hC : Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ Z := by
      have hc0 := B.centralizer_outer hq hK hG hP1P hPc hPn hN1c hm hx0 hx0P1
      have hCx : Subgroup.centralizer ({x} : Set G) =
          MulAut.conj g • Subgroup.centralizer ({g⁻¹ * x * g} : Set G) :=
        conj_eq_smul fun y => mem_centralizer_conj
      rw [hCx, hc0, Subgroup.smul_sup, conj_smul_zpowers, ← hZsmul]
      congr 2
      group
    refine ⟨?_, hC, ?_⟩
    · rw [← orderOf_conj' g x]
      exact B.orderOf_outer hq hK hG hP1P hPc hPn hN1c hm hx0 hx0P1
    · rw [hC]
      exact inf_eq_right.mpr (sup_le (Subgroup.zpowers_le.mpr hx) hZle)
  ·
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hxP1⟩, rfl⟩
      obtain ⟨hx0, hx0P1⟩ := hout x hx hxP1
      refine ⟨(hZmem _).mpr ?_, hcube_ne x hx hxP1⟩
      rw [hconj_pow]
      exact B.cube_mem_zcen hq hK hG hP1P hPc hPn hN1c hx0 hx0P1
    · rintro ⟨hz, hz1⟩
      obtain ⟨x₀, hx₀, hx₀P1, hx₀z⟩ := B.exists_cube_eq hq hK hG hP1P hPc hPn hN1c hm
        ((hZmem z).mp hz) (fun h1 => hz1 ((hconj_one z).mp h1))
      refine ⟨g * x₀ * g⁻¹, ⟨(hQ _).mpr (by rw [hback]; exact hx₀),
        fun h' => hx₀P1 (by have := (hP₁mem _).mp h'; rwa [hback] at this)⟩, ?_⟩
      apply hconj_inj
      simp only
      rw [hconj_pow, hback, hx₀z]
  ·
    set W : Subgroup G := MulAut.conj g • WW S with hW
    have hWmem : ∀ x, x ∈ W ↔ g⁻¹ * x * g ∈ WW S := fun x => mem_conj_smul_iff
    refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      have hmemP₁ : ∀ y, y ∈ P₁ ⊓ Subgroup.centralizer ({t} : Set G) ↔
          g⁻¹ * y * g ∈ FF S := by
        intro y
        rw [← hF1, Subgroup.mem_inf, Subgroup.mem_inf, hP₁mem, mem_centralizer_conj (g := g), htJ]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · ext y; rw [hmemP, hmemP₁]
      · exact isElementaryAbelian_three (fun x hx y hy => hconj_inj _ _ (by
          rw [hconj_mul, hconj_mul]; exact FF_comm ((hmemP x).mp hx) ((hmemP y).mp hy)))
          (fun x hx => by
            rw [← hconj_one, hconj_pow]; exact FF_pow_three ((hmemP x).mp hx))
      · rw [conj_eq_smul hmemP, card_conj_smul, card_FF, hK]
      · rw [eq_bot_iff]
        intro y hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        rw [Subgroup.mem_bot, ← hconj_one]
        have hyF : g⁻¹ * y * g ∈ FF S := (hmemP y).mp ⟨hZle hy1, hy2⟩
        have hyC : g⁻¹ * y * g ∈ CC S hq hK hcT hG := by rw [← hZ0]; exact (hZmem y).mp hy1
        exact CC_inf_FF hq hK hcT hG hyC hyF
      · rw [hP₁, B.PP1_eq_sup hq hK hG hP1P hPc hPn, Subgroup.smul_sup, ← hZsmul,
          ← conj_eq_smul hmemP]
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

end CFSG.Walter.WardLocal
