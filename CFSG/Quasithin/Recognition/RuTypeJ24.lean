module

public import CFSG.Quasithin.Recognition.RuTypeJ23d
public import CFSG.Quasithin.Recognition.RuTypeJ22c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace Sigma

theorem right_eq_one_of_pow_three : ∀ g : SigmaL2F4, g ^ 3 = 1 → g.right = 1 := by
  decide +kernel

end Sigma

namespace SL3

theorem isRow0_of_fix_two : ∀ g ∈ R0, g ≠ 1 → ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A.trace = 0 → (stAct g A = A ∧ stAct (b0 * g * b0⁻¹) A = A) → IsRow0 A := by
  decide +kernel

end SL3

namespace RuDataM

variable (M : RuDataM G) [Finite G]

abbrev commQ (h : G) : Subgroup G :=
  Subgroup.closure {x | ∃ q ∈ ruQ M.T, x = ⁅h, q⁆}

abbrev HB : Subgroup G := ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)

theorem mem_HB {x : G} : x ∈ M.HB ↔ x ∈ ruS M.L ∧ (M.bel : G) * x = x * M.bel := by
  show x ∈ ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G) ↔ _
  rw [M.centralizer_Q_eq, Subgroup.mem_inf, M.mem_centralizer_B]

theorem HB_le_HC : M.HB ≤ M.HC := fun _ hx =>
  M.centralizer_Q_le_HC (Subgroup.mem_inf.mp hx).1 ((M.mem_centralizer_B).mp
    (Subgroup.mem_inf.mp hx).2)

theorem bel_mem_K : (M.bel : G) ∈ M.K := by
  refine M.mem_K_iff.mpr ⟨M.bel_mem_H, Sigma.right_eq_one_of_pow_three _ M.φ_bel.1⟩

theorem exists_HB_U {h : G} (hh : h ∈ M.HC) : ∃ x ∈ M.HB, ∃ u ∈ ruU M.L M.T, h = x * u := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hhH : h ∈ ruH M.T := (Subgroup.mem_inf.mp hh).1
  have hbU : ∀ u ∈ ruU M.L M.T, (M.bel : G) * u * (M.bel : G)⁻¹ ∈ ruU M.L M.T := fun u hu =>
    M.conj_mem_U M.bel_mem_H hu
  have hc := M.comm_K_HC M.bel_mem_K h hh
  have hy : h⁻¹ * ((M.bel : G) * h * (M.bel : G)⁻¹) ∈ ruU M.L M.T := by
    have e : h⁻¹ * ((M.bel : G) * h * (M.bel : G)⁻¹) =
        h⁻¹ * ((M.bel : G) * h * (M.bel : G)⁻¹ * h⁻¹) * h := by group
    rw [e]
    have := M.conj_mem_U (inv_mem hhH) hc
    simpa using this
  have hU3 : ¬ 3 ∣ Nat.card (ruU M.L M.T) := by rw [M.toRuData.card_U]; norm_num
  obtain ⟨u, hu, hfix⟩ := exists_fixed_mem_coset M.bel_pow_three hbU hy hU3
  have hhu : h * u ∈ M.HC := mul_mem hh (M.U_le_HC hu)
  refine ⟨h * u, ?_, u⁻¹, inv_mem hu, by group⟩
  refine ⟨M.HC_le_Q hhu, (M.mem_centralizer_B).mpr ?_⟩
  calc (M.bel : G) * (h * u) = (M.bel : G) * (h * u) * (M.bel : G)⁻¹ * M.bel := by group
    _ = h * u * M.bel := by rw [hfix]

theorem cform_fixB0_mem {A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsFixB0 A)
    (hA' : IsFixB0 A') : M.cform A A' = 0 ∨ M.cform A A' = SL3.e0 := by
  obtain ⟨hAt, hAb⟩ := IsFixB0.props A hA
  obtain ⟨hA't, hA'b⟩ := IsFixB0.props A' hA'
  have := M.cform_stAct hAt hA't M.bel
  rw [M.θ_bel, hAb, hA'b] at this
  exact SL3.b0_fix_vec _ this.symm

theorem cform_b0_b0sq : M.cform !![1, 0, 0; 0, 0, 1; 0, 1, 1] !![1, 0, 0; 0, 1, 1; 0, 1, 0] =
    SL3.e0 := by
  rcases M.cform_fixB0_mem (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) with
    h | h
  · exfalso
    obtain ⟨t1, ht1, hb1, hχ1⟩ := M.exists_t1
    obtain ⟨t2, ht2, -, hχ2⟩ := M.exists_t2
    apply M.t1_t2_not_comm ht1 hb1 hχ1 ht2 hχ2
    have := (M.comm_eq_one_iff_cform ⟨t1, ht1⟩ ⟨t2, ht2⟩).mpr (by rw [hχ1, hχ2]; exact h)
    calc t1 * t2 = t1 * t2 * t1⁻¹ * t2⁻¹ * (t2 * t1) := by group
      _ = t2 * t1 := by rw [show t1 * t2 * t1⁻¹ * t2⁻¹ = 1 from this, one_mul]
  · exact h

theorem cform_fixB0 {A A' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsFixB0 A)
    (hA' : IsFixB0 A') :
    M.cform A A' = if A = 0 ∨ A' = 0 ∨ A = A' then 0 else SL3.e0 := by
  have h12 := M.cform_b0_b0sq
  have t1 : IsTraceZero (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    unfold IsTraceZero; decide
  have t2 : IsTraceZero (!![1, 0, 0; 0, 1, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    unfold IsTraceZero; decide
  have hD : (!![0, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 1] + !![1, 0, 0; 0, 1, 1; 0, 1, 0] := by decide
  have h21 : M.cform !![1, 0, 0; 0, 1, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 0, 1, 1] = SL3.e0 := by
    rw [M.cform_comm t1 t2, h12]
  have hz : ∀ A, IsTraceZero A → M.cform 0 A = 0 := fun A hA => by
    rw [← M.cform_comm (by unfold IsTraceZero; simp) hA]
    exact M.cform_zero hA
  have hss := M.cform_self
  have hDl : ∀ B, IsTraceZero B → M.cform (!![0, 0, 0; 0, 1, 0; 0, 0, 1]) B =
      M.cform !![1, 0, 0; 0, 0, 1; 0, 1, 1] B + M.cform !![1, 0, 0; 0, 1, 1; 0, 1, 0] B :=
    fun B hB => by rw [hD, M.cform_add_left t1 t2 hB]
  have hDr : ∀ B, IsTraceZero B → M.cform B (!![0, 0, 0; 0, 1, 0; 0, 0, 1]) =
      M.cform B !![1, 0, 0; 0, 0, 1; 0, 1, 1] + M.cform B !![1, 0, 0; 0, 1, 1; 0, 1, 0] :=
    fun B hB => by rw [hD, M.cform_add_right hB t1 t2]
  have he : SL3.e0 + SL3.e0 = 0 := by decide
  rcases hA with rfl | rfl | rfl | rfl <;> rcases hA' with rfl | rfl | rfl | rfl
  all_goals first
    | (rw [ite_eq_left (by decide)]; first
        | exact hz _ (by unfold IsTraceZero; decide)
        | exact M.cform_zero (by unfold IsTraceZero; decide)
        | exact hss _)
    | (rw [ite_eq_right (by decide)]; first
        | exact h12
        | exact h21
        | (rw [hDl _ t1, hss, h21, zero_add])
        | (rw [hDl _ t2, hss, h12, add_zero])
        | (rw [hDr _ t1, hss, h12, zero_add])
        | (rw [hDr _ t2, hss, h21, add_zero]))

theorem comm_HB {x y : G} (hx : x ∈ M.HB) (hy : y ∈ M.HB) :
    (Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) =
        Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) → ⁅x, y⁆ = 1) ∧
    (¬ (Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) =
        Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩)) → ⁅x, y⁆ = M.z) := by
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  obtain ⟨hyS, hyb⟩ := M.mem_HB.mp hy
  have hf := M.cform_fixB0 (M.isFixB0_χ hxS hxb) (M.isFixB0_χ hyS hyb)
  have e := M.ψV_comm ⟨x, hxS⟩ ⟨y, hyS⟩
  constructor
  · intro hc
    rw [ite_eq_left hc] at hf
    rw [hf] at e
    have : M.ψV ⟨_, M.comm_mem_V hxS hyS⟩ = 1 := Multiplicative.toAdd.injective e
    have h1 := congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
    exact h1
  · intro hc
    rw [ite_eq_right hc, ← M.ψV_zV] at hf
    rw [hf] at e
    have := M.ψV.injective (Multiplicative.toAdd.injective e)
    exact congrArg Subtype.val this

theorem card_Q_inf_S : Nat.card ↥(ruQ M.T ⊓ ruS M.L) = 2 ^ 9 := by
  have hQL := M.Q_le_L
  let f : (ruQ M.T).subgroupOf M.L →* SL(3, ZMod 2) := M.θ.comp ((ruQ M.T).subgroupOf M.L).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hQL, M.toRuData.card_Q] at h
  have hrange : f.range = SL3.R0 := by
    rw [← M.θQ_eq]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(ruQ M.T ⊓ ruS M.L) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, Subgroup.mem_subgroupOf.mp x.1.2, ?_⟩
        invFun := fun y => ⟨⟨⟨y.1, hQL (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.θ.ker := hx
      rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show M.θ ⟨y.1, _⟩ = 1
      have : (⟨y.1, hQL (Subgroup.mem_inf.mp y.2).1⟩ : M.L) ∈ M.θ.ker := by
        rw [M.θ_ker, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).2
      exact this
  rw [hker, hrange, SL3.card_R0] at h
  omega

theorem centralizer_Q_le_S {h : G} (hh : h ∈ M.HB) (hU : h ∉ ruU M.L M.T) {x : G}
    (hx : x ∈ ruQ M.T) (hxh : x * h = h * x) : x ∈ ruS M.L := by
  obtain ⟨hhS, hhb⟩ := M.mem_HB.mp hh
  by_contra hxS
  have hxL := M.Q_le_L hx
  have hθx : M.θ ⟨x, hxL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hθ1 : M.θ ⟨x, hxL⟩ ≠ 1 := fun h1 => hxS (by
    have : (⟨x, hxL⟩ : M.L) ∈ M.θ.ker := h1
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
    exact this)
  have hfix : ∀ l : M.L, (l : G) * h = h * l →
      stAct (M.θ l) (Multiplicative.toAdd (M.χ ⟨h, hhS⟩)) =
        Multiplicative.toAdd (M.χ ⟨h, hhS⟩) := by
    intro l hl
    have e := M.χ_equiv l ⟨h, hhS⟩ ⟨h, hhS⟩ (by
      show h = (l : G) * h * (l : G)⁻¹
      rw [hl, mul_inv_cancel_right])
    have := congrArg Multiplicative.toAdd e
    rw [toAdd_ofAdd] at this
    exact this.symm
  have h1 := hfix ⟨x, hxL⟩ hxh
  set y : M.L := M.bel * ⟨x, hxL⟩ * M.bel⁻¹
  have hyh : (y : G) * h = h * y := by
    have hbh : (M.bel : G)⁻¹ * h = h * (M.bel : G)⁻¹ := by
      calc (M.bel : G)⁻¹ * h = (M.bel : G)⁻¹ * (h * M.bel) * (M.bel : G)⁻¹ := by group
        _ = (M.bel : G)⁻¹ * (M.bel * h) * (M.bel : G)⁻¹ := by rw [hhb]
        _ = h * (M.bel : G)⁻¹ := by group
    show (M.bel : G) * x * (M.bel : G)⁻¹ * h = h * ((M.bel : G) * x * (M.bel : G)⁻¹)
    calc (M.bel : G) * x * (M.bel : G)⁻¹ * h = (M.bel : G) * x * ((M.bel : G)⁻¹ * h) := by group
      _ = (M.bel : G) * (x * h) * (M.bel : G)⁻¹ := by rw [hbh]; group
      _ = (M.bel : G) * (h * x) * (M.bel : G)⁻¹ := by rw [hxh]
      _ = (M.bel : G) * h * (x * (M.bel : G)⁻¹) := by group
      _ = h * ((M.bel : G) * x * (M.bel : G)⁻¹) := by rw [hhb]; group
  have h2 := hfix y hyh
  rw [show M.θ y = SL3.b0 * M.θ ⟨x, hxL⟩ * SL3.b0⁻¹ by
    simp only [y, map_mul, map_inv, M.θ_bel]] at h2
  have hrow := SL3.isRow0_of_fix_two _ hθx hθ1 _ (M.χ_trace _) ⟨h1, h2⟩
  exact hU ((M.mem_U_iff hhS).mpr hrow)

omit [Finite G] in
theorem comm_HC_Q_mem_U {h q : G} (hh : h ∈ M.HC) (hq : q ∈ ruQ M.T) : ⁅h, q⁆ ∈ ruU M.L M.T := by
  rw [commutatorElement_def]
  exact (M.two.QU_elem _ (M.HC_le_Q hh) q hq).1

@[expose] noncomputable def Fh (h : G) (hh : h ∈ M.HC) (q : ruQ M.T) : Fin 2 → F4 :=
  Multiplicative.toAdd (M.ψU ⟨_, M.comm_HC_Q_mem_U hh q.2⟩)

omit [Finite G] in
theorem Fh_mul {h : G} (hh : h ∈ M.HC) (q q' : ruQ M.T) :
    M.Fh h hh (q * q') = M.Fh h hh q + M.Fh h hh q' := by
  unfold Fh
  have hc1 := M.comm_HC_Q_mem_U hh q.2
  have hc2 := M.comm_HC_Q_mem_U hh q'.2
  have hconj : (q : G) * ⁅h, (q' : G)⁆ * (q : G)⁻¹ ∈ ruU M.L M.T :=
    M.conj_mem_U (pCoreOf_le 2 _ q.2) hc2
  have e : (⟨_, M.comm_HC_Q_mem_U hh (q * q').2⟩ : ruU M.L M.T) =
      ⟨_, hc1⟩ * ⟨_, hconj⟩ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul]
    group
  have e2 : M.ψU ⟨_, hconj⟩ = M.ψU ⟨_, hc2⟩ := by
    have hz := M.two.UZ_central _ q.2 _ hc2
    have hk : (⟨_, hconj⟩ : ruU M.L M.T) * (⟨_, hc2⟩ : ruU M.L M.T)⁻¹ ∈ M.ψU.ker := by
      rw [M.ψU_ker, Subgroup.mem_subgroupOf]
      exact hz
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hk
    exact mul_inv_eq_one.mp hk
  rw [e, M.toAdd_ψU_mul, e2]

omit [Finite G] in
theorem Fh_one {h : G} (hh : h ∈ M.HC) : M.Fh h hh 1 = 0 := by
  have := M.Fh_mul hh 1 1
  rw [mul_one] at this
  exact (add_eq_left.mp this.symm)

@[expose] noncomputable def FhHom (h : G) (hh : h ∈ M.HC) :
    ruQ M.T →* Multiplicative (Fin 2 → F4) where
  toFun q := Multiplicative.ofAdd (M.Fh h hh q)
  map_one' := by rw [M.Fh_one hh]; rfl
  map_mul' q q' := by rw [M.Fh_mul hh]; rfl

theorem Fh_mul_U {h w : G} (hh : h ∈ M.HC) (hw : w ∈ ruU M.L M.T) (q : ruQ M.T) :
    M.Fh (h * w) (mul_mem hh (M.U_le_HC hw)) q = M.Fh h hh q := by
  unfold Fh
  have hc1 := M.comm_HC_Q_mem_U (mul_mem hh (M.U_le_HC hw)) q.2
  have hc2 := M.comm_HC_Q_mem_U hh q.2
  have hwq : ⁅w, (q : G)⁆ ∈ ruZ M.T := by
    have := M.two.UZ_central _ q.2 _ hw
    have e : ⁅w, (q : G)⁆ = ((q : G) * w * (q : G)⁻¹ * w⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact inv_mem this
  have hhz : h * ⁅w, (q : G)⁆ * h⁻¹ = ⁅w, (q : G)⁆ :=
    by rw [(M.Z_comm_H hwq (Subgroup.mem_inf.mp hh).1).symm, mul_inv_cancel_right]
  have e : ⁅h * w, (q : G)⁆ = ⁅w, (q : G)⁆ * ⁅h, (q : G)⁆ := by
    rw [← hhz]
    simp only [commutatorElement_def]
    group
  have hk : (⟨_, hc1⟩ : ruU M.L M.T) * (⟨_, hc2⟩ : ruU M.L M.T)⁻¹ ∈ M.ψU.ker := by
    rw [M.ψU_ker, Subgroup.mem_subgroupOf]
    show ⁅h * w, (q : G)⁆ * ⁅h, (q : G)⁆⁻¹ ∈ ruZ M.T
    rw [e, mul_inv_cancel_right]
    exact hwq
  rw [MonoidHom.mem_ker, map_mul, map_inv] at hk
  rw [mul_inv_eq_one.mp hk]

theorem Fh_conj_K {h k : G} (hh : h ∈ M.HC) (hk : k ∈ M.K) (q : ruQ M.T) :
    M.Fh h hh ⟨k * q * k⁻¹, M.conj_mem_Q (M.K_le_H hk) q.2⟩ =
      sigmaAct (M.φ ⟨k, M.K_le_H hk⟩) (M.Fh h hh q) := by
  have hkH := M.K_le_H hk
  have hw : h⁻¹ * (k⁻¹ * h * k) ∈ ruU M.L M.T := by
    have := M.comm_K_HC (inv_mem hk) h hh
    rw [inv_inv] at this
    have e : h⁻¹ * (k⁻¹ * h * k) = h⁻¹ * (k⁻¹ * h * k * h⁻¹) * h := by group
    rw [e]
    have := M.conj_mem_U (inv_mem (Subgroup.mem_inf.mp hh).1) this
    simpa using this
  set w := h⁻¹ * (k⁻¹ * h * k)
  have hhw : h * w = k⁻¹ * h * k := by simp only [w]; group
  have hconj : k * ⁅h * w, (q : G)⁆ * k⁻¹ = ⁅h, k * (q : G) * k⁻¹⁆ := by
    rw [hhw]
    simp only [commutatorElement_def]
    group
  have hmem := M.comm_HC_Q_mem_U (mul_mem hh (M.U_le_HC hw)) q.2
  have e := M.ψU_conj ⟨k, hkH⟩ ⟨_, hmem⟩
  have e2 : (⟨k * ⁅h * w, (q : G)⁆ * k⁻¹, M.conj_mem_U hkH hmem⟩ : ruU M.L M.T) =
      ⟨_, M.comm_HC_Q_mem_U hh (M.conj_mem_Q hkH q.2)⟩ := Subtype.ext hconj
  rw [show (⟨(k : G) * ⁅h * w, (q : G)⁆ * (k : G)⁻¹, M.conj_mem_U hkH hmem⟩ : ruU M.L M.T) =
    ⟨((⟨k, hkH⟩ : ruH M.T) : G) * ((⟨_, hmem⟩ : ruU M.L M.T) : G) *
      ((⟨k, hkH⟩ : ruH M.T) : G)⁻¹, M.conj_mem_U hkH hmem⟩ from rfl] at e2
  rw [e2] at e
  have h3 := M.Fh_mul_U hh hw q
  unfold Fh at h3 ⊢
  rw [e, h3]

theorem Fh_surj {h : G} (hh : h ∈ M.HC) (hU : h ∉ ruU M.L M.T) (v : Fin 2 → F4) :
    ∃ q : ruQ M.T, M.Fh h hh q = v := by
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U hh
  have hxU : x ∉ ruU M.L M.T := fun hxU => hU (mul_mem hxU hu)
  have hxHC := M.HB_le_HC hx
  have hred : ∀ q, M.Fh (x * u) hh q = M.Fh x hxHC q := fun q => M.Fh_mul_U hxHC hu q
  have hne : ∃ q : ruQ M.T, M.Fh x hxHC q ≠ 0 := by
    by_contra hno
    push Not at hno
    have hZ : ∀ q : ruQ M.T, ⁅x, (q : G)⁆ ∈ ruZ M.T := by
      intro q
      have h0 := hno q
      have : M.ψU ⟨_, M.comm_HC_Q_mem_U hxHC q.2⟩ = 1 := Multiplicative.toAdd.injective h0
      rw [M.ψU_eq_one_iff] at this
      exact this
    let g : ruQ M.T →* ruZ M.T :=
      { toFun := fun q => ⟨_, hZ q⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun q q' => Subtype.ext (by
          have hc : (q : G) * ⁅x, (q' : G)⁆ = ⁅x, (q' : G)⁆ * q :=
            (M.Z_comm_H (hZ q') (pCoreOf_le 2 _ q.2)).symm
          simp only [Subgroup.coe_mul, commutatorElement_def] at hc ⊢
          calc x * (↑q * ↑q') * x⁻¹ * (↑q * ↑q')⁻¹ =
              x * ↑q * x⁻¹ * (↑q)⁻¹ * (↑q * (x * ↑q' * x⁻¹ * (↑q')⁻¹)) * (↑q)⁻¹ := by group
            _ = x * ↑q * x⁻¹ * (↑q)⁻¹ * (x * ↑q' * x⁻¹ * (↑q')⁻¹ * ↑q) * (↑q)⁻¹ := by rw [hc]
            _ = _ := by group) }
    have hcard := Subgroup.card_ker_mul_card_range g
    rw [M.toRuData.card_Q] at hcard
    have hrange : Nat.card g.range ≤ 2 := by
      rw [← M.toRuData.card_Z]
      exact Subgroup.card_le_card_group _
    have hker : Nat.card g.ker ≤ 2 ^ 9 := by
      rw [← M.card_Q_inf_S]
      refine Nat.card_le_card_of_injective (fun q => ⟨q.1.1, q.1.2,
        M.centralizer_Q_le_S hx hxU q.1.2 ?_⟩) ?_
      · have hq := q.2
        rw [MonoidHom.mem_ker] at hq
        have h1 : ⁅x, ((q : ruQ M.T) : G)⁆ = 1 := congrArg Subtype.val hq
        rw [commutatorElement_def] at h1
        calc ((q : ruQ M.T) : G) * x = (x * ↑↑q * x⁻¹ * (↑↑q)⁻¹)⁻¹ * x * ↑↑q := by group
          _ = x * ↑↑q := by rw [h1, inv_one, one_mul]
      · intro a b hab
        have h' := Subtype.ext_iff.mp hab
        exact Subtype.ext (Subtype.ext h')
    have : 2 ^ 11 ≤ 2 ^ 9 * 2 := by
      calc 2 ^ 11 = Nat.card g.ker * Nat.card g.range := hcard.symm
        _ ≤ 2 ^ 9 * 2 := Nat.mul_le_mul hker hrange
    norm_num at this
  obtain ⟨q0, hq0⟩ := hne
  by_cases hv : v = 0
  · exact ⟨1, by rw [hv, M.Fh_one]⟩
  obtain ⟨A, hA⟩ := Sigma.exists_sl_smul_eq hq0 hv
  obtain ⟨k, hk⟩ := M.φ_surj (SemidirectProduct.inl A)
  have hkK : (k : G) ∈ M.K := M.mem_K_iff.mpr ⟨k.2, by rw [hk]; rfl⟩
  refine ⟨⟨(k : G) * q0 * (k : G)⁻¹, M.conj_mem_Q k.2 q0.2⟩, ?_⟩
  rw [hred, M.Fh_conj_K hxHC hkK q0, show (⟨(k : G), M.K_le_H hkK⟩ : ruH M.T) = k from rfl, hk,
    Sigma.sigmaAct_inl, hA]

theorem lemma_J24 {h : G} (hh : h ∈ M.HC) (hU : h ∉ ruU M.L M.T) :
    M.commQ h ⊔ ruZ M.T = ruU M.L M.T ∧ M.commQ h = ruU M.L M.T ∧
      ruQ M.T ⊓ Subgroup.centralizer ({h} : Set G) = Subgroup.zpowers h ⊔ ruU M.L M.T := by
  have hle : M.commQ h ≤ ruU M.L M.T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact M.comm_HC_Q_mem_U hh hq
  have hZU : ruZ M.T ≤ ruU M.L M.T := M.two.Z_le_U
  have h1 : M.commQ h ⊔ ruZ M.T = ruU M.L M.T := by
    refine le_antisymm (sup_le hle hZU) (fun u hu => ?_)
    obtain ⟨q, hq⟩ := M.Fh_surj hh hU (Multiplicative.toAdd (M.ψU ⟨u, hu⟩))
    have hmem := M.comm_HC_Q_mem_U hh q.2
    have hk : (⟨_, hmem⟩ : ruU M.L M.T)⁻¹ * ⟨u, hu⟩ ∈ M.ψU.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      refine inv_mul_eq_one.mpr (Multiplicative.toAdd.injective ?_)
      exact hq
    rw [M.ψU_ker, Subgroup.mem_subgroupOf] at hk
    have e : u = ⁅h, (q : G)⁆ * (⁅h, (q : G)⁆⁻¹ * u) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨q, q.2, rfl⟩))
      (Subgroup.mem_sup_right hk)
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U hh
  have hxU : x ∉ ruU M.L M.T := fun hxU => hU (mul_mem hxU hu)
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  have hxχ : Multiplicative.toAdd (M.χ ⟨x, hxS⟩) ≠ 0 := by
    intro h0
    apply hxU
    have hk : (⟨x, hxS⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact M.V_le_U hk
  have hexy : ∃ y ∈ M.HB, ⁅x, y⁆ = M.z := by
    by_cases hb : Multiplicative.toAdd (M.χ ⟨x, hxS⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1]
    · obtain ⟨y, hyS, hyb, hyχ⟩ := M.exists_t2
      have hy : y ∈ M.HB := M.mem_HB.mpr ⟨hyS, hyb⟩
      refine ⟨y, hy, (M.comm_HB hx hy).2 ?_⟩
      rw [hb, show Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) = _ from hyχ]
      decide
    · obtain ⟨y, hyS, hyb, hyχ⟩ := M.exists_t1
      have hy : y ∈ M.HB := M.mem_HB.mpr ⟨hyS, hyb⟩
      refine ⟨y, hy, (M.comm_HB hx hy).2 ?_⟩
      rw [show Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) = _ from hyχ]
      rintro (h0 | h0 | h0)
      · exact hxχ h0
      · exact absurd h0 (by decide)
      · exact hb h0
  obtain ⟨y, hy, hxy⟩ := hexy
  have hyHC := M.HB_le_HC hy
  have huy : u * y = y * u := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyHC).2 u hu)
  have hzmem : M.z ∈ M.commQ (x * u) := by
    refine Subgroup.subset_closure ⟨y, (Subgroup.mem_inf.mp hy).1, ?_⟩
    rw [← hxy]
    simp only [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = x * (u * y * u⁻¹) * x⁻¹ * y⁻¹ := by rw [huy]; group
      _ = x * u * y * (x * u)⁻¹ * y⁻¹ := by group
  have hZle : ruZ M.T ≤ M.commQ (x * u) := by
    intro w hw
    rcases M.mem_Z_iff.mp hw with rfl | rfl
    · exact one_mem _
    · exact hzmem
  have h2 : M.commQ (x * u) = ruU M.L M.T := by
    rw [← h1, sup_eq_left.mpr hZle]
  refine ⟨h1, h2, ?_⟩
  have hxuQ : x * u ∈ ruQ M.T := M.HC_le_Q hh
  refine le_antisymm (fun q hq => ?_) (sup_le ?_ ?_)
  · obtain ⟨hqQ, hqc⟩ := Subgroup.mem_inf.mp hq
    have hqc' := Subgroup.mem_centralizer_singleton_iff.mp hqc
    have hqHC : q ∈ M.HC := by
      let F := M.FhHom (x * u) hh
      have hsurj : Function.Surjective F := fun v => by
        obtain ⟨q', hq'⟩ := M.Fh_surj hh hU (Multiplicative.toAdd v)
        exact ⟨q', by show Multiplicative.ofAdd _ = v; rw [hq', ofAdd_toAdd]⟩
      have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
      rw [M.toRuData.card_Q, Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F4)),
        show Fintype.card (Multiplicative (Fin 2 → F4)) = 16 from rfl] at hcard
      have hHCker : M.HC.subgroupOf (ruQ M.T) ≤ F.ker := by
        intro q' hq'
        rw [Subgroup.mem_subgroupOf] at hq'
        rw [MonoidHom.mem_ker]
        show Multiplicative.ofAdd (M.Fh (x * u) hh q') = 1
        obtain ⟨x', hx', u', hu', hq'e⟩ := M.exists_HB_U hq'
        have hcomm : ⁅x * u, (q' : G)⁆ ∈ ruZ M.T := by
          have hx'HC := M.HB_le_HC hx'
          have hu'c : u' * x = x * u' := (Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp (M.HB_le_HC hx)).2 u' hu')
          have huc : ∀ g ∈ M.HC, u * g = g * u := fun g hg =>
            (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u hu)
          have hu'c' : ∀ g ∈ M.HC, u' * g = g * u' := fun g hg =>
            (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u' hu')
          have e : ⁅x * u, (q' : G)⁆ = ⁅x, x'⁆ := by
            rw [hq'e]
            simp only [commutatorElement_def]
            have h1 := huc x' hx'HC
            have h2 := hu'c' x (M.HB_le_HC hx)
            have h3 := huc u' (M.U_le_HC hu')
            calc x * u * (x' * u') * (x * u)⁻¹ * (x' * u')⁻¹
                = x * (u * x') * u' * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by group
              _ = x * (x' * u) * u' * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by rw [h1]
              _ = x * x' * (u * u') * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by group
              _ = x * x' * (u' * u) * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by rw [h3]
              _ = x * x' * (u' * x⁻¹) * u'⁻¹ * x'⁻¹ := by group
              _ = x * x' * (x⁻¹ * u') * u'⁻¹ * x'⁻¹ := by
                  rw [show u' * x⁻¹ = x⁻¹ * u' by
                    calc u' * x⁻¹ = x⁻¹ * (x * u') * x⁻¹ := by group
                      _ = x⁻¹ * (u' * x) * x⁻¹ := by rw [h2]
                      _ = x⁻¹ * u' := by group]
              _ = x * x' * x⁻¹ * x'⁻¹ := by group
          rw [e]
          by_cases hc : Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) = 0 ∨
              Multiplicative.toAdd (M.χ ⟨x', (M.mem_HB.mp hx').1⟩) = 0 ∨
              Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) =
                Multiplicative.toAdd (M.χ ⟨x', (M.mem_HB.mp hx').1⟩)
          · rw [(M.comm_HB hx hx').1 hc]
            exact one_mem _
          · rw [(M.comm_HB hx hx').2 hc]
            exact M.z_mem_Z
        have : M.ψU ⟨_, M.comm_HC_Q_mem_U hh q'.2⟩ = 1 := by
          rw [M.ψU_eq_one_iff]
          exact hcomm
        unfold Fh
        rw [this]
        rfl
      have hcardHC : Nat.card (M.HC.subgroupOf (ruQ M.T)) = 2 ^ 7 := by
        rw [card_subgroupOf_of_le M.HC_le_Q, M.card_HC]
      have heq : M.HC.subgroupOf (ruQ M.T) = F.ker :=
        Subgroup.eq_of_le_of_card_ge hHCker (by rw [hcardHC]; omega)
      have hqker : (⟨q, hqQ⟩ : ruQ M.T) ∈ F.ker := by
        rw [MonoidHom.mem_ker]
        show Multiplicative.ofAdd (M.Fh (x * u) hh ⟨q, hqQ⟩) = 1
        have : M.ψU ⟨_, M.comm_HC_Q_mem_U hh hqQ⟩ = 1 := by
          have h1 : ⁅x * u, q⁆ = 1 := by
            rw [commutatorElement_def, ← hqc']
            group
          have : (⟨_, M.comm_HC_Q_mem_U hh hqQ⟩ : ruU M.L M.T) = 1 := Subtype.ext h1
          rw [this, map_one]
        unfold Fh
        rw [this]
        rfl
      rw [← heq, Subgroup.mem_subgroupOf] at hqker
      exact hqker
    obtain ⟨x', hx', u', hu', rfl⟩ := M.exists_HB_U hqHC
    have hcomm : ⁅x, x'⁆ = 1 := by
      have huc : ∀ g ∈ M.HC, u * g = g * u := fun g hg =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u hu)
      have hu'c : ∀ g ∈ M.HC, u' * g = g * u' := fun g hg =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u' hu')
      have h1 := huc x' (M.HB_le_HC hx')
      have h2 := hu'c x (M.HB_le_HC hx)
      have h3 := huc u' (M.U_le_HC hu')
      have hc := hqc'
      rw [commutatorElement_def]
      calc x * x' * x⁻¹ * x'⁻¹ = (x * u) * (x' * u') * (x * u)⁻¹ * (x' * u')⁻¹ := by
            calc x * x' * x⁻¹ * x'⁻¹ = x * x' * (x⁻¹ * u') * u'⁻¹ * x'⁻¹ := by group
              _ = x * x' * (u' * x⁻¹) * u'⁻¹ * x'⁻¹ := by
                  rw [show x⁻¹ * u' = u' * x⁻¹ by
                    calc x⁻¹ * u' = x⁻¹ * (u' * x) * x⁻¹ := by group
                      _ = x⁻¹ * (x * u') * x⁻¹ := by rw [h2]
                      _ = u' * x⁻¹ := by group]
              _ = x * x' * (u' * u) * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by group
              _ = x * x' * (u * u') * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by rw [h3]
              _ = x * (x' * u) * u' * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by group
              _ = x * (u * x') * u' * u⁻¹ * x⁻¹ * u'⁻¹ * x'⁻¹ := by rw [h1]
              _ = _ := by group
        _ = 1 := by rw [← hc]; group
    have hcase : Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) = 0 ∨
        Multiplicative.toAdd (M.χ ⟨x', (M.mem_HB.mp hx').1⟩) = 0 ∨
        Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) =
          Multiplicative.toAdd (M.χ ⟨x', (M.mem_HB.mp hx').1⟩) := by
      by_contra hc
      have := (M.comm_HB hx hx').2 hc
      rw [hcomm] at this
      exact M.z_ne_one this.symm
    have hx'S := (M.mem_HB.mp hx').1
    have hHBV : ∀ w ∈ M.HB, w ∈ ruV M.L → w ∈ ruU M.L M.T := fun w hw hwV => by
      rcases M.eq_of_mem_V_comm_bel hwV (M.mem_HB.mp hw).2 with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact M.V_le_U M.z_mem_V
    rcases hcase with h0 | h0 | h0
    · exact absurd h0 hxχ
    ·
      have hk : (⟨x', hx'S⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
      exact Subgroup.mem_sup_right (mul_mem (hHBV x' hx' hk) hu')
    ·
      have hk : (⟨x, hxS⟩ : ruS M.L)⁻¹ * ⟨x', hx'S⟩ ∈ M.χ.ker := by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        rw [M.toAdd_χ_mul, M.toAdd_χ_inv, h0, toAdd_one]
        ext i j
        have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
        exact h2 _
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
      have hw : x⁻¹ * x' ∈ M.HB := mul_mem (inv_mem hx) hx'
      have hwU := hHBV _ hw hk
      have e : x' * u' = (x * u) * (u⁻¹ * (x⁻¹ * x') * u') := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (mul_mem (mul_mem (inv_mem hu) hwU) hu'))
  · rw [Subgroup.zpowers_le]
    exact ⟨hxuQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  · intro w hw
    refine ⟨M.U_le_Q hw, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 w hw

end RuDataM

end CFSG.Quasithin.RuType
