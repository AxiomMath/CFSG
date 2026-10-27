module

public import CFSG.Quasithin.Recognition.RuTypeJ23c
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace Sigma

theorem fix_order_three : ∀ g : SigmaL2F4, (g ^ 3 = 1 ∧ g ≠ 1) →
    ∀ v : Fin 2 → F4, sigmaAct g v = v → v = 0 := by
  decide +kernel

theorem U0_centralizer_order_three : ∀ g : SigmaL2F4, (g ^ 3 = 1 ∧ g ≠ 1) →
    ∀ u ∈ U0, u * g = g * u → u = 1 := by
  decide +kernel

end Sigma

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem mem_centralizer_B {x : G} :
    x ∈ Subgroup.centralizer (M.B : Set G) ↔ (M.bel : G) * x = x * M.bel := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left h k).eq

theorem φ_bel : M.φ ⟨M.bel, M.bel_mem_H⟩ ^ 3 = 1 ∧ M.φ ⟨M.bel, M.bel_mem_H⟩ ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [← map_pow]
    have : (⟨M.bel, M.bel_mem_H⟩ : ruH M.T) ^ 3 = 1 := Subtype.ext M.bel_pow_three
    rw [this, map_one]
  · have hk : (⟨M.bel, M.bel_mem_H⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ : IsPGroup 2 (ruQ M.T) := pCoreOf_isPGroup 2 _
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨M.bel, hk⟩
    rw [← Subgroup.orderOf_coe, show ((⟨M.bel, hk⟩ : ruQ M.T) : G) = M.bel from rfl,
      M.orderOf_bel] at hn
    rcases n with _ | n
    · norm_num at hn
    · have h2 : 2 ∣ 2 ^ (n + 1) := dvd_pow_self 2 (Nat.succ_ne_zero n)
      rw [← hn] at h2
      norm_num at h2

theorem centralizer_Q_le_HC {q : G} (hq : q ∈ ruQ M.T) (hb : (M.bel : G) * q = q * M.bel) :
    q ∈ M.HC := by
  have e := M.ψQ_conj ⟨M.bel, M.bel_mem_H⟩ ⟨q, hq⟩
  have hqq : (⟨(M.bel : G) * q * (M.bel : G)⁻¹, M.conj_mem_Q M.bel_mem_H hq⟩ : ruQ M.T) =
      ⟨q, hq⟩ := Subtype.ext (by
    show (M.bel : G) * q * (M.bel : G)⁻¹ = q
    rw [hb, mul_inv_cancel_right])
  rw [hqq] at e
  have h0 := Sigma.fix_order_three _ M.φ_bel _ e.symm
  have h1 : M.ψQ ⟨q, hq⟩ = 1 := Multiplicative.toAdd.injective h0
  have hcomm := (M.ψQ_eq_one_iff ⟨q, hq⟩).mp h1
  refine ⟨M.toRuData.T_le_H (M.Q_le_T hq), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  exact (hcomm u hu).symm

theorem HC_le_S : M.HC ≤ ruS M.L := by
  intro h hh
  have hQ := M.HC_le_Q hh
  have hL : h ∈ M.L := M.toRuData.T_le_L (M.Q_le_T hQ)
  exact M.toRuData.mem_S_of_centralizes hL fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 v (M.V_le_U hv)).symm

theorem centralizer_S_le_Q {s : G} (hs : s ∈ ruS M.L) (hb : (M.bel : G) * s = s * M.bel) :
    s ∈ ruQ M.T := by
  have hsH := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
  have hU0 := M.φ_S_mem hs
  have hc : M.φ ⟨s, hsH⟩ * M.φ ⟨M.bel, M.bel_mem_H⟩ = M.φ ⟨M.bel, M.bel_mem_H⟩ * M.φ ⟨s, hsH⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hb.symm
  have h1 := Sigma.U0_centralizer_order_three _ M.φ_bel _ hU0 hc
  have hk : (⟨s, hsH⟩ : ruH M.T) ∈ M.φ.ker := h1
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem centralizer_Q_eq :
    ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G) =
      ruS M.L ⊓ Subgroup.centralizer (M.B : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, M.mem_centralizer_B]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨M.HC_le_S (M.centralizer_Q_le_HC hx hb), hb⟩
  · rintro ⟨hx, hb⟩
    exact ⟨M.centralizer_S_le_Q hx hb, hb⟩

theorem eq_of_mem_V_comm_bel {v : G} (hv : v ∈ ruV M.L) (hb : (M.bel : G) * v = v * M.bel) :
    v = 1 ∨ v = M.z := by
  have h : (M.bel : G) * (⟨v, hv⟩ : ruV M.L) * (M.bel : G)⁻¹ = (⟨v, hv⟩ : ruV M.L) := by
    show (M.bel : G) * v * (M.bel : G)⁻¹ = v
    rw [hb, mul_inv_cancel_right]
  have h1 := (M.toRuData.conj_eq_iff M.bel ⟨v, hv⟩).mp h
  rw [M.θ_bel] at h1
  rcases SL3.b0_fix_vec _ h1 with h0 | h0
  · left
    have : M.ψV ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective h0
    exact congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
  · right
    have : M.ψV ⟨v, hv⟩ = M.ψV M.zV := by
      apply Multiplicative.toAdd.injective
      rw [h0, M.ψV_zV]
    exact congrArg Subtype.val (M.ψV.injective this)

@[expose] def IsFixB0 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  A = 0 ∨ A = !![0, 0, 0; 0, 1, 0; 0, 0, 1] ∨ A = !![1, 0, 0; 0, 0, 1; 0, 1, 1] ∨
    A = !![1, 0, 0; 0, 1, 1; 0, 1, 0]

instance : DecidablePred IsFixB0 := fun A => by unfold IsFixB0; infer_instance

omit [Finite G] in
theorem card_IsFixB0 :
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsFixB0 A} = 4 := by
  decide +kernel

omit [Finite G] in
theorem IsFixB0.props : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsFixB0 A →
    A.trace = 0 ∧ stAct SL3.b0 A = A := by
  decide +kernel

theorem isFixB0_χ {x : G} (hx : x ∈ ruS M.L) (hb : (M.bel : G) * x = x * M.bel) :
    IsFixB0 (Multiplicative.toAdd (M.χ ⟨x, hx⟩)) := by
  have e := M.χ_equiv M.bel ⟨x, hx⟩ ⟨x, hx⟩ (by
    show x = (M.bel : G) * x * (M.bel : G)⁻¹
    rw [hb, mul_inv_cancel_right])
  rw [M.θ_bel] at e
  have h := congrArg Multiplicative.toAdd e
  rw [toAdd_ofAdd] at h
  exact (SL3.fix_b0_iff _ (M.χ_trace _)).mp h.symm

theorem exists_centralizer_S_B {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsFixB0 A) :
    ∃ x, ∃ hx : x ∈ ruS M.L, (M.bel : G) * x = x * M.bel ∧
      Multiplicative.toAdd (M.χ ⟨x, hx⟩) = A := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hAt, hAb⟩ := IsFixB0.props A hA
  obtain ⟨s, hs⟩ := M.χ_surj A hAt
  have hbs : (M.bel : G) * s * (M.bel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.bel.2) s).mp s.2
  have hsV : (s : G)⁻¹ * ((M.bel : G) * s * (M.bel : G)⁻¹) ∈ ruV M.L := by
    have e := M.χ_equiv M.bel s ⟨_, hbs⟩ rfl
    rw [M.θ_bel, hs, toAdd_ofAdd, hAb, ← hs] at e
    have hk : s⁻¹ * ⟨_, hbs⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, e]
      exact inv_mul_cancel _
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hbV : ∀ v ∈ ruV M.L, (M.bel : G) * v * (M.bel : G)⁻¹ ∈ ruV M.L := fun v hv =>
    M.toRuData.conj_mem_V M.bel.2 hv
  have h3 : ¬ 3 ∣ Nat.card (ruV M.L) := by rw [M.toRuData.card_V]; norm_num
  obtain ⟨v, hv, hfix⟩ := exists_fixed_mem_coset M.bel_pow_three hbV hsV h3
  have hsv : (s : G) * v ∈ ruS M.L := mul_mem s.2 (M.toRuData.V_le_S hv)
  refine ⟨_, hsv, ?_, ?_⟩
  · calc (M.bel : G) * (s * v) = (M.bel : G) * (s * v) * (M.bel : G)⁻¹ * M.bel := by group
      _ = s * v * M.bel := by rw [hfix]
  · have e : (⟨(s : G) * v, hsv⟩ : ruS M.L) = s * ⟨v, M.toRuData.V_le_S hv⟩ := rfl
    have hv1 : M.χ ⟨v, M.toRuData.V_le_S hv⟩ = 1 := by
      have : (⟨v, M.toRuData.V_le_S hv⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [M.χ_ker, Subgroup.mem_subgroupOf]
        exact hv
      exact this
    rw [e, map_mul, hv1, mul_one, hs, toAdd_ofAdd]

theorem card_centralizer_S_B :
    Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer (M.B : Set G)) = 2 ^ 3 := by
  classical
  set P := ruS M.L ⊓ Subgroup.centralizer (M.B : Set G)
  have hPS : P ≤ ruS M.L := inf_le_left
  let f : P.subgroupOf (ruS M.L) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    M.χ.comp (P.subgroupOf (ruS M.L)).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hPS] at h
  have hmemP : ∀ {x : G}, x ∈ P ↔ x ∈ ruS M.L ∧ (M.bel : G) * x = x * M.bel := by
    intro x
    rw [Subgroup.mem_inf, M.mem_centralizer_B]
  have hZP : ∀ x ∈ ruZ M.T, x ∈ P := by
    intro x hx
    refine hmemP.mpr ⟨M.toRuData.V_le_S (M.toRuData.Z_le_V hx), ?_⟩
    exact (M.toRuData.mem_H_iff.mp M.bel_mem_H x hx).symm
  have hker : Nat.card f.ker = 2 := by
    refine Eq.trans ?_ M.toRuData.card_Z
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_⟩
        invFun := fun z => ⟨⟨⟨z.1, M.toRuData.V_le_S (M.toRuData.Z_le_V z.2)⟩,
          Subgroup.mem_subgroupOf.mpr (hZP z.1 z.2)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have hxV : x.1.1 ∈ M.χ.ker := hx
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hxV
      have hb := (hmemP.mp (Subgroup.mem_subgroupOf.mp x.1.2)).2
      rcases M.eq_of_mem_V_comm_bel hxV hb with h1 | h1
      · rw [h1]
        exact (ruZ M.T).one_mem
      · rw [h1]
        exact M.z_mem_Z
    · show M.χ ⟨z.1, _⟩ = 1
      have : (⟨z.1, M.toRuData.V_le_S (M.toRuData.Z_le_V z.2)⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [M.χ_ker, Subgroup.mem_subgroupOf]
        exact M.toRuData.Z_le_V z.2
      exact this
  have hrange : Nat.card f.range = 4 := by
    refine Eq.trans ?_ ((Nat.card_eq_fintype_card).trans card_IsFixB0)
    refine Nat.card_congr
      { toFun := fun y => ⟨Multiplicative.toAdd y.1, ?_⟩
        invFun := fun A => ⟨Multiplicative.ofAdd A.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun A => rfl }
    · obtain ⟨x, hx⟩ := y.2
      rw [← hx]
      have hxP := hmemP.mp (Subgroup.mem_subgroupOf.mp x.2)
      exact M.isFixB0_χ x.1.2 hxP.2
    · obtain ⟨x, hx, hb, hxA⟩ := M.exists_centralizer_S_B A.2
      exact ⟨⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr (hmemP.mpr ⟨hx, hb⟩)⟩,
        by rw [← hxA, ofAdd_toAdd]; rfl⟩
  rw [hker, hrange] at h
  rw [← h]
  norm_num

theorem exists_t1 : ∃ t, ∃ ht : t ∈ ruS M.L, (M.bel : G) * t = t * M.bel ∧
    Multiplicative.toAdd (M.χ ⟨t, ht⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1] :=
  M.exists_centralizer_S_B (Or.inr (Or.inr (Or.inl rfl)))

theorem exists_t2 : ∃ t, ∃ ht : t ∈ ruS M.L, (M.bel : G) * t = t * M.bel ∧
    Multiplicative.toAdd (M.χ ⟨t, ht⟩) = !![1, 0, 0; 0, 1, 1; 0, 1, 0] :=
  M.exists_centralizer_S_B (Or.inr (Or.inr (Or.inr rfl)))

omit [Finite G] in
theorem not_mem_V_of_χ_ne {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ≠ 0) : x ∉ ruV M.L := by
  intro hV
  apply h
  have hk : (⟨x, hx⟩ : ruS M.L) ∈ M.χ.ker := by
    rw [M.χ_ker, Subgroup.mem_subgroupOf]
    exact hV
  rw [MonoidHom.mem_ker.mp hk, toAdd_one]

theorem sq_ne_one_of_b0 {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1]) : x ^ 2 ≠ 1 := by
  have hS1 : x ∈ M.S1 := ⟨hx, by rw [h]; exact SL3.b0mat_mem_st1⟩
  exact M.sq_ne_one_of_S1 hS1 (M.not_mem_V_of_χ_ne hx (by rw [h]; decide))

theorem sq_ne_one_of_b0sq {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) = !![1, 0, 0; 0, 1, 1; 0, 1, 0]) : x ^ 2 ≠ 1 := by
  obtain ⟨n, hn⟩ := M.θ_surj SL3.n0
  have hnx : (n : G) * x * (n : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L n.2) x).mp hx
  have hχ : Multiplicative.toAdd (M.χ ⟨_, hnx⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1] := by
    rw [M.χ_conj n ⟨x, hx⟩, hn, h, SL3.n0_swap]
  intro hx2
  apply M.sq_ne_one_of_b0 hnx hχ
  rw [show ((n : G) * x * (n : G)⁻¹) ^ 2 = (n : G) * x ^ 2 * (n : G)⁻¹ by
    rw [pow_two, pow_two]; group, hx2]
  group

theorem t1_t2_not_comm {t1 t2 : G} (ht1 : t1 ∈ ruS M.L) (hb1 : (M.bel : G) * t1 = t1 * M.bel)
    (hχ1 : Multiplicative.toAdd (M.χ ⟨t1, ht1⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1])
    (ht2 : t2 ∈ ruS M.L)
    (hχ2 : Multiplicative.toAdd (M.χ ⟨t2, ht2⟩) = !![1, 0, 0; 0, 1, 1; 0, 1, 0]) :
    t1 * t2 ≠ t2 * t1 := by
  intro hcomm
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set A1 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]
  have hA1 : IsTraceZero A1 := by unfold IsTraceZero; decide
  have h12 : M.cform A1 !![1, 0, 0; 0, 1, 1; 0, 1, 0] = 0 := by
    have := (M.comm_eq_one_iff_cform ⟨t1, ht1⟩ ⟨t2, ht2⟩).mp (by
      show t1 * t2 * t1⁻¹ * t2⁻¹ = 1
      rw [hcomm]
      group)
    rwa [hχ1, hχ2] at this
  have hvan : ∀ A, IsFixB0 A → M.cform A1 A = 0 := by
    rintro A (rfl | rfl | rfl | rfl)
    · exact M.cform_zero hA1
    · have hD : (!![0, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          A1 + !![1, 0, 0; 0, 1, 1; 0, 1, 0] := by decide
      rw [hD, M.cform_add_right hA1 hA1 (by unfold IsTraceZero; decide), M.cform_self, h12,
        add_zero]
    · exact M.cform_self A1
    · exact h12
  have hA10 : A1 ≠ 0 := by decide
  obtain ⟨B', hB', hB'z⟩ := M.Wc_top hA1 hA10 SL3.e0
  set y0 : ruS M.L := M.sOf B'
  have hy0 : M.χ y0 = Multiplicative.ofAdd B' := M.χ_sOf hB'
  have hcz : ⁅t1, (y0 : G)⁆ = M.z := by
    have e := M.ψV_comm ⟨t1, ht1⟩ y0
    rw [hχ1, hy0, toAdd_ofAdd, hB'z, ← M.ψV_zV] at e
    have := M.ψV.injective (Multiplicative.toAdd.injective e)
    exact congrArg Subtype.val this
  set N := ruS M.L ⊓ Subgroup.centralizer ({t1} : Set G)
  have hN : ∀ n ∈ N, (M.bel : G) * n * (M.bel : G)⁻¹ ∈ N := by
    intro n hn
    obtain ⟨hnS, hnc⟩ := Subgroup.mem_inf.mp hn
    have hnc' := Subgroup.mem_centralizer_singleton_iff.mp hnc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.bel.2) n).mp hnS,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hbt : (M.bel : G)⁻¹ * t1 * M.bel = t1 := by
      rw [mul_assoc, ← hb1]
      group
    calc (M.bel : G) * n * (M.bel : G)⁻¹ * t1 = (M.bel : G) * (n * ((M.bel : G)⁻¹ * t1 * M.bel)) *
          (M.bel : G)⁻¹ := by group
      _ = (M.bel : G) * (n * t1) * (M.bel : G)⁻¹ := by rw [hbt]
      _ = (M.bel : G) * (t1 * n) * (M.bel : G)⁻¹ := by rw [hnc']
      _ = (M.bel : G) * (((M.bel : G)⁻¹ * t1 * M.bel) * n) * (M.bel : G)⁻¹ := by rw [hbt]
      _ = t1 * ((M.bel : G) * n * (M.bel : G)⁻¹) := by group
  have hy0N : (y0 : G)⁻¹ * ((M.bel : G) * y0 * (M.bel : G)⁻¹) ∈ N := by
    have hby0 : (M.bel : G) * y0 * (M.bel : G)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.bel.2) y0).mp y0.2
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem y0.2) hby0,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hbz : (M.bel : G) * M.z = M.z * M.bel :=
      (M.toRuData.mem_H_iff.mp M.bel_mem_H M.z M.z_mem_Z).symm
    have hbt : (M.bel : G) * t1 * (M.bel : G)⁻¹ = t1 := by rw [hb1, mul_inv_cancel_right]
    have h1 : t1 * ((M.bel : G) * y0 * (M.bel : G)⁻¹) * t1⁻¹ *
        ((M.bel : G) * y0 * (M.bel : G)⁻¹)⁻¹ = M.z := by
      calc t1 * ((M.bel : G) * y0 * (M.bel : G)⁻¹) * t1⁻¹ * ((M.bel : G) * y0 * (M.bel : G)⁻¹)⁻¹
          = (M.bel : G) * (((M.bel : G)⁻¹ * t1 * M.bel) * y0 * ((M.bel : G)⁻¹ * t1 * M.bel)⁻¹ *
            (y0 : G)⁻¹) * (M.bel : G)⁻¹ := by group
        _ = (M.bel : G) * ⁅t1, (y0 : G)⁆ * (M.bel : G)⁻¹ := by
            rw [show (M.bel : G)⁻¹ * t1 * M.bel = t1 by rw [mul_assoc, ← hb1]; group,
              commutatorElement_def]
        _ = M.z := by rw [hcz, hbz, mul_inv_cancel_right]
    rw [commutatorElement_def] at hcz
    calc (y0 : G)⁻¹ * ((M.bel : G) * y0 * (M.bel : G)⁻¹) * t1 =
        (y0 : G)⁻¹ * (t1 * ((M.bel : G) * y0 * (M.bel : G)⁻¹) * t1⁻¹ *
          ((M.bel : G) * y0 * (M.bel : G)⁻¹)⁻¹)⁻¹ * t1 * ((M.bel : G) * y0 * (M.bel : G)⁻¹) := by
          group
      _ = (y0 : G)⁻¹ * (t1 * y0 * t1⁻¹ * (y0 : G)⁻¹)⁻¹ * t1 *
          ((M.bel : G) * y0 * (M.bel : G)⁻¹) := by rw [h1, hcz]
      _ = t1 * ((y0 : G)⁻¹ * ((M.bel : G) * y0 * (M.bel : G)⁻¹)) := by group
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have htV : t1 ∉ ruV M.L := M.not_mem_V_of_χ_ne ht1 (by rw [hχ1]; exact hA10)
    rw [M.card_centralizer_S ht1 htV]
    norm_num
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset M.bel_pow_three hN hy0N hN3
  obtain ⟨hnS, hnc⟩ := Subgroup.mem_inf.mp hn
  have hnc' := Subgroup.mem_centralizer_singleton_iff.mp hnc
  have hyS : (y0 : G) * n ∈ ruS M.L := mul_mem y0.2 hnS
  have hyb : (M.bel : G) * (y0 * n) = (y0 * n) * M.bel := by
    calc (M.bel : G) * (y0 * n) = (M.bel : G) * (y0 * n) * (M.bel : G)⁻¹ * M.bel := by group
      _ = (y0 * n) * M.bel := by rw [hfix]
  have hyz : ⁅t1, (y0 : G) * n⁆ = M.z := by
    rw [← hcz, commutatorElement_def, commutatorElement_def]
    calc t1 * (y0 * n) * t1⁻¹ * ((y0 : G) * n)⁻¹ = t1 * y0 * (n * t1⁻¹) * n⁻¹ * (y0 : G)⁻¹ := by
          group
      _ = t1 * y0 * (t1⁻¹ * n) * n⁻¹ * (y0 : G)⁻¹ := by
          rw [show n * t1⁻¹ = t1⁻¹ * n by
            calc n * t1⁻¹ = t1⁻¹ * (t1 * n) * t1⁻¹ := by group
              _ = t1⁻¹ * (n * t1) * t1⁻¹ := by rw [hnc']
              _ = t1⁻¹ * n := by group]
      _ = t1 * y0 * t1⁻¹ * (y0 : G)⁻¹ := by group
  have hfixy := M.isFixB0_χ hyS hyb
  have e := M.ψV_comm ⟨t1, ht1⟩ ⟨_, hyS⟩
  rw [hχ1, hvan _ hfixy] at e
  have hz1 : M.ψV ⟨_, M.comm_mem_V ht1 hyS⟩ = 1 := Multiplicative.toAdd.injective e
  have hz : (⟨_, M.comm_mem_V ht1 hyS⟩ : ruV M.L) = M.zV := Subtype.ext hyz
  rw [hz] at hz1
  have := congrArg Multiplicative.toAdd hz1
  rw [M.ψV_zV, toAdd_one] at this
  exact absurd this (by decide)

theorem eq_z_of_involution {x : G} (hx : x ∈ ruS M.L) (hb : (M.bel : G) * x = x * M.bel)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : x = M.z := by
  rcases M.isFixB0_χ hx hb with h | h | h | h
  ·
    have hk : (⟨x, hx⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [h, toAdd_one])
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    rcases M.eq_of_mem_V_comm_bel hk hb with h1 | h1
    · exact absurd h1 hx1
    · exact h1
  ·
    exfalso
    obtain ⟨t1, ht1, hb1, hχ1⟩ := M.exists_t1
    obtain ⟨t2, ht2, hb2, hχ2⟩ := M.exists_t2
    have hsq1 := M.sq_ne_one_of_b0 ht1 hχ1
    have hsq2 := M.sq_ne_one_of_b0sq ht2 hχ2
    have hsqz : ∀ t ∈ ruS M.L, (M.bel : G) * t = t * M.bel → t ^ 2 ≠ 1 → t ^ 2 = M.z := by
      intro t ht htb ht2'
      have hV := M.sq_mem_V ht
      have hb' : (M.bel : G) * t ^ 2 = t ^ 2 * M.bel := (Commute.pow_right htb 2).eq
      rcases M.eq_of_mem_V_comm_bel hV hb' with h1 | h1
      · exact absurd h1 ht2'
      · exact h1
    have hz1 := hsqz t1 ht1 hb1 hsq1
    have hz2 := hsqz t2 ht2 hb2 hsq2
    have hw : (⟨t1 * t2, mul_mem ht1 ht2⟩ : ruS M.L)⁻¹ * ⟨x, hx⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [M.toAdd_χ_mul, M.toAdd_χ_inv,
        show (⟨t1 * t2, mul_mem ht1 ht2⟩ : ruS M.L) = ⟨t1, ht1⟩ * ⟨t2, ht2⟩ from rfl,
        M.toAdd_χ_mul, hχ1, hχ2, h, toAdd_one]
      decide
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hw
    have hwb : (M.bel : G) * ((t1 * t2)⁻¹ * x) = ((t1 * t2)⁻¹ * x) * M.bel := by
      have e1 : (M.bel : G) * (t1 * t2) = (t1 * t2) * M.bel := by
        rw [← mul_assoc, hb1, mul_assoc, hb2, mul_assoc]
      have e2 : (M.bel : G) * (t1 * t2)⁻¹ = (t1 * t2)⁻¹ * M.bel :=
        (Commute.inv_right e1).eq
      rw [← mul_assoc, e2, mul_assoc, hb, mul_assoc]
    have hzc : ∀ g ∈ ruS M.L, g * M.z = M.z * g := fun g hg => M.V_comm_S M.z_mem_V hg
    have hxe : x = t1 * t2 ∨ x = t1 * t2 * M.z := by
      rcases M.eq_of_mem_V_comm_bel hw hwb with h1 | h1
      · left
        have h1' : (t1 * t2)⁻¹ * x = 1 := h1
        rw [inv_mul_eq_one] at h1'
        exact h1'.symm
      · right
        have h1' : (t1 * t2)⁻¹ * x = M.z := h1
        rw [← h1']
        group
    have hsq : (t1 * t2) ^ 2 = 1 := by
      rcases hxe with rfl | rfl
      · exact hx2
      · have hz2' : M.z * M.z = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V M.z_mem_V
        have hc := hzc _ (mul_mem ht1 ht2)
        rw [pow_two] at hx2 ⊢
        calc t1 * t2 * (t1 * t2) = t1 * t2 * (t1 * t2) * (M.z * M.z) := by rw [hz2', mul_one]
          _ = t1 * t2 * ((t1 * t2) * M.z) * M.z := by group
          _ = t1 * t2 * (M.z * (t1 * t2)) * M.z := by rw [hc]
          _ = t1 * t2 * M.z * (t1 * t2 * M.z) := by group
          _ = 1 := hx2
    apply M.t1_t2_not_comm ht1 hb1 hχ1 ht2 hχ2
    have hz2' : M.z * M.z = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V M.z_mem_V
    have hi1 : t1⁻¹ = t1 * M.z := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, hz1]
      exact hz2'
    have hi2 : t2⁻¹ = t2 * M.z := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, hz2]
      exact hz2'
    rw [pow_two] at hsq
    have e : t2 * t1 = t1⁻¹ * t2⁻¹ := by
      calc t2 * t1 = t1⁻¹ * (t1 * t2 * (t1 * t2)) * t2⁻¹ := by group
        _ = t1⁻¹ * t2⁻¹ := by rw [hsq]; group
    rw [e, hi1, hi2]
    have hzt2 := hzc t2 ht2
    calc t1 * t2 = t1 * t2 * (M.z * M.z) := by rw [hz2', mul_one]
      _ = t1 * (t2 * M.z) * M.z := by group
      _ = t1 * (M.z * t2) * M.z := by rw [hzt2]
      _ = t1 * M.z * (t2 * M.z) := by group
  · exact absurd hx2 (M.sq_ne_one_of_b0 hx h)
  · exact absurd hx2 (M.sq_ne_one_of_b0sq hx h)

theorem lemma_J23_7 :
    Nonempty (↥(ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)) ≃* QuaternionGroup 2) := by
  rw [M.centralizer_Q_eq]
  set P := ruS M.L ⊓ Subgroup.centralizer (M.B : Set G)
  have hcard := M.card_centralizer_S_B
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card hcard
  have hmemP : ∀ {x : G}, x ∈ P ↔ x ∈ ruS M.L ∧ (M.bel : G) * x = x * M.bel := by
    intro x
    rw [Subgroup.mem_inf, M.mem_centralizer_B]
  have hinv : ∀ y : CFSG.DisconnectedInvolutionGraph.Helpers.Involution P,
      ((y : P) : G) = M.z := by
    intro y
    have hy := y.2
    rw [← Subgroup.orderOf_coe] at hy
    obtain ⟨hyS, hyb⟩ := hmemP.mp (y : P).2
    refine M.eq_z_of_involution hyS hyb ?_ ?_
    · have := pow_orderOf_eq_one ((y : P) : G)
      rwa [hy] at this
    · intro h1
      rw [h1, orderOf_one] at hy
      omega
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions P := by
    intro y y' _
    exact Subtype.ext (Subtype.ext ((hinv y).trans (hinv y').symm))
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hP hrank with
    hcyc | ⟨e, he, ⟨φ⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
    rw [hcard] at hg
    have h4 : (g : G) ^ 4 = 1 := M.pow_four_S (hmemP.mp g.2).1
    have h4' : g ^ 4 = 1 := Subtype.ext (by simpa using h4)
    have := orderOf_dvd_of_pow_eq_one h4'
    rw [hg] at this
    norm_num at this
  · have hc : Nat.card (QuaternionGroup (2 ^ e)) = 2 ^ 3 := by
      rw [Nat.card_congr φ.toEquiv, hcard]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
    have he1 : e = 1 := by
      have h2 : 2 ^ e = 2 ^ 1 := by
        have : 4 * 2 ^ e = 4 * 2 ^ 1 := by rw [hc]; norm_num
        omega
      exact Nat.pow_right_injective (le_refl 2) h2
    subst he1
    exact ⟨φ.symm⟩

end RuDataM

end CFSG.Quasithin.RuType
