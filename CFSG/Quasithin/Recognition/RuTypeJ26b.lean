module

public import CFSG.Quasithin.Recognition.RuTypeJ26a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace SL3

theorem conj_n0 : ∀ g : SL(3, ZMod 2), (g ^ 2 = 1 ∧ g ≠ 1) →
    ∃ h : SL(3, ZMod 2), h * g * h⁻¹ = n0 := by
  decide +kernel

end SL3

namespace RuDataM

variable (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem isConj_z_of_V {v : G} (hv : v ∈ ruV M.L) (hv1 : v ≠ 1) : IsConj M.z v := by
  have h0 : Multiplicative.toAdd (M.ψV ⟨v, hv⟩) ≠ 0 := by
    intro h0
    apply hv1
    have : M.ψV ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective h0
    exact congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
  obtain ⟨g, hg⟩ := SL3.SL3_transitive SL3.e0 _ (by decide) h0
  obtain ⟨l, rfl⟩ := M.θ_surj g
  have hlz := M.toRuData.conj_mem_V l.2 M.z_mem_V
  have e := M.ψV_equiv l M.zV ⟨_, hlz⟩ rfl
  rw [M.ψV_zV, hg, ofAdd_toAdd] at e
  have := congrArg Subtype.val (M.ψV.injective e)
  refine ⟨⟨(l : G), (l : G)⁻¹, by group, by group⟩, ?_⟩
  show (l : G) * M.z = v * l
  calc (l : G) * M.z = (l : G) * M.z * (l : G)⁻¹ * l := by group
    _ = v * l := by rw [show (l : G) * M.z * (l : G)⁻¹ = v from this]

theorem isConj_z_of_U {u : G} (hu : u ∈ ruU M.L M.T) (hu1 : u ≠ 1) : IsConj M.z u := by
  by_cases hZ : u ∈ ruZ M.T
  · rcases M.mem_Z_iff.mp hZ with h | h
    · exact absurd h hu1
    · rw [h]
  ·
    have hψ : M.ψU ⟨u, hu⟩ ≠ 1 := fun h => hZ ((M.ψU_eq_one_iff _).mp h)
    have hv1 : M.ψU ⟨M.v1V, M.V_le_U M.v1V.2⟩ ≠ 1 := fun h =>
      M.v1_not_mem_Z ((M.ψU_eq_one_iff _).mp h)
    obtain ⟨h, hh, w, hw, e0⟩ := M.exists_conj_mod_Z hv1 hψ
    have e : u = h * (M.v1V : G) * h⁻¹ * w := e0
    have hvw : (M.v1V : G) * (h⁻¹ * w * h) ∈ ruV M.L := by
      have hw' : h⁻¹ * w * h = w := by
        rw [mul_assoc, M.Z_comm_H hw hh, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hw']
      exact mul_mem M.v1V.2 (M.toRuData.Z_le_V hw)
    have hne : (M.v1V : G) * (h⁻¹ * w * h) ≠ 1 := by
      intro h1
      apply hu1
      rw [e]
      calc h * ↑M.v1V * h⁻¹ * w = h * ((M.v1V : G) * (h⁻¹ * w * h)) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hc := M.isConj_z_of_V hvw hne
    have e2 : u = h * ((M.v1V : G) * (h⁻¹ * w * h)) * h⁻¹ := by rw [e]; group
    rw [e2]
    exact hc.trans (isConj_iff.mpr ⟨h, by group⟩)

theorem S_le_K : ruS M.L ≤ M.K := by
  intro s hs
  have hsH := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
  refine M.mem_K_iff.mpr ⟨hsH, ?_⟩
  have := M.φ_S_mem hs
  exact this.2

theorem exists_conj_not_mem_S {q : G} (hq : q ∈ ruQ M.T) (hqC : q ∉ M.HC) :
    ∃ k ∈ M.K, k * q * k⁻¹ ∉ ruS M.L := by
  have hψ : Multiplicative.toAdd (M.ψQ ⟨q, hq⟩) ≠ 0 := by
    intro h0
    apply hqC
    have : M.ψQ ⟨q, hq⟩ = 1 := Multiplicative.toAdd.injective h0
    have hk : (⟨q, hq⟩ : ruQ M.T) ∈ M.ψQ.ker := this
    rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hcardQS := M.card_Q_inf_S
  by_contra hall
  push Not at hall
  have hsub : ∀ w : Fin 2 → F4, w ≠ 0 → ∃ s ∈ ruQ M.T ⊓ ruS M.L,
      ∃ hs : s ∈ ruQ M.T, Multiplicative.toAdd (M.ψQ ⟨s, hs⟩) = w := by
    intro w hw
    obtain ⟨A, hA⟩ := Sigma.exists_sl_smul_eq hψ hw
    obtain ⟨k, hk⟩ := M.φ_surj (SemidirectProduct.inl A)
    have hkK : (k : G) ∈ M.K := M.mem_K_iff.mpr ⟨k.2, by rw [hk]; rfl⟩
    have hkq := M.conj_mem_Q k.2 hq
    refine ⟨_, ⟨hkq, hall k hkK⟩, hkq, ?_⟩
    rw [M.ψQ_conj k ⟨q, hq⟩, hk, Sigma.sigmaAct_inl, hA]
  have hHC : M.HC ≤ ruQ M.T ⊓ ruS M.L := le_inf M.HC_le_Q (M.HC_le_S)
  let f : (ruQ M.T ⊓ ruS M.L).subgroupOf (ruQ M.T) →* Multiplicative (Fin 2 → F4) :=
    M.ψQ.comp ((ruQ M.T ⊓ ruS M.L).subgroupOf (ruQ M.T)).subtype
  have hf := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le inf_le_left, hcardQS] at hf
  have hker : Nat.card f.ker = 2 ^ 7 := by
    rw [← M.card_HC]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_⟩
        invFun := fun h => ⟨⟨⟨h.1, M.HC_le_Q h.2⟩, Subgroup.mem_subgroupOf.mpr (hHC h.2)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun h => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.ψQ.ker := hx
      rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show M.ψQ ⟨h.1, _⟩ = 1
      have : (⟨h.1, M.HC_le_Q h.2⟩ : ruQ M.T) ∈ M.ψQ.ker := by
        rw [M.ψQ_ker, Subgroup.mem_subgroupOf]
        exact h.2
      exact this
  have hrange : 16 ≤ Nat.card f.range := by
    rw [← RuData.card_F4sq]
    refine Nat.card_le_card_of_injective (fun y => ⟨y, ?_⟩) ?_
    · by_cases hy : Multiplicative.toAdd y = 0
      · have : y = 1 := Multiplicative.toAdd.injective (by rw [hy]; rfl)
        rw [this]
        exact one_mem _
      · obtain ⟨s, hsQS, hs, hsy⟩ := hsub _ hy
        exact ⟨⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.mpr hsQS⟩,
          by rw [← ofAdd_toAdd y, ← hsy]; rfl⟩
    · intro a b h
      exact congrArg Subtype.val h
  rw [hker] at hf
  have : 2 ^ 7 * 16 ≤ 2 ^ 9 := by
    calc 2 ^ 7 * 16 ≤ 2 ^ 7 * Nat.card f.range := Nat.mul_le_mul_left _ hrange
      _ = 2 ^ 9 := hf
  norm_num at this

theorem exists_conj_inv_H_K {l : G} (hl : l ∈ M.L) (hlS : l ∉ ruS M.L) (hl2 : l ^ 2 = 1) :
    ∃ g ∈ M.L, g * l * g⁻¹ ∈ ruH M.T ∧ g * l * g⁻¹ ∉ M.K := by
  have hθ1 : M.θ ⟨l, hl⟩ ≠ 1 := by
    intro h1
    apply hlS
    have : (⟨l, hl⟩ : M.L) ∈ M.θ.ker := h1
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  have hθ2 : M.θ ⟨l, hl⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨l, hl⟩ : M.L) ^ 2 = 1 from Subtype.ext hl2, map_one]
  obtain ⟨g, hg⟩ := SL3.conj_n0 _ ⟨hθ2, hθ1⟩
  obtain ⟨m, rfl⟩ := M.θ_surj g
  have hθw : M.θ (m * ⟨l, hl⟩ * m⁻¹) = SL3.n0 := by rw [map_mul, map_mul, map_inv, hg]
  have hwL : (m : G) * l * (m : G)⁻¹ ∈ M.L := (m * ⟨l, hl⟩ * m⁻¹).2
  refine ⟨m, m.2, ?_, ?_⟩
  · have : (m : G) * l * (m : G)⁻¹ ∈ M.LT1 :=
      mem_pullL.mpr ⟨hwL, by
        rw [show (⟨(m : G) * l * (m : G)⁻¹, hwL⟩ : M.L) = m * ⟨l, hl⟩ * m⁻¹ from rfl, hθw]
        exact SL3.n0_mem_Stab0⟩
    rw [← M.L_inf_H] at this
    exact this.2
  · intro hK
    apply M.nel_not_mem_K
    have hs : (M.nel : G)⁻¹ * ((m : G) * l * (m : G)⁻¹) ∈ ruS M.L := by
      have hk : M.nel⁻¹ * (m * ⟨l, hl⟩ * m⁻¹) ∈ M.θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hθw, M.θ_nel, inv_mul_cancel]
      rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    have e : (M.nel : G) = ((m : G) * l * (m : G)⁻¹) *
        ((M.nel : G)⁻¹ * ((m : G) * l * (m : G)⁻¹))⁻¹ := by group
    rw [e]
    exact mul_mem hK (inv_mem (M.S_le_K hs))

theorem exists_inv_H_K : ∃ i ∈ ruH M.T, i ∉ M.K ∧ i ^ 2 = 1 ∧ IsConj M.z i := by
  obtain ⟨l0, hl0, hne⟩ : ∃ l0 ∈ M.L, M.conjU l0 ≠ ruU M.L M.T := by
    obtain ⟨l, hl, hnle⟩ := M.exists_conjU_not_le_Q
    exact ⟨l, hl, fun h => hnle (h ▸ M.U_le_Q)⟩
  obtain ⟨u, hu, huC⟩ := Set.not_subset.mp (M.conjU_inf_Q_not_le_HC hl0 hne)
  obtain ⟨huα, huQ⟩ := Subgroup.mem_inf.mp hu
  have hu0 : l0⁻¹ * u * l0 ∈ ruU M.L M.T := M.mem_conjU.mp huα
  have hu1 : u ≠ 1 := fun h => huC (h ▸ one_mem _)
  have hu01 : l0⁻¹ * u * l0 ≠ 1 := fun h => hu1 (by
    have := congrArg (fun x => l0 * x * l0⁻¹) h
    simpa [mul_assoc] using this)
  have huz : IsConj M.z u := by
    have := M.isConj_z_of_U hu0 hu01
    exact this.trans (isConj_iff.mpr ⟨l0, by group⟩)
  have hu2 : u ^ 2 = 1 := by
    have h := M.U_sq hu0
    have e : u = l0 * (l0⁻¹ * u * l0) * l0⁻¹ := by group
    rw [e, conj_pow, h]
    group
  obtain ⟨k, hk, hkS⟩ := M.exists_conj_not_mem_S huQ huC
  have hkQ := M.conj_mem_Q (M.K_le_H hk) huQ
  have hkL := M.Q_le_L hkQ
  have hk2 : (k * u * k⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hu2]
    group
  obtain ⟨g, hg, hgH, hgK⟩ := M.exists_conj_inv_H_K hkL hkS hk2
  refine ⟨g * (k * u * k⁻¹) * g⁻¹, hgH, hgK, ?_, ?_⟩
  · rw [conj_pow, hk2]
    group
  · exact huz.trans (isConj_iff.mpr ⟨g * k, by group⟩)

theorem mem_Z_of_U_comm_bel {u : G} (hu : u ∈ ruU M.L M.T) (hb : (M.bel : G) * u = u * M.bel) :
    u ∈ ruZ M.T := by
  have e := M.ψU_conj ⟨M.bel, M.bel_mem_H⟩ ⟨u, hu⟩
  have hbu : (⟨(M.bel : G) * u * (M.bel : G)⁻¹, M.conj_mem_U M.bel_mem_H hu⟩ : ruU M.L M.T) =
      ⟨u, hu⟩ := Subtype.ext (by
    show (M.bel : G) * u * (M.bel : G)⁻¹ = u
    rw [hb, mul_inv_cancel_right])
  rw [hbu] at e
  have h0 := Sigma.fix_order_three _ M.φ_bel _ e.symm
  have : M.ψU ⟨u, hu⟩ = 1 := Multiplicative.toAdd.injective h0
  exact (M.ψU_eq_one_iff _).mp this

theorem mem_Z_of_HB_U {x y : G} (hx : x ∈ M.HB) (hy : y ∈ M.HB) (hxy : x⁻¹ * y ∈ ruU M.L M.T) :
    x⁻¹ * y ∈ ruZ M.T := by
  refine M.mem_Z_of_U_comm_bel hxy ?_
  have hxb := (M.mem_HB.mp hx).2
  have hyb := (M.mem_HB.mp hy).2
  have hxb' : (M.bel : G) * x⁻¹ = x⁻¹ * M.bel := (Commute.inv_right hxb).eq
  rw [← mul_assoc, hxb', mul_assoc, hyb, mul_assoc]

theorem exists_HB_conj_z {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1)
    (hib : (M.bel : G) * i = i * M.bel) : ∃ x ∈ ruQ M.T, x * i * x⁻¹ = i * M.z := by
  obtain ⟨t1, ht1, hb1, hχ1⟩ := M.exists_t1
  obtain ⟨t2, ht2, hb2, hχ2⟩ := M.exists_t2
  obtain ⟨t3, ht3, hb3, hχ3⟩ := M.exists_centralizer_S_B (A := !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    (Or.inr (Or.inl rfl))
  have hB1 : t1 ∈ M.HB := M.mem_HB.mpr ⟨ht1, hb1⟩
  have hB2 : t2 ∈ M.HB := M.mem_HB.mpr ⟨ht2, hb2⟩
  have hB3 : t3 ∈ M.HB := M.mem_HB.mpr ⟨ht3, hb3⟩
  have hi' := inv_eq_self_of_sq hi2
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  have hconjHB : ∀ x ∈ M.HB, i * x * i⁻¹ ∈ M.HB := by
    intro x hx
    obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
    refine ⟨M.conj_mem_Q hiH (Subgroup.mem_inf.mp hx).1, (M.mem_centralizer_B).mpr ?_⟩
    have hib' : (M.bel : G) * i⁻¹ = i⁻¹ * M.bel := (Commute.inv_right hib).eq
    calc (M.bel : G) * (i * x * i⁻¹) = i * ((M.bel : G) * x) * i⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, hib]; group
      _ = i * (x * M.bel) * i⁻¹ := by rw [hxb]
      _ = i * x * i⁻¹ * M.bel := by rw [mul_assoc i, mul_assoc x, hib']; group
  have hswap : ∀ (ta tb : G) (hta : ta ∈ ruS M.L) (htb : tb ∈ ruS M.L),
      ta ∈ M.HB → tb ∈ M.HB →
      Multiplicative.toAdd (M.χ ⟨tb, htb⟩) =
        stAct SL3.n0 (Multiplicative.toAdd (M.χ ⟨ta, hta⟩)) →
      (i * ta * i⁻¹)⁻¹ * tb ∈ ruZ M.T := by
    intro ta tb hta htb hBa hBb hab
    have h1 := M.conj_HC_of_not_mem_K hiH hK (M.HB_le_HC hBa)
    have hnt : (M.nel : G) * ta * (M.nel : G)⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.nel.2) ta).mp hta
    have h2 : ((M.nel : G) * ta * (M.nel : G)⁻¹)⁻¹ * tb ∈ ruU M.L M.T := by
      have hk : (⟨_, hnt⟩ : ruS M.L)⁻¹ * ⟨tb, htb⟩ ∈ M.χ.ker := by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        rw [M.toAdd_χ_mul, M.toAdd_χ_inv, M.χ_conj M.nel ⟨ta, hta⟩, M.θ_nel, hab, toAdd_one]
        ext i j
        have h : ∀ a : ZMod 2, a + a = 0 := by decide
        exact h _
      rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
      exact M.V_le_U hk
    have hU : (i * ta * i⁻¹)⁻¹ * tb ∈ ruU M.L M.T := by
      have e : (i * ta * i⁻¹)⁻¹ * tb = (i * ta * i⁻¹)⁻¹ * ((M.nel : G) * ta * (M.nel : G)⁻¹) *
          (((M.nel : G) * ta * (M.nel : G)⁻¹)⁻¹ * tb) := by group
      rw [e]
      exact mul_mem h1 h2
    exact M.mem_Z_of_HB_U (hconjHB ta hBa) hBb hU
  have ha := hswap t1 t2 ht1 ht2 hB1 hB2 (by rw [hχ1, hχ2, SL3.n0_b0mat])
  have ha' := hswap t2 t1 ht2 ht1 hB2 hB1 (by rw [hχ1, hχ2, SL3.n0_swap])
  have hc : (t1 * t2)⁻¹ * t3 ∈ ruZ M.T := by
    have hk : (⟨t1 * t2, mul_mem ht1 ht2⟩ : ruS M.L)⁻¹ * ⟨t3, ht3⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [M.toAdd_χ_mul, M.toAdd_χ_inv,
        show (⟨t1 * t2, mul_mem ht1 ht2⟩ : ruS M.L) = ⟨t1, ht1⟩ * ⟨t2, ht2⟩ from rfl,
        M.toAdd_χ_mul, hχ1, hχ2, hχ3, toAdd_one]
      decide
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact M.mem_Z_of_U_comm_bel (M.V_le_U hk) (by
      have e1 : (M.bel : G) * (t1 * t2) = (t1 * t2) * M.bel := by
        rw [← mul_assoc, hb1, mul_assoc, hb2, mul_assoc]
      have e2 : (M.bel : G) * (t1 * t2)⁻¹ = (t1 * t2)⁻¹ * M.bel := (Commute.inv_right e1).eq
      show (M.bel : G) * ((t1 * t2)⁻¹ * t3) = ((t1 * t2)⁻¹ * t3) * M.bel
      rw [← mul_assoc, e2, mul_assoc, hb3, mul_assoc])
  have h12 : ⁅t1, t2⁆ = M.z := (M.comm_HB hB1 hB2).2 (by
    rw [show Multiplicative.toAdd (M.χ ⟨t1, (M.mem_HB.mp hB1).1⟩) = _ from hχ1,
      show Multiplicative.toAdd (M.χ ⟨t2, (M.mem_HB.mp hB2).1⟩) = _ from hχ2]
    decide)
  have hzc : ∀ w ∈ ruZ M.T, ∀ g ∈ ruH M.T, w * g = g * w := fun w hw g hg => M.Z_comm_H hw hg
  have hz2 : M.z * M.z = 1 := by rw [← pow_two]; exact M.z_sq
  set a := (i * t1 * i⁻¹)⁻¹ * t2
  set a' := (i * t2 * i⁻¹)⁻¹ * t1
  set c := (t1 * t2)⁻¹ * t3
  have hHt1 : t1 ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T ht1)
  have hHt2 : t2 ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T ht2)
  have e1 : i * t1 * i⁻¹ = t2 * a⁻¹ := by simp only [a]; group
  have e2 : i * t2 * i⁻¹ = t1 * a'⁻¹ := by simp only [a']; group
  have e3 : t3 = t1 * t2 * c := by simp only [c]; group
  have hZinv : ∀ w ∈ ruZ M.T, w⁻¹ = w := fun w hw => by
    rcases M.mem_Z_iff.mp hw with h | h <;> rw [h]
    · exact inv_one
    · exact inv_eq_of_mul_eq_one_right hz2
  have hcH : c ∈ ruH M.T :=
    M.toRuData.T_le_H (M.toRuData.S_le_T (M.toRuData.V_le_S (M.toRuData.Z_le_V hc)))
  have haa' : a = a' := by
    have h1 : t1 = t1 * a'⁻¹ * a⁻¹ := by
      calc t1 = (i * i) * t1 * (i * i) := by rw [hii, one_mul, mul_one]
        _ = i * (i * t1 * i⁻¹) * i⁻¹ := by rw [hi']; group
        _ = i * (t2 * a⁻¹) * i⁻¹ := by rw [e1]
        _ = (i * t2 * i⁻¹) * (i * a⁻¹ * i⁻¹) := by group
        _ = t1 * a'⁻¹ * a⁻¹ := by
            rw [e2, show i * a⁻¹ * i⁻¹ = a⁻¹ by
              rw [← hzc _ (inv_mem ha) i hiH, mul_inv_cancel_right]]
    have h2 : a'⁻¹ * a⁻¹ = 1 := by
      have h3 : t1 * (a'⁻¹ * a⁻¹) = t1 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
      exact mul_left_cancel h3
    rw [hZinv a ha, hZinv a' ha'] at h2
    rw [eq_inv_of_mul_eq_one_left h2, hZinv a ha]
  have hit3 : i * t3 * i⁻¹ = t3 * M.z := by
    have h21 : t2 * t1 = t1 * t2 * M.z := by
      rw [commutatorElement_def] at h12
      calc t2 * t1 = (t1 * t2 * t1⁻¹ * t2⁻¹)⁻¹ * (t1 * t2) := by group
        _ = M.z⁻¹ * (t1 * t2) := by rw [h12]
        _ = M.z * (t1 * t2) := by rw [hZinv _ M.z_mem_Z]
        _ = t1 * t2 * M.z := hzc _ M.z_mem_Z _ (mul_mem hHt1 hHt2)
    have hic : i * c * i⁻¹ = c := by rw [← hzc _ hc i hiH, mul_inv_cancel_right]
    have haa : a⁻¹ * a⁻¹ = 1 := by
      rw [hZinv a ha]
      rcases M.mem_Z_iff.mp ha with h | h <;> rw [h]
      · exact one_mul 1
      · exact hz2
    have hat1 : a⁻¹ * t1 = t1 * a⁻¹ := hzc _ (inv_mem ha) t1 hHt1
    have hcz : M.z * c = c * M.z := hzc _ M.z_mem_Z c hcH
    calc i * t3 * i⁻¹ = (i * t1 * i⁻¹) * (i * t2 * i⁻¹) * (i * c * i⁻¹) := by rw [e3]; group
      _ = (t2 * a⁻¹) * (t1 * a⁻¹) * c := by rw [e1, e2, hic, ← haa']
      _ = t2 * (a⁻¹ * t1) * a⁻¹ * c := by group
      _ = t2 * (t1 * a⁻¹) * a⁻¹ * c := by rw [hat1]
      _ = t2 * t1 * (a⁻¹ * a⁻¹) * c := by group
      _ = t2 * t1 * c := by rw [haa, mul_one]
      _ = t1 * t2 * M.z * c := by rw [h21]
      _ = t1 * t2 * (M.z * c) := by group
      _ = t1 * t2 * (c * M.z) := by rw [hcz]
      _ = t3 * M.z := by rw [e3]; group
  refine ⟨t3, (Subgroup.mem_inf.mp hB3).1, ?_⟩
  have hzi : M.z * i = i * M.z := hzc _ M.z_mem_Z i hiH
  have hz3 : M.z * t3 = t3 * M.z :=
    hzc _ M.z_mem_Z t3 (M.toRuData.T_le_H (M.toRuData.S_le_T ht3))
  calc t3 * i * t3⁻¹ = t3 * (i * t3 * i⁻¹)⁻¹ * i := by group
    _ = t3 * (t3 * M.z)⁻¹ * i := by rw [hit3]
    _ = t3 * (M.z * t3)⁻¹ * i := by rw [← hz3]
    _ = M.z⁻¹ * i := by group
    _ = i * M.z := by rw [inv_eq_of_mul_eq_one_right hz2, hzi]

omit [Finite G] in
theorem Q_le_K : ruQ M.T ≤ M.K := by
  intro q hq
  have hqH := pCoreOf_le 2 _ hq
  refine M.mem_K_iff.mpr ⟨hqH, ?_⟩
  have : (⟨q, hqH⟩ : ruH M.T) ∈ M.φ.ker := by
    rw [M.φ_ker, Subgroup.mem_subgroupOf]
    exact hq
  rw [MonoidHom.mem_ker.mp this]
  rfl

theorem conj_of_inv_coset_B {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1)
    (hib : (M.bel : G) * i = i * M.bel) {q : ruQ M.T} (hq : (i * (q : G)) ^ 2 = 1) :
    ∃ g ∈ ruQ M.T, g * i * g⁻¹ = i * q := by
  obtain ⟨x, hxQ, hx⟩ := M.exists_HB_conj_z hiH hK hi2 hib
  obtain ⟨y, hyQ, hy | hy⟩ := M.conj_of_inv_coset hiH hK hi2 hq
  · exact ⟨y⁻¹, inv_mem hyQ, by rw [hy]; group⟩
  · exact ⟨y⁻¹ * x, mul_mem (inv_mem hyQ) hxQ, by rw [hy, ← hx]; group⟩

theorem exists_inv_centralizer_B : ∃ i ∈ ruH M.T, i ∉ M.K ∧ i ^ 2 = 1 ∧
    (M.bel : G) * i = i * M.bel ∧ IsConj M.z i := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨i1, hi1H, hi1K, hi12, hi1z⟩ := M.exists_inv_H_K
  obtain ⟨js, hjs, hjsb⟩ := Sigma.exists_outside_comm _ M.φ_bel
  obtain ⟨x1, hx1⟩ := Sigma.conj_g0 _ (M.φ_inv_props hi1H hi1K hi12)
  obtain ⟨x2, hx2⟩ := Sigma.conj_g0 _ hjs
  obtain ⟨h, hh⟩ := M.φ_surj (x2⁻¹ * x1)
  set i := (h : G) * i1 * (h : G)⁻¹
  have hiH : i ∈ ruH M.T := mul_mem (mul_mem h.2 hi1H) (inv_mem h.2)
  have hiK : i ∉ M.K := fun hK => hi1K (by
    have := M.conj_mem_K (inv_mem h.2) hK
    simpa [i, mul_assoc] using this)
  have hi2 : i ^ 2 = 1 := by
    rw [show i ^ 2 = (h : G) * i1 ^ 2 * (h : G)⁻¹ from conj_pow, hi12]
    group
  have hφi : M.φ ⟨i, hiH⟩ = js := by
    have e : (⟨i, hiH⟩ : ruH M.T) = h * ⟨i1, hi1H⟩ * h⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hh]
    calc x2⁻¹ * x1 * M.φ ⟨i1, hi1H⟩ * (x2⁻¹ * x1)⁻¹ =
        x2⁻¹ * (x1 * M.φ ⟨i1, hi1H⟩ * x1⁻¹) * x2 := by group
      _ = js := by rw [hx1, ← hx2]; group
  have hiz : IsConj M.z i := hi1z.trans (isConj_iff.mpr ⟨h, rfl⟩)
  have hbi : (i : G)⁻¹ * ((M.bel : G) * i * (M.bel : G)⁻¹) ∈ ruQ M.T := by
    have hmem : (i : G)⁻¹ * ((M.bel : G) * i * (M.bel : G)⁻¹) ∈ ruH M.T :=
      mul_mem (inv_mem hiH) (mul_mem (mul_mem M.bel_mem_H hiH) (inv_mem M.bel_mem_H))
    have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
      rw [MonoidHom.mem_ker]
      have e : (⟨_, hmem⟩ : ruH M.T) =
          (⟨i, hiH⟩ : ruH M.T)⁻¹ * (⟨M.bel, M.bel_mem_H⟩ * ⟨i, hiH⟩ * ⟨M.bel, M.bel_mem_H⟩⁻¹) :=
        rfl
      rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hφi, ← hjsb]
      group
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  set d := (i : G)⁻¹ * ((M.bel : G) * i * (M.bel : G)⁻¹)
  have hmapQ : ∀ q : ruQ M.T, d * ((M.bel : G) * q * (M.bel : G)⁻¹) ∈ ruQ M.T := fun q =>
    mul_mem hbi (M.conj_mem_Q M.bel_mem_H q.2)
  have hconj : ∀ q : ruQ M.T, i * (d * ((M.bel : G) * q * (M.bel : G)⁻¹)) =
      (M.bel : G) * (i * q) * (M.bel : G)⁻¹ := fun q => by simp only [d]; group
  let Y := {q : ruQ M.T // (i * (q : G)) ^ 2 = 1}
  let f : Y → Y := fun q => ⟨⟨_, hmapQ q.1⟩, by
    rw [hconj, conj_pow, q.2]
    group⟩
  have hf : Function.Injective f := by
    intro q q' hqq
    have h1 : i * (d * ((M.bel : G) * q.1 * (M.bel : G)⁻¹)) =
        i * (d * ((M.bel : G) * q'.1 * (M.bel : G)⁻¹)) :=
      congrArg (i * ·) (congrArg (fun y : Y => ((y.1 : ruQ M.T) : G)) hqq)
    rw [hconj, hconj] at h1
    have h2 : i * (q.1 : G) = i * q'.1 := by
      have := congrArg (fun x => (M.bel : G)⁻¹ * x * M.bel) h1
      simpa [mul_assoc] using this
    exact Subtype.ext (Subtype.ext (mul_left_cancel h2))
  have : Fintype Y := Fintype.ofFinite Y
  let σ : Equiv.Perm Y := Equiv.ofBijective f hf.bijective_of_finite
  have hσk : ∀ (k : ℕ) (q : Y), i * (((σ ^ k) q).1 : G) =
      (M.bel : G) ^ k * (i * q.1) * ((M.bel : G) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro q; simp
    | succ k ih =>
      intro q
      rw [pow_succ', Equiv.Perm.mul_apply]
      show i * (d * ((M.bel : G) * ((σ ^ k) q).1 * (M.bel : G)⁻¹)) = _
      rw [hconj, ih q]
      group
  have hσ3 : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun q => Subtype.ext (Subtype.ext ?_)
    have h := hσk 3 q
    rw [M.bel_pow_three] at h
    simp only [one_mul, inv_one, mul_one] at h
    exact mul_left_cancel h
  have hY : ¬ 3 ∣ Fintype.card Y := by
    rw [← Nat.card_eq_fintype_card, M.card_inv_coset hiH hiK hi2]
    norm_num
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_fixed_point_of_prime hY hσ3
  have hqfix := hσk 1 q
  rw [pow_one, pow_one, hq] at hqfix
  refine ⟨i * q.1, mul_mem hiH (pCoreOf_le 2 _ q.1.2), fun hK => hiK ?_, q.2, ?_, ?_⟩
  · have := mul_mem hK (inv_mem (M.Q_le_K q.1.2))
    simpa using this
  · calc (M.bel : G) * (i * q.1) = (M.bel : G) * (i * q.1) * (M.bel : G)⁻¹ * M.bel := by group
      _ = i * q.1 * M.bel := by rw [← hqfix]
  ·
    have hi'H : i * q.1 ∈ ruH M.T := mul_mem hiH (pCoreOf_le 2 _ q.1.2)
    have hi'K : i * q.1 ∉ M.K := fun hK => hiK (by
      have := mul_mem hK (inv_mem (M.Q_le_K q.1.2))
      simpa using this)
    have hi'b : (M.bel : G) * (i * q.1) = (i * q.1) * M.bel := by
      calc (M.bel : G) * (i * q.1) = (M.bel : G) * (i * q.1) * (M.bel : G)⁻¹ * M.bel := by
            group
        _ = i * q.1 * M.bel := by rw [← hqfix]
    have hz2 : M.z * M.z = 1 := by rw [← pow_two]; exact M.z_sq
    obtain ⟨y, hyQ, hy | hy⟩ := M.conj_of_inv_coset hiH hiK hi2 q.2
    · rw [hy]
      exact hiz.trans (isConj_iff.mpr ⟨y⁻¹, by group⟩)
    · obtain ⟨x, hxQ, hx⟩ := M.exists_HB_conj_z hi'H hi'K q.2 hi'b
      have hzc : M.z * y = y * M.z := M.Z_comm_H M.z_mem_Z (pCoreOf_le 2 _ hyQ)
      have h1 : i * q.1 * M.z = y⁻¹ * i * y := by
        rw [hy]
        calc y⁻¹ * (i * M.z) * y * M.z = y⁻¹ * i * (M.z * y) * M.z := by group
          _ = y⁻¹ * i * (y * M.z) * M.z := by rw [hzc]
          _ = y⁻¹ * i * y * (M.z * M.z) := by group
          _ = y⁻¹ * i * y := by rw [hz2, mul_one]
      refine hiz.trans ?_
      have h2 : IsConj i (i * q.1 * M.z) := by
        rw [h1]
        exact isConj_iff.mpr ⟨y⁻¹, by group⟩
      rw [← hx] at h2
      exact h2.trans (isConj_iff.mpr ⟨x⁻¹, by group⟩)

theorem conj_inv_H_K {i0 : G} (hi0H : i0 ∈ ruH M.T) (hi0K : i0 ∉ M.K) (hi02 : i0 ^ 2 = 1)
    (hi0b : (M.bel : G) * i0 = i0 * M.bel) {j : G} (hjH : j ∈ ruH M.T) (hjK : j ∉ M.K)
    (hj2 : j ^ 2 = 1) : ∃ h ∈ ruH M.T, h * i0 * h⁻¹ = j := by
  obtain ⟨x1, hx1⟩ := Sigma.conj_g0 _ (M.φ_inv_props hjH hjK hj2)
  obtain ⟨x0, hx0⟩ := Sigma.conj_g0 _ (M.φ_inv_props hi0H hi0K hi02)
  obtain ⟨h, hh⟩ := M.φ_surj (x0⁻¹ * x1)
  set j' := (h : G) * j * (h : G)⁻¹
  have hj'H : j' ∈ ruH M.T := mul_mem (mul_mem h.2 hjH) (inv_mem h.2)
  have hq : i0⁻¹ * j' ∈ ruQ M.T := by
    have hmem : i0⁻¹ * j' ∈ ruH M.T := mul_mem (inv_mem hi0H) hj'H
    have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
      rw [MonoidHom.mem_ker]
      have e : (⟨_, hmem⟩ : ruH M.T) = (⟨i0, hi0H⟩ : ruH M.T)⁻¹ * (h * ⟨j, hjH⟩ * h⁻¹) := rfl
      rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hh]
      calc (M.φ ⟨i0, hi0H⟩)⁻¹ * (x0⁻¹ * x1 * M.φ ⟨j, hjH⟩ * (x0⁻¹ * x1)⁻¹) =
          (M.φ ⟨i0, hi0H⟩)⁻¹ * (x0⁻¹ * (x1 * M.φ ⟨j, hjH⟩ * x1⁻¹) * x0) := by group
        _ = (M.φ ⟨i0, hi0H⟩)⁻¹ * (x0⁻¹ * (x0 * M.φ ⟨i0, hi0H⟩ * x0⁻¹) * x0) := by
            rw [hx1, hx0]
        _ = 1 := by group
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hq2 : (i0 * ((⟨_, hq⟩ : ruQ M.T) : G)) ^ 2 = 1 := by
    show (i0 * (i0⁻¹ * j')) ^ 2 = 1
    rw [mul_inv_cancel_left, show j' ^ 2 = (h : G) * j ^ 2 * (h : G)⁻¹ from conj_pow, hj2]
    group
  obtain ⟨g, hgQ, hg⟩ := M.conj_of_inv_coset_B hi0H hi0K hi02 hi0b hq2
  refine ⟨(h : G)⁻¹ * g, mul_mem (inv_mem h.2) (pCoreOf_le 2 _ hgQ), ?_⟩
  have e : i0 * ((⟨_, hq⟩ : ruQ M.T) : G) = j' := mul_inv_cancel_left i0 j'
  calc (h : G)⁻¹ * g * i0 * ((h : G)⁻¹ * g)⁻¹ = (h : G)⁻¹ * (g * i0 * g⁻¹) * h := by group
    _ = (h : G)⁻¹ * j' * h := by rw [hg, e]
    _ = j := by simp only [j']; group

theorem card_inv_H_K : Nat.card {h : G // h ∈ ruH M.T ∧ h ∉ M.K ∧ h ^ 2 = 1} = 640 := by
  classical
  obtain ⟨i0, hi0H, hi0K, hi02, hi0b, -⟩ := M.exists_inv_centralizer_B
  let Out := {g : SigmaL2F4 // g ^ 2 = 1 ∧ g.right ≠ 1}
  let Inv := {h : G // h ∈ ruH M.T ∧ h ∉ M.K ∧ h ^ 2 = 1}
  let f : Inv → Out := fun h => ⟨M.φ ⟨h.1, h.2.1⟩, M.φ_inv_props h.2.1 h.2.2.1 h.2.2.2⟩
  have hrep : ∀ g : Out, ∃ ig : G, ∃ hig : ig ∈ ruH M.T, ig ∉ M.K ∧ ig ^ 2 = 1 ∧
      M.φ ⟨ig, hig⟩ = g.1 := by
    intro g
    obtain ⟨x0, hx0⟩ := Sigma.conj_g0 _ (M.φ_inv_props hi0H hi0K hi02)
    obtain ⟨x, hx⟩ := Sigma.conj_g0 _ g.2
    obtain ⟨h, hh⟩ := M.φ_surj (x⁻¹ * x0)
    have hmem : (h : G) * i0 * (h : G)⁻¹ ∈ ruH M.T := mul_mem (mul_mem h.2 hi0H) (inv_mem h.2)
    refine ⟨_, hmem, fun hK => hi0K ?_, ?_, ?_⟩
    · have := M.conj_mem_K (inv_mem h.2) hK
      simpa [mul_assoc] using this
    · rw [conj_pow, hi02]
      group
    · have e : (⟨_, hmem⟩ : ruH M.T) = h * ⟨i0, hi0H⟩ * h⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hh]
      calc x⁻¹ * x0 * M.φ ⟨i0, hi0H⟩ * (x⁻¹ * x0)⁻¹ =
          x⁻¹ * (x0 * M.φ ⟨i0, hi0H⟩ * x0⁻¹) * x := by group
        _ = g.1 := by rw [hx0, ← hx]; group
  choose ig hig higK hig2 higφ using hrep
  have hfib : ∀ g : Out, Nat.card {h : Inv // f h = g} = 64 := by
    intro g
    rw [← M.card_inv_coset (hig g) (higK g) (hig2 g)]
    have hQ : ∀ h : {h : Inv // f h = g}, (ig g)⁻¹ * h.1.1 ∈ ruQ M.T := by
      intro h
      have hmem : (ig g)⁻¹ * h.1.1 ∈ ruH M.T := mul_mem (inv_mem (hig g)) h.1.2.1
      have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨_, hmem⟩ : ruH M.T) = (⟨ig g, hig g⟩ : ruH M.T)⁻¹ * ⟨h.1.1, h.1.2.1⟩ := rfl
        have hf := congrArg Subtype.val h.2
        rw [e, map_mul, map_inv, higφ]
        rw [show M.φ ⟨h.1.1, h.1.2.1⟩ = g.1 from hf]
        exact inv_mul_cancel _
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    refine Nat.card_congr
      { toFun := fun h => ⟨⟨_, hQ h⟩, by
          show (ig g * ((ig g)⁻¹ * h.1.1)) ^ 2 = 1
          rw [mul_inv_cancel_left]
          exact h.1.2.2.2⟩
        invFun := fun q => ⟨⟨ig g * q.1, mul_mem (hig g) (pCoreOf_le 2 _ q.1.2), fun hK =>
          higK g (by
            have := mul_mem hK (inv_mem (M.Q_le_K q.1.2))
            simpa using this), q.2⟩, ?_⟩
        left_inv := fun h => Subtype.ext (Subtype.ext (by simp))
        right_inv := fun q => Subtype.ext (Subtype.ext (by simp)) }
    apply Subtype.ext
    show M.φ ⟨ig g * q.1, _⟩ = g.1
    have hq1 : M.φ ⟨q.1, pCoreOf_le 2 _ q.1.2⟩ = 1 := by
      have : (⟨q.1, pCoreOf_le 2 _ q.1.2⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact q.1.2
      exact this
    have e : (⟨ig g * q.1, mul_mem (hig g) (pCoreOf_le 2 _ q.1.2)⟩ : ruH M.T) =
        ⟨ig g, hig g⟩ * ⟨q.1, pCoreOf_le 2 _ q.1.2⟩ := rfl
    rw [e, map_mul, hq1, mul_one, higφ]
  have h10 : Nat.card Out = 10 := by
    rw [Nat.card_eq_fintype_card]
    convert Sigma.card_outside
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h10]
  rfl

theorem mem_U_of_HC_sq {t : G} (ht : t ∈ M.HC) (ht2 : t ^ 2 = 1) : t ∈ ruU M.L M.T := by
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U ht
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  have hxu : x * u = u * x :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (M.HB_le_HC hx)).2 u hu).symm
  have hx2 : x ^ 2 = 1 := by
    have hu2 : u * u = 1 := by rw [← pow_two]; exact M.U_sq hu
    have h := ht2
    rw [pow_two] at h ⊢
    calc x * x = x * x * (u * u) := by rw [hu2, mul_one]
      _ = x * (x * u) * u := by group
      _ = x * (u * x) * u := by rw [hxu]
      _ = x * u * (x * u) := by group
      _ = 1 := h
  by_cases hx1 : x = 1
  · rw [hx1, one_mul]; exact hu
  · rw [M.eq_z_of_involution hxS hxb hx2 hx1]
    exact mul_mem (M.V_le_U M.z_mem_V) hu

theorem comm_HC_mem_Z {a b : G} (ha : a ∈ M.HC) (hb : b ∈ M.HC) : ⁅a, b⁆ ∈ ruZ M.T := by
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U ha
  obtain ⟨y, hy, u', hu', rfl⟩ := M.exists_HB_U hb
  have huc : ∀ g ∈ M.HC, u * g = g * u := fun g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u hu
  have hu'c : ∀ g ∈ M.HC, u' * g = g * u' := fun g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 u' hu'
  have h1 := huc y (M.HB_le_HC hy)
  have h2 := hu'c x (M.HB_le_HC hx)
  have h3 := huc u' (M.U_le_HC hu')
  have e : ⁅x * u, y * u'⁆ = ⁅x, y⁆ := by
    simp only [commutatorElement_def]
    calc x * u * (y * u') * (x * u)⁻¹ * (y * u')⁻¹
        = x * (u * y) * u' * u⁻¹ * x⁻¹ * u'⁻¹ * y⁻¹ := by group
      _ = x * (y * u) * u' * u⁻¹ * x⁻¹ * u'⁻¹ * y⁻¹ := by rw [h1]
      _ = x * y * (u * u') * u⁻¹ * x⁻¹ * u'⁻¹ * y⁻¹ := by group
      _ = x * y * (u' * u) * u⁻¹ * x⁻¹ * u'⁻¹ * y⁻¹ := by rw [h3]
      _ = x * y * (u' * x⁻¹) * u'⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * u') * u'⁻¹ * y⁻¹ := by
          rw [show u' * x⁻¹ = x⁻¹ * u' by
            calc u' * x⁻¹ = x⁻¹ * (x * u') * x⁻¹ := by group
              _ = x⁻¹ * (u' * x) * x⁻¹ := by rw [h2]
              _ = x⁻¹ * u' := by group]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [e]
  by_cases hc : Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩) = 0 ∨
      Multiplicative.toAdd (M.χ ⟨x, (M.mem_HB.mp hx).1⟩) =
        Multiplicative.toAdd (M.χ ⟨y, (M.mem_HB.mp hy).1⟩)
  · rw [(M.comm_HB hx hy).1 hc]
    exact one_mem _
  · rw [(M.comm_HB hx hy).2 hc]
    exact M.z_mem_Z

theorem sq_HC_mem_Z {a : G} (ha : a ∈ M.HC) : a ^ 2 ∈ ruZ M.T := by
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U ha
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  have hxu : x * u = u * x :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (M.HB_le_HC hx)).2 u hu).symm
  have hu2 : u * u = 1 := by rw [← pow_two]; exact M.U_sq hu
  have e : (x * u) ^ 2 = x ^ 2 := by
    rw [pow_two, pow_two]
    calc x * u * (x * u) = x * (u * x) * u := by group
      _ = x * (x * u) * u := by rw [hxu]
      _ = x * x * (u * u) := by group
      _ = x * x := by rw [hu2, mul_one]
  rw [e]
  have hV := M.sq_mem_V hxS
  have hb : (M.bel : G) * x ^ 2 = x ^ 2 * M.bel := (Commute.pow_right hxb 2).eq
  rcases M.eq_of_mem_V_comm_bel hV hb with h | h <;> rw [h]
  · exact one_mem _
  · exact M.z_mem_Z

theorem frattini_HC : frattiniOf M.HC = ruZ M.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥M.HC) := ⟨IsPGroup.of_card M.card_HC⟩
  unfold frattiniOf
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨y, hy | ⟨x, rfl⟩, rfl⟩
    · have hle : _root_.commutator ↥M.HC ≤ (ruZ M.T).comap M.HC.subtype := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro a _ b _
        exact M.comm_HC_mem_Z a.2 b.2
      exact hle hy
    · exact M.sq_HC_mem_Z x.2
  · intro w hw
    rcases M.mem_Z_iff.mp hw with rfl | rfl
    · exact one_mem _
    · obtain ⟨t1, ht1, hb1, hχ1⟩ := M.exists_t1
      have hB1 : t1 ∈ M.HB := M.mem_HB.mpr ⟨ht1, hb1⟩
      have hsq := M.sq_HC_mem_Z (M.HB_le_HC hB1)
      have ht1z : t1 ^ 2 = M.z := by
        rcases M.mem_Z_iff.mp hsq with h | h
        · exact absurd h (M.sq_ne_one_of_b0 ht1 hχ1)
        · exact h
      refine Subgroup.subset_closure ⟨⟨t1, M.HB_le_HC hB1⟩ ^ 2, Or.inr ⟨_, rfl⟩, ?_⟩
      show ((⟨t1, M.HB_le_HC hB1⟩ ^ 2 : ↥M.HC) : G) = M.z
      rw [SubgroupClass.coe_pow]
      exact ht1z

theorem lemma_J26 :
    (∀ i j : G, (i ∈ ruH M.T ∧ i ∉ M.K ∧ i ^ 2 = 1) → (j ∈ ruH M.T ∧ j ∉ M.K ∧ j ^ 2 = 1) →
        ∃ h ∈ ruH M.T, h * i * h⁻¹ = j) ∧
      Nat.card {h : G // h ∈ ruH M.T ∧ h ∉ M.K ∧ h ^ 2 = 1} = 640 ∧
      (∀ i ∈ ruH M.T, i ∉ M.K → i ^ 2 = 1 → IsConj M.z i) ∧
      (∀ l ∈ M.L, l ∉ ruS M.L → l ^ 2 = 1 → IsConj M.z l) ∧
      (∀ q ∈ ruQ M.T, q ^ 2 = 1 → q ≠ 1 → IsConj M.z q) ∧
      Subgroup.closure {t | t ∈ M.HC ∧ t ^ 2 = 1} = ruU M.L M.T ∧
      frattiniOf M.HC = ruZ M.T ∧ (∀ u ∈ ruU M.L M.T, u ≠ 1 → IsConj M.z u) := by
  obtain ⟨i0, hi0H, hi0K, hi02, hi0b, hi0z⟩ := M.exists_inv_centralizer_B
  have h1 : ∀ i j : G, (i ∈ ruH M.T ∧ i ∉ M.K ∧ i ^ 2 = 1) →
      (j ∈ ruH M.T ∧ j ∉ M.K ∧ j ^ 2 = 1) → ∃ h ∈ ruH M.T, h * i * h⁻¹ = j := by
    rintro i j ⟨hiH, hiK, hi2⟩ ⟨hjH, hjK, hj2⟩
    obtain ⟨g, hg, rfl⟩ := M.conj_inv_H_K hi0H hi0K hi02 hi0b hiH hiK hi2
    obtain ⟨g', hg', rfl⟩ := M.conj_inv_H_K hi0H hi0K hi02 hi0b hjH hjK hj2
    exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by group⟩
  have h1z : ∀ i ∈ ruH M.T, i ∉ M.K → i ^ 2 = 1 → IsConj M.z i := by
    intro i hiH hiK hi2
    obtain ⟨g, -, rfl⟩ := M.conj_inv_H_K hi0H hi0K hi02 hi0b hiH hiK hi2
    exact hi0z.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have h2 : ∀ l ∈ M.L, l ∉ ruS M.L → l ^ 2 = 1 → IsConj M.z l := by
    intro l hl hlS hl2
    obtain ⟨g, -, hgH, hgK⟩ := M.exists_conj_inv_H_K hl hlS hl2
    have := h1z _ hgH hgK (by
      rw [conj_pow, hl2]; group)
    exact this.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hΩ : Subgroup.closure {t | t ∈ M.HC ∧ t ^ 2 = 1} = ruU M.L M.T := by
    refine le_antisymm ?_ (fun u hu =>
      Subgroup.subset_closure (show u ∈ {t | t ∈ M.HC ∧ t ^ 2 = 1} from ⟨M.U_le_HC hu, M.U_sq hu⟩))
    rw [Subgroup.closure_le]
    rintro t ⟨ht, ht2⟩
    exact M.mem_U_of_HC_sq ht ht2
  refine ⟨h1, M.card_inv_H_K, h1z, h2, ?_, hΩ, M.frattini_HC, fun u hu hu1 =>
    M.isConj_z_of_U hu hu1⟩
  intro q hq hq2 hq1
  by_cases hqC : q ∈ M.HC
  · exact M.isConj_z_of_U (M.mem_U_of_HC_sq hqC hq2) hq1
  · obtain ⟨k, hk, hkS⟩ := M.exists_conj_not_mem_S hq hqC
    have := h2 _ (M.Q_le_L (M.conj_mem_Q (M.K_le_H hk) hq)) hkS (by
      rw [conj_pow, hq2]; group)
    exact this.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)

end RuDataM

end CFSG.Quasithin.RuType
