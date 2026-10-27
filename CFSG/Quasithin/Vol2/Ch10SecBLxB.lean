module

public import CFSG.Quasithin.Vol2.Ch10SecBLxA
public import CFSG.RankThree.PartOne.HNB.Tools

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.BLx

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T S X Y V : Subgroup G} {b : G}

theorem sq_eq_one_of_mem_blockQ (m : Mem T S X Y V b 2) (hU : blockU Y ≤ V)
    (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y)) {x : G} (hx : x ∈ blockQ Y) :
    x ^ 2 = 1 := by
  obtain ⟨-, hV, hQ⟩ := card_blockQ_of_shape m hU hcard
  have hVQ : V ≤ blockQ Y := m.nat.le
  have hidx : (V.subgroupOf (blockQ Y)).index = 2 := by
    have hm := Subgroup.relIndex_mul_card (H := V) (K := blockQ Y)
    rw [inf_of_le_left hVQ, hQ, hV] at hm
    change V.relIndex (blockQ Y) = 2
    omega
  have hmul : ∀ {a c : G}, a ∈ blockQ Y → c ∈ blockQ Y → (a * c ∈ V ↔ (a ∈ V ↔ c ∈ V)) := by
    intro a c ha hc
    have key := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨a, ha⟩ : ↥(blockQ Y))) (b := ⟨c, hc⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using key
  have hbQ : b ∈ Subgroup.normalizer (blockQ Y : Set G) := C1.le_normalizer_blockQ Y m.bY
  have hbV : b ∈ Subgroup.normalizer (V : Set G) := m.nat.norm m.bY
  have hbv : ∀ v ∈ V, b * v * b⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hbV v).mp hv
  have hfix : ∀ v ∈ V, b * v * b⁻¹ = v → v = 1 := fun v hv h =>
    m.nat.eq_one_of_fix m.bY m.b_odd.2 m.b_odd.1 hv h
  obtain ⟨q, hqQ, hqV⟩ : ∃ q ∈ blockQ Y, q ∉ V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show blockQ Y ≤ V from fun y hy => h y hy)
    omega
  have hbq : b * q * b⁻¹ ∈ blockQ Y := (Subgroup.mem_normalizer_iff.mp hbQ q).mp hqQ
  have hbqV : b * q * b⁻¹ ∉ V := fun h => hqV ((Subgroup.mem_normalizer_iff.mp hbV q).mpr h)
  have hv₀ : q⁻¹ * (b * q * b⁻¹) ∈ V :=
    (hmul ((blockQ Y).inv_mem hqQ) hbq).mpr
      ⟨fun h => absurd (inv_mem_iff.mp h) hqV, fun h => absurd h hbqV⟩
  let f : ↥V → ↥V := fun v => ⟨(v : G) * (b * v * b⁻¹)⁻¹, V.mul_mem v.2 (V.inv_mem (hbv v v.2))⟩
  have hf : Function.Injective f := by
    intro v v' h
    have h' : (v : G) * (b * v * b⁻¹)⁻¹ = (v' : G) * (b * v' * b⁻¹)⁻¹ := congrArg Subtype.val h
    have e1 : (b * v * b⁻¹ : G) = (b * v' * b⁻¹) * ((v' : G)⁻¹ * v) := by
      have h2 := eq_inv_mul_of_mul_eq h'
      calc (b * v * b⁻¹ : G) = ((b * v * b⁻¹)⁻¹)⁻¹ := by group
        _ = ((v : G)⁻¹ * (v' * (b * v' * b⁻¹)⁻¹))⁻¹ := by rw [h2]
        _ = (b * v' * b⁻¹) * ((v' : G)⁻¹ * v) := by group
    have hu : b * ((v' : G)⁻¹ * v) * b⁻¹ = (v' : G)⁻¹ * v := by
      calc b * ((v' : G)⁻¹ * v) * b⁻¹ = (b * v' * b⁻¹)⁻¹ * (b * v * b⁻¹) := by group
        _ = (v' : G)⁻¹ * v := by rw [e1]; group
    have h1 := hfix _ (V.mul_mem (V.inv_mem v'.2) v.2) hu
    exact Subtype.ext (by
      calc (v : G) = v' * ((v' : G)⁻¹ * v) := by group
        _ = v' := by rw [h1, mul_one])
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hv₀⟩
  have hv' : (v : G) * (b * v * b⁻¹)⁻¹ = q⁻¹ * (b * q * b⁻¹) := congrArg Subtype.val hv
  have hwfix : b * (q * v) * b⁻¹ = q * v := by
    have e2 : b * q * b⁻¹ = q * ((v : G) * (b * v * b⁻¹)⁻¹) := by rw [hv']; group
    calc b * (q * v) * b⁻¹ = (b * q * b⁻¹) * (b * v * b⁻¹) := by group
      _ = q * v := by rw [e2]; group
  have hwQ : q * (v : G) ∈ blockQ Y := (blockQ Y).mul_mem hqQ (hVQ v.2)
  have hwV : q * (v : G) ∉ V := fun h => hqV (by
    have := V.mul_mem h (V.inv_mem v.2)
    rwa [mul_inv_cancel_right] at this)
  have hw2V : q * (v : G) * (q * v) ∈ V := (hmul hwQ hwQ).mpr Iff.rfl
  have hw2 : q * (v : G) * (q * v) = 1 := hfix _ hw2V (by
    calc b * (q * v * (q * v)) * b⁻¹ = (b * (q * v) * b⁻¹) * (b * (q * v) * b⁻¹) := by group
      _ = q * v * (q * v) := by rw [hwfix])
  by_cases hxV : x ∈ V
  · exact m.nat.exp x hxV
  · set w := q * (v : G)
    have hu : w⁻¹ * x ∈ V := (hmul ((blockQ Y).inv_mem hwQ) hx).mpr
      ⟨fun h => absurd (inv_mem_iff.mp h) hwV, fun h => absurd h hxV⟩
    have hcw : (w⁻¹ * x) * w = w * (w⁻¹ * x) :=
      (Subgroup.mem_centralizer_iff.mp (m.nat.comm hu) w hwQ).symm
    have hu2 := m.nat.exp _ hu
    have hx' : x = w * (w⁻¹ * x) := by group
    rw [hx', sq]
    calc w * (w⁻¹ * x) * (w * (w⁻¹ * x)) = w * ((w⁻¹ * x) * w) * (w⁻¹ * x) := by group
      _ = w * (w * (w⁻¹ * x)) * (w⁻¹ * x) := by rw [hcw]
      _ = (w * w) * ((w⁻¹ * x) * (w⁻¹ * x)) := by group
      _ = 1 := by rw [hw2, one_mul, ← sq, hu2]

theorem transfer_two {n : ℕ} (m : Mem T S X Y V b n)
    (hcard : Nat.card ↥(⁅S, Subgroup.zpowers b⁆ : Subgroup G) ≤ 2 * (2 ^ n * 4 ^ n)) :
    blockU Y ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := m.nat.nat
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hsq := sq_ne_one m.hn α hαk m.bY m.bo
  have hbN : b ∈ Subgroup.normalizer ((S ⊓ Y : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨m.bS, Subgroup.le_normalizer m.bY⟩
  have hc : Nat.card ↥(⁅S ⊓ Y, Subgroup.zpowers b⁆ : Subgroup G) ≤ 2 * (2 ^ n * 4 ^ n) :=
    (Subgroup.card_le_of_le (Subgroup.commutator_mono inf_le_left le_rfl)).trans hcard
  have h1 := card_commutator_le (by have := m.hn; omega) hF α hαs hαk m.bY hsq m.syl hbN
  set R := ⁅blockQ Y, Subgroup.zpowers b⁆ with hR
  have hRle : Nat.card R ≤ 2 * Nat.card V := by
    rw [m.nat.card]
    have h2 := h1.trans hc
    have hpos : 0 < 2 ^ n := by positivity
    nlinarith
  have hVR : V ≤ R := le_commutator_of_fix m.nat.le (m.nat.norm m.bY) fun x hx hxb =>
    m.nat.eq_one_of_fix m.bY m.b_odd.2 m.b_odd.1 hx (by rw [← hxb, mul_inv_cancel_right])
  have hRV : R ≤ V := by
    by_contra hRV
    have hVpos : 0 < Nat.card V := Nat.card_pos
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hVR
    have hk2 : k ≤ 2 := by
      rw [hk] at hRle
      exact Nat.le_of_mul_le_mul_left (by linarith) hVpos
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hRV (Subgroup.eq_of_le_of_card_ge hVR (by rw [hk, mul_one])).symm.le
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card R := Nat.card_pos
      omega
    have h2V : Nat.card R = 2 * Nat.card V := by
      rw [hk]
      have : k = 2 := by omega
      rw [this, mul_comm]
    have hidx : (V.subgroupOf R).index = 2 := by
      have hm := Subgroup.relIndex_mul_card (H := V) (K := R)
      rw [inf_of_le_left hVR, h2V] at hm
      exact Nat.eq_of_mul_eq_mul_right hVpos hm
    have hbR : Subgroup.zpowers b ≤ Subgroup.normalizer (R : Set G) :=
      le_sup_right.trans (A3.sup_le_normalizer_commutator (blockQ Y) (Subgroup.zpowers b))
    have hbV : Subgroup.zpowers b ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr (m.nat.norm m.bY)
    have hRbV : ⁅R, Subgroup.zpowers b⁆ ≤ V := by
      refine Subgroup.commutator_le.mpr fun r hr g hg => ?_
      have hx : g * r⁻¹ * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hbR hg) r⁻¹).mp (R.inv_mem hr)
      have key := Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨r, hr⟩ : ↥R)) (b := ⟨g * r⁻¹ * g⁻¹, hx⟩)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
      have e : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact key.mpr (inv_mem_iff.symm.trans (Subgroup.mem_normalizer_iff.mp (hbV hg) r⁻¹))
    have hQ2 : IsPGroup 2 (blockQ Y) := m.T2.to_le m.blockQ_le_T
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers b)) (Nat.card (blockQ Y)) := by
      rw [Nat.card_zpowers, hj]
      exact Nat.Coprime.pow_right j (Odd.coprime_two_right m.b_odd.1)
    have hsolv : Group.IsSolvable (blockQ Y) := by
      have := hQ2.isNilpotent
      infer_instance
    have hcc := CFSG.RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable
      (Subgroup.zpowers b) (blockQ Y) (Subgroup.zpowers_le.mpr (C1.le_normalizer_blockQ Y m.bY))
      hcop hsolv
    rw [← hR] at hcc
    exact hRV (hcc ▸ hRbV)
  exact blockU_le_of_commutator m.hn hF m.perf α hαs hαk m.bY
    (fun h => hsq (by rw [h, one_pow])) m.nat.norm hRV

omit [Finite G] in
theorem commutator_le_inf {n : ℕ} (m : Mem T S X Y V b n) : ⁅S, Subgroup.zpowers b⁆ ≤ S ⊓ Y :=
  le_inf (commutator_zpowers_le m.bS)
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr m.bY)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp m.SY))

theorem mem_blockQ_iff_sq (hAS : Ch11.SecH.AS_I_1_3_L2) (m : Mem T S X Y V b 2)
    (hU : blockU Y ≤ V) (hcard : Nat.card (blockQ Y) = 2 * Nat.card (blockU Y)) {x : G} :
    x ∈ blockQ Y ↔ x ∈ S ⊓ Y ∧ x ^ 2 = 1 :=
  ⟨fun hx => ⟨EscapingLocal.pCoreOf_le_of_isSylowTwoOf m.syl hx,
      sq_eq_one_of_mem_blockQ m hU hcard hx⟩,
    fun hx => mem_blockQ_of_sq_eq_one hAS m hcard hx.1.2 hx.2⟩

theorem both_or (hAS : Ch11.SecH.AS_I_1_3_L2) {X₁ X₂ Y₁ Y₂ V₁ V₂ : Subgroup G}
    (m₁ : Mem T S X₁ Y₁ V₁ b 2) (m₂ : Mem T S X₂ Y₂ V₂ b 2) (hs₁ : IsShort2 Y₁) :
    (blockQ Y₁ = blockU Y₁ ∧ blockQ Y₂ = blockU Y₂) ∨
      (Nat.card (blockQ Y₁) = 2 * Nat.card (blockU Y₁) ∧
        Nat.card (blockQ Y₂) = 2 * Nat.card (blockU Y₂) ∧ blockU Y₁ ≤ V₁ ∧ blockU Y₂ ≤ V₂ ∧
        blockQ Y₁ = blockQ Y₂) := by
  have hU₁ := m₁.blockU_le_of_short hs₁
  obtain ⟨F₁, _, _, hF₁, α₁, hαs₁, hαk₁, -⟩ := m₁.nat.nat
  obtain ⟨F₂, _, _, hF₂, α₂, hαs₂, hαk₂, -⟩ := m₂.nat.nat
  have hC₂ := commutator_le_inf m₂
  rcases blockQ_eq_or hAS m₁.hn hF₁ m₁.perf α₁ hαs₁ hαk₁ with hQ₁ | ⟨-, hc₁⟩
  · have hUV₁ := (block_of_natData m₁.hn m₁.perf m₁.char m₁.nat hU₁).2.2.2
    obtain ⟨hS₁, hcS₁⟩ := m₁.sylow (hQ₁.trans hUV₁)
    have hU₂ := m₂.transfer (by rw [hS₁, hcS₁])
    rcases blockQ_eq_or hAS m₂.hn hF₂ m₂.perf α₂ hαs₂ hαk₂ with hQ₂ | ⟨-, hc₂⟩
    · exact Or.inl ⟨hQ₁, hQ₂⟩
    · exfalso
      obtain ⟨hcomm₂, hcard₂⟩ := commutator_inf_eq hAS m₂ hU₂ hc₂
      have hle : S ⊓ Y₂ ≤ ⁅S, Subgroup.zpowers b⁆ :=
        hcomm₂.symm.le.trans (Subgroup.commutator_mono inf_le_left le_rfl)
      have h := Subgroup.card_le_of_le hle
      rw [hcard₂, hS₁, hcS₁] at h
      norm_num at h
  · obtain ⟨hcomm₁, hcard₁⟩ := commutator_inf_eq hAS m₁ hU₁ hc₁
    have hS₁ : ⁅S, Subgroup.zpowers b⁆ = S ⊓ Y₁ :=
      le_antisymm (commutator_le_inf m₁)
        (hcomm₁.symm.le.trans (Subgroup.commutator_mono inf_le_left le_rfl))
    have hU₂ := transfer_two m₂ (by rw [hS₁, hcard₁]; norm_num)
    rcases blockQ_eq_or hAS m₂.hn hF₂ m₂.perf α₂ hαs₂ hαk₂ with hQ₂ | ⟨-, hc₂⟩
    · exfalso
      have hUV₂ := (block_of_natData m₂.hn m₂.perf m₂.char m₂.nat hU₂).2.2.2
      obtain ⟨hS₂, hcS₂⟩ := m₂.sylow (hQ₂.trans hUV₂)
      rw [← hS₂, hS₁, hcard₁] at hcS₂
      norm_num at hcS₂
    · obtain ⟨-, hcard₂⟩ := commutator_inf_eq hAS m₂ hU₂ hc₂
      have hS₂ : ⁅S, Subgroup.zpowers b⁆ = S ⊓ Y₂ :=
        Subgroup.eq_of_le_of_card_ge hC₂ (le_of_eq (by rw [hcard₂, hS₁, hcard₁]))
      have hSS : S ⊓ Y₁ = S ⊓ Y₂ := hS₁.symm.trans hS₂
      refine Or.inr ⟨hc₁, hc₂, hU₁, hU₂, ?_⟩
      ext x
      rw [mem_blockQ_iff_sq hAS m₁ hU₁ hc₁, mem_blockQ_iff_sq hAS m₂ hU₂ hc₂, hSS]

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.BLx
