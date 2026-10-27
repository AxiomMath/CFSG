module

public import CFSG.Quasithin.Recognition.RuTypeJ27c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace Sigma

theorem eq_one_of_fix_line : ∀ σ : SigmaL2F4, (∀ v : Fin 2 → F4, v 1 = 0 → sigmaAct σ v = v) →
    ∀ c : Fin 2 → F4, c 1 ≠ 0 → sigmaAct σ c = c → σ = 1 := by
  decide +kernel

theorem exists_conj_mul_order_five : ∀ a : SigmaL2F4, (a ^ 2 = 1 ∧ a ≠ 1 ∧ a.right = 1) →
    ∃ g : SigmaL2F4, (a * (g * a * g⁻¹)) ^ 5 = 1 ∧ a * (g * a * g⁻¹) ≠ 1 := by
  decide +kernel

end Sigma

theorem quaternion_sq_eq_one : ∀ x : QuaternionGroup 2, x * x = 1 → x = 1 ∨ x = .a 2 := by
  decide

theorem quaternion_a_one_ne : (QuaternionGroup.a 1 : QuaternionGroup 2) ≠ 1 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) ≠ .a 2 := by decide

theorem quaternion_xa_zero_ne : (QuaternionGroup.xa 0 : QuaternionGroup 2) ≠ 1 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) ≠ .a 2 := by decide

theorem quaternion_prod_ne : (QuaternionGroup.a 1 * .xa 0 : QuaternionGroup 2) ≠ 1 ∧
    (QuaternionGroup.a 1 * .xa 0 : QuaternionGroup 2) ≠ .a 2 := by decide

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem mem_HC_of_comm_mem_Z {h q : G} (hh : h ∈ M.HC) (hU : h ∉ ruU M.L M.T)
    (hq : q ∈ ruQ M.T) (hc : ⁅h, q⁆ ∈ ruZ M.T) : q ∈ M.HC := by
  classical
  set f := M.FhHom h hh
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨q', hq'⟩ := M.Fh_surj hh hU (Multiplicative.toAdd y)
    exact ⟨q', by show Multiplicative.ofAdd (M.Fh h hh q') = y; rw [hq']; rfl⟩
  have hker : (M.HC).subgroupOf (ruQ M.T) ≤ f.ker := by
    intro q' hq'
    rw [Subgroup.mem_subgroupOf] at hq'
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (M.Fh h hh q') = 1
    have hZ := M.comm_HC_mem_Z hh hq'
    have h1 : M.ψU ⟨_, M.comm_HC_Q_mem_U hh q'.2⟩ = 1 := (M.ψU_eq_one_iff _).mpr hZ
    unfold Fh
    rw [h1]
    rfl
  have hcardk : Nat.card f.ker = 2 ^ 7 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, M.toRuData.card_Q,
      RuData.card_F4sq] at h
    omega
  have heq : (M.HC).subgroupOf (ruQ M.T) = f.ker := by
    refine Subgroup.eq_of_le_of_card_ge hker ?_
    rw [hcardk, card_subgroupOf_of_le M.HC_le_Q, M.card_HC]
  have hmem : (⟨q, hq⟩ : ruQ M.T) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (M.Fh h hh ⟨q, hq⟩) = 1
    have h1 : M.ψU ⟨_, M.comm_HC_Q_mem_U hh hq⟩ = 1 := (M.ψU_eq_one_iff _).mpr hc
    unfold Fh
    rw [h1]
    rfl
  rw [← heq, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem exists_conj_five {x y : G} (hx : x ∈ ruH M.T) (hy : y ∈ ruH M.T) (hx5 : orderOf x = 5)
    (hy5 : orderOf y = 5) : ∃ c ∈ ruH M.T, c * x * c⁻¹ ∈ Subgroup.zpowers y := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set H := ruH M.T
  have hcardH : Nat.card H = 2 ^ 11 * 120 := M.toRuData.card_H
  have hYp : IsPGroup 5 (Subgroup.zpowers (⟨y, hy⟩ : H)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, hy5]
    exact ⟨1, by norm_num⟩
  obtain ⟨PY, hPY⟩ := hYp.exists_le_sylow
  have hf : (Nat.card H).factorization 5 = 1 := by
    have h1 := PY.card_eq_multiplicity
    have h3 : 5 ∣ Nat.card PY := by
      have := Subgroup.card_dvd_of_le hPY
      rwa [Nat.card_zpowers, Subgroup.orderOf_mk, hy5] at this
    have h4 : Nat.card PY ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
    rw [h1] at h3 h4
    generalize (Nat.card H).factorization 5 = f at h3 h4 ⊢
    rw [hcardH] at h4
    rcases Nat.lt_or_ge f 2 with h | h
    · interval_cases f
      · norm_num at h3
      · rfl
    · exfalso
      have := (pow_dvd_pow 5 h).trans h4
      norm_num at this
  have hle5 : ∀ P : Sylow 5 H, Nat.card P = 5 := fun P => by
    rw [P.card_eq_multiplicity, hf, pow_one]
  have hXp : IsPGroup 5 (Subgroup.zpowers (⟨x, hx⟩ : H)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_mk, hx5]
    exact ⟨1, by norm_num⟩
  obtain ⟨PX, hPX⟩ := hXp.exists_le_sylow
  have hPXeq : (PX : Subgroup H) = Subgroup.zpowers ⟨x, hx⟩ := by
    refine (Subgroup.eq_of_le_of_card_ge hPX (le_of_eq ?_)).symm
    rw [hle5, Nat.card_zpowers, Subgroup.orderOf_mk, hx5]
  have hPYeq : (PY : Subgroup H) = Subgroup.zpowers ⟨y, hy⟩ := by
    refine (Subgroup.eq_of_le_of_card_ge hPY (le_of_eq ?_)).symm
    rw [hle5, Nat.card_zpowers, Subgroup.orderOf_mk, hy5]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H PX PY
  have hmem : c * ⟨x, hx⟩ * c⁻¹ ∈ (PY : Subgroup H) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨⟨x, hx⟩, by rw [hPXeq]; exact Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
  rw [hPYeq, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨c, c.2, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩⟩
  have := congrArg Subtype.val hk
  simpa using this

omit [Finite G] in
theorem conj_z_mem_V {l : G} (hl : l ∈ M.L) : l * M.z * l⁻¹ ∈ ruV M.L :=
  M.toRuData.conj_mem_V hl M.z_mem_V

theorem conj_mem_H_of_HC {l t : G} (hl : l ∈ M.L) (ht : t ∈ M.HC) : l⁻¹ * t * l ∈ ruH M.T := by
  have hU : l * M.z * l⁻¹ ∈ ruU M.L M.T := M.V_le_U (M.conj_z_mem_V hl)
  have hc : l * M.z * l⁻¹ * t = t * (l * M.z * l⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2) _ hU
  rw [M.mem_H_iff_comm]
  calc M.z * (l⁻¹ * t * l) = l⁻¹ * (l * M.z * l⁻¹ * t) * l := by group
    _ = l⁻¹ * (t * (l * M.z * l⁻¹)) * l := by rw [hc]
    _ = l⁻¹ * t * l * M.z := by group

theorem exists_T5_conj_of_conjU
    {l : G} (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) {w : G}
    (hw : w ∈ M.conjU l) (hwQ : w ∉ ruQ M.T) {x : G} (hxH : x ∈ ruH M.T) (hx5 : orderOf x = 5)
    (hinv : w * x * w⁻¹ = x⁻¹) : ∃ t ∈ M.T5 x, t * w * t⁻¹ = w * M.z := by
  classical
  by_contra hall
  push Not at hall
  have hwS : w ∈ ruS M.L := M.conjU_le_S hl hw
  have hwH : w ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hwS)
  have hw0 : l⁻¹ * w * l ∈ ruU M.L M.T := M.mem_conjU.mp hw
  have hw2 : w * w = 1 := by
    have h := M.U_sq hw0
    have e : w * w = l * ((l⁻¹ * w * l) ^ 2) * l⁻¹ := by rw [pow_two]; group
    rw [e, h]
    group
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hTα : ∀ t ∈ M.T5 x, t * w * t⁻¹ ∈ M.conjU l := by
    intro t ht
    have ht' := M.conj_mem_H_of_HC hl (T5_le_HC hxH hx5 ht)
    rw [M.mem_conjU]
    have e : l⁻¹ * (t * w * t⁻¹) * l = (l⁻¹ * t * l) * (l⁻¹ * w * l) * (l⁻¹ * t * l)⁻¹ := by
      group
    rw [e]
    exact M.conj_mem_U ht' hw0
  have hwT : ∀ t ∈ M.T5 x, w * t * w⁻¹ ∈ M.T5 x := by
    rintro t ⟨htQ, htx⟩
    replace htx : t * x = x * t := mem_G5.mp htx
    refine ⟨M.conj_mem_Q hwH htQ, mem_G5.mpr ?_⟩
    have hxw : w * x⁻¹ = x * w := by
      calc w * x⁻¹ = w * x⁻¹ * w⁻¹ * w := by group
        _ = (w * x * w⁻¹)⁻¹ * w := by rw [show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group]
        _ = x * w := by rw [hinv, inv_inv]
    have htx' : t * x⁻¹ = x⁻¹ * t := (Commute.inv_right htx).eq
    calc w * t * w⁻¹ * x = w * t * (w⁻¹ * x * w) * w⁻¹ := by group
      _ = w * t * x⁻¹ * w⁻¹ := by
          rw [show w⁻¹ * x * w = x⁻¹ by
            rw [hwi]
            calc w * x * w = w * x * w⁻¹ := by rw [hwi]
              _ = x⁻¹ := hinv]
      _ = w * (t * x⁻¹) * w⁻¹ := by group
      _ = w * (x⁻¹ * t) * w⁻¹ := by rw [htx']
      _ = (w * x⁻¹) * t * w⁻¹ := by group
      _ = x * (w * t * w⁻¹) := by rw [hxw]; group
  have hcomm : ∀ t ∈ M.T5 x, t * w = w * t := by
    intro t ht
    set c := w * t * w⁻¹ * t⁻¹
    have hcα : c ∈ M.conjU l := by
      have e : c = w * (t * w * t⁻¹)⁻¹ := by simp only [c]; group
      rw [e]
      exact mul_mem hw (inv_mem (hTα t ht))
    have hcT : c ∈ M.T5 x := mul_mem (hwT t ht) (inv_mem ht)
    have hcV : c ∈ ruV M.L := by
      rw [← M.conjU_inf_HC hl hne]
      exact ⟨hcα, T5_le_HC hxH hx5 hcT⟩
    rcases M.mem_Z_iff.mp (mem_Z_of_T5_U hxH hx5 hcT (M.V_le_U hcV)) with h | h
    · calc t * w = c⁻¹ * (w * t) := by simp only [c]; group
        _ = w * t := by rw [h, inv_one, one_mul]
    · exfalso
      apply hall t ht
      have hzw : M.z * w = w * M.z := M.Z_comm_H M.z_mem_Z hwH
      calc t * w * t⁻¹ = c⁻¹ * w := by simp only [c]; group
        _ = M.z * w := by rw [h, inv_eq_of_mul_eq_one_right M.z_mul_self]
        _ = w * M.z := hzw
  have hTQ : ∀ t ∈ M.T5 x, l⁻¹ * t * l ∈ ruQ M.T := by
    intro t ht
    have ht' := M.conj_mem_H_of_HC hl (T5_le_HC hxH hx5 ht)
    have htU := (Subgroup.mem_inf.mp (T5_le_HC hxH hx5 ht)).2
    have hfixV : ∀ v : Fin 2 → F4, v 1 = 0 →
        sigmaAct (M.φ ⟨_, ht'⟩) v = v := by
      intro v hv
      have hmem : Multiplicative.ofAdd v ∈ ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU := by
        rw [M.ψU_V_eq]
        exact hv
      obtain ⟨u, hu, hψ⟩ := hmem
      replace hu : (u : G) ∈ ruV M.L := hu
      have hlu : l * u * l⁻¹ ∈ ruU M.L M.T := M.V_le_U (M.toRuData.conj_mem_V hl hu)
      have hc : l * u * l⁻¹ * t = t * (l * u * l⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp htU) _ hlu
      have hcu : (⟨(l⁻¹ * t * l) * u * (l⁻¹ * t * l)⁻¹, M.conj_mem_U ht' u.2⟩ :
          ruU M.L M.T) = u := Subtype.ext (by
        show (l⁻¹ * t * l) * u * (l⁻¹ * t * l)⁻¹ = u
        calc (l⁻¹ * t * l) * u * (l⁻¹ * t * l)⁻¹ = l⁻¹ * (t * (l * u * l⁻¹)) * t⁻¹ * l := by
              group
          _ = l⁻¹ * (l * u * l⁻¹ * t) * t⁻¹ * l := by rw [hc]
          _ = u := by group)
      have e := M.ψU_conj ⟨_, ht'⟩ u
      rw [hcu, hψ, toAdd_ofAdd] at e
      exact e.symm
    have hfixw : sigmaAct (M.φ ⟨_, ht'⟩) (Multiplicative.toAdd (M.ψU ⟨_, hw0⟩)) =
        Multiplicative.toAdd (M.ψU ⟨_, hw0⟩) := by
      have hcw : (⟨(l⁻¹ * t * l) * (l⁻¹ * w * l) * (l⁻¹ * t * l)⁻¹, M.conj_mem_U ht' hw0⟩ :
          ruU M.L M.T) = ⟨_, hw0⟩ := Subtype.ext (by
        show (l⁻¹ * t * l) * (l⁻¹ * w * l) * (l⁻¹ * t * l)⁻¹ = l⁻¹ * w * l
        calc (l⁻¹ * t * l) * (l⁻¹ * w * l) * (l⁻¹ * t * l)⁻¹ = l⁻¹ * (t * w) * t⁻¹ * l := by
              group
          _ = l⁻¹ * (w * t) * t⁻¹ * l := by rw [hcomm t ht]
          _ = l⁻¹ * w * l := by group)
      have e := M.ψU_conj ⟨_, ht'⟩ ⟨_, hw0⟩
      rw [hcw] at e
      exact e.symm
    have hoff : (Multiplicative.toAdd (M.ψU ⟨_, hw0⟩)) 1 ≠ 0 := by
      intro h0
      have hmem : M.ψU ⟨_, hw0⟩ ∈ ((ruV M.L).subgroupOf (ruU M.L M.T)).map M.ψU := by
        rw [M.ψU_V_eq]
        exact h0
      obtain ⟨u, hu, hψ⟩ := hmem
      replace hu : (u : G) ∈ ruV M.L := hu
      have hk : u⁻¹ * ⟨_, hw0⟩ ∈ M.ψU.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, inv_mul_cancel]
      rw [M.ψU_ker, Subgroup.mem_subgroupOf] at hk
      have hV : l⁻¹ * w * l ∈ ruV M.L := by
        have e : l⁻¹ * w * l = (u : G) * ((u : G)⁻¹ * (l⁻¹ * w * l)) := by group
        rw [e]
        exact mul_mem hu (M.toRuData.Z_le_V hk)
      apply hwQ
      have e : w = l * (l⁻¹ * w * l) * l⁻¹ := by group
      rw [e]
      exact M.U_le_Q (M.V_le_U (M.toRuData.conj_mem_V hl hV))
    have h1 := Sigma.eq_one_of_fix_line _ hfixV _ hoff hfixw
    have hk : (⟨_, ht'⟩ : ruH M.T) ∈ M.φ.ker := h1
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  obtain ⟨w', ⟨hw'α, hw'Q⟩, hw'C⟩ := Set.not_subset.mp (M.conjU_inf_Q_not_le_HC hl hne)
  have hw'0 : l⁻¹ * w' * l ∈ ruU M.L M.T := M.mem_conjU.mp hw'α
  have hcZl : ∀ t ∈ M.T5 x, ⁅t, w'⁆ = 1 ∨ ⁅t, w'⁆ = l * M.z * l⁻¹ := by
    intro t ht
    have h := M.comm_mem_Z (hTQ t ht) hw'0
    have e : ⁅t, w'⁆ = l * ((l⁻¹ * t * l) * (l⁻¹ * w' * l) * (l⁻¹ * t * l)⁻¹ *
        (l⁻¹ * w' * l)⁻¹) * l⁻¹ := by rw [commutatorElement_def]; group
    rcases M.mem_Z_iff.mp h with h1 | h1
    · left; rw [e, h1]; group
    · right; rw [e, h1]
  have hcnZ : ∀ t ∈ M.T5 x, t ∉ ruZ M.T → ⁅t, w'⁆ ∉ ruZ M.T := by
    intro t ht htZ hcZ
    have htU : t ∉ ruU M.L M.T := fun hU => htZ (mem_Z_of_T5_U hxH hx5 ht hU)
    exact hw'C (M.mem_HC_of_comm_mem_Z (T5_le_HC hxH hx5 ht) htU hw'Q hcZ)
  obtain ⟨e⟩ := T5_quaternion hxH hx5
  have hZe : ∀ s : M.T5 x, (s : G) ∈ ruZ M.T → e s = 1 ∨ e s = .a 2 := by
    intro s hs
    apply quaternion_sq_eq_one
    rw [← map_mul]
    have : s * s = 1 := Subtype.ext (by
      rcases M.mem_Z_iff.mp hs with h | h
      · simp [h]
      · simp only [Subgroup.coe_mul, OneMemClass.coe_one]
        rw [h, M.z_mul_self])
    rw [this, map_one]
  set t1 : M.T5 x := e.symm (.a 1)
  set t2 : M.T5 x := e.symm (.xa 0)
  have hnot : ∀ s : M.T5 x, e s ≠ 1 → e s ≠ .a 2 → (s : G) ∉ ruZ M.T := by
    intro s h1 h2 hs
    rcases hZe s hs with h | h
    · exact h1 h
    · exact h2 h
  have ht1 : (t1 : G) ∉ ruZ M.T := hnot t1 (by simpa [t1] using quaternion_a_one_ne.1)
    (by simpa [t1] using quaternion_a_one_ne.2)
  have ht2 : (t2 : G) ∉ ruZ M.T := hnot t2 (by simpa [t2] using quaternion_xa_zero_ne.1)
    (by simp [t2])
  have ht12 : ((t1 * t2 : M.T5 x) : G) ∉ ruZ M.T := hnot (t1 * t2)
    (by simpa [t1, t2] using quaternion_prod_ne.1) (by simp [t1, t2])
  have hval : ∀ s : M.T5 x, (s : G) ∉ ruZ M.T → ⁅(s : G), w'⁆ = l * M.z * l⁻¹ := by
    intro s hs
    rcases hcZl s s.2 with h | h
    · exact absurd (by rw [h]; exact one_mem _) (hcnZ s s.2 hs)
    · exact h
  have h1 := hval t1 ht1
  have h2 := hval t2 ht2
  have h12 := hval (t1 * t2) ht12
  have hU2 : ⁅(t2 : G), w'⁆ ∈ ruU M.L M.T :=
    M.comm_HC_Q_mem_U (T5_le_HC hxH hx5 t2.2) hw'Q
  have hc1 : (t1 : G) * ⁅(t2 : G), w'⁆ = ⁅(t2 : G), w'⁆ * t1 :=
    ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (T5_le_HC hxH hx5 t1.2)).2) _ hU2).symm
  have hprod : ⁅((t1 * t2 : M.T5 x) : G), w'⁆ = ⁅(t2 : G), w'⁆ * ⁅(t1 : G), w'⁆ := by
    have e1 : ⁅((t1 * t2 : M.T5 x) : G), w'⁆ =
        (t1 : G) * ⁅(t2 : G), w'⁆ * (t1 : G)⁻¹ * ⁅(t1 : G), w'⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e1, hc1, mul_inv_cancel_right]
  rw [h12, h1, h2] at hprod
  have hz1 : l * M.z * l⁻¹ = 1 := by
    have := hprod
    calc l * M.z * l⁻¹ = (l * M.z * l⁻¹) * (l * M.z * l⁻¹) * (l * M.z * l⁻¹)⁻¹ := by group
      _ = (l * M.z * l⁻¹) * (l * M.z * l⁻¹)⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel _
  apply M.z_ne_one
  calc M.z = l⁻¹ * (l * M.z * l⁻¹) * l := by group
    _ = 1 := by rw [hz1]; group

theorem exists_inv_T5_conj
    {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ∃ i ∈ ruH M.T, i * i = 1 ∧ IsConj M.z i ∧ i * b * i⁻¹ = b⁻¹ ∧
      ∃ t ∈ M.T5 b, t * i * t⁻¹ = i * M.z := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨l, hl, hnle⟩ := M.exists_conjU_not_le_Q
  have hne : M.conjU l ≠ ruU M.L M.T := fun h => hnle (h ▸ M.U_le_Q)
  obtain ⟨w, hw, hwQ⟩ := Set.not_subset.mp hnle
  have hwS : w ∈ ruS M.L := M.conjU_le_S hl hw
  have hwH : w ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hwS)
  have hwK : w ∈ M.K := M.S_le_K hwS
  have hw0 : l⁻¹ * w * l ∈ ruU M.L M.T := M.mem_conjU.mp hw
  have hw2 : w * w = 1 := by
    have h := M.U_sq hw0
    have e : w * w = l * ((l⁻¹ * w * l) ^ 2) * l⁻¹ := by rw [pow_two]; group
    rw [e, h]
    group
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwz : IsConj M.z w := by
    have hw01 : l⁻¹ * w * l ≠ 1 := fun h => hwQ (by
      have e : w = l * (l⁻¹ * w * l) * l⁻¹ := by group
      rw [e, h]
      simp only [mul_one, mul_inv_cancel]
      exact one_mem _)
    exact (M.isConj_z_of_U hw0 hw01).trans (isConj_iff.mpr ⟨l, by group⟩)
  have hφw : M.φ ⟨w, hwH⟩ ^ 2 = 1 ∧ M.φ ⟨w, hwH⟩ ≠ 1 ∧ (M.φ ⟨w, hwH⟩).right = 1 := by
    refine ⟨?_, fun h1 => hwQ ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨w, hwH⟩ : ruH M.T) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hw2)
      rw [this, map_one]
    · have hk : (⟨w, hwH⟩ : ruH M.T) ∈ M.φ.ker := h1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    · obtain ⟨hk, hk1⟩ := M.mem_K_iff.mp hwK
      exact hk1
  obtain ⟨g, hg5, hg1⟩ := Sigma.exists_conj_mul_order_five _ hφw
  obtain ⟨h, hh⟩ := M.φ_surj g
  set y : G := w * ((h : G) * w * (h : G)⁻¹)
  have hyH : y ∈ ruH M.T := mul_mem hwH (mul_mem (mul_mem h.2 hwH) (inv_mem h.2))
  have hφy : M.φ ⟨y, hyH⟩ = M.φ ⟨w, hwH⟩ * (g * M.φ ⟨w, hwH⟩ * g⁻¹) := by
    have e : (⟨y, hyH⟩ : ruH M.T) = ⟨w, hwH⟩ * (h * ⟨w, hwH⟩ * h⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hh]
  have hy5Q : y ^ 5 ∈ ruQ M.T := by
    have hk : (⟨y, hyH⟩ : ruH M.T) ^ 5 ∈ M.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hφy, hg5]
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    simpa using hk
  set x : G := y ^ (2 ^ 11)
  have hxH : x ∈ ruH M.T := pow_mem hyH _
  have hx5 : orderOf x = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (y ^ 5) ^ (2 ^ 11) = 1 := by
        have := pow_card_eq_one' (G := ruQ M.T) (x := ⟨_, hy5Q⟩)
        rw [M.toRuData.card_Q] at this
        exact congrArg Subtype.val this
      rw [← pow_mul, mul_comm, pow_mul] at h1
      exact h1
    · intro h1
      apply hg1
      have hφx : M.φ ⟨x, hxH⟩ = (M.φ ⟨y, hyH⟩) ^ (2 ^ 11) := by
        rw [← map_pow]
        rfl
      have h2 : (M.φ ⟨y, hyH⟩) ^ (2 ^ 11) = 1 := by
        rw [← hφx, show (⟨x, hxH⟩ : ruH M.T) = 1 from Subtype.ext h1, map_one]
      have h3 : (M.φ ⟨y, hyH⟩) ^ 5 = 1 := by rw [hφy, hg5]
      have hgcd := (pow_gcd_eq_one (a := M.φ ⟨y, hyH⟩)).mpr ⟨h3, h2⟩
      rw [show Nat.gcd 5 (2 ^ 11) = 1 by norm_num, pow_one] at hgcd
      rw [← hφy]
      exact hgcd
  have hinvy : w * y * w⁻¹ = y⁻¹ := by
    simp only [y]
    rw [hwi]
    calc w * (w * ((h : G) * w * (h : G)⁻¹)) * w = (w * w) * ((h : G) * w * (h : G)⁻¹) * w := by
          group
      _ = (h : G) * w * (h : G)⁻¹ * w := by rw [hw2, one_mul]
      _ = (w * ((h : G) * w * (h : G)⁻¹))⁻¹ := by
          simp only [mul_inv_rev, inv_inv, hwi]
          group
  have hinvx : w * x * w⁻¹ = x⁻¹ := by
    simp only [x]
    rw [← conj_pow, hinvy, inv_pow]
  obtain ⟨t, ht, htw⟩ := M.exists_T5_conj_of_conjU hl hne hw hwQ hxH hx5 hinvx
  obtain ⟨c, hcH, hcx⟩ := M.exists_conj_five hxH hbH hx5 hb5
  set x' := c * x * c⁻¹
  have hx'5 : orderOf x' = 5 := by
    show orderOf (c * x * c⁻¹) = 5
    rw [orderOf_conj_eq, hx5]
  have hzp : Subgroup.zpowers x' = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hcx) (le_of_eq ?_)
    rw [Nat.card_zpowers, Nat.card_zpowers, hx'5, hb5]
  have hbx' : b ∈ Subgroup.zpowers x' := by rw [hzp]; exact Subgroup.mem_zpowers b
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hbx'
  have hcz : c * M.z * c⁻¹ = M.z := by
    rw [(M.mem_H_iff_comm.mp hcH).symm, mul_inv_cancel_right]
  refine ⟨c * w * c⁻¹, mul_mem (mul_mem hcH hwH) (inv_mem hcH), ?_, ?_, ?_, ?_⟩
  · calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · exact hwz.trans (isConj_iff.mpr ⟨c, rfl⟩)
  ·
    have hix : (c * w * c⁻¹) * x' * (c * w * c⁻¹)⁻¹ = x'⁻¹ := by
      simp only [x']
      calc c * w * c⁻¹ * (c * x * c⁻¹) * (c * w * c⁻¹)⁻¹ = c * (w * x * w⁻¹) * c⁻¹ := by
            group
        _ = (c * x * c⁻¹)⁻¹ := by rw [hinvx]; group
    rw [← hm, ← conj_zpow, hix, inv_zpow]
  · refine ⟨c * t * c⁻¹, ⟨M.conj_mem_Q hcH ht.1, mem_G5.mpr ?_⟩, ?_⟩
    ·
      have htx : t * x = x * t := mem_G5.mp ht.2
      have htx' : (c * t * c⁻¹) * x' = x' * (c * t * c⁻¹) := by
        simp only [x']
        calc c * t * c⁻¹ * (c * x * c⁻¹) = c * (t * x) * c⁻¹ := by group
          _ = c * (x * t) * c⁻¹ := by rw [htx]
          _ = c * x * c⁻¹ * (c * t * c⁻¹) := by group
      rw [← hm]
      exact ((Commute.zpow_right htx' m)).eq
    · calc c * t * c⁻¹ * (c * w * c⁻¹) * (c * t * c⁻¹)⁻¹ = c * (t * w * t⁻¹) * c⁻¹ := by group
        _ = c * w * c⁻¹ * (c * M.z * c⁻¹) := by rw [htw]; group
        _ = c * w * c⁻¹ * M.z := by rw [hcz]

end RuDataM

end CFSG.Quasithin.RuType
