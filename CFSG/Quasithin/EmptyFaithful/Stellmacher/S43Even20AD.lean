module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AC

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem le_normalizer_centralizer {X Q : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Q : Set G)) :
    X ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, conjSub g (Subgroup.centralizer (Q : Set G)) ≤
      Subgroup.centralizer (Q : Set G) := fun g hg => by
    rw [← conjSub_centralizer, conjSub_eq_of_mem_normalizer (h hg)]
  exact fun g hg => F7.mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (X.inv_mem hg))

variable {α β : Geo H M}

theorem eq_Zv_or_eq_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (h4 : Nat.card (Vn β) = 2 ^ 6) {U : Subgroup G}
    (hZU : Zv β ≤ U) (hUV : U ≤ Vst β) (hUβ : stab β ≤ Subgroup.normalizer (U : Set G))
    (hUM : Mab α β ≤ Subgroup.normalizer (U : Set G)) : U = Zv β ∨ U = Vst β := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  by_cases hUY : U ≤ Yv β
  · rcases eq_or_eq_of_relIndex_two hZU hUY (relIndex_Zv_Yv hA h26 hs hβv) with h | h
    · exact Or.inl h
    · exfalso
      obtain ⟨m, hm, hmN⟩ := exists_Mab_not_normalizer_Yv hA h26 hs hβ
      exact hmN (h ▸ hUM hm)
  right
  obtain ⟨v, hvU, hvY⟩ : ∃ v ∈ U, v ∉ Yv β := by
    by_contra hcon
    push Not at hcon
    exact hUY hcon
  have hvV := hUV hvU
  obtain ⟨l, hl, hvl⟩ := mem_A_of_mem_Vst hA h26 hs hb hβv h4 hvV
  obtain ⟨q, hq, hqv⟩ := exists_comm_not_mem_of_A hA h26 hs hb hβv hl hvl hvY
  have hqU : ⁅q, v⁆ ∈ U := by
    rw [commutatorElement_def]
    exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUβ (pCoreOf_le 2 _ hq)) v).mp hvU)
      (U.inv_mem hvU)
  have hYU : Yv β ≤ U := le_of_relIndex_two (relIndex_Zv_Yv hA h26 hs hβv)
    (Zv_le_Yv hA h26 hs hβv) hZU (comm_Qv_A_mem hA h26 hs hβv hl hq hvl) hqU hqv
  have hAU : ⁅Zv l, Qv β⁆ ≤ U := le_of_relIndex_two (hs.relIndex_Yv_comm hA h26 hβv hl)
    (hs.Yv_le_comm hA h26 hβv hl) hYU hvl hvU hvY
  obtain ⟨g₀, hg₀β, -, hg₀l, -⟩ := hs.exists_rot hA h26 hβv hl
  have hgv : (g₀ : G) * v * (g₀ : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hUβ hg₀β) v).mp hvU
  have hgvA : (g₀ : G) * v * (g₀ : G)⁻¹ ∉ ⁅Zv l, Qv β⁆ := by
    intro h
    have h1 : (g₀ : G) * v * (g₀ : G)⁻¹ ∈ Zv l ⊓ Zv (g₀ • l) := by
      refine ⟨hs.comm_le_Zv hA h26 hβv hl h, ?_⟩
      rw [Zv_smul]
      exact mul_mem_conjSub (hs.comm_le_Zv hA h26 hβv hl hvl)
    rw [hs.inf_Zv_eq_Yv hA h26 hβv hl (smul_mem_nbrs_of_mem_stab g₀ hg₀β hl) (Ne.symm hg₀l)]
      at h1
    apply hvY
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (hs.stab_le_normalizer_Yv hA h26 hβv hg₀β) v).mpr h1
    exact h2
  exact le_antisymm hUV (le_of_relIndex_two (relIndex_A_Vst hA h26 hs hb hβv hl h4)
    (A_le_Vst hl) hAU (hUV hgv) hgv hgvA)

theorem C_le_Qgrp (hA : F53Amalgam H M S) :
    stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) ≤ Qgrp α β := fun c hc => by
  refine (mem_Qgrp_iff hA).mpr ⟨hc.1, fun x hx => ?_⟩
  have h1 : ⁅c, x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm
  rw [h1]
  exact (Zv β).one_mem

theorem centralizer_Qgrp_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (h4 : Nat.card (Vn β) = 2 ^ 6)
    (hV : Mab α β ≤ Subgroup.normalizer (Vst β : Set G))
    (hC : stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) = Cst β) :
    Vst β ⊓ Subgroup.centralizer (Qgrp α β : Set G) = Zv β := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hZV : Zv β ≤ Vst β := (Zv_le_Yv hA h26 hs hβv).trans (hs.Yv_le_Vst hA h26 hβv)
  have hZK : Zv β ≤ Vst β ⊓ Subgroup.centralizer (Qgrp α β : Set G) := fun z hz =>
    ⟨hZV hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      comm_Zv_of_mem_stab hA h26 hs hβv ((mem_Qgrp_iff hA).mp hy).1.2 hz⟩
  rcases eq_Zv_or_eq_Vst hA h26 hs hb hβ h4 hZK inf_le_left
    (le_normalizer_inf (stab_le_normalizer_Vst β)
      (le_normalizer_centralizer (stab_le_normalizer hA h26 hs hβ).1))
    (le_normalizer_inf hV (le_normalizer_centralizer (Mab_le_normalizer hA h26 hs hβ hV).1))
    with h | h
  · exact h
  exfalso
  have hQC : Qgrp α β ≤ stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) := by
    intro y hy
    refine ⟨((mem_Qgrp_iff hA).mp hy).1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [← h] at hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hQeq : Qgrp α β = Cst β := hC ▸ le_antisymm hQC (C_le_Qgrp hA)
  have hCα : Cst β ≤ Qv α := by
    rw [← hs.centralizer_Zv hA hs.vα]
    intro c hc
    refine ⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hc.1, ?_⟩
    exact Subgroup.centralizer_le (Sit43.Zv_le_Vn hβ) hc.2
  have hQαE : Qv α ≤ stab α ⊓ stab β := le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hβ)
  have h8 := relIndex_Qgrp_edge hA h26 hs hb hβ h4
  rw [hQeq, ← Subgroup.relIndex_mul_relIndex _ _ _ hCα hQαE,
    hs.relIndex_Qv_edge_stab hA hβ] at h8
  have h1 : (Cst β).relIndex (Qv α) = 1 := by omega
  exact hs.not_Qv_le_Qv_nbr hA h26 hs.vα hβ
    ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_left)

omit [Finite G] in
theorem forall_fin_three {P : Fin 3 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ i => by fin_cases i <;> assumption⟩

theorem relIndex_Cst_Qgrp (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (h4 : Nat.card (Vn β) = 2 ^ 6)
    (hV : Mab α β ≤ Subgroup.normalizer (Vst β : Set G))
    (hC : stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) = Cst β) :
    (Cst β).relIndex (Qgrp α β) = 8 := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ : α ∈ nbrs β := nbrs_symm hβ
  have hK := centralizer_Qgrp_eq hA h26 hs hb hβ h4 hV hC
  obtain ⟨p, hpY, hpZ⟩ : ∃ p ∈ Yv β, p ∉ Zv β := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Yv β ≤ Zv β from hcon)
    rw [hs.card_Yv hA h26 hβv, hs.card_Zv_true hA h26 hβv] at this
    omega
  obtain ⟨a, ha, haY⟩ := exists_mem_A_not_mem_Yv hA h26 hs hβv hαβ
  obtain ⟨c, hcV, hcA⟩ : ∃ c ∈ Vst β, c ∉ ⁅Zv α, Qv β⁆ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Vst β ≤ ⁅Zv α, Qv β⁆ from hcon)
    rw [hs.card_Vst hA h26 hb hβv h4, hs.card_comm_Qv hA h26 hβv hαβ] at this
    norm_num at this
  have hYV := hs.Yv_le_Vst hA h26 hβv
  have hYA := hs.Yv_le_comm hA h26 hβv hαβ
  have hZY := Zv_le_Yv hA h26 hs hβv
  have hpV : p ∈ Vst β := hYV hpY
  have haV : a ∈ Vst β := A_le_Vst hαβ ha
  have h2 : (⊥ : Subgroup G).relIndex (Zv β) = 2 := by
    rw [Subgroup.relIndex_bot_left, hs.card_Zv_true hA h26 hβv]
  have hPZ : Qgrp α β ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp [Subgroup.mem_bot]
  have hPT : Qgrp α β ≤ Subgroup.normalizer (Zv β : Set G) := fun g hg =>
    stab_le_normalizer_Zv hA β ((mem_Qgrp_iff hA).mp hg).1.2
  have he : ∀ e ∈ Vst β, ∀ y ∈ Qgrp α β, ⁅y, e⁆ ∈ Zv β := fun e he y hy =>
    ((mem_Qgrp_iff hA).mp hy).2 e he
  let f : Fin 3 → ↥(Qgrp α β) →* Multiplicative (ZMod 2) :=
    ![bitHom h2 hPZ hPT (he p hpV), bitHom h2 hPZ hPT (he a haV), bitHom h2 hPZ hPT (he c hcV)]
  refine (relIndex_eq_of_iInf_ker f ?_ ?_).trans (by norm_num)
  · intro y
    rw [forall_fin_three]
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, bitHom_eq_one_iff]
    have hyβ : (y : G) ∈ stab β := ((mem_Qgrp_iff hA).mp y.2).1.2
    constructor
    · intro hy
      rw [← hC] at hy
      have h1 : ∀ e ∈ Vst β, ⁅(y : G), e⁆ ∈ (⊥ : Subgroup G) := fun e he' =>
        Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hy.2 e he').symm)
      exact ⟨h1 p hpV, h1 a haV, h1 c hcV⟩
    · rintro ⟨hp1, ha1, hc1⟩
      have hZ1 : ∀ x ∈ Zv β, ⁅(y : G), x⁆ ∈ (⊥ : Subgroup G) := fun x hx =>
        Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
          (comm_Zv_of_mem_stab hA h26 hs hβv hyβ hx))
      have s1 := comm_mem_of_relIndex_two hA hb hyβ hYV (relIndex_Zv_Yv hA h26 hs hβv) hZY hZ1
        hpY hpZ hp1
      have s2 := comm_mem_of_relIndex_two hA hb hyβ (A_le_Vst hαβ)
        (hs.relIndex_Yv_comm hA h26 hβv hαβ) hYA s1 ha haY ha1
      have s3 := comm_mem_of_relIndex_two hA hb hyβ le_rfl
        (relIndex_A_Vst hA h26 hs hb hβv hαβ h4) (A_le_Vst hαβ) s2 hcV hcA hc1
      rw [← hC]
      refine ⟨((mem_Qgrp_iff hA).mp y.2).1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (s3 x hx))).symm
  · intro x hx
    have hx012 : ¬ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) := fun hc =>
      hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2])
    have hwV : pw p (x 0) * pw a (x 1) * pw c (x 2) ∈ Vst β :=
      (Vst β).mul_mem ((Vst β).mul_mem (pw_mem hpV _) (pw_mem haV _)) (pw_mem hcV _)
    have hpa : pw p (x 0) * pw a (x 1) ∈ ⁅Zv α, Qv β⁆ :=
      (⁅Zv α, Qv β⁆).mul_mem (pw_mem (hYA hpY) _) (pw_mem ha _)
    have hwZ : pw p (x 0) * pw a (x 1) * pw c (x 2) ∉ Zv β := by
      intro hw
      rcases eq_zero_or_eq_one (x 2) with h2' | h2'
      · rw [h2', pw_zero, mul_one] at hw
        rcases eq_zero_or_eq_one (x 1) with h1 | h1
        · rw [h1, pw_zero, mul_one] at hw
          rcases eq_zero_or_eq_one (x 0) with h0 | h0
          · exact hx012 ⟨h0, h1, h2'⟩
          · rw [h0, pw_one] at hw
            exact hpZ hw
        · rw [h1, pw_one] at hw
          apply haY
          have h3 := (Yv β).mul_mem ((Yv β).inv_mem (pw_mem hpY (x 0))) (hZY hw)
          rwa [inv_mul_cancel_left] at h3
      · rw [h2', pw_one] at hw
        apply hcA
        have h3 := (⁅Zv α, Qv β⁆).mul_mem ((⁅Zv α, Qv β⁆).inv_mem hpa) (hYA (hZY hw))
        rwa [inv_mul_cancel_left] at h3
    have hwC : pw p (x 0) * pw a (x 1) * pw c (x 2) ∉
        Subgroup.centralizer (Qgrp α β : Set G) := fun h =>
      hwZ (hK ▸ (⟨hwV, h⟩ : _ ∈ Vst β ⊓ Subgroup.centralizer (Qgrp α β : Set G)))
    obtain ⟨y, hy, hyw⟩ : ∃ y ∈ Qgrp α β,
        ¬ y * (pw p (x 0) * pw a (x 1) * pw c (x 2)) =
          (pw p (x 0) * pw a (x 1) * pw c (x 2)) * y := by
      by_contra hcon
      push Not at hcon
      exact hwC (Subgroup.mem_centralizer_iff.mpr hcon)
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [Fin.sum_univ_three]
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, bitHom_apply]
    have hyβ : y ∈ stab β := ((mem_Qgrp_iff hA).mp hy).1.2
    have hmem : ∀ e ∈ Vst β, ∀ z : ZMod 2, ⁅y, pw e z⁆ ∈ Zv β := fun e he' z =>
      he _ (pw_mem he' z) y hy
    have hc1 : Commute ⁅y, pw a (x 1)⁆ (pw p (x 0)) :=
      Vst_comm hA hb β (hYV (hZY (hmem a haV _))) (pw_mem hpV _)
    have hc2 : Commute ⁅y, pw c (x 2)⁆ (pw p (x 0) * pw a (x 1)) :=
      Vst_comm hA hb β (hYV (hZY (hmem c hcV _))) (A_le_Vst hαβ hpa)
    rw [← bit_comm_pw, ← bit_comm_pw, ← bit_comm_pw,
      ← bit_mul h2 (hmem p hpV _) (hmem a haV _),
      ← bit_mul h2 ((Zv β).mul_mem (hmem p hpV _) (hmem a haV _)) (hmem c hcV _),
      ← comm_mul_right hc1, ← comm_mul_right hc2]
    rw [bit_of_not_mem fun h => hyw
      (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h))]
    decide

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
