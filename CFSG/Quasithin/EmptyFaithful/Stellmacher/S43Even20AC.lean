module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20AB

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem comm_mem_Vst {δ : Geo H M} {g y : G} (hg : g ∈ stab δ) (hy : y ∈ Vst δ) :
    ⁅g, y⁆ ∈ Vst δ := by
  rw [commutatorElement_def]
  exact (Vst δ).mul_mem ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vst δ hg) y).mp hy)
    ((Vst δ).inv_mem hy)

theorem comm_mem_of_relIndex_two (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) {δ : Geo H M}
    {Z L K : Subgroup G} {g : G} (hg : g ∈ stab δ) (hKV : K ≤ Vst δ) (hL : L.relIndex K = 2)
    (hLK : L ≤ K) (hgL : ∀ x ∈ L, ⁅g, x⁆ ∈ Z) {x₀ : G} (hx₀ : x₀ ∈ K) (hx₀L : x₀ ∉ L)
    (hgx₀ : ⁅g, x₀⁆ ∈ Z) : ∀ x ∈ K, ⁅g, x⁆ ∈ Z := by
  let U : Subgroup G :=
    { carrier := {x | x ∈ Vst δ ∧ ⁅g, x⁆ ∈ Z}
      one_mem' := ⟨(Vst δ).one_mem, by simp [Z.one_mem]⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨(Vst δ).mul_mem hx.1 hy.1, ?_⟩
        have hc : Commute ⁅g, y⁆ x := Vst_comm hA hb δ (comm_mem_Vst hg hy.1) hx.1
        rw [comm_mul_right hc]
        exact Z.mul_mem hx.2 hy.2
      inv_mem' := fun {x} hx => by
        have e : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Vst_sq hA hb δ hx.1)
        show x⁻¹ ∈ Vst δ ∧ ⁅g, x⁻¹⁆ ∈ Z
        rw [e]
        exact hx }
  have hLU : L ≤ U := fun x hx => ⟨hKV (hLK hx), hgL x hx⟩
  have hle := le_of_relIndex_two hL hLK hLU hx₀ ⟨hKV hx₀, hgx₀⟩ hx₀L
  exact fun x hx => (hle hx).2

variable {α β : Geo H M}

theorem relIndex_Qgrp_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (h4 : Nat.card (Vn β) = 2 ^ 6) :
    (Qgrp α β).relIndex (Qv β) = 4 := by
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ : α ∈ nbrs β := nbrs_symm hβ
  obtain ⟨ν, l₃, h29⟩ := hs.exists_sit29 hA h26 hβv hαβ
  have hν : ν ∈ nbrs β := h29.n₂
  obtain ⟨a, ha, haY⟩ := exists_mem_A_not_mem_Yv hA h26 hs hβv hαβ
  obtain ⟨b, hb', hbY⟩ := exists_mem_A_not_mem_Yv hA h26 hs hβv hν
  have haV := A_le_Vst hαβ ha
  have hbV := A_le_Vst hν hb'
  have hbA : b ∉ ⁅Zv α, Qv β⁆ := fun h =>
    hbY (A_inf_A_le hA h26 hs hβv hαβ hν h29.ne₁₂ ⟨h, hb'⟩)
  have h2 := relIndex_Zv_Yv hA h26 hs hβv
  have hPZ : Qv β ≤ Subgroup.normalizer (Zv β : Set G) :=
    (pCoreOf_le 2 _).trans (stab_le_normalizer_Zv hA β)
  have hPT : Qv β ≤ Subgroup.normalizer (Yv β : Set G) :=
    (pCoreOf_le 2 _).trans (hs.stab_le_normalizer_Yv hA h26 hβv)
  have hea : ∀ q ∈ Qv β, ⁅q, a⁆ ∈ Yv β := fun q hq => comm_Qv_A_mem hA h26 hs hβv hαβ hq ha
  have heb : ∀ q ∈ Qv β, ⁅q, b⁆ ∈ Yv β := fun q hq => comm_Qv_A_mem hA h26 hs hβv hν hq hb'
  let f : Fin 2 → ↥(Qv β) →* Multiplicative (ZMod 2) :=
    ![bitHom h2 hPZ hPT hea, bitHom h2 hPZ hPT heb]
  refine (relIndex_eq_of_iInf_ker f ?_ ?_).trans (by norm_num)
  · intro q
    rw [Fin.forall_fin_two]
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, bitHom_eq_one_iff]
    constructor
    · intro hq
      have h1 := ((mem_Qgrp_iff hA).mp hq).2
      exact ⟨h1 a haV, h1 b hbV⟩
    · rintro ⟨h1, h1'⟩
      have hqβ : (q : G) ∈ stab β := pCoreOf_le 2 _ q.2
      have hYZ : ∀ x ∈ Yv β, ⁅(q : G), x⁆ ∈ Zv β := fun x hx =>
        comm_Qv_Yv_mem hA h26 hs hβv q.2 hx
      have hAZ := comm_mem_of_relIndex_two hA hb hqβ (A_le_Vst hαβ)
        (hs.relIndex_Yv_comm hA h26 hβv hαβ) (hs.Yv_le_comm hA h26 hβv hαβ) hYZ ha haY h1
      refine (mem_Qgrp_iff hA).mpr ⟨⟨Qv_le_stab_of_mem_nbrs hA hαβ q.2, hqβ⟩, ?_⟩
      exact comm_mem_of_relIndex_two hA hb hqβ le_rfl
        (relIndex_A_Vst hA h26 hs hb hβv hαβ h4) (A_le_Vst hαβ) hAZ hbV hbA h1'
  · intro x hx
    have hx01 : ¬ (x 0 = 0 ∧ x 1 = 0) := fun hc =>
      hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    have hwV : pw a (x 0) * pw b (x 1) ∈ Vst β := (Vst β).mul_mem (pw_mem haV _) (pw_mem hbV _)
    have hwY : pw a (x 0) * pw b (x 1) ∉ Yv β := by
      rcases eq_zero_or_eq_one (x 0) with h0 | h0 <;>
        rcases eq_zero_or_eq_one (x 1) with h1 | h1
      · exact absurd ⟨h0, h1⟩ hx01
      · rw [h0, h1, pw_zero, pw_one, one_mul]
        exact hbY
      · rw [h0, h1, pw_one, pw_zero, mul_one]
        exact haY
      · rw [h0, h1, pw_one, pw_one]
        intro hab
        apply hbA
        have h3 := (⁅Zv α, Qv β⁆).mul_mem ((⁅Zv α, Qv β⁆).inv_mem ha)
          (hs.Yv_le_comm hA h26 hβv hαβ hab)
        simpa using h3
    obtain ⟨q, hq, hqw⟩ := exists_comm_not_mem hA h26 hs hb hβv h4 hwV hwY
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [Fin.sum_univ_two]
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, bitHom_apply]
    have hc : Commute ⁅q, pw b (x 1)⁆ (pw a (x 0)) :=
      Vst_comm hA hb β (comm_mem_Vst (pCoreOf_le 2 _ hq) (pw_mem hbV _)) (pw_mem haV _)
    rw [← bit_comm_pw, ← bit_comm_pw, ← bit_mul h2
      (comm_Qv_A_mem hA h26 hs hβv hαβ hq (pw_mem ha _))
      (comm_Qv_A_mem hA h26 hs hβv hν hq (pw_mem hb' _)), ← comm_mul_right hc,
      bit_of_not_mem hqw]
    decide

theorem relIndex_Qgrp_edge (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (h4 : Nat.card (Vn β) = 2 ^ 6) :
    (Qgrp α β).relIndex (stab α ⊓ stab β) = 8 := by
  have hQE : Qv β ≤ stab α ⊓ stab β :=
    le_inf (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ)) (pCoreOf_le 2 _)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (Qgrp_le_Qv hA h26 hs hβ) hQE,
    relIndex_Qgrp_Qv hA h26 hs hb hβ h4, Sit43.relIndex_Qv_edge hA hs.vα hβ]

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
