module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20BD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem stab_le_normalizer_Wcomm (α : Geo H M) :
    stab α ≤ Subgroup.normalizer (Wcomm α : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Wcomm, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (stab_le_normalizer_Wn α hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)]

omit [Finite G] in
theorem conj_mem_centralizer {W : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (W : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  have hw' : x⁻¹ * w * x⁻¹⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) w).mp hw
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hw'
  calc w * (x * c * x⁻¹) = x * ((x⁻¹ * w * x⁻¹⁻¹) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * w * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * w := by group

omit [Finite G] in
theorem mem_normalizer_centralizer {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer hx, fun hc => ?_⟩
  have := conj_mem_centralizer (Subgroup.inv_mem _ hx) hc
  simpa [mul_assoc] using this

omit [Finite G] in
theorem stab_le_normalizer_Mcent (α : Geo H M) :
    stab α ≤ Subgroup.normalizer (Mcent α : Set G) :=
  le_normalizer_inf (le_normalizer_pCoreOf 2 _)
    fun _ hx => mem_normalizer_centralizer (stab_le_normalizer_Wcomm α hx)

omit [Finite G] in
theorem comm_mem_Zv {α β : Geo H M} (h : Hyp18 α β) {v y : G} (hv : v ∈ Wn α)
    (hy : y ∈ Qv α) : y * v * y⁻¹ * v⁻¹ ∈ Zv α := by
  have h1 := h.comm_Wn_Qv (Subgroup.commutator_mem_commutator hv hy)
  have e : ⁅v, y⁆⁻¹ = y * v * y⁻¹ * v⁻¹ := by simp only [commutatorElement_def]; group
  rw [← e]
  exact (Zv α).inv_mem h1

theorem comm_mem_A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β) {v y : G}
    (hv : v ∈ Vst β) (hy : y ∈ Qv α) : y * v * y⁻¹ * v⁻¹ ∈ ⁅Zv α, Qv β⁆ := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  rw [← hs.Vst_inf_Zv hA h26 hb hβv (nbrs_symm hβ) h.card_Vn]
  refine ⟨?_, comm_mem_Zv h (hs.Vn_le_Wn hA h26 hβ (Vst_le_Vn β hv)) hy⟩
  have h1 : y * v * y⁻¹ ∈ Vst β :=
    (Subgroup.mem_normalizer_iff.mp (h.Vst_normal (hs.Qv_le_Mab hA hβ hy)) v).mp hv
  exact (Vst β).mul_mem h1 ((Vst β).inv_mem hv)

theorem mem_Cst_of_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) {v₀ y : G} (hv₀ : v₀ ∈ Vst β) (hv₀' : v₀ ∉ ⁅Zv α, Qv β⁆)
    (hy : y ∈ Qv α) (hyv : y * v₀ = v₀ * y) : y ∈ Cst β := by
  rw [← h19.C_eq]
  exact ⟨⟨pCoreOf_le 2 _ hy, Qv_le_stab_of_mem_nbrs hA hβ hy⟩,
    mem_centralizer_Vst (relIndex_comm_Vst hA h26 hs hb hβ h.card_Vn) hv₀ hv₀'
      (Qv_le_centralizer_comm hA h26 hs hβ hy) hyv⟩

theorem comm_conj (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β) {v₀ y d : G}
    (hv₀ : v₀ ∈ Vst β) (hv₀' : v₀ ∉ ⁅Zv α, Qv β⁆) (hy : y ∈ Qv α) (hd : d ∈ Mab α β) :
    (d * y * d⁻¹) * v₀ * (d * y * d⁻¹)⁻¹ * v₀⁻¹ = d * (y * v₀ * y⁻¹ * v₀⁻¹) * d⁻¹ := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hAeq := hs.Vst_inf_Zv hA h26 hb hβv (nbrs_symm hβ) h.card_Vn
  have hdα : d ∈ stab α := Mab_le_stab α β hd
  have hv₁ : d⁻¹ * v₀ * d⁻¹⁻¹ ∈ Vst β :=
    (Subgroup.mem_normalizer_iff.mp (h.Vst_normal (Subgroup.inv_mem _ hd)) v₀).mp hv₀
  have hv₁' : d⁻¹ * v₀ * d⁻¹⁻¹ ∉ ⁅Zv α, Qv β⁆ := by
    intro hc
    rw [← hAeq] at hc
    have h1 : d * (d⁻¹ * v₀ * d⁻¹⁻¹) * d⁻¹ ∈ Vst β ⊓ Zv α :=
      ⟨(Subgroup.mem_normalizer_iff.mp (h.Vst_normal hd) _).mp hc.1,
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hdα) _).mp hc.2⟩
    have e : d * (d⁻¹ * v₀ * d⁻¹⁻¹) * d⁻¹ = v₀ := by group
    rw [e, hAeq] at h1
    exact hv₀' h1
  have ha := inv_mul_mem_of_relIndex_two (relIndex_comm_Vst hA h26 hs hb hβ h.card_Vn) hv₀ hv₁
    hv₀' hv₁'
  have hya : Commute (v₀⁻¹ * (d⁻¹ * v₀ * d⁻¹⁻¹)) y :=
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_comm hA h26 hs hβ hy) _ ha
  have h2 := hya.inv_right.eq
  calc (d * y * d⁻¹) * v₀ * (d * y * d⁻¹)⁻¹ * v₀⁻¹
      = d * y * v₀ * ((v₀⁻¹ * (d⁻¹ * v₀ * d⁻¹⁻¹)) * y⁻¹) * d⁻¹ * v₀⁻¹ := by group
    _ = d * y * v₀ * (y⁻¹ * (v₀⁻¹ * (d⁻¹ * v₀ * d⁻¹⁻¹))) * d⁻¹ * v₀⁻¹ := by rw [h2]
    _ = d * (y * v₀ * y⁻¹ * v₀⁻¹) * d⁻¹ := by group

theorem comm_fix (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M} (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β) {v₀ y d : G}
    (hv₀ : v₀ ∈ Vst β) (hv₀' : v₀ ∉ ⁅Zv α, Qv β⁆) (hy : y ∈ Qv α) (hd : d ∈ Mab α β)
    (hc : d * y * d⁻¹ * y⁻¹ ∈ Cst β) :
    d * (y * v₀ * y⁻¹ * v₀⁻¹) = (y * v₀ * y⁻¹ * v₀⁻¹) * d := by
  have e1 := comm_conj hA h26 hs hb hβ h hv₀ hv₀' hy hd
  have hv₀W : v₀ ∈ Wn α := hs.Vn_le_Wn hA h26 hβ (Vst_le_Vn β hv₀)
  set c := d * y * d⁻¹ * y⁻¹ with hc_def
  set fy := y * v₀ * y⁻¹ * v₀⁻¹ with hfy
  have hcv : v₀ * c = c * v₀ := Subgroup.mem_centralizer_iff.mp hc.2 v₀ (Vst_le_Vn β hv₀)
  have hcf : fy * c = c * fy := Subgroup.mem_centralizer_iff.mp
    (Qv_le_centralizer_Zv hA α (Cst_le_Qv hA hs hβ hc)) fy (comm_mem_Zv h hv₀W hy)
  have e2 : (d * y * d⁻¹) * v₀ * (d * y * d⁻¹)⁻¹ * v₀⁻¹ = fy := by
    have e3 : d * y * d⁻¹ = c * y := by rw [hc_def]; group
    calc (d * y * d⁻¹) * v₀ * (d * y * d⁻¹)⁻¹ * v₀⁻¹ = c * fy * v₀ * c⁻¹ * v₀⁻¹ := by
          rw [e3, hfy]; group
      _ = fy * (c * v₀) * c⁻¹ * v₀⁻¹ := by rw [← hcf]; group
      _ = fy := by rw [← hcv]; group
  rw [e2] at e1
  calc d * fy = d * fy * d⁻¹ * d := by group
    _ = fy * d := by rw [← e1]

theorem mem_Zv_of_comm_t3 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α)
    (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α)) {d : ↥(stab α)} (hd : D.ψ d = t3) {z : G}
    (hz : z ∈ ⁅Zv α, Qv β⁆) (hdz : (d : G) * z = z * d) : z ∈ Zv β := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  rw [hs.comm_Qv_eq hA h26 hβv (nbrs_symm hβ), ← D.map_commW_top inf_le_left, D.bar_S] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hw' := (mem_commW_iff orth mem_S5Syl_iff (Uf := Finset.univ) (fun u => by simp) w).mp hw
  have hfix : orth.act t3 w = w := by
    rw [← hd]
    apply D.inj
    rw [D.act_eq, hdz]
    group
  have hall := fix_t3 w hw' hfix
  rw [← hs.Zv_inf_centralizer hA h26 hβv (nbrs_symm hβ), ← D.map_fixW inf_le_left, D.bar_S]
  exact ⟨w, fun b hb => hall b ((mem_S5Syl_iff b).mp hb), rfl⟩

theorem Qv_le_Qgrp_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    {v₀ : G} (hv₀ : v₀ ∈ Vst β) (hv₀' : v₀ ∉ ⁅Zv α, Qv β⁆)
    (hZ : ∀ y ∈ Qv α, y * v₀ * y⁻¹ * v₀⁻¹ ∈ Zv β) : Qv α ≤ Qgrp α β := by
  intro y hy
  refine (mem_Qgrp_iff hA).mpr ⟨⟨pCoreOf_le 2 _ hy, Qv_le_stab_of_mem_nbrs hA hβ hy⟩,
    fun x hx => ?_⟩
  have hyA := Qv_le_centralizer_comm hA h26 hs hβ hy
  by_cases hxA : x ∈ ⁅Zv α, Qv β⁆
  · have h1 := Subgroup.mem_centralizer_iff.mp hyA x hxA
    have : y * x * y⁻¹ * x⁻¹ = 1 := by rw [← h1]; group
    rw [this]
    exact Subgroup.one_mem _
  · have ha := inv_mul_mem_of_relIndex_two (relIndex_comm_Vst hA h26 hs hb hβ h.card_Vn) hv₀
      hx hv₀' hxA
    have h1 : Commute (v₀⁻¹ * x) y := Subgroup.mem_centralizer_iff.mp hyA _ ha
    have h2 := h1.inv_right.eq
    have e : y * x * y⁻¹ * x⁻¹ = y * v₀ * y⁻¹ * v₀⁻¹ := by
      calc y * x * y⁻¹ * x⁻¹ = y * v₀ * ((v₀⁻¹ * x) * y⁻¹) * x⁻¹ := by group
        _ = y * v₀ * (y⁻¹ * (v₀⁻¹ * x)) * x⁻¹ := by rw [h2]
        _ = y * v₀ * y⁻¹ * v₀⁻¹ := by group
    rw [e]
    exact hZ y hy

theorem not_Qv_le_Qgrp (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α) (h20 : Out20bc α β) :
    ¬ Qv α ≤ Qgrp α β := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := Subgroup.relIndex_mul_relIndex _ _ _ hle (Qgrp_le α β)
  rw [h20.relIndex_Q_P, hs.relIndex_Qv_edge_stab hA hβ] at e
  have h1 : (Qv α).relIndex (Qgrp α β) = 1 := by omega
  have hQ : Qgrp α β = Qv α := le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  have hn : stab β ≤ Subgroup.normalizer (Qv α : Set G) := by
    rw [← hQ]
    exact (le_sup_right : stab β ≤ Xgrp α β).trans h20.Q_normal
  exact hs.not_Qv_le_Qv_nbr hA h26 hs.vα hβ
    (le_pCoreOf_of_le_normalizer 2 (Qv_le_stab_of_mem_nbrs hA hβ) hn
      (pCoreOf_isPGroup 2 (stab α)))

theorem exists_t3 {α β : Geo H M} (D : Dict5 (stab α) (stab α ⊓ stab β) (Zv α))
    {C : Subgroup G} (hsec : IsSec (stab α) C (Qv α)) (hcard : C.relIndex (Qv α) ∣ 8) :
    ∃ d : ↥(stab α), D.ψ d = t3 ∧ ∀ y ∈ Qv α, (d : G) * y * (d : G)⁻¹ * y⁻¹ ∈ C := by
  obtain ⟨g, hg⟩ := D.surj c5
  obtain ⟨k, hk⟩ := D.surj (swap 0 1)
  have hg5 : (g : G) ^ 5 ∈ Qv α := by
    have h1 : D.ψ (g ^ 5) = 1 := by rw [map_pow, hg, c5_pow_five]
    have h2 := (D.ker_iff _).mp h1
    rwa [SubgroupClass.coe_pow] at h2
  have hgfix := comm_mem_of_pow_five hsec hcard g.2 fun y hy => hsec.comm _ hg5 _ hy
  have hT : ∀ x, x ∈ cSecIn (stab α) C (Qv α) ↔
      x ∈ stab α ∧ ∀ y ∈ Qv α, x * y * x⁻¹ * y⁻¹ ∈ C := fun x => mem_cSecIn_iff hsec.normL
  have hTn : ∀ x ∈ stab α, ∀ t ∈ cSecIn (stab α) C (Qv α),
      x * t * x⁻¹ ∈ cSecIn (stab α) C (Qv α) := by
    intro x hx t ht
    obtain ⟨htα, htC⟩ := (hT t).mp ht
    refine (hT _).mpr ⟨(stab α).mul_mem ((stab α).mul_mem hx htα) ((stab α).inv_mem hx),
      fun y hy => ?_⟩
    have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ Qv α :=
      (Subgroup.mem_normalizer_iff.mp (hsec.normN ((stab α).inv_mem hx)) y).mp hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (hsec.normL hx) _).mp (htC _ hy')
    have e : x * (t * (x⁻¹ * y * x⁻¹⁻¹) * t⁻¹ * (x⁻¹ * y * x⁻¹⁻¹)⁻¹) * x⁻¹ =
        x * t * x⁻¹ * y * (x * t * x⁻¹)⁻¹ * y⁻¹ := by group
    rwa [e] at h1
  have hgT : (g : G) ∈ cSecIn (stab α) C (Qv α) := (hT _).mpr ⟨g.2, hgfix⟩
  refine ⟨g * k * g⁻¹ * k⁻¹, ?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hk]
    rfl
  · have hmem : ((g * k * g⁻¹ * k⁻¹ : ↥(stab α)) : G) ∈ cSecIn (stab α) C (Qv α) := by
      have e : ((g * k * g⁻¹ * k⁻¹ : ↥(stab α)) : G) =
          (g : G) * ((k : G) * (g : G)⁻¹ * (k : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]
      exact Subgroup.mul_mem _ hgT (hTn _ k.2 _ (Subgroup.inv_mem _ hgT))
    exact ((hT _).mp hmem).2 y hy

theorem not_le_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) :
    ¬ Wcomm α ≤ Subgroup.centralizer (Cst β : Set G) := by
  intro hW
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_Vst_not_mem hA h26 hs hb hβ h.card_Vn
  have hCQ := Cst_le_Qv hA hs hβ
  have hCM : Cst β = Mcent α :=
    le_antisymm (le_inf hCQ (Subgroup.le_centralizer_iff.mp hW)) h19.M_le_C
  have hCn : stab α ≤ Subgroup.normalizer (Cst β : Set G) := hCM ▸ stab_le_normalizer_Mcent α
  have hv₀W : v₀ ∈ Wn α := hs.Vn_le_Wn hA h26 hβ (Vst_le_Vn β hv₀)
  have hKZ : ∀ k ∈ Qv α, ∀ z ∈ Zv α, k * z = z * k := fun k hk z hz =>
    (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α hk) z hz).symm
  have hv : ∀ k ∈ Qv α, k * v₀ * k⁻¹ * v₀⁻¹ ∈ Zv α := fun k hk => comm_mem_Zv h hv₀W hk
  have hker : ∀ y : ↥(Qv α), commHom hKZ (Zv_comm hA α) hv y = 1 → (y : G) ∈ Cst β :=
    fun y hy => mem_Cst_of_comm hA h26 hs hb hβ h h19 hv₀ hv₀' y.2
      ((commHom_eq_one_iff hKZ (Zv_comm hA α) hv y).mp hy)
  have hcomm : ∀ x ∈ Qv α, ∀ y ∈ Qv α, x * y * x⁻¹ * y⁻¹ ∈ Cst β := by
    intro x hx y hy
    have hc := Zv_comm hA α _ (commHom hKZ (Zv_comm hA α) hv ⟨x, hx⟩).2 _
      (commHom hKZ (Zv_comm hA α) hv ⟨y, hy⟩).2
    have h1 := hker (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
      rw [hc]
      group)
    simpa using h1
  have hsq : ∀ x ∈ Qv α, x ^ 2 ∈ Cst β := by
    intro x hx
    have h1 := hker (⟨x, hx⟩ ^ 2) (by
      rw [map_pow]
      apply Subtype.ext
      rw [SubgroupClass.coe_pow]
      exact (isElemAbelian_Zv hA α).2 _ (commHom hKZ (Zv_comm hA α) hv ⟨x, hx⟩).2)
    simpa using h1
  have hsec : IsSec (stab α) (Cst β) (Qv α) := ⟨hCQ, le_normalizer_pCoreOf 2 _, hCn, hcomm, hsq⟩
  have hcard : (Cst β).relIndex (Qv α) ∣ 8 := by
    have hAZ := hs.comm_le_Zv hA h26 hβv (nbrs_symm hβ)
    have hdvd := relIndex_centralizer_dvd (K := Qv α) (Z := ⁅Zv α, Qv β⁆) (v := v₀)
      (fun k hk z hz =>
        (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_comm hA h26 hs hβ hk) z hz).symm)
      (fun a ha b hb => Zv_comm hA α a (hAZ ha) b (hAZ hb))
      (fun k hk => comm_mem_A hA h26 hs hb hβ h hv₀ hk)
    rw [hs.card_comm_Qv hA h26 hβv (nbrs_symm hβ)] at hdvd
    have hle : Qv α ⊓ Subgroup.centralizer ({v₀} : Set G) ≤ Cst β := fun y hy =>
      mem_Cst_of_comm hA h26 hs hb hβ h h19 hv₀ hv₀' hy.1
        (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
    have h3 := Subgroup.relIndex_dvd_of_le_left (Qv α) hle
    rw [Subgroup.inf_relIndex_left] at h3
    exact h3.trans hdvd
  obtain ⟨d, hdψ, hdC⟩ := exists_t3 D hsec hcard
  have hdM : (d : G) ∈ Mab α β := (Sit43.mem_Mab_iff D d).mpr (by rw [hdψ]; exact t3_four)
  have hZ : ∀ y ∈ Qv α, y * v₀ * y⁻¹ * v₀⁻¹ ∈ Zv β := fun y hy =>
    mem_Zv_of_comm_t3 hA h26 hs hβ D hdψ (comm_mem_A hA h26 hs hb hβ h hv₀ hy)
      (comm_fix hA h26 hs hb hβ h hv₀ hv₀' hy hdM (hdC y hy))
  exact not_Qv_le_Qgrp hA h26 hs hβ h20 (Qv_le_Qgrp_of hA h26 hs hb hβ h hv₀ hv₀' hZ)

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B
