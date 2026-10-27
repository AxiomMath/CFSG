module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even20BGen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom Equiv
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Qgrp_le (α β : Geo H M) : Qgrp α β ≤ stab α ⊓ stab β :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem mem_Qgrp_iff (hA : F53Amalgam H M S) {α β : Geo H M} {y : G} :
    y ∈ Qgrp α β ↔ y ∈ stab α ⊓ stab β ∧ ∀ x ∈ Vst β, y * x * y⁻¹ * x⁻¹ ∈ Zv β :=
  mem_cSecIn_iff (inf_le_right.trans (stab_le_normalizer_Zv hA β))

theorem Cst_le_stab (hA : F53Amalgam H M S) {α β : Geo H M} (hβ : β ∈ nbrs α) :
    Cst β ≤ stab α ⊓ stab β :=
  fun _ hg => ⟨Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ) hg.1, pCoreOf_le 2 _ hg.1⟩

theorem Cst_le_Qv (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α) {β : Geo H M}
    (hβ : β ∈ nbrs α) : Cst β ≤ Qv α := by
  intro g hg
  rw [← hs.centralizer_Zv hA hs.vα]
  exact ⟨(Cst_le_stab hA hβ hg).1, Subgroup.centralizer_le (Sit43.Zv_le_Vn hβ) hg.2⟩

omit [Finite G] in
theorem Vst_le_Vn (β : Geo H M) : Vst β ≤ Vn β := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have h1 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn β (pCoreOf_le 2 _ hb))
    a⁻¹).mp (Subgroup.inv_mem _ ha)
  rw [commutatorElement_def]
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ Vn β := Subgroup.mul_mem _ ha h1
  simpa [mul_assoc] using h2

theorem Cst_le_Qgrp (hA : F53Amalgam H M S) {α β : Geo H M} (hβ : β ∈ nbrs α) :
    Cst β ≤ Qgrp α β := by
  intro g hg
  refine (mem_Qgrp_iff hA).mpr ⟨Cst_le_stab hA hβ hg, fun x hx => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hg.2 x (Vst_le_Vn β hx)
  have : g * x * g⁻¹ * x⁻¹ = 1 := by rw [← h1]; group
  rw [this]
  exact Subgroup.one_mem _

theorem Zv_comm (hA : F53Amalgam H M S) (δ : Geo H M) :
    ∀ a ∈ Zv δ, ∀ b ∈ Zv δ, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val ((isElemAbelian_Zv hA δ).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite G] in
theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) : X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) :
      Set G) := fun _ hx => Subgroup.mem_normalizer_iff.mpr fun h =>
  ⟨fun hh => ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) h).mp hh.1,
      (Subgroup.mem_normalizer_iff.mp (hB hx) h).mp hh.2⟩,
    fun hh => ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) h).mpr hh.1,
      (Subgroup.mem_normalizer_iff.mp (hB hx) h).mpr hh.2⟩⟩

theorem relIndex_le_four (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α) {β : Geo H M}
    (hβ : β ∈ nbrs α) {K : Subgroup G} (hK : K ≤ stab α ⊓ stab β)
    (hKn : Mab α β ≤ Subgroup.normalizer (K : Set G)) : (Qv α).relIndex K ≤ 4 := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hKX : K ≤ stab α := hK.trans inf_le_left
  have hcard := D.card_bar hKX
  have hle : D.bar K ≤ S5T := by
    rintro τ ⟨x, hx, rfl⟩
    rw [mem_S5T_iff]
    have hxK : (x : G) ∈ K := hx
    refine core_S5SylF _ ((mem_S5Syl_iff _).mp (D.ψ_mem_S5Syl (hK hxK))) fun σ hσ => ?_
    obtain ⟨m, rfl⟩ := D.surj σ
    have hm : (m : G) ∈ Mab α β := (Sit43.mem_Mab_iff D m).mpr hσ
    have hmx : (m : G) * x * (m : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hm) x).mp hxK
    have e : D.ψ m * D.ψ x * (D.ψ m)⁻¹ = D.ψ ⟨(m : G) * x * (m : G)⁻¹, D.S_le (hK hmx)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, ← mem_S5Syl_iff]
    exact D.ψ_mem_S5Syl (hK hmx)
  have h4 := (Subgroup.card_le_of_le hle).trans_eq card_S5T
  rw [hcard] at h4
  rwa [Subgroup.inf_relIndex_right] at h4

theorem isSylowTwoOf_Mab (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α) {β : Geo H M}
    (hβ : β ∈ nbrs α) : IsSylowTwoOf (stab α ⊓ stab β) (Mab α β) := by
  obtain ⟨-, h2, h3⟩ := sylow_stab_inf_left hA hβ
  have hSM := hs.stab_inf_le_Mab hA hβ
  refine ⟨hSM, h2, fun hdvd => h3 ?_⟩
  have e := Subgroup.relIndex_mul_relIndex _ _ _ hSM (Mab_le_stab α β)
  change 2 ∣ (stab α ⊓ stab β).relIndex (stab α)
  rw [← e]
  exact Dvd.dvd.mul_right hdvd _

theorem relIndex_pCoreOf_le_four (hA : F53Amalgam H M S) {α : Geo H M} (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) : (Qv α).relIndex (pCoreOf 2 (Mab α β)) ≤ 4 :=
  relIndex_le_four hA hs hβ (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_Mab hA hs hβ))
    (le_normalizer_pCoreOf 2 _)

theorem relIndex_comm_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (h4 : Nat.card (Vn β) = 2 ^ 6) : (⁅Zv α, Qv β⁆).relIndex (Vst β) = 2 := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hle : ⁅Zv α, Qv β⁆ ≤ Vst β :=
    (hs.Vst_inf_Zv hA h26 hb hβv (nbrs_symm hβ) h4) ▸ inf_le_left
  have h1 := Subgroup.relIndex_mul_card ⁅Zv α, Qv β⁆ (Vst β)
  rw [inf_eq_left.mpr hle, hs.card_comm_Qv hA h26 hβv (nbrs_symm hβ),
    hs.card_Vst hA h26 hb hβv h4] at h1
  omega

theorem exists_Vst_not_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (h4 : Nat.card (Vn β) = 2 ^ 6) : ∃ v₀ ∈ Vst β, v₀ ∉ ⁅Zv α, Qv β⁆ := by
  by_contra hcon
  push Not at hcon
  have h2 := relIndex_comm_Vst hA h26 hs hb hβ h4
  rw [Subgroup.relIndex_eq_one.mpr hcon] at h2
  omega

omit [Finite G] in
theorem mem_centralizer_Vst {α β : Geo H M} (h2 : (⁅Zv α, Qv β⁆).relIndex (Vst β) = 2)
    {v₀ y : G} (hv₀ : v₀ ∈ Vst β) (hv₀' : v₀ ∉ ⁅Zv α, Qv β⁆)
    (hyA : y ∈ Subgroup.centralizer ((⁅Zv α, Qv β⁆ : Subgroup G) : Set G))
    (hyv : y * v₀ = v₀ * y) : y ∈ Subgroup.centralizer (Vst β : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  by_cases hxA : x ∈ ⁅Zv α, Qv β⁆
  · exact Subgroup.mem_centralizer_iff.mp hyA x hxA
  · have h1 := inv_mul_mem_of_relIndex_two h2 hv₀ hx hv₀' hxA
    have h3 := Subgroup.mem_centralizer_iff.mp hyA _ h1
    calc x * y = v₀ * (v₀⁻¹ * x) * y := by group
      _ = v₀ * (y * (v₀⁻¹ * x)) := by rw [mul_assoc, h3]
      _ = y * v₀ * (v₀⁻¹ * x) := by rw [← mul_assoc, hyv]
      _ = y * x := by group

theorem Qv_le_centralizer_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α) :
    Qv α ≤ Subgroup.centralizer ((⁅Zv α, Qv β⁆ : Subgroup G) : Set G) :=
  (Qv_le_centralizer_Zv hA α).trans
    (Subgroup.centralizer_le (hs.comm_le_Zv hA h26 (Sit43.vtype_true_of_adj hs.vα hβ)
      (nbrs_symm hβ)))

theorem relIndex_Cst_inf_dvd_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) : (Cst β).relIndex (Qgrp α β ⊓ Qv α) ∣ 2 := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_Vst_not_mem hA h26 hs hb hβ h.card_Vn
  have h2 := relIndex_comm_Vst hA h26 hs hb hβ h.card_Vn
  have hZβα : Zv β ≤ Zv α := hs.Zv_le_Zv_nbr hA h26 hβv (nbrs_symm hβ)
  have hdvd := relIndex_centralizer_dvd (K := Qgrp α β ⊓ Qv α) (Z := Zv β) (v := v₀)
    (fun k hk z hz => (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α hk.2) z
      (hZβα hz)).symm)
    (Zv_comm hA β) (fun k hk => ((mem_Qgrp_iff hA).mp hk.1).2 v₀ hv₀)
  rw [hs.card_Zv_true hA h26 hβv] at hdvd
  have hle : (Qgrp α β ⊓ Qv α) ⊓ Subgroup.centralizer ({v₀} : Set G) ≤ Cst β := by
    rintro y ⟨⟨hyQ, hyQa⟩, hyv⟩
    rw [← h19.C_eq]
    refine ⟨Qgrp_le α β hyQ, mem_centralizer_Vst h2 hv₀ hv₀'
      (Qv_le_centralizer_comm hA h26 hs hβ hyQa) ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hyv
  have h3 := Subgroup.relIndex_dvd_of_le_left (Qgrp α β ⊓ Qv α) hle
  rw [Subgroup.inf_relIndex_left] at h3
  exact h3.trans hdvd

theorem relIndex_Cst_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) :
    (Cst β).relIndex (Qgrp α β ⊓ Qv α) = 2 ∧ (Qv α).relIndex (Qgrp α β) = 4 := by
  have hC : Cst β ≤ Qgrp α β ⊓ Qv α := le_inf (Cst_le_Qgrp hA hβ) (Cst_le_Qv hA hs hβ)
  have e := Subgroup.relIndex_mul_relIndex _ _ _ hC (inf_le_left : Qgrp α β ⊓ Qv α ≤ Qgrp α β)
  rw [h20.relIndex_C_Q, Subgroup.inf_relIndex_left] at e
  have h1 := Nat.le_of_dvd (by norm_num) (relIndex_Cst_inf_dvd_two hA h26 hs hb hβ h h19)
  have h4 := relIndex_le_four hA hs hβ (Qgrp_le α β)
    ((le_sup_left : Mab α β ≤ Xgrp α β).trans h20.Q_normal)
  have hpos : 0 < (Cst β).relIndex (Qgrp α β ⊓ Qv α) := by
    unfold Subgroup.relIndex
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  interval_cases hc : (Cst β).relIndex (Qgrp α β ⊓ Qv α) <;> omega

theorem Qgrp_sup_Qv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) : Qgrp α β ⊔ Qv α = pCoreOf 2 (Mab α β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : Qgrp α β ≤ Mab α β := (Qgrp_le α β).trans (hs.stab_inf_le_Mab hA hβ)
  have hQp : IsPGroup 2 (Qgrp α β) := (sylow_stab_inf_left hA hβ).2.1.to_le (Qgrp_le α β)
  have hQn : Mab α β ≤ Subgroup.normalizer (Qgrp α β : Set G) :=
    (le_sup_left : Mab α β ≤ Xgrp α β).trans h20.Q_normal
  have hQO : Qgrp α β ≤ pCoreOf 2 (Mab α β) := le_pCoreOf_of_le_normalizer 2 hQM hQn hQp
  have hQaO : Qv α ≤ pCoreOf 2 (Mab α β) :=
    le_pCoreOf_of_le_normalizer 2 (hs.Qv_le_Mab hA hβ)
      ((Mab_le_stab α β).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 (stab α))
  have hle : Qgrp α β ⊔ Qv α ≤ pCoreOf 2 (Mab α β) := sup_le hQO hQaO
  refine le_antisymm hle ?_
  have hQnα : Qgrp α β ≤ Subgroup.normalizer (Qv α : Set G) :=
    ((Qgrp_le α β).trans inf_le_left).trans (le_normalizer_pCoreOf 2 _)
  have hsup : (Qv α).relIndex (Qgrp α β ⊔ Qv α) = 4 := by
    rw [relIndex_sup_eq_of_le_normalizer hQnα]
    exact (relIndex_Cst_inf hA h26 hs hb hβ h h19 h20).2
  have e := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : Qv α ≤ Qgrp α β ⊔ Qv α) hle
  rw [hsup] at e
  have h4 := relIndex_pCoreOf_le_four hA hs hβ
  have hpos : 0 < (Qgrp α β ⊔ Qv α).relIndex (pCoreOf 2 (Mab α β)) := by
    unfold Subgroup.relIndex
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (Qgrp α β ⊔ Qv α).relIndex (pCoreOf 2 (Mab α β)) = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp h1

theorem comm_inf_le_Cst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20bc α β) : ⁅Qgrp α β ⊓ Qv α, Mab α β⁆ ≤ Cst β :=
  commutator_le_of_relIndex_two (relIndex_Cst_inf hA h26 hs hb hβ h h19 h20).1
    (le_normalizer_inf ((le_sup_left : Mab α β ≤ Xgrp α β).trans h20.Q_normal)
      ((Mab_le_stab α β).trans (le_normalizer_pCoreOf 2 _)))
    ((le_sup_left : Mab α β ≤ Xgrp α β).trans h20.C_normal)

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B
