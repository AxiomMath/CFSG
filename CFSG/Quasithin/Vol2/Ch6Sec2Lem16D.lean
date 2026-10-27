module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16C
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem ustruct_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    (∀ x ∈ uCh611 T L V, ∀ y ∈ uCh611 T L V, ⁅x, y⁆ ∈ zCh611 T) ∧
      zCh611 T ≤ centerOf (uCh611 T L V) ∧ centerOf (uCh611 T L V) ≤ uCh611 T L V ∧
      (∀ z ∈ centerOf (uCh611 T L V), ∀ x ∈ uCh611 T L V, x * z = z * x) ∧
      (∀ x ∈ uCh611 T L V, (∀ y ∈ uCh611 T L V, y * x = x * y) →
        x ∈ centerOf (uCh611 T L V)) ∧
      (∀ z ∈ zCh611 T, z * z = 1) ∧ Nat.card (zCh611 T) = 2 := by
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  have hZU : zCh611 T ≤ uCh611 T L V :=
    (h.omega_le_ZS h331 h432 h512 h614 h615).trans (le_conjClosure _ _)
  refine ⟨fun x hx y hy => ?_, fun z hz => ⟨hZU hz, Subgroup.mem_centralizer_iff.mpr
      fun u hu => (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm⟩, inf_le_left,
    fun z hz x hx => Subgroup.mem_centralizer_iff.mp hz.2 x hx,
    fun x hx hc => ⟨hx, Subgroup.mem_centralizer_iff.mpr hc⟩, fun z hz => ?_, hZ2⟩
  · rw [commutatorElement_def]
    exact h.comm_mem_ch615 h331 h432 h512 h614 h615 hx hy
  · have hZV : zCh611 T ≤ V := (h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left
    rw [← pow_two]
    exact h.toHyp611.isElemAbelian.2 z (hZV hz)

theorem symm_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {w : G} (hwH : w ∈ hCh611 T) (hw2 : w * w = 1)
    {x y : G} (hx : x ∈ uCh611 T L V) (hy : y ∈ uCh611 T L V) : ⁅x, ⁅w, y⁆⁆ = ⁅y, ⁅w, x⁆⁆ := by
  obtain ⟨hcomm, hZZU, -, hZUc, -, hZ2, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  exact comm_comm_symm_ch616 hZZU hZUc hcomm hZ2 hw2
    (fun u hu => (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hwH) u).mp hu)
    (fun z hz => (Subgroup.mem_centralizer_iff.mp hwH z hz).symm) hx hy

theorem alt_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {v : G} (hv : v ∈ V) {u : G} (hu : u ∈ uCh611 T L V) :
    ⁅u, ⁅v, u⁆⁆ = 1 := by
  have := h.comm_conj_eq_one_ch616 h331 h432 h512 h614 h615 hv hu
  rw [← this]
  simp only [commutatorElement_def]
  group

theorem exists_mul_of_mem_sup_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {e : G}
    (he : e ∈ (V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V)) :
    ∃ a ∈ V ⊓ uCh611 T L V, ∃ n ∈ centerOf (uCh611 T L V), a * n = e := by
  obtain ⟨-, -, -, hZUc, -, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hle : V ⊓ uCh611 T L V ≤ Subgroup.normalizer (centerOf (uCh611 T L V) : Set G) :=
    fun x hx => mem_normalizer_of_forall_conj_mem_of_le fun z hz => by
      rw [hZUc z hz x hx.2, mul_inv_cancel_right]
      exact hz
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at he
  obtain ⟨a, ha, n, hn, rfl⟩ := he
  exact ⟨a, ha, n, hn, rfl⟩

theorem ker_iff_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) {y : G} (hy : y ∈ uCh611 T L V) :
    ⁅v, y⁆ ∈ centerOf (uCh611 T L V) ↔
      y ∈ Subgroup.centralizer ((V ⊓ uCh611 T L V : Subgroup G) : Set G) := by
  obtain ⟨-, hZZU, -, hZUc, hcen, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hvH := h.V_le_hCh611 hv
  have hv2 : v * v = 1 := by rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 v hv
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hcommVU : ∀ u ∈ uCh611 T L V, ⁅v, u⁆ ∈ V ⊓ uCh611 T L V := fun u hu =>
    hVUc (Subgroup.commutator_mem_commutator hv hu)
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨a, ha, haz⟩ :=
      h.exists_comm_eq_U_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU e he
    have h1 : y * ⁅v, a⁆ = ⁅v, a⁆ * y := by
      rw [← commutatorElement_eq_one_iff_mul_comm, h.symm_ch616 h331 h432 h512 h614 h615 hvH hv2
        hy ha, commutatorElement_def, hZUc _ hk a ha, mul_inv_cancel_right, mul_inv_cancel]
    have h2 : y * (⁅v, a⁆⁻¹ * e) = (⁅v, a⁆⁻¹ * e) * y := hZUc _ (hZZU haz) y hy
    calc e * y = ⁅v, a⁆ * ((⁅v, a⁆⁻¹ * e) * y) := by group
      _ = ⁅v, a⁆ * (y * (⁅v, a⁆⁻¹ * e)) := by rw [h2]
      _ = (⁅v, a⁆ * y) * (⁅v, a⁆⁻¹ * e) := by group
      _ = (y * ⁅v, a⁆) * (⁅v, a⁆⁻¹ * e) := by rw [h1]
      _ = y * e := by group
  · intro hc
    refine hcen _ (hcommVU y hy).2 fun t ht => ?_
    rw [← commutatorElement_eq_one_iff_mul_comm, h.symm_ch616 h331 h432 h512 h614 h615 hvH hv2
      ht hy, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hc _ (hcommVU t ht)).symm

theorem ker_iff_conj_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) {x : G} (hxH : x ∈ hCh611 T)
    (hxN : x ∈ Subgroup.normalizer
      (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G))
    {y : G} (hy : y ∈ uCh611 T L V) :
    ⁅x * v * x⁻¹, y⁆ ∈ centerOf (uCh611 T L V) ↔
      y ∈ Subgroup.centralizer ((V ⊓ uCh611 T L V : Subgroup G) : Set G) := by
  set U := uCh611 T L V with hUdef
  set ZU := centerOf U with hZUdef
  set P := (V ⊓ U) ⊔ ZU with hPdef
  obtain ⟨-, hZZU, -, hZUc, hcen, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hvH := h.V_le_hCh611 hv
  have hv2 : v * v = 1 := by rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 v hv
  have hwH : x * v * x⁻¹ ∈ hCh611 T :=
    (hCh611 T).mul_mem ((hCh611 T).mul_mem hxH hvH) ((hCh611 T).inv_mem hxH)
  have hw2 : x * v * x⁻¹ * (x * v * x⁻¹) = 1 := by
    calc x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hxH) u).mp hu
  have hxU' : ∀ u ∈ U, x⁻¹ * u * x ∈ U := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (hCh611_le_normalizer_u T L V hxH)) u).mp hu
    simpa using this
  have hxZU : ∀ n ∈ ZU, x * n * x⁻¹ ∈ ZU := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_centerOf_ch615 T L V hxH) n).mp hn
  have hxP : ∀ e ∈ P, x * e * x⁻¹ ∈ P := fun e he => (Subgroup.mem_normalizer_iff.mp hxN e).mp he
  have hxP' : ∀ e ∈ P, x⁻¹ * e * x ∈ P := fun e he => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) e).mp he
    simpa using this
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hcommVU : ∀ u ∈ U, ⁅v, u⁆ ∈ V ⊓ U := fun u hu =>
    hVUc (Subgroup.commutator_mem_commutator hv hu)
  have hconjc : ∀ t : G, ⁅x * v * x⁻¹, t⁆ = x * ⁅v, x⁻¹ * t * x⁆ * x⁻¹ := fun t => by
    simp only [commutatorElement_def]; group
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨e₀, he₀, n, hn, hen⟩ := h.exists_mul_of_mem_sup_ch616 h331 h432 h512 h614 h615
      (hxP' e (Subgroup.mem_sup_left he))
    obtain ⟨a, ha, haz⟩ :=
      h.exists_comm_eq_U_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU e₀ he₀
    set m := x * ((⁅v, a⁆⁻¹ * e₀) * n) * x⁻¹ with hm
    have hmZU : m ∈ ZU := hxZU _ (ZU.mul_mem (hZZU haz) hn)
    have he' : e = ⁅x * v * x⁻¹, x * a * x⁻¹⁆ * m := by
      rw [hm]
      have e1 : e = x * (e₀ * n) * x⁻¹ := by rw [hen]; group
      rw [e1]
      simp only [commutatorElement_def]
      group
    have h1 : y * ⁅x * v * x⁻¹, x * a * x⁻¹⁆ = ⁅x * v * x⁻¹, x * a * x⁻¹⁆ * y := by
      rw [← commutatorElement_eq_one_iff_mul_comm, h.symm_ch616 h331 h432 h512 h614 h615 hwH hw2
        hy (hxU a ha), commutatorElement_def, hZUc _ hk _ (hxU a ha), mul_inv_cancel_right,
        mul_inv_cancel]
    have h2 : y * m = m * y := hZUc _ hmZU y hy
    rw [he']
    calc ⁅x * v * x⁻¹, x * a * x⁻¹⁆ * m * y = ⁅x * v * x⁻¹, x * a * x⁻¹⁆ * (y * m) := by
          rw [mul_assoc, h2]
      _ = (y * ⁅x * v * x⁻¹, x * a * x⁻¹⁆) * m := by rw [h1]; group
      _ = y * (⁅x * v * x⁻¹, x * a * x⁻¹⁆ * m) := by group
  · intro hc
    have hwU : ⁅x * v * x⁻¹, y⁆ ∈ U := by
      rw [hconjc]
      exact hxU _ (hcommVU _ (hxU' y hy)).2
    refine hcen _ hwU fun t ht => ?_
    rw [← commutatorElement_eq_one_iff_mul_comm, h.symm_ch616 h331 h432 h512 h614 h615 hwH hw2
      ht hy, commutatorElement_eq_one_iff_mul_comm]
    have htP : ⁅x * v * x⁻¹, t⁆ ∈ P := by
      rw [hconjc]
      exact hxP _ (Subgroup.mem_sup_left (hcommVU _ (hxU' t ht)))
    obtain ⟨e₀, he₀, n, hn, hen⟩ := h.exists_mul_of_mem_sup_ch616 h331 h432 h512 h614 h615 htP
    rw [← hen]
    have h1 : y * e₀ = e₀ * y := (Subgroup.mem_centralizer_iff.mp hc e₀ he₀).symm
    have h2 : y * n = n * y := hZUc n hn y hy
    calc y * (e₀ * n) = (y * e₀) * n := by group
      _ = e₀ * (y * n) := by rw [h1]; group
      _ = e₀ * n * y := by rw [h2]; group

theorem basis_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) :
    ∃ x₀ ∈ uCh611 T L V, ∃ y₀ ∈ uCh611 T L V, ⁅v, x₀⁆ ∉ centerOf (uCh611 T L V) ∧
      ∀ t ∈ uCh611 T L V, ⁅v, t⁆ ∈ centerOf (uCh611 T L V) ∨
        ⁅v, x₀⁻¹ * t⁆ ∈ centerOf (uCh611 T L V) ∨ ⁅v, y₀⁻¹ * t⁆ ∈ centerOf (uCh611 T L V) ∨
        ⁅v, (x₀ * y₀)⁻¹ * t⁆ ∈ centerOf (uCh611 T L V) := by
  classical
  set U := uCh611 T L V with hUdef
  set Z := zCh611 T with hZdef
  set ZU := centerOf U with hZUdef
  obtain ⟨hcomm, hZZU, -, -, -, -, hZ2⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hV := h.toHyp611.isElemAbelian
  have hVU8 : Nat.card ↥(V ⊓ U) = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  have hZVU : Z ≤ V ⊓ U := fun z hz =>
    ⟨((h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left) hz,
      (le_conjClosure (ch6ZS T L V) (hCh611 T)) (h.omega_le_ZS h331 h432 h512 h614 h615 hz)⟩
  have hVUab : ∀ a ∈ V ⊓ U, ∀ b ∈ V ⊓ U, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha.1 hb.1
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hmem : ∀ u ∈ U, ⁅v, u⁆ ∈ V ⊓ U := fun u hu =>
    hVUc (Subgroup.commutator_mem_commutator hv hu)
  have hmul : ∀ a ∈ U, ∀ b ∈ U, ⁅a, ⁅v, b⁆⁆ ∈ Z := fun a ha b hb => hcomm a ha _ (hmem b hb).2
  have hVZU : V ⊓ ZU = Z :=
    h.inf_centerOf_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have := normal_subgroupOf_ch616 (Z := Z) hVUab
  set ψ := commQuotHom_ch616 (A := U) v hZVU hVUab hmem hmul with hψdef
  have hψ := commQuotHom_apply_ch616 (A := U) v hZVU hVUab hmem hmul
  have hQ := card_quot_ch616 hZVU hZ2 hVU8
  have : Fintype (↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U)) := Fintype.ofFinite _
  have hQ2 : ∀ q : ↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U), q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H e =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have e1 : ((e * e : ↥(V ⊓ U)) : G) = 1 := by
        simp only [Subgroup.coe_mul]
        rw [← pow_two]
        exact hV.2 e e.2.1
      rw [e1]
      exact Z.one_mem
  have hsurj : ∀ q, ∃ a : ↥U, ψ a = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H e =>
      obtain ⟨a, ha, haz⟩ :=
        h.exists_comm_eq_U_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU e e.2
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [hψ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using haz
  have hone : ∀ s : ↥U, ψ s = 1 → ⁅v, (s : G)⁆ ∈ ZU := by
    intro s hs
    rw [hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hs
    exact hZZU hs
  obtain ⟨q₁, hq₁⟩ : ∃ q : ↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U), q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U))) ⊆ {1} := fun q _ => by
      simp [hcon q]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hQ, Finset.card_singleton] at this
    omega
  obtain ⟨q₂, hq₂1, hq₂2⟩ : ∃ q : ↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U), q ≠ 1 ∧ q ≠ q₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (↥(V ⊓ U) ⧸ Z.subgroupOf (V ⊓ U))) ⊆ {1, q₁} :=
      fun q _ => by
        by_cases hq : q = 1
        · simp [hq]
        · simp [hcon q hq]
    have h1 := Finset.card_le_card hsub
    have h2 : ({1, q₁} : Finset _).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hQ] at h1
    omega
  obtain ⟨x₀, hx₀⟩ := hsurj q₁
  obtain ⟨y₀, hy₀⟩ := hsurj q₂
  refine ⟨x₀, x₀.2, y₀, y₀.2, fun hk => hq₁ ?_, fun t ht => ?_⟩
  · have hkZ : ⁅v, (x₀ : G)⁆ ∈ Z := hVZU ▸ (⟨(hmem x₀ x₀.2).1, hk⟩ : ⁅v, (x₀ : G)⁆ ∈ V ⊓ ZU)
    rw [← hx₀, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hkZ
  · rcases eq_or_eq_of_card_four_ch616 hQ hQ2 hq₁ hq₂1 (Ne.symm hq₂2) (ψ ⟨t, ht⟩) with
      h0 | h0 | h0 | h0
    · exact Or.inl (hone _ h0)
    · right; left
      have := hone (x₀⁻¹ * ⟨t, ht⟩) (by rw [map_mul, map_inv, h0, hx₀, inv_mul_cancel])
      simpa using this
    · right; right; left
      have := hone (y₀⁻¹ * ⟨t, ht⟩) (by rw [map_mul, map_inv, h0, hy₀, inv_mul_cancel])
      simpa using this
    · right; right; right
      have := hone ((x₀ * y₀)⁻¹ * ⟨t, ht⟩)
        (by rw [map_mul, map_inv, map_mul, h0, hx₀, hy₀, inv_mul_cancel])
      simpa using this

theorem mem_centralizerMod_of_normalizer_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h512 : Stmt5_1_2) (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {x : G} (hxH : x ∈ hCh611 T)
    (hxN : x ∈ Subgroup.normalizer
      (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G)) :
    x ∈ centralizerMod (centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V))
      (hCh611 T) V := by
  set U := uCh611 T L V with hUdef
  set ZU := centerOf U with hZUdef
  set H := hCh611 T with hHdef
  obtain ⟨hcomm, hZZU, hZUU, hZUc, hcen, -, hZ2⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hHU : ∀ g ∈ H, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hg) u).mp hu
  have hHU' : ∀ g ∈ H, ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun g hg u hu => by
    have := hHU g⁻¹ (H.inv_mem hg) u hu
    simpa using this
  refine mem_centralizerMod.mpr ⟨hxH, mem_normalizer_centralizerMod_ch62
    (hCh611_le_normalizer_centerOf_ch615 T L V hxH) (Subgroup.le_normalizer hxH)
    (hCh611_le_normalizer_u T L V hxH), fun w hw => ?_⟩
  have hwH := h.V_le_hCh611 hw
  have hcH : x * w * x⁻¹ * w⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hxH hwH) (H.inv_mem hxH)) (H.inv_mem hwH)
  refine mem_centralizerMod.mpr ⟨hcH, hCh611_le_normalizer_centerOf_ch615 T L V hcH,
    fun u hu => ?_⟩
  by_cases hwU : w ∈ U
  · have hxw : x * w * x⁻¹ * w⁻¹ ∈ U := U.mul_mem (hHU x hxH w hwU) (U.inv_mem hwU)
    have := hZZU (hcomm _ hxw u hu)
    rwa [commutatorElement_def] at this
  · have hw2 : w * w = 1 := by rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 w hw
    have hw'H : x * w * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hwH) (H.inv_mem hxH)
    have hw'2 : x * w * x⁻¹ * (x * w * x⁻¹) = 1 := by
      calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
    have hN : ∀ t ∈ U, ⁅w, t⁆ ∈ U := fun t ht =>
      (hVUc (Subgroup.commutator_mem_commutator hw ht)).2
    have hN' : ∀ t ∈ U, ⁅x * w * x⁻¹, t⁆ ∈ U := fun t ht => by
      rw [commutatorElement_def]
      exact U.mul_mem (hHU _ hw'H t ht) (U.inv_mem ht)
    obtain ⟨x₀, hx₀, y₀, hy₀, hx₀Z, hdec⟩ :=
      h.basis_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hw hwU
    have key := mul_inv_mem_of_a2_ch616 hZ2 hZZU hZUU hZUc hcen hcomm hN hN'
      (fun a ha b hb => h.symm_ch616 h331 h432 h512 h614 h615 hwH hw2 ha hb)
      (fun a ha b hb => h.symm_ch616 h331 h432 h512 h614 h615 hw'H hw'2 ha hb)
      (fun a ha => h.alt_ch616 h331 h432 h512 h614 h615 hw ha)
      (fun a ha => by
        have e : ⁅a, ⁅x * w * x⁻¹, a⁆⁆ = x * ⁅x⁻¹ * a * x, ⁅w, x⁻¹ * a * x⁆⁆ * x⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e, h.alt_ch616 h331 h432 h512 h614 h615 hw (hHU' x hxH a ha), mul_one,
          mul_inv_cancel])
      (fun a ha => (h.ker_iff_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hw hwU
        ha).trans (h.ker_iff_conj_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hw hwU
          hxH hxN ha).symm)
      hx₀ hy₀ hx₀Z hdec
    have ht : w⁻¹ * u * w ∈ U := by
      have := hHU w⁻¹ (H.inv_mem hwH) u hu
      simpa using this
    have e : x * w * x⁻¹ * w⁻¹ * u * (x * w * x⁻¹ * w⁻¹)⁻¹ * u⁻¹ =
        ⁅x * w * x⁻¹, w⁻¹ * u * w⁆ * ⁅w, w⁻¹ * u * w⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact key _ ht

end Hyp6Sec2

end CFSG.Quasithin.H13
