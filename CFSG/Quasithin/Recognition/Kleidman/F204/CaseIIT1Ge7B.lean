module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropBA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom
open CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem alt5_klein_elems {V : Subgroup Alt5} (hV : Nat.card V = 4) {a b : Alt5} (ha : a ∈ V)
    (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {g : Alt5} (hg : g ∈ V) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨g1, ga, gb, gab⟩ := hcon
  have hbb : b * b = 1 := alt5_klein_sq hV hb
  have hab1 : a * b ≠ 1 := by
    intro h; apply hab
    calc a = a * (b * b) := by rw [hbb, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h, one_mul]
  have haba : a * b ≠ a := by
    intro h; apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h]; group
  have habb : a * b ≠ b := by
    intro h; apply ha1
    calc a = (a * b) * b⁻¹ := by group
      _ = 1 := by rw [h]; group
  set s : Finset Alt5 := {g, 1, a, b, a * b} with hsdef
  have hs : s.card = 5 := by
    rw [hsdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair habb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haba.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨g1, ga, gb, gab⟩
  have hsub : (s : Set Alt5) ⊆ (V : Set Alt5) := by
    intro x hx
    simp only [hsdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hg
    · exact V.one_mem
    · exact ha
    · exact hb
    · exact V.mul_mem ha hb
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hs, ← Nat.card_coe_set_eq] at h
  have : Nat.card (V : Set Alt5) = Nat.card V := rfl
  omega

section Local

variable (F : Frame L1 L2 S D X)
include F

theorem mem_sup_Qv_of_two {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) {t : G} (htx : t ∈ stab x) (htδ : t ∈ stab δ) {k : ℕ}
    (htk : t ^ 2 ^ k = 1) : t ∈ Qv x ⊔ Qv δ := by
  obtain ⟨hTδ, -, hTn⟩ := sylow_sup_Qv F hx hδ
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hUK : Subgroup.zpowers t ≤ stab x ⊓ stab δ := Subgroup.zpowers_le.mpr ⟨htx, htδ⟩
  have hpT : IsPGroup 2 ↥(Qv x ⊔ Qv δ) := hTδ.2.1
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ (Qv x ⊔ Qv δ)) :=
    IsPGroup.to_sup_of_normal_right' hp hpT (hUK.trans hTn)
  have hle : Subgroup.zpowers t ⊔ (Qv x ⊔ Qv δ) ≤ stab δ := sup_le (hUK.trans inf_le_right) hTδ.1
  have heq := F1.eq_of_isSylowTwoOf_le hTδ hle hsup le_sup_right
  rw [heq]
  exact le_sup_left (a := Subgroup.zpowers t) (Subgroup.mem_zpowers t)

theorem mem_Qv_of_fix_two {x δ δ' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) (hδ' : δ' ∈ nbrs x) (hne : δ' ≠ δ) {t : G} (htx : t ∈ stab x)
    (htδ : t ∈ stab δ) (htδ' : t ∈ stab δ') {k : ℕ} (htk : t ^ 2 ^ k = 1) : t ∈ Qv x := by
  have hA := Amal.of_frame F
  have hQn : Qv δ ≤ Subgroup.normalizer (Qv x : Set G) :=
    (hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ)).trans (le_normalizer_pCoreOf 2 (stab x))
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQn).mp (mem_sup_Qv_of_two F hx hδ htx htδ htk)
  have haδ' : a ∈ stab δ' := hA.Qv_le_stab_of_mem_nbrs hδ' ha
  have hbδ' : b ∈ stab δ' := by
    have := (stab δ').mul_mem ((stab δ').inv_mem haδ') htδ'
    rwa [inv_mul_cancel_left] at this
  have hbx : b ∈ stab x := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ) hb
  set bb : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨b, (mem_stab.mp hbx).1⟩ with hbb
  have hfix := vertex_hfree F hx hδ bb hb δ' hδ' hne (smul_eq_of_mem_stab (g := bb) hbδ')
  have hbQ : b ∈ Qv x := by
    rw [← ballStab_one_true F hx]
    unfold ballStab
    refine Subgroup.mem_iInf.mpr fun ν => Subgroup.mem_iInf.mpr fun hν => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hν with h0 | h1
    · rw [← (dist_eq_zero_iff (Amal.of_frame F).amalgam.gen).mp h0]
      exact hbx
    · exact mem_stab_of_smul_eq (g := bb) (hfix ν (dist_eq_one_iff_adj.mp h1))
  exact (Qv x).mul_mem ha hbQ

theorem comm_mem_Qv_of_mem_nbrs {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) {q t : G} (hq : q ∈ Qv δ) (ht : t ∈ Qv δ) :
    q * t * q⁻¹ * t⁻¹ ∈ Qv x := by
  have hA := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hT := card_map_Qv_nbr F hx hδ hφs hφk
  set T := ((Qv δ).subgroupOf (stab x)).map φ with hTdef
  have hQδx : Qv δ ≤ stab x := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ)
  have hq' : φ ⟨q, hQδx hq⟩ ∈ T := ⟨⟨q, hQδx hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have ht' : φ ⟨t, hQδx ht⟩ ∈ T := ⟨⟨t, hQδx ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hsq := fun {k : Alt5} (hk : k ∈ T) => alt5_klein_sq hT hk
  have h1 := hsq hq'
  have h2 := hsq ht'
  have h3 := hsq (T.mul_mem hq' ht')
  set a := φ ⟨q, hQδx hq⟩
  set b := φ ⟨t, hQδx ht⟩
  have hab : a * b * a⁻¹ * b⁻¹ = 1 := by
    have ha : a⁻¹ = a := by
      calc a⁻¹ = a⁻¹ * (a * a) := by rw [h1]; group
        _ = a := by group
    have hb : b⁻¹ = b := by
      calc b⁻¹ = b⁻¹ * (b * b) := by rw [h2]; group
        _ = b := by group
    rw [ha, hb]
    calc a * b * a * b = (a * b) * (a * b) := by group
      _ = 1 := h3
  have : φ (⟨q, hQδx hq⟩ * ⟨t, hQδx ht⟩ * ⟨q, hQδx hq⟩⁻¹ * ⟨t, hQδx ht⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]; exact hab
  have hk := MonoidHom.mem_ker.mpr this
  rw [hφk, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem mem_Qv_of_four {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) {a b : G} (ha : a ∈ Qv δ) (hb : b ∈ Qv δ) (haQ : a ∉ Qv x)
    (hbQ : b ∉ Qv x) (habQ : a⁻¹ * b ∉ Qv x) {q : G} (hq : q ∈ Qv δ) :
    q ∈ Qv x ∨ a⁻¹ * q ∈ Qv x ∨ b⁻¹ * q ∈ Qv x ∨ (a * b)⁻¹ * q ∈ Qv x := by
  have hA := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hT := card_map_Qv_nbr F hx hδ hφs hφk
  have hQδx : Qv δ ≤ stab x := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ)
  have hker : ∀ g : ↥(stab x), φ g = 1 ↔ (g : G) ∈ Qv x := by
    intro g
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hmem : ∀ {g : ↥(stab x)}, (g : G) ∈ Qv δ → φ g ∈ ((Qv δ).subgroupOf (stab x)).map φ :=
    fun {g} hg => ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  set ga : ↥(stab x) := ⟨a, hQδx ha⟩
  set gb : ↥(stab x) := ⟨b, hQδx hb⟩
  set gq : ↥(stab x) := ⟨q, hQδx hq⟩
  have h1 : φ ga ≠ 1 := fun h => haQ ((hker ga).mp h)
  have h2 : φ gb ≠ 1 := fun h => hbQ ((hker gb).mp h)
  have h3 : φ ga ≠ φ gb := by
    intro h
    apply habQ
    have : φ (ga⁻¹ * gb) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (hker _).mp this
  rcases alt5_klein_elems hT (hmem (g := ga) ha) (hmem (g := gb) hb) h1 h2 h3
    (hmem (g := gq) hq) with e | e | e | e
  · exact Or.inl ((hker gq).mp e)
  · refine Or.inr (Or.inl ((hker (ga⁻¹ * gq)).mp ?_))
    rw [map_mul, map_inv, e, inv_mul_cancel]
  · refine Or.inr (Or.inr (Or.inl ((hker (gb⁻¹ * gq)).mp ?_)))
    rw [map_mul, map_inv, e, inv_mul_cancel]
  · refine Or.inr (Or.inr (Or.inr ((hker ((ga * gb)⁻¹ * gq)).mp ?_)))
    rw [map_mul, map_inv, map_mul, e, inv_mul_cancel]

theorem card_Zv_eq_of_vtype_false {d d' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hd : vtype d = false)
    (hd' : vtype d' = false) : Nat.card (Zv d) = Nat.card (Zv d') := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hd
  obtain ⟨g', rfl⟩ := exists_smul_eq_γ₀ hd'
  rw [Zv_smul, Zv_smul]
  unfold conjSub
  rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
    Subgroup.card_map_of_injective (MulAut.conj (g' : G)).injective]

end Local

end CFSG.Quasithin.Kleidman.F204
