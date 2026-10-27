module

public import CFSG.Quasithin.Recognition.F112Crit.OddThree

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

theorem eq_one_or_eq_of_mem_zpowers {c g : G} (hc : orderOf c = 2)
    (hg : g ∈ Subgroup.zpowers c) : g = 1 ∨ g = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have e : c ^ k = c ^ (k % 2) := by rw [← zpow_mod_orderOf, hc]; norm_num
  rw [e]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem comm_inv_mul_inv_mul {x₁ x₂ x₃ c : G} (h21 : x₂ * x₁ * x₂⁻¹ = c * x₁)
    (h23 : x₂ * x₃ * x₂⁻¹ = c * x₃) (h13 : x₁ * x₃ * x₁⁻¹ = c * x₃) (hc : c * x₁ = x₁ * c) :
    (x₁⁻¹ * x₂) * (x₁⁻¹ * x₃) * (x₁⁻¹ * x₂)⁻¹ * (x₁⁻¹ * x₃)⁻¹ = c⁻¹ := by
  have hci : c⁻¹ * x₁ = x₁ * c⁻¹ := (show Commute c x₁ from hc).inv_left.eq
  calc (x₁⁻¹ * x₂) * (x₁⁻¹ * x₃) * (x₁⁻¹ * x₂)⁻¹ * (x₁⁻¹ * x₃)⁻¹
      = x₁⁻¹ * (x₂ * x₁ * x₂⁻¹)⁻¹ * (x₂ * x₃ * x₂⁻¹) * (x₁ * x₃ * x₁⁻¹)⁻¹ * x₁ * x₁ := by group
    _ = x₁⁻¹ * (c * x₁)⁻¹ * (c * x₃) * (c * x₃)⁻¹ * x₁ * x₁ := by rw [h21, h23, h13]
    _ = x₁⁻¹ * x₁⁻¹ * (c⁻¹ * x₁) * x₁ := by group
    _ = x₁⁻¹ * x₁⁻¹ * (x₁ * c⁻¹) * x₁ := by rw [hci]
    _ = x₁⁻¹ * (c⁻¹ * x₁) := by group
    _ = x₁⁻¹ * (x₁ * c⁻¹) := by rw [hci]
    _ = c⁻¹ := by group

theorem comm_mem_of_mem_iSup {ι : Sort*} {V : ι → Subgroup G} {S C : Subgroup G}
    (hVS : ∀ i, V i ≤ S) (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (h : ∀ i j, ∀ v ∈ V i, ∀ w ∈ V j, v * w * v⁻¹ * w⁻¹ ∈ C) {g k : G}
    (hg : g ∈ ⨆ i, V i) (hk : k ∈ ⨆ i, V i) : g * k * g⁻¹ * k⁻¹ ∈ C := by
  have h1 : ∀ i, ∀ v ∈ V i, ∀ k ∈ ⨆ i, V i, v * k * v⁻¹ * k⁻¹ ∈ C := by
    intro i v hv k hk
    have := Subgroup.iSup_induction V (C := fun k => k ∈ S ∧ v * k * v⁻¹ * k⁻¹ ∈ C) hk
      (fun j w hw => ⟨hVS j hw, h i j v hv w hw⟩) ⟨S.one_mem, by simp⟩
      (fun k₁ k₂ hk₁ hk₂ => by
        refine ⟨S.mul_mem hk₁.1 hk₂.1, ?_⟩
        have e : v * (k₁ * k₂) * v⁻¹ * (k₁ * k₂)⁻¹ =
            (v * k₁ * v⁻¹ * k₁⁻¹) * (k₁ * (v * k₂ * v⁻¹ * k₂⁻¹) * k₁⁻¹) := by group
        rw [e]
        exact C.mul_mem hk₁.2 (ConjAut.conj_mem _ (hSC hk₁.1) hk₂.2))
    exact this.2
  have := Subgroup.iSup_induction V (C := fun g => g ∈ S ∧ g * k * g⁻¹ * k⁻¹ ∈ C) hg
    (fun i v hv => ⟨hVS i hv, h1 i v hv k hk⟩) ⟨S.one_mem, by simp⟩
    (fun g₁ g₂ hg₁ hg₂ => by
      refine ⟨S.mul_mem hg₁.1 hg₂.1, ?_⟩
      have e : (g₁ * g₂) * k * (g₁ * g₂)⁻¹ * k⁻¹ =
          (g₁ * (g₂ * k * g₂⁻¹ * k⁻¹) * g₁⁻¹) * (g₁ * k * g₁⁻¹ * k⁻¹) := by group
      rw [e]
      exact C.mul_mem (ConjAut.conj_mem _ (hSC hg₁.1) hg₂.2) hg₁.2)
  exact this.2

theorem exists_three_eq_of_two_mul_lt {α β : Type*} [Fintype β] {E : Set α} (f : α → β)
    (h : 2 * Fintype.card β < Nat.card E) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by
  classical
  have hfin : Finite E := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [Nat.card_eq_zero_of_infinite] at h
    omega
  have : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (fun x : E => f x) (n := 2)
    (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact ⟨a, a.2, b, b.2, c, c.2, fun e => hab (Subtype.ext e), fun e => hac (Subtype.ext e),
    fun e => hbc (Subtype.ext e), ha.trans hb.symm, ha.trans hc.symm⟩

theorem exists_mem_not_mem_of_card_lt {α : Type*} {s : Set α} (t : Finset α)
    (h : t.card < Nat.card s) : ∃ x ∈ s, x ∉ t := by
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ (t : Set α) := fun x hx => Finset.mem_coe.mpr (hcon x hx)
  have := Set.ncard_le_ncard hsub t.finite_toSet
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  omega

variable [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

theorem card_Vv_eq_of_vtype (hc : CritAmalgam G₀ G₁ G₂ T Z) {ε : CosetGeom G₀ G₁ G₂}
    (hε : vtype ε = true) : Nat.card (Vv Z ε) = Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hε
  rw [CosetGeom.Vv_smul hc.normalizes, IsLocalReg.card_conjSub_eq]

theorem Vv_le_ballStab_self (hc : CritAmalgam G₀ G₁ G₂ T Z) {ε : CosetGeom G₀ G₁ G₂}
    (hε : vtype ε = true) : Vv Z ε ≤ ballStab 1 ε := fun v hv => by
  have h2 := lemma63_2' hc hε
  haveI : IsMulCommutative ↥(Vv Z ε) := h2.1.1
  refine mem_ballStab_of_centralizes hc hε ((pCoreOf_le 2 _) (h2.2.1 hv)) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact setLike_mul_comm hw hv

theorem not_mem_ballStab_of_four (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {μ ε ε' : CosetGeom G₀ G₁ G₂}
    (hμ : vtype μ = false) (hε : ε ∈ nbrs μ) (hε' : ε' ∈ nbrs μ) (hne : ε ≠ ε')
    (h4 : Nat.card (Vv Z ε) = 4) (h2 : Nat.card (Vv Z μ) = 2) {v : G} (hv : v ∈ Vv Z ε)
    (hvZ : v ∉ Vv Z μ) : v ∉ ballStab 1 ε' := by
  intro hvB
  have hεt : vtype ε = true := vtype_eq_true_of_mem_nbrs hμ hε
  have hε't : vtype ε' = true := vtype_eq_true_of_mem_nbrs hμ hε'
  have hZε : Vv Z μ ≤ Vv Z ε := Vv_le_Vv_of_mem_nbrs hεt (CosetGeom.mem_nbrs_symm hε)
  have hZB : Vv Z μ ≤ ballStab 1 ε' :=
    (Vv_le_Vv_of_mem_nbrs hε't (CosetGeom.mem_nbrs_symm hε')).trans (Vv_le_ballStab_self hc hε't)
  have hKle : Vv Z ε ⊓ ballStab 1 ε' ≤ Vv Z ε := inf_le_left
  have hZK : Vv Z μ ≤ Vv Z ε ⊓ ballStab 1 ε' := le_inf hZε hZB
  have hKne : Vv Z ε ⊓ ballStab 1 ε' ≠ Vv Z ε := fun h =>
    not_Vv_le_ballStab_of_three hc hb hL hμ hε hε' hne (by rw [← h]; exact inf_le_right)
  have hdvd : Nat.card ↥(Vv Z ε ⊓ ballStab 1 ε') ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hKle
  have hK4 : Nat.card ↥(Vv Z ε ⊓ ballStab 1 ε') ≠ 4 := fun h =>
    hKne (Subgroup.eq_of_le_of_card_ge hKle (by rw [h4, h]))
  have hK2 : Nat.card ↥(Vv Z ε ⊓ ballStab 1 ε') ≤ 2 := by
    by_contra hlt
    exact hK4 (Nat.eq_of_dvd_of_lt_two_mul (by norm_num) hdvd (by omega)).symm
  have hZeq : Vv Z μ = Vv Z ε ⊓ ballStab 1 ε' :=
    Subgroup.eq_of_le_of_card_ge hZK (by rw [h2]; exact hK2)
  exact hvZ (hZeq ▸ ⟨hv, hvB⟩)

theorem mem_ballStab_mul_iff (hG : G₀ = G₁ ⊔ G₂) {θ μ : CosetGeom G₀ G₁ G₂} {X : Subgroup G}
    (hX : IsLocalReg θ 3 X) (hμ : μ ∈ nbrs θ) {g h : G} (hg : g ∈ stab θ ⊓ stab μ)
    (hh : h ∈ stab θ ⊓ stab μ) :
    g * h ∈ ballStab 1 θ ↔ (g ∈ ballStab 1 θ ↔ h ∈ ballStab 1 θ) := by
  have hsq : ∀ s ∈ stab θ ⊓ stab μ, s * s ∈ ballStab 1 θ := fun s hs => by
    have := hX.pow_pred_mem hG hμ hs
    simpa [pow_two] using this
  by_cases hgB : g ∈ ballStab 1 θ <;> by_cases hhB : h ∈ ballStab 1 θ
  · exact iff_of_true ((ballStab 1 θ).mul_mem hgB hhB) (iff_of_true hgB hhB)
  · refine iff_of_false (fun hgh => hhB ?_) (fun e => hhB (e.mp hgB))
    have e : h = g⁻¹ * (g * h) := by group
    rw [e]
    exact (ballStab 1 θ).mul_mem ((ballStab 1 θ).inv_mem hgB) hgh
  · refine iff_of_false (fun hgh => hgB ?_) (fun e => hgB (e.mpr hhB))
    have e : g = (g * h) * h⁻¹ := by group
    rw [e]
    exact (ballStab 1 θ).mul_mem hgh ((ballStab 1 θ).inv_mem hhB)
  · exact iff_of_true (hX.mul_mem_ker hG hμ hg hh (hsq g hg) (hsq h hh) hgB hhB)
      (iff_of_false hgB hhB)

theorem conj_mem_ballStab_iff (a : ↥G₀) (θ : CosetGeom G₀ G₁ G₂) (g : G) :
    (a : G) * g * (a : G)⁻¹ ∈ ballStab 1 θ ↔ g ∈ ballStab 1 (a⁻¹ • θ) := by
  rw [CosetGeom.ballStab_smul, mem_conjSub]
  simp

theorem conj_eq_of_four (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) 3 X₀) (h4 : Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) = 4)
    {μ ε ε' : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) (hε : ε ∈ nbrs μ) (hε' : ε' ∈ nbrs μ)
    (hne : ε ≠ ε') {c : G} (hZ : Vv Z μ = Subgroup.zpowers c) (hco : orderOf c = 2)
    {v v' : G} (hv : v ∈ Vv Z ε) (hvZ : v ∉ Vv Z μ) (hv' : v' ∈ Vv Z ε')
    (hv'Z : v' ∉ Vv Z μ) : v * v' * v⁻¹ = c * v' := by
  have hG := hc.amalgam.gen
  have hεt : vtype ε = true := vtype_eq_true_of_mem_nbrs hμ hε
  have hε't : vtype ε' = true := vtype_eq_true_of_mem_nbrs hμ hε'
  have h2 : Nat.card (Vv Z μ) = 2 := by rw [hZ, Nat.card_zpowers, hco]
  have h4ε : Nat.card (Vv Z ε) = 4 := (card_Vv_eq_of_vtype hc hεt).trans h4
  have h4ε' : Nat.card (Vv Z ε') = 4 := (card_Vv_eq_of_vtype hc hε't).trans h4
  have hvst := Vv_le_stab_inf_of_three hc hb hμ hε hε' hv
  have hyV : v * v' * v⁻¹ ∈ Vv Z ε' :=
    ConjAut.conj_mem _ ((lemma63_2' hc hε't).2.2.2.2 hvst.1) hv'
  have hcomm : ∀ y ∈ Vv Z μ, v * y = y * v := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp (stab_le_centralizer_Vv hc hμ hvst.2)) y hy).symm
  have hyZ : v * v' * v⁻¹ ∉ Vv Z μ := fun hy => hv'Z (by
    have e : v' = v * v' * v⁻¹ :=
      calc v' = v⁻¹ * ((v * v' * v⁻¹) * v) := by group
        _ = v⁻¹ * (v * (v * v' * v⁻¹)) := by rw [hcomm _ hy]
        _ = v * v' * v⁻¹ := by group
    rw [e]
    exact hy)
  obtain ⟨Xε, hXε⟩ := exists_isLocalReg_of_vtype hbase hεt
  have hμε : μ ∈ nbrs ε := CosetGeom.mem_nbrs_symm hε
  have hv'st := Vv_le_stab_inf_of_three hc hb hμ hε' hε hv'
  have hyst := Vv_le_stab_inf_of_three hc hb hμ hε' hε hyV
  have hel := (lemma63_2' hc hε't).1
  have hsq : ∀ y ∈ Vv Z ε', y * y = 1 := fun y hy => by rw [← pow_two]; exact hel.2 y hy
  have hyv' : v * v' * v⁻¹ * v' ∈ ballStab 1 ε :=
    hXε.mul_mem_ker hG hμε hyst hv'st
      (by rw [hsq _ hyV]; exact (ballStab 1 ε).one_mem)
      (by rw [hsq _ hv']; exact (ballStab 1 ε).one_mem)
      (not_mem_ballStab_of_four hc hb hL hμ hε' hε hne.symm h4ε' h2 hyV hyZ)
      (not_mem_ballStab_of_four hc hb hL hμ hε' hε hne.symm h4ε' h2 hv' hv'Z)
  have hyv'Z : v * v' * v⁻¹ * v' ∈ Vv Z μ := by
    by_contra hn
    exact not_mem_ballStab_of_four hc hb hL hμ hε' hε hne.symm h4ε' h2
      ((Vv Z ε').mul_mem hyV hv') hn hyv'
  have hv'i : v'⁻¹ = v' := inv_eq_of_mul_eq_one_left (hsq v' hv')
  have hne1 : v * v' * v⁻¹ * v' ≠ 1 := by
    intro h1
    apply mul_ne_mul_of_three hc hb hbase hμ hε hε' hv
      (not_mem_ballStab_of_four hc hb hL hμ hε hε' hne h4ε h2 hv hvZ) hv'
      (not_mem_ballStab_of_four hc hb hL hμ hε' hε hne.symm h4ε' h2 hv' hv'Z)
    calc v * v' = (v * v' * v⁻¹ * v') * v'⁻¹ * v := by group
      _ = v' * v := by rw [h1, one_mul, hv'i]
  rcases eq_one_or_eq_of_mem_zpowers hco
      (show v * v' * v⁻¹ * v' ∈ Subgroup.zpowers c from hZ ▸ hyv'Z) with h | h
  · exact absurd h hne1
  · calc v * v' * v⁻¹ = (v * v' * v⁻¹ * v') * v'⁻¹ := by group
      _ = c * v' := by rw [h, hv'i]

theorem comm_mem_of_mem_Wv (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) 3 X₀) (h4 : Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) = 4)
    {μ : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) {g k : G} (hg : g ∈ Wv Z μ)
    (hk : k ∈ Wv Z μ) : g * k * g⁻¹ * k⁻¹ ∈ Vv Z μ := by
  obtain ⟨-, hz, -⟩ := corollary77 hc (by rw [hb]; decide) hbase
  obtain ⟨c, hZ, hco, -⟩ := hz μ hμ
  have hW : Wv Z μ = ⨆ x : {δ // δ ∈ nbrs μ}, Vv Z x.1 := by
    unfold Wv
    exact iSup_subtype'
  rw [hW] at hg hk
  have hcent : stab μ ≤ Subgroup.centralizer (Vv Z μ : Set G) := stab_le_centralizer_Vv hc hμ
  refine comm_mem_of_mem_iSup (S := stab μ)
    (fun x => (Vv_le_ballStab_of_three hc hb hμ x.2).trans (CosetGeom.ballStab_le_stab 1 μ))
    (hcent.trans (Subgroup.centralizer_le_normalizer _)) ?_ hg hk
  rintro ⟨ε, hε⟩ ⟨ε', hε'⟩ v hv v' hv'
  have hcomm1 : ∀ {a b : G}, a * b = b * a → a * b * a⁻¹ * b⁻¹ ∈ Vv Z μ := fun e => by
    rw [e, mul_inv_cancel_right, mul_inv_cancel]
    exact (Vv Z μ).one_mem
  have hvμ : v ∈ stab μ := CosetGeom.ballStab_le_stab 1 μ (Vv_le_ballStab_of_three hc hb hμ hε hv)
  have hv'μ : v' ∈ stab μ :=
    CosetGeom.ballStab_le_stab 1 μ (Vv_le_ballStab_of_three hc hb hμ hε' hv')
  by_cases hee : ε = ε'
  · subst hee
    haveI : IsMulCommutative ↥(Vv Z ε) :=
      (lemma63_2' hc (vtype_eq_true_of_mem_nbrs hμ hε)).1.1
    exact hcomm1 (setLike_mul_comm hv hv')
  · by_cases hvZ : v ∈ Vv Z μ
    · exact hcomm1 (Subgroup.mem_centralizer_iff.mp (hcent hv'μ) v hvZ)
    · by_cases hv'Z : v' ∈ Vv Z μ
      · exact hcomm1 (Subgroup.mem_centralizer_iff.mp (hcent hvμ) v' hv'Z).symm
      · rw [conj_eq_of_four hc hb hL hbase h4 hμ hε hε' hee hZ hco hv hvZ hv' hv'Z,
          mul_inv_cancel_right, hZ]
        exact Subgroup.mem_zpowers c

theorem fix_or_fix_or_fix (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) 3 X₀) (h4 : Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) = 4)
    (hN : 10 ≤ Nat.card (nbrs (γ₀ G₀ G₁ G₂))) {δ μ₁ μ₂ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) (hμ₁ : μ₁ ∈ nbrs δ) (hμ₂ : μ₂ ∈ nbrs δ) (hne : μ₁ ≠ μ₂) {a a' : ↥G₀}
    (ha : (a : G) ∈ Wv Z μ₂ ⊓ ballStab 1 δ) (ha' : (a' : G) ∈ Wv Z μ₂ ⊓ ballStab 1 δ)
    {η : CosetGeom G₀ G₁ G₂} (hη : η ∈ nbrs μ₁) (hηδ : η ≠ δ) :
    a • η = η ∨ a' • η = η ∨ (a' * a) • η = η := by
  classical
  have hG := hc.amalgam.gen
  have hμ₁t : vtype μ₁ = false := vtype_eq_false_of_mem_nbrs hδ hμ₁
  have hμ₂t : vtype μ₂ = false := vtype_eq_false_of_mem_nbrs hδ hμ₂
  have hδμ₁ : δ ∈ nbrs μ₁ := CosetGeom.mem_nbrs_symm hμ₁
  obtain ⟨-, hz, -⟩ := corollary77 hc (by rw [hb]; decide) hbase
  obtain ⟨c₁, hZ₁, hco₁, -⟩ := hz μ₁ hμ₁t
  obtain ⟨c₂, hZ₂, hco₂, -⟩ := hz μ₂ hμ₂t
  have h2₁ : Nat.card (Vv Z μ₁) = 2 := by rw [hZ₁, Nat.card_zpowers, hco₁]
  have h4' : ∀ {ε : CosetGeom G₀ G₁ G₂}, vtype ε = true → Nat.card (Vv Z ε) = 4 := fun hε =>
    (card_Vv_eq_of_vtype hc hε).trans h4
  have hN₁ : 10 ≤ Nat.card (nbrs μ₁) := by rw [card_nbrs_eq hc hμ₁t]; exact hN
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hdμ₁ : CosetGeom.dist δ μ₁ ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr hμ₁).le
  have hdμ₂ : CosetGeom.dist δ μ₂ ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr hμ₂).le
  have haμ₁ : (a : G) ∈ stab μ₁ := CosetGeom.ballStab_le_stab_of_dist_le hdμ₁ ha.2
  have ha'μ₁ : (a' : G) ∈ stab μ₁ := CosetGeom.ballStab_le_stab_of_dist_le hdμ₁ ha'.2
  have hnbr : ∀ {g : ↥G₀}, (g : G) ∈ stab μ₁ → ∀ {θ}, θ ∈ nbrs μ₁ → g⁻¹ • θ ∈ nbrs μ₁ :=
    fun hg _ hθ => IsLocalReg.smul_mem_nbrs hθ (by simpa using (stab μ₁).inv_mem hg)
  have hpar : ∀ θ ∈ nbrs μ₁, ∀ g ∈ ballStab 1 μ₁, ∀ h ∈ ballStab 1 μ₁,
      (g * h ∈ ballStab 1 θ ↔ (g ∈ ballStab 1 θ ↔ h ∈ ballStab 1 θ)) := by
    intro θ hθ g hg h hh
    obtain ⟨Xθ, hXθ⟩ := exists_isLocalReg_of_vtype hbase (vtype_eq_true_of_mem_nbrs hμ₁t hθ)
    have hsub : ballStab 1 μ₁ ≤ stab θ ⊓ stab μ₁ :=
      le_inf (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hθ).le)
        (CosetGeom.ballStab_le_stab 1 μ₁)
    exact mem_ballStab_mul_iff hG hXθ (CosetGeom.mem_nbrs_symm hθ) (hsub hg) (hsub hh)
  have hpx : ∀ ε ∈ nbrs μ₁, ∀ x ∈ Vv Z ε, x ∉ Vv Z μ₁ → ∀ θ ∈ nbrs μ₁,
      (x ∈ ballStab 1 θ ↔ θ = ε) := by
    intro ε hε x hx hxZ θ hθ
    constructor
    · intro hxB
      by_contra hθε
      exact not_mem_ballStab_of_four hc hb hL hμ₁t hε hθ (Ne.symm hθε)
        (h4' (vtype_eq_true_of_mem_nbrs hμ₁t hε)) h2₁ hx hxZ hxB
    · rintro rfl
      exact Vv_le_ballStab_self hc (vtype_eq_true_of_mem_nbrs hμ₁t hθ) hx
  have hexV : ∀ ε ∈ nbrs μ₁, ∃ x ∈ Vv Z ε, x ∉ Vv Z μ₁ := fun ε hε =>
    SetLike.not_le_iff_exists.mp fun hle => by
      have := Subgroup.card_le_of_le hle
      rw [h4' (vtype_eq_true_of_mem_nbrs hμ₁t hε), h2₁] at this
      omega
  have hWB : Wv Z μ₁ ≤ ballStab 1 μ₁ := iSup₂_le fun ε hε => Vv_le_ballStab_of_three hc hb hμ₁t hε
  obtain ⟨η', hη', hη'S⟩ := exists_mem_not_mem_of_card_lt (s := nbrs μ₁)
    [δ, η, a⁻¹ • η, a'⁻¹ • η, (a' * a)⁻¹ • η].toFinset
    ((List.toFinset_card_le _).trans_lt (by simp only [List.length_cons, List.length_nil]; omega))
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hη'S
  obtain ⟨hη'δ, hη'η, hη'1, hη'2, hη'3⟩ := hη'S
  obtain ⟨x, hx, hxZ⟩ := hexV η hη
  obtain ⟨x', hx', hx'Z⟩ := hexV η' hη'
  have hxB : x ∈ ballStab 1 μ₁ := Vv_le_ballStab_of_three hc hb hμ₁t hη hx
  have hx'B : x' ∈ ballStab 1 μ₁ := Vv_le_ballStab_of_three hc hb hμ₁t hη' hx'
  obtain ⟨w, hwdef⟩ : ∃ w, x * x' = w := ⟨_, rfl⟩
  have hwW : w ∈ Wv Z μ₁ := hwdef ▸ (Wv Z μ₁).mul_mem (Vv_le_Wv hη hx) (Vv_le_Wv hη' hx')
  have hwB : w ∈ ballStab 1 μ₁ := hWB hwW
  have hw : ∀ θ ∈ nbrs μ₁, (w ∈ ballStab 1 θ ↔ (θ = η ↔ θ = η')) := fun θ hθ => by
    rw [← hwdef, hpar θ hθ x hxB x' hx'B, hpx η hη x hx hxZ θ hθ, hpx η' hη' x' hx' hx'Z θ hθ]
  have hwδ : w ∈ ballStab 1 δ := (hw δ hδμ₁).mpr (iff_of_false hηδ.symm (Ne.symm hη'δ))
  have hconjB : ∀ {g : ↥G₀}, (g : G) ∈ stab μ₁ → ∀ {y : G}, y ∈ ballStab 1 μ₁ →
      (g : G) * y⁻¹ * (g : G)⁻¹ ∈ ballStab 1 μ₁ := fun hg _ hy =>
    ConjAut.conj_mem _ (CosetGeom.le_normalizer_ballStab 1 μ₁ hg) ((ballStab 1 μ₁).inv_mem hy)
  have hstep : ∀ {g : ↥G₀}, (g : G) ∈ stab μ₁ → ∀ {y : G}, y ∈ ballStab 1 μ₁ → ∀ θ ∈ nbrs μ₁,
      (y * ((g : G) * y⁻¹ * (g : G)⁻¹) ∈ ballStab 1 θ ↔
        (y ∈ ballStab 1 θ ↔ y ∈ ballStab 1 (g⁻¹ • θ))) := fun hg _ hy θ hθ => by
    rw [hpar θ hθ _ hy _ (hconjB hg hy), conj_mem_ballStab_iff, Subgroup.inv_mem_iff]
  obtain ⟨u, hudef⟩ : ∃ u, w * ((a : G) * w⁻¹ * (a : G)⁻¹) = u := ⟨_, rfl⟩
  have huB : u ∈ ballStab 1 μ₁ := hudef ▸ (ballStab 1 μ₁).mul_mem hwB (hconjB haμ₁ hwB)
  have hu : ∀ θ ∈ nbrs μ₁, (u ∈ ballStab 1 θ ↔
      (w ∈ ballStab 1 θ ↔ w ∈ ballStab 1 (a⁻¹ • θ))) := fun θ hθ => by
    rw [← hudef]
    exact hstep haμ₁ hwB θ hθ
  obtain ⟨v, hvdef⟩ : ∃ v, u * ((a' : G) * u⁻¹ * (a' : G)⁻¹) = v := ⟨_, rfl⟩
  have hv : ∀ θ ∈ nbrs μ₁, (v ∈ ballStab 1 θ ↔
      (u ∈ ballStab 1 θ ↔ u ∈ ballStab 1 (a'⁻¹ • θ))) := fun θ hθ => by
    rw [← hvdef]
    exact hstep ha'μ₁ huB θ hθ
  have hwμ₂ : w ∈ stab μ₂ := CosetGeom.ballStab_le_stab_of_dist_le hdμ₂ hwδ
  have huW : u ∈ Wv Z μ₂ := by
    have e : w * ((a : G) * w⁻¹ * (a : G)⁻¹) = (w * (a : G) * w⁻¹) * (a : G)⁻¹ := by group
    rw [← hudef, e]
    exact (Wv Z μ₂).mul_mem (ConjAut.conj_mem _ (stab_le_normalizer_Wv hc μ₂ hwμ₂) ha.1)
      ((Wv Z μ₂).inv_mem ha.1)
  have hvZ : v ∈ Vv Z μ₂ := by
    have := comm_mem_of_mem_Wv hc hb hL hbase h4 hμ₂t huW ha'.1
    rw [← hvdef]
    simpa only [mul_assoc] using this
  have hfix : ∀ (g : ↥G₀), g⁻¹ • η = η → g • η = η := by
    intro g e
    calc g • η = g • (g⁻¹ • η) := by rw [e]
      _ = η := smul_inv_smul g η
  have hi1 : a⁻¹ • η ≠ η := fun e => h1 (hfix a e)
  have hi2 : a'⁻¹ • η ≠ η := fun e => h2 (hfix a' e)
  have e3 : (a' * a)⁻¹ • η = a⁻¹ • (a'⁻¹ • η) := by rw [mul_inv_rev, mul_smul]
  have hi3 : a⁻¹ • (a'⁻¹ • η) ≠ η := fun e => h3 (hfix (a' * a) (e3.trans e))
  have hηa : a⁻¹ • η ∈ nbrs μ₁ := hnbr haμ₁ hη
  have hηa' : a'⁻¹ • η ∈ nbrs μ₁ := hnbr ha'μ₁ hη
  have hηaa' : a⁻¹ • (a'⁻¹ • η) ∈ nbrs μ₁ := hnbr haμ₁ hηa'
  have hwη : w ∉ ballStab 1 η := by
    rw [hw η hη]
    exact fun e => hη'η (e.mp rfl).symm
  have hwa : w ∈ ballStab 1 (a⁻¹ • η) := (hw _ hηa).mpr (iff_of_false hi1 fun e => hη'1 e.symm)
  have hwa' : w ∈ ballStab 1 (a'⁻¹ • η) :=
    (hw _ hηa').mpr (iff_of_false hi2 fun e => hη'2 e.symm)
  have hwaa' : w ∈ ballStab 1 (a⁻¹ • (a'⁻¹ • η)) :=
    (hw _ hηaa').mpr (iff_of_false hi3 fun e => hη'3 (e.symm.trans e3.symm))
  have huη : u ∉ ballStab 1 η := by
    rw [hu η hη]
    exact fun e => hwη (e.mpr hwa)
  have hua' : u ∈ ballStab 1 (a'⁻¹ • η) := (hu _ hηa').mpr (iff_of_true hwa' hwaa')
  have hvη : v ∉ ballStab 1 η := by
    rw [hv η hη]
    exact fun e => huη (e.mpr hua')
  have hvc : v = c₂ := by
    rcases eq_one_or_eq_of_mem_zpowers hco₂ (show v ∈ Subgroup.zpowers c₂ from hZ₂ ▸ hvZ) with h | h
    · exact absurd (show v ∈ ballStab 1 η by rw [h]; exact (ballStab 1 η).one_mem) hvη
    · exact h
  obtain ⟨θ₀, hθ₀, hθ₀S⟩ := exists_mem_not_mem_of_card_lt (s := nbrs μ₁)
    [δ, η, η', a • η, a • η', a' • η, a' • η', (a' * a) • η, (a' * a) • η'].toFinset
    ((List.toFinset_card_le _).trans_lt (by simp only [List.length_cons, List.length_nil]; omega))
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at hθ₀S
  obtain ⟨hθδ, hθη, hθη', hθ1, hθ1', hθ2, hθ2', hθ3, hθ3'⟩ := hθ₀S
  have hwθ : ∀ θ ∈ nbrs μ₁, θ ≠ η → θ ≠ η' → w ∈ ballStab 1 θ := fun θ hθ hθη hθη' =>
    (hw θ hθ).mpr (iff_of_false hθη hθη')
  have hback : ∀ (g : ↥G₀) {θ ζ : CosetGeom G₀ G₁ G₂}, θ ≠ g • ζ → g⁻¹ • θ ≠ ζ :=
    fun g θ ζ hne e => hne (by rw [← e, smul_inv_smul])
  have e3' : ∀ ζ : CosetGeom G₀ G₁ G₂, (a' * a) • ζ = a' • (a • ζ) := fun ζ => mul_smul _ _ _
  have hθa : a⁻¹ • θ₀ ∈ nbrs μ₁ := hnbr haμ₁ hθ₀
  have hθa' : a'⁻¹ • θ₀ ∈ nbrs μ₁ := hnbr ha'μ₁ hθ₀
  have hθaa' : a⁻¹ • (a'⁻¹ • θ₀) ∈ nbrs μ₁ := hnbr haμ₁ hθa'
  have hθ3a : a'⁻¹ • θ₀ ≠ a • η := hback a' (by rw [← e3']; exact hθ3)
  have hθ3a' : a'⁻¹ • θ₀ ≠ a • η' := hback a' (by rw [← e3']; exact hθ3')
  have huθ : u ∈ ballStab 1 θ₀ := (hu θ₀ hθ₀).mpr (iff_of_true (hwθ θ₀ hθ₀ hθη hθη')
    (hwθ _ hθa (hback a hθ1) (hback a hθ1')))
  have huθ' : u ∈ ballStab 1 (a'⁻¹ • θ₀) := (hu _ hθa').mpr (iff_of_true
    (hwθ _ hθa' (hback a' hθ2) (hback a' hθ2'))
    (hwθ _ hθaa' (hback a hθ3a) (hback a hθ3a')))
  have hvθ : v ∈ ballStab 1 θ₀ := (hv θ₀ hθ₀).mpr (iff_of_true huθ huθ')
  obtain ⟨Xδ, hXδ⟩ := exists_isLocalReg_of_vtype hbase hδ
  have hc₂V : c₂ ∈ Vv Z δ := Vv_le_Vv_of_mem_nbrs hδ hμ₂ (hZ₂ ▸ Subgroup.mem_zpowers c₂)
  have hc₂Z : c₂ ∉ Vv Z μ₁ := by
    intro hc₂
    apply lemma73_2 hc hδ hXδ hμ₁ hμ₂ hne
    have hle : Vv Z μ₂ ≤ Vv Z μ₁ := by rw [hZ₂, Subgroup.zpowers_le]; exact hc₂
    have h2₂ : Nat.card (Vv Z μ₂) = 2 := by rw [hZ₂, Nat.card_zpowers, hco₂]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2₁, h2₂])).symm
  exact not_mem_ballStab_of_four hc hb hL hμ₁t hδμ₁ hθ₀ (Ne.symm hθδ) (h4' hδ) h2₁ hc₂V hc₂Z
    (hvc ▸ hvθ)

theorem card_Vv_ne_four_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {p : ℕ} {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hN : 10 ≤ Nat.card (nbrs (γ₀ G₀ G₁ G₂))) :
    Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) ≠ 4 := by
  intro h4
  classical
  obtain ⟨hp3, hz, -⟩ := corollary77 hc (by rw [hb]; decide) hbase
  subst hp3
  have hG := hc.amalgam.gen
  have hδ : vtype (γ₁ G₀ G₁ G₂) = true := CosetGeom.vtype_γ₁
  obtain ⟨μ₁, hμ₁⟩ := CosetGeom.exists_adj (γ₁ G₀ G₁ G₂)
  have hμ₁' : μ₁ ∈ nbrs (γ₁ G₀ G₁ G₂) := hμ₁
  obtain ⟨y, hyX, hyN⟩ := hbase.exists_not_mem
  have hyst : y ∈ stab (γ₁ G₀ G₁ G₂) := hbase.le_stab hyX
  have hy0 : y ∈ G₀ := CosetGeom.stab_le _ hyst
  have hμ₂ : (⟨y, hy0⟩ : ↥G₀) • μ₁ ∈ nbrs (γ₁ G₀ G₁ G₂) :=
    IsLocalReg.smul_mem_nbrs hμ₁' hyst
  have hne : μ₁ ≠ (⟨y, hy0⟩ : ↥G₀) • μ₁ := fun e =>
    hyN (hbase.inf_le μ₁ hμ₁' ⟨hyX, CosetGeom.mem_stab_of_smul_eq (g := ⟨y, hy0⟩) e.symm⟩)
  obtain ⟨μ₂, hμ₂def⟩ : ∃ μ₂, (⟨y, hy0⟩ : ↥G₀) • μ₁ = μ₂ := ⟨_, rfl⟩
  rw [hμ₂def] at hμ₂ hne
  have hμ₁t : vtype μ₁ = false := vtype_eq_false_of_mem_nbrs hδ hμ₁'
  have hμ₂t : vtype μ₂ = false := vtype_eq_false_of_mem_nbrs hδ hμ₂
  have hδμ₁ : γ₁ G₀ G₁ G₂ ∈ nbrs μ₁ := CosetGeom.mem_nbrs_symm hμ₁'
  have hδμ₂ : γ₁ G₀ G₁ G₂ ∈ nbrs μ₂ := CosetGeom.mem_nbrs_symm hμ₂
  obtain ⟨c₁, hZ₁, hco₁, -⟩ := hz μ₁ hμ₁t
  obtain ⟨c₂, hZ₂, hco₂, hcc₂⟩ := hz μ₂ hμ₂t
  have h2₁ : Nat.card (Vv Z μ₁) = 2 := by rw [hZ₁, Nat.card_zpowers, hco₁]
  have h2₂ : Nat.card (Vv Z μ₂) = 2 := by rw [hZ₂, Nat.card_zpowers, hco₂]
  have hN₁ : 10 ≤ Nat.card (nbrs μ₁) := by rw [card_nbrs_eq hc hμ₁t]; exact hN
  have hN₂ : 10 ≤ Nat.card (nbrs μ₂) := by rw [card_nbrs_eq hc hμ₂t]; exact hN
  have h4' : ∀ {ε : CosetGeom G₀ G₁ G₂}, vtype ε = true → Nat.card (Vv Z ε) = 4 := fun hε =>
    (card_Vv_eq_of_vtype hc hε).trans h4
  obtain ⟨η, hη, hηS⟩ := exists_mem_not_mem_of_card_lt {γ₁ G₀ G₁ G₂}
    (s := nbrs μ₁) (by rw [Finset.card_singleton]; omega)
  have hηδ : η ≠ γ₁ G₀ G₁ G₂ := fun e => hηS (by rw [e]; exact Finset.mem_singleton_self _)
  have hηt : vtype η = true := vtype_eq_true_of_mem_nbrs hμ₁t hη
  obtain ⟨Xη, hXη⟩ := exists_isLocalReg_of_vtype hbase hηt
  have hμ₁η : μ₁ ∈ nbrs η := CosetGeom.mem_nbrs_symm hη
  have hpar : ∀ g ∈ stab η ⊓ stab μ₁, ∀ h ∈ stab η ⊓ stab μ₁,
      (g ∈ ballStab 1 η ↔ h ∈ ballStab 1 η) → g⁻¹ * h ∈ ballStab 1 η := by
    intro g hg h hh e
    have hg' : g⁻¹ ∈ stab η ⊓ stab μ₁ := (stab η ⊓ stab μ₁).inv_mem hg
    rw [mem_ballStab_mul_iff hG hXη hμ₁η hg' hh, Subgroup.inv_mem_iff]
    exact e
  have hA0 : ∀ g ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), g ∈ G₀ := fun g hg =>
    CosetGeom.stab_le _ (CosetGeom.ballStab_le_stab 1 _ hg.2)
  have hAμ₁ : ∀ g ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), g ∈ stab μ₁ := fun g hg =>
    CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hμ₁').le hg.2
  have horb : ∀ g ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), ∀ h ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂),
      g ∉ stab η → h ∉ stab η → g⁻¹ * h ∈ stab η := by
    intro g hg h hh hgη hhη
    have hg' : g⁻¹ ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂) := (Wv Z μ₂ ⊓ _).inv_mem hg
    rcases fix_or_fix_or_fix hc hb hL hbase h4 hN hδ hμ₁' hμ₂ hne (a := ⟨h, hA0 h hh⟩)
      (a' := ⟨g⁻¹, hA0 _ hg'⟩) hh hg' hη hηδ with e | e | e
    · exact absurd (CosetGeom.mem_stab_of_smul_eq e) hhη
    · exact absurd ((stab η).inv_mem_iff.mp (CosetGeom.mem_stab_of_smul_eq e)) hgη
    · exact CosetGeom.mem_stab_of_smul_eq e
  obtain ⟨c, hcA, hcη⟩ : ∃ c ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂),
      ∀ g ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), g ∉ stab η → c ∉ stab η := by
    by_cases hex : ∃ c ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), c ∉ stab η
    · obtain ⟨c, hcA, hcη⟩ := hex
      exact ⟨c, hcA, fun _ _ _ => hcη⟩
    · exact ⟨1, Subgroup.one_mem _, fun g hg hgη => absurd ⟨g, hg, hgη⟩ hex⟩
  let cls : G → Bool × Bool := fun g =>
    if g ∈ stab η then (true, decide (g ∈ ballStab 1 η)) else (false, decide (c⁻¹ * g ∈ ballStab 1 η))
  have hcls : ∀ g ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂), ∀ h ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂),
      cls g = cls h → g⁻¹ * h ∈ ballStab 1 η := by
    intro g hg h hh e
    by_cases hgη : g ∈ stab η <;> by_cases hhη : h ∈ stab η <;>
      simp only [cls, hgη, hhη, ↓reduceIte, Prod.mk.injEq, eq_self_iff_true, Bool.true_eq_false,
        Bool.false_eq_true, false_and, true_and, decide_eq_decide] at e
    · exact hpar g ⟨hgη, hAμ₁ g hg⟩ h ⟨hhη, hAμ₁ h hh⟩ e
    · have hcη' := hcη g hg hgη
      have hcg := horb c hcA g hg hcη' hgη
      have hch := horb c hcA h hh hcη' hhη
      have hcμ₁ : c⁻¹ ∈ stab μ₁ := (stab μ₁).inv_mem (hAμ₁ c hcA)
      have := hpar _ ⟨hcg, (stab μ₁).mul_mem hcμ₁ (hAμ₁ g hg)⟩ _
        ⟨hch, (stab μ₁).mul_mem hcμ₁ (hAμ₁ h hh)⟩ e
      have e' : (c⁻¹ * g)⁻¹ * (c⁻¹ * h) = g⁻¹ * h := by group
      rwa [e'] at this
  have hexV : ∀ ε : CosetGeom G₀ G₁ G₂, ∃ x : G, ε ∈ nbrs μ₂ → x ∈ Vv Z ε ∧ x ∉ Vv Z μ₂ := by
    intro ε
    by_cases hε : ε ∈ nbrs μ₂
    · obtain ⟨x, hx, hxZ⟩ : ∃ x ∈ Vv Z ε, x ∉ Vv Z μ₂ :=
        SetLike.not_le_iff_exists.mp fun hle => by
          have := Subgroup.card_le_of_le hle
          rw [h4' (vtype_eq_true_of_mem_nbrs hμ₂t hε), h2₂] at this
          omega
      exact ⟨x, fun _ => ⟨hx, hxZ⟩⟩
    · exact ⟨1, fun h => absurd h hε⟩
  choose xf hxf using hexV
  obtain ⟨ε₀, hε₀, hε₀S⟩ := exists_mem_not_mem_of_card_lt {γ₁ G₀ G₁ G₂}
    (s := nbrs μ₂) (by rw [Finset.card_singleton]; omega)
  have hε₀δ : ε₀ ≠ γ₁ G₀ G₁ G₂ := fun e => hε₀S (by rw [e]; exact Finset.mem_singleton_self _)
  have hxδ : ∀ ε ∈ nbrs μ₂, ε ≠ γ₁ G₀ G₁ G₂ → xf ε ∉ ballStab 1 (γ₁ G₀ G₁ G₂) := fun ε hε hεδ =>
    not_mem_ballStab_of_four hc hb hL hμ₂t hε hδμ₂ hεδ (h4' (vtype_eq_true_of_mem_nbrs hμ₂t hε))
      h2₂ (hxf ε hε).1 (hxf ε hε).2
  have hxst : ∀ ε ∈ nbrs μ₂, xf ε ∈ stab (γ₁ G₀ G₁ G₂) ⊓ stab μ₂ := fun ε hε =>
    Vv_le_stab_inf_of_three hc hb hμ₂t hε hδμ₂ (hxf ε hε).1
  obtain ⟨Xδ, hXδ⟩ := exists_isLocalReg_of_vtype hbase hδ
  have hyA : ∀ ε ∈ nbrs μ₂, ε ≠ γ₁ G₀ G₁ G₂ →
      xf ε₀ * xf ε ∈ Wv Z μ₂ ⊓ ballStab 1 (γ₁ G₀ G₁ G₂) := fun ε hε hεδ =>
    ⟨(Wv Z μ₂).mul_mem (Vv_le_Wv hε₀ (hxf ε₀ hε₀).1) (Vv_le_Wv hε (hxf ε hε).1),
      (mem_ballStab_mul_iff hG hXδ hμ₂ (hxst ε₀ hε₀) (hxst ε hε)).mpr
        (iff_of_false (hxδ ε₀ hε₀ hε₀δ) (hxδ ε hε hεδ))⟩
  have hE : 2 * Fintype.card (Bool × Bool) <
      Nat.card ↥{ε | ε ∈ nbrs μ₂ ∧ ε ≠ γ₁ G₀ G₁ G₂} := by
    have hsub : nbrs μ₂ ⊆ {ε | ε ∈ nbrs μ₂ ∧ ε ≠ γ₁ G₀ G₁ G₂} ∪ {γ₁ G₀ G₁ G₂} := by
      intro ε hε
      by_cases hεδ : ε = γ₁ G₀ G₁ G₂
      · exact Or.inr hεδ
      · exact Or.inl ⟨hε, hεδ⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le {ε | ε ∈ nbrs μ₂ ∧ ε ≠ γ₁ G₀ G₁ G₂} {γ₁ G₀ G₁ G₂}
    rw [Set.ncard_singleton] at h2
    have h3 : Nat.card ↥(nbrs μ₂) = (nbrs μ₂).ncard := Nat.card_coe_set_eq _
    rw [Nat.card_coe_set_eq, Fintype.card_prod, Fintype.card_bool]
    omega
  obtain ⟨ε₁, hε₁, ε₂, hε₂, ε₃, hε₃, h12, h13, h23, e12, e13⟩ :=
    exists_three_eq_of_two_mul_lt (fun ε => cls (xf ε₀ * xf ε)) hE
  have hg2 := hcls _ (hyA ε₁ hε₁.1 hε₁.2) _ (hyA ε₂ hε₂.1 hε₂.2) e12
  have hg3 := hcls _ (hyA ε₁ hε₁.1 hε₁.2) _ (hyA ε₃ hε₃.1 hε₃.2) e13
  have e2 : (xf ε₀ * xf ε₁)⁻¹ * (xf ε₀ * xf ε₂) = (xf ε₁)⁻¹ * xf ε₂ := by group
  have e3 : (xf ε₀ * xf ε₁)⁻¹ * (xf ε₀ * xf ε₃) = (xf ε₁)⁻¹ * xf ε₃ := by group
  rw [e2] at hg2
  rw [e3] at hg3
  have hcomm := (ballStab 1 η).mul_mem ((ballStab 1 η).mul_mem ((ballStab 1 η).mul_mem hg2 hg3)
    ((ballStab 1 η).inv_mem hg2)) ((ballStab 1 η).inv_mem hg3)
  have hx₁μ₂ : xf ε₁ ∈ stab μ₂ := (hxst ε₁ hε₁.1).2
  rw [comm_inv_mul_inv_mul
    (conj_eq_of_four hc hb hL hbase h4 hμ₂t hε₂.1 hε₁.1 (Ne.symm h12) hZ₂ hco₂ (hxf ε₂ hε₂.1).1
      (hxf ε₂ hε₂.1).2 (hxf ε₁ hε₁.1).1 (hxf ε₁ hε₁.1).2)
    (conj_eq_of_four hc hb hL hbase h4 hμ₂t hε₂.1 hε₃.1 h23 hZ₂ hco₂ (hxf ε₂ hε₂.1).1
      (hxf ε₂ hε₂.1).2 (hxf ε₃ hε₃.1).1 (hxf ε₃ hε₃.1).2)
    (conj_eq_of_four hc hb hL hbase h4 hμ₂t hε₁.1 hε₃.1 h13 hZ₂ hco₂ (hxf ε₁ hε₁.1).1
      (hxf ε₁ hε₁.1).2 (hxf ε₃ hε₃.1).1 (hxf ε₃ hε₃.1).2)
    (hcc₂ _ hx₁μ₂).symm, Subgroup.inv_mem_iff] at hcomm
  have hc₂V : c₂ ∈ Vv Z (γ₁ G₀ G₁ G₂) :=
    Vv_le_Vv_of_mem_nbrs hδ hμ₂ (hZ₂ ▸ Subgroup.mem_zpowers c₂)
  have hc₂Z : c₂ ∉ Vv Z μ₁ := by
    intro hc₂
    apply lemma73_2 hc hδ hXδ hμ₁' hμ₂ hne
    have hle : Vv Z μ₂ ≤ Vv Z μ₁ := by rw [hZ₂, Subgroup.zpowers_le]; exact hc₂
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2₁, h2₂])).symm
  exact not_mem_ballStab_of_four hc hb hL hμ₁t hδμ₁ hη (Ne.symm hηδ) (h4' hδ) h2₁ hc₂V hc₂Z
    hcomm

theorem false_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {p : ℕ} {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hN : 10 ≤ Nat.card (nbrs (γ₀ G₀ G₁ G₂))) : False := by
  have hδ : vtype (γ₁ G₀ G₁ G₂) = true := CosetGeom.vtype_γ₁
  obtain ⟨-, -, hV⟩ := theorem75 hc (by rw [hb]; decide) hbase
  obtain ⟨hV8, hcomm⟩ := hV (γ₁ G₀ G₁ G₂) hδ
  obtain ⟨x, hx, hxN⟩ := hbase.exists_not_mem
  have hxV : x ∈ Subgroup.normalizer (Vv Z (γ₁ G₀ G₁ G₂) : Set G) :=
    (lemma63_2' hc hδ).2.2.2.2 (hbase.le_stab hx)
  haveI : IsMulCommutative ↥(Vv Z (γ₁ G₀ G₁ G₂)) := (lemma63_2' hc hδ).1.1
  have h4le : 4 ≤ Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) := by
    rw [← hcomm X₀ hbase x hx hxN]
    exact Subgroup.card_le_of_le (ConjAut.commSubgroup_le _ x hxV)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian (lemma63_2' hc hδ).1).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · exact card_Vv_ne_four_of_three hc hb hL hbase hN (by rw [hk]; norm_num)
  · exact card_Vv_ne_eight_of_three hc hb hL hbase (by rw [hk]; norm_num)

end CFSG.Quasithin.F112Crit

end
