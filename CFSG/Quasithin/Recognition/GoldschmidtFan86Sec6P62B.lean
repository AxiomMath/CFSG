module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

variable {L : ZLab Γ G} (F : FanTree Γ G) (H : LabHyp L)
include F H

theorem prod_fix {d ν ξ a b : V} (hd : valence Γ d = 5) (h : Br Γ d ν ξ) (ha : Γ.dist d a = 2)
    (hb : Γ.dist d b = 2) (hma : L.z a • ξ ≠ ξ) (hmb : L.z b • ξ ≠ ξ) :
    (L.z a * L.z b) • ξ = ξ := by
  obtain ⟨ξ', hξ', hne, -⟩ := exists_sibling F hd h
  have hva := (Br.valence F hd (exists_br F ha).choose_spec).2
  have h1 := nbrStab_swap F hd (H.ker d a hd ha) h hξ' hne.symm
  have h2 := nbrStab_swap F hd (H.ker d b hd hb) h hξ' hne.symm
  have e1 : L.z a • ξ = ξ' := h1.resolve_left hma
  have e2 : L.z b • ξ = ξ' := h2.resolve_left hmb
  rw [mul_smul, e2, ← e1, ← mul_smul, z_sq hva, one_smul]

theorem no_four (h40 : Fan40 F) {d ξ₁ ξ₂ ξ₃ ξ₄ : V} (hd : valence Γ d = 5)
    (hN : NoncommAt L d) (h1 : Γ.dist d ξ₁ = 2) (h2 : Γ.dist d ξ₂ = 2) (h3 : Γ.dist d ξ₃ = 2)
    (h4 : Γ.dist d ξ₄ = 2) (n12 : NC L ξ₁ ξ₂) (n13 : NC L ξ₁ ξ₃) (n23 : NC L ξ₂ ξ₃)
    (n14 : NC L ξ₁ ξ₄) (n24 : NC L ξ₂ ξ₄) (n34 : NC L ξ₃ ξ₄) : False := by
  obtain ⟨ν, hν⟩ := exists_br F h4
  have hv4 := (Br.valence F hd hν).2
  have hdist4 : Γ.dist ξ₄ d = 2 := by rw [dist_comm]; exact h4
  have hN4 : NoncommAt L ξ₄ := noncomm_all F hd hv4 hN
  have mv : ∀ {a : V}, Γ.dist d a = 2 → NC L ξ₄ a → L.z a • ξ₄ ≠ ξ₄ :=
    fun ha hn => (nc_iff F H hd hν ha).1 hn
  have key : ∀ {a b : V}, Γ.dist d a = 2 → Γ.dist d b = 2 → NC L a b → NC L ξ₄ a →
      NC L ξ₄ b → (L.z a * L.z b) * (L.z a * L.z b) = L.z d ∧
        L.z a * L.z b ∈ MulAction.stabilizer G ξ₄ ⊓ MulAction.stabilizer G ν ∧
        L.z a * L.z b ∉ nbrStab Γ G ξ₄ := by
    intro a b ha hb hab hna hnb
    have hsq := nc_sq F H hd ha hb hab
    have hKd : L.z a * L.z b ∈ nbrStab Γ G d :=
      (nbrStab Γ G d).mul_mem (H.ker d a hd ha) (H.ker d b hd hb)
    have hfix := prod_fix F H hd hν ha hb (mv ha hna) (mv hb hnb)
    have hst : L.z a * L.z b ∈ MulAction.stabilizer G ξ₄ := MulAction.mem_stabilizer_iff.2 hfix
    refine ⟨hsq, ⟨hst, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hKd ν hν.1)⟩, ?_⟩
    exact lemma_A F h40 H hv4 hN4 hdist4 hst (by rw [hsq])
  obtain ⟨s12, m12, o12⟩ := key h1 h2 n12 n14.symm n24.symm
  obtain ⟨s23, m23, o23⟩ := key h2 h3 n23 n24.symm n34.symm
  obtain ⟨-, -, o13⟩ := key h1 h3 n13 n14.symm n34.symm
  have hadj : Γ.Adj ξ₄ ν := hν.2.1.symm
  have hk : ∀ s : G, s * s = L.z d → s * s ∈ nbrStab Γ G ξ₄ := fun s hs => by
    rw [hs]
    exact H.ker ξ₄ d hv4 hdist4
  have hprod := mul_mem_nbrStab_of_sq_mem F hadj m12 m23 (hk _ s12) (hk _ s23) o12 o23
  apply o13
  have : L.z ξ₂ * L.z ξ₂ = 1 := z_sq (Br.valence F hd (exists_br F h2).choose_spec).2
  have e : L.z ξ₁ * L.z ξ₂ * (L.z ξ₂ * L.z ξ₃) = L.z ξ₁ * L.z ξ₃ := by
    rw [mul_assoc, ← mul_assoc (L.z ξ₂), this, one_mul]
  rwa [e] at hprod

omit H in
theorem exists_four_nbrs {d : V} (hd : valence Γ d = 5) :
    ∃ a b c e : V, Γ.Adj d a ∧ Γ.Adj d b ∧ Γ.Adj d c ∧ Γ.Adj d e ∧ a ≠ b ∧ a ≠ c ∧ a ≠ e ∧
      b ≠ c ∧ b ≠ e ∧ c ≠ e := by
  have hfin : (Γ.neighborSet d).Finite := (F.ncard_neighborSet_le d).2
  have hc : (Γ.neighborSet d).ncard = 4 + 1 := by
    rw [← Nat.card_coe_set_eq]
    exact hd
  obtain ⟨a, t, hat, hins, ht⟩ := (Set.ncard_eq_succ hfin).1 hc
  have hNsub : t ⊆ Γ.neighborSet d := by rw [← hins]; exact Set.subset_insert _ _
  have hfin1 : t.Finite := hfin.subset hNsub
  obtain ⟨b, t1, hbt, hins1, ht1⟩ := (Set.ncard_eq_succ hfin1).1 (show t.ncard = 3 + 1 from ht)
  have h1sub : t1 ⊆ t := by rw [← hins1]; exact Set.subset_insert _ _
  have hfin2 : t1.Finite := hfin1.subset h1sub
  obtain ⟨c, t2, hct, hins2, ht2⟩ := (Set.ncard_eq_succ hfin2).1 (show t1.ncard = 2 + 1 from ht1)
  have h2sub : t2 ⊆ t1 := by rw [← hins2]; exact Set.subset_insert _ _
  have hfin3 : t2.Finite := hfin2.subset h2sub
  obtain ⟨e, t3, het, hins3, -⟩ := (Set.ncard_eq_succ hfin3).1 (show t2.ncard = 1 + 1 from ht2)
  have hat' : a ∈ Γ.neighborSet d := by rw [← hins]; exact Set.mem_insert _ _
  have hbt' : b ∈ t := by rw [← hins1]; exact Set.mem_insert _ _
  have hct1 : c ∈ t1 := by rw [← hins2]; exact Set.mem_insert _ _
  have het2 : e ∈ t2 := by rw [← hins3]; exact Set.mem_insert _ _
  exact ⟨a, b, c, e, hat', hNsub hbt', hNsub (h1sub hct1), hNsub (h1sub (h2sub het2)),
    fun h => hat (h ▸ hbt'), fun h => hat (h ▸ h1sub hct1), fun h => hat (h ▸ h1sub (h2sub het2)),
    fun h => hbt (h ▸ hct1), fun h => hbt (h ▸ h2sub het2), fun h => hct (h ▸ het2)⟩

theorem exists_commuting_other_branch (h40 : Fan40 F) {d κ α : V} (hd : valence Γ d = 5)
    (hN : NoncommAt L d) (h : Br Γ d κ α) : ∃ ν η, Br Γ d ν η ∧ ν ≠ κ ∧ ¬ NC L α η := by
  by_contra hcon
  push Not at hcon
  have hP : ∀ ν₀ l₀ ν η, Br Γ d ν₀ l₀ → Br Γ d ν η → ν ≠ ν₀ → NC L l₀ η := by
    intro ν₀ l₀ ν η h₀ hη hne
    obtain ⟨g, hg, hgα⟩ := exists_stab_smul_br F h40 hd h h₀
    have hgd : g • d = d := MulAction.mem_stabilizer_iff.1 hg
    have hgd' : g⁻¹ • d = d :=
      MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G d).inv_mem hg)
    have hb := Br.smul F g h
    rw [hgd, hgα] at hb
    have hgκ : g • κ = ν₀ := Br.unique F hb h₀
    have hb' := Br.smul F g⁻¹ hη
    rw [hgd'] at hb'
    have hne' : g⁻¹ • ν ≠ κ := by
      intro e
      apply hne
      rw [← hgκ, ← e, smul_inv_smul]
    have hnc := hcon (g⁻¹ • ν) (g⁻¹ • η) hb' hne'
    have := (NC.smul (L := L) (Br.valence F hd h).2 (Br.valence F hd hb').2 g).2 hnc
    rwa [hgα, smul_inv_smul] at this
  obtain ⟨a, b, c, e, ha, hb, hc, he, hab, hac, hae, hbc, hbe, hce⟩ := exists_four_nbrs F hd
  obtain ⟨ξ₁, hξ₁, hn₁⟩ := F.exists_adj_ne a d
  obtain ⟨ξ₂, hξ₂, hn₂⟩ := F.exists_adj_ne b d
  obtain ⟨ξ₃, hξ₃, hn₃⟩ := F.exists_adj_ne c d
  obtain ⟨ξ₄, hξ₄, hn₄⟩ := F.exists_adj_ne e d
  have b1 : Br Γ d a ξ₁ := ⟨ha, hξ₁, hn₁⟩
  have b2 : Br Γ d b ξ₂ := ⟨hb, hξ₂, hn₂⟩
  have b3 : Br Γ d c ξ₃ := ⟨hc, hξ₃, hn₃⟩
  have b4 : Br Γ d e ξ₄ := ⟨he, hξ₄, hn₄⟩
  exact no_four F H h40 hd hN (Br.dist_two F b1) (Br.dist_two F b2) (Br.dist_two F b3)
    (Br.dist_two F b4) (hP a ξ₁ b ξ₂ b1 b2 hab.symm) (hP a ξ₁ c ξ₃ b1 b3 hac.symm)
    (hP b ξ₂ c ξ₃ b2 b3 hbc.symm) (hP a ξ₁ e ξ₄ b1 b4 hae.symm) (hP b ξ₂ e ξ₄ b2 b4 hbe.symm)
    (hP c ξ₃ e ξ₄ b3 b4 hce.symm)

end P62

end CFSG.Quasithin.Fan86
