module

public import CFSG.RankThree.GF2n.Smith81.S81E4StabTor
public import CFSG.RankThree.GF2n.Smith81.S81QStab
public import CFSG.RankThree.GF2n.Smith81.S81E4StabWeyl

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.LieType.RootSystem CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6X


variable {K : Type} [Field K]

set_option maxRecDepth 20000 in
private theorem pr_eight_eq : ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ →
    pr ⟨8, by decide⟩ γ = -γ node1 + γ nodeQ2 := by
  refine (forall_isRoot_iff fun γ => pr ⟨8, by decide⟩ γ = -γ node1 + γ nodeQ2).2 ?_
  unfold pr
  decide +kernel

theorem pr_a0_eq_of_isRoot {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    pr (a0 : Fin e7Data.d) γ = -γ node1 + γ nodeQ2 :=
  pr_eight_eq γ hγ

set_option maxRecDepth 20000 in
private theorem pr_eight_ne_neg_one : ∀ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β →
    β node1 = 0 → 0 < height (τ := .E7) β → pr ⟨8, by decide⟩ β ≠ -1 := by
  refine (forall_isRoot_iff fun β => β node1 = 0 → 0 < height (τ := .E7) β →
    pr ⟨8, by decide⟩ β ≠ -1).2 ?_
  unfold pr
  decide +kernel

theorem pr_a0_ne_neg_one_of_pos {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hz : β node1 = 0) (hpos : 0 < height (τ := .E7) β) : pr (a0 : Fin e7Data.d) β ≠ -1 :=
  pr_eight_ne_neg_one β hβ hz hpos

@[expose] def charSub (χ : ↥(StabP0 K) →* Kˣ) : Subgroup ↥(StabP0 K) where
  carrier := {g | ((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = ((χ g : Kˣ) : K) • p0 K}
  mul_mem' := fun {g h} hg hh => by
    change ((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (((h : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) = _
    rw [hh, map_smul, hg, smul_smul, map_mul, Units.val_mul, mul_comm]
  one_mem' := by
    change p0 K = ((χ 1 : Kˣ) : K) • p0 K
    rw [map_one, Units.val_one, one_smul]
  inv_mem' := fun {g} hg => by
    change (((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K)⁻¹) (p0 K) = ((χ g⁻¹ : Kˣ) : K) • p0 K
    apply ((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K).injective
    rw [map_smul, hg, smul_smul, map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
    exact LinearEquiv.apply_symm_apply _ _

@[expose] def charSubG (χ : ↥(StabP0 K) →* Kˣ) : Subgroup (e7Data_valid.minGroup K) where
  carrier := {g | ∃ x ∈ charSub χ, IndW g (((x : ↥(StabP0 K)) : ↥(EAut0 K)) : W K ≃ₗ[K] W K)}
  mul_mem' := by
    rintro g h ⟨x, hx, hgx⟩ ⟨y, hy, hhy⟩
    exact ⟨x * y, mul_mem hx hy, hgx.mul hhy⟩
  one_mem' := ⟨1, one_mem _, IndW.one⟩
  inv_mem' := by
    rintro g ⟨x, hx, hgx⟩
    exact ⟨x⁻¹, inv_mem hx, hgx.inv⟩

theorem endo_single_a0_of_mem_charSubG {χ : ↥(StabP0 K) →* Kˣ} {g : e7Data_valid.minGroup K}
    (hg : g ∈ charSubG χ) :
    ∃ c : K, endoE g (Finsupp.single (a0 : Fin e7Data.d) 1) =
      c • Finsupp.single (a0 : Fin e7Data.d) 1 := by
  obtain ⟨x, hx, hgx⟩ := hg
  refine ⟨((χ x : Kˣ) : K), ?_⟩
  have hx' : ((x : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = ((χ x : Kˣ) : K) • p0 K := hx
  have h := hgx (p0 K)
  rw [hx', map_smul, p0, emb_single] at h
  exact h.symm

theorem nW_mem_LamG_of_preserves_node1 {w : W7 K}
    (hw : ∀ δ, IsRoot .E7 δ → weylAction (e7Datum K).isFiniteType w δ node1 = δ node1) :
    nW K w ∈ LamG K := by
  refine (Subgroup.closure_le _).2 ?_ (nW_mem_closure_of_preserves {node1} fun δ hδ j hj => by
    rw [Set.mem_singleton_iff.1 hj]
    exact hw δ hδ)
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hi
  refine nm_mem_LamG i ?_
  have h0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
  omega

variable [CharP K 2]

theorem mem_charSubG_of_fix (χ : ↥(StabP0 K) →* Kˣ) {g : e7Data_valid.minGroup K}
    (hgL : g ∈ LamG K)
    (hfix : endoE g (Finsupp.single (a0 : Fin e7Data.d) 1) = Finsupp.single (a0 : Fin e7Data.d) 1)
    (hgg : g * g = 1) : g ∈ charSubG χ := by
  obtain ⟨x, hx⟩ := exists_indW hgL
  have hxE : x ∈ EAut0 K := mem_EAut0_iff.2 ⟨g, hgL, hx⟩
  have hxp : x (p0 K) = p0 K := by
    apply emb_injective
    rw [hx, p0, emb_single, hfix]
  have hS : (⟨x, hxE⟩ : ↥(EAut0 K)) ∈ StabP0 K := ⟨1, one_ne_zero, by rw [one_smul]; exact hxp⟩
  have hxx : (⟨⟨x, hxE⟩, hS⟩ : ↥(StabP0 K)) * ⟨⟨x, hxE⟩, hS⟩ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact IndW.unique (hx.mul hx) (by rw [hgg]; exact IndW.one)
  have hχ1 : χ ⟨⟨x, hxE⟩, hS⟩ = 1 := by
    refine Units.ext (CharTwo.sq_inj.1 ?_)
    rw [Units.val_one, one_pow, sq, ← Units.val_mul, ← map_mul, hxx, map_one, Units.val_one]
  refine ⟨⟨⟨x, hxE⟩, hS⟩, ?_, hx⟩
  change x (p0 K) = _
  rw [hχ1, Units.val_one, one_smul, hxp]

theorem xm_mem_charSubG (χ : ↥(StabP0 K) →* Kˣ) {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp)
    (ha : pr (a0 : Fin e7Data.d) γ ≠ -1) (c : K) : e7Data_valid.xm K γ c ∈ charSubG χ := by
  refine mem_charSubG_of_fix χ (mem_LamG.2 (xu_mem_Lam hγ c)) ?_ ?_
  · exact (forall_endo_single_iff hγ.1 _).2 ha _ (e7Data_valid.xm_mem_rootGroup K γ c)
  · rw [← e7Data_valid.xm_add, CharTwo.add_self_eq_zero, e7Data_valid.xm_zero]

theorem nt_mem_charSubG (χ : ↥(StabP0 K) →* Kˣ) (i : Fin (Tag.rank .E7)) (hi : 2 ≤ i.val)
    (t : Kˣ) : e7Data_valid.nt K i t ∈ charSubG χ := by
  have hsP : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp :=
    D6X.single_mem_Perp i (by omega)
  have hsN : -(Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ Perp := neg_mem_Perp hsP
  have h1 : node1 ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by decide)
  have h2 : nodeQ2 ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by decide)
  have h0 : pr (a0 : Fin e7Data.d) (Pi.single i 1) = 0 := by
    rw [pr_a0_eq_of_isRoot hsP.1, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    rfl
  have h0' : pr (a0 : Fin e7Data.d) (-Pi.single i 1) = 0 := by rw [pr_neg, h0, neg_zero]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact xm_mem_charSubG χ hsP (by rw [h0]; decide) _
  · exact xm_mem_charSubG χ hsN (by rw [h0']; decide) _
  · exact xm_mem_charSubG χ hsP (by rw [h0]; decide) _

theorem hmQ2_mem_charSubG {χ : ↥(StabP0 K) →* Kˣ} (hχ : ∀ c : Kˣ, χ (d0 K c) = c) (c : Kˣ) :
    e7Data_valid.hm K nodeQ2 c ∈ charSubG χ := by
  refine ⟨d0 K c, ?_, fun w => resV0_induces (d0Lam K c) w⟩
  change _ = _
  rw [hχ c]
  exact d0_apply_p0 c

theorem tLam_le_charSubG {χ : ↥(StabP0 K) →* Kˣ} (hχ : ∀ c : Kˣ, χ (d0 K c) = c) :
    TLam K ≤ charSubG χ := by
  refine iSup₂_le fun i hi x hx => ?_
  obtain ⟨t, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
  by_cases h2 : i = nodeQ2
  · subst h2
    exact hmQ2_mem_charSubG hχ t
  · have hi2 : 2 ≤ i.val := by
      have : i.val ≠ 1 := fun h => h2 (Fin.ext h)
      omega
    exact mul_mem (nt_mem_charSubG χ i hi2 t) (inv_mem (nt_mem_charSubG χ i hi2 1))

theorem ulG_le_charSubG (χ : ↥(StabP0 K) →* Kˣ) : ULG K ≤ charSubG χ := by
  have key : UL K ≤ (charSubG χ).map (e7Data_valid.minGroup K).subtype := by
    rw [UL, Subgroup.closure_le]
    rintro _ ⟨β, hβ, hz, hpos, c, rfl⟩
    have hz1 : β node1 = 0 := by rw [← pair_theta β]; exact hz
    exact ⟨_, xm_mem_charSubG χ ⟨hβ, hz⟩ (pr_a0_ne_neg_one_of_pos hβ hz1 hpos) c, rfl⟩
  intro u hu
  obtain ⟨u', hu', e⟩ := key (mem_ULG.1 hu)
  rw [← Subtype.ext e]
  exact hu'

theorem nW_mem_charSubG (χ : ↥(StabP0 K) →* Kˣ) {w : W7 K}
    (hw : ∀ δ, IsRoot .E7 δ → ∀ j ∈ ({node1, nodeQ2} : Set (Fin (Tag.rank .E7))),
      weylAction (e7Datum K).isFiniteType w δ j = δ j) :
    nW K w ∈ charSubG χ := by
  refine (Subgroup.closure_le _).2 ?_ (nW_mem_closure_of_preserves _ hw)
  rintro _ ⟨i, hi, rfl⟩
  have hi2 : 2 ≤ i.val := by
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
    have h0 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi.2 (Fin.ext h)
    omega
  exact nt_mem_charSubG χ i hi2 1

theorem e4StabChar_holds (K : Type) [Field K] [CharP K 2] : E4StabChar K := by
  intro χ hχ g
  obtain ⟨⟨x, hxE⟩, c, hc0, hc⟩ := g
  obtain ⟨gt, hgL, hgx⟩ := mem_EAut0_iff.1 hxE
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hgeq⟩ := Lam_bruhat (mem_LamG.1 hgL)
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := mem_BorL_iff.1 hb₁
  have ht₁' : (nW K w)⁻¹ * t₁ * nW K w ∈ Tor K :=
    inv_conj_mem_iSup_of_mem_weylN (e7Datum_isCTGroupDatum K)
      (nrep_mem_weylN (e7Datum_isCTGroupDatum K) w) ht₁
  obtain ⟨u₂, hu₂, t₂, ht₂, e₃⟩ := mem_BorL_iff.1 (mul_mem (Subgroup.mem_sup_left ht₁') hb₂)
  have hgeq' : gt = u₁ * nW K w * (u₂ * t₂) := by
    rw [hgeq, ← e₃]
    group
  have e : nW K w = u₁⁻¹ * gt * (u₂ * t₂)⁻¹ := by rw [hgeq']; group
  have hNG : ((nW K w : e7Data_valid.minGroup K) : (Module.End K (V K))ˣ) ∈ GG K := by
    have hb₂G : ((u₂ * t₂ : e7Data_valid.minGroup K) : (Module.End K (V K))ˣ) ∈ GG K :=
      mul_mem (UL_le_GG hu₂) (tor_mem_GG ht₂)
    rw [e]
    exact mul_mem (mul_mem (inv_mem (UL_le_GG hu₁)) (Lam_le_GG hgL)) (inv_mem hb₂G)
  have hNL : nW K w ∈ LamG K :=
    nW_mem_LamG_of_preserves_node1 fun δ hδ => node1_weylAction_of_mem_GG hNG hδ
  have ht₂L : t₂ ∈ LamG K := by
    have h : t₂ = u₂⁻¹ * ((nW K w)⁻¹ * u₁⁻¹ * gt) := by rw [hgeq']; group
    rw [h]
    exact mul_mem (inv_mem (ULG_le_LamG hu₂))
      (mul_mem (mul_mem (inv_mem hNL) (inv_mem (ULG_le_LamG hu₁))) hgL)
  have hu₁Q : u₁ ∈ charSubG χ := ulG_le_charSubG χ hu₁
  have hb₂Q : u₂ * t₂ ∈ charSubG χ := mul_mem (ulG_le_charSubG χ hu₂)
    (tLam_le_charSubG hχ (mem_tLam_of_mem_tor_of_mem_lamG ht₂ ht₂L))
  have hgt : endoE gt (Finsupp.single (a0 : Fin e7Data.d) 1) =
      c • Finsupp.single (a0 : Fin e7Data.d) 1 := by
    have h := hgx (p0 K)
    have hc' : x (p0 K) = c • p0 K := hc
    rw [hc', map_smul, p0, emb_single] at h
    exact h.symm
  obtain ⟨c₁, hc₁⟩ := endo_single_a0_of_mem_charSubG (inv_mem hu₁Q)
  obtain ⟨c₂, hc₂⟩ := endo_single_a0_of_mem_charSubG (inv_mem hb₂Q)
  have hNa : endoE (nW K w) (Finsupp.single (a0 : Fin e7Data.d) 1) =
      (c₁ * (c * c₂)) • Finsupp.single (a0 : Fin e7Data.d) 1 := by
    rw [e]
    change e7Data_valid.endo K (u₁⁻¹ * gt * (u₂ * t₂)⁻¹) _ = _
    rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, Module.End.mul_apply, Module.End.mul_apply]
    change endoE u₁⁻¹ (endoE gt (endoE (u₂ * t₂)⁻¹ _)) = _
    rw [hc₂, map_smul, hgt, map_smul, map_smul, hc₁, smul_smul, smul_smul]
    ring_nf
  have hw : ∀ δ, IsRoot .E7 δ → ∀ j ∈ ({node1, nodeQ2} : Set (Fin (Tag.rank .E7))),
      weylAction (e7Datum K).isFiniteType w δ j = δ j := by
    intro δ hδ j hj
    have hδ' : IsRoot .E7 (weylAction (e7Datum K).isFiniteType w δ) :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 (weylAction_mem_roots _ w
        ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hδ))
    have h1 := node1_weylAction_of_mem_GG hNG hδ
    have h2 := pr_weylAction_of_actsAs (actsAs_nrep (e7Datum_isCTGroupDatum K) w) hNa hδ
    rw [pr_a0_eq_of_isRoot hδ', pr_a0_eq_of_isRoot hδ, h1] at h2
    rcases hj with rfl | rfl
    · exact h1
    · exact (add_left_cancel h2 : _)
  have hgtQ : gt ∈ charSubG χ := by
    rw [hgeq']
    exact mul_mem (mul_mem hu₁Q (nW_mem_charSubG χ hw)) hb₂Q
  obtain ⟨y, hy, hgy⟩ := hgtQ
  have hyx : y = ⟨⟨x, hxE⟩, c, hc0, hc⟩ := Subtype.ext (Subtype.ext (IndW.unique hgy hgx))
  rw [← hyx]
  exact hy

end CFSG.RankThree.GF2n.Smith81.D6Spin
