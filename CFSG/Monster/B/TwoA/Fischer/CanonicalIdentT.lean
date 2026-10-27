module

public import CFSG.Monster.B.TwoA.Fischer.FullIntertwiner
public import CFSG.Monster.B.Fischer.CanonicalGroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

theorem orbitW_subset_of_inv
    {M : Set W₀}
    (hM : ∀ (g : CFSG.Blueprint.NativeSporadic.M22) w, w ∈ M → rhoW g w ∈ M) {w : W₀}
    (hw : w ∈ M) : orbitW w ⊆ M := by
  rintro _ ⟨g, rfl⟩
  exact hM g w hw

theorem orbitZ_subset_of_inv
    {M : Set Z}
    (hM : ∀ (g : CFSG.Blueprint.NativeSporadic.M22) z, z ∈ M → zK g z ∈ M) {z : Z}
    (hz : z ∈ M) : orbitZ z ⊆ M := by
  rintro _ ⟨g, rfl⟩
  exact hM g z hz

theorem finite_W₀ : Finite W₀ := Finite.of_equiv _ wEquiv

theorem ncard_Lw_two :
    (Lw 2).ncard = 231 := by
  rw [L2_eq, ncard_orbitW (by simp), wCert_size.2.2.1]

theorem ncard_Lw_three :
    (Lw 3).ncard = 770 := by
  rw [L3_eq, ncard_orbitW (by simp), wCert_size.2.2.2]

theorem Lw_three_subset_of_inv
    {M : Set W₀}
    (hM : ∀ (g : CFSG.Blueprint.NativeSporadic.M22) w, w ∈ M → rhoW g w ∈ M) {w : W₀}
    (hw : w ∈ M) (h3 : w ∈ Lw 3) : Lw 3 ⊆ M := by
  have e : orbitW w = Lw 3 := by
    rw [L3_eq] at h3 ⊢
    exact orbitW_eq_of_mem h3
  rw [← e]
  exact orbitW_subset_of_inv hM hw

theorem eq_Z462_of_inv
    {M : Set Z}
    (hM : ∀ (g : CFSG.Blueprint.NativeSporadic.M22) z, z ∈ M → zK g z ∈ M)
    (hcard : M.ncard = 462) : M = Z462 := by
  have : Finite Z := inferInstance
  have hsub : M ⊆ Z462 := by
    intro z hz
    rcases Z_cover z with h | h | h
    · exact h
    · have e : orbitZ z = Z770 := orbitZ_eq_of_mem h
      have h1 := Set.ncard_le_ncard (e ▸ orbitZ_subset_of_inv hM hz) (Set.toFinite M)
      rw [ncard_Z770] at h1
      omega
    · have e : orbitZ z = Z1232 := orbitZ_eq_of_mem h
      have h1 := Set.ncard_le_ncard (e ▸ orbitZ_subset_of_inv hM hz) (Set.toFinite M)
      rw [ncard_Z1232] at h1
      omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_Z462]) (Set.toFinite _)

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)

@[expose] def labPerm : Equiv.Perm Y :=
  slicePerm act lab Y H.slice.mapsTo ⟨lab x, lab_mem_sliceGroup H.mem.1⟩

theorem coe_labPerm (v : Y) : (H.labPerm v : V) = act (lab x) v := rfl

theorem labPerm_mul_self : H.labPerm * H.labPerm = 1 := by
  refine Equiv.ext fun v => Subtype.ext ?_
  change act (lab x) (act (lab x) v) = v
  rw [← Equiv.Perm.mul_apply, ← map_mul, H.slice.lab_mul_self H.mem.1, map_one,
    Equiv.Perm.one_apply]

variable {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
include H hΦ

theorem phi_clique (z : C) : Φ ⟨z, H.clique.1.1 z.2⟩ = Sum.inl (η z) := hΦ.clique z _ rfl

theorem phi_omega (r : Subgroup.closure (lab '' C)) :
    Φ ⟨act (r : S) x, (H.act_mem_omega r).1⟩ = Sum.inr (Sum.inl (φ (Additive.ofMul r))) :=
  hΦ.omega r _ rfl

theorem phi_base : Φ ⟨x, H.mem.1⟩ = o := by
  rw [hΦ.omega 1 ⟨x, H.mem.1⟩ (by rw [Subgroup.coe_one, map_one, Equiv.Perm.one_apply]),
    ofMul_one, map_zero]
  rfl

theorem kF_smul_phi (g : CFSG.Blueprint.NativeSporadic.M22) (v : Y) :
    kF g • Φ v = Φ ⟨act (H.fixLift g : S) v, H.slice.mapsTo _ (H.fixLift g).2.1 v v.2⟩ := by
  rw [hΦ.equivariant (H.fixLift g) v
    ⟨act (H.fixLift g : S) v, H.slice.mapsTo _ (H.fixLift g).2.1 v v.2⟩ rfl,
    H.alpha_fix _ (H.fixLift_fix g), H.theta_fixLift]

theorem exists_phi_eq_inr_inr {v : Y} (hvC : (v : V) ∉ C)
    (hvΩ : (v : V) ∉ hexadFiber lab Y C ∅) : ∃ z, Φ v = Sum.inr (Sum.inr z) := by
  rcases h : Φ v with i | w | z
  · obtain ⟨a, rfl⟩ := η.surjective i
    have h1 := H.phi_clique hΦ a
    rw [← h] at h1
    have h2 := congrArg Subtype.val (Φ.injective h1)
    exact absurd (h2 ▸ a.2) hvC
  · have h1 := H.phi_omega hΦ (Additive.toMul (φ.symm w))
    rw [ofMul_toMul, LinearEquiv.apply_symm_apply, ← h] at h1
    have h2 := congrArg Subtype.val (Φ.injective h1)
    exact absurd (h2 ▸ H.act_mem_omega _) hvΩ
  · exact ⟨z, rfl⟩

theorem symm_inr_inr_not_mem_clique (z : Z) :
    ((Φ.symm (Sum.inr (Sum.inr z)) : Y) : V) ∉ C := by
  intro h
  have h1 := H.phi_clique hΦ ⟨_, h⟩
  rw [Subtype.coe_eta, Equiv.apply_symm_apply] at h1
  exact Sum.inr_ne_inl h1

theorem symm_inr_inr_not_mem_omega (z : Z) :
    ((Φ.symm (Sum.inr (Sum.inr z)) : Y) : V) ∉ hexadFiber lab Y C ∅ := by
  intro h
  obtain ⟨r, hr⟩ := H.exists_closure_act_eq h
  have h1 := hΦ.omega r _ hr.symm
  rw [Equiv.apply_symm_apply] at h1
  exact Sum.inr_ne_inl (Sum.inr_injective h1)

omit hΦ in
theorem permCongr_phi (v : Y) : Φ.permCongr H.labPerm (Φ v) = Φ (H.labPerm v) := by
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem permCongr_kF (g : CFSG.Blueprint.NativeSporadic.M22) (y : CFSG.Monster.B.Fischer.Y) :
    Φ.permCongr H.labPerm (kF g • y) = kF g • Φ.permCongr H.labPerm y := by
  obtain ⟨v, rfl⟩ := Φ.surjective y
  rw [H.kF_smul_phi hΦ g v, H.permCongr_phi, H.permCongr_phi, H.kF_smul_phi hΦ g]
  congr 1
  apply Subtype.ext
  change act (lab x) (act (H.fixLift g : S) v) = act (H.fixLift g : S) (act (lab x) v)
  rw [← Equiv.Perm.mul_apply, ← map_mul,
    (H.slice.commute_lab_of_act_eq (H.fixLift_fix g)).eq, map_mul, Equiv.Perm.mul_apply]

omit hΦ in
theorem permCongr_permCongr (y : CFSG.Monster.B.Fischer.Y) :
    Φ.permCongr H.labPerm (Φ.permCongr H.labPerm y) = y := by
  obtain ⟨v, rfl⟩ := Φ.surjective y
  rw [H.permCongr_phi, H.permCongr_phi, ← Equiv.Perm.mul_apply, H.labPerm_mul_self,
    Equiv.Perm.one_apply]

theorem permCongr_inl (a : C) :
    Φ.permCongr H.labPerm (Sum.inl (η a)) = Sum.inr (Sum.inl (coordImg (η a))) := by
  rw [← H.phi_clique hΦ a, H.permCongr_phi]
  have h : (H.labPerm ⟨a, H.clique.1.1 a.2⟩ : V) =
      act ((cliqueGen a : Subgroup.closure (lab '' C)) : S) x :=
    H.slice.act_lab_eq_act_lab H.clique H.mem a.2
  rw [hΦ.omega (cliqueGen a) _ h, H.gen]
  rfl

theorem permCongr_coordImg (a : C) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inl (coordImg (η a)))) = Sum.inl (η a) := by
  rw [← H.permCongr_inl hΦ a, H.permCongr_permCongr]

theorem permCongr_o : Φ.permCongr H.labPerm o = o := by
  rw [← H.phi_base hΦ, H.permCongr_phi]
  congr 1
  exact Subtype.ext ((H.slice.act_lab_eq_iff H.mem.1 H.mem.1).2 (Commute.refl _))

theorem phi_conj_fix (k : setStab act lab Y C) (hk : act (k : S) x = x)
    (r : Subgroup.closure (lab '' C))
    (h : (k : S) * r * (k : S)⁻¹ ∈ Subgroup.closure (lab '' C)) :
    φ (Additive.ofMul ⟨(k : S) * r * (k : S)⁻¹, h⟩) = rhoW (θ k) (φ (Additive.ofMul r)) := by
  have h1 := hΦ.equivariant k ⟨act (r : S) x, (H.act_mem_omega r).1⟩
    ⟨act ((⟨(k : S) * r * (k : S)⁻¹, h⟩ : Subgroup.closure (lab '' C)) : S) x,
      (H.act_mem_omega _).1⟩ (act_act_eq_conj hk r).symm
  rw [H.phi_omega hΦ, H.phi_omega hΦ, H.alpha_fix k hk, smul_inr_inl_eq] at h1
  rw [Sum.inl_injective (Sum.inr_injective h1)]
  change Multiplicative.toAdd (1 : Multiplicative W₀) + rhoW (θ k) _ = _
  rw [toAdd_one, zero_add]

theorem rhoW_mem_layer {i : ℕ} {w : W₀}
    (hw : ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C i ∧
      φ (Additive.ofMul r) = w) (g : CFSG.Blueprint.NativeSporadic.M22) :
    ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C i ∧
      φ (Additive.ofMul r) = rhoW g w := by
  obtain ⟨r, hr, rfl⟩ := hw
  have hkC : ∀ z ∈ C, act (H.fixLift g : S) z ∈ C := fun z hz => ((H.fixLift g).2.2 z).2 hz
  have h := conj_mem_closure H.slice.lab_act hkC r r.2
  refine ⟨⟨_, h⟩, conj_mem_labelLayer H.slice.lab_act (H.fixLift g).2 hr, ?_⟩
  rw [H.phi_conj_fix hΦ _ (H.fixLift_fix g) r h, H.theta_fixLift]

omit hΦ in
theorem phi_cliqueGen (a : C) : φ (Additive.ofMul (cliqueGen a)) = coordImg (η a) := H.gen a

theorem layer_two_eq :
    {w : W₀ | ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C 2 ∧
      φ (Additive.ofMul r) = w} = Lw 2 := by
  have := finite_W₀
  set A := {w : W₀ | ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C 2 ∧
      φ (Additive.ofMul r) = w} with hA
  have hcardA : A.ncard = 231 := by
    have e : A = (fun r : Subgroup.closure (lab '' C) => φ (Additive.ofMul r)) ''
        {r | (r : S) ∈ labelLayer lab C 2} := by
      ext w
      simp only [hA, Set.mem_ofPred_eq, Set.mem_image]
    rw [e, Set.ncard_image_of_injective _ (fun a b h => Additive.ofMul.injective (φ.injective h) :
      Function.Injective fun r : Subgroup.closure (lab '' C) => φ (Additive.ofMul r))]
    have e2 : Subtype.val '' {r : Subgroup.closure (lab '' C) | (r : S) ∈ labelLayer lab C 2} =
        labelLayer lab C 2 := by
      ext s
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact hr
      · intro hs
        exact ⟨⟨s, H.ptStab_eq ▸ H.slice.labelLayer_subset H.clique 2 hs⟩, hs, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, e2,
      H.slice.ncard_labelLayer_two H.clique]
  have hsub : A ⊆ Lw 2 := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := hw
    rcases W₀_cover (φ (Additive.ofMul r)) with h0 | h1 | h2 | h3
    · exfalso
      have hr1 : r = 1 := Additive.ofMul.injective (φ.injective (by rw [h0, ofMul_one, map_zero]))
      rw [hr1] at hr
      have := eq_of_mem_labelLayer hr (by rw [labelLayer_zero]; rfl :
        ((1 : Subgroup.closure (lab '' C)) : S) ∈ labelLayer lab C 0)
      omega
    · exfalso
      rw [← range_coordImg] at h1
      obtain ⟨i, hi⟩ := h1
      have hr1 : r = cliqueGen (η.symm i) := by
        apply Additive.ofMul.injective
        apply φ.injective
        rw [H.phi_cliqueGen, Equiv.apply_symm_apply, hi]
      rw [hr1] at hr
      have h1' : ((cliqueGen (η.symm i) : Subgroup.closure (lab '' C)) : S) ∈ labelLayer lab C 1 :=
        by rw [H.slice.labelLayer_one H.clique]; exact ⟨_, (η.symm i).2, rfl⟩
      have := eq_of_mem_labelLayer hr h1'
      omega
    · exact h2
    · exfalso
      have hsub := Lw_three_subset_of_inv (M := A) (fun g w hw => H.rhoW_mem_layer hΦ hw g)
        ⟨r, hr, rfl⟩ h3
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [ncard_Lw_three, hcardA] at h1
      omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_Lw_two, hcardA]) (Set.toFinite _)

theorem exists_layer_three
    {w : W₀} (hw : w ∈ Lw 3) :
    ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C 3 ∧ φ (Additive.ofMul r) = w := by
  set r : Subgroup.closure (lab '' C) := Additive.toMul (φ.symm w) with hr
  have hrw : φ (Additive.ofMul r) = w := by rw [hr, ofMul_toMul, LinearEquiv.apply_symm_apply]
  obtain ⟨i, hi, hri⟩ := H.slice.exists_mem_labelLayer H.clique (H.mem_ptStab r)
  refine ⟨r, ?_, hrw⟩
  interval_cases i
  · exfalso
    rw [labelLayer_zero, Set.mem_singleton_iff] at hri
    have hr1 : r = 1 := Subtype.ext hri
    rw [hr1, ofMul_one, map_zero] at hrw
    exact not_mem_Lw zero_mem_L0 (by norm_num : (0 : ℕ) ≠ 3) (hrw ▸ hw)
  · exfalso
    rw [H.slice.labelLayer_one H.clique] at hri
    obtain ⟨a, ha, hra⟩ := hri
    have hr1 : r = cliqueGen ⟨a, ha⟩ := Subtype.ext hra.symm
    rw [hr1, H.phi_cliqueGen] at hrw
    exact not_mem_Lw (coordImg_mem _) (by norm_num : (1 : ℕ) ≠ 3) (hrw ▸ hw)
  · exfalso
    have h2 : w ∈ Lw 2 := H.layer_two_eq hΦ ▸ ⟨r, hri, hrw⟩
    exact not_mem_Lw h2 (by norm_num : (2 : ℕ) ≠ 3) hw
  · exact hri

theorem permCongr_L2
    {w : W₀} (hw : w ∈ Lw 2) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inl w)) = Sum.inr (Sum.inl w) := by
  rw [← H.layer_two_eq hΦ] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  rw [← H.phi_omega hΦ, H.permCongr_phi]
  congr 1
  exact Subtype.ext (H.slice.act_lab_eq_of_mem_labelLayer_two H.clique H.mem hr)

theorem permCongr_L3_ne
    {w : W₀} (hw : w ∈ Lw 3) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inl w)) ≠ Sum.inr (Sum.inl w) := by
  obtain ⟨r, hr, rfl⟩ := H.exists_layer_three hΦ hw
  rw [← H.phi_omega hΦ, H.permCongr_phi]
  intro h
  exact H.slice.act_lab_ne_of_mem_labelLayer_three H.clique H.mem hr
    (congrArg Subtype.val (Φ.injective h))

theorem nbrZ_eq :
    {z : Z | (sliceGraph lab Y).Adj x ((Φ.symm (Sum.inr (Sum.inr z)) : Y) : V)} =
    Z462 := by
  set ζ : Z → V := fun z => ((Φ.symm (Sum.inr (Sum.inr z)) : Y) : V) with hζ
  have hζinj : Function.Injective ζ := fun z z' h =>
    Sum.inr_injective (Sum.inr_injective (Φ.symm.injective (Subtype.ext h)))
  obtain ⟨_, -, -, hcov, -, -, -, -, -, -, -, -, -⟩ := H.slice.clique_hexad_fibers H.clique
  obtain ⟨_, -, -, -, -, -, hB6, -, h77, -⟩ := H.slice.clique_code_steiner_design H.clique
  set U := ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B with hU
  have hrange : Set.range ζ = U := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      have hvY : ζ z ∈ Y := (Φ.symm (Sum.inr (Sum.inr z))).2
      have hvC := H.symm_inr_inr_not_mem_clique hΦ z
      rcases H.slice.inter_neighborSet_eq_empty_or_mem H.clique hvC with h | h
      · exact absurd ⟨hvY, hvC, h⟩ (H.symm_inr_inr_not_mem_omega hΦ z)
      · exact Set.mem_iUnion₂.2 ⟨_, h, hvY, hvC, rfl⟩
    · intro hv
      obtain ⟨B, hB, hvB⟩ := Set.mem_iUnion₂.1 hv
      have hvΩ : v ∉ hexadFiber lab Y C ∅ := fun h => by
        have e := eq_of_mem_hexadFiber hvB h
        have h6 := (hB6 B hB).2
        rw [e, Set.ncard_empty] at h6
        exact absurd h6 (by decide)
      obtain ⟨z, hz⟩ := H.exists_phi_eq_inr_inr hΦ (v := ⟨v, hvB.1⟩) hvB.2.1 hvΩ
      refine ⟨z, ?_⟩
      simp only [hζ, ← hz, Equiv.symm_apply_apply]
  set M := {z : Z | (sliceGraph lab Y).Adj x (ζ z)} with hM
  have hinv : ∀ (g : CFSG.Blueprint.NativeSporadic.M22) z, z ∈ M → zK g z ∈ M := by
    intro g z hz
    have h1 := H.kF_smul_phi hΦ g (Φ.symm (Sum.inr (Sum.inr z)))
    rw [Equiv.apply_symm_apply, kF_smul_Z, eq_comm, ← Equiv.eq_symm_apply] at h1
    change (sliceGraph lab Y).Adj x ((Φ.symm (Sum.inr (Sum.inr (zK g z))) : Y) : V)
    rw [← h1]
    have h2 := (H.slice.adj_act_iff (H.fixLift g).2.1 x (ζ z)).2 hz
    rwa [H.fixLift_fix] at h2
  have hcard : M.ncard = 462 := by
    have e : M = ζ ⁻¹' ((sliceGraph lab Y).neighborSet x ∩ U) := by
      ext z
      simp only [hM, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
        SimpleGraph.mem_neighborSet]
      exact ⟨fun h => ⟨h, hrange ▸ ⟨z, rfl⟩⟩, fun h => h.1⟩
    rw [e, Set.ncard_preimage_of_injective_subset_range hζinj
      (hrange ▸ Set.inter_subset_right),
      IsFischerSlice.ncard_inter_biUnion_hexadFiber h77 (H.slice.finite.subset fun _ h => h.2.1)
        (fun B hB => H.slice.ncard_neighborSet_inter_hexadFiber H.clique H.mem hB)]
  exact eq_Z462_of_inv hinv hcard

theorem permCongr_Z462
    {z : Z} (hz : z ∈ Z462) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inr z)) = Sum.inr (Sum.inr z) := by
  rw [← H.nbrZ_eq hΦ] at hz
  rw [Equiv.permCongr_apply, ← Equiv.eq_symm_apply]
  apply Subtype.ext
  rw [H.coe_labPerm]
  exact (H.slice.act_lab_eq_iff H.mem.1 hz.2.1).2 hz.2.2.2

theorem permCongr_Z1232_ne
    {z : Z} (hz : z ∈ Z1232) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inr z)) ≠ Sum.inr (Sum.inr z) := by
  intro h
  rw [Equiv.permCongr_apply, ← Equiv.eq_symm_apply] at h
  set v := Φ.symm (Sum.inr (Sum.inr z))
  have hc := (H.slice.act_lab_eq_iff H.mem.1 v.2).1 (congrArg Subtype.val h)
  have hne : x ≠ (v : V) := by
    intro e
    have h1 := H.phi_base hΦ
    rw [show (⟨x, H.mem.1⟩ : Y) = v from Subtype.ext e, Equiv.apply_symm_apply] at h1
    exact Sum.inr_ne_inl (Sum.inr_injective h1)
  have hadj : z ∈ {z : Z | (sliceGraph lab Y).Adj x ((Φ.symm (Sum.inr (Sum.inr z)) : Y) : V)} :=
    ⟨H.mem.1, v.2, hne, hc⟩
  rw [H.nbrZ_eq hΦ] at hadj
  exact not_mem_Z1232_of_mem_Z462 hadj hz

end FullIntertwinerHyp

end CFSG.Monster.B.TwoA.Fischer

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

@[expose] def IsDirectPart
    (y : CFSG.Monster.B.Fischer.Y) : Prop :=
  (∃ i, y = Sum.inl i) ∨ (∃ w, (w = 0 ∨ w ∈ Lw 1 ∨ w ∈ Lw 2) ∧ y = Sum.inr (Sum.inl w)) ∨
    ∃ z ∈ Z462, y = Sum.inr (Sum.inr z)

theorem not_isDirectPart_inr_inl
    {w : W₀} (hw : w ∈ Lw 3) :
    ¬IsDirectPart (Sum.inr (Sum.inl w)) := by
  rintro (⟨i, h⟩ | ⟨w', hw', h⟩ | ⟨z, -, h⟩)
  · exact Sum.inr_ne_inl h
  · obtain rfl := Sum.inl_injective (Sum.inr_injective h)
    rcases hw' with rfl | h1 | h2
    · exact not_mem_Lw zero_mem_L0 (by norm_num : (0 : ℕ) ≠ 3) hw
    · exact not_mem_Lw h1 (by norm_num : (1 : ℕ) ≠ 3) hw
    · exact not_mem_Lw h2 (by norm_num : (2 : ℕ) ≠ 3) hw
  · exact Sum.inl_ne_inr (Sum.inr_injective h)

theorem not_isDirectPart_inr_inr
    {z : Z} (hz : z ∉ Z462) :
    ¬IsDirectPart (Sum.inr (Sum.inr z)) := by
  rintro (⟨i, h⟩ | ⟨w', -, h⟩ | ⟨z', hz', h⟩)
  · exact Sum.inr_ne_inl h
  · exact Sum.inr_ne_inl (Sum.inr_injective h)
  · obtain rfl := Sum.inr_injective (Sum.inr_injective h)
    exact hz hz'

theorem of_not_isDirectPart
    {y : CFSG.Monster.B.Fischer.Y} (h : ¬IsDirectPart y) :
    (∃ w ∈ Lw 3, y = Sum.inr (Sum.inl w)) ∨ ∃ z, (z ∈ Z770 ∨ z ∈ Z1232) ∧
      y = Sum.inr (Sum.inr z) := by
  rcases y with i | w | z
  · exact absurd (Or.inl ⟨i, rfl⟩) h
  · rcases W₀_cover w with h0 | h1 | h2 | h3
    · exact absurd (Or.inr (Or.inl ⟨w, Or.inl h0, rfl⟩)) h
    · exact absurd (Or.inr (Or.inl ⟨w, Or.inr (Or.inl h1), rfl⟩)) h
    · exact absurd (Or.inr (Or.inl ⟨w, Or.inr (Or.inr h2), rfl⟩)) h
    · exact Or.inl ⟨w, h3, rfl⟩
  · rcases Z_cover z with h4 | h7 | h12
    · exact absurd (Or.inr (Or.inr ⟨z, h4, rfl⟩)) h
    · exact Or.inr ⟨z, Or.inl h7, rfl⟩
    · exact Or.inr ⟨z, Or.inr h12, rfl⟩

theorem natCard_Z1232T :
    Nat.card Z1232T = 1232 := by
  rw [Nat.card_coe_set_eq, ncard_Z1232]

theorem finite_L3 :
    Finite L3 := Nat.finite_of_card_ne_zero (by rw [natCard_L3]; norm_num)

theorem finite_Z1232T :
    Finite Z1232T :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Z1232T]; norm_num)

theorem kZ12_mul
    (g g' : CFSG.Blueprint.NativeSporadic.M22) (z : Z1232T) :
    kZ12 (g * g') z = kZ12 g (kZ12 g' z) :=
  Subtype.ext (zK_mul g g' z)

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
  {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
include H hΦ

theorem isDirectPart_permCongr
    {y : CFSG.Monster.B.Fischer.Y} (hy : IsDirectPart y) :
    IsDirectPart (Φ.permCongr H.labPerm y) := by
  rcases hy with ⟨i, rfl⟩ | ⟨w, hw, rfl⟩ | ⟨z, hz, rfl⟩
  · obtain ⟨a, rfl⟩ := η.surjective i
    rw [H.permCongr_inl hΦ a]
    exact Or.inr (Or.inl ⟨_, Or.inr (Or.inl (coordImg_mem _)), rfl⟩)
  · rcases hw with rfl | h1 | h2
    · rw [show (Sum.inr (Sum.inl 0) : CFSG.Monster.B.Fischer.Y) = o from rfl, H.permCongr_o hΦ]
      exact Or.inr (Or.inl ⟨0, Or.inl rfl, rfl⟩)
    · rw [← range_coordImg] at h1
      obtain ⟨i, rfl⟩ := h1
      obtain ⟨a, rfl⟩ := η.surjective i
      rw [H.permCongr_coordImg hΦ a]
      exact Or.inl ⟨_, rfl⟩
    · rw [H.permCongr_L2 hΦ h2]
      exact Or.inr (Or.inl ⟨w, Or.inr (Or.inr h2), rfl⟩)
  · rw [H.permCongr_Z462 hΦ hz]
    exact Or.inr (Or.inr ⟨z, hz, rfl⟩)

theorem not_isDirectPart_permCongr
    {y : CFSG.Monster.B.Fischer.Y} (hy : ¬IsDirectPart y) :
    ¬IsDirectPart (Φ.permCongr H.labPerm y) := fun h => by
  have h1 := H.isDirectPart_permCongr hΦ h
  rw [H.permCongr_permCongr] at h1
  exact hy h1

theorem permCongr_kL (g : CFSG.Blueprint.NativeSporadic.M22) (w : L3) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inl ((kL g w : L3) : W₀))) =
      kF g • Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w : W₀))) := by
  rw [← H.permCongr_kF hΦ g, kF_smul_W]
  rfl

theorem permCongr_kZ12 (g : CFSG.Blueprint.NativeSporadic.M22) (z : Z1232T) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inr ((kZ12 g z : Z1232T) : Z))) =
      kF g • Φ.permCongr H.labPerm (Sum.inr (Sum.inr (z : Z))) := by
  rw [← H.permCongr_kF hΦ g, kF_smul_Z]
  rfl

theorem permCongr_L3
    (w : L3) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w : W₀))) = Sum.inr (Sum.inr (sigmaEquiv w : Z)) := by
  have := finite_L3
  have hnd := H.not_isDirectPart_permCongr hΦ (not_isDirectPart_inr_inl w7.2)
  rcases of_not_isDirectPart hnd with ⟨w', hw', he⟩ | ⟨z, hz, he⟩
  · exfalso
    have hall : ∀ w : L3, ∃ w'' ∈ Lw 3,
        Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w : W₀))) = Sum.inr (Sum.inl w'') := by
      intro w
      obtain ⟨g, rfl⟩ := L3_transitive w
      exact ⟨rhoW g w', rhoW_mem_Lw g hw', by rw [H.permCongr_kL hΦ, he, kF_smul_W]⟩
    choose c hc hcw using hall
    let c' : L3 → L3 := fun w => ⟨c w, hc w⟩
    have hinj : Function.Injective c' := by
      intro w₁ w₂ h
      have e : c w₁ = c w₂ := congrArg Subtype.val h
      have e2 : Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w₁ : W₀))) =
          Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w₂ : W₀))) := by rw [hcw, hcw, e]
      exact Subtype.ext (Sum.inl_injective (Sum.inr_injective
        ((Φ.permCongr H.labPerm).injective e2)))
    let cP : Equiv.Perm L3 := Equiv.ofBijective c' hinj.bijective_of_finite
    have hcomm : ∀ g w, cP (kL g w) = kL g (cP w) := by
      intro g w
      apply Subtype.ext
      have h1 := H.permCongr_kL hΦ g w
      rw [hcw, hcw, kF_smul_W] at h1
      exact Sum.inl_injective (Sum.inr_injective h1)
    have h1 : cP w7 = w7 := by rw [centralizer_L3 hcomm]; rfl
    apply H.permCongr_L3_ne hΦ w7.2
    rw [hcw]
    exact congrArg (fun u : L3 => (Sum.inr (Sum.inl (u : W₀)) : CFSG.Monster.B.Fischer.Y)) h1
  · rcases hz with hz7 | hz12
    · have hall : ∀ w : L3, ∃ z'' ∈ Z770,
          Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w : W₀))) = Sum.inr (Sum.inr z'') := by
        intro w
        obtain ⟨g, rfl⟩ := L3_transitive w
        exact ⟨zK g z, zK_mem_orbitZ g hz7, by rw [H.permCongr_kL hΦ, he, kF_smul_Z]⟩
      choose s hs hsw using hall
      let s' : L3 → Z770T := fun w => ⟨s w, hs w⟩
      have hequiv : ∀ g w, s' (kL g w) = kZ7 g (s' w) := by
        intro g w
        apply Subtype.ext
        have h1 := H.permCongr_kL hΦ g w
        rw [hsw, hsw, kF_smul_Z] at h1
        exact Sum.inr_injective (Sum.inr_injective h1)
      have h1 := congrFun (eq_sigmaL hequiv) w
      rw [hsw]
      exact congrArg (fun u : Z770T => (Sum.inr (Sum.inr (u : Z)) : CFSG.Monster.B.Fischer.Y)) h1
    · exfalso
      have := finite_Z1232T
      have hall : ∀ w : L3, ∃ z'' ∈ Z1232,
          Φ.permCongr H.labPerm (Sum.inr (Sum.inl (w : W₀))) = Sum.inr (Sum.inr z'') := by
        intro w
        obtain ⟨g, rfl⟩ := L3_transitive w
        exact ⟨zK g z, zK_mem_orbitZ g hz12, by rw [H.permCongr_kL hΦ, he, kF_smul_Z]⟩
      choose d hd hdw using hall
      let d' : L3 → Z1232T := fun w => ⟨d w, hd w⟩
      have hequiv : ∀ g w, d' (kL g w) = kZ12 g (d' w) := by
        intro g w
        apply Subtype.ext
        have h1 := H.permCongr_kL hΦ g w
        rw [hdw, hdw, kF_smul_Z] at h1
        exact Sum.inr_injective (Sum.inr_injective h1)
      have hsurj : Function.Surjective d' := by
        intro z''
        obtain ⟨g, rfl⟩ := Z1232_transitive z''
        obtain ⟨g₀, hg₀⟩ := Z1232_transitive (d' w7)
        refine ⟨kL (g * g₀⁻¹) w7, ?_⟩
        rw [hequiv, ← hg₀, ← kZ12_mul, inv_mul_cancel_right]
      have h1 := Nat.card_le_card_of_surjective d' hsurj
      rw [natCard_Z1232T, natCard_L3] at h1
      omega

theorem permCongr_sigma
    (w : L3) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inr (sigmaEquiv w : Z))) = Sum.inr (Sum.inl (w : W₀)) := by
  rw [← H.permCongr_L3 hΦ w, H.permCongr_permCongr]

theorem permCongr_Z1232
    (z : Z1232T) :
    Φ.permCongr H.labPerm (Sum.inr (Sum.inr (z : Z))) = Sum.inr (Sum.inr (tauPerm z : Z)) := by
  have := finite_Z1232T
  have hall : ∀ z : Z1232T, ∃ z'' ∈ Z1232,
      Φ.permCongr H.labPerm (Sum.inr (Sum.inr (z : Z))) = Sum.inr (Sum.inr z'') := by
    intro z
    have hz462 : (z : Z) ∉ Z462 := fun h => not_mem_Z1232_of_mem_Z462 h z.2
    have hnd := H.not_isDirectPart_permCongr hΦ (not_isDirectPart_inr_inr hz462)
    rcases of_not_isDirectPart hnd with ⟨w, hw, he⟩ | ⟨z'', hz'', he⟩
    · exfalso
      have h1 := congrArg (Φ.permCongr H.labPerm) he
      rw [H.permCongr_permCongr, H.permCongr_L3 hΦ ⟨w, hw⟩] at h1
      have h2 : (z : Z) = (sigmaEquiv ⟨w, hw⟩ : Z) := Sum.inr_injective (Sum.inr_injective h1)
      exact not_mem_Z770_of_mem_Z1232 z.2 (h2 ▸ (sigmaEquiv ⟨w, hw⟩).2)
    · rcases hz'' with h7 | h12
      · exfalso
        obtain ⟨w', hw'⟩ := sigmaEquiv.surjective ⟨z'', h7⟩
        have h1 := H.permCongr_L3 hΦ w'
        rw [hw', ← he] at h1
        exact Sum.inl_ne_inr (Sum.inr_injective ((Φ.permCongr H.labPerm).injective h1))
      · exact ⟨z'', h12, he⟩
  choose c hc hcz using hall
  let c' : Z1232T → Z1232T := fun z => ⟨c z, hc z⟩
  have hinj : Function.Injective c' := by
    intro z₁ z₂ h
    have e : c z₁ = c z₂ := congrArg Subtype.val h
    have e2 : Φ.permCongr H.labPerm (Sum.inr (Sum.inr (z₁ : Z))) =
        Φ.permCongr H.labPerm (Sum.inr (Sum.inr (z₂ : Z))) := by rw [hcz, hcz, e]
    exact Subtype.ext (Sum.inr_injective (Sum.inr_injective
      ((Φ.permCongr H.labPerm).injective e2)))
  let cP : Equiv.Perm Z1232T := Equiv.ofBijective c' hinj.bijective_of_finite
  have hcomm : ∀ g z, cP (kZ12 g z) = kZ12 g (cP z) := by
    intro g z
    apply Subtype.ext
    have h1 := H.permCongr_kZ12 hΦ g z
    rw [hcz, hcz, kF_smul_Z] at h1
    exact Sum.inr_injective (Sum.inr_injective h1)
  rcases centralizer_Z1232 hcomm with h1 | h1
  · exfalso
    have h2 : cP z1 = z1 := by rw [h1]; rfl
    apply H.permCongr_Z1232_ne hΦ z1.2
    rw [hcz]
    exact congrArg (fun u : Z1232T => (Sum.inr (Sum.inr (u : Z)) : CFSG.Monster.B.Fischer.Y)) h2
  · rw [hcz]
    have h2 : cP z = tauPerm z := by rw [h1]
    exact congrArg (fun u : Z1232T => (Sum.inr (Sum.inr (u : Z)) : CFSG.Monster.B.Fischer.Y)) h2

theorem permCongr_labPerm :
    Φ.permCongr H.labPerm = tPerm := by
  refine Equiv.ext fun y => ?_
  rw [tPerm_apply]
  rcases y with i | w | z
  · obtain ⟨a, rfl⟩ := η.surjective i
    rw [H.permCongr_inl hΦ a, tFun_inl]
  · rcases W₀_cover w with rfl | h1 | h2 | h3
    · rw [show (Sum.inr (Sum.inl 0) : CFSG.Monster.B.Fischer.Y) = o from rfl, H.permCongr_o hΦ]
      exact (tFun_fixW (not_mem_Lw zero_mem_L0 (by norm_num)) (not_mem_Lw zero_mem_L0
        (by norm_num))).symm
    · have h1' := h1
      rw [← range_coordImg] at h1'
      obtain ⟨i, rfl⟩ := h1'
      obtain ⟨a, rfl⟩ := η.surjective i
      rw [H.permCongr_coordImg hΦ a, tFun_L1 h1, l1Equiv_symm_coordImg]
    · rw [H.permCongr_L2 hΦ h2,
        tFun_fixW (not_mem_Lw h2 (by norm_num)) (not_mem_Lw h2 (by norm_num))]
    · rw [tFun_L3 h3]
      exact H.permCongr_L3 hΦ ⟨w, h3⟩
  · rcases Z_cover z with h | h | h
    · rw [H.permCongr_Z462 hΦ h,
        tFun_fixZ (not_mem_Z770_of_mem_Z462 h) (not_mem_Z1232_of_mem_Z462 h)]
    · obtain ⟨w, hw⟩ := sigmaEquiv.surjective ⟨z, h⟩
      have e : z = (sigmaEquiv w : Z) := by rw [hw]
      have e2 : sigmaEquiv.symm ⟨z, h⟩ = w := by rw [← hw, Equiv.symm_apply_apply]
      rw [tFun_Z770 h, e2]
      subst e
      exact H.permCongr_sigma hΦ w
    · rw [tFun_Z1232 h]
      exact H.permCongr_Z1232 hΦ ⟨z, h⟩

end FullIntertwinerHyp

end CFSG.Monster.B.TwoA.Fischer
