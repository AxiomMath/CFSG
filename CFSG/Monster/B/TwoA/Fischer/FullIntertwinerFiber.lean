module

public import CFSG.Monster.B.TwoA.Fischer.AffineCayley
public import CFSG.Monster.B.Fischer.InducedEncodingBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

theorem wF_mul_kF
    (r : W₀) (k : CFSG.Blueprint.NativeSporadic.M22) :
    wF r * kF k = (⟨Multiplicative.ofAdd r, k⟩ : F₀) :=
  SemidirectProduct.inl_left_mul_inr_right (⟨Multiplicative.ofAdd r, k⟩ : F₀)

theorem smul_inl_eq
    (g : F₀) (i : X₀) :
    g • (Sum.inl i : CFSG.Monster.B.Fischer.Y) = Sum.inl (psiX g.right i) := rfl

theorem smul_inr_inl_eq
    (g : F₀) (u : W₀) :
    g • (Sum.inr (Sum.inl u) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inl (Multiplicative.toAdd g.left + rhoW g.right u)) := rfl

theorem smul_inr_inr_eq
    (g : F₀) (z : Z) :
    g • (Sum.inr (Sum.inr z) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inr (zW (Multiplicative.toAdd g.left) (zK g.right z))) := rfl

theorem hexadOf_zW
    (r : W₀) (z : Z) : hexadOf (zW r z) = hexadOf z := by
  obtain ⟨l, q, rfl⟩ := zMk_surj z
  rfl

theorem zMk_one_injective :
    Function.Injective (zMk 1) := by
  intro q q' h
  obtain ⟨g, h1, h2⟩ := zMk_eq_iff.1 h
  have hg : g = 1 := Subtype.ext (by simpa using h1.symm)
  subst hg
  simpa using h2.symm

theorem hexadOf_zMk_one
    (q : Q₀) : hexadOf (zMk 1 q) = B₀ := by
  rw [hexadOf_zMk, Subgroup.coe_one, map_one, map_perm_one]

theorem exists_eq_zMk_one
    {z : Z} (hz : hexadOf z = B₀) : ∃ q, z = zMk 1 q := by
  obtain ⟨k, q, rfl⟩ := zMk_surj z
  have hk : k ∈ KB := hz
  refine ⟨affA ⟨k, hk⟩ q, ?_⟩
  rw [← zMk_mul, one_mul]

theorem zMk_eq_zMk_one
    {k : CFSG.Blueprint.NativeSporadic.M22} (hk : k ∈ KB) (q : Q₀) :
    zMk k q = zMk 1 (affA ⟨k, hk⟩ q) := by
  rw [← zMk_mul, one_mul]

theorem wF_mul_kF_smul_zMk_one
    (r : W₀) (k : CFSG.Blueprint.NativeSporadic.M22) (q : Q₀) :
    (wF r * kF k) • (Sum.inr (Sum.inr (zMk 1 q)) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inr (zMk k (q + U₀.mkQ (rhoW k⁻¹ r)))) := by
  rw [wF_mul_kF, smul_inr_inr_eq]
  simp only [toAdd_ofAdd, zK_mk, zW_mk, mul_one]

theorem wF_smul_zMk_one
    (r : W₀) (q : Q₀) :
    wF r • (Sum.inr (Sum.inr (zMk 1 q)) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inr (zMk 1 (q + U₀.mkQ r))) := by
  have h := wF_mul_kF_smul_zMk_one r 1 q
  rw [show kF 1 = 1 from map_one SemidirectProduct.inr, mul_one] at h
  rw [h, inv_one, map_one, Module.End.one_apply]

theorem kF_smul_zMk_one
    {g : CFSG.Blueprint.NativeSporadic.M22} (hg : g ∈ KB) (q : Q₀) :
    kF g • (Sum.inr (Sum.inr (zMk 1 q)) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inr (zMk 1 (affA ⟨g, hg⟩ q))) := by
  have e := wF_mul_kF_smul_zMk_one 0 g q
  rw [show wF 0 = 1 by rw [wF, ofAdd_zero, map_one], one_mul] at e
  rw [e, map_zero, map_zero, add_zero, zMk_eq_zMk_one hg]

section OrbitMap

variable {G P P' : Type*} [Group G] (a : G →* Equiv.Perm P) (b : G →* Equiv.Perm P')
  (p₀ : P) (p₀' : P')

open _root_.Classical in
@[expose] def orbitTransport (p : P) : P' :=
  if h : ∃ g, a g p₀ = p then b h.choose p₀' else p₀'

variable {a b p₀ p₀'}

theorem orbitTransport_apply (hstab : ∀ g, a g p₀ = p₀ → b g p₀' = p₀') (g : G) :
    orbitTransport a b p₀ p₀' (a g p₀) = b g p₀' := by
  have h : ∃ g', a g' p₀ = a g p₀ := ⟨g, rfl⟩
  rw [orbitTransport, dite_eq_left h]
  have e : a (g⁻¹ * h.choose) p₀ = p₀ := by
    rw [map_mul, Equiv.Perm.mul_apply, h.choose_spec, map_inv, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply]
  have e' := hstab _ e
  rw [map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq] at e'
  exact e'

theorem act_eq_of_orbit_eq (hstab : ∀ g, b g p₀' = p₀' → a g p₀ = p₀) {g g' : G}
    (h : b g p₀' = b g' p₀') : a g p₀ = a g' p₀ := by
  have e : b (g'⁻¹ * g) p₀' = p₀' := by
    rw [map_mul, Equiv.Perm.mul_apply, h, map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have e' := hstab _ e
  rw [map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.inv_eq_iff_eq] at e'
  exact e'

end OrbitMap

theorem finite_Q₀ : Finite Q₀ := Nat.finite_of_card_ne_zero (by rw [natCard_Q₀]; norm_num)

theorem affOrbit_subset {A : KB →* Equiv.Perm Q₀} {M : Set Q₀} (hM : ∀ h q, q ∈ M → A h q ∈ M)
    {q₀ q : Q₀} (hq : q ∈ M) (hq₀ : q ∈ affOrbit A q₀) : affOrbit A q₀ ⊆ M := by
  obtain ⟨k, rfl⟩ := hq₀
  rintro _ ⟨k', rfl⟩
  show A k' q₀ ∈ M
  have e : A k' q₀ = A (k' * k⁻¹) (A k q₀) := by
    rw [map_mul, Equiv.Perm.mul_apply, map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [e]
  exact hM _ _ hq

theorem ncard_ne_six_of_affLin
    {M : Set Q₀} (hM : ∀ h q, q ∈ M → affLin h q ∈ M) :
    M.ncard ≠ 6 := by
  have := finite_Q₀
  obtain ⟨h0, h3, h1, hcov⟩ := affOrbits_affLin
  intro h6
  by_cases hm1 : ∃ q ∈ M, q ∈ affOrbit affLin (qv 1)
  · obtain ⟨q, hq, hq1⟩ := hm1
    have := Set.ncard_le_ncard (affOrbit_subset hM hq hq1) (Set.toFinite M)
    omega
  by_cases hm3 : ∃ q ∈ M, q ∈ affOrbit affLin (qv 3)
  · obtain ⟨q, hq, hq3⟩ := hm3
    have := Set.ncard_le_ncard (affOrbit_subset hM hq hq3) (Set.toFinite M)
    omega
  have hsub : M ⊆ affOrbit affLin (qv 0) := by
    intro q hq
    rcases hcov q with h | h | h
    · exact h
    · exact absurd ⟨q, hq, h⟩ hm3
    · exact absurd ⟨q, hq, h⟩ hm1
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem coe_eq_of_eq_mul {C : Set V} {f k : setStab act lab Y C} {r : S}
    (hr : r ∈ ptStab act lab Y C) (h : (f : S) = r * k) :
    (f : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C)) = k := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : ((f⁻¹ * k : setStab act lab Y C) : S) = (k : S)⁻¹ * r⁻¹ * ((k : S)⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h]
    group
  rw [e]
  exact conj_mem_ptStab ((setStab act lab Y C).inv_mem k.2) ((ptStab act lab Y C).inv_mem hr)

theorem image_eq_of_eq_mul {C : Set V} {f k : S} {r : S} (hr : r ∈ ptStab act lab Y C)
    (hk : k ∈ setStab act lab Y C) (h : f = r * k) {D : Set V} (hD : D ⊆ C) :
    act f '' D = act k '' D := by
  refine Set.image_congr fun z hz => ?_
  rw [h, map_mul, Equiv.Perm.mul_apply]
  exact hr.2 _ ((hk.2 z).2 (hD hz))

variable (act lab Y) in
structure FullIntertwinerHyp
    (C : Set V) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (x : V) (η : C ≃ X₀)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22)
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀) (α : setStab act lab Y C →* F₀) :
    Prop where
  slice : IsFischerSlice act lab Y
  clique : IsSliceMaxClique lab Y C
  mem : x ∈ hexadFiber lab Y C ∅
  blocks : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
    T.image (fun z => (η z : Fin 24)) ∈ ℬ₀
  perm : ∀ (f : setStab act lab Y C) (z : C),
    (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z)
  gen : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))
  alpha : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
    (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k)

open _root_.Classical in
@[expose] def fibCoord (act : S →* Equiv.Perm V) {C : Set V}
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀) (y₀ v : V) : Q₀ :=
  if h : ∃ r : Subgroup.closure (lab '' C), act (r : S) y₀ = v then
    U₀.mkQ (φ (Additive.ofMul h.choose)) else 0

variable (act lab Y) in
@[expose] def IsAffOrigin
    {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22)
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀) (x y₀ : V) (B : Set V)
    (t : Q₀) : Prop :=
  ∀ (k : setStab act lab Y C) (hk : θ k ∈ KB), act (k : S) x = x →
    ∀ v ∈ hexadFiber lab Y C B,
      fibCoord act φ y₀ (act (k : S) v) + t = affA ⟨θ k, hk⟩ (fibCoord act φ y₀ v + t)

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
include H

theorem ptStab_eq : ptStab act lab Y C = Subgroup.closure (lab '' C) :=
  H.slice.ptStab_eq_closure_of_isSliceMaxClique H.clique

theorem mem_ptStab (r : Subgroup.closure (lab '' C)) : (r : S) ∈ ptStab act lab Y C := by
  rw [H.ptStab_eq]
  exact r.2

theorem mem_setStab (r : Subgroup.closure (lab '' C)) : (r : S) ∈ setStab act lab Y C :=
  ptStab_le_setStab C (H.mem_ptStab r)

theorem exists_eq_mul_fix (f : setStab act lab Y C) :
    ∃ (r : Subgroup.closure (lab '' C)) (k : setStab act lab Y C),
      (f : S) = r * k ∧ act (k : S) x = x := by
  obtain ⟨r, ⟨hr, hrx⟩, -⟩ :=
    H.slice.existsUnique_act_eq H.clique H.mem (H.slice.act_mem_hexadFiber_empty f.2 H.mem)
  have hr' : r ∈ Subgroup.closure (lab '' C) := H.ptStab_eq ▸ hr
  refine ⟨⟨r, hr'⟩, ⟨r⁻¹ * f, (setStab act lab Y C).mul_mem
    ((setStab act lab Y C).inv_mem (ptStab_le_setStab C hr)) f.2⟩, ?_, ?_⟩
  · change (f : S) = r * (r⁻¹ * f)
    group
  · change act (r⁻¹ * f) x = x
    rw [map_mul, Equiv.Perm.mul_apply, ← hrx, act_inv_act]

theorem alpha_right (f : setStab act lab Y C) : (α f).right = θ f := by
  obtain ⟨r, k, hf, hk⟩ := H.exists_eq_mul_fix f
  rw [H.alpha r f k hf hk, wF_mul_kF, coe_eq_of_eq_mul (H.mem_ptStab r) hf]

theorem alpha_closure (r : Subgroup.closure (lab '' C)) (f : setStab act lab Y C)
    (h : (f : S) = r) : α f = wF (φ (Additive.ofMul r)) := by
  rw [H.alpha r f 1 (by rw [h, Subgroup.coe_one, mul_one])
    (by rw [Subgroup.coe_one, map_one, Equiv.Perm.one_apply]), QuotientGroup.mk_one, map_one,
    show kF 1 = 1 from map_one SemidirectProduct.inr, mul_one]

theorem alpha_fix (k : setStab act lab Y C) (hk : act (k : S) x = x) : α k = kF (θ k) := by
  rw [H.alpha 1 k k (by rw [Subgroup.coe_one, one_mul]) hk, ofMul_one, map_zero,
    show wF 0 = 1 by rw [wF, ofAdd_zero, map_one], one_mul]

theorem act_mem_omega (r : Subgroup.closure (lab '' C)) :
    act (r : S) x ∈ hexadFiber lab Y C ∅ :=
  H.slice.act_mem_hexadFiber (H.mem_ptStab r) H.mem

theorem exists_closure_act_eq {v : V} (hv : v ∈ hexadFiber lab Y C ∅) :
    ∃ r : Subgroup.closure (lab '' C), act (r : S) x = v := by
  obtain ⟨r, ⟨hr, hrx⟩, -⟩ := H.slice.existsUnique_act_eq H.clique H.mem hv
  exact ⟨⟨r, H.ptStab_eq ▸ hr⟩, hrx⟩

theorem eq_of_act_eq {r r' : Subgroup.closure (lab '' C)} (h : act (r : S) x = act (r' : S) x) :
    r = r' := by
  obtain ⟨s, -, hs⟩ := H.slice.existsUnique_act_eq H.clique H.mem (H.act_mem_omega r)
  exact Subtype.ext ((hs _ ⟨H.mem_ptStab r, rfl⟩).trans (hs _ ⟨H.mem_ptStab r', h.symm⟩).symm)

theorem exists_image_block_eq {B B' : Set V} (hB : B ∈ cliqueBlocks lab C)
    (hB' : B' ∈ cliqueBlocks lab C) : ∃ f ∈ setStab act lab Y C, act f '' B = B' := by
  obtain ⟨_, -, -, -, -, -, hB6, hT3, -⟩ := H.slice.clique_code_steiner_design H.clique
  obtain ⟨T, hTB, hT⟩ := Set.exists_subset_card_eq (s := B) (n := 3)
    (by rw [(hB6 B hB).2]; norm_num)
  obtain ⟨T', hTB', hT'⟩ := Set.exists_subset_card_eq (s := B') (n := 3)
    (by rw [(hB6 B' hB').2]; norm_num)
  obtain ⟨f, hf, hfT⟩ := H.slice.exists_setStab_image_eq H.clique (hTB.trans (hB6 B hB).1)
    (hTB'.trans (hB6 B' hB').1) (by rw [hT, hT']) (by rw [hT])
  refine ⟨f, hf, ?_⟩
  obtain ⟨B'', -, huniq⟩ := hT3 T' (hTB'.trans (hB6 B' hB').1) hT'
  have h1 := huniq _ ⟨image_mem_cliqueBlocks H.slice.lab_act (fun x hx => (hf.2 x).2 hx)
    (setStabPerm act lab Y C ⟨f, hf⟩) (fun _ => rfl) hB, hfT ▸ Set.image_mono hTB⟩
  have h2 := huniq _ ⟨hB', hTB'⟩
  rw [h1, h2]

theorem exists_act_eq_of_mem_hexadFiber {B B' : Set V} (hB : B ∈ cliqueBlocks lab C)
    (hB' : B' ∈ cliqueBlocks lab C) {y y' : V} (hy : y ∈ hexadFiber lab Y C B)
    (hy' : y' ∈ hexadFiber lab Y C B') : ∃ f ∈ setStab act lab Y C, act f y = y' := by
  obtain ⟨g, hg, hgB⟩ := H.exists_image_block_eq hB hB'
  have hgy : act g y ∈ hexadFiber lab Y C B' := by
    rw [← hgB, ← H.slice.image_hexadFiber hg]
    exact ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hry⟩ :=
    (H.slice.hexadFiber_of_mem_cliqueBlocks H.clique hB').2.1 _ hgy _ hy'
  refine ⟨r * g, (setStab act lab Y C).mul_mem (ptStab_le_setStab C hr) hg, ?_⟩
  rw [map_mul, Equiv.Perm.mul_apply, hry]

omit H [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem eq_of_mem_hexadFiber {B B' : Set V} {v : V} (h : v ∈ hexadFiber lab Y C B)
    (h' : v ∈ hexadFiber lab Y C B') : B = B' :=
  h.2.2.symm.trans h'.2.2

theorem bijective_fix : Function.Bijective (θ.toMonoidHom.comp
    ((QuotientGroup.mk' ((ptStab act lab Y C).subgroupOf (setStab act lab Y C))).comp
      (Subgroup.inclusion (inf_le_left : setStab act lab Y C ⊓ actStab act x ≤
        setStab act lab Y C)))) :=
  θ.bijective.comp ((H.slice.clique_split_regular H.clique).2.2 x H.mem).2.1

@[expose] def fixEquiv :
    ↥(setStab act lab Y C ⊓ actStab act x) ≃* CFSG.Blueprint.NativeSporadic.M22 :=
  MulEquiv.ofBijective _ H.bijective_fix

@[expose] def fixLift (g : CFSG.Blueprint.NativeSporadic.M22) : setStab act lab Y C :=
  Subgroup.inclusion inf_le_left (H.fixEquiv.symm g)

theorem fixLift_fix (g : CFSG.Blueprint.NativeSporadic.M22) :
    act (H.fixLift g : S) x = x :=
  (H.fixEquiv.symm g).2.2

theorem theta_fixLift (g : CFSG.Blueprint.NativeSporadic.M22) : θ (H.fixLift g) = g :=
  H.fixEquiv.apply_symm_apply g

theorem fixLift_theta (k : setStab act lab Y C) (hk : act (k : S) x = x) :
    H.fixLift (θ k) = k := by
  have e : H.fixEquiv ⟨k, k.2, hk⟩ = θ k := rfl
  apply Subtype.ext
  rw [fixLift, ← e, MulEquiv.symm_apply_apply]
  rfl

theorem fixLift_one : H.fixLift 1 = 1 := by
  apply Subtype.ext
  rw [fixLift, map_one]
  rfl

theorem fixLift_mul (g g' : CFSG.Blueprint.NativeSporadic.M22) :
    H.fixLift (g * g') = H.fixLift g * H.fixLift g' := by
  apply Subtype.ext
  rw [fixLift, map_mul]
  rfl

theorem finite_clique : Finite C := (H.slice.finite.subset H.clique.1.1).to_subtype

theorem exists_T₀ : ∃ T₀ : Finset C, T₀.image (fun z => (η z : Fin 24)) = B₀ := by
  have := H.finite_clique
  refine ⟨(Set.toFinite {z : C | (η z : Fin 24) ∈ B₀}).toFinset, ?_⟩
  ext i
  simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hi
    exact ⟨η.symm ⟨i, B₀_subset_X₀ hi⟩, by rw [Equiv.apply_symm_apply]; exact hi,
      by rw [Equiv.apply_symm_apply]⟩

section Fiber

variable {T₀ : Finset C} (hT₀ : T₀.image (fun z => (η z : Fin 24)) = B₀)
include hT₀

omit H in
theorem mem_T₀_iff (z : C) : z ∈ T₀ ↔ (η z : Fin 24) ∈ B₀ := by
  rw [← hT₀, Finset.mem_image]
  constructor
  · exact fun hz => ⟨z, hz, rfl⟩
  · rintro ⟨z', hz', h⟩
    rwa [← η.injective (Subtype.ext h)]

omit H hT₀ in
theorem mem_image_val_iff {T : Finset C} (z : C) : (z : V) ∈ Subtype.val '' (T : Set C) ↔ z ∈ T :=
  Subtype.val_injective.mem_set_image

theorem block_mem : Subtype.val '' (T₀ : Set C) ∈ cliqueBlocks lab C :=
  (H.blocks T₀).2 (hT₀ ▸ B₀_mem_ℬ₀)

omit H hT₀ [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem block_subset : Subtype.val '' (T₀ : Set C) ⊆ C := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem mem_closure_block_iff (r : Subgroup.closure (lab '' C)) :
    (r : S) ∈ Subgroup.closure (lab '' (Subtype.val '' (T₀ : Set C))) ↔
      φ (Additive.ofMul r) ∈ U₀ := by
  have hmono : Subgroup.closure (lab '' (Subtype.val '' (T₀ : Set C))) ≤
      Subgroup.closure (lab '' C) :=
    Subgroup.closure_mono (Set.image_mono (block_subset))
  constructor
  · intro hr
    have key : ∀ (s : S) (hs : s ∈ Subgroup.closure (lab '' (Subtype.val '' (T₀ : Set C)))),
        φ (Additive.ofMul (⟨s, hmono hs⟩ : Subgroup.closure (lab '' C))) ∈ U₀ := by
      intro s hs
      induction hs using Subgroup.closure_induction with
      | mem s hs =>
        obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hs
        have he : (⟨lab z, hmono (Subgroup.subset_closure ⟨z, ⟨z, hz, rfl⟩, rfl⟩)⟩ :
            Subgroup.closure (lab '' C)) = cliqueGen z := rfl
        rw [he, H.gen]
        exact Submodule.subset_span ⟨η z, (mem_T₀_iff hT₀ z).1 hz, rfl⟩
      | one =>
        change φ (Additive.ofMul (1 : Subgroup.closure (lab '' C))) ∈ U₀
        rw [ofMul_one, map_zero]
        exact U₀.zero_mem
      | mul s s' hs hs' ihs ihs' =>
        have he : (⟨s * s', hmono (Subgroup.mul_mem _ hs hs')⟩ : Subgroup.closure (lab '' C)) =
            ⟨s, hmono hs⟩ * ⟨s', hmono hs'⟩ := rfl
        rw [he, ofMul_mul, map_add]
        exact U₀.add_mem ihs ihs'
      | inv s hs ihs =>
        have he : (⟨s⁻¹, hmono (Subgroup.inv_mem _ hs)⟩ : Subgroup.closure (lab '' C)) =
            (⟨s, hmono hs⟩)⁻¹ := rfl
        rw [he, ofMul_inv, map_neg]
        exact U₀.neg_mem ihs
    exact key r hr
  · intro hr
    have key : ∀ w ∈ U₀, ((Additive.toMul (φ.symm w) : Subgroup.closure (lab '' C)) : S) ∈
        Subgroup.closure (lab '' (Subtype.val '' (T₀ : Set C))) := by
      intro w hw
      rw [U₀] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, hi, rfl⟩ := hw
        have hz : η.symm i ∈ T₀ := by
          rw [mem_T₀_iff hT₀, Equiv.apply_symm_apply]
          exact hi
        have he : φ.symm (K₀.mkQ (e i)) = Additive.ofMul (cliqueGen (η.symm i)) := by
          rw [LinearEquiv.symm_apply_eq, H.gen, Equiv.apply_symm_apply]
        rw [he, toMul_ofMul]
        exact Subgroup.subset_closure ⟨_, ⟨η.symm i, hz, rfl⟩, rfl⟩
      | zero => rw [map_zero]; exact Subgroup.one_mem _
      | add w w' _ _ hw hw' => rw [map_add, toMul_add]; exact Subgroup.mul_mem _ hw hw'
      | smul c w _ hw =>
        rcases zmod2_cases c with rfl | rfl
        · rw [zero_smul, map_zero]; exact Subgroup.one_mem _
        · rw [one_smul]; exact hw
    have := key _ hr
    rwa [LinearEquiv.symm_apply_apply, toMul_ofMul] at this

theorem mem_KB_iff_image_block {k : setStab act lab Y C} :
    θ k ∈ KB ↔ act (k : S) '' (Subtype.val '' (T₀ : Set C)) = Subtype.val '' (T₀ : Set C) := by
  have hmemB : ∀ z : C, (act (k : S) z ∈ Subtype.val '' (T₀ : Set C) ↔
      psiHom (θ k) (η z) ∈ B₀) := by
    intro z
    rw [show act (k : S) z = (setStabPerm act lab Y C k z : V) from rfl, mem_image_val_iff,
      mem_T₀_iff hT₀, H.perm]
  constructor
  · intro hk
    apply image_act_eq_of_forall
    intro v
    by_cases hv : v ∈ C
    · obtain ⟨z, rfl⟩ : ∃ z : C, (z : V) = v := ⟨⟨v, hv⟩, rfl⟩
      rw [hmemB z, mem_image_val_iff, mem_T₀_iff hT₀]
      constructor
      · intro h
        have h' := psiHom_mem_B₀ (KB.inv_mem hk) h
        rwa [Subgroup.coe_inv, map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h'
      · exact psiHom_mem_B₀ hk
    · have h1 : act (k : S) v ∉ C := fun h => hv ((k.2.2 v).1 h)
      exact iff_of_false (fun h => h1 (block_subset h)) (fun h => hv (block_subset h))
  · intro hk
    rw [mem_KB]
    refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) (by rw [Finset.card_map])
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    have hjX : (j : Fin 24) ∈ X₀ := B₀_subset_X₀ hj
    set z := η.symm ⟨j, hjX⟩ with hz
    have hzj : (η z : Fin 24) = j := by rw [hz, Equiv.apply_symm_apply]
    have hzT : (z : V) ∈ Subtype.val '' (T₀ : Set C) := by
      rw [mem_image_val_iff, mem_T₀_iff hT₀, hzj]
      exact hj
    have h2 : act (k : S) z ∈ Subtype.val '' (T₀ : Set C) := by
      rw [← hk]
      exact ⟨z, hzT, rfl⟩
    rw [hmemB, hzj] at h2
    exact h2

omit hT₀ in
theorem act_mem_fiber_iff {k : setStab act lab Y C}
    (hk : act (k : S) '' (Subtype.val '' (T₀ : Set C)) = Subtype.val '' (T₀ : Set C)) (v : V) :
    act (k : S) v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) ↔
      v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) := by
  have himg := H.slice.image_hexadFiber k.2 (Subtype.val '' (T₀ : Set C))
  rw [hk] at himg
  conv_lhs => rw [← himg]
  exact (act (k : S)).injective.mem_set_image

theorem fixLift_image_block (h : KB) :
    act (H.fixLift h : S) '' (Subtype.val '' (T₀ : Set C)) = Subtype.val '' (T₀ : Set C) :=
  (H.mem_KB_iff_image_block hT₀).1 (by rw [H.theta_fixLift]; exact h.2)

@[expose] def fibPerm :
    KB →* Equiv.Perm ↥(hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) where
  toFun h := (act (H.fixLift h : S)).subtypePerm
    (H.act_mem_fiber_iff (H.fixLift_image_block hT₀ h))
  map_one' := Equiv.ext fun v => Subtype.ext (by
    change act (H.fixLift ((1 : KB) : CFSG.Blueprint.NativeSporadic.M22) : S) v = v
    rw [Subgroup.coe_one, H.fixLift_one, Subgroup.coe_one, map_one, Equiv.Perm.one_apply])
  map_mul' h h' := Equiv.ext fun v => Subtype.ext (by
    change act (H.fixLift ((h * h' : KB) : CFSG.Blueprint.NativeSporadic.M22) : S) v =
      act (H.fixLift h : S) (act (H.fixLift h' : S) v)
    rw [Subgroup.coe_mul, H.fixLift_mul, Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply])

omit H in
theorem block_nonempty : (Subtype.val '' (T₀ : Set C)).Nonempty := by
  have h2 : (2 : Fin 24) ∈ B₀ := by decide
  rw [← hT₀, Finset.mem_image] at h2
  obtain ⟨z, hz, -⟩ := h2
  exact ⟨z, z, hz, rfl⟩

omit H hT₀ [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
open _root_.Classical in
theorem image_val_image (f : setStab act lab Y C) (T : Finset C) :
    act (f : S) '' (Subtype.val '' (T : Set C)) =
      Subtype.val '' ((T.image (setStabPerm act lab Y C f) : Finset C) : Set C) := by
  rw [Finset.coe_image, Set.image_image, Set.image_image]
  rfl

open _root_.Classical in
theorem map_B₀_eq (f : setStab act lab Y C) :
    B₀.map (psiHom (θ f)).toEmbedding =
      (T₀.image (setStabPerm act lab Y C f)).image (fun z => (η z : Fin 24)) := by
  rw [← hT₀, Finset.map_eq_image, Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun z _ => ?_
  change psiHom (θ f) (η z : Fin 24) = (η (setStabPerm act lab Y C f z) : Fin 24)
  rw [H.perm]

section Base

variable {y₀ : V} (hy₀ : y₀ ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)))
include hy₀

theorem exists_closure_act_eq_fiber {v : V}
    (hv : v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) :
    ∃ r : Subgroup.closure (lab '' C), act (r : S) y₀ = v := by
  obtain ⟨r, hr, hry⟩ :=
    (H.slice.hexadFiber_of_mem_cliqueBlocks H.clique (H.block_mem hT₀)).2.1 _ hy₀ _ hv
  exact ⟨⟨r, H.ptStab_eq ▸ hr⟩, hry⟩

omit hT₀ hy₀ in
theorem act_closure_mem_fiber (r : Subgroup.closure (lab '' C)) {v : V}
    (hv : v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) :
    act (r : S) v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) :=
  H.slice.act_mem_hexadFiber (H.mem_ptStab r) hv

theorem act_eq_act_iff (r r' : Subgroup.closure (lab '' C)) :
    act (r : S) y₀ = act (r' : S) y₀ ↔
      U₀.mkQ (φ (Additive.ofMul r)) = U₀.mkQ (φ (Additive.ofMul r')) := by
  have hstab := ((H.slice.hexadFiber_of_mem_cliqueBlocks H.clique (H.block_mem hT₀)).2.2 y₀
    hy₀).1
  have e1 : act (r : S) y₀ = act (r' : S) y₀ ↔ ((r⁻¹ * r' : Subgroup.closure (lab '' C)) : S) ∈
      ptStab act lab Y C ⊓ actStab act y₀ := by
    rw [Subgroup.mem_inf, mem_actStab]
    refine ⟨fun h => ⟨H.mem_ptStab _, ?_⟩, fun h => ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Equiv.Perm.mul_apply, ← h, act_inv_act]
    · have h2 := h.2
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Equiv.Perm.mul_apply] at h2
      have h3 := congrArg (act (r : S)) h2
      rw [act_act_inv] at h3
      exact h3.symm
  rw [e1, hstab, H.mem_closure_block_iff hT₀, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, ofMul_mul, ofMul_inv, map_add, map_neg, ← Submodule.neg_mem_iff,
    neg_add, neg_neg, ← sub_eq_add_neg]

theorem fibCoord_spec (r : Subgroup.closure (lab '' C)) {v : V} (h : act (r : S) y₀ = v) :
    fibCoord act φ y₀ v = U₀.mkQ (φ (Additive.ofMul r)) := by
  have hex : ∃ r : Subgroup.closure (lab '' C), act (r : S) y₀ = v := ⟨r, h⟩
  rw [fibCoord, dite_eq_left hex]
  exact (H.act_eq_act_iff hT₀ hy₀ _ _).1 (hex.choose_spec.trans h.symm)

theorem fibCoord_base : fibCoord act φ y₀ y₀ = 0 := by
  rw [H.fibCoord_spec hT₀ hy₀ 1 (by rw [Subgroup.coe_one, map_one, Equiv.Perm.one_apply]),
    ofMul_one, map_zero, map_zero]

theorem fibCoord_act (s : Subgroup.closure (lab '' C)) {v : V}
    (hv : v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) :
    fibCoord act φ y₀ (act (s : S) v) =
      fibCoord act φ y₀ v + U₀.mkQ (φ (Additive.ofMul s)) := by
  obtain ⟨r, rfl⟩ := H.exists_closure_act_eq_fiber hT₀ hy₀ hv
  rw [H.fibCoord_spec hT₀ hy₀ r rfl, H.fibCoord_spec hT₀ hy₀ (s * r)
    (by rw [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply]), ofMul_mul, map_add, map_add,
    add_comm]

theorem fibCoord_injOn {v v' : V} (hv : v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)))
    (hv' : v' ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)))
    (h : fibCoord act φ y₀ v = fibCoord act φ y₀ v') : v = v' := by
  obtain ⟨r, rfl⟩ := H.exists_closure_act_eq_fiber hT₀ hy₀ hv
  obtain ⟨r', rfl⟩ := H.exists_closure_act_eq_fiber hT₀ hy₀ hv'
  rw [H.fibCoord_spec hT₀ hy₀ r rfl, H.fibCoord_spec hT₀ hy₀ r' rfl] at h
  exact (H.act_eq_act_iff hT₀ hy₀ r r').2 h

theorem exists_fibCoord_eq (q : Q₀) :
    ∃ v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)), fibCoord act φ y₀ v = q := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective U₀ q
  refine ⟨act ((Additive.toMul (φ.symm w) : Subgroup.closure (lab '' C)) : S) y₀,
    H.act_closure_mem_fiber _ hy₀, ?_⟩
  rw [H.fibCoord_spec hT₀ hy₀ _ rfl, ofMul_toMul, LinearEquiv.apply_symm_apply]

theorem fibCoord_bijective : Function.Bijective
    (fun v : ↥(hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) => fibCoord act φ y₀ v) :=
  ⟨fun v v' h => Subtype.ext (H.fibCoord_injOn hT₀ hy₀ v.2 v'.2 h), fun q => by
    obtain ⟨v, hv, hq⟩ := H.exists_fibCoord_eq hT₀ hy₀ q
    exact ⟨⟨v, hv⟩, hq⟩⟩

@[expose] def fibEquiv : ↥(hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) ≃ Q₀ :=
  Equiv.ofBijective _ (H.fibCoord_bijective hT₀ hy₀)

@[expose] def fibAct : KB →* Equiv.Perm Q₀ :=
  (H.fibEquiv hT₀ hy₀).permCongrHom.toMonoidHom.comp (H.fibPerm hT₀)

theorem fibAct_fibCoord (h : KB) {v : V}
    (hv : v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C))) :
    H.fibAct hT₀ hy₀ h (fibCoord act φ y₀ v) = fibCoord act φ y₀ (act (H.fixLift h : S) v) := by
  have e : (H.fibEquiv hT₀ hy₀).symm (fibCoord act φ y₀ v) = ⟨v, hv⟩ :=
    (Equiv.symm_apply_eq _).2 rfl
  simp only [fibAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.permCongr_apply, e]
  rfl

theorem isAffineAction_fibAct (hconj : ∀ (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
      (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r))) :
    IsAffineAction (H.fibAct hT₀ hy₀) := by
  intro h q q'
  obtain ⟨v, hv, rfl⟩ := H.exists_fibCoord_eq hT₀ hy₀ q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective U₀ q'
  set s : Subgroup.closure (lab '' C) := Additive.toMul (φ.symm w) with hs
  have hsw : φ (Additive.ofMul s) = w := by rw [hs, ofMul_toMul, LinearEquiv.apply_symm_apply]
  have hsv := H.act_closure_mem_fiber s hv
  set k := H.fixLift h with hk
  have hkC : ∀ z ∈ C, act (k : S) z ∈ C := fun z hz => (k.2.2 z).2 hz
  have hconj' : (k : S) * s * (k : S)⁻¹ ∈ Subgroup.closure (lab '' C) :=
    conj_mem_closure H.slice.lab_act hkC s s.2
  have e2 : act (k : S) (act (s : S) v) =
      act ((⟨(k : S) * s * (k : S)⁻¹, hconj'⟩ : Subgroup.closure (lab '' C)) : S)
        (act (k : S) v) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
    congr 2
    group
  have hkv : act (k : S) v ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) :=
    (H.act_mem_fiber_iff (H.fixLift_image_block hT₀ h) v).2 hv
  rw [← hsw, ← H.fibCoord_act hT₀ hy₀ s hv, H.fibAct_fibCoord hT₀ hy₀ h hsv,
    H.fibAct_fibCoord hT₀ hy₀ h hv, e2, H.fibCoord_act hT₀ hy₀ _ hkv, hconj k s hconj',
    rhoQ_mkQ, hk, H.theta_fixLift]

theorem isAffOrigin_iff (t : Q₀) :
    IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t ↔
      IsTranslationIso affA (H.fibAct hT₀ hy₀) t := by
  constructor
  · intro ht h q
    obtain ⟨v, hv, hvq⟩ := H.exists_fibCoord_eq hT₀ hy₀ (q + t)
    have hKB : θ (H.fixLift h) ∈ KB := by rw [H.theta_fixLift]; exact h.2
    have h1 := ht (H.fixLift h) hKB (H.fixLift_fix h) v hv
    have hh : (⟨θ (H.fixLift h), hKB⟩ : KB) = h := Subtype.ext (H.theta_fixLift h)
    rw [hh, hvq, add_assoc, add_self_Q, add_zero] at h1
    rw [← hvq, H.fibAct_fibCoord hT₀ hy₀ h hv, ← h1, add_assoc, add_self_Q, add_zero]
  · intro ht k hKB hkx v hv
    have h1 := ht ⟨θ k, hKB⟩ (fibCoord act φ y₀ v + t)
    rw [add_assoc, add_self_Q, add_zero, H.fibAct_fibCoord hT₀ hy₀ _ hv,
      show ((⟨θ k, hKB⟩ : KB) : CFSG.Blueprint.NativeSporadic.M22) = θ k from rfl,
      H.fixLift_theta k hkx] at h1
    rw [h1, add_assoc, add_self_Q, add_zero]

theorem not_isTranslationIso_affLin (t : Q₀) :
    ¬IsTranslationIso affLin (H.fibAct hT₀ hy₀) t := by
  intro ht
  set N : Set V := (sliceGraph lab Y).neighborSet x ∩
    hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) with hN
  have hinj : Set.InjOn (fun v => fibCoord act φ y₀ v + t) N := fun v hv v' hv' h =>
    H.fibCoord_injOn hT₀ hy₀ hv.2 hv'.2 (add_right_cancel h)
  have hcard : ((fun v => fibCoord act φ y₀ v + t) '' N).ncard = 6 := by
    rw [hinj.ncard_image]
    exact H.slice.ncard_neighborSet_inter_hexadFiber H.clique H.mem (H.block_mem hT₀)
  refine ncard_ne_six_of_affLin (fun h q hq => ?_) hcard
  obtain ⟨v, ⟨hadj, hv⟩, rfl⟩ := hq
  have hkv := (H.act_mem_fiber_iff (H.fixLift_image_block hT₀ h) v).2 hv
  refine ⟨act (H.fixLift h : S) v, ⟨?_, hkv⟩, ?_⟩
  · have h1 := (H.slice.adj_act_iff (H.fixLift h).2.1 x v).2 hadj
    rwa [H.fixLift_fix] at h1
  · have h1 := ht h (fibCoord act φ y₀ v + t)
    rw [add_assoc, add_self_Q, add_zero, H.fibAct_fibCoord hT₀ hy₀ h hv] at h1
    change fibCoord act φ y₀ (act (H.fixLift h : S) v) + t =
      affLin h (fibCoord act φ y₀ v + t)
    rw [h1, add_assoc, add_self_Q, add_zero]

theorem exists_isAffOrigin (hconj : ∀ (f : setStab act lab Y C)
      (r : Subgroup.closure (lab '' C)) (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r))) :
    ∃ t, IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t := by
  rcases affine_classification (H.isAffineAction_fibAct hT₀ hy₀ hconj) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact absurd ht (H.not_isTranslationIso_affLin hT₀ hy₀ t)
  · exact ⟨t, (H.isAffOrigin_iff hT₀ hy₀ t).2 ht⟩

theorem isAffOrigin_unique (hconj : ∀ (f : setStab act lab Y C)
      (r : Subgroup.closure (lab '' C)) (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r)))
    {t t' : Q₀} (ht : IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t)
    (ht' : IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t') : t = t' :=
  isTranslationIso_unique isAffineAction_affA (H.isAffineAction_fibAct hT₀ hy₀ hconj)
    ((H.isAffOrigin_iff hT₀ hy₀ t).1 ht) ((H.isAffOrigin_iff hT₀ hy₀ t').1 ht')

omit hT₀ in
theorem act_mem_image_fiber (f : setStab act lab Y C) :
    act (f : S) y₀ ∈ hexadFiber lab Y C (act (f : S) '' (Subtype.val '' (T₀ : Set C))) := by
  rw [← H.slice.image_hexadFiber f.2]
  exact ⟨y₀, hy₀, rfl⟩

theorem act_fix_iff {t : Q₀} (ht : IsAffOrigin act lab Y θ φ x y₀ (Subtype.val '' (T₀ : Set C)) t)
    (f : setStab act lab Y C) :
    act (f : S) y₀ = y₀ ↔ α f • (Sum.inr (Sum.inr (zMk 1 t)) : CFSG.Monster.B.Fischer.Y) =
      Sum.inr (Sum.inr (zMk 1 t)) := by
  obtain ⟨r, k, hf, hk⟩ := H.exists_eq_mul_fix f
  have hact : act (f : S) y₀ = act (r : S) (act (k : S) y₀) := by
    rw [hf, map_mul, Equiv.Perm.mul_apply]
  have himg : act (f : S) '' (Subtype.val '' (T₀ : Set C)) =
      act (k : S) '' (Subtype.val '' (T₀ : Set C)) :=
    image_eq_of_eq_mul (H.mem_ptStab r) k.2 hf (block_subset)
  have key : ∀ hKB : θ k ∈ KB, fibCoord act φ y₀ (act (f : S) y₀) =
      affA ⟨θ k, hKB⟩ t + t + U₀.mkQ (φ (Additive.ofMul r)) := by
    intro hKB
    have hkB := (H.mem_KB_iff_image_block hT₀).1 hKB
    have hky := (H.act_mem_fiber_iff hkB y₀).2 hy₀
    have h1 := ht k hKB hk y₀ hy₀
    rw [H.fibCoord_base hT₀ hy₀, zero_add] at h1
    have h1' : fibCoord act φ y₀ (act (k : S) y₀) = affA ⟨θ k, hKB⟩ t + t := by
      rw [← h1, add_assoc, add_self_Q, add_zero]
    rw [hact, H.fibCoord_act hT₀ hy₀ r hky, h1']
  rw [H.alpha r f k hf hk, wF_mul_kF_smul_zMk_one]
  constructor
  · intro hfy
    have hfB : act (f : S) '' (Subtype.val '' (T₀ : Set C)) = Subtype.val '' (T₀ : Set C) := by
      have hmem := H.act_mem_image_fiber hy₀ f
      rw [hfy] at hmem
      exact (eq_of_mem_hexadFiber hy₀ hmem).symm
    have hKB : θ k ∈ KB := (H.mem_KB_iff_image_block hT₀).2 (himg.symm.trans hfB)
    have h2 := key hKB
    rw [hfy, H.fibCoord_base hT₀ hy₀] at h2
    rw [zMk_eq_zMk_one hKB, isAffineAction_affA, rhoQ_mkQ]
    change Sum.inr (Sum.inr (zMk 1 (affA ⟨θ k, hKB⟩ t +
      U₀.mkQ (rhoW (θ k) (rhoW (θ k)⁻¹ (φ (Additive.ofMul r))))))) = _
    rw [rhoW_apply_inv]
    have h3 := h2.symm
    rw [add_right_comm] at h3
    rw [(eq_neg_of_add_eq_zero_left h3).trans (neg_Q t)]
  · intro heq
    have hz := Sum.inr_injective (Sum.inr_injective heq)
    have hKB : θ k ∈ KB := by
      have h1 := congrArg hexadOf hz
      rwa [hexadOf_zMk, hexadOf_zMk_one] at h1
    rw [zMk_eq_zMk_one hKB, isAffineAction_affA, rhoQ_mkQ] at hz
    change zMk 1 (affA ⟨θ k, hKB⟩ t +
      U₀.mkQ (rhoW (θ k) (rhoW (θ k)⁻¹ (φ (Additive.ofMul r))))) = _ at hz
    rw [rhoW_apply_inv] at hz
    have hq := zMk_one_injective hz
    have hfX : act (f : S) y₀ ∈ hexadFiber lab Y C (Subtype.val '' (T₀ : Set C)) := by
      rw [hact]
      exact H.act_closure_mem_fiber r ((H.act_mem_fiber_iff
        ((H.mem_KB_iff_image_block hT₀).1 hKB) y₀).2 hy₀)
    apply H.fibCoord_injOn hT₀ hy₀ hfX hy₀
    rw [key hKB, H.fibCoord_base hT₀ hy₀, add_right_comm, hq, add_self_Q]

omit hT₀ in
theorem act_not_mem_clique (f : setStab act lab Y C) : act (f : S) y₀ ∉ C :=
  (H.act_mem_image_fiber hy₀ f).2.1

theorem act_ne_act_omega (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C)) :
    act (r : S) x ≠ act (f : S) y₀ := by
  intro h
  have hmem := H.act_mem_image_fiber hy₀ f
  rw [← h] at hmem
  have h0 := eq_of_mem_hexadFiber (H.act_mem_omega r) hmem
  obtain ⟨z, hz⟩ := block_nonempty hT₀
  have h1 : act (f : S) z ∈ act (f : S) '' (Subtype.val '' (T₀ : Set C)) := ⟨z, hz, rfl⟩
  rw [← h0] at h1
  exact h1

theorem regions {v : V} (hv : v ∈ Y) : (∃ z : C, (z : V) = v) ∨
    (∃ r : Subgroup.closure (lab '' C), act (r : S) x = v) ∨
      ∃ f : setStab act lab Y C, act (f : S) y₀ = v := by
  by_cases hvC : v ∈ C
  · exact Or.inl ⟨⟨v, hvC⟩, rfl⟩
  rcases H.slice.inter_neighborSet_eq_empty_or_mem H.clique hvC with h | h
  · exact Or.inr (Or.inl (H.exists_closure_act_eq ⟨hv, hvC, h⟩))
  · obtain ⟨f, hf, hfv⟩ :=
      H.exists_act_eq_of_mem_hexadFiber (H.block_mem hT₀) h hy₀ ⟨hv, hvC, rfl⟩
    exact Or.inr (Or.inr ⟨⟨f, hf⟩, hfv⟩)

end Base

end Fiber

end FullIntertwinerHyp

end CFSG.Monster.B.TwoA.Fischer
