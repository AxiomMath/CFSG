module

public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Recognition.HSPinnedCert

public section

namespace CFSG.Sporadic.Recognition.HSPinned

open CFSG.Sporadic.Recognition.HSPinned.Native CFSG.Sporadic.HS.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

open scoped Pointwise

abbrev JHS : Type := CFSG.Sporadic.SmallF2.J hsData

theorem hsBaseFacts :
    CFSG.Sporadic.SmallF2.BaseFacts hsData := CFSG.Sporadic.HS.hsFacts.toBaseFacts

noncomputable abbrev hsGenA : JHS := CFSG.Sporadic.SmallF2.a hsData

noncomputable abbrev hsGenB : JHS := CFSG.Sporadic.SmallF2.b hsData

@[expose] def vtxStar (i : ℕ) : Finset (Fin hsData.n) :=
  Finset.univ.filter fun x => x.val ∈ stars[i]!

theorem mem_star {i : ℕ} {x : Fin hsData.n} : x ∈ vtxStar i ↔ x.val ∈ stars[i]! := by
  simp [vtxStar]

theorem starsClosed : ∀ i < 100, vtxA[i]! < 100 ∧ vtxB[i]! < 100 ∧
    ∀ x < 1100, (x ∈ stars[i]! ↔ ap (CFSG.Sporadic.SmallF2.O hsData).alpha x ∈ stars[vtxA[i]!]!) ∧
      (x ∈ stars[i]! ↔ ap (CFSG.Sporadic.SmallF2.O hsData).beta x ∈ stars[vtxB[i]!]!) := by
  have h := starsClosed_check
  unfold starsClosedOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  intro i hi
  have h1 := (allIn_eq_true.1 h) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨hA, hB1⟩, h2⟩ := h1
  refine ⟨hA, hB1, fun x hx => ?_⟩
  have h3 := (allIn_eq_true.1 h2) x (Nat.zero_le _) hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  exact h3

theorem genA_val (z : Fin hsData.n) :
    (hsGenA • z).val = ap (CFSG.Sporadic.SmallF2.O hsData).alpha z.val := by
  rw [← idx_of_lt hsGenA z.isLt]
  exact (CFSG.Sporadic.SmallF2.rep_a hsBaseFacts z.val z.isLt).symm

theorem genB_val (z : Fin hsData.n) :
    (hsGenB • z).val = ap (CFSG.Sporadic.SmallF2.O hsData).beta z.val := by
  rw [← idx_of_lt hsGenB z.isLt]
  exact (CFSG.Sporadic.SmallF2.rep_b hsBaseFacts z.val z.isLt).symm

theorem genA_smul_star
    {i : ℕ} (hi : i < 100) : hsGenA • vtxStar i = vtxStar vtxA[i]! := by
  obtain ⟨-, -, h⟩ := starsClosed i hi
  ext y
  obtain ⟨z, rfl⟩ : ∃ z, hsGenA • z = y := ⟨hsGenA⁻¹ • y, smul_inv_smul _ _⟩
  rw [Finset.smul_mem_smul_finset_iff, mem_star, mem_star, genA_val, ← (h z.val z.isLt).1]

theorem genB_smul_star
    {i : ℕ} (hi : i < 100) : hsGenB • vtxStar i = vtxStar vtxB[i]! := by
  obtain ⟨-, -, h⟩ := starsClosed i hi
  ext y
  obtain ⟨z, rfl⟩ : ∃ z, hsGenB • z = y := ⟨hsGenB⁻¹ • y, smul_inv_smul _ _⟩
  rw [Finset.smul_mem_smul_finset_iff, mem_star, mem_star, genB_val, ← (h z.val z.isLt).2]

theorem star_inj :
    ∀ i < 100, ∀ j < 100, vtxStar i = vtxStar j → i = j := by
  intro i hi j hj h
  rcases stars_inj i hi j hj with rfl | ⟨x, hx, hxj⟩
  · rfl
  · exfalso
    have hx' : x < 1100 := stars_lt i hi x hx
    have : (⟨x, hx'⟩ : Fin hsData.n) ∈ vtxStar i := mem_star.2 hx
    rw [h, mem_star] at this
    exact hxj this

theorem star_closed_A :
    ∀ i < 100, vtxA[i]! < 100 ∧ hsGenA • vtxStar i = vtxStar vtxA[i]! :=
  fun i hi => ⟨(starsClosed i hi).1, genA_smul_star hi⟩

theorem star_closed_B :
    ∀ i < 100, vtxB[i]! < 100 ∧ hsGenB • vtxStar i = vtxStar vtxB[i]! :=
  fun i hi => ⟨(starsClosed i hi).2.1, genB_smul_star hi⟩

@[expose] noncomputable def starEquiv :
    Fin 100 ≃ MulAction.orbit JHS (vtxStar 0) :=
  orbitEquiv (a := hsGenA) (b := hsGenB) (CFSG.Sporadic.SmallF2.closure_ab hsData) (n := 100)
    (by norm_num) vtxStar star_inj (α := fun i => vtxA[i]!) (β := fun i => vtxB[i]!)
    star_closed_A star_closed_B (fun i => vtxPar[i]!) (fun i => vtxLab[i]!)
    (fun i hi hpos => tree_check i hi hpos)

noncomputable instance vtxAction :
    MulAction JHS (Fin 100) := starEquiv.mulAction JHS

theorem starEquiv_smul
    (g : JHS) (i : Fin 100) : starEquiv (g • i) = g • starEquiv i := by
  show starEquiv (starEquiv.symm (g • starEquiv i)) = _
  rw [Equiv.apply_symm_apply]

theorem starEquiv_apply
    (i : Fin 100) : (starEquiv i : Finset (Fin hsData.n)) = vtxStar i.val := rfl

theorem star_smul
    (g : JHS) (i : Fin 100) : vtxStar (g • i : Fin 100).val = g • vtxStar i.val := by
  have := congrArg Subtype.val (starEquiv_smul g i)
  rw [starEquiv_apply] at this
  rw [this]
  rfl

theorem star_eq_iff
    {i j : Fin 100} : vtxStar i.val = vtxStar j.val ↔ i = j :=
  ⟨fun h => Fin.ext (star_inj i.val i.isLt j.val j.isLt h), fun h => by rw [h]⟩

theorem smul_eq_iff
    (g : JHS) (i j : Fin 100) : g • i = j ↔ g • vtxStar i.val = vtxStar j.val := by
  rw [← star_smul, star_eq_iff]

theorem genA_smul_vtx
    (i : Fin 100) : (hsGenA • i).val = vtxA[i.val]! := by
  have h := star_smul hsGenA i
  rw [genA_smul_star i.isLt] at h
  exact star_inj _ (hsGenA • i).isLt _ (star_closed_A i.val i.isLt).1 h

theorem genB_smul_vtx
    (i : Fin 100) : (hsGenB • i).val = vtxB[i.val]! := by
  have h := star_smul hsGenB i
  rw [genB_smul_star i.isLt] at h
  exact star_inj _ (hsGenB • i).isLt _ (star_closed_B i.val i.isLt).1 h

theorem eq_one_of_fix
    (g : JHS) (hg : ∀ i : Fin 100, g • i = i) : g = 1 := by
  apply CFSG.Sporadic.SmallF2.eq_one_of_fix_basis hsBaseFacts
  intro t ht
  have ht20 : t < 20 := by
    have h20 : hsData.basis.size = 20 := hsBaseFacts.basis_size
    omega
  obtain ⟨hi, hj, hw⟩ := wit_check t ht20
  have hbt : hsData.basis[t]! < hsData.n := hsBaseFacts.basis_lt t ht
  rw [idx_of_lt g hbt]
  set i : Fin 100 := ⟨wit[t]!.1, hi⟩
  set j : Fin 100 := ⟨wit[t]!.2, hj⟩
  have hinter : vtxStar i.val ∩ vtxStar j.val = {(⟨hsData.basis[t]!, hbt⟩ : Fin hsData.n)} := by
    ext y
    simp only [Finset.mem_inter, mem_star, Finset.mem_singleton]
    rw [hw y.val y.isLt]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have key : g • (vtxStar i.val ∩ vtxStar j.val) = vtxStar i.val ∩ vtxStar j.val := by
    rw [Finset.smul_finset_inter, ← star_smul, ← star_smul, hg, hg]
  rw [hinter, Finset.smul_finset_singleton, Finset.singleton_inj] at key
  exact congrArg Fin.val key

instance faithfulVtx :
    FaithfulSMul JHS (Fin 100) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix _ fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem exists_smul_zero
    (i : Fin 100) : ∃ g : JHS, g • (⟨0, by norm_num⟩ : Fin 100) = i := by
  obtain ⟨g, hg⟩ := (starEquiv i).2
  exact ⟨g, (smul_eq_iff g _ i).2 hg⟩

instance pretransitiveVtx :
    MulAction.IsPretransitive JHS (Fin 100) :=
  ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_smul_zero x
    obtain ⟨h, hh⟩ := exists_smul_zero y
    exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩⟩

theorem adj_iff_star {x y : Fin 100} :
    adjB x.val y.val = true ↔ x ≠ y ∧ (vtxStar x.val ∩ vtxStar y.val).Nonempty := by
  rw [adj_spec x.val x.isLt y.val y.isLt]
  constructor
  · rintro ⟨hne, t, ht1, ht2⟩
    exact ⟨fun h => hne (by rw [h]), ⟨⟨t, stars_lt _ x.isLt t ht1⟩, by
      simp [mem_star, ht1, ht2]⟩⟩
  · rintro ⟨hne, z, hz⟩
    rw [Finset.mem_inter, mem_star, mem_star] at hz
    exact ⟨fun h => hne (Fin.ext h), z.val, hz.1, hz.2⟩

theorem adjB_smul
    (g : JHS) (x y : Fin 100) :
    adjB (g • x).val (g • y).val = adjB x.val y.val := by
  rw [Bool.eq_iff_iff, adj_iff_star, adj_iff_star, star_smul, star_smul,
    ← Finset.smul_finset_inter, Finset.smul_finset_nonempty, (MulAction.injective g).ne_iff]

end CFSG.Sporadic.Recognition.HSPinned
