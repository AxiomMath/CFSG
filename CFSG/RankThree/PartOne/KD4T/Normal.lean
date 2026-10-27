module

public import CFSG.RankThree.PartOne.KD4T.Inj
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Idx

variable {τ : Tag} [hτ : E6Sub τ]

@[expose] def d4Id (k : Fin Tag.D4.rank) : Fin τ.rank := e6Idx (d4Idx k)

theorem d4Id_mem (k : Fin Tag.D4.rank) : d4Id (τ := τ) k ∈ d4Set τ :=
  (e6Idx_mem_d4Set_iff _).2 (d4Idx_mem k)

theorem d4Id_injective : Function.Injective (d4Id (τ := τ)) :=
  e6Idx_injective.comp d4Idx_injective

theorem exists_d4Id_eq {i : Fin τ.rank} (hi : i ∈ d4Set τ) : ∃ k, d4Id (τ := τ) k = i := by
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (lt_six_of_mem_d4Set hi)
  obtain ⟨l, rfl⟩ := exists_d4Idx_eq ((e6Idx_mem_d4Set_iff k).1 hi)
  exact ⟨l, rfl⟩

theorem cartan_d4Id (k l : Fin Tag.D4.rank) :
    τ.cartan (d4Id k) (d4Id l) = Tag.D4.cartan k l := by
  rw [d4Id, d4Id, cartan_e6Idx]
  exact cartan_d4Idx k l

end Idx

section Scalars

variable {Ω : Type} [Field Ω]

theorem torusRootChar_list_prod_D4'
    (t : Fin Tag.D4.rank → Ωˣ) (k : Fin Tag.D4.rank) :
    torusRootChar (((List.finRange Tag.D4.rank).map fun j => torusElt Tag.D4 Ω j (t j)).prod)
      (Pi.single k 1) = ((t 0 ^ Tag.D4.cartan 0 k * t 1 ^ Tag.D4.cartan 1 k *
        t 2 ^ Tag.D4.cartan 2 k * t 3 ^ Tag.D4.cartan 3 k : Ωˣ) : Ω) := by
  have hd : ∀ (i : Fin Tag.D4.rank) (u : Ωˣ), torusElt Tag.D4 Ω i u ∈ diagonalGroup :=
    fun i u => torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i u)
  have hl : ((List.finRange Tag.D4.rank).map fun j => torusElt Tag.D4 Ω j (t j)).prod =
      torusElt Tag.D4 Ω 0 (t 0) * (torusElt Tag.D4 Ω 1 (t 1) *
        (torusElt Tag.D4 Ω 2 (t 2) * torusElt Tag.D4 Ω 3 (t 3))) := by
    have hf : List.finRange Tag.D4.rank = [0, 1, 2, 3] := by decide
    rw [hf]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hs : ∀ (i : Fin Tag.D4.rank) (u : Ωˣ), torusRootChar (torusElt Tag.D4 Ω i u)
      (Pi.single k 1) = ((u ^ Tag.D4.cartan i k : Ωˣ) : Ω) := fun i u => by
    rw [torusRootChar_torusElt i u (isRoot_single _ k)]
    congr 2
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
  rw [hl, torusRootChar_mul (hd _ _) (mul_mem (hd _ _) (mul_mem (hd _ _) (hd _ _))),
    torusRootChar_mul (hd _ _) (mul_mem (hd _ _) (hd _ _)), torusRootChar_mul (hd _ _) (hd _ _),
    hs, hs, hs, hs]
  simp only [Units.val_mul, mul_assoc]

theorem exists_d4Params
    [IsAlgClosed Ω] (s : Fin Tag.D4.rank → Ωˣ) :
    ∃ t : Fin Tag.D4.rank → Ωˣ, ∀ k : Fin Tag.D4.rank,
      ((t 0 ^ Tag.D4.cartan 0 k * t 1 ^ Tag.D4.cartan 1 k * t 2 ^ Tag.D4.cartan 2 k *
        t 3 ^ Tag.D4.cartan 3 k : Ωˣ) : Ω) = s k := by
  obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift Tag.D4 Ω s
  refine ⟨t, fun k => ?_⟩
  rw [← torusRootChar_list_prod_D4', ← ht]
  refine torusRootChar_eq_of_apply (isRoot_single _ k) ?_
  change rootDiag s (rootVec Tag.D4 Ω (Pi.single k 1)) = _
  rw [rootDiag_rootVec s (isRoot_single _ k)]
  congr 2
  rw [rootChar, Finset.prod_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, zpow_one]

end Scalars

section Torus

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L]

@[expose] def d4TorusWord (t : Fin Tag.D4.rank → Lˣ) : ModGL τ L :=
  torusElt τ L (d4Id 0) (t 0) * torusElt τ L (d4Id 1) (t 1) * torusElt τ L (d4Id 2) (t 2) *
    torusElt τ L (d4Id 3) (t 3)

theorem d4TorusWord_mem_subsystemGroup (t : Fin Tag.D4.rank → Lˣ) :
    (d4TorusWord t : ModGL τ L) ∈ subsystemGroup τ L (d4Set τ) := by
  have h : ∀ (k : Fin Tag.D4.rank) (u : Lˣ), torusElt τ L (d4Id k) u ∈ subsystemGroup τ L (d4Set τ) :=
    fun k u => subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem k) u)
  exact mul_mem (mul_mem (mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _)

theorem d4TorusWord_mem_torusGroup (t : Fin Tag.D4.rank → Lˣ) :
    (d4TorusWord t : ModGL τ L) ∈ torusGroup τ L := by
  have h : ∀ (k : Fin Tag.D4.rank) (u : Lˣ), torusElt τ L (d4Id k) u ∈ torusGroup τ L :=
    fun k u => torusElt_mem_torusGroup _ u
  exact mul_mem (mul_mem (mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _)

theorem torusRootChar_d4TorusWord (t : Fin Tag.D4.rank → Lˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    torusRootChar (d4TorusWord t : ModGL τ L) α =
      ((t 0 ^ (∑ j, τ.cartan (d4Id 0) j * α j) * t 1 ^ (∑ j, τ.cartan (d4Id 1) j * α j) *
        t 2 ^ (∑ j, τ.cartan (d4Id 2) j * α j) * t 3 ^ (∑ j, τ.cartan (d4Id 3) j * α j) : Lˣ) :
          L) := by
  have hd : ∀ (k : Fin Tag.D4.rank) (u : Lˣ), torusElt τ L (d4Id k) u ∈ diagonalGroup :=
    fun k u => torusGroup_le_diagonalGroup (torusElt_mem_torusGroup _ u)
  rw [d4TorusWord, torusRootChar_mul (mul_mem (mul_mem (hd 0 _) (hd 1 _)) (hd 2 _)) (hd 3 _),
    torusRootChar_mul (mul_mem (hd 0 _) (hd 1 _)) (hd 2 _), torusRootChar_mul (hd 0 _) (hd 1 _),
    torusRootChar_torusElt _ _ hα, torusRootChar_torusElt _ _ hα, torusRootChar_torusElt _ _ hα,
    torusRootChar_torusElt _ _ hα]
  simp only [Units.val_mul]

omit hτ in
theorem pair_single_eq (a l : Fin τ.rank) :
    (∑ j, τ.cartan a j * (Pi.single l 1 : Fin τ.rank → ℤ) j) = τ.cartan a l := by
  simp [Pi.single_apply]

theorem exists_d4TorusWord_scalars [IsAlgClosed L] (s : Fin Tag.D4.rank → Lˣ) :
    ∃ t : Fin Tag.D4.rank → Lˣ, ∀ (k : Fin Tag.D4.rank) (c : L),
      d4TorusWord t * xUnit τ L (d4Id k) c * (d4TorusWord t : ModGL τ L)⁻¹ =
        xUnit τ L (d4Id k) (s k * c) ∧
      d4TorusWord t * yUnit τ L (d4Id k) c * (d4TorusWord t : ModGL τ L)⁻¹ =
        yUnit τ L (d4Id k) (((s k)⁻¹ : Lˣ) * c) := by
  obtain ⟨t, hkey⟩ := exists_d4Params s
  have hT := d4TorusWord_mem_torusGroup (τ := τ) (L := L) t
  refine ⟨t, fun k c => ⟨?_, ?_⟩⟩
  · rw [← pinnedX_single, ← pinnedX_single, conj_pinnedX_of_mem_torusGroup hT (isRoot_single _ _),
      torusRootChar_d4TorusWord t (isRoot_single _ _)]
    simp only [pair_single_eq, cartan_d4Id]
    exact congrArg _ (congrArg (· * c) (hkey k))
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      conj_pinnedX_of_mem_torusGroup hT (isRoot_neg_single _ _),
      torusRootChar_d4TorusWord t (isRoot_neg_single _ _)]
    have hn : ∀ a : Fin τ.rank, (∑ j, τ.cartan a j * (-Pi.single (d4Id k) 1 : Fin τ.rank → ℤ) j) =
        -τ.cartan a (d4Id k) := fun a => by
      simp [Pi.single_apply, Finset.sum_neg_distrib]
    simp only [hn, cartan_d4Id]
    have hinv : t 0 ^ (-Tag.D4.cartan 0 k) * t 1 ^ (-Tag.D4.cartan 1 k) *
        t 2 ^ (-Tag.D4.cartan 2 k) * t 3 ^ (-Tag.D4.cartan 3 k) = (s k)⁻¹ := by
      rw [← Units.ext (hkey k)]
      simp only [zpow_neg, mul_inv]
    exact congrArg (pinnedX τ L (-Pi.single (d4Id k) 1))
      (congrArg (· * c) (congrArg Units.val hinv))

end Torus

section Normal

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L]

omit hτ in
theorem rootSL2_single_apply' (i : Fin τ.rank) (A : SL2 L) :
    rootSL2 τ L (Pi.single i 1) A = simpleRootSL2 τ L i A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

omit hτ in
theorem exists_scalars_of_mapsRootLines {a : ModGL τ L} (ha : a ∈ monomialSubgroup τ L)
    {w : WeylGroup τ} (hw : MapsRootLines a w) {j j' : Fin τ.rank}
    (hj : w • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j' 1) :
    ∃ s : Lˣ, ∀ c : L, a * xUnit τ L j c * a⁻¹ = xUnit τ L j' (s * c) ∧
      a * yUnit τ L j c * a⁻¹ = yUnit τ L j' (((s⁻¹ : Lˣ) : L) * c) := by
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq ha hw (isRoot_single τ j) hj
  refine ⟨s, fun c => ⟨?_, ?_⟩⟩
  · have h := hs (uSL c)
    rw [rootSL2_single_apply', rootSL2_single_apply', simpleRootSL2_uSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 τ L j') (conjSL_sl2Upper s c)).trans
      (simpleRootSL2_uSL j' _)
  · have h := hs (vSL c)
    rw [rootSL2_single_apply', rootSL2_single_apply', simpleRootSL2_vSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 τ L j') (conjSL_sl2Lower s c)).trans
      (simpleRootSL2_vSL j' _)

omit hτ in
theorem exists_normalized_of_word {J : Set (Fin τ.rank)} {r : ℕ} (idx : Fin r → Fin τ.rank)
    (hidxmem : ∀ k, idx k ∈ J) (hidx : ∀ i ∈ J, ∃ k, idx k = i)
    (hword : ∀ s : Fin r → Lˣ, ∃ T : ModGL τ L, T ∈ subsystemGroup τ L J ∧ T ∈ torusGroup τ L ∧
      ∀ (k : Fin r) (c : L), T * xUnit τ L (idx k) c * T⁻¹ = xUnit τ L (idx k) (s k * c) ∧
        T * yUnit τ L (idx k) c * T⁻¹ = yUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ J, π i ∈ J)
    (hπ' : ∀ i ∈ J, π.symm i ∈ J)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ J)
    (hact : ∀ j ∈ J, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ q n₁ : ModGL τ L, q ∈ subsystemGroup τ L J ∧ n₁ ∈ monomialSubgroup τ L ∧
      n = q * n₁ ∧ ∀ j ∈ J, ∀ c : L,
        n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c := by
  set w := weylQuotientHom τ L ⟨n, hn⟩ with hw
  set nu := canonicalRep (coxeterSystem τ) L u with hnu
  have hnuQ : nu ∈ subsystemGroup τ L J := canonicalRep_mem_subsystemGroup hu
  have hnuM : nu ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L u
  have hnuMaps : MapsRootLines nu u := mapsRootLines_canonicalRep u
  set a := nu⁻¹ * n with ha_def
  have haM : a ∈ monomialSubgroup τ L := mul_mem (inv_mem hnuM) hn
  have haMaps : MapsRootLines a (u⁻¹ * w) :=
    hnuMaps.inv.mul (mapsRootLines_weylQuotientHom ⟨n, hn⟩)
  have hae : ∀ j ∈ J, (u⁻¹ * w) • (Pi.single j 1 : Fin τ.rank → ℤ) =
      Pi.single (π j) 1 := by
    intro j hj
    rw [mul_smul, hact j hj, inv_smul_smul]
  have hsc : ∀ k : Fin r, ∃ r : Lˣ, ∀ c : L,
      a * xUnit τ L (π.symm (idx k)) c * a⁻¹ = xUnit τ L (idx k) (r * c) ∧
      a * yUnit τ L (π.symm (idx k)) c * a⁻¹ = yUnit τ L (idx k) (((r⁻¹ : Lˣ) : L) * c) :=
    fun k => by
      refine exists_scalars_of_mapsRootLines haM haMaps ?_
      rw [hae _ (hπ' _ (hidxmem k)), Equiv.apply_symm_apply]
  choose r hr using hsc
  obtain ⟨T, hTQ, hTT, ht⟩ := hword (fun k => (r k)⁻¹)
  refine ⟨nu * T⁻¹, T * a, mul_mem hnuQ (inv_mem hTQ), mul_mem (Subgroup.mem_sup_left hTT) haM,
    ?_, ?_⟩
  · rw [ha_def]
    group
  · intro j hj c
    obtain ⟨k, hk⟩ := hidx _ (hπ j hj)
    have hjk : π.symm (idx k) = j := by rw [hk, Equiv.symm_apply_apply]
    obtain ⟨h1x, h1y⟩ := hr k c
    rw [hjk] at h1x h1y
    obtain ⟨h2x, -⟩ := ht k (r k * c)
    obtain ⟨-, h2y⟩ := ht k (((r k)⁻¹ : Lˣ) * c)
    have e1 : (((r k)⁻¹ : Lˣ) : L) * (((r k : Lˣ) : L) * c) = c := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (((r k)⁻¹ : Lˣ)⁻¹ : Lˣ) * (((r k)⁻¹ : Lˣ) * c) = c := by
      rw [inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    refine ⟨?_, ?_⟩
    · calc (T * a) * xUnit τ L j c * (T * a)⁻¹
          = T * (a * xUnit τ L j c * a⁻¹) * T⁻¹ := by group
        _ = T * xUnit τ L (idx k) (r k * c) * T⁻¹ := by rw [h1x]
        _ = xUnit τ L (idx k) c := by rw [h2x, e1]
        _ = xUnit τ L (π j) c := by rw [hk]
    · calc (T * a) * yUnit τ L j c * (T * a)⁻¹
          = T * (a * yUnit τ L j c * a⁻¹) * T⁻¹ := by group
        _ = T * yUnit τ L (idx k) (((r k)⁻¹ : Lˣ) * c) * T⁻¹ := by rw [h1y]
        _ = yUnit τ L (idx k) c := by rw [h2y, e2]
        _ = yUnit τ L (π j) c := by rw [hk]

theorem exists_normalized [IsAlgClosed L] {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ)
    (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Set τ))
    (hact : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ q n₁ : ModGL τ L, q ∈ subsystemGroup τ L (d4Set τ) ∧ n₁ ∈ monomialSubgroup τ L ∧
      n = q * n₁ ∧ ∀ j ∈ d4Set τ, ∀ c : L,
        n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c :=
  exists_normalized_of_word d4Id d4Id_mem (fun _ hi => exists_d4Id_eq hi) (fun s => by
    obtain ⟨t, ht⟩ := exists_d4TorusWord_scalars (τ := τ) (L := L) s
    exact ⟨d4TorusWord t, d4TorusWord_mem_subsystemGroup t, d4TorusWord_mem_torusGroup t, ht⟩)
    hn hπ hπ' hu hact

end Normal

section Lang

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L]

omit hτ in
theorem mem_normalizer_subsystemGroup_of_conj {J : Set (Fin τ.rank)} {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i ∈ J, π i ∈ J) (hπ' : ∀ i ∈ J, π.symm i ∈ J)
    (h : ∀ j ∈ J, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) :
    n₁ ∈ Subgroup.normalizer (subsystemGroup τ L J : Set (ModGL τ L)) := by
  have hle : subsystemGroup τ L J ≤
      (subsystemGroup τ L J).comap (MulAut.conj n₁).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (h i hi c).1]
      exact xUnit_mem_subsystemGroup (hπ i hi) c
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (h i hi c).2]
      exact yUnit_mem_subsystemGroup (hπ i hi) c
  have hle' : subsystemGroup τ L J ≤
      (subsystemGroup τ L J).comap (MulAut.conj n₁⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · have e := (h (π.symm i) (hπ' i hi) c).1
      rw [Equiv.apply_symm_apply] at e
      have e' : n₁⁻¹ * xUnit τ L i c * n₁ = xUnit τ L (π.symm i) c := by
        rw [← e]
        group
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv, e']
      exact xUnit_mem_subsystemGroup (hπ' i hi) c
    · have e := (h (π.symm i) (hπ' i hi) c).2
      rw [Equiv.apply_symm_apply] at e
      have e' : n₁⁻¹ * yUnit τ L i c * n₁ = yUnit τ L (π.symm i) c := by
        rw [← e]
        group
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv, e']
      exact yUnit_mem_subsystemGroup (hπ' i hi) c
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact hle hg
  · intro hg
    have h1 := hle' hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    simpa [mul_assoc] using h1

omit hτ in
theorem exists_conj_twistedFixed_of_word [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {J : Set (Fin τ.rank)} {r : ℕ} (idx : Fin r → Fin τ.rank)
    (hidxmem : ∀ k, idx k ∈ J) (hidx : ∀ i ∈ J, ∃ k, idx k = i)
    (hword : ∀ s : Fin r → Lˣ, ∃ T : ModGL τ L, T ∈ subsystemGroup τ L J ∧ T ∈ torusGroup τ L ∧
      ∀ (k : Fin r) (c : L), T * xUnit τ L (idx k) c * T⁻¹ = xUnit τ L (idx k) (s k * c) ∧
        T * yUnit τ L (idx k) c * T⁻¹ = yUnit τ L (idx k) (((s k)⁻¹ : Lˣ) * c))
    (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ J, π i ∈ J)
    (hπ' : ∀ i ∈ J, π.symm i ∈ J)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ J)
    (hact : ∀ j ∈ J, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ n₁ h : ModGL τ L, n₁ ∈ monomialSubgroup τ L ∧ h ∈ subsystemGroup τ L J ∧
      (∀ j ∈ J, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) ∧
      ∀ g : ModGL τ L,
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
            h * g * h⁻¹ := by
  obtain ⟨q, n₁, hq, hn₁, hnq, hgen⟩ := exists_normalized_of_word idx hidxmem hidx hword hn hπ hπ' hu hact
  have hA := mem_normalizer_subsystemGroup_of_conj hπ hπ' hgen
  obtain ⟨h, hh, hlang⟩ := ((supported_native_affine_realization_and_Lang τ L J).2 ℓ f hf
    n₁ hA).2.2.2 q hq
  refine ⟨n₁, h, hn₁, hh, hgen, fun g => ?_⟩
  have e1 : n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ =
      q * frobTwistGL τ L ℓ f n₁ g * q⁻¹ := by
    rw [hnq, frobTwistGL_apply]
    simp only [entrywiseFrobGL]
    group
  rw [e1, hlang g]
  change _ ↔ frobTwistGL τ L ℓ f n₁ (h * g * h⁻¹) = h * g * h⁻¹
  generalize frobTwistGL τ L ℓ f n₁ (h * g * h⁻¹) = X
  constructor
  · intro e
    rw [← e]
    group
  · intro e
    rw [e]
    group

theorem exists_conj_twistedFixed [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ)
    (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Set τ))
    (hact : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ n₁ h : ModGL τ L, n₁ ∈ monomialSubgroup τ L ∧ h ∈ subsystemGroup τ L (d4Set τ) ∧
      (∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) ∧
      ∀ g : ModGL τ L,
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
            h * g * h⁻¹ :=
  exists_conj_twistedFixed_of_word d4Id d4Id_mem (fun _ hi => exists_d4Id_eq hi) (fun s => by
    obtain ⟨t, ht⟩ := exists_d4TorusWord_scalars (τ := τ) (L := L) s
    exact ⟨d4TorusWord t, d4TorusWord_mem_subsystemGroup t, d4TorusWord_mem_torusGroup t, ht⟩)
    hf hn hπ hπ' hu hact

end Lang

end CFSG.RankThree.PartOne.KD4T
