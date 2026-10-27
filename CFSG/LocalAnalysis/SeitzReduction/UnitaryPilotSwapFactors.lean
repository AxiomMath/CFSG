module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresMonomial
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Images

variable {S G : Type*} [Group S] [Group G]

theorem dichotomy_map_of_isQuasisimple {H : Subgroup S} (hH : CFSG.Open.IsQuasisimple H)
    (φ : S →* G) (M : Subgroup G) (hM : M ≤ H.map φ)
    (hN : H.map φ ≤ normalizer (M : Set G)) :
    M ≤ centralizer ((H.map φ : Subgroup G) : Set G) ∨ M = H.map φ := by
  set M' : Subgroup H := (M.comap φ).subgroupOf H with hM'
  have hnorm : M'.Normal := ⟨fun x hx g => by
    rw [hM', mem_subgroupOf, mem_comap] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hN ⟨g, g.2, rfl⟩) (φ x)).1 hx⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hH M' with hc | ht
  · left
    intro m hm
    obtain ⟨x, hx, rfl⟩ := hM hm
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hxc : (⟨x, hx⟩ : H) ∈ center H := hc (by rw [hM', mem_subgroupOf, mem_comap]; exact hm)
    have hyx := congrArg Subtype.val ((mem_center_iff.1 hxc) ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at hyx
    rw [← map_mul, ← map_mul, hyx]
  · right
    refine le_antisymm hM ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨x, hx⟩ : H) ∈ M' := ht ▸ mem_top _
    rwa [hM', mem_subgroupOf, mem_comap] at hx'

theorem commutator_map_eq_of_isQuasisimple {H : Subgroup S} (hH : CFSG.Open.IsQuasisimple H)
    (φ : S →* G) : ⁅H.map φ, H.map φ⁆ = H.map φ := by
  rw [← map_commutator, Subgroup.isPerfect_iff.1 ⟨hH.1⟩]

theorem map_ne_bot_of_isQuasisimple {H : Subgroup S} (hH : CFSG.Open.IsQuasisimple H)
    (φ : S →* G) (hker : φ.ker ≤ center S) : H.map φ ≠ ⊥ := by
  intro hbot
  have hHk : H ≤ center S := ((map_eq_bot_iff H).1 hbot).trans hker
  have hperf : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.1 ⟨hH.1⟩
  have hab : ⁅H, H⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 (hHk.trans (center_le_centralizer _))
  have : Nontrivial (H ⧸ center H) := hH.2.toNontrivial
  have hnt : Nontrivial H := (QuotientGroup.mk'_surjective (center H)).nontrivial
  exact (nontrivial_iff_ne_bot H).1 hnt (hperf ▸ hab)

end Images

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}
  {X : Subgroup G} {N : Finset (Fin n)}

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

@[expose] noncomputable def fst (I : Finset (Fin n)) : Subgroup G :=
  ((unitaryBlock h I).subgroupOf (unitaryBlock h N)).map (P.Ψ.comp (MonoidHom.inl _ _))

@[expose] noncomputable def snd (I : Finset (Fin n)) : Subgroup G :=
  ((unitaryBlock h I).subgroupOf (unitaryBlock h N)).map (P.Ψ.comp (MonoidHom.inr _ _))

theorem fst_def (I : Finset (Fin n)) :
    P.fst I = ((unitaryBlock h I).subgroupOf (unitaryBlock h N)).map
      (P.Ψ.comp (MonoidHom.inl _ _)) :=
  rfl

theorem snd_def (I : Finset (Fin n)) :
    P.snd I = ((unitaryBlock h I).subgroupOf (unitaryBlock h N)).map
      (P.Ψ.comp (MonoidHom.inr _ _)) :=
  rfl

theorem apply_inl_mem_fst {I : Finset (Fin n)} {x : unitaryBlock h N}
    (hx : (x : unitarySU 2 f K n) ∈ unitaryBlock h I) : P.Ψ (x, 1) ∈ P.fst I :=
  ⟨x, mem_subgroupOf.2 hx, rfl⟩

theorem apply_inr_mem_snd {I : Finset (Fin n)} {x : unitaryBlock h N}
    (hx : (x : unitarySU 2 f K n) ∈ unitaryBlock h I) : P.Ψ (1, x) ∈ P.snd I :=
  ⟨x, mem_subgroupOf.2 hx, rfl⟩

theorem fst_mono {I J : Finset (Fin n)} (hIJ : I ⊆ J) : P.fst I ≤ P.fst J :=
  map_mono fun _ hx => mem_subgroupOf.2 (unitaryBlock_mono h hIJ (mem_subgroupOf.1 hx))

theorem snd_mono {I J : Finset (Fin n)} (hIJ : I ⊆ J) : P.snd I ≤ P.snd J :=
  map_mono fun _ hx => mem_subgroupOf.2 (unitaryBlock_mono h hIJ (mem_subgroupOf.1 hx))

theorem snd_le_centralizer_fst (I J : Finset (Fin n)) :
    P.snd J ≤ centralizer (P.fst I : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, -, rfl⟩
  exact (P.commute_inl_inr x y).eq

theorem fst_le_centralizer_snd (I J : Finset (Fin n)) :
    P.fst J ≤ centralizer (P.snd I : Set G) :=
  le_centralizer_iff.1 (P.snd_le_centralizer_fst J I)

theorem map_conj_fst (I : Finset (Fin n)) :
    (P.fst I).map (MulAut.conj t).toMonoidHom = P.snd I := by
  rw [fst, snd, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap x 1

theorem map_conj_snd (I : Finset (Fin n)) :
    (P.snd I).map (MulAut.conj t).toMonoidHom = P.fst I := by
  rw [fst, snd, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap 1 x

theorem mul_conj_mem_modelToG_of_mem_fst {I : Finset (Fin n)} {x : G} (hx : x ∈ P.fst I) :
    x * (t * x * t⁻¹) ∈ modelToG e (blockSU h I) := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [P.swap, ← map_mul, show ((a, 1) : unitaryBlock h N × unitaryBlock h N) * (1, a) = (a, a) by
    ext <;> simp, P.diag]
  exact symm_mem_modelToG e (unitaryProj_mem_blockSU h (mem_subgroupOf.1 ha))

theorem mul_conj_mem_modelToG_of_mem_snd {I : Finset (Fin n)} {x : G} (hx : x ∈ P.snd I) :
    x * (t * x * t⁻¹) ∈ modelToG e (blockSU h I) := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply]
  rw [P.swap, ← map_mul, show ((1, a) : unitaryBlock h N × unitaryBlock h N) * (a, 1) = (a, a) by
    ext <;> simp, P.diag]
  exact symm_mem_modelToG e (unitaryProj_mem_blockSU h (mem_subgroupOf.1 ha))

theorem exists_mem_fst_mul_conj_eq {I : Finset (Fin n)} (hIN : I ⊆ N) {y : G}
    (hy : y ∈ modelToG e (blockSU h I)) : ∃ x ∈ P.fst I, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  obtain ⟨b, hb, rfl⟩ := hz
  set b' : unitaryBlock h N := ⟨b, unitaryBlock_mono h hIN hb⟩
  refine ⟨P.Ψ (b', 1), P.apply_inl_mem_fst hb, ?_⟩
  rw [P.swap, ← map_mul, show ((b', 1) : unitaryBlock h N × unitaryBlock h N) * (1, b') =
    (b', b') by ext <;> simp, P.diag]

theorem exists_mem_snd_mul_conj_eq {I : Finset (Fin n)} (hIN : I ⊆ N) {y : G}
    (hy : y ∈ modelToG e (blockSU h I)) : ∃ x ∈ P.snd I, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  obtain ⟨b, hb, rfl⟩ := hz
  set b' : unitaryBlock h N := ⟨b, unitaryBlock_mono h hIN hb⟩
  refine ⟨P.Ψ (1, b'), P.apply_inr_mem_snd hb, ?_⟩
  rw [P.swap, ← map_mul, show ((1, b') : unitaryBlock h N × unitaryBlock h N) * (b', 1) =
    (b', b') by ext <;> simp, P.diag]

theorem map_prod_eq_fst_sup_snd (I : Finset (Fin n)) :
    (((unitaryBlock h I).subgroupOf (unitaryBlock h N)).prod
      ((unitaryBlock h I).subgroupOf (unitaryBlock h N))).map P.Ψ = P.fst I ⊔ P.snd I := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxy : ((x, y) : unitaryBlock h N × unitaryBlock h N) = (x, 1) * (1, y) := by
      ext <;> simp
    rw [hxy, map_mul]
    exact mul_mem (mem_sup_left ⟨x, hx, rfl⟩) (mem_sup_right ⟨y, hy, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(x, 1), ⟨hx, one_mem _⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(1, y), ⟨one_mem _, hy⟩, rfl⟩

theorem pieceCore_eq_fst_sup_snd [Finite G] {I : Finset (Fin n)} (hIN : I ⊆ N)
    (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    pieceCore e I = P.fst I ⊔ P.snd I := by
  rw [P.pieceCore_eq_map hIN hI2 hIc hperf hXI, P.map_prod_eq_fst_sup_snd]

theorem ker_comp_inl_le_center :
    (P.Ψ.comp (MonoidHom.inl _ _)).ker ≤ center (unitaryBlock h N) := by
  intro x hx
  have hc := P.ker_le (show ((x, 1) : unitaryBlock h N × unitaryBlock h N) ∈ P.Ψ.ker from hx)
  rw [mem_center_iff] at hc ⊢
  intro y
  simpa using congrArg Prod.fst (hc (y, 1))

theorem ker_comp_inr_le_center :
    (P.Ψ.comp (MonoidHom.inr _ _)).ker ≤ center (unitaryBlock h N) := by
  intro x hx
  have hc := P.ker_le (show ((1, x) : unitaryBlock h N × unitaryBlock h N) ∈ P.Ψ.ker from hx)
  rw [mem_center_iff] at hc ⊢
  intro y
  simpa using congrArg Prod.snd (hc (1, y))

end SwapNeighbourParam

end Factors

section Blocks

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem isQuasisimple_unitaryBlock_subgroupOf {I N : Finset (Fin n)} (hIN : I ⊆ N)
    (hI3 : 3 ≤ I.card) (hIq : (I.card, 2 ^ f) ≠ (3, 2)) :
    CFSG.Open.IsQuasisimple ((unitaryBlock h I).subgroupOf (unitaryBlock h N)) := by
  have hq : CFSG.IsQuasisimple ((unitaryBlock h I).subgroupOf (unitaryBlock h N)) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      ((unitaryBlockEquiv h I).trans
        (Subgroup.subgroupOfEquivOfLe (unitaryBlock_mono h hIN)).symm)
      (isQuasisimple_unitarySU h hI3 hIq)
  have := hq.1
  exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩

theorem permSU_swap_mul_commutator_ne {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {κ : (Units.map h.normHom).ker} (hκ : (κ : Kˣ) ≠ 1) :
    permSU h (Equiv.swap i k) * (permSU h (Equiv.swap i j) *
        torusDiagSU h (unitaryRootTorusHom h hij κ) * (permSU h (Equiv.swap i j))⁻¹ *
          (torusDiagSU h (unitaryRootTorusHom h hij κ))⁻¹) ≠
      (permSU h (Equiv.swap i j) * torusDiagSU h (unitaryRootTorusHom h hij κ) *
          (permSU h (Equiv.swap i j))⁻¹ * (torusDiagSU h (unitaryRootTorusHom h hij κ))⁻¹) *
        permSU h (Equiv.swap i k) := by
  intro hcomm
  set c₀ := unitaryRootTorusHom h hij κ with hc₀
  have hw : permSU h (Equiv.swap i j) * torusDiagSU h c₀ * (permSU h (Equiv.swap i j))⁻¹ =
      torusDiagSU h (unitaryPermParam h (Equiv.swap i j) c₀) := by
    have := permSU_mul_torusDiagSU h (Equiv.swap i j) c₀
    rwa [Equiv.symm_swap] at this
  set c₁ := unitaryPermParam h (Equiv.swap i j) c₀ * c₀⁻¹ with hc₁
  have hc : permSU h (Equiv.swap i j) * torusDiagSU h c₀ * (permSU h (Equiv.swap i j))⁻¹ *
      (torusDiagSU h c₀)⁻¹ = torusDiagSU h c₁ := by
    rw [hw, hc₁, map_mul, map_inv]
  rw [hc] at hcomm
  have hσ : permSU h (Equiv.swap i k) * torusDiagSU h c₁ * (permSU h (Equiv.swap i k))⁻¹ =
      torusDiagSU h (unitaryPermParam h (Equiv.swap i k) c₁) := by
    have := permSU_mul_torusDiagSU h (Equiv.swap i k) c₁
    rwa [Equiv.symm_swap] at this
  have heq : torusDiagSU h (unitaryPermParam h (Equiv.swap i k) c₁) = torusDiagSU h c₁ := by
    rw [← hσ, hcomm, mul_inv_cancel_right]
  have hkk := congrArg
    (fun A : unitarySU 2 f K n => ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k k) heq
  simp only [coe_torusDiagSU, diagonal_apply_eq] at hkk
  have e1 : (unitaryPermParam h (Equiv.swap i k) c₁).1 k = (κ : Kˣ)⁻¹ * (κ : Kˣ)⁻¹ := by
    change c₀.1 ((Equiv.swap i j).symm ((Equiv.swap i k).symm k)) *
      (c₀.1 ((Equiv.swap i k).symm k))⁻¹ = _
    rw [Equiv.symm_swap, Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left]
    change LinearPilot.rootTorusParam i j (κ : Kˣ) j *
      (LinearPilot.rootTorusParam i j (κ : Kˣ) i)⁻¹ = _
    rw [LinearPilot.rootTorusParam_apply_right hij, LinearPilot.rootTorusParam_apply_left]
  have e2 : c₁.1 k = 1 := by
    change c₀.1 ((Equiv.swap i j).symm k) * (c₀.1 k)⁻¹ = 1
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm, mul_inv_cancel]
  rw [e1, e2] at hkk
  have hu : (κ : Kˣ)⁻¹ * (κ : Kˣ)⁻¹ = 1 := Units.ext hkk
  have hinv : (κ : Kˣ)⁻¹ = κ := by
    rw [mul_eq_one_iff_eq_inv, inv_inv] at hu
    exact hu
  exact coe_ne_coe_inv_of_ne_one h hκ (by rw [hinv])

end Blocks

section Intrinsic

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}
  {X : Subgroup G} {N : Finset (Fin n)}

namespace SwapNeighbourParam

variable (P : SwapNeighbourParam e t X N)

theorem commutator_fst {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) : ⁅P.fst I, P.fst I⁆ = P.fst I :=
  commutator_map_eq_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _

theorem commutator_snd {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) : ⁅P.snd I, P.snd I⁆ = P.snd I :=
  commutator_map_eq_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _

theorem fst_ne_bot {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) : P.fst I ≠ ⊥ :=
  map_ne_bot_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _
    P.ker_comp_inl_le_center

theorem snd_ne_bot {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) : P.snd I ≠ ⊥ :=
  map_ne_bot_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _
    P.ker_comp_inr_le_center

theorem dichotomy_fst {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) (M : Subgroup G) (hM : M ≤ P.fst I)
    (hn : P.fst I ≤ normalizer (M : Set G)) :
    M ≤ centralizer (P.fst I : Set G) ∨ M = P.fst I :=
  dichotomy_map_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _ M hM hn

theorem dichotomy_snd {I : Finset (Fin n)} (hIN : I ⊆ N) (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) (M : Subgroup G) (hM : M ≤ P.snd I)
    (hn : P.snd I ≤ normalizer (M : Set G)) :
    M ≤ centralizer (P.snd I : Set G) ∨ M = P.snd I :=
  dichotomy_map_of_isQuasisimple (isQuasisimple_unitaryBlock_subgroupOf h hIN hI3 hIq) _ M hM hn

theorem fst_eq_or_eq [Finite G] {X' : Subgroup G} {N' : Finset (Fin n)}
    (P' : SwapNeighbourParam e t X' N') {I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N')
    (hI3 : 3 ≤ I.card) (hIq : (I.card, 2 ^ f) ≠ (3, 2)) (hIc : 2 ≤ Iᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I)) :
    P'.fst I = P.fst I ∨ P'.fst I = P.snd I := by
  have hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I :=
    commutator_unitaryBlock_eq_of_three_le h hI3 hIq
  have hM : P.fst I ⊔ P.snd I = P'.fst I ⊔ P'.snd I := by
    rw [← P.pieceCore_eq_fst_sup_snd hIN (by omega) hIc hperf hXI,
      ← P'.pieceCore_eq_fst_sup_snd hIN' (by omega) hIc hperf hXI']
  exact F4Pilot.eq_or_eq_of_perfect_of_le_sup (P.snd_le_centralizer_fst I I)
    (P.dichotomy_fst hIN hI3 hIq) (P.dichotomy_snd hIN hI3 hIq) (P'.commutator_fst hIN' hI3 hIq)
    (P'.fst_ne_bot hIN' hI3 hIq) (P'.dichotomy_fst hIN' hI3 hIq) (hM ▸ le_sup_left)
    (hM ▸ F4Pilot.sup_le_normalizer_left_of_le_centralizer (P'.snd_le_centralizer_fst I I))

theorem snd_eq_or_eq [Finite G] {X' : Subgroup G} {N' : Finset (Fin n)}
    (P' : SwapNeighbourParam e t X' N') {I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N')
    (hI3 : 3 ≤ I.card) (hIq : (I.card, 2 ^ f) ≠ (3, 2)) (hIc : 2 ≤ Iᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I)) :
    P'.snd I = P.fst I ∨ P'.snd I = P.snd I := by
  have hperf : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I :=
    commutator_unitaryBlock_eq_of_three_le h hI3 hIq
  have hM : P.fst I ⊔ P.snd I = P'.snd I ⊔ P'.fst I := by
    rw [← P.pieceCore_eq_fst_sup_snd hIN (by omega) hIc hperf hXI, sup_comm,
      ← P'.pieceCore_eq_fst_sup_snd hIN' (by omega) hIc hperf hXI']
  exact F4Pilot.eq_or_eq_of_perfect_of_le_sup (P.snd_le_centralizer_fst I I)
    (P.dichotomy_fst hIN hI3 hIq) (P.dichotomy_snd hIN hI3 hIq) (P'.commutator_snd hIN' hI3 hIq)
    (P'.snd_ne_bot hIN' hI3 hIq) (P'.dichotomy_snd hIN' hI3 hIq) (hM ▸ le_sup_left)
    (hM ▸ F4Pilot.sup_le_normalizer_left_of_le_centralizer (P'.fst_le_centralizer_snd I I))

omit [Group G] in
theorem pair_subset_of_mem {i j : Fin n} (hi : i ∈ N) (hj : j ∈ N) :
    ({i, j} : Finset (Fin n)) ⊆ N := by
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact hi
  · rw [Finset.mem_singleton.1 hx]
    exact hj

theorem not_le_centralizer_fst_pair {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i ∈ N) (hj : j ∈ N) (hk : k ∈ N) :
    ¬ P.fst {i, j} ≤ centralizer (modelToG e (blockSU h {i, j}) : Set G) := by
  intro hle
  obtain ⟨κ, hκN, hκ⟩ := exists_norm_eq_one_ne_one h
  set κ' : (Units.map h.normHom).ker := ⟨κ, h.mem_ker_normUnits.2 hκN⟩ with hκ'
  have hw₀ := permSU_swap_mem_unitaryBlock h i j
  have hd₀ := torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock h hij κ'
  set w : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hj) hw₀⟩ with hw
  set d : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hj) hd₀⟩ with hd
  have h1 : P.Ψ (w, 1) ∈ P.fst {i, j} := P.apply_inl_mem_fst hw₀
  have h2 : P.Ψ (d, d) ∈ modelToG e (blockSU h {i, j}) := by
    rw [P.diag]
    exact symm_mem_modelToG e (unitaryProj_mem_blockSU h hd₀)
  have hcomm : P.Ψ (d, d) * P.Ψ (w, 1) = P.Ψ (w, 1) * P.Ψ (d, d) :=
    mem_centralizer_iff.1 (hle h1) _ h2
  have hker : ((w * d * w⁻¹ * d⁻¹, 1) : unitaryBlock h N × unitaryBlock h N) ∈ P.Ψ.ker := by
    rw [MonoidHom.mem_ker]
    have hsplit : ((w * d * w⁻¹ * d⁻¹, 1) : unitaryBlock h N × unitaryBlock h N) =
        (w, 1) * (d, d) * (w, 1)⁻¹ * (d, d)⁻¹ := by
      ext <;> simp
    rw [hsplit, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hσ₀ := permSU_swap_mem_unitaryBlock h i k
  set σ : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hk) hσ₀⟩ with hσ
  have hc := congrArg (fun z : unitaryBlock h N × unitaryBlock h N =>
    ((z.1 : unitaryBlock h N) : unitarySU 2 f K n)) ((mem_center_iff.1 (P.ker_le hker)) (σ, 1))
  simp only [Prod.mk_mul_mk, mul_one, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  exact permSU_swap_mul_commutator_ne h hij hik hjk (κ := κ') hκ hc

theorem not_le_centralizer_snd_pair {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i ∈ N) (hj : j ∈ N) (hk : k ∈ N) :
    ¬ P.snd {i, j} ≤ centralizer (modelToG e (blockSU h {i, j}) : Set G) := by
  intro hle
  obtain ⟨κ, hκN, hκ⟩ := exists_norm_eq_one_ne_one h
  set κ' : (Units.map h.normHom).ker := ⟨κ, h.mem_ker_normUnits.2 hκN⟩ with hκ'
  have hw₀ := permSU_swap_mem_unitaryBlock h i j
  have hd₀ := torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock h hij κ'
  set w : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hj) hw₀⟩ with hw
  set d : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hj) hd₀⟩ with hd
  have h1 : P.Ψ (1, w) ∈ P.snd {i, j} := P.apply_inr_mem_snd hw₀
  have h2 : P.Ψ (d, d) ∈ modelToG e (blockSU h {i, j}) := by
    rw [P.diag]
    exact symm_mem_modelToG e (unitaryProj_mem_blockSU h hd₀)
  have hcomm : P.Ψ (d, d) * P.Ψ (1, w) = P.Ψ (1, w) * P.Ψ (d, d) :=
    mem_centralizer_iff.1 (hle h1) _ h2
  have hker : ((1, w * d * w⁻¹ * d⁻¹) : unitaryBlock h N × unitaryBlock h N) ∈ P.Ψ.ker := by
    rw [MonoidHom.mem_ker]
    have hsplit : ((1, w * d * w⁻¹ * d⁻¹) : unitaryBlock h N × unitaryBlock h N) =
        (1, w) * (d, d) * (1, w)⁻¹ * (d, d)⁻¹ := by
      ext <;> simp
    rw [hsplit, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hσ₀ := permSU_swap_mem_unitaryBlock h i k
  set σ : unitaryBlock h N := ⟨_, unitaryBlock_mono h (pair_subset_of_mem hi hk) hσ₀⟩ with hσ
  have hc := congrArg (fun z : unitaryBlock h N × unitaryBlock h N =>
    ((z.2 : unitaryBlock h N) : unitarySU 2 f K n)) ((mem_center_iff.1 (P.ker_le hker)) (1, σ))
  simp only [Prod.mk_mul_mk, one_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  exact permSU_swap_mul_commutator_ne h hij hik hjk (κ := κ') hκ hc

end SwapNeighbourParam

end Intrinsic

end CFSG.SeitzReduction.UnitaryPilot
