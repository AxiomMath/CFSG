module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
import CFSG.GroupTheory.WeirSylow.UnitaryBridge
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutBasic

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (StatedSp StatedSU)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem zmod3_mul_self' {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private theorem tau_single_mem (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i : Fin m} (hi : e i ≠ 0) (x : ZMod 3) :
    tau ζ m (Pi.single i x) ∈ blockGroup ζ m (.extension e) := by
  refine tau_mem_blockGroup_extension hK hζ fun l hl => ?_
  rw [Pi.single_eq_of_ne fun hli => hi (by rw [← hli]; exact hl)]

private theorem detF4_tau_single (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i : Fin m} (hi : e i ≠ 0) (c : ZMod 3) :
    detF4 hK hζ e ⟨_, tau_single_mem hK hζ hi (c * e i)⟩ =
      zetaC ζ (Multiplicative.ofAdd c) := by
  rw [detF4_tau hK hζ (tau_single_mem hK hζ hi (c * e i))]
  congr 2
  rw [Finset.sum_eq_single
    (⟨i, (PlaneRaw.mem_extSupport e i).mpr hi⟩ : ↥(PlaneRaw.Code.extSupport e))]
  · rw [Pi.single_eq_same]
    calc e i * (c * e i) = c * (e i * e i) := by ring
      _ = c := by rw [zmod3_mul_self' hi, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne fun h => hb (Subtype.ext h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem mk_tau_single_injective (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} {i : Fin m} (hi : e i ≠ 0) :
    Function.Injective fun c : ZMod 3 =>
      (QuotientGroup.mk ⟨_, tau_single_mem hK hζ hi (c * e i)⟩ :
        ↥(blockGroup ζ m (.extension e)) ⧸ (detF4 hK hζ e).ker) := by
  intro c c' h
  have h' := ((detF4 hK hζ e).eq_iff.mpr (QuotientGroup.eq.mp h)).symm
  rw [detF4_tau_single hK hζ hi c, detF4_tau_single hK hζ hi c'] at h'
  exact Multiplicative.ofAdd.injective (zetaC_injective hζ h')

private theorem three_le_index_ker_detF4 (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    3 ≤ (detF4 hK hζ e).ker.index := by
  obtain ⟨i, hi⟩ : (PlaneRaw.Code.extSupport e).Nonempty := by
    rw [← Finset.card_pos]
    omega
  rw [Subgroup.index_eq_card]
  calc 3 = Nat.card (ZMod 3) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective _
      (mk_tau_single_injective hK hζ ((PlaneRaw.mem_extSupport e i).mp hi))

private theorem index_commutator_blockGroup_le (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    (commutator ↥(blockGroup ζ m (.extension e))).index ≤ 3 := by
  let B := blockGroup ζ m (.extension e)
  let C : Subgroup ↥B := commutator ↥B
  change C.index ≤ 3
  have he0 : e ≠ 0 := by
    intro h
    have : (PlaneRaw.Code.extSupport e).card = 0 := by
      rw [h]
      simp [PlaneRaw.Code.extSupport]
    omega
  obtain ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨ψ⟩⟩ :=
    exists_blockGroup_extension_mulEquiv (ζ := ζ) (m := m) hK hζ he0
  let : Field E := hEfield
  let : Finite E := hEfin
  let : CharP E 2 := hEchar
  let k := (PlaneRaw.Code.extSupport e).card
  have hk : 4 ≤ k := he
  have hCmap : Subgroup.map ψ.toMonoidHom C = commutator ↥(ClassicalBlocks.GUFull k 2 E) := by
    change Subgroup.map ψ.toMonoidHom (commutator ↥B) = commutator ↥(ClassicalBlocks.GUFull k 2 E)
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 ψ.surjective]
  have hCindex_eq : C.index = (commutator ↥(ClassicalBlocks.GUFull k 2 E)).index := by
    rw [← hCmap]
    exact (Subgroup.index_map_equiv C ψ).symm
  rw [hCindex_eq]
  have hcomm_eq : commutator ↥(ClassicalBlocks.GUFull k 2 E) =
      (StatedSU k 2 E).subgroupOf (ClassicalBlocks.GUFull k 2 E) := by
    apply Subgroup.map_injective (ClassicalBlocks.GUFull k 2 E).subtype_injective
    rw [Subgroup.map_subtype_commutator]
    rw [Subgroup.map_subgroupOf_eq_of_le ?_]
    · exact commutator_guFull_eq_statedSU hEcard hk
    · rw [← commutator_guFull_eq_statedSU hEcard hk]
      exact Subgroup.commutator_le_self _
  rw [hcomm_eq]
  let detGU : ↥(ClassicalBlocks.GUFull k 2 E) →* Eˣ :=
    (Matrix.GeneralLinearGroup.det : GL (Fin k) E →* Eˣ).comp
      (ClassicalBlocks.GUFull k 2 E).subtype
  have hker_le : detGU.ker ≤ (StatedSU k 2 E).subgroupOf (ClassicalBlocks.GUFull k 2 E) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxGU : (x : GL (Fin k) E) ∈ ClassicalBlocks.GUFull k 2 E := x.2
    have hxdet : (x : GL (Fin k) E).det = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      simpa [detGU, MonoidHom.comp_apply] using h
    let : Fintype E := Fintype.ofFinite E
    obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := 2) (by
      rw [← Nat.card_eq_fintype_card]; exact hEcard)
    open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure in
    exact mem_statedSU_of_mem_statedGU hUF hQf hxGU
      (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hxdet)
  calc ((StatedSU k 2 E).subgroupOf (ClassicalBlocks.GUFull k 2 E)).index
      ≤ detGU.ker.index := by
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hker_le)
    _ = Nat.card (Set.range detGU) := Subgroup.index_ker _
    _ ≤ Nat.card Eˣ := Finite.card_subtype_le _
    _ = 3 := by
      classical
      let : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hEcard]
      norm_num

private theorem commutator_le_ker_detF4 (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (e : PlaneRaw.V m) :
    commutator ↥(blockGroup ζ m (.extension e)) ≤ (detF4 hK hζ e).ker := by
  let B := blockGroup ζ m (.extension e)
  intro x hx
  have hxY : (x : ↥(StatedSp m K)) ∈ Ycode ζ m (.extension e) := by
    have hxmap : B.subtype x ∈ (commutator ↥B).map B.subtype := Subgroup.mem_map_of_mem _ hx
    rwa [Subgroup.map_subtype_commutator] at hxmap
  have hxeq : x = ⟨(x : ↥(StatedSp m K)), ycode_le_blockGroup ζ _ hxY⟩ := Subtype.ext rfl
  rw [hxeq]
  exact detF4_eq_one_of_mem_ycode hK hζ hxY

private theorem commutator_eq_ker_detF4 (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    commutator ↥(blockGroup ζ m (.extension e)) = (detF4 hK hζ e).ker := by
  let B := blockGroup ζ m (.extension e)
  let C : Subgroup ↥B := commutator ↥B
  let D : Subgroup ↥B := (detF4 hK hζ e).ker
  have hCD : C ≤ D := commutator_le_ker_detF4 hK hζ e
  have hCindex_eq : C.index = D.index := by
    refine le_antisymm ((index_commutator_blockGroup_le hK hζ he).trans
      (three_le_index_ker_detF4 hK hζ he)) ?_
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hCD)
  refine le_antisymm hCD (Subgroup.relIndex_eq_one.mp ?_)
  have h := Subgroup.relIndex_mul_index hCD
  rw [hCindex_eq] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (by rw [one_mul]; exact h)

theorem mem_ycode_extension_iff_detF4 (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card)
    {g : ↥(StatedSp m K)} (hg : g ∈ blockGroup ζ m (.extension e)) :
    g ∈ Ycode ζ m (.extension e) ↔ detF4 hK hζ e ⟨g, hg⟩ = 1 := by
  let B := blockGroup ζ m (.extension e)
  rw [← MonoidHom.mem_ker, ← commutator_eq_ker_detF4 hK hζ he]
  constructor
  · intro hgY
    have hgY' : g ∈ ⁅B, B⁆ := hgY
    rw [← Subgroup.map_subtype_commutator] at hgY'
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hgY'
    have hxeq' : x = ⟨g, hg⟩ := Subtype.ext hxeq
    rwa [hxeq'] at hx
  · intro hmem
    have hgY' : B.subtype ⟨g, hg⟩ ∈ ⁅B, B⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map_of_mem _ hmem
    exact hgY'

private theorem ker_detF4_index (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    (detF4 hK hζ e).ker.index = 3 := by
  refine le_antisymm ?_ (three_le_index_ker_detF4 hK hζ he)
  rw [← commutator_eq_ker_detF4 hK hζ he]
  exact index_commutator_blockGroup_le hK hζ he

private theorem exists_detF4_eq_zetaC (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card)
    (g : ↥(blockGroup ζ m (.extension e))) :
    ∃ c : ZMod 3, detF4 hK hζ e g = zetaC ζ (Multiplicative.ofAdd c) := by
  obtain ⟨i, hi⟩ : (PlaneRaw.Code.extSupport e).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hi' : e i ≠ 0 := (PlaneRaw.mem_extSupport e i).mp hi
  have hcard : Nat.card (ZMod 3) =
      Nat.card (↥(blockGroup ζ m (.extension e)) ⧸ (detF4 hK hζ e).ker) := by
    rw [← Subgroup.index_eq_card, ker_detF4_index hK hζ he]
    simp
  obtain ⟨c, hc⟩ := ((mk_tau_single_injective hK hζ hi').bijective_of_nat_card_le hcard.ge).2
    (QuotientGroup.mk g)
  refine ⟨c, ?_⟩
  rw [← detF4_tau_single hK hζ hi' c]
  exact (detF4 hK hζ e).eq_iff.mpr (QuotientGroup.eq.mp hc)

section TwistedSwaps

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem orientCoeff_of_ne_zero {x : ZMod 3} (h : x ≠ 0) :
    (if x = -1 then (-1 : ZMod 3) else 1) = x := by
  revert x
  decide

private theorem orientCoeff_mul_self (x : ZMod 3) :
    (if x = -1 then (-1 : ZMod 3) else 1) * (if x = -1 then (-1 : ZMod 3) else 1) = 1 := by
  revert x
  decide

private theorem orientEquiv_apply' {m : ℕ} (e v : PlaneRaw.V m) (k : Fin m) :
    PlaneRaw.orientEquiv m e v k = (if e k = -1 then (-1 : ZMod 3) else 1) * v k := by
  simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private theorem swapEquiv_apply' {m : ℕ} (i j : Fin m) (v : PlaneRaw.V m) (k : Fin m) :
    PlaneRaw.swapEquiv m i j v k = v (Equiv.swap i j k) := by
  simp [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private theorem orientEquiv_mul_self' {m : ℕ} (e : PlaneRaw.V m) :
    PlaneRaw.orientEquiv m e * PlaneRaw.orientEquiv m e = 1 := by
  ext w k
  rw [LinearEquiv.mul_apply, orientEquiv_apply', orientEquiv_apply', ← mul_assoc,
    orientCoeff_mul_self, one_mul]
  rfl

private theorem swapVec_eq_swapTwist {m : ℕ} (e : PlaneRaw.V m) {i j : Fin m}
    (hij : i ≠ j) (hi : e i ≠ 0) (hj : e j ≠ 0) (u : PlaneRaw.V m) :
    swapVec e i j u = PlaneRaw.swapTwist m e i j u := by
  have h_inv : (PlaneRaw.orientEquiv m e)⁻¹ = PlaneRaw.orientEquiv m e :=
    inv_eq_of_mul_eq_one_left (orientEquiv_mul_self' e)
  funext k
  rw [PlaneRaw.swapTwist, h_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, orientEquiv_apply',
    swapEquiv_apply', orientEquiv_apply']
  by_cases hki : k = i
  · subst hki
    rw [swapVec_apply_fst e hij, Equiv.swap_apply_left, orientCoeff_of_ne_zero hi,
      orientCoeff_of_ne_zero hj, mul_assoc]
  · by_cases hkj : k = j
    · subst hkj
      rw [swapVec_apply_snd, Equiv.swap_apply_right, orientCoeff_of_ne_zero hi,
        orientCoeff_of_ne_zero hj]
      ring
    · rw [swapVec_apply_of_ne e hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj, ← mul_assoc,
        orientCoeff_mul_self, one_mul]

private theorem swapTwist_self {m : ℕ} (e : PlaneRaw.V m) (i : Fin m) :
    PlaneRaw.swapTwist m e i i = 1 := by
  have h : PlaneRaw.swapEquiv m i i = 1 := by
    ext u k
    rw [swapEquiv_apply', Equiv.swap_self, Equiv.refl_apply]
    rfl
  rw [PlaneRaw.swapTwist, h, mul_one, inv_mul_cancel]

theorem swapTwist_mem_torusAut_ycode (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) {i j : Fin m}
    (hi : e i ≠ 0) (hj : e j ≠ 0) :
    PlaneRaw.swapTwist m e i j ∈ torusAut ζ m (Ycode ζ m (.extension e)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [swapTwist_self]
    exact one_mem_torusAut ζ m _
  have hσB := extSwap_mem_blockGroup hK hζ hi hj hij
  obtain ⟨c, hc⟩ := exists_detF4_eq_zetaC hK hζ he ⟨_, hσB⟩
  have hwB := tau_single_mem hK hζ hi (-c * e i)
  have hyY : extSwap e i j hij * tau ζ m (Pi.single i (-c * e i)) ∈
      Ycode ζ m (.extension e) := by
    rw [mem_ycode_extension_iff_detF4 hK hζ he (mul_mem hσB hwB)]
    change detF4 hK hζ e (⟨_, hσB⟩ * ⟨_, hwB⟩) = 1
    rw [map_mul, hc, detF4_tau_single hK hζ hi (-c), ← map_mul (zetaC ζ), ← ofAdd_add,
      add_neg_cancel, ofAdd_zero, map_one]
  refine ⟨_, hyY, fun u => ?_⟩
  have hw := tau_mul_comm ζ m (Pi.single i (-c * e i)) u
  calc _ = extSwap e i j hij * (tau ζ m (Pi.single i (-c * e i)) * tau ζ m u) *
        (tau ζ m (Pi.single i (-c * e i)))⁻¹ * (extSwap e i j hij)⁻¹ := by group
    _ = extSwap e i j hij * tau ζ m u * (extSwap e i j hij)⁻¹ := by rw [hw]; group
    _ = tau ζ m (swapVec e i j u) := extSwap_conj_tau hK hζ hij hi hj u
    _ = _ := by rw [swapVec_eq_swapTwist e hij hi hj u]

theorem twistedPermGroupOn_subset_torusAut_ycode (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {e : PlaneRaw.V m} (he : 4 ≤ (PlaneRaw.Code.extSupport e).card) :
    ((PlaneRaw.twistedPermGroupOn m e : Subgroup _) : Set _) ⊆
      torusAut ζ m (Ycode ζ m (.extension e)) := by
  refine closure_subset_torusAut ζ m ?_
  rintro _ ⟨i, j, hi, hj, rfl⟩
  exact swapTwist_mem_torusAut_ycode hK hζ he hi hj

end TwistedSwaps

end CFSG.StandardType.GGQ2Frame.SpBlocks
