module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs

@[expose] noncomputable def coorootSp (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    StatedSp (m + 2) K :=
  SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c * Pi.mulSingle 1 c⁻¹)

@[expose] noncomputable def rootDiagSp (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    StatedSp (m + 2) K :=
  longBlock K (m + 2) 1 (SymplecticTorusWeyl.sl2Diag c⁻¹)

private theorem lam_eq_longBlock_C04 {r : ℕ} {K : Type} [Field K] (i : Fin r)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    SymplecticTorusWeyl.lam i g = longBlock K r i g := by
  apply SymplecticTorusWeyl.statedSp_ext
  rfl

private theorem rootDiagSp_eq_torusHom_C04 (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    rootDiagSp m c = SymplecticTorusWeyl.torusHom (Pi.mulSingle 1 c⁻¹) := by
  rw [rootDiagSp, ← lam_eq_longBlock_C04, SymplecticTorusWeyl.lam_sl2Diag]

private theorem sl2Diag_injective_C04 {K : Type} [Field K] :
    Function.Injective (SymplecticTorusWeyl.sl2Diag (k := K)) := by
  intro a b h
  have h00 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [SymplecticTorusWeyl.coe_sl2Diag] at h00
  exact Units.ext h00

private theorem coorootSp_eq_mul_C04 (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    coorootSp m c = SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c) * rootDiagSp m c := by
  rw [coorootSp, map_mul, rootDiagSp_eq_torusHom_C04]

private theorem suppGroup_mono_C04 {n : ℕ} {K : Type} [Field K]
    {S T : Set (Fin n ⊕ Fin n)} (h : S ⊆ T) :
    suppGroup (K := K) S ≤ suppGroup T :=
  fun _ hx r t hrt => hx r t (fun hh => hrt ⟨h hh.1, h hh.2⟩)

private theorem coorootSp_inv_C04 (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    (coorootSp m c)⁻¹ = coorootSp m c⁻¹ := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one' (n := m + 1)
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    rw [← Fin.succ_zero_eq_one' (n := m + 1)] at h
    exact Fin.succ_ne_zero (0 : Fin (m + 1)) h
  rw [coorootSp, coorootSp, ← map_inv]
  congr 1
  funext i
  by_cases hi0 : i = 0
  · subst hi0
    simp [Pi.mulSingle_apply, h01]
  · by_cases hi1 : i = 1
    · subst hi1
      simp [Pi.mulSingle_apply, h10]
    · simp [Pi.mulSingle_apply, hi0, hi1]

theorem rootDiagSp_mem_longRootSp2 (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    rootDiagSp m c ∈ longRootSp2 K (m + 2) 1 := by
  exact ⟨SymplecticTorusWeyl.sl2Diag c⁻¹, rfl⟩

theorem orderOf_rootDiagSp (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    orderOf (rootDiagSp m c) = orderOf c := by
  rw [rootDiagSp, orderOf_injective (longBlock K (m + 2) 1) (longBlock_injective 1),
    orderOf_injective (SymplecticTorusWeyl.sl2Diag (k := K)) sl2Diag_injective_C04,
    orderOf_inv]

theorem orderOf_coorootSp (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    orderOf (coorootSp m c) = orderOf c := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one' (n := m + 1)
  rw [coorootSp,
    orderOf_injective (SymplecticTorusWeyl.torusHom (r := m + 2) (k := K))
      SymplecticTorusWeyl.torusHom_injective,
    orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    have := congrFun h 0
    simpa [Pi.mulSingle_apply, h01] using this
  · intro h
    have h10 : (1 : Fin (m + 2)) ≠ 0 := by
      intro hh
      rw [← Fin.succ_zero_eq_one' (n := m + 1)] at hh
      exact Fin.succ_ne_zero (0 : Fin (m + 1)) hh
    funext i
    by_cases hi0 : i = 0
    · subst hi0
      simp [Pi.mulSingle_apply, h01, h]
    · by_cases hi1 : i = 1
      · subst hi1
        simp [Pi.mulSingle_apply, h10, h]
      · simp [Pi.mulSingle_apply, hi0, hi1]

theorem coorootSp_mul_mul_inv_eq (m : ℕ) {K : Type} [Field K] (c : Kˣ) {x : StatedSp (m + 2) K}
    (hx : x ∈ longRootSp2 K (m + 2) 1) :
    coorootSp m c * x * (coorootSp m c)⁻¹ = rootDiagSp m c * x * (rootDiagSp m c)⁻¹ := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one' (n := m + 1)
  have hz : SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c) ∈
      suppGroup (K := K) (coords (0 : Fin (m + 2))) := by
    rw [← range_longBlock]
    exact ⟨SymplecticTorusWeyl.sl2Diag c, by
      rw [← lam_eq_longBlock_C04, SymplecticTorusWeyl.lam_sl2Diag]⟩
  have hsub : coords (0 : Fin (m + 2)) ⊆ (coords (1 : Fin (m + 2)))ᶜ := by
    intro a ha hb
    rw [mem_coords] at ha hb
    rcases ha with h | h <;> rcases hb with h' | h'
    · exact h01 (Sum.inl.inj (h.symm.trans h'))
    · exact Sum.inl_ne_inr (h.symm.trans h')
    · exact Sum.inr_ne_inl (h.symm.trans h')
    · exact h01 (Sum.inr.inj (h.symm.trans h'))
  have hdx : rootDiagSp m c * x * (rootDiagSp m c)⁻¹ ∈ longRootSp2 K (m + 2) 1 :=
    mul_mem (mul_mem (rootDiagSp_mem_longRootSp2 m c) hx)
      (inv_mem (rootDiagSp_mem_longRootSp2 m c))
  have hdx' : rootDiagSp m c * x * (rootDiagSp m c)⁻¹ ∈
      suppGroup (K := K) (coords (1 : Fin (m + 2))) := by
    rwa [← longRootSp2_eq_suppGroup]
  have hcomm : Commute (rootDiagSp m c * x * (rootDiagSp m c)⁻¹)
      (SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c)) :=
    commute_suppGroup_compl hdx' (suppGroup_mono_C04 hsub hz)
  rw [coorootSp_eq_mul_C04 m c]
  calc
    (SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c) * rootDiagSp m c) * x *
        (SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c) * rootDiagSp m c)⁻¹
        = SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c) *
          (rootDiagSp m c * x * (rootDiagSp m c)⁻¹) *
          (SymplecticTorusWeyl.torusHom (Pi.mulSingle 0 c))⁻¹ := by group
    _ = rootDiagSp m c * x * (rootDiagSp m c)⁻¹ := by
      rw [← hcomm.eq]; group

theorem coorootSp_mem_normalizer_longRootSp2 (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    coorootSp m c ∈ Subgroup.normalizer
      (longRootSp2 K (m + 2) 1 : Set (StatedSp (m + 2) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [coorootSp_mul_mul_inv_eq m c hx]
    exact mul_mem (mul_mem (rootDiagSp_mem_longRootSp2 m c) hx)
      (inv_mem (rootDiagSp_mem_longRootSp2 m c))
  · intro hx
    have h := coorootSp_mul_mul_inv_eq m c⁻¹ hx
    have e : coorootSp m c⁻¹ * (coorootSp m c * x * (coorootSp m c)⁻¹) *
        (coorootSp m c⁻¹)⁻¹ = x := by
      rw [← coorootSp_inv_C04, inv_inv]
      group
    rw [e] at h
    rw [h]
    exact mul_mem (mul_mem (rootDiagSp_mem_longRootSp2 m c⁻¹) hx)
      (inv_mem (rootDiagSp_mem_longRootSp2 m c⁻¹))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
