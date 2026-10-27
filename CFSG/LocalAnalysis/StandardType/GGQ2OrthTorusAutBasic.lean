module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthNormalizerStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

private lemma otb_castAdd_ne_natAdd {n m : ℕ} (a : Fin n) (b : Fin m) :
    Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

private lemma otb_orientEquiv_mul_self {m : ℕ} (e : PlaneRaw.V m) :
    PlaneRaw.orientEquiv m e * PlaneRaw.orientEquiv m e = 1 := by
  ext w k
  simp only [LinearEquiv.mul_apply, PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private lemma otb_orientEquiv_inv {m : ℕ} (e : PlaneRaw.V m) :
    (PlaneRaw.orientEquiv m e)⁻¹ = PlaneRaw.orientEquiv m e :=
  inv_eq_of_mul_eq_one_right (otb_orientEquiv_mul_self e)

private lemma otb_orientEquiv_apply {m : ℕ} (e v : PlaneRaw.V m) (k : Fin m) :
    PlaneRaw.orientEquiv m e v k =
      (if e k = -1 then (-1 : PlaneRaw.F) else 1) * v k := by
  simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private lemma otb_swapEquiv_apply {m : ℕ} (i j : Fin m) (w : PlaneRaw.V m) (k : Fin m) :
    PlaneRaw.swapEquiv m i j w k = w (Equiv.swap i j k) := by
  simp [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private lemma otb_swapTwist_apply {m : ℕ} (e w : PlaneRaw.V m) (i j : Fin m) (k : Fin m) :
    PlaneRaw.swapTwist m e i j w k =
      (if e k = -1 then (-1 : PlaneRaw.F) else 1) *
        (if e (Equiv.swap i j k) = -1 then (-1 : PlaneRaw.F) else 1) *
          w (Equiv.swap i j k) := by
  rw [PlaneRaw.swapTwist, LinearEquiv.mul_apply, LinearEquiv.mul_apply, otb_orientEquiv_inv,
    otb_orientEquiv_apply, otb_swapEquiv_apply, otb_orientEquiv_apply]
  ring

private lemma otb_swap_castAdd {t : ℕ} (δ : Fin 2) (i j a : Fin t) :
    Equiv.swap (Fin.castAdd δ.val i) (Fin.castAdd δ.val j) (Fin.castAdd δ.val a) =
      Fin.castAdd δ.val (Equiv.swap i j a) := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h1 h2 <;> simp_all [Fin.castAdd_inj]

private lemma otb_swap_natAdd {t : ℕ} (δ : Fin 2) (i j : Fin t) (b : Fin δ.val) :
    Equiv.swap (Fin.castAdd δ.val i) (Fin.castAdd δ.val j) (Fin.natAdd t b) = Fin.natAdd t b := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · exact fun h => otb_castAdd_ne_natAdd i b h.symm
  · exact fun h => otb_castAdd_ne_natAdd j b h.symm

variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (t : ℕ) (δ : Fin 2)

theorem otau_add (u v : PlaneRaw.V t) : otau ζ t δ (u + v) = otau ζ t δ u * otau ζ t δ v := by
  rw [otau, otau, otau, map_add, SpBlocks.tau_add, Subgroup.coe_mul]

theorem otau_zero : otau ζ t δ 0 = 1 := by
  rw [otau, map_zero, SpBlocks.tau_zero, Subgroup.coe_one]

theorem otau_injective (hζ : Function.Injective ζ) : Function.Injective (otau ζ t δ) := by
  intro u v h
  have h' : SpBlocks.tau ζ (t + δ.val) (liftV t δ u) =
      SpBlocks.tau ζ (t + δ.val) (liftV t δ v) := Subtype.val_injective h
  have h'' : liftV t δ u = liftV t δ v := SpBlocks.tau_injective hζ (t + δ.val) h'
  funext i
  have hi := congrFun h'' (Fin.castAdd δ.val i)
  simpa [liftV] using hi

variable {ζ t δ}

theorem one_mem_oTorusAut (X : Subgroup ↥(omegaQ (K := K) t δ)) :
    (1 : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) ∈ oTorusAut ζ t δ X :=
  ⟨1, X.one_mem, fun u => by simp⟩

theorem mul_mem_oTorusAut {X : Subgroup ↥(omegaQ (K := K) t δ)}
    {φ ψ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hφ : φ ∈ oTorusAut ζ t δ X)
    (hψ : ψ ∈ oTorusAut ζ t δ X) : φ * ψ ∈ oTorusAut ζ t δ X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  obtain ⟨z, hz, hzψ⟩ := hψ
  refine ⟨y * z, X.mul_mem hy hz, fun u => ?_⟩
  rw [LinearEquiv.mul_apply, ← hyφ, ← hzψ]
  simp only [Subgroup.coe_mul]
  group

theorem inv_mem_oTorusAut {X : Subgroup ↥(omegaQ (K := K) t δ)}
    {φ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hφ : φ ∈ oTorusAut ζ t δ X) :
    φ⁻¹ ∈ oTorusAut ζ t δ X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  refine ⟨y⁻¹, X.inv_mem hy, fun u => ?_⟩
  have h := hyφ (φ⁻¹ u)
  have hu : φ (φ⁻¹ u) = u := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hu] at h
  rw [← h]
  simp only [Subgroup.coe_inv, inv_inv]
  group

theorem closure_subset_oTorusAut {X : Subgroup ↥(omegaQ (K := K) t δ)}
    {s : Set (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t)} (hs : s ⊆ oTorusAut ζ t δ X) :
    (Subgroup.closure s : Set (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t)) ⊆ oTorusAut ζ t δ X := by
  intro φ hφ
  induction hφ using Subgroup.closure_induction with
  | mem x hx => exact hs hx
  | one => exact one_mem_oTorusAut X
  | mul x y _ _ hx hy => exact mul_mem_oTorusAut hx hy
  | inv x _ hx => exact inv_mem_oTorusAut hx

theorem oTorusAut_mono {X Y : Subgroup ↥(omegaQ (K := K) t δ)} (h : X ≤ Y) :
    oTorusAut ζ t δ X ⊆ oTorusAut ζ t δ Y :=
  fun _ ⟨y, hy, hyφ⟩ => ⟨y, h hy, hyφ⟩

private lemma otb_liftV_castAdd (u : PlaneRaw.V t) (a : Fin t) :
    liftV t δ u (Fin.castAdd δ.val a) = u a := by
  simp [liftV]

private lemma otb_liftV_natAdd (u : PlaneRaw.V t) (b : Fin δ.val) :
    liftV t δ u (Fin.natAdd t b) = 0 := by
  simp [liftV]

private lemma otb_mem_liftSupport_castAdd {S : Finset (Fin t)} {a : Fin t} :
    Fin.castAdd δ.val a ∈ liftSupport t δ S ↔ a ∈ S := by
  simp only [liftSupport, Finset.mem_union, Finset.mem_map, Fin.castAddEmb_apply,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, hba⟩ | ⟨b, hba⟩)
    · exact (Fin.castAdd_inj.mp hba.symm ▸ hb)
    · exact absurd hba.symm (otb_castAdd_ne_natAdd a b)
  · intro ha
    exact Or.inl ⟨a, ha, rfl⟩

private lemma otb_mem_extSupport_liftV {e : PlaneRaw.V t} {a : Fin t} :
    Fin.castAdd δ.val a ∈ PlaneRaw.Code.extSupport (liftV t δ e) ↔
      a ∈ PlaneRaw.Code.extSupport e := by
  rw [PlaneRaw.mem_extSupport, PlaneRaw.mem_extSupport]
  simp [liftV]

private lemma otb_liftV_eq_zero_of_mem_support {c : PlaneRaw.Code t} {u : PlaneRaw.V t}
    (hu : ∀ i ∈ PlaneRaw.Code.support c, u i = 0) :
    ∀ i ∈ PlaneRaw.Code.support (liftCode t δ c), liftV t δ u i = 0 := by
  cases c with
  | zero S =>
    change ∀ i ∈ liftSupport t δ S, liftV t δ u i = 0
    refine Fin.addCases (fun a => ?_) (fun b => ?_)
    · intro hi
      rw [otb_liftV_castAdd]
      exact hu a ((otb_mem_liftSupport_castAdd (δ := δ)).mp hi)
    · intro _
      rw [otb_liftV_natAdd]
  | extension e =>
    change ∀ i ∈ PlaneRaw.Code.extSupport (liftV t δ e), liftV t δ u i = 0
    refine Fin.addCases (fun a => ?_) (fun b => ?_)
    · intro hi
      rw [otb_liftV_castAdd]
      exact hu a ((otb_mem_extSupport_liftV (δ := δ)).mp hi)
    · intro _
      rw [otb_liftV_natAdd]

private lemma otb_exists_mem_blockGroup_of_mem_oBlockGroup {c : PlaneRaw.Code t}
    {y : ↥(omegaQ (K := K) t δ)} (hy : y ∈ oBlockGroup ζ t δ c) :
    ∃ g ∈ SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c),
      ((g : ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
  have hy' : (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
      (SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c)).map
        (StatedSp (t + δ.val) K).subtype := Subgroup.mem_comap.mp hy
  exact Subgroup.mem_map.mp hy'

theorem commute_otau_of_mem_oBlockGroup {c : PlaneRaw.Code t} {y : ↥(omegaQ (K := K) t δ)}
    (hy : y ∈ oBlockGroup ζ t δ c) {u : PlaneRaw.V t}
    (hu : ∀ i ∈ PlaneRaw.Code.support c, u i = 0) :
    (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u =
      otau ζ t δ u * (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
  obtain ⟨g, hg, hgy⟩ := otb_exists_mem_blockGroup_of_mem_oBlockGroup hy
  rw [← hgy]
  have hlevi : g ∈ SpBlocks.levi (t + δ.val) (PlaneRaw.Code.support (liftCode t δ c)) := by
    cases c with
    | zero S => exact hg
    | extension e => exact (Subgroup.mem_inf.mp hg).1
  have hcomm : SpBlocks.tau ζ (t + δ.val) (liftV t δ u) * g =
      g * SpBlocks.tau ζ (t + δ.val) (liftV t δ u) :=
    SpBlocks.commute_tau_of_mem_levi (otb_liftV_eq_zero_of_mem_support hu) hlevi
  simpa only [otau, Subgroup.coe_mul] using
    congrArg (fun x : ↥(StatedSp (t + δ.val) K) =>
      (x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hcomm.symm

theorem commute_otau_self_of_mem_oBlockGroup_extension {e : PlaneRaw.V t}
    {y : ↥(omegaQ (K := K) t δ)} (hy : y ∈ oBlockGroup ζ t δ (.extension e)) :
    (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ e =
      otau ζ t δ e * (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
  obtain ⟨g, hg, hgy⟩ := otb_exists_mem_blockGroup_of_mem_oBlockGroup hy
  rw [← hgy]
  have hcent : g ∈ Subgroup.centralizer
      ({SpBlocks.tau ζ (t + δ.val) (liftV t δ e)} : Set ↥(StatedSp (t + δ.val) K)) :=
    (Subgroup.mem_inf.mp hg).2
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcent)
    (SpBlocks.tau ζ (t + δ.val) (liftV t δ e)) (Set.mem_singleton _)
  simpa only [otau, Subgroup.coe_mul] using
    congrArg (fun x : ↥(StatedSp (t + δ.val) K) =>
      (x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hcomm.symm

theorem apply_eq_self_of_commute (hζ : Function.Injective ζ)
    {y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K} {φ : PlaneRaw.V t → PlaneRaw.V t}
    (hφ : ∀ u, y * otau ζ t δ u * y⁻¹ = otau ζ t δ (φ u)) {w : PlaneRaw.V t}
    (hw : y * otau ζ t δ w = otau ζ t δ w * y) : φ w = w := by
  have hcomm : y * otau ζ t δ w * y⁻¹ = otau ζ t δ w := by
    rw [hw]
    group
  have hEq : otau ζ t δ (φ w) = otau ζ t δ w := by
    rw [← hφ w, hcomm]
  exact otau_injective ζ t δ hζ hEq

theorem swapTwist_liftV (e : PlaneRaw.V t) (i j : Fin t) (u : PlaneRaw.V t) :
    PlaneRaw.swapTwist (t + δ.val) (liftV t δ e) (Fin.castAdd δ.val i) (Fin.castAdd δ.val j)
        (liftV t δ u) =
      liftV t δ (PlaneRaw.swapTwist t e i j u) := by
  funext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · rw [otb_swapTwist_apply, otb_swap_castAdd]
    simp only [otb_liftV_castAdd]
    rw [otb_swapTwist_apply]
  · rw [otb_swapTwist_apply, otb_swap_natAdd]
    simp only [otb_liftV_natAdd]
    simp

end CFSG.StandardType.GGQ2Frame.OrthBlocks
