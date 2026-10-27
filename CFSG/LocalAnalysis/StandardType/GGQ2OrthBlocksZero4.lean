module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero3
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalInvolution.Models.SymplecticPairs Matrix
open CFSG.Open (StatedSp)
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)

private theorem isSolvable_of_le_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {K : Subgroup G} (hK : Group.IsSolvable ↥K)
    {L : Subgroup H} (hL : L ≤ K.map f) : Group.IsSolvable ↥L := by
  have hPK : L.comap f ≤ K := by
    rintro x hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hL hx)
    have hkx' : k = x := hf hkx
    subst hkx'
    exact hk
  have hPsolv : Group.IsSolvable ↥(L.comap f) :=
    @Group.isSolvable_of_isSolvable_injective ↥(L.comap f) ↥K _ _
      (Subgroup.inclusion hPK) (Subgroup.inclusion_injective hPK) hK
  have hmap : (L.comap f).map f = L :=
    Subgroup.map_comap_eq_self (hL.trans (Subgroup.map_le_range f K))
  let e : ↥(L.comap f) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.comap f) f hf).trans (MulEquiv.subgroupCongr hmap)
  exact @Group.isSolvable_of_isSolvable_injective ↥L ↥(L.comap f) _ _ e.symm
    e.symm.injective hPsolv

theorem liftV_apply_of_mem_liftSupport {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    {u : PlaneRaw.V t} (hu : ∀ i ∈ S, u i = 0) {j : Fin (t + δ.val)}
    (hj : j ∈ liftSupport t δ S) : liftV t δ u j = 0 := by
  induction j using Fin.addCases with
  | left i =>
    rw [liftV_apply_castAdd]
    exact hu i (mem_liftSupport_castAdd.1 hj)
  | right k => exact liftV_apply_natAdd t δ u k

theorem restrV_eq_zero {t : ℕ} (S : Finset (Fin t)) {u : PlaneRaw.V t}
    (hu : restrV t S u = 0) : ∀ i ∈ S, u i = 0 := by
  intro i hi
  obtain ⟨k, hk⟩ : ∃ k : Fin S.card, S.orderEmbOfFin rfl k = i := by
    have hri : Set.range (S.orderEmbOfFin rfl) = (S : Set (Fin t)) :=
      Finset.range_orderEmbOfFin S rfl
    obtain ⟨k, hk⟩ := (show i ∈ Set.range (S.orderEmbOfFin rfl) by rw [hri]; exact hi)
    exact ⟨k, hk⟩
  have hk' : (k : ℕ) < S.card := k.isLt
  have h := congrFun hu k
  rw [restrV, dif_pos hk'] at h
  rw [← hk]
  exact h

theorem mem_oYcode_zero_iff (hτ : OrthTauMemOmega) (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) (u : PlaneRaw.V t) :
    otau ζ t δ u ∈ (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ↔
      u ∈ PlaneRaw.inside (.orthogonal δ) (.zero S : PlaneRaw.Code t) := by
  constructor
  · intro hmem
    obtain ⟨g, hgY, hgval⟩ := Subgroup.mem_map.mp hmem
    have hgΩ : otau ζ t δ u ∈ omegaQ (K := K) t δ := by
      rw [← hgval]
      exact g.2
    have hgB : (⟨otau ζ t δ u, hgΩ⟩ : ↥(omegaQ (K := K) t δ)) ∈
        oBlockGroup ζ t δ (.zero S) := by
      have hEq : (⟨otau ζ t δ u, hgΩ⟩ : ↥(omegaQ (K := K) t δ)) = g :=
        Subtype.ext hgval.symm
      rw [hEq]
      exact Subgroup.commutator_le_self _ hgY
    rw [PlaneRaw.mem_inside_zero]
    intro i hi
    by_contra hiS
    have hzero : u i = 0 := by
      let j : Fin (t + δ.val) := Fin.castAdd δ.val i
      have hj : j ∉ liftSupport t δ S := fun h => hiS (mem_liftSupport_castAdd.1 h)
      have hblock : ∀ a b : Fin 2,
          (((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) a b) = (1 : Matrix (Fin 2) (Fin 2) K) a b := by
        intro a b
        have hmat := apply_of_not_mem_plane_right ζ t δ S hgB
          (a := WitSpNs.coord a j) (b := WitSpNs.coord b j) (by simpa using hj)
        rw [coe_otau, WitSpNs.planeMat_coord, liftV_apply_castAdd] at hmat
        have hone : (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (WitSpNs.coord a j) (WitSpNs.coord b j) =
            (1 : Matrix (Fin 2) (Fin 2) K) a b := by
          rw [Matrix.one_apply, Matrix.one_apply]
          by_cases hab : a = b
          · rw [if_pos hab, if_pos (by rw [hab])]
          · rw [if_neg hab, if_neg (fun h => hab (by simpa using congrArg WitSpNs.side h))]
        exact hmat.trans hone
      have hζj : ζ (Multiplicative.ofAdd (u i)) = 1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro a b
        exact hblock a b
      have hof : Multiplicative.ofAdd (u i) = 1 :=
        hζ (hζj.trans (map_one ζ).symm)
      have := congrArg Multiplicative.toAdd hof
      simpa using this
    exact (show u i ≠ 0 from by simpa [PlaneRaw.vSupport] using hi) hzero
  · intro hu
    rw [oYcode_map_eq_orthExt ζ hK t δ S hS]
    refine ⟨otau ζ S.card δ (restrV t S u), hτ ζ S.card δ hK (restrV t S u), ?_⟩
    exact (otau_eq_orthExt_otau ζ t δ S
      ((PlaneRaw.mem_inside_zero (.orthogonal δ) S u).1 hu)).symm

theorem commute_oYcode_zero_iff (hτ : OrthTauMemOmega) (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) (u : PlaneRaw.V t) :
    (∀ g ∈ oYcode ζ t δ (.zero S),
        otau ζ t δ u * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u) ↔
      u ∈ PlaneRaw.cent (.orthogonal δ) (.zero S : PlaneRaw.Code t) := by
  have hback : ∀ (w : PlaneRaw.V t),
      w ∈ PlaneRaw.cent (.orthogonal δ) (.zero S : PlaneRaw.Code t) →
      ∀ g ∈ oYcode ζ t δ (.zero S),
        otau ζ t δ w * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ w := by
    intro w hu g hg
    have hu' : ∀ i ∈ S, w i = 0 :=
      (PlaneRaw.mem_cent_zero (.orthogonal δ) S w).1 hu
    have hgΩ : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈ omegaQ (K := K) t δ := g.2
    have hgB : (⟨(g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hgΩ⟩ :
        ↥(omegaQ (K := K) t δ)) ∈ oBlockGroup ζ t δ (.zero S) := by
      change g ∈ ⁅oBlockGroup ζ t δ (.zero S), oBlockGroup ζ t δ (.zero S)⁆ at hg
      exact Subgroup.commutator_le_self _ hg
    have hgfix : ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
          (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) =
        1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) :=
      (mem_oBlockGroup_zero_iff ζ t δ S).1 hgB
    have hgfix' : (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) *
        ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) :=
      one_sub_mul_of_mem_oBlockGroup ζ t δ S hgB
    have hτε : (((otau ζ t δ w : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) *
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) =
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) *
          ((otau ζ t δ w : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
      SpBlocks.tau_mul_planeIdem_comm ζ (t + δ.val) (liftV t δ w)
        (liftSupport t δ S)
    have hP : ((otau ζ t δ w : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) =
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) := by
      have h := SpBlocks.tau_mul_planeIdem_eq ζ (t + δ.val)
        (v := (0 : PlaneRaw.V (t + δ.val))) (w := liftV t δ w)
        (S := liftSupport t δ S) (fun j hj => by
          rw [Pi.zero_apply]
          exact (liftV_apply_of_mem_liftSupport (S := S) hu' (by simpa using hj)).symm)
      rw [SpBlocks.tau_zero] at h
      have h1 : (((1 : ↥(StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) = 1 := rfl
      rw [h1, Matrix.one_mul] at h
      exact h.symm
    have hσ : (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) =
        ((otau ζ t δ w : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) := by
      rw [Matrix.one_mul, hP]
    have hgσ : ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * 1 =
        1 * ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
      rw [mul_one, one_mul]
    have hcomm := SpBlocks.commute_of_block hgfix hgfix' hτε hσ hgσ
    apply Units.ext
    exact hcomm.symm
  constructor
  · intro hcomm
    let u₁ : PlaneRaw.V t := fun i => if i ∈ S then u i else 0
    let u₂ : PlaneRaw.V t := u - u₁
    have hu₁ : PlaneRaw.vSupport u₁ ⊆ S := by
      intro i hi
      by_contra hiS
      have hzero : u₁ i = 0 := by simp [u₁, hiS]
      exact (show u₁ i ≠ 0 from by simpa [PlaneRaw.vSupport] using hi) hzero
    have hu₂ : ∀ i ∈ S, u₂ i = 0 := by
      intro i hi
      simp [u₂, u₁, hi]
    have hdecomp : u = u₁ + u₂ := by
      funext i
      simp [u₂]
    have hu₂cent : u₂ ∈ PlaneRaw.cent (.orthogonal δ) (.zero S : PlaneRaw.Code t) :=
      (PlaneRaw.mem_cent_zero (.orthogonal δ) S u₂).2 hu₂
    have hcomm₂ := hback u₂ hu₂cent
    have hτadd : otau ζ t δ u = otau ζ t δ u₁ * otau ζ t δ u₂ := by
      have hLV : liftV t δ u = liftV t δ u₁ + liftV t δ u₂ := by
        rw [hdecomp, map_add]
      change ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u) : ↥(StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u₁) : ↥(StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u₂) : ↥(StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
      rw [hLV, SpBlocks.tau_add, Subgroup.coe_mul]
    have hcomm₁ : ∀ g ∈ oYcode ζ t δ (.zero S),
        otau ζ t δ u₁ * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u₁ := by
      intro g hg
      have hgτ := hcomm g hg
      have hg₂ := hcomm₂ g hg
      rw [hτadd] at hgτ
      calc otau ζ t δ u₁ * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
          = otau ζ t δ u₁ * ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
              otau ζ t δ u₂) * (otau ζ t δ u₂)⁻¹ := by group
        _ = otau ζ t δ u₁ * (otau ζ t δ u₂ *
              (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) *
              (otau ζ t δ u₂)⁻¹ := by rw [hg₂]
        _ = (otau ζ t δ u₁ * otau ζ t δ u₂) *
              (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
              (otau ζ t δ u₂)⁻¹ := by group
        _ = (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
              (otau ζ t δ u₁ * otau ζ t δ u₂) * (otau ζ t δ u₂)⁻¹ := by rw [hgτ]
        _ = (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u₁ := by group
    let A : ↥(omegaQ (K := K) S.card δ) :=
      ⟨otau ζ S.card δ (restrV t S u₁), hτ ζ S.card δ hK (restrV t S u₁)⟩
    have hAext : orthExt t δ S ((A : ↥(omegaQ (K := K) S.card δ)) :
        GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) = otau ζ t δ u₁ :=
      (otau_eq_orthExt_otau ζ t δ S hu₁).symm
    have hAcomm : ∀ y ∈ omegaQ (K := K) S.card δ,
        y * ((A : ↥(omegaQ (K := K) S.card δ)) :
          GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) =
          ((A : ↥(omegaQ (K := K) S.card δ)) :
            GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) * y := by
      intro y hy
      let gY : ↥(omegaQ (K := K) t δ) :=
        ⟨orthExt t δ S y, orthExt_map_omegaQ_le t δ S ⟨y, hy, rfl⟩⟩
      have hmem : (gY : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
          (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype := by
        rw [oYcode_map_eq_orthExt ζ hK t δ S hS]
        exact ⟨y, hy, rfl⟩
      have hgY : gY ∈ oYcode ζ t δ (.zero S) := by
        obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp hmem
        have hEq : h = gY := Subtype.ext hval
        rwa [hEq] at hh
      have hg1 := hcomm₁ gY hgY
      rw [show (gY : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) = orthExt t δ S y from rfl]
        at hg1
      rw [← hAext] at hg1
      apply orthExt_injective t δ S
      rw [map_mul, map_mul]
      exact hg1.symm
    have hcenter : (A : ↥(omegaQ (K := K) S.card δ)) ∈
        Subgroup.center ↥(omegaQ (K := K) S.card δ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hAcomm y y.2
    have hAone : A = 1 := by
      have h := hcenter
      rw [center_omegaQ_eq_bot hK S.card δ hS] at h
      simpa using h
    have htauone : otau ζ S.card δ (restrV t S u₁) = 1 := congrArg Subtype.val hAone
    have hlift0 : liftV S.card δ (restrV t S u₁) = 0 := by
      have hst : SpBlocks.tau ζ (S.card + δ.val) (liftV S.card δ (restrV t S u₁)) = 1 :=
        Subtype.ext htauone
      have hτeq : SpBlocks.tau ζ (S.card + δ.val) (liftV S.card δ (restrV t S u₁)) =
          SpBlocks.tau ζ (S.card + δ.val) (0 : PlaneRaw.V (S.card + δ.val)) := by
        rw [hst, SpBlocks.tau_zero]
      have hzero := SpBlocks.tau_injective hζ (S.card + δ.val) hτeq
      have := congrFun hzero
      simpa [liftV] using hzero
    have hr0 : restrV t S u₁ = 0 :=
      liftV_injective S.card δ (by rw [hlift0, map_zero])
    have hu₁zero : ∀ i ∈ S, u₁ i = 0 := restrV_eq_zero S hr0
    rw [PlaneRaw.mem_cent_zero]
    intro i hi
    have hdec := congrFun hdecomp i
    rw [Pi.add_apply] at hdec
    rw [hdec, hu₁zero i hi, zero_add]
    exact hu₂ i hi
  · intro hu
    exact hback u hu

theorem isQuasisimple_oYcode_zero (hK : Nat.card K = 2) (t : ℕ) (δ : Fin 2)
    (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    IsQuasisimple ↥(oYcode ζ t δ (.zero S)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (oYcodeMulEquivOmegaQ ζ hK t δ S hS).symm
    (isQuasisimple_omegaQ hK S.card δ hS)

theorem marked_oYcode_zero (hK : Nat.card K = 2) (t : ℕ) (δ : Fin 2)
    (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    LargeEvenMarking ↥(oYcode ζ t δ (.zero S))
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.orthogonal δ) (.zero S : PlaneRaw.Code t)) := by
  refine CFSG.StandardType.largeEvenMarking_congr (oYcodeMulEquivOmegaQ ζ hK t δ S hS) ?_
    (largeEvenMarking_omegaQ hK S.card δ hS)
  intro lab R _ I F θ hlab
  rw [hlab]
  rfl

theorem not_isComponentOf_oYcode_zero (hK : Nat.card K = 2) (t : ℕ) (δ : Fin 2)
    (S : Finset (Fin t))
    (hS : ¬ PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t))
    (X : Subgroup ↥(omegaQ (K := K) t δ)) :
    ¬ IsComponentOf X (oYcode ζ t δ (.zero S)) := by
  have hB : (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ≤
      (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S) :=
    orthBlockGroup_map_le_ext ζ t δ S
  have hY : (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ≤
      (omegaQ (K := K) S.card δ).map (orthExt t δ S) := by
    calc (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype
        = ⁅(oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype,
            (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype⁆ := by
          rw [oYcode, Subgroup.map_commutator]
      _ ≤ ⁅(LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S),
            (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S)⁆ :=
          Subgroup.commutator_mono hB hB
      _ = (omegaQ (K := K) S.card δ).map (orthExt t δ S) := by
          rw [← Subgroup.map_commutator]
          rfl
  have hsolvΩ : Group.IsSolvable ↥(omegaQ (K := K) S.card δ) :=
    isSolvable_omegaQ_of_not_admissible hK S.card δ hS
  have htop : Group.IsSolvable ↥(⊤ : Subgroup ↥(omegaQ (K := K) S.card δ)) :=
    @Group.isSolvable_of_isSolvable_injective
      ↥(⊤ : Subgroup ↥(omegaQ (K := K) S.card δ)) ↥(omegaQ (K := K) S.card δ) _ _
      (Subgroup.topEquiv (G := ↥(omegaQ (K := K) S.card δ))).toMonoidHom
      (Subgroup.topEquiv (G := ↥(omegaQ (K := K) S.card δ))).injective hsolvΩ
  have hY' : (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ≤
      (⊤ : Subgroup ↥(omegaQ (K := K) S.card δ)).map
        ((orthExt t δ S).comp (omegaQ (K := K) S.card δ).subtype) := by
    have hrange : ((orthExt t δ S).comp (omegaQ (K := K) S.card δ).subtype).range =
        (omegaQ (K := K) S.card δ).map (orthExt t δ S) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(x : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [Subgroup.map_top, hrange]
    exact hY
  have hLsolv : Group.IsSolvable ↥((oYcode ζ t δ (.zero S)).map
      (omegaQ (K := K) t δ).subtype) :=
    isSolvable_of_le_map ((orthExt t δ S).comp (omegaQ (K := K) S.card δ).subtype)
      (fun a b hab => Subtype.ext (orthExt_injective t δ S hab)) htop hY'
  have e : ↥(oYcode ζ t δ (.zero S)) ≃*
      ↥((oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype) :=
    Subgroup.equivMapOfInjective (oYcode ζ t δ (.zero S)) (omegaQ (K := K) t δ).subtype
      (omegaQ (K := K) t δ).subtype_injective
  have hsolvY : Group.IsSolvable ↥(oYcode ζ t δ (.zero S)) :=
    @Group.isSolvable_of_isSolvable_injective ↥(oYcode ζ t δ (.zero S))
      ↥((oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype) _ _ e.toMonoidHom
      e.injective hLsolv
  exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hsolvY

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
