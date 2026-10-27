module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Bracket
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Solvable

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Notation.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.TypeStar

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative commutatorElement

/-- The center of a subgroup, viewed as a subgroup of the ambient group. -/
@[expose]
public def CFSG.centerIn {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (H : Set G)

/-- `centerIn H` is the image of the center of `H` in the ambient group. -/
public theorem CFSG.centerIn_eq_map_center {G : Type*} [Group G] (H : Subgroup G) :
    centerIn H = (Subgroup.center H).map H.subtype := by
  simp [centerIn]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxH, hx_centralizer⟩
    have hx_center : (⟨x, hxH⟩ : H) ∈ Subgroup.center H := by
      exact Subgroup.mem_center_iff.mpr (fun h =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp hx_centralizer (h : G) h.property))
    exact ⟨⟨x, hxH⟩, hx_center, rfl⟩
  · intro hx_map
    rcases hx_map with ⟨h, hh, rfl⟩
    have hH : (h : G) ∈ H := h.property
    have h_centralizer : (h : G) ∈ Subgroup.centralizer (H : Set G) := by
      intro g hg
      have h_center := Subgroup.mem_center_iff.mp hh ⟨g, hg⟩
      calc
        g * (h : G) = (⟨g, hg⟩ * h : H).val := by simp
        _ = (h * ⟨g, hg⟩ : H).val := by rw [h_center]
        _ = (h : G) * g := by simp
    exact ⟨hH, h_centralizer⟩
attribute [local simp] CFSG.centerIn_eq_map_center

/-- A solvable nontrivial subgroup has proper commutator subgroup. -/
public theorem CFSG.commutator_lt_self_of_isSolvable {G : Type*} [Group G] (M : Subgroup G)
    [Group.IsSolvable (↥M)] [Nontrivial (↥M)] : ⁅M, M⁆ < M := by
  -- Commutator of `M` is a proper subgroup of `M`.
  have hlt : commutator (↥M) < (⊤ : Subgroup (↥M)) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := (↥M))
  -- Make them subgroups of `G`.
  have hlt' : (commutator (↥M)).map M.subtype < (⊤ : Subgroup (↥M)).map M.subtype :=
      (Subgroup.map_subtype_lt_map_subtype (G' := M) (H := commutator (↥M))
            (K := (⊤ : Subgroup (↥M)))).mpr hlt
  have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
    simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
  simpa [Subgroup.map_subtype_commutator, htop_map] using hlt'

/-- A normal subgroup `H` is *minimal normal* if it has no nontrivial proper normal subgroups. -/
public class CFSG.IsMinimalNormal {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Prop where
  minimal (K : Subgroup G) [K.Normal] : K ≤ H → K = ⊥ ∨ K = H

public theorem CFSG.IsMinimalNormal.eq_of_ne_bot {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] [IsMinimalNormal H]
    (K : Subgroup G) [K.Normal] : K ≤ H → K ≠ ⊥ → K = H := by
  intro h_le h_neq
  exact Or.resolve_left (IsMinimalNormal.minimal K h_le) h_neq

/-- A solvable minimal normal subgroup is abelian. -/
public theorem CFSG.minimalNormal_solvable_isMulCommutative {G : Type*} [Group G] (M : Subgroup G)
    [M.Normal] [Group.IsSolvable (↥M)] [IsMinimalNormal M]
    : IsMulCommutative (↥M) := by
  by_cases hM_bot : M = ⊥
  · subst hM_bot
    infer_instance
  · have hM_nontrivial : Nontrivial (↥M) :=
      (Subgroup.nontrivial_iff_ne_bot M).mpr hM_bot
    have hcomm_lt : ⁅M, M⁆ < M :=
      @commutator_lt_self_of_isSolvable G (inferInstance : Group G) M
        (inferInstance : Group.IsSolvable (↥M)) hM_nontrivial
    have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
      by_contra hne
      have hcomm_eq : ⁅M, M⁆ = M := Or.resolve_left
        (IsMinimalNormal.minimal (⁅M, M⁆) (Subgroup.commutator_le_left (H₁ := M) (H₂ := M))) hne
      exact (ne_of_lt hcomm_lt) hcomm_eq
    have hM_le_centralizer : M ≤ Subgroup.centralizer (M : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := M) (H₂ := M)).mp hcomm_eq_bot
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := M)).mp hM_le_centralizer


/-
**Kind**: Theorem
**Note**: Lemma 1.1
**Stmt**:
Let $M$ be a minimal normal subgroup of a finite group $G$.
If $M$ is solvable, then $M$ is elementary abelian and $M \subset Z(F(G))$.
-/

/--
If `M` is a minimal normal solvable subgroup of a finite group `G`, then
`M` is elementary abelian.
-/
public theorem CFSG.minimalNormal_solvable_exists_isElementaryAbelian {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) [M.Normal] [IsMinimalNormal M] [Group.IsSolvable (↥M)] :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p (↥M) := by
  classical
  by_cases hM_bot : M = ⊥
  · subst hM_bot
    refine ⟨2, by decide, ?_⟩
    refine
      { toIsMulCommutative :=
          ⟨⟨fun x y => by
            apply Subtype.ext
            have hx : (x : G) = 1 := by
              simpa only [Subgroup.mem_bot] using x.property
            have hy : (y : G) = 1 := by
              simpa only [Subgroup.mem_bot] using y.property
            simp [hx, hy]⟩⟩
        exponent_dvd_p := ?_ }
    simp
  · have hM_ne_bot : M ≠ ⊥ := hM_bot
    have hM_comm : IsMulCommutative (↥M) := minimalNormal_solvable_isMulCommutative M

    -- Choose a prime `p` dividing `|M|`.
    have hcard_ne_one : Nat.card (↥M) ≠ 1 := by
      have : 1 < Nat.card (↥M) := (Subgroup.one_lt_card_iff_ne_bot (H := M)).2 hM_ne_bot
      exact ne_of_gt this
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (↥M)) hcard_ne_one
    let hp_fact : Fact p.Prime := ⟨hp_prime⟩

    -- Let `Ω₁(M)` be generated by elements of `M` of order dividing `p`.
    let Ω : Subgroup (↥M) := omega₁ (G := (↥M)) (p := p)
    have hΩ_char : Ω.Characteristic := by
      simpa [Ω] using (omega₁_characteristic (G := (↥M)) (p := p))
    have hΩmap_normal : (Ω.map M.subtype).Normal :=
      @ConjAct.normal_of_characteristic_of_normal G (inferInstance : Group G)
        M (inferInstance : M.Normal) Ω hΩ_char

    -- `Ω` is nontrivial by Cauchy, hence `Ω = ⊤` by minimality.
    have hΩmap_ne_bot : Ω.map M.subtype ≠ ⊥ := by
      simpa [Ω] using
        (@omega₁_map_subtype_ne_bot G (inferInstance : Group G) (inferInstance : Finite G)
          M p hp_fact hp_dvd)
    have hΩmap_eq_M : Ω.map M.subtype = M :=
      @IsMinimalNormal.eq_of_ne_bot G (inferInstance : Group G) M
        (inferInstance : M.Normal) (inferInstance : IsMinimalNormal M)
        (Ω.map M.subtype) hΩmap_normal
        (Subgroup.map_subtype_le (H := M) (K := Ω)) hΩmap_ne_bot
    have hΩ_top : Ω = ⊤ := by
      -- `map M.subtype` is injective on subgroups.
      have hinj : Function.Injective (Subgroup.map M.subtype) :=
        Subgroup.map_injective (f := M.subtype) M.subtype_injective
      have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
        simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
      apply hinj
      simpa [htop_map] using hΩmap_eq_M

    -- Exponent `p`: every element is a product of `p`-torsion elements in an abelian group.
    have hpow : ∀ x : ↥M, x ^ p = 1 := by
      intro x
      have hxΩ : x ∈ Ω := by simp [hΩ_top]
      -- Unfold the definition of `Ω` and use closure induction.
      have hx' : x ∈ Subgroup.closure {y : ↥M | y ^ (p ^ 1) = 1} := by
        simpa [Ω, omega₁, omega] using hxΩ
      refine
        Subgroup.closure_induction (k := {y : ↥M | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
      · intro y hy
        simpa [pow_one] using hy
      · simp
      · intro a b _ha _hb ha hb
        calc
          (a * b) ^ p = a ^ p * b ^ p := by
            exact Commute.mul_pow (hM_comm.is_comm.comm a b) p
          _ = 1 := by simp [ha, hb]
      · intro a _ha ha
        simp [ha]

    have hExp : Monoid.exponent (↥M) ∣ p :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow
    exact ⟨p, hp_prime, ⟨hExp⟩⟩

/--
If `M` is a minimal normal solvable subgroup of a finite group `G`, then
`M` \subset Z(F(G))`.
-/
public theorem CFSG.minimalNormal_solvable_le_centerIn_fittingSubgroup {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) [M.Normal] [IsMinimalNormal M] [Group.IsSolvable (↥M)] :
    M ≤ centerIn (G := G) (fittingSubgroup G) := by
  classical
  by_cases hM_bot : M = ⊥
  · subst hM_bot
    simp
  · have hM_ne_bot : M ≠ ⊥ := hM_bot

    -- `M ≤ F(G)` since `M` is a normal nilpotent subgroup (in fact abelian).
    have hM_comm : IsMulCommutative (↥M) := minimalNormal_solvable_isMulCommutative M
    have hM_le_F : M ≤ fittingSubgroup G := by
      have hnil : Group.IsNilpotent (↥M) := by
        refine ⟨1, ?_⟩
        have hcenter : Subgroup.center (↥M) = ⊤ := by
          ext x
          constructor
          · intro _hx
            simp
          · intro _hx
            rw [Subgroup.mem_center_iff]
            intro y
            simpa using hM_comm.is_comm.comm y x
        simpa [Subgroup.upperCentralSeries_one] using hcenter
      exact le_sSup ⟨inferInstance, hnil⟩

    -- Now show `M` centralizes `F(G)` by nilpotence of `F(G)` and minimality of `M`.
    let F : Subgroup G := fittingSubgroup G
    have hF_normal : F.Normal := by
      simpa [F] using (inferInstance : (fittingSubgroup G).Normal)
    have hF_nilpotent : Group.IsNilpotent (↥F) := by
      simpa [F] using (inferInstance : Group.IsNilpotent (fittingSubgroup G))
    obtain ⟨n, hn⟩ :=
      (Subgroup.nilpotent_iff_lowerCentralSeries (G := (↥F))).1
        hF_nilpotent

    -- Iterated commutators of `M` with `F`.
    let N : ℕ → Subgroup G :=
      fun k => Nat.rec (motive := fun _ => Subgroup G) M (fun _ Nk => ⁅Nk, F⁆) k
    -- Image of the lower central series of the nilpotent subgroup `F`.
    let L : ℕ → Subgroup G :=
      fun k => ((⊤ : Subgroup (↥F)).lowerCentralSeries k).map F.subtype
    have htop_map : (⊤ : Subgroup (↥F)).map F.subtype = F := by
      simpa [MonoidHom.range_eq_map] using (F.range_subtype : F.subtype.range = F)

    have hN_le_L : ∀ k, N k ≤ L k := by
      intro k
      induction k with
      | zero =>
          -- `N 0 = M` and `L 0 = F`.
          simpa [N, L, Subgroup.lowerCentralSeries, htop_map, F] using hM_le_F
      | succ k ih =>
          have h1 : ⁅N k, F⁆ ≤ ⁅L k, F⁆ :=
            Subgroup.commutator_mono ih (le_rfl)
          have hL_succ : L (k + 1) = ⁅L k, F⁆ := by
            simp [L]
          simpa [N, hL_succ] using h1

    have hN_bot : N n = ⊥ := by
      have hL_bot : L n = ⊥ := by
        -- `lowerCentralSeries (↥F) n = ⊥` implies its image in `G` is `⊥`.
        simpa [L] using congrArg (fun K : Subgroup (↥F) => K.map F.subtype) hn
      have : N n ≤ (⊥ : Subgroup G) := by
        simpa [hL_bot] using hN_le_L n
      exact (le_bot_iff.mp this)

    have hMF_bot : ⁅M, F⁆ = ⊥ := by
      by_contra hne
      have hMF_normal : ⁅M, F⁆.Normal :=
        @Subgroup.commutator_normal G (inferInstance : Group G) M F
          (inferInstance : M.Normal) hF_normal
      have hMF_eq : ⁅M, F⁆ = M :=
        @IsMinimalNormal.eq_of_ne_bot G (inferInstance : Group G) M
          (inferInstance : M.Normal) (inferInstance : IsMinimalNormal M)
          (⁅M, F⁆) hMF_normal
          (Subgroup.commutator_le_left (H₁ := M) (H₂ := F)) hne
      have hN_eq : ∀ k, N k = M := by
        intro k
        induction k with
        | zero =>
            simp [N]
        | succ k ih =>
            simp [N, ih, hMF_eq]
      have : (M : Subgroup G) = ⊥ := by
        -- `hN_eq n : N n = M` and `hN_bot : N n = ⊥`.
        have : (⊥ : Subgroup G) = M := by simpa [hN_bot] using (hN_eq n)
        simpa using this.symm
      exact hM_ne_bot this

    have hM_le_centF : M ≤ Subgroup.centralizer (F : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := M) (H₂ := F)).1 hMF_bot

    have hM_le_centerIn : M ≤ centerIn (G := G) F := by
      simpa [centerIn, F] using (le_inf hM_le_F hM_le_centF)
    simpa [F] using hM_le_centerIn

/-- A pair of normal subgroups `K ◁ H` such that there is no normal subgroup strictly between them.
This is the definition of a chief factor in group theory. -/
public class CFSG.IsChiefFactor {G : Type*} [Group G] (K H : Subgroup G) : Prop where
  normal_K : K.Normal
  normal_H : H.Normal
  lt : K < H
  is_maximal : ∀ (N : Subgroup G), N.Normal → K ≤ N → N ≤ H → N = K ∨ N = H

/-- A chief factor of a group `G`, consisting of two subgroups `V ◁ U` with no normal subgroup between. -/
public structure CFSG.ChiefFactor (G : Type*) [Group G] where
  /-- The lower subgroup `V` of the chief factor. -/
  V : Subgroup G
  /-- The upper subgroup `U` of the chief factor. -/
  U : Subgroup G
  /-- Proof that `V ◁ U` is a chief factor. -/
  isChief : IsChiefFactor V U

/-- The subgroup of elements that centralize a chief factor `cf`, i.e., `{g | ∀ u ∈ cf.U, ⁅g, u⁆ ∈ cf.V}`. -/
@[expose]
public def CFSG.centralizerSubgroup {G : Type*} [Group G] (cf : ChiefFactor G) : Subgroup G :=
  { carrier := {g : G | ∀ u : G, u ∈ cf.U → ⁅g, u⁆ ∈ cf.V}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb u hu
      have hVa : ⁅a, u⁆ ∈ cf.V := ha u hu
      have hVb : ⁅b, u⁆ ∈ cf.V := hb u hu
      have hVnorm : cf.V.Normal := cf.isChief.normal_K
      have hconj : a * ⁅b, u⁆ * a⁻¹ ∈ cf.V := hVnorm.conj_mem _ hVb a
      have hmul : (a * ⁅b, u⁆ * a⁻¹) * ⁅a, u⁆ ∈ cf.V := cf.V.mul_mem hconj hVa
      simpa [commutatorElement_def, mul_assoc] using hmul
    inv_mem' := by
      intro a ha u hu
      have hVnorm : cf.V.Normal := cf.isChief.normal_K
      have ha' : ⁅a, u⁆ ∈ cf.V := ha u hu
      have hswap : ⁅u, a⁆ ∈ cf.V := by
        have : (⁅a, u⁆)⁻¹ ∈ cf.V := cf.V.inv_mem ha'
        simpa [commutatorElement_inv] using this
      have hconj : a⁻¹ * ⁅u, a⁆ * a ∈ cf.V := by
        simpa [mul_assoc] using hVnorm.conj_mem _ hswap a⁻¹
      simpa [commutatorElement_def, mul_assoc] using hconj }

public theorem CFSG.centralizerSubgroup_normal {G : Type*} [Group G] (cf : ChiefFactor G) : (centralizerSubgroup cf).Normal := by
  classical
  refine ⟨fun g hg x => ?_⟩
  intro u hu
  have hU_norm : cf.U.Normal := cf.isChief.normal_H
  have hV_norm : cf.V.Normal := cf.isChief.normal_K
  -- Since `U` is normal, `x⁻¹ * u * x ∈ U`.
  have hxux : x⁻¹ * u * x ∈ cf.U := by
    simpa [mul_assoc] using hU_norm.conj_mem u hu x⁻¹
  -- Because `g ∈ centralizerSubgroup cf`, we have `⁅g, x⁻¹ * u * x⁆ ∈ V`.
  have hcomm : ⁅g, x⁻¹ * u * x⁆ ∈ cf.V := hg _ hxux
  -- Conjugating by `x` keeps the commutator inside `V` (since `V` is normal).
  have hconj : x * ⁅g, x⁻¹ * u * x⁆ * x⁻¹ ∈ cf.V :=
    hV_norm.conj_mem _ hcomm x
  -- Rewrite the conjugated commutator as `⁅x * g * x⁻¹, u⁆`.
  have hEq : x * ⁅g, x⁻¹ * u * x⁆ * x⁻¹ = ⁅x * g * x⁻¹, u⁆ := by
    simpa [mul_assoc] using (conjugate_commutatorElement g (x⁻¹ * u * x) x)
  rw [hEq] at hconj
  exact hconj

/-- The centralizer of a chief factor `cf = (V ◁ U)` relative to a subgroup `H`.
This is the subgroup of `H` consisting of elements `g` such that `⁅g, u⁆ ∈ V` for all `u ∈ U`.
Equivalently, it is `H ∩ {g | ∀ u ∈ U, ⁅g, u⁆ ∈ V}`. -/
@[expose]
public def CFSG.centralizerOfChiefFactor {G : Type*} [Group G] (H : Subgroup G) (cf : ChiefFactor G) : Subgroup G :=
  H ⊓ centralizerSubgroup cf

/-- The Fitting subgroup of a subgroup `H`, viewed as a subgroup of the ambient group `G`.
This is the image of `fittingSubgroup H` under the inclusion `H ↪ G`. -/
@[expose]
public def CFSG.fittingSubgroupOf {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (fittingSubgroup (↥H)).map H.subtype

section ChiefFactorBasic

variable {G : Type*} [Group G]

/-- Membership lemma for `centralizerOfChiefFactor`. -/
@[simp] public lemma CFSG.mem_centralizerOfChiefFactor {H : Subgroup G} {cf : ChiefFactor G} {g : G} :
    g ∈ centralizerOfChiefFactor (G := G) H cf ↔
      g ∈ H ∧ ∀ u : G, u ∈ cf.U → ⁅g, u⁆ ∈ cf.V := by
  simp [centralizerOfChiefFactor, centralizerSubgroup, Subgroup.mem_inf]

/-- A subgroup `N` is contained in the centralizer of a chief factor `cf` relative to `H`
if and only if `N ≤ H` and the commutator `⁅N, cf.U⁆` is contained in `cf.V`. -/
public lemma CFSG.le_centralizerOfChiefFactor_iff {H N : Subgroup G} {cf : ChiefFactor G} :
    N ≤ centralizerOfChiefFactor (G := G) H cf ↔ N ≤ H ∧ ⁅N, cf.U⁆ ≤ cf.V := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (mem_centralizerOfChiefFactor (H := H) (cf := cf) (g := x)).1 (h hx) |>.1
    · -- Use the elementwise characterization of `⁅N, cf.U⁆ ≤ cf.V`.
      rw [Subgroup.commutator_le]
      intro n hn u hu
      have hn' := (mem_centralizerOfChiefFactor (H := H) (cf := cf) (g := n)).1 (h hn)
      exact hn'.2 u hu
  · rintro ⟨hNH, hcomm⟩
    intro x hx
    refine (mem_centralizerOfChiefFactor (H := H) (cf := cf) (g := x)).2 ?_
    refine ⟨hNH hx, ?_⟩
    -- Unpack `⁅N, cf.U⁆ ≤ cf.V` using `Subgroup.commutator_le`.
    exact (Subgroup.commutator_le).1 hcomm x hx

/-- If the lower term of a chief factor lies in a normal subgroup `N`, but the upper term does
not, then `N` centralizes that chief factor. -/
public theorem CFSG.le_centralizerOfChiefFactor_of_lower_le_of_not_upper_le
    {N : Subgroup G} (hN : N.Normal) (cf : ChiefFactor G)
    (hV_le_N : cf.V ≤ N) (hU_not_le_N : ¬ cf.U ≤ N) :
    N ≤ centralizerOfChiefFactor (G := G) N cf := by
  classical
  have hU_norm : cf.U.Normal := cf.isChief.normal_H
  have hNinf_norm : (N ⊓ cf.U).Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact ⟨hN.conj_mem x hx.1 g, hU_norm.conj_mem x hx.2 g⟩
  have hV_le_inf : cf.V ≤ N ⊓ cf.U := by
    intro x hx
    exact ⟨hV_le_N hx, cf.isChief.lt.le hx⟩
  have hinf_le_U : N ⊓ cf.U ≤ cf.U := inf_le_right
  rcases cf.isChief.is_maximal (N ⊓ cf.U) hNinf_norm hV_le_inf hinf_le_U with hInf_eq_V |
      hInf_eq_U
  · have hcomm_le_inf : ⁅N, cf.U⁆ ≤ N ⊓ cf.U := Subgroup.commutator_le_inf N cf.U
    have hcomm_le_V : ⁅N, cf.U⁆ ≤ cf.V := by
      simpa [hInf_eq_V] using hcomm_le_inf
    exact
      (le_centralizerOfChiefFactor_iff (G := G) (H := N) (N := N) (cf := cf)).2
        ⟨le_rfl, hcomm_le_V⟩
  · have hU_le_Ninf : cf.U ≤ N ⊓ cf.U := by simp [hInf_eq_U]
    have hU_le_N : cf.U ≤ N := hU_le_Ninf.trans (inf_le_left : N ⊓ cf.U ≤ N)
    exact False.elim (hU_not_le_N hU_le_N)

end ChiefFactorBasic

section ChiefFactorNormal

variable {G : Type*} [Group G]

/-- The centralizer of a chief factor relative to a normal subgroup `H` is itself normal. -/
public theorem CFSG.centralizerOfChiefFactor_normal {H : Subgroup G} (hH : H.Normal) (cf : ChiefFactor G) :
    (centralizerOfChiefFactor (G := G) H cf).Normal := by
  classical
  have hcf_norm : (centralizerSubgroup cf).Normal := centralizerSubgroup_normal cf
  refine ⟨fun n hn g => ?_⟩
  simp only [centralizerOfChiefFactor, Subgroup.mem_inf] at hn ⊢
  exact ⟨hH.conj_mem n hn.1 g, hcf_norm.conj_mem n hn.2 g⟩

end ChiefFactorNormal

section MinimalNormal

variable {G : Type*} [Group G] [Finite G]

/-- Every nontrivial normal subgroup of a finite group contains a minimal nontrivial normal subgroup.
Here "minimal" means minimal with respect to inclusion among nontrivial normal subgroups contained in `N`. -/
public theorem CFSG.exists_minimal_normal_le (N : Subgroup G) (hN : N.Normal) (hN_ne_bot : N ≠ ⊥) :
    ∃ M : Subgroup G,
      M.Normal ∧ M ≤ N ∧ M ≠ ⊥ ∧
        ∀ K : Subgroup G, K.Normal → K ≤ M → K ≠ ⊥ → K = M := by
  classical
  let P : Subgroup G → Prop := fun K => K.Normal ∧ K ≤ N ∧ K ≠ ⊥
  have hex : ∃ n : ℕ, ∃ K : Subgroup G, P K ∧ Nat.card K = n := by
    refine ⟨Nat.card N, N, ?_, rfl⟩
    exact ⟨hN, le_rfl, hN_ne_bot⟩
  let n0 : ℕ := Nat.find hex
  have hn0 : ∃ K : Subgroup G, P K ∧ Nat.card K = n0 := Nat.find_spec hex
  rcases hn0 with ⟨M, hMP, hMcard⟩
  refine ⟨M, hMP.1, hMP.2.1, hMP.2.2, ?_⟩
  intro K hKnorm hKle hK_ne_bot
  have hPK : P K := ⟨hKnorm, hKle.trans hMP.2.1, hK_ne_bot⟩
  -- `Nat.find` gives the minimal cardinality among subgroups satisfying `P`.
  have hmin : n0 ≤ Nat.card K :=
    Nat.find_min' hex ⟨K, hPK, rfl⟩
  have hcard_le : Nat.card M ≤ Nat.card K := by simpa [hMcard] using hmin
  -- Inclusion + cardinalities force equality.
  exact Subgroup.eq_of_le_of_card_ge hKle hcard_le

end MinimalNormal

section FittingSubgroupOfLemmas

variable {G : Type*} [Group G]

/-- The Fitting subgroup of a normal subgroup `H` is normal in the ambient group. -/
public theorem CFSG.fittingSubgroupOf_normal (H : Subgroup G) (hH : H.Normal) :
    (fittingSubgroupOf (G := G) H).Normal := by
  classical
  -- `fittingSubgroup (↥H)` is characteristic in `H`, hence its image in `G` is normal.
  let K : Subgroup (↥H) := fittingSubgroup (↥H)
  have hK_char : K.Characteristic :=
    (show (fittingSubgroup (↥H)).Characteristic from inferInstance)
  have hKmap_normal : (K.map H.subtype).Normal :=
    @ConjAct.normal_of_characteristic_of_normal G (inferInstance : Group G) H hH K hK_char
  simpa [fittingSubgroupOf, K] using hKmap_normal

/-- The infimum over the image of `centralizerOfChiefFactor H` on all chief factors equals
the indexed infimum over all chief factors. -/
public theorem CFSG.sInf_centralizerOfChiefFactor_univ_eq_iInf (H : Subgroup G) :
    sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) =
      ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf := by
  classical
  -- Turn the image of `Set.univ` into a `Set.range`, then use `sInf_range`.
  simpa [Set.image_univ] using
    (sInf_range (f := fun cf : ChiefFactor G => centralizerOfChiefFactor (G := G) H cf))

end FittingSubgroupOfLemmas
