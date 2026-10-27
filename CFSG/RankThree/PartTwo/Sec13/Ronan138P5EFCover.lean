module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5EFLift
public import CFSG.RankThree.PartTwo.Sec4.Ronan138P5Census
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LU3FieldD4Def
import CFSG.RankThree.PartTwo.Sec4.Ronan148LD4Pgu
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5R419
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lx
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Elem
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.KFacts.K71PSU3
import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

section Triple

variable {X : Type*} [Group X] {n : ℕ}

@[expose] def PGUTriple (Y : Subgroup X) (π : Y →* projSU 3 2 n) (P : X → Prop) : Prop :=
  ∃ (u : X) (d t w : Y), P u ∧ u ^ 3 = 1 ∧ d ^ 3 = 1 ∧ t ^ 2 = 1 ∧ u * (d : X) = d * u ∧
    u * (t : X) = t * u ∧ u ∈ Subgroup.normalizer (Y : Set X) ∧ π (d * t) ≠ π (t * d) ∧
    ∀ w' : Y, (w' : X) = u * w * u⁻¹ → π w' ≠ π w

theorem PGUTriple.of_mulEquiv [Finite X] {X' : Type*} [Group X'] (f : X ≃* X')
    {Y : Subgroup X} {π : Y →* projSU 3 2 n} {P : X → Prop} {P' : X' → Prop}
    (hP : ∀ u, P' u → P (f.symm u))
    (h : PGUTriple (Y.map f.toMonoidHom)
      (π.comp (Y.equivMapOfInjective f.toMonoidHom f.injective).symm.toMonoidHom) P') :
    PGUTriple Y π P := by
  set ψ := Y.equivMapOfInjective f.toMonoidHom f.injective with hψ
  obtain ⟨u, d, t, w, hPu, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩ := h
  have hcoe : ∀ z : Y.map f.toMonoidHom, ((ψ.symm z : Y) : X) = f.symm (z : X') := by
    intro z
    apply f.injective
    rw [MulEquiv.apply_symm_apply]
    have : ((ψ (ψ.symm z) : Y.map f.toMonoidHom) : X') = f ((ψ.symm z : Y) : X) := rfl
    rw [← this, MulEquiv.apply_symm_apply]
  refine ⟨f.symm u, ψ.symm d, ψ.symm t, ψ.symm w, hP u hPu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hu3, map_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_pow, ht2, map_one]
  · rw [hcoe, ← map_mul, hud, map_mul]
  · rw [hcoe, ← map_mul, hut, map_mul]
  · apply Subgroup.mem_normalizer_fintype
    intro z hz
    have hz' : f z ∈ Y.map f.toMonoidHom := ⟨z, hz, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp huN (f z)).mp hz'
    rw [Subgroup.mem_map_equiv] at h1
    have h2 : f.symm u * z * (f.symm u)⁻¹ ∈ Y := by
      simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h1
    exact h2
  · change π (ψ.symm d * ψ.symm t) ≠ π (ψ.symm t * ψ.symm d)
    rw [← map_mul, ← map_mul]
    exact hdt
  · intro w'' hw''
    have h1 : ((ψ w'' : Y.map f.toMonoidHom) : X') = u * w * u⁻¹ := by
      change f (w'' : X) = _
      rw [hw'', hcoe, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
    have h2 := hw (ψ w'') h1
    change π (ψ.symm (ψ w'')) ≠ π (ψ.symm w) at h2
    rwa [MulEquiv.symm_apply_apply] at h2

theorem PGUTriple.of_subgroupOf [Finite X] {B Y : Subgroup X} (hYB : Y ≤ B)
    {π : Y →* projSU 3 2 n} {P : X → Prop} {P' : B → Prop} (hP : ∀ u, P' u → P u)
    (h : PGUTriple (Y.subgroupOf B) (π.comp (Subgroup.subgroupOfEquivOfLe hYB).toMonoidHom) P') :
    PGUTriple Y π P := by
  set ψ := Subgroup.subgroupOfEquivOfLe hYB with hψ
  obtain ⟨u, d, t, w, hPu, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩ := h
  refine ⟨(u : X), ψ d, ψ t, ψ w, hP u hPu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hu3, Subgroup.coe_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_pow, ht2, map_one]
  · exact congrArg Subtype.val hud
  · exact congrArg Subtype.val hut
  · apply Subgroup.mem_normalizer_fintype
    intro z hz
    have hzY : (⟨z, hYB hz⟩ : B) ∈ Y.subgroupOf B := Subgroup.mem_subgroupOf.mpr hz
    have h1 := (Subgroup.mem_normalizer_iff.mp huN _).mp hzY
    exact Subgroup.mem_subgroupOf.mp h1
  · change π (ψ d * ψ t) ≠ π (ψ t * ψ d)
    rw [← map_mul, ← map_mul]
    exact hdt
  · intro w'' hw''
    have h1 : (((ψ.symm w'' : Y.subgroupOf B) : B) : X) = (w'' : X) := by
      have : ψ (ψ.symm w'') = w'' := MulEquiv.apply_symm_apply _ _
      exact congrArg Subtype.val this
    have h2 : ((ψ.symm w'' : Y.subgroupOf B) : B) = u * w * u⁻¹ := by
      apply Subtype.ext
      rw [h1, hw'']
      rfl
    have := hw (ψ.symm w'') h2
    change π (ψ (ψ.symm w'')) ≠ π (ψ w) at this
    rwa [MulEquiv.apply_symm_apply] at this

end Triple

variable {G : Type} [Group G] [Finite G]

theorem rho_mk {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    rho L ⟨g, hg⟩ (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp l.2⟩ : L) :
        L ⧸ aschbacherSolvableCore 3 L) :=
  rfl

theorem rho_mk_eq_of_commute {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {l : L} (hl : (l : G) * g = g * l) :
    rho L ⟨g, hg⟩ (l : L ⧸ aschbacherSolvableCore 3 L) = l := by
  rw [rho_mk]
  congr 1
  apply Subtype.ext
  change g * (l : G) * g⁻¹ = l
  rw [← hl, mul_inv_cancel_right]

theorem mk_eq_mk_iff {L : Subgroup G} (u v : L) :
    (u : L ⧸ aschbacherSolvableCore 3 L) = v ↔
      (u : G)⁻¹ * v ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [QuotientGroup.eq]
  constructor
  · intro huv
    exact ⟨_, huv, by simp⟩
  · rintro ⟨t, ht, hte⟩
    have : u⁻¹ * v = t := Subtype.ext (by simpa using hte.symm)
    rwa [this]

theorem isSolvable_inSubgroup_theta (L : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) L) := by
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  exact Group.isSolvable_of_surjective (f := L.subtype.subgroupMap (aschbacherSolvableCore 3 L))
    (L.subtype.subgroupMap_surjective _)

theorem isSolvable_of_le_theta {L W : Subgroup G}
    (hW : W ≤ inSubgroup (aschbacherSolvableCore 3) L) : Group.IsSolvable W := by
  have := isSolvable_inSubgroup_theta L
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hW)

theorem surjective_mk_comp_inclusion {L J : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L) :
    Function.Surjective
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hJL)) := by
  intro d
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective d
  have hlJ : (l : G) ∈ (J : Set G) * (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J _
      (hJL.trans (Sec6.le_normalizer_theta L))]
    exact hcov l.2
  obtain ⟨j, hj, k, hk, hjk⟩ := hlJ
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [← hl]
  apply QuotientGroup.eq.mpr
  obtain ⟨k', hk', rfl⟩ := hk
  have : (Subgroup.inclusion hJL ⟨j, hj⟩)⁻¹ * l = k' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hjk]
    simp
  rw [this]
  exact hk'

theorem le_theta_of_isSolvable {L J W : Subgroup G}
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L) (hWL : W ≤ L)
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) (hWs : Group.IsSolvable W) :
    W ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hq
  set Wb : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (W.subgroupOf L).map q with hWb
  have hn : Wb.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨j, rfl⟩ := surjective_mk_comp_inclusion hJL hcov g
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨Subgroup.inclusion hJL j * w * (Subgroup.inclusion hJL j)⁻¹, ?_, ?_⟩
    · have hw' : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      exact (Subgroup.mem_normalizer_iff.mp (hJW j.2) _).mp hw'
    · rw [hq, map_mul, map_mul, map_inv]
      rfl
  have hWs' : Group.IsSolvable (W.subgroupOf L) := by
    haveI := hWs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hWL).toMonoidHom) (MulEquiv.injective _)
  have hs : Group.IsSolvable Wb := by
    haveI := hWs'
    exact Group.isSolvable_of_surjective (f := q.subgroupMap (W.subgroupOf L))
      (q.subgroupMap_surjective _)
  have h1 := eq_bot_of_isSolvable_of_normal hLq hZ hn hs
  intro w hw
  have hmem : ((⟨w, hWL hw⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ Wb :=
    ⟨⟨w, hWL hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  rw [h1, Subgroup.mem_bot] at hmem
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩

theorem exists_mem_centralizer_of_rho_fixed {Lx : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Lx : Set G)) (hc3 : c ^ 3 = 1)
    {ub : Lx ⧸ aschbacherSolvableCore 3 Lx} (hfix : rho Lx ⟨c, hcN⟩ ub = ub) :
    ∃ m : Lx, (m : G) ∈ Subgroup.centralizer ({c} : Set G) ∧
      (m : Lx ⧸ aschbacherSolvableCore 3 Lx) = ub := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective ub
  obtain ⟨m', hm'c, hm'l⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed (Y := Lx) (M := Lx)
    le_rfl hcN hcN hc3 l.2 hfix
  exact ⟨m', hm'c, hm'l⟩

theorem exists_lift_three_of_rho_fixed {Lx : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Lx : Set G)) (hc3 : c ^ 3 = 1)
    {ub : Lx ⧸ aschbacherSolvableCore 3 Lx} (hfix : rho Lx ⟨c, hcN⟩ ub = ub) (hu3 : ub ^ 3 = 1) :
    ∃ y : Lx, (y : G) ∈ Subgroup.centralizer ({c} : Set G) ∧
      (y : Lx ⧸ aschbacherSolvableCore 3 Lx) = ub ∧ y ^ 3 = 1 := by
  obtain ⟨m, hmc, hmu⟩ := exists_mem_centralizer_of_rho_fixed hcN hc3 hfix
  obtain ⟨k, hku, hk3⟩ := exists_pow_lift_three m hmu hu3
  refine ⟨m ^ k, ?_, hku, hk3⟩
  rw [Subgroup.coe_pow]
  exact Subgroup.pow_mem _ hmc k

theorem mem_normalizer_of_forall_mul {c y : G} {L J W : Subgroup G} (hc3 : c ^ 3 = 1)
    (hL : L ∈ thetaComponentsAt 3 c) (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L) (hWs : Group.IsSolvable W)
    (hyc : y * c = c * y) (hJy : ∀ j ∈ J, ∃ j₁ ∈ J, ∃ w ∈ W, j = y * j₁ * y⁻¹ * w) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hyL
  have hyc' : y * c * y⁻¹ ∈ Subgroup.zpowers c := by
    rw [hyc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hLy := Sec11.map_conj_mem_thetaComponentsAt hc3 hL hyc'
  have hne : L.map (MulAut.conj y).toMonoidHom ≠ L := fun heq =>
    hyL (Sec13.map_conj_eq_iff_mem_normalizer.mp heq)
  have hle := Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hLy hL hne
  set NL := Subgroup.normalizer (L : Set G) with hNL
  have hJN : J ≤ NL := hJL.trans Subgroup.le_normalizer
  set R : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    ((W ⊓ NL).subgroupOf NL).map (rho L) with hR
  have hRs : Group.IsSolvable R := by
    haveI := hWs
    have h1 : Group.IsSolvable ((W ⊓ NL).subgroupOf NL) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_left : W ⊓ NL ≤ W)).comp
          (Subgroup.subgroupOfEquivOfLe (inf_le_right : W ⊓ NL ≤ NL)).toMonoidHom)
        ((Subgroup.inclusion_injective (inf_le_left : W ⊓ NL ≤ W)).comp (MulEquiv.injective _))
    haveI := h1
    exact Group.isSolvable_of_surjective (f := (rho L).subgroupMap _)
      ((rho L).subgroupMap_surjective _)
  set ρJ : J →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (rho L).comp (Subgroup.inclusion hJN) with hρJ
  have hJR : ρJ.range ≤ R := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨j₁, hj₁, w, hw, hjeq⟩ := hJy j j.2
    have hz : y * j₁ * y⁻¹ ∈ Sec4.thetaQuotCentralizer L := hle ⟨j₁, hJL hj₁, rfl⟩
    obtain ⟨zN, hz1, hzrfl⟩ := hz
    have hzG : (zN : G) = y * j₁ * y⁻¹ := hzrfl
    have hwN : w ∈ NL := by
      have : w = (zN : G)⁻¹ * j := by
        rw [hzG, hjeq]
        group
      rw [this]
      exact NL.mul_mem (NL.inv_mem zN.2) (hJN j.2)
    refine ⟨⟨w, hwN⟩, Subgroup.mem_subgroupOf.mpr ⟨hw, hwN⟩, ?_⟩
    have hj : Subgroup.inclusion hJN j = zN * ⟨w, hwN⟩ := Subtype.ext (by
      change (j : G) = (zN : G) * w
      rw [hzG, hjeq])
    have hz1' : rho L zN = 1 := MonoidHom.mem_ker.mp hz1
    change rho L ⟨w, hwN⟩ = rho L (Subgroup.inclusion hJN j)
    rw [hj, map_mul, hz1', one_mul]
  have hJs : Group.IsSolvable J := by
    have hmem : ∀ k : ρJ.ker, ((k : J) : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      intro k
      have h1 : rho L (Subgroup.inclusion hJN (k : J)) = 1 := MonoidHom.mem_ker.mp k.2
      have h2 : ((k : J) : G) ∈ Sec4.thetaQuotCentralizer L :=
        ⟨Subgroup.inclusion hJN (k : J), MonoidHom.mem_ker.mpr h1, rfl⟩
      exact Sec4.Item424Proof.mem_theta_of_mem_thetaQuotCentralizer hZ (hJL (k : J).2) h2
    have hker : Group.IsSolvable ρJ.ker := by
      have := isSolvable_inSubgroup_theta L
      set ι : ρJ.ker →* inSubgroup (aschbacherSolvableCore 3) L :=
        { toFun := fun k => ⟨((k : J) : G), hmem k⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl } with hι
      exact Group.isSolvable_of_isSolvable_injective (f := ι)
        (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg (fun t : inSubgroup (aschbacherSolvableCore 3) L => (t : G)) hab)))
    have hran : Group.IsSolvable ρJ.range := by
      haveI := hRs
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJR)
    haveI := hker
    haveI := hran
    exact Group.isSolvable_of_ker_le_range ρJ.ker.subtype ρJ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hLs : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) := by
    haveI := hJs
    exact Group.isSolvable_of_surjective (surjective_mk_comp_inclusion hJL hcov)
  have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hLq.1
  have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  exact Group.IsPerfect.not_isSolvable _ hLs

section Kinds


theorem step13PZeroEFLift_of_cover (hC : Sec4.K419UnitaryCensusCover) (h46 : Sec4.Item4_6)
    (hD4 : Sec4.Ronan148L.KF138TrialityPGUCent) : Step13PZeroEFLift := by
  intro G _ _ A c L P₀ n hU x hxP hxc Lx hLx hJLx hcN hkind
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hU.sec13
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hLc := h.le_centralizer
  have hL := h.mem_thetaComponentsAt
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  obtain ⟨eL⟩ := hU.iso
  have hn1 : 1 ≤ n := by have := hU.one_lt; omega
  have hq2 : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hU.odd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hL3 : IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ⟨2, n, ⟨Nat.prime_two⟩, hn1, Or.inr ⟨hq2, ⟨eL⟩⟩⟩
  have hZ := center_eq_bot_of_isLThreePi hLq hL3
  have hP₀e := hU.elem
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hq : 2 < 2 ^ (3 * n) := by
    have := hU.one_lt
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcLx : c ∉ Sec4.thetaQuotCentralizer Lx := by
    intro hcC
    have hout : Sec4.InducesOuterTheta c Lx := by
      rcases hkind with hk | hk
      · exact KFacts.InducesStdKind.inducesOuterTheta Lx hk (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta Lx hk (by decide)
    obtain ⟨hN, hnot⟩ := hout
    obtain ⟨hx', h1⟩ := Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mp hcC
    exact hnot ⟨1, by rw [map_one]; exact h1.symm⟩
  have htyped := typed419_of hC h46 hU hxP hxc hLx hJLx hcN hcLx
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) with hJdef
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set θx := inSubgroup (aschbacherSolvableCore 3) Lx with hθx
  have hJL : J ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) := hJL.trans hLc
  have hxL : Subgroup.zpowers x ≤ Sec4.thetaQuotCentralizer L :=
    Subgroup.zpowers_le.mpr (hU.le hxP)
  have hcov : L ≤ J ⊔ θL := by
    have := Sec6.le_residual_inf_centralizer_sup_theta hLp
      (Sec6.isPGroup_zpowers_of_pow_three hx3) hxL
    rwa [Sec6.centralizer_zpowers_eq] at this
  have hJperf : Group.IsPerfect J := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJθ : J ∈ thetaComponentsIn
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) := by
    have := Sec6.residual_inf_centralizer_mem_thetaComponentsIn hL
      (Sec6.isPGroup_zpowers_of_pow_three hx3) hxL
    rwa [Sec6.centralizer_zpowers_eq] at this
  set ρx := rho Lx ⟨c, hcN⟩ with hρx
  set χ : J →* Lx ⧸ aschbacherSolvableCore 3 Lx :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Lx)).comp (Subgroup.inclusion hJLx) with hχ
  set Yb := χ.range with hYb
  have hYbp : Group.IsPerfect Yb := by
    haveI := hJperf
    exact Group.IsPerfect.range χ
  have hYfix : ∀ v ∈ Yb, ρx v = v := by
    rintro _ ⟨j, rfl⟩
    exact rho_mk_eq_of_commute hcN (l := Subgroup.inclusion hJLx j)
      (Subgroup.mem_centralizer_singleton_iff.mp (hJc j.2))
  set ρ₀ : J →* Yb := χ.rangeRestrict with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := χ.rangeRestrict_surjective
  set πL₀ : J →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hJL) with hπL₀
  have hπL₀s : Function.Surjective πL₀ := surjective_mk_comp_inclusion hJL hcov
  have hker : ρ₀.ker ≤ πL₀.ker := by
    intro j hj
    have hj1 : ((Subgroup.inclusion hJLx j : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
    have hjθ : (j : G) ∈ θx := ⟨_, (QuotientGroup.eq_one_iff _).mp hj1, rfl⟩
    have hjθL : (j : G) ∈ θL :=
      le_theta_of_le_thetaQuotCentralizer (S₀ := J ⊓ θx) hLq hZ hJL hcov hJLx inf_le_left
        (inf_le_right.trans (theta_le_thetaQuotCentralizer Lx)) ⟨j.2, hjθ⟩
    obtain ⟨t, ht, hte⟩ := hjθL
    have : Subgroup.inclusion hJL j = t := Subtype.ext hte.symm
    rw [MonoidHom.mem_ker, hπL₀, MonoidHom.comp_apply, this, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr ht]
  set πL : Yb →* L ⧸ aschbacherSolvableCore 3 L := ρ₀.liftOfSurjective hρ₀s ⟨πL₀, hker⟩
    with hπL
  have hπLρ : ∀ j : J, πL (ρ₀ j) = πL₀ j := fun j =>
    ρ₀.liftOfRightInverse_comp_apply (Function.surjInv hρ₀s) (Function.rightInverse_surjInv hρ₀s)
      ⟨πL₀, hker⟩ j
  set π : Yb →* projSU 3 2 n := eL.toMonoidHom.comp πL with hπ
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨j, hj⟩ := hπL₀s (eL.symm z)
    refine ⟨ρ₀ j, ?_⟩
    change eL (πL (ρ₀ j)) = z
    rw [hπLρ, hj, MulEquiv.apply_symm_apply]
  have hπk : Nat.Coprime (Nat.card π.ker) 3 := by
    have hkeq : π.ker = πL₀.ker.map ρ₀ := by
      ext v
      constructor
      · intro hv
        obtain ⟨j, rfl⟩ := hρ₀s v
        have hj : πL₀ j = 1 := by
          apply eL.injective
          rw [map_one, ← hπLρ]
          exact MonoidHom.mem_ker.mp hv
        exact ⟨j, MonoidHom.mem_ker.mpr hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine MonoidHom.mem_ker.mpr ?_
        change eL (πL (ρ₀ j)) = 1
        rw [hπLρ, MonoidHom.mem_ker.mp hj, map_one]
    have hmem : ∀ k : πL₀.ker, Subgroup.inclusion hJL (k : J) ∈ aschbacherSolvableCore 3 L := by
      intro k
      have h1 : ((Subgroup.inclusion hJL (k : J) : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
        MonoidHom.mem_ker.mp k.2
      exact (QuotientGroup.eq_one_iff _).mp h1
    set ι : πL₀.ker →* aschbacherSolvableCore 3 L :=
      { toFun := fun k => ⟨Subgroup.inclusion hJL (k : J), hmem k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl } with hι
    have hιi : Function.Injective ι := fun u v huv =>
      Subtype.ext (Subtype.ext (congrArg (fun t : aschbacherSolvableCore 3 L => ((t : L) : G)) huv))
    have hθ3 : Nat.Coprime (Nat.card (aschbacherSolvableCore 3 L)) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (KFacts.not_three_dvd_card_aschbacherSolvableCore L)).symm
    rw [hkeq]
    exact Nat.Coprime.coprime_dvd_left
      ((Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_injective ι hιi)) hθ3
  set K : Subgroup G := Lx ⊓ Subgroup.centralizer ({c} : Set G) with hK
  have hJK : J ≤ K := le_inf hJLx hJc
  set M : Subgroup G :=
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hMdef
  have hLxC : Lx ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsIn_iff.mp hLx).1
  have hKM : K ≤ M := inf_le_inf_right _ hLxC
  have hJsnM : (J.subgroupOf M).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hJθ).2).2.1
  have hJsnK : (J.subgroupOf K).IsSubnormal := by
    have : J.subgroupOf K = (J.subgroupOf M).comap (Subgroup.inclusion hKM) := by
      ext k
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact hJsnM.comap _
  have htriple : PGUTriple Yb π (fun u => ρx u = u) := by
    rcases htyped with ⟨K', _, hUK, hk⟩ | ⟨K', _, _, hK', σ, hσ, hk⟩
    ·
      obtain ⟨f₀, hf₀, K'', _, _, hK'', ⟨ι⟩⟩ :=
        KFacts.isoPGUThree_barCentralizer_of_field hq hc3 hk
      have hf₀n : f₀ = n := by omega
      subst f₀
      set B := Sec8.barCentralizer (Subgroup.zpowers c) Lx with hB
      have hYB : Yb ≤ B := fun v hv =>
        (KFacts.mem_barCentralizer_zpowers_iff hcN v).mpr (hYfix v hv)
      have hK''u : UnitaryFieldData 2 n K'' :=
        ⟨Nat.prime_two, hn1, by rw [hK'', ← pow_mul, mul_comm]⟩
      refine PGUTriple.of_subgroupOf hYB (P' := fun _ => True)
        (fun u _ => (KFacts.mem_barCentralizer_zpowers_iff hcN u).mp u.2) ?_
      refine PGUTriple.of_mulEquiv ι (P' := fun _ => True) (fun _ _ => trivial) ?_
      have hYBp : Group.IsPerfect (Yb.subgroupOf B) := by
        haveI := hYbp
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hYB).symm.toMonoidHom) (MulEquiv.surjective _)
      have hY₂p : Group.IsPerfect ((Yb.subgroupOf B).map ι.toMonoidHom) := by
        haveI := hYBp
        exact Group.IsPerfect.map ι.toMonoidHom
      obtain ⟨u, d, t, w, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩ :=
        Sec4.Ronan148L.pgu3_triple hU.odd hK''u hY₂p
          ((π.comp (Subgroup.subgroupOfEquivOfLe hYB).toMonoidHom).comp
            ((Yb.subgroupOf B).equivMapOfInjective ι.toMonoidHom ι.injective).symm.toMonoidHom)
          ((hπs.comp (Subgroup.subgroupOfEquivOfLe hYB).surjective).comp (MulEquiv.surjective _))
      exact ⟨u, d, t, w, trivial, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩
    ·
      obtain ⟨e, hx', hR⟩ := hk
      set α := inducedAutHom Lx e ⟨c, hx'⟩ with hα
      have hαapp : ∀ m, α m = e (ρx (e.symm m)) := fun m => rfl
      have hc'3 : (⟨c, hx'⟩ : Subgroup.normalizer (Lx : Set G)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3)
      have hα3 : α ^ 3 = 1 := by
        rw [hα, ← map_pow, hc'3, map_one]
      set Ym := Yb.map e.toMonoidHom with hYm
      have hYα : ∀ v ∈ Ym, α v = v := by
        rintro _ ⟨v, hv, rfl⟩
        rw [hαapp]
        change e (ρx (e.symm (e v))) = e v
        rw [MulEquiv.symm_apply_apply, hYfix v hv]
      have hYmp : Group.IsPerfect Ym := by
        haveI := hYbp
        exact Group.IsPerfect.map e.toMonoidHom
      have hκmem : ∀ k : K, (e.toMonoidHom.comp ((QuotientGroup.mk'
          (aschbacherSolvableCore 3 Lx)).comp (Subgroup.inclusion (inf_le_left : K ≤ Lx)))) k ∈
          Sec4.autFix α := by
        intro k
        refine Sec4.mem_autFix.mpr ?_
        rw [hαapp]
        change e (ρx (e.symm (e ((Subgroup.inclusion (inf_le_left : K ≤ Lx) k : Lx) :
          Lx ⧸ aschbacherSolvableCore 3 Lx)))) = e _
        rw [MulEquiv.symm_apply_apply, rho_mk_eq_of_commute hcN
          (Subgroup.mem_centralizer_singleton_iff.mp k.2.2)]
        rfl
      set κ : K →* Sec4.autFix α := (e.toMonoidHom.comp ((QuotientGroup.mk'
          (aschbacherSolvableCore 3 Lx)).comp (Subgroup.inclusion (inf_le_left : K ≤ Lx)))).codRestrict
          _ hκmem with hκ
      have hκs : Function.Surjective κ := by
        rintro ⟨m, hm⟩
        have hfix : ρx (e.symm m) = e.symm m := by
          have h1 := Sec4.mem_autFix.mp hm
          rw [hαapp] at h1
          apply e.injective
          rw [h1, MulEquiv.apply_symm_apply]
        obtain ⟨l, hlc, hl⟩ := exists_mem_centralizer_of_rho_fixed hcN hc3 hfix
        refine ⟨⟨l, l.2, hlc⟩, Subtype.ext ?_⟩
        show e ((l : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) = m
        rw [hl, MulEquiv.apply_symm_apply]
      have hYsub : Ym.subgroupOf (Sec4.autFix α) = (J.subgroupOf K).map κ := by
        ext w
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨v, ⟨j, rfl⟩, hv⟩
          exact ⟨⟨j, hJK j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, Subtype.ext hv⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨χ ⟨k, Subgroup.mem_subgroupOf.mp hk⟩, ⟨_, rfl⟩, rfl⟩
      have hYsn : (Ym.subgroupOf (Sec4.autFix α)).IsSubnormal := by
        rw [hYsub]
        exact Subgroup.IsSubnormal.map hκs hJsnK
      set ψ := Yb.equivMapOfInjective e.toMonoidHom e.injective with hψ
      set πm : Ym →* projSU 3 2 n := π.comp ψ.symm.toMonoidHom with hπm
      have hπms : Function.Surjective πm := hπs.comp ψ.symm.surjective
      have hπmk : Nat.Coprime (Nat.card πm.ker) 3 := by
        have hle : πm.ker.map ψ.symm.toMonoidHom ≤ π.ker := by
          rintro _ ⟨z, hz, rfl⟩
          exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hz)
        have h1 := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective ψ.symm.injective] at h1
        exact Nat.Coprime.coprime_dvd_left h1 hπk
      refine PGUTriple.of_mulEquiv e (P' := fun u => α u = u) (fun u hu => ?_)
        (hD4 n hU.odd hU.one_lt hU.not_three_dvd K' hK' σ hσ α hα3 hR Ym hYα hYsn hYmp πm
          hπms hπmk)
      have h1 := hαapp u
      rw [hu] at h1
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact h1.symm
  obtain ⟨ub, db, tb, wb, hub, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩ := htriple
  obtain ⟨y, hyc, hyu, hy3⟩ := exists_lift_three_of_rho_fixed hcN hc3 hub hu3
  have hyc' : (y : G) * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
  have hqeq := mk_eq_mk_iff (L := Lx)
  have hqeqL := mk_eq_mk_iff (L := L)
  have hWs : Group.IsSolvable (θx ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :=
    isSolvable_of_le_theta (L := Lx) inf_le_left
  have hJy : ∀ j ∈ J, ∃ j₁ ∈ J, ∃ w ∈ θx ⊓ Subgroup.centralizer ({c} : Set G),
      j = y * j₁ * (y : G)⁻¹ * w := by
    intro j hj
    have h1 : ub⁻¹ * χ ⟨j, hj⟩ * ub ∈ Yb := by
      apply (Subgroup.mem_normalizer_iff.mp huN (ub⁻¹ * χ ⟨j, hj⟩ * ub)).mpr
      rw [show ub * (ub⁻¹ * χ ⟨j, hj⟩ * ub) * ub⁻¹ = χ ⟨j, hj⟩ by group]
      exact ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨j₁, hj₁⟩ := h1
    have h2 : ((Subgroup.inclusion hJLx j₁ : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) =
        ((y⁻¹ * Subgroup.inclusion hJLx ⟨j, hj⟩ * y : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hyu]
      exact hj₁
    have h3 : (j₁ : G)⁻¹ * ((y : G)⁻¹ * j * y) ∈ θx := by
      have := (hqeq _ _).mp h2
      simpa using this
    refine ⟨j₁, j₁.2, y * ((j₁ : G)⁻¹ * ((y : G)⁻¹ * j * y)) * (y : G)⁻¹, ⟨?_, ?_⟩, by group⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Lx y.2) _).mp h3
    · have : (y : G) * ((j₁ : G)⁻¹ * ((y : G)⁻¹ * j * y)) * (y : G)⁻¹ =
          ((y : G) * j₁ * (y : G)⁻¹)⁻¹ * j := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hyc (hJc j₁.2)) (Subgroup.inv_mem _ hyc))) (hJc hj)
  have hyN : (y : G) ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_forall_mul hc3 hL hLq hZ hJL hcov hWs hyc' hJy
  have hJθxL : J ≤ Subgroup.normalizer ((θx ⊓ L : Subgroup G) : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Lx (hJLx hj)) z
    have h2 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (hJL hj) : j ∈ Subgroup.normalizer (L : Set G)) z
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have hθxL : θx ⊓ L ≤ θL :=
    le_theta_of_isSolvable hLq hZ hJL hcov inf_le_right hJθxL
      (isSolvable_of_le_theta (L := Lx) inf_le_left)
  have hint : ∀ v v' : Yb, (v' : Lx ⧸ aschbacherSolvableCore 3 Lx) = ub * v * ub⁻¹ →
      rho L ⟨y, hyN⟩ (πL v) = πL v' := by
    intro v v' hvv'
    obtain ⟨j, rfl⟩ := hρ₀s v
    obtain ⟨j₂, rfl⟩ := hρ₀s v'
    rw [hπLρ, hπLρ]
    have h1 : ((Subgroup.inclusion hJLx j₂ : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) =
        ((y * Subgroup.inclusion hJLx j * y⁻¹ : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hyu]
      exact hvv'
    have h2 : (j₂ : G)⁻¹ * ((y : G) * j * (y : G)⁻¹) ∈ θx := by
      have := (hqeq _ _).mp h1
      simpa using this
    have hyjL : (y : G) * j * (y : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN j).mp (hJL j.2)
    have h3 : (j₂ : G)⁻¹ * ((y : G) * j * (y : G)⁻¹) ∈ θL :=
      hθxL ⟨h2, L.mul_mem (L.inv_mem (hJL j₂.2)) hyjL⟩
    change rho L ⟨y, hyN⟩ ((Subgroup.inclusion hJL j : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.inclusion hJL j₂ : L) : L ⧸ aschbacherSolvableCore 3 L)
    rw [rho_mk]
    exact ((hqeqL _ _).mpr h3).symm
  set σy := rho L ⟨y, hyN⟩ with hσy
  have hfixt : σy (πL tb) = πL tb := hint tb tb (by rw [hut, mul_inv_cancel_right])
  have hfixd : σy (πL db) = πL db := hint db db (by rw [hud, mul_inv_cancel_right])
  have hdtL : πL db * πL tb ≠ πL tb * πL db := by
    intro h'
    apply hdt
    change eL (πL (db * tb)) = eL (πL (tb * db))
    rw [map_mul πL, map_mul πL, h']
  have ht1 : πL tb ≠ 1 := by
    intro h1
    apply hdtL
    rw [h1, mul_one, one_mul]
  have ht2' : (πL tb) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hd3' : (πL db) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  obtain ⟨hV1, hV2, -⟩ := zpowers_involution_witness (j := (1 : L ⧸ aschbacherSolvableCore 3 L))
    ht2' ht1 (by rw [one_mul, mul_one])
  refine ⟨y, ⟨y.2, hyc⟩, by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one], hyN, ?_,
    ⟨Subgroup.zpowers (πL tb), hV1, hV2, ?_⟩, πL db, hd3', hfixd, ?_⟩
  · intro h1
    replace h1 : σy = 1 := h1
    have hw'mem : ub * (wb : Lx ⧸ aschbacherSolvableCore 3 Lx) * ub⁻¹ ∈ Yb :=
      (Subgroup.mem_normalizer_iff.mp huN _).mp wb.2
    have h2 := hint wb ⟨_, hw'mem⟩ rfl
    change σy (πL wb) = _ at h2
    rw [h1, MulAut.one_apply] at h2
    exact hw ⟨_, hw'mem⟩ rfl (by
      change eL (πL ⟨_, hw'mem⟩) = eL (πL wb)
      rw [← h2])
  · intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow, hfixt]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro k hk
    have h1 : ∀ m : ℕ, (σy ^ m) (πL tb) = πL tb := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hfixt, ih]
    have h2 := h1 k
    rw [hk, MulAut.conj_apply] at h2
    apply hdtL
    calc πL db * πL tb = πL db * πL tb * (πL db)⁻¹ * πL db := by group
      _ = πL tb * πL db := by rw [h2]

end Kinds

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
