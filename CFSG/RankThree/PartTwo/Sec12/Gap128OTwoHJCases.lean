module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCore
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Census (CriticalAt)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pRank_le_localRank_of_le_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {T H : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hH : H ≤ Subgroup.normalizer (T : Set G)) : CFSG.pRank p H ≤ localRank p G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hbdd : BddAbove
      {k | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧ CFSG.Assembly.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    obtain ⟨F, -, -, hF⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change CFSG.Open.pRank p H ≤ Nat.card G
    omega
  exact (CFSG.SectionRank.pRank_mono hp.one_lt hH).trans
    (le_csSup hbdd ⟨_, ⟨T, hT, hT2, rfl⟩, rfl⟩)

theorem pRank_fixedSubgroupOf_le {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {D : Subgroup Y} (hD : CriticalAt p D) {t : Y} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : CFSG.pRank p (fixedSubgroupOf (hD.conjD t)) ≤ localRank p Y := by
  set C := fixedSubgroupOf (hD.conjD t)
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hC : ∀ c ∈ C.map D.subtype, c * t = t * c := by
    rintro _ ⟨c, hc, rfl⟩
    have h := congrArg Subtype.val ((mem_fixedSubgroupOf _ c).mp hc)
    rw [hD.conjD_apply] at h
    change (c : Y) * t = t * c
    calc (c : Y) * t = t * c * t⁻¹ * t := by rw [h]
      _ = t * c := by group
  have h1 := Sec4.Census.pRank_le_localRank_of_centralizes hp.out hp2 ht hC
  rwa [← pRank_congr_mulEquiv hp.out.one_lt
    (C.equivMapOfInjective D.subtype D.subtype_injective)] at h1

theorem false_of_e8 {Y : Type} [Group Y] [Finite Y] (π : Y →* NativeSporadic.J2)
    (hπ : Function.Surjective π) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hloc : localRank p Y < 3) {D : Subgroup Y} (hD : CriticalAt p D)
    (hDK : hD.frattiniKer ≤ π.ker)
    (hodd : ∀ t : Y, (∀ d ∈ D, t * d = d * t) → t ^ 2 = 1 → t = 1)
    {A : Type} [CommGroup A] [Finite A] (hA2 : ∀ a : A, a ^ 2 = 1) (hA8 : Nat.card A = 8)
    (ι : A →* Y) (hι : Function.Injective ι) : False := by
  have hDp : IsPGroup p D := (pCore_isPGroup (p := p) (G := Y)).to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  let ρA : A →* MulAut D := hD.conjD.comp ι
  have hinj : Function.Injective ρA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hι
    rw [map_one]
    refine hodd (ι a) (fun d hd => ?_) (by rw [← map_pow, hA2, map_one])
    have h := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : Y)) ha
    simp only [ρA, MonoidHom.comp_apply, hD.conjD_apply, MulAut.one_apply] at h
    calc ι a * d = ι a * d * (ι a)⁻¹ * ι a := by group
      _ = d * ι a := by rw [h]
  have hfixA : ∀ a : A, a ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρA a)) ≤ 2 := by
    intro a ha
    have h1 : CFSG.pRank p (fixedSubgroupOf (ρA a)) ≤ localRank p Y :=
      pRank_fixedSubgroupOf_le hp2 hD (t := ι a) (by rw [← map_pow, hA2, map_one])
        (fun h => ha (hι (by rw [h, map_one])))
    omega
  have h48 := (class_two_eight_action_inverting_quotient hp2 hDp hexp hD.commutator_le_center
    hA2 hA8 ρA hinj hfixA).1
  obtain ⟨V, _, _, _, ρ, hρ, hdim, -⟩ := exists_frattiniModule hp2 hD
  exact false_of_finrank_le_four π hπ (by omega) ρ fun g hg => hDK (hρ g hg)

theorem false_of_central_involution {Y : Type} [Group Y]
    [Finite Y] (π : Y →* NativeSporadic.J2) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Y →* Module.End (ZMod p) V) (hker : ∀ g, ρ g = 1 → π g = 1)
    (hfix : ∀ t : Y, t ^ 2 = 1 → t ≠ 1 → Module.finrank (ZMod p) ((ρ t).eigenspace 1) ≤ 2)
    (L : Subgroup Y) [Group.IsPerfect L] (hL : Function.Surjective (π.comp L.subtype))
    (hLK : Group.IsSolvable (π.comp L.subtype).ker) {z s : Y} (hsL : s ∈ L)
    (hzc : ∀ g ∈ L, g * z = z * g) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (hsz : s ≠ z) : False := by
  have hJ := CFSG.Sporadic.J2.isSimpleGroup_J2
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp.out hp2
  set Z := ρ z with hZ
  set S := ρ s with hS
  have hZZ : ∀ v, Z (Z v) = v := fun v => by
    rw [← Module.End.mul_apply, hZ, ← map_mul, ← pow_two, hz2, map_one, Module.End.one_apply]
  have hSS : ∀ v, S (S v) = v := fun v => by
    rw [← Module.End.mul_apply, hS, ← map_mul, ← pow_two, hs2, map_one, Module.End.one_apply]
  have hzs : s * z = z * s := hzc s hsL
  have hZS : ∀ v, Z (S v) = S (Z v) := fun v => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hZ, hS, ← map_mul, ← map_mul, hzs]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
  have hzs1 : z * s ≠ 1 := fun h => hsz ((eq_inv_of_mul_eq_one_right h).trans hzinv)
  have hzs2 : (z * s) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc s z s, hzs, mul_assoc, ← pow_two s, hs2, mul_one,
      ← pow_two, hz2]
  set Up := Z.eigenspace 1 with hUp
  set Um := Z.eigenspace (-1) with hUm
  have memUp : ∀ v, v ∈ Up ↔ Z v = v := fun v => by
    rw [hUp, Module.End.mem_eigenspace_iff, one_smul]
  have memUm : ∀ v, v ∈ Um ↔ Z v = -v := fun v => by
    rw [hUm, Module.End.mem_eigenspace_iff, neg_smul, one_smul]
  have halves : ∀ (F : Module.End (ZMod p) V) (v : V),
      v = (2⁻¹ : ZMod p) • (v + F v) + (2⁻¹ : ZMod p) • (v - F v) := fun F v => by
    rw [← smul_add, add_add_sub_cancel, ← two_smul (ZMod p) v, smul_smul, inv_mul_cancel₀ h2,
      one_smul]
  have hp' : ∀ v, v + Z v ∈ Up := fun v => (memUp _).mpr (by rw [map_add, hZZ, add_comm])
  have hm' : ∀ v, v - Z v ∈ Um := fun v => (memUm _).mpr (by rw [map_sub, hZZ, neg_sub])
  have hdimUp : Module.finrank (ZMod p) Up ≤ 2 := hfix z hz2 hz1
  have hUmle : Um ≤ S.eigenspace 1 ⊔ (ρ (z * s)).eigenspace 1 := by
    intro u hu
    have hu' := (memUm u).mp hu
    rw [halves S u]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hSS, add_comm]
    · rw [Module.End.mem_eigenspace_iff, one_smul, map_mul, Module.End.mul_apply, ← hZ, ← hS,
        map_sub, hSS, map_sub, hZS, hu', map_neg]
      abel
  have hdimUm : Module.finrank (ZMod p) Um ≤ 4 := by
    have h1 := Submodule.finrank_mono hUmle
    have h2' := Submodule.finrank_add_le_finrank_add_finrank (S.eigenspace 1)
      ((ρ (z * s)).eigenspace 1)
    have h3 : Module.finrank (ZMod p) (S.eigenspace 1) ≤ 2 := hfix s hs2 hs1
    have h4 := hfix (z * s) hzs2 hzs1
    omega
  set ρL := ρ.comp L.subtype with hρL
  have hcomm : ∀ g : L, ∀ v, ρL g (Z v) = Z (ρL g v) := fun g v => by
    change ρ g (ρ z v) = ρ z (ρ g v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hzc g g.2]
  have invUp : ∀ g : L, ∀ u ∈ Up, ρL g u ∈ Up := fun g u hu => by
    rw [memUp] at hu ⊢
    rw [← hcomm, hu]
  have invUm : ∀ g : L, ∀ u ∈ Um, ρL g u ∈ Um := fun g u hu => by
    rw [memUm] at hu ⊢
    rw [← hcomm, hu, map_neg]
  have tUp := forall_apply_eq_of_finrank_le_four hJ (π.comp L.subtype) hL hLK ρL Up invUp
    (by omega)
  have tUm := forall_apply_eq_of_finrank_le_four hJ (π.comp L.subtype) hL hLK ρL Um invUm hdimUm
  have htriv : ∀ g : L, (π.comp L.subtype) g = 1 := by
    intro g
    apply hker
    refine LinearMap.ext fun v => ?_
    have e1 : ρ (L.subtype g) (v + Z v) = v + Z v := tUp g _ (hp' v)
    have e2 : ρ (L.subtype g) (v - Z v) = v - Z v := tUm g _ (hm' v)
    rw [Module.End.one_apply, halves Z v, map_add, map_smul, map_smul, e1, e2]
  obtain ⟨y, hy⟩ := exists_ne (1 : NativeSporadic.J2)
  obtain ⟨g, rfl⟩ := hL y
  exact hy (htriv g)

theorem false_of_unique_involution {L J A : Type*} [Group L] [Finite L] [Group J] [Group A]
    [Finite A] (π : L →* J) (hπ : Function.Surjective π) (hQ : IsPGroup 2 π.ker)
    (hA2 : ∀ a : A, a ^ 2 = 1) (hA8 : Nat.card A = 8) (ι : A →* J) (hι : Function.Injective ι)
    {z : L} (huniq : ∀ s : L, s ^ 2 = 1 → s ≠ 1 → s = z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := ι.range.comap π with hP
  set f : P →* J := π.comp P.subtype with hf
  have hrange : f.range = ι.range := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact m.2
    · intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite ι.range := Finite.of_surjective _ ι.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hcard : Nat.card f.range = 8 := by
    rw [hrange, ← hA8]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hsq : ∀ y ∈ ι.range, y ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hA2, map_one]
  have hsq' : ∀ y : f.range, y ^ 2 = 1 := fun y => Subtype.ext (by
    rw [Subgroup.coe_pow, hsq _ (hrange ▸ y.2), Subgroup.coe_one])
  have hP2 : IsPGroup 2 P := by
    intro x
    have hx2 : (x : L) ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hsq _ x.2
    obtain ⟨k, hk⟩ := hQ ⟨_, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((x : L) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [Subgroup.coe_pow, pow_succ', pow_mul, hk', Subgroup.coe_one]
  have hinv : ∀ u : DisconnectedInvolutionGraph.Helpers.Involution P, ((u : P) : L) = z := by
    intro u
    have hu : orderOf ((u : P) : L) = 2 := by rw [Subgroup.orderOf_coe]; exact u.2
    apply huniq
    · have h := pow_orderOf_eq_one ((u : P) : L)
      rwa [hu] at h
    · intro h
      rw [h, orderOf_one] at hu
      exact absurd hu (by norm_num)
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions P :=
    fun u v _ => Subtype.ext (Subtype.ext ((hinv u).trans (hinv v).symm))
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hP2 hrank with
    hcyc | ⟨n, -, ⟨e⟩⟩
  · have : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hexp := IsCyclic.exponent_eq_card (α := f.range)
    have hdvd : Monoid.exponent f.range ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq'
    rw [hexp, hcard] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  · set h : QuaternionGroup (2 ^ n) →* f.range := f.rangeRestrict.comp e.toMonoidHom with hh
    have hhs : Function.Surjective h := f.rangeRestrict_surjective.comp e.surjective
    set α := h (QuaternionGroup.a 1) with hα
    set β := h (QuaternionGroup.xa 0) with hβ
    have hαpow : ∀ k : ℕ, α ^ k = 1 ∨ α ^ k = α := by
      intro k
      rw [pow_eq_pow_mod k (hsq' α)]
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · left
        rw [h0, pow_zero]
      · right
        rw [h1, pow_one]
    have ha : ∀ i, h (QuaternionGroup.a i) = α ^ i.val := by
      intro i
      rw [hα, ← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    have hmem : ∀ q, h q ∈ ({1, α, β, β * α} : Finset f.range) := by
      intro q
      cases q with
      | a i =>
        rw [ha]
        rcases hαpow i.val with h0 | h1
        · rw [h0]
          simp
        · rw [h1]
          simp
      | xa i =>
        have hq : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
          rw [QuaternionGroup.xa_mul_a, zero_add]
        rw [hq, map_mul, ← hβ, ha]
        rcases hαpow i.val with h0 | h1
        · rw [h0, mul_one]
          simp
        · rw [h1]
          simp
    have : Fintype f.range := Fintype.ofFinite _
    have hle : Nat.card f.range ≤ 4 := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      have hsub : (Finset.univ : Finset f.range) ⊆ {1, α, β, β * α} := fun y _ => by
        obtain ⟨q, rfl⟩ := hhs y
        exact hmem q
      exact (Finset.card_le_card hsub).trans Finset.card_le_four
    omega

end CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
