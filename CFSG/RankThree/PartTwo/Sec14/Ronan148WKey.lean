module

public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec14.Ronan148WLift
import CFSG.RankThree.PartTwo.Sec14.Ronan148DInvObs
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofJ2
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

section Theta

variable (L : Subgroup G)

theorem theta_subgroupOf_normal :
    ((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G))).Normal := by
  refine ⟨fun t ht n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ht ⊢
  have h := Sec12.conj_mem_inSubgroup_theta n.2 ht
  simpa using h

theorem coprime_card_theta_subgroupOf :
    Nat.Coprime 3 (Nat.card ((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G)))) := by
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hle : inSubgroup (aschbacherSolvableCore 3) L ≤ Subgroup.normalizer (L : Set G) := by
    rintro _ ⟨t, -, rfl⟩
    exact Subgroup.le_normalizer t.2
  have hcard : Nat.card ((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G))) = Nat.card (aschbacherSolvableCore 3 ↥L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, inSubgroup,
      Subgroup.card_map_of_injective L.subtype_injective]
  rw [hcard]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3

end Theta

section Inner


theorem exists_inner_mod_theta {L : Subgroup G}
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ u ∈ L, (∀ l ∈ L, (x * l * x⁻¹)⁻¹ * (u * l * u⁻¹) ∈
        inSubgroup (aschbacherSolvableCore 3) L) ∧
      u ^ 3 ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hZ : Subgroup.center (↥L ⧸ θ) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  set N := Subgroup.normalizer (L : Set G)
  let ψ : ↥N →* MulAut (↥L ⧸ θ) := (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom
  have hψ : ∀ (n : ↥N) (l : ↥L), ψ n (QuotientGroup.mk' θ l) =
      QuotientGroup.mk' θ (L.normalizerMonoidHom n l) := fun _ _ => rfl
  have hσ3 : (ψ ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  obtain ⟨ub, hub⟩ := MonoidHom.mem_range.mp
    (KFacts.ks17J2AutThree_of_outer Res2Proof.nonempty_outer_j2 (↥L ⧸ θ) ⟨φ⟩ _ hσ3)
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective θ ub
  refine ⟨u0, u0.2, fun l hl => ?_, ?_⟩
  · have hm : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
    have h1 := congrArg (fun τ : MulAut (↥L ⧸ θ) => τ (QuotientGroup.mk' θ ⟨l, hl⟩)) hub
    simp only [MulAut.conj_apply] at h1
    rw [hψ] at h1
    have e : (L.normalizerMonoidHom ⟨x, hxN⟩ ⟨l, hl⟩ : ↥L) = ⟨x * l * x⁻¹, hm⟩ := rfl
    rw [e] at h1
    have h2 : (⟨x * l * x⁻¹, hm⟩ : ↥L)⁻¹ * (u0 * ⟨l, hl⟩ * u0⁻¹) ∈ θ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h3 : (QuotientGroup.mk (u0 * ⟨l, hl⟩ * u0⁻¹) : ↥L ⧸ θ) =
          QuotientGroup.mk' θ ⟨x * l * x⁻¹, hm⟩ := by
        rw [← h1]
        rfl
      rw [h3]
      exact inv_mul_cancel _
    exact ⟨_, h2, rfl⟩
  · have hu3 : (QuotientGroup.mk' θ u0) ^ 3 = 1 := by
      have h1 : MulAut.conj ((QuotientGroup.mk' θ u0) ^ 3) = MulAut.conj (1 : ↥L ⧸ θ) := by
        rw [map_pow, map_one, hub, hσ3]
      exact Ronan148D.eq_of_conj_eq_of_center_eq_bot hZ h1
    have h1 : u0 ^ 3 ∈ θ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hu3
    exact ⟨u0 ^ 3, h1, by simp⟩

end Inner

section Quot

variable {L : Subgroup G}

theorem mk_eq_mk_of_mem_theta [((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G))).Normal]
    {g h : ↥(Subgroup.normalizer (L : Set G))}
    (hgh : (g : G)⁻¹ * h ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    (QuotientGroup.mk' ((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G))) g) = QuotientGroup.mk' _ h := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hgh)

theorem mk_comm_of_mem_theta [((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
      (Subgroup.normalizer (L : Set G))).Normal]
    {g h : ↥(Subgroup.normalizer (L : Set G))}
    (hgh : ((g : G) * h * (g : G)⁻¹)⁻¹ * h ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    QuotientGroup.mk' ((inSubgroup (aschbacherSolvableCore 3) L).subgroupOf
        (Subgroup.normalizer (L : Set G))) g * QuotientGroup.mk' _ h =
      QuotientGroup.mk' _ h * QuotientGroup.mk' _ g := by
  have h1 := mk_eq_mk_of_mem_theta (g := g * h * g⁻¹) (h := h) (by simpa using hgh)
  rw [map_mul, map_mul, map_inv] at h1
  calc QuotientGroup.mk' _ g * QuotientGroup.mk' _ h
      = (QuotientGroup.mk' _ g * QuotientGroup.mk' _ h * (QuotientGroup.mk' _ g)⁻¹) *
          QuotientGroup.mk' _ g := by group
    _ = QuotientGroup.mk' _ h * QuotientGroup.mk' _ g := by rw [h1]

end Quot

section Main


theorem mem_sup_of_inner_mod_theta {A L : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {c : G} (hcA : c ∈ A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hxc : x * c = c * x) (hx3 : x ^ 3 = 1)
    {u : G} (huL : u ∈ L)
    (hu : ∀ l ∈ L, (x * l * x⁻¹)⁻¹ * (u * l * u⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L)
    (hu3 : u ^ 3 ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    x ∈ L ⊔ A := by
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθLdef
  have hθLL : θL ≤ L := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hLN : L ≤ N := Subgroup.le_normalizer
  haveI hTn : (θL.subgroupOf N).Normal := theta_subgroupOf_normal L
  set T := θL.subgroupOf N with hTdef
  set ρ : ↥N →* ↥N ⧸ T := QuotientGroup.mk' T with hρ
  have huN : u ∈ N := hLN huL
  set xN : ↥N := ⟨x, hxN⟩ with hxNdef
  set uN : ↥N := ⟨u, huN⟩ with huNdef
  set qN : ↥N := uN⁻¹ * xN with hqNdef
  have hθN : ∀ n ∈ N, ∀ t ∈ θL, n * t * n⁻¹ ∈ θL := fun n hn t ht =>
    Sec12.conj_mem_inSubgroup_theta hn ht
  have hxu : ρ xN * ρ uN = ρ uN * ρ xN := by
    have h1 := hu u huL
    rw [show u * u * u⁻¹ = u by group] at h1
    exact mk_comm_of_mem_theta h1
  have hqL : ∀ (l : G) (hl : l ∈ L), ρ qN * ρ ⟨l, hLN hl⟩ = ρ ⟨l, hLN hl⟩ * ρ qN := by
    intro l hl
    refine mk_comm_of_mem_theta ?_
    have h1 := hu l hl
    have h2 : u⁻¹ * ((x * l * x⁻¹)⁻¹ * (u * l * u⁻¹)) * u⁻¹⁻¹ ∈ θL :=
      hθN _ (N.inv_mem huN) _ h1
    have e : ((qN : G) * l * (qN : G)⁻¹)⁻¹ * l =
        u⁻¹ * ((x * l * x⁻¹)⁻¹ * (u * l * u⁻¹)) * u⁻¹⁻¹ := by
      simp only [hqNdef, hxNdef, huNdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h2
  have hqc : ρ qN * ρ ⟨c, hAN hcA⟩ = ρ ⟨c, hAN hcA⟩ * ρ qN := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have huc : u * c = c * u := Subgroup.mem_centralizer_singleton_iff.mp (hLc huL)
    have huc' : u⁻¹ * c = c * u⁻¹ := by
      calc u⁻¹ * c = u⁻¹ * (c * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * c) * u⁻¹ := by rw [huc]
        _ = c * u⁻¹ := by group
    show u⁻¹ * x * c = c * (u⁻¹ * x)
    calc u⁻¹ * x * c = u⁻¹ * (x * c) := by group
      _ = u⁻¹ * (c * x) := by rw [hxc]
      _ = (u⁻¹ * c) * x := by group
      _ = (c * u⁻¹) * x := by rw [huc']
      _ = c * (u⁻¹ * x) := by group
  have hqA : ∀ g ∈ (A.subgroupOf N).map ρ, g * ρ qN = ρ qN * g := by
    have hle : (A.subgroupOf N).map ρ ≤ Subgroup.centralizer ({ρ qN} : Set (↥N ⧸ T)) := by
      have hAsub : A.subgroupOf N =
          (Subgroup.zpowers c).subgroupOf N ⊔ (A ⊓ L).subgroupOf N := by
        conv_lhs => rw [hAeq]
        exact Subgroup.subgroupOf_sup ((Subgroup.zpowers_le.mpr hcA).trans hAN)
          (inf_le_left.trans hAN)
      rw [hAsub, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hgk : g = (⟨c, hAN hcA⟩ : ↥N) ^ k := Subtype.ext (by simpa using hk.symm)
        rw [hgk, map_zpow]
        exact (Commute.zpow_right hqc k).eq.symm
      · rintro _ ⟨g, hg, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hqL (g : G) hg.2).symm
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hq3 : ρ qN ^ 3 = 1 := by
    have hu3' : ρ uN ^ 3 = 1 := by
      have h1 : ρ (uN ^ 3) = ρ 1 := mk_eq_mk_of_mem_theta (by
        show ((uN ^ 3 : ↥N) : G)⁻¹ * ((1 : ↥N) : G) ∈ θL
        rw [Subgroup.coe_pow, Subgroup.coe_one, mul_one]
        exact θL.inv_mem hu3)
      calc ρ uN ^ 3 = ρ (uN ^ 3) := (map_pow ρ uN 3).symm
        _ = ρ 1 := h1
        _ = 1 := map_one ρ
    have hx3' : ρ xN ^ 3 = 1 := by
      have : xN ^ 3 = 1 := Subtype.ext (by simpa [hxNdef] using hx3)
      calc ρ xN ^ 3 = ρ (xN ^ 3) := (map_pow ρ xN 3).symm
        _ = ρ 1 := by rw [this]
        _ = 1 := map_one ρ
    have hc : Commute (ρ uN)⁻¹ (ρ xN) := Commute.inv_left hxu.symm
    have hq : ρ qN = (ρ uN)⁻¹ * ρ xN := by
      rw [hqNdef, map_mul, map_inv]
    calc ρ qN ^ 3 = ((ρ uN)⁻¹ * ρ xN) ^ 3 := by rw [hq]
      _ = (ρ uN)⁻¹ ^ 3 * ρ xN ^ 3 := hc.mul_pow 3
      _ = 1 := by rw [inv_pow, hu3', hx3', inv_one, one_mul]
  obtain ⟨gN, hgA, hgq⟩ := mem_map_of_commute_of_coprime A hAF hAN T
    (coprime_card_theta_subgroupOf L) hqA hq3
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hgA
  have hxeq' : ρ (uN * gN) = ρ xN := by
    rw [map_mul, hgq, hqNdef, map_mul, map_inv, mul_inv_cancel_left]
  rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxeq'
  have ht : (((uN * gN)⁻¹ * xN : ↥N) : G) ∈ θL := Subgroup.mem_subgroupOf.mp hxeq'
  have hxdec : x = u * (gN : G) * (((uN * gN)⁻¹ * xN : ↥N) : G) := by
    simp only [huNdef, hxNdef, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxdec]
  exact (L ⊔ A).mul_mem ((L ⊔ A).mul_mem (Subgroup.mem_sup_left huL)
    (Subgroup.mem_sup_right hgA)) (Subgroup.mem_sup_left (hθLL ht))

theorem mem_sup_of_pow_three_eq_one {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {x : G} (hx : x ∈ Subgroup.centralizer ({c} : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ L ⊔ A := by
  obtain ⟨φ⟩ := hJ
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.toSec13Data.mem_lA.1
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := h.toSec13Data.mem_lA.2.1
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_of_j2 h ⟨φ⟩ hx
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) := (j2_point_facts h.toSec13Data ⟨φ⟩).2.2
  obtain ⟨u, huL, hu, hu3⟩ := exists_inner_mod_theta φ hxN hx3
  exact mem_sup_of_inner_mod_theta h.mem_partTwoF hAN hcA hLc hAeq hxN
    (Subgroup.mem_centralizer_singleton_iff.mp hx) hx3 huL hu hu3

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
