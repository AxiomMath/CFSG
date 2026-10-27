module

public import CFSG.RankThree.GF2n.Tim79aSec22Ti
public import CFSG.RankThree.GF2n.Tim79aSec23Defs
public import CFSG.RankThree.GF2n.Tim79aSec2Root

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

@[expose] def Vtilde (V H : Subgroup G) :
    Subgroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) :=
  (Vy V H).map (QuotientGroup.mk' (Subgroup.center (Xbar V H)))

@[expose] def NoCentralTwist (V H : Subgroup G) : Prop :=
  ∀ z ∈ Subgroup.center (Xbar V H), ∀ d ∈ Dy V H, d * z ∈ Dy V H → z = 1

theorem conj_mem_Dy (hd : Sec23Data V H) {a : Xbar V H} (ha : a ∈ Dy V H) (g : Xbar V H) :
    g * a * g⁻¹ ∈ Dy V H := by
  obtain ⟨d₀, hd₀⟩ := hd.isClass
  rw [hd₀] at ha ⊢
  exact ha.trans (isConj_iff.mpr ⟨g, rfl⟩)

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem isTI_Vy : IsTI (Vy V H) := by
  intro g
  by_cases hbot : Vy V H ⊓ conjSubgroup g (Vy V H) = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨hyV, hyC⟩ := Subgroup.mem_inf.mp hy
  rw [mem_conjSubgroup, Vy, Subgroup.mem_subgroupOf] at hyC
  rw [Vy, Subgroup.mem_subgroupOf] at hyV
  have hy1' : (y : Hbar V H) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hmem : ∀ u : Xbar V H, ((g⁻¹ * u * g : Xbar V H) : Hbar V H) =
      (g : Hbar V H)⁻¹ * (u : Hbar V H) * (g : Hbar V H) := fun u => by simp
  rcases hc.isTI_barOf_V (g : Hbar V H) with h | h
  · exfalso
    apply hy1'
    have : (y : Hbar V H) ∈ barOf V H V ⊓ conjSubgroup (g : Hbar V H) (barOf V H V) := by
      refine Subgroup.mem_inf.mpr ⟨hyV, ?_⟩
      rw [mem_conjSubgroup, ← hmem]
      exact hyC
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · refine inf_eq_left.mpr fun u hu => ?_
    rw [mem_conjSubgroup, Vy, Subgroup.mem_subgroupOf, hmem]
    rw [Vy, Subgroup.mem_subgroupOf] at hu
    have hu' : (u : Hbar V H) ∈ barOf V H V ⊓ conjSubgroup (g : Hbar V H) (barOf V H V) := by
      rw [h]
      exact hu
    exact (mem_conjSubgroup.mp (Subgroup.mem_inf.mp hu').2)

theorem isTI_Vtilde_of_noCentralTwist (hd : Sec23Data V H) (hnt : NoCentralTwist V H) :
    IsTI (Vtilde V H) := by
  intro gt
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gt
  by_cases hbot : Vtilde V H ⊓ conjSubgroup (g : Xbar V H ⧸ Subgroup.center (Xbar V H))
      (Vtilde V H) = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, haV, rfl⟩ := Subgroup.mem_map.mp hxV
  rw [mem_conjSubgroup] at hxC
  obtain ⟨c, hcV, hcg⟩ := Subgroup.mem_map.mp hxC
  have ha1 : a ≠ 1 := fun h => hx1 (Subtype.ext (by simp [h]))
  have haD : a ∈ Dy V H := by
    rw [Vy, Subgroup.mem_subgroupOf] at haV
    exact hc.barOf_V_subset_dbarOf haV (fun h => ha1 (Subtype.ext h))
  have hz : c⁻¹ * (g⁻¹ * a * g) ∈ Subgroup.center (Xbar V H) := by
    refine QuotientGroup.eq.mp ?_
    simpa using hcg
  have hcg' : g⁻¹ * a * g ∈ Dy V H := by
    simpa using conj_mem_Dy hd haD g⁻¹
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hd.noncentral a haD
    rw [inv_one, one_mul] at hz
    have hzc := Subgroup.mem_center_iff.mp hz g
    have h2 : a = g⁻¹ * a * g := by
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = (g⁻¹ * a * g) * g * g⁻¹ := by rw [hzc]
        _ = g⁻¹ * a * g := by group
    rw [h2]
    exact hz
  have hcD : c ∈ Dy V H := by
    rw [Vy, Subgroup.mem_subgroupOf] at hcV
    exact hc.barOf_V_subset_dbarOf hcV (fun h => hc1 (Subtype.ext h))
  have hzt := hnt _ hz c hcD (by rwa [mul_inv_cancel_left])
  have hgc : g⁻¹ * a * g = c := by
    have : c⁻¹ * (g⁻¹ * a * g) = 1 := hzt
    exact (inv_mul_eq_one.mp this).symm
  have hinf : Vy V H ⊓ conjSubgroup g (Vy V H) ≠ ⊥ := by
    intro h
    have : a ∈ Vy V H ⊓ conjSubgroup g (Vy V H) :=
      Subgroup.mem_inf.mpr ⟨haV, by rw [mem_conjSubgroup, hgc]; exact hcV⟩
    rw [h, Subgroup.mem_bot] at this
    exact ha1 this
  have hle : Vy V H ≤ conjSubgroup g (Vy V H) := by
    rcases hc.isTI_Vy g with h | h
    · exact absurd h hinf
    · intro u hu
      have : u ∈ Vy V H ⊓ conjSubgroup g (Vy V H) := by
        rw [h]
        exact hu
      exact (Subgroup.mem_inf.mp this).2
  refine inf_eq_left.mpr fun t ht => ?_
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ht
  rw [mem_conjSubgroup]
  have := mem_conjSubgroup.mp (hle hb)
  exact ⟨g⁻¹ * b * g, this, by simp⟩

end MinCex

theorem eq_one_of_mul_central_mem {X : Type*} [Group X] [Finite X] {D : Set X}
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet D)
    (hconj : ∀ a ∈ D, ∀ g : X, g * a * g⁻¹ ∈ D)
    {d z : X} (hd : d ∈ D) (hdO : d ∉ CFSG.pCore 2 X) (hz : z ∈ Subgroup.center X)
    (hdz : d * z ∈ D) : z = 1 := by
  by_contra hz1
  have inv2 : ∀ a ∈ D, a * a = 1 := fun a ha => by
    rw [← sq, ← hroot.1 a ha]; exact pow_orderOf_eq_one a
  have hd2 := inv2 d hd
  have hcomm : ∀ y : X, Commute z y := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  have hz2 : z * z = 1 := by
    calc z * z = (d * d) * (z * z) := by rw [hd2, one_mul]
      _ = (d * z) * (d * z) := ((hcomm d).mul_mul_mul_comm d z).symm
      _ = 1 := inv2 _ hdz
  have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  obtain ⟨g, hg⟩ : ∃ g : X, ¬ IsPGroup 2 (Subgroup.closure ({d, g * d * g⁻¹} : Set X)) := by
    by_contra h
    push_neg at h
    exact hdO ((BaerSuzuki.baer_suzuki_iff d).mpr h)
  set e := g * d * g⁻¹
  have he : e ∈ D := hconj d hd g
  have he2 := inv2 e he
  have not2 : ∀ n : ℕ, (d * e) ^ 2 ^ n ≠ 1 := fun n h =>
    hg (RankThree.GF2n.Tim78.isPGroup_closure_pair_involutions hd2 he2 h)
  rcases hroot.2.1 d hd e he with h2 | h4 | hodd
  · exact not2 1 (by rw [pow_one, ← h2]; exact pow_orderOf_eq_one _)
  · exact not2 2 (by rw [show (2:ℕ) ^ 2 = 4 by norm_num, ← h4]; exact pow_orderOf_eq_one _)
  · have hco : (orderOf z).Coprime (orderOf (d * e)) := by
      rw [hoz]; exact Nat.coprime_two_left.mpr hodd
    have hord : orderOf (d * z * e) = 2 * orderOf (d * e) := by
      have : d * z * e = z * (d * e) := by rw [← (hcomm d).eq, mul_assoc]
      rw [this, (hcomm _).orderOf_mul_eq_mul_orderOf_of_coprime hco, hoz]
    rcases hroot.2.1 (d * z) hdz e he with h | h | h
    · rw [hord] at h
      have : orderOf (d * e) = 1 := by omega
      exact not2 0 (by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp this)
    · rw [hord] at h
      have : orderOf (d * e) = 2 := by omega
      rw [this] at hodd; exact absurd hodd (by decide)
    · rw [hord] at h
      exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) h

theorem noCentralTwist (hd : Sec23Data V H) : NoCentralTwist V H := by
  intro z hz d hdD hdz
  refine eq_one_of_mul_central_mem hd.root (fun a ha g => conj_mem_Dy hd ha g) hdD ?_ hz hdz
  intro hdO
  apply hd.noncentral d hdD
  have hP : IsPGroup 2 (CFSG.pCore 2 (Xbar V H)) := BaerSuzuki.Helpers.pCore_isPGroup 2
  haveI := BaerSuzuki.Helpers.pCore_normal (G := Xbar V H) 2
  haveI : Group.IsNilpotent (CFSG.pCore 2 (Xbar V H)) := hP.isNilpotent
  exact hd.solv _ inferInstance inferInstance hdO

namespace MinCex

theorem isTI_Vtilde (hc : MinCex M V Q P H) (hd : Sec23Data V H) : IsTI (Vtilde V H) :=
  hc.isTI_Vtilde_of_noCentralTwist hd (noCentralTwist hd)

end MinCex

end CFSG.RankThree.GF2n.Tim79a
