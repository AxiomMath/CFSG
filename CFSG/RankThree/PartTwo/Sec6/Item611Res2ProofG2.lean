module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res2Proof
import CFSG.RankThree.PartTwo.Sec6.Item64
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def KS611G2Cent : Prop :=
  ∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
    ∀ x : X, x ≠ 1 → x ^ 3 = 1 → ∀ V : Subgroup X, CFSG.Assembly.IsElemAbelian 2 V →
      (∀ v ∈ V, x * v = v * x) → Nat.card V ≤ 2

namespace Res611G2

variable {G : Type} [Group G] [Finite G]

theorem mk_conj_eq_of_mem_thetaQuotCentralizer {L : Subgroup G} {g : G}
    (hg : g ∈ thetaQuotCentralizer L) (y : L) (hgy : g * (y : G) * g⁻¹ ∈ L) :
    ((⟨g * (y : G) * g⁻¹, hgy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((y : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨x, hx, rfl⟩ := hg
  have hx' : (thetaQuotMulAut L) (L.normalizerMonoidHom x) = 1 := MonoidHom.mem_ker.mp hx
  have e1 : (⟨(Subgroup.normalizer (L : Set G)).subtype x * (y : G) *
      ((Subgroup.normalizer (L : Set G)).subtype x)⁻¹, hgy⟩ : L) = L.normalizerMonoidHom x y :=
    Subtype.ext rfl
  rw [e1, ← thetaQuotMulAut_mk, hx', MulAut.one_apply]

end Res611G2

open Res611G2

theorem item611NotG2T_of (hK : KS611G2Cent) : Item611NotG2T := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE _ T hT hTL hTθ hdec hcL hG2
  have hEA : E ≤ A := hE.2
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.1.2
  have hCE9 := card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hE.1) hT
  obtain ⟨e, heCE, hec⟩ : ∃ e ∈ E ⊓ Subgroup.centralizer (T : Set G), e ∉ Subgroup.zpowers c := by
    by_contra hall
    push Not at hall
    have hle : E ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.zpowers c := fun x hx => hall x hx
    have h1 := Subgroup.card_le_of_le hle
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
    rw [Nat.card_zpowers, hc3, hCE9] at h1
    omega
  have heA : e ∈ A := hEA heCE.1
  have heT : ∀ t ∈ T, e * t = t * e := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp heCE.2 t ht).symm
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have h1 : c * y * c⁻¹ = y := by rw [hAcomm c hcA y hy.1, mul_inv_cancel_right]
      rw [h1]
      exact hy
    · have h1 : c * y * c⁻¹ ∈ A := hy.1
      have hyA : y ∈ A := by
        have := A.mul_mem (A.mul_mem (A.inv_mem hcA) h1) hcA
        simpa [mul_assoc] using this
      have h2 : c * y * c⁻¹ = y := by rw [hAcomm c hcA y hyA, mul_inv_cancel_right]
      rw [← h2]
      exact hy
  have heS : e ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hdec ▸ heA
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at heS
  obtain ⟨x, ⟨k, rfl⟩, l, ⟨hlA, hlL⟩, hel⟩ := heS
  have hlc : l ∉ Subgroup.zpowers c := by
    intro hl
    apply hec
    have hel' : c ^ k * l = e := hel
    rw [← hel']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers c k) hl
  have hl1 : l ≠ 1 := fun h => hlc (h ▸ Subgroup.one_mem _)
  have hcθ : c ∈ thetaQuotCentralizer L := by
    have : c ∈ A ⊓ thetaQuotCentralizer L := hCA ▸ Subgroup.mem_zpowers c
    exact this.2
  have hckθ : c ^ k ∈ thetaQuotCentralizer L := Subgroup.zpow_mem _ hcθ k
  have hcNL : ∀ (g : G), g ∈ thetaQuotCentralizer L → ∀ y ∈ L, g * y * g⁻¹ ∈ L := by
    rintro g ⟨x, -, rfl⟩ y hy
    exact (Subgroup.mem_normalizer_iff.mp x.2 y).mp hy
  set π : L →* L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
    with hπ
  set lb : L ⧸ aschbacherSolvableCore 3 L := π ⟨l, hlL⟩ with hlb
  have hlb3 : lb ^ 3 = 1 := by
    rw [hlb, ← map_pow]
    have : (⟨l, hlL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA3 l hlA]; rfl)
    rw [this, map_one]
  have hlb1 : lb ≠ 1 := by
    intro h
    have hmem : (⟨l, hlL⟩ : L) ∈ aschbacherSolvableCore 3 L := by
      rw [hlb, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨⟨l, hlL⟩, hmem⟩ : aschbacherSolvableCore 3 L) = 3 :=
      orderOf_eq_prime (Subtype.ext (Subtype.ext (by
        simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hA3 l hlA)))
        (fun h1 => hl1 (congrArg (fun z : aschbacherSolvableCore 3 L => ((z : L) : G)) h1))
    have h3 := orderOf_dvd_natCard (⟨⟨l, hlL⟩, hmem⟩ : aschbacherSolvableCore 3 L)
    rw [hord] at h3
    exact three_not_dvd_card_aschbacherSolvableCore h3
  obtain ⟨hTN, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  set V : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := (T.subgroupOf L).map π with hV
  have hinj : Set.InjOn π (T.subgroupOf L : Set L) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq]
      exact hxy
    have h2 : ((x⁻¹ * y : L) : G) ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨(T.subgroupOf L).mul_mem ((T.subgroupOf L).inv_mem hx) hy, ⟨_, h1, rfl⟩⟩
    rw [hTθ, Subgroup.mem_bot] at h2
    have h3 : x⁻¹ * y = 1 := Subtype.ext h2
    exact (inv_mul_eq_one.mp h3)
  have hV4 : Nat.card V = 4 := by
    have h1 : Nat.card V = Nat.card (T.subgroupOf L) := by
      change Nat.card ((V : Set (L ⧸ aschbacherSolvableCore 3 L))) =
        Nat.card ((T.subgroupOf L : Set L))
      rw [hV, Subgroup.coe_map]
      exact Nat.card_image_of_injOn hinj
    rw [h1, ← hT4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hVab : CFSG.Assembly.IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x', hx', rfl⟩ := x
      obtain ⟨_, y', hy', rfl⟩ := y
      have hT' := hTab.1.is_comm.comm (⟨x', hx'⟩ : T) ⟨y', hy'⟩
      have hxy : x' * y' = y' * x' := Subtype.ext (by
        have := congrArg (fun z : T => (z : G)) hT'
        simpa using this)
      apply Subtype.ext
      change π x' * π y' = π y' * π x'
      rw [← map_mul, ← map_mul, hxy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hTab.2 _ hx)
      rw [this, map_one]
  have hVcomm : ∀ v ∈ V, lb * v = v * lb := by
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := ht
    have hel' : c ^ k * l = e := hel
    have h1 : c ^ k * l * t = t * (c ^ k * l) := by rw [hel']; exact heT t htT
    have h2 : l * (t : G) * l⁻¹ = (c ^ k)⁻¹ * t * ((c ^ k)⁻¹)⁻¹ := by
      calc l * (t : G) * l⁻¹ = (c ^ k)⁻¹ * (c ^ k * l * t) * l⁻¹ := by group
        _ = (c ^ k)⁻¹ * (t * (c ^ k * l)) * l⁻¹ := by rw [h1]
        _ = (c ^ k)⁻¹ * t * ((c ^ k)⁻¹)⁻¹ := by group
    have hconjL : (c ^ k)⁻¹ * (t : G) * ((c ^ k)⁻¹)⁻¹ ∈ L :=
      hcNL _ (Subgroup.inv_mem _ hckθ) t t.2
    have h3 := mk_conj_eq_of_mem_thetaQuotCentralizer (Subgroup.inv_mem _ hckθ) t hconjL
    have h4 : (⟨l, hlL⟩ : L) * t * (⟨l, hlL⟩ : L)⁻¹ =
        ⟨(c ^ k)⁻¹ * (t : G) * ((c ^ k)⁻¹)⁻¹, hconjL⟩ := Subtype.ext h2
    have h5 : π ((⟨l, hlL⟩ : L) * t * (⟨l, hlL⟩ : L)⁻¹) = π t := by
      rw [h4]
      exact h3
    rw [map_mul, map_mul, map_inv] at h5
    rw [hlb]
    calc π ⟨l, hlL⟩ * π t = π ⟨l, hlL⟩ * π t * (π ⟨l, hlL⟩)⁻¹ * π ⟨l, hlL⟩ := by group
      _ = π t * π ⟨l, hlL⟩ := by rw [h5]
  have h := hK _ hG2 lb hlb1 hlb3 V hVab hVcomm
  omega

end CFSG.RankThree.PartTwo.Sec6
