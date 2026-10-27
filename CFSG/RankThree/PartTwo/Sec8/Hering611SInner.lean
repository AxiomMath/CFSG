module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SMax
public import CFSG.RankThree.PartTwo.Sec8.Hering611Lift
public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.KFacts.K71Lift

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

theorem conj_injective_of_center_eq_bot' {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun γ : MulAut K => γ z) hg
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa [MulAut.conj_apply] using this)).symm
  rwa [hZ, Subgroup.mem_bot] at this

theorem qL_injective_on_inf {A L : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A) {a b : L}
    (ha : (a : G) ∈ A) (hb : (b : G) ∈ A) (hab : qL L a = qL L b) : a = b := by
  have h1 : a⁻¹ * b ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hab
  have hc : ((a⁻¹ * b : L) : G) ∈ A := A.mul_mem (A.inv_mem ha) hb
  have hθ : ((a⁻¹ * b : L) : G) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨a⁻¹ * b, h1, rfl⟩
  have h3 : ((a⁻¹ * b : L) : G) = 1 :=
    Sec11.eq_one_of_mem_inSubgroup_theta hθ (hAe.2 _ hc)
  exact inv_mul_eq_one.mp (Subtype.ext h3)

theorem conj_qL_mem_autThetaQuot {A L : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {a : L} (ha : (a : G) ∈ A) :
    (MulAut.conj (qL L a) : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈ autThetaQuot A L :=
  mem_autThetaQuot_iff.mpr
    ⟨(a : G), hAN ha, ha, KFacts.thetaQuotMulAut_compAction_of_mem a.2 (hAN ha)⟩

theorem exists_mem_inf_of_conj_mem {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {x : L ⧸ aschbacherSolvableCore 3 L}
    (hx : (MulAut.conj x : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈ autThetaQuot A L) :
    ∃ a : L, (a : G) ∈ A ∧ qL L a = x := by
  have hinj := conj_injective_of_center_eq_bot' hZ
  obtain ⟨g, hgN, hgA, hg⟩ := mem_autThetaQuot_iff.mp hx
  have hgg : actHom L ⟨g, hgN⟩ = MulAut.conj x := hg
  have hfix : ∀ b (hb : b ∈ A), actHom L ⟨b, hAN hb⟩ x = x := by
    intro b hb
    have hgb : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) * (⟨b, hAN hb⟩ :
        Subgroup.normalizer (L : Set G)) = (⟨b, hAN hb⟩ : Subgroup.normalizer (L : Set G)) *
          ⟨g, hgN⟩ := by
      apply Subtype.ext
      have hcm := congrArg Subtype.val (hAe.1.is_comm.comm ⟨g, hgA⟩ ⟨b, hb⟩)
      exact hcm
    have hc : MulAut.conj x * actHom L ⟨b, hAN hb⟩ =
        actHom L ⟨b, hAN hb⟩ * MulAut.conj x := by
      rw [← hgg, ← map_mul, ← map_mul, hgb]
    apply hinj
    change MulAut.conj (actHom L ⟨b, hAN hb⟩ x) = MulAut.conj x
    rw [← KFacts.mul_mulAutConj_mul_inv, ← hc, mul_inv_cancel_right]
  have hg3 : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (hAe.2 g hgA)
  have hx3 : x ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← hgg, ← map_pow, hg3, map_one]
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective x
  have hqx₀ : qL L x₀ = x := hx₀
  have hcomm : ∀ a : G, ∀ ha : a ∈ A,
      a * (x₀ : G) * a⁻¹ * (x₀ : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro a ha
    have hql : qL L (compAction L ⟨a, hAN ha⟩ x₀ * x₀⁻¹) = 1 := by
      rw [map_mul, map_inv, ← actHom_qL, hqx₀, hfix a ha, mul_inv_cancel]
    have hl : compAction L ⟨a, hAN ha⟩ x₀ * x₀⁻¹ ∈ aschbacherSolvableCore 3 L :=
      (QuotientGroup.eq_one_iff _).mp hql
    exact ⟨_, hl, by simp [coe_compAction]⟩
  have hx3' : (x₀ : G) ^ 3 ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h1 : qL L (x₀ ^ 3) = 1 := by rw [map_pow, hqx₀, hx3]
    exact ⟨x₀ ^ 3, (QuotientGroup.eq_one_iff _).mp h1, by simp⟩
  have hNX : inSubgroup (aschbacherSolvableCore 3) L ≤ L := Subgroup.map_subtype_le _
  obtain ⟨y, hyA, hyL, hy⟩ := exists_mem_of_fixed_coset hAe hAmax hNX
    (Sec6.le_normalizer_theta L) (fun a ha => Sec6.normalizer_le_normalizer_theta L (hAN ha))
    (Sec11.not_three_dvd_card_inSubgroup_theta L) x₀.2 hx3' hcomm
  refine ⟨⟨y, hyL⟩, hyA, ?_⟩
  obtain ⟨w, hw, hwe⟩ := hy
  have hwy : w = (⟨y, hyL⟩ : L)⁻¹ * x₀ := Subtype.ext (by simpa using hwe)
  have hmem : (⟨y, hyL⟩ : L)⁻¹ * x₀ ∈ aschbacherSolvableCore 3 L := by
    rw [← hwy]
    exact hw
  rw [← hqx₀]
  exact QuotientGroup.eq.mpr hmem

theorem card_inf_L_of {A L : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {n : ℕ}
    (hn : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = n) :
    Nat.card ↥(A ⊓ L) = n := by
  have hinj := conj_injective_of_center_eq_bot' hZ
  set ιc : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    MulAut.conj with hιc
  set X : Subgroup (L ⧸ aschbacherSolvableCore 3 L) :=
    (autThetaQuot A L ⊓ ιc.range).comap ιc with hX
  have hmap : X.map ιc = autThetaQuot A L ⊓ ιc.range :=
    Subgroup.map_comap_eq_self inf_le_right
  have hXcard : Nat.card X = n := by
    rw [← hn, ← hmap, Subgroup.card_map_of_injective hinj]
  let φ : ↥(A ⊓ L) →* (L ⧸ aschbacherSolvableCore 3 L) :=
    (qL L).comp (Subgroup.inclusion (inf_le_right : A ⊓ L ≤ L))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨t, ht⟩ h1
    obtain ⟨htA, htL⟩ := Subgroup.mem_inf.mp ht
    have h2 : qL L ⟨t, htL⟩ = qL L 1 := by
      rw [map_one]
      exact h1
    have h3 : (⟨t, htL⟩ : L) = 1 :=
      qL_injective_on_inf hAe (a := ⟨t, htL⟩) (b := 1) htA A.one_mem h2
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext h4
  have hrange : φ.range = X := by
    ext x
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨htA, htL⟩ := Subgroup.mem_inf.mp ht
      rw [hX, Subgroup.mem_comap, Subgroup.mem_inf]
      exact ⟨conj_qL_mem_autThetaQuot (a := ⟨t, htL⟩) hAN htA, ⟨_, rfl⟩⟩
    · intro hx
      rw [hX, Subgroup.mem_comap, Subgroup.mem_inf] at hx
      obtain ⟨a, haA, hax⟩ := exists_mem_inf_of_conj_mem hAe hAmax hAN hZ (x := x) hx.1
      exact ⟨⟨a, Subgroup.mem_inf.mpr ⟨haA, a.2⟩⟩, hax⟩
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hrange, hXcard]

end CFSG.RankThree.PartTwo.Sec8.Hering611
