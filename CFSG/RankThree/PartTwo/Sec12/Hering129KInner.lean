module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KInner

section ElemAb

variable {G : Type} [Group G]

theorem isElemAbelian_sup_zpowers {A : Subgroup G} {y : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hy3 : y ^ 3 = 1) (hyA : ∀ a ∈ A, y * a = a * y) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := fun a ha =>
    mem_normalizer_zpowers_of_commute (hyA a ha).symm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A (Subgroup.zpowers y) hnorm
  have hmem : ∀ z ∈ A ⊔ Subgroup.zpowers y, ∃ a ∈ A, ∃ k : ℤ, z = a * y ^ k := by
    intro z hz
    have hz' : z ∈ ((A ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hz
    rw [hset] at hz'
    obtain ⟨a, ha, w, hw, rfl⟩ := hz'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨a, ha, k, rfl⟩
  have hyk : ∀ (a : G), a ∈ A → ∀ k : ℤ, y ^ k * a = a * y ^ k := fun a ha k =>
    ((Commute.zpow_left (show Commute y a from hyA a ha) k)).eq
  have hmul : ∀ (a b : G), a ∈ A → b ∈ A → ∀ k l : ℤ,
      a * y ^ k * (b * y ^ l) = a * b * y ^ (k + l) := by
    intro a b ha hb k l
    calc a * y ^ k * (b * y ^ l) = a * (y ^ k * b) * y ^ l := by group
      _ = a * (b * y ^ k) * y ^ l := by rw [hyk b hb k]
      _ = a * b * (y ^ k * y ^ l) := by group
      _ = a * b * y ^ (k + l) := by rw [zpow_add]
  refine ⟨⟨⟨fun z w => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha, k, hzk⟩ := hmem z z.2
    obtain ⟨b, hb, l, hwl⟩ := hmem w w.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzk, hwl, hmul a b ha hb k l, hmul b a hb ha l k,
      hAc a ha b hb, add_comm]
  · obtain ⟨a, ha, k, hzk⟩ := hmem z hz
    rw [hzk]
    have hc : Commute a (y ^ k) := (hyk a ha k).symm
    rw [hc.mul_pow, hA.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hy3, one_zpow]

end ElemAb


section Lift

variable {G : Type} [Group G] [Finite G]

theorem eq_of_conj_eq_conj {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) {u v : Q}
    (h : (MulAut.conj u : MulAut Q) = MulAut.conj v) : u = v := by
  have hc : v⁻¹ * u ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    have h1 := congrArg (fun φ : MulAut Q => φ q) h
    simp only [MulAut.conj_apply] at h1
    calc q * (v⁻¹ * u) = v⁻¹ * (v * q * v⁻¹) * u := by group
      _ = v⁻¹ * (u * q * u⁻¹) * u := by rw [h1]
      _ = v⁻¹ * u * q := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem compAction_of_mem {Y : Subgroup G} {y : G} (hy : y ∈ Y)
    (hN : y ∈ Subgroup.normalizer (Y : Set G)) :
    Sec4.compAction Y ⟨y, hN⟩ = MulAut.conj (⟨y, hy⟩ : Y) := by
  ext u
  exact Sec4.normalizerMonoidHom_apply_coe hN u

theorem thetaQuotMulAut_conj (Y : Subgroup G) (u : ↥Y) :
    Sec4.thetaQuotMulAut ↥Y (MulAut.conj u) =
      MulAut.conj (u : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H q => rfl

theorem exists_fixed_rep {A Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    {ŷ : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y}
    (hfix : ∀ (f : G) (hf : f ∈ A),
      Sec4.thetaQuotMulAut ↥Y (Sec4.compAction Y ⟨f, hAN hf⟩) ŷ = ŷ) :
    ∃ c : ↥Y, (c : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = ŷ ∧
      ∀ f ∈ A, f * (c : G) * f⁻¹ = c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ŷ
  let α : A →* MulAut ↥Y := (Sec4.compAction Y).comp (Subgroup.inclusion hAN)
  have hα : ∀ (f : A) (u : ↥Y), ((α f u : ↥Y) : G) = (f : G) * u * (f : G)⁻¹ := fun f u =>
    Sec4.normalizerMonoidHom_apply_coe (hAN f.2) u
  obtain ⟨c, hc, hfix'⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3 α
      (aschbacherSolvableCore 3 ↥Y) hθ3 g).2 (by
      intro f x hx
      have h1 : (x : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = g := (QuotientGroup.eq.mpr hx).symm
      have h2 : ((α f x : ↥Y) : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = g := by
        have := hfix f f.2
        rw [← h1] at this ⊢
        exact this
      exact QuotientGroup.eq.mp h2.symm)
  refine ⟨c, (QuotientGroup.eq.mpr hc).symm, fun f hf => ?_⟩
  have := hfix' ⟨f, hf⟩
  have h3 := hα ⟨f, hf⟩ c
  rw [this] at h3
  exact h3.symm

theorem exists_mem_inf_of_not_inducesOuterTheta {A Y : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G))
    (hZ : Subgroup.center (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = ⊥)
    {e : G} (heA : e ∈ A) (hin : ¬ Sec4.InducesOuterTheta e Y) :
    ∃ y ∈ A ⊓ Y, e * y⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun z => ⟨1, Subtype.ext (by simpa using hAe.2 z z.2)⟩
  set Q := ↥Y ⧸ aschbacherSolvableCore 3 ↥Y with hQ
  let φ : Subgroup.normalizer (Y : Set G) →* MulAut Q :=
    (Sec4.thetaQuotMulAut ↥Y).comp (Sec4.compAction Y)
  have heN := hAN heA
  have hrange : φ ⟨e, heN⟩ ∈ (MulAut.conj : Q →* MulAut Q).range := by
    by_contra h
    exact hin ⟨heN, h⟩
  obtain ⟨ŷ, hŷ⟩ := MonoidHom.mem_range.mp hrange
  have hfix : ∀ (f : G) (hf : f ∈ A), φ ⟨f, hAN hf⟩ ŷ = ŷ := by
    intro f hf
    have h1 : φ ⟨f, hAN hf⟩ * φ ⟨e, heN⟩ * (φ ⟨f, hAN hf⟩)⁻¹ = φ ⟨e, heN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hAc f hf e heA]
      group
    rw [← hŷ, KFacts.mul_mulAutConj_mul_inv] at h1
    exact eq_of_conj_eq_conj hZ h1
  have hcube : ŷ ^ 3 = 1 := by
    have h1 : (φ ⟨e, heN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨e, heN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
        Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hAe.2 e heA)
      rw [this, map_one]
    rw [← hŷ, ← map_pow] at h1
    exact eq_of_conj_eq_conj hZ (by rw [h1, map_one])
  obtain ⟨c, hc, hcf⟩ := exists_fixed_rep hA3 hAN (ŷ := ŷ) hfix
  obtain ⟨-, -, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  set N := aschbacherSolvableCore 3 ↥Y with hN
  set w := Nat.card N with hw
  have hw3 : ¬ 3 ∣ w := hθ3
  have hc3N : c ^ 3 ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow, hc, hcube]
  have hcw : (c ^ 3) ^ w = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨c ^ 3, hc3N⟩)
    exact congrArg Subtype.val this
  set c' : ↥Y := c ^ (w * w) with hc'
  have hc'3 : c' ^ 3 = 1 := by
    rw [hc', ← pow_mul]
    calc c ^ (w * w * 3) = ((c ^ 3) ^ w) ^ w := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [hcw, one_pow]
  have hc'mk : (c' : Q) = ŷ := by
    have hmod : w * w % 3 = 1 := by
      have : w % 3 = 1 ∨ w % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    obtain ⟨t, ht⟩ : ∃ t, w * w = 3 * t + 1 := ⟨w * w / 3, by omega⟩
    rw [hc', QuotientGroup.mk_pow, hc, ht, pow_succ, pow_mul, hcube, one_pow, one_mul]
  have hy3 : ((c' : ↥Y) : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hc'3]
    rfl
  have hyA : ∀ a ∈ A, ((c' : ↥Y) : G) * a = a * ((c' : ↥Y) : G) := by
    intro a ha
    have h1 : a * ((c : ↥Y) : G) * a⁻¹ = c := hcf a ha
    have h2 : a * ((c' : ↥Y) : G) * a⁻¹ = (c' : ↥Y) := by
      rw [hc', Subgroup.coe_pow, ← conj_pow, h1]
    calc ((c' : ↥Y) : G) * a = (a * ((c' : ↥Y) : G) * a⁻¹) * a := by rw [h2]
      _ = a * ((c' : ↥Y) : G) := by group
  have hB := isElemAbelian_sup_zpowers hAe hy3 hyA
  have hyA' : ((c' : ↥Y) : G) ∈ A := by
    have := hAmax _ hB le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨(c' : ↥Y), Subgroup.mem_inf.mpr ⟨hyA', c'.2⟩, ?_⟩
  have hyN : ((c' : ↥Y) : G) ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer c'.2
  have hmem : e * ((c' : ↥Y) : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ heN (Subgroup.inv_mem _ hyN)
  have hker : φ ⟨e * ((c' : ↥Y) : G)⁻¹, hmem⟩ = 1 := by
    have h1 : (⟨e * ((c' : ↥Y) : G)⁻¹, hmem⟩ : Subgroup.normalizer (Y : Set G)) =
        ⟨e, heN⟩ * ⟨(c' : ↥Y), hyN⟩⁻¹ := Subtype.ext (by simp)
    have h2 : φ ⟨(c' : ↥Y), hyN⟩ = MulAut.conj (c' : Q) := by
      change Sec4.thetaQuotMulAut ↥Y (Sec4.compAction Y ⟨(c' : ↥Y), hyN⟩) = _
      rw [compAction_of_mem c'.2 hyN, thetaQuotMulAut_conj]
    rw [h1, map_mul, map_inv, h2, ← hŷ, hc'mk, mul_inv_cancel]
  refine Subgroup.mem_map.mpr ⟨⟨e * ((c' : ↥Y) : G)⁻¹, hmem⟩, ?_, rfl⟩
  exact hker

end Lift

end Hering129KInner

end CFSG.RankThree.PartTwo.Sec12
