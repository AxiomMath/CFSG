module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL
  mk_eq_one_iff card_thL_coprime normalizer_le_normalizer_thL exists_fixed_coset
  not_dvd_card_of_no_order_three eq_one_of_pow_three_of_not_dvd le_normalizer_of_conj_mem)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] noncomputable def phi (L : Subgroup Γ) :
    ↥(Subgroup.normalizer (L : Set Γ)) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom

theorem phi_mk (L : Subgroup Γ) (n : ↥(Subgroup.normalizer (L : Set Γ))) (l : ↥L) :
    phi L n (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
      ((⟨(n : Γ) * l * (n : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 l).mp l.2⟩ : ↥L) :
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  rfl

theorem mem_core_of_coe_mem {L : Subgroup Γ} {y : ↥L} (h : (y : Γ) ∈ thL L) :
    y ∈ aschbacherSolvableCore 3 ↥L := by
  obtain ⟨y', hy', hyy'⟩ := h
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem phi_of_mem (L : Subgroup Γ) {l : Γ} (hl : l ∈ L) (hlN : l ∈ Subgroup.normalizer (L : Set Γ)) :
    phi L ⟨l, hlN⟩ = MulAut.conj ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [phi_mk, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

structure LRData (L R : Subgroup Γ) : Prop where
  cop : Nat.Coprime 3 (Nat.card R)
  normR_L : L ≤ Subgroup.normalizer (R : Set Γ)
  normL_R : R ≤ Subgroup.normalizer (L : Set Γ)
  inf_le : L ⊓ R ≤ thL L
  center : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥

theorem inf_le_thL_of {L R : Subgroup Γ} (hR : Nat.Coprime 3 (Nat.card R))
    (hLR : L ≤ Subgroup.normalizer (R : Set Γ))
    (hX : ∀ N : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), N.Normal → ¬ 3 ∣ Nat.card N →
      N = ⊥) : L ⊓ R ≤ thL L := by
  set π : ↥L →* ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ with hπ
  set M : Subgroup ↥L := (L ⊓ R).subgroupOf L with hM
  set N : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := M.map π with hN
  have hMn : ∀ l : ↥L, ∀ m ∈ M, l * m * l⁻¹ ∈ M := by
    intro l m hm
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmL, hmR⟩ := hm
    refine ⟨?_, ?_⟩
    · simpa using L.mul_mem (L.mul_mem l.2 hmL) (L.inv_mem l.2)
    · have := (Subgroup.mem_normalizer_iff.mp (hLR l.2) (m : Γ)).mp hmR
      simpa using this
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hn
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ x
    refine ⟨l * m * l⁻¹, hMn l m hm, ?_⟩
    simp [hπ]
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h
    have h1 : Nat.card N ∣ Nat.card M := Subgroup.card_map_dvd _ _
    have h2 : Nat.card M ∣ Nat.card R := by
      have hc : M.map L.subtype = (L ⊓ R) ⊓ L := Subgroup.subgroupOf_map_subtype _ _
      have h4 : Nat.card M = Nat.card (M.map L.subtype) :=
        (Subgroup.card_map_of_injective L.subtype_injective).symm
      rw [hc] at h4
      rw [h4]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_right)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR (h.trans (h1.trans h2))
  have hbot := hX N hNn h3
  intro g hg
  have hgM : (⟨g, hg.1⟩ : ↥L) ∈ M := by
    rw [hM, Subgroup.mem_subgroupOf]
    exact hg
  have : π ⟨g, hg.1⟩ ∈ N := ⟨_, hgM, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (mk_eq_one_iff L ⟨g, hg.1⟩).mp this

namespace LRData

variable {L R : Subgroup Γ} (d : LRData L R)
include d

theorem sup_le_normalizer : L ⊔ R ≤ Subgroup.normalizer (L : Set Γ) :=
  sup_le Subgroup.le_normalizer d.normL_R

theorem exists_mul {g : Γ} (hg : g ∈ L ⊔ R) : ∃ l ∈ L, ∃ r ∈ R, g = l * r := by
  have hconj : ∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun r hr l hl =>
    (Subgroup.mem_normalizer_iff.mp (d.normL_R hr) l).mp hl
  let S : Subgroup Γ :=
    { carrier := {g | ∃ l ∈ L, ∃ r ∈ R, g = l * r}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, r₁, hr₁, rfl⟩ ⟨l₂, hl₂, r₂, hr₂, rfl⟩
        refine ⟨l₁ * (r₁ * l₂ * r₁⁻¹), L.mul_mem hl₁ (hconj r₁ hr₁ l₂ hl₂), r₁ * r₂,
          R.mul_mem hr₁ hr₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, r, hr, rfl⟩
        refine ⟨r⁻¹ * l⁻¹ * r⁻¹⁻¹, ?_, r⁻¹, R.inv_mem hr, ?_⟩
        · exact hconj r⁻¹ (R.inv_mem hr) l⁻¹ (L.inv_mem hl)
        · group }
  have hle : L ⊔ R ≤ S := sup_le (fun l hl => ⟨l, hl, 1, one_mem _, by simp⟩)
    (fun r hr => ⟨1, one_mem _, r, hr, by simp⟩)
  exact hle hg

theorem phi_eq_one_of_mem_R {r : Γ} (hr : r ∈ R) (hrN : r ∈ Subgroup.normalizer (L : Set Γ)) :
    phi L ⟨r, hrN⟩ = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [phi_mk, MulAut.one_apply]
    apply QuotientGroup.eq.mpr
    apply mem_core_of_coe_mem
    apply d.inf_le
    have hyL : (y : Γ) ∈ L := y.2
    have hconjL : r * y * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrN y).mp y.2
    refine ⟨?_, ?_⟩
    · change (r * y * r⁻¹)⁻¹ * y ∈ L
      exact L.mul_mem (L.inv_mem hconjL) hyL
    · change (r * y * r⁻¹)⁻¹ * y ∈ R
      have h1 : (y : Γ)⁻¹ * r⁻¹ * y ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (d.normR_L (L.inv_mem hyL)) r⁻¹).mp (R.inv_mem hr)
        simpa [mul_assoc] using this
      have e : (r * y * r⁻¹)⁻¹ * y = r * ((y : Γ)⁻¹ * r⁻¹ * y) := by group
      rw [e]
      exact R.mul_mem hr h1

theorem phi_mul_of_mem {l r : Γ} (hl : l ∈ L) (hr : r ∈ R)
    (hg : l * r ∈ Subgroup.normalizer (L : Set Γ)) :
    phi L ⟨l * r, hg⟩ = phi L ⟨l, Subgroup.le_normalizer hl⟩ := by
  have e : (⟨l * r, hg⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
      ⟨l, Subgroup.le_normalizer hl⟩ * ⟨r, d.normL_R hr⟩ := rfl
  rw [e, map_mul, d.phi_eq_one_of_mem_R hr, mul_one]

theorem phi_eq_one_iff {l : Γ} (hl : l ∈ L) (hlN : l ∈ Subgroup.normalizer (L : Set Γ)) :
    phi L ⟨l, hlN⟩ = 1 ↔ l ∈ thL L := by
  rw [phi_of_mem L hl hlN, ← mk_eq_one_iff L ⟨l, hl⟩]
  constructor
  · intro h
    have hc : ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) => φ z) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
          ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * z *
            ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)⁻¹ *
              ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by rw [this]
        _ = _ := by group
    rw [d.center, Subgroup.mem_bot] at hc
    exact hc
  · intro h
    change MulAut.conj ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1
    rw [show ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 from h, map_one]

theorem eq_one_of_phi_one {g : Γ} (hg : g ∈ L ⊔ R) (hgN : g ∈ Subgroup.normalizer (L : Set Γ))
    (h1 : phi L ⟨g, hgN⟩ = 1) (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨l, hl, r, hr, rfl⟩ := d.exists_mul hg
  rw [d.phi_mul_of_mem hl hr hgN, d.phi_eq_one_iff hl] at h1
  have hlθ := h1
  have hrN : r ∈ Subgroup.normalizer (thL L : Set Γ) :=
    normalizer_le_normalizer_thL L (d.normL_R hr)
  have hconj : ∀ x ∈ thL L, r * x * r⁻¹ ∈ thL L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hrN x).mp hx
  have hl1 := hconj l hlθ
  have hl2 := hconj _ hl1
  have hr3 : r ^ 3 ∈ thL L := by
    have e : (l * r) ^ 3 = l * (r * l * r⁻¹) * (r * (r * l * r⁻¹) * r⁻¹) * r ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [h3] at e
    have : r ^ 3 = (l * (r * l * r⁻¹) * (r * (r * l * r⁻¹) * r⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right e.symm
    rw [this]
    exact (thL L).inv_mem (mul_mem (mul_mem hlθ hl1) hl2)
  have hrθ : r ∈ thL L := by
    have hord : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
    have hcop : Nat.Coprime 3 (orderOf r) := Nat.Coprime.coprime_dvd_right hord d.cop
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact pow_mem hr3 m
  have hgθ : l * r ∈ thL L := mul_mem hlθ hrθ
  have hord1 : orderOf (l * r) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (l * r) ∣ Nat.card (thL L) := Subgroup.orderOf_dvd_natCard _ hgθ
  have hcop : Nat.Coprime 3 (Nat.card (thL L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (card_thL_coprime L)
  have : orderOf (l * r) ∣ Nat.gcd 3 (Nat.card (thL L)) := Nat.dvd_gcd hord1 hord2
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem mem_L_of_pow_three_pow {g : Γ} (hg : g ∈ L ⊔ R) {k : ℕ} (hk : g ^ 3 ^ k = 1) :
    g ∈ L := by
  obtain ⟨l, hl, r, hr, rfl⟩ := d.exists_mul hg
  have hconj : ∀ x ∈ L, r * x * r⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (d.normL_R hr) x).mp hx
  have hconjpow : ∀ n : ℕ, ∀ x ∈ L, r ^ n * x * (r ^ n)⁻¹ ∈ L := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := hconj _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have hform : ∀ n : ℕ, ∃ ln ∈ L, (l * r) ^ n = ln * r ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨ln, hln, h⟩ := ih
      refine ⟨ln * (r ^ n * l * (r ^ n)⁻¹), L.mul_mem hln (hconjpow n l hl), ?_⟩
      rw [pow_succ, h]
      group
  obtain ⟨ln, hln, h⟩ := hform (3 ^ k)
  rw [hk] at h
  have hrk : r ^ 3 ^ k ∈ L := by
    have : r ^ 3 ^ k = ln⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact L.inv_mem hln
  have hord : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
  have hcop : Nat.Coprime (3 ^ k) (orderOf r) :=
    Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right hord d.cop)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hrL : r ∈ L := by
    rw [← hm]
    exact pow_mem hrk m
  exact L.mul_mem hl hrL

end LRData

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
