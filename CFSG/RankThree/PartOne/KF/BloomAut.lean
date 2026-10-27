module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.RankThree.PartOne.KFBloom

open CFSG.ComponentClassification

theorem aut_eq_one_of_central_perfect {H : Type*} [Group H] [hperf : Group.IsPerfect H]
    (α : MulAut H) (hα : ∀ h : H, h⁻¹ * α h ∈ Subgroup.center H) : α = 1 := by
  let φ : H →* Subgroup.center H :=
    { toFun := fun h => ⟨h⁻¹ * α h, hα h⟩
      map_one' := by ext; simp
      map_mul' := fun h k => by
        ext
        have hz : h⁻¹ * α h ∈ Subgroup.center H := hα h
        have := Subgroup.mem_center_iff.mp hz (k⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc k⁻¹ * h⁻¹ * (α h * α k) = k⁻¹ * (h⁻¹ * α h) * α k := by group
          _ = (h⁻¹ * α h) * k⁻¹ * α k := by rw [this]
          _ = h⁻¹ * α h * (k⁻¹ * α k) := by group }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker φ
  ext h
  have : φ h = 1 := (MonoidHom.mem_ker.mp (by rw [hker]; trivial))
  have h2 : h⁻¹ * α h = 1 := congrArg Subtype.val this
  exact (inv_mul_eq_one.mp h2).symm

theorem not_dvd_336 {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) : ¬ p ∣ 336 := by
  intro hd
  have h336 : (336 : ℕ) = 2 ^ 4 * 3 * 7 := by norm_num
  rw [h336] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega

theorem not_dvd_360 {p : ℕ} (hp : p.Prime) (h : 7 ≤ p) : ¬ p ∣ 360 := by
  intro hd
  have h360 : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
  rw [h360] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega

theorem aut_eq_one_of_gl_three_two {H : Type*} [Group H] (e : H ≃* GL (Fin 3) (ZMod 2))
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (α : MulAut H) (hα : α ^ p = 1) : α = 1 := by
  have hpr : p.Prime := Fact.out
  have hord1 : orderOf α ∣ p := orderOf_dvd_of_pow_eq_one hα
  have hord2 : orderOf α ∣ 336 := by
    have h1 : orderOf (MulAut.congr e α) ∣ Nat.card (MulAut (GL (Fin 3) (ZMod 2))) :=
      orderOf_dvd_natCard _
    rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32] at h1
    rwa [MulEquiv.orderOf_eq (MulAut.congr e)] at h1
  rcases (Nat.dvd_prime hpr).mp hord1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hord2
    exact not_dvd_336 hpr hp hord2

theorem aut_eq_one_of_three_alt_six {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (α : MulAut H) (hα : α ^ p = 1) : α = 1 := by
  have hpr : p.Prime := Fact.out
  let ᾱ : MulAut (H ⧸ Subgroup.center H) :=
    QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) α
      (OuterAutomorphisms.center_map_equiv α)
  have hᾱ : ∀ h : H, ᾱ (h : H ⧸ Subgroup.center H) = ((α h : H) : H ⧸ Subgroup.center H) :=
    fun h => rfl
  have hiter : ∀ k : ℕ, ∀ h : H, (ᾱ ^ k) (h : H ⧸ Subgroup.center H) =
      (((α ^ k) h : H) : H ⧸ Subgroup.center H) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, ih, hᾱ, pow_succ', MulAut.mul_apply]
  have hᾱp : ᾱ ^ p = 1 := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hiter, hα]
    rfl
  have hout : Nat.card (OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) ≤ 4 :=
    CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
  have hfin : Finite (MulAut (H ⧸ Subgroup.center H)) :=
    Finite.of_injective (fun f : MulAut (H ⧸ Subgroup.center H) =>
      (f : H ⧸ Subgroup.center H → H ⧸ Subgroup.center H)) DFunLike.coe_injective
  have hfin2 : Finite (OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) :=
    Finite.of_surjective (QuotientGroup.mk' (OuterAutomorphisms.inner (H ⧸ Subgroup.center H)))
      (QuotientGroup.mk'_surjective _)
  have hq : orderOf (QuotientGroup.mk ᾱ :
      OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) = 1 := by
    have h1 : orderOf (QuotientGroup.mk ᾱ :
        OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hᾱp]
      rfl
    have h2 : orderOf (QuotientGroup.mk ᾱ :
        OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) ≤ 4 :=
      (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)).trans hout
    rcases (Nat.dvd_prime hpr).mp h1 with h | h
    · exact h
    · omega
  have hq1 : (QuotientGroup.mk ᾱ : OuterAutomorphisms.Outer (H ⧸ Subgroup.center H)) = 1 :=
    orderOf_eq_one_iff.mp hq
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff ᾱ).mp hq1
  have hbp : b ^ p ∈ Subgroup.center (H ⧸ Subgroup.center H) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : (MulAut.conj (b ^ p)) = 1 := by rw [map_pow, hb, hᾱp]
    have h2 := congrArg (fun f : MulAut (H ⧸ Subgroup.center H) => f x) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc x * b ^ p = (b ^ p * x * (b ^ p)⁻¹) * b ^ p := by rw [h2]
      _ = b ^ p * x := by group
  have hcen : Subgroup.center (H ⧸ Subgroup.center H) = ⊥ := by
    have h1 := OuterAutomorphisms.center_map_equiv e
    rw [CatalogueSchreierAlternating.DegreeSix.center_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp h1
  rw [hcen, Subgroup.mem_bot] at hbp
  have hb1 : b = 1 := by
    have h1 : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hbp
    have h2 : orderOf b ∣ 360 := by
      have := orderOf_dvd_natCard b
      rwa [Nat.card_congr e.toEquiv,
        CatalogueSchreierAlternating.DegreeSix.card_alternating_six] at this
    rcases (Nat.dvd_prime hpr).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at h2
      exact not_dvd_360 hpr hp h2
  have hᾱ1 : ᾱ = 1 := by rw [← hb, hb1, map_one]
  refine aut_eq_one_of_central_perfect α fun h => ?_
  have h1 : ((α h : H) : H ⧸ Subgroup.center H) = (h : H ⧸ Subgroup.center H) := by
    rw [← hᾱ, hᾱ1]
    rfl
  exact QuotientGroup.eq.mp h1.symm

end CFSG.RankThree.PartOne.KFBloom
