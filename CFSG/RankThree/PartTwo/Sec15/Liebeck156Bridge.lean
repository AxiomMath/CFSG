module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.FixedLift

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def TypeK156 : Prop :=
  ∀ (Xt : Type) [Group Xt] [Finite Xt],
    (Sec4.IsTripleCover Xt CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Xt (alternatingGroup (Fin 6)) ∨ Sec14.IsCentralProductA6Covers Xt) →
    ∀ (Yt Pt : Subgroup Xt), Group.IsPerfect ↥Yt → Pt ≤ Yt → IsPGroup 2 Pt →
      ∀ _ : (Pt.subgroupOf Yt).Normal,
      Nonempty (↥Yt ⧸ Pt.subgroupOf Yt ≃* alternatingGroup (Fin 5)) →
      ∀ γ : MulAut Xt, γ ^ 3 = 1 → (∀ y ∈ Yt, γ y ∈ Yt) → (∀ x ∈ Pt, γ x ∈ Pt) →
        (∀ y ∈ Yt, γ y * y⁻¹ ∈ Pt) → (∀ x ∈ Pt, γ x = x → x = 1) → Pt = ⊥

section Abstract

variable {Y Z : Type} [Group Y] [Group Z]

private theorem ker_le_of_isSolvable (hYp : Group.IsPerfect Y) (Q : Subgroup Y) [Q.Normal]
    (hY5 : Nonempty (Y ⧸ Q ≃* alternatingGroup (Fin 5))) (ρ : Y →* Z)
    (hsol : Group.IsSolvable ρ.ker) : ρ.ker ≤ Q := by
  obtain ⟨e⟩ := hY5
  haveI := hYp
  haveI : IsSimpleGroup (Y ⧸ Q) :=
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    e.isSimpleGroup
  exact Sec4.Census.le_of_isSolvable_of_normal inferInstance hsol

variable [Finite Y] {Xt : Type} [Group Xt] [Finite Xt]

private theorem le_ker_of_typeK156 (hK : TypeK156)
    (htype : Sec4.IsTripleCover Xt CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Xt (alternatingGroup (Fin 6)) ∨ Sec14.IsCentralProductA6Covers Xt)
    (Q : Subgroup Y) [Q.Normal] (hQ2 : IsPGroup 2 Q) (hYp : Group.IsPerfect Y)
    (hY5 : Nonempty (Y ⧸ Q ≃* alternatingGroup (Fin 5))) (ρ : Y →* Xt)
    (hsol : Group.IsSolvable ρ.ker) (τ : MulAut Y) (γ : MulAut Xt)
    (hγ : ∀ y, γ (ρ y) = ρ (τ y)) (hγ3 : γ ^ 3 = 1) (hτ3 : τ ^ 3 = 1)
    (hτQ : ∀ q ∈ Q, τ q ∈ Q) (hτc : ∀ y, τ y * y⁻¹ ∈ Q)
    (hτfix : ∀ q ∈ Q, τ q = q → q = 1) : Q ≤ ρ.ker := by
  have hker : ρ.ker ≤ Q := ker_le_of_isSolvable hYp Q hY5 ρ hsol
  haveI := hYp
  have hle : Q.map ρ ≤ ρ.range := Subgroup.map_le_range ρ Q
  have hsub : (Q.map ρ).subgroupOf ρ.range = Q.map ρ.rangeRestrict := by
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact exists_congr fun q => and_congr_right fun _ =>
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hN : ((Q.map ρ).subgroupOf ρ.range).Normal := by
    rw [hsub]
    exact Subgroup.Normal.map inferInstance _ (MonoidHom.rangeRestrict_surjective ρ)
  have hquot : Nonempty (↥ρ.range ⧸ (Q.map ρ).subgroupOf ρ.range ≃*
      alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := hY5
    haveI := hN
    let φ : Y →* ↥ρ.range ⧸ (Q.map ρ).subgroupOf ρ.range :=
      (QuotientGroup.mk' _).comp ρ.rangeRestrict
    have hφs : Function.Surjective φ :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective ρ)
    have hφk : φ.ker = Q := by
      ext y
      rw [MonoidHom.mem_ker]
      change ((ρ.rangeRestrict y : ↥ρ.range) : ↥ρ.range ⧸ (Q.map ρ).subgroupOf ρ.range) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨q, hq, hqy⟩
        have h1 : q⁻¹ * y ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hqy]
          exact inv_mul_cancel _
        simpa using Q.mul_mem hq (hker h1)
      · intro hy
        exact ⟨y, hy, rfl⟩
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hφk).trans e)⟩
  have hγY : ∀ y ∈ ρ.range, γ y ∈ ρ.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨τ y, (hγ y).symm⟩
  have hγP : ∀ x ∈ Q.map ρ, γ x ∈ Q.map ρ := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨τ q, hτQ q hq, (hγ q).symm⟩
  have hγc : ∀ y ∈ ρ.range, γ y * y⁻¹ ∈ Q.map ρ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨τ y * y⁻¹, hτc y, by rw [map_mul, map_inv, hγ]⟩
  have hfix : ∀ x ∈ Q.map ρ, γ x = x → x = 1 := by
    rintro _ ⟨q, hq, rfl⟩ hx
    have hcop : Nat.Coprime 3 (Nat.card ρ.ker) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ2.to_le hker)
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    obtain ⟨g, hg, hτg⟩ := CFSG.AGLEmbeddingD2.Wilson.Proving.exists_fixed_lift_of_pow_three ρ
      hcop τ hτ3 (y := q) fun g hg => by rw [← hγ, hg]; exact hx
    have hgQ : g ∈ Q := by
      have h1 : q⁻¹ * g ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hg]
        exact inv_mul_cancel _
      simpa using Q.mul_mem hq (hker h1)
    rw [← hg, hτfix g hgQ hτg, map_one]
  have hbot := hK Xt htype ρ.range (Q.map ρ) (Group.IsPerfect.range ρ) hle (hQ2.map ρ) hN
    hquot γ hγ3 hγY hγP hγc hfix
  exact (Subgroup.map_eq_bot_iff _).mp hbot

end Abstract

private theorem normalizerMonoidHom_pow_three {G : Type} [Group G] {N : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (N : Set G)) (h3 : c ^ 3 = 1) :
    N.normalizerMonoidHom ⟨c, hc⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have h : (⟨c, hc⟩ : Subgroup.normalizer (N : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  rw [h, map_one]

theorem pCoreOf_le_theta_of_typeK156 (hK : TypeK156) {G : Type} [Group G] [Finite G]
    {X Y : Subgroup G} {c₀ : G}
    (htype : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
      Sec14.IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hYX : Y ≤ X) (hYp : Group.IsPerfect ↥Y)
    (hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)))
    (hc₀X : c₀ ∈ Subgroup.normalizer (X : Set G)) (hc₀Y : c₀ ∈ Subgroup.normalizer (Y : Set G))
    (hc₀3 : c₀ ^ 3 = 1)
    (hc₀c : ∀ y ∈ Y, c₀ * y * c₀⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y)
    (hfix : CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c₀} : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 Y ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  obtain ⟨ι, hι⟩ : ∃ ι : ↥Y →* ↥X, ∀ y, (ι y : G) = y := ⟨Subgroup.inclusion hYX, fun _ => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥Y →* ↥X ⧸ aschbacherSolvableCore 3 ↥X,
      ∀ y, ρ y = ((ι y : ↥X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    ⟨(QuotientGroup.mk' _).comp ι, fun _ => rfl⟩
  obtain ⟨τ, hτ, hτ3⟩ : ∃ τ : MulAut ↥Y,
      (∀ y, ((τ y : ↥Y) : G) = c₀ * y * c₀⁻¹) ∧ τ ^ 3 = 1 :=
    ⟨Y.normalizerMonoidHom ⟨c₀, hc₀Y⟩, fun y => Sec4.normalizerMonoidHom_apply_coe hc₀Y y,
      normalizerMonoidHom_pow_three hc₀Y hc₀3⟩
  obtain ⟨σ, hσ, hσ3⟩ : ∃ σ : MulAut ↥X,
      (∀ x, ((σ x : ↥X) : G) = c₀ * x * c₀⁻¹) ∧ σ ^ 3 = 1 :=
    ⟨X.normalizerMonoidHom ⟨c₀, hc₀X⟩, fun x => Sec4.normalizerMonoidHom_apply_coe hc₀X x,
      normalizerMonoidHom_pow_three hc₀X hc₀3⟩
  obtain ⟨γ, hγ, hγ3⟩ : ∃ γ : MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X),
      (∀ x : ↥X, γ (x : ↥X ⧸ aschbacherSolvableCore 3 ↥X) =
        ((σ x : ↥X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X)) ∧ γ ^ 3 = 1 :=
    ⟨Sec4.thetaQuotMulAut ↥X σ, fun x => Sec4.thetaQuotMulAut_mk σ x,
      by rw [← map_pow, hσ3, map_one]⟩
  have hργ : ∀ y : ↥Y, γ (ρ y) = ρ (τ y) := fun y => by
    have h : σ (ι y) = ι (τ y) := Subtype.ext (by rw [hσ, hι, hι, hτ])
    rw [hρ, hρ, hγ, h]
  have hsol : Group.IsSolvable ρ.ker := by
    haveI : Group.IsSolvable (aschbacherSolvableCore 3 ↥X) :=
      (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
    have hmem : ∀ k : ρ.ker, (ι.comp ρ.ker.subtype) k ∈ aschbacherSolvableCore 3 ↥X := fun k => by
      have h : ρ (k : ↥Y) = 1 := k.2
      rw [hρ] at h
      exact (QuotientGroup.eq_one_iff _).mp h
    refine Group.isSolvable_of_isSolvable_injective
      (f := (ι.comp ρ.ker.subtype).codRestrict (aschbacherSolvableCore 3 ↥X) hmem) ?_
    intro k₁ k₂ h
    have h1 := congrArg (fun z : ↥(aschbacherSolvableCore 3 ↥X) => ((z : ↥X) : G)) h
    exact Subtype.ext (Subtype.ext (by simpa [hι] using h1))
  have hτQ : ∀ q ∈ CFSG.pCore 2 ↥Y, τ q ∈ CFSG.pCore 2 ↥Y := fun q hq =>
    ((pCore_characteristic (p := 2) (G := ↥Y)).fixed τ).symm.le hq
  have hτc : ∀ y : ↥Y, τ y * y⁻¹ ∈ CFSG.pCore 2 ↥Y := fun y => by
    obtain ⟨q, hq, hqe⟩ := hc₀c y y.2
    have h : τ y * y⁻¹ = q :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, hτ]; exact hqe.symm)
    rwa [h]
  have hτfix : ∀ q ∈ CFSG.pCore 2 ↥Y, τ q = q → q = 1 := by
    intro q hq hqf
    have h1 : (q : G) ∈ CFSG.Open.pCoreOf 2 Y := ⟨q, hq, rfl⟩
    have h2 : (q : G) ∈ Subgroup.centralizer ({c₀} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      have h3 := congrArg Subtype.val hqf
      rw [hτ] at h3
      calc c₀ * q = (c₀ * q * c₀⁻¹) * c₀ := by group
        _ = q * c₀ := by rw [h3]
    have h3 : (q : G) ∈ (⊥ : Subgroup G) := hfix ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  have hmain : CFSG.pCore 2 ↥Y ≤ ρ.ker :=
    le_ker_of_typeK156 hK htype (CFSG.pCore 2 ↥Y) pCore_isPGroup hYp hY5 ρ hsol τ γ hργ hγ3 hτ3
      hτQ hτc hτfix
  rintro _ ⟨q, hq, rfl⟩
  have hq1 : ρ q = 1 := hmain hq
  rw [hρ] at hq1
  exact ⟨ι q, (QuotientGroup.eq_one_iff _).mp hq1, hι q⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
