module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwoLocalLevi
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem isElemAbelian_sup_zpowers_of_map_inv {G : Type*} [Group G] (F : G →* G)
    {B : Subgroup G} (hB : IsElemAbelian 3 B) (hFB : ∀ w ∈ B, F w = w) {z : G} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hFz : F z = z⁻¹) (hc : ∀ w ∈ B, w * z = z * w) :
    IsElemAbelian 3 (B ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(B ⊔ Subgroup.zpowers z) = Nat.card B * 3 := by
  have hZ := CFSG.Open.isElemAbelian_zpowers hz3
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hc))
  have hD : Disjoint B (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro w hwB hwz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwz
    have h1 : (z ^ k)⁻¹ = z ^ k := by rw [← inv_zpow, ← hFz, ← map_zpow, hFB _ hwB]
    have h2 : z ^ k * z ^ k = 1 := mul_eq_one_iff_eq_inv.2 h1.symm
    calc z ^ k = (z ^ k) ^ 3 * (z ^ k * z ^ k)⁻¹ := by group
      _ = 1 := by rw [hZ.2 _ hwz, h2, inv_one, one_mul]
  refine ⟨hB.sup_of_commute hZ fun a ha b hb => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute a z from hc a ha).zpow_right k).eq
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B _ hN hD,
      Nat.card_zpowers, orderOf_eq_prime hz3 hz1]


theorem exists_conj_torus_of_twNormTwo (hT : ExcFramesHalf.BigElemAbelianToralBar .E6 3)
    {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) (j : K →+* AlgebraicClosure K₀)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A) (hU : TwNormTwo K σ A) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K₀), ∀ x ∈ A,
      g⁻¹ * baseChangeGL j x * g ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K₀) := by
  set L := AlgebraicClosure K₀
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  haveI : CharP L 2 := charP_of_injective_ringHom j.injective 2
  haveI := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
  obtain ⟨h, hhC, J, hJ, hhL⟩ :=
    exists_conj_le_levi_of_twNormTwo hK hσ hAI (by rw [hk]; exact Odd.pow ⟨1, rfl⟩) hU
  have hCI : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ := le_sup_left
  have hhA : ∀ x ∈ A, h * x * h⁻¹ ∈ twistedE6InndiagGL K σ := fun x hx =>
    mul_mem (mul_mem (hCI hhC) (hAI hx)) (inv_mem (hCI hhC))
  obtain ⟨Fr, hFr⟩ : ∃ Fr : L →+* L, ∀ c, Fr c = c ^ 2 ^ n :=
    ⟨iterateFrobenius L 2 n, fun c => iterateFrobenius_def 2 n c⟩
  obtain ⟨ζ, hz3, hz1, hFz⟩ := exists_leviCochar_inv j hK h3 hJ hFr
  have hcomm : j.comp σ.toRingHom = Fr.comp j := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hFr, map_pow]
  set φ := (baseChangeGL j).comp (MulAut.conj h).toMonoidHom with hφ
  have hφx : ∀ x, φ x = baseChangeGL j (h * x * h⁻¹) := fun x => rfl
  have hφinj : Function.Injective φ := (baseChangeGL_injective j).comp (MulAut.conj h).injective
  have hBF : ∀ w ∈ A.map φ, twistHom TwistTag.E6 L Fr w = w := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hφx, twistHom_baseChangeGL j hcomm, RecipeExcLang.twistHom_eq_of_mem_twInndiag
      (TwE6FieldCore.twistedE6InndiagGL_le_twInndiagGroup σ (hhA x hx))]
  obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers_of_map_inv _ (hA.map φ) hBF hz3 hz1 hFz (by
    rintro _ ⟨x, hx, rfl⟩
    exact baseChangeGL_commute_leviCochar j σ (hhL x hx) ζ)
  have hjA := map_twistedE6InndiagGL_le σ j fun c => by
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (j c) (n := 3) (by norm_num)
    refine ⟨Units.mk0 u fun h0 => c.ne_zero (j.injective ?_), Units.ext (by simpa using hu)⟩
    rw [map_zero, ← hu, h0, zero_pow three_ne_zero]
  have hle : A.map φ ⊔ Subgroup.zpowers (leviCochar L J ζ) ≤ adjointGroup Tag.E6 L := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 (by
      rw [leviCochar_apply]; exact rootDiagUnit_mem_adjointGroup_of_isAlgClosed _))
    rintro _ ⟨x, hx, rfl⟩
    exact hjA (Subgroup.mem_map_of_mem _ (hhA x hx))
  have h3K₀ : ¬ 3 ∣ Nat.card K₀ := fun h3' => by
    have : Fintype K₀ := Fintype.ofFinite K₀
    obtain ⟨m, -, hm⟩ := FiniteField.card K₀ 2
    rw [Nat.card_eq_fintype_card, hm] at h3'
    exact absurd (Nat.le_of_dvd two_pos (Nat.prime_three.dvd_of_dvd_pow h3')) (by norm_num)
  have hEc : Nat.card ↥(A.map φ ⊔ Subgroup.zpowers (leviCochar L J ζ)) = Nat.card A * 3 :=
    hEcard.trans (by rw [Subgroup.card_map_of_injective hφinj])
  obtain ⟨g₁, hg₁, hg₁T⟩ : ∃ g ∈ adjointGroup TwistTag.E6.tag L,
      ∀ x ∈ A.map φ ⊔ Subgroup.zpowers (leviCochar L J ζ),
        g⁻¹ * x * g ∈ torusGroup TwistTag.E6.tag L :=
    hT K₀ h3K₀ _ hle (fun x hx y hy => hE.comm hx hy) hE.2
      ((Nat.mul_le_mul_right 3 hcard).trans_eq hEc.symm)
  refine ⟨(baseChangeGL j h)⁻¹ * g₁,
    mul_mem (inv_mem (hjA (Subgroup.mem_map_of_mem _ (hCI hhC)))) hg₁, fun x hx => ?_⟩
  have e : ((baseChangeGL j h)⁻¹ * g₁)⁻¹ * baseChangeGL j x * ((baseChangeGL j h)⁻¹ * g₁) =
      g₁⁻¹ * φ x * g₁ := by
    rw [hφx, map_mul, map_mul, map_inv]
    group
  rw [e]
  exact hg₁T _ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hx))

end CFSG.StandardType.TwE6RootKill

end
