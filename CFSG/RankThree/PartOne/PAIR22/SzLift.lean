module

public import CFSG.RankThree.PartOne.PAIR22.Lift
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.RankThree.PartOne.S13K.ThetaFixed

public section

namespace CFSG.RankThree.PartOne.PAIR22

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K1320X
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint (SuzukiModel)

theorem suzuki_facts {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 f) :
    CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ ∧ Odd (Nat.card (Outer X)) := by
  have hSz : SuzukiModel X 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, hex, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hSz⟩
    · exact absurd hcl (by decide)
    · exact absurd hex (by decide)
    · exact absurd ht (by decide)
    · exact hSz
  have hout :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} X 2 f hSz).1.2.2
  obtain ⟨-, a, ha, Kf, _, _, rfl, hK, ⟨e⟩⟩ := hSz
  have hs := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  have hp := (CFSG.LieType.Ree.suzuki_perfect ha hK).2
  have hZ := KF132.center_eq_bot_of_simple_perfect hs hp
  have hq := KF132.isQuasisimple_of_simple_perfect hs hp
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, hout⟩
  have hc := Subgroup.map_center_eq e
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 (hc.trans hZ)

variable {G : Type} [Group G]

theorem pairLift_of_szAt [Finite G] {p f : ℕ} {E : Subgroup G}
    {t : MulAut E} (hsplit : E = autFixedInG E t ⊔ autMovedInG E t) (ht2 : t * t = 1) {x : G}
    (hx : x ∈ Subgroup.normalizer (E : Set G)) (hxt : E.normalizerMonoidHom ⟨x, hx⟩ = t)
    (hSz : KF132.SzAt p E f t) : PairLift p E t := by
  obtain ⟨hne, hmod, hmov⟩ := hSz
  obtain ⟨hq, hZ, hodd⟩ := suzuki_facts hmod
  have hKt : IsKt p E t (kZero p E t) := ⟨fun f' hf' => absurd ⟨f', hf'⟩ hne, fun _ => rfl⟩
  have hxC : x ∈ Subgroup.centralizer (autFixedInG E t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    have h1 : x * (a' : G) * x⁻¹ = (a' : G) := by
      have := Equivariance.coe_conjAut hx a'
      have h2 : conjAut E x hx = t := hxt
      rw [h2] at this
      rw [← this]
      exact congrArg Subtype.val (show t a' = a' from ha')
    simpa using (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hxK : x ∈ Subgroup.normalizer (kZero p E t : Set G) := S13K.kZero_mem_normalizer hxC
  set α : MulAut ↥(kZero p E t) := (kZero p E t).normalizerMonoidHom ⟨x, hxK⟩ with hα
  set m := Nat.card (Outer ↥(kZero p E t)) with hm
  have hαm : α ^ m ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(kZero p E t) := by
    have h1 : (QuotientGroup.mk α : Outer ↥(kZero p E t)) ^ m = 1 := pow_card_eq_one'
    rw [← QuotientGroup.mk_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := hαm
  have hαx : ∀ y : ↥(kZero p E t), ((α ^ m) y : G) = x ^ m * (y : G) * (x ^ m)⁻¹ := by
    intro y
    have h1 : α ^ m = (kZero p E t).normalizerMonoidHom (⟨x, hxK⟩ ^ m) := (map_pow _ _ _).symm
    rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hkx : ∀ y : ↥(kZero p E t), (k : G) * y * (k : G)⁻¹ = x ^ m * (y : G) * (x ^ m)⁻¹ := by
    intro y
    rw [← hαx y, ← hk]
    simp [MulAut.conj_apply]
  set c : G := (k : G)⁻¹ * x ^ m with hc
  have hcK : ∀ y ∈ kZero p E t, c * y = y * c := by
    intro y hy
    have := hkx ⟨y, hy⟩
    simp only at this
    rw [hc]
    calc (k : G)⁻¹ * x ^ m * y = (k : G)⁻¹ * (x ^ m * y * (x ^ m)⁻¹) * x ^ m := by group
      _ = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * x ^ m := by rw [← this]
      _ = y * ((k : G)⁻¹ * x ^ m) := by group
  have hcF : ∀ a ∈ autFixedInG E t, c * a = a * c := by
    intro a ha
    have hkc : (k : G) ∈ Subgroup.centralizer (autFixedInG E t : Set G) :=
      S13K.kZero_le_centralizer_fixed p E t k.2
    have hxc : x ^ m ∈ Subgroup.centralizer (autFixedInG E t : Set G) := Subgroup.pow_mem _ hxC m
    have hcc : c ∈ Subgroup.centralizer (autFixedInG E t : Set G) :=
      (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hkc) hxc
    exact (Subgroup.mem_centralizer_iff.mp hcc a ha).symm
  have hle : E ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hsplit]
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hcF a ha
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hcK a (hmov ha)
  have hcE : ∀ e ∈ E, c * e = e * c := fun e he =>
    Subgroup.mem_centralizer_iff.mp (hle he) c rfl
  have hcCent : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => (hcE e he).symm
  have hcN : c ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer (E : Set G) hcCent
  have hcN' : c⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).inv_mem hcN
  have hkG : (k : G) = x ^ m * c⁻¹ := by rw [hc]; group
  have hkN : (k : G) ∈ Subgroup.normalizer (E : Set G) := by
    rw [hkG]
    exact (Subgroup.normalizer (E : Set G)).mul_mem (Subgroup.pow_mem _ hx m) hcN'
  have hcinv : E.normalizerMonoidHom ⟨c⁻¹, hcN'⟩ = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have h1 := hcE e e.2
    calc c⁻¹ * (e : G) * c⁻¹⁻¹ = c⁻¹ * ((e : G) * c) := by group
      _ = (e : G) := by rw [← h1]; group
  have hkt : E.normalizerMonoidHom ⟨(k : G), hkN⟩ = t := by
    have h1 : (⟨(k : G), hkN⟩ : Subgroup.normalizer (E : Set G)) = ⟨x, hx⟩ ^ m * ⟨c⁻¹, hcN'⟩ := by
      apply Subtype.ext
      rw [hkG]
      simp
    rw [h1, map_mul, map_pow, hxt, hcinv, mul_one]
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, sq, ht2, one_pow, one_mul]
  exact ⟨kZero p E t, ⟨hKt, hq, hZ, hmov, (k : G), hkN, k.2, hkt⟩, hq⟩

end CFSG.RankThree.PartOne.PAIR22
