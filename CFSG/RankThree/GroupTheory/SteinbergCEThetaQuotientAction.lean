module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree.LocalRank

variable {G : Type*} [Group G]

instance aschbacherSolvableCore_characteristic (p : ℕ) (H : Type*) [Group H] :
    (aschbacherSolvableCore p H).Characteristic := by
  unfold aschbacherSolvableCore inSubgroup
  infer_instance

@[expose] noncomputable def thetaQuotientConj (p : ℕ) (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ aschbacherSolvableCore p K) :=
  (mulAutQuotientHom (aschbacherSolvableCore p K)).comp K.normalizerMonoidHom

@[expose] noncomputable def thetaQuotientAction (p : ℕ) {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A →* MulAut (K ⧸ aschbacherSolvableCore p K) :=
  (thetaQuotientConj p K).comp (Subgroup.inclusion hAK)

@[expose] noncomputable def thetaQuotientCentralizer (p : ℕ) (A K : Subgroup G) : Subgroup G :=
  A ⊓ (thetaQuotientConj p K).ker.map (Subgroup.normalizer (K : Set G)).subtype

theorem thetaQuotientConj_mk (p : ℕ) (K : Subgroup G) (g : Subgroup.normalizer (K : Set G))
    (k : K) :
    thetaQuotientConj p K g (k : K ⧸ aschbacherSolvableCore p K) =
      ((K.normalizerMonoidHom g k : K) : K ⧸ aschbacherSolvableCore p K) :=
  rfl

theorem thetaQuotientConj_eq_one_iff (p : ℕ) (K : Subgroup G)
    (g : Subgroup.normalizer (K : Set G)) :
    thetaQuotientConj p K g = 1 ↔
      ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  constructor
  · intro h k hk
    have hk' := congrArg (fun φ : MulAut (K ⧸ aschbacherSolvableCore p K) =>
      φ ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore p K)) h
    simp only [thetaQuotientConj_mk, MulAut.one_apply] at hk'
    rw [QuotientGroup.eq_iff_div_mem] at hk'
    refine ⟨_, hk', ?_⟩
    simp [div_eq_mul_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H k =>
    rw [thetaQuotientConj_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem]
    obtain ⟨z, hz, hzk⟩ := h k k.2
    have : z = K.normalizerMonoidHom g k / k := Subtype.ext (by
      simpa [div_eq_mul_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] using hzk)
    rwa [← this]

theorem mem_thetaQuotientCentralizer_iff {p : ℕ} {A K : Subgroup G} {x : G} :
    x ∈ thetaQuotientCentralizer p A K ↔ x ∈ A ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K := by
  simp only [thetaQuotientCentralizer, Subgroup.mem_inf, Subgroup.mem_map, MonoidHom.mem_ker,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨hxA, g, hg, rfl⟩
    exact ⟨hxA, g.2, (thetaQuotientConj_eq_one_iff p K g).mp hg⟩
  · rintro ⟨hxA, hxN, h⟩
    exact ⟨hxA, ⟨x, hxN⟩, (thetaQuotientConj_eq_one_iff p K ⟨x, hxN⟩).mpr h, rfl⟩

theorem thetaQuotientCentralizer_eq_map_ker (p : ℕ) {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    thetaQuotientCentralizer p A K = (thetaQuotientAction p hAK).ker.map A.subtype := by
  ext x
  rw [mem_thetaQuotientCentralizer_iff]
  constructor
  · rintro ⟨hxA, -, h⟩
    exact ⟨⟨x, hxA⟩, (thetaQuotientConj_eq_one_iff p K _).mpr h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, hAK a.2, (thetaQuotientConj_eq_one_iff p K _).mp ha⟩

theorem mem_ker_thetaQuotientAction_iff (p : ℕ) {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (a : A) :
    a ∈ (thetaQuotientAction p hAK).ker ↔
      ∀ k ∈ K, (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K :=
  (MonoidHom.mem_ker).trans (thetaQuotientConj_eq_one_iff p K _)

end CFSG.RankThree.GroupTheory
