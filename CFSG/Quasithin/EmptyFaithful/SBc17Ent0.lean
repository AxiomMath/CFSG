module

public import CFSG.Quasithin.EmptyFaithful.SBc17Out5V
public import CFSG.Quasithin.EmptyFaithful.SBc14Pair
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc17

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_open {K X : Subgroup G} (h : IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal := by
  have h1 := A3.subnormal_comap X.subtype h
  have e2 : X.comap X.subtype = ⊤ := by ext x; simp
  rw [e2] at h1
  exact A3.subnormal_top_iff.1 h1

theorem charTwo_of_mem_cComp [Finite G] {H K : Subgroup G} (hH : CharTwo H) (hK : K ∈ cComp H) :
    CharTwo K :=
  EscapingComponents.charTwo_of_isSubnormal hH (le_of_mem_cComp hK)
    (isSubnormal_subgroupOf_of_open (subnormal_of_mem_cComp hK))

theorem mem_normalizer_sup' {J R : Subgroup G} {k : G}
    (hJ : k ∈ Subgroup.normalizer (J : Set G)) (hR : k ∈ Subgroup.normalizer (R : Set G)) :
    k ∈ Subgroup.normalizer ((J ⊔ R : Subgroup G) : Set G) := by
  have key : ∀ (k : G), k ∈ Subgroup.normalizer (J : Set G) →
      k ∈ Subgroup.normalizer (R : Set G) → ∀ y ∈ J ⊔ R, k * y * k⁻¹ ∈ J ⊔ R := by
    intro k hJ hR
    have h1 : J ⊔ R ≤ (J ⊔ R).comap (MulAut.conj k).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hJ y).mp hy)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hR y).mp hy)
    intro y hy
    exact h1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key k hJ hR y hy, fun hy => ?_⟩
  have h := key k⁻¹ (inv_mem hJ) (inv_mem hR) _ hy
  simpa [mul_assoc] using h

theorem mem_normalizer_V {J R : Subgroup G} {k : G}
    (hJ : k ∈ Subgroup.normalizer (J : Set G)) (hR : k ∈ Subgroup.normalizer (R : Set G)) :
    k ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) :=
  normalizer_le_normalizer_omegaOneCenterOf _
    (normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_sup' hJ hR))

theorem le_normalizer_V (J R : Subgroup G) :
    J ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) :=
  fun _ hx => normalizer_le_normalizer_omegaOneCenterOf _
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (Subgroup.le_normalizer (Subgroup.mem_sup_left hx)))

theorem inf_pCoreOf_sup_le [Finite G] (J R : Subgroup G) :
    J ⊓ pCoreOf 2 (J ⊔ R) ≤ pCoreOf 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊔ R)).to_le inf_le_right)
  intro x hx
  exact SBc14.mem_normalizer_inf (Subgroup.le_normalizer hx)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ R) (Subgroup.mem_sup_left hx))

theorem oTwoZIn_le_of {L : Subgroup G} : oTwoZIn L ≤ L := by
  intro x hx
  obtain ⟨hxL, -⟩ := mem_oTwoZIn_iff.mp hx
  exact hxL

theorem pCoreOf_le_oTwoZIn {L : Subgroup G} : pCoreOf 2 L ≤ oTwoZIn L := by
  intro x hx
  have hxL : x ∈ L := pCoreOf_le 2 L hx
  refine mem_oTwoZIn_iff.mpr ⟨hxL, ?_⟩
  have h1 : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    rw [QuotientGroup.eq_one_iff, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1, Subgroup.mem_subgroupOf]
    exact hx
  rw [h1]
  exact one_mem _

theorem inf_centralizer_le_oTwoZIn [Finite G] {J R V : Subgroup G}
    (h : (J ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (J ⊔ R) ⊔ oTwoZIn J) :
    J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J := by
  intro x hx
  have hx' : x ∈ pCoreOf 2 (J ⊔ R) ⊔ oTwoZIn J := h ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hnorm : oTwoZIn J ≤ Subgroup.normalizer (pCoreOf 2 (J ⊔ R) : Set G) :=
    oTwoZIn_le_of.trans ((le_sup_left : J ≤ J ⊔ R).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊔ R)))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx'
  obtain ⟨o, ho, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  have hzJ : z ∈ J := oTwoZIn_le_of hz
  have hoJ : o ∈ J := by
    have : o = o * z * z⁻¹ := by group
    rw [this]
    exact mul_mem hx.1 (inv_mem hzJ)
  have ho2 : o ∈ oTwoZIn J := pCoreOf_le_oTwoZIn (inf_pCoreOf_sup_le J R ⟨hoJ, ho⟩)
  exact mul_mem ho2 hz

theorem isPGroup_pCore [Finite G] (J : Subgroup G) : IsPGroup 2 ↥(CFSG.pCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← SBc13.pCoreOf_subgroupOf_eq_pCore_J1 J]
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).comap_subtype (K := J)

theorem out5Inner_of_central_cover {X S : Type*} [Group X] [Group S] (hperf : commutator X = ⊤)
    (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)
    (hS : Out5Inner S) : Out5Inner X := by
  intro φ hφ
  have hcen : ∀ (θ : MulAut X) (x : X), θ x ∈ Subgroup.center X ↔ x ∈ Subgroup.center X := by
    intro θ x
    have h1 : ∀ θ : MulAut X, ∀ x ∈ Subgroup.center X, θ x ∈ Subgroup.center X := by
      intro θ x hx
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨y', rfl⟩ := θ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
    refine ⟨fun h => ?_, h1 θ x⟩
    have := h1 θ⁻¹ _ h
    simpa using this
  have hc : ∀ x, π (φ x) = 1 ↔ π x = 1 := by
    intro x
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker]
    exact hcen φ x
  obtain ⟨ψ, hψ⟩ := exists_mulAut_comp π hπ φ hc
  have hpow : ∀ (n : ℕ) (x : X), (ψ ^ n) (π x) = π ((φ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hψ, ih]
  have hψ5 : ψ ^ 5 = 1 := by
    ext s
    obtain ⟨x, rfl⟩ := hπ s
    rw [hpow, hφ]
    rfl
  obtain ⟨g, hg⟩ := hS ψ hψ5
  obtain ⟨ℓ, hℓ⟩ := hπ g
  refine ⟨ℓ, fun x => ?_⟩
  set θ : MulAut X := MulAut.conj ℓ⁻¹ * φ with hθ
  have hθx : ∀ x, θ x = ℓ⁻¹ * φ x * ℓ := by
    intro x
    simp [hθ]
  have hz : ∀ a : X, a * (θ a)⁻¹ ∈ Subgroup.center X := by
    intro a
    rw [← hker, MonoidHom.mem_ker, hθx, map_mul, map_inv, map_mul, map_mul, map_inv, ← hψ, hg,
      hℓ]
    group
  have h1 := eq_of_forall_mul_inv_mem_center hperf θ hz x
  rw [hθx] at h1
  calc φ x = ℓ * (ℓ⁻¹ * φ x * ℓ) * ℓ⁻¹ := by group
    _ = ℓ * x * ℓ⁻¹ := by rw [h1]

theorem out5Inner_isHat_alternating_six {X : Type} [Group X]
    (h : IsHat X (alternatingGroup (Fin 6))) : Out5Inner X := by
  obtain ⟨hq, -, ⟨e⟩⟩ := h
  refine out5Inner_of_central_cover hq.1.commutator_eq_top
    ((e : X ⧸ Subgroup.center X →* ↥(alternatingGroup (Fin 6))).comp
      (QuotientGroup.mk' (Subgroup.center X)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ (out5Inner_alternating (by norm_num))
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  change e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

end SBc17

end CFSG.Quasithin
