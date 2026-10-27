module

public import CFSG.Quasithin.Background.Harris.KFact2d.F4Setup
public import CFSG.Quasithin.Background.Harris.KFact2d.CaseIIBasic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inverts_of_F4 (hF4 : F4Stmt) {K Q D K0 J : Subgroup G} {X : Type} [Group X]
    (π : ↥K →* X) (Ks : Subgroup X) {p : ℕ}
    (hQK : K ≤ Subgroup.normalizer (Q : Set G)) (hQleK : Q ≤ K) (hDK : D ≤ K)
    (hDn : K ≤ Subgroup.normalizer (D : Set G)) (hD : D = K0 ⊔ Q) (hK0K : K0 ≤ K)
    (hperf : ⁅K0, K0⁆ = K0)
    (hJ : ∀ x, x ∈ J ↔ x ∈ D ∧ ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Q) (hQJ : Q ≤ J)
    (hker : π.ker = J.subgroupOf K) (hKs : (D.subgroupOf K).map π = Ks)
    (hcent : Subgroup.centralizer (Ks : Set X) = ⊥)
    (hodd : ∀ y ∈ J, (∃ k : ℕ, y ^ 2 ^ k ∈ Q) → y ∈ Q)
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : IsL3U3 p ↥Ks)
    {v : G} (hvK : v ∈ K) (hv2 : v * v = 1) (hvKs : π ⟨v, hvK⟩ ∉ Ks) :
    ∀ j ∈ J, v * j * v⁻¹ * j ∈ Q := by
  haveI hQN : (Q.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hQK
  haveI hDN : (D.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hDn
  haveI hDbN : (Dbar K Q D).Normal := Subgroup.Normal.map hDN _ (QuotientGroup.mk'_surjective _)
  have hJK : J ≤ K := fun x hx => hDK ((hJ x).mp hx).1
  have hQker : Q.subgroupOf K ≤ π.ker := by
    rw [hker]
    exact Subgroup.subgroupOf_mono K hQJ
  let lam : (↥K ⧸ Q.subgroupOf K) →* X := QuotientGroup.lift (Q.subgroupOf K) π hQker
  have hlam : ∀ x : ↥K, lam (psi K Q x) = π x := fun x => rfl
  let lamE : ↥(Dbar K Q D) →* X := lam.comp (Dbar K Q D).subtype
  have hrange : lamE.range = Ks := by
    rw [← hKs]
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      obtain ⟨d, hd, hdK, hde⟩ := mem_Dbar.mp e.2
      refine ⟨⟨d, hdK⟩, Subgroup.mem_subgroupOf.mpr hd, ?_⟩
      show π ⟨d, hdK⟩ = lam e.1
      rw [← hde]
      rfl
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨psi K Q y, psi_mem_Dbar (Subgroup.mem_subgroupOf.mp hy) y.2⟩, rfl⟩
  have hkerE : lamE.ker = Subgroup.center ↥(Dbar K Q D) := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, hdK, hde⟩ := mem_Dbar.mp e.2
      have h1 : π ⟨d, hdK⟩ = 1 := by
        have : lam e.1 = 1 := he
        rw [← hde] at this
        exact this
      have hdJ : d ∈ J := by
        have : (⟨d, hdK⟩ : ↥K) ∈ π.ker := h1
        rw [hker] at this
        exact Subgroup.mem_subgroupOf.mp this
      have hc := psi_mem_center hJ hDK hdJ hdK
      have : (⟨psi K Q ⟨d, hdK⟩, psi_mem_Dbar hd hdK⟩ : ↥(Dbar K Q D)) = e :=
        Subtype.ext hde
      rwa [this] at hc
    · intro he
      obtain ⟨j, hj, hjK, hje⟩ := center_le_J hJ hDK e he
      show lam e.1 = 1
      rw [← hje]
      have : (⟨j, hjK⟩ : ↥K) ∈ π.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr hj
      exact this
  have eqv : (↥(Dbar K Q D) ⧸ Subgroup.center ↥(Dbar K Q D)) ≃* ↥Ks :=
    (QuotientGroup.quotientMulEquivOfEq hkerE).symm.trans
      ((QuotientGroup.quotientKerEquivRange lamE).trans (MulEquiv.subgroupCongr hrange))
  have hL' : IsL3U3 p (↥(Dbar K Q D) ⧸ Subgroup.center ↥(Dbar K Q D)) :=
    isL3U3_of_mulEquiv eqv hL
  set w : ↥K ⧸ Q.subgroupOf K := psi K Q ⟨v, hvK⟩ with hw
  have hww : w * w = 1 := by
    rw [hw, ← map_mul]
    have : (⟨v, hvK⟩ : ↥K) * ⟨v, hvK⟩ = 1 := Subtype.ext hv2
    rw [this, map_one]
  let v' : MulAut ↥(Dbar K Q D) := MulAut.conjNormal w
  have hv'2 : v' * v' = 1 := by
    show MulAut.conjNormal w * MulAut.conjNormal w = 1
    rw [← map_mul, hww, map_one]
  have hnot : ¬ ∃ g : ↥(Dbar K Q D), ∀ x : ↥(Dbar K Q D),
      v' x * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center ↥(Dbar K Q D) := by
    rintro ⟨g, hg⟩
    apply hvKs
    have hrg : lamE g ∈ Ks := hrange ▸ ⟨g, rfl⟩
    have hcen : (lam w)⁻¹ * lamE g ∈ Subgroup.centralizer (Ks : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hrange ▸ hy
      have h1 := hg x
      rw [← hkerE, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      have h2 : lamE (v' x) = lam w * lamE x * (lam w)⁻¹ := by
        show lam ((MulAut.conjNormal w x : ↥(Dbar K Q D)) : ↥K ⧸ Q.subgroupOf K) = _
        rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
        rfl
      have h3 : lamE (g * x * g⁻¹) = lamE g * lamE x * (lamE g)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [h2, h3] at h1
      calc lamE x * ((lam w)⁻¹ * lamE g)
          = (lam w)⁻¹ * (lam w * lamE x * (lam w)⁻¹) * lamE g := by group
        _ = (lam w)⁻¹ * (lamE g * lamE x * (lamE g)⁻¹) * lamE g := by rw [h1]
        _ = (lam w)⁻¹ * lamE g * lamE x := by group
    rw [hcent, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    have : π ⟨v, hvK⟩ = lamE g := hcen
    rw [this]
    exact hrg
  have hF := hF4 (↥(Dbar K Q D)) p hp hp2 (commutator_Dbar_eq_top hK0K hperf hD hQK hQleK)
    (odd_card_center hJ hDK hodd) hL' v' hv'2 hnot
  intro j hj
  have hjK : j ∈ K := hJK hj
  have hcj := hF _ (psi_mem_center hJ hDK hj hjK)
  have hconj : w * psi K Q ⟨j, hjK⟩ * w⁻¹ = (psi K Q ⟨j, hjK⟩)⁻¹ := by
    have := congrArg Subtype.val hcj
    simp only [v', MulAut.conjNormal_apply, Subgroup.coe_inv] at this
    exact this
  have h1 : psi K Q ((⟨v, hvK⟩ : ↥K) * ⟨j, hjK⟩ * (⟨v, hvK⟩ : ↥K)⁻¹ * ⟨j, hjK⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, ← hw, hconj, inv_mul_cancel]
  have h2 : ((⟨v, hvK⟩ : ↥K) * ⟨j, hjK⟩ * (⟨v, hvK⟩ : ↥K)⁻¹ * ⟨j, hjK⟩) ∈ Q.subgroupOf K :=
    (QuotientGroup.eq_one_iff _).mp h1
  simpa using Subgroup.mem_subgroupOf.mp h2

end CFSG.Quasithin.Background.Harris.KFact2d
