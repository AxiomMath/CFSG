module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rD
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

section Abstract

variable {K L : Type*} [Group K] [Group L]

theorem uc22s21ru3a_isCoatom_subgroupOf {G : Type*} [Group G] {T X : Subgroup G} (h : T ⋖ X) :
    IsCoatom (T.subgroupOf X) := by
  have hTX : T ≤ X := h.lt.le
  refine ⟨fun htop => h.lt.not_ge (Subgroup.subgroupOf_eq_top.mp htop), fun b hb => ?_⟩
  have hTb : T ≤ b.map X.subtype := fun t ht => ⟨⟨t, hTX ht⟩, hb.le ht, rfl⟩
  have hbX : (b.map X.subtype).subgroupOf X = b :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective b
  have hne : T ≠ b.map X.subtype := by
    intro heq
    apply hb.ne
    rw [heq, hbX]
  have hlt : T < b.map X.subtype := lt_of_le_of_ne hTb hne
  have hX : b.map X.subtype = X :=
    (Subgroup.map_subtype_le b).eq_of_not_lt (h.2 hlt)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (x : G) ∈ b.map X.subtype := by rw [hX]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem uc22s21ru3a_isCoatom_map (ρ : K →* L) (hρ : Function.Surjective ρ) {T' : Subgroup K}
    (hker : ρ.ker ≤ T') (h : IsCoatom T') : IsCoatom (T'.map ρ) := by
  have hcm : (T'.map ρ).comap ρ = T' := by
    rw [Subgroup.comap_map_eq, sup_eq_left.2 hker]
  refine ⟨fun htop => h.1 ?_, fun b hb => ?_⟩
  · rw [← hcm, htop, Subgroup.comap_top]
  · have hlt : T' < b.comap ρ := by
      rw [← hcm]
      exact (Subgroup.comap_lt_comap_of_surjective hρ).2 hb
    have hb' := h.2 _ hlt
    rw [← Subgroup.map_comap_eq_self_of_surjective hρ b, hb', Subgroup.map_top,
      ρ.range_eq_top_of_surjective hρ]

variable {W : Type*} [Group W]

theorem uc22s21ru3a_piece {q : ℕ} {S R : Subgroup W} (hS : IsCoatom S) (hR : R.Normal)
    (hR0 : R ≠ ⊥) (hq : IsPGroup q ↥R) (hdisj : Disjoint R S) :
    R ⊔ S = ⊤ ∧ IsPiece q S R := by
  have hinf : R ⊓ S = ⊥ := disjoint_iff.mp hdisj
  have hRS : R ⊔ S = ⊤ := by
    rcases hS.le_iff.1 (le_sup_right : S ≤ R ⊔ S) with h | h
    · exact h
    · exfalso
      apply hR0
      rw [eq_bot_iff, ← hinf]
      exact le_inf le_rfl (le_sup_left.trans h.le)
  refine ⟨hRS, hR0, hq, by rw [Subgroup.normalizer_eq_top]; exact le_top, fun Z hZR hZS => ?_⟩
  rcases hS.le_iff.1 (le_sup_right : S ≤ Z ⊔ S) with h | h
  · right
    refine le_antisymm hZR fun n hn => ?_
    have hn' : n ∈ ((Z ⊔ S : Subgroup W) : Set W) := by rw [h]; exact Subgroup.mem_top n
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z S hZS] at hn'
    obtain ⟨z, hz, s, hs, rfl⟩ := hn'
    have hsR : s ∈ R := by
      have : z⁻¹ * (z * s) ∈ R := R.mul_mem (R.inv_mem (hZR hz)) hn
      simpa using this
    have hs1 : s = 1 := by
      have : s ∈ R ⊓ S := ⟨hsR, hs⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.1 this
    simpa [hs1] using hz
  · left
    have : Z ≤ R ⊓ S := le_inf hZR (le_sup_left.trans h.le)
    rw [hinf] at this
    exact this.trans bot_le

end Abstract

section Exists

variable {X : Type*} [Group X] [Finite X]

theorem uc22s21ru3a_exists_piece (hX : Group.IsSolvable X) {T' : Subgroup X}
    (hT2 : IsPGroup 2 ↥T') (hcoat : IsCoatom T') (hK : CFSG.pCore 2 X ≤ T') :
    ∃ (q : ℕ) (R : Subgroup (X ⧸ CFSG.pCore 2 X)), q.Prime ∧ q ≠ 2 ∧ R.Normal ∧
      R.comap (QuotientGroup.mk' (CFSG.pCore 2 X)) ⊔ T' = ⊤ ∧
      IsPiece q (T'.map (QuotientGroup.mk' (CFSG.pCore 2 X))) R := by
  classical
  haveI := hX
  set ρ : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker ≤ T' := by
    rw [hρ, QuotientGroup.ker_mk']
    exact hK
  have hS : IsCoatom (T'.map ρ) := uc22s21ru3a_isCoatom_map ρ hρs hker hcoat
  have h2 : IsPGroup 2 ↥(T'.map ρ) := hT2.map ρ
  haveI : Nontrivial (X ⧸ CFSG.pCore 2 X) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hS.1 (eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 1]; exact one_mem _)
  have hO : ∀ Q : Subgroup (X ⧸ CFSG.pCore 2 X), Q.Normal → IsPGroup 2 ↥Q → Q = ⊥ := by
    intro Q hQn hQp
    have h1 : Q ≤ CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) := le_sSup ⟨hQn, hQp⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := X) (p := 2)] at h1
    exact le_bot_iff.1 h1
  obtain ⟨r, N, hr, hrodd, hNn, hN1, -, hNr⟩ :=
    CFSG.Quasithin.B1.exists_normal_elem_abelian_odd inferInstance inferInstance hO
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  have hNp : IsPGroup r ↥N := fun g => ⟨1, Subtype.ext (by simpa using hNr g.1 g.2)⟩
  have hdisj : Disjoint N (T'.map ρ) := IsPGroup.disjoint_of_ne r 2 hr2 N _ hNp h2
  obtain ⟨hNS, hpiece⟩ := uc22s21ru3a_piece hS hNn hN1 hNp hdisj
  refine ⟨r, N, hr, hr2, hNn, ?_, hpiece⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : ρ x ∈ ((N ⊔ T'.map ρ : Subgroup _) : Set _) := by
    rw [hNS]
    exact Subgroup.mem_top _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N (T'.map ρ)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)] at hx
  obtain ⟨n, hn, s, ⟨t, ht, rfl⟩, hns⟩ := hx
  have hxt : x * t⁻¹ ∈ N.comap ρ := by
    rw [Subgroup.mem_comap, map_mul, map_inv, ← hns]
    simpa using hn
  simpa using Subgroup.mul_mem_sup hxt ht

end Exists

section LemmaD

variable {G : Type} [Group G] [Finite G]

theorem uc22s21ru3a_le_or_le {X T H₁ H₂ : Subgroup G} (hTX : IsSylowIn 2 T X) (hcov : T ⋖ X)
    (hsol : Group.IsSolvable ↥X) (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hH : F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) :
    X ≤ H₁ ∨ X ≤ H₂ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowIn 2 (T.subgroupOf X) ⊤ := uc22s21rd_isSylowIn_subgroupOf hTX
  have hK : CFSG.pCore 2 ↥X ≤ T.subgroupOf X :=
    CFSG.pCore_isPGroup.le_sylow_of_normal hTX.toSylow
  obtain ⟨q, R, hq, hq2, hRn, hPT, hR0, hRq, -, hirr⟩ :=
    uc22s21ru3a_exists_piece hsol hS.isPGroup (uc22s21ru3a_isCoatom_subgroupOf hcov) hK
  haveI := hRn
  refine uc22s21rd_le_or_le hq hq2 hTX hT₁ hT₂ hH (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
    (by rw [QuotientGroup.ker_mk']) hR0 hRq ?_ ?_ hPT hirr
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact le_top

end LemmaD

end CFSG.LocalAnalysis.UniquenessCase.UC22
