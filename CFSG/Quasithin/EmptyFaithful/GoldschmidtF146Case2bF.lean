module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bD
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bE

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Dict

variable {G : Type} [Group G] {M H K : Subgroup G}

@[expose] def rho (M : Subgroup G) (hKH : K ≤ H) : ↥K →* E2.StarQuot M H :=
  (E2.star M H K).subtype.comp (Case2a.starHom hKH)

@[expose] def Khat (M : Subgroup G) (hKH : K ≤ H) (P : Subgroup (E2.StarQuot M H)) : Subgroup G :=
  (P.comap (rho M hKH)).map K.subtype

theorem rho_apply (hKH : K ≤ H) (x : ↥K) :
    rho M hKH x = ((Subgroup.inclusion hKH x : ↥H) : E2.StarQuot M H) := rfl

variable {hKH : K ≤ H} {P : Subgroup (E2.StarQuot M H)}

theorem mem_Khat {x : G} :
    x ∈ Khat M hKH P ↔ ∃ hx : x ∈ K, ((⟨x, hKH hx⟩ : ↥H) : E2.StarQuot M H) ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Khat_le : Khat M hKH P ≤ K := Subgroup.map_subtype_le _

theorem range_rho : (rho M hKH).range = E2.star M H K := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (Case2a.starHom hKH x).2
  · intro hy
    obtain ⟨x, hx⟩ := Case2a.starHom_surjective hKH ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem star_map_subtype (X : Subgroup ↥K) :
    E2.star M H (X.map K.subtype) = X.map (rho M hKH) := by
  ext y
  constructor
  · intro hy
    obtain ⟨h, ⟨k, hk, hkh⟩, rfl⟩ := Case2a.exists_of_mem_star hy
    refine ⟨k, hk, ?_⟩
    rw [rho_apply]
    congr 1
    exact Subtype.ext hkh
  · rintro ⟨k, hk, rfl⟩
    exact GoldS146R.mem_imgJ.mpr ⟨Subgroup.inclusion hKH k, ⟨k, hk, rfl⟩, rfl⟩

variable [Finite G]

theorem star_perfectCore_Khat (hP : P ≤ E2.star M H K) :
    E2.star M H (perfectCore (Khat M hKH P)) = perfectCore P := by
  have h1 : perfectCore (Khat M hKH P) = (perfectCore (P.comap (rho M hKH))).map K.subtype :=
    (map_perfectCore K.subtype _).symm
  rw [h1, star_map_subtype (hKH := hKH), map_perfectCore, Subgroup.map_comap_eq, range_rho,
    inf_eq_right.mpr hP]

omit [Finite G] in
theorem mem_normalizer_perfectCore_Khat {g : G} (hgH : g ∈ H)
    (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgP : ((⟨g, hgH⟩ : ↥H) : E2.StarQuot M H) ∈
      Subgroup.normalizer (P : Set (E2.StarQuot M H))) :
    g ∈ Subgroup.normalizer (perfectCore (Khat M hKH P) : Set G) := by
  have key : ∀ (g : G) (hgH : g ∈ H), g ∈ Subgroup.normalizer (K : Set G) →
      ((⟨g, hgH⟩ : ↥H) : E2.StarQuot M H) ∈ Subgroup.normalizer (P : Set (E2.StarQuot M H)) →
      ∀ x, x ∈ Khat M hKH P → g * x * g⁻¹ ∈ Khat M hKH P := by
    intro g hgH hgK hgP x hx
    obtain ⟨hxK, hxP⟩ := mem_Khat.mp hx
    refine mem_Khat.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgK x).mp hxK, ?_⟩
    have e : ((⟨g * x * g⁻¹, H.mul_mem (H.mul_mem hgH (hKH hxK)) (H.inv_mem hgH)⟩ : ↥H) :
        E2.StarQuot M H) = ((⟨g, hgH⟩ : ↥H) : E2.StarQuot M H) *
          ((⟨x, hKH hxK⟩ : ↥H) : E2.StarQuot M H) * ((⟨g, hgH⟩ : ↥H) : E2.StarQuot M H)⁻¹ := rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgP _).mp hxP
  refine normalizer_le_normalizer_perfectCore _ ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hgH hgK hgP x, fun h => ?_⟩
  have hgi : ((⟨g⁻¹, H.inv_mem hgH⟩ : ↥H) : E2.StarQuot M H) ∈
      Subgroup.normalizer (P : Set (E2.StarQuot M H)) := by
    have : ((⟨g⁻¹, H.inv_mem hgH⟩ : ↥H) : E2.StarQuot M H) =
        ((⟨g, hgH⟩ : ↥H) : E2.StarQuot M H)⁻¹ := rfl
    rw [this]
    exact inv_mem hgP
  have := key g⁻¹ (H.inv_mem hgH) (inv_mem hgK) hgi _ h
  simpa [mul_assoc] using this


end Dict

section Perm

variable {Y : Type} [Group Y] {L U : Subgroup Y} {m : ℕ} {F : Type} [Field F]
  {P : Fin 2 → Subgroup Y}

theorem conj_mem_pair (hP : ParabData m L U F P) {y : Y}
    (hyL : y ∈ Subgroup.normalizer (L : Set Y)) (hyU : y ∈ Subgroup.normalizer (U : Set Y))
    (j : Fin 2) : ∃ k : Fin 2, B6.conjSub y (P j) = P k := by
  have hL : B6.conjSub y L = L := B6.conjSub_eq_self hyL
  have hU : B6.conjSub y U = U := B6.conjSub_eq_self hyU
  have hUA : U ≤ B6.conjSub y (P j) := by
    rw [← hU]
    exact (B6.conjSub y).monotone (hP.sylow_le j)
  have hAL : B6.conjSub y (P j) ≤ L := by
    rw [← hL]
    exact (B6.conjSub y).monotone (hP.le j)
  have hcov : B6.conjSub y (P j) ⋖ L := by
    have h := (hP.max (P j) (hP.sylow_le j) (hP.le j)).2 ⟨j, rfl⟩
    have := (apply_covBy_apply_iff (B6.conjSub y)).2 h
    rwa [hL] at this
  obtain ⟨k, hk⟩ := (hP.max _ hUA hAL).1 hcov
  exact ⟨k, hk⟩

theorem fix_or_swap (hP : ParabData m L U F P) {y : Y}
    (hyL : y ∈ Subgroup.normalizer (L : Set Y)) (hyU : y ∈ Subgroup.normalizer (U : Set Y)) :
    (B6.conjSub y (P 1) = P 1 ∧ B6.conjSub y (P 0) = P 0) ∨
      (B6.conjSub y (P 1) = P 0 ∧ B6.conjSub y (P 0) = P 1) := by
  obtain ⟨k1, h1⟩ := conj_mem_pair hP hyL hyU 1
  obtain ⟨k0, h0⟩ := conj_mem_pair hP hyL hyU 0
  fin_cases k1 <;> fin_cases k0
  · exact absurd ((B6.conjSub y).injective (h1.trans h0.symm)) (Ne.symm hP.ne)
  · exact Or.inr ⟨h1, h0⟩
  · exact Or.inl ⟨h1, h0⟩
  · exact absurd ((B6.conjSub y).injective (h1.trans h0.symm)) (Ne.symm hP.ne)

theorem not_perfectCore_le_inf [Finite Y] [Finite F] (hP : ParabData m L U F P) (hm : 2 ≤ m) :
    ¬ perfectCore (P 1) ≤ P 0 ⊓ P 1 := by
  intro hle
  obtain ⟨g, hg, -⟩ := hP.levi 1
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hP.card
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian
    (exists_four hm hP.card)
  have h1 : Nontrivial SL(2, F) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (Subsingleton.elim _ _)
  have h2 : Nontrivial ↥(perfectCore (P 1)) := hg.nontrivial
  have h3 : Group.IsPerfect ↥(perfectCore (P 1)) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have h4 : Group.IsSolvable ↥(perfectCore (P 1)) :=
    have := hP.solv
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable _ h4

end Perm

end CFSG.Quasithin.F146Field.Case2b
