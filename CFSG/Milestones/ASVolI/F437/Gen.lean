module

public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.Milestones.ASVolI.F4Sylow
public import CFSG.Milestones.ASVolI.F431.BCoreGenQ

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Basic

variable {E : Type} [Group E]

theorem burnsideF437_not_mem_Gp [Finite E] {Gp R : Subgroup E} {fb : E}
    (hsyl : ChF.IsSylowOf 2 R (cenIn Gp fb)) (hR : fb ∉ R) (hsq : fb * fb = 1) : fb ∉ Gp := by
  intro hfG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfC : fb ∈ cenIn Gp fb := ⟨hfG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcen : Subgroup.centralizer ({fb} : Set E) =
      Subgroup.centralizer ((Subgroup.zpowers fb : Subgroup E) : Set E) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hle : Subgroup.zpowers fb ≤ pCoreOf 2 (cenIn Gp fb) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.zpowers_le (H := cenIn Gp fb)).mpr hfC) ?_ ?_
    · intro x hx
      have hx' : x ∈ Subgroup.centralizer ((Subgroup.zpowers fb : Subgroup E) : Set E) :=
        hcen ▸ hx.2
      exact Subgroup.centralizer_le_normalizer _ hx'
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      refine orderOf_eq_prime (by rw [sq]; exact hsq) ?_
      rintro rfl
      exact hR R.one_mem
  exact hR ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl) (hle (Subgroup.mem_zpowers fb)))

theorem burnsideF437_ne_one {R : Subgroup E} {fb : E} (hR : fb ∉ R) : fb ≠ 1 := by
  rintro rfl
  exact hR R.one_mem

theorem burnsideF437_conj_mem {Gp : Subgroup E} [Gp.Normal] {fb : E} :
    ∀ e ∈ Subgroup.centralizer ({fb} : Set E), ∀ d ∈ cenIn Gp fb, e * d * e⁻¹ ∈ cenIn Gp fb := by
  intro e he d hd
  refine ⟨Subgroup.Normal.conj_mem inferInstance d hd.1 e, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ he hd.2) (Subgroup.inv_mem _ he)

theorem burnsideF437_zpowers_le {Gp : Subgroup E} {fb : E} :
    Subgroup.zpowers fb ≤
      Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) ⊓
        Subgroup.centralizer ({fb} : Set E) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact (Subgroup.mem_centralizer_singleton_iff.mp hd.2)

end Basic

section Completion

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF437_phi_eq (β : Cpl M₁ M₂ Y) (c : ↥(M₁ ⊓ M₂)) :
    β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c) = β.φ2 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c) :=
  (β.comm1 c).trans (β.comm2 c).symm

theorem burnsideF437_common (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {a : ↥M₁} {b : ↥M₂}
    (hab : β.φ1 a = β.φ2 b) :
    ∃ c : ↥(M₁ ⊓ M₂), (c : E) = a ∧ (c : E) = b := by
  have hmem : β.φ1 a ∈ β.φ1.range ⊓ β.φ2.range := ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
  rw [β.inter] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_, ?_⟩
  · have h1 : β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c) = β.φ1 a := (β.comm1 c).trans hc
    have := hβ.1 h1
    exact congrArg Subtype.val this
  · have h2 : β.φ2 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c) = β.φ2 b :=
      (β.comm2 c).trans (hc.trans hab)
    have := hβ.2.2 h2
    exact congrArg Subtype.val this

theorem burnsideF437_inter_map (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (Gp : Subgroup E) (fb : E) :
    ((f437DbarOne Gp M₁ fb).subgroupOf M₁).map (f1 (c := β)) ⊓
        ((f437DbarTwo Gp M₂ fb).subgroupOf M₂).map (f2 (c := β)) =
      ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb).subgroupOf (M₁ ⊓ M₂)).map (bmap β) := by
  apply le_antisymm
  · rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have hab' : β.φ1 a = β.φ2 b := by
      have := congrArg Subtype.val hab
      simpa using this.symm
    obtain ⟨c, hca, hcb⟩ := burnsideF437_common β hβ hab'
    have ha' : ((show ↥M₁ from a) : E) ∈ f437DbarOne Gp M₁ fb := ha
    refine ⟨c, ?_, ?_⟩
    · show (c : E) ∈ cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb
      refine ⟨⟨?_, c.2⟩, ?_⟩
      · rw [hca]; exact ha'.1.1
      · rw [hca]; exact ha'.2
    · apply Subtype.ext
      show β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c) = β.φ1 a
      congr 1
      exact Subtype.ext hca
  · rintro x ⟨c, hc, rfl⟩
    have hc' : (c : E) ∈ cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb := hc
    refine ⟨⟨(RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c, ?_, rfl⟩,
      ⟨(RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c, ?_, ?_⟩⟩
    · show (c : E) ∈ f437DbarOne Gp M₁ fb
      exact ⟨⟨hc'.1.1, hc'.1.2.1⟩, hc'.2⟩
    · show (c : E) ∈ f437DbarTwo Gp M₂ fb
      exact ⟨⟨hc'.1.1, hc'.1.2.2⟩, hc'.2⟩
    · apply Subtype.ext
      exact (burnsideF437_phi_eq β c).symm

@[expose] def burnsideF437_mid {Gp : Subgroup E} {fb : E}
    (g : ↥(f437DbarOne Gp M₁ fb ⊓ f437DbarTwo Gp M₂ fb)) : ↥(M₁ ⊓ M₂) :=
  ⟨(g : E), g.2.1.1.2, g.2.2.1.2⟩

theorem burnsideF437_map_range_codRestrict {A : Type} [Group A] (f : A →* Y) (S : Subgroup Y)
    (h : ∀ a, f a ∈ S) : ((f.codRestrict S h).range).map S.subtype = f.range := by
  rw [MonoidHom.map_range]
  rfl

theorem burnsideF437_left_mem (β : Cpl M₁ M₂ Y) (Gp : Subgroup E) (fb : E)
    (a : ↥(f437DbarOne Gp M₁ fb)) : f437Left Gp β fb a ∈ f437D Gp β fb :=
  Subgroup.mem_sup_left ⟨a, rfl⟩

theorem burnsideF437_right_mem (β : Cpl M₁ M₂ Y) (Gp : Subgroup E) (fb : E)
    (a : ↥(f437DbarTwo Gp M₂ fb)) : f437Right Gp β fb a ∈ f437D Gp β fb :=
  Subgroup.mem_sup_right ⟨a, rfl⟩

noncomputable def burnsideF437_restriction (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (Gp : Subgroup E) (fb : E) : (f437Delta Gp M₁ M₂ fb).Completion (f437D Gp β fb) where
  φ1 := (f437Left Gp β fb).codRestrict _ (burnsideF437_left_mem β Gp fb)
  φ12 := ((f437Left Gp β fb).comp (f437Delta Gp M₁ M₂ fb).α1).codRestrict _
    (fun a => burnsideF437_left_mem β Gp fb _)
  φ2 := (f437Right Gp β fb).codRestrict _ (burnsideF437_right_mem β Gp fb)
  comm1 _ := rfl
  comm2 g := by
    apply Subtype.ext
    exact (burnsideF437_phi_eq β (burnsideF437_mid (Gp := Gp) (fb := fb) g)).symm
  inter := by
    apply le_antisymm
    · rintro y ⟨⟨a, rfl⟩, ⟨b, hab⟩⟩
      have hab' : β.φ1 (Subgroup.inclusion
            ((inf_le_left : (Gp ⊓ M₁) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₁).trans
              inf_le_right) a) =
          β.φ2 (Subgroup.inclusion
            ((inf_le_left : (Gp ⊓ M₂) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₂).trans
              inf_le_right) b) := by
        have := congrArg Subtype.val hab
        exact this.symm
      obtain ⟨c, hca, hcb⟩ := burnsideF437_common β hβ hab'
      have hcD1 : (c : E) ∈ f437DbarOne Gp M₁ fb := by
        rw [hca]; exact a.2
      have hcD2 : (c : E) ∈ f437DbarTwo Gp M₂ fb := by
        rw [hcb]; exact b.2
      refine ⟨(⟨c, hcD1, hcD2⟩ : ↥(f437DbarOne Gp M₁ fb ⊓ f437DbarTwo Gp M₂ fb)), ?_⟩
      apply Subtype.ext
      show β.φ1 _ = β.φ1 _
      congr 1
      exact Subtype.ext hca
    · rintro y ⟨g, rfl⟩
      refine ⟨⟨(f437Delta Gp M₁ M₂ fb).α1 g, rfl⟩, ⟨(f437Delta Gp M₁ M₂ fb).α2 g, ?_⟩⟩
      apply Subtype.ext
      exact (burnsideF437_phi_eq β (burnsideF437_mid (Gp := Gp) (fb := fb) g)).symm
  gen := by
    apply Subgroup.map_injective (f437D Gp β fb).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype]
    exact congrArg₂ (· ⊔ ·) (burnsideF437_map_range_codRestrict _ _ _)
      (burnsideF437_map_range_codRestrict _ _ _)

theorem burnsideF437_restriction_faithful (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (Gp : Subgroup E) (fb : E) : (burnsideF437_restriction β hβ Gp fb).IsFaithful := by
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h : β.φ1 (Subgroup.inclusion
          ((inf_le_left : (Gp ⊓ M₁) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₁).trans
            inf_le_right) a) =
        β.φ1 (Subgroup.inclusion
          ((inf_le_left : (Gp ⊓ M₁) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₁).trans
            inf_le_right) b) := congrArg Subtype.val hab
    exact Subgroup.inclusion_injective _ (hβ.1 h)
  · have h : β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 (burnsideF437_mid (Gp := Gp) (fb := fb) a)) =
        β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 (burnsideF437_mid (Gp := Gp) (fb := fb) b)) :=
      congrArg Subtype.val hab
    have h1 := congrArg Subtype.val (hβ.1 h)
    exact Subtype.ext h1
  · have h : β.φ2 (Subgroup.inclusion
          ((inf_le_left : (Gp ⊓ M₂) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₂).trans
            inf_le_right) a) =
        β.φ2 (Subgroup.inclusion
          ((inf_le_left : (Gp ⊓ M₂) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ Gp ⊓ M₂).trans
            inf_le_right) b) := congrArg Subtype.val hab
    exact Subgroup.inclusion_injective _ (hβ.2.2 h)

theorem burnsideF437_restriction_exists (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (Gp : Subgroup E) (fb : E) :
    ∃ restriction : (f437Delta Gp M₁ M₂ fb).Completion (f437D Gp β fb),
      restriction.IsFaithful ∧
      (∀ generator, (restriction.φ1 generator : Y) = f437Left Gp β fb generator) ∧
      (∀ generator, (restriction.φ2 generator : Y) = f437Right Gp β fb generator) ∧
      (∀ edge, (restriction.φ12 edge : Y) =
        f437Left Gp β fb ((f437Delta Gp M₁ M₂ fb).α1 edge)) :=
  ⟨burnsideF437_restriction β hβ Gp fb, burnsideF437_restriction_faithful β hβ Gp fb,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end Completion

section Sylow

variable {E : Type} [Group E]

theorem burnsideF437_conjSub_eq_iff {g : E} {H : Subgroup E} :
    conjSub g H = H ↔ g ∈ Subgroup.normalizer (H : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ conjSub g H := mul_mem_conjSub hx
      rwa [h] at this
    · intro hx
      rw [← h, mem_conjSub] at hx
      simpa [mul_assoc] using hx
  · intro h
    ext x
    rw [mem_conjSub, h (g⁻¹ * x * g)]
    simp [mul_assoc]

theorem burnsideF437_mem_normalizer_inf {g : E} {A B : Subgroup E}
    (hA : g ∈ Subgroup.normalizer (A : Set E)) (hB : g ∈ Subgroup.normalizer (B : Set E)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup E) : Set E) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem burnsideF437_card_conjSub (g : E) (H : Subgroup E) :
    Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem burnsideF437_conjSub_normal {Gp : Subgroup E} [Gp.Normal] (g : E) : conjSub g Gp = Gp :=
  burnsideF437_conjSub_eq_iff.mpr (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top g)

theorem burnsideF437_sylow_sbar [Finite E] {Gp B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics 2 Gp B P₁ P₂) :
    ChF.IsSylowOf 2 (pCoreOf 2 B) Gp ∧ B = Gp ⊓ Subgroup.normalizer (pCoreOf 2 B : Set E) := by
  obtain ⟨S, hS, hBS⟩ := burnsideF45_pCoreOf_eq_of_isLieParabolics Nat.prime_two hP
  obtain ⟨⟨S', hS', hB⟩, -⟩ := hP
  have hSS' : S = S' := by
    have hS'B : S' ≤ B := by rw [hB]; exact le_inf hS'.1 Subgroup.le_normalizer
    have hBN : B ≤ Subgroup.normalizer (S' : Set E) := by rw [hB]; exact inf_le_right
    have h1 : S' ≤ pCoreOf 2 B :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS'B hBN hS'.2.1
    rw [hBS] at h1
    obtain ⟨x, -, hx⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hS' hS.1 hS.2.1
    have h2 : Nat.card S ≤ Nat.card S' := by
      have := Subgroup.card_le_of_le hx
      rwa [burnsideF437_card_conjSub] at this
    exact (Subgroup.eq_of_le_of_card_ge h1 h2).symm
  rw [hBS]
  exact ⟨hS, hSS' ▸ hB⟩

theorem burnsideF437_normalizer_sbar_le [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hB : Gp ⊓ (M₁ ⊓ M₂) =
      Gp ⊓ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E)) :
    Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) ≤ M₁ ⊓ M₂ := by
  intro e he
  obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
  have hhN : h ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (burnsideF4m_mem_normalizer_inf (Gp := Gp) hh)
  have hnN : n ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) := by
    have := (Subgroup.normalizer _).mul_mem he ((Subgroup.normalizer _).inv_mem hhN)
    simpa using this
  have hnB : n ∈ Gp ⊓ (M₁ ⊓ M₂) := by rw [hB]; exact ⟨hn, hnN⟩
  exact (M₁ ⊓ M₂).mul_mem hnB.2 hh

theorem burnsideF437_normalizer_le_of_unique [Finite E] {Gp M₁ M₂ R : Subgroup E} [Gp.Normal]
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hB : Gp ⊓ (M₁ ⊓ M₂) =
      Gp ⊓ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E))
    (hsyl : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp)
    (hRS : R ≤ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (huniq : ∀ S : Subgroup E, ChF.IsSylowOf 2 S Gp → R ≤ S → S = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :
    Subgroup.normalizer (R : Set E) ≤ M₁ ⊓ M₂ := by
  intro g hg
  refine burnsideF437_normalizer_sbar_le hsplit hB ?_
  rw [← burnsideF437_conjSub_eq_iff]
  refine huniq _ ?_ ?_
  · have := CFSG.Quasithin.F7.isSylowTwoOf_conj hsyl g
    rw [burnsideF437_conjSub_normal (Gp := Gp) g] at this
    exact this
  · rw [← burnsideF437_conjSub_eq_iff.mpr hg]
    exact conjSub_mono g hRS

theorem burnsideF437_frattini [Finite E] {Gp M₁ M₂ R : Subgroup E} [Gp.Normal] {fb : E}
    (hsyl : ChF.IsSylowOf 2 R (cenIn Gp fb))
    (hRN : Subgroup.normalizer (R : Set E) ≤ M₁ ⊓ M₂) :
    ∀ e ∈ Subgroup.centralizer ({fb} : Set E), ∃ d ∈ cenIn Gp fb,
      ∃ h ∈ Subgroup.centralizer ({fb} : Set E) ⊓ (M₁ ⊓ M₂), e = d * h := by
  intro e he
  have hle : conjSub e R ≤ cenIn Gp fb := by
    intro x hx
    rw [mem_conjSub] at hx
    have := burnsideF437_conj_mem e he _ (hsyl.1 hx)
    simpa [mul_assoc] using this
  obtain ⟨d, hd, hdle⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hsyl hle
    (CFSG.Quasithin.F7.isPGroup_conjSub hsyl.2.1)
  have heq : conjSub e R = conjSub d R :=
    Subgroup.eq_of_le_of_card_ge hdle (by
      rw [burnsideF437_card_conjSub, burnsideF437_card_conjSub])
  have hN : d⁻¹ * e ∈ Subgroup.normalizer (R : Set E) := by
    rw [← burnsideF437_conjSub_eq_iff, conjSub_mul, heq, conjSub_conjSub_inv]
  refine ⟨d, hd, d⁻¹ * e, ⟨?_, hRN hN⟩, by group⟩
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.2) he

theorem burnsideF437_pCoreOf_cen [Finite E] {Gp M₁ M₂ : Subgroup E} {fb : E}
    (hsyl : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E))
      (cenIn Gp fb)) :
    pCoreOf 2 (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb) =
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) with hR
  have hRle : R ≤ cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb :=
    inf_le_inf_right _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hle2 : cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb ≤ cenIn Gp fb := inf_le_inf_right _ inf_le_left
  refine le_antisymm ?_ ?_
  · exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
      (CFSG.Quasithin.F7.isSylowTwoOf_mono_right hsyl hRle hle2)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRle ?_ hsyl.2.1
    intro x hx
    refine burnsideF437_mem_normalizer_inf ?_ ?_
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx.1
    · exact Subgroup.le_normalizer hx.2

theorem burnsideF437_dynkin [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal] {fb : E}
    (hsyl : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E))
      (cenIn Gp fb))
    (hRN : Subgroup.normalizer
      ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) : Subgroup E) : Set E) ≤
        M₁ ⊓ M₂) :
    ∀ e ∈ Subgroup.centralizer ({fb} : Set E),
      e ∈ Subgroup.normalizer ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb : Subgroup E) : Set E) →
      e ∈ Subgroup.normalizer ((f437DbarOne Gp M₁ fb : Subgroup E) : Set E) := by
  intro e he heN
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ heN
  rw [burnsideF437_pCoreOf_cen hsyl] at h1
  have h2 := hRN h1
  exact burnsideF437_mem_normalizer_inf (burnsideF4m_mem_normalizer_inf (Gp := Gp) h2.1)
    (Subgroup.le_normalizer he)

theorem burnsideF437_sup_eq {Gp M₁ M₂ : Subgroup E} {fb : E}
    (hP : IsLieParabolics 2 (f437Dbar Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb)
      (f437DbarOne Gp M₁ fb) (f437DbarTwo Gp M₂ fb)) :
    f437DbarOne Gp M₁ fb ⊔ f437DbarTwo Gp M₂ fb = f437Dbar Gp fb :=
  burnsideF4j_parabolics_gen hP

theorem burnsideF437_inf_eq {Gp M₁ M₂ : Subgroup E} {fb : E} :
    f437DbarOne Gp M₁ fb ⊓ f437DbarTwo Gp M₂ fb = cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb := by
  ext x
  simp only [f437DbarOne, f437DbarTwo, cenIn, Subgroup.mem_inf]
  tauto

end Sylow

end CFSG.ASVolI
