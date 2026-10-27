module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Coords

open CFSG.Open

variable {G : Type*} [Group G]

theorem eq_of_mk'_eq_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hA : IsPGroup p A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
  have hdisj : Disjoint A N := Subgroup.disjoint_of_coprime_natCard hcop
  have hmem : a⁻¹ * b ∈ N := QuotientGroup.eq.mp h
  have h1 : a⁻¹ * b = 1 :=
    Subgroup.disjoint_def.mp hdisj (A.mul_mem (A.inv_mem ha) hb) hmem
  exact inv_mul_eq_one.mp h1

theorem card_map_mk' [Finite G] {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hA : IsPGroup p A) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp A.subtype) := fun a b hab =>
    Subtype.ext (eq_of_mk'_eq_of_isPGroup N hN hA a.2 b.2 hab)
  have hrange : ((QuotientGroup.mk' N).comp A.subtype).range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_hom_lift {V : Type*} [Group V] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hA : IsPGroup p A)
    (f : V →* G ⧸ N) (hf : f.range ≤ A.map (QuotientGroup.mk' N)) :
    ∃ g : V →* G, g.range ≤ A ∧ (QuotientGroup.mk' N).comp g = f := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp A.subtype) := fun a b hab =>
    Subtype.ext (eq_of_mk'_eq_of_isPGroup N hN hA a.2 b.2 hab)
  have hrange : ((QuotientGroup.mk' N).comp A.subtype).range = A.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hf' : ∀ v, f v ∈ ((QuotientGroup.mk' N).comp A.subtype).range := fun v =>
    hrange ▸ hf ⟨v, rfl⟩
  let ι : A ≃* ((QuotientGroup.mk' N).comp A.subtype).range := MonoidHom.ofInjective hinj
  let g : V →* G := A.subtype.comp (ι.symm.toMonoidHom.comp (f.codRestrict _ hf'))
  refine ⟨g, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact (ι.symm ⟨f v, hf' v⟩).2
  · ext v
    have h := congrArg Subtype.val (ι.apply_symm_apply ⟨f v, hf' v⟩)
    exact h

theorem mem_normalizer_of_conj_mem {A : Subgroup G} [Finite A] {n : G}
    (h : ∀ a ∈ A, n * a * n⁻¹ ∈ A) : n ∈ Subgroup.normalizer (A : Set G) :=
  Subgroup.mem_normalizer_fintype h

theorem centralizer_image_eq_map_conj {V : Type*} (f f₀ : V → G) (g : G)
    (h : ∀ v, f v = g * f₀ v * g⁻¹) (S : Set V) :
    Subgroup.centralizer (f '' S) =
      (Subgroup.centralizer (f₀ '' S)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have key : ∀ x ∈ S, (f x * y = y * f x) ↔
      (f₀ x * (MulAut.conj g).symm y = (MulAut.conj g).symm y * f₀ x) := by
    intro x _
    rw [h x, MulAut.conj_symm_apply]
    constructor
    · intro e
      have e' := congrArg (fun z => g⁻¹ * z * g) e
      simpa [mul_assoc] using e'
    · intro e
      have e' := congrArg (fun z => g * z * g⁻¹) e
      simpa [mul_assoc] using e'
  constructor
  · intro H x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact (key x' hx').mp (H _ ⟨x', hx', rfl⟩)
  · intro H x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact (key x' hx').mpr (H _ ⟨x', hx', rfl⟩)

theorem centralizer_singleton_eq_map_conj {x y g : G} (h : x = g * y * g⁻¹) :
    Subgroup.centralizer ({x} : Set G) =
      (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
  have := centralizer_image_eq_map_conj (fun _ : Unit => x) (fun _ : Unit => y) g (fun _ => h)
    {()}
  simpa [Set.image_singleton] using this

theorem centralizer_singleton_inv_eq (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem centralizer_image_inv_eq {V : Type*} (f : V → G) (S : Set V) :
    Subgroup.centralizer ((fun v => (f v)⁻¹) '' S) = Subgroup.centralizer (f '' S) := by
  ext y
  simp only [Subgroup.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · intro H x hx
    exact (Commute.inv_left_iff (a := f x) (b := y)).mp (H hx)
  · intro H x hx
    exact (Commute.inv_left_iff (a := f x) (b := y)).mpr (H hx)

theorem eq_zpowers_of_card_eq_three {X : Subgroup G} (hX : Nat.card X = 3) {x : G} (hx : x ∈ X)
    (hx1 : x ≠ 1) : X = Subgroup.zpowers x := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hzp_le : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hx
  have hdiv : orderOf x ∣ 3 := by
    have hd := Subgroup.card_dvd_of_le hzp_le
    rwa [Nat.card_zpowers, hX] at hd
  have ho3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge hzp_le ?_).symm
  rw [Nat.card_zpowers, ho3, hX]

theorem centralizer_eq_of_card_eq_three {X : Subgroup G} (hX : Nat.card X = 3) {x : G}
    (hx : x ∈ X) (hx1 : x ≠ 1) :
    Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) := by
  conv_lhs => rw [eq_zpowers_of_card_eq_three hX hx hx1, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]

theorem pRank_map_conj [Finite G] {p : ℕ} (hp : 1 < p) (g : G) (H : Subgroup G) :
    CFSG.Open.pRank p (H.map (MulAut.conj g).toMonoidHom) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective (H.map (MulAut.conj g).toMonoidHom)
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rwa [Subgroup.map_map, hid, Subgroup.map_id] at h
  · exact CFSG.SectionRank.pRank_le_map hp (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective H

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Coords
