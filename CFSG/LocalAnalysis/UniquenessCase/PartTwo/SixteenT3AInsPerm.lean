module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private noncomputable def s16t_a_permFun {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) : ι :=
  Classical.choose (hperm (g : MulAut T) g.2 i)

private theorem s16t_a_permFun_spec {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} {Y : ι → Subgroup T}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16t_a_permFun hperm g i) :=
  Classical.choose_spec (hperm (g : MulAut T) g.2 i)

private theorem s16t_a_permFun_injective {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) :
    Function.Injective (s16t_a_permFun hperm g) := by
  intro i j hij
  apply hinj
  have hi := s16t_a_permFun_spec hperm g i
  have hj := s16t_a_permFun_spec hperm g j
  rw [hij] at hi
  exact Subgroup.map_injective (g : MulAut T).injective (hi.trans hj.symm)

private noncomputable def s16t_a_perm {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} [Fintype ι] {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) : Equiv.Perm ι :=
  Equiv.ofBijective (s16t_a_permFun hperm g)
    ⟨s16t_a_permFun_injective hinj hperm g,
      (Finite.injective_iff_surjective).1 (s16t_a_permFun_injective hinj hperm g)⟩

private theorem s16t_a_perm_spec {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} [Fintype ι] {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g : ↥X) (i : ι) :
    (Y i).map (g : MulAut T).toMonoidHom = Y (s16t_a_perm hinj hperm g i) :=
  s16t_a_permFun_spec hperm g i

private theorem s16t_a_perm_mul {T : Type} [CommGroup T] {X : Subgroup (MulAut T)}
    {ι : Type} [Fintype ι] {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (g h : ↥X) :
    s16t_a_perm hinj hperm (g * h) = s16t_a_perm hinj hperm g * s16t_a_perm hinj hperm h := by
  ext i
  apply hinj
  rw [← s16t_a_perm_spec hinj hperm (g * h) i, Equiv.Perm.mul_apply,
    ← s16t_a_perm_spec hinj hperm g (s16t_a_perm hinj hperm h i),
    ← s16t_a_perm_spec hinj hperm h i, Subgroup.map_map]
  rfl

theorem s16t_a_exists_perm_hom {T : Type} [CommGroup T] {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} (hinj : Function.Injective Y) {X : Subgroup (MulAut T)}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) :
    ∃ ρ : ↥X →* Equiv.Perm ι, ∀ (g : ↥X) (i : ι),
      (Y i).map (g : MulAut T).toMonoidHom = Y (ρ g i) :=
  ⟨MonoidHom.mk' (s16t_a_perm hinj hperm) (s16t_a_perm_mul hinj hperm),
    fun g i => s16t_a_perm_spec hinj hperm g i⟩

theorem s16t_a_fix_of_pGroup_of_not_dvd {T : Type} [CommGroup T] {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} (hinj : Function.Injective Y) {X : Subgroup (MulAut T)}
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ (Fintype.card ι).factorial) {P : Subgroup (MulAut T)} (hPX : P ≤ X)
    (hPp : IsPGroup p ↥P) : ∀ f ∈ P, ∀ i, (Y i).map f.toMonoidHom = Y i := by
  classical
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom hinj hperm
  intro f hf i
  obtain ⟨k, hk⟩ := hPp ⟨f, hf⟩
  have hk' : (⟨f, hPX hf⟩ : ↥X) ^ (p ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf (ρ ⟨f, hPX hf⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hk', map_one]
  have h2 : orderOf (ρ ⟨f, hPX hf⟩) ∣ (Fintype.card ι).factorial := by
    have := orderOf_dvd_card (G := Equiv.Perm ι) (x := ρ ⟨f, hPX hf⟩)
    rwa [Fintype.card_perm] at this
  have hcop : Nat.Coprime (p ^ k) (Fintype.card ι).factorial :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have h3 : orderOf (ρ ⟨f, hPX hf⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : ρ ⟨f, hPX hf⟩ = 1 := orderOf_eq_one_iff.1 h3
  have h5 := hρ ⟨f, hPX hf⟩ i
  rw [h4] at h5
  exact h5

theorem s16t_a_dvd_card_of_fixing {T : Type} [CommGroup T] {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = 3) {Y : ι → Subgroup T} (hinj : Function.Injective Y)
    {X Λ : Subgroup (MulAut T)} (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    (hsurj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i))
    (hΛX : Λ ≤ X) (h9 : 9 ∣ Nat.card Λ)
    (hfix : ∀ f ∈ Λ, ∀ i, (Y i).map f.toMonoidHom = Y i) : 27 ∣ Nat.card X := by
  classical
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom hinj hperm
  have hsurjρ : Function.Surjective ρ := by
    intro π
    obtain ⟨g, hg, hgπ⟩ := hsurj π
    refine ⟨⟨g, hg⟩, ?_⟩
    ext i
    apply hinj
    exact (hρ ⟨g, hg⟩ i).symm.trans (hgπ i)
  have hrange : Nat.card ρ.range = 6 := by
    rw [MonoidHom.range_eq_top_of_surjective ρ hsurjρ, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_perm, hι]
    rfl
  have hle : Λ.subgroupOf X ≤ ρ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    ext i
    apply hinj
    rw [← hρ g i]
    exact hfix (g : MulAut T) (Subgroup.mem_subgroupOf.1 hg) i
  have hcardΛ : Nat.card (Λ.subgroupOf X) = Nat.card Λ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛX).toEquiv
  have hdvd : Nat.card (Λ.subgroupOf X) ∣ Nat.card ρ.ker := Subgroup.card_dvd_of_le hle
  rw [hcardΛ] at hdvd
  obtain ⟨m, hm⟩ := h9.trans hdvd
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hm, hrange] at hcard
  exact ⟨2 * m, by rw [← hcard]; ring⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
