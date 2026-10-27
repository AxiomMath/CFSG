module

public import CFSG.RankThree.PartOne.KF.CentralQuot

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU

theorem exists_mulAut_of_ker {H Q : Type*} [Group H] [Group Q] (ε : H →* Q)
    (hε : Function.Surjective ε) (β : MulAut H) (hβ : ∀ x, ε (β x) = 1 ↔ ε x = 1) :
    ∃ α : MulAut Q, ∀ x, α (ε x) = ε (β x) := by
  let φ : H →* Q := ε.comp β.toMonoidHom
  have hker : ε.ker ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (hβ x).2 hx
  let α₀ : Q →* Q := MonoidHom.liftOfSurjective ε hε ⟨φ, hker⟩
  have hα₀ : ∀ x, α₀ (ε x) = ε (β x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ε (Function.surjInv hε)
      (Function.rightInverse_surjInv hε) ⟨φ, hker⟩ x
  have hinj : Function.Injective α₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := hε a
    rw [hα₀] at ha
    exact (hβ x).1 ha
  have hsurj : Function.Surjective α₀ := by
    intro a
    obtain ⟨x, rfl⟩ := hε a
    exact ⟨ε (β.symm x), by rw [hα₀, MulEquiv.apply_symm_apply]⟩
  exact ⟨MulEquiv.ofBijective α₀ ⟨hinj, hsurj⟩, hα₀⟩

theorem map_mem_center {H : Type*} [Group H] (β : MulAut H) {x : H}
    (hx : x ∈ Subgroup.center H) : β x ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  have h := hx (β.symm g)
  calc g * β x = β (β.symm g * x) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = β (x * β.symm g) := by rw [h]
    _ = β x * g := by rw [map_mul, MulEquiv.apply_symm_apply]

theorem ker_eq_center {H Q : Type*} [Group H] [Group Q] {p : ℕ} {ε : H →* Q}
    (hε : IsCentralPQuot p ε) (hQ : ∀ z ∈ Subgroup.center Q, z = 1) :
    ε.ker = Subgroup.center H := by
  refine le_antisymm hε.central (fun z hz => ?_)
  rw [MonoidHom.mem_ker]
  apply hQ
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := hε.surjective q
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]

theorem exists_mulAut_of_normalizer {G Q : Type*} [Group G] [Group Q] {p : ℕ} {L : Subgroup G}
    (ε : ↥L →* Q) (hε : IsCentralPQuot p ε) (hQ : ∀ z ∈ Subgroup.center Q, z = 1) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∃ α : MulAut Q, ∀ x : ↥L, α (ε x) = ε (L.normalizerMonoidHom ⟨y, hyL⟩ x) := by
  refine exists_mulAut_of_ker ε hε.surjective (L.normalizerMonoidHom ⟨y, hyL⟩) fun x => ?_
  rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, ker_eq_center hε hQ]
  constructor
  · intro h
    have := map_mem_center (L.normalizerMonoidHom ⟨y, hyL⟩).symm h
    rwa [MulEquiv.symm_apply_apply] at this
  · exact map_mem_center _

theorem exists_scalar_of_aut {G Q : Type*} [Group G] [Finite G] [Group Q] {p : ℕ}
    {L F : Subgroup G} {T : Subgroup Q} (ε : ↥L →* Q) (hε : IsCentralPQuot p ε) (hFL : F ≤ L)
    (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hT1 : ∀ t ∈ T, ∃ f : F, ε (Subgroup.inclusion hFL f) = t)
    (hT2 : ∀ f : F, ε (Subgroup.inclusion hFL f) ∈ T)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) (α : MulAut Q)
    (hα : ∀ x : ↥L, α (ε x) = ε (L.normalizerMonoidHom ⟨y, hyL⟩ x)) (g : Q) (n : ℤ)
    (hgn : ∀ t ∈ T, α t = g * t ^ n * g⁻¹) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∀ f ∈ F, y * f * y⁻¹ = h * f ^ n * h⁻¹ := by
  classical
  let Fl : F →* ↥L := Subgroup.inclusion hFL
  have hFlexp : ∀ f : F, Fl f ^ p = 1 := fun f => Subtype.ext (hFexp _ f.2)
  have hTfin : Finite T :=
    Finite.of_surjective (fun f : F => (⟨ε (Fl f), hT2 f⟩ : T)) fun t =>
      let ⟨f, hf⟩ := hT1 t.1 t.2
      ⟨f, Subtype.ext hf⟩
  have hyFmem : ∀ f : F, y * (f : G) * y⁻¹ ∈ F := fun f =>
    (Subgroup.mem_normalizer_iff.mp hyF f).mp f.2
  have hβ : ∀ f : F, L.normalizerMonoidHom ⟨y, hyL⟩ (Fl f) = Fl ⟨y * (f : G) * y⁻¹, hyFmem f⟩ :=
    fun f => rfl
  have hαT : ∀ t ∈ T, α t ∈ T := by
    intro t ht
    obtain ⟨f, rfl⟩ := hT1 t ht
    rw [hα, hβ]
    exact hT2 _
  have hpowT : ∀ t ∈ T, t ^ n ∈ T := fun t ht => zpow_mem ht n
  have hinj : Function.Injective (fun t : T => (⟨t.1 ^ n, hpowT t.1 t.2⟩ : T)) := by
    intro t₁ t₂ h
    have h' : t₁.1 ^ n = t₂.1 ^ n := congrArg Subtype.val h
    have : α t₁.1 = α t₂.1 := by rw [hgn _ t₁.2, hgn _ t₂.2, h']
    exact Subtype.ext (α.injective this)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  have hgT : ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro t ht
    obtain ⟨t₀, ht₀⟩ := hsurj ⟨t, ht⟩
    have h1 : t₀.1 ^ n = t := congrArg Subtype.val ht₀
    have := hαT _ t₀.2
    rwa [hgn _ t₀.2, h1] at this
  obtain ⟨x₀, hx₀⟩ := hε.surjective g
  have hmemF : ∀ z : ↥L, z ^ p = 1 → ε z ∈ T → (z : G) ∈ F := by
    intro z hz hzT
    obtain ⟨f', hf'⟩ := hT1 _ hzT
    have := hε.eq_of_map_eq (hFlexp f') hz hf'
    rw [← this]
    exact f'.2
  have hconjF : ∀ f : F, (x₀ : G) * (f : G) * (x₀ : G)⁻¹ ∈ F := by
    intro f
    have hp : (x₀ * Fl f * x₀⁻¹) ^ p = 1 := by
      rw [conj_pow, hFlexp, mul_one, mul_inv_cancel]
    refine hmemF (x₀ * Fl f * x₀⁻¹) hp ?_
    rw [map_mul, map_mul, map_inv, hx₀]
    exact hgT _ (hT2 f)
  have hhF : (x₀ : G) ∈ Subgroup.normalizer (F : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun f hf => ?_
    exact hconjF ⟨f, hf⟩
  refine ⟨x₀, x₀.2, hhF, fun f hf => ?_⟩
  set f₀ : F := ⟨f, hf⟩ with hf₀
  have ha : (L.normalizerMonoidHom ⟨y, hyL⟩ (Fl f₀)) ^ p = 1 := by
    rw [← map_pow, hFlexp, map_one]
  have hb : (x₀ * Fl f₀ ^ n * x₀⁻¹) ^ p = 1 := by
    rw [conj_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hFlexp, one_zpow,
      mul_one, mul_inv_cancel]
  have hab : ε (L.normalizerMonoidHom ⟨y, hyL⟩ (Fl f₀)) = ε (x₀ * Fl f₀ ^ n * x₀⁻¹) := by
    rw [← hα, hgn _ (hT2 f₀), map_mul, map_mul, map_inv, map_zpow, hx₀]
  have := congrArg Subtype.val (hε.eq_of_map_eq ha hb hab)
  exact this

end CFSG.RankThree.PartOne.KFOUT3
