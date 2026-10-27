module

public import CFSG.Timmesfeld.ARS.CaseMF4Maps
public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.ARS.Sec12Center

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Timmesfeld CFSG.LieType.CurtisTits Matrix
open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CaseM

theorem eq_one_of_mem_center_sl2 {K : Type} [Field K] [CharP K 2]
    {g : SpecialLinearGroup (Fin 2) K} (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) :
    g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (r + 1) * (r + 1) = 0 := by
      have e : (r + 1) * (r + 1) = (r ^ 2 + 1) + (r + r) := by ring
      rw [e, hr, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have h3 : r + 1 = 0 := mul_self_eq_zero.1 h2
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h3
  subst hr1
  ext i j
  rw [← hrg]
  simp

theorem exists_lift_range {L K H : Type*} [Group L] [Group K] [Group H] (ι : L →* K)
    (Φ : L →* H) (h : ι.ker ≤ Φ.ker) :
    ∃ θ : ι.range →* H, ∀ y, θ ⟨ι y, y, rfl⟩ = Φ y := by
  have hsurj : Function.Surjective ι.rangeRestrict := ι.rangeRestrict_surjective
  refine ⟨ι.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj) ⟨Φ, by rwa [MonoidHom.ker_rangeRestrict]⟩, fun y => ?_⟩
  exact ι.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ y

section Generic

variable {K : Type} [Group K] (X : (Fin 4 → ℤ) → Subgroup K) {L : Type} [Group L]
  (XL : (Fin 3 → ℤ) → Subgroup L) {G : Type} [Group G]

theorem exists_node1 {f : ℕ} (ι : L →* K)
    (hιX : ∀ γ ∈ c3PairRoots, (X γ : Set K) = ι '' (XL (c3Coords γ) : Set L))
    {l : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* K} (hl : Function.Injective l)
    (hl3 : (X ![0, 1, 0, 0] : Set K) = Set.range (fun c => l (tv 1 2 c)))
    (hl4 : (X (-![0, 1, 0, 0]) : Set K) = Set.range (fun c => l (tv 2 1 c)))
    (Φ : L →* G) (hker : Φ.ker ≤ Subgroup.center L) (θV : ι.range →* G)
    (hθV : ∀ y, θV ⟨ι y, y, rfl⟩ = Φ y) {P₂ Q₂ : Subgroup G}
    (hP₂ : (XL (longC3 2)).map Φ = P₂) (hQ₂ : (XL (-longC3 2)).map Φ = Q₂) :
    ∃ ρ₁ : SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G, Function.Injective ρ₁ ∧
      (upperUnipotent (GaloisField 2 f)).map ρ₁ = P₂ ∧
      (lowerUnipotent (GaloisField 2 f)).map ρ₁ = Q₂ ∧
      (∀ c (h : l (tv 1 2 c) ∈ ι.range), ρ₁ (tv 0 1 c) = θV ⟨_, h⟩) ∧
      (∀ c (h : l (tv 2 1 c) ∈ ι.range), ρ₁ (tv 1 0 c) = θV ⟨_, h⟩) := by
  have hα₁ : (![0, 1, 0, 0] : Fin 4 → ℤ) ∈ c3PairRoots := by
    rw [mem_c3PairRoots_iff]; decide
  have hα₁' : (-![0, 1, 0, 0] : Fin 4 → ℤ) ∈ c3PairRoots := by
    rw [mem_c3PairRoots_iff]; decide
  have hP2 : c3Coords ![0, 1, 0, 0] = longC3 2 := by decide
  have hQ2 : c3Coords (-![0, 1, 0, 0]) = -longC3 2 := by decide
  have hXV : ∀ γ ∈ c3PairRoots, X γ ≤ ι.range := by
    intro γ hγ x hx
    have hx' : x ∈ (X γ : Set K) := hx
    rw [hιX γ hγ] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact ⟨y, rfl⟩
  have hθV' : ∀ y (h : ι y ∈ ι.range), θV ⟨ι y, h⟩ = Φ y := fun y _ => hθV y
  have hmem' : ∀ {γ : Fin 4 → ℤ} {g : GaloisField 2 f → K}, (X γ : Set K) = Set.range g →
      ∀ c, g c ∈ X γ := fun h c => by
    rw [← SetLike.mem_coe, h]
    exact ⟨c, rfl⟩
  have hV : ∀ {γ : Fin 4 → ℤ}, γ ∈ c3PairRoots → ∀ x (hx : x ∈ X γ),
      ∃ y ∈ XL (c3Coords γ), ι y = x := by
    intro γ hγ x hx
    have hx' : x ∈ (X γ : Set K) := hx
    rw [hιX γ hγ] at hx'
    exact hx'
  have h₁ : ∀ g, l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) g) ∈ ι.range :=
    sl2_mem_of_tv (l.comp (SL.blockHom (GaloisField 2 f) (1 : Fin 2)))
      (fun c => by
        rw [MonoidHom.comp_apply, blockHom_tv_upper]
        exact hXV _ hα₁ (hmem' hl3 c))
      (fun c => by
        rw [MonoidHom.comp_apply, blockHom_tv_lower]
        exact hXV _ hα₁' (hmem' hl4 c))
  let ρ₁ : SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G :=
    θV.comp ((l.comp (SL.blockHom (GaloisField 2 f) (1 : Fin 2))).codRestrict ι.range h₁)
  have hρ₁ : ∀ g, ρ₁ g = θV ⟨l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) g), h₁ g⟩ :=
    fun g => rfl
  have e1 : ∀ c, SL.blockHom (GaloisField 2 f) (1 : Fin 2) (tv 0 1 c) = tv 1 2 c :=
    fun c => blockHom_tv_upper 1 c
  have e2 : ∀ c, SL.blockHom (GaloisField 2 f) (1 : Fin 2) (tv 1 0 c) = tv 2 1 c :=
    fun c => blockHom_tv_lower 1 c
  have hρ₁12 : ∀ c (h : l (tv 1 2 c) ∈ ι.range), ρ₁ (tv 0 1 c) = θV ⟨_, h⟩ := fun c h => by
    rw [hρ₁]
    congr 2
    exact congrArg l (e1 c)
  have hρ₁21 : ∀ c (h : l (tv 2 1 c) ∈ ι.range), ρ₁ (tv 1 0 c) = θV ⟨_, h⟩ := fun c h => by
    rw [hρ₁]
    congr 2
    exact congrArg l (e2 c)
  have hρ₁inj : Function.Injective ρ₁ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨y, hy⟩ := h₁ g
    have hy1 : Φ y = 1 := by
      rw [← hθV' y ⟨y, rfl⟩, ← hg, hρ₁]
      congr 2
    have hyc : y ∈ Subgroup.center L := hker hy1
    have hcomm1 : ∀ x ∈ ι.range,
        Commute (l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) g)) x := by
      rintro _ ⟨x, rfl⟩
      rw [← hy, Commute, SemiconjBy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hyc x)]
    have hgen : ∀ g' : SpecialLinearGroup (Fin 2) (GaloisField 2 f), Commute g g' := by
      intro g'
      have key := sl2_mem_of_tv (MonoidHom.id _)
        (H := Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin 2) (GaloisField 2 f))))
        (fun c => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h := hcomm1 _ (hXV _ hα₁ (hmem' hl3 c))
          have h' : l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) (g * tv 0 1 c)) =
              l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) (tv 0 1 c * g)) := by
            rw [map_mul, map_mul, map_mul, map_mul, e1]
            exact h
          exact (SL.blockHom_injective _ (hl h')).symm)
        (fun c => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h := hcomm1 _ (hXV _ hα₁' (hmem' hl4 c))
          have h' : l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) (g * tv 1 0 c)) =
              l (SL.blockHom (GaloisField 2 f) (1 : Fin 2) (tv 1 0 c * g)) := by
            rw [map_mul, map_mul, map_mul, map_mul, e2]
            exact h
          exact (SL.blockHom_injective _ (hl h')).symm) g'
      rw [Subgroup.mem_centralizer_singleton_iff] at key
      exact key.symm
    exact eq_one_of_mem_center_sl2 (Subgroup.mem_center_iff.2 fun g' => (hgen g').eq.symm)
  have hup : (upperUnipotent (GaloisField 2 f)).map ρ₁ = P₂ := by
    apply SetLike.coe_injective
    rw [← Linear.range_tv_upper]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨y, hy, hyc⟩ := hV hα₁ _ (hmem' hl3 c)
      show ρ₁ (tv 0 1 c) ∈ P₂
      rw [hρ₁12 c (hXV _ hα₁ (hmem' hl3 c))]
      have : θV ⟨l (tv 1 2 c), hXV _ hα₁ (hmem' hl3 c)⟩ = Φ y := by
        rw [← hθV' y ⟨y, rfl⟩]
        congr 2
        exact hyc.symm
      rw [this, ← hP₂, ← hP2]
      exact ⟨y, hy, rfl⟩
    · rintro hz
      rw [SetLike.mem_coe, ← hP₂, ← hP2] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hιy : ι y ∈ X ![0, 1, 0, 0] := by
        have h : ι y ∈ ι '' (XL (c3Coords ![0, 1, 0, 0]) : Set L) := ⟨y, hy, rfl⟩
        rw [← hιX _ hα₁] at h
        exact h
      have hιy' : ι y ∈ (X ![0, 1, 0, 0] : Set K) := hιy
      rw [hl3] at hιy'
      obtain ⟨c, hc⟩ := hιy'
      have hc' : l (tv 1 2 c) = ι y := hc
      refine ⟨c, ?_⟩
      show ρ₁ (tv 0 1 c) = Φ y
      rw [hρ₁12 c (by rw [hc']; exact ⟨y, rfl⟩), ← hθV' y ⟨y, rfl⟩]
      congr 2
  have hlow : (lowerUnipotent (GaloisField 2 f)).map ρ₁ = Q₂ := by
    apply SetLike.coe_injective
    rw [← Linear.range_tv_lower]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨y, hy, hyc⟩ := hV hα₁' _ (hmem' hl4 c)
      show ρ₁ (tv 1 0 c) ∈ Q₂
      rw [hρ₁21 c (hXV _ hα₁' (hmem' hl4 c))]
      have : θV ⟨l (tv 2 1 c), hXV _ hα₁' (hmem' hl4 c)⟩ = Φ y := by
        rw [← hθV' y ⟨y, rfl⟩]
        congr 2
        exact hyc.symm
      rw [this, ← hQ₂, ← hQ2]
      exact ⟨y, hy, rfl⟩
    · rintro hz
      rw [SetLike.mem_coe, ← hQ₂, ← hQ2] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hιy : ι y ∈ X (-![0, 1, 0, 0]) := by
        have h : ι y ∈ ι '' (XL (c3Coords (-![0, 1, 0, 0])) : Set L) := ⟨y, hy, rfl⟩
        rw [← hιX _ hα₁'] at h
        exact h
      have hιy' : ι y ∈ (X (-![0, 1, 0, 0]) : Set K) := hιy
      rw [hl4] at hιy'
      obtain ⟨c, hc⟩ := hιy'
      have hc' : l (tv 2 1 c) = ι y := hc
      refine ⟨c, ?_⟩
      show ρ₁ (tv 1 0 c) = Φ y
      rw [hρ₁21 c (by rw [hc']; exact ⟨y, rfl⟩), ← hθV' y ⟨y, rfl⟩]
      congr 2
  exact ⟨ρ₁, hρ₁inj, hup, hlow, hρ₁12, hρ₁21⟩


theorem exists_edge {G : Type} [Group G] [Finite G] {R : Set (Subgroup G)} (hR : IsRootClass R)
    (hiso : NoIsolated R) {f : ℕ} {E F P₂ Q₂ : Subgroup G} (hER : E ∈ R) (hFR : F ∈ R)
    (hPR : P₂ ∈ R) (hQR : Q₂ ∈ R) (hPQ : Opposite P₂ Q₂) (hEF : Opposite E F)
    (d1 : Special R P₂ E) (d2 : Commuting Q₂ E) (d3 : ⁅Q₂, ⁅P₂, E⁆⁆ = E) (d4 : Commuting P₂ F)
    (d5 : ⁅⁅P₂, E⁆, F⁆ = P₂) (d6 : Special R Q₂ F) (hq : Nat.card P₂ = 2 ^ f)
    {ρ₁ : SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G} (hρ₁ : Function.Injective ρ₁)
    (hup : (upperUnipotent (GaloisField 2 f)).map ρ₁ = P₂)
    (hlow : (lowerUnipotent (GaloisField 2 f)).map ρ₁ = Q₂) :
    ∃ ψE : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* G,
      (∀ c, ψE (tv 1 2 c) = ρ₁ (tv 0 1 c)) ∧ (∀ c, ψE (tv 2 1 c) = ρ₁ (tv 1 0 c)) ∧
      Set.range (fun c => ψE (tv 0 1 c)) = (E : Set G) ∧
      Set.range (fun c => ψE (tv 1 0 c)) = (F : Set G) := by
  obtain ⟨ψ₀, ρE, ⟨-, hρEup, hρElow⟩, hψ₀⟩ := Linear.exists_sl3_right hR hiso hPR hER hQR hFR
    d1 hPQ hEF d2 d3 d4 d5 d6 hq hρ₁ hup hlow
  refine ⟨ψ₀.comp (Linear.revHom (GaloisField 2 f) 3), fun c => ?_, fun c => ?_, ?_, ?_⟩
  · change ψ₀ (Linear.revHom _ 3 (tv 1 2 c)) = _
    rw [Linear.revHom_tv]
    exact (hψ₀ c).1
  · change ψ₀ (Linear.revHom _ 3 (tv 2 1 c)) = _
    rw [Linear.revHom_tv]
    exact (hψ₀ c).2.1
  · have h : ∀ c, (ψ₀.comp (Linear.revHom (GaloisField 2 f) 3)) (tv 0 1 c) = ρE (tv 0 1 c) :=
      fun c => by
        change ψ₀ (Linear.revHom _ 3 (tv 0 1 c)) = _
        rw [Linear.revHom_tv]
        exact (hψ₀ c).2.2.1
    simp only [h]
    rw [Linear.range_tv_upper, hρEup]
  · have h : ∀ c, (ψ₀.comp (Linear.revHom (GaloisField 2 f) 3)) (tv 1 0 c) = ρE (tv 1 0 c) :=
      fun c => by
        change ψ₀ (Linear.revHom _ 3 (tv 1 0 c)) = _
        rw [Linear.revHom_tv]
        exact (hψ₀ c).2.2.2
    simp only [h]
    rw [Linear.range_tv_lower, hρElow]


theorem exists_f4Frame_of_levis {G : Type} [Group G] [Finite G] {R : Set (Subgroup G)}
    (hR : IsRootClass R) (hiso : NoIsolated R)
    (hgenL : ⨆ k : Fin 3, (XL (Pi.single k 1) ⊔ XL (-Pi.single k 1)) = ⊤)
    {f : ℕ} {k' : Type} [Field k'] (ι : L →* K)
    (hιX : ∀ γ ∈ c3PairRoots, (X γ : Set K) = ι '' (XL (c3Coords γ) : Set L))
    {l : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* K} (hl : Function.Injective l)
    (hl1 : (X ![1, 0, 0, 0] : Set K) = Set.range (fun c => l (tv 0 1 c)))
    (hl2 : (X (-![1, 0, 0, 0]) : Set K) = Set.range (fun c => l (tv 1 0 c)))
    (hl3 : (X ![0, 1, 0, 0] : Set K) = Set.range (fun c => l (tv 1 2 c)))
    (hl4 : (X (-![0, 1, 0, 0]) : Set K) = Set.range (fun c => l (tv 2 1 c)))
    (hl5 : (X ![1, 1, 0, 0] : Set K) = Set.range (fun c => l (tv 0 2 c)))
    (hl6 : (X (-![1, 1, 0, 0]) : Set K) = Set.range (fun c => l (tv 2 0 c)))
    (m : Fin 4 → SpecialLinearGroup (Fin 2) (GaloisField 2 f) × SpecialLinearGroup (Fin 2) k' →* K)
    (hm : ∀ j : Fin 4, (j = 2 ∨ j = 3) → Function.Injective (m j) ∧
      (X (Pi.single j 1) : Set K) = Set.range (fun c => m j (1, tv 0 1 c)) ∧
      (X (-Pi.single j 1) : Set K) = Set.range (fun c => m j (1, tv 1 0 c)) ∧
      ∀ c, m j (tv 0 1 c, 1) = l (tv 0 1 c) ∧ m j (tv 1 0 c, 1) = l (tv 1 0 c))
    (Φ : L →* G) (hker : Φ.ker ≤ Subgroup.center L) (hιΦ : ι.ker ≤ Φ.ker)
    {E F P₂ Q₂ : Subgroup G} (hER : E ∈ R) (hFR : F ∈ R) (hPR : P₂ ∈ R) (hQR : Q₂ ∈ R)
    (hPQ : Opposite P₂ Q₂) (hEF : Opposite E F)
    (d1 : Special R P₂ E) (d2 : Commuting Q₂ E) (d3 : ⁅Q₂, ⁅P₂, E⁆⁆ = E) (d4 : Commuting P₂ F)
    (d5 : ⁅⁅P₂, E⁆, F⁆ = P₂) (d6 : Special R Q₂ F) (hq : Nat.card P₂ = 2 ^ f)
    (hP₂ : (XL (longC3 2)).map Φ = P₂) (hQ₂ : (XL (-longC3 2)).map Φ = Q₂)
    (hdr : ∀ a b : Fin 3, a ≠ b → ∀ γ : Fin 3 → ℤ,
      Symplectic.toStd 3 γ = Pi.single a 1 - Pi.single b 1 →
        Commuting ((XL γ).map Φ) E ∧ Commuting ((XL γ).map Φ) F)
    (htop : Φ.range ⊔ E ⊔ F = ⊤) :
    ∃ ψ : ∀ γ, X γ → G,
      (∀ t : Fin 4,
        ExtendsToHom X (![c3PairRoots, edge01Roots, edge0Roots 2, edge0Roots 3] t) ψ) ∧
      Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪
        Set.range (ψ (-Pi.single k 1))) = ⊤ ∧
      (∃ k, ∃ x, ψ (Pi.single k 1) x ≠ 1) ∧
      (E : Set G) = Set.range (ψ (Pi.single 0 1)) ∧
      (F : Set G) = Set.range (ψ (-Pi.single 0 1)) := by
  obtain ⟨θV, hθV⟩ := exists_lift_range ι Φ hιΦ
  have hθV' : ∀ y (h : ι y ∈ ι.range), θV ⟨ι y, h⟩ = Φ y := fun y _ => hθV y
  have hXV : ∀ γ ∈ c3PairRoots, X γ ≤ ι.range := by
    intro γ hγ x hx
    have hx' : x ∈ (X γ : Set K) := hx
    rw [hιX γ hγ] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact ⟨y, rfl⟩
  obtain ⟨ρ₁, hρ₁inj, hup, hlow, hρ₁12, hρ₁21⟩ :=
    exists_node1 X XL ι hιX hl hl3 hl4 Φ hker θV hθV hP₂ hQ₂
  obtain ⟨ψE, hψE12, hψE21, hrE, hrF⟩ :=
    exists_edge hR hiso hER hFR hPR hQR hPQ hEF d1 d2 d3 d4 d5 d6 hq hρ₁inj hup hlow
  have hψE : ∀ c (h : l (tv 1 2 c) ∈ ι.range), ψE (tv 1 2 c) = θV ⟨_, h⟩ := fun c h =>
    (hψE12 c).trans (hρ₁12 c h)
  have hψE' : ∀ c (h : l (tv 2 1 c) ∈ ι.range), ψE (tv 2 1 c) = θV ⟨_, h⟩ := fun c h =>
    (hψE21 c).trans (hρ₁21 c h)
  have hV1 : ∀ γ (hγ : γ ∈ c3PairRoots) x (hx : x ∈ X γ),
      θV ⟨x, hXV γ hγ hx⟩ ∈ (XL (c3Coords γ)).map Φ := by
    intro γ hγ x hx
    have hx' : x ∈ (X γ : Set K) := hx
    rw [hιX γ hγ] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [hθV']
    exact ⟨y, hy, rfl⟩
  have hV2 : ∀ γ (hγ : γ ∈ c3PairRoots) y (hy : y ∈ XL (c3Coords γ)), ι y ∈ X γ := by
    intro γ hγ y hy
    have h : ι y ∈ ι '' (XL (c3Coords γ) : Set L) := ⟨y, hy, rfl⟩
    rw [← hιX γ hγ] at h
    exact h
  have hdiff : ∀ j : Fin 4, (j = 2 ∨ j = 3) → ∀ γ : Fin 4 → ℤ,
      (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
        ∃ a b : Fin 3, a ≠ b ∧
          Symplectic.toStd 3 (c3Coords γ) = Pi.single a 1 - Pi.single b 1 := by
    rintro j (rfl | rfl) γ (rfl | rfl)
    · exact ⟨1, 2, by decide, by decide⟩
    · exact ⟨2, 1, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide⟩
    · exact ⟨1, 0, by decide, by decide⟩
  have hE' : ∀ c, ψE (tv 0 1 c) ∈ E := fun c => by
    rw [← SetLike.mem_coe, ← hrE]
    exact ⟨c, rfl⟩
  have hF' : ∀ c, ψE (tv 1 0 c) ∈ F := fun c => by
    rw [← SetLike.mem_coe, ← hrF]
    exact ⟨c, rfl⟩
  have hcomm : ∀ j : Fin 4, (j = 2 ∨ j = 3) → ∀ x (hx : x ∈ ι.range),
      (x ∈ X (Pi.single j 1) ∨ x ∈ X (-Pi.single j 1)) →
        ∀ c, Commute (ψE (tv 0 1 c)) (θV ⟨x, hx⟩) ∧ Commute (ψE (tv 1 0 c)) (θV ⟨x, hx⟩) := by
    intro j hj x hx hγx c
    have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
    obtain ⟨hsj, hsj'⟩ := single_mem_c3PairRoots hj0
    have key : ∀ γ : Fin 4 → ℤ, γ ∈ c3PairRoots → (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
        x ∈ X γ →
          Commute (ψE (tv 0 1 c)) (θV ⟨x, hx⟩) ∧ Commute (ψE (tv 1 0 c)) (θV ⟨x, hx⟩) := by
      intro γ hγc hγ hxγ
      obtain ⟨a, b, hab, hst⟩ := hdiff j hj γ hγ
      obtain ⟨hUE, hUF⟩ := hdr a b hab _ hst
      have hu := hV1 γ hγc x hxγ
      exact ⟨(hUE _ hu _ (hE' c)).symm, (hUF _ hu _ (hF' c)).symm⟩
    rcases hγx with h | h
    · exact key _ hsj (Or.inl rfl) h
    · exact key _ hsj' (Or.inr rfl) h
  obtain ⟨ψ, e1, e2, e3, e4, hψV, r1, r2⟩ :=
    exists_f4Maps X θV hXV hl hl1 hl2 hl3 hl4 hl5 hl6 m hm ψE hψE hψE' hcomm
  have hrE' : (E : Set G) = Set.range (ψ (Pi.single 0 1)) := by rw [r1, hrE]
  have hrF' : (F : Set G) = Set.range (ψ (-Pi.single 0 1)) := by rw [r2, hrF]
  refine ⟨ψ, fun t => ?_, ?_, ?_, hrE', hrF'⟩
  · fin_cases t
    exacts [e1, e2, e3, e4]
  · set T := Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪
      Set.range (ψ (-Pi.single k 1))) with hT
    have hsub : ∀ k : Fin 4, Set.range (ψ (Pi.single k 1)) ⊆ T ∧
        Set.range (ψ (-Pi.single k 1)) ⊆ T := fun k =>
      ⟨fun y hy => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl hy⟩),
        fun y hy => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr hy⟩)⟩
    have hET : E ≤ T := fun e he => (hsub 0).1 (by rw [← hrE']; exact he)
    have hFT : F ≤ T := fun e he => (hsub 0).2 (by rw [← hrF']; exact he)
    have key : ∀ k : Fin 4, k ≠ 0 → ∀ γ : Fin 4 → ℤ, (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) →
        (XL (c3Coords γ)).map Φ ≤ T := by
      rintro k hk γ hγ _ ⟨z, hz, rfl⟩
      have hγc : γ ∈ c3PairRoots := by
        rcases hγ with rfl | rfl
        exacts [(single_mem_c3PairRoots hk).1, (single_mem_c3PairRoots hk).2]
      have hz' := hV2 γ hγc z hz
      have hψz : ψ γ ⟨ι z, hz'⟩ = Φ z := by rw [hψV γ hγc, hθV']
      rcases hγ with rfl | rfl
      · exact (hsub k).1 ⟨_, hψz⟩
      · exact (hsub k).2 ⟨_, hψz⟩
    have hk : ∀ k : Fin 3, ∃ k' : Fin 4, k' ≠ 0 ∧ c3Coords (Pi.single k' 1) = Pi.single k 1 ∧
        c3Coords (-Pi.single k' 1) = -Pi.single k 1 := by decide
    have hVT : Φ.range ≤ T := by
      rw [MonoidHom.range_eq_map, ← hgenL, Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rw [Subgroup.map_sup]
      obtain ⟨k', hk', h1, h2⟩ := hk k
      exact sup_le (h1 ▸ key k' hk' _ (Or.inl rfl)) (h2 ▸ key k' hk' _ (Or.inr rfl))
    rw [eq_top_iff, ← htop]
    exact sup_le (sup_le hVT hET) hFT
  · obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    have : e ∈ Set.range (ψ (Pi.single 0 1)) := by rw [← hrE']; exact he
    obtain ⟨x, hx⟩ := this
    exact ⟨0, x, hx ▸ he1⟩

end Generic

end CaseM

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem levi_sup_eq_top {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hF : F ∈ lambdaStar R A₀ A) : levi R A A₀ ⊔ E ⊔ F = ⊤ := by
  have hA := hS.mem
  have hS₀ : Sec12 R A₀ A := hS.of_mem_omegaSet hS.opp.1 ⟨hA, hS.opp.2.symm⟩
  have hlevi : levi R A₀ A = levi R A A₀ := by simp only [levi, leviSet, Set.inter_comm]
  set H := levi R A A₀ ⊔ E ⊔ F with hH
  have hV : levi R A A₀ ≤ H := le_sup_left.trans le_sup_left
  have hEH : E ≤ H := le_sup_right.trans le_sup_left
  have hFH : F ≤ H := le_sup_right
  have hconj : ∀ {B : Subgroup G} {v : G}, B ≤ H → v ∈ H → conjSub B v ≤ H := by
    rintro B v hB hv _ ⟨b, hb, rfl⟩
    exact H.mul_mem (H.mul_mem hv (hB hb)) (H.inv_mem hv)
  have hΛ : ∀ B ∈ lambdaStar R A A₀, B ≤ H := fun B hB => by
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hA hS.sec8.2
      hS.max hS.opp hE hB
    exact hconj hEH (hV hv)
  have hΛ₀ : ∀ B ∈ lambdaStar R A₀ A, B ≤ H := fun B hB => by
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS₀.hyp hS₀.mem
      hS₀.sec8.2 hS₀.max hS₀.opp hF hB
    exact hconj hFH (hV (hlevi ▸ hv))
  have hM : M R A ≤ H := by
    rw [M_eq_gen_lambdaStar hS.hyp hA hS.opp]
    exact gen_le hΛ
  have hM₀ : M R A₀ ≤ H := by
    rw [M_eq_gen_lambdaStar hS₀.hyp hS₀.mem hS₀.opp]
    exact gen_le hΛ₀
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top hS.hyp hA hS.opp]
  exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hM) ((le_sup_left : A₀ ≤ M R A₀).trans hM₀)


theorem map_center_eq_one {L : Type*} [Group L] (Φ : L →* G) (hrange : Φ.range = levi R A A₀)
    {z : L} (hz : z ∈ Subgroup.center L) : Φ z = 1 := by
  have hzV : Φ z ∈ levi R A A₀ := hrange ▸ ⟨z, rfl⟩
  have hc : (⟨Φ z, hzV⟩ : levi R A A₀) ∈ Subgroup.center (levi R A A₀) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨v, hv⟩
    rw [← hrange] at hv
    obtain ⟨y, rfl⟩ := hv
    apply Subtype.ext
    change Φ y * Φ z = Φ z * Φ y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y)]
  rw [hS.center_levi_eq_bot, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

end Sec12

end CFSG.Timmesfeld.ARS
