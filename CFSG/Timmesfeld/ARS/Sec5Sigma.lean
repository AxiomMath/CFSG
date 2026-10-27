module

public import CFSG.Timmesfeld.ARS.Sec5Elation

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def IsSigmaSubgroup (R : Set (Subgroup G)) (H : Subgroup G) : Prop :=
  ∃ S ⊆ R, H = gen S

@[expose] def IsSigmaMaximal (R : Set (Subgroup G)) (H : Subgroup G) : Prop :=
  IsSigmaSubgroup R H ∧ H ≠ ⊤ ∧ ∀ K, IsSigmaSubgroup R K → H ≤ K → K = H ∨ K = ⊤

@[expose] def centralGroup (R : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  gen (centralSet R A)

theorem isSigmaSubgroup_gen {S : Set (Subgroup G)} (hS : S ⊆ R) : IsSigmaSubgroup R (gen S) :=
  ⟨S, hS, rfl⟩

theorem isSigmaSubgroup_centralGroup (A : Subgroup G) : IsSigmaSubgroup R (centralGroup R A) :=
  isSigmaSubgroup_gen fun _ hB => hB.1

theorem IsSigmaSubgroup.eq_gen {H : Subgroup G} (hH : IsSigmaSubgroup R H) :
    H = gen {B | B ∈ R ∧ B ≤ H} := by
  obtain ⟨S, hS, rfl⟩ := hH
  exact le_antisymm (gen_mono fun B hB => ⟨hS hB, le_gen hB⟩) (gen_le fun B hB => hB.2)

theorem le_centralGroup {A B : Subgroup G} (hB : B ∈ centralSet R A) : B ≤ centralGroup R A :=
  le_gen hB

theorem commuting_centralGroup (A : Subgroup G) : Commuting A (centralGroup R A) :=
  commuting_iff_le_centralizer.2 (gen_le fun _ hB => commuting_iff_le_centralizer.1 hB.2)

theorem conjSub_centralGroup (hR : IsRootClass R) (A : Subgroup G) (g : G) :
    conjSub (centralGroup R A) g = centralGroup R (conjSub A g) := by
  have key : ∀ (X : Subgroup G) (x : G), conjSub (centralGroup R X) x ≤
      centralGroup R (conjSub X x) := fun X x => by
    rw [centralGroup, conjSub_gen]
    exact gen_le fun _ ⟨B, hB, e⟩ => e ▸ le_gen ⟨hR.conjSub_mem hB.1 x, hB.2.conjSub x⟩
  refine le_antisymm (key A g) ?_
  have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (key (conjSub A g) g⁻¹)
  change conjSub (conjSub (centralGroup R (conjSub A g)) g⁻¹) g ≤
    conjSub (centralGroup R (conjSub (conjSub A g) g⁻¹)) g at h1
  rwa [Plane.conjSub_inv_conjSub, Plane.conjSub_conjSub_inv] at h1

theorem centralGroup_ne_top {A B : Subgroup G} (hA : A ≠ ⊥) (hAB : Opposite A B) :
    centralGroup R A ≠ ⊤ := fun h =>
  hAB.not_commuting hA ((commuting_centralGroup A).mono le_rfl (h ▸ le_top))

section Sigma

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
include hR hiso hnd

theorem isWeakTI_conjSub_image_of_lt {D K : Subgroup G} (hD : D ∈ R) (hK : IsSigmaSubgroup R K)
    (hCK : centralGroup R D < K) (hKtop : K ≠ ⊤) :
    IsWeakTI R ((fun x => conjSub D x) '' (K : Set G)) := by
  set Δ := (fun x => conjSub D x) '' (K : Set G) with hΔdef
  have hDK : D ≤ K := (le_centralGroup ⟨hD, hR.commuting_self hD⟩).trans hCK.le
  have hΔR : Δ ⊆ R := by
    rintro _ ⟨x, -, rfl⟩
    exact hR.conjSub_mem hD x
  have hΔK : ∀ X ∈ Δ, X ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact conjSub_le hDK hx
  have hstab : ∀ k ∈ K, conjSet Δ k = Δ := by
    intro k hk
    ext X
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨k * x, K.mul_mem hk hx, conjSub_mul D k x⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨conjSub D (k⁻¹ * x), ⟨k⁻¹ * x, K.mul_mem (K.inv_mem hk) hx, rfl⟩, ?_⟩
      change conjSub (conjSub D (k⁻¹ * x)) k = conjSub D x
      rw [← conjSub_mul, mul_inv_cancel_left]
  have hCX : ∀ X ∈ Δ, ∀ U ∈ centralSet R X, U ≤ K := by
    rintro _ ⟨x, hx, rfl⟩ U hU
    have hU' : conjSub U x⁻¹ ∈ centralSet R D := by
      refine ⟨hR.conjSub_mem hU.1 x⁻¹, ?_⟩
      have := hU.2.conjSub x⁻¹
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    have h1 : conjSub U x⁻¹ ≤ K := (le_centralGroup hU').trans hCK.le
    calc U = conjSub (conjSub U x⁻¹) x := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
      _ ≤ K := conjSub_le h1 hx
  have hiso' : ∀ X ∈ Δ, ∀ A ∈ R, A ≤ K → ¬ Opposite X A := by
    intro X hX A hA hAK hXA
    apply hKtop
    rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top_of hR hiso hnd (hΔR hX) ⟨hA, hXA⟩]
    exact sup_le (gen_le fun U hU => hCX X hX U ⟨hU.1.1, hU.1.2.2⟩) hAK
  have hline : ∀ X ∈ Δ, ∀ Y ∈ Δ, Y ∈ lambdaSet R X → ∀ T ∈ R, T ≤ X ⊔ Y → T ∈ Δ := by
    intro X hX Y hY hYX T hT hTle
    by_cases hTX : T = X
    · exact hTX ▸ hX
    obtain ⟨U, hU, u, hu, hYu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso (hΔR hX) hYX (hΔR hY)
      le_sup_right hYX.1.2.1 hT hTle hTX
    rw [← hYu, ← hstab u (hCX X hX U ⟨hU.1.1, hU.1.2.2⟩ hu)]
    exact conjSub_mem_conjSet hY u
  refine ⟨hΔR, ?_, ?_, fun c hc => ?_⟩
  ·
    by_contra! hall
    have hD' : D ∈ Δ := ⟨1, K.one_mem, conjSub_one D⟩
    apply hCK.not_ge
    rw [hK.eq_gen]
    refine gen_le fun B hB => le_centralGroup ⟨hB.1, ?_⟩
    refine (Sec3.commuting_of_forall_conjSub_eq hR hB.1 hD (fun b hb => ?_) hiso).symm
    exact (hall D hD' _ ⟨b, hB.2 hb, rfl⟩).symm
  ·
    intro hΔ
    apply hKtop
    rw [eq_top_iff, ← hR.gen]
    exact iSup₂_le fun A hA => hΔK A (hΔ ▸ hA)
  ·
    suffices hcK : (Δ ∩ conjSet Δ c).Nonempty → c ∈ K by
      by_cases hne : (Δ ∩ conjSet Δ c).Nonempty
      · right
        rw [hstab c (hcK hne), Set.inter_self]
      · left
        exact Set.not_nonempty_iff_eq_empty.1 hne
    rintro ⟨A, hA, hAc⟩
    obtain ⟨F, hF, hcF, hc1⟩ := hc
    have hAR := hΔR hA
    have hcc : c⁻¹ = c := hR.inv_eq hF hcF
    have hAc' : conjSub A c ∈ Δ := by
      have := (mem_conjSet).1 hAc
      rwa [hcc] at this
    by_cases hfix : conjSub A c = A
    ·
      have hFA : Commuting F A := by
        by_cases hFA : F = A
        · exact hFA ▸ hR.commuting_self hF
        rcases hR.rel F hF A hAR hFA with h | h | h
        · exact h
        · exact absurd (h.eq_one_of_conjSub_eq hcF hfix) hc1
        · obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hAR
          exact absurd (eq_one_of_commute_of_special hR hiso hF hAR h hcF hc1 ha
            (Sec3.commute_of_conjSub_eq hR hiso hF hAR hcF hfix a ha)) ha1
      exact hCX A hA F ⟨hF, hFA.symm⟩ hcF
    ·
      have hFA : F ≠ A := fun e => hfix (conjSub_of_mem (e ▸ hcF))
      have hs : Special R A F := by
        rcases hR.rel A hAR F hF hFA.symm with h | h | h
        · exact absurd (conjSub_of_forall_commute fun x hx => (h x hx c hcF).symm) hfix
        · exact absurd (Sec5.opposite_conjSub_self h hcF hc1) (hiso' A hA _ (hR.conjSub_mem hAR c)
            (hΔK _ hAc'))
        · exact h
      have hAcl : conjSub A c ∈ lambdaSet R A :=
        QD.conjSub_mem_lambdaSet_of_special hR hiso hF hAR hs.symm hcF hc1
      have hEle : ⁅A, F⁆ ≤ A ⊔ conjSub A c := by
        rw [sup_conjSub_eq_sup_commutator hR hiso hAR hF hs hcF hc1]
        exact le_sup_right
      have hEΔ : ⁅A, F⁆ ∈ Δ := hline A hA _ hAc' hAcl _ hs.1 hEle
      exact hCX _ hEΔ F ⟨hF, hs.2.2⟩ hcF

theorem not_isSigmaMaximal_iff {D : Subgroup G} (hD : D ∈ R) :
    ¬ IsSigmaMaximal R (centralGroup R D) ↔ ∃ K, IsSigmaSubgroup R K ∧
      centralGroup R D < K ∧ K ≠ ⊤ ∧ IsWeakTI R ((fun x => conjSub D x) '' (K : Set G)) := by
  constructor
  · intro hmax
    obtain ⟨F, hF, hDF⟩ := hiso D hD
    have hne := centralGroup_ne_top (R := R) (hR.ne_bot D hD) hDF
    obtain ⟨K, hK, hle, hKne, hKtop⟩ : ∃ K, IsSigmaSubgroup R K ∧ centralGroup R D ≤ K ∧
        K ≠ centralGroup R D ∧ K ≠ ⊤ := by
      by_contra! hall
      exact hmax ⟨isSigmaSubgroup_centralGroup D, hne, fun K hK hle => by
        by_cases h : K = centralGroup R D
        · exact Or.inl h
        · exact Or.inr (hall K hK hle h)⟩
    have hlt : centralGroup R D < K := lt_of_le_of_ne hle (Ne.symm hKne)
    exact ⟨K, hK, hlt, hKtop, isWeakTI_conjSub_image_of_lt hR hiso hnd hD hK hlt hKtop⟩
  · rintro ⟨K, hK, hlt, hKtop, -⟩ hmax
    rcases hmax.2.2 K hK hlt.le with h | h
    · exact hlt.ne h.symm
    · exact hKtop h

end Sigma

end CFSG.Timmesfeld.ARS
