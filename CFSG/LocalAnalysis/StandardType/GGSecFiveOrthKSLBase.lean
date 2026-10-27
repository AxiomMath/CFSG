module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGKSLClassicalTag (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def GGSecFiveOrthKSLOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K J : Subgroup G) (x : G),
    orderOf x = 3 → x ∈ Subgroup.normalizer (K : Set G) →
    (¬ ∀ k ∈ K, ∃ c ∈ Subgroup.center ↥K, (c : G) = k * x * k⁻¹ * x⁻¹) →
    LargeEvenMarking K (fun lab _ _ I _ θ => S lab ∧ lab.n = 1 ∧
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = x⁻¹ * l * x) φ) →
    CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K) →
    (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) →
    ∃ m : ℕ, 8 ≤ m ∧ Subgroup.center ↥K = ⊥ ∧ Nonempty (↥K ≃* ↥(StatedSL m (ZMod 2)))

theorem ggSecFiveOrthKSLInput_of_on {S : LargeEvenLabel → Prop} (h : GGSecFiveOrthKSLOn S)
    (hS : ∀ lab, LargeEvenInLambda2 lab → lab.n = 1 → S lab) : GGSecFiveOrthKSLInput := by
  intro G _ _ K J x hx3 hxN hnc hmark hJ hJf
  obtain ⟨hK, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, hn, _⟩ := largeEvenRawDatum_exists hraw
  exact h G K J x hx3 hxN hnc ⟨hK, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hS lab hlab hn, hP⟩) hraw⟩ hJ hJf

theorem GGSecFiveOrthKSLOn.mono {S T : LargeEvenLabel → Prop} (hS : GGSecFiveOrthKSLOn S)
    (h : ∀ lab, LargeEvenInLambda2 lab → lab.n = 1 → T lab → S lab) : GGSecFiveOrthKSLOn T := by
  intro G _ _ K J x hx3 hxN hnc hmark hJ hJf
  obtain ⟨hK, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, hT, hn, _⟩ := largeEvenRawDatum_exists hraw
  exact hS G K J x hx3 hxN hnc ⟨hK, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _, hP⟩ => ⟨hs, hna, θ, h lab hlab hn hT, hP⟩) hraw⟩ hJ hJf

theorem GGSecFiveOrthKSLOn.or {S T : LargeEvenLabel → Prop} (hS : GGSecFiveOrthKSLOn S)
    (hT : GGSecFiveOrthKSLOn T) : GGSecFiveOrthKSLOn fun lab => S lab ∨ T lab := by
  intro G _ _ K J x hx3 hxN hnc hmark hJ hJf
  obtain ⟨hK, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, hST, _⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G K J x hx3 hxN hnc ⟨hK, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hP⟩ => ⟨hs, hna, θ, h, hP⟩) hraw⟩ hJ hJf
  · exact hT G K J x hx3 hxN hnc ⟨hK, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hP⟩ => ⟨hs, hna, θ, h, hP⟩) hraw⟩ hJ hJf

section Proj

variable {X : Type} [Group X] {R : Type} [Group R]

theorem ggKSL_proj_surjective (θ : X ⧸ Subgroup.center X ≃* R) :
    Function.Surjective (TablePThreeKG.proj θ) := fun r => by
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, rfl⟩

theorem ggKSL_ker_proj_le_center (θ : X ⧸ Subgroup.center X ≃* R) :
    (TablePThreeKG.proj θ).ker ≤ Subgroup.center X := fun l hl => by
  have h0 : θ (QuotientGroup.mk l) = 1 := hl
  have h1 : (QuotientGroup.mk l : X ⧸ Subgroup.center X) = 1 := by
    simpa using θ.injective (h0.trans (map_one θ).symm)
  exact (QuotientGroup.eq_one_iff l).mp h1

theorem ggInducedAut_eq_of_proj (θ : X ⧸ Subgroup.center X ≃* R) {e : MulAut X}
    {φ : MulAut R} (h : ∀ l : X, φ (TablePThreeKG.proj θ l) = TablePThreeKG.proj θ (e l)) :
    ggInducedAut θ e = φ := by
  ext r
  obtain ⟨l, rfl⟩ := ggKSL_proj_surjective θ r
  rw [h l]
  exact ggInducedAut_apply θ e l

end Proj

section Transport

variable {G : Type} [Group G] {K J : Subgroup G} {x : G}

theorem ggKSL_centralizer_inv (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

theorem ggKSL_transport (hx3 : orderOf x = 3) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K)) :
    ∃ e : MulAut ↥K, e ^ 3 = 1 ∧ (∀ l : ↥K, (e l : G) = x⁻¹ * l * x) ∧
      CFSG.Assembly.IsComponentOf (J.subgroupOf K) (ggFixSub e) ∧
      Nonempty (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
        ↥J ⧸ Subgroup.center ↥J) := by
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hxN
  have he : ∀ l : ↥K, ((K.normalizerMonoidHom ⟨x⁻¹, hxN'⟩ l : ↥K) : G) = x⁻¹ * l * x := by
    intro l
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  refine ⟨K.normalizerMonoidHom ⟨x⁻¹, hxN'⟩, ?_, he, ?_, ?_⟩
  · rw [← map_pow]
    have h1 : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simp [inv_pow, ← hx3])
    rw [h1, map_one]
  · have hJ' : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({x⁻¹} : Set G)) := by
      rw [ggKSL_centralizer_inv, inf_comm]
      exact hJ
    exact ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN' hJ'
  · have hJK : J ≤ K := hJ.1.trans inf_le_right
    exact ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)⟩

end Transport

end CFSG.StandardType

end
