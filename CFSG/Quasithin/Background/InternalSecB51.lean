module

public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

section AutOn

variable {G : Type} [Group G] {U Y L : Subgroup G}

theorem autOn_le_autOn_of_le (hLY : L ≤ Y) : autOn L U ≤ autOn Y U :=
  CFSG.Quasithin.AutOn.autOn_mono hLY

theorem autOn_normal_of (hYL : Y ≤ Subgroup.normalizer (L : Set G)) :
    ∀ x ∈ autOn Y U, ∀ k ∈ autOn L U, x * k * x⁻¹ ∈ autOn L U := by
  intro x hx k hk
  obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
  obtain ⟨l, hlL, rfl⟩ := Setup.mem_autOn_iff.1 hk
  rw [← map_inv, ← map_mul, ← map_mul]
  refine Setup.mem_autOn_iff.2 ⟨g * l * g⁻¹, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hYL hgY) l).1 hlL

theorem autOn_two_of (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (U : Set G)) :
    ∀ x ∈ autOn Y U, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn L U := by
  intro x hx
  obtain ⟨g, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hx
  obtain ⟨e, he⟩ := h2 _ hgY
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact conjAct_mem_autOn_of_mem_sup hLU _ he

theorem pCoreOf_autOn_eq_bot_of_isPrimeReduced {V M : Subgroup G} (hVM : V ≤ M)
    (hR : IsPrimeReduced 2 (V.subgroupOf M)) : pCoreOf 2 (autOn M V) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVM, hR⟩)

end AutOn

theorem sqtkGroup_subgroup {X : Type} [Group X] [Finite X] (hS : SQTKGroup X)
    (H : Subgroup X) : SQTKGroup ↥H := by
  refine ⟨fun p hp hp2 => ?_, hS.2.subgroup H⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt H.subtype H.subtype_injective
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := hS.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ 2
  omega

theorem centerOf_le_quasithinGenFitting {Ω : Type} [Group Ω] (J : Subgroup Ω) :
    centerOf J ≤ quasithinGenFitting J := by
  refine le_sup_of_le_left (le_sSup ⟨fun x hx => hx.1, ⟨fun n hn g => ?_⟩, ?_⟩)
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := Subgroup.mem_centralizer_iff.mp hn.2 (g : Ω) g.2
    refine ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2), ?_⟩
    have e : (g : Ω) * (n : Ω) * (g : Ω)⁻¹ = n := by rw [h1, mul_inv_cancel_right]
    simpa [e] using hn.2
  · let _ : CommGroup ↥(centerOf J) :=
      { (inferInstance : Group ↥(centerOf J)) with
        mul_comm := fun a b => Subtype.ext
          ((Subgroup.mem_centralizer_iff.mp b.2.2 (a : Ω) a.2.1)) }
    exact CommGroup.isNilpotent

section B51

variable {G : Type} [Group G] [Finite G] {W Y L : Subgroup G} [IsMulCommutative ↥W]

theorem b51Hyp_ffJ_autOn (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G))
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hS : SQTKGroup ↥(autOn L W)) {A : Subgroup (MulAut ↥W)}
    (hA : IsFFStarOffender (autOn Y W) A) (hLA : ⁅autOn L W, A⁆ = autOn L W) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) ∧ A ≤ ffJ (autOn Y W) := by
  set X := autOn Y W with hX
  set K := autOn L W with hK
  set J := ffJ X with hJ
  have hKX : K ≤ X := autOn_le_autOn_of_le hLY
  have hKn := autOn_normal_of (U := W) hYL
  have hX2 := autOn_two_of (Y := Y) ((hLY.trans hYW)) h2
  have hKJ : K ≤ J := B1Red.K_le_ffJ hKX hA hLA
  have hJX : J ≤ X := B6.ffJ_le X
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hF : quasithinGenFitting J = K :=
    quasithinGenFitting_eq_of_two_pow hKJ (fun y hy l hl => hKn y (hJX hy) l hl)
      (B1Red.isQuasisimple_to_open hq) (fun y hy => hX2 y (hJX hy)) hQ
  have hZ : centerOf J ≤ K := hF ▸ centerOf_le_quasithinGenFitting J
  exact ⟨⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hKJ, hQ, (ffJ_ffJ _).symm⟩, B6.le_ffJ hA⟩

theorem b53Hyp_ffJ_autOn (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hS : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) : B53Hyp (ffJ (autOn Y W)) := by
  set X := autOn Y W with hX
  set J := ffJ X with hJ
  have hJX : J ≤ X := B6.ffJ_le X
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  set ρ := autOnHom hYW with hρ
  set H : Subgroup ↥Y := (J.subgroupOf X).comap ρ with hH
  let f : ↥H →* ↥J :=
    { toFun := fun h => ⟨((ρ (h : ↥Y) : ↥X) : MulAut ↥W), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := autOnHom_surjective hYW ⟨j, hJX hj⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show ρ y ∈ J.subgroupOf X
      rw [Subgroup.mem_subgroupOf, hy]
      exact hj
    · apply Subtype.ext
      show ((ρ y : ↥X) : MulAut ↥W) = j
      rw [hy]
  refine ⟨hQ, (ffJ_ffJ _).symm, ↥H, inferInstance, inferInstance, f.ker, inferInstance,
    sqtkGroup_subgroup hS H, ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem b56Cases_of_isFFModule (h56 : AsB56) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hS : SQTKGroup ↥Y)
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hFF : IsFFModule (autOn Y W)) :
    B56Case1 (ffJ (autOn Y W)) ∨ B56Case2 (ffJ (autOn Y W)) ∨ B56Case3 (ffJ (autOn Y W)) ∨
      B56Case4 (ffJ (autOn Y W)) ∨ B56Case5 (ffJ (autOn Y W)) := by
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v v.2)
  exact h56 ↥W hV _ (ffJ_ne_bot_of_isFFModule hV hFF) (b53Hyp_ffJ_autOn hYW hS hO2)

end B51

end CFSG.Quasithin.InternalSec
