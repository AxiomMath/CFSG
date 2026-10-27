module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem card_center_eq_card_inf_centralizer {M : Type} [Group M] (L' : Subgroup M) :
    Nat.card (Subgroup.center L') =
      Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  have hmap : (Subgroup.center L').map L'.subtype =
      L' ⊓ Subgroup.centralizer (L' : Set M) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
    · rintro ⟨hgL, hgc⟩
      refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc y.1 y.2)
  rw [← hmap]
  exact Nat.card_congr
    ((Subgroup.center L').equivMapOfInjective L'.subtype L'.subtype_injective).toEquiv

theorem position_innerModel_twE6
    {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) {M : Type} [Group M] [Finite M]
    {L' E : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* TwE6Delta.RecipeR K n}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E (TwE6Delta.RecipeI K n) θ hE) :
    ∃ E₀ : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian p E₀ ∧ p ^ 4 ≤ Nat.card E₀ ∧
      (∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ E₀, g * e = e * g) → g ^ p = 1 → g ∈ E₀) ∧
      ∀ e : E, ∃ r ∈ E₀, ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj r := by
  classical
  have : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  set A : Subgroup (MulAut (TwE6Delta.RecipeR K n)) := ggLAutImage L' θ E with hAdef
  have hI : (A : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    intro a ha
    rw [hAdef] at ha
    simp only [ggLAutImage] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x := Subtype.ext rfl
    rw [← hxe]
    exact hpos.2.2.2.1 ⟨(x : M), hx⟩
  have hA : IsElemAbelian p A := by
    rw [hAdef]
    exact ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hpos.2.1 _) (ggLAut L' θ)
  have hperf : commutator (TwE6Delta.RecipeR K n) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ y
    have hl : l ∈ commutator L' := by rw [hpos.1]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem (ggQuotHom θ) hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ggQuotHom_surjective θ), ← commutator_def] at h1
  have hZ : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥ :=
    TwE6Delta.center_recipeR_eq_bot hn hK
  have hIp : GGOutdiagPrime p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hcp : GGCenterPrime p (TwE6Delta.RecipeR K n) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  have hZc : ¬ p ∣ Nat.card (Subgroup.center L') :=
    hcp ↥L' (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hpos.1
  have hZ' : ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
    rw [← card_center_eq_card_inf_centralizer L']
    exact hZc
  have hscA : GGTorusSelfCent p A := by
    rw [hAdef]
    exact ggTorusSelfCent_ggLAutImage hpos hp hZ'
  obtain ⟨Λ, hΛeq, -, -, hAΛ, hEabΛ, hcardΛ, hscΛ⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp (MonoidHom.id (TwE6Delta.RecipeR K n))
      (fun x => ⟨x, rfl⟩) (by simp) hperf hA
      (fun a ha => ⟨a, hI ha, fun _ => rfl⟩) hscA
  have hΛconj : Λ = (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
    MonoidHom.ext fun e => hΛeq (x := e) rfl
  set E₀ : Subgroup (TwE6Delta.RecipeR K n) :=
    A.comap (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) with hE₀def
  have hcomap : A.comap Λ = E₀ := by rw [hΛconj, hE₀def]
  refine ⟨E₀, hcomap ▸ hEabΛ, ?_, hcomap ▸ hscΛ, ?_⟩
  · have hE₀card : Nat.card E₀ = Nat.card A := hcomap ▸ hcardΛ
    have hlift : p ^ TwE6Delta.liftRank p ≤ Nat.card A := by
      rw [hAdef]
      exact pow_le_card_ggLAutImage hpos hp (ggTorusLift_twE6Add_holds hn hK hp hpq)
    have hlift5 : p ^ 5 ≤ Nat.card A := by rwa [TwE6Delta.liftRank_of_ne hp3] at hlift
    rw [hE₀card]
    exact (Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 5)).trans hlift5
  · intro e
    have ha : ggLAut L' θ ⟨e, hE e.2⟩ ∈ A := by
      rw [hAdef, ggLAutImage]
      exact Subgroup.mem_map.mpr ⟨⟨e, hE e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
    obtain ⟨r, hr⟩ := hAΛ _ ha
    rw [hΛconj] at hr
    exact ⟨r, by show MulAut.conj r ∈ A; rw [hr]; exact ha, hr.symm⟩

end CFSG.StandardType
