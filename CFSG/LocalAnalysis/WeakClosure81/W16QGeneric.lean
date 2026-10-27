module

public import CFSG.LocalAnalysis.WeakClosure81.W16QSetup
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_elemCenterIn_of_le_centralizer {T Z : Subgroup G} (hZT : Z ≤ T)
    (hZc : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) (hZ2 : ∀ z ∈ Z, z * z = 1) :
    Z ≤ elemCenterIn 2 T := by
  intro z hz
  rw [mem_elemCenterIn_iff]
  refine ⟨hZT hz, ?_⟩
  intro A hA
  obtain ⟨hAT, hAe, hAcard⟩ := mem_elemFamilyIn.1 hA
  haveI : IsElementaryAbelian 2 ↥A := hAe
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hZ2 z hz
  haveI : IsElementaryAbelian 2 ↥(Subgroup.zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hzcent : Subgroup.zpowers z ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun a ha => (hZc z hz a (hAT ha)).symm
  have hB : IsElementaryAbelian 2 ↥(A ⊔ Subgroup.zpowers z) :=
    IsElementaryAbelian.sup_of_le_centralizer hzcent
  have hBT : A ⊔ Subgroup.zpowers z ≤ T :=
    sup_le hAT (Subgroup.zpowers_le.2 (hZT hz))
  have hcard : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≤ Nat.card ↥A := by
    have h := card_le_pow_pRank_of_le (p := 2) hBT hB
    rwa [← hAcard] at h
  have hEq : A ⊔ Subgroup.zpowers z = A :=
    (Subgroup.eq_of_le_of_card_ge (H := A) le_sup_left hcard).symm
  exact hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem fam16Q_normalizer {M V₀ U R K E : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hUE : U ⊔ V₀ ≤ E) (hR : R ≤ normalizer (E : Set G)) (hK : K ≤ normalizer (E : Set G))
    (hKU : K ≤ centralizer (U : Set G)) (hKM : ¬ K ≤ M) :
    Fam16Q M V₀ U R (normalizer (E : Set G)) := by
  refine ⟨hR, fun h => hKM fun k hk => h ⟨hK hk, hKU hk⟩, ?_⟩
  have hle : conjClosure (U ⊔ V₀) (normalizer (E : Set G)) ≤ E :=
    CFSG.Quasithin.conjClosure_le fun h hh z hz => (Subgroup.mem_normalizer_iff.1 hh z).1 (hUE hz)
  intro x hx y hy
  exact hE x (hle hx) y (hle hy)

theorem Cfg1616.exists_fam16Q_of_forall_le {M V₀ V U S H : Subgroup G}
    (c : Cfg1616 M V₀ V U S H) {R : Subgroup G} (hR : IsSylowIn 2 R (F11.CTilde M V₀ V))
    (hSR : S ≤ R) (hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S)
    (hA : ∀ A ∈ elemFamilyIn 2 (tSub16 V₀ S), A ≤ qSub16 V₀ V S H) :
    ∃ H' : Subgroup G, Fam16Q M V₀ U R H' := by
  have hEq := elemCenterIn_eq_of_forall_le 2 hQT hA
  have hZV : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hUE : U ⊔ V₀ ≤ elemCenterIn 2 (qSub16 V₀ V S H) := by
    rw [hEq]
    refine le_elemCenterIn_of_le_centralizer (hZV.trans c.V_le_tSub16) ?_ ?_
    · intro z hz t ht
      have hU : U ≤ centralizer ({t} : Set G) := fun u hu =>
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (c.cex.S_le_centralizer ht.1) u hu)
      have hV₀ : V₀ ≤ centralizer ({t} : Set G) := fun w hw =>
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 ht.2 w hw)
      exact Subgroup.mem_centralizer_singleton_iff.1 (sup_le hU hV₀ hz)
    · intro z hz
      have := c.cex.hyp.h6.elemAbelian.2 z (hZV hz)
      rwa [pow_two] at this
  refine ⟨normalizer (elemCenterIn 2 (qSub16 V₀ V S H) : Set G), fam16Q_normalizer ?_ hUE ?_ ?_
    c.conjClosure_le_centralizer c.not_conjClosure_le⟩
  · exact (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.1
      (elemCenterIn_isElementaryAbelian 2 (qSub16 V₀ V S H))).1
  · exact (Cex16.le_normalizer_tSub16 c.one c.std c.cex hR.isPGroup hR.le hSR).trans
      (normalizer_le_normalizer_elemCenterIn_of_forall_le 2 hQT hA)
  · exact (c.conjClosure_le_H.trans c.le_normalizer_qSub16).trans
      (normalizer_le_normalizer_elemCenterIn 2 (qSub16 V₀ V S H))

end CFSG.LocalAnalysis.WeakClosure81

end
