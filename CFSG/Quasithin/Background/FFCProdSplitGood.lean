module

public import CFSG.Quasithin.Background.FFCProdSplit
public import CFSG.Quasithin.Background.FFC5S3
public import CFSG.Quasithin.Background.FFC4CaseI

public section

namespace CFSG.Quasithin

namespace FFC

namespace ProdSplit

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G G₁ G₂ : Subgroup (MulAut V)}

theorem false_of_threeRank2 (hG₁ : G₁ ≤ G) (hG₂ : G₂ ≤ G)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hq : IsQuotientOfSQTKTauCeti ↥G)
    (hs3 : S3Elems ↥G₁) (hX : ThreeRank2 ↥G₂) : False := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := hX
  obtain ⟨t, c, ht2, ht1, hc3, hc1, htc⟩ := hs3
  have htc' : (t : MulAut V) * c * (t : MulAut V)⁻¹ = (c : MulAut V)⁻¹ := by
    have := congrArg Subtype.val htc
    simpa using this
  have hxG : (x : MulAut V) ∈ G := hG₂ x.2
  have hyG : (y : MulAut V) ∈ G := hG₂ y.2
  refine false_of_commuting_threes hq (t := (t : MulAut V)) (c := (c : MulAut V))
    (x := (x : MulAut V)) (y := (y : MulAut V)) (hG₁ t.2) (hG₁ c.2) hxG hyG
    (by simpa using congrArg Subtype.val ht2) (fun h' => ht1 (Subtype.ext h'))
    (by simpa using congrArg Subtype.val hc3) (fun h' => hc1 (Subtype.ext h')) htc'
    (fun h' => hx1 (Subtype.ext h')) (by simpa using congrArg Subtype.val hx3)
    (by simpa using congrArg Subtype.val hy3) (by simpa using congrArg Subtype.val hxy) ?_ ?_ ?_ ?_ ?_
  · intro hmem
    apply hyx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  · exact (hcomm t t.2 _ x.2).symm
  · exact (hcomm c c.2 _ x.2).symm
  · exact (hcomm t t.2 _ y.2).symm
  · exact (hcomm c c.2 _ y.2).symm

theorem good (hsup : G₁ ⊔ G₂ = G) (hinf : G₁ ⊓ G₂ = ⊥)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1)
    (hI : B58Inputs) (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥)
    (hs3 : S3Elems ↥G₁) : GoodFactor (autSub G₂ (fixV G₁)) := by
  have hq := isQuotientOfSQTKTauCeti_of_b53 hc.hyp
  have hb53 := b53 hsup hcomm hfaith hc.hyp.1 hc.hyp.2.1 hq
  have hV₂ : ∀ v : ↥(fixV G₁), v ^ 2 = 1 := fun v => Subtype.ext (hc.hV v)
  have hmin := hc.minimal ↥(fixV G₁) hV₂ (autSub G₂ (fixV G₁)) (autSub_ne_bot hcomm hfaith hG₂) hb53
    (card_lt hsup hinf hcomm hfaith hG₁)
  have hno : ¬ ThreeRank2 ↥(autSub G₂ (fixV G₁)) := fun hx =>
    false_of_threeRank2 (hsup ▸ le_sup_left) (hsup ▸ le_sup_right) hcomm hq hs3
      (hx.of_mulEquiv (resEquiv (stab hcomm) hfaith).symm)
  rcases hmin with hc1 | hc2 | hc3 | hc4 | hc5
  · exact good_of_case1 hI ↥(fixV G₁) hV₂ _ hb53 (autSub_ne_bot hcomm hfaith hG₂) hno hc1
  · exact good_of_case2 hV₂ hc2
  · exact absurd (threeRank2_of_case3 hc3) hno
  · exact absurd (threeRank2_of_case4 hc4) hno
  · exact absurd (threeRank2_of_case5 hc5) hno

end ProdSplit

end FFC

end CFSG.Quasithin
