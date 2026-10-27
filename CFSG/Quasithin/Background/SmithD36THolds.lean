module

public import CFSG.Quasithin.Background.SmithD36TSec
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.F918L4
public import CFSG.Quasithin.Background.F918R7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem d36QhatGluedTight_of_b42
    (hB42 : AsB42) (hA21 : AsA21SQTKSection) (hL38 : D3L38) :
    D36QhatGluedTight := by
  intro W _ _ M Mp T L V t n hD hex
  exfalso
  obtain ⟨A, hA⟩ := hex
  have : IsSimpleGroup ↥L :=
    H13.VolI.isSimpleGroup_of_a38Types (hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq).1
  obtain ⟨x, y, hxX, -, hg1, hxy, -, hxU, hxN, hyL, hF5⟩ := d36t_lift hL38 n hA
  have hF6 : ∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      ¬ ∀ w ∈ V.map s.toMonoidHom, (x : MulAut W) w * w⁻¹ ∈ fixV L :=
    fun s _ hsN => d36t_not_triv hL38 n x y hxX hg1 hxy hxN hyL hsN
  have hUV := d36t_U_eq_V hL38 n hxU hxN hF5 hF6
  obtain ⟨v₀, hv₀, hv₀x⟩ : ∃ v ∈ V, (x : MulAut W) v * v⁻¹ ∉ fixV L := by
    by_contra h
    push Not at h
    refine hF6 1 T.one_mem (Subgroup.one_mem _) fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := hw
    simpa using h v hv
  have hDle : commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom ≤
      V ⊓ fixV Mp := fun d hd => ⟨hUV ▸ hd.1, d36t_D_le_fixV hL38 n hd⟩
  rw [hUV] at hxU hF5
  have hcard := d36t_card_fixV_le_two hB42 hA21 hL38 n hxX hxU hF5 hv₀ hv₀x
  have h4 : 2 ^ 2 ≤ Nat.card ↥(commSub (orbSup T V) L ⊓
      (commSub (orbSup T V) L).map t.toMonoidHom) := by
    rw [card_eq_two_pow n.std.hyp.exp]
    exact Nat.pow_le_pow_right (by norm_num) hD
  have h5 := Subgroup.card_le_of_le hDle
  omega

theorem d36QhatGluedTight_holds
    : D36QhatGluedTight :=
  d36QhatGluedTight_of_b42 asB42_holds asA21SQTKSection (d3L38_of_a38 d3A38_holds)

end CFSG.Quasithin
