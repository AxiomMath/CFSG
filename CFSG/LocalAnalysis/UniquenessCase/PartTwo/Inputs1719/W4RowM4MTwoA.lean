module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Chain
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup

theorem two_pow_four_le_index_of_gen {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {G : Type} [Group G] [Finite G] (ι : G →* MulAut W)
    (hι : Function.Injective ι) {c t : G} (hct : IsConj c t)
    (hgen : ∃ cs : List G, cs.length ≤ 20 ∧
      Subgroup.closure {v : G | ∃ g ∈ cs, v = g * c * g⁻¹} = ⊤)
    {x y : Fin 4 → G} {z : G} (hcfg : HeisCfg 3 4 x y z) :
    2 ^ 4 ≤ (fixV (zpowers (ι t))).index := by
  obtain ⟨h, hh⟩ := isConj_iff.1 hct
  obtain ⟨cs, hcslen, hcs⟩ := hgen
  have hconv : c = h⁻¹ * t * h := by rw [← hh]; group
  have hstep : ∀ g : G, ι (g * h⁻¹) * ι t * (ι (g * h⁻¹))⁻¹ = ι (g * c * g⁻¹) := by
    intro g
    rw [hconv]
    simp only [map_mul, map_inv]
    group
  set hs : List (MulAut W) := cs.map (fun g => ι (g * h⁻¹)) with hhs
  have hhslen : hs.length ≤ 20 := by rw [hhs, List.length_map]; exact hcslen
  have himg : {y | ∃ h' ∈ hs, y = h' * ι t * h'⁻¹} =
      ι '' {v : G | ∃ g ∈ cs, v = g * c * g⁻¹} := by
    ext y
    constructor
    · rintro ⟨h', hh', rfl⟩
      rw [hhs, List.mem_map] at hh'
      obtain ⟨g, hg, rfl⟩ := hh'
      exact ⟨g * c * g⁻¹, ⟨g, hg, rfl⟩, (hstep g).symm⟩
    · rintro ⟨v, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨ι (g * h⁻¹), by rw [hhs, List.mem_map]; exact ⟨g, hg, rfl⟩, (hstep g).symm⟩
  have hclosure : Subgroup.closure {y | ∃ h' ∈ hs, y = h' * ι t * h'⁻¹} = ι.range := by
    rw [himg, ← MonoidHom.map_closure, hcs, MonoidHom.range_eq_map]
  have hzmem : ι z ∈ ι.range := MonoidHom.mem_range.2 ⟨z, rfl⟩
  have h1 : (fixV (zpowers (ι z))).index ≤ (fixV (zpowers (ι t))).index ^ hs.length := by
    calc (fixV (zpowers (ι z))).index
        ≤ (fixV ι.range).index := index_fixV_le_of_le (Subgroup.zpowers_le.2 hzmem)
      _ = (fixV (Subgroup.closure {y | ∃ h' ∈ hs, y = h' * ι t * h'⁻¹})).index := by
            rw [hclosure]
      _ ≤ (fixV (zpowers (ι t))).index ^ hs.length :=
            B42Disp.index_fixV_closure_conj_elt_le (ι t) hs
  have hιz : ι z ≠ 1 := by
    intro hz1
    exact hcfg.z1 (hι (by rw [hz1, map_one]))
  have hbound : 2 ^ (3 ^ 4 * orderOf (2 : ZMod 3)) ≤
      Nat.card (CFSG.QuasithinUnique.Setup.X1.imgT (ι z)) :=
    two_pow_le_card_imgT_of_heisCfg (p := 3) (n := 4) hW (by norm_num)
      (HeisCfg.map ι hcfg hιz)
  have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hexp : 3 ^ 4 * 2 = 162 := by norm_num
  have hbound' : 2 ^ 162 ≤ Nat.card (CFSG.QuasithinUnique.Setup.X1.imgT (ι z)) := by
    simpa only [hord, hexp] using hbound
  have hcard :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.index_fixV_zpowers_eq_card_imgT
      (W := W) (ι z)
  have hzbound : 2 ^ 162 ≤ (fixV (zpowers (ι z))).index := by
    rw [hcard]; exact hbound'
  have h2 : 2 ^ 162 ≤ (fixV (zpowers (ι t))).index ^ hs.length := hzbound.trans h1
  have hpow : (fixV (zpowers (ι t))).index ^ hs.length ≤
      (fixV (zpowers (ι t))).index ^ 20 :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hhslen
  have h2' : 2 ^ 162 ≤ (fixV (zpowers (ι t))).index ^ 20 := h2.trans hpow
  by_contra hnot
  have hlt : (fixV (zpowers (ι t))).index < 2 ^ 4 := not_le.1 hnot
  have hlt80 : (fixV (zpowers (ι t))).index ^ 20 < (2 ^ 4) ^ 20 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  have h80 : 2 ^ 162 < 2 ^ 80 := by
    have hpow80 : (2 ^ 4) ^ 20 = 2 ^ 80 := by rw [← pow_mul]
    calc 2 ^ 162 ≤ (fixV (zpowers (ι t))).index ^ 20 := h2'
      _ < (2 ^ 4) ^ 20 := hlt80
      _ = 2 ^ 80 := hpow80
  have hle : 2 ^ 80 ≤ 2 ^ 162 :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by norm_num : 80 ≤ 162)
  exact absurd h80 (not_lt.2 hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
