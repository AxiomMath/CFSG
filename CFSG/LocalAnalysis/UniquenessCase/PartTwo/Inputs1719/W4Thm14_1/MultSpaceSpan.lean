module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

theorem stableUnder_iSup_map {L : Subgroup (MulAut W)} (A : Subgroup W) :
    StableUnder L (⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) := by
  intro l hl u hu
  refine Subgroup.iSup_induction
    (fun g : MulAut W => ⨆ (_ : g ∈ L), A.map (g : MulAut W).toMonoidHom)
    (C := fun u => l u ∈ (⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom)) hu ?_ ?_ ?_
  · intro g y hy
    refine Subgroup.iSup_induction (fun _ : g ∈ L => A.map (g : MulAut W).toMonoidHom)
      (C := fun y => l y ∈ (⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom)) hy ?_ ?_ ?_
    · intro hg a ha
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      exact Subgroup.mem_iSup_of_mem (l * g)
        (Subgroup.mem_iSup_of_mem (L.mul_mem hl hg)
          (Subgroup.mem_map.mpr ⟨a₀, ha₀, rfl⟩))
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro x y hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy

theorem le_stabSub_fixV {T M : Subgroup (MulAut W)}
    (hM : M ≤ Subgroup.centralizer (T : Set (MulAut W))) : M ≤ stabSub (fixV T) := by
  intro m hm
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    rw [mem_fixV] at hu ⊢
    intro t ht
    have hcomm : m * t = t * m := (Subgroup.mem_centralizer_iff.mp (hM hm) t ht).symm
    have hmul : m (t u) = t (m u) := by
      rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
    calc t u = m⁻¹ (m (t u)) := (MulEquiv.symm_apply_apply m (t u)).symm
      _ = m⁻¹ (t (m u)) := by rw [hmul]
      _ = m⁻¹ (m u) := by rw [hu t ht]
      _ = u := MulEquiv.symm_apply_apply m u
  · intro hu
    rw [mem_fixV] at hu ⊢
    intro t ht
    have hcomm : t * m = m * t := Subgroup.mem_centralizer_iff.mp (hM hm) t ht
    calc t (m u) = (t * m) u := by rw [MulAut.mul_apply]
      _ = (m * t) u := by rw [hcomm]
      _ = m (t u) := by rw [MulAut.mul_apply]
      _ = m u := by rw [hu t ht]

theorem iSup_map_fixV_eq_top {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {T : Subgroup (MulAut W)}
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) :
    (⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom) = ⊤ := by
  have hTS : fixV T ≤ (⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom) := by
    intro u hu
    exact Subgroup.mem_iSup_of_mem (1 : MulAut W)
      (Subgroup.mem_iSup_of_mem L.one_mem
        (Subgroup.mem_map.mpr ⟨u, hu, by
          change (1 : MulAut W) u = u
          rw [MulAut.one_apply]⟩))
  have hIle : ∀ I ∈ irrSet L, I ≤ (⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom) := by
    intro I hI
    let S : Subgroup W := ⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom
    have hJstab : StableUnder L (I ⊓ S) :=
      stableUnder_inf (stableUnder_of_mem_irrSet hI) (stableUnder_iSup_map (fixV T))
    have hNbot : I ⊓ fixV L = ⊥ := by rw [hfix, inf_bot_eq]
    have hJneBot : I ⊓ S ≠ ⊥ := by
      intro hbot
      obtain ⟨⟨z, hzI, hzT⟩, hz1, -⟩ :=
        (Nat.card_eq_two_iff' (1 : ↥(I ⊓ fixV T))).mp (hT I hI)
      have hzS : z ∈ S := hTS hzT
      have hzbot : z ∈ (⊥ : Subgroup W) := by
        rw [← hbot]
        exact ⟨hzI, hzS⟩
      exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzbot))
    rcases hI.2.2.2.2 (I ⊓ S) hJstab (hNbot.symm ▸ bot_le) inf_le_left with hJN | hJI
    · exact absurd (by rw [hJN, hNbot]) hJneBot
    · calc I = I ⊓ S := hJI.symm
        _ ≤ S := inf_le_right
  refine le_antisymm le_top ?_
  rw [← hspan]
  exact iSup₂_le hIle

theorem eq_one_of_mem_centralizer_of_forall_fixV {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {T : Subgroup (MulAut W)}
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) {m : MulAut W}
    (hm : m ∈ Subgroup.centralizer (L : Set (MulAut W))) (hmT : ∀ u ∈ fixV T, m u = u) :
    m = 1 := by
  have hS : (⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom) = ⊤ :=
    iSup_map_fixV_eq_top hfix hspan hT
  have hstab : StableUnder L (fixV (Subgroup.zpowers m)) := by
    intro l hl u hu
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    have hcomm : m * l = l * m := (Subgroup.mem_centralizer_iff.mp hm l hl).symm
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hu]
  have hTF : fixV T ≤ fixV (Subgroup.zpowers m) := by
    intro u hu
    rw [mem_fixV_zpowers_iff_apply]
    exact hmT u hu
  have hSF : (⨆ g ∈ L, (fixV T).map (g : MulAut W).toMonoidHom) ≤
      fixV (Subgroup.zpowers m) := by
    refine iSup₂_le fun g hg => ?_
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact hstab g hg v (hTF hv)
  have htop : fixV (Subgroup.zpowers m) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hS]
    exact hSF
  ext u
  have hu : u ∈ fixV (Subgroup.zpowers m) := by rw [htop]; exact Subgroup.mem_top u
  rw [mem_fixV_zpowers_iff_apply] at hu
  simpa using hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
