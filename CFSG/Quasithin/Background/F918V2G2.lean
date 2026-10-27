module

public import CFSG.Quasithin.Background.F918V2Defs
public import CFSG.Quasithin.Background.F918V2GA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

variable {W : Type} [CommGroup W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem v2g_lt (hlt : commSub V L < commSub (orbSup T V) L) : V < orbSup T V := by
  refine lt_of_le_of_ne (le_orbSup T V) fun h => ?_
  rw [← h] at hlt
  exact lt_irrefl _ hlt

theorem v2g_hC [Finite W] (hD : D3Std M L T L V) :
    ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g := by
  obtain ⟨hVinv, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hq : CFSG.IsQuasisimple ↥L := hD.hyp.quasi
  let K : Subgroup ↥L :=
    { carrier := {g | ∀ v ∈ V, (g : MulAut W) v = v}
      one_mem' := fun v _ => rfl
      mul_mem' := fun {a b} ha hb v hv => by
        show (a : MulAut W) ((b : MulAut W) v) = v
        rw [hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        show ((a : MulAut W)⁻¹) v = v
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact (ha v hv).symm }
  have hKn : K.Normal := by
    refine ⟨fun k hk g v hv => ?_⟩
    show ((g : MulAut W) * (k : MulAut W) * (g⁻¹ : ↥L) ) v = v
    have h1 : ((g : MulAut W)⁻¹) v ∈ V := hVinv _ (L.inv_mem g.2) v hv
    simp only [MulAut.mul_apply, Subgroup.coe_inv]
    rw [hk _ h1]
    exact MulAut.apply_inv_self _ _ _
  intro g hg hgV x hx
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKn with h | h
  · exfalso
    have hall : ∀ v ∈ V, ∀ y ∈ L, y v = v := fun v hv y hy => by
      have : (⟨y, hy⟩ : ↥L) ∈ K := by rw [h]; trivial
      exact this v hv
    have hV : V ≤ fixV L := fun v hv y hy => hall v hv y hy
    have : commSub V L = ⊥ := commSub_eq_bot_iff.2 hV
    rw [hVcomm] at this
    rw [this] at hVlt
    exact absurd hVlt (by simp)
  · have hgK : (⟨g, hg⟩ : ↥L) ∈ K := fun v hv => hgV v hv
    have := Subgroup.mem_center_iff.mp (h hgK) ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm


variable {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q]

theorem v2g_orbSup_map (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M)
    (hsum : orbSup T V = V ⊔ V.map (t : MulAut W).toMonoidHom ⊔ (orbSup T V ⊓ fixV L)) :
    (orbSup T V).map π = V.map π ⊔ t • V.map π := by
  rw [v2g_smul_map π hπM, hsum, Subgroup.map_sup, Subgroup.map_sup]
  have : (orbSup T V ⊓ fixV L).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, ← hker]
    exact (inf_le_right.trans (by rw [hker]))
  rw [this, sup_bot_eq]


theorem v2g_hnot [Finite W] (hD : D3Std M L T L V) (hVc : V = commSub V L) (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (htT : (t : MulAut W) ∈ T)
    (hne : orbSup T V ≠ ⊤) :
    ∃ g : ↥M, ¬ g • V.map π ≤ V.map π ⊔ t • V.map π := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  obtain ⟨hVinv, -, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  set Y : Subgroup W := V ⊔ V.map (t : MulAut W).toMonoidHom with hY
  have htM : (t : MulAut W) ∈ M := t.2
  have hLtV : ∀ l ∈ L, ∀ y ∈ V.map (t : MulAut W).toMonoidHom,
      l y ∈ V.map (t : MulAut W).toMonoidHom := by
    rintro l hl _ ⟨v, hv, rfl⟩
    have hl' : ((t : MulAut W)⁻¹ * l * ((t : MulAut W)⁻¹)⁻¹) ∈ L :=
      hMn _ (M.inv_mem htM) l hl
    refine ⟨((t : MulAut W)⁻¹ * l * ((t : MulAut W)⁻¹)⁻¹) v, hVinv _ hl' v hv, ?_⟩
    show (t : MulAut W) (((t : MulAut W)⁻¹ * l * ((t : MulAut W)⁻¹)⁻¹) v) = l ((t : MulAut W) v)
    simp [MulAut.mul_apply]
  have hLY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y := by
    intro l hl y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hVinv l hl a ha) (hLtV l hl b hb)
  have hLconj : ∀ m ∈ M, L.map (MulAut.conj (m : MulAut W)).toMonoidHom = L := fun m hm =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD.hyp.Mp_normal hm)
  have hmV : ∀ m ∈ M, V.map (m : MulAut W).toMonoidHom ≤ Y := by
    intro m hm
    have h1 := hcon ⟨m, hm⟩
    rw [v2g_smul_map π hπM, v2g_smul_map π hπM] at h1
    have h2 : (V.map (m : MulAut W).toMonoidHom).map π ≤ Y.map π := by
      rw [hY, Subgroup.map_sup]
      exact h1
    have h3 : V.map (m : MulAut W).toMonoidHom ≤ Y ⊔ fixV L := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h2 ⟨x, hx, rfl⟩
      refine Subgroup.mem_sup.2 ⟨y, hy, y⁻¹ * x, ?_, by group⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have h4 : commSub (V.map (m : MulAut W).toMonoidHom) L = V.map (m : MulAut W).toMonoidHom := by
      have := commSub_map_conj (m : MulAut W) V L
      rw [hLconj m hm, ← hVc] at this
      exact this
    calc V.map (m : MulAut W).toMonoidHom = commSub (V.map (m : MulAut W).toMonoidHom) L := h4.symm
      _ ≤ commSub (Y ⊔ fixV L) L := commSub_mono h3 le_rfl
      _ = commSub Y L := commSub_sup_fixV le_rfl
      _ ≤ Y := commSub_le_of_invariant hLY
  have hgen := hD.hyp.gen
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  exact (hmV m hm).trans (sup_le (le_orbSup T V) (map_le_orbSup htT))


theorem v2g_twoTypeBase [Finite W] (hD : D3Std M L T L V) (π : W →* Q)
    (hπs : Function.Surjective π)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (htT : (t : MulAut W) ∈ T) (htV : (t : MulAut W) ∉ stabSub V)
    (h4 : ∀ s ∈ T, s ∈ stabSub V ∨ (t : MulAut W)⁻¹ * s ∈ stabSub V)
    (hni : ¬ XMod.Iso ↥(L.subgroupOf M) (V.map π) (t • V.map π)) :
    TwoTypeBase (L.subgroupOf M) (T.subgroupOf M) (V.map π) t := by
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  obtain ⟨hVinv, hVcomm, hVlt, hVmin⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hinv : XMod.IsInv ↥(L.subgroupOf M) (V.map π) := by
    rintro a _ ⟨v, hv, rfl⟩
    have ha : ((a : ↥M) : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp a.2
    show (a : ↥M) • π v ∈ V.map π
    rw [hπM]
    exact ⟨_, hVinv _ ha v hv, rfl⟩
  refine ⟨fun q => ?_, fun g l hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_, hni⟩
  · obtain ⟨w, rfl⟩ := hπs q
    rw [← map_pow, hD.hyp.exp w, map_one]
  · exact Subgroup.mem_subgroupOf.mpr (hMn _ g.2 _ (Subgroup.mem_subgroupOf.mp hl))
  · have hMpM : L ≤ M := le_of_mem_cComp hD.hyp.comp
    refine ⟨hinv, bot_lt_iff_ne_bot.2 fun h => ?_, fun J hJ _ hJle => ?_⟩
    · have hV : V ≤ fixV L := by
        have := (Subgroup.map_eq_bot_iff V).1 h
        rwa [hker] at this
      exact absurd (inf_eq_left.2 hV) hVlt.ne
    · set J' : Subgroup W := V ⊓ J.comap π with hJ'
      have hJ'inv : ∀ x ∈ L, ∀ w ∈ J', x w ∈ J' := by
        rintro x hx w ⟨hwV, hwJ⟩
        refine ⟨hVinv x hx w hwV, ?_⟩
        have h1 := hJ ⟨⟨x, hMpM hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ (π w) hwJ
        change (⟨x, hMpM hx⟩ : ↥M) • π w ∈ J at h1
        rw [hπM] at h1
        exact h1
      rcases hVmin J' hJ'inv (fun x hx => ⟨hx.1, by
          show π x ∈ J
          rw [(MonoidHom.mem_ker).1 (by rw [hker]; exact hx.2 : x ∈ π.ker)]
          exact J.one_mem⟩) inf_le_left with h | h
      · left
        refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
        obtain ⟨v, hv, rfl⟩ := hJle hy
        have : v ∈ J' := ⟨hv, hy⟩
        rw [h] at this
        exact (MonoidHom.mem_ker).1 (by rw [hker]; exact this.2)
      · right
        refine le_antisymm hJle ?_
        rintro _ ⟨v, hv, rfl⟩
        have : v ∈ J' := by rw [h]; exact hv
        exact this.2
  · exact A4.isPGroup_subgroupOf_of_le hD.hyp.sylow.1 hD.hyp.sylow.2.1
  · have e : (⨆ g : ↥M, g • V.map π) = (⨆ g : ↥M, V.map (g : MulAut W).toMonoidHom).map π := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun g => v2g_smul_map π hπM V g
    rw [e]
    have h2 : (⨆ g : ↥M, V.map (g : MulAut W).toMonoidHom) = ⊤ := by
      refine top_unique ?_
      rw [← hD.hyp.gen]
      refine iSup₂_le fun m hm => ?_
      exact le_iSup (fun g : ↥M => V.map (g : MulAut W).toMonoidHom) ⟨m, hm⟩
    rw [h2, Subgroup.map_top_of_surjective π hπs]
  · exact Subgroup.mem_subgroupOf.mpr htT
  · intro s hs
    have hsT : (s : MulAut W) ∈ T := Subgroup.mem_subgroupOf.mp hs
    rcases h4 _ hsT with h | h
    · left
      rw [v2g_smul_map π hπM, mem_stabSub_iff_map_eq.mp h]
    · right
      rw [v2g_smul_map π hπM, v2g_smul_map π hπM]
      have h1 : V.map ((t : MulAut W)⁻¹ * (s : MulAut W)).toMonoidHom = V :=
        mem_stabSub_iff_map_eq.mp h
      have h2 : V.map (s : MulAut W).toMonoidHom = V.map (t : MulAut W).toMonoidHom := by
        have e : (s : MulAut W) = (t : MulAut W) * ((t : MulAut W)⁻¹ * (s : MulAut W)) := by group
        conv_lhs => rw [e]
        rw [CFSG.Quasithin.map_mul_aut', h1]
      rw [h2]
  · intro h
    exact htV (v2g_stab_of_smul_eq hD π hπM hker t h)

end Z391

end CFSG.Quasithin
