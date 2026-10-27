module

public import CFSG.Quasithin.Background.F918Z8a
public import CFSG.Quasithin.Background.F918Z8b
public import CFSG.Quasithin.Background.F918M0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Aux

variable {W : Type} [CommGroup W]

theorem d321h_stab_commSub {X : Subgroup (MulAut W)} {Y : Subgroup W} {g : MulAut W}
    (hgY : g ∈ stabSub Y) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    g ∈ stabSub (commSub Y X) :=
  CFSG.Quasithin.StabLat.mem_stabSub_commSub hgY hgX

theorem d321h_commSub_sup_le {L : Subgroup (MulAut W)} {A B : Subgroup W} (hB : B ≤ fixV L) :
    commSub (A ⊔ B) L ≤ commSub A L := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  have e : x (a * b) * (a * b)⁻¹ = x a * a⁻¹ := by
    rw [map_mul, hB hb x hx, mul_inv_rev]
    group
  rw [e]
  exact Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩

theorem d321h_fix_of_perfect {L : Subgroup (MulAut W)} {Z : Subgroup W} (hperf : ⁅L, L⁆ = L)
    (hZ : Z ≤ fixV L) {u : W} (hu : ∀ l ∈ L, l u * u⁻¹ ∈ Z) : u ∈ fixV L := by
  have hstep : ∀ w : W, (∀ l ∈ L, l w * w⁻¹ ∈ Z) → ∀ a ∈ L, ∀ l ∈ L,
      l (a w) * (a w)⁻¹ ∈ Z := by
    intro w hw a ha l hl
    have e : l (a w) * (a w)⁻¹ = ((l * a) w * w⁻¹) * (a w * w⁻¹)⁻¹ := by
      simp only [MulAut.mul_apply]
      group
    rw [e]
    exact Z.mul_mem (hw (l * a) (L.mul_mem hl ha)) (Z.inv_mem (hw a ha))
  have hcomm : ∀ w : W, (∀ l ∈ L, l w * w⁻¹ ∈ Z) → ∀ a ∈ L, ∀ b ∈ L, a (b w) = b (a w) := by
    intro w hw a ha b hb
    have h1 : a (b w * w⁻¹) = b w * w⁻¹ := hZ (hw b hb) a ha
    have h2 : b (a w * w⁻¹) = a w * w⁻¹ := hZ (hw a ha) b hb
    rw [map_mul, map_inv] at h1 h2
    calc a (b w) = (a (b w) * (a w)⁻¹) * a w := by group
      _ = (b w * w⁻¹) * a w := by rw [h1]
      _ = (a w * w⁻¹) * b w := by ac_rfl
      _ = (b (a w) * (b w)⁻¹) * b w := by rw [h2]
      _ = b (a w) := by group
  have hK : L ≤ MulAction.stabilizer (MulAut W) u := by
    conv_lhs => rw [← hperf]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    change a * b * a⁻¹ * b⁻¹ ∈ MulAction.stabilizer (MulAut W) u
    rw [MulAction.mem_stabilizer_iff]
    have hg1 : ∀ l ∈ L, l (b⁻¹ u) * (b⁻¹ u)⁻¹ ∈ Z := hstep u hu b⁻¹ (L.inv_mem hb)
    have hg2 : ∀ l ∈ L, l (a⁻¹ (b⁻¹ u)) * (a⁻¹ (b⁻¹ u))⁻¹ ∈ Z :=
      hstep _ hg1 a⁻¹ (L.inv_mem ha)
    have h3 := hcomm _ hg2 a ha b hb
    have e : (a * b * a⁻¹ * b⁻¹ : MulAut W) • u = a (b (a⁻¹ (b⁻¹ u))) := by
      simp [MulAut.mul_apply]
    rw [e, h3]
    simp
  intro l hl
  exact MulAction.mem_stabilizer_iff.mp (hK hl)

end Aux

@[expose] def tildeImg {W : Type} [CommGroup W] (U Z V : Subgroup W) : Subgroup (Sec U Z) :=
  (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))

section Normalized

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

set_option linter.unusedVariables false in
theorem d321_stab_V (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hVT : commSub (orbSup T V) L = V) :
    T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub V := by
  intro s hs
  have h := d321h_stab_commSub (le_stabSub_orbSup T V hs.1) hs.2
  rwa [hVT] at h

set_option linter.unusedVariables false in
theorem d321_orbSup_eq (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hVT : commSub (orbSup T V) L = V) :
    orbSup T V = V ⊔ V.map t.toMonoidHom := by
  have hS := d321_stab_V hL38 hstd htT htL hMp hVT
  have hsT := (hL38 W M Mp T L V hstd t htT htL hMp).2.2.2
  refine le_antisymm (orbSup_le fun s hs => ?_) (sup_le (le_orbSup T V) (map_le_orbSup htT))
  rcases hsT s hs with h | h
  · have hsV : s ∈ stabSub V := hS ⟨hs, d321a_mem_normalizer_iff.mpr h⟩
    rw [mem_stabSub_iff_map_eq.mp hsV]
    exact le_sup_left
  · have h1 : conjAutSub (t⁻¹ * s) L = L := by
      rw [d321a_conjAutSub_mul, h, conjAutSub_inv_conjAutSub]
    have hts : t⁻¹ * s ∈ stabSub V :=
      hS ⟨T.mul_mem (T.inv_mem htT) hs, d321a_mem_normalizer_iff.mpr h1⟩
    have e : V.map s.toMonoidHom = V.map t.toMonoidHom := by
      have e' : s = t * (t⁻¹ * s) := by group
      conv_lhs => rw [e', map_mul_aut', mem_stabSub_iff_map_eq.mp hts]
    rw [e]
    exact le_sup_right

theorem d321h_le_commV (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : V ≤ commV L :=
  calc V = commSub V L := (d321_comm_eq hstd hMp htriv).symm
    _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
    _ = commV L := (commV_eq_commSub L).symm

theorem d321h_perm (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L := by
  obtain ⟨hA38, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hstd.hyp.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  exact fun g hg => d321a_perm hLs hnab hcomm hMp hstd.hyp.Mp_normal hg

theorem d321h_iSup_le_commV (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    (⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom) ≤ commV L := by
  have hVU := d321h_le_commV hstd hMp htriv
  refine iSup₂_le fun m hm => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact d321a_commV_stable (Subgroup.mem_inf.mp hm).2 (hVU hv)

omit [Finite W] in
theorem d321h_mem_iSup {m : MulAut W} (hm : m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)))
    {v : W} (hv : v ∈ V) :
    m v ∈ ⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom :=
  Subgroup.mem_iSup_of_mem m (Subgroup.mem_iSup_of_mem hm ⟨v, hv, rfl⟩)

theorem d321h_top_eq_iSup (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    (⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom) ⊔
      (⨆ m ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), V.map m.toMonoidHom).map
        t.toMonoidHom = ⊤ := by
  have hperm := d321h_perm hL38 hstd htT htL hMp
  have htM : t ∈ M := hstd.hyp.sylow.1 htT
  refine eq_top_iff.mpr (hstd.hyp.gen.symm.le.trans (iSup₂_le fun g hg => ?_))
  rintro _ ⟨v, hv, rfl⟩
  rcases hperm g hg with h | h
  · exact Subgroup.mem_sup_left (d321h_mem_iSup ⟨hg, d321a_mem_normalizer_iff.mpr h⟩ hv)
  · have h1 : conjAutSub (t⁻¹ * g) L = L := by
      rw [d321a_conjAutSub_mul, h, conjAutSub_inv_conjAutSub]
    exact Subgroup.mem_sup_right ⟨(t⁻¹ * g) v, d321h_mem_iSup
      ⟨M.mul_mem (M.inv_mem htM) hg, d321a_mem_normalizer_iff.mpr h1⟩ hv,
      by simp [MulAut.mul_apply]⟩

theorem d321h_top_eq (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    commV L ⊔ (commV L).map t.toMonoidHom = ⊤ := by
  have h := d321h_iSup_le_commV hstd hMp htriv
  exact eq_top_iff.mpr ((d321h_top_eq_iSup hL38 hstd htT htL hMp).ge.trans
    (sup_le_sup h (Subgroup.map_mono h)))

theorem d321h_map_le_fixV (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    (commV L).map t.toMonoidHom ≤ fixV L := by
  have hU : commV L ≤ fixV (conjAutSub t L) := (d321_struct hL38 hstd htT htL hMp htriv).2
  have hti : conjAutSub t⁻¹ L = conjAutSub t L := by
    have h1 := d321b_conj_conj hL38 hstd htT htL hMp
    have := congrArg (conjAutSub t⁻¹) h1
    rw [conjAutSub_inv_conjAutSub] at this
    exact this.symm
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_fixV]
  intro l hl
  have hy : t⁻¹ * l * t ∈ conjAutSub t L := by
    rw [← hti, mem_conjAutSub_iff]
    have e : t⁻¹⁻¹ * (t⁻¹ * l * t) * t⁻¹ = l := by group
    rw [e]
    exact hl
  have e : l (t u) = t ((t⁻¹ * l * t) u) := by simp [MulAut.mul_apply]
  show l (t u) = t u
  rw [e, hU hu _ hy]

theorem d321_tilde_ne_top (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hVT : commSub (orbSup T V) L = V) (htop : orbSup T V ≠ ⊤) :
    tildeImg (commV L) (commV L ⊓ fixV Mp) V ≠ ⊤ := by
  intro htil
  have hVL : commSub V L = V := d321_comm_eq hstd hMp htriv
  have hVU : V ≤ commV L := d321h_le_commV hstd hMp htriv
  have hUt := d321h_map_le_fixV hL38 hstd htT htL hMp htriv
  have htop' := d321h_top_eq hL38 hstd htT htL hMp htriv
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hZfix : commV L ⊓ fixV Mp ≤ fixV L := fun z hz l hl => hz.2 l (hLMp hl)
  have hUle : commV L ≤ V ⊔ (commV L ⊓ fixV Mp) := by
    intro u hu
    have hmem : (QuotientGroup.mk ⟨u, hu⟩ : Sec (commV L) (commV L ⊓ fixV Mp)) ∈
        tildeImg (commV L) (commV L ⊓ fixV Mp) V := by
      rw [htil]
      trivial
    obtain ⟨v, hv, hveq⟩ := hmem
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hveq)
    have h2 := Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hv) h1
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h2
  have hU1 : commV L ≤ commSub (commV L) L :=
    calc commV L = commSub ⊤ L := commV_eq_commSub L
      _ = commSub (commV L ⊔ (commV L).map t.toMonoidHom) L := by rw [htop']
      _ ≤ commSub (commV L) L := d321h_commSub_sup_le hUt
  have hUV : commV L ≤ V :=
    calc commV L ≤ commSub (commV L) L := hU1
      _ ≤ commSub (V ⊔ (commV L ⊓ fixV Mp)) L := commSub_mono hUle le_rfl
      _ ≤ commSub V L := d321h_commSub_sup_le hZfix
      _ = V := hVL
  have hUeq : commV L = V := le_antisymm hUV hVU
  apply htop
  rw [d321_orbSup_eq hL38 hstd htT htL hMp htriv hVT]
  rw [hUeq] at htop'
  exact htop'

theorem d321_fix_tilde (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    fixV (autSec L (commV L) (commV L ⊓ fixV Mp)) = ⊥ := by
  have hUt : commV L ≤ fixV (conjAutSub t L) := (d321_struct hL38 hstd htT htL hMp htriv).2
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hstd.hyp.quasi.1
  have hLU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu =>
    d321a_commV_stable (Subgroup.le_normalizer hl) hu
  have hLstab : L ≤ stabSub (commV L) := d321a_le_stabSub_of_inv hLU
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix := mk_mem_fixV_autQuot.mp hx
  have hu : ∀ l ∈ L, l (u : W) * (u : W)⁻¹ ∈ commV L ⊓ fixV Mp := by
    intro l hl
    have hg : resHom (commV L) ⟨l, hLstab hl⟩ ∈ autSub L (commV L) :=
      mem_autSub.mpr ⟨⟨l, hLstab hl⟩, hl, rfl⟩
    have hlZ : l ∈ stabSub (commV L ⊓ fixV Mp) :=
      centSub_le_stabSub _ (fun z hz => hz.2 l (hLMp hl))
    have hgs : resHom (commV L) ⟨l, hLstab hl⟩ ∈
        stabSub ((commV L ⊓ fixV Mp).subgroupOf (commV L)) := by
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hlZ (y : W)
    exact Subgroup.mem_subgroupOf.mp (hfix _ hg hgs)
  have hZfix : commV L ⊓ fixV Mp ≤ fixV L := fun z hz l hl => hz.2 l (hLMp hl)
  have hfixL : (u : W) ∈ fixV L := d321h_fix_of_perfect hperf hZfix hu
  have hfixMp : (u : W) ∈ fixV Mp := by
    rw [hMp, d321a_fixV_sup]
    exact ⟨hfixL, hUt u.2⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr ⟨u.2, hfixMp⟩)

end Normalized

end CFSG.Quasithin
