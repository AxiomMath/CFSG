module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapG
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapR
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapFaith
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapTensor
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourClausesB
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  refine le_antisymm ?_ ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (u * v) * (u * v)⁻¹ = (x u * u⁻¹) * (x v * v⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc x u * x v * (v⁻¹ * u⁻¹)
          = x u * x v * (u⁻¹ * v⁻¹) := by rw [mul_comm (v⁻¹) (u⁻¹)]
        _ = x u * (x v * (u⁻¹ * v⁻¹)) := by rw [mul_assoc]
        _ = x u * (u⁻¹ * (x v * v⁻¹)) := by
              rw [← mul_assoc (x v) (u⁻¹) (v⁻¹), mul_comm (x v) (u⁻¹), mul_assoc]
        _ = (x u * u⁻¹) * (x v * v⁻¹) := by rw [← mul_assoc]
    rw [h1]
    exact (commSub A X ⊔ commSub B X).mul_mem
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩))
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w16f_commSub_map_conj (g : MulAut W) (J : Subgroup W)
    (A : Subgroup (MulAut W)) :
    commSub (J.map g.toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) =
      (commSub J A).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

private theorem w16f_stableUnder_top (X : Subgroup (MulAut W)) : StableUnder X ⊤ :=
  fun _ _ _ _ => Subgroup.mem_top _

private theorem w16f_stableUnder_bot (X : Subgroup (MulAut W)) : StableUnder X ⊥ :=
  fun _ _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]

private theorem w16f_le_stabSub_of_stable {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hxu => by
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hxu
    rwa [MulAut.inv_apply_self] at h1, h x hx u⟩

private theorem w16f_stableUnder_sup {X Z : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : StableUnder X U) (hZ : StableUnder Z U) : StableUnder (X ⊔ Z) U := by
  intro g hg u hu
  exact (mem_stabSub.mp (sup_le (w16f_le_stabSub_of_stable hX)
    (w16f_le_stabSub_of_stable hZ) hg) u).2 hu

private theorem w16f_mem_stabSub_of_maps {t : MulAut W} (ht2 : orderOf t = 2) {U : Subgroup W}
    (h : ∀ u ∈ U, t u ∈ U) : t ∈ stabSub U := by
  have ht : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  rw [mem_stabSub]
  intro u
  exact ⟨fun htu => by
    have h1 := h (t u) htu
    rwa [← MulAut.mul_apply, ht, MulAut.one_apply] at h1, h u⟩

private theorem w16f_map_eq_self_of_mem_stabSub {U : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub U) : U.map g.toMonoidHom = U := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_stabSub.mp hg v).mpr hv
  · intro hu
    exact ⟨g⁻¹ u, (mem_stabSub.mp hg (g⁻¹ u)).mp (by simpa using hu),
      MulEquiv.apply_symm_apply g u⟩

private theorem w16f_commutator_sup_sup_self {A B : Subgroup (MulAut W)}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) (sup_le ?_ ?_)
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

private theorem w16f_sec_stab {K : Subgroup (MulAut W)} {t : MulAut W} {U₀ U : Subgroup W}
    (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀)
    (htU : ∀ u ∈ U, t u ∈ U) (htU₀ : ∀ u ∈ U₀, t u ∈ U₀) (ht2 : orderOf t = 2) :
    K ≤ secStabAll U U₀ ∧ K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀ ∧
      t ∈ secStabAll U U₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact ⟨(w16f_le_stabSub_of_stable hirr.2.1) (Subgroup.mem_sup_left hg),
      (w16f_le_stabSub_of_stable hirr.2.2.1) (Subgroup.mem_sup_left hg)⟩
  · intro g hg
    exact ⟨(w16f_le_stabSub_of_stable hirr.2.1) (Subgroup.mem_sup_right hg),
      (w16f_le_stabSub_of_stable hirr.2.2.1) (Subgroup.mem_sup_right hg)⟩
  · exact ⟨w16f_mem_stabSub_of_maps ht2 htU, w16f_mem_stabSub_of_maps ht2 htU₀⟩

private theorem w16f_isIrrOn_of_le_sup {L : Subgroup (MulAut W)} {U U₀ R : Subgroup W}
    (hirr : IsIrrOn L U U₀) (hRleU : R ≤ U) (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U)
    (hRstab : StableUnder L R) (hRne : R ≠ ⊥) : IsIrrOn L R ⊥ := by
  refine ⟨lt_of_le_of_ne bot_le (Ne.symm hRne), hRstab, w16f_stableUnder_bot L, ?_⟩
  intro J hJstab _ hJle
  have hJsupstab : StableUnder L (J ⊔ U₀) := stableUnder_sup hJstab hirr.2.2.1
  have hcases :=
    hirr.2.2.2 (J ⊔ U₀) hJsupstab le_sup_right (sup_le (hJle.trans hRleU) hirr.1.le)
  rcases hcases with hcase | hcase
  · have hJU₀ : J ≤ U₀ := le_trans le_sup_left (le_of_eq hcase)
    have hJbot : J ≤ (⊥ : Subgroup W) := by rw [← hinf]; exact le_inf hJle hJU₀
    exact Or.inl (le_bot_iff.mp hJbot)
  · refine Or.inr (le_antisymm hJle ?_)
    intro r hr
    have hrmem : r ∈ J ⊔ U₀ := by
      rw [hcase]
      exact hsup ▸ Subgroup.mem_sup_left hr
    obtain ⟨j, hj, u, hu, hju⟩ := Subgroup.mem_sup.mp hrmem
    have huR : u ∈ R := by
      have hmem : j⁻¹ * r ∈ R := R.mul_mem (R.inv_mem (hJle hj)) hr
      rwa [← hju, ← mul_assoc, inv_mul_cancel, one_mul] at hmem
    have hu_bot : u ∈ (⊥ : Subgroup W) := by
      rw [← hinf]; exact ⟨huR, hu⟩
    have hu1 : u = 1 := Subgroup.mem_bot.mp hu_bot
    have hrj : r = j := by rw [← hju, hu1, mul_one]
    rw [hrj]; exact hj

theorem w16f_case_one_swap (hW : ∀ w : W, w ^ 2 = 1)
    {Y K : Subgroup (MulAut W)}
    (hY : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hK : IsComponentOf K Y) {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u) :
    Conc4_134 Y K t := by
  classical
  let K' : Subgroup (MulAut W) := K.map (MulAut.conj t).toMonoidHom
  let L : Subgroup (MulAut W) := K ⊔ K'
  let H : Subgroup (MulAut W) := L ⊔ Subgroup.zpowers t
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hK'comp : IsComponentOf K' Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK ht
  have hne : K ≠ K' := fun h => hmove h.symm
  have hcomm : ⁅K, K'⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hK hK'comp hne
  have hKperf : ⁅K, K⁆ = K := by
    have hq := hK.2.2.1
    have hmap := Subgroup.map_subtype_commutator K
    rw [hq, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hK'perf : ⁅K', K'⁆ = K' := by
    have hq := hK'comp.2.2.1
    have hmap := Subgroup.map_subtype_commutator K'
    rw [hq, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hLperf : ⁅L, L⁆ = L := w16f_commutator_sup_sup_self hKperf hK'perf
  have hKne : K ≠ ⊥ :=
    K.nontrivial_iff_ne_bot.mp (CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2)
  have hLnt : ¬ commSub ⊤ L ≤ ⊥ := by
    intro h
    have hfix : L ≤ centSub ⊤ := by
      intro l hl
      rw [mem_centSub]
      intro w _
      exact ((commSub_eq_bot_iff.mp (le_bot_iff.mp h)) (Subgroup.mem_top w)) l hl
    have hKle : K ≤ ⊥ := by
      intro k hk
      rw [Subgroup.mem_bot]
      ext w
      simpa using (mem_centSub.mp (hfix (Subgroup.mem_sup_left hk)) w (Subgroup.mem_top w))
    exact hKne (le_bot_iff.mp hKle)
  obtain ⟨U₀, U, hU₀le, hUU₂, hirrH, hcommU₀le, hntU⟩ :=
    exists_chief_nontrivial (L := L) (H := H) hLperf le_sup_left (w16f_stableUnder_bot H)
      (w16f_stableUnder_top H) bot_le hLnt
  have hU₀U : U₀ ≤ U := hirrH.1.le
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htU : ∀ u ∈ U, t u ∈ U := fun u hu => hirrH.2.1 t htH u hu
  have htU₀ : ∀ u ∈ U₀, t u ∈ U₀ := fun u hu => hirrH.2.2.1 t htH u hu
  have hirrL : IsIrrOn L U U₀ := swap_chief_isIrr hKperf ht2' hcomm htr hirrH hntU
  obtain ⟨n, hn2, hn3, _hcost, F, hFfield, hFfin, hFcard, hT⟩ :=
    swap_chief_nat hW (A3.isQuasisimple_iff_open.mpr hK.2.2) ht2 hmove hcomm htr hrk
      hirrL htU htU₀ hntU
  obtain ⟨hKs, hK's, hts⟩ := w16f_sec_stab hirrL htU htU₀ ht2
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨x, hxK, hxodd, hfx, hfy⟩ := exists_odd_fpf_lift hW hKs hts hU₀U hF4 hT
  let y : MulAut W := t * x * t⁻¹
  have hyK' : y ∈ K' := Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
  have hyo : Odd (orderOf y) := by
    have h1 : orderOf ((MulAut.conj t) x) = orderOf x :=
      orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective x
    rwa [show y = (MulAut.conj t) x from rfl, h1]
  have hU₀bot : commSub U₀ L = ⊥ := le_bot_iff.mp hcommU₀le
  obtain ⟨hR_eq, hRstabL, hRinf, hRsup⟩ :=
    swap_odd_pair_commSub hW hcomm hxK hyK' hxodd hyo hU₀U hirrL.2.1 hU₀bot hfx hfy
  let R : Subgroup W := commSub U (Subgroup.zpowers x)
  have hUmap : U.map t.toMonoidHom = U :=
    w16f_map_eq_self_of_mem_stabSub (w16f_mem_stabSub_of_maps ht2 htU)
  have hzpows : (Subgroup.zpowers x).map (MulAut.conj t).toMonoidHom =
      Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    rfl
  have htRmaps : ∀ u ∈ R, t u ∈ R := by
    intro u hu
    have h1 : t u ∈ (commSub U (Subgroup.zpowers x)).map t.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [← w16f_commSub_map_conj t U (Subgroup.zpowers x), hUmap, hzpows] at h1
    rw [← hR_eq] at h1
    exact h1
  have htR : StableUnder (Subgroup.zpowers t) R := by
    intro a ha u hu
    have hstab : a ∈ stabSub R :=
      Subgroup.zpowers_le.mpr (w16f_mem_stabSub_of_maps ht2 htRmaps) ha
    exact (mem_stabSub.mp hstab u).2 hu
  have hRstabH : StableUnder H R := w16f_stableUnder_sup hRstabL htR
  have hRnt : ¬ commSub R L ≤ ⊥ := by
    intro h
    have hRbot : commSub R L = ⊥ := le_bot_iff.mp h
    have hUL : commSub U L ≤ U₀ := by
      rw [← hRsup, w16f_commSub_sup, hRbot, hU₀bot]
      simp
    exact hntU hUL
  have hRL : commSub ⊤ L ≤ R := by
    by_contra hnot
    have h2top : 2 ≤ secCost t ⊤ R :=
      swap_section_cost_ge_two hW (A3.isQuasisimple_iff_open.mpr hK.2.2) ht2 hmove hcomm
        htr hrk hRstabH (w16f_stableUnder_top H) le_top hnot
    have h2bot : 2 ≤ secCost t R ⊥ :=
      swap_section_cost_ge_two hW (A3.isQuasisimple_iff_open.mpr hK.2.2) ht2 hmove hcomm
        htr hrk (w16f_stableUnder_bot H) hRstabH bot_le hRnt
    have hadd : secCost t R ⊥ + secCost t ⊤ R ≤ secCost t ⊤ ⊥ :=
      secCost_add_le (fun u hu => htR t (Subgroup.mem_zpowers t) u hu) bot_le le_top
    have htb : secCost t ⊤ ⊥ = rk ↥(commSub ⊤ (Subgroup.zpowers t)) := secCost_top_bot t
    omega
  have hRU : R ≤ U :=
    commSub_le_of_invariant (fun z hz u hu =>
      hirrL.2.1 z ((Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hxK)) hz) u hu)
  have hRstabJ : StableUnder L (commSub R L) :=
    stableUnder_commSub (fun h hh x hx => L.mul_mem (L.mul_mem hh hx) (L.inv_mem hh)) hRstabL
  have hRne : R ≠ ⊥ := by
    intro h
    have hRbot : commSub U (Subgroup.zpowers x) = ⊥ := h
    have hUeq : U₀ = U := by rw [← hRsup, hRbot, bot_sup_eq]
    exact (ne_of_lt hirrH.1) hUeq
  have hirrR : IsIrrOn L R ⊥ :=
    w16f_isIrrOn_of_le_sup hirrL hRU hRinf hRsup hRstabL hRne
  have hRCL : commSub R L = R := by
    rcases hirrR.2.2.2 (commSub R L) hRstabJ bot_le (commSub_le_of_invariant hRstabL) with h | h
    · exact absurd (h ▸ le_rfl) hRnt
    · exact h
  have hRL_eq : commSub ⊤ L = R := by
    apply le_antisymm hRL
    rw [← hRCL]
    exact commSub_mono le_top le_rfl
  have hKR : StableUnder K R := fun g hg u hu => hRstabL g (Subgroup.mem_sup_left hg) u hu
  have hK'R : StableUnder K' R := fun g hg u hu => hRstabL g (Subgroup.mem_sup_right hg) u hu
  have hKtriv : commSub ⊤ K ≤ R := by
    have h1 : commSub ⊤ K ≤ commSub ⊤ L := commSub_mono le_rfl le_sup_left
    rwa [hRL_eq] at h1
  have hK'triv : commSub ⊤ K' ≤ R := by
    have h1 : commSub ⊤ K' ≤ commSub ⊤ L := commSub_mono le_rfl le_sup_right
    rwa [hRL_eq] at h1
  have hKf : K ⊓ centSub R = ⊥ := swap_faithful_on_commSub hW hY hK hKR hKtriv
  have hK'f : K' ⊓ centSub R = ⊥ := swap_faithful_on_commSub hW hY hK'comp hK'R hK'triv
  have hNatTensor : NatTensor (K ⊔ K') R ⊥ 2 n :=
    natTensor_of_secMatTensor hKs hK's hcomm hRU hRstabL hRinf hRsup hKf hK'f hFcard hT
  have hIsL2 : UC22.IsL2 ↥K n :=
    isL2_of_secMatTensor hKs hK's hRU hKR hRinf hRsup hKf hn2 hFcard hT
  have hNatTensor' : NatTensor L (commSub ⊤ L) ⊥ 2 n := by
    rw [hRL_eq]
    exact hNatTensor
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hirrR' : IsIrrOn L (commSub ⊤ L) ⊥ := by rw [hRL_eq]; exact hirrR
  have hclause : ∀ g ∈ Y, g ∉ normalizer ((K ⊔ K.map (MulAut.conj t).toMonoidHom :
      Subgroup (MulAut W)) : Set (MulAut W)) →
      commSub ((commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)).map g.toMonoidHom)
        (K ⊔ K.map (MulAut.conj t).toMonoidHom) = ⊥ :=
    fun g hg hgL => s134_clause_one hW' hK ht hmove hirrR' hg hgL
  have hn23 : n = 2 ∨ n = 3 := by omega
  rcases hn23 with hn | hn
  · subst hn
    exact Or.inl ⟨Or.inr (Or.inl ⟨hIsL2, hNatTensor'⟩), hclause⟩
  · subst hn
    exact Or.inl ⟨Or.inr (Or.inr ⟨hIsL2, hNatTensor'⟩), hclause⟩

end CFSG.LocalAnalysis.WeakClosure81
