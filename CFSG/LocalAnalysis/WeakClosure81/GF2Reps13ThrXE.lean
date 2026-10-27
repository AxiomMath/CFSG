module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private def w16g_delta (s : MulAut W) : W →* W where
  toFun w := s w * w⁻¹
  map_one' := by simp
  map_mul' w v := by
    rw [map_mul, mul_inv_rev]
    ac_rfl

@[simp] private theorem w16g_delta_apply (s : MulAut W) (w : W) :
    w16g_delta s w = s w * w⁻¹ := rfl

private theorem w16g_map_delta_le (s : MulAut W) {U : Subgroup W}
    (hU : ∀ u ∈ U, s u ∈ U) : U.map (w16g_delta s) ≤ U := by
  rintro y ⟨u, hu, rfl⟩
  exact U.mul_mem (hU u hu) (U.inv_mem hu)

private theorem w16g_map_eq_self_of_forall_mem (s : MulAut W) {U : Subgroup W}
    (hU : ∀ u ∈ U, s u ∈ U) : U.map s.toMonoidHom = U := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨u, hu, rfl⟩
    exact hU u hu
  · rw [Subgroup.card_map_of_injective s.injective]

private theorem w16g_inv_mem_of_forall_mem (s : MulAut W) {U : Subgroup W}
    (hU : ∀ u ∈ U, s u ∈ U) : ∀ u ∈ U, s⁻¹ u ∈ U := by
  have hmap : U.map s.toMonoidHom = U := w16g_map_eq_self_of_forall_mem s hU
  intro u hu
  have hu' : u ∈ U.map s.toMonoidHom := by rw [hmap]; exact hu
  obtain ⟨v, hv, hsv⟩ := Subgroup.mem_map.mp hu'
  have hsv' : s v = u := hsv
  rw [← hsv', ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  exact hv

private theorem w16g_zpowers_mul_inv_mem_map_delta (s : MulAut W) {U : Subgroup W}
    (hU : ∀ u ∈ U, s u ∈ U) :
    ∀ x ∈ Subgroup.zpowers s, ∀ u ∈ U, x u * u⁻¹ ∈ U.map (w16g_delta s) := by
  let T : Subgroup (MulAut W) :=
    { carrier := {x | ∀ u ∈ U, x u * u⁻¹ ∈ U.map (w16g_delta s)}
      one_mem' := fun u _ => by
        rw [MulAut.one_apply, mul_inv_cancel]
        exact Subgroup.one_mem _
      mul_mem' := by
        intro a b ha hb u hu
        have hbu : b u ∈ U := by
          have h1 : b u * u⁻¹ ∈ U := w16g_map_delta_le s hU (hb u hu)
          have h2 : (b u * u⁻¹) * u = b u := by group
          exact h2 ▸ U.mul_mem h1 hu
        have h2 : a (b u) * (b u)⁻¹ ∈ U.map (w16g_delta s) := ha (b u) hbu
        have h3 : b u * u⁻¹ ∈ U.map (w16g_delta s) := hb u hu
        have h4 := (U.map (w16g_delta s)).mul_mem h2 h3
        have h5 : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
          rw [MulAut.mul_apply]; group
        rwa [h5]
      inv_mem' := by
        intro a ha u hu
        have haU : ∀ v ∈ U, a v ∈ U := by
          intro v hv
          have h1 : a v * v⁻¹ ∈ U := w16g_map_delta_le s hU (ha v hv)
          have h2 : (a v * v⁻¹) * v = a v := by group
          exact h2 ▸ U.mul_mem h1 hv
        have hmem : a⁻¹ u ∈ U := w16g_inv_mem_of_forall_mem a haU u hu
        have h2 : a (a⁻¹ u) * (a⁻¹ u)⁻¹ ∈ U.map (w16g_delta s) := ha (a⁻¹ u) hmem
        have h3 : (a (a⁻¹ u) * (a⁻¹ u)⁻¹)⁻¹ ∈ U.map (w16g_delta s) :=
          (U.map (w16g_delta s)).inv_mem h2
        have h4 : a (a⁻¹ u) = u := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        have h5 : a⁻¹ u * u⁻¹ = (a (a⁻¹ u) * (a⁻¹ u)⁻¹)⁻¹ := by
          rw [h4]; group
        rwa [h5] }
  have hsT : s ∈ T := by
    intro u hu
    exact Subgroup.mem_map_of_mem (w16g_delta s) hu
  intro x hx u hu
  exact (Subgroup.zpowers_le.mpr hsT) hx u hu

private theorem w16g_commSub_zpowers_eq_map_delta (s : MulAut W) {U : Subgroup W}
    (hU : ∀ u ∈ U, s u ∈ U) :
    commSub U (Subgroup.zpowers s) = U.map (w16g_delta s) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    exact w16g_zpowers_mul_inv_mem_map_delta s hU x hx w hw
  · refine Subgroup.map_le_iff_le_comap.mpr fun u hu => ?_
    rw [Subgroup.mem_comap, w16g_delta_apply]
    exact Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, u, hu, rfl⟩

private theorem w16g_card_map_delta_of_ker (s : MulAut W) {U : Subgroup W}
    (hker : ∀ u ∈ U, w16g_delta s u = 1 → u = 1) :
    Nat.card ↥(U.map (w16g_delta s)) = Nat.card ↥U := by
  let f : ↥U → ↥(U.map (w16g_delta s)) :=
    fun u => ⟨w16g_delta s u, Subgroup.mem_map_of_mem _ u.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h1 : w16g_delta s a = w16g_delta s b := congrArg Subtype.val hab
      have h2 : w16g_delta s ((a : W) * (b : W)⁻¹) = 1 := by
        rw [map_mul, MonoidHom.map_inv, h1, mul_inv_cancel]
      have h3 : (a : W) * (b : W)⁻¹ = 1 :=
        hker _ (U.mul_mem a.2 (U.inv_mem b.2)) h2
      exact Subtype.ext (mul_inv_eq_one.mp h3)
    · obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem rk_commSub_iSup_eq_sum {ι : Type*} [Fintype ι] (hW : ∀ w : W, w * w = 1)
    (s : MulAut W) (F : ι → Subgroup W) (hF : iSupIndep F) (hs : ∀ i, ∀ u ∈ F i, s u ∈ F i) :
    rk ↥(commSub (⨆ i, F i) (Subgroup.zpowers s)) =
      ∑ i, rk ↥(commSub (F i) (Subgroup.zpowers s)) := by
  have hsSup : ∀ u ∈ ⨆ i, F i, s u ∈ ⨆ i, F i := by
    intro u hu
    exact Subgroup.iSup_induction F (C := fun u => s u ∈ ⨆ i, F i) hu
      (fun i v hv => Subgroup.mem_iSup_of_mem i (hs i v hv))
      (by rw [map_one]; exact Subgroup.one_mem _)
      (fun a b ha hb => by rw [map_mul]; exact Subgroup.mul_mem _ ha hb)
  have hindep : iSupIndep fun i => (F i).map (w16g_delta s) :=
    hF.mono fun i => w16g_map_delta_le s (hs i)
  calc rk ↥(commSub (⨆ i, F i) (Subgroup.zpowers s))
      = rk ↥((⨆ i, F i).map (w16g_delta s)) := by
        rw [w16g_commSub_zpowers_eq_map_delta s hsSup]
    _ = rk ↥(⨆ i, (F i).map (w16g_delta s)) := by
        rw [Subgroup.map_iSup]
    _ = ∑ i, rk ↥((F i).map (w16g_delta s)) :=
        w16g_rk_iSup_eq_sum (fun w => by rw [pow_two]; exact hW w) _ hindep
    _ = ∑ i, rk ↥(commSub (F i) (Subgroup.zpowers s)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [w16g_commSub_zpowers_eq_map_delta s (hs i)]

theorem rk_commSub_swap (hW : ∀ w : W, w * w = 1) {s : MulAut W} (hs2 : s * s = 1)
    {U U' : Subgroup W} (hUU' : U' = U.map s.toMonoidHom) (hdisj : U ⊓ U' = ⊥) :
    rk ↥U' = rk ↥U ∧ rk ↥(commSub (U ⊔ U') (Subgroup.zpowers s)) = rk ↥U := by
  have hcardU' : Nat.card ↥U' = Nat.card ↥U := by
    rw [hUU', Subgroup.card_map_of_injective s.injective]
  have hss : U'.map s.toMonoidHom = U := by
    rw [hUU', Subgroup.map_map]
    have hcomp : s.toMonoidHom.comp s.toMonoidHom = MonoidHom.id W := by
      ext x
      change s (s x) = x
      rw [← MulAut.mul_apply, hs2, MulAut.one_apply]
    rw [hcomp, Subgroup.map_id]
  have hsupmap : (U ⊔ U').map s.toMonoidHom = U ⊔ U' := by
    rw [Subgroup.map_sup, ← hUU', hss, sup_comm]
  have hstableSup : ∀ w ∈ U ⊔ U', s w ∈ U ⊔ U' := by
    intro w hw
    rw [← hsupmap]
    exact Subgroup.mem_map_of_mem _ hw
  have hU'mapδ : U'.map (w16g_delta s) ≤ U.map (w16g_delta s) := by
    rw [hUU']
    rintro y ⟨u', ⟨u, hu, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨u⁻¹, U.inv_mem hu, ?_⟩
    rw [w16g_delta_apply, w16g_delta_apply, MulEquiv.map_inv, inv_inv]
    change (s u)⁻¹ * u = s (s u) * (s u)⁻¹
    rw [show s (s u) = u by rw [← MulAut.mul_apply, hs2, MulAut.one_apply]]
    exact mul_comm _ _
  have hδeq : (U ⊔ U').map (w16g_delta s) = U.map (w16g_delta s) := by
    rw [Subgroup.map_sup, sup_eq_left.mpr hU'mapδ]
  have hker : ∀ u ∈ U, w16g_delta s u = 1 → u = 1 := by
    intro u hu h
    have hsu : s u = u := by
      rw [w16g_delta_apply, mul_inv_eq_one] at h
      exact h
    have hmem : u ∈ U' := by
      rw [hUU']
      exact Subgroup.mem_map.mpr ⟨u, hu, hsu⟩
    have : u ∈ U ⊓ U' := ⟨hu, hmem⟩
    rw [hdisj] at this
    exact Subgroup.mem_bot.mp this
  refine ⟨?_, ?_⟩
  · unfold rk
    rw [hcardU']
  · rw [w16g_commSub_zpowers_eq_map_delta s hstableSup, hδeq]
    unfold rk
    rw [w16g_card_map_delta_of_ker s hker]

theorem rk_commSub_fixed_inverted (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 3 X) {s : MulAut W} (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) {U : Subgroup W} (hU : U ∈ s13IsoComps X)
    (hsU : ∀ u ∈ U, s u ∈ U) (hinv : ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X U) :
    2 * rk ↥(commSub U (Subgroup.zpowers s)) = rk ↥U := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hHmem : s13KerOn X U ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 X :=
    s13KerOn_mem_hyperplanes hW hp3 hp32 hX hU
  have hHle : s13KerOn X U ≤ X := hHmem.1
  have hHidx : (s13KerOn X U).relIndex X = 3 := hHmem.2
  have hXnotle : ¬ X ≤ s13KerOn X U := by
    intro hle
    have h1 : (s13KerOn X U).relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hHidx] at h1
    norm_num at h1
  have hex : ∃ x ∈ X, x ∉ s13KerOn X U := by
    by_contra h
    apply hXnotle
    intro x hx
    by_contra hxH
    exact h ⟨x, hx, hxH⟩
  obtain ⟨x, hxX, hxH⟩ := hex
  have hx3 : x ^ 3 = 1 := hX.2 x hxX
  have hstabU : StableUnder X U := s13IsoComps_stable hU
  obtain ⟨U₀, hIrr₀, hne₀, hUeq⟩ := hU
  let y : MulAut W := s * x * s⁻¹
  have hyX : y ∈ X := hsX x hxX
  have hyx : s * y * s⁻¹ = x := by
    have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    simp only [y]
    rw [hs_inv]
    calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
      _ = x := by rw [hs2]; group
  let xm : MulAut W := y * x⁻¹
  have hxmX : xm ∈ X := X.mul_mem hyX (X.inv_mem hxX)
  have hxm_inv : s * xm * s⁻¹ = xm⁻¹ := by
    rw [show xm = y * x⁻¹ from rfl]
    have h1 : s * (y * x⁻¹) * s⁻¹ = (s * y * s⁻¹) * (s * x * s⁻¹)⁻¹ := by group
    rw [h1, hyx]
    rw [show s * x * s⁻¹ = y from rfl]
    group
  have h0 : y * x ∈ s13KerOn X U := by
    have h := hinv x hxX
    simpa [y] using h
  have hxm_notH : xm ∉ s13KerOn X U := by
    intro hxmH
    apply hxH
    have hx_inv2 : x⁻¹ = x ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx3)
    have hx_inv3 : x⁻¹ = x * x := by rw [hx_inv2, pow_two]
    have hx_eq : xm = (y * x) * x := by
      rw [show xm = y * x⁻¹ from rfl, hx_inv3]
      group
    rw [hx_eq] at hxmH
    have h0inv : (y * x)⁻¹ ∈ s13KerOn X U := (s13KerOn X U).inv_mem h0
    have hx : x = (y * x)⁻¹ * ((y * x) * x) := by group
    rw [hx]
    exact (s13KerOn X U).mul_mem h0inv hxmH
  have hxm3 : xm ^ 3 = 1 := hX.2 xm hxmX
  have hxm_ne1 : xm ≠ 1 :=
    fun h => hxm_notH (h.symm ▸ (s13KerOn X U).one_mem)
  have horder : orderOf xm = 3 := orderOf_eq_prime hxm3 hxm_ne1
  have hX1card : Nat.card ↥(Subgroup.zpowers xm) = 3 := by
    rw [Nat.card_zpowers, horder]
  have hX1rank : IsElemAbelianOfRank 3 1 ↥(Subgroup.zpowers xm) :=
    w16g_isElemAbelianOfRank_one_of_card hp3 hX1card
  have hX1le : Subgroup.zpowers xm ≤ X := Subgroup.zpowers_le.mpr hxmX
  have hxm_notCent : xm ∉ centSub U₀ := by
    intro hxc
    apply hxm_notH
    rw [s13KerOn, hUeq, w16g_inf_centSub_s13IsoSum_eq hIrr₀]
    exact ⟨hxmX, hxc⟩
  have hxm_nt : ∃ u ∈ U₀, xm u ≠ u := by
    by_contra h
    apply hxm_notCent
    rw [mem_centSub]
    intro u hu
    by_contra hne
    exact h ⟨u, hu, hne⟩
  have hfix_xm : U ⊓ fixV (Subgroup.zpowers xm) = ⊥ := by
    rw [hUeq]
    exact w16g_inf_fixV_zpowers_eq_bot hW hX.1 hIrr₀ hxmX hxm_nt
  have hfixker : ∀ u ∈ U, w16g_delta xm u = 1 → u = 1 := by
    intro u hu h
    have hxu : xm u = u := by
      rw [w16g_delta_apply, mul_inv_eq_one] at h
      exact h
    have hmem : u ∈ U ⊓ fixV (Subgroup.zpowers xm) := by
      refine ⟨hu, mem_fixV.mpr ?_⟩
      intro y hy
      exact MulAction.mem_stabilizer_iff.mp
        (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hxu) hy)
    exact Subgroup.mem_bot.mp (hfix_xm ▸ hmem)
  have hcommU : commSub U (Subgroup.zpowers xm) = U := by
    rw [w16g_commSub_zpowers_eq_map_delta xm (hstabU xm hxmX)]
    exact Subgroup.eq_of_le_of_card_ge (w16g_map_delta_le xm (hstabU xm hxmX))
      (le_of_eq (w16g_card_map_delta_of_ker xm hfixker).symm)
  have hinvX1 : ∀ a ∈ Subgroup.zpowers xm, s * a * s⁻¹ = a⁻¹ :=
    fun a ha => w16g_conj_inv_of_mem_zpowers hxm_inv ha
  have hUX1 : StableUnder (Subgroup.zpowers xm) U :=
    fun a ha u hu => hstabU a (hX1le ha) u hu
  have hs_ne1 : s ≠ 1 := by
    intro hs1
    apply hxH
    have h2 : x ^ 2 ∈ s13KerOn X U := by
      have h := hinv x hxX
      rw [hs1] at h
      simpa [pow_two] using h
    have hx_eq : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx3, one_mul]
    rw [hx_eq]
    exact (s13KerOn X U).pow_mem h2 2
  have hs2pow : s ^ 2 = 1 := by rw [pow_two]; exact hs2
  have hsOrd : orderOf s = 2 := orderOf_eq_prime hs2pow hs_ne1
  have hbridge :=
    rk_commSub_eq_two_mul_of_inverted_on (fun w => by rw [pow_two]; exact hW w) hsOrd
      hp3 hp32 (by norm_num : 0 < 1) hX1rank hinvX1 hUX1 hsU
  rw [hcommU] at hbridge
  exact hbridge.symm

theorem even_rk_commSub_fixed_central (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 3 X) {s : MulAut W} (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) {U : Subgroup W} (hU : U ∈ s13IsoComps X)
    (hsU : ∀ u ∈ U, s u ∈ U) (hcent : ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ s13KerOn X U) :
    Even (rk ↥(commSub U (Subgroup.zpowers s))) := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hHmem : s13KerOn X U ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 X :=
    s13KerOn_mem_hyperplanes hW hp3 hp32 hX hU
  have hHle : s13KerOn X U ≤ X := hHmem.1
  have hHidx : (s13KerOn X U).relIndex X = 3 := hHmem.2
  have hXnotle : ¬ X ≤ s13KerOn X U := by
    intro hle
    have h1 : (s13KerOn X U).relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hHidx] at h1
    norm_num at h1
  have hex : ∃ x ∈ X, x ∉ s13KerOn X U := by
    by_contra h
    apply hXnotle
    intro x hx
    by_contra hxH
    exact h ⟨x, hx, hxH⟩
  obtain ⟨x, hxX, hxH⟩ := hex
  have hx3 : x ^ 3 = 1 := hX.2 x hxX
  have hstabU : StableUnder X U := s13IsoComps_stable hU
  obtain ⟨U₀, hIrr₀, hne₀, hUeq⟩ := hU
  have hxcent : x ∉ centSub U₀ := by
    intro hxc
    apply hxH
    rw [s13KerOn, hUeq, w16g_inf_centSub_s13IsoSum_eq hIrr₀]
    exact ⟨hxX, hxc⟩
  have hxcent' : ¬ ∀ u ∈ U₀, x u = u := fun h => hxcent (mem_centSub.mpr h)
  push Not at hxcent'
  obtain ⟨u, hu, hxu⟩ := hxcent'
  have hfixU : U ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    rw [hUeq]
    exact w16g_inf_fixV_zpowers_eq_bot hW hX.1 hIrr₀ hxX ⟨u, hu, hxu⟩
  have hMleU : commSub U (Subgroup.zpowers s) ≤ U := by
    rw [w16g_commSub_zpowers_eq_map_delta s hsU]
    exact w16g_map_delta_le s hsU
  have hfixM : commSub U (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    rw [eq_bot_iff]
    calc commSub U (Subgroup.zpowers s) ⊓ fixV (Subgroup.zpowers x)
        ≤ U ⊓ fixV (Subgroup.zpowers x) := inf_le_inf_right _ hMleU
      _ = ⊥ := hfixU
  have hxs_comm : ∀ v ∈ U, s (x v) = x (s v) := by
    intro v hv
    have hh : s * x * s⁻¹ * x⁻¹ ∈ centSub U := by
      have h := hcent x hxX
      rw [s13KerOn] at h
      exact h.2
    have hconj : (s * x * s⁻¹ * x⁻¹) * x = s * x * s⁻¹ := by group
    have hone : (s * x * s⁻¹) (s v) = s (x v) := by
      rw [MulAut.mul_apply, MulAut.mul_apply,
        show s⁻¹ (s v) = v by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]]
    calc s (x v) = (s * x * s⁻¹) (s v) := hone.symm
      _ = ((s * x * s⁻¹ * x⁻¹) * x) (s v) := by rw [hconj]
      _ = (s * x * s⁻¹ * x⁻¹) (x (s v)) := by rw [MulAut.mul_apply]
      _ = x (s v) :=
        mem_centSub.mp hh (x (s v)) (hstabU x hxX (s v) (hsU v hv))
  have hMstab : ∀ m ∈ commSub U (Subgroup.zpowers s),
      x m ∈ commSub U (Subgroup.zpowers s) := by
    intro m hm
    rw [w16g_commSub_zpowers_eq_map_delta s hsU] at hm ⊢
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hm
    refine Subgroup.mem_map.mpr ⟨x v, hstabU x hxX v hv, ?_⟩
    rw [w16g_delta_apply, w16g_delta_apply, map_mul, map_inv, hxs_comm v hv]
  have hx_ne1 : x ≠ 1 := fun h => hxH (h.symm ▸ (s13KerOn X U).one_mem)
  have hxorder : orderOf x = 3 := orderOf_eq_prime hx3 hx_ne1
  have hdvd : dParam 3 ∣ rk ↥(commSub U (Subgroup.zpowers s)) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.dParam_dvd_rk
      (fun w => by rw [pow_two]; exact hW w) hp3 hp32 hxorder hMstab hfixM
  have hdParam3 : dParam 3 = 2 := by
    rw [dParam]
    exact (orderOf_eq_iff (by norm_num : 0 < 2)).2
      ⟨by decide, by intro m hm _; interval_cases m <;> decide⟩
  rw [hdParam3] at hdvd
  exact even_iff_two_dvd.mpr hdvd

end CFSG.LocalAnalysis.WeakClosure81
