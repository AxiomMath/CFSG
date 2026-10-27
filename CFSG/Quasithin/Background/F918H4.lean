module

public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin

section Part3Aux

variable {W : Type} [CommGroup W]

private theorem p3_le_stabSub_of_forall_mem {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : X ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hgu => ?_, fun hu => h g hg u hu⟩
  simpa using h g⁻¹ (X.inv_mem hg) _ hgu

private theorem p3_le_stabSub_commSub_of_forall_mem {X : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : ∀ y ∈ X, ∀ w ∈ Y, y w ∈ Y) : X ≤ stabSub (commSub Y X) := by
  have key : ∀ y ∈ X, ∀ w ∈ commSub Y X, y w ∈ commSub Y X := by
    intro y hy w hw
    refine Subgroup.closure_induction (p := fun w _ => y w ∈ commSub Y X) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, hl, v, hv, rfl⟩
      have : y (l v * v⁻¹) = (y * l * y⁻¹) (y v) * (y v)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [this]
      exact Subgroup.subset_closure ⟨y * l * y⁻¹, X.mul_mem (X.mul_mem hy hl) (X.inv_mem hy), y v,
        hY y hy v hv, rfl⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commSub Y X).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commSub Y X).inv_mem ha
  exact p3_le_stabSub_of_forall_mem key

private theorem p3_forall_mem_orbSup_of_invariant {Mp T : Subgroup (MulAut W)} {V : Subgroup W}
    (hT : T ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hV : ∀ g ∈ Mp, ∀ v ∈ V, g v ∈ V) :
    ∀ g ∈ Mp, ∀ w ∈ orbSup T V, g w ∈ orbSup T V := by
  intro g hg w hw
  have h : orbSup T V ≤ (orbSup T V).comap g.toMonoidHom := by
    refine orbSup_le fun t ht => ?_
    rintro _ ⟨v, hv, rfl⟩
    show g (t v) ∈ orbSup T V
    have hg' : t⁻¹ * g * t ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hT ht) g).mp hg
    have e : g (t v) = t ((t⁻¹ * g * t) v) := by simp [MulAut.mul_apply]
    rw [e]
    exact map_le_orbSup ht ⟨_, hV _ hg' v hv, rfl⟩
  exact h hw

private theorem p3_isSumMod_map_of_injective {H : Type} [CommGroup H] (f : H →* W)
    (hf : Function.Injective f) {C A B Tot : Subgroup H} (h : IsSumMod C A B Tot) :
    IsSumMod (C.map f) (A.map f) (B.map f) (Tot.map f) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h1, Subgroup.map_sup, Subgroup.map_sup]
  · rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_inf _ _ f hf]
    exact Subgroup.map_mono h2

private theorem p3_map_eq_of_mem_stabSub {V : Subgroup W} {x : MulAut W} (hx : x ∈ stabSub V) :
    V.map x.toMonoidHom = V := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hx w).mpr hw
  · intro hv
    refine ⟨x⁻¹ v, (hx _).mp ?_, by simp⟩
    simpa using hv

private theorem p3_resHom_mem_stabSub_subgroupOf_iff {U V : Subgroup W} (hVU : V ≤ U)
    (s : stabSub U) :
    resHom U s ∈ stabSub (V.subgroupOf U) ↔ (s : MulAut W) ∈ stabSub V := by
  constructor
  · intro h w
    by_cases hw : w ∈ U
    · have := h ⟨w, hw⟩
      simpa [Subgroup.mem_subgroupOf, resHom_apply] using this
    · have h1 : s.1 w ∉ U := fun h' => hw ((s.2 w).mp h')
      exact ⟨fun h' => absurd (hVU h') h1, fun h' => absurd (hVU h') hw⟩
  · intro h u
    simpa [Subgroup.mem_subgroupOf, resHom_apply] using h u

private theorem p3_map_subtype_orbSup_autSub {S : Subgroup (MulAut W)} {U V : Subgroup W}
    (hSU : S ≤ stabSub U) (hVU : V ≤ U) :
    (orbSup (autSub S U) (V.subgroupOf U)).map U.subtype = orbSup S V := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine orbSup_le fun t' ht' => ?_
    obtain ⟨g, hgS, rfl⟩ := mem_autSub.mp ht'
    rintro _ ⟨v', hv', rfl⟩
    show ((resHom U g v' : U) : W) ∈ orbSup S V
    rw [resHom_apply]
    exact map_le_orbSup hgS ⟨(v' : W), hv', rfl⟩
  · refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hsU : s ∈ stabSub U := hSU hs
    have hmem : resHom U ⟨s, hsU⟩ ∈ autSub S U := mem_autSub.mpr ⟨⟨s, hsU⟩, hs, rfl⟩
    have h1 : (⟨v, hVU hv⟩ : U) ∈ V.subgroupOf U := hv
    have h2 : resHom U ⟨s, hsU⟩ ⟨v, hVU hv⟩ ∈ orbSup (autSub S U) (V.subgroupOf U) :=
      map_le_orbSup hmem ⟨_, h1, rfl⟩
    exact ⟨_, h2, by simp [resHom_apply]⟩

private theorem p3_nonempty_mulEquiv_autSub {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : X ≤ stabSub U) (hf : ∀ g ∈ X, (∀ u ∈ U, g u = u) → g = 1) :
    Nonempty (↥X ≃* ↥(autSub X U)) := by
  let φ : ↥X →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hX)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply hf g.1 g.2
    intro u hu
    exact congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : W)) hg
  have hrange : φ.range = autSub X U := by
    ext y
    rw [MonoidHom.mem_range, mem_autSub]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g.1, hX g.2⟩, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hg⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

private theorem p3_faithful_of_isSimpleGroup {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hS : IsSimpleGroup ↥X) (hX : X ≤ stabSub U) (hne : ∃ g ∈ X, ∃ u ∈ U, g u ≠ u) :
    ∀ g ∈ X, (∀ u ∈ U, g u = u) → g = 1 := by
  let φ : ↥X →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hX)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · intro g hg hfix
    have h1 : (⟨g, hg⟩ : ↥X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      ext u
      exact hfix u u.2
    rw [hk, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    obtain ⟨g, hg, u, hu, hgu⟩ := hne
    have h1 : (⟨g, hg⟩ : ↥X) ∈ φ.ker := by rw [hk]; trivial
    rw [MonoidHom.mem_ker] at h1
    exact hgu (congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : W)) h1)

private theorem p3_exists_moved_of_mem_irrPlus {Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (h : V ∈ IrrPlus Mp (⊤ : Subgroup W)) : ∃ v ∈ V, ∃ g ∈ Mp, g v ≠ v := by
  by_contra hcon
  push Not at hcon
  refine h.2.2.2.1.not_ge fun v hv => ?_
  exact ⟨hv, fun a => hcon v hv a a.2⟩

private theorem p3_inf_fixV_sup_eq {X Y : Subgroup (MulAut W)} {A : Subgroup W}
    (h : ∀ a ∈ A, ∀ g ∈ Y, g a = a) : A ⊓ fixV (X ⊔ Y) = A ⊓ fixV X := by
  refine le_antisymm (inf_le_inf_left _ (fun v hv g hg => hv g ((le_sup_left : X ≤ X ⊔ Y) hg))) ?_
  rintro v ⟨hvA, hvX⟩
  refine ⟨hvA, ?_⟩
  have hle : X ⊔ Y ≤ MulAction.stabilizer (MulAut W) v :=
    sup_le (fun x hx => (MulAction.mem_stabilizer_iff).mpr (hvX x hx))
      (fun y hy => (MulAction.mem_stabilizer_iff).mpr (h v hvA y hy))
  intro g hg
  exact (MulAction.mem_stabilizer_iff).mp (hle hg)

end Part3Aux

section Part3

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36_part3_of_simple (hS : IsSimpleGroup ↥L) (h35 : D35) (hA38 : D36A38) (hL38 : D3L38)
    (n : D36Norm M Mp T L V t)
    (hq : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    commSub (orbSup T V) L = V ∨
      (IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
        (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
        (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
          commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom ∧
            IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
              (commSub (orbSup T V) L)) ∧
        Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)) := by
  by_cases hVU : commSub (orbSup T V) L = V
  · exact Or.inl hVU
  refine Or.inr ?_
  have hVle : V ≤ commSub (orbSup T V) L := d36_V_le_U hL38 n
  have hlt : V < commSub (orbSup T V) L := lt_of_le_of_ne hVle (Ne.symm hVU)
  have hstd := d36_restrict hL38 n hq
  obtain ⟨hlt', hcent⟩ := d36_restrict_aux hL38 n hlt
  have hUeq := d36_U_eq hL38 n
  have hpart1 := d36_part1 hL38 n
  obtain ⟨hA38L, -, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have hMpinv : ∀ g ∈ Mp, ∀ v ∈ V, g v ∈ V := fun g hg v hv => n.std.hyp.irr.2.1 ⟨g, hg⟩ v hv
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    n.std.hyp.Mp_eq ▸ le_normalizer_conjClosure L T
  have hVTinv := p3_forall_mem_orbSup_of_invariant hTn hMpinv
  have hLMp : L ≤ Mp := by rw [n.Mp_eq]; exact le_sup_left
  have hLVT : L ≤ stabSub (orbSup T V) :=
    hLMp.trans (p3_le_stabSub_of_forall_mem hVTinv)
  have hLU : L ≤ stabSub (commSub (orbSup T V) L) :=
    p3_le_stabSub_commSub_of_forall_mem fun y hy w hw => hVTinv y (hLMp hy) w hw
  have hUVT : commSub (orbSup T V) L ≤ orbSup T V :=
    commSub_le_of_invariant fun x hx w hw => hVTinv x (hLMp hx) w hw
  have hSU : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commSub (orbSup T V) L) := by
    rw [hUeq]
    exact le_stabSub_orbSup _ _
  have hUfix : commSub (orbSup T V) L ⊓ fixV Mp = commSub (orbSup T V) L ⊓ fixV L := by
    rw [n.Mp_eq]
    exact p3_inf_fixV_sup_eq hpart1.2
  have hVfix : V ⊓ fixV Mp = V ⊓ fixV L := by
    rw [n.Mp_eq]
    exact p3_inf_fixV_sup_eq n.triv
  have hne : ∃ g ∈ L, ∃ u ∈ commSub (orbSup T V) L, g u ≠ u := by
    obtain ⟨v, hv, g, hg, hgv⟩ := p3_exists_moved_of_mem_irrPlus n.std.hyp.irr
    by_contra hcon
    push Not at hcon
    apply hgv
    have hvL : v ∈ fixV L := fun x hx => hcon x hx v (hVle hv)
    have : v ∈ V ⊓ fixV Mp := by
      rw [hVfix]
      exact ⟨hv, hvL⟩
    exact this.2 g hg
  have hker := p3_faithful_of_isSimpleGroup hS hLU hne
  obtain ⟨eU⟩ := p3_nonempty_mulEquiv_autSub hLU hker
  obtain ⟨eVT⟩ := p3_nonempty_mulEquiv_autSub hLVT
    (fun g hg hfix => hker g hg fun u hu => hfix u (hUVT hu))
  obtain ⟨-, ⟨t', ht', ht'V⟩, hsum, hfive⟩ := h35 _ _ _ _ _ _ hstd hlt' hcent
  obtain ⟨hpsl, hnat⟩ := hA38 _ _ _ (a38Types_congr eU hA38L) hfive
  have hIsoPSL := isPSL_congr (eU.symm.trans eVT) hpsl
  clear hstd hlt' hcent hq hpart1 hLVT hUVT hker hne hVU hlt eU eVT hMpinv hTn hVTinv hpsl
  generalize commSub (orbSup T V) L = U at *
  generalize hSdef : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) = S at *
  have hinj : Function.Injective U.subtype := Subgroup.subtype_injective _
  have hOrb : (orbSup (autSub S U) (V.subgroupOf U)).map U.subtype = U :=
    (p3_map_subtype_orbSup_autSub hSU hVle).trans hUeq.symm
  have hVmap : (V.subgroupOf U).map U.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVle
  have hfixmap : (fixV (autSub L U)).map U.subtype = U ⊓ fixV L := map_subtype_fixV_autSub hLU
  refine ⟨hIsoPSL, ?_, ?_, ?_⟩
  · obtain ⟨g, hgS, hgres⟩ := mem_autSub.mp ht'
    rw [← hSdef] at hgS
    refine ⟨g, hgS.1, hgS.2, fun hgV => ht'V ?_⟩
    rw [← hgres]
    exact (p3_resHom_mem_stabSub_subgroupOf_iff hVle g).mpr hgV
  · intro s hsT hsN hsV
    have hsS : s ∈ S := hSdef ▸ ⟨hsT, hsN⟩
    have hsU : s ∈ stabSub U := hSU hsS
    have hmem : resHom U ⟨s, hsU⟩ ∈ autSub S U := mem_autSub.mpr ⟨⟨s, hsU⟩, hsS, rfl⟩
    have hnot : resHom U ⟨s, hsU⟩ ∉ stabSub (V.subgroupOf U) := fun h =>
      hsV ((p3_resHom_mem_stabSub_subgroupOf_iff hVle ⟨s, hsU⟩).mp h)
    obtain ⟨hidx, hsum'⟩ := hsum _ hmem hnot
    refine ⟨?_, ?_⟩
    ·
      refine hUeq.trans (le_antisymm (orbSup_le fun x hx => ?_)
        (sup_le (le_orbSup S V) (map_le_orbSup hsS)))
      have hxU : x ∈ stabSub U := hSU hx
      have hxmem : resHom U ⟨x, hxU⟩ ∈ autSub S U := mem_autSub.mpr ⟨⟨x, hxU⟩, hx, rfl⟩
      rcases hidx _ hxmem with h | h
      · rw [p3_map_eq_of_mem_stabSub
          ((p3_resHom_mem_stabSub_subgroupOf_iff hVle ⟨x, hxU⟩).mp h)]
        exact le_sup_left
      · have h' : s⁻¹ * x ∈ stabSub V := by
          have h1 : resHom U (⟨s, hsU⟩⁻¹ * ⟨x, hxU⟩) ∈ stabSub (V.subgroupOf U) := by
            rw [map_mul, map_inv]
            exact h
          exact (p3_resHom_mem_stabSub_subgroupOf_iff hVle _).mp h1
        have e : x.toMonoidHom = s.toMonoidHom.comp (s⁻¹ * x).toMonoidHom := by
          ext w
          simp
        rw [e, ← Subgroup.map_map, p3_map_eq_of_mem_stabSub h']
        exact le_sup_right
    · have h2 := p3_isSumMod_map_of_injective _ hinj hsum'
      have hs_map : ((V.subgroupOf U).map (resHom U ⟨s, hsU⟩).toMonoidHom).map U.subtype =
          V.map s.toMonoidHom := by
        rw [Subgroup.map_map]
        have e : U.subtype.comp (resHom U ⟨s, hsU⟩).toMonoidHom = s.toMonoidHom.comp U.subtype := by
          ext u
          simp [resHom_apply]
        rw [e, ← Subgroup.map_map, hVmap]
      have hC : (orbSup (autSub S U) (V.subgroupOf U) ⊓ fixV (autSub L U)).map U.subtype =
          U ⊓ fixV L := by
        rw [Subgroup.map_inf _ _ _ hinj, hOrb, hfixmap]
        exact inf_eq_right.mpr inf_le_left
      rw [hC, hVmap, hs_map, hOrb] at h2
      rwa [hUfix]
  · obtain ⟨K, hK, hKfin, hKcard, π, hπ⟩ := hnat
    have hc := G64.RealizesVia.card_eq hπ
    rw [G64.card_natMod, hKcard] at hc
    have h1 : Nat.card ↥(V.subgroupOf U) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv
    have e : (V.subgroupOf U ⊓ fixV (autSub L U)).map U.subtype = V ⊓ fixV Mp := by
      rw [Subgroup.map_inf _ _ _ hinj, hVmap, hfixmap, hVfix, ← inf_assoc,
        inf_eq_left.mpr hVle]
    have h2 : Nat.card ↥(V.subgroupOf U ⊓ fixV (autSub L U)) = Nat.card ↥(V ⊓ fixV Mp) := by
      rw [← e]
      exact (Subgroup.card_map_of_injective hinj).symm
    rw [h1, h2] at hc
    simpa using hc

theorem d36_part3 (h35 : D35) (hA38 : D36A38) (hL38 : D3L38)
    (n : D36Norm M Mp T L V t)
    (hq : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    commSub (orbSup T V) L = V ∨
      (IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
        (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
        (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
          commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom ∧
            IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
              (commSub (orbSup T V) L)) ∧
        Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)) := by
  obtain ⟨hA38L, -, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  exact d36_part3_of_simple
    (CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38L) h35 hA38 hL38 n hq

end Part3

end CFSG.Quasithin
