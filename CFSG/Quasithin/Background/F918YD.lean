module

public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.F918P8B
public import CFSG.Quasithin.Background.F918YC

public section

namespace CFSG.Quasithin

section YDAux

variable {W : Type} [CommGroup W]

private theorem yd_map_eq_of_mem {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) {x : MulAut W} (hx : x ∈ L) :
    V.map x.toMonoidHom = V := by
  refine le_antisymm ?_ fun v hv => ⟨x⁻¹ v, hinv x⁻¹ (L.inv_mem hx) v hv, by simp⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hinv x hx v hv

private theorem yd_mem_stabSub_of_map_eq {V : Subgroup W} {g : MulAut W}
    (h : V.map g.toMonoidHom = V) : g ∈ stabSub V :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

private theorem yd_map_mul (a b : MulAut W) (V : Subgroup W) :
    V.map (a * b).toMonoidHom = (V.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem yd_resHom_mem_stabSub_iff {U V : Subgroup W} (hVU : V ≤ U) (s : stabSub U) :
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

private theorem yd_map_subtype_map {U V : Subgroup W} (hVU : V ≤ U) {s : MulAut W}
    (hs : s ∈ stabSub U) :
    ((V.subgroupOf U).map (resHom U ⟨s, hs⟩).toMonoidHom).map U.subtype = V.map s.toMonoidHom := by
  rw [Subgroup.map_map]
  have e : U.subtype.comp (resHom U ⟨s, hs⟩).toMonoidHom = s.toMonoidHom.comp U.subtype := by
    ext u
    simp [resHom_apply]
  rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hVU]

private theorem yd_sup_eq_top {U V : Subgroup W} (hVU : V ≤ U) {s : MulAut W} (hs : s ∈ stabSub U)
    (hU : U = V ⊔ V.map s.toMonoidHom) :
    V.subgroupOf U ⊔ (V.subgroupOf U).map (resHom U ⟨s, hs⟩).toMonoidHom = ⊤ := by
  apply Subgroup.map_injective U.subtype_injective
  rw [Subgroup.map_sup, yd_map_subtype_map hVU hs, Subgroup.map_subgroupOf_eq_of_le hVU, ← hU,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem yd_conj_mem_autSub {L : Subgroup (MulAut W)} {U : Subgroup W} {g : stabSub U}
    (hg : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))) {x : MulAut ↥U}
    (hx : x ∈ autSub L U) : resHom U g * x * (resHom U g)⁻¹ ∈ autSub L U := by
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hx
  refine mem_autSub.mpr ⟨g * l * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hg l).mp hl

private theorem yd_normalizes {L : Subgroup (MulAut W)} {U : Subgroup W} {s : MulAut W}
    (hs : s ∈ stabSub U) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (x : MulAut ↥U) :
    x ∈ autSub L U ↔ resHom U ⟨s, hs⟩ * x * (resHom U ⟨s, hs⟩)⁻¹ ∈ autSub L U := by
  refine ⟨yd_conj_mem_autSub hsN, fun h => ?_⟩
  have h1 := yd_conj_mem_autSub (g := ⟨s, hs⟩⁻¹) (Subgroup.inv_mem _ hsN) h
  simpa [map_inv, mul_assoc] using h1

private theorem yd_forall_mem_orbSup {Mp T : Subgroup (MulAut W)} {V : Subgroup W}
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

private theorem yd_exists_moved {Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (h : V ∈ IrrPlus Mp (⊤ : Subgroup W)) : ∃ v ∈ V, ∃ g ∈ Mp, g v ≠ v := by
  by_contra hcon
  push Not at hcon
  refine h.2.2.2.1.not_ge fun v hv => ?_
  exact ⟨hv, fun a => hcon v hv a a.2⟩

private theorem yd_lt_of_sup [Finite W] {V U : Subgroup W} {s : MulAut W} (hVU : V ≤ U)
    (hU : U = V ⊔ V.map s.toMonoidHom) (hsV : s ∉ stabSub V) : V < U := by
  refine lt_of_le_of_ne hVU fun h => hsV (yd_mem_stabSub_of_map_eq ?_)
  have h1 : V.map s.toMonoidHom ≤ V :=
    calc V.map s.toMonoidHom ≤ V ⊔ V.map s.toMonoidHom := le_sup_right
      _ = U := hU.symm
      _ = V := h.symm
  exact Subgroup.eq_of_le_of_card_ge h1 (by rw [Subgroup.card_map_of_injective s.injective])

end YDAux

private theorem yd_assemble {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U V : Subgroup W} {s : MulAut W}
    (hexp : ∀ w : ↥U, w ^ 2 = 1) (hVU : V ≤ U) (hsU : s ∈ stabSub U)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) (hsV : s ∉ stabSub V)
    (hU : U = V ⊔ V.map s.toMonoidHom) (hint : V ⊓ V.map s.toMonoidHom ≤ fixV L)
    (hZne : V ⊓ fixV L ≠ ⊥)
    (hinv : ∀ x ∈ autSub L U, ∀ v ∈ V.subgroupOf U, x v ∈ V.subgroupOf U)
    (hcomm : XMod.commOf ↥(autSub L U) (V.subgroupOf U) = V.subgroupOf U)
    (hnat : BinaryNaturalSL (autSub L U) (V.subgroupOf U) (V.subgroupOf U ⊓ fixV (autSub L U)) 3 1)
    (hnot : ¬ SecIsoL (autSub L U) (V.subgroupOf U) (V.subgroupOf U ⊓ fixV (autSub L U))
        ((V.subgroupOf U).map (resHom U ⟨s, hsU⟩).toMonoidHom)
        ((V.subgroupOf U).map (resHom U ⟨s, hsU⟩).toMonoidHom ⊓ fixV (autSub L U))) :
    N4Base ↥U (autSub L U) (V.subgroupOf U) (resHom U ⟨s, hsU⟩) := by
  have hZne' : V.subgroupOf U ⊓ fixV (autSub L U) ≠ ⊥ := by
    intro h
    apply hZne
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hVU hx.1⟩ : ↥U) ∈ V.subgroupOf U ⊓ fixV (autSub L U) :=
      ⟨hx.1, mem_fixV_autSub.mpr fun g hg _ => hx.2 g hg⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  refine ⟨hexp, hinv, hcomm, hnat, ?_, yd_normalizes hsU hsN, ?_, ?_, yd_sup_eq_top hVU hsU hU, ?_⟩
  · have h1 : 1 < Nat.card ↥(V.subgroupOf U ⊓ fixV (autSub L U)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hZne'
    have h2 := card_fixV_le_two_of_natural3 hexp (autSub L U) (V.subgroupOf U) hinv hcomm hnat
    omega
  · intro h
    exact hsV ((yd_resHom_mem_stabSub_iff hVU ⟨s, hsU⟩).mp (yd_mem_stabSub_of_map_eq h))
  · rintro ⟨l₀, hl₀, hc⟩
    refine hnot (secIsoL_of_commuting hinv hc ?_)
    rw [yd_map_mul, yd_map_eq_of_mem hinv (Subgroup.inv_mem _ hl₀)]
  · intro x hx
    have h1 : (x : W) ∈ V.map s.toMonoidHom := by
      have : (x : W) ∈ ((V.subgroupOf U).map (resHom U ⟨s, hsU⟩).toMonoidHom).map U.subtype :=
        ⟨x, hx.2, rfl⟩
      rwa [yd_map_subtype_map hVU hsU] at this
    exact mem_fixV_autSub.mpr fun g hg _ => hint ⟨hx.1, h1⟩ g hg

theorem d36_n4_base (h35 : D35)
    (hA38 : D36A38) (hL38 : D3L38)
    {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (n : D36Norm M Mp T L V t)
    (hq : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ))
    {s : MulAut W} (hsT : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hsV : s ∉ stabSub V)
    (hU : commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom)
    (hsum : IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
      (commSub (orbSup T V) L))
    (hZne : V ⊓ fixV Mp ≠ ⊥) :
    ∃ σ : MulAut ↥(commSub (orbSup T V) L),
      N4Base ↥(commSub (orbSup T V) L) (autSub L (commSub (orbSup T V) L))
        (V.subgroupOf (commSub (orbSup T V) L)) σ := by
  have hVle : V ≤ commSub (orbSup T V) L := d36_V_le_U hL38 n
  have hlt : V < commSub (orbSup T V) L := yd_lt_of_sup hVle hU hsV
  have hstd := d36_restrict hL38 n hq
  obtain ⟨hlt', hcent⟩ := d36_restrict_aux hL38 n hlt
  have hUeq := d36_U_eq hL38 n
  obtain ⟨hA38L, -, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have hMpinv : ∀ g ∈ Mp, ∀ v ∈ V, g v ∈ V := fun g hg v hv => n.std.hyp.irr.2.1 ⟨g, hg⟩ v hv
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    n.std.hyp.Mp_eq ▸ le_normalizer_conjClosure L T
  have hLMp : L ≤ Mp := by rw [n.Mp_eq]; exact le_sup_left
  have hLVT : L ≤ stabSub (orbSup T V) :=
    le_stabSub_of_forall_mem fun g hg w hw => yd_forall_mem_orbSup hTn hMpinv g (hLMp hg) w hw
  have hLU : L ≤ stabSub (commSub (orbSup T V) L) := fun g hg =>
    mem_stabSub_commSub (hLVT hg) (Subgroup.le_normalizer hg)
  have hsU : s ∈ stabSub (commSub (orbSup T V) L) := by
    rw [hUeq]
    exact le_stabSub_orbSup _ _ ⟨hsT, hsN⟩
  have hS : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38L
  have hnc : ¬ L ≤ centSub (commSub (orbSup T V) L) := by
    intro hle
    obtain ⟨v, hv, g, hg, hgv⟩ := yd_exists_moved n.std.hyp.irr
    have hstab : Mp ≤ MulAction.stabilizer (MulAut W) v := by
      rw [n.Mp_eq]
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact MulAction.mem_stabilizer_iff.mpr (hle hg v (hVle hv))
      · exact MulAction.mem_stabilizer_iff.mpr (n.triv v hv g hg)
    exact hgv (MulAction.mem_stabilizer_iff.mp (hstab hg))
  have eU := autSubEquivOfFaithful hLU (inf_centSub_eq_bot_of_isSimpleGroup hS hLU hnc)
  obtain ⟨-, -, hsum35, hfive⟩ := h35 _ _ _ _ _ _ hstd hlt' hcent
  obtain ⟨-, hnat⟩ := hA38 _ _ _ (a38Types_congr eU hA38L) hfive
  have hmem : resHom _ ⟨s, hsU⟩ ∈
      autSub (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub (orbSup T V) L) :=
    mem_autSub.mpr ⟨⟨s, hsU⟩, ⟨hsT, hsN⟩, rfl⟩
  have hnots : resHom _ ⟨s, hsU⟩ ∉ stabSub (V.subgroupOf (commSub (orbSup T V) L)) := fun h =>
    hsV ((yd_resHom_mem_stabSub_iff hVle ⟨s, hsU⟩).mp h)
  have hnot := d310_not_secIsoL hstd hmem (hsum35 _ hmem hnots).2
  have hint : V ⊓ V.map s.toMonoidHom ≤ fixV L := by
    intro x hx g hg
    have h1 := hsum.2 ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
    exact h1.2 g (hLMp hg)
  have hZne' : V ⊓ fixV L ≠ ⊥ := by
    intro h
    apply hZne
    rw [eq_bot_iff] at h ⊢
    exact (inf_le_inf_left V fun x hx g hg => hx g (hLMp hg)).trans h
  exact ⟨resHom _ ⟨s, hsU⟩, yd_assemble hstd.hyp.exp hVle hsU hsN hsV hU hint hZne'
    (fun x hx v hv => hstd.hyp.irr.2.1 ⟨x, hx⟩ v hv) hstd.hyp.irr.2.2.1 hnat hnot⟩

end CFSG.Quasithin
