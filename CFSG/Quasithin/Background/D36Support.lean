module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D216Sub

public section

namespace CFSG.Quasithin

namespace D36

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem qhatOf_autSub_le_of_offender {Y : Type} [CommGroup Y] [Finite Y]
    (hY : ∀ y : Y, y ^ 2 = 1) {X A : Subgroup (MulAut Y)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {U : Subgroup Y}
    (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) : qhatOf (autSub X U) ≤ (r : WithTop ℚ) := by
  obtain ⟨r', hr', -, hAk, -⟩ := QhatStar_spec hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  obtain ⟨⟨hA2, hAr⟩, hAk3⟩ := hAk
  have hplus : A ∈ RPlus X := D2_3_2 hA2 hAk3 (by rw [hAr]; exact hr'.symm)
  have h5 := D2_5 hY (X := X) (A := A) (r := r') ⟨⟨hA2, hAr.le⟩, hplus⟩ hU hUA
  exact kq_le_iff.mpr ⟨autSub A U, h5.1, commSeries_autSub_eq_bot hU hAk3, h5.2⟩

theorem exists_rat_of_qhatOf_le {Y : Type} [CommGroup Y] [Finite Y]
    {X : Subgroup (MulAut Y)} {c : ℚ} (h : qhatOf X ≤ (c : WithTop ℚ)) :
    ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ c := by
  have hne : qhatOf X ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  exact ⟨r, hr.symm, WithTop.coe_le_coe.mp (hr ▸ h)⟩

theorem isPGroup_of_mem_QhatStar {Y : Type} [CommGroup Y] [Finite Y]
    {X A : Subgroup (MulAut Y)} (hA : A ∈ QhatStar X) : IsPGroup 2 A := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.isElemAbelian2.isPGroup

section AutSub

variable {W : Type} [CommGroup W]

theorem autSub_conjBy {D : Subgroup (MulAut W)} {U : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub U) :
    autSub (conjBy g D) U = conjBy (resHom U ⟨g, hg⟩) (autSub D U) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨h, hhD, rfl⟩ := mem_autSub.mp hφ
    rw [mem_conjBy_iff] at hhD ⊢
    have hk : g⁻¹ * (h : MulAut W) * g ∈ stabSub U :=
      (stabSub U).mul_mem ((stabSub U).mul_mem ((stabSub U).inv_mem hg) h.2) hg
    refine mem_autSub.mpr ⟨⟨g⁻¹ * (h : MulAut W) * g, hk⟩, hhD, ?_⟩
    have e : (⟨g⁻¹ * (h : MulAut W) * g, hk⟩ : stabSub U) = ⟨g, hg⟩⁻¹ * h * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_mul, map_inv]
  · intro hφ
    rw [mem_conjBy_iff] at hφ
    obtain ⟨k, hkD, hk⟩ := mem_autSub.mp hφ
    refine mem_autSub.mpr ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · exact mem_conjBy_of_mem hkD
    · rw [map_mul, map_mul, map_inv, hk]
      group

theorem autSub_le_stabSub_subgroupOf {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hDU : D ≤ stabSub U) : autSub D VT ≤ stabSub (U.subgroupOf VT) := by
  intro φ hφ u
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  exact hDU hg u

theorem commSub_subgroupOf_autSub_ne_bot {D : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hDVT : D ≤ stabSub VT) (hUV : U ≤ VT) (hne : commSub U D ≠ ⊥) :
    commSub (U.subgroupOf VT) (autSub D VT) ≠ ⊥ := by
  intro h
  apply hne
  have := map_commSub_autSub hDVT (U.subgroupOf VT)
  rw [h, Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hUV] at this
  exact this.symm

theorem map_autSub_autSub_le {X : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) :
    (autSub (autSub X VT) (U.subgroupOf VT)).map
        ((MulAut.congr (Subgroup.subgroupOfEquivOfLe hUV)).toMonoidHom) ≤ autSub X U := by
  rintro φ ⟨ψ, hψ, rfl⟩
  obtain ⟨g, hgY, rfl⟩ := mem_autSub.mp hψ
  obtain ⟨h, hhX, hh⟩ := mem_autSub.mp hgY
  have hhU : (h : MulAut W) ∈ stabSub U := by
    intro u
    by_cases hu : u ∈ VT
    · have := g.2 ⟨u, hu⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hh, resHom_apply] at this
      exact this
    · have hnu : ¬ u ∈ U := fun h' => hu (hUV h')
      have hnh : ¬ (h : MulAut W) u ∈ VT := fun h' => hu ((h.2 u).mp h')
      exact ⟨fun h' => absurd (hUV h') hnh, fun h' => absurd h' hnu⟩
  refine mem_autSub.mpr ⟨⟨h, hhU⟩, hhX, ?_⟩
  ext u
  show ((resHom U ⟨h, hhU⟩ u : ↥U) : W) =
    ((resHom (U.subgroupOf VT) g ⟨⟨u, hUV u.2⟩, u.2⟩ : ↥(U.subgroupOf VT)) : ↥VT).1
  rw [resHom_apply, resHom_apply, ← hh, resHom_apply]

end AutSub

section Sylow

theorem isSylowTwoOf_map_hom {G K : Type*} [Group G] [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

variable {W : Type} [CommGroup W]

theorem autSub_eq_map {X : Subgroup (MulAut W)} {U : Subgroup W} (hXS : X ≤ stabSub U)
    {Y : Subgroup (MulAut W)} (hYX : Y ≤ X) :
    autSub Y U = (Y.subgroupOf X).map ((resHom U).comp (Subgroup.inclusion hXS)) := by
  ext φ
  rw [mem_autSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hgY, rfl⟩
    exact ⟨⟨g.1, hYX hgY⟩, hgY, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hXS x.2⟩, hx, rfl⟩

theorem isSylowTwoOf_autSub {X T : Subgroup (MulAut W)} {U : Subgroup W}
    (hXS : X ≤ stabSub U) (hTX : T ≤ X) (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (autSub T U) (autSub X U) := by
  have h := isSylowTwoOf_map_hom hT ((resHom U).comp (Subgroup.inclusion hXS))
  rw [← autSub_eq_map hXS hTX] at h
  have hX : autSub X U = ((resHom U).comp (Subgroup.inclusion hXS)).range := by
    rw [autSub_eq_map hXS le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rwa [hX]

end Sylow

section Orb

variable {W : Type} [CommGroup W]

theorem mem_orbSup_of_mem_Mp {Mp T : Subgroup (MulAut W)} {V : Subgroup W}
    (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hV : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V) {x : MulAut W} (hx : x ∈ Mp) :
    ∀ u ∈ orbSup T V, x u ∈ orbSup T V := by
  intro u hu
  have : (orbSup T V).map x.toMonoidHom ≤ orbSup T V := by
    simp only [orbSup, Subgroup.map_iSup]
    refine iSup_le fun s => iSup_le fun hs => ?_
    rw [Subgroup.map_map]
    rintro _ ⟨v, hv, rfl⟩
    have hy : s⁻¹ * x * s ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn hs) x).mp hx
    have e : (x.toMonoidHom.comp s.toMonoidHom) v = s ((s⁻¹ * x * s) v) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact map_le_orbSup hs ⟨(s⁻¹ * x * s) v, hV _ hy v hv, rfl⟩
  exact this ⟨u, hu, rfl⟩

theorem le_stabSub_orbSup_Mp {Mp T : Subgroup (MulAut W)} {V : Subgroup W}
    (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hV : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V) : Mp ≤ stabSub (orbSup T V) := by
  intro x hx u
  refine ⟨fun h => ?_, fun h => mem_orbSup_of_mem_Mp hTn hV hx u h⟩
  have := mem_orbSup_of_mem_Mp hTn hV (Mp.inv_mem hx) _ h
  simpa using this

theorem exists_conj_commSub_ne_bot {T D : Subgroup (MulAut W)} {V U VT : Subgroup W}
    (hVT : VT = orbSup T V) (hVU : V ≤ U) (hnot : ¬ VT ≤ fixV D) :
    ∃ g ∈ T, commSub U (conjBy g D) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply hnot
  rw [hVT]
  refine orbSup_le fun s hs => ?_
  rintro _ ⟨v, hv, rfl⟩
  have h1 := commSub_eq_bot_iff.mp (hcon s⁻¹ (T.inv_mem hs)) (hVU hv)
  have h2 := mem_fixV_conjBy.mp h1
  simpa using h2

end Orb

section Comm

variable {W : Type} [CommGroup W]

theorem mul_inv_mem_commSub {Mp L L' : Subgroup (MulAut W)} {V VT : Subgroup W}
    (hMp : Mp = L ⊔ L') (hVT : V ≤ VT) (hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V)
    (htriv : ∀ v ∈ V, ∀ g ∈ L', g v = v) :
    ∀ x ∈ Mp, ∀ v ∈ V, x v * v⁻¹ ∈ commSub VT L := by
  let P : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ Mp ∧ ∀ v ∈ V, x v * v⁻¹ ∈ commSub VT L}
      one_mem' := ⟨Mp.one_mem, fun v _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨Mp.mul_mem haM hbM, fun v hv => ?_⟩
        have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact mul_mem (ha (b v) (hinv b hbM v hv)) (hb v hv)
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨Mp.inv_mem haM, fun v hv => ?_⟩
        have hw : a⁻¹ v ∈ V := hinv a⁻¹ (Mp.inv_mem haM) v hv
        have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
          rw [show a (a⁻¹ v) = v by simp]
          group
        rw [e]
        exact inv_mem (ha (a⁻¹ v) hw) }
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have hL'Mp : L' ≤ Mp := by rw [hMp]; exact le_sup_right
  have hL : L ≤ P := fun l hl =>
    ⟨hLMp hl, fun v hv => Subgroup.subset_closure ⟨l, hl, v, hVT hv, rfl⟩⟩
  have hL' : L' ≤ P := fun g hg =>
    ⟨hL'Mp hg, fun v hv => by rw [htriv v hv g hg]; simp⟩
  have hMpP : Mp ≤ P := by rw [hMp]; exact sup_le hL hL'
  exact fun x hx => (hMpP hx).2

theorem le_commSub_of_commOf {Mp L L' : Subgroup (MulAut W)} {V VT : Subgroup W}
    (hMp : Mp = L ⊔ L') (hVT : V ≤ VT) (hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V)
    (htriv : ∀ v ∈ V, ∀ g ∈ L', g v = v) (hcomm : XMod.commOf ↥Mp V = V) :
    V ≤ commSub VT L := by
  rw [← hcomm]
  exact (XMod.commOf_le_iff (A := ↥Mp)).mpr fun a v hv =>
    mul_inv_mem_commSub hMp hVT hinv htriv a.1 a.2 v hv

end Comm

section Part2

theorem part2_aux {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {X T : Subgroup (MulAut W)} {V VT U : Subgroup W} (hVT : VT = orbSup T V)
    (hTX : T ≤ X) (hXS : X ≤ stabSub VT) (hSyl : IsSylowTwoOf T X)
    (hq : qhatOf (autSub X VT) ≤ ((2 : ℚ) : WithTop ℚ))
    (hVU : V ≤ U) (hUV : U ≤ VT)
    (hAct : ∀ D : Subgroup (MulAut W), D ≤ T → autSub D VT ∈ QhatStar (autSub T VT) →
      D ≤ stabSub U) :
    qhatOf (autSub X U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hTS : T ≤ stabSub VT := hTX.trans hXS
  have hY : ∀ y : ↥VT, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hexp y.1)
  obtain ⟨r, hr, hr2⟩ := exists_rat_of_qhatOf_le hq
  have hTX' : autSub T VT ≤ autSub X VT := autSub_mono hTX VT
  have hSyl' : IsSylowTwoOf (autSub T VT) (autSub X VT) := isSylowTwoOf_autSub hXS hTX hSyl
  obtain ⟨B, hB⟩ := QhatStar_nonempty hr hr2
  obtain ⟨x, hx, hBx⟩ := F7.isSylowTwoOf_exists_conj_le hSyl' (QhatStar_le hB)
    (isPGroup_of_mem_QhatStar hB)
  have hA₀ : conjBy x⁻¹ B ∈ QhatStar (autSub X VT) :=
    conjBy_mem_QhatStar hB ((autSub X VT).inv_mem hx)
  have hA₀T : conjBy x⁻¹ B ≤ autSub T VT := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have := hBx hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  have hQ : QhatStar (autSub T VT) = {A | A ∈ QhatStar (autSub X VT) ∧ A ≤ autSub T VT} :=
    QhatStar_of_le216 hr hr2 hA₀ hA₀T hTX'
  have hA₀T' : conjBy x⁻¹ B ∈ QhatStar (autSub T VT) := by
    rw [hQ]
    exact ⟨hA₀, hA₀T⟩
  obtain ⟨D, hDT, hDA⟩ := exists_le_of_le_autSub hA₀T
  have hnot : ¬ VT ≤ fixV D := by
    intro h
    have : autSub D VT = ⊥ :=
      (autSub_eq_bot_iff (hDT.trans hTS)).mpr (commSub_eq_bot_iff.mpr h)
    exact ne_bot_of_mem_QhatStar216 hA₀ (hDA ▸ this)
  obtain ⟨g, hgT, hgne⟩ := exists_conj_commSub_ne_bot hVT hVU hnot
  have hgS : g ∈ stabSub VT := hTS hgT
  have hD'T : conjBy g D ≤ T := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e]
    exact T.mul_mem (T.mul_mem hgT (hDT hy)) (T.inv_mem hgT)
  have hcongr : autSub (conjBy g D) VT = conjBy (resHom VT ⟨g, hgS⟩) (conjBy x⁻¹ B) := by
    rw [← hDA]
    exact autSub_conjBy hgS
  have hgT' : resHom VT ⟨g, hgS⟩ ∈ autSub T VT := mem_autSub.mpr ⟨⟨g, hgS⟩, hgT, rfl⟩
  have hA' : autSub (conjBy g D) VT ∈ QhatStar (autSub T VT) := by
    rw [hcongr]
    exact conjBy_mem_QhatStar hA₀T' hgT'
  have hD'U : conjBy g D ≤ stabSub U := hAct _ hD'T hA'
  have hA'X : autSub (conjBy g D) VT ∈ QhatStar (autSub X VT) := by
    rw [hQ] at hA'
    exact hA'.1
  have h1 : qhatOf (autSub (autSub X VT) (U.subgroupOf VT)) ≤ (r : WithTop ℚ) :=
    qhatOf_autSub_le_of_offender hY hr hA'X (autSub_le_stabSub_subgroupOf hD'U)
      (commSub_subgroupOf_autSub_ne_bot (hD'T.trans hTS) hUV hgne)
  have h2 := kq_map_mulAutCongr_le (Subgroup.subgroupOfEquivOfLe hUV)
    (autSub (autSub X VT) (U.subgroupOf VT)) 3
  have h3 : kq (autSub X U) 3 ≤
      kq ((autSub (autSub X VT) (U.subgroupOf VT)).map
        ((MulAut.congr (Subgroup.subgroupOfEquivOfLe hUV)).toMonoidHom)) 3 :=
    kq_le_kq_of_le216 (map_autSub_autSub_le hUV) 3
  exact h3.trans (h2.trans (h1.trans (WithTop.coe_le_coe.mpr hr2)))

end Part2

end D36

end CFSG.Quasithin
