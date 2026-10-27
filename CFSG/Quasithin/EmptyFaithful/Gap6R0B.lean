module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.D2Decomp

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {V : Type*} [CommGroup V]

section Gen

variable {X Tb : Subgroup (MulAut V)}

theorem gen_summand (hTb : Tb ≤ X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {U W : Subgroup V} (hsup : U ⊔ W = ⊤) (hinf : U ⊓ W = ⊥)
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) (hW : ∀ g ∈ X, ∀ w ∈ W, g w ∈ W)
    {S : Subgroup V} (hSW : S ≤ W) (hS : ∀ g ∈ X, ∀ z ∈ fixV Tb ⊓ W, g z ∈ S) : S = W := by
  have hall : S ⊔ U = ⊤ := by
    apply hgen
    intro g hg z hz
    have hzv : z ∈ U ⊔ W := by rw [hsup]; exact Subgroup.mem_top z
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hzv
    have hwT : w ∈ fixV Tb := by
      intro t ht
      have h1 : t (u * w) = u * w := hz t ht
      rw [map_mul] at h1
      have h3 : u⁻¹ * t u = w * (t w)⁻¹ := by
        have h2 : t u * t w = u * w := h1
        calc u⁻¹ * t u = u⁻¹ * (t u * t w) * (t w)⁻¹ := by group
          _ = u⁻¹ * (u * w) * (t w)⁻¹ := by rw [h2]
          _ = w * (t w)⁻¹ := by group
      have h4 : w * (t w)⁻¹ ∈ U ⊓ W :=
        ⟨h3 ▸ U.mul_mem (U.inv_mem hu) (hU t (hTb ht) u hu),
          W.mul_mem hw (W.inv_mem (hW t (hTb ht) w hw))⟩
      rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h4
      exact h4.symm
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hU g hg u hu))
      (Subgroup.mem_sup_left (hS g hg w ⟨hwT, hw⟩))
  refine le_antisymm hSW fun x hx => ?_
  have hxs : x ∈ S ⊔ U := by rw [hall]; exact Subgroup.mem_top x
  obtain ⟨s, hs, u', hu', hsx⟩ := Subgroup.mem_sup.mp hxs
  have h5 : u' ∈ U ⊓ W := by
    refine ⟨hu', ?_⟩
    have : u' = s⁻¹ * x := by rw [← hsx]; group
    rw [this]
    exact W.mul_mem (W.inv_mem (hSW hs)) hx
  rw [hinf, Subgroup.mem_bot] at h5
  rw [h5, mul_one] at hsx
  rw [← hsx]
  exact hs

theorem autSub_mem_sylow2Of (hTb : Tb ∈ sylow2Of X) {W : Subgroup V} (hXW : X ≤ stabSub W) :
    autSub Tb W ∈ sylow2Of (autSub X W) := by
  obtain ⟨hTX, hTp, hTi⟩ := hTb
  let ρ : ↥X →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hXW)
  have hrange : ρ.range = autSub X W := by
    ext φ
    rw [MonoidHom.mem_range, mem_autSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXW x.2⟩, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (Tb.subgroupOf X).map ρ = autSub Tb W := by
    ext φ
    rw [Subgroup.mem_map, mem_autSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hXW x.2⟩, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hTX hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hp2 : IsPGroup 2 ↥(Tb.subgroupOf X) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  refine ⟨autSub_mono hTX W, ?_, ?_⟩
  · rw [← hmap]
    exact hp2.map ρ
  · rw [← hmap, ← hrange]
    have h1 : ((Tb.subgroupOf X).map ρ).subgroupOf ρ.range =
        (Tb.subgroupOf X).map ρ.rangeRestrict := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
    rw [h1]
    intro hd
    apply hTi
    exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem pCoreOf_two_autSub_eq_bot [Finite V] (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {U W : Subgroup V} (hsup : U ⊔ W = ⊤) (hinf : U ⊓ W = ⊥)
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) (hW : ∀ g ∈ X, ∀ w ∈ W, g w ∈ W) :
    pCoreOf 2 (autSub X W) = ⊥ := by
  have hTX : Tb ≤ X := hsyl.1
  have hXW : X ≤ stabSub W := by
    intro g hg u
    refine ⟨fun hu => ?_, fun hu => hW g hg u hu⟩
    have := hW g⁻¹ (X.inv_mem hg) (g u) hu
    simpa using this
  have hTsyl : IsSylowTwoOf (autSub Tb W) (autSub X W) := autSub_mem_sylow2Of hsyl hXW
  have hQT : pCoreOf 2 (autSub X W) ≤ autSub Tb W := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  let S : Subgroup V := (fixV (Subgroup.zpowers q)).map W.subtype
  have hfix : ∀ g ∈ X, ∀ z ∈ fixV Tb ⊓ W, g z ∈ S := by
    intro g hg z hz
    have hgs : g ∈ stabSub W := hXW hg
    set gb : MulAut ↥W := resHom W ⟨g, hgs⟩ with hgb
    have hgbm : gb ∈ autSub X W := mem_autSub.mpr ⟨⟨g, hgs⟩, hg, rfl⟩
    have hconj : gb⁻¹ * q * gb ∈ pCoreOf 2 (autSub X W) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (autSub X W) ((autSub X W).inv_mem hgbm)) q).mp hq
      simpa [mul_assoc] using h1
    obtain ⟨t, htT, hteq⟩ := mem_autSub.mp (hQT hconj)
    set z' : ↥W := ⟨z, hz.2⟩ with hz'
    have h2 : (gb⁻¹ * q * gb) z' = z' := by
      rw [← hteq]
      ext
      exact hz.1 _ htT
    have h3 : q (gb z') = gb z' := by
      have := congrArg gb h2
      simpa using this
    refine ⟨gb z', ?_, rfl⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hpow : ∀ k : ℤ, (q ^ k) (gb z') = gb z' := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [zpow_add_one, MulAut.mul_apply, h3, ih]
      | pred n ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : q⁻¹ (gb z') = gb z' := (MulEquiv.symm_apply_eq q).mpr h3.symm
        rw [this]
        exact ih
    exact hpow k
  have hSW : S ≤ W := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hSeq : S = W := gen_summand hTX hgen hsup hinf hU hW hSW hfix
  ext w
  have hw : (w : V) ∈ S := by rw [hSeq]; exact w.2
  obtain ⟨w', hw', hww'⟩ := hw
  have : w' = w := Subtype.ext hww'
  rw [← this]
  have := hw' q (Subgroup.mem_zpowers q)
  simpa using this

end Gen

end Gap6

end CFSG.Quasithin
