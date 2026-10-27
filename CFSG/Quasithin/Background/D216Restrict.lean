module

public import CFSG.Quasithin.Background.D216Sub
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

section Restrict

variable {V : Type*} [CommGroup V] [Finite V]

structure SuppData (G : Subgroup (MulAut V)) (U W : Subgroup V) : Prop where
  sup : U ⊔ W = ⊤
  inf : U ⊓ W = ⊥
  stab : G ≤ stabSub U
  triv : G ≤ centSub W

variable {G : Subgroup (MulAut V)} {U W : Subgroup V}

omit [Finite V] in
theorem SuppData.inf_centSub (h : SuppData G U W) : G ⊓ centSub U = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ U ⊔ W := by rw [h.sup]; exact Subgroup.mem_top v
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv
  show g (u * w) = (1 : MulAut V) (u * w)
  rw [map_mul, hg.2 u hu, h.triv hg.1 w hw]
  rfl

omit [Finite V] in
theorem SuppData.mono (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    SuppData A U W := ⟨h.sup, h.inf, hA.trans h.stab, hA.trans h.triv⟩

theorem SuppData.rk_autSub (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    rk (autSub A U) = rk A := by
  have := rk_autSub_add_rk_inf (h.stab.trans' hA)
  have h0 : A ⊓ centSub U = ⊥ := le_bot_iff.mp (h.inf_centSub ▸ inf_le_inf_right _ hA)
  rw [h0, rk_bot] at this
  omega

omit [Finite V] in
theorem SuppData.fixV_eq (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    fixV A = (U ⊓ fixV A) ⊔ W := by
  have hWfix : W ≤ fixV A := fun w hw a ha => h.triv (hA ha) w hw
  apply le_antisymm
  · intro x hx
    have hxs : x ∈ U ⊔ W := by rw [h.sup]; exact Subgroup.mem_top x
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hxs
    have hu' : u ∈ fixV A := by
      have : u = (u * w) * w⁻¹ := by group
      rw [this]
      exact (fixV A).mul_mem hx ((fixV A).inv_mem (hWfix hw))
    exact Subgroup.mul_mem_sup ⟨hu, hu'⟩ hw
  · exact sup_le inf_le_right hWfix

omit [Finite V] in
theorem SuppData.isDirectSum_fixV (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    IsDirectSum (fixV A) (U ⊓ fixV A) W :=
  ⟨(h.fixV_eq hA).symm, le_bot_iff.mp (h.inf ▸ inf_le_inf inf_le_left le_rfl)⟩

theorem SuppData.rkIdx_fixV (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    rkIdx (fixV A) = rkIdx (fixV (autSub A U)) := by
  have hAs : A ≤ stabSub U := hA.trans h.stab
  have h1 := rk_eq_add_of_isDirectSum (h.isDirectSum_fixV hA)
  have h2 := rk_eq_add_of_isDirectSum (W := (⊤ : Subgroup V)) (U₁ := U) (U₂ := W) ⟨h.sup, h.inf⟩
  rw [rk_top] at h2
  have h3 := rk_add_rkIdx (fixV A)
  have h4 := rkIdx_autSub_add hAs
  omega

theorem SuppData.rAV_autSub (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    rAV (autSub A U) = rAV A := by
  unfold rAV
  rw [h.rk_autSub hA, h.rkIdx_fixV hA]


omit [Finite V] in
theorem commSub_map_subtype {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U)
    (S : Subgroup U) :
    commSub (S.map U.subtype) A = (commSub S (autSub A U)).map U.subtype := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨g, hg, w, hw, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hw
    exact ⟨resHom U ⟨g, hA hg⟩ s * s⁻¹,
      ⟨resHom U ⟨g, hA hg⟩, mem_autSub.mpr ⟨⟨g, hA hg⟩, hg, rfl⟩, s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨φ, hφ, s, hs, rfl⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact ⟨g, hg, s, ⟨s, hs, rfl⟩, rfl⟩

omit [Finite V] in
theorem SuppData.commSub_top (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    commSub ⊤ A = commSub U A := by
  have hWfix : W ≤ fixV A := fun w hw a ha => h.triv (hA ha) w hw
  rw [← h.sup, commSub_sup_left, (commSub_eq_bot_iff.mpr hWfix), sup_bot_eq]

omit [Finite V] in
theorem SuppData.map_commSeries (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G)
    (k : ℕ) : (commSeries (autSub A U) (k + 1)).map U.subtype = commSeries A (k + 1) := by
  have hAs : A ≤ stabSub U := hA.trans h.stab
  induction k with
  | zero =>
    have e1 : commSeries (autSub A U) 1 = commSub ⊤ (autSub A U) := by
      rw [commSeries_one, commV_eq_commSub]
    have e2 : commSeries A 1 = commSub ⊤ A := by rw [commSeries_one, commV_eq_commSub]
    rw [e1, e2, h.commSub_top hA, ← commSub_map_subtype hAs, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  | succ k ih =>
    have e1 : commSeries (autSub A U) (k + 2) =
        commSub (commSeries (autSub A U) (k + 1)) (autSub A U) := rfl
    have e2 : commSeries A (k + 2) = commSub (commSeries A (k + 1)) A := rfl
    rw [e1, e2, ← commSub_map_subtype hAs, ih]

omit [Finite V] in
theorem SuppData.commSeries_eq_bot_iff (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G)
    {k : ℕ} (hk : 1 ≤ k) : commSeries (autSub A U) k = ⊥ ↔ commSeries A k = ⊥ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [← h.map_commSeries hA j]
  exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).symm


omit [Finite V] in
theorem SuppData.eq_of_resHom_eq (h : SuppData G U W) {g k : MulAut V} (hg : g ∈ G) (hk : k ∈ G)
    (e : resHom U ⟨g, h.stab hg⟩ = resHom U ⟨k, h.stab hk⟩) : g = k := by
  have h1 : (⟨g, h.stab hg⟩ * ⟨k, h.stab hk⟩⁻¹ : stabSub U) ∈ (resHom U).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]
  rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
  have h2 : g * k⁻¹ ∈ G ⊓ centSub U := ⟨G.mul_mem hg (G.inv_mem hk), h1⟩
  rw [h.inf_centSub, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

omit [Finite V] in
theorem SuppData.autSub_le_iff (h : SuppData G U W) {A A' : Subgroup (MulAut V)} (hA : A ≤ G)
    (hA' : A' ≤ G) : autSub A U ≤ autSub A' U ↔ A ≤ A' := by
  constructor
  · intro hle g hg
    obtain ⟨a', ha', e⟩ := mem_autSub.mp (hle (mem_autSub.mpr ⟨⟨g, h.stab (hA hg)⟩, hg, rfl⟩))
    have : g = a' := h.eq_of_resHom_eq (hA hg) (hA' ha') (by
      rw [← e]) 
    rw [this]
    exact ha'
  · intro hle
    exact autSub_mono hle U


def extAutSub (U : Subgroup V) (B : Subgroup (MulAut U)) : Subgroup (MulAut V) :=
  (B.comap (resHom U)).map (stabSub U).subtype

omit [Finite V] in
theorem mem_extAutSub {U : Subgroup V} {B : Subgroup (MulAut U)} {g : MulAut V} :
    g ∈ extAutSub U B ↔ ∃ hg : g ∈ stabSub U, resHom U ⟨g, hg⟩ ∈ B := by
  unfold extAutSub
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite V] in
theorem autSub_lift {G : Subgroup (MulAut V)} {U : Subgroup V} {B : Subgroup (MulAut U)}
    (hB : B ≤ autSub G U) : autSub (G ⊓ extAutSub U B) U = B := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨hgs, hB'⟩ := mem_extAutSub.mp hg.2
    exact hB'
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp (hB hφ)
    exact mem_autSub.mpr ⟨g, ⟨hg, mem_extAutSub.mpr ⟨g.2, hφ⟩⟩, rfl⟩

omit [Finite V] in
theorem SuppData.lift_autSub (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    G ⊓ extAutSub U (autSub A U) = A := by
  apply le_antisymm
  · rintro g ⟨hgG, hg⟩
    obtain ⟨hgs, hB'⟩ := mem_extAutSub.mp hg
    obtain ⟨a, ha, e⟩ := mem_autSub.mp hB'
    exact (h.eq_of_resHom_eq (hA ha) hgG (by rw [e])) ▸ ha
  · intro a ha
    exact ⟨hA ha, mem_extAutSub.mpr ⟨h.stab (hA ha), mem_autSub.mpr ⟨⟨a, h.stab (hA ha)⟩, ha, rfl⟩⟩⟩


omit [Finite V] in
theorem SuppData.isElemAbelian2_autSub_iff (h : SuppData G U W) {A : Subgroup (MulAut V)}
    (hA : A ≤ G) : IsElemAbelian2 (autSub A U) ↔ IsElemAbelian2 A := by
  have hAs : A ≤ stabSub U := hA.trans h.stab
  constructor
  · rintro ⟨hc, hsq⟩
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · refine h.eq_of_resHom_eq (G.mul_mem (hA ha) (hA hb)) (G.mul_mem (hA hb) (hA ha)) ?_
      have e := hc _ (mem_autSub.mpr ⟨⟨a, hAs ha⟩, ha, rfl⟩) _
        (mem_autSub.mpr ⟨⟨b, hAs hb⟩, hb, rfl⟩)
      rw [← map_mul, ← map_mul] at e
      exact e
    · refine h.eq_of_resHom_eq (G.pow_mem (hA ha) 2) G.one_mem ?_
      have e := hsq _ (mem_autSub.mpr ⟨⟨a, hAs ha⟩, ha, rfl⟩)
      rw [← map_pow] at e
      have e' : resHom U (⟨a, hAs ha⟩ ^ 2) = resHom U 1 := by rw [e, map_one]
      exact e'
  · rintro ⟨hc, hsq⟩
    refine ⟨fun φ hφ ψ hψ => ?_, fun φ hφ => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      obtain ⟨k, hk, rfl⟩ := mem_autSub.mp hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ hg _ hk)
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hsq _ hg)
      rw [this, map_one]

omit [Finite V] in
theorem SuppData.autSub_eq_bot_iff' (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    autSub A U = ⊥ ↔ A = ⊥ := by
  constructor
  · intro hb
    have h1 : commSub U A = ⊥ := (autSub_eq_bot_iff (hA.trans h.stab)).mp hb
    have h2 : A ≤ G ⊓ centSub U := le_inf hA (fun g hg u hu => (commSub_eq_bot_iff.mp h1) hu g hg)
    rw [h.inf_centSub] at h2
    exact le_bot_iff.mp h2
  · rintro rfl
    unfold autSub
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  

omit [Finite V] in
theorem SuppData.isA2_autSub_iff (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    IsA2 (autSub G U) (autSub A U) ↔ IsA2 G A := by
  unfold IsA2
  rw [h.autSub_le_iff hA le_rfl, ne_eq, ne_eq, h.autSub_eq_bot_iff' hA,
    h.isElemAbelian2_autSub_iff hA]

omit [Finite V] in
theorem SuppData.exists_autSub_eq (_h : SuppData G U W) {B : Subgroup (MulAut U)}
    (hB : B ≤ autSub G U) : ∃ A, A ≤ G ∧ autSub A U = B :=
  ⟨G ⊓ extAutSub U B, inf_le_left, autSub_lift hB⟩

theorem SuppData.mem_kRle_iff (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G)
    {k : ℕ} (r : ℚ) (hk : 1 ≤ k) :
    autSub A U ∈ kRle (autSub G U) k r ↔ A ∈ kRle G k r := by
  unfold kRle Rle
  show (IsA2 (autSub G U) (autSub A U) ∧ rAV (autSub A U) ≤ r) ∧ commSeries (autSub A U) k = ⊥ ↔
    (IsA2 G A ∧ rAV A ≤ r) ∧ commSeries A k = ⊥
  rw [h.isA2_autSub_iff hA, h.rAV_autSub hA, h.commSeries_eq_bot_iff hA hk]

theorem SuppData.kqValues_eq (h : SuppData G U W) {k : ℕ} (hk : 1 ≤ k) :
    kqValues (autSub G U) k = kqValues G k := by
  ext s
  constructor
  · rintro ⟨B, hB, hBk, rfl⟩
    obtain ⟨A, hAG, rfl⟩ := h.exists_autSub_eq hB.1
    exact ⟨A, (h.isA2_autSub_iff hAG).mp hB, (h.commSeries_eq_bot_iff hAG hk).mp hBk,
      (h.rAV_autSub hAG).symm⟩
  · rintro ⟨A, hA, hAk, rfl⟩
    exact ⟨autSub A U, (h.isA2_autSub_iff hA.1).mpr hA,
      (h.commSeries_eq_bot_iff hA.1 hk).mpr hAk, h.rAV_autSub hA.1⟩

theorem SuppData.kq_eq (h : SuppData G U W) {k : ℕ} (hk : 1 ≤ k) :
    kq (autSub G U) k = kq G k := by
  unfold kq
  congr 1
  ext s
  simp only [Set.Finite.mem_toFinset, h.kqValues_eq hk]

theorem SuppData.qhatOf_eq (h : SuppData G U W) : qhatOf (autSub G U) = qhatOf G :=
  h.kq_eq (by norm_num)

theorem SuppData.mem_QhatStar_iff (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    autSub A U ∈ QhatStar (autSub G U) ↔ A ∈ QhatStar G := by
  constructor
  · rintro ⟨r, hq, hr2, hmem, hmin⟩
    refine ⟨r, h.qhatOf_eq ▸ hq, hr2, (h.mem_kRle_iff hA r (by norm_num)).mp hmem, ?_⟩
    intro A' hA' hle
    have hA'G : A' ≤ G := hA'.1.1.1
    have h1 : autSub A' U ∈ kRle (autSub G U) 3 r := (h.mem_kRle_iff hA'G r (by norm_num)).mpr hA'
    have h2 : autSub A' U = autSub A U := hmin _ h1 (autSub_mono hle U)
    exact le_antisymm hle ((h.autSub_le_iff hA hA'G).mp h2.symm.le)
  · rintro ⟨r, hq, hr2, hmem, hmin⟩
    refine ⟨r, h.qhatOf_eq ▸ hq, hr2, (h.mem_kRle_iff hA r (by norm_num)).mpr hmem, ?_⟩
    intro B hB hle
    obtain ⟨A', hA'G, rfl⟩ := h.exists_autSub_eq hB.1.1.1
    have h1 : A' ∈ kRle G 3 r := (h.mem_kRle_iff hA'G r (by norm_num)).mp hB
    have h2 : A' = A := hmin _ h1 ((h.autSub_le_iff hA'G hA).mp hle)
    rw [h2]

theorem SuppData.Jhat_autSub (h : SuppData G U W) : Jhat (autSub G U) = autSub (Jhat G) U := by
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    obtain ⟨r, -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
    obtain ⟨A, hAG, rfl⟩ := h.exists_autSub_eq hB2.1
    exact autSub_mono (le_Jhat ((h.mem_QhatStar_iff hAG).mp hB)) U
  · have hY : Jhat (autSub G U) ≤ autSub G U := Jhat_le _
    obtain ⟨A', hA'G, hA'⟩ := h.exists_autSub_eq hY
    have hJ : Jhat G ≤ A' := by
      refine iSup₂_le fun A hA => ?_
      have hAG : A ≤ G := by
        obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
        exact hA2.1
      have : autSub A U ≤ autSub A' U := by
        rw [hA']
        exact le_Jhat ((h.mem_QhatStar_iff hAG).mpr hA)
      exact (h.autSub_le_iff hAG hA'G).mp this
    rw [← hA']
    exact autSub_mono hJ U


omit [Finite V] in
theorem SuppData.autSub_iSup (h : SuppData G U W) {S : Set (Subgroup (MulAut V))}
    (hS : ∀ A ∈ S, A ≤ G) : autSub (⨆ A ∈ S, A) U = ⨆ A ∈ S, autSub A U := by
  apply le_antisymm
  · have hY : (⨆ A ∈ S, autSub A U) ≤ autSub G U :=
      iSup₂_le fun A hA => autSub_mono (hS A hA) U
    obtain ⟨A', hA'G, hA'⟩ := h.exists_autSub_eq hY
    have hle : (⨆ A ∈ S, A) ≤ A' := by
      refine iSup₂_le fun A hA => ?_
      have : autSub A U ≤ autSub A' U := by
        rw [hA']
        exact le_iSup₂ (f := fun A (_ : A ∈ S) => autSub A U) A hA
      exact (h.autSub_le_iff (hS A hA) hA'G).mp this
    rw [← hA']
    exact autSub_mono hle U
  · exact iSup₂_le fun A hA => autSub_mono (le_iSup₂ (f := fun A (_ : A ∈ S) => A) A hA) U

omit [Finite V] in
theorem commSub_eq_map_commV {A : Subgroup (MulAut V)} (hA : A ≤ stabSub U) :
    commSub U A = (commV (autSub A U)).map U.subtype := by
  rw [commV_eq_commSub, ← commSub_map_subtype hA, ← MonoidHom.range_eq_map, Subgroup.range_subtype]


theorem SuppData.isIndecomposablePair_autSub (h : SuppData G U W) (hG : IsIndecomposablePair G) :
    IsIndecomposablePair (autSub G U) := by
  refine ⟨?_, ?_⟩
  · rw [h.Jhat_autSub, ← hG.1]
  · rintro ⟨H₁, H₂, U₁, U₂, hH₁, hH₂, Q₁, Q₂, hQ, hdisj, hHH₁, hHH₂, hdir, hc₁, hc₂, hz₁, hz₂⟩
    apply hG.2
    have hQ₁sub : Q₁ ⊆ QhatStar (autSub G U) := fun A hA => by rw [hQ]; exact Or.inl hA
    have hQ₂sub : Q₂ ⊆ QhatStar (autSub G U) := fun A hA => by rw [hQ]; exact Or.inr hA
    have hH₁le : H₁ ≤ autSub G U := by
      rw [hHH₁]
      exact iSup₂_le fun B hB => le_of_mem_QhatStar216 (hQ₁sub hB)
    have hH₂le : H₂ ≤ autSub G U := by
      rw [hHH₂]
      exact iSup₂_le fun B hB => le_of_mem_QhatStar216 (hQ₂sub hB)
    set G₁ : Subgroup (MulAut V) := G ⊓ extAutSub U H₁ with hG₁
    set G₂ : Subgroup (MulAut V) := G ⊓ extAutSub U H₂ with hG₂
    have hG₁G : G₁ ≤ G := inf_le_left
    have hG₂G : G₂ ≤ G := inf_le_left
    have haut₁ : autSub G₁ U = H₁ := autSub_lift hH₁le
    have haut₂ : autSub G₂ U = H₂ := autSub_lift hH₂le
    have hG₁ne : G₁ ≠ ⊥ := by
      intro hb
      apply hH₁
      rw [← haut₁, hb]
      unfold autSub
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    have hG₂ne : G₂ ≠ ⊥ := by
      intro hb
      apply hH₂
      rw [← haut₂, hb]
      unfold autSub
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    let Q₁' : Set (Subgroup (MulAut V)) := {A | A ∈ QhatStar G ∧ autSub A U ∈ Q₁}
    let Q₂' : Set (Subgroup (MulAut V)) := {A | A ∈ QhatStar G ∧ autSub A U ∈ Q₂}
    have hQ' : QhatStar G = Q₁' ∪ Q₂' := by
      ext A
      constructor
      · intro hA
        have : autSub A U ∈ Q₁ ∪ Q₂ := by
          rw [← hQ]
          exact (h.mem_QhatStar_iff (le_of_mem_QhatStar216 hA)).mpr hA
        rcases this with h1 | h2
        · exact Or.inl ⟨hA, h1⟩
        · exact Or.inr ⟨hA, h2⟩
      · rintro (⟨hA, -⟩ | ⟨hA, -⟩) <;> exact hA
    have hdisj' : Disjoint Q₁' Q₂' := by
      rw [Set.disjoint_left]
      rintro A ⟨-, h1⟩ ⟨-, h2⟩
      exact Set.disjoint_left.mp hdisj h1 h2
    have hgen : ∀ (Q : Set (Subgroup (MulAut U))) (H : Subgroup (MulAut U)),
        H = ⨆ B ∈ Q, B → Q ⊆ QhatStar (autSub G U) →
        G ⊓ extAutSub U H = ⨆ A ∈ {A | A ∈ QhatStar G ∧ autSub A U ∈ Q}, A := by
      intro Q H hH hQs
      have hS : ∀ A ∈ {A | A ∈ QhatStar G ∧ autSub A U ∈ Q}, A ≤ G :=
        fun A hA => le_of_mem_QhatStar216 hA.1
      have himg : ⨆ A ∈ {A | A ∈ QhatStar G ∧ autSub A U ∈ Q}, autSub A U = H := by
        rw [hH]
        apply le_antisymm
        · exact iSup₂_le fun A hA => le_iSup₂ (f := fun B (_ : B ∈ Q) => B) _ hA.2
        · refine iSup₂_le fun B hB => ?_
          obtain ⟨A, hAG, rfl⟩ := h.exists_autSub_eq (le_of_mem_QhatStar216 (hQs hB))
          exact le_iSup₂ (f := fun A (_ : A ∈ {A | A ∈ QhatStar G ∧ autSub A U ∈ Q}) => autSub A U)
            A ⟨(h.mem_QhatStar_iff hAG).mp (hQs hB), hB⟩
      have hle : (⨆ A ∈ {A | A ∈ QhatStar G ∧ autSub A U ∈ Q}, A) ≤ G := iSup₂_le hS
      rw [← himg, ← h.autSub_iSup hS, h.lift_autSub hle]
    have hG₁gen : G₁ = ⨆ A ∈ Q₁', A := hgen Q₁ H₁ hHH₁ hQ₁sub
    have hG₂gen : G₂ = ⨆ A ∈ Q₂', A := hgen Q₂ H₂ hHH₂ hQ₂sub
    set V₁ : Subgroup V := U₁.map U.subtype with hV₁
    set V₂ : Subgroup V := U₂.map U.subtype ⊔ W with hV₂
    have hUV : U₁.map U.subtype ⊔ U₂.map U.subtype = U := by
      rw [← Subgroup.map_sup, hdir.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hW1 : ∀ {A : Subgroup (MulAut V)}, A ≤ G → commSub W A = ⊥ := fun hA =>
      commSub_eq_bot_iff.mpr (fun w hw a ha => h.triv (hA ha) w hw)
    have hcomm₁ : commSub U G₁ = (commV H₁).map U.subtype := by
      rw [commSub_eq_map_commV (hG₁G.trans h.stab), haut₁]
    have hcomm₂ : commSub U G₂ = (commV H₂).map U.subtype := by
      rw [commSub_eq_map_commV (hG₂G.trans h.stab), haut₂]
    refine ⟨G₁, G₂, V₁, V₂, hG₁ne, hG₂ne, Q₁', Q₂', hQ', hdisj', hG₁gen, hG₂gen, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [hV₂, ← sup_assoc, hUV, h.sup]
      · refine le_bot_iff.mp ?_
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hx2
        have hxU : x ∈ U := by
          obtain ⟨u, -, rfl⟩ := hx1
          exact u.2
        have hyU : y ∈ U := by
          obtain ⟨u, -, rfl⟩ := hy
          exact u.2
        have hz' : z ∈ U ⊓ W := ⟨by
          have : z = y⁻¹ * x := by rw [← hyz]; group
          rw [this]
          exact U.mul_mem (U.inv_mem hyU) hxU, hz⟩
        rw [h.inf] at hz'
        have hz1 : z = 1 := hz'
        have hxy : x = y := by rw [← hyz, hz1, mul_one]
        have : x ∈ U₁.map U.subtype ⊓ U₂.map U.subtype := ⟨hx1, hxy ▸ hy⟩
        have hmap : U₁.map U.subtype ⊓ U₂.map U.subtype = ⊥ := by
          rw [← Subgroup.map_inf _ _ _ U.subtype_injective, hdir.2, Subgroup.map_bot]
        rw [hmap] at this
        exact this
    · rw [commV_eq_commSub, h.commSub_top (hG₁G)]
      rw [hcomm₁]
      exact Subgroup.map_mono hc₁
    · rw [commV_eq_commSub, h.commSub_top (hG₂G), hcomm₂]
      exact (Subgroup.map_mono hc₂).trans le_sup_left
    · rw [hV₂, commSub_sup_left, hW1 hG₁G, sup_bot_eq,
        commSub_map_subtype (hG₁G.trans h.stab) U₂, haut₁, hz₁, Subgroup.map_bot]
    · rw [hV₁, commSub_map_subtype (hG₂G.trans h.stab) U₁, haut₂, hz₂, Subgroup.map_bot]

end Restrict
end CFSG.Quasithin
