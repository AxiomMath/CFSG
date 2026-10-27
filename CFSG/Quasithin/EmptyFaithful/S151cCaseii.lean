module

public import CFSG.Quasithin.EmptyFaithful.S151cTwoBl
public import CFSG.Quasithin.EmptyFaithful.S151cY36

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.QuasithinUnique (IsSylowTwoOf)

section Caseii151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

theorem gen_summand (h : Setting151c X Tb Xc) {W W' : Subgroup V}
    (hW : ∀ x ∈ X, ∀ u ∈ W, x u ∈ W) (hW' : ∀ x ∈ X, ∀ u ∈ W', x u ∈ W')
    (hinf : W ⊓ W' = ⊥) (hsup : W ⊔ W' = ⊤) :
    W ≤ Subgroup.closure {x | ∃ g ∈ X, ∃ z ∈ fixV Tb ⊓ W, g z = x} := by
  set Q₁ := Subgroup.closure {x | ∃ g ∈ X, ∃ z ∈ fixV Tb ⊓ W, g z = x} with hQ₁
  set Q₂ := Subgroup.closure {x | ∃ g ∈ X, ∃ z ∈ fixV Tb ⊓ W', g z = x} with hQ₂
  have hQ₁W : Q₁ ≤ W := by
    refine (Subgroup.closure_le W).mpr ?_
    rintro _ ⟨g, hg, z, hz, rfl⟩
    exact hW g hg z hz.2
  have hQ₂W' : Q₂ ≤ W' := by
    refine (Subgroup.closure_le W').mpr ?_
    rintro _ ⟨g, hg, z, hz, rfl⟩
    exact hW' g hg z hz.2
  have htop : Q₁ ⊔ Q₂ = ⊤ := by
    refine h.gen (Q₁ ⊔ Q₂) ?_
    intro g hg z hz
    have hz' : z ∈ W ⊔ W' := by rw [hsup]; exact Subgroup.mem_top z
    obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.mp hz'
    have hwfix : w ∈ fixV Tb ∧ w' ∈ fixV Tb := by
      have key : ∀ t ∈ Tb, t w = w ∧ t w' = w' := by
        intro t ht
        have hmul : t w * t w' = w * w' := by rw [← map_mul]; exact hz t ht
        have hdiv : t w / w = w' / t w' := by
          rw [div_eq_div_iff_mul_eq_mul]
          calc t w * t w' = w * w' := hmul
            _ = w' * w := mul_comm _ _
        have hA : t w / w ∈ W := by
          rw [div_eq_mul_inv]
          exact W.mul_mem (hW t (h.syl.1 ht) w hw) (W.inv_mem hw)
        have hB : t w / w ∈ W' := by
          rw [hdiv, div_eq_mul_inv]
          exact W'.mul_mem hw' (W'.inv_mem (hW' t (h.syl.1 ht) w' hw'))
        have h0 : t w / w ∈ W ⊓ W' := ⟨hA, hB⟩
        rw [hinf, Subgroup.mem_bot] at h0
        have h1 : t w = w := div_eq_one.mp h0
        refine ⟨h1, ?_⟩
        have hmul' := hmul
        rw [h1] at hmul'
        exact mul_left_cancel hmul'
      exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩
    have hgw : g w ∈ Q₁ := Subgroup.subset_closure ⟨g, hg, w, ⟨hwfix.1, hw⟩, rfl⟩
    have hgw' : g w' ∈ Q₂ := Subgroup.subset_closure ⟨g, hg, w', ⟨hwfix.2, hw'⟩, rfl⟩
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgw) (Subgroup.mem_sup_right hgw')
  intro x hx
  have hx' : x ∈ Q₁ ⊔ Q₂ := by rw [htop]; exact Subgroup.mem_top x
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := Subgroup.mem_sup.mp hx'
  have hq₂W : q₂ ∈ W := by
    have h1 : q₁⁻¹ * (q₁ * q₂) ∈ W := W.mul_mem (W.inv_mem (hQ₁W hq₁)) hx
    have e : q₁⁻¹ * (q₁ * q₂) = q₂ := by group
    rwa [e] at h1
  have hq₂0 : q₂ ∈ W ⊓ W' := ⟨hq₂W, hQ₂W' hq₂⟩
  rw [hinf, Subgroup.mem_bot] at hq₂0
  rw [hq₂0, mul_one]
  exact hq₁

omit [Finite V] in
theorem genTop_of_le_closure {Xr H : Subgroup (MulAut V)} {U : Subgroup V} (hXr : Xr ≤ stabSub U)
    (hle : U ≤ Subgroup.closure {x | ∃ g ∈ Xr, ∃ z ∈ fixV H ⊓ U, g z = x}) :
    GenTop (autSub Xr U) (autSub H U) := by
  unfold GenTop
  rw [eq_top_iff]
  intro u _
  set S' : Set ↥U := {x | ∃ ψ ∈ autSub Xr U, ∃ z ∈ fixV (autSub H U), ψ z = x} with hS'
  have hsub : {x : V | ∃ g ∈ Xr, ∃ z ∈ fixV H ⊓ U, g z = x} ⊆ U.subtype '' S' := by
    rintro _ ⟨g, hg, z, hz, rfl⟩
    have hgz : g z ∈ U := ((hXr hg) z).mpr hz.2
    refine ⟨⟨g z, hgz⟩, ⟨resHom U ⟨g, hXr hg⟩, mem_autSub.mpr ⟨⟨g, hXr hg⟩, hg, rfl⟩,
      ⟨z, hz.2⟩, ?_, rfl⟩, rfl⟩
    rw [mem_fixV_autSub]
    intro t ht _
    exact hz.1 t ht
  have h1 : (u : V) ∈ Subgroup.closure (U.subtype '' S') :=
    (Subgroup.closure_mono hsub) (hle u.2)
  rw [← MonoidHom.map_closure] at h1
  obtain ⟨y, hy, hyu⟩ := h1
  have hyu' : y = u := Subtype.ext hyu
  rw [← hyu']
  exact hy

theorem coe_sup_sup_eq_mul {G : Type*} [Group G] {A B T : Subgroup G}
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hTA : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hTB : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) :
    ((A ⊔ B ⊔ T : Subgroup G) : Set G) = (A : Set G) * (B : Set G) * (T : Set G) := by
  have hmem : ∀ {x : G}, x ∈ (A : Set G) * (B : Set G) * (T : Set G) ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ t ∈ T, a * b * t = x := by
    intro x
    simp only [Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, t, ht, rfl⟩
      exact ⟨a, ha, b, hb, t, ht, rfl⟩
    · rintro ⟨a, ha, b, hb, t, ht, rfl⟩
      exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, t, ht, rfl⟩
  let S : Subgroup G :=
    { carrier := (A : Set G) * (B : Set G) * (T : Set G)
      one_mem' := hmem.mpr ⟨1, A.one_mem, 1, B.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        intro x y hx hy
        obtain ⟨a, ha, b, hb, t, ht, rfl⟩ := hmem.mp hx
        obtain ⟨a', ha', b', hb', t', ht', rfl⟩ := hmem.mp hy
        have h1 : t * a' * t⁻¹ ∈ A := hTA t ht a' ha'
        have h2 : t * b' * t⁻¹ ∈ B := hTB t ht b' hb'
        have h3 : b * (t * a' * t⁻¹) * b⁻¹ ∈ A := hBA b hb _ h1
        refine hmem.mpr ⟨a * (b * (t * a' * t⁻¹) * b⁻¹), A.mul_mem ha h3, b * (t * b' * t⁻¹),
          B.mul_mem hb h2, t * t', T.mul_mem ht ht', ?_⟩
        group
      inv_mem' := by
        intro x hx
        obtain ⟨a, ha, b, hb, t, ht, rfl⟩ := hmem.mp hx
        have h1 : t⁻¹ * a⁻¹ * t⁻¹⁻¹ ∈ A := hTA t⁻¹ (T.inv_mem ht) a⁻¹ (A.inv_mem ha)
        have h2 : t⁻¹ * b⁻¹ * t⁻¹⁻¹ ∈ B := hTB t⁻¹ (T.inv_mem ht) b⁻¹ (B.inv_mem hb)
        have h3 : (t⁻¹ * b⁻¹ * t⁻¹⁻¹) * (t⁻¹ * a⁻¹ * t⁻¹⁻¹) * (t⁻¹ * b⁻¹ * t⁻¹⁻¹)⁻¹ ∈ A :=
          hBA _ h2 _ h1
        refine hmem.mpr ⟨(t⁻¹ * b⁻¹ * t⁻¹⁻¹) * (t⁻¹ * a⁻¹ * t⁻¹⁻¹) * (t⁻¹ * b⁻¹ * t⁻¹⁻¹)⁻¹, h3,
          t⁻¹ * b⁻¹ * t⁻¹⁻¹, h2, t⁻¹, T.inv_mem ht, ?_⟩
        group }
  have hA : A ≤ S := fun a ha => hmem.mpr ⟨a, ha, 1, B.one_mem, 1, T.one_mem, by simp⟩
  have hB : B ≤ S := fun b hb => hmem.mpr ⟨1, A.one_mem, b, hb, 1, T.one_mem, by simp⟩
  have hT : T ≤ S := fun t ht => hmem.mpr ⟨1, A.one_mem, 1, B.one_mem, t, ht, by simp⟩
  have hle1 : A ⊔ B ⊔ T ≤ S := sup_le (sup_le hA hB) hT
  have hle2 : S ≤ A ⊔ B ⊔ T := by
    intro x hx
    obtain ⟨a, ha, b, hb, t, ht, rfl⟩ := hmem.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right ht)
  have hS : A ⊔ B ⊔ T = S := le_antisymm hle1 hle2
  rw [hS]
  rfl

open Classical in
theorem block_le_Xc (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hn1 : ¬ ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥) {L : Subgroup (MulAut V)}
    (hL : L ∈ I) : L ≤ Xc := by
  obtain ⟨K, hK, hLK⟩ := exists_comp h hr hr2 hI hL
  have hKne : K ≠ ⊥ := fun e => hI.ne_bot L hL (le_bot_iff.mp (e ▸ hLK))
  rcases dich h hI hK hKne with ⟨hJ, hf⟩ | ⟨-, hKc, -⟩
  · exact absurd ⟨K, hK, hJ, hf⟩ hn1
  · exact hLK.trans hKc

open Classical in
theorem exists_unique_block (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I)
    (hn1 : ¬ ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥) :
    ∃ L ∈ I, ∀ L' ∈ I, L' = L := by
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  obtain ⟨L, hL, -⟩ := hI.cover A ((QhatStar_Jhat hr hr2).symm ▸ hA)
  refine ⟨L, hL, fun L' hL' => ?_⟩
  by_contra hne
  exact two_blocks_false h hr hr2 hI (fun L hL => block_S3Block h hr hr2 hI hn1 hL)
    (fun L hL => block_le_Xc h hr hr2 hI hn1 hL) hL' hL hne

open Classical in
theorem caseii_Y (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) (hLn : NormalIn X L)
    (hnot : ¬ commV L ≤ Subgroup.closure {x | ∃ g ∈ L, ∃ z ∈ fixV Tb ⊓ commV L, g z = x})
    (hCinf : commV L ⊓ fixV L = ⊥) (hCsup : commV L ⊔ fixV L = ⊤) :
    autSub X (commV L) = autSub L (commV L) ⊔
        Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L))) ∧
      Nat.card (autSub Tb (commV L)) = 4 ∧ IsOmegaFourPlus (autSub X (commV L)) := by
  have hs := suppData_block h hI hL
  have hLX : L ≤ X := (block_le_J hI hL).trans (Jhat_le X)
  have hUinv : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu =>
    hLn.commV_invariant hx hu
  have hCinv : ∀ x ∈ X, ∀ u ∈ fixV L, x u ∈ fixV L := fun x hx u hu =>
    hLn.fixV_invariant hx hu
  have hXs : X ≤ stabSub (commV L) := le_stabSub_of_invariant hUinv
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hcard : Nat.card ↥(commV L) = 16 := hS.card_commV h.sq
  obtain ⟨⟨e⟩, -⟩ := (S3Block_iff hs).mp hS
  have hfix := block_hfix h hr hr2 hI hL e
  have hsylL : IsSylowTwoOf (Tb ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.syl : IsSylowTwoOf Tb X) hLX hLn.le_normalizer
  have hLcard : Nat.card L = 6 := by
    obtain ⟨⟨e'⟩, -⟩ := hS
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t₀ ∈ Tb ⊓ L, t₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : Tb ⊓ L = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    apply hsylL.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot, hLcard]
    norm_num
  have hts : t₀ ∈ stabSub (commV L) := hXs (h.syl.1 ht₀.1)
  set t : MulAut ↥(commV L) := resHom (commV L) ⟨t₀, hts⟩ with ht
  have htH : t ∈ autSub Tb (commV L) := mem_autSub.mpr ⟨⟨t₀, hts⟩, ht₀.1, rfl⟩
  have htL : t ∈ autSub L (commV L) := mem_autSub.mpr ⟨⟨t₀, hts⟩, ht₀.2, rfl⟩
  have ht1 : t ≠ 1 := by
    intro e1
    have : t₀ ∈ L ⊓ centSub (commV L) := ⟨ht₀.2, by
      have := ker_resHom (commV L)
      have hk : (⟨t₀, hts⟩ : ↥(stabSub (commV L))) ∈ (resHom (commV L)).ker := e1
      rw [this, Subgroup.mem_subgroupOf] at hk
      exact hk⟩
    rw [hs.inf_centSub, Subgroup.mem_bot] at this
    exact ht₀1 this
  have hnot' : ¬ GenTop (autSub L (commV L)) (autSub Tb (commV L)) :=
    not_genTop_of_not_le_closure h hUinv hnot
  have hgen : GenTop (autSub X (commV L)) (autSub Tb (commV L)) :=
    genTop_of_le_closure hXs (gen_summand h hUinv hCinv hCinf hCsup)
  exact Y_eq_of_not_genTop hUsq hcard e hfix (autSub_mono hLX _)
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := mem_autSub.mp hy
      exact resHom_mem_normalizer_autSub hXs hLX hLn hx)
    (autSub_mono h.syl.1 _) (isPGroup_autSub h.syl.2.1) ⟨t, ⟨htH, htL⟩, ht1⟩ hnot' hgen

open Classical in
theorem caseii_Xc (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) (hS : S3Block L) (hLn : NormalIn X L)
    (hfixne : fixV L ≠ ⊥)
    (hY : autSub X (commV L) = autSub L (commV L) ⊔
        Subgroup.centralizer (autSub L (commV L) : Set (MulAut ↥(commV L))))
    (hH4 : Nat.card (autSub Tb (commV L)) = 4) :
    (Xc : Set (MulAut V)) = ((X ⊓ centSub (commV L) : Subgroup (MulAut V)) : Set (MulAut V)) *
        ((X ⊓ centSub (fixV L) : Subgroup (MulAut V)) : Set (MulAut V)) * (Tb : Set (MulAut V)) ∧
      Xc.relIndex X = 3 := by
  have hs := suppData_block h hI hL
  have hLX : L ≤ X := (block_le_J hI hL).trans (Jhat_le X)
  have hUinv : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu =>
    hLn.commV_invariant hx hu
  have hCinv : ∀ x ∈ X, ∀ u ∈ fixV L, x u ∈ fixV L := fun x hx u hu =>
    hLn.fixV_invariant hx hu
  have hXs : X ≤ stabSub (commV L) := le_stabSub_of_invariant hUinv
  obtain ⟨⟨e⟩, -⟩ := (S3Block_iff hs).mp hS
  have hLU : Nat.card (autSub L (commV L)) = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcentn : ∀ {W : Subgroup V}, (∀ x ∈ X, ∀ u ∈ W, x u ∈ W) → ∀ x ∈ X,
      ∀ a ∈ X ⊓ centSub W, x * a * x⁻¹ ∈ X ⊓ centSub W := by
    intro W hW x hx a ha
    refine ⟨X.mul_mem (X.mul_mem hx ha.1) (X.inv_mem hx), fun u hu => ?_⟩
    have h1 : x⁻¹ u ∈ W := hW x⁻¹ (X.inv_mem hx) u hu
    show x (a (x⁻¹ u)) = u
    rw [ha.2 _ h1]
    simp
  have hcentXc : ∀ {W : Subgroup V}, (∀ x ∈ X, ∀ u ∈ W, x u ∈ W) → W ≠ ⊥ → X ⊓ centSub W ≤ Xc := by
    intro W hW hW0 a ha
    have hpos := rk_inf_fixV_pos_of_isPGroup_two h.sq h.syl.2.1
      (fun g hg u hu => hW g (h.syl.1 hg) u hu) hW0
    have hne : (W ⊓ fixV Tb : Subgroup V) ≠ ⊥ := (rk_pos_iff_ne_bot' h.sq).mp hpos
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hz1' : z ≠ 1 := fun e1 => hz1 (Subtype.ext e1)
    have hZ1 : Subgroup.zpowers z ≤ fixV Tb := Subgroup.zpowers_le.mpr hz.2
    have hZ1ne : Subgroup.zpowers z ≠ ⊥ := fun e1 => hz1' (Subgroup.zpowers_eq_bot.mp e1)
    refine h.hU _ hZ1 hZ1ne ⟨ha.1, ?_⟩
    intro u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, ha.2 z hz.1]
  have hUne : commV L ≠ ⊥ := fun e1 => hI.ne_bot L hL (eq_bot_of_commV_eq_bot e1)
  set A : Subgroup (MulAut V) := X ⊓ centSub (commV L) with hA
  set B : Subgroup (MulAut V) := X ⊓ centSub (fixV L) with hB
  have hAXc : A ≤ Xc := hcentXc hUinv hUne
  have hBXc : B ≤ Xc := hcentXc hCinv hfixne
  set S : Subgroup (MulAut V) := A ⊔ B ⊔ Tb with hSdef
  have hSXc : S ≤ Xc := sup_le (sup_le hAXc hBXc) h.tb_le
  have hSX : S ≤ X := hSXc.trans h.xc_le
  have hSset := coe_sup_sup_eq_mul (A := A) (B := B) (T := Tb)
    (fun b hb a ha => hcentn hUinv b hb.1 a ha)
    (fun t ht a ha => hcentn hUinv t (h.syl.1 ht) a ha)
    (fun t ht b hb => hcentn hCinv t (h.syl.1 ht) b hb)
  have hLB : L ≤ B := fun l hl => ⟨hLX hl, fun c hc => hc l hl⟩
  have hLS : L ≤ S := (hLB.trans (le_sup_right.trans le_sup_left))
  have hTS : Tb ≤ S := le_sup_right
  have hAS : A ≤ S := le_sup_left.trans le_sup_left
  have hXc1 := card_autSub_mul hXs
  have hSs : S ≤ stabSub (commV L) := hSX.trans hXs
  have hSc := card_autSub_mul hSs
  have hSinf : S ⊓ centSub (commV L) = A :=
    le_antisymm (inf_le_inf_right _ hSX) (le_inf hAS inf_le_right)
  have hYcard : Nat.card (autSub X (commV L)) = 36 := by
    rw [hY, card_sup_of_normalizes
      (Subgroup.centralizer_le_normalizer (s := (autSub L (commV L) : Set (MulAut ↥(commV L)))))
      (inf_centralizer_eq_bot_D3 e), hLU, block_card_centralizer h hr hr2 hI hL hS]
  have hSdvd : Nat.card (autSub S (commV L)) ∣ 36 :=
    hYcard ▸ Subgroup.card_dvd_of_le (autSub_mono hSX _)
  have h6 : 6 ∣ Nat.card (autSub S (commV L)) :=
    hLU ▸ Subgroup.card_dvd_of_le (autSub_mono hLS _)
  have h4 : 4 ∣ Nat.card (autSub S (commV L)) :=
    hH4 ▸ Subgroup.card_dvd_of_le (autSub_mono hTS _)
  have h12 : 12 ∣ Nat.card (autSub S (commV L)) := by
    have h126 : Nat.lcm 6 4 ∣ Nat.card (autSub S (commV L)) := Nat.lcm_dvd h6 h4
    have hl : Nat.lcm 6 4 = 12 := by norm_num
    rwa [hl] at h126
  have hrel : S.relIndex X * Nat.card S = Nat.card X := by
    have := Subgroup.relIndex_mul_card S X
    rwa [inf_eq_left.mpr hSX] at this
  have hApos : 0 < Nat.card A := Nat.card_pos
  have h36 : S.relIndex X * Nat.card (autSub S (commV L)) = 36 := by
    have e1 : Nat.card X = 36 * Nat.card A := by rw [← hXc1, hYcard]
    have e2 : Nat.card S = Nat.card (autSub S (commV L)) * Nat.card A := by rw [← hSc, hSinf]
    rw [e1, e2] at hrel
    have h3 : (S.relIndex X * Nat.card (autSub S (commV L))) * Nat.card A =
        36 * Nat.card A := by rw [← hrel]; ring
    exact Nat.eq_of_mul_eq_mul_right hApos h3
  have hSne : S.relIndex X ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact h.xc_ne (h1.trans hSXc)
  have hrel3 : S.relIndex X = 3 := by
    obtain ⟨m, hm⟩ := h12
    have h' : S.relIndex X * (12 * m) = 36 := by rw [← hm]; exact h36
    have h3 : S.relIndex X * m = 3 := by
      have h'' : 12 * (S.relIndex X * m) = 36 := by rw [← h']; ring
      omega
    have hd : S.relIndex X ∣ 3 := ⟨m, h3.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd h1 hSne
    · exact h1
  have hXcrel : Xc.relIndex X = 3 ∧ Xc ≤ S := by
    have hmul := Subgroup.relIndex_mul_relIndex S Xc X hSXc h.xc_le
    rw [hrel3] at hmul
    have hd : Xc.relIndex X ∣ 3 := ⟨S.relIndex Xc, by rw [← hmul]; ring⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h1
      exact h.xc_ne h1
    · refine ⟨h1, ?_⟩
      rw [h1] at hmul
      have h2 : S.relIndex Xc = 1 := by omega
      rwa [Subgroup.relIndex_eq_one] at h2
  have hXcS : Xc = S := le_antisymm hXcrel.2 hSXc
  refine ⟨?_, hXcrel.1⟩
  rw [hXcS]
  exact hSset

structure Case6Aut (X Tb Xc J : Subgroup (MulAut V)) : Prop where
  dihedral : Nonempty (↥J ≃* DihedralGroup 3)
  card_U : Nat.card (commV J) = 16
  fix_ne : fixV J ≠ ⊥
  inf_eq : commV J ⊓ fixV J = ⊥
  sup_eq : commV J ⊔ fixV J = ⊤
  omega : IsOmegaFourPlus (autSub X (commV J))
  xc_eq : (Xc : Set (MulAut V)) = ((X ⊓ centSub (commV J) : Subgroup (MulAut V)) : Set (MulAut V)) *
    ((X ⊓ centSub (fixV J) : Subgroup (MulAut V)) : Set (MulAut V)) * (Tb : Set (MulAut V))
  index : Xc.relIndex X = 3

open Classical in
theorem caseii_main (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hn1 : ¬ ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥) :
    Case6Aut X Tb Xc (Jhat X) := by
  obtain ⟨L, hL, hLu⟩ := exists_unique_block h hr hr2 hI hn1
  have hS : S3Block L := block_S3Block h hr hr2 hI hn1 hL
  have hJL : Jhat X = L := by
    apply le_antisymm
    · rw [hI.sup_eq]
      exact iSup₂_le fun L' hL' => (hLu L' hL').le
    · exact block_le_J hI hL
  have hLnorm : ∀ x ∈ X, conjBy x L = L := fun x hx =>
    hLu _ (block_conj_mem h hr hr2 hI hL hx)
  have hLn : NormalIn X L := fun x hx k hk => by
    have := mem_conjBy_of_mem (g := x) hk
    rwa [hLnorm x hx] at this
  have hK : IsComp X I L := Or.inl ⟨L, hL, hLnorm, rfl⟩
  obtain ⟨hfixne, hLXc, hnot'⟩ : fixV L ≠ ⊥ ∧ L ≤ Xc ∧
      ¬ commV L ≤ Subgroup.closure {x | ∃ g ∈ L, ∃ z ∈ fixV Tb ⊓ commV L, g z = x} := by
    rcases dich h hI hK (hI.ne_bot L hL) with ⟨hJ, hf⟩ | H
    · exact absurd ⟨L, hK, hJ, hf⟩ hn1
    · exact H
  have hcop := commV_fitting_sup_fixV h.sq h.o2
  have hFJ : fittingOf (Jhat X) ≤ Jhat X := fittingOf_le _
  have hcomm_eq : commV (Jhat X) = commV (fittingOf (Jhat X)) :=
    le_antisymm (commV_Jhat_le_v0 h) (commV_mono216 hFJ)
  have hfix_eq : fixV (Jhat X) = fixV (fittingOf (Jhat X)) :=
    le_antisymm (fun c hc f hf => hc f (hFJ hf)) (fun c hc j hj => h.central c hc j hj)
  have hCinf : commV L ⊓ fixV L = ⊥ := by rw [← hJL, hcomm_eq, hfix_eq]; exact hcop.2
  have hCsup : commV L ⊔ fixV L = ⊤ := by rw [← hJL, hcomm_eq, hfix_eq]; exact hcop.1
  obtain ⟨hY, hH4, hom⟩ := caseii_Y h hr hr2 hI hL hS hLn hnot' hCinf hCsup
  obtain ⟨hxc, hidx⟩ := caseii_Xc h hr hr2 hI hL hS hLn hfixne hY hH4
  rw [hJL]
  exact ⟨hS.1, hS.card_commV h.sq, hfixne, hCinf, hCsup, hom, hxc, hidx⟩

end Caseii151c

end CFSG.Quasithin
