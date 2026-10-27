module

public import CFSG.Quasithin.EmptyFaithful.S151cS3
public import CFSG.Quasithin.EmptyFaithful.S151cShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Two151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

@[expose] def stabConj (X L : Subgroup (MulAut V)) : Subgroup (MulAut V) where
  carrier := {x | x ∈ X ∧ conjBy x L = L}
  one_mem' := ⟨X.one_mem, conjBy_one L⟩
  mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, by rw [← conjBy_conjBy, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by
    have h := congrArg (conjBy a⁻¹) ha.2
    rw [conjBy_conjBy, inv_mul_cancel, conjBy_one] at h
    exact h.symm⟩

omit [Finite V] in
theorem mem_stabConj {X L : Subgroup (MulAut V)} {x : MulAut V} :
    x ∈ stabConj X L ↔ x ∈ X ∧ conjBy x L = L := Iff.rfl

omit [Finite V] in
theorem conjBy_inv_eq_of_eq {L L' : Subgroup (MulAut V)} {x : MulAut V}
    (h : conjBy x L = L') : conjBy x⁻¹ L' = L := by
  rw [← h, conjBy_conjBy, inv_mul_cancel, conjBy_one]

omit [Finite V] in
theorem conjBy_eq_self_of_mem {L : Subgroup (MulAut V)} {l : MulAut V} (hl : l ∈ L) :
    conjBy l L = L := by
  ext y
  rw [mem_conjBy_iff]
  constructor
  · intro h
    have h1 := L.mul_mem (L.mul_mem hl h) (L.inv_mem hl)
    have e : l * (l⁻¹ * y * l) * l⁻¹ = y := by group
    rwa [e] at h1
  · intro h
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) h) hl

omit [Finite V] in
theorem conjBy_eq_self_of_commute {L : Subgroup (MulAut V)} {x : MulAut V}
    (hx : ∀ l ∈ L, x * l = l * x) : conjBy x L = L := by
  ext y
  rw [mem_conjBy_iff]
  constructor
  · intro h
    have h1 := hx _ h
    have e : y = x⁻¹ * y * x := by
      calc y = (y * x) * x⁻¹ := by group
        _ = (x * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = ((x⁻¹ * y * x) * x) * x⁻¹ := by rw [h1]
        _ = x⁻¹ * y * x := by group
    rw [e]
    exact h
  · intro h
    have h1 := hx y h
    have e : x⁻¹ * y * x = y := by
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [h1]
        _ = y := by group
    rw [e]
    exact h

omit [Finite V] in
theorem mem_stabSub_commV_of_conjBy {L : Subgroup (MulAut V)} {x : MulAut V}
    (hx : conjBy x L = L) : x ∈ stabSub (commV L) := by
  intro u
  have hmap : (commV L).map x.toMonoidHom = commV L := by rw [← commV_conjBy, hx]
  constructor
  · intro hu
    rw [← hmap] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    have : v = u := x.injective hvu
    rw [this] at hv
    exact hv
  · intro hu
    rw [← hmap]
    exact ⟨u, hu, rfl⟩

omit [Finite V] in
theorem resHom_conj_mem_autSub' {L : Subgroup (MulAut V)} {U : Subgroup V} {x : MulAut V}
    (hxs : x ∈ stabSub U) (hxL : ∀ k ∈ L, x * k * x⁻¹ ∈ L) {y : MulAut ↥U}
    (hy : y ∈ autSub L U) :
    resHom U ⟨x, hxs⟩ * y * (resHom U ⟨x, hxs⟩)⁻¹ ∈ autSub L U := by
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hy
  have hxl : x * (l : MulAut V) * x⁻¹ ∈ L := hxL l hl
  have hxlX : x * (l : MulAut V) * x⁻¹ ∈ stabSub U :=
    (stabSub U).mul_mem ((stabSub U).mul_mem hxs l.2) ((stabSub U).inv_mem hxs)
  refine mem_autSub.mpr ⟨⟨x * l * x⁻¹, hxlX⟩, hxl, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite V] in
theorem le_closure_of_genTop {L H : Subgroup (MulAut V)} {U : Subgroup V} (hH : H ≤ stabSub U)
    (hgen : GenTop (autSub L U) (autSub H U)) :
    U ≤ Subgroup.closure {x | ∃ g ∈ L, ∃ z ∈ fixV H ⊓ U, g z = x} := by
  intro u hu
  have h1 : u ∈ (Subgroup.closure {x : ↥U | ∃ ψ ∈ autSub L U, ∃ z ∈ fixV (autSub H U),
      ψ z = x}).map U.subtype :=
    ⟨⟨u, hu⟩, by rw [show Subgroup.closure _ = ⊤ from hgen]; trivial, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine (Subgroup.closure_mono ?_) h1
  rintro _ ⟨x, ⟨ψ, hψ, z, hz, rfl⟩, rfl⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ
  refine ⟨g, hg, (z : V), ⟨?_, z.2⟩, rfl⟩
  exact fun t ht => (mem_fixV_autSub.mp hz) t ht (hH ht)

open Classical in
theorem genTop_of_not_S3Block (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) (hnS : ¬ S3Block L)
    {T₀ : Subgroup (MulAut V)} (hT₀ : T₀ ≤ Tb) (hT₀n : ∀ t ∈ T₀, conjBy t L = L) :
    GenTop (autSub L (commV L)) (autSub T₀ (commV L)) := by
  have hs := suppData_block h hI hL
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hH := block_d217hyp h hr hr2 hI hL
  have hD := (block_d217 h hr hr2 hI hL).2
  have hH2 : IsPGroup 2 (autSub T₀ (commV L)) := isPGroup_autSub (h.syl.2.1.to_le hT₀)
  have hTs : ∀ t ∈ T₀, t ∈ stabSub (commV L) := fun t ht =>
    mem_stabSub_commV_of_conjBy (hT₀n t ht)
  have hHn : ∀ τ ∈ autSub T₀ (commV L), ∀ y ∈ autSub L (commV L),
      τ * y * τ⁻¹ ∈ autSub L (commV L) := by
    intro τ hτ y hy
    obtain ⟨t, htT, rfl⟩ := mem_autSub.mp hτ
    exact resHom_conj_mem_autSub' (hTs t htT) (fun k hk => by
      have := mem_conjBy_of_mem (g := (t : MulAut V)) hk
      rwa [hT₀n t htT] at this) hy
  have hUne : commV L ≠ ⊥ := fun e => hI.ne_bot L hL (eq_bot_of_commV_eq_bot e)
  have hrkpos : 0 < rk ↥(commV L) := by
    rcases Nat.eq_zero_or_pos (rk ↥(commV L)) with h0 | h0
    · exfalso
      apply hUne
      refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
      have := (rk_eq_zero_iff_of_isPGroup (G := V) (H := commV L)
        ((isPGroup_two_of_sq_eq_one h.sq).to_subgroup _)).mp h0
      rw [this] at hu
      exact hu
    · exact h0
  have hfix : fixV (autSub T₀ (commV L)) ≠ ⊥ := by
    have := rk_fixV_pos_of_isPGroup_two hUsq hH2 hrkpos
    intro hbot
    rw [hbot, rk_bot] at this
    exact lt_irrefl _ this
  have hnot : ¬ (Nonempty (↥(autSub L (commV L)) ≃* DihedralGroup 3) ∧ rk ↥(commV L) = 4) :=
    fun hc => hnS ((S3Block_iff hs).mpr hc)
  exact genTop_of_concl hUsq hH hD hnot hH2 hHn hfix

open Classical in
theorem pair_le_closure (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L L' : Subgroup (MulAut V)} (hL : L ∈ I) (hL' : L' ∈ I) (hne : L' ≠ L) {σ : MulAut V}
    (hσ : σ ∈ Tb) (eσ : conjBy σ L = L')
    (horb : ∀ x ∈ X, conjBy x L = L ∨ conjBy x L = L') (hnS : ¬ S3Block L) :
    commV L ≤ Subgroup.closure {x | ∃ g ∈ L ⊔ L', ∃ z ∈ fixV Tb ⊓ commV (L ⊔ L'), g z = x} := by
  have hs := suppData_block h hI hL
  have hσX : σ ∈ X := h.syl.1 hσ
  set T₀ : Subgroup (MulAut V) := stabConj Tb L with hT₀def
  have hT₀Tb : T₀ ≤ Tb := fun t ht => ht.1
  have hT₀n : ∀ t ∈ T₀, conjBy t L = L := fun t ht => ht.2
  have hσ2 : σ * σ ∈ T₀ := by
    refine ⟨Tb.mul_mem hσ hσ, ?_⟩
    rcases horb (σ * σ) (X.mul_mem hσX hσX) with h2 | h2
    · exact h2
    · exfalso
      apply hne
      have h3 : conjBy σ L' = conjBy σ L :=
        calc conjBy σ L' = conjBy σ (conjBy σ L) := by rw [eσ]
          _ = conjBy (σ * σ) L := conjBy_conjBy _ _ _
          _ = L' := h2
          _ = conjBy σ L := eσ.symm
      exact conjBy_injective σ h3
  have hσ'L : conjBy σ L' = L := by
    rw [← eσ, conjBy_conjBy]
    exact hσ2.2
  have hσinv : conjBy σ⁻¹ L = L' := conjBy_inv_eq_of_eq hσ'L
  have hstab' : ∀ t ∈ T₀, conjBy t L' = L' := by
    intro t ht
    have h1 : conjBy t L' = conjBy (t * σ) L := by rw [← eσ, conjBy_conjBy]
    rcases horb (t * σ) (X.mul_mem (h.syl.1 ht.1) hσX) with h2 | h2
    · exfalso
      apply hne
      have : conjBy t L' = conjBy t L := by rw [h1, h2, ht.2]
      exact conjBy_injective t this
    · rw [h1, h2]
  have hσconj : ∀ t ∈ T₀, σ⁻¹ * t * σ ∈ T₀ := by
    intro t ht
    refine ⟨Tb.mul_mem (Tb.mul_mem (Tb.inv_mem hσ) ht.1) hσ, ?_⟩
    have : conjBy (σ⁻¹ * t * σ) L = conjBy σ⁻¹ (conjBy t (conjBy σ L)) := by
      rw [conjBy_conjBy, conjBy_conjBy]
    rw [this, eσ, hstab' t ht]
    exact conjBy_inv_eq_of_eq eσ
  have hgen := genTop_of_not_S3Block h hr hr2 hI hL hnS hT₀Tb hT₀n
  have hT₀s : T₀ ≤ stabSub (commV L) := fun t ht => mem_stabSub_commV_of_conjBy (hT₀n t ht)
  have hU1 := le_closure_of_genTop hT₀s hgen
  set Q : Subgroup V := Subgroup.closure
    {x | ∃ g ∈ L ⊔ L', ∃ z ∈ fixV Tb ⊓ commV (L ⊔ L'), g z = x} with hQ
  have hkey : ∀ c ∈ fixV T₀ ⊓ commV L, ∀ l ∈ L, l c * c⁻¹ ∈ Q := by
    intro c hc l hl
    have hcT : ∀ t ∈ T₀, t c = c := fun t ht => hc.1 t ht
    have hσc : ∀ t ∈ T₀, t (σ c) = σ c := by
      intro t ht
      have e : t * σ = σ * (σ⁻¹ * t * σ) := by group
      calc t (σ c) = (t * σ) c := rfl
        _ = (σ * (σ⁻¹ * t * σ)) c := by rw [e]
        _ = σ ((σ⁻¹ * t * σ) c) := rfl
        _ = σ c := by rw [hcT _ (hσconj t ht)]
    have hσ2c : σ (σ c) = c := by
      show (σ * σ) c = c
      exact hcT _ hσ2
    have hσcU' : σ c ∈ commV L' := by
      have : σ c ∈ commV (conjBy σ L) := by
        rw [commV_conjBy]
        exact ⟨c, hc.2, rfl⟩
      rwa [eσ] at this
    have hzfix : c * σ c ∈ fixV Tb := by
      intro t ht
      rcases horb t (h.syl.1 ht) with h2 | h2
      · have htT₀ : t ∈ T₀ := ⟨ht, h2⟩
        rw [map_mul, hcT t htT₀, hσc t htT₀]
      ·
        have hsT : t * σ⁻¹ ∈ T₀ := by
          refine ⟨Tb.mul_mem ht (Tb.inv_mem hσ), ?_⟩
          have hLt : conjBy t L' = L := by
            have h1 : conjBy t L' = conjBy (t * σ) L := by rw [← eσ, conjBy_conjBy]
            rcases horb (t * σ) (X.mul_mem (h.syl.1 ht) hσX) with h3 | h3
            · rw [h1, h3]
            · exfalso
              apply hne
              have : conjBy t L' = conjBy t L := by rw [h1, h3, h2]
              exact conjBy_injective t this
          rw [← conjBy_conjBy, hσinv, hLt]
        have hts : t = (t * σ⁻¹) * σ := by group
        have hsc : (t * σ⁻¹) c = c := hcT _ hsT
        have hssc : (t * σ⁻¹) (σ c) = σ c := hσc _ hsT
        calc t (c * σ c) = ((t * σ⁻¹) * σ) (c * σ c) := by rw [← hts]
          _ = (t * σ⁻¹) (σ c * σ (σ c)) := by rw [MulAut.mul_apply, map_mul]
          _ = (t * σ⁻¹) (σ c * c) := by rw [hσ2c]
          _ = σ c * c := by rw [map_mul, hssc, hsc]
          _ = c * σ c := mul_comm _ _
    have hzU : c * σ c ∈ commV (L ⊔ L') :=
      Subgroup.mul_mem _ (commV_mono216 (le_sup_left : L ≤ L ⊔ L') hc.2)
        (commV_mono216 (le_sup_right : L' ≤ L ⊔ L') hσcU')
    have hfixl : l (σ c) = σ c := (hI.triv L' hL' L hL hne hσcU') l hl
    have hz_mem : c * σ c ∈ Q :=
      Subgroup.subset_closure ⟨1, (L ⊔ L').one_mem, c * σ c, ⟨hzfix, hzU⟩, rfl⟩
    have hlz_mem : l (c * σ c) ∈ Q :=
      Subgroup.subset_closure ⟨l, (le_sup_left : L ≤ L ⊔ L') hl, c * σ c, ⟨hzfix, hzU⟩, rfl⟩
    have h3 := Q.mul_mem hlz_mem (Q.inv_mem hz_mem)
    have e : l (c * σ c) * (c * σ c)⁻¹ = l c * c⁻¹ := by
      rw [map_mul, hfixl]; group
    rwa [e] at h3
  have hP : ∀ u : V, u ∈ Subgroup.closure
      {x | ∃ g ∈ L, ∃ z ∈ fixV T₀ ⊓ commV L, g z = x} → ∀ l ∈ L, l u * u⁻¹ ∈ Q := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, c, hc, rfl⟩ := hx
      intro l hl
      have h1 := hkey c hc (l * g) (L.mul_mem hl hg)
      have h2 := hkey c hc g hg
      have h3 := Q.mul_mem h1 (Q.inv_mem h2)
      have e : l (g c) * (g c)⁻¹ = (l * g) c * c⁻¹ * (g c * c⁻¹)⁻¹ := by
        rw [MulAut.mul_apply]; group
      rwa [← e] at h3
    | one =>
      intro l hl
      rw [map_one, one_mul, inv_one]
      exact Q.one_mem
    | mul x y _ _ hx hy =>
      intro l hl
      have h3 := Q.mul_mem (hx l hl) (hy l hl)
      have e : l (x * y) * (x * y)⁻¹ = (l x * x⁻¹) * (l y * y⁻¹) := by
        rw [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _
      rwa [← e] at h3
    | inv x _ hx =>
      intro l hl
      have h3 := Q.inv_mem (hx l hl)
      have e : l x⁻¹ * (x⁻¹)⁻¹ = (l x * x⁻¹)⁻¹ := by rw [map_inv, mul_inv, inv_inv]
      rwa [← e] at h3
  have hprop : ∀ u ∈ commV L, ∀ l ∈ L, l u * u⁻¹ ∈ Q := fun u hu => hP u (hU1 hu)
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hH := block_d217hyp h hr hr2 hI hL
  have hcyc : IsCyclic ↥(fittingOf L) :=
    orbit_two_fitting_cyclic h hr hr2 hI hL hL' hne.symm eσ.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(fittingOf L))
  set a : MulAut V := (g : MulAut V) with ha
  have haF : a ∈ fittingOf L := g.2
  have haL : a ∈ L := fittingOf_le L haF
  have has : a ∈ stabSub (commV L) := le_stabSub_commV L haL
  have hfpf : ∀ u : ↥(commV L), a (u : V) = u → u = 1 := by
    intro u hau
    have hfix' : u ∈ fixV (autSub (fittingOf L) (commV L)) := by
      rw [mem_fixV_autSub]
      intro f hf hfs
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨f, hf⟩)
      have hfn : f = a ^ n := by
        have := congrArg Subtype.val hn
        simpa [Subgroup.coe_zpow, ha] using this.symm
      have hmem : (u : V) ∈ fixV (Subgroup.zpowers a) := mem_fixV_zpowers_iff.mpr hau
      rw [hfn]
      exact hmem (a ^ n) (Subgroup.zpow_mem_zpowers a n)
    rw [hs.autSub_fittingOf, fixV_fittingOf_eq_bot hUsq hH.o2 hH.comm_fitting] at hfix'
    exact Subgroup.mem_bot.mp hfix'
  let d : ↥(commV L) →* ↥(commV L) :=
    MonoidHom.mk' (fun u => ⟨a (u : V) * (u : V)⁻¹,
      Subgroup.mul_mem _ ((has (u : V)).mpr u.2) (Subgroup.inv_mem _ u.2)⟩) (by
      intro u v
      apply Subtype.ext
      simp only [Subgroup.coe_mul, map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hdinj : Function.Injective d := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : a (u : V) * (u : V)⁻¹ = 1 := congrArg Subtype.val hu
    exact hfpf u (mul_inv_eq_one.mp h1)
  have hdsurj : Function.Surjective d := Finite.injective_iff_surjective.mp hdinj
  intro u₀ hu₀
  obtain ⟨u, hu⟩ := hdsurj ⟨u₀, hu₀⟩
  have h1 : a (u : V) * (u : V)⁻¹ = u₀ := congrArg Subtype.val hu
  rw [← h1]
  exact hprop u u.2 a haL

open Classical in
omit [Finite V] in
theorem iSup_pair151c {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut V) → α)
    (a b : Subgroup (MulAut V)) :
    (⨆ L ∈ ({a, b} : Finset (Subgroup (MulAut V))), f L) = f a ⊔ f b := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact le_sup_left
    · rw [Finset.mem_singleton.mp hL]
      exact le_sup_right
  · exact sup_le
      (le_iSup₂ (f := fun L (_ : L ∈ ({a, b} : Finset (Subgroup (MulAut V)))) => f L) a
        (by simp))
      (le_iSup₂ (f := fun L (_ : L ∈ ({a, b} : Finset (Subgroup (MulAut V)))) => f L) b
        (by simp))

omit [Finite V] in
theorem commV_sup_le151c (L₁ L₂ : Subgroup (MulAut V)) :
    commV (L₁ ⊔ L₂) ≤ commV L₁ ⊔ commV L₂ :=
  CFSG.Quasithin.FixVLat.commV_sup_le L₁ L₂

theorem S3Block_of_conj {L L' : Subgroup (MulAut V)} {x : MulAut V} (hLL' : conjBy x L = L')
    (hS : S3Block L) : S3Block L' := by
  subst hLL'
  obtain ⟨⟨e⟩, hr⟩ := hS
  refine ⟨⟨(Subgroup.equivMapOfInjective L (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).symm.trans e⟩, ?_⟩
  rw [rk_commV_conjBy, hr]

open Classical in
theorem two_orbit_S3Block (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂)
    (hnot : ¬ commV (L₁ ⊔ L₂) ≤ Subgroup.closure
      {x | ∃ g ∈ L₁ ⊔ L₂, ∃ z ∈ fixV Tb ⊓ commV (L₁ ⊔ L₂), g z = x}) :
    S3Block L₁ ∧ S3Block L₂ := by
  obtain ⟨σ, hσ, eσ⟩ := exists_swap_of_orbit_two h hne hx₂ e₂ horb
  have hσ'L₂ : conjBy σ⁻¹ L₂ = L₁ := conjBy_inv_eq_of_eq eσ
  have horb₂ : ∀ x ∈ X, conjBy x L₂ = L₂ ∨ conjBy x L₂ = L₁ := by
    intro x hx
    have e : conjBy x L₂ = conjBy (x * σ) L₁ := by rw [← eσ, conjBy_conjBy]
    rcases horb (x * σ) (X.mul_mem hx (h.syl.1 hσ)) with h3 | h3
    · right; rw [e, h3]
    · left; rw [e, h3]
  have hS : S3Block L₁ ∨ S3Block L₂ := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hQ1 := pair_le_closure h hr hr2 hI h1 h2 hne hσ eσ horb hn1
    have hQ2 := pair_le_closure h hr hr2 hI h2 h1 hne.symm (Tb.inv_mem hσ) hσ'L₂ horb₂ hn2
    rw [sup_comm L₂ L₁] at hQ2
    apply hnot
    exact (commV_sup_le151c L₁ L₂).trans (sup_le hQ1 hQ2)
  refine ⟨?_, ?_⟩
  · rcases hS with hS | hS
    · exact hS
    · exact S3Block_of_conj (conjBy_inv_eq_of_eq e₂) hS
  · rcases hS with hS | hS
    · exact S3Block_of_conj e₂ hS
    · exact hS

open Classical in
theorem block_S3Block (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    (hn1 : ¬ ∃ K, IsComp X I K ∧ Jhat X = K ∧ fixV (Jhat X) = ⊥) {L : Subgroup (MulAut V)}
    (hL : L ∈ I) : S3Block L := by
  have hs := suppData_block h hI hL
  by_cases hnot : ∃ x ∈ X, conjBy x L ≠ L
  · obtain ⟨L₂, hL₂, hne, ⟨x₂, hx₂, e₂⟩, horb⟩ := orbit_le_two h hr hr2 hI hL hnot
    have hK : IsComp X I (L ⊔ L₂) := Or.inr ⟨L, hL, L₂, hL₂, hne, ⟨x₂, hx₂, e₂⟩, horb, rfl⟩
    have hKne : L ⊔ L₂ ≠ ⊥ := fun e => hI.ne_bot L hL (le_bot_iff.mp (e ▸ le_sup_left))
    rcases dich h hI hK hKne with ⟨hJ, hf⟩ | ⟨-, -, hnot'⟩
    · exact absurd ⟨L ⊔ L₂, hK, hJ, hf⟩ hn1
    · exact (two_orbit_S3Block h hr hr2 hI hL hL₂ hne hx₂ e₂ horb hnot').1
  · push Not at hnot
    have hK : IsComp X I L := Or.inl ⟨L, hL, hnot, rfl⟩
    rcases dich h hI hK (hI.ne_bot L hL) with ⟨hJ, hf⟩ | ⟨-, -, hnot'⟩
    · exact absurd ⟨L, hK, hJ, hf⟩ hn1
    · obtain ⟨e, hr4⟩ := block_S3rk4_of_not_genTop h hr hr2 hI hL hK.normalIn hnot'
      exact (S3Block_iff hs).mpr ⟨e, hr4⟩

end Two151c

end CFSG.Quasithin
