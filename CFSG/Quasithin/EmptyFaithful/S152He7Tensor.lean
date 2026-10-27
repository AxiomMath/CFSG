module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S152He6Core

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He6 CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

variable {W : Type} [CommGroup W]

section Key

variable [Finite W]

theorem card_le_card_cmt_mul {a a' : MulAut W} (hW : ∀ w : W, w * w = 1) (ha' : a' * a' = 1)
    (hcomm : a * a' = a' * a) {S : Subgroup W} (hS : ∀ u ∈ S, a u ∈ S)
    (hSfix : ∀ u ∈ S, a' u = u → u = 1) : Nat.card S ≤ Nat.card (cmt (a * a') ⊤) := by
  have hinv : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hW v)
  have haa' : ∀ v, a (a' v) = a' (a v) := fun v => congrArg (fun m : MulAut W => m v) hcomm
  have ha'a' : ∀ v, a' (a' v) = v := fun v => congrArg (fun m : MulAut W => m v) ha'
  have hker : ∀ s ∈ S, (a * a') s * s⁻¹ = 1 → s = 1 := by
    intro s hs hz
    have h1 : a (a' s) = s := mul_inv_eq_one.1 hz
    set t : W := a' s * s⁻¹ with ht
    have hts : a' s = t * s := by rw [ht, inv_mul_cancel_right]
    have hat : a' t = t := by
      calc a' t = a' (a' s) * (a' s)⁻¹ := by rw [ht, map_mul, map_inv]
        _ = s * (a' s)⁻¹ := by rw [ha'a']
        _ = (a' s * s⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
        _ = t := by rw [← ht, hinv]
    have hat2 : a t = s * a s := by
      have h2 : a t * a s = s := by rw [← map_mul, ← hts, h1]
      calc a t = (a t * a s) * (a s)⁻¹ := by rw [mul_inv_cancel_right]
        _ = s * (a s)⁻¹ := by rw [h2]
        _ = s * a s := by rw [hinv]
    have hmemS : a t ∈ S := by
      rw [hat2]
      exact S.mul_mem hs (hS s hs)
    have hfixat : a' (a t) = a t := by rw [← haa', hat]
    have h3 : a t = 1 := hSfix _ hmemS hfixat
    have h4 : t = 1 := by
      have : a t = a 1 := by rw [h3, map_one]
      exact a.injective this
    have h5 : a' s = s := by rw [hts, h4, one_mul]
    exact hSfix s hs h5
  let f : ↥S → ↥(cmt (a * a') ⊤) := fun s => ⟨dsp (a * a') (s : W), ⟨s, Subgroup.mem_top _, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro s s' h
    have h' : dsp (a * a') (s : W) = dsp (a * a') (s' : W) := congrArg Subtype.val h
    have hmul : dsp (a * a') ((s : W) * (s' : W)⁻¹) = 1 := by
      rw [map_mul, map_inv, h', mul_inv_cancel]
    have := hker _ (S.mul_mem s.2 (S.inv_mem s'.2)) (by rw [← dsp_apply]; exact hmul)
    exact Subtype.ext (mul_inv_eq_one.1 this)
  exact Nat.card_le_card_of_injective f hinj

theorem six_le_card_of_faithful (P : PairData W) (h168 : Nat.card ↥P.A = 168) {S : Subgroup W}
    (hS : ∀ g ∈ P.A, ∀ u ∈ S, g u ∈ S) (hnt : ∃ g ∈ P.A, ∃ u ∈ S, g u ≠ u) :
    6 ≤ Nat.card ↥S := by
  have hinj := restrHom_injective P.simpA hS hnt
  have h1 : Nat.card ↥P.A ≤ Nat.card (MulAut ↥S) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (MulAut ↥S) ≤ Nat.card (Equiv.Perm ↥S) :=
    Nat.card_le_card_of_injective (fun φ : MulAut ↥S => φ.toEquiv) MulEquiv.toEquiv_injective
  rw [Nat.card_perm] at h2
  by_contra hlt
  push Not at hlt
  have h3 : (Nat.card ↥S).factorial ≤ (5 : ℕ).factorial := Nat.factorial_le (by omega)
  have h4 : (5 : ℕ).factorial = 120 := by decide
  omega

end Key

section MinK

variable [Finite W]

@[expose] def KInv (P : PairData W) (S : Subgroup W) : Prop :=
  (∀ g ∈ P.A, ∀ u ∈ S, g u ∈ S) ∧ (∀ g ∈ P.A', ∀ u ∈ S, g u ∈ S)

@[expose] def IsMinK (P : PairData W) (S : Subgroup W) : Prop :=
  S ≠ ⊥ ∧ KInv P S ∧ ∀ S' ≤ S, KInv P S' → S' = ⊥ ∨ S' = S

theorem exists_isMinK_le (P : PairData W) {U : Subgroup W} (hU : KInv P U) (hne : U ≠ ⊥) :
    ∃ S ≤ U, IsMinK P S := by
  classical
  let 𝒮 : Set (Subgroup W) := {S | S ≤ U ∧ S ≠ ⊥ ∧ KInv P S}
  obtain ⟨S, ⟨hSU, hSne, hSK⟩, hmin⟩ :=
    Set.exists_min_image 𝒮 (fun S => Nat.card S) (Set.toFinite _) ⟨U, le_rfl, hne, hU⟩
  refine ⟨S, hSU, hSne, hSK, fun S' hS'S hS'K => ?_⟩
  by_cases hS' : S' = ⊥
  · exact Or.inl hS'
  · right
    have hc : Nat.card S ≤ Nat.card S' := hmin S' ⟨hS'S.trans hSU, hS', hS'K⟩
    exact Subgroup.eq_of_le_of_card_ge hS'S hc

omit [Finite W] in
theorem kInv_fixV_A (P : PairData W) : KInv P (fixV P.A) :=
  ⟨fun g hg u hu => by rw [mem_fixV.1 hu g hg]; exact hu, fun g hg u hu => P.fixA_inv hg hu⟩

omit [Finite W] in
theorem kInv_fixV_A' (P : PairData W) : KInv P (fixV P.A') :=
  ⟨fun g hg u hu => P.fixA'_inv hg hu, fun g hg u hu => by rw [mem_fixV.1 hu g hg]; exact hu⟩

theorem not_nontrivial_both (P : PairData W) (h168 : Nat.card ↥P.A = 168) {a a' : MulAut W}
    (ha : a ∈ P.A) (ha' : a' ∈ P.A') (ha'2 : a' * a' = 1) (hz : Nat.card (cmt (a * a') ⊤) ≤ 4)
    {S : Subgroup W} (hS : IsMinK P S) (hanc : ∃ u ∈ S, a u ≠ u) (ha'nc : ∃ u ∈ S, a' u ≠ u) :
    False := by
  classical
  obtain ⟨hSne, ⟨hSA, hSA'⟩, hSmin⟩ := hS
  obtain ⟨S₀, hS₀S, hS₀ne, hS₀A, hS₀min⟩ : ∃ S₀ ≤ S, S₀ ≠ ⊥ ∧ (∀ g ∈ P.A, ∀ u ∈ S₀, g u ∈ S₀) ∧
      ∀ S'' ≤ S₀, (∀ g ∈ P.A, ∀ u ∈ S'', g u ∈ S'') → S'' = ⊥ ∨ S'' = S₀ := by
    let 𝒮 : Set (Subgroup W) := {T | T ≤ S ∧ T ≠ ⊥ ∧ ∀ g ∈ P.A, ∀ u ∈ T, g u ∈ T}
    obtain ⟨S₀, ⟨h1, h2, h3⟩, hmin⟩ :=
      Set.exists_min_image 𝒮 (fun T => Nat.card T) (Set.toFinite _) ⟨S, le_rfl, hSne, hSA⟩
    refine ⟨S₀, h1, h2, h3, fun S'' hS''S₀ hS''A => ?_⟩
    by_cases hS'' : S'' = ⊥
    · exact Or.inl hS''
    · right
      have hc : Nat.card S₀ ≤ Nat.card S'' := hmin S'' ⟨hS''S₀.trans h1, hS'', hS''A⟩
      exact Subgroup.eq_of_le_of_card_ge hS''S₀ hc
  let Tset : Set W := {x | ∃ g' ∈ P.A', ∃ u ∈ S₀, x = g' u}
  let T₀ : Subgroup W := Subgroup.closure Tset
  have hTset_A : ∀ h ∈ P.A, ∀ x ∈ Tset, h x ∈ Tset := by
    rintro h hh _ ⟨g', hg', u, hu, rfl⟩
    refine ⟨g', hg', h u, hS₀A h hh u hu, ?_⟩
    have := congrArg (fun m : MulAut W => m u) (P.comm h hh g' hg')
    exact this
  have hTset_A' : ∀ h ∈ P.A', ∀ x ∈ Tset, h x ∈ Tset := by
    rintro h hh _ ⟨g', hg', u, hu, rfl⟩
    exact ⟨h * g', P.A'.mul_mem hh hg', u, hu, rfl⟩
  have hT₀inv : ∀ (h : MulAut W), (∀ x ∈ Tset, h x ∈ T₀) → ∀ x ∈ T₀, h x ∈ T₀ := by
    intro h hh x hx
    have : T₀ ≤ T₀.comap (h : MulAut W).toMonoidHom :=
      (Subgroup.closure_le _).2 fun y hy => hh y hy
    exact this hx
  have hT₀A : ∀ h ∈ P.A, ∀ x ∈ T₀, h x ∈ T₀ := fun h hh =>
    hT₀inv h fun x hx => Subgroup.subset_closure (hTset_A h hh x hx)
  have hT₀A' : ∀ h ∈ P.A', ∀ x ∈ T₀, h x ∈ T₀ := fun h hh =>
    hT₀inv h fun x hx => Subgroup.subset_closure (hTset_A' h hh x hx)
  have hS₀T : S₀ ≤ T₀ := fun u hu => Subgroup.subset_closure ⟨1, P.A'.one_mem, u, hu, by simp⟩
  have hT₀S : T₀ ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g', hg', u, hu, rfl⟩
    exact hSA' g' hg' u (hS₀S hu)
  have hT₀ne : T₀ ≠ ⊥ := by
    intro h
    apply hS₀ne
    rw [eq_bot_iff]
    intro u hu
    have := hS₀T hu
    rwa [h] at this
  have hT₀S' : T₀ = S := (hSmin T₀ hT₀S ⟨hT₀A, hT₀A'⟩).resolve_left hT₀ne
  obtain ⟨x, ⟨g', hg', u, hu, rfl⟩, hx⟩ : ∃ x ∈ Tset, a' x ≠ x := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy, hy1⟩ := ha'nc
    apply hy1
    have hle : T₀ ≤ fixV (Subgroup.zpowers a') := by
      refine (Subgroup.closure_le _).2 fun z hz => ?_
      rw [SetLike.mem_coe, mem_fixV_zpowers]
      exact hall z hz
    have : y ∈ T₀ := by rw [hT₀S']; exact hy
    exact mem_fixV_zpowers.1 (hle this)
  set S₁ : Subgroup W := S₀.map (g' : MulAut W).toMonoidHom with hS₁
  have hS₁A : ∀ h ∈ P.A, ∀ y ∈ S₁, h y ∈ S₁ := by
    rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨h v, hS₀A h hh v hv, ?_⟩
    have := congrArg (fun m : MulAut W => m v) (P.comm h hh g' hg')
    exact this.symm
  have hxS₁ : g' u ∈ S₁ := ⟨u, hu, rfl⟩
  have hS₁min : ∀ S'' ≤ S₁, (∀ g ∈ P.A, ∀ y ∈ S'', g y ∈ S'') → S'' = ⊥ ∨ S'' = S₁ := by
    intro S'' hS''S₁ hS''A
    set R : Subgroup W := S''.map (g'⁻¹ : MulAut W).toMonoidHom with hR
    have hRS₀ : R ≤ S₀ := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨v, hv, hvy⟩ := hS''S₁ hy
      have : (g'⁻¹ : MulAut W) y = v := by
        rw [← hvy]
        exact MulAut.inv_apply_self W g' v
      show (g'⁻¹ : MulAut W) y ∈ S₀
      rw [this]
      exact hv
    have hRA : ∀ h ∈ P.A, ∀ y ∈ R, h y ∈ R := by
      rintro h hh _ ⟨y, hy, rfl⟩
      refine ⟨h y, hS''A h hh y hy, ?_⟩
      have h1 : h * g'⁻¹ = g'⁻¹ * h := by
        have := P.comm h hh g' hg'
        calc h * g'⁻¹ = g'⁻¹ * (g' * h) * g'⁻¹ := by group
          _ = g'⁻¹ * (h * g') * g'⁻¹ := by rw [this]
          _ = g'⁻¹ * h := by group
      have := congrArg (fun m : MulAut W => m y) h1
      exact this.symm
    rcases hS₀min R hRS₀ hRA with h0 | h0
    · left
      rw [eq_bot_iff]
      intro y hy
      have : (g'⁻¹ : MulAut W) y ∈ R := ⟨y, hy, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      have h2 : (g'⁻¹ : MulAut W) y = (g'⁻¹ : MulAut W) 1 := by rw [this, map_one]
      exact (g'⁻¹ : MulAut W).injective h2
    · right
      refine le_antisymm hS''S₁ ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [← h0] at hv
      obtain ⟨y, hy, hyv⟩ := hv
      have : (g' : MulAut W) v = y := by
        rw [← hyv]
        exact MulAut.apply_inv_self W g' y
      show (g' : MulAut W) v ∈ S''
      rw [this]
      exact hy
  have hcent : ∀ h ∈ P.A, ∀ y ∈ fixV (Subgroup.zpowers a'), h y ∈ fixV (Subgroup.zpowers a') := by
    intro h hh y hy
    rw [mem_fixV_zpowers] at hy ⊢
    have := congrArg (fun m : MulAut W => m y) (P.comm' ha' hh)
    calc a' (h y) = (a' * h) y := rfl
      _ = (h * a') y := this
      _ = h y := by rw [MulAut.mul_apply, hy]
  have hI : S₁ ⊓ fixV (Subgroup.zpowers a') = ⊥ := by
    rcases hS₁min (S₁ ⊓ fixV (Subgroup.zpowers a')) inf_le_left (fun h hh y hy =>
        ⟨hS₁A h hh y hy.1, hcent h hh y hy.2⟩) with h | h
    · exact h
    · exfalso
      have : g' u ∈ S₁ ⊓ fixV (Subgroup.zpowers a') := by rw [h]; exact hxS₁
      exact hx (mem_fixV_zpowers.1 this.2)
  have hnt₁ : ∃ g ∈ P.A, ∃ y ∈ S₁, g y ≠ y := by
    by_contra hall
    push Not at hall
    have hS₀D : S₀ ≤ fixV P.A := by
      intro v hv
      rw [mem_fixV]
      intro g hg
      have h1 := hall g hg (g' v) ⟨v, hv, rfl⟩
      have h2 : (g' : MulAut W) (g v) = g' v := by
        have := congrArg (fun m : MulAut W => m v) (P.comm g hg g' hg')
        exact this.symm.trans h1
      exact g'.injective h2
    have hN : S ⊓ fixV P.A = S := by
      rcases hSmin (S ⊓ fixV P.A) inf_le_left
          ⟨fun g hg u hu => ⟨hSA g hg u hu.1, (kInv_fixV_A P).1 g hg u hu.2⟩,
            fun g hg u hu => ⟨hSA' g hg u hu.1, (kInv_fixV_A P).2 g hg u hu.2⟩⟩ with h | h
      · exfalso
        apply hS₀ne
        rw [eq_bot_iff]
        intro v hv
        have : v ∈ S ⊓ fixV P.A := ⟨hS₀S hv, hS₀D hv⟩
        rwa [h] at this
      · exact h
    obtain ⟨y, hy, hy1⟩ := hanc
    apply hy1
    have : y ∈ S ⊓ fixV P.A := by rw [hN]; exact hy
    exact mem_fixV.1 this.2 a ha
  have h6 : 6 ≤ Nat.card ↥S₁ := six_le_card_of_faithful P h168 hS₁A hnt₁
  have h7 : Nat.card ↥S₁ ≤ Nat.card (cmt (a * a') ⊤) :=
    card_le_card_cmt_mul P.hW ha'2 (P.comm a ha a' ha') (hS₁A a ha) fun y hy hy' => by
      have : y ∈ S₁ ⊓ fixV (Subgroup.zpowers a') := ⟨hy, mem_fixV_zpowers.2 hy'⟩
      rw [hI, Subgroup.mem_bot] at this
      exact this
  omega

end MinK

section Structure

variable [Finite W]

structure GoodPair (P : PairData W) (a a' : MulAut W) : Prop where
  ha : a ∈ P.A
  ha' : a' ∈ P.A'
  ha1 : a ≠ 1
  ha'1 : a' ≠ 1
  ha'2 : a' * a' = 1
  hz : Nat.card (cmt (a * a') ⊤) ≤ 4

variable {P : PairData W} {a a' : MulAut W}

omit [Finite W] in
theorem exists_moved {g : MulAut W} (hg : g ≠ 1) : ∃ w : W, g w ≠ w := by
  by_contra h
  push Not at h
  exact hg (MulEquiv.ext h)

omit [Finite W] in
theorem fixes_of_simple_A (P : PairData W) {a : MulAut W} (ha : a ∈ P.A) (ha1 : a ≠ 1)
    {S : Subgroup W} (hS : ∀ g ∈ P.A, ∀ u ∈ S, g u ∈ S) (h : ∀ u ∈ S, a u = u) :
    S ≤ fixV P.A := fun u hu =>
  mem_fixV.2 fun g hg => acts_trivially_of_simple P.simpA hS ha ha1 h g hg u hu

omit [Finite W] in
theorem fixes_of_simple_A' (P : PairData W) {a' : MulAut W} (ha' : a' ∈ P.A') (ha'1 : a' ≠ 1)
    {S : Subgroup W} (hS : ∀ g ∈ P.A', ∀ u ∈ S, g u ∈ S) (h : ∀ u ∈ S, a' u = u) :
    S ≤ fixV P.A' := fun u hu =>
  mem_fixV.2 fun g hg => acts_trivially_of_simple P.simpA' hS ha' ha'1 h g hg u hu

theorem GoodPair.dichotomy (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168) {S : Subgroup W}
    (hS : IsMinK P S) : S ≤ fixV P.A ∨ S ≤ fixV P.A' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hanc : ∃ u ∈ S, a u ≠ u := by
    by_contra h
    push Not at h
    exact hn1 (fixes_of_simple_A P G.ha G.ha1 hS.2.1.1 h)
  have ha'nc : ∃ u ∈ S, a' u ≠ u := by
    by_contra h
    push Not at h
    exact hn2 (fixes_of_simple_A' P G.ha' G.ha'1 hS.2.1.2 h)
  exact not_nontrivial_both P h168 G.ha G.ha' G.ha'2 G.hz hS hanc ha'nc

omit [Finite W] in
theorem GoodPair.top_ne_bot (G : GoodPair P a a') : (⊤ : Subgroup W) ≠ ⊥ := by
  intro h
  obtain ⟨w, hw⟩ := exists_moved G.ha1
  apply hw
  have : w ∈ (⊥ : Subgroup W) := h ▸ Subgroup.mem_top w
  rw [Subgroup.mem_bot.1 this]
  exact map_one a

theorem GoodPair.sup_eq_top (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168) :
    fixV P.A ⊔ fixV P.A' = ⊤ := by
  refine (P.irr _ fun g hg u hu => P.fixSup_inv hg hu).resolve_left fun hbot => ?_
  have hK : KInv P (⊤ : Subgroup W) := ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  obtain ⟨S, -, hS⟩ := exists_isMinK_le P hK G.top_ne_bot
  rcases G.dichotomy h168 hS with h | h
  · exact hS.1 (eq_bot_iff.2 (h.trans (le_sup_left.trans hbot.le)))
  · exact hS.1 (eq_bot_iff.2 (h.trans (le_sup_right.trans hbot.le)))

omit [Finite W] in
theorem GoodPair.inf_eq_bot (G : GoodPair P a a') : fixV P.A ⊓ fixV P.A' = ⊥ := by
  refine (P.irr _ ?_).resolve_right fun htop => ?_
  · intro g hg u hu
    rcases P.fix_stay_or_swap hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 u hu.1, h2 u hu.2⟩
    · exact ⟨h2 u hu.2, h1 u hu.1⟩
  · obtain ⟨w, hw⟩ := exists_moved G.ha1
    apply hw
    have : w ∈ fixV P.A ⊓ fixV P.A' := by rw [htop]; exact Subgroup.mem_top w
    exact mem_fixV.1 this.1 a G.ha

theorem GoodPair.fixA_ne_bot (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168) :
    fixV P.A ≠ ⊥ := by
  intro h
  have h2 := G.sup_eq_top h168
  rw [h, bot_sup_eq] at h2
  obtain ⟨w, hw⟩ := exists_moved G.ha'1
  apply hw
  have : w ∈ fixV P.A' := by rw [h2]; exact Subgroup.mem_top w
  exact mem_fixV.1 this a' G.ha'

theorem GoodPair.fixA'_ne_bot (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168) :
    fixV P.A' ≠ ⊥ := by
  intro h
  have h2 := G.sup_eq_top h168
  rw [h, sup_bot_eq] at h2
  obtain ⟨w, hw⟩ := exists_moved G.ha1
  apply hw
  have : w ∈ fixV P.A := by rw [h2]; exact Subgroup.mem_top w
  exact mem_fixV.1 this a G.ha

theorem GoodPair.card_cmt_fixA' (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168) :
    Nat.card (cmt a (fixV P.A')) = 2 := by
  set D := fixV P.A with hD
  set D' := fixV P.A' with hD'
  have hDD' := G.inf_eq_bot
  have haa' : a * a' = a' * a := P.comm a G.ha a' G.ha'
  have hXne : cmt a' D ≠ ⊥ := by
    intro h
    have h1 : ∀ u ∈ D, a' u = u := cmt_eq_bot_iff.1 h
    have h2 : D ≤ fixV P.A' :=
      fixes_of_simple_A' P G.ha' G.ha'1 (fun g hg u hu => P.fixA_inv hg hu) h1
    apply G.fixA_ne_bot h168
    rw [eq_bot_iff, ← hDD']
    exact le_inf le_rfl h2
  have hYne : cmt a D' ≠ ⊥ := by
    intro h
    have h1 : ∀ u ∈ D', a u = u := cmt_eq_bot_iff.1 h
    have h2 : D' ≤ fixV P.A :=
      fixes_of_simple_A P G.ha G.ha1 (fun g hg u hu => P.fixA'_inv hg hu) h1
    apply G.fixA'_ne_bot h168
    rw [eq_bot_iff, ← hDD']
    exact le_inf h2 le_rfl
  have hXD : cmt a' D ≤ D := cmt_le_of_invariant fun u hu => P.fixA_inv G.ha' hu
  have hYD' : cmt a D' ≤ D' := cmt_le_of_invariant fun u hu => P.fixA'_inv G.ha hu
  have hXz : cmt a' D ≤ cmt (a * a') ⊤ := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_cmt.1 hv
    refine mem_cmt.2 ⟨d, Subgroup.mem_top d, ?_⟩
    show (a * a') d * d⁻¹ = a' d * d⁻¹
    rw [MulAut.mul_apply, mem_fixV.1 (P.fixA_inv G.ha' hd) a G.ha]
  have hYz : cmt a D' ≤ cmt (a * a') ⊤ := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_cmt.1 hv
    refine mem_cmt.2 ⟨d, Subgroup.mem_top d, ?_⟩
    show (a * a') d * d⁻¹ = a d * d⁻¹
    rw [MulAut.mul_apply, mem_fixV.1 hd a' G.ha']
  let m : ↥(cmt a' D) × ↥(cmt a D') → ↥(cmt (a * a') ⊤) := fun p =>
    ⟨(p.1 : W) * (p.2 : W), (cmt (a * a') ⊤).mul_mem (hXz p.1.2) (hYz p.2.2)⟩
  have hm : Function.Injective m := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : (x : W) * (y : W) = (x' : W) * (y' : W) := congrArg Subtype.val h
    have h1 : (x' : W)⁻¹ * (x : W) = (y' : W) * (y : W)⁻¹ := by
      calc (x' : W)⁻¹ * (x : W) = (x' : W)⁻¹ * ((x : W) * (y : W)) * (y : W)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel_right]
        _ = (x' : W)⁻¹ * ((x' : W) * (y' : W)) * (y : W)⁻¹ := by rw [h']
        _ = (y' : W) * (y : W)⁻¹ := by rw [inv_mul_cancel_left]
    have hmem : (x' : W)⁻¹ * (x : W) ∈ D ⊓ D' :=
      ⟨D.mul_mem (D.inv_mem (hXD x'.2)) (hXD x.2), by
        rw [h1]
        exact D'.mul_mem (hYD' y'.2) (D'.inv_mem (hYD' y.2))⟩
    rw [hDD', Subgroup.mem_bot] at hmem
    have hx : x = x' := Subtype.ext (inv_mul_eq_one.1 hmem).symm
    have hy : y = y' := by
      rw [hmem] at h1
      exact Subtype.ext (mul_inv_eq_one.1 h1.symm).symm
    rw [hx, hy]
  have hcard : Nat.card ↥(cmt a' D) * Nat.card ↥(cmt a D') ≤ 4 := by
    have := Nat.card_le_card_of_injective m hm
    rw [Nat.card_prod] at this
    exact this.trans G.hz
  have hX2 : 2 ≤ Nat.card ↥(cmt a' D) := (Subgroup.one_lt_card_iff_ne_bot _).2 hXne
  have hY2 : 2 ≤ Nat.card ↥(cmt a D') := (Subgroup.one_lt_card_iff_ne_bot _).2 hYne
  have : Nat.card ↥(cmt a D') ≤ 2 := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul hX2 (show 3 ≤ Nat.card ↥(cmt a D') by omega)
    omega
  omega

theorem GoodPair.cmt_eq_of_isMinK (G : GoodPair P a a') (h168 : Nat.card ↥P.A = 168)
    {S : Subgroup W} (hS : IsMinK P S) (hle : S ≤ fixV P.A') : cmt a S = cmt a (fixV P.A') := by
  have hne : cmt a S ≠ ⊥ := by
    intro h
    have h1 : ∀ u ∈ S, a u = u := cmt_eq_bot_iff.1 h
    have h2 : S ≤ fixV P.A := fixes_of_simple_A P G.ha G.ha1 hS.2.1.1 h1
    apply hS.1
    rw [eq_bot_iff, ← G.inf_eq_bot]
    exact le_inf h2 hle
  exact PairData.eq_of_le_of_card_le_two (cmt_mono hle) hne (G.card_cmt_fixA' h168).le

end Structure

end CFSG.Quasithin.He7
