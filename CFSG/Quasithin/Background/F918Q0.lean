module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def commModSub (U : Subgroup V) (A : Subgroup (MulAut V)) (D : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ g ∈ A, g u * u⁻¹ ∈ D}
  one_mem' := ⟨U.one_mem, fun g _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
    refine ⟨U.mul_mem haU hbU, fun g hg => ?_⟩
    have e : g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
      rw [map_mul]; simp only [mul_inv_rev]; ac_rfl
    rw [e]
    exact D.mul_mem (ha g hg) (hb g hg)
  inv_mem' := by
    rintro a ⟨haU, ha⟩
    refine ⟨U.inv_mem haU, fun g hg => ?_⟩
    have e : g a⁻¹ * (a⁻¹)⁻¹ = (g a * a⁻¹)⁻¹ := by
      rw [map_inv]; simp only [inv_inv, mul_inv_rev]; ac_rfl
    rw [e]
    exact D.inv_mem (ha g hg)

theorem mem_commModSub {U D : Subgroup V} {A : Subgroup (MulAut V)} {u : V} :
    u ∈ commModSub U A D ↔ u ∈ U ∧ ∀ g ∈ A, g u * u⁻¹ ∈ D := Iff.rfl

theorem commModSub_le (U : Subgroup V) (A : Subgroup (MulAut V)) (D : Subgroup V) :
    commModSub U A D ≤ U := fun _ h => h.1


theorem map_mem_map_of_comm {U : Subgroup V} {a g : MulAut V} (hc : g * a = a * g)
    (hg : ∀ u ∈ U, g u ∈ U) : ∀ v ∈ U.map a.toMonoidHom, g v ∈ U.map a.toMonoidHom := by
  rintro v ⟨u, hu, rfl⟩
  refine ⟨g u, hg u hu, ?_⟩
  have := congrArg (fun φ : MulAut V => φ u) hc
  simpa using this.symm

theorem stab_map_of_comm {U : Subgroup V} {a g : MulAut V} (hc : g * a = a * g)
    (hg : g ∈ stabSub U) : g ∈ stabSub (U.map a.toMonoidHom) := by
  have hc' : g⁻¹ * a = a * g⁻¹ := by
    have := congrArg (fun φ : MulAut V => g⁻¹ * φ * g⁻¹) hc
    simpa [mul_assoc] using this.symm
  have hg' : g⁻¹ ∈ stabSub U := (stabSub U).inv_mem hg
  intro v
  constructor
  · intro h
    have := map_mem_map_of_comm hc' (fun u hu => (hg' u).mpr hu) (g v) h
    simpa using this
  · exact map_mem_map_of_comm hc (fun u hu => (hg u).mpr hu) v

section Main

variable [Finite V]

omit [Finite V] in
theorem rk_map_aut_eq (U : Subgroup V) (a : MulAut V) : rk ↥(U.map a.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective a.injective]

theorem rk_fixV_swap_le {U : Subgroup V} {a : MulAut V} {A₀ : Subgroup (MulAut V)}
    (ha : a * a = 1) (hcomm : ∀ g ∈ A₀, g * a = a * g) (hstab : A₀ ≤ stabSub U)
    (hsum : U ⊔ U.map a.toMonoidHom = ⊤) :
    rk ↥(fixV A₀ ⊓ fixV (Subgroup.zpowers a)) + rk ↥(U ⊓ U.map a.toMonoidHom) ≤
      rk ↥((U ⊓ U.map a.toMonoidHom) ⊓ fixV A₀) +
        rk ↥(commModSub U A₀ (U ⊓ U.map a.toMonoidHom)) := by
  set aU := U.map a.toMonoidHom with haU_def
  set D := U ⊓ aU with hD_def
  set F := fixV A₀ ⊓ fixV (Subgroup.zpowers a) with hF_def
  set Uh := commModSub U A₀ D with hUh_def
  have hstab2 : ∀ g ∈ A₀, g ∈ stabSub aU := fun g hg => stab_map_of_comm (hcomm g hg) (hstab hg)
  have c1 : F ≤ Uh ⊔ aU := by
    intro x hx
    have hxY : x ∈ U ⊔ aU := by rw [hsum]; exact Subgroup.mem_top x
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hxY
    refine Subgroup.mul_mem_sup ?_ hw
    refine ⟨hu, fun g hg => ?_⟩
    have hfix : g (u * w) = u * w := hx.1 g hg
    rw [map_mul] at hfix
    have hgu : g u ∈ U := (hstab hg u).mpr hu
    have hgw : g w ∈ aU := (hstab2 g hg w).mpr hw
    refine ⟨U.mul_mem hgu (U.inv_mem hu), ?_⟩
    have h1 : (g u * u⁻¹) * (g w * w⁻¹) = 1 := by
      calc (g u * u⁻¹) * (g w * w⁻¹) = (g u * g w) * (u⁻¹ * w⁻¹) := mul_mul_mul_comm _ _ _ _
        _ = (u * w) * (u⁻¹ * w⁻¹) := by rw [hfix]
        _ = 1 := by rw [mul_mul_mul_comm]; simp
    have h2 : g u * u⁻¹ = (g w * w⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact aU.inv_mem (aU.mul_mem hgw (aU.inv_mem hw))
  have c2 : F ⊓ aU ≤ D ⊓ fixV A₀ := by
    rintro x ⟨hxF, hxa⟩
    have hxa' : x ∈ aU := hxa
    obtain ⟨u', hu', hx⟩ := hxa
    have hfa : a x = x := hxF.2 a (Subgroup.mem_zpowers a)
    have h3 : a x = u' := by
      rw [← hx]
      have := congrArg (fun φ : MulAut V => φ u') ha
      simpa using this
    refine ⟨⟨?_, hxa'⟩, hxF.1⟩
    rw [← hfa, h3]; exact hu'
  have hDinv : ∀ g ∈ A₀, ∀ x ∈ D, g x ∈ D := fun g hg x hx =>
    ⟨(hstab hg x).mpr hx.1, (hstab2 g hg x).mpr hx.2⟩
  have c3 : Uh ⊓ aU = D := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨⟨hx.1, fun g hg => D.mul_mem (hDinv g hg x hx) (D.inv_mem hx)⟩, hx.2⟩
  have h1 := rk_sup_add_rk_inf F aU
  have h2 := rk_sup_add_rk_inf Uh aU
  have h3 : rk ↥(F ⊔ aU) ≤ rk ↥(Uh ⊔ aU) := rk_mono (sup_le c1 le_sup_right)
  have h4 : rk ↥(F ⊓ aU) ≤ rk ↥(D ⊓ fixV A₀) := rk_mono c2
  rw [c3] at h2
  omega

theorem rk_sup_swap_add_rk_inf {U : Subgroup V} {a : MulAut V}
    (hsum : U ⊔ U.map a.toMonoidHom = ⊤) :
    rk V + rk ↥(U ⊓ U.map a.toMonoidHom) = 2 * rk ↥U := by
  have h := rk_sup_add_rk_inf U (U.map a.toMonoidHom)
  rw [hsum, rk_top, rk_map_aut_eq] at h
  omega

theorem exists_complement_of_isElemAbelian2 {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) {g : MulAut V}
    (hg : g ∈ A) (hg1 : g ≠ 1) :
    ∃ A₁ : Subgroup (MulAut V), A₁ ≤ A ∧ g ∉ A₁ ∧ A₁ ⊔ Subgroup.zpowers g = A := by
  let S : Set (Subgroup (MulAut V)) := {B | B ≤ A ∧ g ∉ B}
  have hS : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨⊥, bot_le, by simpa using hg1⟩
  obtain ⟨A₁, ⟨hA₁le, hgA₁⟩, hmax⟩ := Set.Finite.exists_maximalFor (fun B => B) S hS hne
  have hsq : ∀ y ∈ A, y * y = 1 := fun y hy => by simpa [pow_two] using hA.2 y hy
  refine ⟨A₁, hA₁le, hgA₁, le_antisymm (sup_le hA₁le (Subgroup.zpowers_le.mpr hg)) ?_⟩
  intro x hx
  by_cases hxA₁ : x ∈ A₁
  · exact Subgroup.mem_sup_left hxA₁
  ·
    let B : Subgroup (MulAut V) :=
      { carrier := {y | y ∈ A₁ ∨ ∃ a ∈ A₁, y = a * x}
        one_mem' := Or.inl A₁.one_mem
        mul_mem' := by
          rintro y z (hy | ⟨a, ha, rfl⟩) (hz | ⟨b, hb, rfl⟩)
          · exact Or.inl (A₁.mul_mem hy hz)
          · exact Or.inr ⟨y * b, A₁.mul_mem hy hb, by simp [mul_assoc]⟩
          · refine Or.inr ⟨a * z, A₁.mul_mem ha hz, ?_⟩
            rw [mul_assoc, hA.1 x hx z (hA₁le hz), mul_assoc]
          · refine Or.inl ?_
            have : a * x * (b * x) = (a * b) * (x * x) := by
              rw [mul_assoc, ← mul_assoc x b x, hA.1 x hx b (hA₁le hb), mul_assoc b x x,
                ← mul_assoc a b (x * x)]
            rw [this, hsq x hx, mul_one]
            exact A₁.mul_mem ha hb
        inv_mem' := by
          rintro y (hy | ⟨a, ha, rfl⟩)
          · exact Or.inl (A₁.inv_mem hy)
          · refine Or.inr ⟨a⁻¹, A₁.inv_mem ha, ?_⟩
            have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
            rw [mul_inv_rev, hxi]
            exact hA.1 x hx a⁻¹ (A.inv_mem (hA₁le ha)) }
    have hBA : B ≤ A := by
      rintro y (hy | ⟨a, ha, rfl⟩)
      · exact hA₁le hy
      · exact A.mul_mem (hA₁le ha) hx
    have hA₁B : A₁ ≤ B := fun y hy => Or.inl hy
    have hxB : x ∈ B := Or.inr ⟨1, A₁.one_mem, by simp⟩
    have hgB : g ∈ B := by
      by_contra hgB
      have := hmax (j := B) ⟨hBA, hgB⟩ hA₁B
      exact hxA₁ (this hxB)
    rcases hgB with hgA | ⟨a, ha, hga⟩
    · exact absurd hgA hgA₁
    ·
      have hxe : x = a⁻¹ * g := by rw [hga]; group
      rw [hxe]
      exact Subgroup.mul_mem_sup (A₁.inv_mem ha) (Subgroup.mem_zpowers g)


omit [Finite V] in
theorem mem_fixV_zpowers_iff_apply_eq {g : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite V] in
theorem fixV_sup_eq_inf_fixV (A B : Subgroup (MulAut V)) : fixV (A ⊔ B) = fixV A ⊓ fixV B :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq A B


theorem rk_lt_of_lt_isElemAbelian2 {A₁ A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) (h : A₁ < A) :
    rk ↥A₁ < rk ↥A := by
  have hA₁ : IsElemAbelian2 A₁ :=
    ⟨fun a ha b hb => hA.1 a (h.le ha) b (h.le hb), fun a ha => hA.2 a (h.le ha)⟩
  have h1 := card_eq_two_pow_of_isPGroup hA₁.isPGroup
  have h2 := card_eq_two_pow_of_isPGroup hA.isPGroup
  have hlt : Nat.card ↥A₁ < Nat.card ↥A := by
    by_contra hge
    push Not at hge
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hge)
  rw [h1, h2] at hlt
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt

theorem rk_commModSub_le {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) {U D : Subgroup V}
    (hDU : D ≤ U) :
    rk ↥(commModSub U A D) ≤ rk ↥(U ⊓ fixV A) + rk ↥A * rk ↥D := by
  induction' hn : rk ↥A using Nat.strong_induction_on with n ih generalizing A U D
  by_cases hA1 : A = ⊥
  · subst hA1
    have h1 : commModSub U ⊥ D = U := by
      ext u; simp [mem_commModSub]
    have h2 : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      ext v; simp [mem_fixV]
    have hn0 : n = 0 := by rw [← hn]; exact rk_bot
    rw [h1, h2, hn0, inf_top_eq]
    simp
  · obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have hgA : (g : MulAut V) ∈ A := g.2
    have hg1' : (g : MulAut V) ≠ 1 := fun h => hg1 (Subtype.ext h)
    obtain ⟨A₁, hA₁le, hgA₁, hA₁g⟩ := exists_complement_of_isElemAbelian2 hA hgA hg1'
    set gg : MulAut V := (g : MulAut V) with hgg
    have hA₁ : IsElemAbelian2 A₁ :=
      ⟨fun a ha b hb => hA.1 a (hA₁le ha) b (hA₁le hb), fun a ha => hA.2 a (hA₁le ha)⟩
    have hlt : rk ↥A₁ < n := hn ▸ rk_lt_of_lt_isElemAbelian2 hA (lt_of_le_of_ne hA₁le (fun h => hgA₁ (h ▸ hgA)))
    set U' : Subgroup V := U ⊓ fixV (Subgroup.zpowers gg) with hU'
    set D' : Subgroup V := D ⊓ U' with hD'
    have hD'U' : D' ≤ U' := inf_le_right
    have IH := ih (rk ↥A₁) hlt hA₁ hD'U' rfl
    set W : Subgroup V := commModSub U A₁ D ⊓ commModSub U (Subgroup.zpowers gg) D with hW
    have hatW : commModSub U A D ≤ W := fun u hu =>
      ⟨⟨hu.1, fun x hx => hu.2 x (hA₁le hx)⟩,
        ⟨hu.1, fun x hx => hu.2 x (Subgroup.zpowers_le.mpr hgA hx)⟩⟩
    let φ : ↥W →* ↥D :=
      MonoidHom.mk' (fun u => ⟨gg u.1 * (u.1)⁻¹, u.2.2.2 gg (Subgroup.mem_zpowers gg)⟩) (by
        intro u v
        apply Subtype.ext
        show gg ((u * v : ↥W) : V) * ((u * v : ↥W) : V)⁻¹ = (gg u.1 * (u.1)⁻¹) * (gg v.1 * (v.1)⁻¹)
        have e : ((u * v : ↥W) : V) = u.1 * v.1 := rfl
        rw [e, map_mul, mul_inv_rev, mul_comm ((v : V)⁻¹) ((u : V)⁻¹)]
        exact (mul_mul_mul_comm _ _ _ _).symm)
    have hker : φ.ker = (W ⊓ fixV (Subgroup.zpowers gg)).subgroupOf W := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h' : gg (u : V) * (u : V)⁻¹ = 1 := congrArg Subtype.val h
        exact ⟨u.2, mem_fixV_zpowers_iff_apply_eq.mpr (mul_inv_eq_one.mp h')⟩
      · rintro ⟨-, h⟩
        apply Subtype.ext
        show gg (u : V) * (u : V)⁻¹ = 1
        rw [mul_inv_eq_one]
        exact mem_fixV_zpowers_iff_apply_eq.mp h
    have hKW : W ⊓ fixV (Subgroup.zpowers gg) ≤ W := inf_le_left
    have hrkker : rk ↥φ.ker = rk ↥(W ⊓ fixV (Subgroup.zpowers gg)) := by
      unfold rk
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv]
    have hcardW : Nat.card ↥W = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
      rw [← Subgroup.index_ker φ]
      exact (Subgroup.card_mul_index φ.ker).symm
    have hrkW : rk ↥W = rk ↥φ.ker + rk ↥φ.range := by
      unfold rk
      rw [hcardW, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
    have hrange : rk ↥φ.range ≤ rk ↥D := (rk_mono (le_top (a := φ.range))).trans (le_of_eq rk_top)
    have hfixg : ∀ {h : MulAut V}, h ∈ A → ∀ {u : V}, gg u = u → gg (h u * u⁻¹) = h u * u⁻¹ := by
      intro h hh u hu
      have hc := congrArg (fun φ : MulAut V => φ u) (hA.1 h hh gg hgA)
      simp only [MulAut.mul_apply] at hc
      rw [map_mul, map_inv, hu, ← hc, hu]
    have hK : W ⊓ fixV (Subgroup.zpowers gg) = commModSub U' A₁ D' := by
      ext u
      constructor
      · rintro ⟨⟨⟨huU, hu1⟩, -⟩, hfix⟩
        have hgu : gg u = u := mem_fixV_zpowers_iff_apply_eq.mp hfix
        refine ⟨⟨huU, hfix⟩, fun h hh => ⟨hu1 h hh, ?_⟩⟩
        exact ⟨hDU (hu1 h hh), mem_fixV_zpowers_iff_apply_eq.mpr (hfixg (hA₁le hh) hgu)⟩
      · rintro ⟨⟨huU, hfix⟩, hu1⟩
        refine ⟨⟨⟨huU, fun h hh => (hu1 h hh).1⟩, ⟨huU, fun x hx => ?_⟩⟩, hfix⟩
        have : x u = u := hfix x hx
        rw [this]; simp
    have hfixA : fixV A = fixV A₁ ⊓ fixV (Subgroup.zpowers gg) := by
      rw [← hA₁g, fixV_sup_eq_inf_fixV]
    have hU'fix : U' ⊓ fixV A₁ = U ⊓ fixV A := by
      rw [hfixA, hU', inf_right_comm, inf_assoc]
    have hD'D : rk ↥D' ≤ rk ↥D := rk_mono inf_le_left
    have hhatW : rk ↥(commModSub U A D) ≤ rk ↥W := rk_mono hatW
    have hKrk : rk ↥(W ⊓ fixV (Subgroup.zpowers gg)) ≤
        rk ↥(U ⊓ fixV A) + rk ↥A₁ * rk ↥D' := by
      rw [hK, ← hU'fix]
      exact IH
    have hmul : rk ↥A₁ * rk ↥D' ≤ rk ↥A₁ * rk ↥D := Nat.mul_le_mul_left _ hD'D
    have hfin : (rk ↥A₁ + 1) * rk ↥D ≤ n * rk ↥D := Nat.mul_le_mul_right _ hlt
    have hexp : (rk ↥A₁ + 1) * rk ↥D = rk ↥A₁ * rk ↥D + rk ↥D := by ring
    calc rk ↥(commModSub U A D) ≤ rk ↥W := hhatW
      _ = rk ↥φ.ker + rk ↥φ.range := hrkW
      _ ≤ rk ↥(W ⊓ fixV (Subgroup.zpowers gg)) + rk ↥D := by rw [hrkker]; exact Nat.add_le_add_left hrange _
      _ ≤ rk ↥(U ⊓ fixV A) + rk ↥A₁ * rk ↥D' + rk ↥D := Nat.add_le_add_right hKrk _
      _ ≤ rk ↥(U ⊓ fixV A) + rk ↥A₁ * rk ↥D + rk ↥D := by
          exact Nat.add_le_add_right (Nat.add_le_add_left hmul _) _
      _ = rk ↥(U ⊓ fixV A) + (rk ↥A₁ + 1) * rk ↥D := by rw [hexp]; ring
      _ ≤ rk ↥(U ⊓ fixV A) + n * rk ↥D := Nat.add_le_add_left hfin _


theorem swap_rank_bound (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {a : MulAut V}
    {A₀ : Subgroup (MulAut V)} (hA₀ : IsElemAbelian2 A₀)
    (ha : a * a = 1) (hcomm : ∀ g ∈ A₀, g * a = a * g) (hstab : A₀ ≤ stabSub U)
    (hsum : U ⊔ U.map a.toMonoidHom = ⊤)
    (hfaith : ∀ g ∈ A₀, (∀ u ∈ U, g u * u⁻¹ ∈ U ⊓ U.map a.toMonoidHom) → g = 1)
    (hD : rk ↥(U ⊓ U.map a.toMonoidHom) ≤ 1)
    (h3 : rk ↥(U ⊓ U.map a.toMonoidHom) + 2 < rk ↥U)
    (hA : rk V ≤ rk ↥(fixV A₀ ⊓ fixV (Subgroup.zpowers a)) + 2 * (rk ↥A₀ + 1)) :
    A₀ ≠ ⊥ ∧ rk ↥U ≤ rk ↥(U ⊓ fixV A₀) + 2 * rk ↥A₀ := by
  set aU := U.map a.toMonoidHom with haU
  set D := U ⊓ aU with hDdef
  have h1 : rk ↥(fixV A₀ ⊓ fixV (Subgroup.zpowers a)) + rk ↥D ≤
      rk ↥(D ⊓ fixV A₀) + rk ↥(commModSub U A₀ D) := rk_fixV_swap_le ha hcomm hstab hsum
  have h2 : rk V + rk ↥D = 2 * rk ↥U := rk_sup_swap_add_rk_inf hsum
  have h4 : rk ↥(D ⊓ fixV A₀) ≤ rk ↥(U ⊓ fixV A₀) := rk_mono (inf_le_inf_right _ inf_le_left)
  have h4' : rk ↥(D ⊓ fixV A₀) ≤ rk ↥D := rk_mono inf_le_left
  have hhat : commModSub U A₀ D ≤ U := commModSub_le U A₀ D
  have hrkhat : rk ↥(commModSub U A₀ D) ≤ rk ↥U := rk_mono hhat
  by_cases hbot : A₀ = ⊥
  · exfalso
    have hh : commModSub U A₀ D = U := by
      ext u
      constructor
      · exact fun h => h.1
      · intro hu
        refine ⟨hu, fun g hg => ?_⟩
        rw [hbot, Subgroup.mem_bot] at hg
        subst hg
        simp
    have hb0 : rk ↥A₀ = 0 := by rw [hbot]; exact rk_bot
    rw [hh] at h1
    omega
  · refine ⟨hbot, ?_⟩
    have hb : 1 ≤ rk ↥A₀ := hA₀.rk_pos hbot
    have hlt : rk ↥(commModSub U A₀ D) < rk ↥U := by
      by_contra hge
      push Not at hge
      have heq : commModSub U A₀ D = U := eq_of_le_of_rk_le hV hhat hge
      apply hbot
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact hfaith g hg fun u hu => (show u ∈ commModSub U A₀ D by rw [heq]; exact hu).2 g hg
    have hL2 := rk_commModSub_le hA₀ (U := U) (D := D) inf_le_left
    have hmulD : rk ↥A₀ * rk ↥D ≤ rk ↥A₀ := by
      calc rk ↥A₀ * rk ↥D ≤ rk ↥A₀ * 1 := Nat.mul_le_mul_left _ hD
        _ = rk ↥A₀ := mul_one _
    have hL2' : rk ↥(commModSub U A₀ D) ≤ rk ↥(U ⊓ fixV A₀) + rk ↥A₀ :=
      hL2.trans (Nat.add_le_add_left hmulD _)
    omega

end Main

end CFSG.Quasithin
