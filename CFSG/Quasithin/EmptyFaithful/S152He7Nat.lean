module

public import CFSG.Quasithin.EmptyFaithful.S152He7Tensor
public import CFSG.Quasithin.EmptyFaithful.S152He7TransB42
public import CFSG.Quasithin.Background.FFC2Ident

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He6 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
  CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

section NatB42

variable {V : Type} [CommGroup V] [Finite V]

theorem b4Hyp_of_simple {Λ : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥Λ)
    (hnc : ∃ a b : ↥Λ, a * b ≠ b * a) (hnot2 : ¬ IsPGroup 2 ↥Λ) (hSQ : SQTKGroup ↥Λ)
    (hirr : ∀ U : Subgroup V, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : (⊤ : Subgroup V) ≠ ⊥) : B4Hyp Λ Λ := by
  have hperf : Group.IsPerfect ↥Λ := isPerfect_of_simple_noncomm hnc
  have hq : CFSG.IsQuasisimple ↥Λ := LRed5.isQuasisimple_of_simple_nonabelian hperf hnc
  have hqo : CFSG.Open.IsQuasisimple ↥Λ := ⟨Group.isPerfect_def.1 hperf, hq.2.1⟩
  have hO2 : pCoreOf 2 Λ = ⊥ := pCoreOf_two_eq_bot_of_simple hs hnot2
  have hfst : quasithinGenFitting Λ = Λ :=
    InternalSec.quasithinGenFitting_eq_of_two_pow le_rfl
      (fun y hy l hl => Λ.mul_mem (Λ.mul_mem hy hl) (Λ.inv_mem hy)) hqo
      (fun y hy => ⟨0, by simpa using hy⟩) hO2
  have hirrΛ : XMod.IsIrrSec ↥Λ (⊥ : Subgroup V) ⊤ :=
    ⟨bot_lt_iff_ne_bot.2 hnt, fun J hJ _ _ => hirr J (fun l hl u hu => hJ ⟨l, hl⟩ u hu)⟩
  exact ⟨hSQ, hfst.symm, hq, hirrΛ⟩

theorem natural_of_transvection_168
    (hB42 : AsB42) (hV : ∀ v : V, v * v = 1) {Λ : Subgroup (MulAut V)}
    (hN : Nat.card ↥Λ = 168) (hs : IsSimpleGroup ↥Λ) (hSQ : SQTKGroup ↥Λ)
    (hirr : ∀ U : Subgroup V, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤)
    {ζ : MulAut V} (hζ : ζ ∈ Λ) (hζ1 : ζ ≠ 1) (hζi : (fixV (Subgroup.zpowers ζ)).index = 2) :
    ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) →* ↥Λ,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))).RealizesVia Λ ⊤ ⊥ π := by
  classical
  have := hs
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  have hnc : ∃ a b : ↥Λ, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥Λ := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥Λ)
    rw [hN] at hp
    norm_num at hp
  have hnot2 : ¬ IsPGroup 2 ↥Λ := by
    intro hp
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    have h3 : 3 ∣ Nat.card ↥Λ := by rw [hN]; norm_num
    rw [hm] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hnt : (⊤ : Subgroup V) ≠ ⊥ := fun h => hζ1 (MulEquiv.ext fun w => by
    have : w ∈ (⊥ : Subgroup V) := h ▸ Subgroup.mem_top w
    rw [Subgroup.mem_bot.1 this, map_one]
    rfl)
  have hb4 : B4Hyp Λ Λ := b4Hyp_of_simple hs hnc hnot2 hSQ hirr hnt
  obtain ⟨hA, hAcard⟩ := isFFStarOffender_of_transvection hV hζ hζ1 hζi
  have hffJ : ffJ Λ = Λ := by
    have hle : ffJ Λ ≤ Λ := EmptyFaithfulMultiple.FFL.ffJ_le Λ
    have hA' : Subgroup.zpowers ζ ≤ ffJ Λ := B19.le_ffJ hA
    rcases eq_bot_or_eq_of_normal' hs hle (fun g hg m hm =>
      (Subgroup.mem_normalizer_iff.mp (EmptyFaithfulMultiple.FFL.le_normalizer_ffJ Λ hg) m).mp hm)
      with h | h
    · exfalso
      apply hζ1
      have : ζ ∈ ffJ Λ := hA' (Subgroup.mem_zpowers ζ)
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exact h
  have hconcl := hB42 V hV2 Λ Λ hb4 _ hA
  have hIdent : AsB42Ident := FFC.asB42Ident_of_b42 hB42
  rcases B5.b42_cases hIdent hV2 hb4 hA hconcl with ⟨-, hpair, -⟩ | ⟨hne, -⟩
  · rcases LRed5.b42_cases (Or.inl hN) hpair with ⟨-, π, hπ⟩ | ⟨h360, -⟩
    · exact ⟨π, hπ⟩
    · omega
  · exact absurd hffJ hne

end NatB42

section Normalizer

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem conj_apply_eq (g h : MulAut W) (s : W) : h (g s) = g ((g⁻¹ * h * g) s) := by
  have : (g⁻¹ * h * g) s = g⁻¹ (h (g s)) := rfl
  rw [this]
  exact (MulAut.apply_inv_self W g _).symm

omit [Finite W] in
theorem IsMinK.map_of_conj (P : PairData W) {S : Subgroup W} (hS : IsMinK P S) {g : MulAut W}
    (hA : ∀ h ∈ P.A, g⁻¹ * h * g ∈ P.A) (hA' : ∀ h ∈ P.A', g⁻¹ * h * g ∈ P.A')
    (hA2 : ∀ h ∈ P.A, g * h * g⁻¹ ∈ P.A) (hA'2 : ∀ h ∈ P.A', g * h * g⁻¹ ∈ P.A') :
    IsMinK P (S.map (g : MulAut W).toMonoidHom) := by
  obtain ⟨hSne, ⟨hSA, hSA'⟩, hSmin⟩ := hS
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro h
    apply hSne
    rw [eq_bot_iff]
    intro u hu
    have : (g : MulAut W) u ∈ S.map (g : MulAut W).toMonoidHom := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact g.injective (this.trans (map_one g).symm)
  · rintro h hh _ ⟨s, hs, rfl⟩
    exact ⟨(g⁻¹ * h * g) s, hSA _ (hA h hh) s hs, (conj_apply_eq g h s).symm⟩
  · rintro h hh _ ⟨s, hs, rfl⟩
    exact ⟨(g⁻¹ * h * g) s, hSA' _ (hA' h hh) s hs, (conj_apply_eq g h s).symm⟩
  · intro T hTS hT
    set R : Subgroup W := T.map (g⁻¹ : MulAut W).toMonoidHom with hR
    have hRS : R ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨v, hv, hvy⟩ := hTS hy
      have : (g⁻¹ : MulAut W) y = v := by
        rw [← hvy]
        exact MulAut.inv_apply_self W g v
      show (g⁻¹ : MulAut W) y ∈ S
      rw [this]
      exact hv
    have hRK : KInv P R := by
      constructor
      · rintro h hh _ ⟨y, hy, rfl⟩
        refine ⟨(g * h * g⁻¹) y, hT.1 _ (hA2 h hh) y hy, ?_⟩
        have := conj_apply_eq g⁻¹ h y
        rw [inv_inv] at this
        exact this.symm
      · rintro h hh _ ⟨y, hy, rfl⟩
        refine ⟨(g * h * g⁻¹) y, hT.2 _ (hA'2 h hh) y hy, ?_⟩
        have := conj_apply_eq g⁻¹ h y
        rw [inv_inv] at this
        exact this.symm
    rcases hSmin R hRS hRK with h0 | h0
    · left
      rw [eq_bot_iff]
      intro y hy
      have : (g⁻¹ : MulAut W) y ∈ R := ⟨y, hy, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      have h2 : (g⁻¹ : MulAut W) y = (g⁻¹ : MulAut W) 1 := by rw [this, map_one]
      exact (g⁻¹ : MulAut W).injective h2
    · right
      refine le_antisymm hTS ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [← h0] at hv
      obtain ⟨y, hy, hyv⟩ := hv
      have : (g : MulAut W) v = y := by
        rw [← hyv]
        exact MulAut.apply_inv_self W g y
      show (g : MulAut W) v ∈ T
      rw [this]
      exact hy

theorem GoodPair.invariant_of_normalizes {P : PairData W} {a a' : MulAut W} (G : GoodPair P a a')
    (h168 : Nat.card ↥P.A = 168) {S : Subgroup W} (hS : IsMinK P S) (hle : S ≤ fixV P.A')
    {g : MulAut W} (hg : g ∈ P.Xb) (hgA : ∀ x, x ∈ P.A ↔ g * x * g⁻¹ ∈ P.A) :
    ∀ u ∈ S, g u ∈ S := by
  have hgA' : ∀ x, x ∈ P.A' ↔ g * x * g⁻¹ ∈ P.A' := by
    rcases P.norm g hg with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exfalso
      apply ne_bot_of_simple P.simpA
      rw [eq_bot_iff]
      intro x hx
      have h3 : g * x * g⁻¹ ∈ P.A ⊓ P.A' := ⟨(hgA x).1 hx, (h1 x).1 hx⟩
      rw [P.inf_eq_bot, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_bot]
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
  have hc : ∀ {B : Subgroup (MulAut W)} (hB : ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B) (h : MulAut W),
      h ∈ B → g⁻¹ * h * g ∈ B := by
    intro B hB h hh
    rw [hB]
    have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rw [this]
    exact hh
  have hmin := hS.map_of_conj P (fun h hh => hc hgA h hh) (fun h hh => hc hgA' h hh)
    (fun h hh => (hgA h).1 hh) (fun h hh => (hgA' h).1 hh)
  set gS : Subgroup W := S.map (g : MulAut W).toMonoidHom with hgS
  have hgSle : gS ≤ fixV P.A' := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_fixV]
    intro h hh
    have h1 := conj_apply_eq g h s
    change h (g s) = g s
    rw [h1, mem_fixV.1 (hle hs) _ (hc hgA' h hh)]
  have hc1 := G.cmt_eq_of_isMinK h168 hS hle
  have hc2 := G.cmt_eq_of_isMinK h168 hmin hgSle
  have hne : cmt a (fixV P.A') ≠ ⊥ := by
    intro h
    have := G.card_cmt_fixA' h168
    rw [h] at this
    simp at this
  have hcS : cmt a (fixV P.A') ≤ S := by
    rw [← hc1]
    exact cmt_le_of_invariant fun u hu => hS.2.1.1 a G.ha u hu
  have hcgS : cmt a (fixV P.A') ≤ gS := by
    rw [← hc2]
    exact cmt_le_of_invariant fun u hu => hmin.2.1.1 a G.ha u hu
  have hI : S ⊓ gS = S := by
    rcases hS.2.2 (S ⊓ gS) inf_le_left
        ⟨fun h hh u hu => ⟨hS.2.1.1 h hh u hu.1, hmin.2.1.1 h hh u hu.2⟩,
          fun h hh u hu => ⟨hS.2.1.2 h hh u hu.1, hmin.2.1.2 h hh u hu.2⟩⟩ with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ S ⊓ gS := ⟨hcS hv, hcgS hv⟩
      rwa [h] at this
    · exact h
  have hSgS : S ≤ gS := by
    rw [← hI]
    exact inf_le_right
  have hcard : Nat.card ↥gS ≤ Nat.card ↥S :=
    (Subgroup.card_map_of_injective (f := (g : MulAut W).toMonoidHom) g.injective).le
  have hEq : S = gS := Subgroup.eq_of_le_of_card_ge hSgS hcard
  intro u hu
  have : g u ∈ gS := ⟨u, hu, rfl⟩
  rwa [← hEq] at this

end Normalizer

section Assembly

variable {W : Type} [CommGroup W] [Finite W]

theorem noOuter_of_goodPair
    (hB42 : AsB42) (P : PairData W) (h168 : Nat.card ↥P.A = 168) (hSQ : SQTKGroup ↥P.Xb)
    (hAX : P.A ≤ P.Xb) {a a' : MulAut W} (G : GoodPair P a a') :
    ∀ g ∈ P.Xb, (∀ x, x ∈ P.A ↔ g * x * g⁻¹ ∈ P.A) →
      ∃ l ∈ P.A, ∀ x ∈ P.A, g * x * g⁻¹ = l * x * l⁻¹ := by
  classical
  intro g hg hgA
  obtain ⟨S, hSle, hS⟩ := exists_isMinK_le P (kInv_fixV_A' P) (G.fixA'_ne_bot h168)
  have hSA : ∀ h ∈ P.A, ∀ u ∈ S, h u ∈ S := hS.2.1.1
  have hst : P.A ≤ stabSub S := fun h hh u => by
    refine ⟨fun hu => ?_, fun hu => hSA h hh u hu⟩
    rw [← MulAut.inv_apply_self W h u]
    exact hSA h⁻¹ (P.A.inv_mem hh) _ hu
  have hfaith : ∀ h ∈ P.A, (∀ v ∈ S, h v = v) → h = 1 := by
    intro h hh hfix
    by_contra h1
    have h2 : S ≤ fixV P.A := fixes_of_simple_A P hh h1 hSA hfix
    apply hS.1
    rw [eq_bot_iff, ← G.inf_eq_bot]
    exact le_inf h2 hSle
  set Λ : Subgroup (MulAut ↥S) := autSub P.A S with hΛ
  obtain ⟨e, he⟩ : ∃ e : ↥P.A ≃* ↥Λ,
      ∀ (h : ↥P.A) (w : ↥S), S.subtype ((e h : MulAut ↥S) w) = (h : MulAut W) (S.subtype w) :=
    ⟨FFC.resEquiv hst hfaith, fun h w => by
      rw [FFC.resEquiv_apply hst hfaith h]
      exact FFC.resG_apply hst h w⟩
  have hsimp : IsSimpleGroup ↥Λ := by
    have := P.simpA
    exact e.symm.isSimpleGroup
  have hcardΛ : Nat.card ↥Λ = 168 := by
    rw [hΛ, FFC.card_autSub_eq hst hfaith]
    exact h168
  have hSQΛ : SQTKGroup ↥Λ := sqtkGroup_of_mulEquiv' e.symm (sqtkGroup_of_le hSQ hAX)
  have hirrΛ : ∀ U : Subgroup ↥S, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    set U' : Subgroup W := U.map S.subtype with hU'
    have hK : KInv P U' := by
      constructor
      · rintro h hh _ ⟨u, hu, rfl⟩
        have hmem : resHom S ⟨h, hst hh⟩ ∈ Λ := mem_autSub.mpr ⟨⟨h, hst hh⟩, hh, rfl⟩
        exact ⟨_, hU _ hmem u hu, rfl⟩
      · rintro h hh _ ⟨u, hu, rfl⟩
        have : h (u : W) = u := mem_fixV.1 (hSle u.2) h hh
        change h (u : W) ∈ U'
        rw [this]
        exact ⟨u, hu, rfl⟩
    have hU'S : U' ≤ S := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    rcases hS.2.2 U' hU'S hK with h0 | h0
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : W) ∈ U' := ⟨u, hu, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro u _
      have : (u : W) ∈ U' := by rw [h0]; exact u.2
      obtain ⟨u', hu', hu'u⟩ := this
      have : u' = u := Subtype.ext hu'u
      rw [← this]
      exact hu'
  have haS : a ∈ stabSub S := hst G.ha
  set ζ : MulAut ↥S := resHom S ⟨a, haS⟩ with hζ
  have hζΛ : ζ ∈ Λ := mem_autSub.mpr ⟨⟨a, haS⟩, G.ha, rfl⟩
  have hζi : (fixV (Subgroup.zpowers ζ)).index = 2 := by
    have h1 := index_restr_eq S a (hSA a G.ha) (hSA a⁻¹ (P.A.inv_mem G.ha))
    have h2 : restrAut S a (hSA a G.ha) (hSA a⁻¹ (P.A.inv_mem G.ha)) = ζ :=
      MulEquiv.ext fun u => rfl
    rw [h2] at h1
    rw [h1, G.cmt_eq_of_isMinK h168 hS hSle]
    exact G.card_cmt_fixA' h168
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot, CFSG.QuasithinUnique.Setup.X1.fixV_bot,
      Subgroup.index_top] at hζi
    omega
  have hWS : ∀ v : ↥S, v * v = 1 := fun v => Subtype.ext (P.hW v)
  obtain ⟨π, hπ⟩ := natural_of_transvection_168 hB42 hWS hcardΛ hsimp hSQΛ hirrΛ hζΛ hζ1 hζi
  have hπW := FFC.RealizesVia.transport (S.subtype) S.subtype_injective e he hπ
  have hTop : (⊤ : Subgroup ↥S).map S.subtype = S := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact s.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [hTop, Subgroup.map_bot] at hπW
  have hgS : ∀ u ∈ S, g u ∈ S := G.invariant_of_normalizes h168 hS hSle hg hgA
  have hgi : ∀ x, x ∈ P.A ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ P.A := by
    intro x
    rw [inv_inv]
    have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    constructor
    · intro hx
      exact (hgA (g⁻¹ * x * g)).2 (by rw [e1]; exact hx)
    · intro hx
      have := (hgA (g⁻¹ * x * g)).1 hx
      rwa [e1] at this
  have hgS' : ∀ u ∈ S, g⁻¹ u ∈ S := G.invariant_of_normalizes h168 hS hSle (P.Xb.inv_mem hg) hgi
  exact LRed5.inner_of_natural_section hπW hgS hgS'
    (fun z hz => by rw [Subgroup.mem_bot.1 hz, map_one]; exact Subgroup.one_mem _)
    (fun z hz => by rw [Subgroup.mem_bot.1 hz, map_one]; exact Subgroup.one_mem _)
    (fun l hl => (hgA l).1 hl)

end Assembly

end CFSG.Quasithin.He7
