module

public import CFSG.Quasithin.EmptyFaithful.SBd8SmallU33
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ord
public import CFSG.Quasithin.Background.SmithB51G2DExcl
public import CFSG.Quasithin.EmptyFaithful.LRed5Models
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FR

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.ComponentClassification.OuterAutomorphisms

section General

theorem isPGroup_outer_of_card_le_ch615 {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) (h : Nat.card (MulAut X) ≤ 2 * Nat.card X) :
    IsPGroup 2 (Outer X) := by
  have hker : (MulAut.conj : X →* MulAut X).ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have hcen : g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hc, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner X) = Nat.card X := by
    have e : X ≃* (MulAut.conj : X →* MulAut X).range :=
      MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).mp hker)
    exact (Nat.card_congr e.toEquiv).symm
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hq := (inner X).card_eq_card_quotient_mul_card_subgroup
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hprod : Nat.card (Outer X) * Nat.card X = Nat.card (MulAut X) := by rw [hq, hinn]
  have hle : Nat.card (Outer X) ≤ 2 :=
    Nat.le_of_mul_le_mul_right (hprod.trans_le h) hpos
  have hA : 0 < Nat.card (MulAut X) := Nat.card_pos
  have hne : Nat.card (Outer X) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; omega
  rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [h1]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [h1]; rfl)

theorem eq_or_eq_of_card_two_ch615 {α : Type*} {p : α → Prop} (h : Nat.card {a // p a} = 2)
    {a b c : α} (ha : p a) (hb : p b) (hc : p c) (hab : a ≠ b) : c = a ∨ c = b := by
  have h' : ({x | p x} : Set α).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact h
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.mp h'
  have ha' : a ∈ ({x, y} : Set α) := hs ▸ ha
  have hb' : b ∈ ({x, y} : Set α) := hs ▸ hb
  have hc' : c ∈ ({x, y} : Set α) := hs ▸ hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb' hc'
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hab

theorem normalizer_eq_of_lattice_ch615 {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    {S P P' : Subgroup X} (hlat : ∀ Y, S ≤ Y → Y = S ∨ Y = P ∨ Y = P' ∨ Y = ⊤) (hSP : S < P)
    (hP : P ≠ ⊤) (hPP' : P ≠ P') (hc : Nat.card ↥P = Nat.card ↥P') :
    Subgroup.normalizer (P : Set X) = P := by
  have hle : P ≤ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer
  rcases hlat _ (hSP.le.trans hle) with h | h | h | h
  · rw [h] at hle
    exact absurd hle (not_le_of_gt hSP)
  · exact h
  · rw [h] at hle
    exact absurd (Subgroup.eq_of_le_of_card_ge hle hc.symm.le) hPP'
  · rcases (Subgroup.normalizer_eq_top_iff.mp h).eq_bot_or_eq_top with h' | h'
    · rw [h'] at hSP
      exact absurd hSP (not_lt_bot)
    · exact absurd h' hP

@[expose] def resAct_ch615 {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ h : ↥H, ∀ w ∈ W, (h : MulAut V) w ∈ W) : ↥H →* MulAut ↥W where
  toFun h :=
    { toFun := fun w => ⟨(h : MulAut V) w, hW h w w.2⟩
      invFun := fun w => ⟨((h⁻¹ : ↥H) : MulAut V) w, hW h⁻¹ w w.2⟩
      left_inv := fun w => Subtype.ext (MulAut.inv_apply_self V (h : MulAut V) w)
      right_inv := fun w => Subtype.ext (MulAut.apply_inv_self V (h : MulAut V) w)
      map_mul' := fun a b => Subtype.ext (map_mul (h : MulAut V) (a : V) (b : V)) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl

theorem g2Derived_of_b51_ch615 {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (hc : Nat.card ↥L = 6048) (h : B51Part1 G L) :
    G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1 := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, ⟨hU, hU0⟩, h₁, h₂⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, hind, hsup, hreal⟩
  · exact U3.GC137.g2NaturalDerived_of_modulePair hc hB
  · exfalso
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at h1
    rcases LRed5.sl3_cases (EmptyFaithfulMultiple.FFL.one_le_of_card hK) with hm | hm
    · subst hm
      rw [hc] at h1
      norm_num at h1
    · omega
  · exfalso
    have h1 := card_eq_of_nat_realizes1527d h₁
    rcases hn with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at h1
      omega
    · rw [card_statedSL_five_zmod1527d] at h1
      omega
  · exfalso
    have h1 := card_eq_of_nat_realizes1527d (hreal ⟨0, hk1⟩)
    rcases hn with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at h1
      omega
    · rw [card_statedSL_five_zmod1527d] at h1
      omega

theorem isSylowTwoOf_subgroupOf_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {S F : Subgroup Γ}
    (hS : IsSylowTwoOf S F) : IsSylowTwoOf (S.subgroupOf F) ⊤ := by
  have := isSylowTwoOf_map_ch615 (MulEquiv.refl ↥F) hS
  have e1 : (S.subgroupOf F).map (MulEquiv.refl ↥F).toMonoidHom = S.subgroupOf F := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  rwa [e1] at this

theorem fix_or_fix_of_trio_ch615 {V : Type} [CommGroup V] [Finite V]
    {F : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥F) (hns : ¬ Group.IsSolvable ↥F)
    (hcard : Nat.card ↥F = 6048) (hV2 : ∀ v : V, v * v = 1) (hfix : fixV F = ⊥)
    {W : Subgroup V} (hW : ∀ h : ↥F, ∀ w ∈ W, (h : MulAut V) w ∈ W) (h64 : Nat.card ↥W = 64)
    {S : Subgroup (MulAut V)} (hS₀ : IsSylowTwoOf (S.subgroupOf F) ⊤)
    (htr : ∀ w, (∀ s ∈ S, s w = w) → w ∈ W) (htrio : SBd8.TrioShape ↥F (S.subgroupOf F))
    {R₁ R₂ : Subgroup (MulAut V)} (h1S : S ≤ R₁) (h1F : R₁ ≤ F) (h1ne : R₁ ≠ S)
    (h1s : Group.IsSolvable ↥R₁) (h2S : S ≤ R₂) (h2F : R₂ ≤ F) (h2ne : R₂ ≠ S)
    (h2s : Group.IsSolvable ↥R₂) (hne : R₁ ≠ R₂) :
    (∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R₁, x w = w) ∨
      (∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R₂, x w = w) := by
  classical
  obtain ⟨-, P₀, P₁, h01, h0t, h1t, h0lt, h1lt, hc0, hc1, hlat⟩ := htrio
  set S₀ := S.subgroupOf F with hS₀def
  set ψ : ↥F →* MulAut ↥W := resAct_ch615 F W hW with hψ
  have hW2 : ∀ v : ↥W, v * v = 1 := fun v => Subtype.ext (hV2 v)
  have hnofix : ∀ v : ↥W, (∀ x, ψ x v = v) → v = 1 := by
    intro v hv
    have hv' : (v : V) ∈ fixV F := by
      show ∀ x ∈ F, x v = v
      intro x hx
      exact congrArg Subtype.val (hv ⟨x, hx⟩)
    rw [hfix] at hv'
    exact Subtype.ext (Subgroup.mem_bot.mp hv')
  have hS32 : Nat.card ↥S₀ = 32 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS₀.2.1
    have hidx := hS₀.2.2
    rw [show (S₀.subgroupOf ⊤).index = S₀.index from Subgroup.relIndex_top_right _] at hidx
    have hmul := Subgroup.card_mul_index S₀
    rw [hk, hcard] at hmul
    have hk13 : k < 13 := by
      by_contra hk'
      have h13 : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S₀.index := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hmul
        omega
      have : 2 ^ 13 * 1 ≤ 2 ^ k * S₀.index := Nat.mul_le_mul h13 hpos
      omega
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  have hidxS : S₀.index = 189 := by
    have hmul := Subgroup.card_mul_index S₀
    rw [hS32, hcard] at hmul
    omega
  have hidx0 : P₀.index = 63 := by
    have hmul := Subgroup.card_mul_index P₀
    rw [hc0, hS32, hcard] at hmul
    omega
  have hidx1 : P₁.index = 63 := by
    have hmul := Subgroup.card_mul_index P₁
    rw [hc1, hS32, hcard] at hmul
    omega
  have hn0 : Subgroup.normalizer (P₀ : Set ↥F) = P₀ :=
    normalizer_eq_of_lattice_ch615 hlat h0lt h0t h01 (by rw [hc0, hc1])
  have hn1 : Subgroup.normalizer (P₁ : Set ↥F) = P₁ :=
    normalizer_eq_of_lattice_ch615 (S := S₀) (P' := P₀)
      (fun Y hY => by rcases hlat Y hY with h | h | h | h <;> tauto) h1lt h1t (Ne.symm h01)
      (by rw [hc0, hc1])
  have hcard2 := U3.fixed_card_two_of_lattice hW2 h64 ψ hnofix hS₀.2.1
    (by rw [hidxS]; norm_num) hlat hidx0 hidx1 hn0 hn1
  have hRcases : ∀ R : Subgroup (MulAut V), S ≤ R → R ≤ F → R ≠ S → Group.IsSolvable ↥R →
      R.subgroupOf F = P₀ ∨ R.subgroupOf F = P₁ := by
    intro R hSR hRF hRS hRs
    have hle : S₀ ≤ R.subgroupOf F := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hSR (Subgroup.mem_subgroupOf.mp hx))
    rcases hlat _ hle with h | h | h | h
    · exfalso
      apply hRS
      have hSF : S ≤ F := fun x hx => hRF (hSR hx)
      rw [hS₀def, Subgroup.subgroupOf_inj, inf_eq_left.mpr hRF, inf_eq_left.mpr hSF] at h
      exact h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hFR : F ≤ R := fun x hx => by
        have : (⟨x, hx⟩ : ↥F) ∈ R.subgroupOf F := by
          rw [h]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      rw [le_antisymm hRF hFR] at hRs
      exact hns hRs
  have hRinj : R₁.subgroupOf F = R₂.subgroupOf F → R₁ = R₂ := fun h => by
    rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr h1F, inf_eq_left.mpr h2F] at h
  by_cases hex : ∃ v : ↥W, v ≠ 1 ∧ ∀ s ∈ S₀, ψ s v = v
  · obtain ⟨v₀, hv₀1, hv₀S⟩ := hex
    have huniq : ∀ v : ↥W, (∀ s ∈ S₀, ψ s v = v) → v = 1 ∨ v = v₀ := fun v hv =>
      eq_or_eq_of_card_two_ch615 hcard2 (fun s _ => map_one _) hv₀S hv (Ne.symm hv₀1)
    obtain ⟨hstab, -⟩ := U3.stab_orbit_of_lattice h64 ψ hnofix (by rw [hidxS]; norm_num) hlat
      hidx0 hidx1 hv₀1 hv₀S
    have hfixR : ∀ R : Subgroup (MulAut V), R ≤ F →
        (∀ x : ↥F, ψ x v₀ = v₀ ↔ x ∈ R.subgroupOf F) →
        ∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R, x w = w := by
      intro R hRF hRv w hw x hx
      have hwW := htr w hw
      rcases huniq ⟨w, hwW⟩ (fun s hs => Subtype.ext (hw s.1 (Subgroup.mem_subgroupOf.mp hs)))
        with h | h
      · have hw1 : w = 1 := congrArg Subtype.val h
        rw [hw1, map_one]
      · have h2 : ψ ⟨x, hRF hx⟩ v₀ = v₀ :=
          (hRv ⟨x, hRF hx⟩).mpr (Subgroup.mem_subgroupOf.mpr hx)
        have h3 : ψ ⟨x, hRF hx⟩ ⟨w, hwW⟩ = ⟨w, hwW⟩ := by
          rw [h]
          exact h2
        exact congrArg Subtype.val h3
    rcases hRcases R₁ h1S h1F h1ne h1s with ha | ha <;>
      rcases hRcases R₂ h2S h2F h2ne h2s with hb | hb
    · exact absurd (hRinj (ha.trans hb.symm)) hne
    · rcases hstab with hst | hst
      · exact Or.inl (hfixR R₁ h1F fun x => by rw [ha]; exact hst x)
      · exact Or.inr (hfixR R₂ h2F fun x => by rw [hb]; exact hst x)
    · rcases hstab with hst | hst
      · exact Or.inr (hfixR R₂ h2F fun x => by rw [hb]; exact hst x)
      · exact Or.inl (hfixR R₁ h1F fun x => by rw [ha]; exact hst x)
    · exact absurd (hRinj (ha.trans hb.symm)) hne
  ·
    left
    intro w hw x _
    have hwW := htr w hw
    have h1' : (⟨w, hwW⟩ : ↥W) = 1 := by
      by_contra hne1
      exact hex ⟨⟨w, hwW⟩, hne1, fun s hs =>
        Subtype.ext (hw s.1 (Subgroup.mem_subgroupOf.mp hs))⟩
    have hw1 : w = 1 := congrArg Subtype.val h1'
    rw [hw1, map_one]

end General

section U33

theorem isPGroup_outer_u33_ch615 :
    IsPGroup 2 (Outer U33G) :=
  isPGroup_outer_of_card_le_ch615 center_u33Pres_eq_bot
    (by rw [card_u33Pres]; exact card_mulAut_u33Pres_le)

theorem dLemmaFacts_u33_ch615
    {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ} (e : ↥F ≃* U33G) :
    DLemmaFacts_ch615 F := by
  have hs : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hns : ¬ Group.IsSolvable U33G := fun h => by
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr h
    have htop : Subgroup.center U33G = ⊤ := eq_top_iff.mpr fun g _ =>
      Subgroup.mem_center_iff.mpr fun y => hcomm y g
    rw [center_u33Pres_eq_bot] at htop
    have h1 : Nat.card (⊤ : Subgroup U33G) = Nat.card (⊥ : Subgroup U33G) := by rw [htop]
    rw [Subgroup.card_top, Subgroup.card_bot, card_u33Pres] at h1
    omega
  have hNX : ∀ S₀ : Subgroup U33G, IsSylowTwoOf S₀ ⊤ → ∀ g : U33G,
      (∀ s ∈ S₀, g * s * g⁻¹ ∈ S₀) → g ∈ S₀ := by
    intro S₀ hS₀ g hg
    have htr := SBd8.TrioShape.of_equiv_sylow (MulEquiv.refl U33G) GoldS146R.isSylowTwoOf_u33_T
      SBd8.trioShape_u33G hS₀
    have hgN := mem_normalizer_of_conj_mem_l32_ch615 hg
    rw [htr.1] at hgN
    exact hgN
  exact dLemmaFacts_of_mulEquiv_ch615 e hns (exists_eq_conj_of_outer_ch615 isPGroup_outer_u33_ch615)
    hNX fun S₀ hS₀ _ hSR _ _ g hg =>
      mem_of_normalizes_overgroup_ch615 hS₀ (fun g' _ h => hNX S₀ hS₀ g' h) hSR le_top
        (Subgroup.mem_top g) fun r hr => hg r hr

end U33

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_g2two_fix_ch615
    (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨g₂⟩ := nonempty_g2Two_commutator_equiv hK
  have hdl := dLemmaFacts_u33_ch615 (e.trans (g₂.trans u33EquivSubG2.symm))
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := isSimpleGroup_u33Pres
    exact (e.trans (g₂.trans u33EquivSubG2.symm)).isSimpleGroup
  exact c.false_of_case1_dLemma_fix_ch615 h432 hU hN hdl
    (center_of_isSimpleGroup_ch615 hs hdl.1) hfix

theorem false_of_case1_g2two_nofix_ch615
    (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) : False := by
  obtain ⟨g₂⟩ := nonempty_g2Two_commutator_equiv hK
  have hdl := dLemmaFacts_u33_ch615 (e.trans (g₂.trans u33EquivSubG2.symm))
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := isSimpleGroup_u33Pres
    exact (e.trans (g₂.trans u33EquivSubG2.symm)).isSimpleGroup
  have h6048 : Nat.card ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = 6048 := by
    rw [Nat.card_congr (e.trans (g₂.trans u33EquivSubG2.symm)).toEquiv, card_u33Pres]
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  obtain ⟨K', _, _, hK', π, hπ⟩ := g2Derived_of_b51_ch615 h6048 h1.2.1.1
  rw [hfix, bot_inf_eq] at hπ
  have : CharP K' 2 := FFC.charP_two_of_card_pow hK'
  have h64 := G64.RealizesVia.card_eq hπ
  rw [B5.G2D.card_zornQMod, Subgroup.card_bot, mul_one,
    (by simpa using hK' : Nat.card K' = 2)] at h64
  have hS₀ := isSylowTwoOf_subgroupOf_ch615 hS
  refine c.false_of_two_overgroups_ch615 hU hN
    ((quasithinGenFitting_le _).trans (B6.ffJ_le _)) (le_normalizer_genFitting_ch615 hU) hdl
    (center_of_isSimpleGroup_ch615 hs hdl.1) (c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1)
    fun R₁ R₂ h1S h1F h1ne h1s h2S h2F h2ne h2s hne =>
      fix_or_fix_of_trio_ch615 hs hdl.1 h6048 (fun v => by rw [← sq]; exact IntMod.sq_eq_one v)
        hfix hπ.2.2.2.1 (by rw [h64]; norm_num) hS₀ (fun w hw => by
          have := mem_commV_sup_fixV_ch615 IntMod.sq_eq_one hS.2.2 hw
          rwa [hfix, sup_bot_eq] at this)
        (SBd8.trioShape_U33 ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩ hS₀)
        h1S h1F h1ne h1s h2S h2F h2ne h2s hne

end Cx615C

end CFSG.Quasithin.H13
