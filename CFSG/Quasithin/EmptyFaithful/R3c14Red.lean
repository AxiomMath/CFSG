module

public import CFSG.Quasithin.EmptyFaithful.R3c14Cfg
public import CFSG.Quasithin.EmptyFaithful.R3c10Elim

public section

namespace CFSG.Quasithin.R3c14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10
open CFSG.ComponentClassification
open scoped commutatorElement

section Quot

variable {G : Type} [Group G]

theorem quot_normalizes [Finite G] {L A B : Subgroup G} (hB : B ≤ L)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) := by
  intro t' ht'
  obtain ⟨l, hl, rfl⟩ := ht'
  have hlA : (l : G) ∈ A := Subgroup.mem_subgroupOf.mp hl
  have hlB : (l : G) ∈ Subgroup.normalizer (B : Set G) := hAB hlA
  have hlB' : l ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    (SBc2.mem_normalizer_subgroupOf_iff hB l).mpr hlB
  refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
  obtain ⟨a, ha, rfl⟩ := hvbar
  refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlB' a).mp ha, ?_⟩
  simp [map_mul, map_inv]

theorem center_quot_eq_bot {L : Subgroup G} [Group.IsPerfect ↥L] :
    Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
  have h1 : PerfectAutomorphisms.centerQuotientHom ↥L (MulAut.conj l) = 1 := by
    rw [OuterAutomorphisms.centerQuotient_conj]
    ext y
    have hc := Subgroup.mem_center_iff.mp hx y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc _ = y * (QuotientGroup.mk' (Subgroup.center ↥L) l) *
          (QuotientGroup.mk' (Subgroup.center ↥L) l)⁻¹ := by rw [hc]
      _ = y := by group
  have h2 : MulAut.conj l = 1 :=
    PerfectAutomorphisms.centerQuotientHom_injective ↥L (h1.trans (map_one _).symm)
  have hl : l ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := DFunLike.congr_fun h2 g
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc g * l = (l * g * l⁻¹) * l := by rw [h3]
      _ = l * g := by group
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff l).mpr hl)

end Quot

section Red

variable {G : Type} [Group G] [Finite G]

theorem elConfig_of_ctx1 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) :
    ElConfig (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hq.1
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hMIV : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) :=
    R3c8.MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    hMIY ⟨hSM hs, hSI hs⟩
  have hV2Y : V₂ ≤ Yp := by
    have h1 : ⁅V₂, Yp⁆ ≤ Yp := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (Yp : Set G) := hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
      have h2 : v * y * v⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
      have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [this]
      exact Yp.mul_mem h2 (Yp.inv_mem hy)
    rwa [o.b_V2.1] at h1
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => hMIV ⟨hYpM hy, hYpI hy⟩
  obtain ⟨eV⟩ := o.b_V2.2
  have hV4 : Nat.card V₂ = 4 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hV2sq : ∀ v ∈ V₂, v * v = 1 := by
    intro v hv
    have h1 : eV ⟨v, hv⟩ * eV ⟨v, hv⟩ = 1 := by
      ext i
      simp
      exact CharTwo.add_self_eq_zero _
    have : (⟨v, hv⟩ : ↥V₂) * ⟨v, hv⟩ = 1 := eV.injective (by rw [map_mul, h1, map_one])
    simpa using congrArg Subtype.val this
  obtain ⟨a, hcard⟩ : ∃ a : ℕ, Nat.card ↥Yp = 2 ^ a * 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 := o.a_ord
    rw [h1, ha, h2, mul_comm]
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [o.a_eq]
      rw [oPrimeResidualOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [o.a_eq]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    have h1 : ⁅Yp, V₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 : ⁅V₂, Yp⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    rw [o.b_V2.1] at h2
    have : Nat.card V₂ = 1 := by rw [h2]; simp
    omega
  have hfix : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1 :=
    fixed_eq_one_of_gen hV4 hgen hYN hact
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQL : Q ≤ L := inf_le_right
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hY3 : ∀ x ∈ Yp, (∃ k : ℕ, orderOf x = 3 ^ k) → x ^ 3 = 1 := by
    intro x hx ⟨k, hk⟩
    have hd : orderOf x ∣ 2 ^ a * 3 := hcard ▸ Subgroup.orderOf_dvd_natCard Yp hx
    have hcop : Nat.Coprime (orderOf x) (2 ^ a) := by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨y₀, hy₀Y, hy₀3, hy₀n⟩ : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxY, hxk⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hxY (hY3 x hxY hxk) v hv).symm
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hTsyl : IsSylowTwoOf ((Q.subgroupOf L).map π) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hcomm : ∀ (a₀ : ↥L) (v₀ : ↥L), (a₀ : G) ∈ Yp → (v₀ : G) ∈ V₂ →
      π a₀ * π v₀ = π v₀ * π a₀ → (a₀ : G) * v₀ = v₀ * a₀ := by
    intro a₀ v₀ ha hv hc
    have h1 : π (a₀ * v₀ * a₀⁻¹ * v₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 : a₀ * v₀ * a₀⁻¹ * v₀⁻¹ ∈ Z := by
      rw [← hker]
      exact h1
    have h3 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ centerOf L :=
      SBc2.mem_centerOf_iff_center.mpr h2
    have h4 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ V₂ := by
      have h5 : (a₀ : G) * v₀ * (a₀ : G)⁻¹ ∈ V₂ :=
        (Subgroup.mem_normalizer_iff.mp (hYN ha) (v₀ : G)).mp hv
      have h6 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) =
          ((a₀ : G) * v₀ * (a₀ : G)⁻¹) * (v₀ : G)⁻¹ := rfl
      rw [h6]
      exact V₂.mul_mem h5 (V₂.inv_mem hv)
    have h7 := hVz _ h4 h3
    calc (a₀ : G) * v₀ = (a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) * (v₀ * a₀) := by
          rw [show (((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) * ((v₀ : G) * a₀)) = (a₀ : G) * v₀ by
            simp [mul_assoc]]
      _ = v₀ * a₀ := by rw [h7, one_mul]
  have hKcard : Nat.card (V₂.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2L).toEquiv
  have hinj : Function.Injective (π.comp (V₂.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card ((V₂.subgroupOf L).map π) = 4 := by
    have h1 : (π.comp (V₂.subgroupOf L).subtype).range = (V₂.subgroupOf L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  have hVbar2 : ∀ v ∈ (V₂.subgroupOf L).map π, v * v = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2sq _ hxV)
    rw [this, map_one]
  have hfixbar : ∀ v ∈ (V₂.subgroupOf L).map π,
      (∀ h ∈ (Yp.subgroupOf L).map π, h * v = v * h) → v = 1 := by
    rintro _ ⟨v₀, hv₀, rfl⟩ hc
    have hv : (v₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hv₀
    have : v₀ = 1 := by
      have h1 : (v₀ : G) = 1 := by
        refine hfix _ hv fun b hb => ?_
        have := hcomm ⟨b, hYL hb⟩ v₀ hb hv (hc _ ⟨⟨b, hYL hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
        exact this
      exact Subtype.ext h1
    rw [this, map_one]
  have hybar : ∃ y ∈ (Yp.subgroupOf L).map π, y ^ 3 = 1 ∧
      ¬ ∀ v ∈ (V₂.subgroupOf L).map π, y * v = v * y := by
    refine ⟨π ⟨y₀, hYL hy₀Y⟩, ⟨⟨y₀, hYL hy₀Y⟩, Subgroup.mem_subgroupOf.mpr hy₀Y, rfl⟩, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨y₀, hYL hy₀Y⟩ : ↥L) ^ 3 = 1 := Subtype.ext hy₀3
      rw [this, map_one]
    · intro hall
      apply hy₀n
      intro v hv
      exact hcomm ⟨y₀, hYL hy₀Y⟩ ⟨v, hV2L hv⟩ hy₀Y hv
        (hall _ ⟨⟨v, hV2L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩)
  have hSq : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := hSL
  let ρ : ↥(Sgp153 T V₁) →* MulAut (↥L ⧸ Z) :=
    (PerfectAutomorphisms.centerQuotientHom ↥L).comp
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hSq))
  have hρ : ∀ (s : ↥(Sgp153 T V₁)) (l : ↥L),
      ρ s (π l) = π (Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l) := fun s l =>
    PerfectAutomorphisms.onCenterQuotient_apply_mk _ l
  have hρcoe : ∀ (s : ↥(Sgp153 T V₁)) (l : ↥L),
      ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l : ↥L) : G) =
        (s : G) * l * (s : G)⁻¹ := fun s l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hSq s) l
  have hρne : ∀ s : ↥(Sgp153 T V₁), (s : G) ∉ Subgroup.centralizer (L : Set G) → ρ s ≠ 1 := by
    intro s hs h1
    apply hs
    have h2 : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) = 1 :=
      PerfectAutomorphisms.centerQuotientHom_injective ↥L (h1.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := DFunLike.congr_fun h2 ⟨l, hl⟩
    have h4 := congrArg Subtype.val h3
    rw [hρcoe] at h4
    simp only [MulAut.one_apply] at h4
    show l * (s : G) = (s : G) * l
    calc l * (s : G) = ((s : G) * l * (s : G)⁻¹) * (s : G) := by rw [h4]
      _ = (s : G) * l := by group
  obtain ⟨s₀, hs₀S, hs₀C, hs₀L⟩ : ∃ s ∈ Sgp153 T V₁, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    apply o.c_cent
    apply le_antisymm
    · intro s hs
      exact ⟨hs.1, hcon s hs.1 hs.2⟩
    · intro s hs
      exact ⟨hs.1, Subgroup.centralizer_le (fun x hx => hYL hx) hs.2⟩
  let W : Subgroup ↥(Sgp153 T V₁) := (Subgroup.centralizer (Yp : Set G)).subgroupOf (Sgp153 T V₁)
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.centralizer (Yp : Set G) := hn
    show ((g * n * g⁻¹ : ↥(Sgp153 T V₁)) : G) ∈ Subgroup.centralizer (Yp : Set G)
    rw [Subgroup.mem_centralizer_iff] at hn' ⊢
    intro y hy
    have hy' : (g : G)⁻¹ * y * (g : G) ∈ Yp := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (g⁻¹ : ↥(Sgp153 T V₁)).2) y).mp
      simpa using this hy
    have h1 := hn' _ hy'
    show y * ((g : G) * n * (g : G)⁻¹) = ((g : G) * n * (g : G)⁻¹) * y
    calc y * ((g : G) * n * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * y * (g : G)) * n) * (g : G)⁻¹ := by group
      _ = (g : G) * (n * ((g : G)⁻¹ * y * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * n * (g : G)⁻¹) * y := by group
  have hSfin : IsPGroup 2 ↥(Sgp153 T V₁) := hSyl.2.1
  have hRp : IsPGroup 2 ↥ρ.range := hSfin.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hRfin : Finite ↥ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hRnil : Group.IsNilpotent ↥ρ.range := hRp.isNilpotent
  have hWpn : (W.map ρ.rangeRestrict).Normal := hWn.map _ ρ.rangeRestrict_surjective
  have hWpne : W.map ρ.rangeRestrict ≠ ⊥ := by
    intro hb
    have hmem : ρ.rangeRestrict ⟨s₀, hs₀S⟩ ∈ W.map ρ.rangeRestrict :=
      ⟨⟨s₀, hs₀S⟩, hs₀C, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    apply hρne ⟨s₀, hs₀S⟩ hs₀L
    exact congrArg Subtype.val hmem
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hWpne
  obtain ⟨⟨ζ', hζ'W, hζ'Z⟩, hζ'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  obtain ⟨w, hwW, hwζ⟩ := hζ'W
  have hwC : (w : G) ∈ Subgroup.centralizer (Yp : Set G) := hwW
  have hζρ : (ζ' : MulAut (↥L ⧸ Z)) = ρ w := (congrArg Subtype.val hwζ).symm
  have hζne : (ζ' : MulAut (↥L ⧸ Z)) ≠ 1 := fun h1 => hζ'1 (Subtype.ext (Subtype.ext h1))
  have hζH : ∀ h ∈ (Yp.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) h = h := by
    rintro _ ⟨l₀, hl₀, rfl⟩
    have hl₀Y : (l₀ : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hl₀
    rw [hζρ, hρ]
    congr 1
    refine Subtype.ext ?_
    rw [hρcoe]
    have hc := Subgroup.mem_centralizer_iff.mp hwC (l₀ : G) hl₀Y
    calc (w : G) * (l₀ : G) * (w : G)⁻¹ = (l₀ : G) * (w : G) * (w : G)⁻¹ := by rw [← hc]
      _ = (l₀ : G) := by group
  have hζT : ∀ t ∈ (Q.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) t = t := by
    rintro _ ⟨q₀, hq₀, rfl⟩
    have hq₀Q : (q₀ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq₀
    let sq : ↥(Sgp153 T V₁) := ⟨(q₀ : G), hQS hq₀Q⟩
    have hρsq : ∀ x : ↥L ⧸ Z, ρ sq x = π q₀ * x * (π q₀)⁻¹ := by
      intro x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Z x
      have e : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq sq) l = q₀ * l * q₀⁻¹ :=
        Subtype.ext (hρcoe sq l)
      show ρ sq (π l) = π q₀ * π l * (π q₀)⁻¹
      rw [hρ, e, map_mul, map_mul, map_inv]
    have hcomm' := Subgroup.mem_center_iff.mp hζ'Z ⟨ρ sq, ⟨sq, rfl⟩⟩
    have hcomm'' : ρ sq * (ζ' : MulAut (↥L ⧸ Z)) = (ζ' : MulAut (↥L ⧸ Z)) * ρ sq :=
      congrArg Subtype.val hcomm'
    have hd : (π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hcomm'' ((ζ' : MulAut (↥L ⧸ Z)).symm y)
      simp only [MulAut.mul_apply, hρsq, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      calc y * ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀))
          = (π q₀)⁻¹ * (π q₀ * y * (π q₀)⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by group
        _ = (π q₀)⁻¹ * ((ζ' : MulAut (↥L ⧸ Z)) (π q₀) * y *
              ((ζ' : MulAut (↥L ⧸ Z)) (π q₀))⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by
          rw [h1]
        _ = ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀)) * y := by group
    rw [center_quot_eq_bot, Subgroup.mem_bot] at hd
    exact (inv_mul_eq_one.mp hd).symm
  refine ⟨(Q.subgroupOf L).map π, (V₂.subgroupOf L).map π, (Yp.subgroupOf L).map π,
    (ζ' : MulAut (↥L ⧸ Z)), hTsyl, ?_⟩
  exact ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hVQ (Subgroup.mem_subgroupOf.mp hx)), hVbar4, hVbar2,
    quot_normalizes hV2L (fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩),
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV2Y (Subgroup.mem_subgroupOf.mp hx)),
    quot_normalizes hV2L hYN,
    quot_normalizes hYL (fun q hq => hSN (hQS hq)), hybar, hfixbar, hζne, hζT, hζH⟩

end Red

end CFSG.Quasithin.R3c14
