module

public import CFSG.Quasithin.EmptyFaithful.R3c15Cl
public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.EmptyFaithful.ModHPerm

public section

namespace CFSG.Quasithin.ModH.Cl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15 CFSG.Quasithin.ModH
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

@[expose] def NoTwoKlein (X : Type) [Group X] : Prop :=
  ∀ {T V₁ V₂ : Subgroup X}, IsSylowTwoOf T ⊤ → V₁ ≤ T → V₂ ≤ T → Nat.card ↥V₁ = 4 →
    Nat.card ↥V₂ = 4 → (∀ v ∈ V₁, v * v = 1) → (∀ v ∈ V₂, v * v = 1) →
      T ≤ Subgroup.normalizer (V₁ : Set X) → T ≤ Subgroup.normalizer (V₂ : Set X) →
        V₁ ⊓ V₂ = ⊥ → False

theorem NoTwoKlein.of_centerSmall {X : Type} [Group X] [Finite X] (hcs : CenterSmall X) :
    NoTwoKlein X := by
  intro T V₁ V₂ hT hV₁T hV₂T h4₁ h4₂ _ _ hN₁ hN₂ hinf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, -⟩ := K1.isSylowTwoOf_top_iff.mp hT
  obtain ⟨v₁, hv₁V, hv₁1, hv₁T⟩ := SBd13.exists_fixed_ne_one hp hN₁ h4₁
  obtain ⟨v₂, hv₂V, hv₂1, hv₂T⟩ := SBd13.exists_fixed_ne_one hp hN₂ h4₂
  rcases hcs T hT v₁ v₂ (hV₁T hv₁V) (hV₂T hv₂V) hv₁T hv₂T with h | h | h
  · exact hv₁1 h
  · exact hv₂1 h
  · have : v₁ ∈ V₁ ⊓ V₂ := ⟨hv₁V, h ▸ hv₂V⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hv₁1 this

theorem NoTwoKlein.of_equiv {X X' : Type} [Group X] [Group X'] [Finite X] (e : X ≃* X')
    (h : NoTwoKlein X') : NoTwoKlein X := by
  intro T V₁ V₂ hT hV₁T hV₂T h4₁ h4₂ h2₁ h2₂ hN₁ hN₂ hinf
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hT
  have hcard : ∀ V : Subgroup X, Nat.card ↥(V.map e.toMonoidHom) = Nat.card ↥V := fun V =>
    (Nat.card_congr (V.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hnorm : ∀ V : Subgroup X, T ≤ Subgroup.normalizer (V : Set X) →
      T.map e.toMonoidHom ≤ Subgroup.normalizer ((V.map e.toMonoidHom : Subgroup X') : Set X') := by
    intro V hV t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff e V t₀).mpr (hV ht₀)
  have hsq : ∀ V : Subgroup X, (∀ v ∈ V, v * v = 1) → ∀ v ∈ V.map e.toMonoidHom, v * v = 1 := by
    rintro V hV _ ⟨v, hv, rfl⟩
    show e v * e v = 1
    rw [← map_mul, hV v hv, map_one]
  refine h hT' (Subgroup.map_mono hV₁T) (Subgroup.map_mono hV₂T) ((hcard V₁).trans h4₁)
    ((hcard V₂).trans h4₂) (hsq V₁ h2₁) (hsq V₂ h2₂) (hnorm V₁ hN₁) (hnorm V₂ hN₂) ?_
  rw [← Subgroup.map_inf _ _ _ e.injective, hinf, Subgroup.map_bot]

section Case1Main

variable {G : Type} [Group G] [Finite G]

theorem l_cl_case1_gen {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) (hY : Yp = Y153 Mc M) (hnk : NoTwoKlein (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨hYN₂, hfix₂, hV2Y, hMIV⟩ := R3c10.ctx2_facts h113 c
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  obtain ⟨hY₁, -⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
  have hYN₁ : Yp ≤ Subgroup.normalizer (V₁ : Set G) := hY ▸ hY₁
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV14 : Nat.card V₁ = 4 := hh.decomp.card₁
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  have hV1sq : ∀ x ∈ V₁, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₁ hx)
    rw [← sq]
    exact this
  have hVS : VZ T M ≤ Sgp153 T V₁ := by
    intro v hv
    refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
    have hc' := congrArg Subtype.val
      (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
    have : v * k * v⁻¹ = k := by
      have h1 : v * k = k * v := hc'
      rw [h1]
      group
    rw [this]
    exact hk
  have hV1S : V₁ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₁ hv)
  have htM : t ∈ M := hh.decomp.t_mem
  have hYt : ∀ y, y ∈ Yp ↔ t * y * t⁻¹ ∈ Yp := fun y => by
    rw [hY]
    exact Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M htM) y
  have hfix₁ : ∀ x ∈ V₁, (∀ a ∈ Yp, a * x = x * a) → x = 1 := by
    intro x hx hc
    have hx' : t * x * t⁻¹ ∈ V₂ := hh.decomp.swap₁ x hx
    have h1 : t * x * t⁻¹ = 1 := hfix₂ _ hx' fun a ha => by
      have hta : t⁻¹ * a * t ∈ Yp := (hYt (t⁻¹ * a * t)).mpr (by
        rw [show t * (t⁻¹ * a * t) * t⁻¹ = a by group]
        exact ha)
      have h2 := hc _ hta
      calc a * (t * x * t⁻¹) = t * ((t⁻¹ * a * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * a * t)) * t⁻¹ := by rw [h2]
        _ = (t * x * t⁻¹) * a := by group
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have hgen : Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    conv_lhs => rw [c.facts.theta]
    rw [thetaOf, Subgroup.closure_le]
    intro x hx
    have hxY : x ∈ Yp := by
      rw [c.facts.theta]
      exact Subgroup.subset_closure hx
    exact Subgroup.subset_closure ⟨hxY, 1, by simpa using hx.2⟩
  have hV1N : V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun v hv =>
    hMIY ⟨hSM (hV1S hv), hSI (hV1S hv)⟩
  have hV1Y : V₁ ≤ Yp := by
    rcases R3c9.centralizes_or_le_of_generated_by_threePow hgen hV1N hYN₁ hV14 with hc | ⟨hle, -⟩
    · exfalso
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₁, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : V₁ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
        rw [this, Subgroup.card_bot] at hV14
        omega
      exact hu1 (hfix₁ u hu fun a ha => hc a ha u hu)
    · exact hle
  have hV1L : V₁ ≤ L := hV1Y.trans hYL
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hQS : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁ := inf_le_left
  have hV1Q : V₁ ≤ Sgp153 T V₁ ⊓ L := le_inf hV1S hV1L
  have hV2Q : V₂ ≤ Sgp153 T V₁ ⊓ L := le_inf hV2S hV2L
  have hQV₂ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq =>
    hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hQV₁ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₁ : Set G) := fun q hq => (hQS hq).2
  have hVz₁ : ∀ x ∈ V₁, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix₁ x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hVz₂ : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix₂ x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  have hTsyl : IsSylowTwoOf (((Sgp153 T V₁ ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  obtain ⟨h4₁, h2₁⟩ := quot_klein hV1L hV14 hV1sq hVz₁
  obtain ⟨h4₂, h2₂⟩ := quot_klein hV2L hV4 hV2sq hVz₂
  refine hnk hTsyl (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV1Q (Subgroup.mem_subgroupOf.mp hx)))
    (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV2Q (Subgroup.mem_subgroupOf.mp hx))) h4₁ h4₂ h2₁ h2₂
    (quot_normalizes hV1L hQV₁) (quot_normalizes hV2L hQV₂) ?_
  rw [eq_bot_iff]
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  have hab' : (QuotientGroup.mk' (Subgroup.center ↥L)) a = (QuotientGroup.mk' (Subgroup.center ↥L)) b :=
    hab.symm
  have hZ' : a⁻¹ * b ∈ Subgroup.center ↥L := by
    have := (QuotientGroup.eq (a := a) (b := b)).mp hab'
    exact this
  have hz : ((a : G))⁻¹ * (b : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hZ'
  have hb1 : (b : G) = 1 :=
    eq_one_of_central_quot hh.decomp.inf hYN₁ hYN₂ hfix₂ hYL (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb) hz
  have : b = 1 := Subtype.ext hb1
  rw [← hab, this, map_one]
  exact Subgroup.one_mem _

end Case1Main

theorem false_of_close {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (h113 : StageLemma14113) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {X : Type} [Group X]
    (qe : (↥L ⧸ Subgroup.center ↥L) ≃* X)
    (hpt : ∀ (T' : Sylow 2 X) (α : MulAut X), (∀ t' ∈ (T' : Subgroup X), α t' = t') →
      ∃ z : (T' : Subgroup X), z ∈ Subgroup.center (T' : Subgroup X) ∧
        ∀ g : X, α g = (z : X) * g * (z : X)⁻¹)
    (hcs : CenterSmall X) : False := by
  have : Finite X := Finite.of_equiv _ qe.toEquiv
  rcases c.hyp.cases with hY | hU
  · exact l_cl_case1_gen h113 c hN hYL hY (NoTwoKlein.of_equiv qe (NoTwoKlein.of_centerSmall hcs))
  · exact not_elConfig_of_center hpt hcs (ElConfig.map qe (elConfig_of_ctx2 h113 c hN hYL hU))

end CFSG.Quasithin.ModH.Cl
