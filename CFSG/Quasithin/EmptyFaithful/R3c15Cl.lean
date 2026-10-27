module

public import CFSG.Quasithin.EmptyFaithful.R3c15Gen
public import CFSG.Quasithin.EmptyFaithful.R3c14Lin
public import CFSG.Quasithin.EmptyFaithful.R3c11Cl

public section

namespace CFSG.Quasithin.R3c15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Case2

variable {G : Type} [Group G] [Finite G]

theorem elConfig_of_ctx2 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L)
    (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) :
    ElConfig (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hq.1
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨hYN, hfix, hV2Y, hMIV⟩ := R3c10.ctx2_facts h113 c
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    hMIY ⟨hSM hs, hSI hs⟩
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Sgp153 T V₁ ⊓ L := le_inf hV2S hV2L
  have hQS : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq =>
    hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  obtain ⟨y, hyO, -, hyfpf⟩ := hh.hyp.exists_Yplus_fpf h113 hh.decomp
  have hyYp : y ∈ Yp := by
    rw [hU.2]
    exact hyO
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ orderOf x = 3} := by
    apply le_antisymm
    · conv_lhs => rw [c.facts.theta]
      rw [thetaOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [c.facts.theta]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : V₂ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      rw [this, Subgroup.card_bot] at hV4
      omega
    apply hyfpf u hu hu1
    have := Subgroup.mem_centralizer_iff.mp (hle hyYp) u hu
    calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [this]
      _ = u := by group
  have hy : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxY, hx3⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hxY (by rw [← hx3]; exact pow_orderOf_eq_one x) v hv).symm
  have hNV1 : Subgroup.normalizer (V₁ : Set G) ≤ M :=
    (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU.1).1
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
  have hYV1 : ∀ v ∈ V₁, v ∈ Subgroup.centralizer (Yp : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) := by
      have : b ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := hU.2 ▸ hb
      exact oTwoUpper_le _ this
    exact (Subgroup.mem_centralizer_iff.mp hb'.2 v hv).symm
  have hs : ∃ s ∈ Sgp153 T V₁, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    apply c.c33.not_le
    have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hcon v (hV1S hv) (hYV1 v hv)) l hl).symm
    exact hLC.trans ((Subgroup.centralizer_le_normalizer _).trans hNV1)
  exact elConfig_of_data hZ hQsyl hSyl.2.1 hSL hSN hQS hYL hV2Y hYN hQV hVQ hV4 hV2sq hfix hy hs

end Case2

section Case1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_central_quot {L V₁ V₂ Yp : Subgroup G} (hinf : V₁ ⊓ V₂ = ⊥)
    (hY₁ : Yp ≤ Subgroup.normalizer (V₁ : Set G)) (hY₂ : Yp ≤ Subgroup.normalizer (V₂ : Set G))
    (hfix₂ : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1) (hYL : Yp ≤ L)
    {a b : G} (ha : a ∈ V₁) (hb : b ∈ V₂) (hz : a⁻¹ * b ∈ centerOf L) : b = 1 := by
  refine hfix₂ b hb fun y hy => ?_
  have hyz : y * (a⁻¹ * b) = (a⁻¹ * b) * y := Subgroup.mem_centralizer_iff.mp hz.2 y (hYL hy)
  have hu₁ : y * a⁻¹ * y⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hY₁ hy) a⁻¹).mp (V₁.inv_mem ha)
  have hu₂ : y * b * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hY₂ hy) b).mp hb
  have hprod : (y * a⁻¹ * y⁻¹) * (y * b * y⁻¹) = a⁻¹ * b := by
    calc (y * a⁻¹ * y⁻¹) * (y * b * y⁻¹) = y * (a⁻¹ * b) * y⁻¹ := by group
      _ = (a⁻¹ * b * y) * y⁻¹ := by rw [hyz]
      _ = a⁻¹ * b := by group
  have h1 : a * (y * a⁻¹ * y⁻¹) = b * (y * b * y⁻¹)⁻¹ := by
    have h0 : a * ((y * a⁻¹ * y⁻¹) * (y * b * y⁻¹)) = b := by
      rw [hprod]
      group
    calc a * (y * a⁻¹ * y⁻¹)
        = a * ((y * a⁻¹ * y⁻¹) * (y * b * y⁻¹)) * (y * b * y⁻¹)⁻¹ := by group
      _ = b * (y * b * y⁻¹)⁻¹ := by rw [h0]
  have hmem1 : a * (y * a⁻¹ * y⁻¹) ∈ V₁ := V₁.mul_mem ha hu₁
  have hmem2 : b * (y * b * y⁻¹)⁻¹ ∈ V₂ := V₂.mul_mem hb (V₂.inv_mem hu₂)
  have hbot : a * (y * a⁻¹ * y⁻¹) ∈ V₁ ⊓ V₂ := ⟨hmem1, h1 ▸ hmem2⟩
  rw [hinf, Subgroup.mem_bot] at hbot
  have h2 : b * (y * b * y⁻¹)⁻¹ = 1 := h1 ▸ hbot
  have h3 : y * b * y⁻¹ = b := (mul_inv_eq_one.mp h2).symm
  calc y * b = (y * b * y⁻¹) * y := by group
    _ = b * y := by rw [h3]

omit [Finite G] in
theorem quot_klein {L V : Subgroup G} (hVL : V ≤ L) (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v * v = 1) (hVz : ∀ x ∈ V, x ∈ centerOf L → x = 1) :
    Nat.card ((V.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) = 4 ∧
      ∀ v ∈ (V.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)), v * v = 1 := by
  classical
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hker : π.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hKcard : Nat.card (V.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  have hinj : Function.Injective (π.comp (V.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Subgroup.center ↥L := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  refine ⟨?_, ?_⟩
  · have h1 : (π.comp (V.subgroupOf L).subtype).range = (V.subgroupOf L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  · rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2 _ hxV)
    rw [this, map_one]

end Case1

section Pair

theorem no_two_klein_psl {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1) {T V₁ V₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hV₁T : V₁ ≤ T) (hV₂T : V₂ ≤ T) (h4₁ : Nat.card V₁ = 4) (h4₂ : Nat.card V₂ = 4)
    (h2₁ : ∀ v ∈ V₁, v * v = 1) (h2₂ : ∀ v ∈ V₂, v * v = 1)
    (hN₁ : T ≤ Subgroup.normalizer (V₁ : Set X)) (hN₂ : T ≤ Subgroup.normalizer (V₂ : Set X))
    (hinf : V₁ ⊓ V₂ = ⊥) : False := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let ψ : X ≃* SLn n :=
    φ.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two n K hK2)
  have hT' : IsSylowTwoOf (T.map ψ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map ψ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective]
    exact hi
  have : Finite (SLn n) := Finite.of_equiv X ψ.toEquiv
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT' (isSylow_U n (by omega))
  set Φ : X ≃* SLn n := ψ.trans (MulAut.conj g) with hΦ
  have hΦT : T.map Φ.toMonoidHom = unitriangular n (ZMod 2) := by
    rw [← hg, Subgroup.map_map]
    rfl
  have key : ∀ V : Subgroup X, V ≤ T → Nat.card V = 4 → (∀ v ∈ V, v * v = 1) →
      T ≤ Subgroup.normalizer (V : Set X) → z0 hn ∈ V.map Φ.toMonoidHom := by
    intro V hVT hV4 hV2 hNV
    refine z0_mem_V hn (hΦT ▸ Subgroup.map_mono hVT) ?_ ?_
    · rw [← hV4]
      exact (Nat.card_congr (V.equivMapOfInjective Φ.toMonoidHom Φ.injective).toEquiv).symm
    · rw [← hΦT]
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      exact (R3c11.mem_normalizer_map_equiv_iff Φ V t₀).mpr (hNV ht₀)
  have hz : z0 hn ∈ V₁.map Φ.toMonoidHom ⊓ V₂.map Φ.toMonoidHom :=
    ⟨key V₁ hV₁T h4₁ h2₁ hN₁, key V₂ hV₂T h4₂ h2₂ hN₂⟩
  rw [← Subgroup.map_inf _ _ _ Φ.injective, hinf, Subgroup.map_bot] at hz
  exact z0_ne_one hn (Subgroup.mem_bot.mp hz)

end Pair

section Case1Main

variable {G : Type} [Group G] [Finite G]

theorem l_cl_case1 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) (hY : Yp = Y153 Mc M) {n : ℕ} (hn : 3 ≤ n)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 1) : False := by
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
  refine no_two_klein_psl hn hX hTsyl (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
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

section Main

variable {G : Type} [Group G] [Finite G]

theorem l_cl {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {n : ℕ} (hn : 3 ≤ n)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 1) : False := by
  rcases c.hyp.cases with hY | hU
  · exact l_cl_case1 h113 c hN hYL hY hn hX
  · exact not_elConfig_of_psl hn hX (elConfig_of_ctx2 h113 c hN hYL hU)

end Main

end CFSG.Quasithin.R3c15
