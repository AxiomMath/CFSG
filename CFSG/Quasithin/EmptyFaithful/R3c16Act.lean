module

public import CFSG.Quasithin.EmptyFaithful.R3c15Cl

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15
open scoped commutatorElement

@[expose] def NoThreeAct (X : Type) [Group X] : Prop :=
  ∀ {T V : Subgroup X}, IsSylowTwoOf T ⊤ → V ≤ T → Nat.card V = 4 →
    T ≤ Subgroup.normalizer (V : Set X) → ∀ {y : X}, y ∈ Subgroup.normalizer (V : Set X) →
      ∀ {k : ℕ}, y ^ (3 ^ k) = 1 → ∀ v ∈ V, y * v = v * y

theorem not_elConfig_of_noThreeAct {X : Type} [Group X] (hX : NoThreeAct X) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, h⟩
  obtain ⟨y, hyH, hy3, hyn⟩ := h.y3
  exact hyn (hX hT h.VT h.V4 h.TV (h.HV hyH) (k := 1) (by simpa using hy3))

section Cl

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_quot_comm {L V₂ Yp : Subgroup G} (hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G))
    (hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1) {a₀ v₀ : ↥L} (ha : (a₀ : G) ∈ Yp)
    (hv : (v₀ : G) ∈ V₂)
    (hc : QuotientGroup.mk' (Subgroup.center ↥L) a₀ * QuotientGroup.mk' (Subgroup.center ↥L) v₀ =
      QuotientGroup.mk' (Subgroup.center ↥L) v₀ * QuotientGroup.mk' (Subgroup.center ↥L) a₀) :
    (a₀ : G) * v₀ = v₀ * a₀ := by
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
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

theorem cl_of_noThreeAct {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) (hX : NoThreeAct (↥L ⧸ Subgroup.center ↥L)) : False := by
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
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hQS : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁ := inf_le_left
  have hV2Q : V₂ ≤ Sgp153 T V₁ ⊓ L := le_inf hV2S hV2L
  have hQV₂ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq =>
    hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hVz₂ : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix₂ x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hgen : Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    conv_lhs => rw [c.facts.theta]
    rw [thetaOf, Subgroup.closure_le]
    intro x hx
    have hxY : x ∈ Yp := by
      rw [c.facts.theta]
      exact Subgroup.subset_closure hx
    exact Subgroup.subset_closure ⟨hxY, 1, by simpa using hx.2⟩
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : V₂ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      rw [this, Subgroup.card_bot] at hV4
      omega
    exact hu1 (hfix₂ u hu fun b hb => (Subgroup.mem_centralizer_iff.mp (hle hb) u hu).symm)
  have hy : ∃ y ∈ Yp, ∃ k : ℕ, y ^ (3 ^ k) = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    refine hgen.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
    obtain ⟨hxY, k, hk⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hxY k (by rw [← hk]; exact pow_orderOf_eq_one x) v hv).symm
  obtain ⟨y, hyY, k, hyk, hyn⟩ := hy
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  have hTsyl : IsSylowTwoOf (((Sgp153 T V₁ ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  obtain ⟨h4₂, h2₂⟩ := quot_klein hV2L hV4 hV2sq hVz₂
  have hVT' : (V₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      ((Sgp153 T V₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV2Q (Subgroup.mem_subgroupOf.mp hx))
  have hTN := quot_normalizes hV2L hQV₂
  have hyL : y ∈ L := hYL hyY
  have hyN : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L) ∈
      Subgroup.normalizer (((V₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) :=
    quot_normalizes hV2L hYN₂ ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hyY, rfl⟩
  have hyk' : (QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L)) ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥L) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one]
  have hcent := hX hTsyl hVT' h4₂ hTN hyN hyk'
  apply hyn
  intro v hv
  have hc := hcent (QuotientGroup.mk' (Subgroup.center ↥L) (⟨v, hV2L hv⟩ : ↥L))
    ⟨⟨v, hV2L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  exact comm_of_quot_comm hYN₂ hVz₂ (a₀ := ⟨y, hyL⟩) (v₀ := ⟨v, hV2L hv⟩) hyY hv hc

end Cl

end CFSG.Quasithin.R3c16
