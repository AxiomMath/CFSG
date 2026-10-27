module

public import CFSG.Quasithin.Vol2.Ch11SecC37B1
public import CFSG.Quasithin.Vol2.Ch11SecB22Two
public import CFSG.Quasithin.Vol2.Ch11SecC37N1
public import CFSG.Quasithin.Vol2.Ch11SecC37N2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conjAct_apply_coe (U : Subgroup G)
    (z : ↥(Subgroup.normalizer (U : Set G))) (w : ↥U) :
    ((conjAct U z w : ↥U) : G) = (z : G) * w * (z : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion le_rfl z) w

theorem conjAct_mem_normalizer_autOn {U P : Subgroup G} {x : ↥(Subgroup.normalizer (U : Set G))}
    (hx : (x : G) ∈ Subgroup.normalizer (P : Set G)) :
    conjAct U x ∈ Subgroup.normalizer ((autOn P U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn _ hx

@[expose] def TorusHyp (L U Z' : Subgroup G) : Prop :=
  ∀ S : Subgroup (MulAut ↥U), QuasithinUnique.IsSylowTwoOf S (autOn L U) →
    ∀ y ∈ autOn L U, y ∈ Subgroup.normalizer (S : Set (MulAut ↥U)) →
      (∀ w : ↥U, (∀ s ∈ S, s w * w⁻¹ ∈ Z'.subgroupOf U) → y w * w⁻¹ ∈ Z'.subgroupOf U) ∨
      (∀ w : ↥U, (∀ s ∈ S, s w * w⁻¹ ∈ Z'.subgroupOf U) → y w * w⁻¹ ∈ Z'.subgroupOf U →
        w ∈ Z'.subgroupOf U)

theorem torusDich [Finite G] {U Z' L P : Subgroup G} (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hP : QuasithinUnique.IsSylowTwoOf P L) (hT : TorusHyp L U Z') {d : G} (hdL : d ∈ L)
    (hdP : d ∈ Subgroup.normalizer (P : Set G)) :
    (∀ u ∈ U, (∀ p ∈ P, p * u * p⁻¹ = u) → d * u * d⁻¹ * u⁻¹ ∈ Z') ∨
      (∀ u ∈ U, (∀ p ∈ P, p * u * p⁻¹ = u) → d * u * d⁻¹ * u⁻¹ ∈ Z' → u ∈ Z') := by
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hP hLU
  have hy : conjAct U ⟨d, hLU hdL⟩ ∈ autOn L U := ⟨⟨d, hLU hdL⟩, hdL, rfl⟩
  have hyN := conjAct_mem_normalizer_autOn (P := P) (x := ⟨d, hLU hdL⟩) hdP
  have hfix : ∀ w : ↥U, (∀ p ∈ P, p * (w : G) * p⁻¹ = w) →
      ∀ s ∈ autOn P U, s w * w⁻¹ ∈ Z'.subgroupOf U := by
    rintro w hw s ⟨z, hz, rfl⟩
    have h1 : conjAct U z w = w := Subtype.ext ((conjAct_apply_coe U z w).trans
      (hw z (Subgroup.mem_subgroupOf.mp hz)))
    rw [h1, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hyw : ∀ w : ↥U, ((conjAct U ⟨d, hLU hdL⟩ w * w⁻¹ : ↥U) : G) = d * w * d⁻¹ * (w : G)⁻¹ :=
    fun w => by rw [Subgroup.coe_mul, conjAct_apply_coe, Subgroup.coe_inv]
  rcases hT _ hS _ hy hyN with h | h
  · left
    intro u hu hfu
    have := h ⟨u, hu⟩ (hfix ⟨u, hu⟩ hfu)
    rw [Subgroup.mem_subgroupOf, hyw] at this
    exact this
  · right
    intro u hu hfu hdu
    exact Subgroup.mem_subgroupOf.mp (h ⟨u, hu⟩ (hfix ⟨u, hu⟩ hfu)
      (by rw [Subgroup.mem_subgroupOf, hyw]; exact hdu))

theorem torusHyp_SL3 [Finite G] (hTor : FactTorusLineSL3) {L U Z' : Subgroup G}
    [IsMulCommutative ↥U] (hU2 : ∀ u ∈ U, u ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL (V := ↥U) (autOn L U) ⊤ (Z'.subgroupOf U) 3 n) :
    TorusHyp L U Z' := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hnat
  intro S hS
  exact (hTor F n hn hF ↥U (fun w => Subtype.ext (by simpa using hU2 w w.2)) _ _ π hπ S hS).2

theorem torusHyp_Sp4 [Finite G] (hTor : FactTorusLineSp4) {L U Z' : Subgroup G}
    [IsMulCommutative ↥U] (hU2 : ∀ u ∈ U, u ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSp4 (V := ↥U) (autOn L U) ⊤ (Z'.subgroupOf U) n) :
    TorusHyp L U Z' := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hnat
  intro S hS
  exact (hTor F n hn hF ↥U (fun w => Subtype.ext (by simpa using hU2 w w.2)) _ _ π hπ S hS).2

namespace Set37

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G}
  (s : Set37 T L I n V₁ H g)
include s

theorem pCoreOf_L_le_T : pCoreOf 2 L ≤ T :=
  (F7.pCoreOf_mono_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer s.hyp.normal)).trans
    (F7.isSylowTwoOf_pCoreOf_le s.sylow_LT)

theorem sylow_TL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
  F7.isSylowTwoOf_inf_normal s.sylow_LT le_sup_left s.hyp.normal

theorem inf_le_normalizer (h1102 : Stmt11_0_2) (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5)
    (h1136 : Stmt11_3_6) (hB : FactSL2Borel) (hBS : FactBorelOddSL3) (hBP : FactBorelOddSp4) :
    H ⊓ Subgroup.normalizer (L : Set G) ⊓ L ≤
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨_, -, -, ⟨e₁⟩, -⟩ := h1102 G T L I n s.hyp
  have hker : ∀ y : ↥L, y ∈ CFSG.pCore 2 ↥L → (y : G) ∈ T := by
    intro y hy
    rw [pCore_eq_subgroupOf, Subgroup.mem_subgroupOf] at hy
    exact s.pCoreOf_L_le_T hy
  have hY₀ : ∀ x ∈ H ⊓ Subgroup.normalizer (L : Set G) ⊓ L, Odd (orderOf x) →
      x ^ (2 ^ n - 1) = 1 := fun x hx hodd => s.pow_eq_one_of_odd h1135 h1136 hB hx.1 hodd
  have hTY : T ⊓ L ≤ H ⊓ Subgroup.normalizer (L : Set G) ⊓ L :=
    fun t ht => ⟨⟨s.T_le ht.1, s.hyp.normal ht.1⟩, ht.2⟩
  have h1 : 1 ≤ n := by have := s.two_le; omega
  rcases s.kind h1134 with ⟨F, _, _, hF, ⟨e₂⟩⟩ | ⟨F, _, _, hF, ⟨e₂⟩⟩
  · refine le_normalizer_of_borel s.sylow_TL
      (Odd.mul (SecA.odd_two_pow_sub_one (by omega)) (SecA.odd_two_pow_sub_one (by omega)))
      (B51.card_SL3_eq_pow hF) (e₂.toMonoidHom.comp (e₁.toMonoidHom.comp (QuotientGroup.mk' _)))
      (e₂.surjective.comp (e₁.surjective.comp (QuotientGroup.mk'_surjective _)))
      (fun y hy => hker y ?_) (fun Y U hUY hU2 hUc hodd => hBS F n s.two_le hF Y U hUY hU2 hUc hodd)
      hTY inf_le_right hY₀
    simpa only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hy
  · refine le_normalizer_of_borel s.sylow_TL
      (Odd.mul (SecA.odd_two_pow_sub_one (by omega)) (SecA.odd_two_pow_sub_one (by omega)))
      (B51.card_Sp4_eq_pow hF) (e₂.toMonoidHom.comp (e₁.toMonoidHom.comp (QuotientGroup.mk' _)))
      (e₂.surjective.comp (e₁.surjective.comp (QuotientGroup.mk'_surjective _)))
      (fun y hy => hker y ?_) (fun Y U hUY hU2 hUc hodd => hBP F n s.two_le hF Y U hUY hU2 hUc hodd)
      hTY inf_le_right hY₀
    simpa only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hy

theorem d0Of_le_normalizer (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (hB : FactSL2Borel) (hBS : FactBorelOddSL3)
    (hBP : FactBorelOddSp4) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    d0Of D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := fun _ hd =>
  s.inf_le_normalizer h1102 h1134 h1135 h1136 hB hBS hBP ⟨hD.1 (d0Of_le_self D hd),
    d0Of_le h1104 h1134 h1135 h1136 hB s.hyp hJ s.hV₁ s.h31 s.hnot s.hAT s.hAC hD hd⟩

theorem inf_le_centralizer_V₁ (hFC1 : SecB.FactFlagOneCentral) (h1102 : Stmt11_0_2) :
    T ⊓ L ≤ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨hV, hn, hLV, hVL, hnat, -, -⟩ := SecB.natSetting h1102 s.hyp
  exact hFC1 G L (fsuV T I) T V₁ n hV hn hLV hVL hnat s.sylow_LT (SecA.T_le_normalizer_fsuV T I)
    s.hyp.normal (SecA.IsVi.cV_le s.hV₁) (SecA.IsVi.le_fsuV s.hV₁)
    (SecA.IsVi.isEndStable s.hV₁) (by rw [SecA.IsVi.relIndex_eq s.hV₁, mul_one])
    (SecA.IsVi.le_normalizer s.hV₁)

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
