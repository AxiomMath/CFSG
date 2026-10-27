module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaModel
public import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaRep
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelDim
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec11Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 CFSG.RankThree.GF2n.Smith81 QuadraticMap Module


section Order

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Ctx.pow_dvd_card_Xbar_of_omega (hc : Ctx M Q Z B) {m x : ℕ} (hx : 2 ≤ x)
    (hΩ : IsOmegaLieModel (XbarMod M Q Z B) m x) :
    (2 ^ x) ^ (m * (m - 1)) ∣ Nat.card ↥(Xbar M Q Z B) := by
  rw [← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq
    (hc.center_Xbar_eq_bot_of_omega hx hΩ)).trans QuotientGroup.quotientBot).toEquiv]
  rcases hΩ with h | h | ⟨rfl, h⟩
  · have h4 : 4 ≤ m := h.admissible.2.2
    rw [h.card_eq_lieOrd (by omega)]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd h4 _
  · have h4 : 4 ≤ m := h.admissible.2.2
    rw [h.card_eq_lieOrd (by omega)]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd h4 _
  · rw [h.card_eq_lieOrd (by norm_num)]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSU) (n := 4) (by decide) _

theorem Ctx.isSimpleGroup_Xbar_of_omega (hc : Ctx M Q Z B) {m x : ℕ} (hx : 2 ≤ x)
    (hΩ : IsOmegaLieModel (XbarMod M Q Z B) m x) : IsSimpleGroup ↥(Xbar M Q Z B) := by
  have : IsSimpleGroup (XbarMod M Q Z B) := by
    rcases hΩ with h | h | ⟨-, h⟩ <;> exact h.isSimpleGroup_of_mem_classicalTags (by decide)
  exact ((QuotientGroup.quotientMulEquivOfEq
    (hc.center_Xbar_eq_bot_of_omega hx hΩ)).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end Order

theorem cmOmegaFiltration_of (hΩ : OmegaSiegelDimStatement) : CMOmegaFiltration := by
  intro G _ _ M Q Z B _ hc n m x _ _ ha2 hLie hZ
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hx : 2 ≤ x := by
    by_contra h
    obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
    all_goals simp at hZ; omega
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, φker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  obtain ⟨K', _, _, _, N, _, _, _, QN, hK', hndN, hdimN, hm3, ψ, hψ⟩ :=
    hc.exists_omega_model hx hLie
  obtain ⟨ρV, hinj, hiso, hfix, htop, hsieg, hcompat⟩ :=
    hc.exists_cmComm_action_of_mulEquiv ha2 hD φ hφπ φker hφQ ψ
  obtain ⟨hnd, -, -, -, -⟩ := hc.cmComm_kantor_instance ha2 hD φ hφπ hφQ
  have hKZ : Nat.card K = Nat.card Z := hD.card
  obtain ⟨a, haL, haA⟩ := ha2
  obtain ⟨s₀, hs₀a, hs₀⟩ := hc.exists_lift_a2 (a := ⟨a, hc.LB_le_M haL⟩) (h := ⟨haL, haA⟩)
  have hE : ((xbarHToXbar M Q Z B s₀ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [hs₀]
    refine ⟨⟨⟨a, hc.LB_le_M haL⟩, rfl, haA⟩, 1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  have hdim := hΩ K' K (by rw [hK', hZ, hKZ]) (hKZ ▸ hq4) N QN hndN m hdimN hm3 _
    (cmCommQf B φ) hnd ρV hinj hiso
    ⟨ψ (xbarHToXbar M Q Z B s₀), hψ _ hE, hsieg s₀ (hs₀a ▸ haL) (hs₀a ▸ haA)⟩ hfix htop
  have := hc.isSimpleGroup_Xbar_of_omega hx hLie
  have : IsSimpleGroup ↥(elementaryGroup QN) := ψ.symm.isSimpleGroup
  have hX : Nat.card K ^ (m * (m - 1)) ∣ Nat.card ↥(elementaryGroup QN) := by
    rw [hKZ, ← hZ, ← Nat.card_congr ψ.toEquiv]
    exact hc.pow_dvd_card_Xbar_of_omega hx hLie
  have hfaith : ∀ s : ↥(XbarPre M Q Z B),
      (∀ e ∈ cmComm M Q Z B K γ M₀ φ, φ ⟨s, XbarPre_le_H0 hc s.2⟩ e = e) → (s : G) ∈ Q :=
    fun s hs => hc.mem_Q_of_cmCommAct_eq_one hD φ hφπ φker hφQ
      (s := ⟨⟨s, XbarPre_le_H0 hc s.2⟩, (mem_XbarH_iff hc _).mpr s.2⟩)
      (LinearEquiv.ext fun v => Subtype.ext (hs v v.2))
  have hirr : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m →
      ∀ U : Submodule K M₀.E, U ≤ cmComm M Q Z B K γ M₀ φ →
        (∀ s : ↥(XbarPre M Q Z B), ∀ u ∈ U, φ ⟨s, XbarPre_le_H0 hc s.2⟩ u ∈ U) →
          U = ⊥ ∨ U = cmComm M Q Z B K γ M₀ φ := by
    intro hV U hU hUinv
    have hmc : (U.comap (cmComm M Q Z B K γ M₀ φ).subtype).map
        (cmComm M Q Z B K γ M₀ φ).subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hU]
    have hinv : ∀ g, ∀ w ∈ U.comap (cmComm M Q Z B K γ M₀ φ).subtype,
        ρV g w ∈ U.comap (cmComm M Q Z B K γ M₀ φ).subtype := by
      intro g w hw
      obtain ⟨s, rfl⟩ := (ψ.surjective.comp (xbarHToXbar_surjective hc)) g
      rw [Function.comp_apply, hcompat s]
      exact hUinv ⟨_, (mem_XbarH_iff hc _).mp s.2⟩ w hw
    rcases eq_bot_or_eq_top_of_pow_dvd_card hnd ρV hiso hfix (by omega) hX hV _ hinv with h | h
    · left
      rw [← hmc, h, Submodule.map_bot]
    · right
      rw [← hmc, h, Submodule.map_top, Submodule.range_subtype]
  have hX1 : ⁅Z, XbarPre M Q Z B⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    have hcomm : z * s = s * z :=
      Subgroup.mem_centralizer_iff.mp (XbarPre_le_H0 hc hs).2 z hz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact Z.one_mem
  refine ⟨Z, Z ⊔ ⁅Q, XbarPre M Q Z B⁆, le_rfl, le_sup_left,
    sup_le hc.hyp.Z_normal.1 (commutator_le_Q hc), hX1, rfl, ?_⟩
  rcases hLie with h | h | ⟨rfl, h⟩
  · have h4 : 4 ≤ m := h.admissible.2.2
    have hV : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m := hdim.resolve_right (by omega)
    obtain ⟨X, hXrep, hXirr⟩ :=
      exists_naturalRep_cmComm_of_irreducible hc hD φ hφπ φker (2 * m) hV hfaith (hirr hV)
    exact Or.inl ⟨Or.inl h, K, inferInstance, inferInstance, hKZ, X, hXrep, hXirr⟩
  · have h4 : 4 ≤ m := h.admissible.2.2
    have hV : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m := hdim.resolve_right (by omega)
    obtain ⟨X, hXrep, hXirr⟩ :=
      exists_naturalRep_cmComm_of_irreducible hc hD φ hφπ φker (2 * m) hV hfaith (hirr hV)
    exact Or.inl ⟨Or.inr h, K, inferInstance, inferInstance, hKZ, X, hXrep, hXirr⟩
  · refine Or.inr ⟨rfl, h, ?_⟩
    rcases hdim with hV | ⟨-, hV8⟩
    · obtain ⟨X, hXrep, hXirr⟩ :=
        exists_naturalRep_cmComm_of_irreducible hc hD φ hφπ φker 6 hV hfaith (hirr hV)
      exact Or.inl ⟨K, inferInstance, inferInstance, hKZ, X, hXrep, hXirr⟩
    · exact Or.inr (exists_psu4_module_data hc hD φ hφπ φker hV8 hfaith)

end CFSG.RankThree.GF2n.Stroth80
