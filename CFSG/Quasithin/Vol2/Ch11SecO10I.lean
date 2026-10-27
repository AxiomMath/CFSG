module

public import CFSG.Quasithin.Vol2.Ch11SecO10A
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Vol2.Ch11SecE42S3c

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecE

variable {G : Type} [Group G] [Finite G]

theorem mem_omegaOneCenter_of {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) : z ∈ quasithinOmegaOneCenter T :=
  Subgroup.subset_closure ⟨⟨SecA.fsuV_le_T h hz.1, hz.2⟩, (SecA.isElemAbelian_fsuV h).2 z hz.1⟩

theorem not_kindG2_kz (h331 : Stmt3_3_1) (h1132 : Stmt11_3_2) {T K I' V'₁ : Subgroup G} {n : ℕ}
    (hK : Hyp11 G T K I' n) (hV'₁ : IsVi T K I' n 1 V'₁) {z : G}
    (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hKz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hG2 : KindG2 K (fsuV T I') n) : False := by
  obtain ⟨H, hH⟩ := SecA.exists_isHStar h331 hK
  have hn : 2 ≤ n := hK.one_lt
  have hmoves : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro hc
    have hZH := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hzZ
    apply hH.2.1
    intro x hx
    exact hKz (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hZH x hx))
  have hnot : ¬ KindSL3 K (fsuV T I') n := fun hs =>
    SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn hs hG2
  have hc := h1132 G T K I' n V'₁ H hK hV'₁ ⟨hH, hmoves, fun hs => absurd hs hnot⟩
  exact SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn hc.1 hG2

theorem false_of_rOf_eq_rOf_one (hF : Facts42) (hF43 : Facts43) (hN : SecA.NatFacts)
    (hPar : ParInFacts) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1115 : Stmt11_1_5) (h1141 : Stmt11_4_1) {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}
    {z : G} (hc : Conf11_4_2 T L I n V₁ z) {I' V'₁ : Subgroup G}
    (hK : Hyp11 G T (kz L V₁ z) I' n) (hV'₁ : IsVi T (kz L V₁ z) I' n 1 V'₁)
    (hR : ROf T L V₁ = ROf T (kz L V₁ z) V'₁) : False := by
  have h := hc.hyp
  obtain ⟨-, -, hKz, hnC, -, hzV₁⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hXR := cartan_le_normalizer_rOf hN hPar h1102 h hcV hc.vi hX
  have hNK : Subgroup.normalizer (ROf T (kz L V₁ z) V'₁ : Set G) ≤
      Subgroup.normalizer (kz L V₁ z : Set G) := by
    rcases h1115 G T _ I' n V'₁ hK hV'₁ with hle | ⟨-, -, hCT, -⟩
    · exact hle
    · have hz := mem_inf_centralizer_kz hF43 h1102 h1110 h1111 h1141 hc
      rw [hCT] at hz
      exact absurd (Subgroup.mem_bot.mp hz) hc.ne_one
  rw [hR] at hXR
  exact hnC (le_centralizer_of_cartan hF h1102 h1141 h hc.vi hX hzV₁ hc.ne_one (hXR.trans hNK)
    hKz)

end CFSG.Quasithin.Vol2.Ch11.O10
