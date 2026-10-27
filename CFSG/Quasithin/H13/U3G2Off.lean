module

public import CFSG.Quasithin.H13.U3G2Img
public import CFSG.Quasithin.H13.U3X10U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G]

theorem isMaxElemAbelian_le_baum [Finite G] {R A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    A ≤ baum R := by
  refine le_inf hA.1 ?_
  rw [le_centralizer_iff]
  intro c hc a ha
  have hcA : c ∈ A := by
    rw [(omegaOne_centralizer_thompsonJ R).2] at hc
    exact (mem_iInf.1 (mem_iInf.1 hc A) hA)
  exact B2F.isElemAbelian_comm hA.2.1 ha hcA

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem L₁_le
    (S : HullSetting G T L V z) : L₁Of L S.V₁ ≤ L :=
  (oTwoRes_le _).trans inf_le_left

theorem V_le_R₁
    (S : HullSetting G T L V z) : V ≤ pCoreOf 2 (L₁Of L S.V₁ ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (S.hVT.trans le_sup_right)
    (sup_le (S.L₁_le.trans S.hLV) S.hTV)
    (B2F.isPGroup_of_isElemAbelian (isElemAbelian_of_isElementaryAbelian' V))

theorem R₁_le_T
    (S : HullSetting G T L V z) : pCoreOf 2 (L₁Of L S.V₁ ⊔ T) ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (A5.isSylowTwoOf_of_le S.hH.sylow le_sup_right)

theorem le_normalizer_R₁
    (S : HullSetting G T L V z) :
    L₁Of L S.V₁ ⊔ T ≤ normalizer (pCoreOf 2 (L₁Of L S.V₁ ⊔ T) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem l₁_mem_L₁T
    (S : HullSetting G T L V z) : S.l₁ ∈ L₁Of L S.V₁ ⊔ T := by
  have hl₁N : S.l₁ ∈ L ⊓ normalizer (S.V₁ : Set G) := by
    rw [S.normalizer_V₁]
    exact ⟨S.l₁_mem, S.l₁_H⟩
  exact S.inf_normalizer_V₁_le hl₁N

theorem imgL_eq_bot_iff
    (S : HullSetting G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) :
    S.imgL X = ⊥ ↔ X ≤ centralizer (V : Set G) := by
  constructor
  · intro h x hx
    have h1 := S.glLin_rho_mem_imgL hx (hXN hx)
    rw [h, mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact (mem_centralizer_V_iff (hXN hx) (S.rho_spec _)).2 h1
  · intro h
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL.1 hg
    rw [mem_bot, (mem_centralizer_V_iff hxN (S.rho_spec _)).1 (h hxX), map_one]

theorem offender_eq
    (S : HullSetting G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) A) :
    (A ⊓ centralizer (V : Set G)).relIndex A * Nat.card ↥(V ⊓ centralizer (A : Set G)) = 64 :=
  le_antisymm (S.card_mul_card_le (hA.1.trans S.R₁_le_T) hA.2.1)
    (S.hV64 ▸ card_le_relIndex_mul_card (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁ hA)

theorem imgL_A
    (S : HullSetting G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) A) :
    S.imgL A = ⊥ ∨ IsA1 (S.imgL A) := by
  have hAT : A ≤ T := hA.1.trans S.R₁_le_T
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans S.hTV
  by_cases hbot : S.imgL A = ⊥
  · exact Or.inl hbot
  right
  refine isA1_of_xStable (S.imgL_le_S0L hAT) (S.isElementaryAbelian_imgL hA.2.1) ?_ hbot ?_
  · rw [S.card_imgL hAN, ← S.card_inf_centralizer hAN]
    exact S.offender_eq hA
  · intro e he
    obtain ⟨a, haN, haA, rfl⟩ := S.mem_imgL.1 he
    have hl₁ : S.l₁ ∈ normalizer (pCoreOf 2 (L₁Of L S.V₁ ⊔ T) : Set G) :=
      S.le_normalizer_R₁ S.l₁_mem_L₁T
    have hc : S.l₁ * a * S.l₁⁻¹ ∈ T :=
      S.R₁_le_T ((mem_normalizer_iff.1 hl₁ a).1 (hA.1 haA))
    have hρ : S.rho ⟨S.l₁, S.l₁_N⟩ = xGL := S.rho_eq_of_spec S.l₁_N S.l₁_spec
    have e : (⟨S.l₁ * a * S.l₁⁻¹, S.hTV hc⟩ : normalizer (V : Set G)) =
        ⟨S.l₁, S.l₁_N⟩ * ⟨a, haN⟩ * ⟨S.l₁, S.l₁_N⟩⁻¹ := rfl
    have h1 := S.rho_T_mem hc
    rw [e, map_mul, map_mul, map_inv, hρ] at h1
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem V₃_le_A
    (S : HullSetting G T L V z) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) A) : S.V₃ ≤ A := by
  have hAN : A ≤ normalizer (V : Set G) := (hA.1.trans S.R₁_le_T).trans S.hTV
  rcases S.imgL_A hA with h | h
  · have hAC := (S.imgL_eq_bot_iff hAN).1 h
    have hsup := (B24_three (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁ hA (S.hV64.trans
      (S.offender_eq hA).symm)).1
    rw [inf_eq_left.2 hAC] at hsup
    have heq : A = A ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hsup.1 hsup.2.1)
    exact S.le3.trans (heq ▸ le_sup_right)
  · have h1 := S.inf_centralizer_eq hAN
    rw [h.linFix_eq, ← S.V₃_eq_pullSub] at h1
    rw [← h1]
    exact inf_centralizer_le_of_isMaxElemAbelian (isElemAbelian_of_isElementaryAbelian' V)
      S.V_le_R₁ hA

theorem B_le
    (S : HullSetting G T L V z) :
    baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ≤ centralizer (S.V₃ : Set G) := by
  have h : S.V₃ ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))) := by
    rw [(omegaOne_centralizer_thompsonJ _).2]
    exact le_iInf₂ fun A hA => S.V₃_le_A hA
  exact inf_le_right.trans (centralizer_le h)

theorem V_le_B
    (S : HullSetting G T L V z) : V ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))
  have hsup := (B24_three (isElemAbelian_of_isElementaryAbelian' V) S.V_le_R₁ hA (S.hV64.trans
    (S.offender_eq hA).symm)).1
  exact le_sup_right.trans (isMaxElemAbelian_le_baum hsup)

theorem B_le_T
    (S : HullSetting G T L V z) : baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ≤ T :=
  inf_le_left.trans S.R₁_le_T

theorem T_le_normalizer_B
    (S : HullSetting G T L V z) :
    T ≤ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G) :=
  (le_sup_right.trans S.le_normalizer_R₁).trans (normalizer_le_normalizer_baum _)

theorem imgL_B_fix
    (S : HullSetting G T L V z) :
    ∀ e ∈ S.imgL (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))), ∀ w ∈ V3sub, e w = w := by
  intro e he w hw
  obtain ⟨b, hbN, hbB, rfl⟩ := S.mem_imgL.1 he
  have h1 : b ∈ centralizer (pullSub S.Φ V3sub : Set G) := by
    rw [← S.V₃_eq_pullSub]
    exact S.B_le hbB
  exact (mem_centralizer_pullSub_iff hbN (S.rho_spec _) V3sub).1 h1 w hw

theorem card_B_le
    (S : HullSetting G T L V z) :
    (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)).relIndex
      (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))) ≤ 8 := by
  rw [← S.card_imgL (S.B_le_T.trans S.hTV)]
  exact card_le_eight_of_fix (S.imgL_le_S0L S.B_le_T) S.imgL_B_fix

end HullSetting

end CFSG.Quasithin.H13.U3
