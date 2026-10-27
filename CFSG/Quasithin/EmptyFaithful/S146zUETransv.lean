module

public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.F9G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

namespace S146zU

namespace UE

section Sup

variable {G : Type*} [Group G]

theorem mIdx_sup_le_one {X C Z : Subgroup G} (hXC : X ≤ C) (hC : Nat.card C = 2)
    (hN : C ≤ Subgroup.normalizer (Z : Set G)) : mIdx (X ⊔ Z) Z ≤ 1 := by
  have hdvd : Z.relIndex (X ⊔ Z) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff']
    rcases HypF98.eq_bot_or_eq_of_card_eq_two hC hXC with hX | hX
    · refine ⟨1, Subgroup.one_mem _, fun b hb => Or.inr ?_⟩
      rwa [hX, bot_sup_eq] at hb
    · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥C)).mp hC
      have hyy : (y : G) * y = 1 := by
        have hmem : y * y ∈ ({1, y} : Set ↥C) := by
          by_cases h1 : y * y = 1
          · exact Or.inl h1
          · exact Or.inr (huniq _ h1)
        rcases hmem with h1 | h1
        · simpa using congrArg Subtype.val h1
        · exfalso
          have : y = 1 := by simpa using h1
          exact hy this
      have hXN : X ≤ Subgroup.normalizer (Z : Set G) := hX ▸ hN
      refine ⟨(y : G), Subgroup.mem_sup_left (hX ▸ y.2), fun b hb => ?_⟩
      have hb' : b ∈ ((X ⊔ Z : Subgroup G) : Set G) := hb
      rw [Subgroup.coe_mul_of_left_le_normalizer_right X Z hXN] at hb'
      obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hb'
      by_cases hx1 : (⟨x, hX ▸ hx⟩ : ↥C) = 1
      · right
        have : x = 1 := by simpa using congrArg Subtype.val hx1
        rw [this, one_mul]
        exact hz
      · left
        have hxy : (⟨x, hX ▸ hx⟩ : ↥C) = y := huniq _ hx1
        have : x = y := by simpa using congrArg Subtype.val hxy
        rw [this, ← mul_assoc, hyy, one_mul]
        exact hz
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · simp [mIdx, h]
  · simp [mIdx, h]

end Sup

section Transv

variable {G : Type*} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

theorem exists_conj_pair_of_transvection (h : HypF98 T V L V₁ Vp H)
    (s : F8Setup T V L H γ γ' g) {W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hWV : W ≤ conjClosure V H) (hcomm : ⁅W, F8.Uγ Vp H (g : G)⁆ = V₁) :
    ∃ B C : Subgroup G, B ≤ H ∧ IsElemAbelian 2 B ∧ ¬ B ≤ pCoreOf 2 H ∧
      ⁅B, conjClosure Vp H⁆ = C ∧ C ≤ conjClosure Vp H ∧ Nat.card C = 2 ∧ C ⊓ V₁ = ⊥ := by
  have hBL := h.conjSub_inv_V_le_pCoreOf_L₁T s hWV
  have hBH : conjSub (g : G)⁻¹ W ≤ H :=
    hBL.trans ((pCoreOf_le 2 _).trans h.L₁T_le_H)
  have hBel := isElemAbelian_conjSub (g := (g : G)⁻¹) hW
  have hcardV₁' : Nat.card (conjSub (g : G)⁻¹ V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
  have hUconj : conjSub (g : G)⁻¹ (F8.Uγ Vp H (g : G)) = conjClosure Vp H := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hBU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ = conjSub (g : G)⁻¹ V₁ := by
    rw [← hUconj, conjSub_commutator, hcomm]
  have hV₁'inf : conjSub (g : G)⁻¹ V₁ ⊓ V₁ = ⊥ := by
    have h5b := h.F913_5b s
    have := congrArg (conjSub (g : G)⁻¹) h5b
    rw [conjSub_inf, conjSub_bot] at this
    have e : conjSub (g : G)⁻¹ (F8.A₁ V₁ (g : G)) = V₁ := by
      rw [F8.A₁, conjSub_conjSub_inv]
    rwa [e] at this
  have hBUU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ conjClosure Vp H := by
    refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
    have hbH := hBH hb
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hbH) u).mp hu
    show b * u * b⁻¹ * u⁻¹ ∈ conjClosure Vp H
    exact (conjClosure Vp H).mul_mem (by simpa using this) ((conjClosure Vp H).inv_mem hu)
  refine ⟨conjSub (g : G)⁻¹ W, conjSub (g : G)⁻¹ V₁, hBH, hBel, ?_, hBU, hBU ▸ hBUU, hcardV₁',
    hV₁'inf⟩
  intro hle
  have h1 : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
    have := V₁.inv_mem (h.commutator_conjClosure_le u hu b (hle hb))
    have e : (u * b * u⁻¹ * b⁻¹)⁻¹ = b * u * b⁻¹ * u⁻¹ := by group
    rwa [e] at this
  rw [hBU] at h1
  have : conjSub (g : G)⁻¹ V₁ = ⊥ := le_bot_iff.mp (hV₁'inf ▸ le_inf le_rfl h1)
  have h2 : Nat.card (conjSub (g : G)⁻¹ V₁) = 1 := by rw [this]; simp
  omega

theorem exists_element_rank_le_one (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    (hD : F8.Uγ Vp H (g : G) = F8.Dγ Vp V₁ H (g : G)) :
    ∃ b ∈ H, b ∉ pCoreOf 2 H ∧
      mIdx (⁅conjClosure Vp H, Subgroup.zpowers b⁆ ⊔ V₁) V₁ ≤ 1 := by
  have key : ∀ {W : Subgroup G}, IsElemAbelian 2 W → W ≤ conjClosure V H →
      ⁅W, F8.Uγ Vp H (g : G)⁆ = V₁ →
      ∃ b ∈ H, b ∉ pCoreOf 2 H ∧
        mIdx (⁅conjClosure Vp H, Subgroup.zpowers b⁆ ⊔ V₁) V₁ ≤ 1 := by
    intro W hW hWV hcomm
    obtain ⟨B, C, hBH, -, hBQ, hBU, hCU, hC, -⟩ :=
      exists_conj_pair_of_transvection h s hW hWV hcomm
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    refine ⟨b, hBH hb, hbQ, ?_⟩
    have hle : ⁅conjClosure Vp H, Subgroup.zpowers b⁆ ≤ C := by
      rw [← hBU, Subgroup.commutator_comm B]
      exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hb)
    have hCN : C ≤ Subgroup.normalizer (V₁ : Set G) :=
      hCU.trans (h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans h.H_normalizes_V₁))
    exact mIdx_sup_le_one hle hC hCN
  rcases h.F916_1 s hD with ⟨-, -, -, hT⟩ | ⟨-, -, -, -, hT⟩
  · exact key h.F911_3 (conjClosure_mono h.Vp_le_V le_rfl) hT
  · exact key h.elemAbelian (le_conjClosure V H) hT

end Transv

end UE

end S146zU

end CFSG.Quasithin
