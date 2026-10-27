module

public import CFSG.RankThree.GF2n.Stroth80.Sec54Final
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Split
public import CFSG.RankThree.GF2n.Stroth80.Sec54Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem comm_mul_left_mul_inv (q x u : G) :
    ⁅q * x, u⁆ * ⁅x, u⁆⁻¹ = ⁅q, x * u * x⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

private theorem comm_mul_right (x a b : G) : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

private theorem conj_comm_eq (s x y : G) :
    ⁅s, ⁅x, y⁆⁆ = ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem stroth54FC_hNW_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hN : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z) :
    ∀ x ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, y⁆ ∈ Z := by
  classical
  have hsp : SpNat hc t := by
    obtain ⟨K, hK, hKf, hKc, hrep⟩ := hV
    exact ⟨K, hK, hKf, hKc, m, hm, hrep⟩
  have hs8 : Sec8Hyp hc n t := ⟨hs, ⟨m, hm, hV⟩⟩
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot hs hsp
  have hs6 : Stroth6Hyp hc n t := ⟨hs, hN⟩
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set W1 : Subgroup G := Sec8W1 M Q Z B t r with hW1def
  have hWQ : W ≤ Q := inf_le_left
  have hW1Q : W1 ≤ Q := inf_le_left
  have hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hc.hyp.toHyp79.comm_mem_V ha hb
  have hRN : ∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ⁅s, x⁆ ∈ Q :=
    HS6.central_of_hypPlane h51 hc hs6 (Or.inl hsp) hr hplane
  have hRW : ∀ s ∈ Rt M (LB M Q B) t, ∀ y ∈ W, ⁅s, y⁆ ∈ W1 :=
    sec54_comm_W_le_W1 h34 hRoot h51 hc hs hm hV hs8 hr hplane
  have hNW1 : ∀ x ∈ hc.CN t, ∀ w ∈ W1, ⁅x, w⁆ ∈ Z := by
    intro x hx w hw
    have hw' : w ∈ Sec8V1 M Q Z B t r := by
      rw [sec54_vone_eq_Wt h34 hRoot h51 hc hs hm hV hN hr hplane]
      exact hw
    exact sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane x hx w hw'
  intro x hx y hy
  have hxR : x ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hx).1
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hxM
  have hxW : x ∈ Subgroup.normalizer (W : Set G) :=
    sec8_Wt_mem_normalizer hxQ (hc.Rt_normalizes_Vt hs.mem hxR)
  have hwW : ⁅x, y⁆ ∈ W := by
    rw [commutatorElement_def]
    exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp hxW y).mp hy) (W.inv_mem hy)
  have hwR : ∀ s ∈ Rt M (LB M Q B) t, ⁅s, ⁅x, y⁆⁆ ∈ Z := by
    intro s hsR
    have hq : ⁅s, x⁆ ∈ Q := hRN s hsR x hx
    have hw1 : ⁅s, y⁆ ∈ W1 := hRW s hsR y hy
    have hu : ⁅s, y⁆ * y ∈ Q := Q.mul_mem (hW1Q hw1) (hWQ hy)
    have hxu : x * (⁅s, y⁆ * y) * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ _).mp hu
    have h1 : ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, ⁅s, y⁆ * y⁆⁻¹ ∈ Z := by
      rw [comm_mul_left_mul_inv]
      exact hQQ _ hq _ hxu
    have h2 : ⁅x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ ∈ Z := by
      rw [comm_mul_right]
      have h3 : ⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹ * ⁅x, y⁆⁻¹ ∈ Z := by
        have := hQQ _ (hW1Q hw1) _ (hWQ hwW)
        rwa [commutatorElement_def] at this
      have h4 : ⁅x, ⁅s, y⁆⁆ ∈ Z := hNW1 x hx _ hw1
      have e : ⁅x, ⁅s, y⁆⁆ * (⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹) * ⁅x, y⁆⁻¹ =
          ⁅x, ⁅s, y⁆⁆ * (⁅s, y⁆ * ⁅x, y⁆ * ⁅s, y⁆⁻¹ * ⁅x, y⁆⁻¹) := by group
      rw [e]
      exact Z.mul_mem h4 h3
    rw [conj_comm_eq]
    have e : ⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹ =
        (⁅⁅s, x⁆ * x, ⁅s, y⁆ * y⁆ * ⁅x, ⁅s, y⁆ * y⁆⁻¹) * (⁅x, ⁅s, y⁆ * y⁆ * ⁅x, y⁆⁻¹) := by group
    rw [e]
    exact Z.mul_mem h1 h2
  exact sec54_centralizer_Wt_le_Z h34 hRoot h51 hc hs hm hV hr hplane hwW hwR

end CFSG.RankThree.GF2n.Stroth80
