module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm
public import CFSG.RankThree.GF2n.Stroth80.Sec7VtQ

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_wild_join (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (h310chi : Stroth310ChiStatement) (hSec : Sec7WVSecCardStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (h4 : OmegaPlusNat hc t 4) {x g : G} (hgM : g ∈ M)
    (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z)
    (hQx : ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t))
    (hex : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) :
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z ∧
      Vt M (LB M Q B) B Z t < Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) ∧
      Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤
        Wt Q (Vt M (LB M Q B) B Z t) ∧
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r (Vt M (LB M Q B) B Z t ⊔
        conjSubgroup g (Vt M (LB M Q B) B Z t)) =
          Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) ∧
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hQM : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hxNV : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    mem_normalizer_Vt_of_comm_mem M Q (LB M Q B) B Z sec39_Q_le_LB hc.hyp.Q_normal.2 hxM
      (hc.conj_Z_eq hxM) hxt
  have hxW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro w hw
    have h1 := conj_mem_Wt (hQM x hxM) hxNV hw
    have e : ⁅x, w⁆ = (x * w * x⁻¹) * w⁻¹ := rfl
    rw [e]
    exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem h1 ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hw)
  let P : Subgroup G := Subgroup.closure
    ({y | ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), y = ⁅x, w⁆} ∪
      ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G))
  have hSP : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ P := fun w hw =>
    Subgroup.subset_closure (Or.inl ⟨w, hw, rfl⟩)
  have hVP : Vt M (LB M Q B) B Z t ≤ P := fun v hv => Subgroup.subset_closure (Or.inr hv)
  have hPW : P ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    rw [Subgroup.closure_le]
    rintro y (⟨w, hw, rfl⟩ | hy)
    · exact hxW w hw
    · exact hVW hy
  have hPle : P ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [Subgroup.closure_le]
    rintro y (⟨w, hw, rfl⟩ | hy)
    · exact Subgroup.mem_sup_right (hQx w (hWQ hw))
    · exact Subgroup.mem_sup_left hy
  have hVlt : Vt M (LB M Q B) B Z t < P := by
    obtain ⟨w0, hw0, hw0V⟩ := hex
    refine lt_of_le_of_ne hVP fun h => hw0V ?_
    rw [h]
    exact hSP w0 hw0
  have hRinv : ∀ r ∈ Rt M (LB M Q B) t, ∀ p ∈ P, r * p * r⁻¹ ∈ P := by
    intro r hr p hp
    have hrN : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      hc.Rt_normalizes_Vt ht hr
    have hcN : ⁅r, x⁆ ∈ hc.CN t := comm_mem_CN_of_vanish hc hs hxM hxt hxV hr
    induction hp using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | hy
      · have hw' : r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
          conj_mem_Wt (hQM r (hRM hr)) hrN hw
        have h1 := sec7_N_comm_W_le_V h52a hA hc hs _ hcN _ (hxW _ hw')
        have h3 := sec7_N_comm_W_le_V h52a hA hc hs _ hcN _ hw'
        have e : r * ⁅x, w⁆ * r⁻¹ = ⁅⁅r, x⁆, ⁅x, r * w * r⁻¹⁆⁆ * ⁅x, r * w * r⁻¹⁆ *
            ⁅⁅r, x⁆, r * w * r⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact P.mul_mem (P.mul_mem (hVP h1) (hSP _ hw')) (hVP h3)
      · exact hVP ((Subgroup.mem_normalizer_iff.mp hrN y).mp hy)
    | one => simpa using P.one_mem
    | mul a b _ _ ha hb =>
      have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
      rw [e]
      exact P.mul_mem ha hb
    | inv a _ ha =>
      have e : r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
      rw [e]
      exact P.inv_mem ha
  have hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P := by
    intro r hr
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : r⁻¹ * y * r ∈ P := mem_conjSubgroup.mp hy
      have := hRinv r hr _ hy'
      simpa [mul_assoc] using this
    · rw [mem_conjSubgroup]
      have := hRinv r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr) y hy
      simpa using this
  obtain ⟨k, hk⟩ := ((hSec G M Q Z B hc n t hs P hVP hPW hPR 4 (by norm_num)).2 h4 (by norm_num))
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hV9 := card_Vt_orthogonal hc (t := t) (m := 4) (by norm_num) (Or.inl h4)
  have hV8 : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card ↥Z * Nat.card ↥Z ^ 8 := by
    simpa using hV9
  have hsupcard := card_sup_conj_mul_le hc hZV hVQ hgM
  have hinfsup := card_sup_mul_card_inf_conj hc hZV hVQ hgM
  have hPle_card : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊔
      conjSubgroup g (Vt M (LB M Q B) B Z t)) := Subgroup.card_le_of_le hPle
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hsup8 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 := by
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) *
          Nat.card ↥Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) *
            Nat.card ↥(Vt M (LB M Q B) B Z t) := hsupcard
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * (Nat.card ↥Z * Nat.card ↥Z ^ 8) := by
        rw [← hV8]
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 * Nat.card ↥Z := by ring
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hP1 : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact hVlt.ne (Subgroup.eq_of_le_of_card_ge hVP hP1)
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have h8 : 2 ^ (4 - 1) * k = 8 * k := by norm_num
    rw [h8] at hk
    have hpow : Nat.card ↥Z ^ 16 ≤ Nat.card ↥Z ^ (8 * k) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 16 ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 := by
      calc Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 16 ≤
          Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (8 * k) :=
            Nat.mul_le_mul_left _ hpow
        _ = Nat.card ↥P := hk.symm
        _ ≤ _ := hPle_card.trans hsup8
    have h2 : Nat.card ↥Z ^ 16 ≤ Nat.card ↥Z ^ 8 := Nat.le_of_mul_le_mul_left h1 hVpos
    have h3 : Nat.card ↥Z ^ 8 < Nat.card ↥Z ^ 16 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  subst hk1
  have hP8 : Nat.card ↥P = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 := by
    rw [hk]
    norm_num
  have hPeq : P = Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    Subgroup.eq_of_le_of_card_ge hPle (by rw [hP8]; exact hsup8)
  rw [← hPeq]
  refine ⟨?_, hVlt, hPW, hPR, hP8⟩
  have hZg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := hc.Z_le_conjSubgroup hZV hgM
  rw [hPeq] at hP8
  have hcancel : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) *
      Nat.card ↥Z ^ 8 = Nat.card ↥Z * Nat.card ↥Z ^ 8 := by
    refine Nat.eq_of_mul_eq_mul_left hVpos ?_
    calc Nat.card ↥(Vt M (LB M Q B) B Z t) *
          (Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) *
            Nat.card ↥Z ^ 8) =
        (Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8) *
          Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) := by ring
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t) := by
        rw [← hP8]
        exact hinfsup
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * (Nat.card ↥Z * Nat.card ↥Z ^ 8) := by
        rw [← hV8]
  have hinf : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥Z :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hZpos 8) hcancel
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hZV hZg) (le_of_eq hinf)).symm

end CFSG.RankThree.GF2n.Stroth80
