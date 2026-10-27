module

public import CFSG.RankThree.GF2n.Tim78S48AffCent
import CFSG.RankThree.GF2n.Tim78S48AffCnt
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

open Aff

namespace Aff

theorem comm_comm_self (x y : G) (hy : y * y = 1) :
    ⁅⁅x, y⁆, y⁆ = ⁅x, y⁆ * ⁅x, y⁆ := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hyy : ∀ z : G, y * (y * z) = z := fun z => by rw [← mul_assoc, hy, one_mul]
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hyinv, mul_assoc, hyy]

end Aff

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H


theorem aC_cent_W (h48 : Hyp48 M B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {c : G} (hc : c ∈ H.aC g) :
    ∀ w ∈ B ⊔ conjSubgroup g B, c * w = w * c := by
  intro w hw
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy =>
      (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
  have h1 : c * b = b * c := (H.center_Q hb (H.aC_le_Q hc)).symm
  calc c * (b * z) = (c * b) * z := by group
    _ = (b * c) * z := by rw [h1]
    _ = b * (c * z) := by group
    _ = b * (z * c) := by rw [hcent c hc z hz]
    _ = (b * z) * c := by group

theorem aC_le_conj_M
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    H.aC g ≤ conjSubgroup g M := by
  intro c hc
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_B_ne_bot g)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  exact H.centralizer_le_conj hy hy1'
    (Subgroup.mem_centralizer_singleton_iff.mpr (hcent c hc y hy))

theorem aC_le_normalizer_Tg
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    H.aC g ≤ Subgroup.normalizer (conjSubgroup g T : Set G) := fun _ hc =>
  mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (H.aC_le_conj_M hcent hc)

theorem aC_comm_mem_kernel (h48 : Hyp48 M B T g)
    (htrans : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B),
      ∃ h ∈ T ⊔ conjSubgroup g T, U = conjSubgroup h B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {c x : G}
    (hc : c ∈ H.aC g) (hx : x ∈ T ⊔ conjSubgroup g T) : ⁅x, c⁆ ∈ kernel48 B T g := by
  have h := comm_mem_kernel (H.X_le_normalizer_W h48)
    (H.aC_le_normalizer_X h48 htrans hc) (H.aC_cent_W h48 hcent hc) hx
  have e : ⁅x, c⁆ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact (kernel48 B T g).inv_mem h

theorem aC_comm_Tg (h48 : Hyp48 M B T g)
    (htrans : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B),
      ∃ h ∈ T ⊔ conjSubgroup g T, U = conjSubgroup h B)
    (hcomm : ∀ h ∈ T ⊔ conjSubgroup g T, ∀ k ∈ kernel48 B T g, ⁅h, k⁆ ∈ B ⊔ conjSubgroup g B)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {c t' : G}
    (hc : c ∈ H.aC g) (ht' : t' ∈ conjSubgroup g T) : ⁅t', c⁆ ∈ conjSubgroup g B := by
  obtain ⟨x, hxX, hxB⟩ := htrans _ ⟨⟨g, rfl⟩, le_sup_right⟩
  have hxT : conjSubgroup g T = conjSubgroup x T := H.conj_T_eq_of_conj_B_eq hxB
  have ht'g := ht'
  rw [hxT] at ht'
  obtain ⟨t, ht, rfl⟩ := mem_conj_iff.mp ht'
  have hk : ⁅x⁻¹, c⁆ ∈ kernel48 B T g :=
    H.aC_comm_mem_kernel h48 htrans hcent hc ((T ⊔ conjSubgroup g T).inv_mem hxX)
  have hkW : ⁅t, ⁅x⁻¹, c⁆⁆ ∈ B ⊔ conjSubgroup g B :=
    hcomm t (Subgroup.mem_sup_left ht) _ hk
  have htc : t * c = c * t :=
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) c hc.1).symm
  have hct : c * t⁻¹ * c⁻¹ = t⁻¹ := by
    have : c * t⁻¹ = t⁻¹ * c := by
      have := congrArg (fun z => t⁻¹ * z * t⁻¹) htc
      simpa [mul_assoc] using this
    rw [this]; group
  have e1 : ⁅t, x⁻¹ * c * x⁆ = ⁅t, ⁅x⁻¹, c⁆⁆ := by
    have e2 : x⁻¹ * c * x = ⁅x⁻¹, c⁆ * c := by simp only [commutatorElement_def]; group
    rw [e2]
    set k := ⁅x⁻¹, c⁆ with hkdef
    calc ⁅t, k * c⁆ = t * k * (c * t⁻¹ * c⁻¹) * k⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅t, k⁆ := by rw [hct]; simp only [commutatorElement_def]
  have e : ⁅x * t * x⁻¹, c⁆ = x * ⁅t, ⁅x⁻¹, c⁆⁆ * x⁻¹ := by
    rw [← e1]; simp only [commutatorElement_def]; group
  have hW : ⁅x * t * x⁻¹, c⁆ ∈ B ⊔ conjSubgroup g B := by
    rw [e]
    have hxW := H.X_le_normalizer_W h48 hxX
    exact (Subgroup.mem_normalizer_iff.mp hxW _).mp hkW |> fun h => by
      simpa [mul_assoc] using h
  have hTg : ⁅x * t * x⁻¹, c⁆ ∈ conjSubgroup g T := by
    have hcN := H.aC_le_normalizer_Tg hcent hc
    have : ⁅x * t * x⁻¹, c⁆ = (x * t * x⁻¹) * (c * (x * t * x⁻¹)⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact (conjSubgroup g T).mul_mem ht'g ((Subgroup.mem_normalizer_iff.mp hcN _).mp
      ((conjSubgroup g T).inv_mem ht'g))
  rw [← hTgW]
  exact ⟨hTg, hW⟩


theorem aC_sq_eq_one (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {c : G} (hc : c ∈ H.aC g) :
    c * c = 1 := by
  obtain ⟨n, hn, hnat, hpart, htrans, hKel, hKform, hWA, hA, hcomm, hrel, K₁, hK₁X, hK₁B, hK₁Bg,
    hK₁cyc, hK₁card, hK₁A, hK₁fpf, hK₁pts⟩ := h1
  have hc2B : c * c ∈ B := by
    have := H.sq_mem (H.aC_le_Q hc)
    rwa [pow_two] at this
  have hWK : B ⊔ conjSubgroup g B ≤ kernel48 B T g := by
    show _ ≤ (T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)
    rw [hKform]; exact le_sup_left
  have hAK : T ⊓ conjSubgroup g T ≤ kernel48 B T g := by
    show _ ≤ (T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)
    rw [hKform]; exact le_sup_right
  have hcK : ∀ k ∈ kernel48 B T g, c * k = k * c := by
    intro k hk
    have hk' : k ∈ (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) := by rw [← hKform]; exact hk
    obtain ⟨w, hw, a, ha, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun a ha w hw => comm_of_isElemAbelian hKel (hAK ha) (hWK hw)) hk'
    have hca : c * a = a * c :=
      Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ha.1) c hc.1
    calc c * (w * a) = (c * w) * a := by group
      _ = (w * c) * a := by rw [H.aC_cent_W h48 hcent hc w hw]
      _ = w * (c * a) := by group
      _ = w * (a * c) := by rw [hca]
      _ = (w * a) * c := by group
  have hX : ∀ h ∈ T ⊔ conjSubgroup g T, h * (c * c) * h⁻¹ = c * c := by
    intro h hh
    have hk := H.aC_comm_mem_kernel h48 htrans hcent hc hh
    set k := ⁅h, c⁆ with hkdef
    have hkc : c * k = k * c := hcK k hk
    have hkk : k * k = 1 := IsElemAbelian.mul_self_eq_one hKel hk
    have e1 : h * c * h⁻¹ = k * c := by simp only [hkdef, commutatorElement_def]; group
    calc h * (c * c) * h⁻¹ = (h * c * h⁻¹) * (h * c * h⁻¹) := by group
      _ = (k * c) * (k * c) := by rw [e1]
      _ = k * (c * k) * c := by group
      _ = k * (k * c) * c := by rw [hkc]
      _ = (k * k) * (c * c) := by group
      _ = c * c := by rw [hkk, one_mul]
  have hK₁ne : K₁ ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h, Subgroup.card_bot] at hK₁card
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₁ne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  exact hK₁fpf x hx hx1' (c * c) hc2B (hX x (hK₁X hx))

theorem aC_elem (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    Assembly.IsElemAbelian 2 (H.aC g) := by
  have hsq : ∀ c ∈ H.aC g, c * c = 1 := fun c hc => H.aC_sq_eq_one h48 h1 hcent hc
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact comm_of_mul_self_eq_one (hsq a a.2) (hsq b b.2) (hsq _ ((H.aC g).mul_mem a.2 b.2))
  · rw [pow_two]; exact hsq x hx


theorem aC_inf_Bg (hBgQ : conjSubgroup g B ⊓ Q = ⊥) : H.aC g ⊓ conjSubgroup g B = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_right _ H.aC_le_P).trans (H.P_inf_Bg hBgQ).le)

theorem card_aL (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    Nat.card (H.aC g ⊔ conjSubgroup g B : Subgroup G) = Nat.card (H.aC g) * Nat.card B := by
  have hnorm : H.aC g ≤ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    le_normalizer_of_comm hcent
  have h := PartTwo.Sec6.card_sup_mul_card_inf hnorm
  rw [H.aC_inf_Bg hBgQ, Subgroup.card_bot, mul_one, card_conjSubgroup] at h
  exact h

theorem relIndex_aL (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    (H.aC g).relIndex (H.aC g ⊔ conjSubgroup g B) = Nat.card B := by
  have h := Subgroup.relIndex_mul_card (H := H.aC g) (K := H.aC g ⊔ conjSubgroup g B)
  rw [inf_eq_left.mpr le_sup_left, H.card_aL hBgQ hcent, mul_comm (Nat.card (H.aC g))] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem aL_elem (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    Assembly.IsElemAbelian 2 (H.aC g ⊔ conjSubgroup g B) :=
  IsElemAbelian.sup_of_commute (H.aC_elem h48 h1 hcent)
    (isElemAbelian_conjSubgroup H.elemAb g) hcent

theorem aC_conj_Q (h48 : Hyp48 M B T g) {x c : G} (hx : x ∈ Q) (hc : c ∈ H.aC g) :
    x * c * x⁻¹ ∈ H.aC g := by
  have e : x * c * x⁻¹ = ⁅x, c⁆ * c := by simp only [commutatorElement_def]; group
  rw [e]
  exact (H.aC g).mul_mem (H.B_le_aC h48 (H.commutator_mem hx (H.aC_le_Q hc))) hc

theorem comm_Q_Bg_mem_aC (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hpart : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U)
    {x y : G} (hx : x ∈ Q) (hy : y ∈ conjSubgroup g B) : ⁅x, y⁆ ∈ H.aC g := by
  by_cases hy1 : y = 1
  · rw [hy1]; simpa using (H.aC g).one_mem
  have hxPT : x ∈ P ⊔ T := H.Q_eq_sup ▸ hx
  obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun t ht p hp =>
      (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) p hp).symm) hxPT
  have hyP : y ∈ Subgroup.normalizer (P : Set G) := H.M_le_normalizer_P (h48.leM hy)
  have hxy : ⁅p * t, y⁆ ∈ P := by
    have e : ⁅p * t, y⁆ = (p * ⁅t, y⁆ * p⁻¹) * ⁅p, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine P.mul_mem ?_ ?_
    · have hty : ⁅t, y⁆ ∈ B := by
        have := B.inv_mem (h48.comm_T y hy t ht)
        rwa [commutatorElement_inv] at this
      exact (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P (H.P_le_M hp)) _).mp
        (H.B_le_P hty) |> fun h => by simpa [mul_assoc] using h
    · have e2 : ⁅p, y⁆ = p * (y * p⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e2]
      exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp hyP p⁻¹).mp (P.inv_mem hp))
  refine H.mem_aC_of_comm_mem h48 hP hBgQ hpart hxy hy hy1 ?_
  have hyy : y * y = 1 := IsElemAbelian.mul_self_eq_one (isElemAbelian_conjSubgroup H.elemAb g) hy
  rw [comm_comm_self _ _ hyy]
  have := H.sq_mem (H.P_le_Q hxy)
  rwa [pow_two] at this


theorem Q_comm_aL (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hpart : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {x l : G} (hx : x ∈ Q)
    (hl : l ∈ H.aC g ⊔ conjSubgroup g B) : ⁅x, l⁆ ∈ H.aC g := by
  obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun y hy c hc => (hcent c hc y hy).symm) hl
  have e : ⁅x, c * y⁆ = (x * c * x⁻¹) * ⁅x, y⁆ * c⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (H.aC g).mul_mem ((H.aC g).mul_mem (H.aC_conj_Q h48 hx hc)
    (H.comm_Q_Bg_mem_aC h48 hP hBgQ hpart hx hy)) ((H.aC g).inv_mem hc)

theorem Q_le_normalizer_aL (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hpart : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    Q ≤ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun l hl => ?_
  have e : x * l * x⁻¹ = ⁅x, l⁆ * l := by simp only [commutatorElement_def]; group
  rw [e]
  exact (H.aC g ⊔ conjSubgroup g B).mul_mem (Subgroup.mem_sup_left
    (H.Q_comm_aL h48 hP hBgQ hpart hcent hx hl)) hl

theorem T_comm_aL (h48 : Hyp48 M B T g) {t l : G} (ht : t ∈ T)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hl : l ∈ H.aC g ⊔ conjSubgroup g B) : ⁅l, t⁆ ∈ B := by
  obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun y hy c hc => (hcent c hc y hy).symm) hl
  have hct : c * t = t * c := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) c hc.1
  have e : ⁅c * y, t⁆ = c * ⁅y, t⁆ * c⁻¹ * ⁅c, t⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : ⁅c, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hct
  rw [e, h1, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp (H.P_le_normalizer_B hc.1) _).mp (h48.comm_T y hy t ht)

theorem T_inf_centralizer_aL (h48 : Hyp48 M B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    T ⊓ Subgroup.centralizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G) =
      T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  have hWL : B ⊔ conjSubgroup g B ≤ H.aC g ⊔ conjSubgroup g B :=
    sup_le_sup_right (H.B_le_aC h48) _
  ext t
  constructor
  · rintro ⟨ht, hc⟩
    exact ⟨ht, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWL) hc⟩
  · rintro ⟨ht, hc⟩
    refine ⟨ht, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    obtain ⟨c, hcC, y, hy, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun y hy c hc => (hcent c hc y hy).symm) hl
    have hct : c * t = t * c := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) c hcC.1
    have hyt : y * t = t * y := Subgroup.mem_centralizer_iff.mp hc y (Subgroup.mem_sup_right hy)
    calc c * y * t = c * (y * t) := by group
      _ = c * (t * y) := by rw [hyt]
      _ = (c * t) * y := by group
      _ = (t * c) * y := by rw [hct]
      _ = t * (c * y) := by group


theorem card_aC (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    {y : G} (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) :
    Nat.card (H.aC g) = Nat.card B * (H.aC g).relIndex P ∧
      ∀ c ∈ H.aC g, ∃ p ∈ P, ∃ β ∈ B, ⁅p, y⁆ = c * β := by
  have hpart := h1.part_W
  obtain ⟨F, hFB, hF2⟩ := H.exists_hyperplane
  have hCab : ∀ a ∈ H.aC g, ∀ b ∈ H.aC g, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian (H.aC_elem h48 h1 hcent) ha hb
  refine card_eq_mul_relIndex (B := B) (F := F) (P := P) (C := H.aC g) (H.B_le_aC h48)
    H.aC_le_P (fun a ha b hb => H.commutator_mem (H.P_le_Q ha) (H.P_le_Q hb))
    (fun b hb p hp => H.center_Q hb (H.P_le_Q hp)) hCab hFB hF2
    (fun y hy hyF => H.center_quotient hFB hF2 hy hyF) (fun p => ⁅p, y⁆)
    (fun p hp => H.comm_Q_Bg_mem_aC h48 hP hBgQ hpart (H.P_le_Q hp) hy)
    (fun p hp => ?_) (fun p hp p' hp' => ?_) (fun p hp hpB => ?_)
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcent p hp y hy)]; exact B.one_mem
  ·
    refine ⟨⁅p, ⁅p', y⁆⁆, H.commutator_mem (H.P_le_Q hp) (H.P_le_Q (H.aC_le_P
      (H.comm_Q_Bg_mem_aC h48 hP hBgQ hpart (H.P_le_Q hp') hy))), ?_⟩
    have hc' := H.comm_Q_Bg_mem_aC h48 hP hBgQ hpart (H.P_le_Q hp') hy
    have hc := H.comm_Q_Bg_mem_aC h48 hP hBgQ hpart (H.P_le_Q hp) hy
    have e : ⁅p * p', y⁆ = ⁅p, ⁅p', y⁆⁆ * ⁅p', y⁆ * ⁅p, y⁆ := by
      simp only [commutatorElement_def]; group
    have hβ : ⁅p, ⁅p', y⁆⁆ ∈ B := H.commutator_mem (H.P_le_Q hp) (H.aC_le_Q hc')
    rw [e]
    have h2 : ⁅p', y⁆ * ⁅p, y⁆ = ⁅p, y⁆ * ⁅p', y⁆ := hCab _ hc' _ hc
    have h3 : ⁅p, ⁅p', y⁆⁆ * (⁅p', y⁆ * ⁅p, y⁆) = (⁅p', y⁆ * ⁅p, y⁆) * ⁅p, ⁅p', y⁆⁆ :=
      (H.center_Q hβ (Q.mul_mem (H.aC_le_Q hc') (H.aC_le_Q hc)))
    calc ⁅p, ⁅p', y⁆⁆ * ⁅p', y⁆ * ⁅p, y⁆ = ⁅p, ⁅p', y⁆⁆ * (⁅p', y⁆ * ⁅p, y⁆) := by group
      _ = (⁅p', y⁆ * ⁅p, y⁆) * ⁅p, ⁅p', y⁆⁆ := h3
      _ = (⁅p, y⁆ * ⁅p', y⁆) * ⁅p, ⁅p', y⁆⁆ := by rw [h2]
      _ = ⁅p, y⁆ * ⁅p', y⁆ * ⁅p, ⁅p', y⁆⁆ := by group
  · exact H.mem_aC_of_comm_mem h48 hP hBgQ hpart hp hy hy1 hpB


theorem L_comm_Tg (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {l t' : G}
    (hl : l ∈ H.aC g ⊔ conjSubgroup g B) (ht' : t' ∈ conjSubgroup g T) :
    ⁅l, t'⁆ ∈ conjSubgroup g B := by
  obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun y hy c hc => (hcent c hc y hy).symm) hl
  have e : ⁅c * y, t'⁆ = c * ⁅y, t'⁆ * c⁻¹ * ⁅c, t'⁆ := by
    simp only [commutatorElement_def]; group
  have h1' : ⁅y, t'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.Tg_comm_Bg ht' hy).symm
  have h2 : ⁅c, t'⁆ ∈ conjSubgroup g B := by
    have := (conjSubgroup g B).inv_mem
      (H.aC_comm_Tg h48 h1.trans_X h1.comm_X_K hTgW hcent hc ht')
    rwa [commutatorElement_inv] at this
  rw [e, h1', mul_one, mul_inv_cancel, one_mul]
  exact h2

theorem Tg_le_normalizer_aL (h48 : Hyp48 M B T g) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    conjSubgroup g T ≤ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  intro t' ht'
  refine Subgroup.mem_normalizer_fintype fun l hl => ?_
  have e : t' * l * t'⁻¹ = (⁅l, t'⁆)⁻¹ * l := by simp only [commutatorElement_def]; group
  rw [e]
  exact (H.aC g ⊔ conjSubgroup g B).mul_mem ((H.aC g ⊔ conjSubgroup g B).inv_mem
    (Subgroup.mem_sup_right (H.L_comm_Tg h48 h1 hTgW hcent hl ht'))) hl

theorem X_le_normalizer_aL (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (h1 : Phase1 B T g) (hBgQ : conjSubgroup g B ⊓ Q = ⊥)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    T ⊔ conjSubgroup g T ≤
      Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  sup_le ((H.T_le_Q).trans (H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent))
    (H.Tg_le_normalizer_aL h48 h1 hTgW hcent)


end Hyp4

end CFSG.RankThree.GF2n.Tim78
