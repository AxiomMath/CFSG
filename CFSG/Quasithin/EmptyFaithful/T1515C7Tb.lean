module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Cbar
public import CFSG.Quasithin.EmptyFaithful.T1515C4Grp

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section SevenTb

@[expose] def restrictAut {V : Type*} [CommGroup V] (z : MulAut V) (W : Subgroup V)
    (h : ∀ w ∈ W, z w ∈ W) (h' : ∀ w ∈ W, z⁻¹ w ∈ W) : MulAut ↥W where
  toFun w := ⟨z w, h w w.2⟩
  invFun w := ⟨z⁻¹ w, h' w w.2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem card_modEq_one_of_fpf {V : Type*} [CommGroup V] [Finite V] {z : MulAut V} (hz3 : z ^ 3 = 1)
    {W : Subgroup V} (hWz : ∀ w ∈ W, z w ∈ W) (hfpf : ∀ w ∈ W, z w = w → w = 1) :
    Nat.card W ≡ 1 [MOD 3] := by
  have hW' := fun w (hw : w ∈ W) => inv_apply_mem_of_pow hz3 hWz hw
  set ζ : MulAut ↥W := restrictAut z W hWz hW' with hζ
  have hζ3 : ζ ^ 3 = 1 := by
    have : ζ ^ 3 = ζ * (ζ * ζ) := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
    rw [this]
    refine MulEquiv.ext fun w => Subtype.ext ?_
    show z (z (z (w : V))) = (w : V)
    exact apply_cube_c4 hz3 _
  have h := card_modEq_fixOf hζ3
  have hfix : fixOf ζ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hzw : z (w : V) = w := congrArg Subtype.val (show ζ w = w from hw)
    exact Subgroup.mem_bot.mpr (Subtype.ext (hfpf w w.2 hzw))
  rw [hfix, Subgroup.card_bot] at h
  exact h

variable {V : Type} [CommGroup V]

namespace SevenGen

variable {A Tb : Subgroup (MulAut V)} {t τ x y z : MulAut V} [Finite V] (h : SevenCtx A Tb t)
  (g : SevenGen A Tb τ x y z)
include h g

theorem fix_y_inf_fix_x : fixOf y ⊓ fixOf x = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hy, hx⟩
  have hy' : y c = c := hy
  have hx' : x c = c := hx
  have hyi : y⁻¹ c = c := by
    calc y⁻¹ c = y⁻¹ (y c) := by rw [hy']
      _ = c := by simp
  have hxi : x⁻¹ c = c := by
    calc x⁻¹ c = x⁻¹ (x c) := by rw [hx']
      _ = c := by simp
  have hz : z c = c := by
    rw [g.zdef]
    show x (y (x⁻¹ (y⁻¹ c))) = c
    rw [hyi, hxi, hy', hx']
  exact Subgroup.mem_bot.mpr (fpf_z' h g c hz)

theorem fix_y_le_fix_tau : fixOf y ≤ fixOf τ := fun c hc => tau_fix_y h g c hc

theorem fix_x_le_fix_tau : fixOf x ≤ fixOf τ := fun c hc => tau_fix_x h g c hc

theorem card_fix_y_sup_fix_x : Nat.card (fixOf y ⊔ fixOf x : Subgroup V) = 16 := by
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixOf y) (fixOf x)
    (fun a _ b _ => mul_comm a b)
  rw [fix_y_inf_fix_x h g, Subgroup.card_bot, mul_one, (card_fix_y' h g).1, card_fix_x h g] at h1
  omega

theorem card_fix_tau : Nat.card (fixOf τ) = 16 := by
  have hle : fixOf y ⊔ fixOf x ≤ fixOf τ := sup_le (fix_y_le_fix_tau h g) (fix_x_le_fix_tau h g)
  have h16 : 16 ≤ Nat.card (fixOf τ) := by
    have := Subgroup.card_le_of_le hle
    rw [card_fix_y_sup_fix_x h g] at this
    exact this
  have hd : Nat.card (fixOf τ) ∣ 64 := by
    have := card_fixOf_dvd τ
    rwa [h.card_V] at this
  have hmod : Nat.card (fixOf τ) ≡ 1 [MOD 3] := by
    refine card_modEq_one_of_fpf (z3 h g) (fun w hw => ?_) (fun w _ hzw => fpf_z' h g w hzw)
    exact apply_mem_fixOf_of_commute g.tau_z.symm hw
  have hne : Nat.card (fixOf τ) ≠ 64 := by
    intro h64
    apply fixOf_ne_top g.tau_ne
    apply Subgroup.eq_top_of_card_eq
    rw [h64, h.card_V]
  have hle64 := Nat.le_of_dvd (by norm_num) hd
  unfold Nat.ModEq at hmod
  generalize Nat.card (fixOf τ) = c at *
  interval_cases c <;> omega

theorem fixOf_tau_eq : fixOf τ = fixOf y ⊔ fixOf x := by
  have hle : fixOf y ⊔ fixOf x ≤ fixOf τ := sup_le (fix_y_le_fix_tau h g) (fix_x_le_fix_tau h g)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_fix_tau h g, card_fix_y_sup_fix_x h g])).symm

theorem y_not_Z : y ∉ frattiniIn (oTwoUpper A) := by
  intro hy
  have hc : x * y = y * x := h.Z_central hy g.xP
  have e : y * x * y⁻¹ = x := by
    calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [hc]
      _ = x := by group
  have e2 := yx_rel h g
  rw [e] at e2
  have hz2 : z ^ 2 = 1 := by
    have : x * z ^ 2 = x * 1 := by rw [← e2, mul_one]
    exact mul_left_cancel this
  apply g.z1
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [z3 h g, hz2]; group

theorem Cbar_sup_T : sixCbar A (fixOf y) ⊔ Tb = A := by
  set K : Subgroup (MulAut V) := sixCbar A (fixOf y) ⊔ Tb with hK
  have hKA : K ≤ A := sup_le inf_le_left h.Tb_le
  set K₀ : Subgroup (MulAut V) := oTwoUpper A ⊓ K with hK₀
  have hyK : y ∈ K₀ := ⟨g.yP, Subgroup.mem_sup_left (y_mem_Cbar g)⟩
  have hTK : Tb ≤ K := le_sup_right
  set Zs : Subgroup (MulAut V) := frattiniIn (oTwoUpper A) with hZs
  have hTbN : Tb ≤ Subgroup.normalizer (K₀ : Set (MulAut V)) := by
    have key : ∀ u ∈ Tb, ∀ w ∈ K₀, u * w * u⁻¹ ∈ K₀ := fun u hu w hw =>
      ⟨SevenCtx.P_conj (h.Tb_le hu) hw.1, K.mul_mem (K.mul_mem (hTK hu) hw.2) (K.inv_mem (hTK hu))⟩
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fun hw => key u hu w hw
    · intro hw
      have := key u⁻¹ (Tb.inv_mem hu) _ hw
      simpa [mul_assoc] using this
  have hTbNZ : Tb ≤ Subgroup.normalizer (Zs : Set (MulAut V)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fun hw => h.Z_conj (h.Tb_le hu) hw
    · intro hw
      have := h.Z_conj (h.Tb_le (Tb.inv_mem hu)) hw
      simpa [mul_assoc] using this
  have hirr := h.irr.2.2.2 (Zs ⊔ K₀) le_sup_left (sup_le h.Z_le_P inf_le_left)
    (fun u hu => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hTbNZ hu, hTbN hu⟩)
  have hWP : Zs ⊔ K₀ = oTwoUpper A := by
    rcases hirr with hZ | hP
    · exfalso
      have : y ∈ Zs ⊔ K₀ := Subgroup.mem_sup_right hyK
      rw [hZ] at this
      exact y_not_Z h g this
    · exact hP
  have hKZ : Zs ≤ K₀ := by
    have hne : K₀ ⊓ Zs ≠ ⊥ := by
      intro hbot
      refine h.no_central_complement (Q := K₀) inf_le_left hbot ?_
      rw [sup_comm]
      exact hWP
    have hd : Nat.card (K₀ ⊓ Zs : Subgroup (MulAut V)) ∣ 3 := by
      rw [← h.card_Z]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · have : K₀ ⊓ Zs = Zs := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, h.card_Z])
      exact inf_eq_right.mp this
  have hPK : oTwoUpper A ≤ K := by
    rw [← hWP]
    exact sup_le (hKZ.trans inf_le_right) inf_le_right
  apply le_antisymm hKA
  calc A = oTwoUpper A ⊔ Tb := h.eq_sup_sylow
    _ ≤ K := sup_le hPK hTK

omit [Finite V] in
theorem inf_A₀ {p : MulAut V} (hp : p ∈ oTwoUpper A) (ht : t = p * τ) :
    Tb ⊓ (oTwoUpper A ⊔ Subgroup.zpowers t) = Subgroup.zpowers τ := by
  apply le_antisymm
  · rintro u ⟨huT, huA⟩
    have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (oTwoUpper A : Set (MulAut V)) :=
      Subgroup.zpowers_le.mpr (le_normalizer_oTwoUpper A h.t_mem)
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper A) (Subgroup.zpowers t) hle
    have huA' : u ∈ ((oTwoUpper A ⊔ Subgroup.zpowers t : Subgroup (MulAut V)) : Set (MulAut V)) :=
      huA
    rw [hset] at huA'
    obtain ⟨q, hq, w, hw, hqw'⟩ := huA'
    have hqw : q * w = u := hqw'
    rcases zpowers_cases_two h.t_sq hw with hw1 | hw1
    · rw [hw1, mul_one] at hqw
      have hqT : q ∈ oTwoUpper A ⊓ Tb := ⟨hq, by rw [hqw]; exact huT⟩
      rw [h.P_inf_Tb, Subgroup.mem_bot] at hqT
      rw [← hqw, hqT]
      exact Subgroup.one_mem _
    · rw [hw1] at hqw
      have h1 : q * p ∈ oTwoUpper A := (oTwoUpper A).mul_mem hq hp
      have h2 : q * p ∈ Tb := by
        have : q * p = u * τ⁻¹ := by rw [← hqw, ht]; group
        rw [this]
        exact Tb.mul_mem huT (Tb.inv_mem g.tau_mem)
      have h3 : q * p ∈ oTwoUpper A ⊓ Tb := ⟨h1, h2⟩
      rw [h.P_inf_Tb, Subgroup.mem_bot] at h3
      have hu : u = τ := by
        calc u = q * t := hqw.symm
          _ = (q * p) * τ := by rw [ht]; group
          _ = τ := by rw [h3, one_mul]
      rw [hu]
      exact Subgroup.mem_zpowers τ
  · rw [Subgroup.zpowers_le]
    refine ⟨g.tau_mem, ?_⟩
    have : τ = p⁻¹ * t := by rw [ht]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((oTwoUpper A).inv_mem hp))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

omit [Finite V] h g in
theorem fixV_zpowers_tau : fixV (Subgroup.zpowers τ) = fixOf τ := by
  ext v
  constructor
  · intro hv
    exact hv _ (Subgroup.mem_zpowers _)
  · intro hv a ha
    exact apply_eq_of_mem_zpowers hv ha

end SevenGen

end SevenTb

end CFSG.Quasithin
