module

public import CFSG.Quasithin.Vol2.Ch12Sec8OnePara
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11H
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11K

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

abbrev lsCh617 (T L V : Subgroup G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G))

omit [Finite G] in
theorem ls_le_ch617 : lsCh617 T L V ≤ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) :=
  oTwoUpper_le _

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem lin_fix_ch617 {l : G} (hlL : l ∈ L)
    (hlN : l ∈ Subgroup.normalizer (ch6ZS T L V : Set G)) {s : G} (hs : s ∈ ch6ZS T L V)
    (hs1 : s ≠ 1) (hls : l * s * l⁻¹ = s) :
    l ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  obtain ⟨v₀, hv₀0, hv₀⟩ := h.exists_isLine625_ZS
  set m : Subgroup.normalizer (V : Set G) := ⟨l, h.toHyp611.L_le_normalizer hlL⟩ with hm
  have hlin := (h.isLin625_and_det_of_mem_L m hlL).1
  obtain ⟨μ, hμ⟩ : ∃ μ, h.data.conj m v₀ = μ • v₀ := by
    have h1 : h.vec625 v₀ ∈ ch6ZS T L V := (hv₀ v₀).mpr ⟨1, (one_smul _ _).symm⟩
    have h2 : l * h.vec625 v₀ * l⁻¹ ∈ ch6ZS T L V := (Subgroup.mem_normalizer_iff.mp hlN _).mp h1
    rw [show l * h.vec625 v₀ * l⁻¹ = h.vec625 (h.data.conj m v₀) from h.conj_vec625 m v₀] at h2
    exact (hv₀ _).mp h2
  have hconj : ∀ c : h.data.K, l * h.vec625 (c • v₀) * l⁻¹ = h.vec625 ((c * μ) • v₀) := by
    intro c
    rw [show l * h.vec625 (c • v₀) * l⁻¹ = h.vec625 (h.data.conj m (c • v₀)) from
      h.conj_vec625 m (c • v₀), hlin, hμ, smul_smul]
  obtain ⟨ws, rfl⟩ := h.exists_vec625_eq ((show ch6ZS T L V ≤ V from inf_le_left) hs)
  obtain ⟨c₀, rfl⟩ := (hv₀ ws).mp hs
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    exact hs1 (by rw [zero_smul, h.vec625_zero])
  have hμ1 : μ = 1 := by
    have h1 := hconj c₀
    rw [hls] at h1
    have h2 := h.vec625_injective h1
    have h3 : (c₀ * μ - c₀) • v₀ = 0 := by rw [sub_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have : c₀ * (μ - 1) = 0 := by rw [mul_sub, mul_one]; exact h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hc₀
      · exact sub_eq_zero.mp h5
    · exact absurd h4 hv₀0
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨w, rfl⟩ := h.exists_vec625_eq ((show ch6ZS T L V ≤ V from inf_le_left) hy)
  obtain ⟨c, rfl⟩ := (hv₀ w).mp hy
  have h1 := hconj c
  rw [hμ1, mul_one] at h1
  calc h.vec625 (c • v₀) * l = (l * h.vec625 (c • v₀) * l⁻¹) * l := by rw [h1]
    _ = l * h.vec625 (c • v₀) := by group

theorem exists_diag_ch617 : ∃ d ∈ lsCh617 T L V, d ^ 3 = 1 ∧
    d ∈ Subgroup.normalizer (ch6ZS T L V : Set G) ∧ ∀ x ∈ V, d * x * d⁻¹ = x → x = 1 := by
  obtain ⟨d, hdL, hd3, hdN, -, hfix, -, -⟩ := h.exists_diag_ch611
  have hodd : Odd (orderOf d) := by
    have hdvd : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1 <;> rw [h1] <;> decide
  exact ⟨d, mem_oTwoUpper_of_odd ⟨hdL, hdN⟩ hodd, hd3, hdN, hfix⟩

theorem T_le_normalizer_ls_ch617 : T ≤ Subgroup.normalizer (lsCh617 T L V : Set G) := by
  intro t ht
  apply normalizer_le_normalizer_oTwoUpper
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    h.toHyp611Nat.T_le_normalizer_L ht
  have htZ : t ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    h.toHyp611Nat.T_le_normalizer_ZS ht
  have htN : t ∈ Subgroup.normalizer
      (Subgroup.normalizer (ch6ZS T L V : Set G) : Set G) := Subgroup.le_normalizer htZ
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htL, htN⟩

theorem coe_sup_ch617 : ((lsCh617 T L V ⊔ T : Subgroup G) : Set G) =
    (T : Set G) * (lsCh617 T L V : Set G) := by
  rw [sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ h.T_le_normalizer_ls_ch617

theorem sup_le_normalizer_ZS_ch617 :
    lsCh617 T L V ⊔ T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
  sup_le (ls_le_ch617.trans inf_le_right) fun _ ht => h.toHyp611Nat.T_le_normalizer_ZS ht

theorem centralizer_le_T_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    (lsCh617 T L V ⊔ T) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ T := by
  rintro x ⟨hx, hxC⟩
  have hx' : x ∈ ((lsCh617 T L V ⊔ T : Subgroup G) : Set G) := hx
  rw [h.coe_sup_ch617] at hx'
  obtain ⟨t, ht, l, hl, htl⟩ := hx'
  replace htl : t * l = x := htl
  subst htl
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ zCh611 T, z ≠ 1 := by
    have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have htz : t * z = z * t := by
    have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
    exact (Subgroup.mem_centralizer_iff.mp (hA.sylow_H.1 ht) z hzZ).symm
  have hlz : l * z * l⁻¹ = z := by
    have h1 : (t * l) * z * (t * l)⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hxC z (hZZS hzZ), mul_inv_cancel_right]
    have e : l * z * l⁻¹ = t⁻¹ * ((t * l) * z * (t * l)⁻¹) * t := by group
    rw [e, h1, mul_assoc, ← htz, inv_mul_cancel_left]
  have hlL := (ls_le_ch617 hl).1
  have hlC := h.lin_fix_ch617 hlL (ls_le_ch617 hl).2 (hZZS hzZ) hz1 hlz
  exact T.mul_mem ht (h.mem_T_of_mem_L_ch611 hlL hlC)

theorem pCoreOf_le_centralizer_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    pCoreOf 2 (lsCh617 T L V ⊔ T) ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
  have hTsyl : IsSylowTwoOf T (lsCh617 T L V ⊔ T) :=
    E6.isSylowIn_of_le (⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩)
      le_sup_right le_top
  have hOT : pCoreOf 2 (lsCh617 T L V ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  obtain ⟨d, hdLS, -, hdN, hfix⟩ := h.exists_diag_ch617
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ zCh611 T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  set w := d⁻¹ * z * d with hw
  have hwZS : w ∈ ch6ZS T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) z).mp (hZZS hzZ)
    simpa [hw] using this
  have hwZ : w ∉ zCh611 T := by
    intro hwZ
    have hw1 : w ≠ 1 := fun h1 => hz1 (by
      have : z = d * w * d⁻¹ := by rw [hw]; group
      rw [this, h1]; group)
    have hwz : w = z := SteinbergBS.eq_of_card_le_two hZ2.le hwZ hzZ hw1 hz1
    have hdz : d * z * d⁻¹ = z := by
      have : z = d * w * d⁻¹ := by rw [hw]; group
      calc d * z * d⁻¹ = d * w * d⁻¹ := by rw [hwz]
        _ = z := this.symm
    exact hz1 (hfix z ((h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left hzZ) hdz)
  intro q hq
  have hqT := hOT hq
  have hdq : d * q * d⁻¹ ∈ pCoreOf 2 (lsCh617 T L V ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hdLS)) q).mp hq
  have hcz : ∀ y ∈ T, y * z = z * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hA.sylow_H.1 hy) z hzZ).symm
  have hqz := hcz q hqT
  have hqw : q * w = w * q := by
    have h1 := hcz _ (hOT hdq)
    rw [hw]
    calc q * (d⁻¹ * z * d) = d⁻¹ * ((d * q * d⁻¹) * z) * d := by group
      _ = d⁻¹ * (z * (d * q * d⁻¹)) * d := by rw [h1]
      _ = d⁻¹ * z * d * q := by group
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS hs with e | e | e | e
  · rw [e]; group
  · rw [e]; exact hqz.symm
  · rw [e]; exact hqw.symm
  · rw [e]
    calc z * w * q = z * (w * q) := by group
      _ = z * (q * w) := by rw [hqw]
      _ = (z * q) * w := by group
      _ = (q * z) * w := by rw [hqz]
      _ = q * (z * w) := by group

theorem centralizer_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    (lsCh617 T L V ⊔ T) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) =
      pCoreOf 2 (lsCh617 T L V ⊔ T) := by
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _)
    (h.pCoreOf_le_centralizer_ch617 h331 h432 h512 h614 h615))
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left
    ((le_inf Subgroup.le_normalizer (h.sup_le_normalizer_ZS_ch617.trans
      (normalizer_le_normalizer_centralizer'' (ch6ZS T L V)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf) ?_
  exact h.sylow.1.to_le (h.centralizer_le_T_ch617 h331 h432 h512 h614 h615)

end Hyp6Sec2

end CFSG.Quasithin.H13
