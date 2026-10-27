module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqSquare
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

private theorem exists_mul_self_not_mem_of_sz {L T : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) (hT : IsSylowTwoOf T L) :
    ∃ x ∈ T, x * x ∉ pCoreOf 2 L := by
  classical
  obtain ⟨e⟩ := hSz
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  have hB : fusionBenderBorel (oTwoQuot ↥L) (2 ^ (2 * a + 1)) 2 :=
    fusionBenderBorel_of_mulEquiv_sz (L := oTwoQuot ↥L) ha e
  obtain ⟨-, -, -, hZ, hcard⟩ := hB P
  by_contra hcon
  push Not at hcon
  have hsq : ∀ y ∈ (P : Subgroup (oTwoQuot ↥L)), y * y = 1 := by
    intro y hy
    rw [hP] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    have h1 : (x * x : ↥L) ∈ pCore 2 ↥L :=
      (F1.mem_pCore_iff_coe (x * x : ↥L)).mpr (by simpa using hcon (x : G) hxT)
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have hcomm : ∀ y ∈ (P : Subgroup (oTwoQuot ↥L)), ∀ z ∈ (P : Subgroup (oTwoQuot ↥L)),
      y * z = z * y := by
    intro y hy z hz
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hsq z hz)
    calc y * z = (y * z)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem hy hz))).symm
      _ = z * y := by rw [mul_inv_rev, hy', hz']
  have htop : Subgroup.center (P : Subgroup (oTwoQuot ↥L)) = ⊤ :=
    eq_top_iff.mpr fun w _ => Subgroup.mem_center_iff.mpr fun v =>
      Subtype.ext (hcomm v.1 v.2 w.1 w.2)
  rw [htop, Subgroup.card_top, hcard] at hZ
  have h2 : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  nlinarith

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem P1_le_normalizer_Z1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem P2_le_normalizer_Z2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem Q2_le_S (hF : F112HypW L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)

private theorem S_le_Gw_zero_one (hF : F112HypW L1 L2 S) :
    S ≤ t.Gw 0 1 := by
  rw [t.Gw_zero_one hF]
  exact le_sup_right

private theorem card_mul_card_le_card_sup_of_inf_eq_bot {V D : Subgroup G} (h : V ⊓ D = ⊥) :
    Nat.card V * Nat.card D ≤ Nat.card ↥(V ⊔ D) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : ↥V × ↥D => (⟨(p.1 : G) * p.2,
    mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ : ↥(V ⊔ D))) ?_
  rintro ⟨v, d⟩ ⟨v', d'⟩ hvd
  have h1 : (v : G) * d = v' * d' := congrArg Subtype.val hvd
  have h2 : (v' : G)⁻¹ * v = d' * (d : G)⁻¹ := by
    calc (v' : G)⁻¹ * v = (v' : G)⁻¹ * (v * d) * (d : G)⁻¹ := by group
      _ = (v' : G)⁻¹ * (v' * d') * (d : G)⁻¹ := by rw [h1]
      _ = d' * (d : G)⁻¹ := by group
  have h3 : (v' : G)⁻¹ * v ∈ V ⊓ D :=
    Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem v'.2) v.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
  rw [h, mem_bot] at h3
  have hv : (v : G) = v' := (inv_mul_eq_one.mp h3).symm
  have hd : (d : G) = d' := by
    rw [hv] at h1
    exact (mul_left_cancel h1)
  exact Prod.ext (Subtype.ext hv) (Subtype.ext hd)

private theorem map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

private theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (zpowers_le.mpr hH) (zpowers_le.mpr hK)
    (mem_zpowers g)

private theorem L1_le_Gv_zero : L1 ≤ t.Gv 0 := by
  rw [t.Gv_zero]
  exact le_sup_left

private theorem L1_le_normalizer_Qv_zero : L1 ≤ normalizer (t.Qv 0 : Set G) :=
  t.L1_le_Gv_zero.trans (t.Gv_le_normalizer_Qv 0)

private theorem P1_le_normalizer_L1 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P1 L1 L2 S ≤ normalizer (L1 : Set G) :=
  sup_le le_normalizer (bigB_le_normalizer_of_hyp111 hfr.hF.1)

private theorem pCoreOf_le_Qv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 L1 ≤ t.Qv 0 := by
  rw [t.Qv_zero]
  exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1

private theorem Qv_zero_inf_L1_le : t.Qv 0 ⊓ L1 ≤ pCoreOf 2 L1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun l hl => inf_normalizer_le_normalizer_inf
      (mem_inf.mpr ⟨t.L1_le_normalizer_Qv_zero hl, le_normalizer hl⟩))
    ((t.isPGroup_Qv 0).to_le inf_le_left)

private theorem S_le_sup_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S ≤ t.Qv 0 ⊔ (S ⊓ L1) := by
  have h := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  rw [t.Qv_zero, sup_comm]
  exact h.le

private theorem Qv_one_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ S := by
  rw [t.Qv_one]
  exact Q2_le_S hfr.hF

private theorem Qv_one_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ L1 ⊔ t.Qv 0 :=
  (t.Qv_one_le_S hfr).trans ((t.S_le_sup_Qv_zero hfr).trans
    (sup_le le_sup_right (inf_le_right.trans le_sup_left)))

private theorem Qv_one_le_normalizer_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) := by
  have h := (t.Qv_le_Gv hfr 1).1
  rw [sub_self] at h
  exact h.trans (t.Gv_le_normalizer_Qv 0)

private theorem Qv_zero_le_normalizer_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 0 ≤ normalizer (t.Qv 1 : Set G) := by
  have h := (t.Qv_le_Gv hfr 0).2
  rw [zero_add] at h
  exact h.trans (t.Gv_le_normalizer_Qv 1)

private theorem mem_qv_tau_iff (Q₁ Q₂ : Subgroup G) {i j : ℤ} (hij : j = i + 2) {y : G} :
    y ∈ qv Q₁ Q₂ t.x₁ t.x₂ j ↔ (t.x₂ * t.x₁)⁻¹ * y * (t.x₂ * t.x₁) ∈ qv Q₁ Q₂ t.x₁ t.x₂ i := by
  subst hij
  have h := map_qv_tau_pow (Q₁ := Q₁) (Q₂ := Q₂) (x₁ := t.x₁) (x₂ := t.x₂) i 1
  rw [zpow_one, mul_one] at h
  rw [← h, mem_map_conj_iff]

private theorem mem_win_tau_iff (Q₁ Q₂ : Subgroup G) {a b c d : ℤ} (hc : c = a + 2)
    (hd : d = b + 2) {y : G} :
    y ∈ win Q₁ Q₂ t.x₁ t.x₂ c d ↔
      (t.x₂ * t.x₁)⁻¹ * y * (t.x₂ * t.x₁) ∈ win Q₁ Q₂ t.x₁ t.x₂ a b := by
  subst hc hd
  have h := map_win_tau_pow (Q₁ := Q₁) (Q₂ := Q₂) (x₁ := t.x₁) (x₂ := t.x₂) a b 1
  rw [zpow_one, mul_one] at h
  rw [← h, mem_map_conj_iff]

private theorem card_Zv_add_two_mul (i k : ℤ) :
    Nat.card (t.Zv (i + 2 * k)) = Nat.card (t.Zv i) := by
  show Nat.card (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (i + 2 * k)) =
    Nat.card (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ i)
  rw [← map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂) i k]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

private theorem Zv_two_le (hZ0 : t.Zv 0 ≤ t.Gw (-3) 3) : t.Zv 2 ≤ t.Gw (-1) 5 := by
  intro y hy
  have h1 : (t.x₂ * t.x₁)⁻¹ * y * (t.x₂ * t.x₁) ∈ t.Zv 0 :=
    (t.mem_qv_tau_iff (Z1 L1 L2 S) (Z2 L1 L2 S) (i := 0) (j := 2) (by norm_num)).mp hy
  exact (t.mem_win_tau_iff (P1 L1 L2 S) (P2 L1 L2 S) (a := -3) (b := 3) (c := -1) (d := 5)
    (by norm_num) (by norm_num)).mpr (hZ0 h1)

private theorem Zv_neg_two_le (hZ0 : t.Zv 0 ≤ t.Gw (-3) 3) : t.Zv (-2) ≤ t.Gw (-5) 1 := by
  intro y hy
  have e : (t.x₂ * t.x₁)⁻¹ * ((t.x₂ * t.x₁) * y * (t.x₂ * t.x₁)⁻¹) * (t.x₂ * t.x₁) = y := by
    group
  have h1 : (t.x₂ * t.x₁) * y * (t.x₂ * t.x₁)⁻¹ ∈ t.Zv 0 := by
    refine (t.mem_qv_tau_iff (Z1 L1 L2 S) (Z2 L1 L2 S) (i := -2) (j := 0) (by norm_num)).mpr ?_
    rw [e]
    exact hy
  have h2 := (t.mem_win_tau_iff (P1 L1 L2 S) (P2 L1 L2 S) (a := -5) (b := 1) (c := -3) (d := 3)
    (by norm_num) (by norm_num)).mp (hZ0 h1)
  rwa [e] at h2

private theorem Zv_neg_two_inf_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 7)) = ⊥)
    (hZw : t.Zv (-2) ≤ t.Gw (-5) 1) : t.Zv (-2) ⊓ t.Qv 1 = ⊥ := by
  have hQ := (t.Qv_le_Gv hfr 1).2
  rw [show (1 : ℤ) + 1 = 2 by norm_num] at hQ
  have hle : t.Zv (-2) ⊓ t.Qv 1 ≤ t.Gw (-5) 2 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ 1 ∨ i = 2 by omega) with h3 | rfl
    · exact mem_win_iff.mp (hZw (mem_inf.mp hy).1) i h1 h3
    · exact hQ (mem_inf.mp hy).2
  have h := t.le_pCoreOf_Gw hfr (show (-5 : ℤ) < 2 by norm_num)
    ((t.isPGroup_Zv (-2)).to_le inf_le_left) hle
  have hm := hmax (-5)
  rw [show (-5 : ℤ) + 7 = 2 by norm_num] at hm
  rw [hm] at h
  exact le_bot_iff.mp h

private theorem Zv_two_inf_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 7)) = ⊥)
    (hZw : t.Zv 2 ≤ t.Gw (-1) 5) : t.Zv 2 ⊓ t.Qv (-1) = ⊥ := by
  have hQ := (t.Qv_le_Gv hfr (-1)).1
  rw [show (-1 : ℤ) - 1 = -2 by norm_num] at hQ
  have hle : t.Zv 2 ⊓ t.Qv (-1) ≤ t.Gw (-2) 5 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -2 ∨ -1 ≤ i by omega) with rfl | h3
    · exact hQ (mem_inf.mp hy).2
    · exact mem_win_iff.mp (hZw (mem_inf.mp hy).1) i h3 h2
  have h := t.le_pCoreOf_Gw hfr (show (-2 : ℤ) < 5 by norm_num)
    ((t.isPGroup_Zv 2).to_le inf_le_left) hle
  have hm := hmax (-2)
  rw [show (-2 : ℤ) + 7 = 5 by norm_num] at hm
  rw [hm] at h
  exact le_bot_iff.mp h

private theorem S_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZw : t.Zv (-2) ≤ t.Gw (-5) 1) (hbot : t.Zv (-2) ⊓ t.Qv 1 = ⊥)
    (hcard : 2 ^ f ≤ Nat.card (t.Zv (-2))) : S ≤ t.Zv (-2) ⊔ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS : t.Zv (-2) ≤ S := by
    have h := t.le_pCoreOf_Gw hfr (show (0 : ℤ) < 1 by norm_num) (t.isPGroup_Zv (-2))
      (hZw.trans (win_mono (by norm_num) le_rfl))
    rwa [t.pCoreOf_Gw_zero_one hfr] at h
  have hQS := t.Qv_one_le_S hfr
  have h9 := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one] at h9
  have h3 := Subgroup.relIndex_mul_card (t.Qv 1) S
  rw [h9, inf_eq_left.mpr hQS] at h3
  have hprod := card_mul_card_le_card_sup_of_inf_eq_bot hbot
  have hsup : t.Zv (-2) ⊔ t.Qv 1 = S :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZS hQS) (by
      rw [← h3]
      exact (Nat.mul_le_mul_right _ hcard).trans hprod)
  exact hsup.ge

private theorem exists_mul_self_not_mem_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hS : S ≤ t.Qv 0 ⊔ t.Qv 1) :
    ∃ s ∈ t.Qv 1, s * s ∉ t.Qv 0 := by
  obtain ⟨x, hxT, hxx⟩ := exists_mul_self_not_mem_of_sz hfr.ha hfr.hSz hfr.hF.1.h1.sylow
  have hN := t.Qv_one_le_normalizer_Qv_zero hfr
  have hxL : x ∈ L1 := (mem_inf.mp hxT).2
  obtain ⟨q, hq, p, hp, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp (hS (mem_inf.mp hxT).1)
  refine ⟨p, hp, fun hpp => hxx (t.Qv_zero_inf_L1_le (mem_inf.mpr ⟨?_, mul_mem hxL hxL⟩))⟩
  have e : q * p * (q * p) = q * (p * q * p⁻¹) * (p * p) := by group
  rw [e]
  exact mul_mem (mul_mem hq ((mem_normalizer_iff.mp (hN hp) q).mp hq)) hpp

private theorem Zv_zero_comm {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    ∀ z ∈ t.Zv 0, ∀ y ∈ t.Qv (-1), z * y = y * z := by
  intro z hz y hy
  have hy' : t.x₁⁻¹ * y * t.x₁ ∈ t.Qv 1 := by
    have h := (t.track.mem_qv_neg_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _)
      (-1) (y := y)).mp hy
    rwa [neg_neg] at h
  have hMc : L1 ⊔ t.Qv 0 ≤ centralizer (t.Zv 0 : Set G) :=
    sup_le hZL (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0))
  have hMN : P1 L1 L2 S ≤ normalizer ((L1 ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (P1_le_normalizer_L1 hfr)
      (by rw [← t.Gv_zero]; exact t.Gv_le_normalizer_Qv 0)
  have hyM : y ∈ L1 ⊔ t.Qv 0 := by
    have h := (mem_normalizer_iff.mp (hMN t.track.x₁_mem) (t.x₁⁻¹ * y * t.x₁)).mp
      (t.Qv_one_le_sup hfr hy')
    rwa [show t.x₁ * (t.x₁⁻¹ * y * t.x₁) * t.x₁⁻¹ = y by group] at h
  exact Subgroup.mem_centralizer_iff.mp (hMc hyM) z hz

private theorem Zv_two_comm {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    ∀ z ∈ t.Zv 2, ∀ y ∈ t.Qv 1, z * y = y * z := by
  intro z hz y hy
  have hz' := (t.mem_qv_tau_iff (Z1 L1 L2 S) (Z2 L1 L2 S) (i := 0) (j := 2) (by norm_num)).mp hz
  have hy' :=
    (t.mem_qv_tau_iff (Q1 L1 L2 S) (Q2 L1 L2 S) (i := -1) (j := 1) (by norm_num)).mp hy
  have h := t.Zv_zero_comm hfr hZL _ hz' _ hy'
  have e1 : (t.x₂ * t.x₁)⁻¹ * z * (t.x₂ * t.x₁) * ((t.x₂ * t.x₁)⁻¹ * y * (t.x₂ * t.x₁)) =
      (t.x₂ * t.x₁)⁻¹ * (z * y) * (t.x₂ * t.x₁) := by group
  have e2 : (t.x₂ * t.x₁)⁻¹ * y * (t.x₂ * t.x₁) * ((t.x₂ * t.x₁)⁻¹ * z * (t.x₂ * t.x₁)) =
      (t.x₂ * t.x₁)⁻¹ * (y * z) * (t.x₂ * t.x₁) := by group
  rw [e1, e2] at h
  exact mul_left_cancel (mul_right_cancel h)

private theorem inf_le_sup_D {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ2Q0 : t.Zv 2 ≤ t.Qv 0) (hZ2Q1 : t.Zv 2 ≤ t.Qv 1) (hbot : t.Zv 2 ⊓ t.Qv (-1) = ⊥)
    (hcard : 2 ^ f ≤ Nat.card (t.Zv 2)) :
    t.Qv 1 ⊓ t.Qv 0 ≤ t.Zv 2 ⊔ (t.Qv 1 ⊓ t.Qv (-1)) := by
  have hX : IsPGroup 2 ↥(t.Qv 1 ⊓ t.Qv 0) := (t.isPGroup_Qv 0).to_le inf_le_right
  have hQm := (t.Qv_le_Gv hfr 0).1
  rw [zero_sub] at hQm
  have hXw : t.Qv 1 ⊓ t.Qv 0 ≤ t.Gw (-1) (-1 + 1) := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -1 ∨ i = 0 by omega) with rfl | rfl
    · exact hQm (mem_inf.mp hy).2
    · exact t.Qv_le_Gv_self 0 (mem_inf.mp hy).2
  have h2 := t.relIndex_Qv_le hfr (-1) hX (Or.inr hXw)
  rw [if_neg (show ¬ Even (-1 : ℤ) by decide)] at h2
  have h3 := Subgroup.relIndex_mul_card (t.Qv (-1)) (t.Qv 1 ⊓ t.Qv 0)
  have hYbot : t.Zv 2 ⊓ (t.Qv (-1) ⊓ (t.Qv 1 ⊓ t.Qv 0)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ inf_le_left).trans hbot.le)
  have hprod := card_mul_card_le_card_sup_of_inf_eq_bot hYbot
  have hle : t.Zv 2 ⊔ (t.Qv (-1) ⊓ (t.Qv 1 ⊓ t.Qv 0)) ≤ t.Qv 1 ⊓ t.Qv 0 :=
    sup_le (le_inf hZ2Q1 hZ2Q0) inf_le_right
  have heq : t.Zv 2 ⊔ (t.Qv (-1) ⊓ (t.Qv 1 ⊓ t.Qv 0)) = t.Qv 1 ⊓ t.Qv 0 :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [← h3]
      exact (Nat.mul_le_mul_right _ (h2.trans hcard)).trans hprod)
  rw [← heq]
  exact sup_le_sup_left (le_inf (inf_le_right.trans inf_le_left) inf_le_left) _

private theorem D_le {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ⊓ t.Qv (-1) ≤ t.Qv 1 ⊓ t.Qv 0 := by
  have hQ := (t.Qv_le_Gv hfr 1).1
  rw [sub_self] at hQ
  refine le_inf inf_le_left (t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num)
    (by norm_num) ((t.isPGroup_Qv 1).to_le inf_le_left) ?_)
  intro y hy
  refine mem_win_iff.mpr fun i h1 h2 => ?_
  rcases (show i = -1 ∨ i = 0 ∨ i = 1 by omega) with rfl | rfl | rfl
  · exact t.Qv_le_Gv_self (-1) (mem_inf.mp hy).2
  · exact hQ (mem_inf.mp hy).1
  · exact t.Qv_le_Gv_self 1 (mem_inf.mp hy).1

private theorem Qv_zero_le_normalizer_D {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv 0 ≤ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) := by
  have h1 := (t.Qv_le_Gv hfr 0).2
  have h2 := (t.Qv_le_Gv hfr 0).1
  rw [zero_add] at h1
  rw [zero_sub] at h2
  exact fun x hx => inf_normalizer_le_normalizer_inf
    (mem_inf.mpr ⟨t.Gv_le_normalizer_Qv 1 (h1 hx), t.Gv_le_normalizer_Qv (-1) (h2 hx)⟩)

private theorem L1_le_normalizer_D
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hZ1 : ¬ t.Zv 1 ≤ t.Gv (-1)) :
    L1 ≤ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hQ2le := t.pCoreOf_le_Qv_zero hfr
  have hQ0N := t.Qv_zero_le_normalizer_D hfr
  have hZ1N : t.Zv 1 ≤ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) :=
    fun z hz => (Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr
      fun d hd => Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 1 hz) d (mem_inf.mp hd).1)
  have hZm1N : t.Zv (-1) ≤ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) :=
    fun z hz => (Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr
      fun d hd => Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer (-1) hz) d
        (mem_inf.mp hd).2)
  have hSQ := t.S_le_sup_Qv_zero hfr
  have hTQ : S ⊓ L1 ≤ normalizer (t.Qv 0 : Set G) := inf_le_right.trans t.L1_le_normalizer_Qv_zero
  have hXN : (t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1) ≤
      normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) :=
    inf_le_left.trans (sup_le hZ1N hQ0N)
  have hXD : t.D1 ≤ normalizer (((t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1) : Subgroup G) : Set G) := by
    intro d hd
    have hdK : d ∈ t.K := mem_sup_left hd
    exact A4.mem_normalizer_inf (mem_normalizer_sup (t.Gv_le_normalizer_Zv 1 (t.K_le_Gv 1 hdK))
      (t.Gv_le_normalizer_Qv 0 (t.K_le_Gv 0 hdK))) ((t.hD1hall.1.trans inf_le_right) hd)
  have hXnot : ¬ (t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1) ≤ pCoreOf 2 L1 := by
    intro hX
    apply hZ1
    have hZQ : t.Zv 1 ≤ t.Qv 0 := by
      intro y hy
      have hyS : y ∈ S := t.Qv_one_le_S hfr (t.Zv_le_Qv 1 hy)
      obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ).mp (hSQ hyS)
      have hτX : τ ∈ (t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1) := by
        refine mem_inf.mpr ⟨?_, hτ⟩
        have e : τ = q⁻¹ * y := by rw [hyqτ]; group
        rw [e]
        exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
      rw [hyqτ]
      exact mul_mem hq (hQ2le (hX hτX))
    have h := (t.Qv_le_Gv hfr 0).1
    rw [zero_sub] at h
    exact hZQ.trans h
  have hKI := mem_sup_pCoreOf_of_torus_of_sz hfr.ha hfr.hSz hTsyl t.hD1hall inf_le_right hXD hXnot
  have hx₁L1 : t.x₁ ∈ normalizer (L1 : Set G) := P1_le_normalizer_L1 hfr t.track.x₁_mem
  have hx₁O : t.x₁ ∈ normalizer (pCoreOf 2 L1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 hx₁L1
  have hT'syl : IsSylowTwoOf ((S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom) L1 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₁) hTsyl
    rwa [map_conj_eq_of_mem hx₁L1] at h
  have hXmap : ((t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1)).map (MulAut.conj t.x₁).toMonoidHom ≤
      normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom)
      (inf_le_left : (t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1) ≤ t.Zv 1 ⊔ t.Qv 0)
    have hZ := t.track.map_qv_x₁ P1_le_normalizer_Z1 P2_le_normalizer_Z2 1
    have hQ := t.track.map_qv_x₁ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) 0
    rw [neg_zero] at hQ
    rw [Subgroup.map_sup, hZ, hQ] at h1
    exact h1.trans (sup_le hZm1N hQ0N)
  have h : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 →
      x ∈ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) ⊔ pCoreOf 2 L1 :=
    fun x hx hxx => sup_le_sup_right hXN _ (hKI x hx hxx)
  have h' : ∀ x ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ normalizer ((t.Qv 1 ⊓ t.Qv (-1) : Subgroup G) : Set G) ⊔ pCoreOf 2 L1 := by
    intro x hx hxx
    rw [mem_map_conj_iff] at hx
    have hxx' : t.x₁⁻¹ * x * t.x₁ * (t.x₁⁻¹ * x * t.x₁) ∈ pCoreOf 2 L1 := by
      have e : t.x₁⁻¹ * x * t.x₁ * (t.x₁⁻¹ * x * t.x₁) = t.x₁⁻¹ * (x * x) * t.x₁⁻¹⁻¹ := by
        group
      rw [e]
      exact (mem_normalizer_iff.mp (inv_mem hx₁O) _).mp hxx
    have hx' : x ∈ (((t.Zv 1 ⊔ t.Qv 0) ⊓ (S ⊓ L1)) ⊔ pCoreOf 2 L1).map
        (MulAut.conj t.x₁).toMonoidHom := mem_map_conj_iff.mpr (hKI _ hx hxx')
    rw [Subgroup.map_sup, map_conj_eq_of_mem hx₁O] at hx'
    exact sup_le_sup_right hXmap _ hx'
  have hne : S ⊓ L1 ≠ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := by
    intro heq
    have hTG01 : S ⊓ L1 ≤ t.Gw 0 1 := inf_le_left.trans (t.S_le_Gw_zero_one hfr.hF)
    have hT'G : (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom ≤ t.Gw (-1) 0 := by
      have h1 := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hTG01
      have e := t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 0 1
      rw [neg_zero] at e
      exact h1.trans e.le
    have hTw : S ⊓ L1 ≤ t.Gw (-1) 1 := by
      intro y hy
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      rcases (show i = -1 ∨ 0 ≤ i by omega) with rfl | h3
      · have hy' : y ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := heq ▸ hy
        exact mem_win_iff.mp (hT'G hy') (-1) le_rfl (by norm_num)
      · exact mem_win_iff.mp (hTG01 hy) i h3 h2
    have hTQ0 : S ⊓ L1 ≤ t.Qv 0 :=
      t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num)
        hTsyl.2.1 hTw
    have hSle : S ≤ t.Qv 0 := hSQ.trans (sup_le le_rfl hTQ0)
    have hQS : (t.Qv 0).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
    have h9 := (t.relIndex_Qv_pCoreOf hfr 0).2
    rw [zero_add, t.pCoreOf_Gw_zero_one hfr, if_pos (show Even (0 : ℤ) by decide), hQS] at h9
    have h2 : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
    nlinarith
  have hGen := le_sup_pCoreOf_of_sylow_ne_of_sz hfr.ha hfr.hSz hTsyl hT'syl hne h h'
  exact hGen.trans (sup_le le_rfl (hQ2le.trans hQ0N))

private theorem sup_Qv_zero_eq_of_normal {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (N : Subgroup G) (hNL : N ≤ L1 ⊔ t.Qv 0)
    (hLN : L1 ⊔ t.Qv 0 ≤ normalizer (N : Set G)) (hNQ : ¬ N ≤ t.Qv 0) :
    N ⊔ t.Qv 0 = L1 ⊔ t.Qv 0 := by
  have hsim : IsSimpleGroup (oTwoQuot ↥L1) :=
    (BenderType.suzuki a hfr.ha (Classical.choice hfr.hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))).isSimple
  have hQ2L := t.pCoreOf_le_Qv_zero hfr
  have hL1N := t.L1_le_normalizer_Qv_zero
  have hML : N ⊔ t.Qv 0 ≤ L1 ⊔ t.Qv 0 := sup_le hNL le_sup_right
  have hLM : L1 ⊔ t.Qv 0 ≤ normalizer ((N ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hLN (sup_le hL1N le_normalizer)
  have hM1N : L1 ≤ normalizer (((N ⊔ t.Qv 0) ⊓ L1 : Subgroup G) : Set G) := fun l hl =>
    inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hLM (mem_sup_left hl), le_normalizer hl⟩)
  have hM1Q : ¬ (N ⊔ t.Qv 0) ⊓ L1 ≤ pCoreOf 2 L1 := by
    intro h
    apply hNQ
    intro n hn
    have hnL : n ∈ t.Qv 0 ⊔ L1 := by
      rw [sup_comm]
      exact hNL hn
    obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hL1N).mp hnL
    have hlM : l ∈ N ⊔ t.Qv 0 := by
      have e : l = q⁻¹ * (q * l) := by group
      rw [e]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hn)
    exact mul_mem hq (hQ2L (h (mem_inf.mpr ⟨hlM, hl⟩)))
  have hcov := sup_pCoreOf_eq_of_normal_of_isSimple hsim inf_le_right hM1N hM1Q
  refine le_antisymm hML (sup_le ?_ le_sup_right)
  exact hcov.ge.trans (sup_le inf_le_left (hQ2L.trans le_sup_right))

theorem false_of_b_eq_three
    {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 0 ≤ t.Gw (-3) 3) (hZ1 : ¬ t.Zv 1 ≤ t.Gv (-1))
    (hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 7)) = ⊥)
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) (hcard : 2 ^ f ≤ Nat.card (t.Zv 0)) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2w := t.Zv_two_le hZ0
  have hZm2w := t.Zv_neg_two_le hZ0
  have hc2 : 2 ^ f ≤ Nat.card (t.Zv 2) := by
    have h := t.card_Zv_add_two_mul 0 1
    rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at h
    rw [h]
    exact hcard
  have hcm2 : 2 ^ f ≤ Nat.card (t.Zv (-2)) := by
    have h := t.card_Zv_add_two_mul 0 (-1)
    rw [show (0 : ℤ) + 2 * (-1) = -2 by norm_num] at h
    rw [h]
    exact hcard
  have hZ2Q0 : t.Zv 2 ≤ t.Qv 0 := t.le_Qv_of_le_Gw hfr (u := -1) (w := 5) (j := 0)
    (by norm_num) (by norm_num) (t.isPGroup_Zv 2) hZ2w
  have hZ2Q1 : t.Zv 2 ≤ t.Qv 1 := t.le_Qv_of_le_Gw hfr (u := -1) (w := 5) (j := 1)
    (by norm_num) (by norm_num) (t.isPGroup_Zv 2) hZ2w
  have hZm2Q0 : t.Zv (-2) ≤ t.Qv 0 := t.le_Qv_of_le_Gw hfr (u := -5) (w := 1) (j := 0)
    (by norm_num) (by norm_num) (t.isPGroup_Zv (-2)) hZm2w
  have hbot1 := t.Zv_neg_two_inf_eq_bot hfr hmax hZm2w
  have hbot2 := t.Zv_two_inf_eq_bot hfr hmax hZ2w
  obtain ⟨s, hs, hss⟩ := t.exists_mul_self_not_mem_Qv_zero hfr
    ((t.S_le_sup hfr hZm2w hbot1 hcm2).trans (sup_le_sup_right hZm2Q0 _))
  have hnorm := le_normalizer_inf_of_sq_not_mem (L := L1 ⊔ t.Qv 0) (Q := t.Qv 0) (P := t.Qv 1)
    (D := t.Qv 1 ⊓ t.Qv (-1)) (A := t.Zv 2)
    (sup_le t.L1_le_normalizer_Qv_zero le_normalizer)
    (sup_le (t.L1_le_normalizer_D hfr hZ1) (t.Qv_zero_le_normalizer_D hfr))
    (t.D_le hfr) (t.Qv_one_le_sup hfr) (t.Qv_zero_le_normalizer_Qv_one hfr)
    (fun z hz => by
      rw [t.Zv_eq 2] at hz
      exact A4.sq_eq_one_of_mem_omegaOneCenterOf hz)
    (t.Zv_two_comm hfr hZL) (t.inf_le_sup_D hfr hZ2Q0 hZ2Q1 hbot2 hc2) hs
    (by rwa [pow_two]) (t.sup_Qv_zero_eq_of_normal hfr)
  have hP1 : P1 L1 L2 S ≤ normalizer ((t.Qv 1 ⊓ t.Qv 0 : Subgroup G) : Set G) := by
    refine sup_le (le_sup_left.trans hnorm) fun b hb => ?_
    have hb' : b ∈ t.Gw 0 1 := by
      rw [t.Gw_zero_one hfr.hF]
      exact hb
    exact inf_normalizer_le_normalizer_inf (mem_inf.mpr
      ⟨t.Gv_le_normalizer_Qv 1 (win_le_qv (by norm_num) le_rfl hb'),
        t.Gv_le_normalizer_Qv 0 (win_le_qv le_rfl (by norm_num) hb')⟩)
  have hx := inv_mem (hP1 t.track.x₁_mem)
  have hsub : t.Zv 2 ≤ t.Qv (-1) := by
    intro z hz
    have h1 := (mem_normalizer_iff.mp hx z).mp (mem_inf.mpr ⟨hZ2Q1 hz, hZ2Q0 hz⟩)
    rw [inv_inv] at h1
    have h2 := t.track.mem_qv_neg_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _)
      (-1) (y := z)
    rw [neg_neg] at h2
    exact h2.mpr (mem_inf.mp h1).1
  have hZ2bot : t.Zv 2 = ⊥ := le_bot_iff.mp ((le_inf le_rfl hsub).trans hbot2.le)
  rw [hZ2bot, Subgroup.card_bot] at hc2
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

end Track

end CFSG.Quasithin.Stroth.Rq

end
