module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7ConjSection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_wild_subgroup (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) (hx2 : x ^ 2 ∈ Q)
    (hQx : ∃ g ∈ M, ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t))
    (hex : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) :
    ∃ P : Subgroup G, Vt M (LB M Q B) B Z t < P ∧ P ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) ∧
      Nat.card ↥P * Nat.card ↥P ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) ∧
      ∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
        Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 * m) := by
  classical
  obtain ⟨Md, iD, iA, κ, hκ, S, hSA, hS2, hSw⟩ :=
    exists_conj_section_data h52a hA h310chi hc hs hxM hxt hxV hx2
  haveI : Finite Md := hκ.finite
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hWn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun r hr y hy =>
    conj_mem_Wt (hQM (hRM hr)) (hc.Rt_normalizes_Vt ht hr) hy
  have hsurj : ∀ a : Md, ∃ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      Multiplicative.toAdd (κ w) = a := by
    intro a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    exact ⟨w, by rw [hw]; rfl⟩
  let T : Md →+ Md := S + AddMonoidHom.id Md
  have hTa : ∀ a, T a = S a + a := fun a => rfl
  have h2 : ∀ a : Md, a + a = 0 := hκ.two
  have hTT : ∀ a, T (T a) = 0 := by
    intro a
    rw [hTa, hTa, map_add, hS2]
    have e : a + S a + (S a + a) = (a + a) + (S a + S a) := by abel
    rw [e, h2, h2, add_zero]
  have hTA : ∀ (r : ↥(Rt M (LB M Q B) t)) (a : Md), r • T a = T (r • a) := by
    intro r a
    rw [hTa, hTa, hSA, smul_add]
  have hTκ : ∀ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ c : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      (c : G) = ⁅x, (w : G)⁆ ∧
        κ c = Multiplicative.ofAdd (T (Multiplicative.toAdd (κ w))) := by
    intro w
    obtain ⟨u, hu1, hu2⟩ := hSw w
    refine ⟨u * w⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      simp only [commutatorElement_def]
    · rw [map_mul, map_inv, hu2, hTa, ofAdd_add]
      have hneg : Multiplicative.ofAdd (Multiplicative.toAdd (κ w)) =
          (Multiplicative.ofAdd (Multiplicative.toAdd (κ w)))⁻¹ := by
        rw [← ofAdd_neg]
        congr 1
        exact (neg_eq_of_add_eq_zero_left (h2 _)).symm
      rw [ofAdd_toAdd] at hneg ⊢
      rw [← hneg]
  obtain ⟨P, hVP, hPW, hPsec⟩ := exists_secSub_eq hVW hκ T.range
  have hmemP : ∀ y : ↥(Wt Q (Vt M (LB M Q B) B Z t)), (y : G) ∈ P ↔
      Multiplicative.toAdd (κ y) ∈ T.range := fun y => by
    rw [← hPsec]
    exact (toAdd_mem_secSub_iff hκ hVP y).symm
  have hPn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ P, r * y * r⁻¹ ∈ P := by
    intro r hr y hy
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := hPW hy
    have hrW : r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hWn r hr y hyW
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    have h1 := hκ.act ⟨r, hr⟩ ⟨y, hyW⟩ ⟨r * y * r⁻¹, hrW⟩ rfl
    refine (hmemP ⟨r * y * r⁻¹, hrW⟩).mpr ?_
    rw [h1, toAdd_ofAdd]
    refine ⟨(⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) • a, ?_⟩
    rw [← hTA, ha]
  have hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P := by
    intro r hr
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : r⁻¹ * y * r ∈ P := mem_conjSubgroup.mp hy
      have := hPn r hr _ hy'
      simpa [mul_assoc] using this
    · rw [mem_conjSubgroup]
      have := hPn r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr) y hy
      simpa using this
  have hVPlt : Vt M (LB M Q B) B Z t < P := by
    obtain ⟨w0, hw0, hw0V⟩ := hex
    refine lt_of_le_of_ne hVP fun h => hw0V ?_
    obtain ⟨c, hc1, hc2⟩ := hTκ ⟨w0, hw0⟩
    have : (c : G) ∈ P := (hmemP c).mpr (by
      rw [hc2, toAdd_ofAdd]
      exact ⟨_, rfl⟩)
    rw [h, ← hc1]
    exact this
  obtain ⟨g, hg, hQg⟩ := hQx
  have hPle : P ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro y hy
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := hPW hy
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    obtain ⟨w, rfl⟩ := hsurj a
    obtain ⟨c, hc1, hc2⟩ := hTκ w
    have h1 : κ ⟨y, hyW⟩ = κ c := by
      rw [hc2, ha, ofAdd_toAdd]
    have h2 : y * (c : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := (hκ.eq_iff ⟨y, hyW⟩ c).mp h1
    have e : y = (y * (c : G)⁻¹) * (c : G) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right ?_)
    rw [hc1]
    exact hQg _ (hWQ w.2)
  refine ⟨P, hVPlt, hPW, hPR, ?_, ?_⟩
  ·
    have hPcard := natCard_secSub_mul hVW hκ hVP hPW
    rw [hPsec] at hPcard
    have hWcard := natCard_eq_of_isSecMod hVW hκ
    have hkr := AddSubgroup.card_ker_mul_card_range T
    have hle : T.range ≤ T.ker := by
      rintro _ ⟨a, rfl⟩
      exact AddMonoidHom.mem_ker.mpr (hTT a)
    have hcle : Nat.card ↥T.range ≤ Nat.card ↥T.ker := AddSubgroup.card_le_of_le hle
    have hsq : Nat.card ↥T.range * Nat.card ↥T.range ≤ Nat.card Md := by
      calc Nat.card ↥T.range * Nat.card ↥T.range ≤ Nat.card ↥T.ker * Nat.card ↥T.range :=
          Nat.mul_le_mul_right _ hcle
        _ = Nat.card Md := hkr
    rw [← hPcard]
    calc Nat.card ↥T.range * Nat.card ↥(Vt M (LB M Q B) B Z t) *
          (Nat.card ↥T.range * Nat.card ↥(Vt M (LB M Q B) B Z t)) =
        (Nat.card ↥T.range * Nat.card ↥T.range) * Nat.card ↥(Vt M (LB M Q B) B Z t) *
          Nat.card ↥(Vt M (LB M Q B) B Z t) := by ring
      _ ≤ Nat.card Md * Nat.card ↥(Vt M (LB M Q B) B Z t) *
          Nat.card ↥(Vt M (LB M Q B) B Z t) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsq)
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) := by
        rw [hWcard]
        ring
  · intro m hm2 hmtype
    have hcardP : Nat.card ↥P ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
      Nat.card_mono (Set.toFinite _) hPle
    have h1 := card_sup_conj_mul_le hc sec39_Z_le_Vt (hc.Vt_le_Q t) hg
    have hV := card_Vt_orthogonal hc hm2 hmtype
    have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc Nat.card ↥P * Nat.card ↥Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊔
          conjSubgroup g (Vt M (LB M Q B) B Z t)) * Nat.card ↥Z :=
        Nat.mul_le_mul_right _ hcardP
      _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t) := h1
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * (Nat.card ↥Z * Nat.card ↥Z ^ (2 * m)) := by
        rw [← hV]
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 * m) * Nat.card ↥Z := by ring

theorem no_wild_minus6_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hMi : OmegaMinusNat hc t 3)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) (hx2 : x ^ 2 ∈ Q)
    (hQx : ∃ g ∈ M, ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  by_contra hex
  push Not at hex
  obtain ⟨P, hVP, hPW, hPR, -, hPord⟩ :=
    exists_wild_subgroup h52a hA h310chi hc hs hxM hxt hxV hx2 hQx hex
  have hbound := hPord 3 (by norm_num) (Or.inr hMi)
  obtain ⟨k, hk⟩ := ((sec7WVSecCard_of hA hPts h52a h52b) _ M Q Z B hc n t hs P hVP.le hPW hPR 3
    (by norm_num)).1 hMi
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hcardle : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact (ne_of_lt hVP) (Subgroup.eq_of_le_of_card_ge hVP.le hcardle)
  have h3 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 ^ 3 * k) ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 * 3) := hk ▸ hbound
  have h4 := Nat.le_of_mul_le_mul_left h3 hVpos
  have h5 := (Nat.pow_le_pow_iff_right hq).mp h4
  norm_num at h5
  omega

theorem no_wild_plus8_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp : OmegaPlusNat hc t 4)
    (hn : n < 16) {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) (hx2 : x ^ 2 ∈ Q)
    (hQx : ∃ g ∈ M, ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  by_contra hex
  push Not at hex
  obtain ⟨P, hVP, hPW, hPR, hPsq, -⟩ :=
    exists_wild_subgroup h52a hA h310chi hc hs hxM hxt hxV hx2 hQx hex
  obtain ⟨k, hk⟩ := ((sec7WVSecCard_of hA hPts h52a h52b) _ M Q Z B hc n t hs P hVP.le hPW hPR 4
    (by norm_num)).2 hp (by norm_num)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hcardle : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact (ne_of_lt hVP) (Subgroup.eq_of_le_of_card_ge hVP.le hcardle)
  have h52c : Stroth52cStatement := stroth_5_2c_of_chi h310chi
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hchi := card_mul_card_of_isChiIso
    (h52c _ M Q Z B hc n t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl) hWQ hZV
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  have hV4 := n12N_card_V hc t 4 (by norm_num) (Or.inl hp)
  have hVq : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ 9 := by
    rw [hV4]
    ring
  have hPq : Nat.card ↥P = Nat.card Z ^ (9 + 8 * k) := by
    rw [hk, hVq, ← pow_add]
    norm_num
  have e2 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ (2 * n + 2) := by
    rw [mul_comm, ← hchi, hQc]
    ring
  rw [hPq, e2, ← pow_add] at hPsq
  have h5 := (Nat.pow_le_pow_iff_right hq).mp hPsq
  omega

end CFSG.RankThree.GF2n.Stroth80
