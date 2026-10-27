module
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cSkew
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4cPlane
public section
namespace CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.Monster.B.Geometry Module
open scoped Classical
variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]
private lemma plh_inf_eq_bot_iff_not_le {a Y : Submodule K (Fin 4 → K)}
    (ha : finrank K a = 1) : a ⊓ Y = ⊥ ↔ ¬ a ≤ Y := by
  constructor
  · intro h hle
    have hbot : a = ⊥ := by rw [← inf_eq_left.mpr hle]; exact h
    have h0 : finrank K a = 0 := by rw [hbot, finrank_bot]
    omega
  · intro h
    by_contra hne
    have h0 : finrank K ↥(a ⊓ Y) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(a ⊓ Y) ≤ 1 := ha ▸ Submodule.finrank_mono inf_le_left
    have h1 : finrank K ↥(a ⊓ Y) = 1 := by omega
    have heq : a ⊓ Y = a :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, ha])
    exact h (heq ▸ inf_le_right)
private lemma plh_finrank_sup_point {L a : Submodule K (Fin 4 → K)}
    (hL : finrank K L = 2) (ha : finrank K a = 1) (h : ¬ a ≤ L) :
    finrank K ↥(L ⊔ a) = 3 := by
  have hinf : L ⊓ a = ⊥ := by
    rw [inf_comm]
    exact (plh_inf_eq_bot_iff_not_le ha).mpr h
  rw [finrank_sup_of_disjoint (disjoint_iff.mpr hinf), hL, ha]
private lemma plh_conj_not_le_of_le (hK : Nat.card K = (2 ^ f) ^ 2)
    {c L : Submodule K (Fin 4 → K)} (hc : finrank K c = 1) (hcL : c ≤ L)
    (hskew : L ⊓ sgS K f 4 L = ⊥) : ¬ sgS K f 4 c ≤ L := by
  intro h
  have h' : c ≤ sgS K f 4 L := by
    have hmono := sgS_mono (f := f) h
    rwa [sgS_sgS hK c] at hmono
  have hle : c ≤ L ⊓ sgS K f 4 L := le_inf hcL h'
  rw [hskew] at hle
  have hc0 : c = ⊥ := le_bot_iff.mp hle
  rw [hc0, finrank_bot] at hc
  omega
private lemma plh_sup_conj_eq_of_le (hK : Nat.card K = (2 ^ f) ^ 2)
    {c L H : Submodule K (Fin 4 → K)} (hc : finrank K c = 1) (hL : finrank K L = 2)
    (hcL : c ≤ L) (hskew : L ⊓ sgS K f 4 L = ⊥) (hH : finrank K H = 3) (hLH : L ≤ H)
    (hcH : sgS K f 4 c ≤ H) : L ⊔ sgS K f 4 c = H := by
  have hncL : ¬ sgS K f 4 c ≤ L := plh_conj_not_le_of_le (f := f) hK hc hcL hskew
  have hσc1 : finrank K (sgS K f 4 c) = 1 := by rw [finrank_sgS hK]; exact hc
  have hS3 : finrank K ↥(L ⊔ sgS K f 4 c) = 3 := plh_finrank_sup_point hL hσc1 hncL
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hLH hcH) (by rw [hS3, hH])
private lemma plh_inf_of_le_skew {L t R : Submodule K (Fin 4 → K)} (htR : t ≤ R)
    (hLR : L ⊓ R = ⊥) : L ⊓ t = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf] at hw
  have hw' : w ∈ L ⊓ R := ⟨hw.1, htR hw.2⟩
  rw [hLR] at hw'
  exact hw'
private lemma plh_adj_data (hK : Nat.card K = (2 ^ f) ^ 2)
    {p q : Submodule K (Fin 4 → K)} (h : AdmAdj (Adm4c (K := K) f) p q) :
    finrank K p = 1 ∧ finrank K q = 1 ∧ sgS K f 4 p ≠ p ∧ sgS K f 4 q ≠ q ∧
      p ≠ q ∧ (p ⊔ q) ⊓ sgS K f 4 (p ⊔ q) = ⊥ ∧
      finrank K ↥(p ⊔ sgS K f 4 p) = 2 ∧
      finrank K ↥(q ⊔ sgS K f 4 q) = 2 ∧
      (p ⊔ sgS K f 4 p) ⊓ (q ⊔ sgS K f 4 q) = ⊥ := by
  obtain ⟨hpq, L, H, hpLH, hqLH⟩ := h
  have hp1 : finrank K p = 1 := hpLH.1.p1
  have hq1 : finrank K q = 1 := hqLH.1.p1
  have hpn : sgS K f 4 p ≠ p := adm4c_nonreal (f := f) hK hpLH
  have hqn : sgS K f 4 q ≠ q := adm4c_nonreal (f := f) hK hqLH
  have hLp : L = p ⊔ q := by
    refine (Submodule.eq_of_le_of_finrank_eq (sup_le hpLH.1.pL hqLH.1.pL) ?_).symm
    rw [finrank_sup_of_ne_pts hp1 hq1 hpq, hpLH.1.L2]
  have hskew : (p ⊔ q) ⊓ sgS K f 4 (p ⊔ q) = ⊥ := by
    rw [← hLp]; exact hpLH.2.2.1
  exact ⟨hp1, hq1, hpn, hqn, hpq, hskew,
    finrank_realLine (f := f) hK hp1 hpn, finrank_realLine (f := f) hK hq1 hqn,
    (skew_iff (f := f) hK hp1 hq1 hpn hqn hpq).mp hskew⟩
private lemma plh_bad_card_le_one [Fintype K] (hK : Nat.card K = (2 ^ f) ^ 2)
    {u v : Fin 4 → K}
    {Rc S : Submodule K (Fin 4 → K)}
    (hR2 : finrank K ↥(Submodule.span K {u, v}) = 2) (hRc2 : finrank K Rc = 2)
    (hRcS : Rc ≤ S) (hdisj : Rc ⊓ Submodule.span K {u, v} = ⊥) (hS3 : finrank K S = 3) :
    (Finset.univ.filter (fun lam : K => u + lam • v ∈ S)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro lam hlam lam' hlam'
  rw [Finset.mem_filter] at hlam hlam'
  by_contra hne
  have hsub : (lam - lam') • v ∈ S := by
    have h1 : (u + lam • v) - (u + lam' • v) ∈ S := Submodule.sub_mem _ hlam.2 hlam'.2
    have heq : (u + lam • v) - (u + lam' • v) = (lam - lam') • v := by
      rw [sub_smul]; abel
    rwa [heq] at h1
  have hlamne : lam - lam' ≠ 0 := sub_ne_zero.mpr hne
  have hvS : v ∈ S := by
    have h1 : (lam - lam')⁻¹ • ((lam - lam') • v) ∈ S := Submodule.smul_mem _ _ hsub
    rwa [smul_smul, inv_mul_cancel₀ hlamne, one_smul] at h1
  have huS : u ∈ S := by
    have h1 : (u + lam • v) - lam • v ∈ S :=
      Submodule.sub_mem _ hlam.2 (Submodule.smul_mem _ _ hvS)
    simpa using h1
  have hRle : Submodule.span K {u, v} ≤ S := by
    rw [Submodule.span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact huS
    · exact hvS
  have hsup_le : Rc ⊔ Submodule.span K {u, v} ≤ S := sup_le hRcS hRle
  have h4 : finrank K ↥(Rc ⊔ Submodule.span K {u, v}) = 4 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hdisj), hRc2, hR2]
  have hle := Submodule.finrank_mono hsup_le
  rw [h4, hS3] at hle
  omega
private lemma plh_not_conj_self_le (hK : Nat.card K = (2 ^ f) ^ 2)
    {t L R : Submodule K (Fin 4 → K)} (ht1 : finrank K t = 1) (hnt : sgS K f 4 t ≠ t)
    (htR : t ⊔ sgS K f 4 t = R) (hLR : L ⊓ R = ⊥) :
    ¬ sgS K f 4 t ≤ L ⊔ t := by
  intro hst
  obtain ⟨w, -, hwspan⟩ := exists_eq_span_of_finrank_eq_one ht1
  have htRle : t ≤ R := by rw [← htR]; exact le_sup_left
  have hstRle : sgS K f 4 t ≤ R := by rw [← htR]; exact le_sup_right
  have hwt : w ∈ t := by rw [hwspan]; exact Submodule.mem_span_singleton_self w
  have hwR : w ∈ R := htRle hwt
  have hw'mem : sgv K f 4 w ∈ sgS K f 4 t := by
    rw [mem_sgS, sgv_sgv hK]
    exact hwt
  have hw'R : sgv K f 4 w ∈ R := hstRle hw'mem
  obtain ⟨l, hl, y, hy, hsum⟩ := Submodule.mem_sup.mp (hst hw'mem)
  rw [hwspan] at hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
  have hlR : l ∈ R := by
    have hl_eq : l = sgv K f 4 w - c • w := by
      rw [← hsum, ← hc]; abel
    rw [hl_eq]
    exact Submodule.sub_mem _ hw'R (Submodule.smul_mem _ _ hwR)
  have hlbot : l = 0 := by
    have hmem : l ∈ L ⊓ R := ⟨hl, hlR⟩
    rw [hLR] at hmem
    exact hmem
  have hw'eq : sgv K f 4 w = c • w := by rw [← hsum, hlbot, zero_add, ← hc]
  have hle : sgS K f 4 t ≤ t := by
    rw [hwspan, sgS_span_singleton hK, Submodule.span_singleton_le_iff_mem, hw'eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  exact hnt (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_sgS hK]))
private lemma plh_countA (q : ℕ) (hq : 4 ≤ q) : 3 * q ^ 2 + 1 < q ^ 4 := by
  have hq' : (4 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have h : (3 : ℤ) * (q : ℤ) ^ 2 + 1 < (q : ℤ) ^ 4 := by
    nlinarith [sq_nonneg ((q : ℤ) - 4), sq_nonneg ((q : ℤ) ^ 2 - 4 * (q : ℤ))]
  exact_mod_cast h
private lemma plh_countB (q : ℕ) (hq : 4 ≤ q) :
    3 * (q ^ 3 - q) + 3 * q ^ 2 + q < q ^ 4 := by
  have hle : 3 * (q ^ 3 - q) ≤ 3 * q ^ 3 := by
    have h := Nat.sub_le (q ^ 3) q
    omega
  have hq' : (4 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hmain : (3 : ℤ) * (q : ℤ) ^ 3 + 3 * (q : ℤ) ^ 2 + q < (q : ℤ) ^ 4 := by
    nlinarith [sq_nonneg ((q : ℤ) - 4), sq_nonneg ((q : ℤ) ^ 2 - 4 * (q : ℤ))]
  have hmain' : 3 * q ^ 3 + 3 * q ^ 2 + q < q ^ 4 := by exact_mod_cast hmain
  omega
private lemma plh_side (hK : Nat.card K = (2 ^ f) ^ 2)
    {a b t R : Submodule K (Fin 4 → K)}
    (ha1 : finrank K a = 1) (hb1 : finrank K b = 1) (ht1 : finrank K t = 1)
    (hna : sgS K f 4 a ≠ a) (hnb : sgS K f 4 b ≠ b) (hnt : sgS K f 4 t ≠ t)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hLab2 : finrank K ↥(a ⊔ b) = 2)
    (hsab : (a ⊔ b) ⊓ sgS K f 4 (a ⊔ b) = ⊥)
    (hRa : (a ⊔ sgS K f 4 a) ⊓ R = ⊥) (hRb : (b ⊔ sgS K f 4 b) ⊓ R = ⊥)
    (htR : t ⊔ sgS K f 4 t = R) (hLabR : (a ⊔ b) ⊓ R = ⊥)
    (hnsa : ¬ sgS K f 4 a ≤ (a ⊔ b) ⊔ t)
    (hnsb : ¬ sgS K f 4 b ≤ (a ⊔ b) ⊔ t)
    (hnst : ¬ sgS K f 4 t ≤ (a ⊔ b) ⊔ t) :
    AdmAdj (Adm4c (K := K) f) a t ∧ AdmAdj (Adm4c (K := K) f) b t ∧
      AdmPlanar (Adm4c (K := K) f) a b t := by
  have htRle : t ≤ R := by rw [← htR]; exact le_sup_left
  have hdisjLabT : (a ⊔ b) ⊓ t = ⊥ := plh_inf_of_le_skew htRle hLabR
  have hH3 : finrank K ↥((a ⊔ b) ⊔ t) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hdisjLabT), hLab2, ht1]
  have hLabH : (a ⊔ b) ≤ (a ⊔ b) ⊔ t := le_sup_left
  have htH : t ≤ (a ⊔ b) ⊔ t := le_sup_right
  have haH : a ≤ (a ⊔ b) ⊔ t := le_sup_left.trans le_sup_left
  have hbH : b ≤ (a ⊔ b) ⊔ t := le_sup_right.trans le_sup_left
  have hLat2 : finrank K ↥(a ⊔ t) = 2 := finrank_sup_of_ne_pts ha1 ht1 hat
  have hLbt2 : finrank K ↥(b ⊔ t) = 2 := finrank_sup_of_ne_pts hb1 ht1 hbt
  have hLatSkew : (a ⊔ t) ⊓ sgS K f 4 (a ⊔ t) = ⊥ :=
    (skew_iff (f := f) hK ha1 ht1 hna hnt hat).mpr (by rw [htR]; exact hRa)
  have hLbtSkew : (b ⊔ t) ⊓ sgS K f 4 (b ⊔ t) = ⊥ :=
    (skew_iff (f := f) hK hb1 ht1 hnb hnt hbt).mpr (by rw [htR]; exact hRb)
  have hflag_a_Lab : IsFlag a (a ⊔ b) ((a ⊔ b) ⊔ t) :=
    ⟨ha1, hLab2, hH3, le_sup_left, hLabH⟩
  have hflag_b_Lab : IsFlag b (a ⊔ b) ((a ⊔ b) ⊔ t) :=
    ⟨hb1, hLab2, hH3, le_sup_right, hLabH⟩
  have hflag_a_Lat : IsFlag a (a ⊔ t) ((a ⊔ b) ⊔ t) :=
    ⟨ha1, hLat2, hH3, le_sup_left, sup_le haH htH⟩
  have hflag_t_Lat : IsFlag t (a ⊔ t) ((a ⊔ b) ⊔ t) :=
    ⟨ht1, hLat2, hH3, le_sup_right, sup_le haH htH⟩
  have hflag_b_Lbt : IsFlag b (b ⊔ t) ((a ⊔ b) ⊔ t) :=
    ⟨hb1, hLbt2, hH3, le_sup_left, sup_le hbH htH⟩
  have hflag_t_Lbt : IsFlag t (b ⊔ t) ((a ⊔ b) ⊔ t) :=
    ⟨ht1, hLbt2, hH3, le_sup_right, sup_le hbH htH⟩
  have hadm_a_Lab : Adm4c f a (a ⊔ b) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_a_Lab).mpr ⟨hnsa, hsab⟩
  have hadm_b_Lab : Adm4c f b (a ⊔ b) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_b_Lab).mpr ⟨hnsb, hsab⟩
  have hadm_a_Lat : Adm4c f a (a ⊔ t) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_a_Lat).mpr ⟨hnsa, hLatSkew⟩
  have hadm_t_Lat : Adm4c f t (a ⊔ t) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_t_Lat).mpr ⟨hnst, hLatSkew⟩
  have hadm_b_Lbt : Adm4c f b (b ⊔ t) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_b_Lbt).mpr ⟨hnsb, hLbtSkew⟩
  have hadm_t_Lbt : Adm4c f t (b ⊔ t) ((a ⊔ b) ⊔ t) :=
    (adm4c_iff_of_flag (f := f) hK hflag_t_Lbt).mpr ⟨hnst, hLbtSkew⟩
  refine ⟨⟨hat, a ⊔ t, (a ⊔ b) ⊔ t, ⟨hflag_a_Lat, hadm_a_Lat⟩,
      ⟨hflag_t_Lat, hadm_t_Lat⟩⟩,
    ⟨hbt, b ⊔ t, (a ⊔ b) ⊔ t, ⟨hflag_b_Lbt, hadm_b_Lbt⟩,
      ⟨hflag_t_Lbt, hadm_t_Lbt⟩⟩, ?_⟩
  exact ⟨(a ⊔ b) ⊔ t, a ⊔ b, b ⊔ t, a ⊔ t,
    ⟨hflag_a_Lab, hadm_a_Lab⟩, ⟨hflag_b_Lab, hadm_b_Lab⟩,
    ⟨hflag_b_Lbt, hadm_b_Lbt⟩, ⟨hflag_t_Lbt, hadm_t_Lbt⟩,
    ⟨hflag_t_Lat, hadm_t_Lat⟩, ⟨hflag_a_Lat, hadm_a_Lat⟩⟩
theorem adm4c_coneTri (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    AdmConeTri (Adm4c (K := K) f) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro x y z hxy hyz hzx
  obtain ⟨hx1, hy1, hxn, hyn, hxyne, hskewxy, hRx2, hRy2, hRxRy⟩ :=
    plh_adj_data (f := f) hK hxy
  obtain ⟨_, hz1, _, hzn, hyzne, hskewyz, _, hRz2, hRyRz⟩ :=
    plh_adj_data (f := f) hK hyz
  obtain ⟨_, _, _, _, hzxne, hskewzx, _, _, hRzRx⟩ :=
    plh_adj_data (f := f) hK hzx
  have hxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx1 hy1 hxyne
  have hyz2 : finrank K ↥(y ⊔ z) = 2 := finrank_sup_of_ne_pts hy1 hz1 hyzne
  have hzx2 : finrank K ↥(z ⊔ x) = 2 := finrank_sup_of_ne_pts hz1 hx1 hzxne
  let Rx : Submodule K (Fin 4 → K) := x ⊔ sgS K f 4 x
  let Ry : Submodule K (Fin 4 → K) := y ⊔ sgS K f 4 y
  let Rz : Submodule K (Fin 4 → K) := z ⊔ sgS K f 4 z
  let Lxy : Submodule K (Fin 4 → K) := x ⊔ y
  let Lyz : Submodule K (Fin 4 → K) := y ⊔ z
  let Lzx : Submodule K (Fin 4 → K) := z ⊔ x
  let Rs : Finset (Submodule K (Fin 4 → K)) := {Rx, Ry, Rz}
  let Ls : Finset (Submodule K (Fin 4 → K)) := {Lxy, Lyz, Lzx}
  have hR : ∀ R ∈ Rs, finrank K R = 2 ∧ sgS K f 4 R = R := by
    intro R hR
    simp only [Rs, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ⟨hRx2, sgS_realLine (f := f) hK x⟩
    · exact ⟨hRy2, sgS_realLine (f := f) hK y⟩
    · exact ⟨hRz2, sgS_realLine (f := f) hK z⟩
  have hL : ∀ L ∈ Ls, finrank K L = 2 ∧ L ⊓ sgS K f 4 L = ⊥ := by
    intro L hL
    simp only [Ls, Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨hxy2, hskewxy⟩
    · exact ⟨hyz2, hskewyz⟩
    · exact ⟨hzx2, hskewzx⟩
  have hRscard : Rs.card ≤ 3 := by
    simpa only [Rs] using Finset.card_le_three (a := Rx) (b := Ry) (c := Rz)
  have hLscard : Ls.card ≤ 3 := by
    simpa only [Ls] using Finset.card_le_three (a := Lxy) (b := Lyz) (c := Lzx)
  have hcountA : Rs.card * (2 ^ f) ^ 2 + 1 < (2 ^ f) ^ 4 := by
    have h := plh_countA (2 ^ f) hq
    have hmul : Rs.card * (2 ^ f) ^ 2 ≤ 3 * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hRscard
    omega
  have hcountB : Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) + Ls.card * (2 ^ f) ^ 2 + 2 ^ f <
      (2 ^ f) ^ 4 := by
    have hmulR : Rs.card * ((2 ^ f) ^ 3 - 2 ^ f) ≤ 3 * ((2 ^ f) ^ 3 - 2 ^ f) :=
      Nat.mul_le_mul_right _ hRscard
    have hmulL : Ls.card * (2 ^ f) ^ 2 ≤ 3 * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hLscard
    have h := plh_countB (2 ^ f) hq
    omega
  obtain ⟨u, v, hu, hv, huv, hRs, hLs⟩ :=
    exists_real_plane (f := f) hK Rs Ls hR hL hcountA hcountB
  let R0 : Submodule K (Fin 4 → K) := Submodule.span K {u, v}
  have hR0_2 : finrank K R0 = 2 := huv
  have hRxR0 : Rx ⊓ R0 = ⊥ := hRs Rx (by simp [Rs])
  have hRyR0 : Ry ⊓ R0 = ⊥ := hRs Ry (by simp [Rs])
  have hRzR0 : Rz ⊓ R0 = ⊥ := hRs Rz (by simp [Rs])
  have hLxyR0 : Lxy ⊓ R0 = ⊥ := hLs Lxy (by simp [Ls])
  have hLyzR0 : Lyz ⊓ R0 = ⊥ := hLs Lyz (by simp [Ls])
  have hLzxR0 : Lzx ⊓ R0 = ⊥ := hLs Lzx (by simp [Ls])
  let S1 : Submodule K (Fin 4 → K) := (x ⊔ y) ⊔ sgS K f 4 x
  let S2 : Submodule K (Fin 4 → K) := (x ⊔ y) ⊔ sgS K f 4 y
  let S3 : Submodule K (Fin 4 → K) := (y ⊔ z) ⊔ sgS K f 4 y
  let S4 : Submodule K (Fin 4 → K) := (y ⊔ z) ⊔ sgS K f 4 z
  let S5 : Submodule K (Fin 4 → K) := (z ⊔ x) ⊔ sgS K f 4 z
  let S6 : Submodule K (Fin 4 → K) := (z ⊔ x) ⊔ sgS K f 4 x
  let T : Finset (Submodule K (Fin 4 → K)) := {S1, S2, S3, S4, S5, S6}
  have hσx1 : finrank K (sgS K f 4 x) = 1 := by rw [finrank_sgS hK]; exact hx1
  have hσy1 : finrank K (sgS K f 4 y) = 1 := by rw [finrank_sgS hK]; exact hy1
  have hσz1 : finrank K (sgS K f 4 z) = 1 := by rw [finrank_sgS hK]; exact hz1
  have hS1_3 : finrank K S1 = 3 :=
    plh_finrank_sup_point hxy2 hσx1 (plh_conj_not_le_of_le (f := f) hK hx1 le_sup_left hskewxy)
  have hS2_3 : finrank K S2 = 3 :=
    plh_finrank_sup_point hxy2 hσy1 (plh_conj_not_le_of_le (f := f) hK hy1 le_sup_right hskewxy)
  have hS3_3 : finrank K S3 = 3 :=
    plh_finrank_sup_point hyz2 hσy1 (plh_conj_not_le_of_le (f := f) hK hy1 le_sup_left hskewyz)
  have hS4_3 : finrank K S4 = 3 :=
    plh_finrank_sup_point hyz2 hσz1 (plh_conj_not_le_of_le (f := f) hK hz1 le_sup_right hskewyz)
  have hS5_3 : finrank K S5 = 3 :=
    plh_finrank_sup_point hzx2 hσz1 (plh_conj_not_le_of_le (f := f) hK hz1 le_sup_left hskewzx)
  have hS6_3 : finrank K S6 = 3 :=
    plh_finrank_sup_point hzx2 hσx1 (plh_conj_not_le_of_le (f := f) hK hx1 le_sup_right hskewzx)
  have hbad1 : ∀ S ∈ T,
      (Finset.univ.filter (fun lam : K => u + lam • v ∈ S)).card ≤ 1 := by
    intro S hS
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRx2
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hRxR0 hS1_3
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRy2
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hRyR0 hS2_3
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRy2
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hRyR0 hS3_3
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRz2
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hRzR0 hS4_3
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRz2
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hRzR0 hS5_3
    · exact plh_bad_card_le_one (f := f) hK hR0_2 hRx2
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hRxR0 hS6_3
  let bad : Finset K :=
    T.biUnion (fun S => Finset.univ.filter (fun lam : K => u + lam • v ∈ S))
  have hTcard : T.card ≤ 6 := by
    simpa only [T] using Finset.card_le_six (a := S1) (b := S2) (c := S3) (d := S4)
      (e := S5) (f := S6)
  have hbadcard : bad.card ≤ 6 := by
    calc bad.card ≤ ∑ S ∈ T, (Finset.univ.filter (fun lam : K => u + lam • v ∈ S)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ S ∈ T, 1 := Finset.sum_le_sum hbad1
      _ = T.card := by simp
      _ ≤ 6 := hTcard
  let moved : Finset K := Finset.univ.filter (fun lam : K => sg K f lam ≠ lam)
  have hmoved_card : moved.card = Nat.card {lam : K // sg K f lam ≠ lam} := by
    simp only [moved, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmoved_gt : 6 < moved.card := by
    have h12 : 12 ≤ Nat.card K - 2 ^ f := by
      rw [hK, pow_two]
      have hsub : 2 ^ f * 2 ^ f - 2 ^ f = 2 ^ f * (2 ^ f - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [hsub]
      have hmul : 4 * 3 ≤ 2 ^ f * (2 ^ f - 1) := Nat.mul_le_mul hq (by omega)
      omega
    have hge := card_sg_moved_ge (K := K) (f := f) hK
    rw [← hmoved_card] at hge
    omega
  obtain ⟨lam, hlam_mem, hlam_notMem⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := bad) (t := moved) (by omega)
  have hlam_sg : sg K f lam ≠ lam := (Finset.mem_filter.mp hlam_mem).2
  have hlam_out : ∀ S ∈ T, u + lam • v ∉ S := by
    intro S hS hmem
    exact hlam_notMem (Finset.mem_biUnion.mpr
      ⟨S, hS, Finset.mem_filter.mpr ⟨Finset.mem_univ lam, hmem⟩⟩)
  have hreal := realPlane_point (f := f) hK hu hv huv (lam := lam) hlam_sg
  let t : Submodule K (Fin 4 → K) := Submodule.span K {u + lam • v}
  have ht1 : finrank K t = 1 := hreal.1
  have htn : sgS K f 4 t ≠ t := hreal.2.1
  have htR : t ⊔ sgS K f 4 t = R0 := hreal.2.2
  have htRle : t ≤ R0 := by rw [← htR]; exact le_sup_left
  have hw1 : u + lam • v ∉ S1 := hlam_out S1 (by simp [T])
  have hw2 : u + lam • v ∉ S2 := hlam_out S2 (by simp [T])
  have hw3 : u + lam • v ∉ S3 := hlam_out S3 (by simp [T])
  have hw4 : u + lam • v ∉ S4 := hlam_out S4 (by simp [T])
  have hw5 : u + lam • v ∉ S5 := hlam_out S5 (by simp [T])
  have hw6 : u + lam • v ∉ S6 := hlam_out S6 (by simp [T])
  have htS1 : ¬ t ≤ S1 := fun h => hw1 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have htS2 : ¬ t ≤ S2 := fun h => hw2 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have htS3 : ¬ t ≤ S3 := fun h => hw3 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have htS4 : ¬ t ≤ S4 := fun h => hw4 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have htS5 : ¬ t ≤ S5 := fun h => hw5 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have htS6 : ¬ t ≤ S6 := fun h => hw6 (h (Submodule.mem_span_singleton_self (u + lam • v)))
  have hHxy3 : finrank K ↥((x ⊔ y) ⊔ t) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr (plh_inf_of_le_skew htRle hLxyR0)), hxy2, ht1]
  have hHyz3 : finrank K ↥((y ⊔ z) ⊔ t) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr (plh_inf_of_le_skew htRle hLyzR0)), hyz2, ht1]
  have hHzx3 : finrank K ↥((z ⊔ x) ⊔ t) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr (plh_inf_of_le_skew htRle hLzxR0)), hzx2, ht1]
  have hnSx : ¬ sgS K f 4 x ≤ (x ⊔ y) ⊔ t := by
    intro h
    have heq : (x ⊔ y) ⊔ sgS K f 4 x = (x ⊔ y) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hx1 hxy2 le_sup_left hskewxy hHxy3 le_sup_left h
    exact htS1 (by change t ≤ (x ⊔ y) ⊔ sgS K f 4 x; exact heq.symm ▸ le_sup_right)
  have hnSy : ¬ sgS K f 4 y ≤ (x ⊔ y) ⊔ t := by
    intro h
    have heq : (x ⊔ y) ⊔ sgS K f 4 y = (x ⊔ y) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hy1 hxy2 le_sup_right hskewxy hHxy3 le_sup_left h
    exact htS2 (by change t ≤ (x ⊔ y) ⊔ sgS K f 4 y; exact heq.symm ▸ le_sup_right)
  have hnStxy : ¬ sgS K f 4 t ≤ (x ⊔ y) ⊔ t :=
    plh_not_conj_self_le (f := f) hK ht1 htn htR hLxyR0
  have hnSy2 : ¬ sgS K f 4 y ≤ (y ⊔ z) ⊔ t := by
    intro h
    have heq : (y ⊔ z) ⊔ sgS K f 4 y = (y ⊔ z) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hy1 hyz2 le_sup_left hskewyz hHyz3 le_sup_left h
    exact htS3 (by change t ≤ (y ⊔ z) ⊔ sgS K f 4 y; exact heq.symm ▸ le_sup_right)
  have hnSz : ¬ sgS K f 4 z ≤ (y ⊔ z) ⊔ t := by
    intro h
    have heq : (y ⊔ z) ⊔ sgS K f 4 z = (y ⊔ z) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hz1 hyz2 le_sup_right hskewyz hHyz3 le_sup_left h
    exact htS4 (by change t ≤ (y ⊔ z) ⊔ sgS K f 4 z; exact heq.symm ▸ le_sup_right)
  have hnStyz : ¬ sgS K f 4 t ≤ (y ⊔ z) ⊔ t :=
    plh_not_conj_self_le (f := f) hK ht1 htn htR hLyzR0
  have hnSz3 : ¬ sgS K f 4 z ≤ (z ⊔ x) ⊔ t := by
    intro h
    have heq : (z ⊔ x) ⊔ sgS K f 4 z = (z ⊔ x) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hz1 hzx2 le_sup_left hskewzx hHzx3 le_sup_left h
    exact htS5 (by change t ≤ (z ⊔ x) ⊔ sgS K f 4 z; exact heq.symm ▸ le_sup_right)
  have hnSx3 : ¬ sgS K f 4 x ≤ (z ⊔ x) ⊔ t := by
    intro h
    have heq : (z ⊔ x) ⊔ sgS K f 4 x = (z ⊔ x) ⊔ t :=
      plh_sup_conj_eq_of_le (f := f) hK hx1 hzx2 le_sup_right hskewzx hHzx3 le_sup_left h
    exact htS6 (by change t ≤ (z ⊔ x) ⊔ sgS K f 4 x; exact heq.symm ▸ le_sup_right)
  have hnStzx : ¬ sgS K f 4 t ≤ (z ⊔ x) ⊔ t :=
    plh_not_conj_self_le (f := f) hK ht1 htn htR hLzxR0
  have hxt : x ≠ t := by
    intro h
    have hxR : x ≤ R0 := by rw [h]; exact htRle
    have hle : x ≤ Rx ⊓ R0 := le_inf le_sup_left hxR
    rw [hRxR0] at hle
    have hx0 : x = ⊥ := le_bot_iff.mp hle
    rw [hx0, finrank_bot] at hx1
    omega
  have hyt : y ≠ t := by
    intro h
    have hyR : y ≤ R0 := by rw [h]; exact htRle
    have hle : y ≤ Ry ⊓ R0 := le_inf le_sup_left hyR
    rw [hRyR0] at hle
    have hy0 : y = ⊥ := le_bot_iff.mp hle
    rw [hy0, finrank_bot] at hy1
    omega
  have hzt : z ≠ t := by
    intro h
    have hzR : z ≤ R0 := by rw [h]; exact htRle
    have hle : z ≤ Rz ⊓ R0 := le_inf le_sup_left hzR
    rw [hRzR0] at hle
    have hz0 : z = ⊥ := le_bot_iff.mp hle
    rw [hz0, finrank_bot] at hz1
    omega
  have hxy_side := plh_side (f := f) hK hx1 hy1 ht1 hxn hyn htn hxyne hxt hyt hxy2
    hskewxy hRxR0 hRyR0 htR hLxyR0 hnSx hnSy hnStxy
  have hyz_side := plh_side (f := f) hK hy1 hz1 ht1 hyn hzn htn hyzne hyt hzt hyz2
    hskewyz hRyR0 hRzR0 htR hLyzR0 hnSy2 hnSz hnStyz
  have hzx_side := plh_side (f := f) hK hz1 hx1 ht1 hzn hxn htn hzxne hzt hxt hzx2
    hskewzx hRzR0 hRxR0 htR hLzxR0 hnSz3 hnSx3 hnStzx
  exact ⟨t, hxy_side.1, hxy_side.2.1, hyz_side.2.1,
    hxy_side.2.2, hyz_side.2.2, hzx_side.2.2⟩
end CFSG.ClassicalInvolution.Phan.PhanE
end
