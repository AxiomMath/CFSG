module

public import CFSG.Quasithin.Recognition.St84.Sec5GA

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

@[expose] def ZtExt (Y : Setup Γ G) (i : ℤ) (l r : ℕ) : Prop :=
  (∀ j : ℤ, -(l : ℤ) ≤ j → j ≤ (r : ℤ) → Y.Zt i ≤ Y.Gi (i + j)) ∧
    ¬ Y.Zt i ≤ Y.Gi (i + (r : ℤ) + 1) ∧ ¬ Y.Zt i ≤ Y.Gi (i - (l : ℤ) - 1)

theorem ZtExt.one_le {Y : Setup Γ G} {i : ℤ} {l r : ℕ} (he : Y.ZtExt i l r) :
    1 ≤ l ∧ 1 ≤ r := by
  have hZl : Y.Zt i ≤ Y.Gi (i - 1) :=
    (Y.Zt_le_Z i).trans ((Y.Z_le_Q i).trans ((Y.Q_le_Gi_adj i).trans inf_le_left))
  have hZr : Y.Zt i ≤ Y.Gi (i + 1) :=
    (Y.Zt_le_Z i).trans ((Y.Z_le_Q i).trans ((Y.Q_le_Gi_adj i).trans inf_le_right))
  constructor
  · rcases Nat.eq_zero_or_pos l with h | h
    · exfalso
      apply he.2.2
      simpa [h] using hZl
    · exact h
  · rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      apply he.2.1
      simpa [h] using hZr
    · exact h

theorem ZtExt.Zt_two_mul_le_Gi {Y : Setup Γ G} {l r : ℕ} (he : Y.ZtExt 0 l r) (m : ℤ) :
    ∀ j : ℤ, -(l : ℤ) ≤ j → j ≤ (r : ℤ) → Y.Zt (2 * m) ≤ Y.Gi (2 * m + j) := by
  intro j h1 h2
  have hZt : Y.Zt (2 * m) = conjSub (Y.τ ^ m) (Y.Zt 0) := by
    simpa using Y.Zt_add m 0
  rw [hZt]
  have hle : Y.Zt 0 ≤ Y.Gi (0 + j) := he.1 j h1 h2
  have hconj : conjSub (Y.τ ^ m) (Y.Zt 0) ≤ conjSub (Y.τ ^ m) (Y.Gi (0 + j)) :=
    conjSub_mono _ hle
  rw [← Y.Gi_add m (0 + j)] at hconj
  rwa [show (0 : ℤ) + j + 2 * m = 2 * m + j from by ring] at hconj

theorem ZtExt.Zt_le_Gi_zero {Y : Setup Γ G} {r₀ : ℕ} (he : Y.ZtExt 0 r₀ r₀)
    (heven : Even r₀) : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := by
  obtain ⟨k, hk⟩ := heven
  have hcast : (r₀ : ℤ) = 2 * (k : ℤ) := by
    have h : (r₀ : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    linarith
  have h := he.Zt_two_mul_le_Gi (k : ℤ) (-(r₀ : ℤ)) (by linarith) (by linarith)
  have h2 : 2 * (k : ℤ) + -(r₀ : ℤ) = 0 := by linarith
  rw [h2] at h
  exact hcast.symm ▸ h

theorem ZtExt.add_two_mul {Y : Setup Γ G} {i : ℤ} {l r : ℕ} (he : Y.ZtExt i l r) (m : ℤ) :
    Y.ZtExt (i + 2 * m) l r := by
  have hZt : Y.Zt (i + 2 * m) = conjSub (Y.τ ^ m) (Y.Zt i) := Y.Zt_add m i
  have hGi : ∀ j : ℤ, Y.Gi (i + 2 * m + j) = conjSub (Y.τ ^ m) (Y.Gi (i + j)) := by
    intro j
    have h := Y.Gi_add m (i + j)
    rwa [show i + j + 2 * m = i + 2 * m + j by ring] at h
  refine ⟨?_, ?_, ?_⟩
  · intro j h1 h2
    rw [hZt, hGi]
    exact conjSub_mono _ (he.1 j h1 h2)
  · intro hle
    apply he.2.1
    have h := conjSub_mono (Y.τ ^ (-m)) hle
    have hZ : conjSub (Y.τ ^ (-m)) (Y.Zt (i + 2 * m)) = Y.Zt i := by
      have h' := Y.Zt_add (-m) (i + 2 * m)
      rw [show i + 2 * m + 2 * (-m) = i by ring] at h'
      exact h'.symm
    have hG : conjSub (Y.τ ^ (-m)) (Y.Gi (i + 2 * m + (r : ℤ) + 1)) =
        Y.Gi (i + (r : ℤ) + 1) := by
      have h' := Y.Gi_add (-m) (i + 2 * m + (r : ℤ) + 1)
      rw [show i + 2 * m + (r : ℤ) + 1 + 2 * (-m) = i + (r : ℤ) + 1 by ring] at h'
      exact h'.symm
    rwa [hZ, hG] at h
  · intro hle
    apply he.2.2
    have h := conjSub_mono (Y.τ ^ (-m)) hle
    have hZ : conjSub (Y.τ ^ (-m)) (Y.Zt (i + 2 * m)) = Y.Zt i := by
      have h' := Y.Zt_add (-m) (i + 2 * m)
      rw [show i + 2 * m + 2 * (-m) = i by ring] at h'
      exact h'.symm
    have hG : conjSub (Y.τ ^ (-m)) (Y.Gi (i + 2 * m - (l : ℤ) - 1)) =
        Y.Gi (i - (l : ℤ) - 1) := by
      have h' := Y.Gi_add (-m) (i + 2 * m - (l : ℤ) - 1)
      rw [show i + 2 * m - (l : ℤ) - 1 + 2 * (-m) = i - (l : ℤ) - 1 by ring] at h'
      exact h'.symm
    rwa [hZ, hG] at h

theorem ZtExt.mirror1 {Y : Setup Γ G} {i : ℤ} {l r : ℕ} (he : Y.ZtExt i l r) :
    Y.mirror1.ZtExt (2 - i) r l := by
  have hZ : Y.mirror1.Zt (2 - i) = Y.Zt i := by
    rw [Setup.mirror1_Zt]
    congr 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro j h1 h2
    have h := he.1 (-j) (by omega) (by omega)
    have hGi : Y.mirror1.Gi (2 - i + j) = Y.Gi (i + -j) := by
      rw [Setup.mirror1_Gi]
      congr 1
      ring
    rw [hZ, hGi]
    exact h
  · intro hle
    apply he.2.2
    have hGi : Y.mirror1.Gi (2 - i + (l : ℤ) + 1) = Y.Gi (i - (l : ℤ) - 1) := by
      rw [Setup.mirror1_Gi]
      congr 1
      ring
    rw [hZ, hGi] at hle
    exact hle
  · intro hle
    apply he.2.1
    have hGi : Y.mirror1.Gi (2 - i - (r : ℤ) - 1) = Y.Gi (i + (r : ℤ) + 1) := by
      rw [Setup.mirror1_Gi]
      congr 1
      ring
    rw [hZ, hGi] at hle
    exact hle

theorem ZtExt.reverse {Y : Setup Γ G} {l r : ℕ} (he : Y.ZtExt 0 l r) :
    Y.reverse.ZtExt 0 r l := by
  refine ⟨?_, ?_, ?_⟩
  · intro j h1 h2
    have h := he.1 (-j) (by omega) (by omega)
    simpa [Setup.reverse_Zt, Setup.reverse_Gi] using h
  · intro hle
    apply he.2.2
    have hle' : Y.Zt 0 ≤ Y.Gi (-1 + -(l : ℤ)) := by
      simpa [Setup.reverse_Zt, Setup.reverse_Gi] using hle
    have harg : (-1 : ℤ) + -(l : ℤ) = (0 : ℤ) - (l : ℤ) - 1 := by ring
    rwa [harg] at hle'
  · intro hle
    apply he.2.1
    have hle' : Y.Zt 0 ≤ Y.Gi (1 + (r : ℤ)) := by
      simpa [Setup.reverse_Zt, Setup.reverse_Gi] using hle
    have harg : (1 : ℤ) + (r : ℤ) = (0 : ℤ) + (r : ℤ) + 1 := by ring
    rwa [harg] at hle'

theorem comm_Zt_Zt_le_Z (Y : Setup Γ G) {r₀ : ℕ} (he : Y.ZtExt 0 r₀ r₀) :
    ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have haG : a ∈ Y.Gi (r₀ : ℤ) := by
    have h := he.1 (r₀ : ℤ) (by linarith) (le_refl _) ha
    simpa using h
  have hbZ : b ∈ Y.Z (r₀ : ℤ) := Y.Zt_le_Z (r₀ : ℤ) hb
  have hconj : a * b * a⁻¹ ∈ Y.Z (r₀ : ℤ) := by
    have h := mul_mem_conjSub (g := a) (H := Y.Z (r₀ : ℤ)) hbZ
    rwa [Y.Z_normal (r₀ : ℤ) a haG] at h
  have hmem : (a * b * a⁻¹) * b⁻¹ ∈ Y.Z (r₀ : ℤ) :=
    Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hbZ)
  simpa only [mul_assoc] using hmem

private theorem Q_le_centralizer_Zt (Y : Setup Γ G) (m : ℤ) :
    Y.Q m ≤ Subgroup.centralizer (Y.Zt m : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzc : z ∈ Subgroup.centralizer (Y.Q m : Set G) := (Y.Z_le_center m (Zt_le_Z Y m hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm

private theorem map_fixedPointSubgroup_eq_inf {G : Type*} [Group G] {W R : Subgroup G}
    [Subgroup.Normalizes R W] :
    (CFSG.fixedPointSubgroup ↥R ↥W).map W.subtype =
      W ⊓ Subgroup.centralizer (R : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hfix := hy ⟨k, hk⟩
    have hcoe := congrArg (fun t : ↥W => (t : G)) hfix
    simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hcoe
    calc k * (y : G) = (k * (y : G) * k⁻¹) * k := by group
      _ = (y : G) * k := by rw [hcoe]
  · rintro ⟨hxW, hxC⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    intro a
    apply Subtype.ext
    simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    calc (a : G) * x * (a : G)⁻¹ = (x * (a : G)) * (a : G)⁻¹ := by
          rw [Subgroup.mem_centralizer_iff.mp hxC (a : G) a.2]
      _ = x := by group

private theorem eq_commutator_of_inf_centralizer_eq_bot {G : Type*} [Group G]
    {W R : Subgroup G} [Subgroup.Normalizes R W] [Finite ↥W] [Finite ↥R]
    (hW2 : IsPGroup 2 W) (hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hRodd : Odd (Nat.card ↥R))
    (hinf : W ⊓ Subgroup.centralizer (R : Set G) = ⊥) : W = ⁅W, R⁆ := by
  letI : IsMulCommutative ↥W := IsMulCommutative.of_comm
    (fun a b => Subtype.ext (hWcomm a.1 a.2 b.1 b.2))
  have hsolv : Group.IsSolvable ↥W := inferInstance
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW2
  have hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥W) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hRodd).pow_right n
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := ↥W) (A := ↥R) hsolv hcop inferInstance
  have hF := map_fixedPointSubgroup_eq_inf (W := W) (R := R)
  have hC := CFSG.commutatorAction_subgroup_conj_map_eq_commutator W R
    Subgroup.Normalizes.le_normalizer
  have htop : Subgroup.map W.subtype (⊤ : Subgroup ↥W) = W := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) W
  have h := congrArg (Subgroup.map W.subtype) hcompl.sup_eq_top
  rw [Subgroup.map_sup, htop, hF, hC, hinf, bot_sup_eq] at h
  exact h.symm

theorem exists_ZtExt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {i : ℤ} (hZ : Y.Zt i ≠ ⊥) :
    ∃ l r : ℕ, 1 ≤ l ∧ 1 ≤ r ∧ Y.ZtExt i l r := by
  classical
  obtain ⟨r, -, -, hr⟩ := exists_isMaxRegLen Y H
  have hZt_le_Z : Y.Zt i ≤ Y.Z i := Y.Zt_le_Z i
  have hZt2 : IsPGroup 2 ↥(Y.Zt i) := Y.isPGroup_Zt i
  have hle0 : Y.Zt i ≤ Y.Gi i := hZt_le_Z.trans ((Y.Z_le_Q i).trans (Y.Q_le_Gi i))
  have hle1 : Y.Zt i ≤ Y.Gi (i + 1) := hZt_le_Z.trans ((Y.Z_le_Q i).trans (by
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert i (Y.vert (i + 1)) (Y.adj i) q hq)))
  have hlem1 : Y.Zt i ≤ Y.Gi (i - 1) := hZt_le_Z.trans ((Y.Z_le_Q i).trans (by
    intro q hq
    have hadj : Γ.Adj (Y.vert i) (Y.vert (i - 1)) := by
      have h := (Y.adj (i - 1)).symm
      rwa [show i - 1 + 1 = i by ring] at h
    exact MulAction.mem_stabilizer_iff.mpr
      (Y.Q_fixes_neighbors_vert i (Y.vert (i - 1)) hadj q hq)))
  have hex : ∃ k : ℕ, ¬ Y.Zt i ≤ Y.Gi (i + (k : ℤ)) := by
    refine ⟨r + 1, ?_⟩
    intro hle
    have harc : Y.arcStab i (i + ((r : ℤ) + 1)) = Y.GT := by
      have h := hr.2 i (r + 1) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h
    have hZI : Y.Zt i ≤ Y.arcStab i (i + ((r : ℤ) + 1)) := by
      rw [Y.arcStab_eq_inf (by omega)]
      exact le_inf hle0 (by simpa only [Nat.cast_add, Nat.cast_one] using hle)
    have hZGT : Y.Zt i ≤ Y.GT := harc ▸ hZI
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.GT) (B := Y.Zt i) H.odd_GT hZt2
    rw [inf_eq_right.mpr hZGT] at hbot
    exact hZ hbot
  have hexl : ∃ k : ℕ, ¬ Y.Zt i ≤ Y.Gi (i - (k : ℤ)) := by
    refine ⟨r + 1, ?_⟩
    intro hle
    have hsum : i - ((r : ℤ) + 1) + ((r + 1 : ℕ) : ℤ) = i := by push_cast; ring
    have harc : Y.arcStab (i - ((r : ℤ) + 1)) i = Y.GT := by
      have h := hr.2 (i - ((r : ℤ) + 1)) (r + 1) (by omega)
      simpa only [hsum] using h
    have hZI : Y.Zt i ≤ Y.arcStab (i - ((r : ℤ) + 1)) i := by
      rw [Y.arcStab_eq_inf (by omega)]
      exact le_inf hle hle0
    have hZGT : Y.Zt i ≤ Y.GT := harc ▸ hZI
    have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.GT) (B := Y.Zt i) H.odd_GT hZt2
    rw [inf_eq_right.mpr hZGT] at hbot
    exact hZ hbot
  set rr := Nat.find hex with hrrdef
  set ll := Nat.find hexl with hlldef
  have hrr_spec : ¬ Y.Zt i ≤ Y.Gi (i + ((rr : ℕ) : ℤ)) := by
    simpa only [hrrdef] using Nat.find_spec hex
  have hll_spec : ¬ Y.Zt i ≤ Y.Gi (i - ((ll : ℕ) : ℤ)) := by
    simpa only [hlldef] using Nat.find_spec hexl
  have hrr2 : 2 ≤ rr := by
    have h0 : rr ≠ 0 := by
      intro h
      exact hrr_spec (by rw [h]; simpa using hle0)
    have h1 : rr ≠ 1 := by
      intro h
      exact hrr_spec (by rw [h]; simpa using hle1)
    omega
  have hll2 : 2 ≤ ll := by
    have h0 : ll ≠ 0 := by
      intro h
      exact hll_spec (by rw [h]; simpa using hle0)
    have h1 : ll ≠ 1 := by
      intro h
      exact hll_spec (by rw [h]; simpa using hlem1)
    omega
  have hright : ∀ j : ℤ, 0 ≤ j → j ≤ ((rr - 1 : ℕ) : ℤ) → Y.Zt i ≤ Y.Gi (i + j) := by
    intro j hj0 hj
    have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hlt : j.toNat < rr := by
      have h1 : (j.toNat : ℤ) ≤ ((rr - 1 : ℕ) : ℤ) := by rw [hjcast]; exact hj
      omega
    have hlt' : j.toNat < Nat.find hex := by rwa [← hrrdef]
    have hmin := Nat.find_min hex hlt'
    have := of_not_not hmin
    simpa only [hjcast] using this
  have hleft : ∀ j : ℤ, -((ll - 1 : ℕ) : ℤ) ≤ j → j ≤ 0 → Y.Zt i ≤ Y.Gi (i + j) := by
    intro j hj0 hj
    set k : ℕ := (-j).toNat with hk
    have hkcast : ((k : ℕ) : ℤ) = -j := by
      rw [hk]
      exact Int.toNat_of_nonneg (by omega)
    have hlt : k < ll := by
      have h1 : (k : ℤ) < (ll : ℤ) := by
        rw [hkcast]
        have h2 : -(j : ℤ) ≤ ((ll - 1 : ℕ) : ℤ) := by omega
        have h3 : (ll : ℤ) = ((ll - 1 : ℕ) : ℤ) + 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
        omega
      exact_mod_cast h1
    have hlt' : k < Nat.find hexl := by rwa [← hlldef]
    have hmin := Nat.find_min hexl hlt'
    have hres := of_not_not hmin
    have hkj : i - (k : ℤ) = i + j := by rw [hkcast]; ring
    rwa [hkj] at hres
  refine ⟨ll - 1, rr - 1, by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2
    rcases le_total 0 j with hj | hj
    · exact hright j hj hj2
    · exact hleft j (by omega) hj
  · have hcast : i + ((rr - 1 : ℕ) : ℤ) + 1 = i + (rr : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
    rwa [hcast]
  · have hcast : i - ((ll - 1 : ℕ) : ℤ) - 1 = i - (ll : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
    rwa [hcast]

theorem Zt_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (i : ℤ) :
    Y.Z i = (Y.Z i ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.Zt i ∧
      Y.Zt i ⊓ Subgroup.centralizer (Y.K : Set G) = ⊥ ∧ ⁅Y.Zt i, Y.K⁆ = Y.Zt i := by
  have hKH : Y.K ≤ Subgroup.normalizer (Y.Z i : Set G) := Y.K_le_normalizer_Z i
  haveI hHfin : Finite ↥(Y.Z i) := finite_of_le_stabilizer Y.hyp (H := Y.Z i) (Y.Z_le_Gi i)
  haveI hKfin : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (H := Y.K) (Y.K_le_Gi 0)
  letI hNorm : Subgroup.Normalizes Y.K (Y.Z i) := ⟨hKH⟩
  have hcommH : ∀ x ∈ Y.Z i, ∀ y ∈ Y.Z i, x * y = y * x := Y.Z_commute i
  haveI hMC : IsMulCommutative ↥(Y.Z i) :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hcommH a.1 a.2 b.1 b.2))
  have hHsolv : Group.IsSolvable ↥(Y.Z i) := inferInstance
  have hH2 : IsPGroup 2 ↥(Y.Z i) := (pCoreOf_isPGroup' (Y.Gi i)).to_le (Y.Z_le_Q i)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH2
  have hKodd : Odd (Nat.card ↥Y.K) := by
    rw [← GT_eq_K_of_sec5Hyp Y H]
    exact H.odd_GT
  have hcop : Nat.Coprime (Nat.card ↥Y.K) (Nat.card ↥(Y.Z i)) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hKodd).pow_right n
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := ↥(Y.Z i)) (A := ↥Y.K) hHsolv hcop hMC
  have hF := map_fixedPointSubgroup_eq_inf (W := Y.Z i) (R := Y.K)
  have hC : (CFSG.commutatorAction (A := ↥Y.K) (G := ↥(Y.Z i))).map (Y.Z i).subtype =
      Y.Zt i := by
    rw [Setup.Zt]
    exact CFSG.commutatorAction_subgroup_conj_map_eq_commutator (Y.Z i) Y.K hKH
  have htopH : Subgroup.map (Y.Z i).subtype (⊤ : Subgroup ↥(Y.Z i)) = Y.Z i := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) (Y.Z i)
  have hsup : Y.Z i = (Y.Z i ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.Zt i := by
    have h := congrArg (Subgroup.map (Y.Z i).subtype) hcompl.sup_eq_top
    rw [Subgroup.map_sup, htopH, hF, hC] at h
    exact h.symm
  have hdisj : Y.Zt i ⊓ Subgroup.centralizer (Y.K : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxZt, hxC⟩
    have hxZ : x ∈ Y.Z i := Zt_le_Z Y i hxZt
    have hxF : x ∈ (CFSG.fixedPointSubgroup ↥Y.K ↥(Y.Z i)).map (Y.Z i).subtype := by
      rw [hF]
      exact Subgroup.mem_inf.mpr ⟨hxZ, hxC⟩
    have hxCa : x ∈ (CFSG.commutatorAction (A := ↥Y.K) (G := ↥(Y.Z i))).map
        (Y.Z i).subtype := by
      rw [hC]
      exact hxZt
    obtain ⟨y, hyF, hyx⟩ := Subgroup.mem_map.mp hxF
    obtain ⟨z, hzC, hzx⟩ := Subgroup.mem_map.mp hxCa
    have hy : y = (⟨x, hxZ⟩ : ↥(Y.Z i)) := Subtype.ext hyx
    have hz : z = (⟨x, hxZ⟩ : ↥(Y.Z i)) := Subtype.ext hzx
    have hmem : (⟨x, hxZ⟩ : ↥(Y.Z i)) ∈
        CFSG.fixedPointSubgroup ↥Y.K ↥(Y.Z i) ⊓
          CFSG.commutatorAction (A := ↥Y.K) (G := ↥(Y.Z i)) :=
      ⟨hy ▸ hyF, hz ▸ hzC⟩
    have hzero : (⟨x, hxZ⟩ : ↥(Y.Z i)) = 1 := by
      have hinf : CFSG.fixedPointSubgroup ↥Y.K ↥(Y.Z i) ⊓
          CFSG.commutatorAction (A := ↥Y.K) (G := ↥(Y.Z i)) = ⊥ :=
        disjoint_iff.mp hcompl.disjoint
      exact Subgroup.mem_bot.mp (hinf ▸ hmem)
    exact Subtype.ext_iff.mp hzero
  have hthird : ⁅Y.Zt i, Y.K⁆ = Y.Zt i := by
    have hKnorm : Y.K ≤ Subgroup.normalizer (Y.Zt i : Set G) := Y.K_le_normalizer_Zt i
    haveI hCfin : Finite ↥(Y.Zt i) :=
      finite_of_le_stabilizer Y.hyp (H := Y.Zt i) ((Zt_le_Z Y i).trans (Y.Z_le_Gi i))
    letI hNormC : Subgroup.Normalizes Y.K (Y.Zt i) := ⟨hKnorm⟩
    have hcommC : ∀ x ∈ Y.Zt i, ∀ y ∈ Y.Zt i, x * y = y * x :=
      fun x hx y hy => hcommH x (Zt_le_Z Y i hx) y (Zt_le_Z Y i hy)
    exact (eq_commutator_of_inf_centralizer_eq_bot (W := Y.Zt i) (R := Y.K)
      (hH2.to_le (Zt_le_Z Y i)) hcommC hKodd hdisj).symm
  exact ⟨hsup, hdisj, hthird⟩

theorem even_of_ZtExt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {i : ℤ} {l r : ℕ}
    (he : Y.ZtExt i l r) : Even (i - (l : ℤ)) ∧ Even (i + (r : ℤ)) := by
  have hZt2 : IsPGroup 2 ↥(Y.Zt i) := Y.isPGroup_Zt i
  have hZtK : ⁅Y.Zt i, Y.K⁆ = Y.Zt i := (Zt_eq Y H i).2.2
  have hReven : Even (i + (r : ℤ)) := by
    rcases Int.even_or_odd (i + (r : ℤ)) with hev | hodd
    · exact hev
    · exfalso
      have hle : Y.Zt i ≤ Y.Gi (i + (r : ℤ)) := by
        simpa using he.1 (r : ℤ) (by omega) le_rfl
      have hZQ : Y.Zt i ≤ Y.Q (i + (r : ℤ)) :=
        hZtK ▸ comm_K_le_Q_of_odd Y H hodd hle hZt2
      have hcon : ¬ Y.Zt i ≤ Y.Gi (i + (r : ℤ) + 1) := by
        simpa using he.2.1
      exact hcon (hZQ.trans (by
        intro q hq
        exact MulAction.mem_stabilizer_iff.mpr
          (Y.Q_fixes_neighbors_vert (i + (r : ℤ)) (Y.vert (i + (r : ℤ) + 1))
            (Y.adj (i + (r : ℤ))) q hq)))
  have hLeven : Even (i - (l : ℤ)) := by
    rcases Int.even_or_odd (i - (l : ℤ)) with hev | hodd
    · exact hev
    · exfalso
      have hle : Y.Zt i ≤ Y.Gi (i - (l : ℤ)) := by
        simpa [sub_eq_add_neg] using he.1 (-(l : ℤ)) (by omega) (by omega)
      have hZQ : Y.Zt i ≤ Y.Q (i - (l : ℤ)) :=
        hZtK ▸ comm_K_le_Q_of_odd Y H hodd hle hZt2
      have hcon : ¬ Y.Zt i ≤ Y.Gi (i - (l : ℤ) - 1) := by
        simpa using he.2.2
      exact hcon (hZQ.trans (((Y.Q_le_Gi_adj (i - (l : ℤ))).trans inf_le_left)))
  exact ⟨hLeven, hReven⟩

private theorem map_conj_le_centralizer_Zt (Y : Setup Γ G) {b : ℤ} {U : Subgroup G}
    (hU : U ≤ Subgroup.centralizer (Y.Zt b : Set G)) {y : G}
    (hy : y ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.L b) :
    U.map (MulAut.conj y).toMonoidHom ≤ Subgroup.centralizer (Y.Zt b : Set G) := by
  obtain ⟨hyN, hyL⟩ := Subgroup.mem_inf.mp hy
  have hyGb : y ∈ Y.Gi b := Y.L_le_Gi b hyL
  have hZb_conj : (Y.Z b).map (MulAut.conj y).toMonoidHom = Y.Z b := by
    have h := Y.Z_normal b y hyGb
    simpa [conjSub] using h
  have hK_conj : (Y.K).map (MulAut.conj y).toMonoidHom = Y.K := by
    have h := (Subgroup.mem_normalizer_iff_map_conj_eq (H := Y.K) (g := y)).mp hyN
    simpa [conjSub] using h
  have hZtb_conj : (Y.Zt b).map (MulAut.conj y).toMonoidHom = Y.Zt b := by
    rw [Setup.Zt, Subgroup.map_commutator, hZb_conj, hK_conj]
  rw [Subgroup.map_le_iff_le_comap]
  intro w hw
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro z hz
  have hzy : y⁻¹ * z * y ∈ Y.Zt b := by
    have hmem : z ∈ (Y.Zt b).map (MulAut.conj y).toMonoidHom := by
      rw [hZtb_conj]
      exact hz
    rw [Subgroup.mem_map] at hmem
    obtain ⟨u, hu, huz⟩ := hmem
    have huz' : u = y⁻¹ * z * y := by
      rw [← huz]
      show u = y⁻¹ * (y * u * y⁻¹) * y
      group
    rw [← huz']
    exact hu
  have hcomm := Subgroup.mem_centralizer_iff.mp (hU hw) (y⁻¹ * z * y) hzy
  calc z * ((MulAut.conj y) w : G) = y * ((y⁻¹ * z * y) * w) * y⁻¹ := by
        show z * (y * w * y⁻¹) = y * ((y⁻¹ * z * y) * w) * y⁻¹
        group
    _ = y * (w * (y⁻¹ * z * y)) * y⁻¹ := by rw [← hcomm]
    _ = ((MulAut.conj y) w : G) * z := by
        show y * (w * (y⁻¹ * z * y)) * y⁻¹ = y * w * y⁻¹ * z
        group

private theorem Zt_eq_bot_of_L_le_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {b : ℤ} (hb : Even b) (hL : Y.L b ≤ Subgroup.centralizer (Y.Zt b : Set G)) :
    Y.Zt b = ⊥ := by
  have hKLeLb : Y.K ≤ Y.L b := K_le_L_of_even Y H hb
  have hZtbK : ⁅Y.Zt b, Y.K⁆ = Y.Zt b := (Zt_eq Y H b).2.2
  have hZtC : Y.Zt b ≤ Subgroup.centralizer (Y.L b : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hL hy) x hx).symm
  have hcommL : ⁅Y.Zt b, Y.L b⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZtC
  have hmono : ⁅Y.Zt b, Y.K⁆ ≤ ⁅Y.Zt b, Y.L b⁆ :=
    Subgroup.commutator_mono le_rfl hKLeLb
  have hbot : ⁅Y.Zt b, Y.K⁆ = ⊥ := by
    rw [hcommL] at hmono
    exact le_bot_iff.mp hmono
  rw [← hZtbK]
  exact hbot

private theorem Zt_le_Gi_of_ZtExt (Y : Setup Γ G) {l r : ℕ} (he : Y.ZtExt 0 l r)
    {m j : ℤ} (hm : Even m) (h1 : -(l : ℤ) ≤ j - m) (h2 : j - m ≤ (r : ℤ)) :
    Y.Zt m ≤ Y.Gi j := by
  rw [Zt_le_Gi_iff Y hm]
  simpa using he.1 (j - m) h1 h2

private theorem not_Zt_le_Gi_of_ZtExt (Y : Setup Γ G) {l r : ℕ} (he : Y.ZtExt 0 l r)
    {m j : ℤ} (hm : Even m) (h : j - m = (r : ℤ) + 1) : ¬ Y.Zt m ≤ Y.Gi j := by
  intro hle
  rw [Zt_le_Gi_iff Y hm] at hle
  rw [h] at hle
  have hle' : Y.Zt 0 ≤ Y.Gi (0 + (r : ℤ) + 1) := by simpa using hle
  exact he.2.1 hle'

private theorem not_Zt_le_Gi_of_ZtExt_left (Y : Setup Γ G) {l r : ℕ} (he : Y.ZtExt 0 l r)
    {m j : ℤ} (hm : Even m) (h : j - m = -(l : ℤ) - 1) : ¬ Y.Zt m ≤ Y.Gi j := by
  intro hle
  rw [Zt_le_Gi_iff Y hm] at hle
  rw [h] at hle
  have hle' : Y.Zt 0 ≤ Y.Gi (0 - (l : ℤ) - 1) := by simpa using hle
  exact he.2.2 hle'

private theorem not_lt_of_ZtExt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {l r : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 l r) : ¬ l < r := by
  obtain ⟨hLevenZ, hRevenZ⟩ := even_of_ZtExt Y H he
  have hLeven : Even l := by
    obtain ⟨c, hc⟩ := hLevenZ
    exact ⟨(-c).toNat, by omega⟩
  have hReven : Even r := by
    obtain ⟨c, hc⟩ := hRevenZ
    exact ⟨c.toNat, by omega⟩
  have hKH : ∀ i : ℤ, Y.K ≤ Subgroup.normalizer (Y.Z i : Set G) :=
    fun i => Y.K_le_normalizer_Z i
  have hZt_le_Z : ∀ i : ℤ, Y.Zt i ≤ Y.Z i := fun i => Zt_le_Z Y i
  have hZt2 : ∀ i : ℤ, IsPGroup 2 ↥(Y.Zt i) := fun i => Y.isPGroup_Zt i
  have hQle : Y.Zt 0 ≤ Y.Q 0 := (hZt_le_Z 0).trans (Y.Z_le_Q 0)
  have hle1 : Y.Zt 0 ≤ Y.Gi 1 := hQle.trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_right) hq)
  have hlem1 : Y.Zt 0 ≤ Y.Gi (-1) := hQle.trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_left) hq)
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · exfalso
      apply he.2.2
      rw [h]
      simpa using hlem1
    · exact h
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      apply he.2.1
      rw [h]
      simpa using hle1
    · exact h
  intro hlt
  set b : ℕ := r - l with hbdef
  have hbcast : (b : ℤ) = (r : ℤ) - (l : ℤ) := by
    rw [hbdef]
    exact Nat.cast_sub hlt.le
  have hbEvenNat : Even b := by
    obtain ⟨a, ha⟩ := hReven
    obtain ⟨c, hc⟩ := hLeven
    rw [hbdef]
    exact ⟨a - c, by omega⟩
  have hbEvenZ : Even (b : ℤ) := by
    obtain ⟨d, hd⟩ := hbEvenNat
    exact ⟨(d : ℤ), by rw [hd]; push_cast; ring⟩
  have hREvenZ : Even (r : ℤ) := by
    obtain ⟨d, hd⟩ := hReven
    exact ⟨(d : ℤ), by rw [hd]; push_cast; ring⟩
  have hZr_fix_b : Y.Zt (r : ℤ) ≤ Y.Gi (b : ℤ) :=
    Zt_le_Gi_of_ZtExt Y he hREvenZ (by omega) (by omega)
  have hZr_fix_b1 : Y.Zt (r : ℤ) ≤ Y.Gi ((b : ℤ) + 1) :=
    Zt_le_Gi_of_ZtExt Y he hREvenZ (by omega) (by omega)
  have hZr_not_bm1 : ¬ Y.Zt (r : ℤ) ≤ Y.Gi ((b : ℤ) - 1) :=
    not_Zt_le_Gi_of_ZtExt_left Y he hREvenZ (by rw [hbcast]; ring)
  have hZr_not_Qb : ¬ Y.Zt (r : ℤ) ≤ Y.Q (b : ℤ) := by
    intro hQ
    apply hZr_not_bm1
    refine hQ.trans ?_
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj (b : ℤ)).trans inf_le_left) hq
  have hZb_fix_r : Y.Zt (b : ℤ) ≤ Y.Gi (r : ℤ) :=
    Zt_le_Gi_of_ZtExt Y he hbEvenZ (by omega) (by omega)
  have hZb_fix_rm1 : Y.Zt (b : ℤ) ≤ Y.Gi ((r : ℤ) - 1) :=
    Zt_le_Gi_of_ZtExt Y he hbEvenZ (by omega) (by omega)
  have hZb_fix_rp1 : Y.Zt (b : ℤ) ≤ Y.Gi ((r : ℤ) + 1) :=
    Zt_le_Gi_of_ZtExt Y he hbEvenZ (by omega) (by omega)
  have hZbQ : Y.Zt (b : ℤ) ≤ Y.Q (r : ℤ) := by
    have hne : Y.vert ((r : ℤ) - 1) ≠ Y.vert ((r : ℤ) + 1) := by
      intro h
      have := Y.vert_injective h
      omega
    exact le_pCoreOf_of_isPGroup_fixes_two Y.hyp (hZt2 (b : ℤ)) hZb_fix_r
      (by
        have h := (Y.adj ((r : ℤ) - 1)).symm
        rwa [show (r : ℤ) - 1 + 1 = (r : ℤ) by ring] at h)
      (Y.adj (r : ℤ)) hne
      (fun y hy => MulAction.mem_stabilizer_iff.mp (hZb_fix_rm1 hy))
      (fun y hy => MulAction.mem_stabilizer_iff.mp (hZb_fix_rp1 hy))
  have hcent : Y.Zt (r : ℤ) ≤ Subgroup.centralizer (Y.Zt (b : ℤ) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxZ : x ∈ Y.Z (r : ℤ) := hZt_le_Z (r : ℤ) hx
    have hxcen : x ∈ Subgroup.centralizer (Y.Q (r : ℤ) : Set G) := (Y.Z_le_center (r : ℤ) hxZ).2
    have hyQ : y ∈ Y.Q (r : ℤ) := hZbQ hy
    exact Subgroup.mem_centralizer_iff.mp hxcen y hyQ
  have hKU : Y.K ≤ Subgroup.normalizer (Y.Zt (r : ℤ) : Set G) :=
    Y.K_le_normalizer_Zt (r : ℤ)
  have hGL2 := (gen_of_K_invariant Y H hbEvenZ (hZt2 (r : ℤ)) hZr_fix_b hKU hZr_not_Qb
    hZr_fix_b1).2
  have hQbW : Y.Q (b : ℤ) ≤ Subgroup.centralizer (Y.Zt (b : ℤ) : Set G) :=
    Q_le_centralizer_Zt Y (b : ℤ)
  have hconjW : ∀ y ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.L (b : ℤ),
      (Y.Zt (r : ℤ)).map (MulAut.conj y).toMonoidHom ≤
        Subgroup.centralizer (Y.Zt (b : ℤ) : Set G) := by
    intro y hy
    exact map_conj_le_centralizer_Zt Y hcent hy
  have hLbW : Y.L (b : ℤ) ≤ Subgroup.centralizer (Y.Zt (b : ℤ) : Set G) :=
    hGL2 _ hQbW hconjW
  have hZtbot : Y.Zt (b : ℤ) = ⊥ :=
    Zt_eq_bot_of_L_le_centralizer Y H hbEvenZ hLbW
  exact Zt_ne_bot_of_even Y hbEvenZ hZ hZtbot

theorem s52_step1 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {l r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 l r₀) : l = r₀ ∧ Even r₀ := by
  have hrevHe : Y.reverse.ZtExt 0 r₀ l := he.reverse
  have hZrev : Y.reverse.Zt 0 ≠ ⊥ := by
    rw [Setup.reverse_Zt]
    simpa using hZ
  have hA := not_lt_of_ZtExt Y H hZ he
  have hB := not_lt_of_ZtExt Y.reverse H.reverse hZrev hrevHe
  have hEven : Even r₀ := by
    obtain ⟨c, hc⟩ := (even_of_ZtExt Y H he).2
    exact ⟨c.toNat, by omega⟩
  exact ⟨by omega, hEven⟩

@[expose] def Step2Conclusion (Y : Setup Γ G) (s : ℕ) (r r₀ : ℕ) : Prop :=
  2 * r₀ = r ∨
    (2 * r₀ + 2 = r ∧
      ¬ (Y.LeftTransAt 1 ((1 : ℤ) + (r : ℤ)) ∧
        Y.RightTransAt 1 ((1 : ℤ) + (r : ℤ))) ∧ s < r) ∨
    (r = 6 ∧ s = 7 ∧ r₀ = 2 ∧ Y.HasB 0 2 ∧
      Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6 ∧
      Y.LeftTransAt 1 7 ∧ Y.RightTransAt 1 7)

private theorem even_r_of_isMaxRegLen (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r : ℕ}
    (hr : Y.IsMaxRegLen r) : Even r := by
  rcases Nat.lt_or_ge r (s - 1) with hlt | hge
  · exfalso
    have hr1s : r + 1 < s := by omega
    obtain ⟨a, hL, hR⟩ := hr.1
    have hreg : Regular Γ G (Y.line.arc a (r + 1)) :=
      H.sing.2.1 (r + 1) (by omega) hr1s (Y.line.arc a (r + 1))
    have hRr : Y.RightTransAt a (a + ((r + 1 : ℕ) : ℤ)) :=
      (Y.rightTransitive_arc_iff a (by omega)).mp hreg.2
    have hne := Y.arcStab_ne_GT_of_rightTransAt (by omega : a < a + ((r + 1 : ℕ) : ℤ)) hRr
    have hGT : Y.arcStab a (a + ((r + 1 : ℕ) : ℤ)) = Y.GT := hr.2 a (r + 1) (by omega)
    exact hne hGT
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    ·
      obtain ⟨k, hk⟩ := H.odd_s
      rw [← heq]
      exact ⟨k, by omega⟩
    ·
      obtain ⟨o, -, hpar⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
        (fun v a b ha hb => Y.hyp.locTrans ha hb) Y.hyp.edgeTrans Y.hyp.preservesParts
        H.sing H.odd_s
      obtain ⟨a, hL, hR⟩ := hr.1
      have hrs : s ≤ r := by omega
      have hreg : Regular Γ G (Y.line.arc a r) :=
        ⟨(Y.leftTransitive_arc_iff a r).mpr hL,
          (Y.rightTransitive_arc_iff a (by omega)).mpr hR⟩
      obtain ⟨he1, he2⟩ := hpar r hrs (Y.line.arc a r) hreg
      have hd : Γ.dist (Y.vert a) (Y.vert (a + (r : ℤ))) = r := by
        have h := Line.dist_eq Y.hyp.isTree Y.line (i := a) (j := a + (r : ℤ)) (by omega)
        have h' : ((a + (r : ℤ)) - a).toNat = r := by
          rw [show a + (r : ℤ) - a = (r : ℤ) by ring, Int.toNat_natCast]
        simpa only [h', mul_one] using h
      have he1' : Even (Γ.dist o (Y.vert a)) := by
        rwa [Line.arc_vert_zero] at he1
      have he2' : Even (Γ.dist o (Y.vert (a + (r : ℤ)))) := by
        have hlast := Line.arc_vert_last Y.line (a := a) (b := a + (r : ℤ)) (by omega)
        have hcast : ((a + (r : ℤ)) - a).toNat = r := by
          rw [show a + (r : ℤ) - a = (r : ℤ) by ring, Int.toNat_natCast]
        rw [hcast] at hlast
        rwa [hlast] at he2
      have hdvd1 : 2 ∣ Γ.dist o (Y.vert a) := even_iff_two_dvd.mp he1'
      have hdvd2 : 2 ∣ Γ.dist o (Y.vert (a + (r : ℤ))) := even_iff_two_dvd.mp he2'
      have hsum : 2 ∣ Γ.dist o (Y.vert a) + Γ.dist o (Y.vert (a + (r : ℤ))) +
          Γ.dist (Y.vert a) (Y.vert (a + (r : ℤ))) := by
        rw [show Γ.dist o (Y.vert a) + Γ.dist o (Y.vert (a + (r : ℤ))) +
            Γ.dist (Y.vert a) (Y.vert (a + (r : ℤ))) =
          Γ.dist o (Y.vert a) + Γ.dist (Y.vert a) (Y.vert (a + (r : ℤ))) +
            Γ.dist o (Y.vert (a + (r : ℤ))) from by ring]
        exact even_iff_two_dvd.mp
          (IsTree.even_dist_add_dist_add_dist Y.hyp.isTree o (Y.vert a) (Y.vert (a + (r : ℤ))))
      rw [hd] at hsum
      have h12 : 2 ∣ Γ.dist o (Y.vert a) + Γ.dist o (Y.vert (a + (r : ℤ))) :=
        Nat.dvd_add hdvd1 hdvd2
      have hdiff := Nat.dvd_sub hsum h12
      rw [show Γ.dist o (Y.vert a) + Γ.dist o (Y.vert (a + (r : ℤ))) + r -
          (Γ.dist o (Y.vert a) + Γ.dist o (Y.vert (a + (r : ℤ)))) = r from by omega] at hdiff
      exact even_iff_two_dvd.mpr hdiff

private theorem two_mul_le_of_ZtExt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀) : 2 * r₀ ≤ r := by
  by_contra hcon
  push Not at hcon
  have harc : Y.arcStab (-(r₀ : ℤ)) (r₀ : ℤ) = Y.GT := by
    have h := hr.2 (-(r₀ : ℤ)) (2 * r₀) (by omega)
    have hidx : -(r₀ : ℤ) + ((2 * r₀ : ℕ) : ℤ) = (r₀ : ℤ) := by push_cast; ring
    simpa only [hidx] using h
  have hZI : Y.Zt 0 ≤ Y.arcStab (-(r₀ : ℤ)) (r₀ : ℤ) := by
    rw [Y.arcStab_eq_inf (by omega)]
    exact le_inf (by simpa using he.1 (-(r₀ : ℤ)) le_rfl (by omega))
      (by simpa using he.1 (r₀ : ℤ) (by omega) le_rfl)
  have hZGT : Y.Zt 0 ≤ Y.GT := harc ▸ hZI
  have hZt_le_Z : Y.Zt 0 ≤ Y.Z 0 := Zt_le_Z Y 0
  have hZt2 : IsPGroup 2 ↥(Y.Zt 0) := Y.isPGroup_Zt 0
  have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.GT) (B := Y.Zt 0) H.odd_GT hZt2
  rw [inf_eq_right.mpr hZGT] at hbot
  exact hZ hbot

theorem regular_at_zero_or_one (Y : Setup Γ G) {r : ℕ} (hr : Y.IsMaxRegLen r) :
    (Y.LeftTransAt 0 (r : ℤ) ∧ Y.RightTransAt 0 (r : ℤ)) ∨
      (Y.LeftTransAt 1 (1 + (r : ℤ)) ∧ Y.RightTransAt 1 (1 + (r : ℤ))) := by
  obtain ⟨a, hL, hR⟩ := hr.1
  rcases Int.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have hL' := Y.leftTransAt_add (-k) a (a + (r : ℤ)) hL
    have hR' := Y.rightTransAt_add (-k) a (a + (r : ℤ)) hR
    have ha : a + 2 * (-k) = 0 := by rw [hk]; ring
    have hr' : a + (r : ℤ) + 2 * (-k) = (r : ℤ) := by rw [hk]; ring
    rw [ha, hr'] at hL' hR'
    exact ⟨hL', hR'⟩
  · right
    have hL' := Y.leftTransAt_add (-k) a (a + (r : ℤ)) hL
    have hR' := Y.rightTransAt_add (-k) a (a + (r : ℤ)) hR
    have ha : a + 2 * (-k) = 1 := by rw [hk]; ring
    have hr' : a + (r : ℤ) + 2 * (-k) = 1 + (r : ℤ) := by rw [hk]; ring
    rw [ha, hr'] at hL' hR'
    exact ⟨hL', hR'⟩

private theorem relIndex_sup_left_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    [Finite ↥H] [Finite ↥K] [Finite ↥(H ⊔ K)] [Finite ↥(H ⊓ K)]
    (hH : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = H.relIndex K := by
  have hN : K.relIndex (H ⊔ K) = K.relIndex H :=
    F1.relIndex_sup_eq_of_le_normalizer hH
  set a : ℕ := H.relIndex (H ⊔ K) with ha
  set b : ℕ := K.relIndex (H ⊔ K) with hb
  set c : ℕ := H.relIndex K with hc
  set nC : ℕ := Nat.card ↥H with hnC
  set nK : ℕ := Nat.card ↥K with hnK
  set nI : ℕ := Nat.card ↥(H ⊓ K) with hnI
  set nS : ℕ := Nat.card ↥(H ⊔ K) with hnS
  have E1 : a * nC = nS := by
    have h := Subgroup.relIndex_mul_card (H := H) (K := H ⊔ K)
    rw [inf_eq_left.mpr le_sup_left] at h
    simpa [a, nC, nS] using h
  have E2 : b * nK = nS := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
    rw [inf_eq_left.mpr le_sup_right] at h
    simpa [b, nK, nS] using h
  have E3 : b * nI = nC := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [inf_comm] at h
    simpa [b, nI, nC, hN] using h
  have E4 : c * nI = nK := by
    simpa [c, nI, nK] using Subgroup.relIndex_mul_card (H := H) (K := K)
  have hbpos : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    rw [hb0, zero_mul] at E3
    exact (Nat.card_pos (α := ↥H)).ne' E3.symm
  have hIpos : 0 < nI := by
    rw [hnI]
    exact Nat.card_pos
  have hEq : a * (b * nI) = c * (b * nI) := by
    calc a * (b * nI) = a * nC := by rw [E3]
      _ = nS := E1
      _ = b * nK := E2.symm
      _ = b * (c * nI) := by rw [E4]
      _ = c * (b * nI) := by ring
  have h := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hbpos hIpos) hEq
  simpa [a, c] using h

private theorem K_le_of_L_eq_sup_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {j : ℤ}
    (hj : Even j) {C : Subgroup G} (hCL : C ≤ Y.L j)
    (hKC : Y.K ≤ Subgroup.normalizer (C : Set G)) (hL : Y.L j = C ⊔ Y.Q j) :
    Y.K ≤ C := by
  have hKleL : Y.K ≤ Y.L j := K_le_L_of_even Y H hj
  have hQj2 : IsPGroup 2 ↥(Y.Q j) := pCoreOf_isPGroup' (Y.Gi j)
  have hQjL : Y.Q j ≤ Y.L j :=
    le_oTwoPrime_of_isPGroup hQj2 (Y.Q_le_Gi j)
  have hCK_le : C ⊔ Y.K ≤ Y.L j := sup_le hCL hKleL
  haveI hQjFin : Finite ↥(Y.Q j) := finite_of_le_stabilizer Y.hyp (H := Y.Q j) (Y.Q_le_Gi j)
  haveI hLjFin : Finite ↥(Y.L j) := finite_of_le_stabilizer Y.hyp (H := Y.L j) (Y.L_le_Gi j)
  haveI hCfin : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hCL) (Subgroup.inclusion_injective _)
  obtain ⟨nq, hnq⟩ := IsPGroup.iff_card.mp hQj2
  have hCNQ : C ≤ Subgroup.normalizer (Y.Q j : Set G) :=
    hCL.trans ((Y.L_le_Gi j).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)))
  have hCQ_le : C ⊔ Y.Q j ≤ Y.L j := by rw [hL]
  haveI hCQfin : Finite ↥(C ⊔ Y.Q j) :=
    Finite.of_injective (Subgroup.inclusion hCQ_le) (Subgroup.inclusion_injective _)
  haveI hCIfin : Finite ↥(C ⊓ Y.Q j) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hCrelL : C.relIndex (Y.L j) = (C ⊓ Y.Q j).relIndex (Y.Q j) := by
    rw [hL]
    rw [relIndex_sup_left_of_le_normalizer (H := C) (K := Y.Q j) hCNQ,
      Subgroup.inf_relIndex_right]
  have hCrelL_dvd : C.relIndex (Y.L j) ∣ Nat.card ↥(Y.Q j) := by
    rw [hCrelL]
    exact Subgroup.relIndex_dvd_card (H := C ⊓ Y.Q j) (K := Y.Q j)
  have hdvd : C.relIndex (C ⊔ Y.K) ∣ C.relIndex (Y.L j) :=
    ⟨(C ⊔ Y.K).relIndex (Y.L j),
      (Subgroup.relIndex_mul_relIndex (H := C) (K := C ⊔ Y.K) (L := Y.L j)
        le_sup_left hCK_le).symm⟩
  have hKodd : Odd (Nat.card ↥Y.K) := Y.odd_card_K
  have hodd : Odd (C.relIndex (C ⊔ Y.K)) := by
    have hKrel : C.relIndex (C ⊔ Y.K) = C.relIndex Y.K := by
      rw [sup_comm]
      exact F1.relIndex_sup_eq_of_le_normalizer hKC
    rw [hKrel]
    exact Odd.of_dvd_nat hKodd (Subgroup.relIndex_dvd_card (H := C) (K := Y.K))
  rw [hnq] at hCrelL_dvd
  obtain ⟨m, -, hm⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hCrelL_dvd
  rw [hm] at hdvd
  obtain ⟨k, -, hk⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    have hev : Even (C.relIndex (C ⊔ Y.K)) := even_iff_two_dvd.mpr (hk ▸ h2)
    exact (Nat.not_even_iff_odd.mpr hodd) hev
  have hrel1 : C.relIndex (C ⊔ Y.K) = 1 := by rw [hk, hk0, pow_zero]
  have hKCeq : C ⊔ Y.K = C := le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) le_sup_left
  have hKleC : Y.K ≤ C := by
    have h : Y.K ≤ C ⊔ Y.K := le_sup_right
    rwa [hKCeq] at h
  exact hKleC

private theorem K_le_centralizer_pCoreOf_arcStab (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) {a : ℤ} (ha : a = 0 ∨ a = 1)
    (hregL : Y.LeftTransAt a (a + (r : ℤ)))
    (hregR : Y.RightTransAt a (a + (r : ℤ)))
    (hupper : 2 * (r₀ : ℤ) + 3 ≤ a + (r : ℤ)) :
    Y.K ≤ Subgroup.centralizer (pCoreOf 2 (Y.arcStab a (a + (r : ℤ))) : Set G) ∧
      Y.L ((r₀ : ℤ) + 2) =
        (Subgroup.centralizer (pCoreOf 2 (Y.arcStab a (a + (r : ℤ))) : Set G) ⊓
          Y.L ((r₀ : ℤ) + 2)) ⊔ Y.Q ((r₀ : ℤ) + 2) := by
  set Q : Subgroup G := pCoreOf 2 (Y.arcStab a (a + (r : ℤ))) with hQdef
  have hQleArc : Q ≤ Y.arcStab a (a + (r : ℤ)) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hRpos : 1 ≤ r₀ := he.one_le.1
  have hRevenNat : Even r₀ := (s52_step1 Y H hZ he).2
  have hReven : Even (r₀ : ℤ) := by
    obtain ⟨k, hk⟩ := hRevenNat
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  let j : ℤ := (r₀ : ℤ) + 2
  have hjval : j = (r₀ : ℤ) + 2 := rfl
  have hje : Even j := by
    obtain ⟨k, hk⟩ := hReven
    exact ⟨k + 1, by show (r₀ : ℤ) + 2 = (k + 1) + (k + 1); omega⟩
  have h2even : Even (2 : ℤ) := by norm_num
  have hm2even : Even (2 * (r₀ : ℤ) + 2) := by
    obtain ⟨k, hk⟩ := hReven
    exact ⟨2 * k + 1, by show 2 * (r₀ : ℤ) + 2 = (2 * k + 1) + (2 * k + 1); omega⟩
  have hQ2 : Q ≤ Y.Q 2 := by
    rw [hQdef]
    exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := a) (c := a + (r : ℤ)) (by omega) (by omega)
  have hQ2r : Q ≤ Y.Q (2 * (r₀ : ℤ) + 2) := by
    rw [hQdef]
    exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := a) (c := a + (r : ℤ)) (by omega) (by omega)
  have hKQ : Y.K ≤ Subgroup.normalizer (Q : Set G) := by
    have h := (Y.K_le_GT.trans (Y.GT_le_arcStab a (a + (r : ℤ)))).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.arcStab a (a + (r : ℤ))))
    simpa [hQdef] using h
  have hU1le : Y.Zt 2 ≤ Y.Gi j :=
    Zt_le_Gi_of_ZtExt Y he h2even (by omega) (by omega)
  have hU1fixa : Y.Zt 2 ≤ Y.Gi (j - 1) :=
    Zt_le_Gi_of_ZtExt Y he h2even (by omega) (by omega)
  have hU1notb : ¬ Y.Zt 2 ≤ Y.Gi (j + 1) :=
    not_Zt_le_Gi_of_ZtExt Y he h2even (by rw [hjval]; ring)
  have hU2le : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Y.Gi j :=
    Zt_le_Gi_of_ZtExt Y he hm2even (by omega) (by omega)
  have hU2fixb : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Y.Gi (j + 1) :=
    Zt_le_Gi_of_ZtExt Y he hm2even (by omega) (by omega)
  have hU2nota : ¬ Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Y.Gi (j - 1) :=
    not_Zt_le_Gi_of_ZtExt_left Y he hm2even (by rw [hjval]; ring)
  have hU1isP : IsPGroup 2 ↥(Y.Zt 2) := Y.isPGroup_Zt 2
  have hU2isP : IsPGroup 2 ↥(Y.Zt (2 * (r₀ : ℤ) + 2)) := Y.isPGroup_Zt _
  have hU1L : Y.Zt 2 ≤ Y.L j := le_oTwoPrime_of_isPGroup hU1isP hU1le
  have hU2L : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Y.L j := le_oTwoPrime_of_isPGroup hU2isP hU2le
  have hKU1 : Y.K ≤ Subgroup.normalizer (Y.Zt 2 : Set G) := Y.K_le_normalizer_Zt 2
  have hKU2 : Y.K ≤ Subgroup.normalizer (Y.Zt (2 * (r₀ : ℤ) + 2) : Set G) :=
    Y.K_le_normalizer_Zt (2 * (r₀ : ℤ) + 2)
  have hQj_fixes_one : Y.Q j ≤ Y.Gi (j + 1) := by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj j).trans inf_le_right) hq
  have hQj_fixes_pred : Y.Q j ≤ Y.Gi (j - 1) := by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj j).trans inf_le_left) hq
  have hU1notQj : ¬ Y.Zt 2 ≤ Y.Q j := by
    intro h
    exact hU1notb (h.trans hQj_fixes_one)
  have hU2notQj : ¬ Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Y.Q j := by
    intro h
    exact hU2nota (h.trans hQj_fixes_pred)
  have hGL2 := gen_of_K_invariant Y H hje hU2isP hU2le hKU2 hU2notQj hU2fixb
  have hU2sup : Y.Zt (2 * (r₀ : ℤ) + 2) ⊔ Y.Q j = Y.edgeSylow j := by
    simpa [Setup.edgeSylow] using hGL2.1
  have hGL1 := gen_of_K_invariant Y.reverse H.reverse (j := -j) (U := Y.Zt 2)
    (by simpa using hje.neg) hU1isP
    (by simpa [Setup.reverse_Gi] using hU1le) hKU1
    (by simpa [Setup.reverse_Q] using hU1notQj)
    (by
      have h := hU1fixa
      simpa [Setup.reverse_Gi, show -(-j + 1) = j - 1 by ring] using h)
  have hU1sup' : Y.Zt 2 ⊔ Y.Q j = pCoreOf 2 (Y.Gi j ⊓ Y.Gi (j - 1)) := by
    have h := hGL1.1
    rw [Setup.reverse_Q, show -(-j) = j by ring, Setup.reverse_Gi, Setup.reverse_Gi,
      show -(-j + 1) = j - 1 by ring] at h
    exact h
  have hU1sup : Y.Zt 2 ⊔ Y.Q j = Y.edgeSylow (j - 1) := by
    show Y.Zt 2 ⊔ Y.Q j = pCoreOf 2 (Y.Gi (j - 1) ⊓ Y.Gi (j - 1 + 1))
    rw [show j - 1 + 1 = j by ring, inf_comm]
    exact hU1sup'
  have hQU1 : Q ≤ Subgroup.centralizer (Y.Zt 2 : Set G) :=
    hQ2.trans (Q_le_centralizer_Zt Y 2)
  have hQU2 : Q ≤ Subgroup.centralizer (Y.Zt (2 * (r₀ : ℤ) + 2) : Set G) :=
    hQ2r.trans (Q_le_centralizer_Zt Y _)
  have hU1C : Y.Zt 2 ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.mpr hQU1
  have hU2C : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.mpr hQU2
  have hU1NQ : Y.Zt 2 ≤ Subgroup.normalizer (Y.Q j : Set G) :=
    hU1L.trans ((Y.L_le_Gi j).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)))
  have hU2NQ : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ Subgroup.normalizer (Y.Q j : Set G) :=
    hU2L.trans ((Y.L_le_Gi j).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)))
  have hU1idx : (Y.Zt 2 ⊓ Y.Q j).relIndex (Y.Zt 2) = 2 ^ Y.n j := by
    rw [Subgroup.inf_relIndex_left]
    have h2 : (Y.Q j).relIndex (Y.Zt 2) = (Y.Q j).relIndex (Y.Zt 2 ⊔ Y.Q j) :=
      (F1.relIndex_sup_eq_of_le_normalizer hU1NQ).symm
    rw [h2, hU1sup]
    have h := Y.relIndex_Q_succ_edgeSylow (j - 1)
    rwa [show j - 1 + 1 = j by ring] at h
  have hU2idx : (Y.Zt (2 * (r₀ : ℤ) + 2) ⊓ Y.Q j).relIndex
      (Y.Zt (2 * (r₀ : ℤ) + 2)) = 2 ^ Y.n j := by
    rw [Subgroup.inf_relIndex_left]
    have h2 : (Y.Q j).relIndex (Y.Zt (2 * (r₀ : ℤ) + 2)) =
        (Y.Q j).relIndex (Y.Zt (2 * (r₀ : ℤ) + 2) ⊔ Y.Q j) :=
      (F1.relIndex_sup_eq_of_le_normalizer hU2NQ).symm
    rw [h2, hU2sup]
    exact Y.relIndex_Q_edgeSylow j
  have hLgen : Y.L j = Y.Zt 2 ⊔ Y.Zt (2 * (r₀ : ℤ) + 2) ⊔ Y.Q j :=
    L_eq_sup_of_fixes Y j (A := Y.Zt 2) (B := Y.Zt (2 * (r₀ : ℤ) + 2))
      (a := Y.vert (j - 1)) (b := Y.vert (j + 1))
      (by
        have h := (Y.adj (j - 1)).symm
        rwa [show j - 1 + 1 = j by ring] at h)
      (Y.adj j)
      (by
        intro h; have := Y.vert_injective h; omega)
      hU1L hU2L hU1fixa hU2fixb hU1idx hU2idx
  let C : Subgroup G := Subgroup.centralizer (Q : Set G) ⊓ Y.L j
  have hU1C' : Y.Zt 2 ≤ C := le_inf hU1C hU1L
  have hU2C' : Y.Zt (2 * (r₀ : ℤ) + 2) ≤ C := le_inf hU2C hU2L
  have hQj2 : IsPGroup 2 ↥(Y.Q j) := pCoreOf_isPGroup' (Y.Gi j)
  have hQjL : Y.Q j ≤ Y.L j :=
    le_oTwoPrime_of_isPGroup hQj2 (Y.Q_le_Gi j)
  have hLsupC : Y.L j = C ⊔ Y.Q j := by
    refine le_antisymm ?_ (sup_le inf_le_right hQjL)
    rw [hLgen]
    exact sup_le ((sup_le hU1C' hU2C').trans le_sup_left) le_sup_right
  have hKnormC : Y.K ≤ Subgroup.normalizer (C : Set G) := by
    have hKcen : Y.K ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change conjSub k (Subgroup.centralizer (Q : Set G)) = Subgroup.centralizer (Q : Set G)
      have hkQ : conjSub k Q = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKQ hk)
      rw [← conjSub_centralizer k Q, hkQ]
    have hKL : Y.K ≤ Subgroup.normalizer (Y.L j : Set G) :=
      (Y.K_le_Gi j).trans (le_normalizer_oTwoPrime (Y.Gi j))
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : conjSub k (Subgroup.centralizer (Q : Set G)) = Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKcen hk)
    have h2 : conjSub k (Y.L j) = Y.L j :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKL hk)
    change conjSub k (Subgroup.centralizer (Q : Set G) ⊓ Y.L j) =
      Subgroup.centralizer (Q : Set G) ⊓ Y.L j
    rw [conjSub_inf, h1, h2]
  have hKleC : Y.K ≤ C := K_le_of_L_eq_sup_Q Y H hje inf_le_right hKnormC hLsupC
  refine ⟨hKleC.trans inf_le_left, ?_⟩
  simpa [hQdef, j] using hLsupC

private theorem not_regular_zero_of_small (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hre : Even (r : ℤ))
    (hregL : Y.LeftTransAt 0 (r : ℤ)) (hregR : Y.RightTransAt 0 (r : ℤ))
    (hr : 2 * r₀ + 3 ≤ r) : False := by
  have hr3 : 3 ≤ r := by omega
  have hr0 : (0 : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : 0 < r)
  set Q : Subgroup G := pCoreOf 2 (Y.arcStab 0 (r : ℤ)) with hQdef
  have hQleArc : Q ≤ Y.arcStab 0 (r : ℤ) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hKQ : Y.K ≤ Subgroup.centralizer (Q : Set G) := by
    have h := (K_le_centralizer_pCoreOf_arcStab Y H hZ he (a := 0) (Or.inl rfl)
      (by simpa using hregL) (by simpa using hregR)
      (by simpa using (show (2 * (r₀ : ℤ) + 3 ≤ (r : ℤ)) by exact_mod_cast hr))).1
    simpa [hQdef] using h
  have hQK : Q ≤ Subgroup.centralizer (Y.K : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKQ hk) q hq).symm
  have hKA : Y.K ≤ Y.arcStab 0 (r : ℤ) :=
    Y.K_le_GT.trans (Y.GT_le_arcStab 0 (r : ℤ))
  have hA : Y.arcStab 0 (r : ℤ) ≤ Y.Gi 0 ⊓ Y.Gi 1 :=
    le_inf (Y.arcStab_le_Gi_left hr0) (Y.arcStab_le_Gi_left_succ hr0)
  have hsupQ : Y.K ⊔ Q = Y.arcStab 0 (r : ℤ) := by
    have h := (Y.pCoreOf_eq_inf_edgeSylow 0 hKA hA).2
    simpa [hQdef] using h
  have hnr : 2 ≤ Y.n (r : ℤ) := by
    obtain ⟨m, hm⟩ := hre
    rw [show (r : ℤ) = 0 + 2 * m by omega, Y.n_add, H.n_zero]
    exact H.two_le
  obtain ⟨kK, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Y.torus_ne_bot (r : ℤ) hnr)
  let k : G := kK
  have hkKi' : k ∈ Y.Ki (r : ℤ) := kK.2
  have hk : k ∈ Y.K := hkKi'.1
  have hk1' : k ≠ 1 := by
    intro h
    exact hk1 (Subtype.ext h)
  have hQfix : ∀ q ∈ Q, q • Y.vert ((r : ℤ) + 1) = Y.vert ((r : ℤ) + 1) := by
    intro q hq
    have hqGr : q ∈ Y.Gi (r : ℤ) := hQleArc.trans (Y.arcStab_le_Gi_right hr0) hq
    have hqGrm1 : q ∈ Y.Gi ((r : ℤ) - 1) :=
      hQleArc.trans (Y.arcStab_le_Gi_right_pred hr0) hq
    have hqpred : q • Y.vert ((r : ℤ) - 1) = Y.vert ((r : ℤ) - 1) :=
      MulAction.mem_stabilizer_iff.mp hqGrm1
    have hqinvGr : q⁻¹ ∈ Y.Gi (r : ℤ) := (Y.Gi (r : ℤ)).inv_mem hqGr
    have hadj : Γ.Adj (Y.vert (r : ℤ)) (q⁻¹ • Y.vert ((r : ℤ) + 1)) := by
      have h1 : Γ.Adj (q⁻¹ • Y.vert (r : ℤ)) (q⁻¹ • Y.vert ((r : ℤ) + 1)) :=
        (Y.hyp.adj_smul q⁻¹ _ _).mpr (Y.adj (r : ℤ))
      rwa [MulAction.mem_stabilizer_iff.mp hqinvGr] at h1
    have hcomm : k * q⁻¹ = q⁻¹ * k := by
      have hqk : q * k = k * q := (Subgroup.mem_centralizer_iff.mp (hQK hq) k hk).symm
      calc k * q⁻¹ = q⁻¹ * (q * k) * q⁻¹ := by group
        _ = q⁻¹ * (k * q) * q⁻¹ := by rw [hqk]
        _ = q⁻¹ * k := by group
    have hkfixv : k • Y.vert ((r : ℤ) + 1) = Y.vert ((r : ℤ) + 1) :=
      ((Y.torus_fixed (r : ℤ) hnr hkKi' hk1' (Y.vert ((r : ℤ) + 1))
        (Y.adj (r : ℤ))).mpr (Or.inr rfl))
    have hkfix : k • (q⁻¹ • Y.vert ((r : ℤ) + 1)) = q⁻¹ • Y.vert ((r : ℤ) + 1) := by
      calc k • (q⁻¹ • Y.vert ((r : ℤ) + 1)) = (k * q⁻¹) • Y.vert ((r : ℤ) + 1) :=
            (mul_smul k q⁻¹ _).symm
        _ = (q⁻¹ * k) • Y.vert ((r : ℤ) + 1) := by rw [hcomm]
        _ = q⁻¹ • (k • Y.vert ((r : ℤ) + 1)) := mul_smul q⁻¹ k _
        _ = q⁻¹ • Y.vert ((r : ℤ) + 1) := by rw [hkfixv]
    have hcases := (Y.torus_fixed (r : ℤ) hnr hkKi' hk1'
      (q⁻¹ • Y.vert ((r : ℤ) + 1)) hadj).mp hkfix
    rcases hcases with hcase | hcase
    · have hv : Y.vert ((r : ℤ) + 1) = Y.vert ((r : ℤ) - 1) := by
        have := congrArg (fun x => q • x) hcase
        simpa [hqpred] using this
      exact absurd hv (by intro h; have := Y.vert_injective h; omega)
    · have := congrArg (fun x => q • x) hcase
      simpa using this.symm
  have harcfix : Y.arcStab 0 (r : ℤ) ≤ Y.Gi ((r : ℤ) + 1) := by
    rw [← hsupQ]
    exact sup_le (Y.K_le_Gi ((r : ℤ) + 1)) (fun q hq => hQfix q hq)
  obtain ⟨c, hcadj, hcne1, hcne2⟩ := exists_adj_ne_ne (v := Y.vert (r : ℤ))
    (a := Y.vert ((r : ℤ) - 1)) (b := Y.vert ((r : ℤ) + 1))
    (Y.hyp.three_le_card (Y.vert (r : ℤ)))
  obtain ⟨g, hg, hgmap⟩ := hregR (Y.vert ((r : ℤ) + 1)) c (Y.adj (r : ℤ))
    (by intro h; have := Y.vert_injective h; omega) hcadj hcne1
  have hgfix : g • Y.vert ((r : ℤ) + 1) = Y.vert ((r : ℤ) + 1) :=
    MulAction.mem_stabilizer_iff.mp (harcfix hg)
  exact hcne2 (by rw [← hgmap, hgfix])

private theorem le_eight_of_regular_arc (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hre : Even r)
    (hregL : Y.LeftTransAt 1 (1 + (r : ℤ))) (hregR : Y.RightTransAt 1 (1 + (r : ℤ)))
    (h2r : 2 * r₀ + 2 ≤ r) : r ≤ 8 := by
  obtain ⟨m, hm⟩ := hre
  have h2m : 2 * m = r := by omega
  have hupper : 2 * (r₀ : ℤ) + 3 ≤ 1 + (r : ℤ) := by
    have h := (show (2 * (r₀ : ℤ) + 2 ≤ (r : ℤ)) by exact_mod_cast h2r)
    omega
  have hKQ := (K_le_centralizer_pCoreOf_arcStab Y H hZ he (a := 1) (Or.inr rfl)
    hregL hregR hupper).1
  have hc : pCoreOf 2 (Y.arcStab 1 (1 + (r : ℤ))) ≤
      Subgroup.centralizer (Y.K : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKQ hk) q hq).symm
  have hrm : ((2 * m : ℕ) : ℤ) = (r : ℤ) := by exact_mod_cast h2m
  have hreg : Y.RightTransAt 1 (1 + ((2 * m : ℕ) : ℤ)) := by
    rw [hrm]
    exact hregR
  have hc' : pCoreOf 2 (Y.arcStab 1 (1 + ((2 * m : ℕ) : ℤ))) ≤
      Subgroup.centralizer (Y.K : Set G) := by
    rw [hrm]
    exact hc
  have h8 := le_eight_of_regular Y H (a := 1) (by norm_num : Odd (1 : ℤ)) (m := m) hreg hc'
  omega


private theorem J_le_normalizer_Qs_add (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (m : ℤ) :
    Y.J (1 + 2 * m) ≤ Subgroup.normalizer (Y.Qs (1 + 2 * m) : Set G) := by
  rw [Y.J_add m 1, Y.Qs_add m 1]
  change conjSub (Y.τ ^ m) (Y.J 1) ≤
    Subgroup.normalizer (conjSub (Y.τ ^ m) (Y.Qs 1) : Set G)
  exact conjSub_le_normalizer (J_one_le_normalizer_Qs_one Y H)

private theorem eq_bot_of_normal_J_shift (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (m : ℤ)
    {X : Subgroup G} (h2 : IsPGroup 2 X)
    (hj1 : Y.J (-1 + 2 * m) ≤ Subgroup.normalizer (X : Set G))
    (hj2 : Y.J (1 + 2 * m) ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≤ Y.Gi (-1 + 2 * m) ⊓ Y.Gi (1 + 2 * m)) : X = ⊥ := by
  set X' : Subgroup G := conjSub (Y.τ ^ (-m : ℤ)) X with hX'def
  have hGi1 : conjSub (Y.τ ^ (-m : ℤ)) (Y.Gi (-1 + 2 * m)) = Y.Gi (-1) := by
    have h := Y.Gi_add m (-1)
    rw [h, ← conjSub_mul, show Y.τ ^ (-m : ℤ) * Y.τ ^ m = 1 by group, conjSub_one]
  have hGi2 : conjSub (Y.τ ^ (-m : ℤ)) (Y.Gi (1 + 2 * m)) = Y.Gi 1 := by
    have h := Y.Gi_add m 1
    rw [h, ← conjSub_mul, show Y.τ ^ (-m : ℤ) * Y.τ ^ m = 1 by group, conjSub_one]
  have hX' : X' ≤ Y.Gi (-1) ⊓ Y.Gi 1 := by
    have h := conjSub_mono (Y.τ ^ (-m : ℤ)) hX
    rwa [conjSub_inf, hGi1, hGi2] at h
  have hJ1 : Y.J 1 ≤ Subgroup.normalizer (X' : Set G) := by
    have hJ1' : conjSub (Y.τ ^ (-m : ℤ)) (Y.J (1 + 2 * m)) = Y.J 1 := by
      have h := Y.J_add m 1
      rw [h]
      change conjSub (Y.τ ^ (-m : ℤ)) (conjSub (Y.τ ^ m) (Y.J 1)) = Y.J 1
      rw [← conjSub_mul, show Y.τ ^ (-m : ℤ) * Y.τ ^ m = 1 by group, conjSub_one]
    have h := conjSub_le_normalizer (g := Y.τ ^ (-m : ℤ)) hj2
    rwa [hJ1'] at h
  have hJneg : Y.J (-1) ≤ Subgroup.normalizer (X' : Set G) := by
    have hJneg' : conjSub (Y.τ ^ (-m : ℤ)) (Y.J (-1 + 2 * m)) = Y.J (-1) := by
      have h := Y.J_add m (-1)
      rw [h]
      change conjSub (Y.τ ^ (-m : ℤ)) (conjSub (Y.τ ^ m) (Y.J (-1))) = Y.J (-1)
      rw [← conjSub_mul, show Y.τ ^ (-m : ℤ) * Y.τ ^ m = 1 by group, conjSub_one]
    have h := conjSub_le_normalizer (g := Y.τ ^ (-m : ℤ)) hj1
    rwa [hJneg'] at h
  have hx : X' = ⊥ := eq_bot_of_normal_J Y H
    (CFSG.Quasithin.F7.isPGroup_conjSub (g := Y.τ ^ (-m : ℤ)) h2) hJ1 hJneg hX'
  have hXeq : X = conjSub (Y.τ ^ m) X' := by
    rw [hX'def]
    rw [← conjSub_mul, show Y.τ ^ m * Y.τ ^ (-m : ℤ) = 1 by group, conjSub_one]
  rw [hXeq, hx]
  simp [conjSub]

private theorem eq_or_eq_or_eq_of_adj (Y : Setup Γ G) {v : ℤ} (hv : Y.n v = 1) {a b c p : V}
    (ha : Γ.Adj (Y.vert v) a) (hb : Γ.Adj (Y.vert v) b) (hc : Γ.Adj (Y.vert v) c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hp : Γ.Adj (Y.vert v) p) :
    p = a ∨ p = b ∨ p = c := by
  have hcard : (Γ.neighborSet (Y.vert v)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq, (Y.hyp.valency (Y.vert v)).2]
    change 2 ^ Y.n v + 1 = 3
    rw [hv]
    norm_num
  have hset : Γ.neighborSet (Y.vert v) = ({a, b, c} : Set V) := by
    have hthree : ({a, b, c} : Set V).ncard = 3 :=
      (Set.ncard_eq_three).mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro x hx
      rw [SimpleGraph.mem_neighborSet]
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    · rw [hcard]
      exact hthree.ge
    · exact Y.hyp.finite_neighborSet (Y.vert v)
  have hp' : p ∈ Γ.neighborSet (Y.vert v) := by simpa using hp
  rw [hset] at hp'
  simpa using hp'

private theorem trans_of_two_transpositions (Y : Setup Γ G) {v : ℤ} (hv : Y.n v = 1)
    {a b : V} (ha : Γ.Adj (Y.vert v) a) (hb : Γ.Adj (Y.vert v) b) (hab : a ≠ b)
    {L : Subgroup G} (hL : L ≤ Y.Gi v)
    {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx2 : ∃ m : ℕ, x ^ 2 ^ m = 1) (hy2 : ∃ m : ℕ, y ^ 2 ^ m = 1)
    (hxa : x • a = a) (hyb : y • b = b)
    (hxb : x • b ≠ b) (hya : y • a ≠ a)
    (hxQ : x ∉ Y.Q v) (hyQ : y ∉ Y.Q v) :
    ∀ p q : V, Γ.Adj (Y.vert v) p → Γ.Adj (Y.vert v) q → ∃ g ∈ L, g • p = q := by
  obtain ⟨c, hcadj, hca, hcb⟩ := exists_adj_ne_ne (v := Y.vert v) (a := a) (b := b)
    (Y.hyp.three_le_card (Y.vert v))
  have hmem : ∀ p : V, Γ.Adj (Y.vert v) p → p = a ∨ p = b ∨ p = c :=
    fun p hp => eq_or_eq_or_eq_of_adj Y hv ha hb hcadj hab hca.symm hcb.symm hp
  have hxfix : x • Y.vert v = Y.vert v := MulAction.mem_stabilizer_iff.mp (hL hxL)
  have hyfix : y • Y.vert v = Y.vert v := MulAction.mem_stabilizer_iff.mp (hL hyL)
  have hxbadj : Γ.Adj (Y.vert v) (x • b) := by
    have h := (Y.hyp.adj_smul x (Y.vert v) b).mpr hb
    rwa [hxfix] at h
  have hxbc : x • b = c := by
    rcases hmem (x • b) hxbadj with h | h | h
    · exfalso
      exact hab (MulAction.injective x (h.trans hxa.symm)).symm
    · exact absurd h hxb
    · exact h
  have hxc : x • c = b := by
    have hxca : Γ.Adj (Y.vert v) (x • c) := by
      have h := (Y.hyp.adj_smul x (Y.vert v) c).mpr hcadj
      rwa [hxfix] at h
    rcases hmem (x • c) hxca with h | h | h
    · exfalso
      exact hca (MulAction.injective x (h.trans hxa.symm))
    · exact h
    · exfalso
      exact hxQ (mem_pCoreOf_of_fixes_two Y.hyp (hL hxL) hx2 ha hcadj hca.symm hxa h)
  have hyaadj : Γ.Adj (Y.vert v) (y • a) := by
    have h := (Y.hyp.adj_smul y (Y.vert v) a).mpr ha
    rwa [hyfix] at h
  have hyac : y • a = c := by
    rcases hmem (y • a) hyaadj with h | h | h
    · exact absurd h hya
    · exfalso
      exact hab (MulAction.injective y (h.trans hyb.symm))
    · exact h
  have hyc : y • c = a := by
    have hyca : Γ.Adj (Y.vert v) (y • c) := by
      have h := (Y.hyp.adj_smul y (Y.vert v) c).mpr hcadj
      rwa [hyfix] at h
    rcases hmem (y • c) hyca with h | h | h
    · exact h
    · exfalso
      exact hcb (MulAction.injective y (h.trans hyb.symm))
    · exfalso
      exact hyQ (mem_pCoreOf_of_fixes_two Y.hyp (hL hyL) hy2 hb hcadj hcb.symm hyb h)
  intro p q hp hq
  rcases hmem p hp with hpa | hpb | hpc
  · rw [hpa]
    rcases hmem q hq with hqa | hqb | hqc
    · rw [hqa]; exact ⟨1, one_mem L, by simp⟩
    · rw [hqb]
      refine ⟨x * y, L.mul_mem hxL hyL, ?_⟩
      calc (x * y) • a = x • (y • a) := mul_smul x y a
        _ = x • c := by rw [hyac]
        _ = b := hxc
    · rw [hqc]; exact ⟨y, hyL, hyac⟩
  · rw [hpb]
    rcases hmem q hq with hqa | hqb | hqc
    · rw [hqa]
      refine ⟨y * x, L.mul_mem hyL hxL, ?_⟩
      calc (y * x) • b = y • (x • b) := mul_smul y x b
        _ = y • c := by rw [hxbc]
        _ = a := hyc
    · rw [hqb]; exact ⟨1, one_mem L, by simp⟩
    · rw [hqc]; exact ⟨x, hxL, hxbc⟩
  · rw [hpc]
    rcases hmem q hq with hqa | hqb | hqc
    · rw [hqa]; exact ⟨y, hyL, hyc⟩
    · rw [hqb]; exact ⟨x, hxL, hxc⟩
    · rw [hqc]; exact ⟨1, one_mem L, by simp⟩

private theorem pCoreOf_arcStab_one_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {b : ℤ}
    (hb : 1 < b) (hregL : Y.LeftTransAt 1 b) : pCoreOf 2 (Y.arcStab 1 b) ≠ ⊥ := by
  intro hbot
  have hKA : Y.K ≤ Y.arcStab 1 b := Y.K_le_GT.trans (Y.GT_le_arcStab 1 b)
  have hA : Y.arcStab 1 b ≤ Y.Gi 1 ⊓ Y.Gi 2 :=
    le_inf (Y.arcStab_le_Gi_left hb) (Y.arcStab_le_Gi_left_succ hb)
  have hsupQ : Y.K ⊔ pCoreOf 2 (Y.arcStab 1 b) = Y.arcStab 1 b :=
    (Y.pCoreOf_eq_inf_edgeSylow 1 hKA hA).2
  have harcK : Y.arcStab 1 b = Y.K := by rw [← hsupQ, hbot, sup_bot_eq]
  obtain ⟨c, hcadj, hcne0, hcne2⟩ := exists_adj_ne_ne (v := Y.vert 1)
    (a := Y.vert 0) (b := Y.vert 2) (Y.hyp.three_le_card (Y.vert 1))
  obtain ⟨g, hg, hgmap⟩ := hregL (Y.vert 0) c (by simpa using (Y.adj 0).symm)
    (by intro h; have := Y.vert_injective h; norm_num at this) hcadj hcne2
  have hgK : g ∈ Y.K := harcK ▸ hg
  have hfix : g • Y.vert 0 = Y.vert 0 := K_fixes_nbr_one Y H (Y.adj 0).symm g hgK
  exact hcne0 (by rw [← hgmap, hfix])

private theorem trans_normalizer_inf_Gi_of_L_eq (Y : Setup Γ G) {Q : Subgroup G} {j : ℤ}
    (hL : Y.L j = (Subgroup.centralizer (Q : Set G) ⊓ Y.L j) ⊔ Y.Q j) :
    ∀ a b : V, Γ.Adj (Y.vert j) a → Γ.Adj (Y.vert j) b →
      ∃ g ∈ Subgroup.normalizer (Q : Set G) ⊓ Y.Gi j, g • a = b := by
  intro a b ha hb
  have hCjN : (Subgroup.centralizer (Q : Set G) ⊓ Y.L j) ≤
      Subgroup.normalizer (Y.Q j : Set G) :=
    inf_le_right.trans ((Y.L_le_Gi j).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi j)))
  obtain ⟨l, hlL, hlab⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert j)).trans a b ha hb
  have hl : (l : G) ∈
      ((Subgroup.centralizer (Q : Set G) ⊓ Y.L j : Subgroup G) : Set G) * (Y.Q j : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCjN, ← hL]
    exact hlL
  obtain ⟨c, hcC, q, hqQ, hcq⟩ := hl
  refine ⟨c, ?_, ?_⟩
  · refine ⟨Subgroup.centralizer_le_normalizer (Q : Set G) hcC.1, ?_⟩
    exact Y.L_le_Gi j hcC.2
  · have hqfix : q • a = a :=
      MulAction.mem_stabilizer_iff.mp (Y.Q_fixes_neighbors_vert j a ha q hqQ)
    calc c • a = c • (q • a) := by rw [hqfix]
      _ = (c * q) • a := (mul_smul c q a).symm
      _ = l • a := congrArg (fun g => g • a) hcq
      _ = b := hlab

private theorem not_isMaxRegLen_eight (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hr₀ : r₀ = 2)
    (h8 : Y.IsMaxRegLen 8) (hregL : Y.LeftTransAt 1 9) (hregR : Y.RightTransAt 1 9) :
    False := by
  set Q : Subgroup G := pCoreOf 2 (Y.arcStab 1 9) with hQdef
  have hQleArc : Q ≤ Y.arcStab 1 9 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hKA : Y.K ≤ Y.arcStab 1 9 := Y.K_le_GT.trans (Y.GT_le_arcStab 1 9)
  have hA : Y.arcStab 1 9 ≤ Y.Gi 1 ⊓ Y.Gi 2 :=
    le_inf (Y.arcStab_le_Gi_left (by norm_num)) (Y.arcStab_le_Gi_left_succ (by norm_num))
  have hsupQ : Y.K ⊔ Q = Y.arcStab 1 9 := by
    have h := (Y.pCoreOf_eq_inf_edgeSylow 1 hKA hA).2
    simpa [hQdef] using h
  have h2reg : 2 * (2 : ℕ) + 3 ≤ (1 : ℤ) + 9 := by norm_num
  have hKQ' := K_le_centralizer_pCoreOf_arcStab Y H hZ he (a := 1) (r := 8) (Or.inr rfl)
    (by simpa using hregL) (by simpa using hregR) (by simpa [hr₀] using h2reg)
  have hKQ : Y.K ≤ Subgroup.centralizer (Q : Set G) := by
    simpa [hQdef] using hKQ'.1
  have hQne : Q ≠ ⊥ := by
    simpa [hQdef] using pCoreOf_arcStab_one_ne_bot Y H (by norm_num : (1 : ℤ) < 9) hregL
  have hQK : Q ≤ Subgroup.centralizer (Y.K : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKQ hk) q hq).symm
  have hQ3 : Q ≤ Y.Q 3 := by
    rw [hQdef]
    exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 9) (by norm_num) (by norm_num)
  have hQ7 : Q ≤ Y.Q 7 := by
    rw [hQdef]
    exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 9) (by norm_num) (by norm_num)
  have hQQs3 : Q ≤ Y.Qs 3 := le_inf hQ3 (hQK)
  have hQQs7 : Q ≤ Y.Qs 7 := le_inf hQ7 hQK
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hab1 := (goldschmidt_small_apply Y H hdJ hd3).1
  have hQs3comm : IsMulCommutative ↥(Y.Qs 3) := by
    haveI : IsMulCommutative ↥(Y.Qs 1) := hab1
    have hq := Y.Qs_add 1 1
    rw [show (1 : ℤ) + 2 * 1 = 3 by norm_num] at hq
    rw [hq]
    exact Subgroup.map_isMulCommutative (G := G) (H := Y.Qs 1)
      (f := (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom)
  have hQs7comm : IsMulCommutative ↥(Y.Qs 7) := by
    haveI : IsMulCommutative ↥(Y.Qs 1) := hab1
    have hq := Y.Qs_add 3 1
    rw [show (1 : ℤ) + 2 * 3 = 7 by norm_num] at hq
    rw [hq]
    exact Subgroup.map_isMulCommutative (G := G) (H := Y.Qs 1)
      (f := (MulAut.conj (Y.τ ^ (3 : ℤ))).toMonoidHom)
  haveI hG3 : Finite ↥(Y.Gi 3) := Y.hyp.finite_stab (Y.vert 3)
  haveI hG5 : Finite ↥(Y.Gi 5) := Y.hyp.finite_stab (Y.vert 5)
  haveI hG7 : Finite ↥(Y.Gi 7) := Y.hyp.finite_stab (Y.vert 7)
  haveI : Finite ↥(Y.Qs 3) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans (Y.Q_le_Gi 3)))
      (Subgroup.inclusion_injective _)
  haveI : Finite ↥(Y.Qs 5) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans (Y.Q_le_Gi 5)))
      (Subgroup.inclusion_injective _)
  haveI : Finite ↥(Y.Qs 7) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans (Y.Q_le_Gi 7)))
      (Subgroup.inclusion_injective _)
  have h2Qs3 : IsPGroup 2 ↥(Y.Qs 3) := (pCoreOf_isPGroup' (Y.Gi 3)).to_le inf_le_left
  have h2Qs7 : IsPGroup 2 ↥(Y.Qs 7) := (pCoreOf_isPGroup' (Y.Gi 7)).to_le inf_le_left
  have hQs3Q4 : Y.Qs 3 ≤ Y.Q 4 := by
    have hU : Y.Qs 3 ≤ Y.Gi 4 := by
      intro x hx
      exact by simpa using ((Y.Q_le_Gi_adj 3).trans inf_le_right) hx.1
    have hcomm : ⁅Y.Qs 3, Y.K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    exact le_Q_of_comm_K_eq_bot Y H (by norm_num : Even (4 : ℤ)) hU h2Qs3 hcomm
  have hQs3Gi5 : Y.Qs 3 ≤ Y.Gi 5 := by
    intro x hx
    exact by simpa using ((Y.Q_le_Gi_adj 4).trans inf_le_right) (hQs3Q4 hx)
  have hQs7Q6 : Y.Qs 7 ≤ Y.Q 6 := by
    have hU : Y.Qs 7 ≤ Y.Gi 6 := by
      intro x hx
      exact by simpa using ((Y.Q_le_Gi_adj 7).trans inf_le_left) hx.1
    have hcomm : ⁅Y.Qs 7, Y.K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    exact le_Q_of_comm_K_eq_bot Y H (by norm_num : Even (6 : ℤ)) hU h2Qs7 hcomm
  have hQs7Gi5 : Y.Qs 7 ≤ Y.Gi 5 := by
    intro x hx
    exact by simpa using ((Y.Q_le_Gi_adj 6).trans inf_le_left) (hQs7Q6 hx)
  have hQs3notQ5 : ¬ Y.Qs 3 ≤ Y.Q 5 := by
    intro hle
    have hleQs5 : Y.Qs 3 ≤ Y.Qs 5 := le_inf hle inf_le_right
    have hcard : Nat.card ↥(Y.Qs 5) = Nat.card ↥(Y.Qs 3) := by
      have hq := Y.Qs_add 1 3
      rw [show (3 : ℤ) + 2 * 1 = 5 by norm_num] at hq
      rw [hq]
      exact Subgroup.card_map_of_injective
        (f := (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom) (MulEquiv.injective _)
    have heq : Y.Qs 3 = Y.Qs 5 :=
      Subgroup.eq_of_le_of_card_ge hleQs5 (le_of_eq hcard)
    have hJ3 : Y.J 3 ≤ Subgroup.normalizer (Y.Qs 3 : Set G) := by
      simpa using J_le_normalizer_Qs_add Y H 1
    have hJ5 : Y.J 5 ≤ Subgroup.normalizer (Y.Qs 3 : Set G) := by
      rw [heq]
      simpa using J_le_normalizer_Qs_add Y H 2
    have hX : Y.Qs 3 ≤ Y.Gi 3 ⊓ Y.Gi 5 :=
      le_inf (inf_le_left.trans (Y.Q_le_Gi 3)) hQs3Gi5
    have hbot := eq_bot_of_normal_J_shift Y H 2 (by simpa using h2Qs3)
      (by simpa using hJ3) (by simpa using hJ5) (by simpa using hX)
    exact hQne (le_bot_iff.mp (hQQs3.trans (le_of_eq hbot)))
  have hQs7notQ5 : ¬ Y.Qs 7 ≤ Y.Q 5 := by
    intro hle
    have hleQs5 : Y.Qs 7 ≤ Y.Qs 5 := le_inf hle inf_le_right
    have hcard : Nat.card ↥(Y.Qs 5) = Nat.card ↥(Y.Qs 7) := by
      have hc5 : Nat.card ↥(Y.Qs 5) = Nat.card ↥(Y.Qs 3) := by
        have hq := Y.Qs_add 1 3
        rw [show (3 : ℤ) + 2 * 1 = 5 by norm_num] at hq
        rw [hq]
        exact Subgroup.card_map_of_injective
          (f := (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom) (MulEquiv.injective _)
      have hc7 : Nat.card ↥(Y.Qs 7) = Nat.card ↥(Y.Qs 3) := by
        have hq := Y.Qs_add 2 3
        rw [show (3 : ℤ) + 2 * 2 = 7 by norm_num] at hq
        rw [hq]
        exact Subgroup.card_map_of_injective
          (f := (MulAut.conj (Y.τ ^ (2 : ℤ))).toMonoidHom) (MulEquiv.injective _)
      exact hc5.trans hc7.symm
    have heq : Y.Qs 7 = Y.Qs 5 :=
      Subgroup.eq_of_le_of_card_ge hleQs5 (le_of_eq hcard)
    have hJ7 : Y.J 7 ≤ Subgroup.normalizer (Y.Qs 7 : Set G) := by
      simpa using J_le_normalizer_Qs_add Y H 3
    have hJ5 : Y.J 5 ≤ Subgroup.normalizer (Y.Qs 7 : Set G) := by
      rw [heq]
      simpa using J_le_normalizer_Qs_add Y H 2
    have hX : Y.Qs 7 ≤ Y.Gi 5 ⊓ Y.Gi 7 :=
      le_inf hQs7Gi5 (inf_le_left.trans (Y.Q_le_Gi 7))
    have hbot := eq_bot_of_normal_J_shift Y H 3 (by simpa using h2Qs7)
      (by simpa using hJ5) (by simpa using hJ7) (by simpa using hX)
    exact hQne (le_bot_iff.mp (hQQs7.trans (le_of_eq hbot)))
  have hn5 : Y.n (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = 1 + 2 * 2 by norm_num, Y.n_add, H.n_one]
  have hne46 : Y.vert 4 ≠ Y.vert 6 := by
    intro h; have := Y.vert_injective h; norm_num at this
  obtain ⟨x, hxQs3, hxQ5⟩ := Set.not_subset.mp hQs3notQ5
  obtain ⟨y, hyQs7, hyQ5⟩ := Set.not_subset.mp hQs7notQ5
  have hxGi5 : x ∈ Y.Gi 5 := hQs3Gi5 hxQs3
  have hyGi5 : y ∈ Y.Gi 5 := hQs7Gi5 hyQs7
  have hx4 : x • Y.vert 4 = Y.vert 4 :=
    by simpa using ((Y.Q_le_Gi_adj 3).trans inf_le_right) hxQs3.1
  have hy6 : y • Y.vert 6 = Y.vert 6 :=
    by simpa using ((Y.Q_le_Gi_adj 7).trans inf_le_left) hyQs7.1
  obtain ⟨mx, hmx⟩ := h2Qs3 ⟨x, hxQs3⟩
  have hxpow : ∃ m : ℕ, x ^ 2 ^ m = 1 :=
    ⟨mx, by simpa using congrArg Subtype.val hmx⟩
  obtain ⟨my, hmy⟩ := h2Qs7 ⟨y, hyQs7⟩
  have hypow : ∃ m : ℕ, y ^ 2 ^ m = 1 :=
    ⟨my, by simpa using congrArg Subtype.val hmy⟩
  have hx6ne : x • Y.vert 6 ≠ Y.vert 6 := by
    intro hfix
    exact hxQ5 (mem_pCoreOf_of_fixes_two Y.hyp hxGi5 hxpow (Y.adj 4).symm (Y.adj 5)
      hne46 (by simpa using hx4) hfix)
  have hy4ne : y • Y.vert 4 ≠ Y.vert 4 := by
    intro hfix
    exact hyQ5 (mem_pCoreOf_of_fixes_two Y.hyp hyGi5 hypow (Y.adj 4).symm (Y.adj 5)
      hne46 hfix (by simpa using hy6))
  have hxCent : x ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (congrArg Subtype.val
      (hQs3comm.is_comm.comm (⟨x, hxQs3⟩ : ↥(Y.Qs 3)) ⟨q, hQQs3 hq⟩)).symm
  have hyCent : y ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (congrArg Subtype.val
      (hQs7comm.is_comm.comm (⟨y, hyQs7⟩ : ↥(Y.Qs 7)) ⟨q, hQQs7 hq⟩)).symm
  have hxNQ : x ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer (Q : Set G) hxCent
  have hyNQ : y ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer (Q : Set G) hyCent
  have hxmem : x ∈ Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 5 := ⟨hxNQ, hxGi5⟩
  have hymem : y ∈ Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 5 := ⟨hyNQ, hyGi5⟩
  have htrans5 := trans_of_two_transpositions Y hn5 (a := Y.vert 4) (b := Y.vert 6)
    (by simpa using (Y.adj 4).symm) (by simpa using Y.adj 5) hne46
    (L := Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 5) inf_le_right hxmem hymem hxpow hypow
    hx4 hy6 hx6ne hy4ne hxQ5 hyQ5

  have hL4eq : Y.L 4 = (Subgroup.centralizer (Q : Set G) ⊓ Y.L 4) ⊔ Y.Q 4 := by
    have h := hKQ'.2
    rw [hr₀] at h
    simpa [hQdef, show (1 : ℤ) + 8 = 9 by norm_num] using h
  have htrans4 := trans_normalizer_inf_Gi_of_L_eq Y (Q := Q) (j := 4) hL4eq
  have hQ4Gi : Q ≤ Y.Gi 4 :=
    hQleArc.trans (Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have hQ5Gi : Q ≤ Y.Gi 5 :=
    hQleArc.trans (Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have hQbot : Q = ⊥ :=
    eq_bot_of_normalizer_trans Y.hyp (α := Y.vert 4) (β := Y.vert 5) (Y.adj 4)
      (le_inf hQ4Gi hQ5Gi) htrans4 htrans5
  exact hQne hQbot


private theorem Z_zero_fix_two_imp_neg (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hfix : Y.Z 0 ≤ Y.Gi 2) : Y.Z 0 ≤ Y.Gi (-2) := by
  have hZGi0 : Y.Z 0 ≤ Y.Gi 0 := (Y.Z_le_Q 0).trans (Y.Q_le_Gi 0)
  have hZGiNeg1 : Y.Z 0 ≤ Y.Gi (-1) := (Y.Z_le_Q 0).trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_left) hq)
  obtain ⟨g, hg, hgswap⟩ := Y.exists_normalizer_K_move (H := Y.Gi 0) 0 (Y.K_le_Gi 0)
    le_rfl (fun a b ha hb => Y.hyp.locTrans ha hb)
    (w := Y.vert (-1)) (w' := Y.vert 1)
    (by simpa using (Y.adj (-1)).symm) (by simpa using Y.adj 0)
    (fun k hk => Y.K_fix k hk (-1)) (fun k hk => Y.K_fix k hk 1)
  have hgG0 : g ∈ Y.Gi 0 := hg.1
  have hfixg : Y.Z 0 ≤ MulAction.stabilizer G (g • Y.vert 2) := by
    rw [stabilizer_smul_eq_conjSub, ← Y.Z_normal 0 g hgG0]
    exact conjSub_mono g hfix
  have hg2adj : Γ.Adj (Y.vert (-1)) (g • Y.vert 2) := by
    have h := (Y.hyp.adj_smul g (Y.vert 1) (Y.vert 2)).mpr (Y.adj 1)
    rwa [hgswap] at h
  have hg2ne0 : g • Y.vert 2 ≠ Y.vert 0 := by
    intro h
    have h' : Y.vert 2 = g⁻¹ • Y.vert 0 := by
      have := congrArg (fun x => g⁻¹ • x) h
      simpa using this
    have hg'inv : g⁻¹ ∈ Y.Gi 0 := (Y.Gi 0).inv_mem hgG0
    rw [MulAction.mem_stabilizer_iff.mp hg'inv] at h'
    have := Y.vert_injective h'
    norm_num at this
  have hnneg1 : Y.n (-1) = 1 := by
    rw [show (-1 : ℤ) = 1 + 2 * (-1) by norm_num, Y.n_add, H.n_one]
  intro z hz
  show z • Y.vert (-2) = Y.vert (-2)
  have hzGi1 : z ∈ Y.Gi (-1) := hZGiNeg1 hz
  have hz0 : z • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp (hZGi0 hz)
  have hzfixg2 : z • (g • Y.vert 2) = g • Y.vert 2 :=
    MulAction.mem_stabilizer_iff.mp (hfixg hz)
  by_cases hg2eq : g • Y.vert 2 = Y.vert (-2)
  · rw [← hg2eq]; exact hzfixg2
  · have hz2adj : Γ.Adj (Y.vert (-1)) (z • Y.vert (-2)) := by
      have h := (Y.hyp.adj_smul z (Y.vert (-1)) (Y.vert (-2))).mpr
        (by simpa using (Y.adj (-2)).symm)
      rwa [MulAction.mem_stabilizer_iff.mp hzGi1] at h
    have hmem3 : z • Y.vert (-2) = Y.vert 0 ∨ z • Y.vert (-2) = Y.vert (-2) ∨
        z • Y.vert (-2) = g • Y.vert 2 :=
      eq_or_eq_or_eq_of_adj Y hnneg1 (Y.adj (-1)) (by simpa using (Y.adj (-2)).symm)
        hg2adj (by intro h; have := Y.vert_injective h; norm_num at this)
        hg2ne0.symm (fun h => hg2eq h.symm) hz2adj
    rcases hmem3 with h | h | h
    · exfalso
      have := Y.vert_injective (MulAction.injective z (h.trans hz0.symm))
      norm_num at this
    · exact h
    · exfalso
      exact hg2eq (MulAction.injective z (h.trans hzfixg2.symm)).symm

private theorem Z_zero_fix_two_iff (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Z 0 ≤ Y.Gi 2 ↔ Y.Z 0 ≤ Y.Gi (-2) := by
  constructor
  · exact Z_zero_fix_two_imp_neg Y H
  · intro hneg
    have h := Z_zero_fix_two_imp_neg Y.reverse H.reverse (by
      simpa [Setup.reverse_Gi, Setup.reverse_Z] using hneg)
    simpa [Setup.reverse_Gi, Setup.reverse_Z] using h

private theorem Z_zero_commutator_Z_two_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 2 2) : ⁅Y.Z 0, Y.Z 2⁆ ≠ ⊥ := by
  intro hcomm
  have hZ0C : Y.Z 0 ≤ Subgroup.centralizer (Y.Z 2 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hUC : Y.Zt 0 ≤ Subgroup.centralizer (Y.Z 2 : Set G) :=
    (Zt_le_Z Y 0).trans hZ0C
  have hZt0Gi2 : Y.Zt 0 ≤ Y.Gi 2 := he.1 2 (by norm_num) le_rfl
  have hZt0Gi1 : Y.Zt 0 ≤ Y.Gi 1 := he.1 1 (by norm_num) (by norm_num)
  have hKU : Y.K ≤ Subgroup.normalizer (Y.Zt 0 : Set G) := Y.K_le_normalizer_Zt 0
  have hU2 : IsPGroup 2 (Y.Zt 0) := Y.isPGroup_Zt 0
  have hUnotQ2 : ¬ Y.Zt 0 ≤ Y.reverse.Q (-2) := by
    intro h
    have h3 : Y.Zt 0 ≤ Y.Gi 3 := h.trans (by
      rw [Setup.reverse_Q, show -(-2 : ℤ) = 2 by norm_num]
      intro q hq
      exact by simpa using ((Y.Q_le_Gi_adj 2).trans inf_le_right) hq)
    exact he.2.1 (by simpa using h3)
  have hUrev : Y.Zt 0 ≤ Y.reverse.Gi (-2) := by
    simpa [Setup.reverse_Gi, show -(-2 : ℤ) = 2 by norm_num] using hZt0Gi2
  have hωrev : Y.Zt 0 ≤ Y.reverse.Gi ((-2 : ℤ) + 1) := by
    simpa [Setup.reverse_Gi, show -((-2 : ℤ) + 1) = 1 by norm_num] using hZt0Gi1
  have hGL := gen_of_K_invariant Y.reverse H.reverse (j := (-2 : ℤ))
    (by norm_num : Even (-2 : ℤ)) (U := Y.Zt 0) hU2 hUrev hKU hUnotQ2 hωrev
  have hQ2C : Y.Q 2 ≤ Subgroup.centralizer (Y.Z 2 : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ centerOf (Y.Q 2) := Y.Z_le_center 2 hz
    exact (Subgroup.mem_centralizer_iff.mp hzc.2 q hq).symm
  have hUW : ∀ y ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.reverse.L (-2),
      (Y.Zt 0).map (MulAut.conj y).toMonoidHom ≤
        Subgroup.centralizer (Y.Z 2 : Set G) := by
    intro y hy
    have hyL : y ∈ Y.L 2 := by
      simpa [Setup.reverse_L, show -(-2 : ℤ) = 2 by norm_num] using hy.2
    have hyG2 : y ∈ Y.Gi 2 := Y.L_le_Gi 2 hyL
    have hZy : conjSub y (Y.Z 2) = Y.Z 2 := Y.Z_normal 2 y hyG2
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Subgroup.mem_map] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    have hcommU : u₀ ∈ Subgroup.centralizer (Y.Z 2 : Set G) := hUC hu₀
    have hzy : y⁻¹ * z * y ∈ Y.Z 2 := by
      have hmem : z ∈ conjSub y (Y.Z 2) := by rw [hZy]; exact hz
      rwa [mem_conjSub] at hmem
    have hcy := Subgroup.mem_centralizer_iff.mp hcommU (y⁻¹ * z * y) hzy
    calc z * (y * u₀ * y⁻¹) = y * ((y⁻¹ * z * y) * u₀) * y⁻¹ := by group
      _ = y * (u₀ * (y⁻¹ * z * y)) * y⁻¹ := by rw [hcy]
      _ = (y * u₀ * y⁻¹) * z := by group
  have hL2C : Y.reverse.L (-2) ≤ Subgroup.centralizer (Y.Z 2 : Set G) :=
    hGL.2 (Subgroup.centralizer (Y.Z 2 : Set G)) hQ2C hUW
  have hKL2 : Y.K ≤ Y.reverse.L (-2) := by
    simpa [Setup.reverse_L, show -(-2 : ℤ) = 2 by norm_num] using
      K_le_L_of_even Y H (by norm_num : Even (2 : ℤ))
  have hKZ2 : ⁅Y.K, Y.Z 2⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKL2.trans hL2C
  have hZ2K : ⁅Y.Z 2, Y.K⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm]
  have hZt2ne : Y.Zt 2 ≠ ⊥ := Zt_ne_bot_of_even Y even_two hZ
  exact hZt2ne (by simpa [Setup.Zt] using hZ2K)

private theorem HasB_zero_two_of_fix_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (he : Y.ZtExt 0 2 2) (hfix2 : Y.Z 0 ≤ Y.Gi 2) : Y.HasB 0 2 := by
  have hnegtwo : Y.Z 0 ≤ Y.Gi (-2) := (Z_zero_fix_two_iff Y H).mp hfix2
  have hZGi0 : Y.Z 0 ≤ Y.Gi 0 := (Y.Z_le_Q 0).trans (Y.Q_le_Gi 0)
  have hZGi1 : Y.Z 0 ≤ Y.Gi 1 := (Y.Z_le_Q 0).trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_right) hq)
  have hZGiNeg1 : Y.Z 0 ≤ Y.Gi (-1) := (Y.Z_le_Q 0).trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_left) hq)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj1 : ((j.natAbs : ℕ) : ℤ) ≤ 2 := by exact_mod_cast hj
    have hjle : j ≤ 2 := by
      have := Int.le_natAbs (a := j)
      omega
    have hjge : -(2 : ℤ) ≤ j := by
      have h := Int.le_natAbs (a := -j)
      rw [Int.natAbs_neg] at h
      omega
    interval_cases j
    · simpa using hnegtwo
    · simpa using hZGiNeg1
    · simpa using hZGi0
    · simpa using hZGi1
    · simpa using hfix2
  · intro h
    exact he.2.1 ((Zt_le_Z Y 0).trans h)
  · intro h
    exact he.2.2 ((Zt_le_Z Y 0).trans h)

private theorem Z_le_Gi_iff_of_even (Y : Setup Γ G) {m j : ℤ} (hm : Even m) :
    Y.Z m ≤ Y.Gi j ↔ Y.Z 0 ≤ Y.Gi (j - m) := by
  obtain ⟨k, hk⟩ := hm
  have hm2 : m = 2 * k := by omega
  have hZ := Y.Z_add k 0
  rw [show (0 : ℤ) + 2 * k = m by omega] at hZ
  have hG := Y.Gi_add k (j - m)
  rw [show j - m + 2 * k = j by omega] at hG
  rw [hZ, hG]
  exact Subgroup.map_le_map_iff_of_injective
    (MulEquiv.injective (MulAut.conj (Y.τ ^ k)))

private theorem commutator_Z_two_Z_four_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 2 2) : ⁅Y.Z 2, Y.Z 4⁆ ≠ ⊥ := by
  intro h
  apply Z_zero_commutator_Z_two_ne_bot Y H hZ he
  have hz2 : Y.Z 2 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 0) := by
    have hh := Y.Z_add 1 0
    rwa [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at hh
  have hz4 : Y.Z 4 = conjSub (Y.τ ^ (1 : ℤ)) (Y.Z 2) := by
    have hh := Y.Z_add 1 2
    rwa [show (2 : ℤ) + 2 * 1 = 4 by norm_num] at hh
  have hc : conjSub (Y.τ ^ (1 : ℤ)) ⁅Y.Z 0, Y.Z 2⁆ = ⊥ := by
    rw [← conjSub_commutator, ← hz2, ← hz4]
    exact h
  have := congrArg (conjSub (Y.τ ^ (-1 : ℤ))) hc
  rw [← conjSub_mul, show Y.τ ^ (-1 : ℤ) * Y.τ ^ (1 : ℤ) = 1 by group,
    conjSub_one] at this
  simpa [conjSub] using this

private theorem pCoreOf_GT_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    pCoreOf 2 Y.GT = ⊥ := by
  have h2 : IsPGroup 2 ↥(pCoreOf 2 Y.GT) := pCoreOf_isPGroup' Y.GT
  have hle : pCoreOf 2 Y.GT ≤ Y.GT := CFSG.LieType.BorelTits.pCoreOf_le 2 Y.GT
  have hdvd : Nat.card ↥(pCoreOf 2 Y.GT) ∣ Nat.card ↥Y.GT :=
    Subgroup.card_dvd_of_le hle
  rcases h2.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd (h.trans hdvd) H.odd_GT.not_two_dvd_nat

private theorem regular_zero_six_of_fix_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 2 2) (h6 : Y.IsMaxRegLen 6)
    (hfix2 : Y.Z 0 ≤ Y.Gi 2) : Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6 := by
  have hnegtwo : Y.Z 0 ≤ Y.Gi (-2) := (Z_zero_fix_two_iff Y H).mp hfix2
  have hZGi0 : Y.Z 0 ≤ Y.Gi 0 := (Y.Z_le_Q 0).trans (Y.Q_le_Gi 0)
  have hZGi1 : Y.Z 0 ≤ Y.Gi 1 := (Y.Z_le_Q 0).trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_right) hq)
  have hZGiNeg1 : Y.Z 0 ≤ Y.Gi (-1) := (Y.Z_le_Q 0).trans (by
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_left) hq)
  have hZ0 : ∀ j : ℤ, -2 ≤ j → j ≤ 2 → Y.Z 0 ≤ Y.Gi j := by
    intro j h1 h2
    interval_cases j
    · exact hnegtwo
    · exact hZGiNeg1
    · exact hZGi0
    · exact hZGi1
    · exact hfix2
  have hZ2fix : ∀ j : ℤ, 0 ≤ j → j ≤ 4 → Y.Z 2 ≤ Y.Gi j := by
    intro j h1 h2
    rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (2 : ℤ))]
    exact hZ0 (j - 2) (by omega) (by omega)
  have hZ4fix : ∀ j : ℤ, 2 ≤ j → j ≤ 6 → Y.Z 4 ≤ Y.Gi j := by
    intro j h1 h2
    rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (4 : ℤ))]
    exact hZ0 (j - 4) (by omega) (by omega)
  have hZ2leGi4 : Y.Z 2 ≤ Y.Gi 4 := hZ2fix 4 (by norm_num) (by norm_num)
  have hZ4leGi2 : Y.Z 4 ≤ Y.Gi 2 := hZ4fix 2 (by norm_num) (by norm_num)
  have hcomm24 : ⁅Y.Z 2, Y.Z 4⁆ ≠ ⊥ := commutator_Z_two_Z_four_ne_bot Y H hZ he
  have hZ4N : Y.Z 4 ≤ Subgroup.normalizer (Y.Z 2 : Set G) :=
    hZ4leGi2.trans (Y.Gi_le_normalizer_Z 2)
  have hZ2N : Y.Z 2 ≤ Subgroup.normalizer (Y.Z 4 : Set G) :=
    hZ2leGi4.trans (Y.Gi_le_normalizer_Z 4)
  have hcomm_le : ⁅Y.Z 2, Y.Z 4⁆ ≤ Y.Z 2 ⊓ Y.Z 4 := by
    refine le_inf ?_ ?_
    · have h := (Subgroup.le_normalizer_iff_commutator_le_right (H := Y.Z 4)
        (K := Y.Z 2)).mp hZ4N
      rwa [Subgroup.commutator_comm] at h
    · exact (Subgroup.le_normalizer_iff_commutator_le_right (H := Y.Z 2)
        (K := Y.Z 4)).mp hZ2N
  have harc0 : Y.arcStab 0 6 = Y.Gi 0 ⊓ Y.Gi 6 := Y.arcStab_eq_inf (by norm_num)
  have hcomm_arc : ⁅Y.Z 2, Y.Z 4⁆ ≤ Y.arcStab 0 6 := by
    rw [harc0]
    refine le_inf ?_ ?_
    · exact (hcomm_le.trans inf_le_left).trans (hZ2fix 0 (by norm_num) (by norm_num))
    · exact (hcomm_le.trans inf_le_right).trans (hZ4fix 6 (by norm_num) (by norm_num))
  have harcGi2 : Y.arcStab 0 6 ≤ Y.Gi 2 :=
    Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num)
  have harcGi4 : Y.arcStab 0 6 ≤ Y.Gi 4 :=
    Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num)
  have hNcomm : Y.arcStab 0 6 ≤ Subgroup.normalizer ((⁅Y.Z 2, Y.Z 4⁆ : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hg2 : conjSub g (Y.Z 2) = Y.Z 2 := Y.Z_normal 2 g (harcGi2 hg)
    have hg4 : conjSub g (Y.Z 4) = Y.Z 4 := Y.Z_normal 4 g (harcGi4 hg)
    change conjSub g (⁅Y.Z 2, Y.Z 4⁆ : Subgroup G) = (⁅Y.Z 2, Y.Z 4⁆ : Subgroup G)
    rw [← conjSub_commutator, hg2, hg4]
  have hcomm2 : IsPGroup 2 ↥⁅Y.Z 2, Y.Z 4⁆ :=
    (pCoreOf_isPGroup' (Y.Gi 2)).to_le
      ((hcomm_le.trans inf_le_left).trans (Y.Z_le_Q 2))
  set P : Subgroup G := pCoreOf 2 (Y.arcStab 0 6) with hPdef
  have hPle : ⁅Y.Z 2, Y.Z 4⁆ ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (N := ⁅Y.Z 2, Y.Z 4⁆)
      hcomm_arc (Subgroup.normal_subgroupOf_of_le_normalizer hNcomm) hcomm2
  have hPne : P ≠ ⊥ := by
    intro hbot
    exact hcomm24 (le_bot_iff.mp (hPle.trans (le_of_eq hbot)))
  have hParc : P ≤ Y.arcStab 0 6 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPnorm0 : Y.arcStab 0 6 ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.arcStab 0 6)
  have hPnotleft : ¬ P ≤ Y.Gi (-1) := by
    intro hle
    have hPle' : P ≤ Y.arcStab (-1) 6 := by
      rw [Y.arcStab_eq_inf (by norm_num : (-1 : ℤ) ≤ 6)]
      refine le_inf hle ?_
      exact (hParc.trans (le_of_eq harc0)) |>.trans inf_le_right
    have hKle : Y.arcStab (-1) 6 ≤ Y.arcStab 0 6 := Y.arcStab_anti (by norm_num) (by norm_num)
    have hN : (P.subgroupOf (Y.arcStab (-1) 6)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hKle.trans hPnorm0)
    have hPleO : P ≤ pCoreOf 2 (Y.arcStab (-1) 6) :=
      CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (N := P) hPle' hN
        (pCoreOf_isPGroup' (Y.arcStab 0 6))
    have hGT : Y.arcStab (-1) 6 = Y.GT := by
      have h := h6.2 (-1) 7 (by norm_num)
      simpa using h
    have hGTbot : pCoreOf 2 Y.GT = ⊥ := pCoreOf_GT_eq_bot Y H
    rw [hGT, hGTbot] at hPleO
    exact hPne (le_bot_iff.mp hPleO)
  have hPnotright : ¬ P ≤ Y.Gi 7 := by
    intro hle
    have hPle' : P ≤ Y.arcStab 0 7 := by
      rw [Y.arcStab_eq_inf (by norm_num : (0 : ℤ) ≤ 7)]
      refine le_inf ?_ hle
      exact (hParc.trans (le_of_eq harc0)) |>.trans inf_le_left
    have hKle : Y.arcStab 0 7 ≤ Y.arcStab 0 6 := Y.arcStab_anti (by norm_num) (by norm_num)
    have hN : (P.subgroupOf (Y.arcStab 0 7)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hKle.trans hPnorm0)
    have hPleO : P ≤ pCoreOf 2 (Y.arcStab 0 7) :=
      CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (N := P) hPle' hN
        (pCoreOf_isPGroup' (Y.arcStab 0 6))
    have hGT : Y.arcStab 0 7 = Y.GT := by
      have h := h6.2 0 7 (by norm_num)
      simpa using h
    have hGTbot : pCoreOf 2 Y.GT = ⊥ := pCoreOf_GT_eq_bot Y H
    rw [hGT, hGTbot] at hPleO
    exact hPne (le_bot_iff.mp hPleO)
  exact regular_of_pCoreOf Y (by norm_num : (0 : ℤ) < 6) hPnotright hPnotleft

theorem s_sub_one_le_of_isMaxRegLen (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r : ℕ}
    (hr : Y.IsMaxRegLen r) : s - 1 ≤ r := by
  by_contra h
  have hlt : r < s - 1 := by omega
  have hk : 1 ≤ s - 1 := by omega
  have hreg := H.sing.2.1 (s - 1) hk (by omega : s - 1 < s) (Y.line.arc 0 (s - 1))
  have hR : Y.RightTransAt 0 (((s - 1 : ℕ)) : ℤ) := by
    have h := (Y.rightTransitive_arc_iff 0 hk).mp hreg.2
    simpa using h
  have hGT : Y.arcStab 0 (((s - 1 : ℕ)) : ℤ) = Y.GT := by
    simpa using hr.2 0 (s - 1) hlt
  exact Y.arcStab_ne_GT_of_rightTransAt (by omega : (0 : ℤ) < ((s - 1 : ℕ) : ℤ)) hR hGT

private theorem s_eq_seven_of_isMaxRegLen_six (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hr₀ : r₀ = 2)
    (h6 : Y.IsMaxRegLen 6) (hregL : Y.LeftTransAt 1 7) (hregR : Y.RightTransAt 1 7) :
    s = 7 ∧ Y.HasB 0 2 ∧ Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6 := by
  subst hr₀
  by_cases hfix2 : Y.Z 0 ≤ Y.Gi 2
  · have hB : Y.HasB 0 2 := HasB_zero_two_of_fix_two Y H he hfix2
    have hreg06 : Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6 :=
      regular_zero_six_of_fix_two Y H hZ he h6 hfix2
    have hsle7 : s ≤ 7 := by
      have := s_sub_one_le_of_isMaxRegLen Y H h6
      omega
    have hs7 : s = 7 := by
      have hs5or7 : s = 5 ∨ s = 7 := by
        obtain ⟨k, hk⟩ := H.odd_s
        have h5 := H.five_le
        omega
      rcases hs5or7 with h5 | h7
      · exfalso
        obtain ⟨e, hee⟩ := exists_regular_parity Y H
        have h0 : (0 : ZMod 2) = e := by
          have h := hee 0 6 (by omega) hreg06.1 hreg06.2
          simpa using h
        have h1 : (1 : ZMod 2) = e := by
          have h := hee 1 6 (by omega) (by simpa using hregL) (by simpa using hregR)
          simpa using h
        exact zero_ne_one (h0.trans h1.symm)
      · exact h7
    exact ⟨hs7, hB, hreg06.1, hreg06.2⟩
  ·
    exfalso
    have hnegtwo : ¬ Y.Z 0 ≤ Y.Gi (-2) := fun h =>
      hfix2 ((Z_zero_fix_two_iff Y H).mpr h)
    set Q : Subgroup G := pCoreOf 2 (Y.arcStab 1 7) with hQdef
    have hQleArc : Q ≤ Y.arcStab 1 7 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hKQ' := K_le_centralizer_pCoreOf_arcStab Y H hZ he (a := 1) (r := 6) (Or.inr rfl)
      hregL hregR (by norm_num)
    have hKQ : Y.K ≤ Subgroup.centralizer (Q : Set G) := by simpa [hQdef] using hKQ'.1
    have hKA : Y.K ≤ Y.arcStab 1 7 := Y.K_le_GT.trans (Y.GT_le_arcStab 1 7)
    have hA : Y.arcStab 1 7 ≤ Y.Gi 1 ⊓ Y.Gi 2 :=
      le_inf (Y.arcStab_le_Gi_left (by norm_num)) (Y.arcStab_le_Gi_left_succ (by norm_num))
    have hsupQ : Y.K ⊔ Q = Y.arcStab 1 7 := by
      have h := (Y.pCoreOf_eq_inf_edgeSylow 1 hKA hA).2
      simpa [hQdef] using h
    have hQne : Q ≠ ⊥ := by
      simpa [hQdef] using pCoreOf_arcStab_one_ne_bot Y H (by norm_num : (1 : ℤ) < 7) hregL
    have hZGi0 : Y.Z 0 ≤ Y.Gi 0 := (Y.Z_le_Q 0).trans (Y.Q_le_Gi 0)
    have hZGi1 : Y.Z 0 ≤ Y.Gi 1 := (Y.Z_le_Q 0).trans (by
      intro q hq
      exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_right) hq)
    have hZGiNeg1 : Y.Z 0 ≤ Y.Gi (-1) := (Y.Z_le_Q 0).trans (by
      intro q hq
      exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_left) hq)
    have hZ0fix : ∀ j : ℤ, -1 ≤ j → j ≤ 1 → Y.Z 0 ≤ Y.Gi j := by
      intro j h1 h2
      interval_cases j
      · exact hZGiNeg1
      · exact hZGi0
      · exact hZGi1
    have hZ2fix : ∀ j : ℤ, 1 ≤ j → j ≤ 3 → Y.Z 2 ≤ Y.Gi j := by
      intro j h1 h2
      rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (2 : ℤ))]
      exact hZ0fix (j - 2) (by omega) (by omega)
    have hZ4fix : ∀ j : ℤ, 3 ≤ j → j ≤ 5 → Y.Z 4 ≤ Y.Gi j := by
      intro j h1 h2
      rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (4 : ℤ))]
      exact hZ0fix (j - 4) (by omega) (by omega)
    have hZ2not4 : ¬ Y.Z 2 ≤ Y.Gi 4 := by
      rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (2 : ℤ))]
      norm_num
      exact hfix2
    have hZ4not2 : ¬ Y.Z 4 ≤ Y.Gi 2 := by
      rw [Z_le_Gi_iff_of_even Y (by norm_num : Even (4 : ℤ))]
      norm_num
      exact hnegtwo
    obtain ⟨z2, hz2Z2, hz2Gi4⟩ := Set.not_subset.mp hZ2not4
    obtain ⟨z4, hz4Z4, hz4Gi2⟩ := Set.not_subset.mp hZ4not2
    have hz2Gi3 : z2 ∈ Y.Gi 3 := hZ2fix 3 (by norm_num) (by norm_num) hz2Z2
    have hz4Gi3 : z4 ∈ Y.Gi 3 := hZ4fix 3 (by norm_num) (by norm_num) hz4Z4
    have hz2fix2 : z2 • Y.vert 2 = Y.vert 2 :=
      MulAction.mem_stabilizer_iff.mp (hZ2fix 2 (by norm_num) (by norm_num) hz2Z2)
    have hz4fix4 : z4 • Y.vert 4 = Y.vert 4 :=
      MulAction.mem_stabilizer_iff.mp (hZ4fix 4 (by norm_num) (by norm_num) hz4Z4)
    have hz2pow : ∃ m : ℕ, z2 ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup' (Y.Gi 2)).to_le (Y.Z_le_Q 2) ⟨z2, hz2Z2⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hz4pow : ∃ m : ℕ, z4 ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup' (Y.Gi 4)).to_le (Y.Z_le_Q 4) ⟨z4, hz4Z4⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hQ2 : Q ≤ Y.Q 2 := by
      rw [hQdef]
      exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 7) (by norm_num) (by norm_num)
    have hQ4 : Q ≤ Y.Q 4 := by
      rw [hQdef]
      exact Y.pCoreOf_arcStab_le_Q_of_lt_of_lt (a := 1) (c := 7) (by norm_num) (by norm_num)
    have hz2Cent : z2 ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hzc : z2 ∈ centerOf (Y.Q 2) := Y.Z_le_center 2 hz2Z2
      exact Subgroup.mem_centralizer_iff.mp hzc.2 q (hQ2 hq)
    have hz4Cent : z4 ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hzc : z4 ∈ centerOf (Y.Q 4) := Y.Z_le_center 4 hz4Z4
      exact Subgroup.mem_centralizer_iff.mp hzc.2 q (hQ4 hq)
    have hz2N := Subgroup.centralizer_le_normalizer (Q : Set G) hz2Cent
    have hz4N := Subgroup.centralizer_le_normalizer (Q : Set G) hz4Cent
    have hz2mem : z2 ∈ Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 3 := ⟨hz2N, hz2Gi3⟩
    have hz4mem : z4 ∈ Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 3 := ⟨hz4N, hz4Gi3⟩
    have hz2notQ3 : z2 ∉ Y.Q 3 := by
      intro h
      exact hz2Gi4 (by simpa using ((Y.Q_le_Gi_adj 3).trans inf_le_right) h)
    have hz4notQ3 : z4 ∉ Y.Q 3 := by
      intro h
      exact hz4Gi2 (by simpa using ((Y.Q_le_Gi_adj 3).trans inf_le_left) h)
    have hnv3 : Y.n 3 = 1 := by
      rw [show (3 : ℤ) = 1 + 2 * 1 by norm_num, Y.n_add, H.n_one]
    have htrans3 := trans_of_two_transpositions Y (v := 3) hnv3
      (a := Y.vert 2) (b := Y.vert 4) (L := Subgroup.normalizer (Q : Set G) ⊓ Y.Gi 3)
      (by simpa using (Y.adj 2).symm) (by simpa using Y.adj 3)
      (by intro h; have := Y.vert_injective h; norm_num at this)
      inf_le_right hz2mem hz4mem hz2pow hz4pow hz2fix2 hz4fix4
      (by intro h; exact hz2Gi4 (by simpa using h))
      (by intro h; exact hz4Gi2 (by simpa using h)) hz2notQ3 hz4notQ3
    have hL4eq : Y.L 4 = (Subgroup.centralizer (Q : Set G) ⊓ Y.L 4) ⊔ Y.Q 4 := by
      simpa [hQdef, show (1 : ℤ) + 6 = 7 by norm_num] using hKQ'.2
    have htrans4 := trans_normalizer_inf_Gi_of_L_eq Y (Q := Q) (j := 4) hL4eq
    have hQ3Gi : Q ≤ Y.Gi 3 :=
      hQleArc.trans (Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
    have hQ4Gi : Q ≤ Y.Gi 4 :=
      hQleArc.trans (Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
    have hQbot : Q = ⊥ :=
      eq_bot_of_normalizer_trans Y.hyp (α := Y.vert 3) (β := Y.vert 4) (Y.adj 3)
        (le_inf hQ3Gi hQ4Gi) htrans3 htrans4
    exact hQne hQbot

private theorem s_lt_of_not_regular_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r : ℕ}
    (hr : Y.IsMaxRegLen r) (hre : Even r)
    (hreg1 : ¬ (Y.LeftTransAt 1 ((1 : ℤ) + (r : ℤ)) ∧
      Y.RightTransAt 1 ((1 : ℤ) + (r : ℤ)))) : s < r := by
  have hs1 : s - 1 ≤ r := s_sub_one_le_of_isMaxRegLen Y H hr
  by_contra hsr'
  have hsr'' : r ≤ s := by omega
  have hsrle : s ≤ r + 1 := Nat.sub_le_iff_le_add.mp hs1
  have hseq : s = r + 1 := by
    rcases (by omega : s = r ∨ s = r + 1) with h | h
    · exfalso
      have hevenS : Even s := by rw [h]; exact hre
      exact (Nat.not_even_iff_odd.mpr H.odd_s) hevenS
    · exact h
  have h5 := H.five_le
  have hlen : 1 ≤ r := by omega
  have hrlt : r < s := by omega
  have hP : Regular Γ G (Y.line.arc 1 r) := H.sing.2.1 r hlen hrlt (Y.line.arc 1 r)
  have hL : Y.LeftTransAt 1 (((1 : ℤ)) + (r : ℤ)) :=
    (Y.leftTransitive_arc_iff 1 r).mp hP.1
  have hR : Y.RightTransAt 1 (((1 : ℤ)) + (r : ℤ)) :=
    (Y.rightTransitive_arc_iff 1 hlen).mp hP.2
  exact hreg1 ⟨by simpa using hL, by simpa using hR⟩

private theorem step2Conclusion_of_regular_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀)
    (hre : Even r)
    (hreg1 : Y.LeftTransAt 1 ((1 : ℤ) + (r : ℤ)) ∧
      Y.RightTransAt 1 ((1 : ℤ) + (r : ℤ)))
    (h2r2 : 2 * r₀ + 2 ≤ r) : Y.Step2Conclusion s r r₀ := by
  have hr₀even : Even r₀ := (s52_step1 Y H hZ he).2
  have hr₀pos : 1 ≤ r₀ := he.one_le.1
  have h8 : r ≤ 8 := le_eight_of_regular_arc Y H hZ he hre hreg1.1 hreg1.2 h2r2
  have hr₀eq2 : r₀ = 2 := by
    obtain ⟨b, hb⟩ := hr₀even
    omega
  have hr6or8 : r = 6 ∨ r = 8 := by
    obtain ⟨k, hk⟩ := hre
    omega
  rcases hr6or8 with hr6 | hr8
  · have h6 : Y.IsMaxRegLen 6 := by simpa [hr6] using hr
    obtain ⟨hs7, hB, hreg0L, hreg0R⟩ :=
      s_eq_seven_of_isMaxRegLen_six Y H hZ he hr₀eq2 h6
        (by simpa [hr6] using hreg1.1) (by simpa [hr6] using hreg1.2)
    exact Or.inr (Or.inr ⟨hr6, hs7, hr₀eq2, hB, hreg0L, hreg0R,
      by simpa [hr6] using hreg1.1, by simpa [hr6] using hreg1.2⟩)
  · have h8' : Y.IsMaxRegLen 8 := by simpa [hr8] using hr
    exfalso
    exact not_isMaxRegLen_eight Y H hZ he hr₀eq2 h8'
      (by simpa [hr8] using hreg1.1) (by simpa [hr8] using hreg1.2)

theorem s52_step2 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀) :
    Y.Step2Conclusion s r r₀ := by
  have hreNat : Even r := even_r_of_isMaxRegLen Y H hr
  have hre : Even (r : ℤ) := by
    obtain ⟨k, hk⟩ := hreNat
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  have h2r : 2 * r₀ ≤ r := two_mul_le_of_ZtExt Y H hZ hr he
  have hr₀pos : 1 ≤ r₀ := he.one_le.1
  have hr₀even : Even r₀ := (s52_step1 Y H hZ he).2
  have hs1r : s - 1 ≤ r := s_sub_one_le_of_isMaxRegLen Y H hr
  rcases regular_at_zero_or_one Y hr with hreg0 | hreg1
  ·
    by_cases h2eq : 2 * r₀ = r
    · exact Or.inl h2eq
    · have h2lt : 2 * r₀ < r := lt_of_le_of_ne h2r h2eq
      have h2r2 : 2 * r₀ + 2 ≤ r := by
        obtain ⟨a, ha⟩ := hreNat
        obtain ⟨b, hb⟩ := hr₀even
        omega
      by_cases hreg1' : Y.LeftTransAt 1 ((1 : ℤ) + (r : ℤ)) ∧
          Y.RightTransAt 1 ((1 : ℤ) + (r : ℤ))
      · exact step2Conclusion_of_regular_one Y H hZ hr he hreNat hreg1' h2r2
      ·
        have hr2eq : 2 * r₀ + 2 = r := by
          by_contra hne'
          have hlt : 2 * r₀ + 2 < r := lt_of_le_of_ne h2r2 hne'
          have h3r : 2 * r₀ + 3 ≤ r := by omega
          exact not_regular_zero_of_small Y H hZ he hre hreg0.1 hreg0.2 h3r
        have hsr : s < r := s_lt_of_not_regular_one Y H hr hreNat hreg1'
        exact Or.inr (Or.inl ⟨hr2eq, hreg1', hsr⟩)
  ·
    by_cases h2eq : 2 * r₀ = r
    · exact Or.inl h2eq
    · have h2lt : 2 * r₀ < r := lt_of_le_of_ne h2r h2eq
      have h2r2 : 2 * r₀ + 2 ≤ r := by
        obtain ⟨a, ha⟩ := hreNat
        obtain ⟨b, hb⟩ := hr₀even
        omega
      exact step2Conclusion_of_regular_one Y H hZ hr he hreNat hreg1 h2r2

theorem comm_Zt_ne_bot_of_ZtExt (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≠ ⊥ := by
  intro hbot
  have hRevenNat : Even r₀ := (s52_step1 Y H hZ he).2
  have hReven : Even (r₀ : ℤ) := by
    obtain ⟨d, hd⟩ := hRevenNat
    exact ⟨(d : ℤ), by rw [hd]; push_cast; ring⟩
  have hZt_le_Z : ∀ i : ℤ, Y.Zt i ≤ Y.Z i := fun i => Zt_le_Z Y i
  have hZt2 : ∀ i : ℤ, IsPGroup 2 ↥(Y.Zt i) := fun i => Y.isPGroup_Zt i
  have hZtr_ne : Y.Zt (r₀ : ℤ) ≠ ⊥ := Zt_ne_bot_of_even Y hReven hZ
  have hQle0 : Y.Zt 0 ≤ Y.Q 0 := (hZt_le_Z 0).trans (Y.Z_le_Q 0)
  have hr1 : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h | h
    · exfalso
      apply he.2.1
      rw [h]
      simpa using hQle0.trans (by
        intro q hq
        exact by simpa using ((Y.Q_le_Gi_adj 0).trans inf_le_right) hq)
    · exact h
  have hfixr : Y.Zt 0 ≤ Y.Gi (r₀ : ℤ) := by
    simpa using he.1 (r₀ : ℤ) (by omega) le_rfl
  have hfixrm1 : Y.Zt 0 ≤ Y.Gi ((r₀ : ℤ) - 1) := by
    simpa using he.1 ((r₀ : ℤ) - 1) (by omega) (by omega)
  have hnotQ : ¬ Y.Zt 0 ≤ Y.Q (r₀ : ℤ) := by
    intro hQ
    have hcon : ¬ Y.Zt 0 ≤ Y.Gi ((r₀ : ℤ) + 1) := by simpa using he.2.1
    apply hcon
    refine hQ.trans ?_
    intro q hq
    exact by simpa using ((Y.Q_le_Gi_adj (r₀ : ℤ)).trans inf_le_right) hq
  have hKU : Y.K ≤ Subgroup.normalizer (Y.Zt 0 : Set G) := Y.K_le_normalizer_Zt 0
  have hEvenNeg : Even (-(r₀ : ℤ)) := hReven.neg
  have hGL := gen_of_K_invariant Y.reverse H.reverse (j := -(r₀ : ℤ)) (U := Y.Zt 0) hEvenNeg
    (hZt2 0)
    (by rw [Setup.reverse_Gi]; simpa using hfixr)
    (by simpa only [Setup.reverse_K] using hKU)
    (by rw [Setup.reverse_Q]; simpa using hnotQ)
    (by
      rw [Setup.reverse_Gi]
      convert hfixrm1 using 2
      ring)
  have hLqr : Y.Q (r₀ : ℤ) ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) :=
    Q_le_centralizer_Zt Y (r₀ : ℤ)
  have hcent0 : Y.Zt 0 ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
  have hconj : ∀ y ∈ Subgroup.normalizer (Y.K : Set G) ⊓ Y.L (r₀ : ℤ),
      (Y.Zt 0).map (MulAut.conj y).toMonoidHom ≤
        Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    intro y hy
    exact map_conj_le_centralizer_Zt Y hcent0 hy
  have hLcent : Y.L (r₀ : ℤ) ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    have h := hGL.2 (Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G))
      (by simpa using hLqr) (by
        intro y hy
        exact hconj y (by simpa using hy))
    simpa using h
  have hZtbot : Y.Zt (r₀ : ℤ) = ⊥ :=
    Zt_eq_bot_of_L_le_centralizer Y H hReven hLcent
  exact hZtr_ne hZtbot

theorem Gi_one_le_normalizer_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Gi 1 ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := by
  have hf : (Y.Gi 1 ⊓ Y.Gi 2) ⊔ Y.L 1 = Y.Gi 1 := by
    simpa using frattini_oTwoPrime Y.hyp (Y.adj 1)
  have hKS : Y.K ⊔ Y.edgeSylow 1 = Y.Gi 1 ⊓ Y.Gi 2 := by
    simpa using Y.K_sup_edgeSylow 1
  have hS : Y.edgeSylow 1 ≤ Y.L 1 := Y.edgeSylow_le_L 1
  have hG1 : Y.Gi 1 = Y.L 1 ⊔ Y.K := by
    calc Y.Gi 1 = (Y.Gi 1 ⊓ Y.Gi 2) ⊔ Y.L 1 := hf.symm
      _ = (Y.K ⊔ Y.edgeSylow 1) ⊔ Y.L 1 := by rw [hKS]
      _ = Y.L 1 ⊔ Y.K := by rw [sup_assoc, sup_eq_right.mpr hS, sup_comm]
  have hK : Y.K ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := Y.K_le_normalizer_Zt 1
  have hKnormQ : Y.K ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (Y.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  have hcomm_sup : ⁅Y.Z 1, Y.Q 1 ⊔ Y.K⁆ ≤ Y.Zt 1 := by
    rw [sup_comm, Setup.Zt]
    refine Subgroup.commutator_le.mpr ?_
    intro z hz b hb
    have hcoe : (↑(Y.K ⊔ Y.Q 1) : Set G) = (Y.K : Set G) * (Y.Q 1 : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right Y.K (Y.Q 1) hKnormQ
    have hb' : b ∈ (↑(Y.K ⊔ Y.Q 1) : Set G) := hb
    rw [hcoe] at hb'
    obtain ⟨k, hk, q, hq, rfl⟩ := hb'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hzq : ⁅z, q⁆ = 1 := by
      have hzc : z ∈ Subgroup.centralizer (Y.Q 1 : Set G) := (Y.Z_le_center 1 hz).2
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hzc q hq).symm
    have hmem : ⁅z, k⁆ ∈ ⁅Y.Z 1, Y.K⁆ := Subgroup.commutator_mem_commutator hz hk
    rw [hzq, mul_one]
    rwa [show ⁅z, k⁆ * k * k⁻¹ = ⁅z, k⁆ by group]
  have hconjK : ∀ {l : G}, l ∈ Y.L 1 → conjSub l Y.K ≤ Y.Q 1 ⊔ Y.K := by
    intro l hl x hx
    rw [mem_conjSub] at hx
    have hyl : ⁅l⁻¹ * x * l, l⁆ ∈ Y.Q 1 :=
      (Subgroup.commutator_le.mp (comm_K_L_one_le Y H)) (l⁻¹ * x * l) hx l hl
    have hcomm : ⁅l, l⁻¹ * x * l⁆ ∈ Y.Q 1 := by
      rw [← commutatorElement_inv]
      exact (Y.Q 1).inv_mem hyl
    have heq : x = ⁅l, l⁻¹ * x * l⁆ * (l⁻¹ * x * l) := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hcomm hx
  have hL : Y.L 1 ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : conjSub l (Y.Zt 1) ≤ Y.Zt 1 := by
      have hZ : conjSub l (Y.Z 1) = Y.Z 1 := Y.Z_normal 1 l (Y.L_le_Gi 1 hl)
      have hmap : conjSub l (Y.Zt 1) = ⁅conjSub l (Y.Z 1), conjSub l Y.K⁆ := by
        rw [Setup.Zt, conjSub, Subgroup.map_commutator]
        rfl
      rw [hmap, hZ]
      exact (Subgroup.commutator_mono le_rfl (hconjK hl)).trans hcomm_sup
    have hle_inv : conjSub l⁻¹ (Y.Zt 1) ≤ Y.Zt 1 := by
      have hl' : l⁻¹ ∈ Y.L 1 := (Y.L 1).inv_mem hl
      have hZ : conjSub l⁻¹ (Y.Z 1) = Y.Z 1 := Y.Z_normal 1 l⁻¹ (Y.L_le_Gi 1 hl')
      have hmap : conjSub l⁻¹ (Y.Zt 1) = ⁅conjSub l⁻¹ (Y.Z 1), conjSub l⁻¹ Y.K⁆ := by
        rw [Setup.Zt, conjSub, Subgroup.map_commutator]
        rfl
      rw [hmap, hZ]
      exact (Subgroup.commutator_mono le_rfl (hconjK hl')).trans hcomm_sup
    have hge : Y.Zt 1 ≤ conjSub l (Y.Zt 1) := by
      have := conjSub_mono l hle_inv
      rwa [conjSub_inv_conjSub] at this
    exact le_antisymm hle hge
  rw [hG1]
  exact sup_le hL hK

private theorem L_zero_le_centralizer_Z_zero_of_S_le (Y : Setup Γ G)
    (hS : Y.S ≤ Subgroup.centralizer (Y.Z 0 : Set G)) :
    Y.L 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
  have hSylL : IsSylowTwoOf Y.S (Y.L 0) := by
    have h := Y.isSylowTwoOf_edgeSylow_L 0
    rwa [Y.edgeSylow_zero] at h
  haveI hLfin : Finite ↥(Y.L 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.L 0) (Y.L_le_Gi 0)
  change Subgroup.closure {x : G | x ∈ Y.Gi 0 ∧ ∃ n : ℕ, x ^ 2 ^ n = 1} ≤
    Subgroup.centralizer (Y.Z 0 : Set G)
  rw [Subgroup.closure_le (K := Subgroup.centralizer (Y.Z 0 : Set G))]
  rintro x ⟨hxG0, n, hxn⟩
  have hxL : x ∈ Y.L 0 := Subgroup.subset_closure ⟨hxG0, n, hxn⟩
  show x ∈ Subgroup.centralizer (Y.Z 0 : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨S₀, hS₀⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hSylL
  let x' : ↥(Y.L 0) := ⟨x, hxL⟩
  have hx'n : x' ^ 2 ^ n = 1 := by
    apply Subtype.ext
    simpa [x'] using hxn
  have hx2' : IsPGroup 2 (Subgroup.zpowers x') := isPGroup_zpowers_of_pow_two hx'n
  obtain ⟨Q, hQ⟩ := hx2'.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq ↥(Y.L 0) S₀ Q
  have hxQ : x' ∈ (Q : Subgroup ↥(Y.L 0)) := hQ (Subgroup.mem_zpowers x')
  have hxQ' : x' ∈ ((l • S₀ : Sylow 2 ↥(Y.L 0)) : Subgroup ↥(Y.L 0)) := by
    rw [hl]
    exact hxQ
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ'
  have hxS : ((l : G))⁻¹ * x * (l : G) ∈ Y.S := by
    have h1 := hxQ'
    rw [hS₀, Subgroup.mem_subgroupOf] at h1
    simpa [x', MulAut.conj_symm_apply, mul_assoc] using h1
  have hxconj : x ∈ conjSub (l : G) Y.S := mem_conjSub.mpr hxS
  have hlG0 : (l : G) ∈ Y.Gi 0 := Y.L_le_Gi 0 l.2
  have hZl : conjSub (l : G) (Y.Z 0) = Y.Z 0 := Y.Z_normal 0 (l : G) hlG0
  have hconjS : conjSub (l : G) Y.S ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    rw [mem_conjSub] at ha
    have hzy : (l : G)⁻¹ * z' * (l : G) ∈ Y.Z 0 := by
      have hmem : z' ∈ conjSub (l : G) (Y.Z 0) := by rw [hZl]; exact hz'
      rwa [mem_conjSub] at hmem
    have hcomm := Subgroup.mem_centralizer_iff.mp (hS ha) ((l : G)⁻¹ * z' * (l : G)) hzy
    calc z' * a = (l : G) * (((l : G)⁻¹ * z' * (l : G)) * ((l : G)⁻¹ * a * (l : G))) *
          (l : G)⁻¹ := by group
      _ = (l : G) * (((l : G)⁻¹ * a * (l : G)) * ((l : G)⁻¹ * z' * (l : G))) *
          (l : G)⁻¹ := by rw [hcomm]
      _ = a * z' := by group
  exact Subgroup.mem_centralizer_iff.mp (hconjS hxconj) z hz
theorem Zt_one_inf_centralizer_S_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 ≠ ⊥) :
    Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G) ≤ Y.Zt 0 := by
  set W : Subgroup G := Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G) with hWdef
  have hZt_le_Z : Y.Zt 1 ≤ Y.Z 1 := Zt_le_Z Y 1
  have hWleZt : W ≤ Y.Zt 1 := inf_le_left
  have hWcentS : W ≤ Subgroup.centralizer (Y.S : Set G) := inf_le_right
  have hWleQ1 : W ≤ Y.Q 1 := hWleZt.trans ((hZt_le_Z).trans (Y.Z_le_Q 1))
  have hWleS : W ≤ Y.S := hWleQ1.trans (Y.Q_le_edgeSylow_right 1)
  have hQ1fin : Finite ↥(Y.Q 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 1) (Y.Q_le_Gi 1)
  haveI hWfin : Finite ↥W := Finite.of_injective (Subgroup.inclusion hWleQ1)
    (Subgroup.inclusion_injective _)
  haveI hKfin : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (H := Y.K) (Y.K_le_Gi 0)
  have hW2 : IsPGroup 2 ↥W := (pCoreOf_isPGroup' (Y.Gi 1)).to_le hWleQ1
  have hKodd : Odd (Nat.card ↥Y.K) := Y.odd_card_K
  have hKnormZt : Y.K ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := Y.K_le_normalizer_Zt 1
  have hKnormW : Y.K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hKS : conjSub k Y.S = Y.S := by
      have hkG : k ∈ Y.Gi 0 ⊓ Y.Gi 1 := ⟨Y.K_le_Gi 0 hk, Y.K_le_Gi 1 hk⟩
      have hconjG : conjSub k (Y.Gi 0 ⊓ Y.Gi 1) = Y.Gi 0 ⊓ Y.Gi 1 := by
        rw [conjSub_inf, conjSub_eq_of_mem hkG.1, conjSub_eq_of_mem hkG.2]
      unfold Setup.S
      rw [← pCoreOf_conjSub, hconjG]
    have hKC : conjSub k (Subgroup.centralizer (Y.S : Set G)) =
        Subgroup.centralizer (Y.S : Set G) := by
      rw [← conjSub_centralizer, hKS]
    have hKZt : conjSub k (Y.Zt 1) = Y.Zt 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnormZt hk)
    change conjSub k (Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G)) =
      Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G)
    rw [conjSub_inf, hKZt, hKC]
  have hWQ0 : W ≤ Y.Q 0 := by
    by_contra hnot
    have hWleG0 : W ≤ Y.Gi 0 := hWleQ1.trans (by
      intro q hq
      exact by simpa using ((Y.Q_le_Gi_adj 1).trans inf_le_left) hq)
    have hWleG1 : W ≤ Y.Gi 1 := hWleQ1.trans (Y.Q_le_Gi 1)
    have hGL := gen_of_K_invariant Y H (j := 0) (U := W) (by norm_num : Even (0 : ℤ))
      hW2 hWleG0 hKnormW hnot hWleG1
    have hsupS : W ⊔ Y.Q 0 = Y.S := by
      simpa [Setup.S] using hGL.1
    have hQ0centZ0 : Y.Q 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzc : z ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Y.Z_le_center 0 hz).2
      exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm
    have hWcentZ0 : W ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzS : z ∈ Y.S := ((Y.Z_le_Q 0).trans (Y.Q_le_edgeSylow_left 0)) hz
      exact Subgroup.mem_centralizer_iff.mp (hWcentS hw) z hzS
    have hScentZ0 : Y.S ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
      rw [← hsupS]
      exact sup_le hWcentZ0 hQ0centZ0
    have hLcentZ0 := L_zero_le_centralizer_Z_zero_of_S_le Y hScentZ0
    have hZK : ⁅Y.Z 0, Y.K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hLcentZ0 (K_le_L_zero Y H hk)) z hz).symm
    exact hZ (by simpa [Setup.Zt] using hZK)
  have hWcS : W ≤ centerOf Y.S := le_inf hWleS hWcentS
  have hWZ0 : W ≤ Y.Z 0 := by
    intro w hw
    have hterm : centerOf Y.S ⊓ Y.Q 0 ≤ Y.Z 0 := by
      have hSylS : IsSylowTwoOf Y.S (Y.Gi 0) := by
        simpa [Y.edgeSylow_zero] using
          isSylowTwoOf_of_edgeStab Y.hyp (Y.adj 0) (Y.isSylowTwoOf_edgeSylow 0)
      exact le_iSup₂_of_le Y.S hSylS le_rfl
    exact hterm (Subgroup.mem_inf.mpr ⟨hWcS hw, hWQ0 hw⟩)
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
    fun x hx y hy => Y.Z_commute 1 x (hZt_le_Z (hWleZt hx)) y (hZt_le_Z (hWleZt hy))
  have hinf : W ⊓ Subgroup.centralizer (Y.K : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxZt : x ∈ Y.Zt 1 := hWleZt hxW
    have hmem : x ∈ Y.Zt 1 ⊓ Subgroup.centralizer (Y.K : Set G) := ⟨hxZt, hxC⟩
    rw [(Zt_eq Y H 1).2.1] at hmem
    exact Subgroup.mem_bot.mp hmem
  letI : Subgroup.Normalizes Y.K W := ⟨hKnormW⟩
  have hWeq : W = ⁅W, Y.K⁆ :=
    eq_commutator_of_inf_centralizer_eq_bot (W := W) (R := Y.K) hW2 hWcomm hKodd hinf
  have hWleZt0 : W ≤ Y.Zt 0 := by
    rw [hWeq]
    have h := Subgroup.commutator_mono hWZ0 (le_refl Y.K)
    simpa [Setup.Zt] using h
  simpa [hWdef] using hWleZt0

end Setup

end CFSG.Quasithin.St84