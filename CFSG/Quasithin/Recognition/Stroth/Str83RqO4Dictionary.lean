module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain
import CFSG.RankThree.S4Free.StellmacherSzModule
import CFSG.GroupTheory.DedekindNormalizer

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

variable {L1 L2 S : Subgroup G}

theorem Q1_le_S (hF : F112HypW L1 L2 S) : Q1 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)

theorem Q2_le_S (hF : F112HypW L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)

theorem S_eq_sup_left {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
  eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)

theorem S_eq_sup_right {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
  eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))

theorem Z1_ne_Z2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    Z1 L1 L2 S ≠ Z2 L1 L2 S := by
  intro hEq
  obtain ⟨t⟩ := hfr.nonempty_track
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    intro hbot
    exact t.Zv_ne_bot hfr.hF 0 (by rwa [t.Zv_zero])
  have hX : Z1 L1 L2 S ≤ bigB L1 L2 S :=
    (A4.omegaOneCenterOf_le (Q1 L1 L2 S)).trans
      ((Q1_le_S hfr.hF).trans le_sup_right)
  have hP1Z1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hP2Z2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have h1 : L1 ≤ (P1 L1 L2 S ⊓ normalizer (Z1 L1 L2 S : Set G)) ⊔ Q1 L1 L2 S :=
    (le_inf le_sup_left (le_sup_left.trans hP1Z1)).trans le_sup_left
  have h2 : L2 ≤ (P2 L1 L2 S ⊓ normalizer (Z1 L1 L2 S : Set G)) ⊔ Q2 L1 L2 S := by
    rw [hEq]
    exact (le_inf le_sup_left (le_sup_left.trans hP2Z2)).trans le_sup_left
  exact hZ1ne (eq_bot_of_le_bigB hfr.hF.1 hX h1 h2)

theorem normalizer_inf_le_bigB {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    P2 L1 L2 S ⊓ normalizer ((S ⊓ L2 : Subgroup G) : Set G) ≤ bigB L1 L2 S := by
  intro y hy
  obtain ⟨hyP2, hyN⟩ := Subgroup.mem_inf.mp hy
  have hBL2 : bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
    rw [bigB]
    exact sup_le (sup_le hfr.hF.1.h2.borel_le
      ((F1.borelOf_le L2 S).trans
        (Subgroup.le_normalizer : L2 ≤ normalizer (L2 : Set G)))) hfr.hF.1.h2.normalizes
  have hBS : bigB L1 L2 S ≤ normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    (le_inf hfr.hN hBL2).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := L2))
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := L2) (K := bigB L1 L2 S)
      hBL2).mp hyP2
  have hlN : l ∈ normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
    have h := (normalizer ((S ⊓ L2 : Subgroup G) : Set G)).mul_mem hyN
      ((normalizer ((S ⊓ L2 : Subgroup G) : Set G)).inv_mem (hBS hb))
    rwa [mul_inv_cancel_right] at h
  have hlB : l ∈ bigB L1 L2 S := by
    refine (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S) ?_
    exact ⟨hl, hlN⟩
  exact (bigB L1 L2 S).mul_mem hlB hb

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem map_Gv_x₁ (i : ℤ) :
    (t.Gv i).map (MulAut.conj t.x₁).toMonoidHom = t.Gv (-i) :=
  t.track.map_qv_x₁ Subgroup.le_normalizer Subgroup.le_normalizer i

theorem map_Gv_x₂ (i : ℤ) :
    (t.Gv i).map (MulAut.conj t.x₂).toMonoidHom = t.Gv (2 - i) :=
  t.track.map_qv_x₂ Subgroup.le_normalizer Subgroup.le_normalizer i

theorem map_Qv_x₁ (i : ℤ) :
    (t.Qv i).map (MulAut.conj t.x₁).toMonoidHom = t.Qv (-i) :=
  t.track.map_qv_x₁ (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) i

theorem map_Qv_x₂ (i : ℤ) :
    (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) :=
  t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) i

theorem map_Zv_x₁ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₁).toMonoidHom = t.Zv (-i) := by
  have hP1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hP2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  exact t.track.map_qv_x₁ hP1 hP2 i

theorem map_Zv_x₂ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (2 - i) := by
  have hP1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hP2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  exact t.track.map_qv_x₂ hP1 hP2 i

theorem x₁_mem_Gv_zero : t.x₁ ∈ t.Gv 0 := by
  rw [t.Gv_zero]
  exact t.track.x₁_mem

theorem x₁_not_mem_Gv_one : t.x₁ ∉ t.Gv 1 := by
  rw [t.Gv_one]
  exact t.track.x₁_not_mem

theorem x₂_mem_Gv_one : t.x₂ ∈ t.Gv 1 := by
  rw [t.Gv_one]
  exact t.track.x₂_mem

theorem x₂_not_mem_Gv_zero : t.x₂ ∉ t.Gv 0 := by
  rw [t.Gv_zero]
  exact t.track.x₂_not_mem

theorem GT_le_Gw (a b : ℤ) : t.GT ≤ t.Gw a b := by
  intro y hy
  exact mem_win_iff.mpr fun i _ _ => iInf_le (fun i : ℤ => t.Gv i) i hy

theorem GT_le_Gv (i : ℤ) : t.GT ≤ t.Gv i :=
  iInf_le (fun i : ℤ => t.Gv i) i

theorem K_le_GT : t.K ≤ t.GT := by
  intro x hx
  exact mem_iInf.mpr fun i => t.K_le_Gv i hx

theorem Gw_add_one (c : ℤ) : t.Gw c (c + 1) = t.Gv c ⊓ t.Gv (c + 1) := by
  ext y
  rw [mem_inf]
  constructor
  · intro hy
    exact ⟨mem_win_iff.mp hy c le_rfl (by omega),
      mem_win_iff.mp hy (c + 1) (by omega) le_rfl⟩
  · rintro ⟨h1, h2⟩
    exact mem_win_iff.mpr fun i h1' h2' => by
      rcases (show i = c ∨ i = c + 1 by omega) with rfl | rfl
      · exact h1
      · exact h2

theorem Gw_sub_one_add_one (c : ℤ) :
    t.Gw (c - 1) (c + 1) = t.Gv (c - 1) ⊓ t.Gv c ⊓ t.Gv (c + 1) := by
  ext y
  rw [mem_inf, mem_inf]
  constructor
  · intro hy
    exact ⟨⟨mem_win_iff.mp hy (c - 1) (by omega) (by omega),
      mem_win_iff.mp hy c (by omega) (by omega)⟩,
      mem_win_iff.mp hy (c + 1) (by omega) (by omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact mem_win_iff.mpr fun i h1' h2' => by
      rcases (show i = c - 1 ∨ i = c ∨ i = c + 1 by omega) with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3

theorem x₁_mem_normalizer_pCoreOf_GT : t.x₁ ∈ normalizer (pCoreOf 2 t.GT : Set G) := by
  have hmap : (t.GT).map (MulAut.conj t.x₁).toMonoidHom = t.GT := by
    change (⨅ i : ℤ, t.Gv i).map (MulAut.conj t.x₁).toMonoidHom = ⨅ i : ℤ, t.Gv i
    rw [Subgroup.map_iInf (MulAut.conj t.x₁).toMonoidHom (MulAut.conj t.x₁).injective
      (s := fun i => t.Gv i)]
    simp only [t.map_Gv_x₁]
    refine le_antisymm ?_ ?_
    · exact le_iInf fun i => by
        simpa using iInf_le (fun j : ℤ => t.Gv (-j)) (-i)
    · exact le_iInf fun i => by
        simpa using iInf_le (fun j : ℤ => t.Gv j) (-i)
  have hx : t.x₁ ∈ normalizer (t.GT : Set G) := by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (normalizer_le_normalizer_pCoreOf 2 t.GT) hx

theorem x₂_mem_normalizer_pCoreOf_GT : t.x₂ ∈ normalizer (pCoreOf 2 t.GT : Set G) := by
  have hmap : (t.GT).map (MulAut.conj t.x₂).toMonoidHom = t.GT := by
    change (⨅ i : ℤ, t.Gv i).map (MulAut.conj t.x₂).toMonoidHom = ⨅ i : ℤ, t.Gv i
    rw [Subgroup.map_iInf (MulAut.conj t.x₂).toMonoidHom (MulAut.conj t.x₂).injective
      (s := fun i => t.Gv i)]
    simp only [t.map_Gv_x₂]
    refine le_antisymm ?_ ?_
    · exact le_iInf fun i => by
        have h : 2 - (2 - i) = i := by omega
        simpa [h] using iInf_le (fun j : ℤ => t.Gv (2 - j)) (2 - i)
    · exact le_iInf fun i => by
        simpa using iInf_le (fun j : ℤ => t.Gv j) (2 - i)
  have hx : t.x₂ ∈ normalizer (t.GT : Set G) := by
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (normalizer_le_normalizer_pCoreOf 2 t.GT) hx

theorem K_le_normalizer_pCoreOf_GT : t.K ≤ normalizer (pCoreOf 2 t.GT : Set G) :=
  t.K_le_GT.trans (le_normalizer_pCoreOf 2 t.GT)

theorem pCoreOf_GT_le_Qv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (i : ℤ) : pCoreOf 2 t.GT ≤ t.Qv i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 (pCoreOf 2 t.GT) := pCoreOf_isPGroup 2 t.GT
  have hXw : pCoreOf 2 t.GT ≤ t.Gw (i - 1) (i + 1) :=
    (pCoreOf_le 2 t.GT).trans (t.GT_le_Gw (i - 1) (i + 1))
  exact t.le_Qv_of_le_Gw hfr (u := i - 1) (w := i + 1) (j := i) (by omega) (by omega) hX hXw

theorem K_le_normalizer_Qv (i : ℤ) : t.K ≤ normalizer (t.Qv i : Set G) :=
  fun x hx => t.Gv_le_normalizer_Qv i (t.K_le_Gv i hx)

theorem K_le_normalizer_Zv (i : ℤ) : t.K ≤ normalizer (t.Zv i : Set G) :=
  fun x hx => t.Gv_le_normalizer_Zv i (t.K_le_Gv i hx)

theorem K_comm {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ∀ x ∈ t.K, ∀ y ∈ t.K, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a hfr.ha (Classical.choice hfr.hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hfr.hf (Classical.choice hfr.hL2)
  have hc1 := card_isCyclic_of_hallTwoPrime hfr.hF.1.h1.sylow t.hD1hall t.hD1sup hBt1
  have hc2 := card_isCyclic_of_hallTwoPrime hfr.hF.1.h2.sylow t.hD2hall t.hD2sup hBt2
  haveI : IsCyclic ↥t.D1 := hc1.2
  haveI : IsCyclic ↥t.D2 := hc2.2
  have hcomm1 : ∀ x ∈ t.D1, ∀ y ∈ t.D1, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥t.D1) ⟨y, hy⟩)
  have hcomm2 : ∀ x ∈ t.D2, ∀ y ∈ t.D2, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥t.D2) ⟨y, hy⟩)
  have hD2N : t.D1 ≤ normalizer (t.D2 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have h : x * y * x⁻¹ = y := by
      rw [t.hcomm x hx y hy]
      group
    rwa [h]
  intro x hx y hy
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer (H := t.D1) (K := t.D2) hD2N).mp hx
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer (H := t.D1) (K := t.D2) hD2N).mp hy
  calc x1 * x2 * (y1 * y2) = x1 * (x2 * y1) * y2 := by group
    _ = x1 * (y1 * x2) * y2 := by rw [(t.hcomm y1 hy1 x2 hx2).symm]
    _ = x1 * y1 * (x2 * y2) := by group
    _ = y1 * x1 * (x2 * y2) := by rw [hcomm1 x1 hx1 y1 hy1]
    _ = y1 * x1 * (y2 * x2) := by rw [hcomm2 x2 hx2 y2 hy2]
    _ = y1 * (x1 * y2) * x2 := by group
    _ = y1 * (y2 * x1) * x2 := by rw [t.hcomm x1 hx1 y2 hy2]
    _ = y1 * y2 * (x1 * x2) := by group

theorem card_D1 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    Nat.card t.D1 = 2 ^ (2 * a + 1) - 1 := by
  have hBt1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a hfr.ha (Classical.choice hfr.hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  exact (card_isCyclic_of_hallTwoPrime hfr.hF.1.h1.sylow t.hD1hall t.hD1sup hBt1).1

theorem card_D2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    Nat.card t.D2 = 2 ^ f - 1 := by
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hfr.hf (Classical.choice hfr.hL2)
  exact (card_isCyclic_of_hallTwoPrime hfr.hF.1.h2.sylow t.hD2hall t.hD2sup hBt2).1

theorem P1_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S ⊔ t.K := by
  have hLS : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X : Subgroup G => L1 ⊔ X) (S_eq_sup_left hfr)
    rw [h1, ← sup_assoc]
    have h2 : L1 ⊔ (S ⊓ L1) = L1 := by
      rw [sup_eq_left]
      show S ⊓ L1 ≤ L1
      exact inf_le_right
    rw [h2]
  have hPB : P1 L1 L2 S = (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by
    calc P1 L1 L2 S = L1 ⊔ bigB L1 L2 S := rfl
      _ = L1 ⊔ (S ⊔ t.K) := by
        rw [t.hBsplit]
        rw [sup_assoc]
      _ = (L1 ⊔ S) ⊔ t.K := by rw [← sup_assoc]
      _ = (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by rw [hLS]
  exact hPB.le

theorem inf_L2_ne_map_x₂ {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    S ⊓ L2 ≠ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := by
  intro heq
  have hTG01 : S ⊓ L2 ≤ t.Gw 0 1 :=
    inf_le_left.trans (by rw [t.Gw_zero_one hfr.hF]; exact le_sup_right)
  have hT'G12 : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ t.Gw 1 2 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hTG01
    have e := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    rw [show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num] at e
    exact h.trans e.le
  have hTG02 : S ⊓ L2 ≤ t.Gw 0 2 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ 1 ∨ i = 2 by omega) with h3 | rfl
    · exact mem_win_iff.mp (hTG01 hy) i h1 h3
    · have hy' : y ∈ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := heq ▸ hy
      exact mem_win_iff.mp (hT'G12 hy') 2 (by norm_num) le_rfl
  have hTQ : S ⊓ L2 ≤ t.Qv 1 :=
    t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num)
      hfr.hF.1.h2.sylow.2.1 hTG02
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) := by
    rw [t.Qv_one, sup_comm]
    exact S_eq_sup_right hfr
  have hSle : S ≤ t.Qv 1 := hSQ.le.trans (sup_le le_rfl hTQ)
  have hQS : (t.Qv 1).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one, hQS] at h9
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

theorem isSylowTwoOf_map_x₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    IsSylowTwoOf ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) L2 := by
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hBL2 : bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
    rw [bigB]
    exact sup_le (sup_le hfr.hF.1.h2.borel_le
      ((F1.borelOf_le L2 S).trans
        (Subgroup.le_normalizer : L2 ≤ normalizer (L2 : Set G)))) hfr.hF.1.h2.normalizes
  have hx₂L2 : t.x₂ ∈ normalizer (L2 : Set G) :=
    (sup_le Subgroup.le_normalizer hBL2 : P2 L1 L2 S ≤ normalizer (L2 : Set G))
      t.track.x₂_mem
  have hx₂L2map : L2.map (MulAut.conj t.x₂).toMonoidHom = L2 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₂L2
  have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₂) hTsyl
  rwa [hx₂L2map] at h

abbrev Sm : Subgroup G := S.map (MulAut.conj t.x₂).toMonoidHom

abbrev L0 : Subgroup G := S ⊔ t.Sm

abbrev W : Subgroup G := t.Qv 0 ⊓ t.Qv 2

abbrev Ap : Subgroup G := t.Qv 1 ⊓ t.Qv 0

abbrev Am : Subgroup G := t.Qv 1 ⊓ t.Qv 2

theorem L2_le_L0 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    L2 ≤ t.L0 := by
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hT'syl : IsSylowTwoOf ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) L2 :=
    t.isSylowTwoOf_map_x₂ hfr
  have hne : S ⊓ L2 ≠ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom :=
    t.inf_L2_ne_map_x₂ hfr
  have hQ2S : pCoreOf 2 L2 ≤ S := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm L1 L2 S] at h
    exact h.trans (Q2_le_S hfr.hF)
  have hX : (S ⊔ t.Sm) ⊔ pCoreOf 2 L2 = S ⊔ t.Sm := by
    rw [sup_eq_left]
    exact hQ2S.trans le_sup_left
  have hTX : S ⊓ L2 ≤ (S ⊔ t.Sm) ⊔ pCoreOf 2 L2 :=
    (inf_le_left : S ⊓ L2 ≤ S).trans (le_sup_left.trans le_sup_left)
  have hT'X : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤
      (S ⊔ t.Sm) ⊔ pCoreOf 2 L2 :=
    (Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) inf_le_left).trans
      (le_sup_right.trans le_sup_left)
  have h := le_sup_pCoreOf_of_sylow_ne_of_l2 (L := L2) (X := S ⊔ t.Sm)
    hfr.hf hfr.hL2 hTsyl hT'syl hne hTX hT'X
  rwa [hX] at h

theorem L0_le_Gv_one : t.L0 ≤ t.Gv 1 := by
  have hS : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)
  have hSm : t.Sm ≤ P2 L1 L2 S := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact (P2 L1 L2 S).mul_mem
      ((P2 L1 L2 S).mul_mem t.track.x₂_mem (hS hs))
      ((P2 L1 L2 S).inv_mem t.track.x₂_mem)
  rw [t.Gv_one]
  exact sup_le hS hSm

theorem Qv_le_Sm {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ t.Sm ∧ t.Qv 2 ≤ t.Sm := by
  constructor
  · have e := t.map_Qv_x₂ 1
    rw [show (2 : ℤ) - 1 = 1 by norm_num] at e
    calc t.Qv 1 = (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom := e.symm
      _ ≤ S.map (MulAut.conj t.x₂).toMonoidHom :=
          Subgroup.map_mono (t.Qv_one.trans_le (Q2_le_S hfr.hF))
  · have e := t.map_Qv_x₂ 0
    rw [sub_zero] at e
    calc t.Qv 2 = (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom := e.symm
      _ ≤ S.map (MulAut.conj t.x₂).toMonoidHom :=
          Subgroup.map_mono (t.Qv_zero.trans_le (Q1_le_S hfr.hF))

theorem L0_le_normalizer_Qv_one : t.L0 ≤ normalizer (t.Qv 1 : Set G) :=
  t.L0_le_Gv_one.trans (t.Gv_le_normalizer_Qv 1)

theorem L0_le_normalizer_Zv_one : t.L0 ≤ normalizer (t.Zv 1 : Set G) :=
  t.L0_le_Gv_one.trans (t.Gv_le_normalizer_Zv 1)

theorem Qv_one_le_normalizer_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) ∧ t.Qv 1 ≤ normalizer (t.Qv 2 : Set G) := by
  have h1 : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) := by
    have hQ2P1 : Q2 L1 L2 S ≤ P1 L1 L2 S :=
      (Q2_le_S hfr.hF).trans ((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S))
    rw [t.Qv_one, t.Qv_zero]
    exact hQ2P1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  refine ⟨h1, ?_⟩
  have hnorm : (normalizer (t.Qv 0 : Set G)).map (MulAut.conj t.x₂).toMonoidHom =
      normalizer ((t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom) :=
    Subgroup.map_equiv_normalizer_eq (t.Qv 0) (MulAut.conj t.x₂)
  have e1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    have e := t.map_Qv_x₂ 1
    rwa [show (2 : ℤ) - 1 = 1 by norm_num] at e
  have e0 : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    have e := t.map_Qv_x₂ 0
    rwa [sub_zero] at e
  calc t.Qv 1 = (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom := e1.symm
    _ ≤ (normalizer (t.Qv 0 : Set G)).map (MulAut.conj t.x₂).toMonoidHom :=
        Subgroup.map_mono h1
    _ = normalizer ((t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom) := hnorm
    _ = normalizer (t.Qv 2 : Set G) := by rw [e0]

private theorem eq_Q1_Q2_of_inf_le_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : Q2 L1 L2 S ≤ Q1 L1 L2 S)
    (hX : Q1 L1 L2 S ⊓ (S ⊓ L2) ≤ pCoreOf 2 L2) :
    Q1 L1 L2 S = Q2 L1 L2 S := by
  have hQ1S : Q1 L1 L2 S ≤ S := Q1_le_S hfr.hF
  have hpCoreQ2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm L1 L2 S] at h
    exact h
  have hST : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := S_eq_sup_right hfr
  have hQ2NT : Q2 L1 L2 S ≤ normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    (le_inf ((Q2_le_S hfr.hF).trans
        (Subgroup.le_normalizer : S ≤ normalizer (S : Set G)))
      ((Q2_le_S hfr.hF).trans hfr.hF.1.h2.normalizes)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := L2))
  have hXQ2 : Q1 L1 L2 S ⊓ (S ⊓ L2) ≤ Q2 L1 L2 S := hX.trans hpCoreQ2
  have hmod : Q1 L1 L2 S ⊓ ((S ⊓ L2) ⊔ Q2 L1 L2 S) =
      (Q1 L1 L2 S ⊓ (S ⊓ L2)) ⊔ Q2 L1 L2 S := by
    have h := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer
      (S := Q2 L1 L2 S) (T := S ⊓ L2) (U := Q1 L1 L2 S) hQ hQ2NT
    rwa [sup_comm (Q2 L1 L2 S) (S ⊓ L2),
      sup_comm (Q2 L1 L2 S) (Q1 L1 L2 S ⊓ (S ⊓ L2))] at h
  calc Q1 L1 L2 S = Q1 L1 L2 S ⊓ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
        (inf_eq_left.mpr (by rw [← hST]; exact hQ1S)).symm
    _ = (Q1 L1 L2 S ⊓ (S ⊓ L2)) ⊔ Q2 L1 L2 S := hmod
    _ = Q2 L1 L2 S := sup_eq_right.mpr hXQ2

private theorem false_of_S_le_Q1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hSQ1 : S ≤ Q1 L1 L2 S) : False := by
  have hS1eq : S ⊓ L1 = pCoreOf 2 L1 := by
    refine le_antisymm ?_ (le_inf ?_ (pCoreOf_le 2 L1))
    · calc S ⊓ L1 ≤ Q1 L1 L2 S ⊓ L1 := inf_le_inf hSQ1 le_rfl
        _ = L1 ⊓ Q1 L1 L2 S := inf_comm _ _
        _ = pCoreOf 2 L1 := str86_inf_p1_q1 hfr.hF
    · exact (Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1).trans (Q1_le_S hfr.hF)
  have hodd : ¬ 2 ∣ (S ⊓ L1).relIndex L1 := by
    simpa [Subgroup.relIndex] using hfr.hF.1.h1.sylow.2.2
  have hrel : (S ⊓ L1).relIndex L1 = Nat.card (oTwoQuot ↥L1) := by
    rw [hS1eq]
    have e2 : (pCoreOf 2 L1).subgroupOf L1 = pCore 2 ↥L1 := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      exact (F1.mem_pCore_iff_coe x).symm
    exact congrArg (fun K : Subgroup ↥L1 => K.index) e2
  have h2 : 2 ∣ (S ⊓ L1).relIndex L1 := by
    rw [hrel]
    obtain ⟨e⟩ := hfr.hSz
    rw [Nat.card_congr e.toEquiv]
    rw [CFSG.RankThree.S4Free.SzNatural.card_sz]
    have h : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← pow_mul]
      exact dvd_pow_self 2 (by omega)
    exact (h.mul_right _).mul_right _
  exact hodd h2

private theorem false_of_Q1_eq_Q2 {L1 L2 S : Subgroup G} (u : Track L1 L2 S)
    {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ1eq : Q1 L1 L2 S = Q2 L1 L2 S) : False := by
  have hX : Q1 L1 L2 S ≤ bigB L1 L2 S := (Q1_le_S hfr.hF).trans le_sup_right
  have hP1N : P1 L1 L2 S ≤ normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hP2N : P2 L1 L2 S ≤ normalizer (Q2 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have h1 : L1 ≤ (P1 L1 L2 S ⊓ normalizer (Q1 L1 L2 S : Set G)) ⊔ Q1 L1 L2 S :=
    (le_inf le_sup_left (le_sup_left.trans hP1N)).trans le_sup_left
  have h2 : L2 ≤ (P2 L1 L2 S ⊓ normalizer (Q1 L1 L2 S : Set G)) ⊔ Q2 L1 L2 S := by
    rw [hQ1eq]
    exact (le_inf le_sup_left (le_sup_left.trans hP2N)).trans le_sup_left
  have hbot := eq_bot_of_le_bigB hfr.hF.1 hX h1 h2
  have hQ1ne : Q1 L1 L2 S ≠ ⊥ := by
    intro h
    exact u.Qv_ne_bot hfr.hF 0 (by rwa [u.Qv_zero])
  exact hQ1ne hbot

theorem Qv_one_not_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ¬ t.Qv 1 ≤ t.Qv 0 := by
  intro hle
  have hQ : Q2 L1 L2 S ≤ Q1 L1 L2 S := by
    rwa [t.Qv_one, t.Qv_zero] at hle
  let T : Subgroup G := S ⊓ L2
  let X : Subgroup G := Q1 L1 L2 S ⊓ T
  have hT : IsSylowTwoOf T L2 := hfr.hF.1.h2.sylow
  have hXT : X ≤ T := inf_le_right
  have hD2N : t.D2 ≤ normalizer (Q1 L1 L2 S : Set G) := by
    rw [← t.Qv_zero]
    exact (le_sup_right : t.D2 ≤ t.K).trans (t.K_le_normalizer_Qv 0)
  have hDTN : t.D2 ≤ normalizer (T : Set G) :=
    t.hD2hall.1.trans (inf_le_right : L2 ⊓ normalizer (T : Set G) ≤ normalizer (T : Set G))
  have hXD : t.D2 ≤ normalizer (X : Set G) :=
    (le_inf hD2N hDTN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Q1 L1 L2 S) (K := T))
  have hpCoreQ2 : pCoreOf 2 L2 ≤ Q2 L1 L2 S := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm L1 L2 S] at h
    exact h
  have hST : S = T ⊔ Q2 L1 L2 S := S_eq_sup_right hfr
  by_cases hXle : X ≤ pCoreOf 2 L2
  · exact false_of_Q1_eq_Q2 t hfr (eq_Q1_Q2_of_inf_le_pCoreOf hfr hQ hXle)
  · have hKI := le_sup_pCoreOf_of_torus_of_l2 (L := L2) hfr.hf hfr.hL2 hT
        t.hD2hall hXT hXD hXle
    have hTQ1 : T ≤ Q1 L1 L2 S :=
      hKI.trans (sup_le inf_le_left (hpCoreQ2.trans hQ))
    have hSQ1 : S ≤ Q1 L1 L2 S := by
      calc S = T ⊔ Q2 L1 L2 S := hST
        _ ≤ Q1 L1 L2 S := sup_le hTQ1 hQ
    exact false_of_S_le_Q1 hfr hSQ1

theorem map_W_x₂ : t.W.map (MulAut.conj t.x₂).toMonoidHom = t.W := by
  rw [W, Subgroup.map_inf (t.Qv 0) (t.Qv 2) (MulAut.conj t.x₂).toMonoidHom
    (MulAut.conj t.x₂).injective]
  have e0 : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    have e := t.map_Qv_x₂ 0
    rwa [sub_zero] at e
  have e2 : (t.Qv 2).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 0 := by
    have e := t.map_Qv_x₂ 2
    rwa [show (2 : ℤ) - 2 = 0 by norm_num] at e
  rw [e0, e2, inf_comm (t.Qv 2) (t.Qv 0)]

theorem map_Ap_x₂ : t.Ap.map (MulAut.conj t.x₂).toMonoidHom = t.Am := by
  rw [Ap, Am, Subgroup.map_inf (t.Qv 1) (t.Qv 0) (MulAut.conj t.x₂).toMonoidHom
    (MulAut.conj t.x₂).injective]
  have e1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    have e := t.map_Qv_x₂ 1
    rwa [show (2 : ℤ) - 1 = 1 by norm_num] at e
  have e0 : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    have e := t.map_Qv_x₂ 0
    rwa [sub_zero] at e
  rw [e1, e0]

theorem map_Am_x₂ : t.Am.map (MulAut.conj t.x₂).toMonoidHom = t.Ap := by
  rw [Ap, Am, Subgroup.map_inf (t.Qv 1) (t.Qv 2) (MulAut.conj t.x₂).toMonoidHom
    (MulAut.conj t.x₂).injective]
  have e1 : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
    have e := t.map_Qv_x₂ 1
    rwa [show (2 : ℤ) - 1 = 1 by norm_num] at e
  have e2 : (t.Qv 2).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 0 := by
    have e := t.map_Qv_x₂ 2
    rwa [show (2 : ℤ) - 2 = 0 by norm_num] at e
  rw [e1, e2]

theorem W_le_Qv_one {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.W ≤ t.Qv 1 := by
  have hW2 : IsPGroup 2 t.W := (t.isPGroup_Qv 0).to_le inf_le_left
  have hWG : t.W ≤ t.Gw 0 2 := by
    intro y hy
    obtain ⟨hy0, hy2⟩ := Subgroup.mem_inf.mp hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact t.Qv_le_Gv_self 0 hy0
    · exact (t.Qv_le_Gv hfr 0).2 hy0
    · exact t.Qv_le_Gv_self 2 hy2
  exact t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num)
    hW2 hWG

theorem Ap_inf_Am {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Ap ⊓ t.Am = t.W := by
  have hW : t.Qv 0 ⊓ t.Qv 2 ≤ t.Qv 1 := t.W_le_Qv_one hfr
  rw [Ap, Am, W]
  refine le_antisymm ?_ ?_
  · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  · exact le_inf (le_inf hW inf_le_left) (le_inf hW inf_le_right)

end Track

end CFSG.Quasithin.Stroth.Rq

end
