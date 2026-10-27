module

public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.E3OffenderB

public section

namespace CFSG.Quasithin.E3

open CFSG.Open
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {T V : Subgroup G}

omit [Finite G] in
theorem exists_mem_gammaSet_of_wParam_eq {k : ℕ} (hk : wParam T V = k) :
    ∃ A ∈ gammaSet V k T, ¬ A ≤ Subgroup.centralizer (V : Set G) := by
  have hk1 : ¬ wClos V k T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    intro hle
    have : ((k + 1 : ℕ) : ℕ∞) ≤ wParam T V := by
      refine le_iInf₂ fun j hj => ?_
      have h1 : (k : ℕ∞) ≤ j := hk ▸ iInf₂_le j hj
      have h2 : j ≠ k := fun hjk => hj (hjk ▸ hle)
      have h1' : k ≤ j := Nat.cast_le.mp h1
      exact Nat.cast_le.mpr (by omega)
    rw [hk] at this
    exact absurd (Nat.cast_le.mp this) (by omega)
  by_contra hcon
  exact hk1 (iSup₂_le fun A hA => le_inf hA.1 (not_not.mp fun h => hcon ⟨A, hA, h⟩))

theorem eq_inf_normalizer_of_mem_gammaSet (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {k : ℕ}
    (hk : wParam T V = k) {A : Subgroup G} {h : G} (hAT : A ≤ T) (hAh : A ≤ conjSubgroup V h)
    (hAk : mQuot (conjSubgroup V h) A = k) (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    A = conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G) ∧ IsWOffenderAt T V h := by
  have hAB : A ≤ conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hAh (hAT.trans hT.normal)
  have hBk : mQuot (conjSubgroup V h) (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) ≤ k :=
    hAk ▸ mQuot_mono hAB
  have hVh2 : IsPGroup 2 (conjSubgroup V h) :=
    isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) h
  have hBk' :
      mQuot (conjSubgroup V h) (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) = k := by
    by_contra hne
    have hlt := lt_of_le_of_ne hBk hne
    apply hAC
    refine hAB.trans ?_
    have hTN : IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
      B6.isSylowTwoOf_mono hT.sylow hT.normal le_top
    have hB2 : IsPGroup 2 ↥(conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) :=
      hVh2.to_le inf_le_left
    obtain ⟨n, hn, hle⟩ := exists_le_conj_of_isSylowIn hTN inf_le_right hB2
    have h1 : conjSubgroup (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤ T := by
      have := conjSubgroup_mono_left n⁻¹ hle
      rwa [conjSubgroup_conj_inv] at this
    have hmem : conjSubgroup (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ∈
        gammaSet V (mQuot (conjSubgroup V h) (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)))
          T := by
      refine ⟨h1, h * n⁻¹, ?_, ?_⟩
      · rw [← conjSubgroup_conjSubgroup]
        exact conjSubgroup_mono_left n⁻¹ inf_le_left
      · rw [← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    have h2 : conjSubgroup (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤
        Subgroup.centralizer (V : Set G) :=
      ((le_wClos hmem).trans (wClos_le_of_lt_wParam (by rw [hk]; exact_mod_cast hlt))).trans
        inf_le_right
    have hnV : conjSubgroup V n = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
    have h3 := conjSubgroup_mono_left n h2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, conjSubgroup_centralizer,
      hnV] at h3
  refine ⟨?_, fun hbot => hAC (hAh.trans ?_), by rw [hk, hBk']⟩
  · have hadd := mQuot_add (V := conjSubgroup V h) hAB inf_le_left
    rw [hAk, hBk'] at hadd
    have h0 : mQuot (conjSubgroup V h ⊓ Subgroup.normalizer (V : Set G)) A = 0 := by omega
    exact (mQuot_eq_zero_iff (hVh2.to_le inf_le_left) hAB).1 h0
  · exact le_centralizer_iff_comm.mp (commutator_eq_bot_iff_le_centralizer'.mp hbot)

theorem exists_isWOffenderAt_le (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {k : ℕ}
    (hk : wParam T V = k) :
    ∃ g : G, IsWOffenderAt T V g ∧ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ T := by
  obtain ⟨A, ⟨hAT, g, hAg, hAk⟩, hAC⟩ := exists_mem_gammaSet_of_wParam_eq hk
  obtain ⟨hA, hg⟩ := eq_inf_normalizer_of_mem_gammaSet hV hT hk hAT hAg hAk hAC
  exact ⟨g, hg, hA ▸ hAT⟩

theorem mem_aSet_autOn [IsMulCommutative ↥V] (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    (hw : 0 < wParam T V) {g : G} (hg : IsWOffenderAt T V g)
    (hAT : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ T)
    (hdisj : V ⊓ conjSubgroup V g = ⊥) {j k : ℕ} (hk : wParam T V = k)
    (hj : ((j + k : ℕ) : ℕ∞) ≤ rParam V) (hj1 : 1 ≤ j) :
    autOn (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) V ∈ aSet j (autOn T V) := by
  set A := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) with hAdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono inf_le_left (isElemAbelian_conjSubgroup hV g)
  refine ⟨A4.autOn_mono hAT, ?_, isElemAbelian2_autOn hV hAel hAN, ?_⟩
  · intro hbot
    have h28 := e3_28_three hV hT (Or.inl hw) hg
    have hrk : rk ↥(autI hV A) = 0 := by
      have : autI hV A = ⊥ := hbot
      rw [this, rk_bot]
    rw [hrk, hk] at h28
    have h1 : rParam V ≤ (k : ℕ∞) := by
      have := tsub_le_iff_right.1 h28
      simpa using this
    have h2 : ((j + k : ℕ) : ℕ∞) ≤ k := hj.trans h1
    have h3 : j + k ≤ k := by exact_mod_cast h2
    omega
  · intro B hB hBj
    refine le_antisymm (fun v hv => ?_) (fun v hv x hx => hv x (hB hx))
    have hk' : ((j - 1 : ℕ) : ℕ∞) + wParam T V + 1 ≤ rParam V := by
      have e : ((j - 1 : ℕ) : ℕ∞) + (k : ℕ∞) + 1 = ((j + k : ℕ) : ℕ∞) := by
        rw [show j + k = (j - 1) + k + 1 by omega, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      rw [hk, e]
      exact hj
    have h32 := e3_32 hV hg hk'
    have hBle : B ≤ autI hV A := hB
    have hBk : mQuot (autI hV A) B ≤ j - 1 := by
      have : mQuot (autOn A V) B < j := hBj
      exact Nat.le_sub_one_of_lt this
    have hle : fixV (show Subgroup (MulAut (IntMod V hV)) from B) ≤
        gammaCheck (j - 1) (autI hV A) :=
      le_iSup_of_le B (le_iSup_of_le hBle (le_iSup_of_le hBk le_rfl))
    have hvΓ : (v : IntMod V hV) ∈ gammaCheck (j - 1) (autI hV A) := hle hv
    have hvN : (v : G) ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
      (Subgroup.mem_inf.1 (h32 ⟨v, hvΓ, rfl⟩)).2
    intro x hx
    obtain ⟨a, rfl⟩ := (A4.mem_autOn_iff hAN).1 hx
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    have haV : (a : G) * v * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hAN a.2) v).1 v.2
    have hc : (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ ∈ V ⊓ conjSubgroup V g := by
      refine ⟨V.mul_mem haV (V.inv_mem v.2), ?_⟩
      have ha : (a : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.1 a.2).1
      have h1 : (v : G) * (a : G)⁻¹ * (v : G)⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.1 hvN _).1 ((conjSubgroup V g).inv_mem ha)
      have h2 := (conjSubgroup V g).mul_mem ha h1
      rwa [show (a : G) * ((v : G) * (a : G)⁻¹ * (v : G)⁻¹) =
        (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ by group] at h2
    rw [hdisj, Subgroup.mem_bot] at hc
    exact mul_inv_eq_one.1 hc

end CFSG.Quasithin.E3
