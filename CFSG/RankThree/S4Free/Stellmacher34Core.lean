module

public import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.RankThree.S4Free.Stellmacher33Dihedral
import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.RankThree.S4Free.StellmacherL24

public section

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Blueprint
open CFSG.RankThree.S4Free.Stell33 (LCfgCore)
open scoped commutatorElement Pointwise

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_mul_ne_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  by_contra h
  push Not at h
  have hc : commutator (suzukiGroup a K) = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact h y x
  have htop := (CFSG.LieType.Ree.suzuki_perfect ha hK).1
  rw [hc] at htop
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (suzukiGroup a K)
  have hx : x ∈ (⊥ : Subgroup (suzukiGroup a K)) := htop ▸ mem_top x
  have hy : y ∈ (⊥ : Subgroup (suzukiGroup a K)) := htop ▸ mem_top y
  rw [mem_bot] at hx hy
  exact hxy (hx.trans hy.symm)

theorem not_isPGroup_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsPGroup 2 (suzukiGroup a K) := by
  intro h
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  haveI := hfin
  haveI := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.isNilpotent
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_suzuki ha hK
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 inferInstance x y)

theorem exists_fpf_center {X : Type*} [Group X] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* suzukiGroup a K) (S : Sylow 2 X) :
    ∃ c ∈ normalizer ((S : Subgroup X) : Set X),
      ∀ z ∈ (S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X), c * z * c⁻¹ = z → z = 1 := by
  obtain ⟨C, hC, -, -, hSC, htrans⟩ := Suzuki.exists_cyclic_complement ha hK e S
  obtain ⟨g, hg⟩ := hC.exists_generator
  refine ⟨g, hSC ▸ mem_sup_right g.2, fun z hz hgz => ?_⟩
  by_contra hz1
  have hcomm : Commute (g : X) z := by
    have : (g : X) * z * (g : X)⁻¹ * (g : X) = z * g := by rw [hgz]
    rw [commute_iff_eq, ← this, inv_mul_cancel_right]
  have hCz : ∀ t ∈ C, t * z * t⁻¹ = z := by
    intro t ht
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨t, ht⟩)
    have htk : t = (g : X) ^ k := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    rw [htk, ((hcomm.zpow_left k).eq), mul_inv_cancel_right]
  have hsub : ((S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) : Set X) ⊆ {1, z} := by
    intro z' hz'
    by_cases h1 : z' = 1
    · exact Or.inl h1
    · obtain ⟨t, ht, htz⟩ := htrans z hz z' hz' hz1 h1
      right
      rw [← htz, hCz t ht]
      exact Set.mem_singleton z
  have hcard := (Suzuki.card_sylow_and_center ha hK e S).2.1
  have hle : Nat.card ((S : Subgroup X) ⊓ centralizer ((S : Subgroup X) : Set X) : Subgroup X) ≤
      2 := by
    have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc _ ≤ ({1, z} : Set X).ncard := Set.ncard_le_ncard hsub
      _ ≤ ({z} : Set X).ncard + 1 := Set.ncard_insert_le 1 {z}
      _ = 2 := by rw [Set.ncard_singleton]
  rw [hcard] at hle
  have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Suzuki

variable {Λ : Type*} [Group Λ]

structure SzCfg (T W R : Subgroup Λ) {a : ℕ} {K : Type} [Field K] [Finite K]
    (φ : Λ →* suzukiGroup a K) : Prop where
  isPGroup_T : IsPGroup 2 T
  not_dvd_index : ¬ 2 ∣ T.index
  elemAb : CFSG.Open.IsElemAbelian 2 W
  W_le_T : W ≤ T
  T_le_normalizer : T ≤ normalizer (W : Set Λ)
  normalizer_ne_top : normalizer (W : Set Λ) ≠ ⊤
  sup_conj : ∀ x : Λ, x ∉ normalizer (W : Set Λ) → W ⊔ W.map (MulAut.conj x).toMonoidHom = ⊤
  oTwo_le : oTwo Λ ≤ R
  not_dvd_relIndex : ¬ 2 ∣ (oTwo Λ).relIndex R
  one_le : 1 ≤ a
  card_K : Nat.card K = 2 ^ (2 * a + 1)
  surjective : Function.Surjective φ
  ker_eq : φ.ker = R

namespace SzCfg

variable [Finite Λ] {T W R : Subgroup Λ} {a : ℕ} {K : Type} [Field K] [Finite K]
  {φ : Λ →* suzukiGroup a K}

noncomputable abbrev sylowT (h : SzCfg T W R φ) : Sylow 2 Λ :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  h.isPGroup_T.toSylow h.not_dvd_index

theorem coe_sylowT (h : SzCfg T W R φ) : (h.sylowT : Subgroup Λ) = T :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow_coe _ _

theorem oTwo_le_T (h : SzCfg T W R φ) : oTwo Λ ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← h.coe_sylowT]
  exact (Stell.oTwo_isPGroup Λ).le_sylow_of_normal h.sylowT

theorem normal_R (h : SzCfg T W R φ) : R.Normal := h.ker_eq ▸ φ.normal_ker

theorem exists_not_mem (h : SzCfg T W R φ) : ∃ x : Λ, x ∉ normalizer (W : Set Λ) := by
  by_contra hx
  push Not at hx
  exact h.normalizer_ne_top (eq_top_iff.mpr fun x _ => hx x)

theorem comm_W (h : SzCfg T W R φ) {v w : Λ} (hv : v ∈ W) (hw : w ∈ W) : v * w = w * v :=
  congrArg Subtype.val (h.elemAb.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)

theorem sq_W (h : SzCfg T W R φ) {w : Λ} (hw : w ∈ W) : w ^ 2 = 1 := h.elemAb.2 w hw

theorem map_conj_le_of_normal {Q : Subgroup Λ} [Q.Normal] {V : Subgroup Λ} (hVQ : V ≤ Q)
    (x : Λ) : V.map (MulAut.conj x).toMonoidHom ≤ Q := by
  rintro _ ⟨v, hv, rfl⟩
  exact (inferInstance : Q.Normal).conj_mem v (hVQ hv) x

theorem eq_top_of_le (h : SzCfg T W R φ) {Q : Subgroup Λ} [Q.Normal] (hWQ : W ≤ Q) : Q = ⊤ := by
  obtain ⟨x, hx⟩ := h.exists_not_mem
  rw [eq_top_iff, ← h.sup_conj x hx]
  exact sup_le hWQ (map_conj_le_of_normal hWQ x)


theorem not_isPGroup (h : SzCfg T W R φ) : ¬ IsPGroup 2 Λ := fun h2 =>
  not_isPGroup_suzuki h.one_le h.card_K (h2.of_surjective φ h.surjective)

theorem ne_top_of_isPGroup (h : SzCfg T W R φ) {Q : Subgroup Λ} (hQ : IsPGroup 2 Q) : Q ≠ ⊤ := by
  rintro rfl
  exact h.not_isPGroup (hQ.of_equiv Subgroup.topEquiv)

theorem R_ne_top (h : SzCfg T W R φ) : R ≠ ⊤ := by
  intro hR
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Ree.suzuki_simple h.one_le h.card_K
  obtain ⟨y, hy⟩ := exists_ne (1 : suzukiGroup a K)
  obtain ⟨x, rfl⟩ := h.surjective y
  have : x ∈ φ.ker := h.ker_eq ▸ hR ▸ mem_top x
  exact hy this

theorem not_le_oTwo (h : SzCfg T W R φ) : ¬ W ≤ oTwo Λ := fun hWO =>
  h.ne_top_of_isPGroup (Stell.oTwo_isPGroup Λ) (h.eq_top_of_le hWO)

theorem normalizer_le (h : SzCfg T W R φ) :
    normalizer (T : Set Λ) ≤ normalizer (W : Set Λ) := by
  intro y hy
  by_contra hyW
  have hsup := h.sup_conj y hyW
  have hle : W ⊔ W.map (MulAut.conj y).toMonoidHom ≤ T := by
    refine sup_le h.W_le_T ?_
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.mp hy w).mp (h.W_le_T hw)
  rw [hsup] at hle
  exact h.ne_top_of_isPGroup h.isPGroup_T (top_le_iff.mp hle)

theorem ker_le_normalizer (h : SzCfg T W R φ) : R ≤ normalizer (W : Set Λ) := by
  intro r hr
  by_contra hrW
  have hsup := h.sup_conj r hrW
  have hφr : φ r = 1 := (MonoidHom.mem_ker).mp (h.ker_eq ▸ hr)
  have hcomp : φ.comp (MulAut.conj r).toMonoidHom = φ := by
    ext w
    simp [MulAut.conj_apply, hφr]
  have himg : W.map φ = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) hsup
    rwa [Subgroup.map_sup, Subgroup.map_map, hcomp, sup_idem,
      Subgroup.map_top_of_surjective φ h.surjective] at h1
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_suzuki h.one_le h.card_K
  have hx : x ∈ W.map φ := himg ▸ mem_top x
  have hy : y ∈ W.map φ := himg ▸ mem_top y
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact hxy (by rw [← map_mul, ← map_mul, h.comm_W hv hw])

theorem mem_oTwo_of_pow_eq_one (h : SzCfg T W R φ) {g : Λ} (hgR : g ∈ R) {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : g ∈ oTwo Λ := by
  set ψ := QuotientGroup.mk' (oTwo Λ) with hψ
  have hcard : ¬ 2 ∣ Nat.card (R.map ψ) := by
    rw [← relIndex_ker, hψ, QuotientGroup.ker_mk']
    exact h.not_dvd_relIndex
  set o : R.map ψ := ⟨ψ g, mem_map_of_mem ψ hgR⟩ with ho
  have h1 : o ^ 2 ^ k = 1 := Subtype.ext (by simp [ho, ← map_pow, hg])
  have hc : Nat.Coprime (2 ^ k) (Nat.card (R.map ψ)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp
      fun he => hcard (even_iff_two_dvd.mp he)))
  have h4 := Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard o)
  have h5 : o = 1 := orderOf_eq_one_iff.mp h4
  have h6 : ψ g = 1 := congrArg Subtype.val h5
  rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h6

theorem inf_ker_le_oTwo (h : SzCfg T W R φ) : W ⊓ R ≤ oTwo Λ := fun w hw =>
  h.mem_oTwo_of_pow_eq_one hw.2 (k := 1) (by rw [pow_one]; exact h.sq_W hw.1)

theorem exists_lcfgCore (h : SzCfg T W R φ) : ∃ u : Λ, u ∉ normalizer (W : Set Λ) ∧ u * u = 1 ∧
    LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u := by
  obtain ⟨x, hx⟩ := h.exists_not_mem
  have hWx : ¬ W.map (MulAut.conj x).toMonoidHom ≤ normalizer (W : Set Λ) := by
    intro hle
    apply h.normalizer_ne_top
    rw [eq_top_iff, ← h.sup_conj x hx]
    exact sup_le le_normalizer hle
  obtain ⟨u, ⟨w, hw, rfl⟩, hu⟩ := Set.not_subset.mp hWx
  have huu : (MulAut.conj x).toMonoidHom w * (MulAut.conj x).toMonoidHom w = 1 := by
    rw [← map_mul, ← pow_two, h.sq_W hw, map_one]
  refine ⟨_, hu, huu, ⟨le_top, h.elemAb, le_top, ?_, Stell.oTwo_isPGroup Λ,
    h.oTwo_le_T.trans h.T_le_normalizer, mem_top _, huu ▸ one_mem _, h.sup_conj _ hu⟩⟩
  rw [normalizer_eq_top_iff.mpr inferInstance]

end SzCfg

end CFSG.RankThree.S4Free.Stell34
