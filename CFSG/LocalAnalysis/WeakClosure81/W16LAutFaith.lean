module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {X : Type} [Group X] [Finite X]

private lemma w16l_map_conjSubgroup (α : MulAut X) (A : Subgroup X) (g : X) :
    (conjSubgroup A g).map α.toMonoidHom =
      conjSubgroup (A.map α.toMonoidHom) (α g) := by
  ext y
  simp only [Subgroup.mem_map_equiv, mem_conjSubgroup_iff, map_mul, map_inv,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private lemma w16l_mem_normalizer_conj {A : Subgroup X} {g w : X} :
    g * w * g⁻¹ ∈ Subgroup.normalizer (A : Set X) ↔
      w ∈ Subgroup.normalizer (conjSubgroup A g : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    convert this using 2 <;> group
  · intro h y
    have := h (g⁻¹ * y * g)
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff] at this
    convert this using 2 <;> group

private lemma w16l_conjSubgroup_mul_inv_eq {A : Subgroup X} {g h : X}
    (hgh : conjSubgroup A h = conjSubgroup A g) : conjSubgroup A (h * g⁻¹) = A := by
  rw [← conjSubgroup_conjSubgroup A h g⁻¹, hgh, conjSubgroup_conjSubgroup A g g⁻¹,
    mul_inv_cancel, conjSubgroup_one]

private lemma w16l_ne_bot_of_card_two_pow {Y : Subgroup X} {n : ℕ} (hn : 1 < n)
    (hY : Nat.card Y = 2 ^ n) : Y ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at hY
  have hne : 2 ^ n ≠ 1 := by
    have := one_lt_pow' (by norm_num : (1 : ℕ) < 2) (by omega : n ≠ 0)
    omega
  exact hne hY.symm

theorem mulAut_eq_one_of_normalizes_conj (hperf : commutator X = ⊤)
    (hsimp : ∀ N : Subgroup X, N.Normal → N ≤ Subgroup.center X ∨ N = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center X))) {Y : Subgroup X} (hY2 : IsPGroup 2 Y)
    (hY1 : Y ≠ ⊥) (α : MulAut X)
    (hα : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  haveI : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI := h
    exact hY1 (Subgroup.eq_bot_of_subsingleton Y)
  have hYnotNormal : ¬ Y.Normal := by
    intro hYN
    rcases hsimp Y hYN with hYZ | hYtop
    · obtain ⟨k, hk⟩ := hY2.exists_card_eq
      have hoddY : Odd (Nat.card Y) :=
        hodd.of_dvd_nat (Subgroup.card_dvd_of_le hYZ)
      have hoddk : Odd (2 ^ k) := by rwa [hk] at hoddY
      have hk0 : k = 0 := by
        by_contra hk0
        have : Odd 2 := (Nat.odd_pow_iff hk0).1 hoddk
        norm_num at this
      have hcard1 : Nat.card Y = 1 := by rw [hk, hk0, pow_zero]
      exact hY1 ((Subgroup.eq_bot_iff_card Y).2 hcard1)
    · have htop2 : IsPGroup 2 (⊤ : Subgroup X) := by rwa [← hYtop]
      have hX2 : IsPGroup 2 X := htop2.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent X := hX2.isNilpotent
      haveI : Group.IsPerfect X := ⟨hperf⟩
      exact Group.IsPerfect.not_isNilpotent X hX2.isNilpotent
  let N : X → Subgroup X := fun x => Subgroup.normalizer (conjSubgroup Y x : Set X)
  let K : Subgroup X := ⨅ x, N x
  have hKleN1 : K ≤ N 1 := iInf_le N 1
  have hN1ne : N 1 ≠ ⊤ := by
    intro htop
    exact hYnotNormal
      (Subgroup.normalizer_eq_top_iff.mp (by simpa [N, conjSubgroup_one] using htop))
  have hKne : K ≠ ⊤ := fun htop => hN1ne (top_le_iff.mp (htop ▸ hKleN1))
  have hKnormal : K.Normal := by
    refine ⟨fun w hw g => ?_⟩
    simp only [K, N, Subgroup.mem_iInf] at hw ⊢
    intro x
    have hx : w ∈ Subgroup.normalizer (conjSubgroup (conjSubgroup Y x) g : Set X) := by
      simpa [conjSubgroup_conjSubgroup] using hw (x * g)
    exact (w16l_mem_normalizer_conj (A := conjSubgroup Y x) (g := g) (w := w)).mpr hx
  have hKZ : K ≤ Subgroup.center X := by
    rcases hsimp K hKnormal with h | h
    · exact h
    · exact absurd h hKne
  have hcK : ∀ g : X, α g * g⁻¹ ∈ K := by
    intro g
    simp only [K, N, Subgroup.mem_iInf]
    intro x
    let W : Subgroup X := conjSubgroup Y x
    have hW : W.map α.toMonoidHom = W := hα x
    have hWg : (conjSubgroup W g).map α.toMonoidHom = conjSubgroup W g := by
      have := hα (x * g)
      simpa [W, conjSubgroup_conjSubgroup] using this
    have hEq : conjSubgroup W (α g) = conjSubgroup W g := by
      have h1 : (conjSubgroup W g).map α.toMonoidHom =
          conjSubgroup (W.map α.toMonoidHom) (α g) := w16l_map_conjSubgroup α W g
      rw [hWg, hW] at h1
      exact h1.symm
    exact (conjSubgroup_eq_iff_mem_normalizer).1 (w16l_conjSubgroup_mul_inv_eq hEq)
  let c : X →* Subgroup.center X :=
    { toFun := fun g => ⟨α g * g⁻¹, hKZ (hcK g)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Subtype.ext
        have hch : α h * h⁻¹ ∈ Subgroup.center X := hKZ (hcK h)
        have hcomm : g⁻¹ * (α h * h⁻¹) = (α h * h⁻¹) * g⁻¹ :=
          Subgroup.mem_center_iff.1 hch g⁻¹
        show α (g * h) * (g * h)⁻¹ = (α g * g⁻¹) * (α h * h⁻¹)
        rw [map_mul, mul_inv_rev]
        calc α g * α h * (h⁻¹ * g⁻¹) = α g * ((α h * h⁻¹) * g⁻¹) := by group
          _ = α g * (g⁻¹ * (α h * h⁻¹)) := by rw [← hcomm]
          _ = (α g * g⁻¹) * (α h * h⁻¹) := by group }
  have hker : commutator X ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hperf] at hker
  ext g
  have h1 : c g = 1 := hker (Subgroup.mem_top g)
  have h2 : α g * g⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.1 h2

private lemma w16l_simple_facts {Y : Subgroup X} {n : ℕ} (hn : 1 < n)
    (hY : Nat.card Y = 2 ^ n) (hS : IsSimpleGroup X) :
    (∃ a b : X, a * b ≠ b * a) ∧ commutator X = ⊤ ∧ Subgroup.center X = ⊥ := by
  haveI := hS.toNontrivial
  have hna : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    haveI : IsMulCommutative X := by
      rw [isMulCommutative_iff]
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    have hpX : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).1 hS
    have hdvd : Nat.card Y ∣ Nat.card X := by
      simpa using (Subgroup.card_dvd_of_le (H := Y) (K := (⊤ : Subgroup X)) le_top)
    have h2 : 2 ∣ Nat.card X := by
      have h2Y : 2 ∣ Nat.card Y := by
        rw [hY]
        exact dvd_pow_self 2 (by omega : n ≠ 0)
      exact h2Y.trans hdvd
    have hp2 : Nat.card X = 2 := by
      rcases hpX.eq_one_or_self_of_dvd 2 h2 with h1 | h1
      · norm_num at h1
      · exact h1.symm
    have h4 : 4 ∣ Nat.card X := by
      have h4Y : 4 ∣ Nat.card Y := by
        rw [hY]
        exact pow_dvd_pow 2 (by omega : 2 ≤ n)
      exact h4Y.trans hdvd
    rw [hp2] at h4
    norm_num at h4
  have hperf : commutator X = ⊤ := by
    haveI : (commutator X).Normal := by
      rw [show commutator X = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ from
        _root_.commutator_def X]
      infer_instance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      have hcomm : IsMulCommutative X := (commutator_eq_bot_iff X).mp h
      obtain ⟨a, b, hab⟩ := hna
      exact hab (isMulCommutative_iff.mp hcomm a b)
    · exact h
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hc : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr h
      rw [hperf] at hc
      exact top_ne_bot hc
  exact ⟨hna, hperf, hZ⟩

private lemma w16l_faith_of_simple {Y : Subgroup X} {n : ℕ} (hn : 1 < n)
    (hY : Nat.card Y = 2 ^ n) (hYe : IsElemAbelian 2 Y) (hS : IsSimpleGroup X)
    (α : MulAut X)
    (hα : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  obtain ⟨-, hperf, hZ⟩ := w16l_simple_facts hn hY hS
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hsimp : ∀ N : Subgroup X, N.Normal → N ≤ Subgroup.center X ∨ N = ⊤ := by
    intro N hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact Or.inl (by rw [h]; exact bot_le)
    · exact Or.inr h
  exact mulAut_eq_one_of_normalizes_conj hperf hsimp hodd hYe.isPGroup
    (w16l_ne_bot_of_card_two_pow hn hY) α hα

theorem autRank166_faith_psl {Y : Subgroup X} {n : ℕ} (hn : 1 < n) (hY : Nat.card Y = 2 ^ n)
    (hYe : IsElemAbelian 2 Y) (hX : CFSG.Quasithin.IsPSL 2 2 n X) (α : MulAut X)
    (hα : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  exact w16l_faith_of_simple hn hY hYe (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n hX).2
    α hα

theorem autRank166_faith_sz {Y : Subgroup X} {n : ℕ} (hn : 1 < n) (hY : Nat.card Y = 2 ^ n)
    (hYe : IsElemAbelian 2 Y) (hX : CFSG.Quasithin.IsSz n X) (α : MulAut X)
    (hα : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  exact w16l_faith_of_simple hn hY hYe (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hX).2
    α hα

theorem autRank166_faith_u3 {Y : Subgroup X} {n : ℕ} (hn : 1 < n) (hY : Nat.card Y = 2 ^ n)
    (hYe : IsElemAbelian 2 Y) (hX : IsU3Shape X n) (α : MulAut X)
    (hα : ∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) : α = 1 := by
  haveI hS : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hX.2.1
  have hodd : Odd (Nat.card (Subgroup.center X)) :=
    Odd.of_dvd_nat (by norm_num : Odd 3) hX.2.2
  have hsimp : ∀ N : Subgroup X, N.Normal → N ≤ Subgroup.center X ∨ N = ⊤ := by
    intro N hN
    haveI := hN
    let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
    haveI hNmap : (N.map π).Normal :=
      hN.map π (QuotientGroup.mk'_surjective (N := Subgroup.center X))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
    · left
      have hle : N ≤ π.ker := (Subgroup.map_eq_bot_iff (f := π) (H := N)).1 hbot
      rwa [QuotientGroup.ker_mk'] at hle
    · right
      have hsup : N ⊔ Subgroup.center X = ⊤ := by
        have h := QuotientGroup.comap_map_mk' (Subgroup.center X) N
        rw [htop] at h
        simpa [sup_comm] using h.symm
      have hcomm : ⁅(N ⊔ Subgroup.center X), (N ⊔ Subgroup.center X)⁆ ≤ N := by
        rw [Subgroup.commutator_sup_left (N ⊔ Subgroup.center X) N (Subgroup.center X),
          Subgroup.commutator_sup_right N (Subgroup.center X) N,
          Subgroup.commutator_sup_right N (Subgroup.center X) (Subgroup.center X)]
        rw [Subgroup.commutator_center_right, Subgroup.commutator_center_left,
          Subgroup.commutator_center_left]
        simp only [sup_bot_eq, bot_sup_eq]
        exact Subgroup.commutator_le_left N N
      have htopN : (⊤ : Subgroup X) ≤ N := by
        calc (⊤ : Subgroup X) = commutator X := hX.1.symm
          _ = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := _root_.commutator_def X
          _ = ⁅(N ⊔ Subgroup.center X), (N ⊔ Subgroup.center X)⁆ := by rw [← hsup]
          _ ≤ N := hcomm
      exact top_le_iff.mp htopN
  exact mulAut_eq_one_of_normalizes_conj hX.1 hsimp hodd hYe.isPGroup
    (w16l_ne_bot_of_card_two_pow hn hY) α hα

end CFSG.LocalAnalysis.WeakClosure81

end
