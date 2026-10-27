module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUCoreW
public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUQuot

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4PSU

open Matrix CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)
open CFSG.Open (IsElemAbelian pCoreOf)
open scoped commutatorElement

variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

theorem tvESU_param_eq {x x' : Fin n → K} {s s' : K} {hxs : TvAdm hK i j x s}
    {hxs' : TvAdm hK i j x' s'} (he : tvESU hK hij x s hxs = tvESU hK hij x' s' hxs') :
    x = x' ∧ s = s' := by
  have hm := congrArg (fun g : unitarySU 2 1 K n =>
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) he
  simp only [coe_tvESU] at hm
  have hentry : ∀ a, tvE hK i j x s a i = tvE hK i j x' s' a i := fun a =>
    congrFun (congrFun hm a) i
  refine ⟨funext fun a => ?_, ?_⟩
  · by_cases hai : a = i
    · rw [hai, hxs.1, hxs'.1]
    · by_cases haj : a = j
      · rw [haj, hxs.2.1, hxs'.2.1]
      · have h := hentry a
        have hva : tvVec (K := K) i j a = 0 := by simp [tvVec_apply, hai, haj]
        rw [tvE_apply, tvE_apply, one_apply_ne hai, hva, tvVec_left hij] at h
        simpa using h
  · have h := hentry j
    rw [tvE_apply, tvE_apply, one_apply_ne hij.symm, tvVec_left hij, tvVec_right hij, hxs.1,
      hxs'.1, hxs.2.1, hxs'.2.1, map_zero] at h
    simpa using h

theorem tvBar_dotProduct_eq_of_commute {x x' : Fin n → K} {s s' : K} (hxs : TvAdm hK i j x s)
    (hxs' : TvAdm hK i j x' s')
    (hc : tvESU hK hij x s hxs * tvESU hK hij x' s' hxs' =
      tvESU hK hij x' s' hxs' * tvESU hK hij x s hxs) :
    tvBar hK x ⬝ᵥ x' = tvBar hK x' ⬝ᵥ x := by
  rw [tvESU_mul, tvESU_mul] at hc
  have := (tvESU_param_eq hij hc).2
  linear_combination this

theorem tvTransSU_mul_self : tvTransSU hK hij * tvTransSU hK hij = 1 := by
  rw [tvTransSU, tvESU_mul, ← tvESU_zero_zero hK hij]
  exact tvESU_congr hK hij (add_zero 0)
    (by rw [tvBar_zero, zero_dotProduct, add_zero, CharTwo.add_self_eq_zero]) _ _

theorem tvTransSU_ne_one : tvTransSU hK hij ≠ 1 := by
  intro h
  rw [tvTransSU, ← tvESU_zero_zero hK hij] at h
  exact one_ne_zero (tvESU_param_eq hij h).2

theorem mem_zpowers_tvTransSU_iff {g : unitarySU 2 1 K n} :
    g ∈ Subgroup.zpowers (tvTransSU hK hij) ↔ g = 1 ∨ g = tvTransSU hK hij := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hord : orderOf (tvTransSU hK hij) = 2 :=
      orderOf_eq_prime (by rw [sq, tvTransSU_mul_self]) (tvTransSU_ne_one hij)
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem eq_zero_of_tvESU_mem_zpowers {x : Fin n → K} {s : K} {hxs : TvAdm hK i j x s}
    (h : tvESU hK hij x s hxs ∈ Subgroup.zpowers (tvTransSU hK hij)) : x = 0 := by
  rcases (mem_zpowers_tvTransSU_iff hij).1 h with h1 | h1
  · rw [← tvESU_zero_zero hK hij] at h1
    exact (tvESU_param_eq hij h1).1
  · rw [tvTransSU] at h1
    exact (tvESU_param_eq hij h1).1

theorem tvESU_zero_mem_zpowers {t : K} (ht : TvAdm hK i j 0 t) :
    tvESU hK hij 0 t ht ∈ Subgroup.zpowers (tvTransSU hK hij) := by
  rcases eq_zero_or_eq_one_of_tvAdm_zero ht with rfl | rfl
  · rw [tvESU_zero_zero]
    exact one_mem _
  · exact Subgroup.mem_zpowers _

theorem conj_dSU_tvESU {k l : Fin n} (hkl : k ≠ l) (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) {x : Fin n → K} {s : K} (hxs : TvAdm hK i j x s) :
    ∃ hxs' : TvAdm hK i j (diagonal (dKL k l) *ᵥ x) s,
      dSU hkl * tvESU hK hij x s hxs * (dSU hkl)⁻¹ =
        tvESU hK hij (diagonal (dKL k l) *ᵥ x) s hxs' :=
  conj_tvESU hK hij (dSU_mem_unitaryBlock hkl hk hl) hxs

theorem permSU_threeCycle_mem_centralizer {k l p : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hl : l ∈ ({i, j}ᶜ : Finset (Fin n))) (hp : p ∈ ({i, j}ᶜ : Finset (Fin n))) :
    permSU hK (Equiv.swap k l * Equiv.swap k p) ∈ Subgroup.centralizer {tvTransSU hK hij} :=
  unitaryBlock_le_centralizer_tvTransSU hK hij
    (permSU_mem_unitaryBlock (swap_mul_swap_fix hk hl hp).1 (swap_mul_swap_fix hk hl hp).2)

theorem pCoreOf_centralizer_le_tvRadical (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) :
    pCoreOf 2 (Subgroup.centralizer {tvTransSU hK hij}) ≤ tvRadical hK hij := by
  have hN := le_normalizer_pCoreOf_two (Subgroup.centralizer {tvTransSU hK hij})
  exact le_tvRadical_of_isPGroup hij hJ (pCoreOf_two_le _) (isPGroup_pCoreOf_two _)
    (fun k hk l hl hkl => hN (dSU_mem_centralizer hij hkl hk hl))
    (fun k hk l hl p hp _ _ _ => hN (permSU_threeCycle_mem_centralizer hij hk hl hp))

theorem dKL_twice_eq {k l p : Fin n} (hkl : k ≠ l) (hkp : k ≠ p) (hlp : l ≠ p) (x : Fin n → K) :
    diagonal (dKL k p) *ᵥ (diagonal (dKL k l) *ᵥ x + x) + (diagonal (dKL k l) *ᵥ x + x) =
      Pi.single k (ω * x k) := by
  obtain ⟨-, -, h1k, h1l, h1o⟩ := diagKL_spec hkl
  obtain ⟨-, -, h2k, h2p, h2o⟩ := diagKL_spec hkp
  ext a
  simp only [Pi.add_apply, mulVec_diagonal, Pi.single_apply]
  by_cases hak : a = k
  · rw [if_pos hak, hak, h1k, h2k]
    linear_combination (x k) * omega_sq + add_self_K (ω * x k + x k)
  · rw [if_neg hak]
    by_cases hal : a = l
    · rw [hal, h1l, h2o l (fun h => hkl h.symm) hlp, one_mul]
      exact add_self_K _
    · by_cases hap : a = p
      · rw [hap, h2p, h1o p (fun h => hkp h.symm) (fun h => hlp h.symm), one_mul]
        linear_combination (ω ^ 2 + 1) * add_self_K (x p)
      · rw [h1o a hak hal, h2o a hak hap, one_mul, one_mul]
        linear_combination 2 * add_self_K (x a)

theorem le_zpowers_of_commute (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    {F : Subgroup (unitarySU 2 1 K n)} (hFR : F ≤ tvRadical hK hij)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hD : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ hkl : k ≠ l,
      ∀ f ∈ F, dSU hkl * f * (dSU hkl)⁻¹ ∈ F) :
    F ≤ Subgroup.zpowers (tvTransSU hK hij) := by
  have hstep : ∀ {k l : Fin n} (hkl : k ≠ l), k ∈ ({i, j}ᶜ : Finset (Fin n)) →
      l ∈ ({i, j}ᶜ : Finset (Fin n)) → ∀ {x : Fin n → K} {s : K} (hxs : TvAdm hK i j x s),
      tvESU hK hij x s hxs ∈ F →
      ∃ (s' : K) (hxs' : TvAdm hK i j (diagonal (dKL k l) *ᵥ x + x) s'),
        tvESU hK hij (diagonal (dKL k l) *ᵥ x + x) s' hxs' ∈ F := by
    intro k l hkl hk hl x s hxs hf
    obtain ⟨hxs₁, hconj⟩ := conj_dSU_tvESU hij hkl hk hl hxs
    have hg := mul_mem (hD k hk l hl hkl _ hf) (inv_mem hf)
    rw [hconj, tvESU_inv, tvESU_mul] at hg
    exact ⟨_, _, hg⟩
  intro f hf
  obtain ⟨x, s, hxs, rfl⟩ := exists_eq_tvESU_of_mem_tvRadical hK hij (hFR hf)
  suffices hx0 : x = 0 by
    subst hx0
    exact tvESU_zero_mem_zpowers hij hxs
  by_contra hx0
  obtain ⟨k, hk0⟩ := Function.ne_iff.mp hx0
  have hki : k ≠ i := fun h => hk0 (by rw [h, hxs.1]; rfl)
  have hkj : k ≠ j := fun h => hk0 (by rw [h, hxs.2.1]; rfl)
  have hkJ : k ∈ ({i, j}ᶜ : Finset (Fin n)) := mem_compl_of_ne hki hkj
  obtain ⟨l, hl, hlk⟩ := Finset.exists_mem_ne (by omega : 1 < ({i, j}ᶜ : Finset (Fin n)).card) k
  have hkl : k ≠ l := fun h => hlk h.symm
  have hcardk : 1 < (({i, j}ᶜ : Finset (Fin n)).erase k).card := by
    rw [Finset.card_erase_of_mem hkJ]
    omega
  obtain ⟨p, hp, hpl⟩ := Finset.exists_mem_ne hcardk l
  have hpk : p ≠ k := Finset.ne_of_mem_erase hp
  have hpJ : p ∈ ({i, j}ᶜ : Finset (Fin n)) := Finset.mem_of_mem_erase hp
  have hkp : k ≠ p := fun h => hpk h.symm
  have hlp : l ≠ p := fun h => hpl h.symm
  obtain ⟨s₁, hy, hyF⟩ := hstep hkl hkJ hl hxs hf
  obtain ⟨s₂, hz, hzF⟩ := hstep hkp hkJ hpJ hy hyF
  obtain ⟨hw, hwconj⟩ := conj_dSU_tvESU hij hkl hkJ hl hz
  have hwF := hD k hkJ l hl hkl _ hzF
  rw [hwconj] at hwF
  have key := tvBar_dotProduct_eq_of_commute hij hz hw (hF _ hzF _ hwF)
  rw [dKL_twice_eq hkl hkp hlp] at key
  set c : K := ω * x k with hc
  have hDc : diagonal (dKL k l) *ᵥ Pi.single k c = Pi.single k (ω * c) := by
    ext a
    rw [mulVec_diagonal, Pi.single_apply, Pi.single_apply]
    split_ifs with hak
    · rw [hak, (diagKL_spec hkl).2.2.1]
    · rw [mul_zero]
  rw [hDc, tvBar_single, tvBar_single, single_dotProduct, single_dotProduct, Pi.single_eq_same,
    Pi.single_eq_same, bar_apply_K, bar_apply_K] at key
  have hc3 : c ^ 3 = 0 := by
    linear_combination (-1 : K) * key - c ^ 3 * omega_sq
  have hc0 : c = 0 := pow_eq_zero_iff (by norm_num) |>.1 hc3
  rw [hc] at hc0
  exact hk0 ((mul_eq_zero.1 hc0).resolve_left omega_ne_zero)

theorem eq_zpowers_of_isElemAbelian (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    {E : Subgroup (unitarySU 2 1 K n)} (hE : IsElemAbelian 2 E)
    (hzE : Subgroup.zpowers (tvTransSU hK hij) ≤ E)
    (hEC : E ≤ Subgroup.centralizer {tvTransSU hK hij})
    (hW : ∀ x ∈ coreW hij, ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    E = Subgroup.zpowers (tvTransSU hK hij) := by
  have hN : ∀ x ∈ coreW hij, x ∈ Subgroup.normalizer (E : Set (unitarySU 2 1 K n)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨hW x hx e, fun h => ?_⟩
    have := hW x⁻¹ (inv_mem hx) _ h
    simpa [mul_assoc] using this
  have hP2 : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 g g.2)⟩
  have hER : E ≤ tvRadical hK hij := le_tvRadical_of_isPGroup hij hJ hEC hP2
    (fun k hk l hl hkl => hN _ (dSU_mem_coreW hij hJ hk hl hkl))
    (fun k hk l hl p hp hkl hkp hlp =>
      hN _ (permSU_threeCycle_mem_coreW hij hJ hk hl hp hkl hkp hlp))
  refine le_antisymm (le_zpowers_of_commute hij hJ hER (fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) ?_) hzE
  intro k hk l hl hkl f hf
  exact hW _ (dSU_mem_coreW hij hJ hk hl hkl) f hf

theorem mem_zpowers_of_forall_commutator (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    {s : unitarySU 2 1 K n} (hs : s ∈ tvRadical hK hij)
    (hc : ∀ x ∈ coreW hij, x⁻¹ * s⁻¹ * x * s ∈ Subgroup.zpowers (tvTransSU hK hij)) :
    s ∈ Subgroup.zpowers (tvTransSU hK hij) := by
  obtain ⟨y, t, hyt, rfl⟩ := exists_eq_tvESU_of_mem_tvRadical hK hij hs
  suffices hy0 : y = 0 by
    subst hy0
    exact tvESU_zero_mem_zpowers hij hyt
  have hω1 : ω + 1 ≠ 0 := by
    rw [← omega_sq]
    exact pow_ne_zero 2 omega_ne_zero
  funext a
  rcases eq_or_eq_or_mem_compl i j a with rfl | rfl | haJ
  · exact hyt.1
  · exact hyt.2.1
  obtain ⟨l, hl, hla⟩ := Finset.exists_mem_ne (by omega : 1 < ({i, j}ᶜ : Finset (Fin n)).card) a
  have hal : a ≠ l := fun h => hla h.symm
  have hx := hc _ (inv_mem (dSU_mem_coreW hij hJ haJ hl hal))
  rw [inv_inv] at hx
  obtain ⟨hyt', hconj⟩ := conj_dSU_tvESU hij hal haJ hl hyt
  have e : dSU hal * (tvESU hK hij y t hyt)⁻¹ * (dSU hal)⁻¹ * tvESU hK hij y t hyt =
      (dSU hal * tvESU hK hij y t hyt * (dSU hal)⁻¹)⁻¹ * tvESU hK hij y t hyt := by
    group
  rw [e, hconj, tvESU_inv, tvESU_mul] at hx
  have h0 := congrFun (eq_zero_of_tvESU_mem_zpowers hij hx) a
  rw [Pi.add_apply, mulVec_diagonal, (diagKL_spec hal).2.2.1, Pi.zero_apply] at h0
  have h1 : (ω + 1) * y a = 0 := by linear_combination h0
  exact (mul_eq_zero.1 h1).resolve_left hω1

theorem normalizer_zpowers_tvTransSU :
    Subgroup.normalizer (Subgroup.zpowers (tvTransSU hK hij) : Set (unitarySU 2 1 K n)) =
      Subgroup.centralizer {tvTransSU hK hij} := by
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rcases (mem_zpowers_tvTransSU_iff hij).1 ((h _).1 (Subgroup.mem_zpowers _)) with h1 | h1
    · exfalso
      apply tvTransSU_ne_one hij
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    · calc g * tvTransSU hK hij = g * tvTransSU hK hij * g⁻¹ * g := by group
        _ = tvTransSU hK hij * g := by rw [h1]
  · intro hg x
    have hcomm : ∀ y : unitarySU 2 1 K n, y = 1 ∨ y = tvTransSU hK hij → g * y * g⁻¹ = y := by
      rintro y (rfl | rfl)
      · group
      · rw [hg, mul_inv_cancel_right]
    have hcomm' : ∀ y : unitarySU 2 1 K n, y = 1 ∨ y = tvTransSU hK hij → g⁻¹ * y * g = y := by
      rintro y (rfl | rfl)
      · group
      · calc g⁻¹ * tvTransSU hK hij * g = g⁻¹ * (tvTransSU hK hij * g) := by group
          _ = g⁻¹ * (g * tvTransSU hK hij) := by rw [hg]
          _ = tvTransSU hK hij := by group
    constructor
    · intro hx
      rw [hcomm x ((mem_zpowers_tvTransSU_iff hij).1 hx)]
      exact hx
    · intro hx
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, hcomm' _ ((mem_zpowers_tvTransSU_iff hij).1 hx)]
      exact hx

theorem coreW_spec (hJ : 3 ≤ ({i, j}ᶜ : Finset (Fin n)).card) :
    coreW hij ≤
        ⁅⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆,
          ⁅Subgroup.centralizer {tvTransSU hK hij}, Subgroup.centralizer {tvTransSU hK hij}⁆⁆ ∧
      CFSG.GroupTheory.oddOrderClosure (coreW hij) = coreW hij ∧
      pCoreOf 2 (Subgroup.normalizer
        (Subgroup.zpowers (tvTransSU hK hij) : Set (unitarySU 2 1 K n))) ≤ coreW hij ∧
      (∀ E : Subgroup (unitarySU 2 1 K n), IsElemAbelian 2 E →
        Subgroup.zpowers (tvTransSU hK hij) ≤ E → E ≤ Subgroup.centralizer {tvTransSU hK hij} →
        (∀ x ∈ coreW hij, ∀ e ∈ E, x * e * x⁻¹ ∈ E) → E = Subgroup.zpowers (tvTransSU hK hij)) ∧
      (∀ s ∈ pCoreOf 2 (Subgroup.normalizer
          (Subgroup.zpowers (tvTransSU hK hij) : Set (unitarySU 2 1 K n))),
        (∀ x ∈ coreW hij, x⁻¹ * s⁻¹ * x * s ∈ Subgroup.zpowers (tvTransSU hK hij)) →
          s ∈ Subgroup.zpowers (tvTransSU hK hij)) := by
  rw [normalizer_zpowers_tvTransSU hij]
  exact ⟨coreW_le hij, oddOrderClosure_coreW hij,
    (pCoreOf_centralizer_le_tvRadical hij hJ).trans (tvRadical_le_coreW hij hJ),
    fun E hE hzE hEC hW => eq_zpowers_of_isElemAbelian hij hJ hE hzE hEC hW,
    fun s hs hc => mem_zpowers_of_forall_commutator hij hJ
      (pCoreOf_centralizer_le_tvRadical hij hJ hs) hc⟩

end CFSG.RankThree.GF2n.Stroth78.Sec4PSU
