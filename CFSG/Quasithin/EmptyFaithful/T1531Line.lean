module

public import CFSG.Quasithin.EmptyFaithful.T1531Gold
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Conj

variable {G : Type} [Group G]

theorem conjSubgroup_eq_of_mem_normalizer {V : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) : conjSubgroup V m = V := by
  ext x
  rw [mem_conjSubgroup_iff]
  exact (Subgroup.mem_normalizer_iff.mp hm x).symm

theorem conjSubgroup_le_of_mem {V M E : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    {m : G} (hm : m ∈ M) (hEV : E ≤ V) : conjSubgroup E m ≤ V :=
  calc conjSubgroup E m ≤ conjSubgroup V m := E3.conjSubgroup_mono_left m hEV
    _ = V := conjSubgroup_eq_of_mem_normalizer (hMV hm)

theorem not_normalizer_conj_le {M E : Subgroup G} {m : G} (hm : m ∈ M)
    (h : ¬ Subgroup.normalizer (E : Set G) ≤ M) :
    ¬ Subgroup.normalizer (conjSubgroup E m : Set G) ≤ M := by
  intro hle
  apply h
  have h1 : conjSubgroup (Subgroup.normalizer (conjSubgroup E m : Set G)) m⁻¹ =
      Subgroup.normalizer (E : Set G) := by
    rw [E3.conjSubgroup_normalizer, E3.conjSubgroup_conj_inv]
  have h2 : conjSubgroup M m⁻¹ = M :=
    conjSubgroup_eq_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hm))
  calc Subgroup.normalizer (E : Set G)
      = conjSubgroup (Subgroup.normalizer (conjSubgroup E m : Set G)) m⁻¹ := h1.symm
    _ ≤ conjSubgroup M m⁻¹ := E3.conjSubgroup_mono_left _ hle
    _ = M := h2

theorem exists_conj_isSylowTwoOf [Finite G] {T M : Subgroup G} (E : Subgroup G)
    (hT : IsSylowTwoOf T M) :
    ∃ m ∈ M, IsSylowTwoOf (T ⊓ Subgroup.normalizer (conjSubgroup E m : Set G))
      (M ⊓ Subgroup.normalizer (conjSubgroup E m : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : (⊥ : Subgroup G) ≤
    M ⊓ Subgroup.normalizer (E : Set G)) IsPGroup.of_bot
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hT' : IsSylowIn 2 T M := hT
  obtain ⟨h, hh, hPle⟩ := E3.exists_le_conj_of_isSylowIn hT' hPM hP.isPGroup
  refine ⟨h⁻¹, M.inv_mem hh, ?_⟩
  have hMc : conjSubgroup M h⁻¹ = M :=
    conjSubgroup_eq_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hh))
  have hN' : conjSubgroup (M ⊓ Subgroup.normalizer (E : Set G)) h⁻¹ =
      M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G) := by
    rw [E3.conjSubgroup_inf, hMc, E3.conjSubgroup_normalizer]
  have hP'le : conjSubgroup P h⁻¹ ≤ M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G) := by
    rw [← hN']
    exact E3.conjSubgroup_mono_left h⁻¹ hP.le
  have hP'dvd : ¬ 2 ∣ (conjSubgroup P h⁻¹).relIndex
      (M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G)) := by
    rw [← hN', E3.relIndex_conjSubgroup]
    exact hP.not_dvd_relIndex
  have hPT : conjSubgroup P h⁻¹ ≤ T := by
    have := E3.conjSubgroup_mono_left h⁻¹ hPle
    rwa [E3.conjSubgroup_conj_inv] at this
  have hQ : conjSubgroup P h⁻¹ ≤ T ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G) :=
    le_inf hPT (hP'le.trans inf_le_right)
  have hQN : T ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G) ≤
      M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G) := inf_le_inf_right _ hT.1
  refine ⟨hQN, (hT.2.1).to_le inf_le_left, ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hQ hQN
  have hdvd : (T ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G)) ∣
      (conjSubgroup P h⁻¹).relIndex (M ⊓ Subgroup.normalizer (conjSubgroup E h⁻¹ : Set G)) :=
    Dvd.intro_left _ hmul
  exact fun h2 => hP'dvd (h2.trans hdvd)

end Conj

section RParam

variable {G : Type} [Group G]

theorem exists_of_rParam_eq_two {V : Subgroup G} (h : E3.rParam V = 2) :
    ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      E3.mQuot V U = 2 := by
  by_contra hno
  push Not at hno
  have h3 : (3 : ℕ∞) ≤ E3.rParam V := by
    refine le_iInf₂ fun U hU => ?_
    have h2 : (2 : ℕ∞) ≤ (E3.mQuot V U : ℕ∞) := h ▸ E3.rParam_le_mQuot hU.1 hU.2
    have hne : (E3.mQuot V U : ℕ∞) ≠ 2 := by exact_mod_cast hno U hU.1 hU.2
    have hlt : (2 : ℕ∞) < (E3.mQuot V U : ℕ∞) := lt_of_le_of_ne h2 (Ne.symm hne)
    have := (ENat.add_one_le_iff (by simp : (2 : ℕ∞) ≠ ⊤)).mpr hlt
    have e : (2 : ℕ∞) + 1 = 3 := by norm_num
    rwa [e] at this
  rw [h] at h3
  norm_num at h3

end RParam

section Line

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_line_aux (c : Ctx153 G T Mc M V₁ V₂ t) (hr : Res15365Two T M) :
    ∃ E : Subgroup G, E ≤ VZ T M ∧ Nat.card E = 4 ∧
      ¬ Subgroup.normalizer (E : Set G) ≤ M := by
  obtain ⟨U, hUV, hUC, hm⟩ := exists_of_rParam_eq_two hr
  have hVp : IsPGroup 2 (VZ T M) := B2F.isPGroup_of_isElemAbelian c.hyp.elemAbelian
  have hcard : Nat.card (VZ T M) = 2 ^ (E3.mQuot (VZ T M) U) * Nat.card U :=
    E3.card_eq_two_pow_mul hVp hUV
  have h16 := c.hyp.card_VZ
  rw [hm, h16] at hcard
  have hU4 : Nat.card U = 4 := by norm_num at hcard; omega
  refine ⟨U, hUV, hU4, fun hle => hUC ?_⟩
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := c.hyp.isHv_of_inM' c.hyp.inM
  rw [← hHv]
  exact (Subgroup.centralizer_le_normalizer (U : Set G)).trans hle

omit [Finite G] in
theorem lineData153_of (r46 : Res15346 T M V₁ V₂) {E : Subgroup G} (hEV : E ≤ VZ T M)
    (hc : Nat.card E = 4) (hnot : ¬ Subgroup.normalizer (E : Set G) ≤ M)
    (hc16 : Nat.card (VZ T M) = 16)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (E : Set G))
      (M ⊓ Subgroup.normalizer (E : Set G))) : LineData153 T M V₁ V₂ E := by
  have hbot : ⊥ < E := by
    refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    rw [hb, Subgroup.card_bot] at hc
    omega
  have hlt : E < VZ T M := lt_of_le_of_ne hEV fun e => by
    rw [e, hc16] at hc
    omega
  exact ⟨hEV, hc, r46.totSingular_of_normalizer E hEV hbot hlt hnot, hnot, hsyl⟩

theorem exists_lineData153 (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (hr : Res15365Two T M) : ∃ E : Subgroup G, LineData153 T M V₁ V₂ E := by
  obtain ⟨E₀, hV, hc, hnot⟩ := exists_line_aux c hr
  obtain ⟨m, hm, hsyl⟩ := exists_conj_isSylowTwoOf E₀ c.hyp.isSylowTwoOf
  refine ⟨conjSubgroup E₀ m, lineData153_of r46 ?_ ?_ ?_ c.hyp.card_VZ hsyl⟩
  · exact conjSubgroup_le_of_mem c.hyp.le_normalizer hm hV
  · rw [E3.card_conjSubgroup]; exact hc
  · exact not_normalizer_conj_le hm hnot

end Line

end CFSG.Quasithin
