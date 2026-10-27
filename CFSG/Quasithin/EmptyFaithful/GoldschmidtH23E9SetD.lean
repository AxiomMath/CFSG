module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9SetB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9SetC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5F

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_e9Data {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hCE : IsCE1513 T M) (h5 : Ce15Six T Mc M 5) (hE9 : HasE9 T Mc M)
    (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (_h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, E9Pre T Mc M Z₁ Z₂ V₁ V₂ ∧ Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ ∧
      (∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
        IsPGroup 5 Y' ∧
        ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
        ⁅V₂, Y'⁆ = V₂ ∧ Y' ≤ Subgroup.normalizer (V₂ : Set G) ∧
        s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) ∧ V₂ ≤ s1516 T Z₁) ∧
      Nat.card Z₁ = 4 := by
  have hVZ : V154 T Mc M = VZ T M := V154_eq_VZ_of_six5 h5
  have hVe : IsElemAbelian 2 (V154 T Mc M) := by
    rw [hVZ]
    exact isElemAbelian_VZ hq hM.1.1
  obtain ⟨d, -⟩ := exists_six5Data hq hM h5 hVe
  obtain ⟨x₁, x₂, r⟩ := exists_reflData d h5 h113
  have hnot : ¬ Ce15Small T Mc M := not_ce15Small_of_six5 h5
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z₁ : Subgroup G, Z₁ = vE1516 T Mc M ⊓ d.V₁ := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂⟩ : ∃ Z₂ : Subgroup G, Z₂ = vE1516 T Mc M ⊓ d.V₂ := ⟨_, rfl⟩
  have hz₁ := r.z₁_eq hZ₁ rfl
  have hz₂ := r.z₂_eq hZ₂ rfl
  have hcard : Nat.card Z₁ = 4 := by
    rw [hz₁]
    exact r.card_z₁
  have hZ₁ne : Z₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hZ₁V₁ : Z₁ ≤ d.V₁ := hZ₁ ▸ inf_le_right
  have hZ₂V₂ : Z₂ ≤ d.V₂ := hZ₂ ▸ inf_le_right
  have hZ₁E : Z₁ ≤ vE1516 T Mc M := hZ₁ ▸ inf_le_left
  have hZ₂E : Z₂ ≤ vE1516 T Mc M := hZ₂ ▸ inf_le_left
  have hVE : vE1516 T Mc M = Z₁ ⊔ Z₂ := by
    rw [r.vE, hz₁, hz₂, ← Subgroup.map_sup]
    rfl
  have hVT : V154 T Mc M ≤ T := by
    rw [hVZ]
    exact (isTwoReducedIn_VZ hq hM.1.1).2
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    rw [hVZ]
    exact le_conjClosure _ _
  have hZE : quasithinOmegaOneCenter T ≤ vE1516 T Mc M := by
    intro z hz
    refine ⟨hZV hz, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    have hjT : j ∈ T := Setting1516.thompsonJi_le_self1516 T 1 hj
    have hzc := (quasithinOmegaOneCenter_le_center T hz).2
    exact Subgroup.mem_centralizer_iff.mp hzc j hjT
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hrank : 1 < CFSG.Open.pRank 2 T :=
    one_lt_pRank_of_card hVe hVT (by have := h5.card_eq; omega)
  have hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega)
      (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJC) inf_le_left
  obtain ⟨Y', hY, hYJ, hY5, hSY, hYc, hYa⟩ := Gen.p_sub d hZ₁V₁ hZ₁ne h19.six_autOn hJR
  have hYN₂ : Y' ≤ Subgroup.normalizer (d.V₂ : Set G) := fun y hy =>
    Gen.centralizer_le_normalizer₂ d hZ₁V₁ hZ₁ne ⟨(hY hy).1, (hY hy).2⟩
  have hSN₂ : s1516 T Z₁ ≤ Subgroup.normalizer (d.V₂ : Set G) := fun s hs =>
    Gen.centralizer_le_normalizer₂ d hZ₁V₁ hZ₁ne ⟨d.hTM hs.1, hs.2⟩
  have hVS : d.V₂ ≤ s1516 T Z₁ := by
    intro v hv
    have hvV : v ∈ V154 T Mc M := d.V₂_le_V hv
    refine ⟨hVT hvV, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have := hVe.1.is_comm.comm (⟨z, d.V₁_le_V (hZ₁V₁ hz)⟩ : ↥(V154 T Mc M)) ⟨v, hvV⟩
    exact congrArg Subtype.val this
  have hsetting : Setting1516 T Mc M Z₁ Z₂ d.V₁ d.V₂ :=
    { ce15 := Or.inr (Or.inl ⟨5, Or.inr rfl, h5⟩)
      hV := hVZ
      z1_ne := hZ₁ne
      z1_le := hZ₁E
      z2_le := hZ₂E
      vE_sup := ⟨sup_le hZ₁E hZ₂E, hVE ▸ hZE⟩
      vE_sup_small := fun h => absurd h hnot
      vE_inf := le_bot_iff.1 (d.V₁_inf_V₂ ▸ inf_le_inf hZ₁V₁ hZ₂V₂)
      caseI := Gen.caseI d hq hM rfl h15 h19 hY hYa
      caseI_small := fun h => absurd h hnot
      sylow := sylow_of_refl d r hz₁
      extra_small := fun h => absurd h hnot
      v2_le := d.V₂_le_V
      v2_comm := Gen.v2_comm d hZ₁V₁ hZ₁ne hY hY5 hYc
      z2_le_v2 := fun _ => hZ₂V₂
      decomp_seven := fun h7 => absurd h7 h5.not_seven
      decomp_other := fun _ => ⟨d.V₁_le_V, hZ₁V₁, d.V₁_sup_V₂, d.V₁_inf_V₂⟩
      swap_small := fun h => absurd h hnot
      ranks_four := fun h4 => absurd (h4.card_eq.symm.trans h5.card_eq) (by norm_num)
      ranks_six := fun _ => ⟨d.card_V₁, d.card_V₂, fun h => absurd h hnot⟩
      ranks_seven := fun h7 => absurd h7 h5.not_seven
      seven_P := fun h7 => absurd h7 h5.not_seven
      index_two := fun h => absurd h hnot
      diagonal := fun h => absurd h hnot
      index_v1 := fun h => absurd h hnot
      y_facts := fun h => absurd h hnot
      p_sub := ⟨5, Or.inr rfl, Y', hY, hYJ, hY5, hSY, hYc⟩ }
  exact ⟨Z₁, Z₂, d.V₁, d.V₂, ⟨h5, hE9, ⟨hVe, d, rfl, rfl⟩, hZ₁, hZ₂⟩, ⟨hq, hM, hCE, hsetting⟩,
    ⟨Y', hY, hYJ, hY5, hSY, hYc, hYN₂, hSN₂, hVS⟩, hcard⟩

end CFSG.Quasithin.E9
