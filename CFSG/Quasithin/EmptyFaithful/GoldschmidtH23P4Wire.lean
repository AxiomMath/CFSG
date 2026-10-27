module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Wire
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5D1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5D2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5F
public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Lemma15123FiveInputV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Concl T Mc M Z₁ L →
    Lemma15121Concl Mc Z₁ L → Ce15Six T Mc M 5 → Setting1516Extra T Mc M Z₁ →
    (∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      IsPGroup 5 Y' ∧
      ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
      ⁅V₂, Y'⁆ = V₂ ∧ Y' ≤ Subgroup.normalizer (V₂ : Set G) ∧
      s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) ∧ V₂ ≤ s1516 T Z₁) → False

variable {G : Type} [Group G] [Finite G]

section Assembly

variable {T Mc M : Subgroup G}

theorem exists_setting_six5_with_YV (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h5 : Ce15Six T Mc M 5) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h113 : Lemma15113Four T Mc M)
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut ↥(V154 T Mc M)),
      E ≤ autOn M (V154 T Mc M) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ ∧
      ∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
        IsPGroup 5 Y' ∧
        ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
        ⁅V₂, Y'⁆ = V₂ ∧ Y' ≤ Subgroup.normalizer (V₂ : Set G) ∧
        s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) ∧ V₂ ≤ s1516 T Z₁ := by
  have hVZ : V154 T Mc M = VZ T M := V154_eq_VZ_of_six5 h5
  have hVe : IsElemAbelian 2 (V154 T Mc M) := by
    rw [hVZ]
    exact isElemAbelian_VZ hq hM.1.1
  obtain ⟨d, hA₀⟩ := exists_six5Data hq hM h5 hVe
  have hnot : ¬ Ce15Small T Mc M := not_ce15Small_of_six5 h5
  have hJ : autI hVe (thompsonJi T 1) ≤ d.S.A₁ ⊔ d.S.A₂ := by
    rcases h113 with ⟨h1, -⟩ | ⟨h3, -⟩
    · rw [← hA₀]
      exact (le_of_eq h1).trans inf_le_right
    · exfalso
      have h4 := h3.1
      have h6 := h5.card_eq
      omega
  have hVT : V154 T Mc M ≤ T := by
    rw [hVZ]
    exact (isTwoReducedIn_VZ hq hM.1.1).2
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    rw [hVZ]
    exact le_conjClosure _ _
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hrank : 1 < CFSG.Open.pRank 2 T :=
    one_lt_pRank_of_card hVe hVT (by have := h5.card_eq; omega)
  have hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega)
      (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJC) inf_le_left
  have hJS : thompsonJi T 1 ≤ d.Sg := d.J_le_Sg hJ
  have hz1 : d.Z₁ ≤ vE1516 T Mc M := fun x hx =>
    ⟨d.V₁_le_V (d.Z₁_le_V₁ hx), Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.mp hx.2 j (hJS hj)⟩
  have hz2 : d.Z₂ ≤ vE1516 T Mc M := fun x hx =>
    ⟨d.V₂_le_V (d.Z₂_le_V₂ hx), Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.mp hx.2 j (hJS hj)⟩
  obtain ⟨Y', hY, hYJ, hY5, hSY, hYc, hYa⟩ := d.p_sub_aux h19.six_autOn hJR
  have hYN₁ : ∀ y ∈ Y', y ∈ Subgroup.normalizer (d.V₁ : Set G) := fun y hy =>
    d.centralizer_le_normalizer ⟨(hY hy).1, (hY hy).2⟩
  have hYN₂ : Y' ≤ Subgroup.normalizer (d.V₂ : Set G) := fun y hy =>
    d.mem_normalizer_V₂ (hY hy).1 (hYN₁ y hy)
  have hSN₂ : s1516 T d.Z₁ ≤ Subgroup.normalizer (d.V₂ : Set G) := by
    rw [d.s1516_eq]
    exact fun s hs => d.mem_normalizer_V₂ (d.hTM hs.1) hs.2
  have hVS : d.V₂ ≤ s1516 T d.Z₁ := by
    rw [d.s1516_eq]
    intro v hv
    have hvV : v ∈ V154 T Mc M := d.V₂_le_V hv
    refine ⟨hVT hvV, ?_⟩
    show v ∈ Subgroup.normalizer (d.V₁ : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcomm : ∀ y ∈ d.V₁, v * y = y * v := fun y hy => by
      have := hVe.1.is_comm.comm (⟨v, hvV⟩ : ↥(V154 T Mc M)) ⟨y, d.V₁_le_V hy⟩
      exact congrArg Subtype.val this
    constructor
    · intro hx
      have h2 : v * x * v⁻¹ = x := by rw [hcomm x hx]; group
      rw [h2]
      exact hx
    · intro hx
      have h1 := hcomm _ hx
      have h3 : v * (v * x * v⁻¹) = v * x := by rw [h1]; group
      have h2 : v * x * v⁻¹ = x := mul_left_cancel h3
      rwa [h2] at hx
  refine ⟨d.Z₁, d.Z₂, d.V₁, d.V₂, ?_, Y', hY, hYJ, hY5, hSY, hYc, hYN₂, hSN₂, hVS⟩
  refine
    { ce15 := Or.inr (Or.inl ⟨5, Or.inr rfl, h5⟩)
      hV := hVZ
      z1_ne := d.Z₁_ne_bot
      z1_le := hz1
      z2_le := hz2
      vE_sup := ⟨sup_le hz1 hz2, d.Z_le_sup hZV⟩
      vE_sup_small := fun h => absurd h hnot
      vE_inf := d.Z₁_inf_Z₂
      caseI := d.caseI hq hM rfl h15 h19 hY hYa
      caseI_small := fun h => absurd h hnot
      sylow := d.sylow
      extra_small := fun h => absurd h hnot
      s_normal := d.s_normal
      prime_o2 := d.prime_o2 hNoE9
      v2_le := d.V₂_le_V
      v2_comm := d.v2_comm hY hY5 hYc
      z2_le_v2 := fun _ => d.Z₂_le_V₂
      decomp_seven := fun h7 => absurd h7 h5.not_seven
      decomp_other := fun _ => ⟨d.V₁_le_V, d.Z₁_le_V₁, d.V₁_sup_V₂, d.V₁_inf_V₂⟩
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

end Assembly

theorem lemma15123Standalone_of_fiveV (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hNoE9 : SixFiveNoE9) (h15 : StageLemma1515CE) (h19s : StageLemma1519)
    (h113 : StageLemma15113) (h14 : StageLemma15114) (hI20 : Lemma15120InputU)
    (hI21 : Lemma15121InputU) (hFive : Lemma15123FiveInputV) : Lemma15123Standalone := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE h5
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX, hY⟩ := exists_setting_six5_with_YV hq hM h5 (h15 G T Mc M hq hM hCE)
    (h19s G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four (hNoE9 G T Mc M hq hM hCE h5)
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 as116Statement hC hSX.toExtra h15' h14' h19' h17
  have hx18 := lemma_15_1_18_extra hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19_used h37 h38 hC h18c hx18
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 : Lemma15120Concl T Mc M Z₁ L := by
    obtain ⟨h2, h3⟩ := hI20 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL hx18
    exact ⟨lemma_15_1_20_sylow h18c.four hL20,
      lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20, h2,
      fun hc => ⟨isPGroup_two_center_of_isComponentOf1515c hc h19c.one, h3 hc⟩⟩
  have h21 : Lemma15121Concl Mc Z₁ L := hI21 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hx18
  exact hFive G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h20 h21 h5 hSX.toExtra hY

end CFSG.Quasithin
