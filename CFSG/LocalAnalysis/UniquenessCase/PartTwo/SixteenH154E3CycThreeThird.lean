module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeThird_isPGroup_two_of_le {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) : IsPGroup 2 U := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using hV.2 g.1 (hUV g.2))⟩

private theorem s16h_e3_CycThreeThird_wConj_le_v (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) : X ≤ V := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hW : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp125.pairFacts.le_normalizer hm)
  exact (Subgroup.map_mono hW).trans (le_of_eq hVm)

private theorem s16h_e3_CycThreeThird_exists_mul_mem_v0 {V₀ V A C : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV0V : V₀ ≤ V) (hAV : A ≤ V) (hCV : C ≤ V)
    (hC0 : C ≤ V₀) {w : G} (hw : w ∈ A ⊔ C) : ∃ a ∈ A, w * a⁻¹ ∈ V₀ := by
  haveI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  have hwV : w ∈ V := (sup_le hAV hCV) hw
  have hmem : (⟨w, hwV⟩ : ↥V) ∈ (A.subgroupOf V) ⊔ (C.subgroupOf V) := by
    rw [← Subgroup.subgroupOf_sup hAV hCV]
    exact Subgroup.mem_subgroupOf.mpr hw
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
  have hzC : (z : G) ∈ C := Subgroup.mem_subgroupOf.mp hz
  have hyz' : (y : G) * (z : G) = w := by
    simpa using congrArg (fun t : ↥V => (t : G)) hyz
  have hcomm : (y : G) * (z : G) = (z : G) * (y : G) :=
    Subgroup.mul_comm_of_mem_isMulCommutative (H := V) y.2 z.2
  have hw_eq : w * (y : G)⁻¹ = (z : G) := by
    rw [← hyz', hcomm]
    group
  exact ⟨(y : G), hyA, by rw [hw_eq]; exact hC0 hzC⟩

private theorem s16h_e3_CycThreeThird_cElt_le_of_mul_mem_v0 {M V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV0V : V₀ ≤ V) (hMV : M ≤ normalizer (V : Set G))
    {u w : G} (huV : u ∈ V) (hwV : w ∈ V) (hwu : w * u⁻¹ ∈ V₀) :
    F11.CElt M V₀ u ≤ F11.CElt M V₀ w := by
  haveI : IsMulCommutative ↥V := hV.1
  intro x hx
  obtain ⟨hxM, hxN0, hxu⟩ := hx
  refine ⟨hxM, hxN0, ?_⟩
  set c : G := w * u⁻¹ with hc
  have hcV0 : c ∈ V₀ := hwu
  have hcV : c ∈ V := hV0V hcV0
  have hw_eq : w = c * u := by rw [hc]; group
  have hxV : x ∈ normalizer (V : Set G) := hMV hxM
  have hcuV : x * c * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxV c).1 hcV
  have hd : x * c * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxN0 c).1 hcV0
  have hxuV : x * u * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxV u).1 huV
  have hcomm1 : (x * u * x⁻¹) * (x * c * x⁻¹) = (x * c * x⁻¹) * (x * u * x⁻¹) :=
    Subgroup.mul_comm_of_mem_isMulCommutative (H := V) hxuV hcuV
  have hcomm2 : (x * c * x⁻¹) * u⁻¹ = u⁻¹ * (x * c * x⁻¹) :=
    Subgroup.mul_comm_of_mem_isMulCommutative (H := V) hcuV (V.inv_mem huV)
  have hidentity : x * w * x⁻¹ * w⁻¹ =
      (x * u * x⁻¹ * u⁻¹) * (x * c * x⁻¹ * c⁻¹) := by
    rw [hw_eq]
    calc x * (c * u) * x⁻¹ * (c * u)⁻¹
        = (x * c * x⁻¹) * (x * u * x⁻¹) * (u⁻¹ * c⁻¹) := by group
      _ = (x * u * x⁻¹) * (x * c * x⁻¹) * (u⁻¹ * c⁻¹) := by rw [← hcomm1]
      _ = (x * u * x⁻¹) * ((x * c * x⁻¹) * u⁻¹) * c⁻¹ := by group
      _ = (x * u * x⁻¹) * (u⁻¹ * (x * c * x⁻¹)) * c⁻¹ := by rw [hcomm2]
      _ = (x * u * x⁻¹ * u⁻¹) * (x * c * x⁻¹ * c⁻¹) := by group
  rw [hidentity]
  exact V₀.mul_mem hxu (V₀.mul_mem hd (V₀.inv_mem hcV0))

private theorem s16h_e3_CycThreeThird_disj
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (h3 : D.sig = {3}) (hv1 : v1Sub D.M V₀ V hV L ≤ V₀)
    (hu₁ : ∀ w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hcent : ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ w ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) ∨
        ∃ E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M,
          E ≤ centralizer ({w} : Set G) := by
  intro X hX Y hY hXY w hw hw1
  have hV0v1 : V₀ ≤ v1Sub D.M V₀ V hV L := by
    by_cases h0 : V₀ = ⊥
    · subst h0; exact bot_le
    · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
  by_cases hw0 : w ∈ V₀
  · exact Or.inl (hu₁ w (mem_sup_right (hV0v1 hw0)) hw1)
  · refine Or.inr ?_
    have hXYV : X ⊔ Y ≤ V :=
      sup_le (s16h_e3_CycThreeThird_wConj_le_v D h.hyp151 hV hX)
        (s16h_e3_CycThreeThird_wConj_le_v D h.hyp151 hV hY)
    have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
    have hU1V : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L ≤ V := sup_le hXYV hV1V
    have hwV : w ∈ V := hU1V hw
    have hV0V : V₀ ≤ V := h.hyp151.hyp125.pairFacts.le
    obtain ⟨a, ha, hwa⟩ :=
      s16h_e3_CycThreeThird_exists_mul_mem_v0 hV hV0V hXYV hV1V hv1 hw
    have haV : a ∈ V := hXYV ha
    have hdvd_u : 3 ∣ Nat.card ↥(F11.CElt D.M V₀ a) := hcent X hX Y hY hXY a ha
    have hle := s16h_e3_CycThreeThird_cElt_le_of_mul_mem_v0 (M := D.M) hV hV0V
      h.hyp151.hyp125.pairFacts.le_normalizer haV hwV hwa
    have hdvd_w : 3 ∣ Nat.card ↥(F11.CElt D.M V₀ w) :=
      hdvd_u.trans (Subgroup.card_dvd_of_le hle)
    have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 S.h127 h.hyp151.hyp125
    have hV0p : IsPGroup 2 V₀ :=
      s16h_e3_CycThreeThird_isPGroup_two_of_le h.hyp151.hyp125.pairFacts.elemAbelian₀ le_rfl
    have h4 : Nat.card V₀ ≤ 4 := by
      rw [card_eq_two_pow_mSub hV0p]
      have hsmall : mSub V₀ ≤ 2 := h.hyp16.small
      interval_cases mSub V₀ <;> norm_num
    obtain ⟨n, -, hn⟩ := r113_holds D V₀ V hH h4 w hwV hw0
    have hcard : Nat.card ↥(F11.CElt D.M V₀ w) =
        (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) *
          Nat.card ↥((D.M ⊓ centralizer ({w} : Set G)) ⊓ F11.CElt D.M V₀ w) :=
      (Subgroup.relIndex_mul_card _ _).symm
    rw [hcard, hn] at hdvd_w
    have h3card : 3 ∣
        Nat.card ↥((D.M ⊓ centralizer ({w} : Set G)) ⊓ F11.CElt D.M V₀ w) := by
      have hcop : Nat.Coprime 3 (2 ^ n) :=
        Nat.prime_two.coprime_pow_of_not_dvd (by norm_num)
      exact hcop.dvd_of_dvd_mul_left hdvd_w
    have h3cent : 3 ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) :=
      h3card.trans (Subgroup.card_dvd_of_le inf_le_left)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hyord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(D.M ⊓ centralizer ({w} : Set G))) 3 h3cent
    let E : Subgroup G := Subgroup.zpowers (y : G)
    have hEcard : Nat.card E = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe y, hyord]
    have hEM : E ≤ D.M := (Subgroup.zpowers_le.mpr y.2).trans inf_le_left
    have hEC : E ≤ centralizer ({w} : Set G) :=
      (Subgroup.zpowers_le.mpr y.2).trans inf_le_right
    have h3mem : 3 ∈ D.sig := by rw [h3]; simp
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
      S.hSig.sig1_sp 3 (by rw [← hσ]; exact h3mem)
    exact ⟨E, s16h_e3_omega_mem_uniqueSet_of_card_prime D Nat.prime_three hsp hEM hEcard, hEC⟩

theorem s16h_e3_cyclic_third_three
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (h3 : D.sig = {3}) (hv1 : v1Sub D.M V₀ V hV L ≤ V₀)
    (hu₁ : ∀ w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hcent : ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u)) :
    ∀ g : G, g ∉ D.M → ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      (X ⊔ Y ⊔ v1Sub D.M V₀ V hV L) ⊓
        conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g = ⊥ := by
  intro g hg X hX Y hY hXY
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxU₁, hxU₂⟩ := Subgroup.mem_inf.mp hx
  have hXYV : X ⊔ Y ≤ V :=
    sup_le (s16h_e3_CycThreeThird_wConj_le_v D h.hyp151 hV hX)
      (s16h_e3_CycThreeThird_wConj_le_v D h.hyp151 hV hY)
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hU1V : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L ≤ V := sup_le hXYV hV1V
  have hxV : x ∈ V := hU1V hxU₁
  have hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x hxV⟩
  have huMg : UniqueMax (conjSubgroup D.M g)
      (conjSubgroup D.M g ⊓ centralizer ({x} : Set G)) :=
    uniqueMax_conjSubgroup_of_mem hu₁ hxU₂ hx1
  have hKMg : rankThreeIsMaxTwoLocal (conjSubgroup D.M g) :=
    UC6.isMaxTwoLocal_conj (show IsMaxTwoLocalSubgroup D.M from D.maxLocal) g
  have hcentx : centralizer ({x} : Set G) ≤ conjSubgroup D.M g :=
    (centralizer_le_of_uniqueMax hKMg hx1 hx2 huMg).1
  rcases s16h_e3_CycThreeThird_disj D S hσ hV h h3 hv1 hu₁ hcent X hX Y hY hXY x hxU₁ hx1 with
    hu | ⟨E, hE, hEC⟩
  · obtain ⟨-, hnotle⟩ := centralizer_le_of_uniqueMax D.maxLocal hx1 hx2 hu
    exact hnotle g hg fun y hy => hcentx (Subgroup.mem_inf.mp hy).2
  · have hEg : E ≤ conjSubgroup D.M g := hEC.trans hcentx
    have h2 : conjSubgroup D.M g = D.M := hE.2 g⁻¹ hEg
    have hgN : g ∈ normalizer (D.M : Set G) := conjSubgroup_eq_iff_mem_normalizer.mp h2
    rw [UC6.normalizer_eq_of_isMaxTwoLocal (show IsMaxTwoLocalSubgroup D.M from D.maxLocal)] at hgN
    exact hg hgN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
