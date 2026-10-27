module

public import CFSG.RankThree.PartOne.S13K.KFLift
public import CFSG.RankThree.PartOne.S13K.KF133One
public import CFSG.RankThree.PartOne.S13K.Reinst
public import CFSG.RankThree.PartOne.S13K.Pair134Embed
public import CFSG.RankThree.PartOne.S13K.ThetaFixed
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartOne.S11d.ThetaCalc
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import all CFSG.Timmesfeld.Orders.Distinct

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem not_psl_three_and_psl_four {Q : Type} [Group Q] {a g : ℕ} (hg : 2 ≤ g)
    (h1 : StatedClassicalModel Q .PSL 3 2 a) (h2 : StatedClassicalModel Q .PSL 4 2 g) : False := by
  have c1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h1).1 rfl
  have c2 := (CFSG.Timmesfeld.card_statedClassicalModel_two h2).1 rfl
  obtain ⟨⟨-, ha, -, -, -⟩, -⟩ := h1
  obtain ⟨⟨-, hg1, -, -, -⟩, -⟩ := h2
  have heq : CFSG.Open.ordA 2 (2 ^ a) = CFSG.Open.ordA 3 (2 ^ g) := c1.symm.trans c2
  have P1 := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (f := a) (by norm_num) ha
  have P2 := CFSG.Timmesfeld.Orders.profile_ordA (n := 3) (f := g) (by norm_num) hg1
  rw [heq] at P1
  obtain ⟨hN, hZ⟩ := CFSG.Timmesfeld.Orders.Profile.transfer P1 P2
  have ha2 : a = 2 * g := by norm_num at hN; omega
  have hz1 : CFSG.Timmesfeld.Orders.zA 2 a (6 * g) :=
    ⟨3, by simp, ⟨1, by rw [ha2]; ring⟩⟩
  obtain ⟨i, hi, hdvd⟩ := (hZ (6 * g) (by omega) (by omega)).mp hz1
  simp only [Finset.mem_Icc] at hi
  have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
  nlinarith [hi.2]

theorem isSubnormal_subgroupOf_of_normal' {G : Type} [Group G] {K N M : Subgroup G} (hKN : K ≤ N)
    (hK : (K.subgroupOf N).Normal) (hN : (N.subgroupOf M).IsSubnormal) :
    (K.subgroupOf M).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (H := K.subgroupOf M) (K := N.subgroupOf M)
    (fun x hx => hKN hx) ?_ hN
  refine Subgroup.Normal.isSubnormal ⟨fun x hx y => ?_⟩
  have hx' : ((x : ↥M) : G) ∈ K := hx
  have hxN : ((x : ↥M) : G) ∈ N := hKN hx'
  have hyN : ((y : ↥M) : G) ∈ N := y.2
  exact hK.conj_mem ⟨((x : ↥M) : G), hxN⟩ hx' ⟨((y : ↥M) : G), hyN⟩

theorem kZero_mem_thetaComponents {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} {t : MulAut E} (hq : CFSG.IsQuasisimple ↥(kZero p E t)) :
    (kZero p E t).subgroupOf (Subgroup.centralizer (autFixedInG E t : Set G)) ∈
      thetaComponents p ↥(Subgroup.centralizer (autFixedInG E t : Set G)) := by
  set C := Subgroup.centralizer (autFixedInG E t : Set G) with hC
  set Λ : Subgroup G := inSubgroup (fun K _ => layer K) C with hΛ
  set K := kZero p E t with hK
  have hKdef : K = pElementSubgroup p Λ := rfl
  have hKΛ : K ≤ Λ := by
    rw [hKdef]
    unfold pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hKC : K ≤ C := kZero_le_centralizer_fixed p E t
  have hnorm : ∀ g ∈ Λ, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    have h1 : K ≤ K.comap (MulAut.conj g).toMonoidHom := by
      rw [hKdef]
      unfold pElementSubgroup
      rw [Subgroup.closure_le]
      intro y hy
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact Λ.mul_mem (Λ.mul_mem hg hy.1) (Λ.inv_mem hg)
      · obtain ⟨k, hk⟩ := hy.2
        refine ⟨k, ?_⟩
        have := MulEquiv.orderOf_eq (MulAut.conj g) y
        simpa [MulAut.conj_apply, hk] using this
    exact h1 hx
  have hKn : (K.subgroupOf Λ).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKΛ).mpr fun g hg => ?_
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hnorm g hg x hx, fun hx => ?_⟩
    have h1 := hnorm g⁻¹ (Λ.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1
  have hΛn : (Λ.subgroupOf C).Normal := by
    have h1 : Λ.subgroupOf C = layer ↥C :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [h1]
    have := LocalCores.layer_characteristic (G := ↥C)
    infer_instance
  have hsn : (K.subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal' hKΛ hKn hΛn.isSubnormal
  have hq' : CFSG.IsQuasisimple ↥(K.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hq
  exact mem_thetaComponents_of_quasisimple hp hq' hsn

theorem normalizes_of_mem_thetaCompE {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {J : Subgroup G}
    (hJ : J ∈ thetaCompE p E) : E ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨B, hB, hJB⟩ := hJ
  obtain ⟨b, hbB, -, hJb⟩ := mem_thetaComponentFamily_iff.mp hJB
  exact h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components
    (hB.1 hbB) hJb

theorem pair_cases_dich (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hLift : KFLiftAll)
    (h133 : KF133Two) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hcase : E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J))
    {t s : MulAut E} (ht : t ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E) :
    (∃ (e : G) (I₁ I₂ : Subgroup G), e ∈ E ∧ e ≠ 1 ∧ e ∈ autFixedInG E t ∧ e ∈ autFixedInG E s ∧
        I₁ ∈ thetaComponentsAt p e ∧ I₂ ∈ thetaComponentsAt p e ∧
        I₁ ≠ I₂ ∧ kZero p E t ≤ I₁ ∧ kZero p E s ≤ I₂) ∨
      ∃ J ∈ thetaCompZeroStarE p E, kZero p E t ≤ J ∧ kZero p E s ≤ J := by
  have hp := h.prime
  have hLt := hLift G p A c L E h hF hF13 hT hcase t ht
  have hLs := hLift G p A c L E h hF hF13 hT hcase s hs
  obtain ⟨hrt, X, hX, htX⟩ := ht
  obtain ⟨hrs, Y, hY, hsY⟩ := hs
  have ht' : t ∈ reflectionSet p E := ⟨hrt, X, hX, htX⟩
  have hs' : s ∈ reflectionSet p E := ⟨hrs, Y, hY, hsY⟩
  obtain ⟨B, c', hB, hc'B, hc'1, hX12, hXF, hX13, hXT⟩ := hRe G p A c L E h hF13 hT X hX
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨⟨e, hee⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hF13.axes t ht' s hs')
  have he1 : e ≠ 1 := fun h1 => hne (Subtype.ext h1)
  have hetE : e ∈ autFixedInG E t := (Subgroup.mem_inf.mp hee).1
  have hesE : e ∈ autFixedInG E s := (Subgroup.mem_inf.mp hee).2
  have heE : e ∈ E := Subgroup.map_subtype_le _ hetE
  have hqt := hLt.1
  have hqs := hLs.1
  have hLt' : KFLiftAt p E t := hLt
  have hLs' : KFLiftAt p E s := hLs
  obtain ⟨I₁, hI₁, hKI₁⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hetE
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  obtain ⟨I₂, hI₂, hKI₂⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hesE
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hqs)
  by_cases hI : I₁ = I₂
  · subst hI
    right
    have hc := h133 G p B c' X E hX12 hXF hX13 hXT t ht' htX (kZero p E t) hLt'.isKt e hetE he1 I₁
      hI₁ hKI₁
    rcases hc with ⟨hEB, f, hf1, hpf, hmodel4⟩ | ⟨J, hJ, hIJ⟩
    · exfalso
      have hBcard : Nat.card B = p ^ 3 := hB.2.2.1
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have hf1' : f = 1 := by omega
        subst hf1'
        have h3 : p ∣ 3 := by simpa using hpf
        have := Nat.le_of_dvd (by norm_num) h3
        have := Sec12Three.five_le hX12
        omega
      rcases hcase with hEA | ⟨hEA, hall⟩
      · apply hEA
        refine (Subgroup.eq_of_le_of_card_ge h.A_le_E (le_of_eq ?_)).symm
        rw [h.A_card, ← hBcard, hEB]
      · have hBA : B = A := by
          refine Subgroup.eq_of_le_of_card_ge (hEA ▸ hB.1) (le_of_eq ?_)
          rw [h.A_card, hBcard]
        have hXz : X ∈ sectionTenZeroStar p A := hBA ▸ Sec12Three.L_mem_zeroStar hX12
        obtain ⟨a, ha1, hpa, hmodel3⟩ := hall X hXz
        exact not_psl_three_and_psl_four hf2 hmodel3 hmodel4
    · have hθI : inSubgroup (aschbacherSolvableCore p) I₁ ≤
          inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
        rw [theta_eq_inf_of_mem_thetaComponentsAt hp hI₁]
        exact inf_le_right
      have hEI : E ≤ Subgroup.normalizer (I₁ : Set G) :=
        h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI₁
      have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_of_mem_thetaCompE h hJ.2.1
      have hfix : ∀ {u : MulAut E} {K : Subgroup G}, IsKt p E u K → e ∈ autFixedInG E u →
          K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p) I₁ ⊓
            Subgroup.centralizer (autFixedInG E u : Set G) : Subgroup G) : Set G) :=
        fun hK he' => (isKt_centralizes_fixed_theta hp hK he').trans
          (Subgroup.centralizer_le (inf_le_inf_right _ hθI))
      have hPE : ∀ u : MulAut E, autFixedInG E u ≤ E := fun u => Subgroup.map_subtype_le _
      have hPp : ∀ u : MulAut E, IsPGroup p ↥(autFixedInG E u) := fun u =>
        isPGroup_of_le_elementaryAbelian hE (hPE u)
      exact ⟨J, hJ,
        le_of_sectionTenRel_fixed hp hqt.1 hKI₁ hIJ (hPp t) ((hPE t).trans hEI) ((hPE t).trans hEJ)
          (kZero_le_centralizer_fixed p E t) (hfix hLt'.isKt hetE),
        le_of_sectionTenRel_fixed hp hqs.1 hKI₂ hIJ (hPp s) ((hPE s).trans hEI) ((hPE s).trans hEJ)
          (kZero_le_centralizer_fixed p E s) (hfix hLs'.isKt hesE)⟩
  · left
    exact ⟨e, I₁, I₂, heE, he1, hetE, hesE, hI₁, hI₂, hI, hKI₁, hKI₂⟩

theorem kf134Pair_of_inputs (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hLift : KFLiftAll)
    (h133 : KF133Two) : KF134Pair := by
  intro G _ _ p A c L E h hF hF13 hT hcase t ht s hs hts
  have hp := h.prime
  have hLt := hLift G p A c L E h hF hF13 hT hcase t ht
  have hLs := hLift G p A c L E h hF hF13 hT hcase s hs
  obtain ⟨hqt, hct, hnt, hmt, kt, hkt, hktK, hkt_eq⟩ := hLt
  obtain ⟨hqs, hcs, hns, hms, ks, hks, hksK, hks_eq⟩ := hLs
  rcases pair_cases_dich hS hRe hLift h133 h hF hF13 hT hcase ht hs with
    ⟨e, I₁, I₂, heE, -, -, -, hI₁, hI₂, hne, hK₁, hK₂⟩ | ⟨J, hJ, hKJ, hKsJ⟩
  · exfalso
    apply hts
    have := commute_of_distinct_components hp h.E_elem heE hI₁ hI₂ hne (hK₁ hktK) (hK₂ hksK) hkt hks
    rw [hkt_eq, hks_eq] at this
    exact this
  · exact ⟨J, hJ, Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKJ hktK, hkt, hkt_eq⟩,
      Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKsJ hksK, hks, hks_eq⟩⟩

end CFSG.RankThree.PartOne.S13K
