module

public import CFSG.RankThree.PartOne.DISTX.Row9Struct
public import CFSG.RankThree.PartOne.S13K.Comm134
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open Equiv

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem exists_common_fixed (h : Sec12Hyp G p A c L E) (hcard : Nat.card E = p ^ 4)
    {t d s : MulAut E} (ht : t ∈ reflectionSet p E) (hd : d ∈ reflectionSet p E)
    (hs : s ∈ reflectionSet p E) :
    ∃ e : G, e ∈ autFixedInG E t ∧ e ∈ autFixedInG E d ∧ e ∈ autFixedInG E s ∧ e ≠ 1 := by
  obtain ⟨-, -, -, hct⟩ := Sec13Base.reflection_facts h ht
  obtain ⟨-, -, -, hcd⟩ := Sec13Base.reflection_facts h hd
  obtain ⟨-, -, -, hcs⟩ := Sec13Base.reflection_facts h hs
  have hp := h.prime
  have hindex : ∀ {X : Subgroup E}, Nat.card E = Nat.card X * p → X.index = p := fun {X} hX =>
    Nat.eq_of_mul_eq_mul_left Nat.card_pos ((Subgroup.card_mul_index X).trans hX)
  have hXi := hindex hct
  have hYi := hindex hcd
  have hZi := hindex hcs
  set C := autFixed E t ⊓ autFixed E d ⊓ autFixed E s with hC
  have hcardC : p ≤ Nat.card ↥C := by
    by_contra hlt
    push Not at hlt
    have h1 := Subgroup.card_mul_index C
    have h2 : (autFixed E t ⊓ autFixed E d).index ≤ p * p := by
      have := Subgroup.index_inf_le (H := autFixed E t) (K := autFixed E d)
      rwa [hXi, hYi] at this
    have h2' : C.index ≤ p * p * p := by
      have := Subgroup.index_inf_le (H := autFixed E t ⊓ autFixed E d) (K := autFixed E s)
      rw [hZi] at this
      exact this.trans (Nat.mul_le_mul_right p h2)
    have h3 : Nat.card ↥C * C.index ≤ (p - 1) * (p * p * p) := Nat.mul_le_mul (by omega) h2'
    have h4 : (p - 1) * (p * p * p) < p ^ 4 := by
      have : 0 < p := hp.pos
      calc (p - 1) * (p * p * p) < p * (p * p * p) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = p ^ 4 := by ring
    omega
  have hne : C ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hcardC
    have := hp.two_le
    omega
  obtain ⟨⟨e, he⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1 : (e : G) ≠ 1 := fun h1 => hne1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨⟨het, hed⟩, hes⟩ := he
  exact ⟨(e : G), ⟨e, het, rfl⟩, ⟨e, hed, rfl⟩, ⟨e, hes, rfl⟩, he1⟩

theorem same_member_of_component (hRe : Sec13Reinst)
    (hLift : KFLiftAll) (h133 : KF133Two) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A) {t d : MulAut E}
    (ht : t ∈ reflectionSet p E) (hd : d ∈ reflectionSet p E) {e : G} (hetE : e ∈ autFixedInG E t)
    (hedE : e ∈ autFixedInG E d) (he1 : e ≠ 1) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKtI : kZero p E t ≤ I) (hKdI : kZero p E d ≤ I) :
    ∃ J ∈ thetaCompZeroStarE p E, kZero p E t ≤ J ∧ kZero p E d ≤ J := by
  have hp := h.prime
  have hcase : E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A →
      IsLThreeTypeAt p J) := Or.inl hEA
  have hLt := hLift G p A c L E h hF hF13 hT hcase t ht
  have hLd := hLift G p A c L E h hF hF13 hT hcase d hd
  have hqt := hLt.1
  have hqd := hLd.1
  have hLt' : KFLiftAt p E t := hLt
  have hLd' : KFLiftAt p E d := hLd
  obtain ⟨hrt, X, hX, htX⟩ := ht
  have ht' : t ∈ reflectionSet p E := ⟨hrt, X, hX, htX⟩
  obtain ⟨B, c', hB, hc'B, hc'1, hX12, hXF, hX13, hXT⟩ := hRe G p A c L E h hF13 hT X hX
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have heE : e ∈ E := Subgroup.map_subtype_le _ hetE
  have hc := h133 G p B c' X E hX12 hXF hX13 hXT t ht' htX (kZero p E t) hLt'.isKt e hetE he1 I hI
    hKtI
  rcases hc with ⟨hEB, f, hf1, hpf, hmodel4⟩ | ⟨J, hJ, hIJ⟩
  · exfalso
    apply hEA
    have hBcard : Nat.card B = p ^ 3 := hB.2.2.1
    refine (Subgroup.eq_of_le_of_card_ge h.A_le_E (le_of_eq ?_)).symm
    rw [h.A_card, ← hBcard, hEB]
  · have hθI : inSubgroup (aschbacherSolvableCore p) I ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
      rw [theta_eq_inf_of_mem_thetaComponentsAt hp hI]
      exact inf_le_right
    have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
      h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
    have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_of_mem_thetaCompE h hJ.2.1
    have hfix : ∀ {u : MulAut E} {K : Subgroup G}, IsKt p E u K → e ∈ autFixedInG E u →
        K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p) I ⊓
          Subgroup.centralizer (autFixedInG E u : Set G) : Subgroup G) : Set G) :=
      fun hK he' => (isKt_centralizes_fixed_theta hp hK he').trans
        (Subgroup.centralizer_le (inf_le_inf_right _ hθI))
    have hPE : ∀ u : MulAut E, autFixedInG E u ≤ E := fun u => Subgroup.map_subtype_le _
    have hPp : ∀ u : MulAut E, IsPGroup p ↥(autFixedInG E u) := fun u =>
      isPGroup_of_le_elementaryAbelian hE (hPE u)
    exact ⟨J, hJ,
      le_of_sectionTenRel_fixed hp hqt.1 hKtI hIJ (hPp t) ((hPE t).trans hEI) ((hPE t).trans hEJ)
        (kZero_le_centralizer_fixed p E t) (hfix hLt'.isKt hetE),
      le_of_sectionTenRel_fixed hp hqd.1 hKdI hIJ (hPp d) ((hPE d).trans hEI) ((hPE d).trans hEJ)
        (kZero_le_centralizer_fixed p E d) (hfix hLd'.isKt hedE)⟩

theorem commute_of_partner (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hLift : KFLiftAll)
    (h133 : KF133Two) (hSame : KFCommSame) (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A) (hcard : Nat.card E = p ^ 4)
    {t d s : MulAut E} (ht : t ∈ reflectionSet p E) (hd : d ∈ reflectionSet p E)
    (hs : s ∈ reflectionSet p E) (hts : t * s ≠ s * t) (hds : d * s ≠ s * d) (hne : t ≠ d)
    (hcomm : t * d = d * t) : kZero p E t ≤ Subgroup.centralizer (kZero p E d : Set G) := by
  have hp := h.prime
  have hcase : E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A →
      IsLThreeTypeAt p J) := Or.inl hEA
  have hLt := hLift G p A c L E h hF hF13 hT hcase t ht
  have hLd := hLift G p A c L E h hF hF13 hT hcase d hd
  have hLs := hLift G p A c L E h hF hF13 hT hcase s hs
  obtain ⟨e, het, hed, hes, he1⟩ := exists_common_fixed h hcard ht hd hs
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have heE : e ∈ E := Subgroup.map_subtype_le _ het
  have hEel : ∀ u : MulAut E, IsElementaryAbelian p ↥(autFixedInG E u) := fun u =>
    isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)
  obtain ⟨hqt, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hLt
  obtain ⟨hqd, -, -, -, kd, hkd, hkdK, hkd_eq⟩ := hLd
  obtain ⟨hqs, -, -, -, ks, hks, hksK, hks_eq⟩ := hLs
  obtain ⟨It, hIt, hKt⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1 (hEel t) het
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  obtain ⟨Id, hId, hKd⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1 (hEel d) hed
    (kZero_le_centralizer_fixed p E d) (kZero_mem_thetaComponents hp hqd)
  obtain ⟨Is, hIs, hKs⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1 (hEel s) hes
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hqs)
  have hIts : It = Is := by
    by_contra hne'
    apply hts
    have := commute_of_distinct_components hp hE heE hIt hIs hne' (hKt hktK) (hKs hksK) hkt hks
    rw [hkt_eq, hks_eq] at this
    exact this
  have hIds : Id = Is := by
    by_contra hne'
    apply hds
    have := commute_of_distinct_components hp hE heE hId hIs hne' (hKd hkdK) (hKs hksK) hkd hks
    rw [hkd_eq, hks_eq] at this
    exact this
  subst hIts hIds
  obtain ⟨J, hJ, hKtJ, hKdJ⟩ := same_member_of_component hRe hLift h133 h hF hF13 hT hEA ht hd het
    hed he1 hIt hKt hKd
  obtain ⟨B, c', hB, hc'B, hc'1, hJ12, hJF, hJ13, hJT⟩ := hRe G p A c L E h hF13 hT J hJ
  exact (hSame G p B c' J E hJ12 hJF hJ13 hJT (hcase_of_reinst h hB hcase) t ht
    (Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtJ hktK, hkt, hkt_eq⟩) d hd
    (Sec12Three.mem_torusImage_iff.mpr ⟨kd, hKdJ hkdK, hkd, hkd_eq⟩) hne hcomm).1

omit [Finite G] in
theorem conjBy_le_centralizer (w : G) {K₁ K₂ : Subgroup G}
    (h : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) :
    conjBy w K₁ ≤ Subgroup.centralizer (conjBy w K₂ : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have hab := Subgroup.mem_centralizer_iff.mp (h ha) b hb
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  calc w * b * w⁻¹ * (w * a * w⁻¹) = w * (b * a) * w⁻¹ := by group
    _ = w * (a * b) * w⁻¹ := by rw [hab]
    _ = w * a * w⁻¹ * (w * b * w⁻¹) := by group

theorem kf134Comm_of_members (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hLift : KFLiftAll)
    (h133 : KF133Two) (hSame : KFCommSame) (h136 : Node136) (h138I : Node138I)
    (h124b : Node124b) : KF134Comm := by
  intro G _ _ p A c L E h hF hF13 hT hEA hrow hD3 hTr s hs t ht hst hcomm
  have hp := h.prime
  obtain ⟨hclosure, ⟨ψ⟩, hcard, hno11, -⟩ :=
    Sec138Trans.rowNine_data h136 h138I h124b h hF hF13 hT hEA
  obtain ⟨t₀, ht₀, ht₀Γ⟩ : ∃ t ∈ reflectionSet p E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    have h24 : Nat.card (torusImage E L) = 24 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    rw [hempty, Subgroup.closure_empty] at hclosure
    rw [hclosure, Subgroup.card_bot] at h24
    omega
  obtain ⟨x, hx, hxs⟩ := hTr t₀ ht₀ s hs
  obtain ⟨w, hw, hwx⟩ := WeylIso.exists_lift (WeylIso.closure_le_weyl hx)
  have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := inv_mem hw
  set a := conjAut E w hw with ha
  have hsa : s = a * t₀ * a⁻¹ := by rw [← hxs, ← hwx]
  have ht' : a⁻¹ * t * a ∈ reflectionSet p E := by
    have := conj_mem_reflectionSet hp ht hw'
    rwa [Equivariance.conjAut_inv hw, inv_inv] at this
  have hta : t = a * (a⁻¹ * t * a) * a⁻¹ := by group
  have hcomm' : (a⁻¹ * t * a) * t₀ = t₀ * (a⁻¹ * t * a) := by
    have h1 : a * ((a⁻¹ * t * a) * t₀) * a⁻¹ = a * (t₀ * (a⁻¹ * t * a)) * a⁻¹ := by
      calc a * ((a⁻¹ * t * a) * t₀) * a⁻¹ = t * (a * t₀ * a⁻¹) := by group
        _ = (a * t₀ * a⁻¹) * t := by rw [← hsa]; exact hcomm.symm
        _ = a * (t₀ * (a⁻¹ * t * a)) * a⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hne' : a⁻¹ * t * a ≠ t₀ := fun h1 => hst (by
    rw [hsa, ← h1]
    exact hta.symm)
  obtain ⟨s', hs', hs't, hs'd⟩ := exists_partner h hF hF13 hD3 hTr hcard hno11 hclosure ψ ht₀ ht₀Γ
    ht' hcomm' hne'
  have hcore := commute_of_partner hS hRe hLift h133 hSame h hF hF13 hT hEA hcard ht₀ ht' hs'
    (fun h1 => hs't h1.symm) (fun h1 => hs'd h1.symm) hne'.symm hcomm'.symm
  have hks := kZero_conj p t₀ hw
  have hkt := kZero_conj p (a⁻¹ * t * a) hw
  rw [← ha, ← hsa] at hks
  rw [← ha, ← hta] at hkt
  rw [hks, hkt]
  exact conjBy_le_centralizer w hcore

end CFSG.RankThree.PartOne.DISTX
