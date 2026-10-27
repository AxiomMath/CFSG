module

public import CFSG.RankThree.PartOne.K133One.Split
public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.S13K.Comm134

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

@[expose] def DistinctCommute (p : ℕ) {E : Subgroup G} (s t : MulAut E) : Prop :=
  ∀ (e : G) (I₁ I₂ : Subgroup G), e ∈ autFixedInG E s → e ∈ autFixedInG E t → e ≠ 1 →
    I₁ ∈ thetaComponentsAt p e → I₂ ∈ thetaComponentsAt p e → I₁ ≠ I₂ → kZero p E s ≤ I₁ →
    kZero p E t ≤ I₂ → kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G)

omit [Finite G] in
theorem eq_one_of_le_autFixedInG {E : Subgroup G} {s : MulAut E} (h : E ≤ autFixedInG E s) :
    s = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (h x.2)
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

omit [Finite G] in
theorem false_of_kZero_le {p : ℕ} {E : Subgroup G} {c : G} {s t : MulAut E}
    (hFs : E ⊓ Subgroup.centralizer (kZero p E s : Set G) = autFixedInG E s)
    (hFt : E ⊓ Subgroup.centralizer (kZero p E t : Set G) = autFixedInG E t)
    (hcs : c ∈ autFixedInG E s) (hmov : autMovedInG E t = Subgroup.zpowers c)
    (hsplit : E = autFixedInG E t ⊔ autMovedInG E t) (hs1 : s ≠ 1)
    (hle : kZero p E s ≤ kZero p E t) : False := by
  have h1 : autFixedInG E t ≤ autFixedInG E s := by
    rw [← hFs, ← hFt]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hle)
  have h2 : E ≤ autFixedInG E s :=
    hsplit.le.trans (sup_le h1 (by rw [hmov]; exact Subgroup.zpowers_le.2 hcs))
  exact hs1 (eq_one_of_le_autFixedInG h2)

theorem dvd_two_pow_double_sub_one {p f : ℕ} (h : p ∣ 2 ^ f + 1) : p ∣ 2 ^ (2 * f) - 1 := by
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ f = b + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  have hq : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * b := by
    rw [pow_mul', sq, hb]
    have : (b + 1) * (b + 1) - 1 = (b + 1 + 1) * b := by
      rw [show (b + 1) * (b + 1) = (b + 1 + 1) * b + 1 by ring]
      rfl
    rw [this]
  rw [hq]
  exact dvd_mul_of_dvd_left h b

theorem comm_clause_row8 (hS : SchreierFor InCatalog) (hRe : Sec13Reinst)
    {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} {f : ℕ} (h : Sec12Hyp G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hpf : p ∣ 2 ^ f + 1) {z : MulAut E} (hz : Inverter p E z)
    {s t r : MulAut E} (hs : s ∈ reflectionSet p E) (hsL : s ∈ torusImage E L)
    (hr : r ∈ reflectionSet p E) (hrL : r ∈ torusImage E L) {y : G}
    (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hty : t = conjAut E y hy * r * (conjAut E y hy)⁻¹) (hKs : KFAt p E f s)
    (hKt : KFAt p E (2 * f) t) (hmov : autMovedInG E t = Subgroup.zpowers c) (hne : s ≠ t)
    (hcomm : s * t = t * s) (hnc : ∀ x ∈ reflectionGroup p E, x * s * x⁻¹ ≠ t)
    (hDist : DistinctCommute p s t) :
    kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
      kZero p E s ⊓ kZero p E t = ⊥ := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have ht : t ∈ reflectionSet p E := hty ▸ conj_mem_reflectionSet hp hr hy
  have hLs : KFLiftAt p E s := KFAt.toLiftAt hKs
  have hLt : KFLiftAt p E t := KFAt.toLiftAt hKt
  have hqs := hLs.1
  have hqt := hLt.1
  have hcs := hLs.2.1
  obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hLs
  obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hLt
  have hYmem : conjBy y L ∈ thetaCompZeroStarE p E :=
    conjBy_mem_thetaCompZeroStarE hp hy hF13.inZeroStar
  obtain ⟨B', c'', hB', -, -, hY12, -, hY13, -⟩ :=
    hRe G p A c L E h hF13 hT _ hYmem
  have htY : t ∈ torusImage E (conjBy y L) := by
    rw [torusImage_conjBy E L hy, hty]
    exact Subgroup.mem_map_of_mem (MulAut.conj (conjAut E y hy)).toMonoidHom hrL
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨⟨e, hee⟩, hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hF13.axes s hs t ht)
  have he1 : e ≠ 1 := fun h1 => hne' (Subtype.ext h1)
  have hesE : e ∈ autFixedInG E s := (Subgroup.mem_inf.mp hee).1
  have hetE : e ∈ autFixedInG E t := (Subgroup.mem_inf.mp hee).2
  have heE : e ∈ E := Subgroup.map_subtype_le _ hesE
  obtain ⟨I₁, hI₁, hKI₁⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hesE
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hqs)
  obtain ⟨I₂, hI₂, hKI₂⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hetE
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  by_cases hI : I₁ = I₂
  · subst hI
    exfalso
    have hEBp : E = B' :=
      (Subgroup.eq_of_le_of_card_ge hB'.1 (by rw [hcard, hB'.2.2.1])).symm
    have hp2 : p ≠ 2 := by omega
    have hsplit : K133.SplitType p (kZero p E t) :=
      K133.splitType_of_psl_two hp hp2 hKt.2.1 (dvd_two_pow_double_sub_one hpf)
    have hθI : inSubgroup (aschbacherSolvableCore p) I₁ ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
      rw [theta_eq_inf_of_mem_thetaComponentsAt hp hI₁]
      exact inf_le_right
    have hEI : E ≤ Subgroup.normalizer (I₁ : Set G) :=
      h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI₁
    have hEJ : E ≤ Subgroup.normalizer (kZero p E t : Set G) :=
      E_le_normalizer_kZero h.E_elem t
    have hPE : autFixedInG E s ≤ E := Subgroup.map_subtype_le _
    rcases K133One.kf133One_clause_one_of_liftAt hS hY12 hY13 hEBp ht htY (KFAt.toLiftAt hKt)
        hsplit hetE he1 hI₁ hKI₂ with hi | hiii
    ·
      have hIJ : sectionTenRel p I₁ (kZero p E t) := by
        unfold sectionTenRel
        rw [inf_eq_right.2 hKI₂]
        exact hi
      have hfix : kZero p E s ≤ Subgroup.centralizer
          ((inSubgroup (aschbacherSolvableCore p) I₁ ⊓
            Subgroup.centralizer (autFixedInG E s : Set G) : Subgroup G) : Set G) :=
        (isKt_centralizes_fixed_theta hp (KFAt.toLiftAt hKs).isKt hesE).trans
          (Subgroup.centralizer_le (inf_le_inf_right _ hθI))
      have hle : kZero p E s ≤ kZero p E t :=
        le_of_sectionTenRel_fixed hp hqs.1 hKI₁ hIJ (isPGroup_of_le_elementaryAbelian hE hPE)
          (hPE.trans hEI) (hPE.trans hEJ) (kZero_le_centralizer_fixed p E s) hfix
      have hcfix : c ∈ autFixedInG E s := by
        have := Sec13Base.fixes_c_of_mem_torusImage h hcE hsL
        exact Subgroup.mem_map.2 ⟨⟨c, hcE⟩, this, rfl⟩
      have hs1 : s ≠ 1 := fun h1 => by
        have := hs.1.1
        rw [h1, orderOf_one] at this
        omega
      exact false_of_kZero_le hKs.2.2.1 hKt.2.2.1 hcfix hmov (hF13.reflection t ht).1 hs1 hle
    ·
      have hsJ' : s ∈ torusImage E I₁ :=
        Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKI₁ hksK, hks, hks_eq⟩
      have htJ' : t ∈ torusImage E I₁ :=
        Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKI₂ hktK, hkt, hkt_eq⟩
      obtain ⟨B, c', h', hF', hc'E, hc'1, hEB, r', hr', hmodel', hW⟩ :=
        member_package hF13 hcard hz hiii
      obtain ⟨x, hx, hxst⟩ :=
        commuting_conj hF13 h' hF' hcard hc'E hr' hW hs hsJ' ht htJ' hne hcomm
      exact hnc x (torusImage_le_reflectionGroup hF' hx) hxst
  · have hc : kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) :=
      hDist e I₁ I₂ hesE hetE he1 hI₁ hI₂ hI hKI₁ hKI₂
    exact ⟨hc, inf_eq_bot_of_centralizes hc hcs⟩

end CFSG.RankThree.PartOne.K1320
