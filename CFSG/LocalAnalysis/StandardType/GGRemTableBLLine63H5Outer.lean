module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Two
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

theorem three_dvd_of_zpow_mem_range_sixth [Finite K] (h3 : 3 ∣ Nat.card Kˣ)
    (h2 : ¬ 2 ∣ Nat.card Kˣ) {u : Kˣ} (hu : u ∉ (powMonoidHom 6 : Kˣ →* Kˣ).range) {i : ℤ}
    (hi : u ^ i ∈ (powMonoidHom 6 : Kˣ →* Kˣ).range) : (3 : ℤ) ∣ i := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
  rw [zpow_mem_range_sixth_iff hg h3 h2] at hu
  rw [← _root_.zpow_mul, zpow_mem_range_sixth_iff hg h3 h2] at hi
  exact (Int.prime_three.dvd_mul.mp hi).resolve_left hu

theorem three_dvd_of_isInner_zpow [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6))
    (hgn : ¬ IsInner n g) {i : ℤ} (hi : IsInner n (g ^ i)) : (3 : ℤ) ∣ i := by
  obtain ⟨h3, h2⟩ := card_units_dvd_odd hKd hpq
  obtain ⟨t, ht⟩ := det_eq_pow_six_of_isInner hi hKd
  refine three_dvd_of_zpow_mem_range_sixth h3 h2 (det_not_mem_range_sixth hKd hpq hgU hgn) ?_
  refine ⟨t, ?_⟩
  have h1 : ((GeneralLinearGroup.det (g ^ i) : Kˣ) : K) = (t : K) ^ 6 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact ht
  rw [map_zpow] at h1
  exact Units.ext (by simpa using h1.symm)

theorem isInner_zpow_of_projConj [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {g : GL (Fin 6) K}
    (hgN : g ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (s : ↥(unitarySU 2 n K 6)) (i : ℤ)
    (h : TableB.projConj (unitarySU 2 n K 6)
        ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ *
      TableB.projConj (unitarySU 2 n K 6) ⟨g, hgN⟩ ^ i = 1) : IsInner n (g ^ i) := by
  have hKc : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  rw [← map_zpow, ← map_mul] at h
  have hsc := TableBUE.mem_scalars_of_projConj_eq_one hKd hKc (by norm_num) hdq
    Nat.prime_three hpq h
  rw [largeEvenScalars_def] at hsc
  obtain ⟨t, ht⟩ := hsc
  have ht' : GeneralLinearGroup.scalar (Fin 6) t = (s : GL (Fin 6) K) * g ^ i := by
    rw [ht]
    simp
  have hg : g ^ i = (s : GL (Fin 6) K)⁻¹ * GeneralLinearGroup.scalar (Fin 6) t := by
    rw [ht']
    exact (inv_mul_cancel_left _ _).symm
  refine ⟨t, s⁻¹, ?_⟩
  rw [hg, Subgroup.coe_inv]
  exact (commute_scalar t _).eq

theorem ggLAut_mk_eq_conj {G : Type} [Group G] (L : Subgroup G) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (l : L) :
    ggLAut L θ ⟨(l : G), Subgroup.le_normalizer l.2⟩ = MulAut.conj (ggQuotHom θ l) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l' =>
    rw [ggLAut_apply, MulAut.conj_apply]
    have h1 : (L.normalizerMonoidHom ⟨(l : G), Subgroup.le_normalizer l.2⟩ l' : L) =
        l * l' * l⁻¹ := Subtype.ext rfl
    rw [h1]
    show ggQuotHom θ (l * l' * l⁻¹) = ggQuotHom θ l * ggQuotHom θ l' * (ggQuotHom θ l)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem three_dvd_of_ggLAut_mul_zpow [Finite K] {G : Type} [Group G] (L : Subgroup G)
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6)) (hgn : ¬ IsInner n g)
    (hac : ggLAut L θ ⟨a, ha⟩ = TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩)
    (l : L) (i : ℤ)
    (h : ggLAut L θ (⟨(l : G), Subgroup.le_normalizer l.2⟩ * ⟨a, ha⟩ ^ i) = 1) :
    (3 : ℤ) ∣ i := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ggQuotHom θ l)
  rw [map_mul, map_zpow, hac, ggLAut_mk_eq_conj, ← hs] at h
  have hc := TableB.projConj_of_mem (unitarySU 2 n K 6) (s : GL (Fin 6) K) s.2
  have h' : TableB.projConj (unitarySU 2 n K 6)
        ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ *
      TableB.projConj (unitarySU 2 n K 6) ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩ ^ i = 1 := by
    rw [hc]
    exact h
  exact three_dvd_of_isInner_zpow hKd hpq hgU hgn (isInner_zpow_of_projConj hKd hpq _ s i h')

theorem mem_of_ggLAut_eq_one_of_mem_sup [Finite K] {G : Type} [Group G] (L : Subgroup G)
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6)) (hgn : ¬ IsInner n g)
    (hac : ggLAut L θ ⟨a, ha⟩ = TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩)
    {h : G} (hh : h ∈ L ⊔ Subgroup.zpowers a) (hhN : h ∈ Subgroup.normalizer (L : Set G))
    (h1 : ggLAut L θ ⟨h, hhN⟩ = 1) : h ∈ L := by
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr ha
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L _ hzN] at hh
  obtain ⟨l, hl, y, hy, rfl⟩ := Set.mem_mul.mp hh
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hNmem : (⟨l * a ^ i, hhN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨l, Subgroup.le_normalizer hl⟩ * ⟨a, ha⟩ ^ i := Subtype.ext (by simp)
  rw [hNmem] at h1
  obtain ⟨j, rfl⟩ := three_dvd_of_ggLAut_mul_zpow L hKd hpq θ ha hgU hgn hac ⟨l, hl⟩ i h1
  have hai : a ^ ((3 : ℤ) * j) = 1 := by
    rw [_root_.zpow_mul]
    simp [ha3]
  rw [hai, mul_one]
  exact hl

theorem five_le_twoLocalRank_of_outer {K : Type} [Field K] [Finite K] {n : ℕ} {G : Type} [Group G]
    [Finite G] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {L : Subgroup G} (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    (hZ : IsPGroup 2 (Subgroup.center L))
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6)) (hgn : ¬ IsInner n g)
    (hac : ggLAut L θ ⟨a, ha⟩ = TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩)
    {x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxC : ∀ l ∈ L, x * l = l * x) (hxa : x * a = a * x)
    (hxL : x ∉ L) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  classical
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr ha
  set H : Subgroup G := L ⊔ Subgroup.zpowers a with hHdef
  have hLH : L ≤ H := le_sup_left
  have haH : a ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hzN
  set π := ggBeta L θ hHN with hπ
  have hker : ∀ y : ↥H, π y = 1 → (y : G) ∈ L := fun y hy =>
    mem_of_ggLAut_eq_one_of_mem_sup L hKd hpq θ ha ha3 hgU hgn hac y.2 (hHN y.2) hy
  have hN : IsPGroup 2 π.ker := by
    intro y
    have hy1 : π (y : ↥H) = 1 := y.2
    have hyL : ((y : ↥H) : G) ∈ L := hker y hy1
    have hyc : (⟨((y : ↥H) : G), hyL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (mem_centralizer_of_ggLAut_eq_one L θ hL (g := ⟨_, hHN (y : ↥H).2⟩) hy1) l l.2)
    obtain ⟨k, hk⟩ := hZ ⟨_, hyc⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(Subgroup.center L) => ((z : L) : G)) hk
    simpa using this
  have hinn : ∀ s : ↥(unitarySU 2 n K 6),
      TableB.projConj (unitarySU 2 n K 6) ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ ∈
        π.range := by
    intro s
    obtain ⟨l, hl⟩ := ggQuotHom_surjective θ (LargeEvenProjMk (unitarySU 2 n K 6) s)
    refine ⟨⟨(l : G), hLH l.2⟩, ?_⟩
    refine (ggLAut_mk_eq_conj L θ l).trans ?_
    rw [hl]
    exact (TableB.projConj_of_mem (unitarySU 2 n K 6) (s : GL (Fin 6) K) s.2).symm
  have hgr : TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩ ∈ π.range :=
    ⟨⟨a, haH⟩, hac⟩
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hxC l hl).symm) ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm)
  have hxC' : ∀ h ∈ H, x * h = h * x := fun h hh =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hHx hh)).symm
  have hxH : x ∉ H := by
    intro hxH
    apply hxL
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => (hxC l hl).symm
    exact hker ⟨x, hxH⟩ (ggLAut_eq_one_of_mem_centralizer L θ (g := ⟨x, hHN hxH⟩) hxcent)
  exact five_le_twoLocalRank_of_inner_outer hKd hpq hx3 hx1 hxH hxC' π hN hinn hgU hgn hgr

end CFSG.StandardType.Line63.H5

end
