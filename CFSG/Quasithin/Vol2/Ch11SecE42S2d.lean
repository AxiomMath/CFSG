module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

section PSL

variable {p : ℕ} [Fact p.Prime]

theorem isSimpleGroup_psl (hp5 : 5 ≤ p) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)

theorem commutator_psl_eq_top (hp5 : 5 ≤ p) :
    commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = ⊤ := by
  have hperf := A1c.sl2_isPerfect hp5
  have h1 : (⊤ : Subgroup (SL(2, ZMod p))).map (Dickson.pslMap p) = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr Dickson.pslMap_surjective
  rw [commutator_def, ← h1, ← Subgroup.map_commutator, ← commutator_def, hperf.commutator_eq_top]

theorem eq_bot_of_normal_two_psl (hp5 : 5 ≤ p)
    {N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := isSimpleGroup_psl (p := p) hp5
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have h2' : IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := fun g => by
      obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsNilpotent (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      h2'.isNilpotent
    have hsol : Group.IsSolvable ↥(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (ZMod p))) := inferInstance
    have hbot := eq_bot_of_perfect_of_solvable (B := ⊤)
      (by rw [← commutator_def, commutator_psl_eq_top hp5]) hsol
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    have ha : a = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top b)
    exact hab (ha.trans hb.symm)

theorem isQuasisimple_psl (hp5 : 5 ≤ p) :
    CFSG.IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hs := isSimpleGroup_psl (p := p) hp5
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra hc
  push Not at hc
  have hcomm : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  rw [commutator_psl_eq_top hp5] at hcomm
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  have ha : a = 1 := Subgroup.mem_bot.mp (hcomm ▸ Subgroup.mem_top a)
  have hb : b = 1 := Subgroup.mem_bot.mp (hcomm ▸ Subgroup.mem_top b)
  exact hab (ha.trans hb.symm)

end PSL

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

abbrev kJ (T L V₁ K : Subgroup G) : Subgroup G :=
  perfectCore (K ⊓ Subgroup.normalizer (ROf T L V₁ : Set G))

omit [Finite G] in
theorem kJ_le (T L V₁ K : Subgroup G) :
    kJ T L V₁ K ≤ K ⊓ Subgroup.normalizer (ROf T L V₁ : Set G) :=
  perfectCore_le _

theorem lOf_le_kJ {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K) : LOf L V₁ ≤ kJ T L V₁ K :=
  le_perfectCore_of_perfect (le_inf hLK (lOf_le_normalizer_rOf T L V₁)) (perfectCore_perfect _)

omit [Finite G] in
theorem T_le_normalizer_kJ {V₁ K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer (kJ T L V₁ K : Set G) := fun _ ht =>
  normalizer_le_normalizer_perfectCore _ (SecD.mem_normalizer_inf (hTK ht)
    (Subgroup.le_normalizer (T_le_normalizer_rOf T L V₁ ht)))

theorem exists_kJ_preimage (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (φ : ↥K →* SL(2, ZMod p)) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K)
    (hRK : ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K) :
    ∀ s : SL(2, ZMod p), ∃ k : ↥K, (k : G) ∈ kJ T L V₁ K ∧ φ k = s := by
  set H₁ : Subgroup ↥K := (K ⊓ Subgroup.normalizer (ROf T L V₁ : Set G)).subgroupOf K with hH₁
  have hdec := exists_mul_of_rOf h hLK hTK hRK
  have hmap : H₁.map φ = ⊤ := by
    rw [eq_top_iff]
    intro s _
    obtain ⟨g, rfl⟩ := hφs s
    obtain ⟨o, ho, k, hk, hgk⟩ := hdec g g.2
    refine ⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    have ho' : φ ⟨o, SecD.oTwoTwoPrime_le K ho⟩ = 1 := (hφk _).mpr ho
    have hg : g = ⟨o, SecD.oTwoTwoPrime_le K ho⟩ * ⟨k, hk.1⟩ := Subtype.ext hgk
    rw [hg, map_mul, ho', one_mul]
  have hperf : perfectCore (⊤ : Subgroup (SL(2, ZMod p))) = ⊤ := by
    apply perfectCore_eq_self_of_perfect
    rw [← commutator_def]
    exact (A1c.sl2_isPerfect hp5).commutator_eq_top
  have hcore := map_perfectCore φ H₁
  rw [hmap, hperf] at hcore
  have hKJ : (perfectCore H₁).map K.subtype = kJ T L V₁ K := by
    rw [map_perfectCore, hH₁, Subgroup.subgroupOf_map_subtype, inf_right_comm, inf_idem]
  intro s
  have hs : s ∈ (perfectCore H₁).map φ := hcore ▸ Subgroup.mem_top s
  obtain ⟨k, hk, rfl⟩ := hs
  exact ⟨k, hKJ ▸ ⟨k, hk, rfl⟩, rfl⟩

theorem le_centralizer_of_kJ (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (φ : ↥K →* SL(2, ZMod p)) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K)
    (hRK : ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K) {C : Subgroup G}
    (hO : oTwoTwoPrime K ≤ C) (hJ : kJ T L V₁ K ≤ C) : K ≤ C := by
  intro g hg
  obtain ⟨k, hk, hφ⟩ := exists_kJ_preimage h hLK hTK hp5 φ hφs hφk hRK (φ ⟨g, hg⟩)
  have h1 : φ (⟨g, hg⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, hφ, mul_inv_cancel]
  have h2 := hO ((hφk _).mp h1)
  have e : g = ((⟨g, hg⟩ * k⁻¹ : ↥K) : G) * k := by simp
  rw [e]
  exact C.mul_mem h2 (hJ hk)

theorem mem_rOf_of_theta (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} [Fact p.Prime]
    (φ : ↥K →* SL(2, ZMod p)) (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K)
    (hinv : ∀ k : ↥K, φ k = A1c.sl2NegOne p → ∀ o : ↥K, (o : G) ∈ oTwoTwoPrime K →
      ((k * o * k⁻¹ * o : ↥K) : G) ∈ pCoreOf 2 K)
    {r : G} (hrR : r ∈ ROf T L V₁) (hrK : r ∈ K) (hφr : φ ⟨r, hrK⟩ = A1c.sl2NegOne p)
    (k : ↥K) (hk : (k : G) ∈ kJ T L V₁ K)
    (hk1 : φ k = 1 ∨ φ k = A1c.sl2NegOne p) : (k : G) ∈ ROf T L V₁ := by
  have hkN := (kJ_le T L V₁ K hk).2
  have hle := inf_normalizer_le_rOf h hLK hTK φ hinv hrR hrK hφr
  rcases hk1 with h1 | h1
  · exact hle ⟨(hφk k).mp h1, hkN⟩
  · have h2 : φ (k * ⟨r, hrK⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, hφr, mul_inv_cancel]
    have h3 : ((k * ⟨r, hrK⟩⁻¹ : ↥K) : G) ∈ ROf T L V₁ :=
      hle ⟨(hφk _).mp h2, Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ (Subgroup.le_normalizer hrR))⟩
    have e : (k : G) = ((k * ⟨r, hrK⟩⁻¹ : ↥K) : G) * r := by simp
    rw [e]
    exact (ROf T L V₁).mul_mem h3 hrR

end CFSG.Quasithin.Vol2.Ch11.SecE
