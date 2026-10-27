module

public import CFSG.Milestones.ASVolI.C61.HypBase
public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped MatrixGroups

theorem burnsideC56_sl2_of_isPSL {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      Nonempty (Y ≃* SL(2, K)) := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn : 2 ≤ n := by
    by_contra hlt
    have h1 : n = 1 := by omega
    subst h1
    exact hne rfl
  let _ : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  exact ⟨hn, K, inferInstance, inferInstance, hK', ⟨(e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      CFSG.Walter.psl2MulEquivSL2OfCharTwo⟩⟩

theorem burnsideC56_sl2_nonabelian (K : Type) [Field K] : ∃ a b : SL(2, K), a * b ≠ b * a := by
  refine ⟨burnsideC5h_p1_utri 1, burnsideC5h_p1_ltri 1, fun h => ?_⟩
  have h1 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_mul, burnsideC5h_p1_coe_utri, burnsideC5h_p1_coe_ltri,
    Matrix.mul_apply, Fin.sum_univ_two] at h1

theorem burnsideC56_sl2_isSimple {K : Type} [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = 2 ^ n) : IsSimpleGroup SL(2, K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  have h4 : 4 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem burnsideC56_sl2_card {K : Type} [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = 2 ^ n) : 60 ≤ Nat.card SL(2, K) ∧ 2 ∣ Nat.card SL(2, K) := by
  rw [burnsideC5h_p1_sl2_card K, hK]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
  refine ⟨?_, Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _⟩
  calc 60 = 4 * 15 := by norm_num
    _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h4 (by omega)

theorem burnsideC56_isPSL_simple {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    IsSimpleGroup Y := by
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  have := burnsideC56_sl2_isSimple hn hK
  exact e.isSimpleGroup

theorem burnsideC56_isPSL_nonabelian {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  obtain ⟨a, b, hab⟩ := burnsideC56_sl2_nonabelian K
  refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
  have := congrArg e h'
  simpa using this

theorem burnsideC56_isPSL_card {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    60 ≤ Nat.card Y ∧ 2 ∣ Nat.card Y := by
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  rw [Nat.card_congr e.toEquiv]
  exact burnsideC56_sl2_card hn hK

theorem burnsideC56_isPSL_umax {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S := by
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  exact burnsideC56_umax_of_mulEquiv e fun S hS hSi =>
    burnsideC5h_p1_umax_sl2 (F := K) (n := n) (by omega) hK hS hSi

section Dickson

open CFSG.GH74.GLS.IVK.Lifted in
theorem burnsideC56_catalog_of_quotient_psl2_even {m : ℕ} (hm : m ≠ 0) {S : Type} [Group S]
    [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a)
    (σ : PSL(2, GaloisField 2 m) →* S) (hσ : Function.Surjective σ) :
    CFSG.Blueprint.Catalog S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm
  by_cases h1 : m = 1
  · exfalso
    subst h1
    apply not_isSolvable_of_simple_nonabelian hab
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 2 ^ 1 * 3 ^ 1 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
      norm_num
    have hsl := isSolvable_of_card_two_three hc
    have hpsl : Group.IsSolvable (PSL(2, GaloisField 2 1)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1))))
    exact Group.isSolvable_of_surjective hσ
  · have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsimple : IsSimpleGroup (PSL(2, GaloisField 2 m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcard]; exact h4)
    have hinj := injective_of_surjective_simple σ hσ
    let e : PSL(2, GaloisField 2 m) ≃* S := MulEquiv.ofBijective σ ⟨hinj, hσ⟩
    have hLie : CFSG.Blueprint.LieModel S .PSL 2 2 m :=
      Or.inl ⟨by decide, statedClassicalModel_psl_two_lifted 2 m h4 e.symm⟩
    exact CFSG.Blueprint.lieModel_catalog S _ _ _ _ hLie

open CFSG.GH74.GLS.IVK.Lifted in
theorem burnsideC56_catalog_of_psl2_subgroup_quotient_even {F : Type} [Field F] [Finite F]
    {f : ℕ} (hf : f ≠ 0) (hF : Nat.card F = 2 ^ f) (Hb : Subgroup PSL(2, F))
    {S : Type} [Group S] [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a) (ρ : ↥Hb →* S)
    (hρ : Function.Surjective ρ) : CFSG.Blueprint.Catalog S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∀ {m : ℕ}, m ∣ f → m ≠ 0 := fun {m} hm h0 => hf (by
    rw [h0] at hm
    exact zero_dvd_iff.1 hm)
  rcases psl2_subgroup_dichotomy hF Hb with hsolv | hA5 | ⟨m, hm, hPSL⟩ | ⟨m, hm, hPGL⟩
  · exact absurd (Group.isSolvable_of_surjective hρ) (not_isSolvable_of_simple_nonabelian hab)
  · obtain ⟨e⟩ := hA5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : Function.Surjective (ρ.comp e.symm.toMonoidHom) := hρ.comp e.symm.surjective
    have hinj := injective_of_surjective_simple (ρ.comp e.symm.toMonoidHom) hs
    exact Or.inr (Or.inl ⟨5, le_rfl,
      ⟨(MulEquiv.ofBijective (ρ.comp e.symm.toMonoidHom) ⟨hinj, hs⟩).symm⟩⟩)
  · obtain ⟨e⟩ := hPSL
    exact burnsideC56_catalog_of_quotient_psl2_even (hne hm) hab (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.surjective)
  · obtain ⟨e⟩ := hPGL
    have hm0 : m ≠ 0 := hne (Dvd.dvd.trans (dvd_mul_left m 2) hm)
    let σ : PSL(2, GaloisField 2 m) →* S :=
      (ρ.comp e.symm.toMonoidHom).comp
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField 2 m))
    have hσ : Function.Surjective σ :=
      (hρ.comp e.symm.surjective).comp
        (CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective (GaloisField 2 m))
    exact burnsideC56_catalog_of_quotient_psl2_even hm0 hab σ hσ

theorem burnsideC56_sl2_isKGroupCat {F : Type} [Field F] [Finite F] {f : ℕ} (hf : f ≠ 0)
    (hF : Nat.card F = 2 ^ f) : CFSG.SectionRank.IsKGroupCat SL(2, F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  intro H N hN hS
  by_cases hab : ∀ a b : H ⧸ N, a * b = b * a
  · exact CFSG.Quasithin.H13.U3.GC137.SQ.catalog_of_comm hab
  · push Not at hab
    let ε : SL(2, F) ≃* PSL(2, F) := (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
    let ι : ↥H ≃* ↥(H.map ε.toMonoidHom) := H.equivMapOfInjective ε.toMonoidHom ε.injective
    let ρ : ↥(H.map ε.toMonoidHom) →* H ⧸ N := (QuotientGroup.mk' N).comp ι.symm.toMonoidHom
    have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective N).comp ι.symm.surjective
    exact burnsideC56_catalog_of_psl2_subgroup_quotient_even hf hF _ hab ρ hρ

theorem burnsideC56_card_alt_four : Nat.card ↥(alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem burnsideC56_sl2_rankLeTwo {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) : CFSG.Quasithin.H13.U3.GC137.SQ.RankLeTwo SL(2, F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  intro p hp hp2 E hE
  have : Fact p.Prime := ⟨hp⟩
  let ε : SL(2, F) ≃* PSL(2, F) := (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
  set Eb : Subgroup PSL(2, F) := E.map ε.toMonoidHom with hEb
  have hcard : Nat.card Eb = Nat.card E := Subgroup.card_map_of_injective ε.injective
  have hEp : IsPGroup p E := CFSG.Quasithin.H13.U3.GC137.SQ.isPGroup_of_isElemAbelian hE
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hodd : ¬ 2 ∣ Nat.card E := by
    rw [hk]
    intro h2
    have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  have hev : ∀ (X : Type) [Group X], 2 ∣ Nat.card X → Nonempty (↥Eb ≃* X) → False := by
    intro X _ h2 ⟨e⟩
    rw [← Nat.card_congr e.toEquiv, hcard] at h2
    exact hodd h2
  have hpos : 0 < p := hp.pos
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF Eb with
    ⟨m, -, hcm, -⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ |
      ⟨m, t, hm1, -, -, -, E', C, -, -, hE'card, -⟩ | ⟨m, hm, he⟩ | ⟨m, hm, he⟩
  · rw [hcard] at hcm
    have hm0 : m = 0 := by
      by_contra h0
      exact hodd (hcm ▸ dvd_pow_self 2 h0)
    rw [hcm, hm0, pow_zero]
    exact Nat.one_le_pow _ _ hpos
  · have hexp : Monoid.exponent ↥Eb ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨y, hy, hyx⟩ := x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hyx, ← map_pow, hE.2 y hy, map_one, Subgroup.coe_one]
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    calc Nat.card E ≤ p := Nat.le_of_dvd hpos hexp
      _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  · exact (hev _ (by rw [DihedralGroup.nat_card]; exact dvd_mul_right 2 z) he).elim
  · exact (hev _ (by rw [burnsideC56_card_alt_four]; norm_num) he).elim
  · refine (hev _ ?_ he).elim
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  · exact (hev _ (by rw [burnsideC56_card_alt_five]; norm_num) he).elim
  · exfalso
    apply hodd
    rw [← hcard]
    have h1 : 2 ∣ Nat.card E' := by
      rw [hE'card]
      exact dvd_pow_self 2 (by omega)
    exact h1.trans (Subgroup.card_subgroup_dvd_card E')
  · exact (hev _ (CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.two_dvd_natCard_psl2 _) he).elim
  · refine (hev _ ?_ he).elim
    rw [CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.card_pgl2_eq_mul]
    exact Dvd.dvd.mul_right (CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.two_dvd_natCard_psl2 _) _

theorem burnsideC56_isPSL_isKGroupCat {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    CFSG.SectionRank.IsKGroupCat Y := by
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv
    (burnsideC56_sl2_isKGroupCat (F := K) (by omega) hK') e

theorem burnsideC56_isPSL_rankLeTwo {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    CFSG.Quasithin.H13.U3.GC137.SQ.RankLeTwo Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := burnsideC56_sl2_of_isPSL h
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  exact CFSG.Quasithin.H13.U3.GC137.SQ.rankLeTwo_of_mulEquiv e
    (burnsideC56_sl2_rankLeTwo (F := K) hK')

end Dickson

end CFSG.ASVolI
