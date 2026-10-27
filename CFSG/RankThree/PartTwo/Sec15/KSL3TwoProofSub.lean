module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def KS1522OutThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r f : ℕ) [Fact r.Prime], IsLThreeEpsAt S r f →
    ¬ 9 ∣ Nat.card S → ∀ α : MulAut S, α ^ 3 = 1 → ∃ s : S, ∀ x : S, α x = s * x * s⁻¹

namespace KSL3Two

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

section GroupTheory

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_mul_mem_centralizer {M : Subgroup G} [Finite M] (hM3 : ¬ 3 ∣ Nat.card M)
    {t x : G} (ht3 : t ^ 3 = 1) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (htx : x⁻¹ * (t * x * t⁻¹) ∈ M) : ∃ m ∈ M, t * (x * m) * t⁻¹ = x * m := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ m ∈ M, x⁻¹ * (t * (x * m) * t⁻¹) ∈ M := by
    intro m hm
    have e : x⁻¹ * (t * (x * m) * t⁻¹) = (x⁻¹ * (t * x * t⁻¹)) * (t * m * t⁻¹) := by group
    rw [e]
    exact mul_mem htx (htM m hm)
  let φ : Function.End M := fun m => ⟨x⁻¹ * (t * (x * m) * t⁻¹), hmem m m.2⟩
  have hφ3 : φ ^ 3 ^ 1 = 1 := by
    rw [pow_one, pow_three, Function.End.mul_def, Function.End.mul_def]
    funext m
    apply Subtype.ext
    simp only [φ, Function.comp_apply, Function.End.one_def, id]
    have ht3' : t * t * t = 1 := by rw [← pow_three', ht3]
    calc x⁻¹ * (t * (x * (x⁻¹ * (t * (x * (x⁻¹ * (t * (x * ↑m) * t⁻¹))) * t⁻¹))) * t⁻¹)
        = x⁻¹ * ((t * t * t) * (x * ↑m) * (t * t * t)⁻¹) := by group
      _ = ↑m := by rw [ht3']; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq hφ3
  have hcard : Fintype.card M = Nat.card M := Fintype.card_eq_nat_card
  obtain ⟨⟨m, hfix⟩⟩ : Nonempty (Function.fixedPoints φ) := by
    rw [← Fintype.card_pos_iff]
    by_contra h0
    push Not at h0
    have h0' : Fintype.card (Function.fixedPoints φ) = 0 := by omega
    rw [h0', hcard] at hmod
    exact hM3 (Nat.modEq_zero_iff_dvd.mp hmod)
  refine ⟨m, m.2, ?_⟩
  have h := congrArg Subtype.val (show φ m = m from hfix)
  simp only [φ] at h
  calc t * (x * ↑m) * t⁻¹ = x * (x⁻¹ * (t * (x * ↑m) * t⁻¹)) := by group
    _ = x * ↑m := by rw [h]

theorem eight_dvd (q : ℕ) (s : ℕ → ℕ) (hs : ∀ q, Odd q → 2 ∣ s q) :
    8 ∣ q ^ 3 * ((q ^ 2 - 1) * s q) := by
  rcases Nat.even_or_odd q with ⟨k, rfl⟩ | hq
  · exact Dvd.dvd.mul_right (⟨k ^ 3, by ring⟩) _
  · obtain ⟨k, rfl⟩ := hq
    have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    obtain ⟨u, hu⟩ := hs _ ⟨k, rfl⟩
    rw [h1, hj, hu]
    exact Dvd.intro ((2 * k + 1) ^ 3 * (2 * (j * u))) (by ring)

theorem isSimpleGroup_and_not_isSolvable {S : Type} [Group S] {r f : ℕ} [Fact r.Prime]
    (hS : IsLThreeEpsAt S r f) : IsSimpleGroup S ∧ ¬ Group.IsSolvable S := by
  have key : ∀ {T : Type} [Group T], IsSimpleGroup T → 8 ∣ Nat.card T →
      ¬ Group.IsSolvable T := by
    intro T _ hT h8 hsol
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := T)).mpr hsol
    let _ : CommGroup T := { ‹Group T› with mul_comm := hcomm }
    have hp : (Nat.card T).Prime := IsSimpleGroup.prime_card
    have h2 : 2 ∣ Nat.card T := (show (2 : ℕ) ∣ 8 by norm_num).trans h8
    have h2' : Nat.card T = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    rw [h2'] at h8
    norm_num at h8
  have hcop : ∀ m : ℕ, Nat.Coprime 8 (Nat.gcd 3 m) := fun m =>
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 m) (by norm_num)
  rcases hS with hL | ⟨hq2, ⟨φ⟩⟩
  · obtain ⟨φ⟩ := hL
    have hsimp : IsSimpleGroup (projSL 3 (GaloisField r f)) :=
      Sec4.Item462AltProof.isSimpleGroup_projSL_three _
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField r f)
    have h8 : 8 ∣ Nat.card (projSL 3 (GaloisField r f)) := by
      refine (hcop (Nat.card (GaloisField r f) - 1)).dvd_of_dvd_mul_right ?_
      rw [hc]
      exact eight_dvd _ (fun q => q ^ 3 - 1) fun q hq => by
        have : Odd (q ^ 3) := hq.pow
        obtain ⟨k, hk⟩ := this
        exact ⟨k, by omega⟩
    exact ⟨φ.isSimpleGroup, fun hsol => key hsimp h8
      (Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective)⟩
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq2
      · exact h
    have hsimp : IsSimpleGroup (projSU 3 r f) :=
      Sec4.Item462AltProof.isSimpleGroup_projSU_three r f hf (by omega)
    have hc := KFacts.KS14.card_projSU_three_mul_gcd r f hf
    have h8 : 8 ∣ Nat.card (projSU 3 r f) := by
      refine (hcop (r ^ f + 1)).dvd_of_dvd_mul_right ?_
      rw [hc]
      exact eight_dvd _ (fun q => q ^ 3 + 1) fun q hq => by
        have : Odd (q ^ 3) := hq.pow
        obtain ⟨k, hk⟩ := this
        exact ⟨k + 1, by omega⟩
    exact ⟨φ.isSimpleGroup, fun hsol => key hsimp h8
      (Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective)⟩

end GroupTheory

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem not_eightyOne_dvd {q : ℕ} (hq : ModThree π q) (h9 : ¬ (q % 9 = 1 ∨ q % 9 = 8)) :
    ¬ 81 ∣ q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
  have h1 : 1 ≤ q := by
    cases π
    · change q % 3 = 2 at hq; omega
    · change q % 3 = 1 at hq; omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h1
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ h1
  have hr : (q : ZMod 81).val = q % 81 := ZMod.val_natCast _ _
  cases π
  · change q % 3 = 2 at hq
    change ¬ 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2]
    push_cast
    have key : ∀ x : ZMod 81, x.val % 3 = 2 → x.val % 9 ≠ 8 →
        x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) ≠ 0 := by decide
    refine key (q : ZMod 81) ?_ ?_
    · rw [hr, Nat.mod_mod_of_dvd _ (by norm_num)]; exact hq
    · rw [hr, Nat.mod_mod_of_dvd _ (by norm_num)]; omega
  · change q % 3 = 1 at hq
    change ¬ 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2,
      Nat.cast_sub h3]
    push_cast
    have key : ∀ x : ZMod 81, x.val % 3 = 1 → x.val % 9 ≠ 1 →
        x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) ≠ 0 := by decide
    refine key (q : ZMod 81) ?_ ?_
    · rw [hr, Nat.mod_mod_of_dvd _ (by norm_num)]; exact hq
    · rw [hr, Nat.mod_mod_of_dvd _ (by norm_num)]; omega

theorem not_dvd_card_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) :
    ¬ 27 ∣ Nat.card (projImage (slPi π 3 (p ^ f) K)) := by
  intro h27
  apply not_eightyOne_dvd hq h9
  rw [← Sec13.card_projImage_slPi_mul_three hK hq]
  exact Nat.mul_dvd_mul h27 (dvd_refl 3)

theorem isSolvable_inf_centralizer_of_lift (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {ŷ : GL (Fin 3) K} (hŷS : ŷ ∈ slPi π 3 (p ^ f) K) (hŷ3 : ŷ ^ 3 = 1)
    (hy1 : ProjGenLinGroup.mk ŷ ≠ 1) :
    Group.IsSolvable ↥(projImage (slPi π 3 (p ^ f) K) ⊓
      Subgroup.centralizer {ProjGenLinGroup.mk ŷ}) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdet : (ŷ : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hŷS).2
  have hŷs : ∀ c : K, (ŷ : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hy1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet
      exact zero_ne_one hdet
    exact mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hŷ3m : (ŷ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hŷ3, Units.val_one]
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hŷ3m hdet hŷs
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  set Q := P⁻¹ with hQ
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hcomm : ∀ {M M' : Matrix (Fin 3) (Fin 3) K},
      M * (ŷ : Matrix (Fin 3) (Fin 3) K) = (ŷ : Matrix (Fin 3) (Fin 3) K) * M →
      M' * (ŷ : Matrix (Fin 3) (Fin 3) K) = (ŷ : Matrix (Fin 3) (Fin 3) K) * M' →
      M * M' = M' * M := by
    intro M M' hM hM'
    have hY : ∀ N : Matrix (Fin 3) (Fin 3) K,
        N * (ŷ : Matrix (Fin 3) (Fin 3) K) = (ŷ : Matrix (Fin 3) (Fin 3) K) * N →
        N * (τ ^ (j : ℕ) • (ŷ : Matrix (Fin 3) (Fin 3) K)) =
          (τ ^ (j : ℕ) • (ŷ : Matrix (Fin 3) (Fin 3) K)) * N := by
      intro N hN
      rw [Matrix.mul_smul, Matrix.smul_mul, hN]
    have hd := eq_diagonal_of_commute hτ hτ1 (conj_commute hPQ hQP hPD (hY M hM))
    have hd' := eq_diagonal_of_commute hτ hτ1 (conj_commute hPQ hQP hPD (hY M' hM'))
    have hc : (Q * M * P) * (Q * M' * P) = (Q * M' * P) * (Q * M * P) := by
      rw [hd, hd', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      exact mul_comm _ _
    rw [conj_mul hPQ, conj_mul hPQ] at hc
    rw [← unconj hPQ (M * M'), hc, unconj hPQ]
  set L := slPi π 3 (p ^ f) K with hL
  set C := centMod L ŷ with hC
  have hker : Group.IsSolvable ↥(commHom L ŷ).ker := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have ha := (Subgroup.mem_subgroupOf.mp ((ker_commHom L ŷ).le a.2))
    have hb := (Subgroup.mem_subgroupOf.mp ((ker_commHom L ŷ).le b.2))
    have ha' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
    have hb' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hb).2
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    refine hcomm ?_ ?_
    · have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) ha'
      simp only [Units.val_mul] at h'
      exact h'
    · have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hb'
      simp only [Units.val_mul] at h'
      exact h'
  have hsc : Group.IsSolvable ↥(StatedScalars (Fin 3) K) := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    obtain ⟨u, hu⟩ := a.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u _).eq.symm
  have hCsol : Group.IsSolvable C :=
    Group.isSolvable_of_ker_le_range (commHom L ŷ).ker.subtype (commHom L ŷ)
      (by rw [Subgroup.range_subtype])
  set ρ : C →* ProjGenLinGroup (Fin 3) K := ProjGenLinGroup.mk.comp C.subtype with hρ
  have hρsol : Group.IsSolvable ρ.range :=
    Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  have hle : projImage L ⊓ Subgroup.centralizer {ProjGenLinGroup.mk ŷ} ≤ ρ.range := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨s, hs, rfl⟩ := hz1
    have hsc := Subgroup.mem_centralizer_singleton_iff.mp hz2
    refine ⟨⟨s, mem_centMod_iff_scalar.mpr ⟨hs, s * ŷ * s⁻¹ * ŷ⁻¹, ?_, by group⟩⟩, rfl⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hsc]
    group
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem isSolvable_inf_centralizer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {y : ProjGenLinGroup (Fin 3) K}
    (hyS : y ∈ projImage (slPi π 3 (p ^ f) K)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Group.IsSolvable ↥(projImage (slPi π 3 (p ^ f) K) ⊓ Subgroup.centralizer {y}) := by
  obtain ⟨ŷ, hŷS, rfl⟩ := hyS
  exact isSolvable_inf_centralizer_of_lift hK hq hŷS
    (pow_three_eq_one_of_lift hK h9 hŷS hy3) hy1

end Model

section Reduction

variable {X : Type} [Group X]

theorem isSolvable_centralizer [Finite X] {n : ℕ} (hn : 1 ≤ n) (hiso : Sec4.IsoLThreePi X 2 n)
    (h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) {e : X} (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({e} : Set X)) := by
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
  set S := projImage (slPi π 3 (2 ^ n) F) with hS
  set ψ : X →* Matrix.ProjGenLinGroup (Fin 3) F := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hsol : Group.IsSolvable ↥(S ⊓ Subgroup.centralizer {ψ e}) :=
    isSolvable_inf_centralizer hF hq (Sec16.not_nine_dvd_card_sub_one hF h9)
      (φ e).2 (by rw [← map_pow, he3, map_one])
      (fun h => he1 (hψinj (by rw [h, map_one])))
  have hmap : ∀ c : ↥(Subgroup.centralizer ({e} : Set X)),
      (ψ.comp (Subgroup.centralizer ({e} : Set X)).subtype) c ∈
        S ⊓ Subgroup.centralizer {ψ e} := by
    intro c
    refine Subgroup.mem_inf.mpr ⟨(φ c).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, hc]
  set ι := (ψ.comp (Subgroup.centralizer ({e} : Set X)).subtype).codRestrict
    (S ⊓ Subgroup.centralizer {ψ e}) hmap with hι
  refine Group.isSolvable_of_isSolvable_injective (f := ι) fun a b h => Subtype.ext (hψinj ?_)
  have h' := congrArg Subtype.val h
  simpa [hι] using h'

end Reduction

end KSL3Two

open KSL3Two

theorem ks1522HessSub_of (hOut : KS1522OutThree) : KS1522HessSub := by
  intro X _ _ n hn hiso h9 E hEa hE9 K hEK N _ hN2 r f _ hS
  by_contra hEK'
  obtain ⟨e, heE, heK⟩ := Set.not_subset.mp hEK'
  obtain ⟨hSsimp, hSsol⟩ := isSimpleGroup_and_not_isSolvable hS
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
  have h27 : ¬ 27 ∣ Nat.card X := by
    rw [Nat.card_congr φ.toEquiv]
    exact not_dvd_card_projImage hF hq h9
  have hK9 : ¬ 9 ∣ Nat.card K := by
    intro h9K
    have hprod := card_sup_mul_card_inf hEK
    rw [hE9] at hprod
    have hinf : Nat.card (E ⊓ K : Subgroup X) ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card (E ⊓ K : Subgroup X) ≠ 9 := by
      intro h
      apply heK
      have hEK2 : E ⊓ K = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hE9])
      have heEK : e ∈ E ⊓ K := by
        rw [hEK2]
        exact heE
      exact heEK.2
    have hle3 : Nat.card (E ⊓ K : Subgroup X) ∣ 3 := by
      have hdv : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [hdv] at hinf
      obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hinf
      interval_cases i
      · rw [hik]; norm_num
      · rw [hik]; norm_num
      · exact absurd (by rw [hik]; norm_num) hne
    apply h27
    have h81 : 81 ∣ Nat.card (E ⊔ K : Subgroup X) * Nat.card (E ⊓ K : Subgroup X) := by
      rw [hprod]
      exact Nat.mul_dvd_mul (dvd_refl 9) h9K
    have h27s : 27 ∣ Nat.card (E ⊔ K : Subgroup X) := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hle3 with h1 | h1
      · rw [h1, mul_one] at h81
        exact (by norm_num : (27 : ℕ) ∣ 81).trans h81
      · rw [h1] at h81
        omega
    exact h27s.trans (Subgroup.card_subgroup_dvd_card _)
  have hS9 : ¬ 9 ∣ Nat.card (↥K ⧸ N) := by
    intro h
    apply hK9
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    exact Dvd.dvd.mul_right h _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNinv : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)),
      N.map (K.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom = N := by
    intro t ht
    set σ := K.normalizerMonoidHom ⟨t, ht⟩ with hσ
    have hNσ : (N.map σ.toMonoidHom).Normal :=
      Subgroup.Normal.map ‹N.Normal› σ.toMonoidHom σ.surjective
    set M := (N.map σ.toMonoidHom).map (QuotientGroup.mk' N) with hMdef
    have hMn : M.Normal := Subgroup.Normal.map hNσ _ (QuotientGroup.mk'_surjective N)
    have hM2 : IsPGroup 2 M := (hN2.map σ.toMonoidHom).map _
    rcases hSsimp.eq_bot_or_eq_top_of_normal M with hM | hM
    · have hle : N.map σ.toMonoidHom ≤ N := by
        intro x hx
        have hxM : QuotientGroup.mk' N x ∈ M := ⟨x, hx, rfl⟩
        rw [hM, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxM
        exact hxM
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective])
    · exfalso
      apply hSsol
      have hP : IsPGroup 2 (↥K ⧸ N) := by
        rw [hM] at hM2
        exact hM2.of_equiv Subgroup.topEquiv
      have := hP.isNilpotent
      infer_instance
  have heN : e ∈ Subgroup.normalizer (K : Set X) := hEK heE
  have he3 : e ^ 3 = 1 := hEa.2 e heE
  set σ := K.normalizerMonoidHom ⟨e, heN⟩ with hσ
  set α : MulAut (↥K ⧸ N) := QuotientGroup.congr N N σ (hNinv e heN) with hα
  have hαmk : ∀ x : ↥K, α (QuotientGroup.mk x) = QuotientGroup.mk (σ x) := fun x =>
    QuotientGroup.congr_mk N N σ (hNinv e heN) x
  have hα3 : α ^ 3 = 1 := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hαmk, hαmk, hαmk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      change e * (e * (e * (x : X) * e⁻¹) * e⁻¹) * e⁻¹ = (x : X)
      have he3' : e * e * e = 1 := by rw [← pow_three', he3]
      calc e * (e * (e * (x : X) * e⁻¹) * e⁻¹) * e⁻¹
          = (e * e * e) * (x : X) * (e * e * e)⁻¹ := by group
        _ = (x : X) := by rw [he3']; group
  obtain ⟨s, hs⟩ := hOut (↥K ⧸ N) r f hS hS9 α hα3
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  set N' : Subgroup X := N.map K.subtype with hN'
  have hmemN' : ∀ m : ↥K, (m : X) ∈ N' ↔ m ∈ N := fun m =>
    ⟨fun ⟨m₀, hm₀, h⟩ => (Subtype.ext h : m₀ = m) ▸ hm₀, fun hm => ⟨m, hm, rfl⟩⟩
  have hN'K : ∀ m ∈ N', m ∈ K := by
    rintro _ ⟨m₀, -, rfl⟩
    exact m₀.2
  let Pr : X → Prop := fun t => t ∈ Subgroup.normalizer (K : Set X) ∧
    (∀ m ∈ N', t * m * t⁻¹ ∈ N') ∧ (∀ x ∈ K, x⁻¹ * (t * x * t⁻¹) ∈ N')
  have hPr1 : Pr 1 := ⟨one_mem _, fun m hm => by simpa using hm,
    fun x _ => by simp⟩
  have hPrmul : ∀ t t', Pr t → Pr t' → Pr (t * t') := by
    rintro t t' ⟨htK, htN, htc⟩ ⟨ht'K, ht'N, ht'c⟩
    refine ⟨mul_mem htK ht'K, fun m hm => ?_, fun x hx => ?_⟩
    · have := htN _ (ht'N m hm)
      simpa [mul_assoc] using this
    · have hy : t' * x * t'⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp ht'K x).mp hx
      have h1 := ht'c x hx
      have h2 := htc _ hy
      have e1 : x⁻¹ * (t * t' * x * (t * t')⁻¹) =
          (x⁻¹ * (t' * x * t'⁻¹)) * ((t' * x * t'⁻¹)⁻¹ * (t * (t' * x * t'⁻¹) * t⁻¹)) := by
        group
      rw [e1]
      exact mul_mem h1 h2
  have hPrpow : ∀ t, Pr t → ∀ m : ℕ, Pr (t ^ m) := by
    intro t ht m
    induction m with
    | zero => simpa using hPr1
    | succ m ih => rw [pow_succ]; exact hPrmul _ _ ih ht
  set g : X := (k : X)⁻¹ * e with hg
  have hkN : (k : X) ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer k.2
  have hPg : Pr g := by
    refine ⟨mul_mem (inv_mem hkN) heN, fun m hm => ?_, fun x hx => ?_⟩
    · obtain ⟨m₀, hm₀, rfl⟩ := hm
      change g * (m₀ : X) * g⁻¹ ∈ N'
      have hσm : σ m₀ ∈ N := by
        rw [← hNinv e heN]
        exact ⟨m₀, hm₀, rfl⟩
      have hk : (k⁻¹ * σ m₀ * k⁻¹⁻¹ : ↥K) ∈ N := ‹N.Normal›.conj_mem _ hσm k⁻¹
      have e1 : g * (m₀ : X) * g⁻¹ = ((k⁻¹ * σ m₀ * k⁻¹⁻¹ : ↥K) : X) := by
        change (k : X)⁻¹ * e * (m₀ : X) * ((k : X)⁻¹ * e)⁻¹ =
          (k : X)⁻¹ * (e * (m₀ : X) * e⁻¹) * ((k : X)⁻¹)⁻¹
        group
      rw [e1]
      exact (hmemN' _).mpr hk
    · set x₀ : ↥K := ⟨x, hx⟩ with hx₀
      have h1 := hs (QuotientGroup.mk x₀)
      rw [hαmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq] at h1
      have h1' : (k * x₀ * k⁻¹)⁻¹ * σ x₀ ∈ N := by
        rw [show (k * x₀ * k⁻¹)⁻¹ * σ x₀ = ((σ x₀)⁻¹ * (k * x₀ * k⁻¹))⁻¹ by group]
        exact inv_mem h1
      have h2 : (k⁻¹ * ((k * x₀ * k⁻¹)⁻¹ * σ x₀) * k⁻¹⁻¹ : ↥K) ∈ N :=
        ‹N.Normal›.conj_mem _ h1' k⁻¹
      have e1 : x⁻¹ * (g * x * g⁻¹) =
          ((k⁻¹ * ((k * x₀ * k⁻¹)⁻¹ * σ x₀) * k⁻¹⁻¹ : ↥K) : X) := by
        change x⁻¹ * ((k : X)⁻¹ * e * x * ((k : X)⁻¹ * e)⁻¹) =
          (k : X)⁻¹ * (((k : X) * x * (k : X)⁻¹)⁻¹ * (e * x * e⁻¹)) * ((k : X)⁻¹)⁻¹
        group
      rw [e1]
      exact (hmemN' _).mpr h2
  have hgK : g ∉ K := by
    intro hgK
    apply heK
    have : e = (k : X) * g := by rw [hg]; group
    rw [this]
    exact mul_mem k.2 hgK
  have hg3 : g ^ 3 ∈ K := by
    have e1 : g ^ 3 = (k : X)⁻¹ * (e * (k : X)⁻¹ * e⁻¹) * ((e * e) * (k : X)⁻¹ * (e * e)⁻¹) *
        (e * e * e) := by
      rw [pow_three', hg]
      group
    have he3' : e * e * e = 1 := by rw [← pow_three', he3]
    rw [e1, he3', mul_one]
    have hee : e * e ∈ Subgroup.normalizer (K : Set X) := mul_mem heN heN
    exact mul_mem (mul_mem (inv_mem k.2)
      ((Subgroup.mem_normalizer_iff.mp heN _).mp (inv_mem k.2)))
      ((Subgroup.mem_normalizer_iff.mp hee _).mp (inv_mem k.2))
  set o := orderOf g with ho
  have ho0 : 0 < o := orderOf_pos g
  have h3o : 3 ∣ o := by
    by_contra h3
    have hcop : Nat.Coprime 3 o := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have ho1 : o ≠ 1 := by
      intro h1
      apply hgK
      rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    apply hgK
    have : g = (g ^ 3) ^ t := by
      rw [← pow_mul, ← pow_mod_orderOf, ← ho, ht, pow_one]
    rw [this]
    exact Subgroup.pow_mem _ hg3 t
  obtain ⟨c, hc⟩ := h3o
  have hc0 : c ≠ 0 := by
    rintro rfl
    omega
  set es := g ^ c with hes
  have hes_ord : orderOf es = 3 := by
    rw [hes, orderOf_pow_of_dvd hc0 ⟨3, by rw [← ho, hc]; ring⟩, ← ho, hc,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]
  have hes3 : es ^ 3 = 1 := by rw [← hes_ord]; exact pow_orderOf_eq_one es
  have hes1 : es ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hes_ord
    omega
  have hPes : Pr es := hPrpow g hPg c
  have hN'card : ¬ 3 ∣ Nat.card N' := by
    rw [hN', Subgroup.card_map_of_injective K.subtype_injective]
    obtain ⟨m, hm⟩ := hN2.exists_card_eq
    rw [hm]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hcop : ∀ x ∈ K, ∃ m ∈ N', es * (x * m) * es⁻¹ = x * m := fun x hx =>
    exists_mul_mem_centralizer hN'card hes3 hPes.2.1 (hPes.2.2 x hx)
  set C : Subgroup X := K ⊓ Subgroup.centralizer ({es} : Set X) with hC
  set χ : C →* ↥K ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion inf_le_left) with hχ
  have hχs : Function.Surjective χ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨m, hmN', hm⟩ := hcop x x.2
    obtain ⟨m₀, hm₀, rfl⟩ := hmN'
    have hm' : es * ((x : X) * (m₀ : X)) * es⁻¹ = (x : X) * (m₀ : X) := hm
    have hcomm : es * ((x : X) * (m₀ : X)) = (x : X) * (m₀ : X) * es := by
      calc es * ((x : X) * (m₀ : X)) = es * ((x : X) * (m₀ : X)) * es⁻¹ * es := by group
        _ = (x : X) * (m₀ : X) * es := by rw [hm']
    have hxm : (x : X) * (m₀ : X) ∈ C := by
      refine ⟨mul_mem x.2 m₀.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      first
        | exact hcomm
        | exact hcomm.symm
    refine ⟨⟨(x : X) * (m₀ : X), hxm⟩, ?_⟩
    rw [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    apply QuotientGroup.eq.mpr
    have : (Subgroup.inclusion (inf_le_left : C ≤ K) ⟨(x : X) * (m₀ : X), hxm⟩)⁻¹ * x =
        m₀⁻¹ := by
      apply Subtype.ext
      change ((x : X) * (m₀ : X))⁻¹ * (x : X) = ((m₀⁻¹ : ↥K) : X)
      rw [Subgroup.coe_inv]
      group
    rw [this]
    exact inv_mem hm₀
  have hCsol : Group.IsSolvable C := by
    have := isSolvable_centralizer hn hiso h9 hes3 hes1
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : C ≤ Subgroup.centralizer ({es} : Set X)))
      (Subgroup.inclusion_injective _)
  exact hSsol (Group.isSolvable_of_surjective hχs)

end CFSG.RankThree.PartTwo.Sec15
