module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LieType.Simplicity.TrialityD4
import CFSG.LieType.Simplicity.Classical
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL StatedSU)
open CFSG.Blueprint

namespace Item2130Res3Proof

theorem three_ne_zero_of_not_dvd {K : Type} [Field K] [Finite K] (h : ¬ 3 ∣ Nat.card K) :
    ((3 : ℕ) : K) ≠ 0 := by
  intro h0
  have := Fintype.ofFinite K
  obtain ⟨m, hq, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).mp h0
  have hchar : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdvd
  rw [← Nat.card_eq_fintype_card, hchar] at hcard
  exact h (hcard ▸ dvd_pow_self 3 m.ne_zero)

theorem card_le_nine_of_det {K : Type} [Field K] [Finite K] (h3 : ((3 : ℕ) : K) ≠ 0)
    {X : Type} [Group X] (f : X →* GL (Fin 3) K) (hf : Function.Injective f)
    (hdet : ∀ x : X, ((f x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {E : Subgroup X} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hc : ∀ g ∈ E.map f, ∀ h ∈ E.map f, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have he : ∀ g ∈ E.map f, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hd : ∀ g ∈ E.map f, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact hdet a
  have h := PartOne.LIT.card_le_sq_of_det_gl Nat.prime_three h3 (by simp) (E.map f) hc he hd
  rw [Subgroup.card_map_of_injective hf] at h
  simpa using h

theorem not_isE27_of_isSLThreePiAt {X : Type} [Group X] {q : ℕ} (hX : Sec4.IsSLThreePiAt X q)
    {E : Subgroup X} (hE : Late.IsE27 E) : False := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨φ⟩⟩ | ⟨hK, hq, ⟨φ⟩⟩⟩ := hX
  · have h3 : ¬ 3 ∣ Nat.card K := by rw [hK]; omega
    have h := card_le_nine_of_det (three_ne_zero_of_not_dvd h3)
      ((StatedSL 3 K).subtype.comp φ.toMonoidHom)
      ((Subgroup.subtype_injective _).comp φ.injective)
      (fun x => PartOne.LIT.mem_closure_det (fun g hg => hg) _ (φ x).2) hE.1
    rw [hE.2] at h
    norm_num at h
  · have h3 : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro hd
      have := Nat.prime_three.dvd_of_dvd_pow hd
      omega
    have h := card_le_nine_of_det (three_ne_zero_of_not_dvd h3)
      ((StatedSU 3 q K).subtype.comp φ.toMonoidHom)
      ((Subgroup.subtype_injective _).comp φ.injective)
      (fun x => PartOne.LIT.mem_closure_det (fun g hg => hg.1) _ (φ x).2) hE.1
    rw [hE.2] at h
    norm_num at h

theorem not_isE27_of_SL3 {X : Type} [Group X] {n : ℕ} (hn : 0 < n) (φ : X ≃* SL3 n)
    {E : Subgroup X} (hE : Late.IsE27 E) : False := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h3 : ¬ 3 ∣ Nat.card (GaloisField 2 n) := by
    rw [hcard]
    intro hd
    have := Nat.prime_three.dvd_of_dvd_pow hd
    omega
  have h := card_le_nine_of_det (three_ne_zero_of_not_dvd h3)
    (Matrix.SpecialLinearGroup.toGL.comp φ.toMonoidHom)
    (Matrix.SpecialLinearGroup.toGL_injective.comp φ.injective)
    (fun x => (φ x).2) hE.1
  rw [hE.2] at h
  norm_num at h

variable {G : Type} [Group G] [Finite G]

theorem center_ne_bot {Y : Subgroup G} {b : G} (hbY : b ∈ Y) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hYb : Y ≤ Subgroup.centralizer ({b} : Set G)) : Subgroup.center (lBar Y) ≠ ⊥ := by
  obtain ⟨-, -, hN3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hbY3 : (⟨b, hbY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have h1 : ((⟨b, hbY⟩ : Y) : lBar Y) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    have := Sec13.eq_one_of_pow_three_pow_of_not_dvd hN3 h (k := 1) (by rw [pow_one, hbY3])
    exact hb1 (congrArg Subtype.val this)
  have hZ : ((⟨b, hbY⟩ : Y) : lBar Y) ∈ Subgroup.center (lBar Y) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hYb x.2))
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hZ
  exact h1 hZ

section Centre

variable {X : Type} [Group X]

theorem prod_ne_of_fst_ne {a b c d : ℕ} (h : a ≠ c) : (a, b) ≠ (c, d) := fun e =>
  h (congrArg Prod.fst e)

theorem prod_ne_of_snd_ne {a b c : ℕ} (h : b ≠ c) : (a, b) ≠ (a, c) := fun e =>
  h (congrArg Prod.snd e)

theorem center_eq_bot_of_isoLThreePi {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p) (he : 1 ≤ e)
    (hq : IsQuasisimple X) (h : Sec4.IsoLThreePi X p e) : Subgroup.center X = ⊥ := by
  have hp : p.Prime := Fact.out
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact Sec13.Res5Proof.center_eq_bot_of_projSL (n := 3) ⟨hp, he, by norm_num,
      prod_ne_of_fst_ne (by norm_num), prod_ne_of_fst_ne (by norm_num)⟩ hq φ
  · refine Sec13.Res5Proof.center_eq_bot_of_projSU (n := 3) ⟨hp, he, le_rfl, ?_⟩ hq φ
    refine prod_ne_of_snd_ne fun h => ?_
    have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    omega

theorem center_eq_bot_of_lieP
    {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hq : IsQuasisimple X)
    (h : ChevalleyExceptionalModel X .G2 p 1 ∨ Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))) ∨
      ∃ e : ℕ, 1 ≤ e ∧ Sec4.IsoLThreePi X p e) : Subgroup.center X = ⊥ := by
  have hp : p.Prime := Fact.out
  rcases h with hG2 | ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨e, he, hL⟩
  · have := (LieType.Simplicity.fam_g2_simplicity X p 1 hG2).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
  · exact Sec13.Res5Proof.center_eq_bot_of_projSp ⟨hp, le_rfl, le_rfl,
      prod_ne_of_snd_ne (by rw [pow_one]; omega)⟩ hq φ
  · exact Sec13.Res5Proof.center_eq_bot_of_projSU (n := 4) ⟨hp, le_rfl, by norm_num,
      prod_ne_of_fst_ne (by norm_num)⟩ hq φ
  · exact Sec13.Res5Proof.center_eq_bot_of_projSL (n := 4) ⟨hp, le_rfl, by norm_num,
      prod_ne_of_fst_ne (by norm_num), prod_ne_of_fst_ne (by norm_num)⟩ hq φ
  · exact center_eq_bot_of_isoLThreePi hp3 he hq hL

theorem center_eq_bot_of_alt7 (hq : IsQuasisimple X) (φ : X ≃* alternatingGroup (Fin 7)) :
    Subgroup.center X = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq φ

theorem center_eq_bot_of_table
    {Y : Subgroup X} [Finite X] (hq : IsQuasisimple (lBar Y)) {A : Subgroup X}
    (h : Table211 A Y) : Subgroup.center (lBar Y) = ⊥ := by
  have hs : ∀ s ∈ Sec4.sporadics46, Nonempty (lBar Y ≃* NativeSporadic.Carrier s) →
      Subgroup.center (lBar Y) = ⊥ := fun s hs ⟨φ⟩ =>
    Sec13.Res5Proof.center_eq_bot_of_sporadic hq hs φ
  rcases h with ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ |
      ⟨hM, -⟩ | ⟨hM, -⟩
  · exact hs .M12 (by simp [Sec4.sporadics46]) hM
  · exact hs .M22 (by simp [Sec4.sporadics46]) hM
  · exact hs .M23 (by simp [Sec4.sporadics46]) hM
  · exact hs .M24 (by simp [Sec4.sporadics46]) hM
  · exact hs .J2 (by simp [Sec4.sporadics46]) hM
  · exact hs .J4 (by simp [Sec4.sporadics46]) hM
  · exact hs .HS (by simp [Sec4.sporadics46]) hM
  · exact hs .He (by simp [Sec4.sporadics46]) hM
  · exact hs .Ru (by simp [Sec4.sporadics46]) hM

theorem center_eq_bot_of_lThree {n : ℕ} (hn : 0 < n) (hq : IsQuasisimple X)
    (φ : X ≃* projSL 3 (GaloisField 2 n)) : Subgroup.center X = ⊥ :=
  Sec13.Res5Proof.center_eq_bot_of_projSL (n := 3) ⟨Nat.prime_two, hn, by norm_num,
    prod_ne_of_fst_ne (by norm_num), prod_ne_of_fst_ne (by norm_num)⟩ hq φ

theorem center_eq_bot_of_chevTwo
    {n : ℕ} (hq : IsQuasisimple X)
    (h : ChevalleyExceptionalModel X .G2 2 n ∨ ChevalleyExceptionalModel X .trialityD4 2 n) :
    Subgroup.center X = ⊥ := by
  rcases h with h | h
  · have := (LieType.Simplicity.fam_g2_simplicity X 2 n h).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
  · have := (LieType.Simplicity.fam_3d4_simplicity X 2 n h).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)

theorem center_eq_bot_of_rankTwoEven (hq : IsQuasisimple X)
    (h : (∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
      Nonempty (X ≃* projSU 5 2 2) ∨ StatedClassicalModel X .PSL 4 2 1 ∨
      StatedClassicalModel X .PSL 5 2 1) : Subgroup.center X = ⊥ := by
  rcases h with ⟨n, hn, hne, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | h | h
  · have h4 : 4 ≤ 2 ^ n := by
      obtain ⟨k, rfl⟩ := hne
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Sec13.Res5Proof.center_eq_bot_of_projSp ⟨Nat.prime_two, hn, le_rfl,
      prod_ne_of_snd_ne (by omega)⟩ hq φ
  · exact Sec13.Res5Proof.center_eq_bot_of_projSU (n := 4) ⟨Nat.prime_two, hn, by norm_num,
      prod_ne_of_fst_ne (by norm_num)⟩ hq φ
  · exact Sec13.Res5Proof.center_eq_bot_of_projSU (n := 5) ⟨Nat.prime_two, by norm_num,
      by norm_num, by decide⟩ hq φ
  · have := (LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)
  · have := (LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
    exact Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hq (MulEquiv.refl X)

end Centre

theorem nonempty_lBar_equiv_lBarA {A Y : Subgroup G} {b : G} (hYb : Y ∈ thetaComponentsAt 3 b)
    (hAC : A ≤ Subgroup.centralizer ({b} : Set G)) (hA : IsPGroup 3 A) (hAY : A ≤ Y) :
    Nonempty (lBar Y ≃* ↥(Sec13.lBarA b Y A)) := by
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := hAY.trans Subgroup.le_normalizer
  obtain ⟨eX⟩ := Item211Proof.nonempty_quotX_equiv_lBarA hYb hAC hA hAN
  obtain ⟨Φ₀, -⟩ := Item211Proof.exists_lEquiv (L := Y) hAN
  have htop : Item211Proof.lOne Y A = ⊤ := by
    have h1 : Y.subgroupOf (Y ⊔ A) = ⊤ := by
      rw [sup_eq_left.mpr hAY]
      exact Subgroup.subgroupOf_self Y
    rw [Item211Proof.lOne, h1, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  exact ⟨Φ₀.trans ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans eX))⟩

theorem not_isHeisCentral_of_le {A Y : Subgroup G} {b : G} (hYb : Y ∈ thetaComponentsAt 3 b)
    (hAC : A ≤ Subgroup.centralizer ({b} : Set G)) (hA : IsPGroup 3 A) (hAY : A ≤ Y) :
    ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) := by
  intro hH
  obtain ⟨e⟩ := nonempty_lBar_equiv_lBarA hYb hAC hA hAY
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hq.1
  exact Sec13.ON134.not_isPerfect_of_isHeisCentral hH
    (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

end Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21
