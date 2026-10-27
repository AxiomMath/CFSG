module

public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofR
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Step158InnerRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    Sec8.IsZ3PGLThreePi (lBarA c L A) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
    ∀ X ∈ scriptY4 A (lB A), X ≤ L →
      ∃ B : Subgroup G, B ≤ X ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 9

@[expose] noncomputable def Step158InnerX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    Sec8.IsZ3PGLThreePi (lBarA c L A) →
    ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ L ⊓ Y →
      ∃ S : Subgroup G, A ≤ S ∧ S ≤ X ⊔ A ∧ IsPGroup 3 S ∧ ∃ x ∈ S, x ^ 3 = 1 ∧ x ∉ A

@[expose] noncomputable def Step158CartanCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∃ E F : Subgroup G, E ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        Nat.card E = 27 ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L ∧ IsF138N L E F ∧ F ≤ Subgroup.normalizer (Y : Set G)

namespace Proof158Inner

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {T K B : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T K) (hB : IsPGroup p B) (hBK : B ≤ K) :
    ∃ k ∈ K, B.map (MulAut.conj k).toMonoidHom ≤ T := by
  have hB' : IsPGroup p (B.subgroupOf K) := hB.comap_subtype
  obtain ⟨Q, hQ⟩ := hB'.exists_le_sylow
  have hQ' : CFSG.ABGLocalTools.IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  have hBQ : B ≤ (Q : Subgroup K).map K.subtype := fun b hb =>
    ⟨⟨b, hBK hb⟩, hQ (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  obtain ⟨k, hk, hkeq⟩ := Proof158Steps.exists_conj_of_isSylowOf hT hQ'
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hb' := hBQ hb
  rw [hkeq] at hb'
  obtain ⟨t, ht, htb⟩ := hb'
  have : (MulAut.conj k⁻¹).toMonoidHom b = t := by
    rw [← htb]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact ht

theorem mem_of_eq_omegaOneThree {N P A S : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P N) (hΩ : A = omegaOneThree P)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hS : IsPGroup 3 S) (hSN : S ≤ N) (hAS : A ≤ S)
    {x : G} (hx : x ∈ S) (hx3 : x ^ 3 = 1) : x ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS' : IsPGroup 3 (S.subgroupOf N) := hS.comap_subtype
  obtain ⟨Q', hQ'⟩ := hS'.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 ((Q' : Subgroup N).map N.subtype) N := ⟨Q', rfl⟩
  have hSP' : S ≤ (Q' : Subgroup N).map N.subtype := fun s hs =>
    ⟨⟨s, hSN hs⟩, hQ' (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  obtain ⟨k, -, hk⟩ := Proof158Steps.exists_conj_of_isSylowOf hP hP'
  have hmemΩ : ∀ y ∈ (Q' : Subgroup N).map N.subtype, y ^ 3 = 1 → k⁻¹ * y * k ∈ A := by
    intro y hy hy3
    rw [hk] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : k⁻¹ * (MulAut.conj k).toMonoidHom z * k = z := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hz', hΩ]
    refine Subgroup.subset_closure ⟨hz, ?_⟩
    have h3 : ((MulAut.conj k).toMonoidHom z) ^ 3 = (MulAut.conj k).toMonoidHom (z ^ 3) :=
      (map_pow _ z 3).symm
    rw [hy3] at h3
    exact (MulAut.conj k).injective (by simpa using h3.symm)
  have hmapA : A.map (MulAut.conj k⁻¹).toMonoidHom = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := hmemΩ a (hSP' (hAS ha)) (hA.2 a ha)
      simpa [MulAut.conj_apply] using h1
    · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
  have hxk : k⁻¹ * x * k ∈ A := hmemΩ x (hSP' hx) hx3
  rw [← hmapA] at hxk
  obtain ⟨a, ha, hax⟩ := hxk
  have hax' : k⁻¹ * a * k = k⁻¹ * x * k := by simpa [MulAut.conj_apply] using hax
  have : a = x := by simpa using hax'
  exact this ▸ ha

theorem card_inf_le_three {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) : Nat.card (A ⊓ L : Subgroup G) ≤ 3 := by
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hD.card_eq]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases j
  · rw [hj]; norm_num
  · rw [hj]; norm_num
  · exact (Proof1511.false_of_card_nine_of_isZ3PGLThreePi hD hcL (by rw [hj]; norm_num)
      hPGL).elim
  · exfalso
    have hEq : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hj, hD.card_eq]; norm_num)
    have hc : c ∈ A ⊓ L := by
      rw [hEq]
      exact hD.mem_A
    exact hcL hc.2

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem nontrivial_of_isQuasisimple {X : Type*} [Group X] (hq : IsQuasisimple X) :
    Nontrivial X := by
  obtain ⟨x, y, hxy⟩ := hq.2.2
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hxy
  have : Subsingleton (X ⧸ Subgroup.center X) := QuotientGroup.mk_surjective.subsingleton
  exact Subsingleton.elim _ _

end Proof158Inner

open Proof158Inner Proof158Steps

theorem step158Inner_of (h : Step158InnerX) : Step158Inner := by
  intro G _ _ A c L hR p e _ he hL3 Y hY hmeet P hAP hP hΩ hPGL
  obtain ⟨X, hX, hXLY⟩ := hmeet
  obtain ⟨S, hAS, hSXA, hS3, x, hxS, hx3, hxA⟩ := h G A c L hR p e he hL3 hPGL Y hY X hX hXLY
  apply hxA
  have hD := hR.toSec13Data
  have hXA : X ⊔ A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) := by
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact (hXLY.trans inf_le_left).trans
        (hD.le_centralizer.trans (centralizer_le_normalizer_zpowers c))
    · exact (hXLY.trans inf_le_right).trans Subgroup.le_normalizer
    · exact hD.A_le_centralizer.trans (centralizer_le_normalizer_zpowers c)
    · exact hY.1.1.2
  exact mem_of_eq_omegaOneThree hP hΩ hD.isElemAbelian hS3 (hSXA.trans hXA) hAS hxS hx3

theorem step158InnerX_of
    (h131 : Item131) (hK : Step158InnerRank) : Step158InnerX := by
  intro G _ _ A c L hR p e _ he hL3 hPGL Y hY X hX hXLY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := hR.toSec13Data
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have := nontrivial_of_isQuasisimple hq
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD
    (Sec14.center_eq_bot_of_isLThreePi ⟨p, e, inferInstance, he, hL3⟩ hq.1)
  have htype : ∃ x ∈ A, Sec4.InducesTypeOn L x 3 := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, hprod, -⟩ |
        ⟨-, -, ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩, -⟩ | ⟨-, -, -, hx⟩ | ⟨hcL', -⟩
    · exact (Proof1514.false_of_prod_of_isZ3PGLThreePi hD hcL hprod hPGL).elim
    · exact (Proof1511.not_isoLThreePi_of_prod_M12 hD e12 hL3).elim
    · exact (Proof1511.not_isoLThreePi_of_prod_J2 hD eJ hL3).elim
    · exact hx
    · exact (hcL hcL').elim
  have hAL3 := card_inf_le_three hD hcL hPGL
  obtain ⟨B, hBX, hB3, hB9⟩ := hK G A c L hR p e he hL3 hPGL htype X hX (hXLY.trans inf_le_left)
  have hAXA : A ≤ X ⊔ A := le_sup_right
  have hA' : IsPGroup 3 (A.subgroupOf (X ⊔ A)) :=
    (isPGroup_of_isElemAbelian hD.isElemAbelian).comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  set S := (Q : Subgroup ↥(X ⊔ A)).map (X ⊔ A).subtype with hSdef
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S (X ⊔ A) := ⟨Q, rfl⟩
  have hAS : A ≤ S := fun a ha => ⟨⟨a, hAXA ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  obtain ⟨k, hk, hBk⟩ := exists_conj_le_of_isSylowOf hSyl (isPGroup_of_isElemAbelian hB3)
    (hBX.trans le_sup_left)
  have hXN : X ⊔ A ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.1.2
  have hBkX : B.map (MulAut.conj k).toMonoidHom ≤ X := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXN hk) b).mp (hBX hb)
  have hcardBk : Nat.card (B.map (MulAut.conj k).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hB9]
  have hnot : ¬ B.map (MulAut.conj k).toMonoidHom ≤ A := by
    intro hle
    have hle' : B.map (MulAut.conj k).toMonoidHom ≤ A ⊓ L :=
      le_inf hle (hBkX.trans (hXLY.trans inf_le_left))
    have := Subgroup.card_le_of_le hle'
    omega
  obtain ⟨y, hyB, hyA⟩ := Set.not_subset.mp hnot
  refine ⟨S, hAS, hSyl.le, hSyl.isPGroup, y, hBk hyB, ?_, hyA⟩
  obtain ⟨b, hb, rfl⟩ := hyB
  rw [← map_pow, hB3.2 b hb, map_one]

theorem step158Inner_of_rank
    (h131 : Item131) (hK : Step158InnerRank) : Step158Inner :=
  step158Inner_of (step158InnerX_of h131 hK)

theorem step158Cartan_of (h : Step158CartanCore) : Step158Cartan := by
  intro G _ _ A c L hR p e _ he hL3 Y hY hmeet P hAP hP hΩ
  obtain ⟨E, F, hEP, hE3, hE27, hEC, hEtype, hF, hFY⟩ :=
    h G A c L hR p e he hL3 Y hY hmeet P hAP hP hΩ
  have h3L : 3 ∣ Nat.card L := by
    have h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rcases hL3 with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
      · exact KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ
    exact h3.trans (Subgroup.card_quotient_dvd_card _)
  have hcE : c ∈ E := by
    have hc : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
    rw [← hEC] at hc
    exact hc.1
  refine ⟨E, F, ⟨hEP, hcE, hE3, hE27, ?_, hEC, hEtype, hF, hFY⟩⟩
  exact (hEP.trans (hP.le.trans inf_le_left)).trans
    (Sec16.normalizer_zpowers_le_normalizer_L hR h3L)

theorem item158Y0R_of_res2
    (h131 : Item131) (h138 : Item138N) (hK : Step158InnerRank)
    (hC : Step158CartanCore) : Item158Y0R :=
  item158Y0R_of h131 h138 (step158Inner_of_rank h131 hK) (step158Cartan_of hC) step158R

end CFSG.RankThree.PartTwo.Sec15
