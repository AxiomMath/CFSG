module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125Bar
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentCore
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix (ProjGenLinGroup)

theorem exists_sl2_slPi_two {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]
    (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (slPi π 2 (p ^ f) Kf ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have := hKf.finite
  have : Fact p.Prime := ⟨hKf.prime⟩
  cases π
  · have hcard : Nat.card Kf = (p ^ f) ^ 2 := hKf.card
    have : CharP Kf p := hKf.unitary.charP
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := Kf) (r := p) (f := f) hcard
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield (F := Kf) (p := p) (f := f) hcard
    exact ⟨_, inferInstance, inferInstance, hF, ⟨e.symm⟩⟩
  · have hcard : Nat.card Kf = p ^ f := hKf.card
    exact ⟨Kf, inferInstance, inferInstance, hcard, ⟨statedSLEquiv 2 Kf⟩⟩

theorem exists_model_explicit {G : Type} [Group G] [Finite G] {Y K : Subgroup G} {c : G}
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y))
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 2 < p ^ f ∧
      ((p ^ f % 3 = 1 ∧ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
          projImage (slPi true 3 (p ^ f) (GaloisField p f)))) ∨
        (p ^ f % 3 = 2 ∧ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
          projImage (slPi false 3 (p ^ f) (GaloisField p (2 * f)))))) := by
  obtain ⟨p, e, hp, he, hiso⟩ := hY
  have h2 : 2 ≤ p ^ e := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  rcases hiso with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · exact ⟨p, e, hp, he, by omega, Or.inl ⟨hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _))⟩⟩⟩
  · set φ' := φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage p e)) with hφ'
    refine ⟨p, e, hp, he, ?_, Or.inr ⟨hq3, ⟨φ'⟩⟩⟩
    by_contra hle
    have hpe : p ^ e = 2 := by omega
    have hKf : PiField false p e (GaloisField p (2 * e)) :=
      ⟨hp.out, he, by
        rw [GaloisField.card p (2 * e) (by omega)]
        change p ^ (2 * e) = (p ^ e) ^ 2
        rw [← pow_mul, mul_comm]⟩
    apply KS11LieProof.not_isSolvable_thetaQuot hcN hc3 hK
    have hs : Group.IsSolvable (slPi false 3 (p ^ e) (GaloisField p (2 * e))) :=
      Sec13.isSolvable_slPi_two hKf hpe
    have hs' : Group.IsSolvable (projImage (slPi false 3 (p ^ e) (GaloisField p (2 * e)))) :=
      Group.isSolvable_of_surjective (projOf_surjective _)
    exact Group.isSolvable_of_isSolvable_injective (f := φ'.toMonoidHom) φ'.injective

theorem exists_block_sl2 {G : Type} [Group G] [Finite G] {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf)) :
    (∃ g ∈ glPi π 3 (p ^ f) Kf, ∃ e : Kfˣ, (e : Kf) ^ 3 = 1 ∧ e ≠ 1 ∧
      ∀ m, (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)) m :
          ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (g * diagE e * g⁻¹) * m *
          (ProjGenLinGroup.mk (g * diagE e * g⁻¹))⁻¹) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (((K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨h₀, hh₀, e, he3, he1, hαc, hKblock⟩ :=
    KS11LieProof.core_block hcN hc3 hK hT hKf hq hq2 φ
  have hblk := KS11LieProof.block_mem_image hcN hc3 hK hT hKf hq hq2 φ hh₀ hαc hKblock
  have himg := KS11LieProof.exists_block_of_mem hKf φ hh₀ hKblock
  obtain ⟨F, _, _, hFcard, ⟨e2⟩⟩ := exists_sl2_slPi_two hKf hq hq2
  set J := (K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hJ
  have hmapJ : J.map φ.toMonoidHom = (KS11LieProof.blockProj hKf hh₀).range := by
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hj
      obtain ⟨B, hB⟩ := himg y (Subgroup.mem_subgroupOf.mp hy)
      exact ⟨B, hB.symm⟩
    · rintro ⟨B, rfl⟩
      obtain ⟨y, hyK, hy⟩ := hblk B
      exact ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) y,
        ⟨y, Subgroup.mem_subgroupOf.mpr hyK, rfl⟩, hy⟩
  have e1 : J ≃* (KS11LieProof.blockProj hKf hh₀).range :=
    (φ.subgroupMap J).trans (MulEquiv.subgroupCongr hmapJ)
  exact ⟨⟨h₀, hh₀, e, he3, he1, hαc⟩, F, inferInstance, inferInstance, hFcard,
    ⟨e1.trans ((MonoidHom.ofInjective (KS11LieProof.blockProj_injective hKf hh₀)).symm.trans
      e2)⟩⟩

theorem l3_cases {G : Type} [Group G] [Finite G] {Y I : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hI : I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    {n : ℕ} (hn0 : 0 < n) (hne : Even n)
    (hIn : Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* projSL 2 (GaloisField 2 n)))
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) :
    InducesTypeTwoL2 Y c ∨
      Nonempty (imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hne; omega
  have hIY : I ≤ Y := (le_of_mem_thetaComponentsIn hI).trans inf_le_left
  obtain ⟨eK⟩ := Sec4.Item426.nonempty_quotTheta_map_equiv Y hIY
  have hIT : IsType424 (I ⧸ aschbacherSolvableCore 3 I) := Or.inl ⟨n, hn0, hIn⟩
  have hmod : 2 ^ n % 3 = 1 := modThree_of_even hne
  obtain ⟨p, f, hp, hf, hq2, hmodel⟩ := exists_model_explicit hY hcN hc3 hI
  rcases hmodel with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  ·
    have hKf : PiField true p f (GaloisField p f) :=
      ⟨hp.out, hf, by rw [GaloisField.card p f (by omega)]; rfl⟩
    obtain ⟨⟨g, hg, e', he3, he1, hα⟩, F, _, _, hFcard, ⟨e2⟩⟩ :=
      exists_block_sl2 hcN hc3 hI hIT hKf hq3 hq2 φ
    have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; omega
    have hJ : imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) F := e2
    rcases sl2_quot_card hF4 hJ hn2 ⟨eK.symm.trans hIn.some⟩ with h2 | ⟨h5, -⟩
    · left
      rw [hFcard] at h2
      have hp2 : p = 2 := by
        have : p ∣ 2 ^ n := by
          rw [← h2]
          exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow this)
      subst hp2
      have hfn : f = n := Nat.pow_right_injective (le_refl 2) h2
      subst hfn
      refine ⟨hcN, f, hn0, hne, φ.trans (MulEquiv.subgroupCongr
        (Sec4.projSL_eq_projImage (2 ^ f) (GaloisField 2 f))).symm,
        g * diagE e' * g⁻¹, ⟨e', he3, he1, 1, one_mem _, g, hg, by group⟩, ?_⟩
      intro z
      have h := hα (φ z)
      rw [MulAut.congr_apply] at h
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
      exact h
    · exfalso
      rw [hFcard] at h5
      omega
  ·
    have hKf : PiField false p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, by
        rw [GaloisField.card p (2 * f) (by omega)]
        change p ^ (2 * f) = (p ^ f) ^ 2
        rw [← pow_mul, mul_comm]⟩
    obtain ⟨-, F, _, _, hFcard, ⟨e2⟩⟩ := exists_block_sl2 hcN hc3 hI hIT hKf hq3 hq2 φ
    have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; omega
    have hJ : imageI Y I ≃* Matrix.SpecialLinearGroup (Fin 2) F := e2
    rcases sl2_quot_card hF4 hJ hn2 ⟨eK.symm.trans hIn.some⟩ with h2 | ⟨h5, -⟩
    · exfalso
      rw [hFcard] at h2
      omega
    · right
      exact ⟨hJ.trans (sl2_mulEquiv_five h5)⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
