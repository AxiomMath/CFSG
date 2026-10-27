module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLieL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GorensteinWalter

theorem kDiag_transport {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y)
    (hY : ∀ (θ : MulAut Y), Odd (orderOf θ) →
      ∀ S : Sylow 2 Y, (∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) →
      ∀ P : Subgroup Y, IsParabolicTwo Y P →
        (S : Subgroup Y) ≤ Subgroup.normalizer (P : Set Y) →
        ∀ x ∈ P, θ x ∈ P) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective e e.surjective
  intro θ hodd S hSθ P hP hSP x hx
  let θ' : MulAut Y := MulAut.congr e θ
  have horder : orderOf θ' = orderOf θ :=
    orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ
  have hodd' : Odd (orderOf θ') := by
    rw [horder]
    exact hodd
  let S' : Sylow 2 Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS'coe : (S' : Subgroup Y) = (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS'θ : ∀ y ∈ (S' : Subgroup Y), θ' y ∈ (S' : Subgroup Y) := by
    intro y hy
    rw [hS'coe] at hy ⊢
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have happ : θ' (e.toMonoidHom s) = e.toMonoidHom (θ s) := by
      simp [θ', MulAut.congr_apply]
    rw [happ]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hSθ s hs)
  have hP' : IsParabolicTwo Y (P.map e.toMonoidHom) :=
    IsParabolicTwo.map hP e.toMonoidHom e.surjective
  have hSP' : (S' : Subgroup Y) ≤
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [hS'coe]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.le_normalizer_map (f := e.toMonoidHom) (H := P)
      (Subgroup.mem_map_of_mem e.toMonoidHom (hSP hs))
  have hmem : θ' (e x) ∈ (P.map e.toMonoidHom : Subgroup Y) :=
    hY θ' hodd' S' hS'θ (P.map e.toMonoidHom) hP' hSP' (e x)
      (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have happx : θ' (e x) = e (θ x) := by
    simp [θ', MulAut.congr_apply]
  rw [happx] at hmem
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem

theorem kDiag_psl2 (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    ∀ (θ : MulAut (PSL2 K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (PSL2 K),
      (∀ x ∈ (S : Subgroup (PSL2 K)), θ x ∈ (S : Subgroup (PSL2 K))) →
    ∀ P : Subgroup (PSL2 K), IsParabolicTwo (PSL2 K) P →
      (S : Subgroup (PSL2 K)) ≤ Subgroup.normalizer (P : Set (PSL2 K)) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro θ _hodd S hSθ P hP hSP x hx
  obtain ⟨S₀, hS₀P⟩ := hP
  have hPpar : IsParabolicTwo (PSL2 K) P := ⟨S₀, hS₀P⟩
  have hcoat : IsCoatom (Subgroup.normalizer (S₀ : Set (PSL2 K))) := by
    let U : Sylow 2 (PSL2 K) := psl2UpperUnipotentSylow K hK
    let Usub : Subgroup (PSL2 K) := (U : Subgroup (PSL2 K))
    have hU : Usub = psl2UpperUnipotentSubgroup K :=
      psl2UpperUnipotentSylow_coe K hK
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 K) U S₀
    have hS₀eq : (S₀ : Subgroup (PSL2 K)) =
        Usub.map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    have hset : (S₀ : Set (PSL2 K)) =
        ((Usub.map (MulAut.conj g).toMonoidHom : Subgroup (PSL2 K)) : Set (PSL2 K)) :=
      congrArg (fun H : Subgroup (PSL2 K) => (H : Set (PSL2 K))) hS₀eq
    have hN : Subgroup.normalizer (S₀ : Set (PSL2 K)) =
        (Subgroup.normalizer (Usub : Set (PSL2 K))).map
          (MulAut.conj g).toMonoidHom := by
      rw [hset]
      exact (Subgroup.map_equiv_normalizer_eq Usub (MulAut.conj g)).symm
    have hB : Subgroup.normalizer (Usub : Set (PSL2 K)) = psl2Borel K := by
      rw [hU]
      exact psl2UpperUnipotent_normalizer_eq_borel K
    have hNborel : Subgroup.normalizer (S₀ : Set (PSL2 K)) =
        (psl2Borel K).map (MulAut.conj g).toMonoidHom := by
      rw [hN, hB]
    rw [hNborel]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g))
      (psl2Borel K)).2 (CFSG.Quasithin.H13.P31X.l2_psl2Borel_isCoatom K)
  rcases hcoat.le_iff.mp hS₀P with hPtop | hPN
  · rw [hPtop]
    exact Subgroup.mem_top _
  ·
    have hSP' : (S : Subgroup (PSL2 K)) ≤ P :=
      IsParabolicTwo.le_of_le_normalizer hPpar S.isPGroup' hSP
    have hS₀P' : (S₀ : Subgroup (PSL2 K)) ≤ P :=
      Subgroup.le_normalizer.trans hS₀P
    have hnorm : (S₀.subgroupOf P).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀P').mpr ?_
      rw [hPN]
      exact le_rfl
    let T₁ : Sylow 2 P := S₀.subtype hS₀P'
    let T₂ : Sylow 2 P := S.subtype hSP'
    have hnormT₁ : (T₁ : Subgroup P).Normal := hnorm
    have hT₂T₁ : T₂ = T₁ := by
      haveI : (T₁ : Subgroup P).Normal := hnormT₁
      obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P T₁ T₂
      rw [← hp, Sylow.smul_eq_of_normal]
    have hSS₀ : S = S₀ := Sylow.subtype_injective hT₂T₁
    have hPN' : P = Subgroup.normalizer (S : Set (PSL2 K)) := by
      rw [hPN, hSS₀]
    let Ssub : Subgroup (PSL2 K) := (S : Subgroup (PSL2 K))
    have hsetS : (S : Set (PSL2 K)) = (Ssub : Set (PSL2 K)) := rfl
    have hmapS : Ssub.map θ.toMonoidHom = Ssub := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hSθ y hy
      · rw [Subgroup.card_map_of_injective θ.injective]
    have hmapN : (Subgroup.normalizer (Ssub : Set (PSL2 K))).map θ.toMonoidHom =
        Subgroup.normalizer (Ssub : Set (PSL2 K)) := by
      rw [Subgroup.map_equiv_normalizer_eq Ssub θ, hmapS]
    have hPN'' : P = Subgroup.normalizer (Ssub : Set (PSL2 K)) := by
      rw [hPN', hsetS]
    rw [hPN''] at hx ⊢
    exact hmapN ▸ Subgroup.mem_map_of_mem θ.toMonoidHom hx

theorem kDiag_of_isL2 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsL2 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hX' : CFSG.Blueprint.LieModel X .PSL 2 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSL 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX' ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hn1 : 1 ≤ n := hadm.2.1
  have hEven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  haveI : CharP K 2 := ringChar.of_eq hchar
  exact kDiag_transport
    (e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    (kDiag_psl2 K hcard)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
