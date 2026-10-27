module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20za
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_good_rankOneG
    (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) :
    ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E ∧
      uc22pwlie_Gal (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1) := by
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hTL := hL.1
  let U : Sylow 2 (Bar2 L) := (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL)
  have hψ : ∀ (g : ↥D.T) (x : Bar2 L),
      x ∈ (U : Subgroup (Bar2 L)) ↔ uc22pwIndHom L D.T hTL g x ∈ (U : Subgroup (Bar2 L)) :=
    fun g x => uc22p20u_ind_sylowBar D hL (hTL g.2) g.2 x
  have key : ∃ E : Subgroup (Bar2 L), uc22pwlie_ConclAt uc22pwr1_shape (Bar2 L) (U : Subgroup (Bar2 L)) ↥D.T
      (uc22pwIndHom L D.T hTL) n m' E ∧ uc22pwlie_Gal (U : Subgroup (Bar2 L)) E (uc22pwIndHom L D.T hTL) := by
    rcases hsh with h | h | h
    · exact uc22pwr1_concl_of_isSzG h U D.sylowM.isPGroup _ hψ hm' hnem
    · exact uc22pwr1_concl_of_isL2G h U D.sylowM.isPGroup _ hψ hm' hnem
    · exact uc22pwr1_concl_of_isSU3G hq hn h U D.sylowM.isPGroup _ hψ hm' hnem
  obtain ⟨E, ⟨hEU, ⟨hcyc, hsq, hodd⟩, hpi, hinv, hα, w, hw2, hwinv, hwtop⟩, hG⟩ := key
  exact ⟨E, uc22pw_good_of_induced D hL hm' hnem hEU inferInstance hodd
    (uc22pw_rank_of_cyclic_squarefree hcyc hsq) hpi hinv hα ⟨w, hw2, hwinv, hwtop⟩, hG⟩

theorem uc22pw_good_graphG (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {n : ℕ} (hn : 2 < n)
    (hsh : IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) :
    ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E ∧
      (uc22pwlie_Gal (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1) ∨
        uc22pwlie_RShape (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1)) := by
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hTL := hL.1
  let U : Sylow 2 (Bar2 L) := (uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL)
  have hψ : ∀ (g : ↥D.T) (x : Bar2 L),
      x ∈ (U : Subgroup (Bar2 L)) ↔ uc22pwIndHom L D.T hTL g x ∈ (U : Subgroup (Bar2 L)) :=
    fun g x => uc22p20u_ind_sylowBar D hL (hTL g.2) g.2 x
  have key : ∃ E : Subgroup (Bar2 L), uc22pwlie_ConclAt uc22pwI2Ep (Bar2 L) (U : Subgroup (Bar2 L)) ↥D.T
      (uc22pwIndHom L D.T hTL) n m' E ∧
      (uc22pwlie_Gal (U : Subgroup (Bar2 L)) E (uc22pwIndHom L D.T hTL) ∨
        uc22pwlie_RShape (U : Subgroup (Bar2 L)) E (uc22pwIndHom L D.T hTL)) := by
    rcases hsh with h | h
    · obtain ⟨E, hE, hG⟩ := uc22pwI3_concl_of_isSL3G hq hn h U D.sylowM.isPGroup _ hψ hm' hnem
      exact ⟨E, hE, Or.inl hG⟩
    · obtain ⟨E, hE, hR⟩ := uc22pwlie_sp4_of_isSp4R hn h U D.sylowM.isPGroup _ hψ hm' hnem
      exact ⟨E, hE, Or.inr hR⟩
  obtain ⟨E, ⟨hEU, ⟨hab, hodd, hrank⟩, hpi, hinv, hα, w, hw2, hwinv, hwtop⟩, hsh'⟩ := key
  exact ⟨E, uc22pw_good_of_induced D hL hm' hnem hEU hab hodd hrank hpi hinv hα ⟨w, hw2, hwinv, hwtop⟩,
    hsh'⟩

theorem uc22pw_alike_of_shape (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {E : Subgroup (Bar2 L)}
    (hEab : IsMulCommutative E) (hEodd : Odd (Nat.card E))
    (hsh : uc22pwlie_Gal (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1) ∨
      uc22pwlie_RShape (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1))
    {F : Subgroup (Bar2 L)} (hFE : F ≤ E) : uc22pwAlike D L F := by
  rintro _ ⟨s, hs, hsT, rfl⟩ _ ⟨t, ht, htT, rfl⟩ hF₁ hF₂ hi₁ hn₁ hi₂ hn₂
  rcases hsh with hG | hR
  · exact uc22pwc_alike_of_gal (uc22p20i_sylowBar_isPGroup D) hEab hEodd hG hFE (g₁ := ⟨s, hsT⟩)
      (g₂ := ⟨t, htT⟩) hF₁ hF₂ hi₁ hn₁ hi₂ hn₂
  · exact uc22pwc_alike_of_rshape (uc22p20i_sylowBar_isPGroup D) hR hFE (g₁ := ⟨s, hsT⟩)
      (g₂ := ⟨t, htT⟩) hF₁ hF₂ hi₁ hn₁ hi₂ hn₂

theorem uc22pw_notInv35_of_shape (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {E : Subgroup (Bar2 L)}
    (hEodd : Odd (Nat.card E))
    (hsh : uc22pwlie_Gal (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1) ∨
      uc22pwlie_RShape (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1)) :
    ∀ φ ∈ uc22p20uA D L, ∀ x₃ ∈ E, ∀ x₅ ∈ E, orderOf x₃ = 3 → orderOf x₅ = 5 →
      φ x₃ * x₃ ∈ uc22p20iSylowBar D L → φ x₅ * x₅ ∈ uc22p20iSylowBar D L → False := by
  rintro _ ⟨t, ht, htT, rfl⟩ x₃ h₃ x₅ h₅ ho₃ ho₅ hi₃ hi₅
  rcases hsh with hG | hR
  · exact uc22pwc_not_inv35_of_gal (uc22p20i_sylowBar_isPGroup D) hEodd hG ⟨t, htT⟩ h₃ h₅ ho₃ ho₅ hi₃ hi₅
  · exact uc22pwc_not_inv35_of_rshape (uc22p20i_sylowBar_isPGroup D) hR ⟨t, htT⟩ h₃ h₅ ho₃ ho₅ hi₃ hi₅

theorem uc22pw_ch214U_single
    (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {n : ℕ} (hn : 2 < n)
    (hsh : (IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) ∨ (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n)) :
    ∃ B0 : Subgroup G, Choice214U D L B0 ∧ B0 ∈ calB1 D.T D.M L ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  obtain ⟨E, hE, hshape⟩ : ∃ E : Subgroup (Bar2 L), uc22pwGood D L n E ∧
      (uc22pwlie_Gal (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1) ∨
        uc22pwlie_RShape (uc22p20iSylowBar D L) E (uc22pwIndHom L D.T hL.1)) := by
    rcases hsh with h | h
    · obtain ⟨E, hE, hG⟩ := uc22pw_good_rankOneG D hL hq hn h
      exact ⟨E, hE, Or.inl hG⟩
    · exact uc22pw_good_graphG D hL hq hn h
  obtain ⟨-, hEab, hEodd, -⟩ := id hE
  exact uc22pw_lift214 D hB h1930 hL hn hE (fun F hFE => uc22pw_alike_of_shape D hL hEab hEodd hshape hFE)
    (uc22pw_notInv35_of_shape D hL hEodd hshape)

end CFSG.LocalAnalysis.UniquenessCase.UC22
