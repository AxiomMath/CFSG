module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafGen
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKSetup
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafModel
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafPlusFour
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafNeDual
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafStar
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafDualPairOrth

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))
variable {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n) (ψ : UK n f →* X) (p : ℕ)
  (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
include hn hH
variable (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
  (hB : SetD n f ψ J S J') (hF : FullD n f ψ D S) (hE : EpsD n f S J' ε)
  (heJ : IsPrimIdemIn (AdS f S) e_J)
include S J' ε e_J hB hF hE heJ
variable (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
  (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
include heD hKG₀ hKcomp hJK
variable (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .POmegaMinus n f p ψ R Rm)
  (hKne : K ≠ J)
include hR hR0 hKne

theorem nbrpmmx_K_sl
    (hcase : e_J ≠ ε ∧ Fadj n f e_J ≠ e_J ∧ ε = e_J + Fadj n f e_J ∧
      blockDegree (AdS f S) e_J < 2)
    (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ) (hrankJ : rk f e_J = kJ + 1) :
    (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
      OrthOut f K R (kJ + 1) := by
  have hψ : ψ.ker ≤ Subgroup.center (UK n f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpmmx_K_setup n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K
      hKG₀ hKcomp hJK R Rm hR hR0 hKne
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  obtain ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩ := hB
  obtain ⟨hεE, hJ'ε⟩ := hE
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj n f e' ≠ e' ∧ ε' = e' + Fadj n f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx n f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hrank_eps : rk f ε = 2 * (kJ + 1) :=
    rank_eps n f S hSU hS heJ hcase.2.1 hcase.2.2.1 kJ hrankJ
  have horth : e_J * Fadj n f e_J = 0 := dualPair_orth n f S hSU hS heJ hcase.2.1
  have heJε : e_J * ε = e_J := by
    rw [hcase.2.2.1, mul_add, heJ.2.1.eq, horth, add_zero]
  have heJε' : e_J * ε' = e_J := by
    calc e_J * ε' = (e_J * ε) * ε' := by rw [heJε]
      _ = e_J * (ε * ε') := by rw [Matrix.mul_assoc]
      _ = e_J * ε := by rw [htie]
      _ = e_J := heJε
  have hε'A : ε' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) hε'.1
  have hba' : ε' * ε = ε := (hcomm ε' ε hε'A hεE.1).trans htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK n f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK n f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpmmx_plus_four n f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpmmx_K_model (X := X) n f hn hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpmmx_rootVia n f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have hle := rank_le_of_mul_eq hεE.2.1 htie hba'
    have hrk' : rk f e' = rk f ε' := by rw [heq]
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact Or.inr ⟨t'', m, β, ht'', h3, by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · have htieJ : e_J * e' = e_J := by rw [heq]; exact heJε'
    exact (notSU hSe hS hS' hodd' heJ he' htieJ hcase.2.2.2 (by omega)).elim
  · obtain ⟨hne1, hpair', hεeq'⟩ := hsplit''.resolve_left hne
    obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpmmx_K_model (X := X) n f hn hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inr (Or.inr ⟨hne, hd⟩))
    obtain ⟨rfl, hm⟩ := htype.2.2 ⟨hne, hd⟩
    have hvia := nbrpmmx_rootVia n f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have hG := gram_det n f
    have hGh := gram_transpose n f
    have hinv : Fadj n f (Fadj n f e') = e' :=
      Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e'
    have hrk'' : rk f (Fadj n f e') = rk f e' := rank_formAdj hG
    have hsumJ : e_J * e' + e_J * Fadj n f e' = e_J := by
      rw [← mul_add, ← hεeq', heJε']
    have hJe' : e_J * e' = 0 ∨ e_J * e' = e_J := by
      apply heJ.2.2.2
      · exact Subalgebra.mul_mem _ heJ.1 he'A
      · rw [IsIdempotentElem]
        calc (e_J * e') * (e_J * e') = e_J * (e' * (e_J * e')) := by rw [mul_assoc]
          _ = e_J * ((e' * e_J) * e') := by rw [mul_assoc]
          _ = e_J * ((e_J * e') * e') := by rw [hcomm e' e_J he'A heJ.1]
          _ = e_J * (e_J * (e' * e')) := by rw [mul_assoc]
          _ = e_J * (e_J * e') := by rw [he'.2.1.eq]
          _ = (e_J * e_J) * e' := by rw [mul_assoc]
          _ = e_J * e' := by rw [heJ.2.1.eq]
      · rw [mul_assoc, hcomm e' e_J he'A heJ.1, ← mul_assoc, heJ.2.1.eq]
    have hlt' : rk f e_J < rk f e' := by
      rcases hJe' with h0 | hA
      · have hB' : e_J * Fadj n f e' = e_J := by
          have h := hsumJ
          rw [h0, zero_add] at h
          exact h
        have hPrim'' := nbrpmmx_isPrimIdemIn_formAdj n f S' hSU' hS' he'
        have hstar_ne : Fadj n f e' ≠ ε' := by
          intro h
          apply hne1
          have hh := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm n f)) h
          rw [hinv, hε'.2.2.2.1] at hh
          exact hh
        have hstar_pair : Fadj n f (Fadj n f e') ≠ Fadj n f e' := by
          rw [hinv]; exact fun h => hpair' h.symm
        have hstar_sum : ε' = Fadj n f e' + Fadj n f (Fadj n f e') := by
          rw [hinv]; exact hεeq'.trans (add_comm _ _)
        have hne2 : e_J ≠ Fadj n f e' :=
          nbrpmmx_ne_dual n f ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
            hK'ε' heJ hcase.2.2.2 ⟨hstar_ne, hstar_pair, hstar_sum⟩ hPrim''
        have hstarA : Fadj n f e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) hPrim''.1
        have hba2 : Fadj n f e' * e_J = e_J := (hcomm _ e_J hstarA heJ.1).trans hB'
        have hlt := rank_lt_of_mul_eq heJ.2.1 hB' hba2 hne2
        omega
      · have hne2 : e_J ≠ e' :=
          nbrpmmx_ne_dual n f ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
            hK'ε' heJ hcase.2.2.2 ⟨hne1, hpair', hεeq'⟩ he'
        have hba1 : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans hA
        exact rank_lt_of_mul_eq heJ.2.1 hA hba1 hne2
    obtain ⟨kK, rfl⟩ : ∃ kK, m = kK + 1 := ⟨m - 1, by omega⟩
    exact Or.inl ⟨kK, β, by omega, hβ, hvia⟩


end CFSG.StandardType.ClassicalPosition.NbrLeaf
