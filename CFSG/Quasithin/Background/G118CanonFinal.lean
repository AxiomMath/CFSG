module

public import CFSG.Quasithin.Background.G118CanonNine
public import CFSG.Quasithin.Background.G118CanonScan
public import CFSG.Quasithin.Background.G118CanonLemmas
public import CFSG.Quasithin.Background.G117CanonFinal
public import CFSG.Quasithin.Background.G93Apply
public import CFSG.Quasithin.Background.SzG11TensorMain
public import CFSG.Quasithin.Background.P3Sp44
public import CFSG.Quasithin.Background.P3GL24
public import CFSG.Quasithin.Background.G118Data
public import CFSG.Quasithin.Background.G118Scan

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Pointwise
open CFSG.Quasithin.G11.G118

namespace G11

namespace Canon

section Final

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem f2_false_A5_c {Q : ConclPred} (hC9 : G118NineContains Q) (hNine : G118NineInput)
    (hs : QSetup Q B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2)
    (hd : Module.finrank (ZMod 2) V = 8)
    (hmod : ∃ (b c : GaloisField 2 1), (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hI.irrPlus.1)
        (StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) b c)))
    (φ : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5))) : False := by
  obtain ⟨⟨e⟩, -⟩ := f2_S3_c hs.conf hI hnf D hk hF
  exact hs.notConcl (hC9.c9 B Γ X
    (hNine V Γ L I hI.irrPlus.1 D hs.conf.h108.H_le hd hk ⟨φ⟩ ⟨e⟩ (Or.inl ⟨hF, hmod⟩)))

theorem f4_false_SL_c {Q : ConclPred} (hQ : QContains Q) (hC9 : G118NineContains Q)
    (hNine : G118NineInput) (hs : QSetup Q B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 4)
    (hd : Module.finrank (ZMod 2) V = 8) (hB : fixedSpace X = Submodule.span (ZMod 2) {v₁})
    (φ : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5)))
    (hD4 : GL24SubInput)
    (hnat : IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hI.irrPlus.1)
      (StatedSL 2 (GaloisField 2 2))) : False := by
  have h108 := hs.conf.h108
  have hN := normalClosure_normal Γ L
  rcases f4_dichotomy_c hs.conf hI hnf D hk hF hB hD4 with hS | hA |
    ⟨a, b, haC, hbC, ha3, hb3, ha1, hb1, hba, hba2, hab⟩
  ·
    obtain ⟨eS⟩ := hS
    exact hs.notConcl (hC9.c9 B Γ X
      (hNine V Γ L I hI.irrPlus.1 D h108.H_le hd hk ⟨φ⟩ ⟨eS⟩ (Or.inr ⟨hF, hnat⟩)))
  ·
    obtain ⟨eA⟩ := hA
    have hmap := fstar_map_eq_of_alt_five h108.H_le hN φ eA
    have hcomm : ∀ h ∈ normalClosure Γ L, ∀ c ∈ centΓ Γ (normalClosure Γ L), h * c = c * h :=
      fun h hh c hc => ((mem_centΓ_iff.1 hc).2 h hh)
    apply hs.notConcl
    refine hQ.c7 B Γ X ⟨hd, ?_, ?_⟩
    · rw [hmap]
      exact SzG11S.om4PlusTensor V (normalClosure Γ L) (centΓ Γ (normalClosure Γ L)) I
        hI.homogeneous hI.irrPlus h108.fixedSpace_H h108.sSup_isIrr
        ((Nat.card_congr D.endEquiv.toEquiv).trans hF) hd hI.faithful ⟨φ⟩
        (fun c hc => centΓ_le_centralizer hc) ⟨eA⟩
    · rw [hmap]
      intro hXle
      obtain ⟨x₀, hx₀X, hx₀nc⟩ := exists_not_comm_kappa_c hs.conf D hF hB
      obtain ⟨h, hh, c, hc, hx₀hc⟩ := mem_sup_of_commute' hcomm (hXle hx₀X)
      apply hx₀nc
      intro f
      have hcc := centralizer_comm_kappa D (centΓ_le_centralizer hc) f
      have hhk := D.κ_comm f h hh
      have e1 : ((h * c : GLV V) : Module.End (ZMod 2) V) =
          (h : Module.End (ZMod 2) V) * (c : Module.End (ZMod 2) V) := rfl
      rw [hx₀hc, e1, mul_assoc, hcc, ← mul_assoc, ← hhk, mul_assoc]
  ·
    obtain ⟨E, hE, haE, hbE, hcomm, hexp, hnc⟩ :=
      exists_noncyclic_exp3 hab ha3 hb3 ha1 hb1 hba hba2
    obtain ⟨s, t, ht2, ht1, hs3, hs1, hts⟩ := g118_exists_S3_alt_five
    have hEC : E ≤ centΓ Γ (normalClosure Γ L) := by
      rw [hE]
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haC
      · exact hbC
    have hEΓ : E ≤ Γ := hEC.trans inf_le_left
    set s' : ↥(normalClosure Γ L) := φ.symm s with hs'
    set t' : ↥(normalClosure Γ L) := φ.symm t with ht'
    have ht2' : t' * t' = 1 := by rw [ht', ← map_mul, ht2, map_one]
    have ht1' : t' ≠ 1 := fun h => ht1 (φ.symm.injective (by rw [← ht', h, map_one]))
    have hs3' : s' ^ 3 = 1 := by rw [hs', ← map_pow, hs3, map_one]
    have hs1' : s' ≠ 1 := fun h => hs1 (φ.symm.injective (by rw [← hs', h, map_one]))
    have hts' : t' * s' * t'⁻¹ = s'⁻¹ := by
      rw [hs', ht', ← map_inv, ← map_mul, ← map_mul, hts, map_inv]
    exact G117.no_S3_noncyclic hs.conf.sqtk (h108.H_le t'.2) (h108.H_le s'.2) hEΓ
      (by simpa using congrArg Subtype.val ht2') (fun h => ht1' (Subtype.ext h))
      (by simpa using congrArg Subtype.val hs3') (fun h => hs1' (Subtype.ext h))
      (by simpa using congrArg Subtype.val hts') hcomm hexp hnc
      (fun e he => ((mem_centΓ_iff.1 (hEC he)).2 t' t'.2).symm)
      (fun e he => ((mem_centΓ_iff.1 (hEC he)).2 s' s'.2).symm)

theorem k2_false_c {Q : ConclPred} (hQ : QContains Q) (hC9 : G118NineContains Q)
    (hNine : G118NineInput) (hs : QSetup Q B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (hItop : I ≠ ⊤)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hE11 : E11Stmt) (hApply : G93ApplyStmt) (hD1 : SL24IsoA5)
    (hD3 : Sp44RankInput) (hD4 : GL24SubInput) : False := by
  have h108 := hs.conf.h108
  have hI0 : I ≠ ⊥ := (isIrr_I h108 hI).ne_bot
  have h3 : 2 < Module.finrank (ZMod 2) I := h108.two_lt_finrank (isIrr_I h108 hI)
  obtain ⟨D⟩ := hE11 V (normalClosure Γ L) I hI.homogeneous hI.irrPlus h108.fixedSpace_H
    h108.sSup_isIrr
  have hk : Module.finrank D.F D.U = 2 := by
    have h := D.finrank_mul
    rw [hd] at h
    have h' : Module.finrank D.F D.U * Module.finrank (ZMod 2) I =
        2 * Module.finrank (ZMod 2) I := h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h'
  have hY1 : 2 ≤ Nat.card ↥(centralizerIn X (normalClosure Γ L)) := by
    obtain ⟨y, hy, hy1⟩ := exists_mem_centralizerIn_ne_one h108 hI hnf
    have : (2 : ℕ) ≤ Nat.card ↥(centralizerIn X (normalClosure Γ L)) := by
      by_contra hlt
      push Not at hlt
      have hcard1 : Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 1 := by
        have : 0 < Nat.card ↥(centralizerIn X (normalClosure Γ L)) := Nat.card_pos
        omega
      have := Subgroup.card_eq_one.1 hcard1
      rw [this] at hy
      exact hy1 (Subgroup.mem_bot.1 hy)
    exact this
  have hY2 : Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 2 := by
    by_cases hq : Nat.card D.F = 2
    · have := card_centralizerIn_le_two_of_card_two h108 D hk hq
      omega
    · exact card_centralizerIn_eq_two_of_not_endTrivial_c hs.conf hI hnf D hd
        (fun h => hq ((endTrivial_iff_card_two D hI0).1 h))
  obtain ⟨m, hKI, hHI, hXcard, hdI, hconc, A, hAX, hAsup, hAfaith, hAcard⟩ :=
    g118_apply_c hs.conf hI hApply hY2 hd
  have hsd := selfDual_restrictRange_top hHI hI.selfDual
  have hscan := g118_scan_nat hconc hsd hdI h3
  have hfix : Nat.card D.F ≠ 2 → fixedSpace X = Submodule.span (ZMod 2) {v₁} := by
    intro hq
    by_contra hB
    obtain ⟨-, hET⟩ := not_fixedSpace_imp_c hs.conf hI hItop hB
    exact hq ((endTrivial_iff_card_two D hI0).1 hET)
  rcases hscan with ⟨hd4, hm2, hnat, hend⟩ | ⟨hd4, hm2, hmod, hiso, hend⟩ |
      ⟨hd4, hperm, hend⟩ | ⟨hd8, hm6, hnat, hend⟩ | ⟨hd6, hm4, hperm, hend⟩
  ·
    have hF4 : Nat.card D.F = 4 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -, -⟩ := id hnat
    obtain ⟨eD1⟩ := id hD1
    exact f4_false_SL_c hQ hC9 hNine hs hI hnf D hk hF4 (by omega) (hfix (by omega))
      ((restrictRangeEquiv hHI hI.faithful).trans (φ'.trans eD1)) hD4 hnat
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ'⟩ := hiso
    obtain ⟨eD1⟩ := hD1
    exact f2_false_A5_c hC9 hNine hs hI hnf D hk hF2 (by omega) hmod
      ((restrictRangeEquiv hHI hI.faithful).trans (φ'.trans eD1))
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -⟩ := hperm
    exact f2_false_big_c hs.conf hI hnf D hk hF2 (n := 6) (Or.inl rfl)
      ((restrictRangeEquiv hHI hI.faithful).trans φ')
  ·
    have hF4 : Nat.card D.F = 4 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    exact f4_false_Sp_c hs.conf hI D hF4 (hfix (by omega)) hHI hAX hAsup hAfaith hAcard hm6
      hnat hD3
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -⟩ := hperm
    exact f2_false_big_c hs.conf hI hnf D hk hF2 (n := 8) (Or.inr rfl)
      ((restrictRangeEquiv hHI hI.faithful).trans φ')

end Final

section G118NineCanon


theorem g11_8_canon
    {Q : ConclPred} (hQ : QContains Q) (hC9 : G118NineContains Q)
    (hNine : G118NineInput) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
      QSetup Q B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∃ k : ℕ, Module.finrank (ZMod 2) V = k * Module.finrank (ZMod 2) I ∧ 2 < k) ∧
          fixedSpace X = Submodule.span (ZMod 2) {v₁} := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs I hI
  have h108 := hs.conf.h108
  obtain ⟨hnf, hItop⟩ := g11_7_canon hQ V B Γ v₁ W X X₀ L hs I hI
  have hge := CFSG.Quasithin.G11.G118.two_mul_finrank_le h108 hI hItop
  obtain ⟨D⟩ := e11 V (normalClosure Γ L) I hI.homogeneous hI.irrPlus h108.fixedSpace_H
    h108.sSup_isIrr
  have hk : Module.finrank (ZMod 2) V = Module.finrank D.F D.U * Module.finrank (ZMod 2) I :=
    D.finrank_mul.symm
  by_cases hlt : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V
  · refine ⟨⟨Module.finrank D.F D.U, hk, ?_⟩, ?_⟩
    · by_contra hle
      push Not at hle
      have := Nat.mul_le_mul_right (Module.finrank (ZMod 2) I) hle
      omega
    · by_contra hB
      have := (not_fixedSpace_imp_c hs.conf hI hItop hB).1
      omega
  · exfalso
    have hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I := by omega
    exact k2_false_c hQ hC9 hNine hs hI hnf hItop hd e11
      (g93_apply Harris.g93StmtDimensionOnly_holds) G118.sl24IsoA5
      G118.sp44RankInput G118.gl24SubInput

end G118NineCanon

end Canon

end G11

end CFSG.Quasithin
