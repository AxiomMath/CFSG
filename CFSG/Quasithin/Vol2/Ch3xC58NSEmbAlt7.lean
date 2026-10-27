module

public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbA7c
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbC127
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourJNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Main
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.QuasithinUnique.L246C127.Emb

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cjSub_eq_of_mem_normalizer {H : Type*} [Group H] {g : H} {A : Subgroup H}
    (hg : g ∈ Subgroup.normalizer (A : Set H)) : cjSub g A = A := by
  refine le_antisymm (cjSub_le hg le_rfl) ?_
  calc A = cjSub g (cjSub g⁻¹ A) := (cjSub_cjSub_inv g A).symm
    _ ≤ cjSub g A := cjSub_mono (cjSub_le (inv_mem hg) le_rfl)

omit [Finite G] in
theorem mem_normalizer_of_cjSub_eq {H : Type*} [Group H] {g : H} {A : Subgroup H}
    (h : cjSub g A = A) : g ∈ Subgroup.normalizer (A : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h, mem_cjSub]
    simpa [mul_assoc] using hx
  · intro hx
    rw [← h, mem_cjSub] at hx
    simpa [mul_assoc] using hx

omit [Finite G] in
theorem commutator_eq_of_autI_eq {V : Subgroup G} (hV : IsElemAbelian 2 V) {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G))
    (h : autI hV A = autI hV B) : ⁅V, A⁆ = ⁅V, B⁆ := by
  have key : ∀ {A B : Subgroup G}, A ≤ Subgroup.normalizer (V : Set G) →
      B ≤ Subgroup.normalizer (V : Set G) → autI hV A = autI hV B → ⁅V, A⁆ ≤ ⁅V, B⁆ := by
    intro A B hA hB h
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have hmem : convI hV ⟨a, hA ha⟩ ∈ autI hV B := h ▸ convI_mem_autI hV ha (hA ha)
    obtain ⟨b, hbB, hb⟩ := (mem_autI hV).1 hmem
    have hc : ((b⁻¹ * ⟨a, hA ha⟩ : Subgroup.normalizer (V : Set G)) : G) ∈
        Subgroup.centralizer (V : Set G) := by
      rw [← convI_eq_one_iff hV, map_mul, map_inv, hb, inv_mul_cancel]
    have hcv : (b : G)⁻¹ * a * v = v * ((b : G)⁻¹ * a) := by
      have := Subgroup.mem_centralizer_iff.mp hc v hv
      simpa [mul_assoc] using this.symm
    have e : ⁅v, a⁆ = ⁅v, (b : G)⁆ := by
      have ha' : a = (b : G) * ((b : G)⁻¹ * a) := by group
      rw [commutatorElement_def, commutatorElement_def]
      calc v * a * v⁻¹ * a⁻¹
          = v * (b : G) * (((b : G)⁻¹ * a) * v⁻¹) * a⁻¹ := by group
        _ = v * (b : G) * (v⁻¹ * ((b : G)⁻¹ * a)) * a⁻¹ := by
            congr 2
            calc (b : G)⁻¹ * a * v⁻¹ = v⁻¹ * (v * ((b : G)⁻¹ * a)) * v⁻¹ := by group
              _ = v⁻¹ * ((b : G)⁻¹ * a * v) * v⁻¹ := by rw [hcv]
              _ = v⁻¹ * ((b : G)⁻¹ * a) := by group
        _ = v * (b : G) * v⁻¹ * (b : G)⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hv hbB
  exact le_antisymm (key hA hB h) (key hB hA h.symm)

theorem le_normalizer_blockU_of_alt7 (hB42 : L238.AltBlockStatementJCat (G := G))
    {X T P K L N : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hPX : P ≤ X) (hTP : T ≤ P) (hK : IsChi0Block P K)
    (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hV : IsElemAbelian 2 (VZ T X)) (hL : IsBlock2 X L) (hKL : K ≤ L)
    (hULV : blockU L ≤ VZ T X) (eL : ↥(autI hV L) ≃* alternatingGroup (Fin 7))
    (eK : ↥(autI hV K) ≃* alternatingGroup (Fin 5))
    (hsyl : IsSylowTwoOf (autI hV T ⊓ autI hV L) (autI hV L)) (hNX : N ≤ X)
    (hNT : N ≤ Subgroup.normalizer (T : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    N ≤ Subgroup.normalizer (blockU K : Set G) := by
  have S : Setting X T P K := ⟨hX, hT, hPX, hTP, hK.1⟩
  have hXV : X ≤ Subgroup.normalizer (VZ T X : Set G) := S.hXV
  have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hL.2.1.trans hXV
  have hLalt := isAltQuotient_of_equiv hV hLN eL
  have hm : Odd 7 := ⟨3, rfl⟩
  have hJT : thompsonJ T ≤ T := (C1GN.thompsonJ_le_baum T).trans (C1GN.baum_le T)
  have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
    L238.le_normalizer_of_isAltQuotient hX h38 hT hL hULV hm (by norm_num) hLalt hKL
      (L238.not_isPGroup_two_of_isShort2 hK.1.1) hJT (hKJ.le.trans hKL)
  have hnotKC : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) :=
    C1GN.not_le_of_isAltQuotient (isAltQuotient_of_equiv hV S.hKN eK) (by norm_num)
  have hKLJ : K ≤ ⁅L, thompsonJ T⁆ :=
    calc K = ⁅K, thompsonJ T⁆ := hKJ.symm
      _ ≤ ⁅L, thompsonJ T⁆ := Subgroup.commutator_mono hKL le_rfl
  have hnotLJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
    hnotKC (hKLJ.trans h)
  have S' : Setting X T X L := ⟨hX, hT, le_rfl, hT.1, hL⟩
  have hc : Subgroup.center ↥(autI hV L) = ⊥ :=
    center_eq_bot_of_mulEquiv eL (alternatingGroup.center_eq_bot (by simp))
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    rcases hB42 X T L hX hSQ hT hL hULV hJN hnotLJ ⟨7, hm, by norm_num, hLalt⟩ with hchi | hexc
    · rcases hchi.2 with ⟨e, he, hlin⟩ | ⟨m', -, hm3, hAlt⟩
      · exfalso
        have hno := S'.noOrderFour_autI_of_types hV hULV (Or.inl ⟨e, he, hlin⟩) hc
        exact not_noOrderFour_alt (by norm_num) (hno.of_mulEquiv eL.symm)
      · obtain ⟨α, hα, hker, -⟩ := id hAlt
        obtain ⟨φ⟩ := S'.nonempty_equiv_of_center_eq_bot hV hULV α hα hker hc
        have hcard : Nat.card (alternatingGroup (Fin m')) = Nat.card (alternatingGroup (Fin 7)) :=
          (Nat.card_congr φ.symm.toEquiv).trans (Nat.card_congr eL.toEquiv)
        have : Nontrivial (Fin m') := Fin.nontrivial_iff_two_le.mpr (by omega)
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
          card_alternatingGroup, Fintype.card_fin, Fintype.card_fin] at hcard
        have h2 : 2 ∣ m'.factorial := Nat.dvd_factorial (by norm_num) (by omega)
        have h7 : (7 : ℕ).factorial = 5040 := by decide
        rw [h7] at hcard
        have hf : m'.factorial = (7 : ℕ).factorial := by
          rw [h7]
          omega
        have hm'7 : m' = 7 := (Nat.factorial_inj (by omega)).mp hf
        subst hm'7
        exact L246A7.le_normalizer_of_alt7 hSQ h38 hL hAlt
    · exact L238.le_normalizer_of_exceptionalA7_cat hSQ h38 hL hexc
  have hU : blockU K = ⁅VZ T X, K⁆ := le_antisymm (S.blockU_le_commutator_VZ hKZ) S.comm_V_le
  have hAL : autI hV K ≤ autI hV L := autI_mono hV hKL
  intro n hn
  have hnX : n ∈ X := hNX hn
  have hnV : n ∈ Subgroup.normalizer (VZ T X : Set G) := hXV hnX
  have hnL : cjSub n L = L := cjSub_eq_of_mem_normalizer (hXL hnX)
  have hnT : n ∈ Subgroup.normalizer (T : Set G) := hNT hn
  set B := autI hV (cjSub n K) with hBdef
  have hBmap : (autI hV K).map (MulAut.conj (convI hV ⟨n, hnV⟩)).toMonoidHom = B :=
    autI_cjSub hV hnV K
  have hBL : B ≤ autI hV L := by
    rw [← hnL]
    exact autI_mono hV (cjSub_mono hKL)
  have eB : ↥B ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hBmap.symm).trans ((Subgroup.equivMapOfInjective (autI hV K)
      (MulAut.conj (convI hV ⟨n, hnV⟩)).toMonoidHom (MulAut.conj _).injective).symm.trans eK)
  have hDA : autI hV T ⊓ autI hV L ≤ Subgroup.normalizer (autI hV K : Set _) := by
    intro d hd
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hd.1
    apply mem_normalizer_of_cjSub_eq
    show (autI hV K).map (MulAut.conj (convI hV t)).toMonoidHom = autI hV K
    rw [autI_cjSub hV t.2 K, cjSub_eq_of_mem_normalizer (hTK htT)]
  have hDB : autI hV T ⊓ autI hV L ≤ Subgroup.normalizer (B : Set _) := by
    intro d hd
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hd.1
    apply mem_normalizer_of_cjSub_eq
    show (autI hV (cjSub n K)).map (MulAut.conj (convI hV t)).toMonoidHom = autI hV (cjSub n K)
    rw [autI_cjSub hV t.2 (cjSub n K)]
    have hs : n⁻¹ * (t : G) * n ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnT) (t : G)).mp htT
      simpa using this
    have e1 : cjSub (t : G) (cjSub n K) = cjSub n (cjSub (n⁻¹ * (t : G) * n) K) := by
      ext x
      simp only [mem_cjSub]
      have e : (n⁻¹ * (t : G) * n)⁻¹ * (n⁻¹ * x * n) * (n⁻¹ * (t : G) * n) =
          n⁻¹ * ((t : G)⁻¹ * x * (t : G)) * n := by group
      rw [e]
    rw [e1, cjSub_eq_of_mem_normalizer (hTK hs)]
  have key : autI hV K = B :=
    CFSG.Quasithin.C58NS.Emb.eq_of_normalized_of_equiv eL hAL hBL eK eB hsyl hDA hDB
  have hKV : K ≤ Subgroup.normalizer (VZ T X : Set G) := S.hKN
  have hKnV : cjSub n K ≤ Subgroup.normalizer (VZ T X : Set G) :=
    cjSub_le (Subgroup.le_normalizer hnV) hKV
  have hcomm := commutator_eq_of_autI_eq hV hKV hKnV key
  apply mem_normalizer_of_cjSub_eq
  rw [hU]
  have e2 : cjSub n ⁅VZ T X, K⁆ = ⁅cjSub n (VZ T X), cjSub n K⁆ := by
    unfold cjSub
    rw [Subgroup.map_commutator]
  rw [e2, cjSub_eq_of_mem_normalizer hnV, ← hcomm]

end CFSG.QuasithinUnique.L246C127.Emb
