module

public import CFSG.GroupTheory.SylowInfSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFourN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Data

theorem mem_hSet_of_mem_calMOf_ne (D : Data G) {N : Subgroup G} (hN : N ∈ calMOf D.T)
    (hNM : N ≠ D.M) : N ∈ hSet D.T D.M :=
  ⟨hN.2, fun h => hNM (hN.1.2 D.M D.maxLocal.1 h).symm, D.standing.charTwo N hN.1.1⟩

end Data

theorem exists_le_calLStar (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    ∃ L' ∈ calLStar D.T D.M, L ≤ L' := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨L', hLL', hmax⟩ := Finite.exists_le_maximal hL
  exact ⟨L', hmax, hLL'⟩

theorem exists_ctx23L_L_eq (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (h208 : S20_8 D)
    (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {L : Subgroup G} (hL : L ∈ calLStar D.T D.M) :
    ∃ c : Ctx23L D Ch, c.L = L := by
  obtain ⟨c21, hL0L⟩ := uc22main1_ctx21 D Ch h1930 h2010 hCh hL.1
  let N : Subgroup G :=
    normalizer ((⨆ K ∈ calLOf D.T D.M (normalizer (L : Set G)), K : Subgroup G) : Set G)
  have hN : calMOf (L ⊔ D.T) = {N} := h208 h1930 L hL
  exact ⟨⟨⟨c21, c₀.hTI⟩, L, hL, hL0L, N, hN⟩, rfl⟩

theorem le_cCompSpan_of_mem_calLOf (D : Data G) {H L : Subgroup G} (hTH : D.T ≤ H)
    (hL : L ∈ calLOf D.T D.M H) : L ≤ CFSG.Quasithin.cCompSpan H := by
  obtain ⟨⟨-, -, -, K, hK, hLK⟩, hsub⟩ := hL
  have hKL : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKL
  rw [hLK]
  exact iSup_le fun t => CFSG.Quasithin.le_cCompSpan (uc22p20b_cj_mem_cComp hKH (hTH t.2))

theorem cCompSpan_le_normalizer_of_mem_calLOf (D : Data G) {H L : Subgroup G} (hTH : D.T ≤ H)
    (hL : L ∈ calLOf D.T D.M H) : CFSG.Quasithin.cCompSpan H ≤ normalizer (L : Set G) := by
  obtain ⟨⟨-, -, -, K, hK, hLK⟩, hsub⟩ := hL
  have hKL : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKL
  rw [hLK]
  exact uc22p20b_le_normalizer_iSup (fun t : D.T => uc22p20bCj (t : G) K)
    (CFSG.Quasithin.cCompSpan H) fun t =>
      uc22p20e_cCompSpan_le_normalizer (uc22p20b_cj_mem_cComp hKH (hTH t.2))

theorem inf_le_centralizer_U_of_calL (D : Data G) (Ch : Choice2011 G) (hin : S23_4_inputN D Ch)
    (h1930 : H1930 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {L : Subgroup G} (hL : L ∈ calL D.T D.M) :
    D.T ⊓ L ≤ centralizer (D.U : Set G) := by
  obtain ⟨L', hL', hLL'⟩ := exists_le_calLStar D hL
  obtain ⟨c, rfl⟩ := exists_ctx23L_L_eq D Ch h1930 h208 h2010 hCh c₀ hL'
  have hLof : c.L ∈ calLOf D.T D.M c.N :=
    ⟨c.hL.1, (Ctx23L.N_facts c h208 h1930).2.2.1⟩
  have hXle : c.L ≤ X23_4 D c.N := le_iSup₂_of_le c.L hLof le_rfl
  have hQleA : D.T ⊓ c.L ≤ X23_4 D c.N ⊓ D.M :=
    le_inf (inf_le_right.trans hXle) (inf_le_left.trans D.sylowM.le)
  have hQp : IsPGroup 2 ↥(D.T ⊓ c.L) := D.sylowM.isPGroup.to_le inf_le_left
  have hU : IsElemAbelian 2 D.U :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2
  have hAnorm : X23_4 D c.N ⊓ D.M ≤ normalizer (D.U : Set G) := by
    rw [Data.normalizer_U_eq D]
    exact inf_le_right
  obtain ⟨hAcomm, hirr⟩ := hin h1930 c
  have hQleC : D.T ⊓ c.L ≤ centralizer (D.U : Set G) :=
    CFSG.GroupTheory.pSubgroup_le_centralizer_of_irreducible
      (p := 2) (U := D.U) (A := X23_4 D c.N ⊓ D.M) hU (Data.U_ne_bot D) hAnorm hAcomm hirr
      hQp (hQleA.trans le_sup_left)
  exact (inf_le_inf_left D.T hLL').trans hQleC

theorem le_centralizer_U_of_isPGroup (D : Data G) (Ch : Choice2011 G) (hin : S23_4_inputN D Ch)
    (h1930 : H1930 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {L Q : Subgroup G} (hL : L ∈ calL D.T D.M) (hQ : IsPGroup 2 Q)
    (hQL : Q ≤ L ⊓ D.M) : Q ≤ centralizer (D.U : Set G) := by
  have hS : D.T ⊓ L ≤ centralizer (D.U : Set G) :=
    inf_le_centralizer_U_of_calL D Ch hin h1930 h208 h2010 hCh c₀ hL
  have hT : IsSylowOf 2 D.T (L ⊔ D.T) := D.sylowG.of_le le_sup_right le_top
  have hTL : IsSylowOf 2 (D.T ⊓ L) L :=
    hT.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hL.1)
  have hTM : D.T ⊓ L ≤ L ⊓ D.M :=
    le_inf (inf_le_right : D.T ⊓ L ≤ L) (inf_le_left.trans D.sylowM.le)
  have hTLM : IsSylowOf 2 (D.T ⊓ L) (L ⊓ D.M) := hTL.of_le hTM inf_le_left
  have hMC : D.M ≤ normalizer (centralizer (D.U : Set G) : Set G) := by
    rw [← Data.normalizer_U_eq D]
    exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (D.U)
  set C : Subgroup G := centralizer (D.U : Set G)
  have hPleK : D.T ⊓ L ≤ C ⊓ (L ⊓ D.M) := le_inf hS hTM
  have hKH : C ⊓ (L ⊓ D.M) ≤ L ⊓ D.M := inf_le_right
  have hHK : L ⊓ D.M ≤ normalizer ((C ⊓ (L ⊓ D.M) : Subgroup G) : Set G) :=
    (le_inf (inf_le_right.trans hMC) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact (CFSG.GroupTheory.le_of_isPGroup_of_isSylowOf_le_normal hTLM hPleK hKH hHK hQ hQL).trans
    inf_le_left

@[expose] def X23_4hat (D : Data G) (N : Subgroup G) : Subgroup G :=
  ⨆ L' ∈ {L' | ∃ L ∈ calLOf D.T D.M N, ∃ m ∈ N ⊓ D.M,
    L' = L.map (MulAut.conj m).toMonoidHom}, L'

private abbrev X23_4hatIndex (D : Data G) (N : Subgroup G) :=
  {L : Subgroup G // L ∈ calLOf D.T D.M N} × ↥(N ⊓ D.M)

private def X23_4hatGen (D : Data G) (N : Subgroup G) (p : X23_4hatIndex D N) :
    Subgroup G :=
  (p.1 : Subgroup G).map (MulAut.conj (p.2 : G)).toMonoidHom

private theorem X23_4hat_eq_iSup (D : Data G) (N : Subgroup G) :
    X23_4hat D N = ⨆ p : X23_4hatIndex D N, X23_4hatGen D N p := by
  unfold X23_4hat
  rw [show {L' : Subgroup G | ∃ L ∈ calLOf D.T D.M N, ∃ m ∈ N ⊓ D.M,
      L' = L.map (MulAut.conj m).toMonoidHom} = Set.range (X23_4hatGen D N) from ?_]
  · rw [iSup_range]
  · ext K
    constructor
    · rintro ⟨L, hL, m, hm, rfl⟩
      exact ⟨(⟨L, hL⟩, ⟨m, hm⟩), rfl⟩
    · rintro ⟨⟨⟨L, hL⟩, ⟨m, hm⟩⟩, rfl⟩
      exact ⟨L, hL, m, hm, rfl⟩

private theorem X23_4_le_X23_4hat (D : Data G) (N : Subgroup G) :
    X23_4 D N ≤ X23_4hat D N := by
  rw [X23_4hat_eq_iSup]
  refine iSup₂_le fun L hL => ?_
  let p : X23_4hatIndex D N :=
    (⟨L, hL⟩, (⟨1, ⟨N.one_mem, D.M.one_mem⟩⟩ : ↥(N ⊓ D.M)))
  have hp : X23_4hatGen D N p = L := by
    have h1 : ((p.2 : ↥(N ⊓ D.M)) : G) = 1 := rfl
    rw [X23_4hatGen, h1]
    rw [show MulAut.conj (1 : G) = 1 by ext x; simp]
    change Subgroup.map (MonoidHom.id G) L = L
    exact Subgroup.map_id L
  rw [← hp]
  exact le_iSup (fun q => X23_4hatGen D N q) p

private theorem X23_4hat_le (D : Data G) (N : Subgroup G) : X23_4hat D N ≤ N := by
  rw [X23_4hat_eq_iSup]
  refine iSup_le fun p => ?_
  rintro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  exact N.mul_mem (N.mul_mem p.2.property.1 (CFSG.Quasithin.A3.subnormal_le p.1.2.2 hl))
    (N.inv_mem p.2.property.1)

private theorem cCompSpan_conj_mem_X23_4hatGen (D : Data G) {N : Subgroup G} (hTN : D.T ≤ N)
    (p : X23_4hatIndex D N) {c x : G} (hc : c ∈ CFSG.Quasithin.cCompSpan N)
    (hx : x ∈ X23_4hatGen D N p) : c * x * c⁻¹ ∈ X23_4hatGen D N p := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  have hNnorm : N ≤ normalizer ((CFSG.Quasithin.cCompSpan N : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20e_cCompSpan_le N)).mp
      (uc22p20b_normal_cCompSpan N)
  have hy : ((p.2 : ↥(N ⊓ D.M)) : G)⁻¹ * c * ((p.2 : ↥(N ⊓ D.M)) : G) ∈
      CFSG.Quasithin.cCompSpan N :=
    by simpa using (Subgroup.mem_normalizer_iff.1 (hNnorm (N.inv_mem p.2.property.1)) c).mp hc
  have hNL : CFSG.Quasithin.cCompSpan N ≤ normalizer (p.1 : Subgroup G) :=
    cCompSpan_le_normalizer_of_mem_calLOf D hTN p.1.2
  have hyl : (((p.2 : ↥(N ⊓ D.M)) : G)⁻¹ * c * ((p.2 : ↥(N ⊓ D.M)) : G)) * l *
      (((p.2 : ↥(N ⊓ D.M)) : G)⁻¹ * c * ((p.2 : ↥(N ⊓ D.M)) : G))⁻¹ ∈
      (p.1 : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.1 (hNL hy) l).mp hl
  refine Subgroup.mem_map.mpr ⟨_, hyl, ?_⟩
  change MulAut.conj ((p.2 : ↥(N ⊓ D.M)) : G)
      ((((p.2 : ↥(N ⊓ D.M)) : G)⁻¹ * c * ((p.2 : ↥(N ⊓ D.M)) : G)) * l *
        (((p.2 : ↥(N ⊓ D.M)) : G)⁻¹ * c * ((p.2 : ↥(N ⊓ D.M)) : G))⁻¹) =
    c * MulAut.conj ((p.2 : ↥(N ⊓ D.M)) : G) l * c⁻¹
  simp only [MulAut.conj_apply]
  group

private theorem cCompSpan_le_normalizer_X23_4hatGen (D : Data G) {N : Subgroup G}
    (hTN : D.T ≤ N) (p : X23_4hatIndex D N) :
    CFSG.Quasithin.cCompSpan N ≤ normalizer (X23_4hatGen D N p : Set G) := by
  rintro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact cCompSpan_conj_mem_X23_4hatGen D hTN p hc
  · intro hx
    have h := cCompSpan_conj_mem_X23_4hatGen D hTN p (c := c⁻¹) (x := c * x * c⁻¹)
      ((CFSG.Quasithin.cCompSpan N).inv_mem hc) hx
    simpa [mul_assoc] using h

private theorem X23_4hatGen_le_cCompSpan (D : Data G) {N : Subgroup G} (hTN : D.T ≤ N)
    (p : X23_4hatIndex D N) : X23_4hatGen D N p ≤ CFSG.Quasithin.cCompSpan N := by
  rintro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  have hNnorm : N ≤ normalizer ((CFSG.Quasithin.cCompSpan N : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20e_cCompSpan_le N)).mp
      (uc22p20b_normal_cCompSpan N)
  exact (Subgroup.mem_normalizer_iff.1 (hNnorm p.2.property.1) l).mp
    (le_cCompSpan_of_mem_calLOf D hTN p.1.2 hl)

private theorem X23_4hatGen_inf_le_centralizer (D : Data G) (Ch : Choice2011 G)
    (hin : S23_4_inputN D Ch) (h1930 : H1930 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {N : Subgroup G} (p : X23_4hatIndex D N) :
    D.T ⊓ X23_4hatGen D N p ≤ centralizer (D.U : Set G) := by
  obtain ⟨L, m⟩ := p
  set K : Subgroup G := X23_4hatGen D N (L, m) with hK
  set Q : Subgroup G := (D.T ⊓ K).map
    (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom with hQ
  have hcomp₁ : (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom.comp
      (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)).toMonoidHom = MonoidHom.id G := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  have hQleL : Q ≤ (L : Subgroup G) := by
    calc Q ≤ K.map (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom :=
          Subgroup.map_mono inf_le_right
      _ = (L : Subgroup G) := by
          rw [hK, X23_4hatGen, Subgroup.map_map, hcomp₁, Subgroup.map_id]
  have hQleM : Q ≤ D.M := by
    refine (Subgroup.map_mono (f := (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom)
      (inf_le_left : D.T ⊓ K ≤ D.T)).trans ?_
    rintro x ⟨t, ht, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem m.property.2) (D.sylowM.le ht))
      (by simpa using m.property.2)
  have hQp : IsPGroup 2 Q :=
    (D.sylowM.isPGroup.to_le (inf_le_left : D.T ⊓ K ≤ D.T)).map
      (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom
  have hQleC : Q ≤ centralizer (D.U : Set G) :=
    le_centralizer_U_of_isPGroup D Ch hin h1930 h208 h2010 hCh c₀ L.2.1 hQp
      (le_inf hQleL hQleM)
  have hMC : D.M ≤ normalizer (centralizer (D.U : Set G) : Set G) := by
    rw [← Data.normalizer_U_eq D]
    exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (D.U)
  have hCmap : (centralizer (D.U : Set G)).map
      (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)).toMonoidHom = centralizer (D.U : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMC m.property.2)
  have hmap : Q.map (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)).toMonoidHom = D.T ⊓ K := by
    rw [hQ, Subgroup.map_map]
    have hcomp₂ : (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)).toMonoidHom.comp
        (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp₂, Subgroup.map_id]
  have hle := Subgroup.map_mono (f := (MulAut.conj ((m : ↥(N ⊓ D.M)) : G)).toMonoidHom) hQleC
  rwa [hmap, hCmap] at hle

private theorem cCompSpan_le_normalizer_X23_4hat (D : Data G) {N : Subgroup G}
    (hTN : D.T ≤ N) :
    CFSG.Quasithin.cCompSpan N ≤ normalizer (X23_4hat D N : Set G) := by
  rw [X23_4hat_eq_iSup]
  exact uc22p20b_le_normalizer_iSup (fun p => X23_4hatGen D N p)
    (CFSG.Quasithin.cCompSpan N) fun p => cCompSpan_le_normalizer_X23_4hatGen D hTN p

private theorem X23_4hat_map_conj_le (D : Data G) {N : Subgroup G} {m : G} (hmN : m ∈ N)
    (hmM : m ∈ D.M) :
    (X23_4hat D N).map (MulAut.conj m).toMonoidHom ≤ X23_4hat D N := by
  rw [X23_4hat_eq_iSup, Subgroup.map_iSup]
  refine iSup_le fun p => ?_
  have hterm : (X23_4hatGen D N p).map (MulAut.conj m).toMonoidHom =
      X23_4hatGen D N (p.1, (⟨m * (p.2 : G),
        N.mul_mem hmN p.2.property.1, D.M.mul_mem hmM p.2.property.2⟩ : ↥(N ⊓ D.M))) := by
    rw [X23_4hatGen, X23_4hatGen, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hterm]
  exact le_iSup (fun q => X23_4hatGen D N q) _

private theorem mem_normalizer_X23_4hat_of_mem (D : Data G) {N : Subgroup G} {m : G}
    (hmN : m ∈ N) (hmM : m ∈ D.M) : m ∈ normalizer (X23_4hat D N : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := X23_4hat_map_conj_le D hmN hmM
  have h2 := X23_4hat_map_conj_le D (N.inv_mem hmN) (D.M.inv_mem hmM)
  refine le_antisymm h1 ?_
  have hcomp : ((X23_4hat D N).map (MulAut.conj m⁻¹).toMonoidHom).map
      (MulAut.conj m).toMonoidHom = X23_4hat D N := by
    rw [Subgroup.map_map]
    have hid : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hid, Subgroup.map_id]
  calc X23_4hat D N = ((X23_4hat D N).map (MulAut.conj m⁻¹).toMonoidHom).map
        (MulAut.conj m).toMonoidHom := hcomp.symm
    _ ≤ (X23_4hat D N).map (MulAut.conj m).toMonoidHom := Subgroup.map_mono h2

private theorem le_normalizer_X23_4hat (D : Data G) {N : Subgroup G} (h204 : S20_4 D)
    (h1930 : H1930 D) (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) :
    N ≤ normalizer (X23_4hat D N : Set G) := by
  have hprod := h204 h1930 N (Data.mem_hSet_of_mem_calMOf_ne D hN hNM)
  have hcomp := cCompSpan_le_normalizer_X23_4hat D hN.2
  have hXleComp : X23_4 D N ≤ CFSG.Quasithin.cCompSpan N :=
    iSup₂_le fun L hL => le_cCompSpan_of_mem_calLOf D hN.2 hL
  intro n hn
  have hn' : n ∈ ((⨆ L ∈ calLOf D.T D.M N, L : Subgroup G) : Set G) *
      ((N ⊓ D.M : Subgroup G) : Set G) := by
    rw [hprod]
    exact hn
  obtain ⟨x, hx, m, hm, rfl⟩ := hn'
  exact (normalizer (X23_4hat D N : Set G)).mul_mem (hcomp (hXleComp hx))
    (mem_normalizer_X23_4hat_of_mem D hm.1 hm.2)

private theorem X23_4hat_inf_le_centralizer (D : Data G) (Ch : Choice2011 G)
    (hin : S23_4_inputN D Ch) (h1930 : H1930 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {N : Subgroup G} (hN : N ∈ calMOf D.T) :
    D.T ⊓ X23_4hat D N ≤ centralizer (D.U : Set G) := by
  have hT : IsSylowOf 2 D.T N := D.sylowG.of_le hN.2 le_top
  have hE : CFSG.Open.IsSubnormal (CFSG.Quasithin.cCompSpan N) N :=
    CFSG.Open.IsSubnormal.step (uc22p20e_cCompSpan_le N) (uc22p20b_normal_cCompSpan N)
      (CFSG.Open.IsSubnormal.refl N)
  rw [X23_4hat_eq_iSup,
    ← iSup_range (g := (fun x : Subgroup G => x)) (f := X23_4hatGen D N)]
  refine CFSG.GroupTheory.inf_iSup_le_of_normal_family (p := 2) (T := D.T) (H := N)
    (E := CFSG.Quasithin.cCompSpan N) (Q := centralizer (D.U : Set G)) hT hE
    (Set.range (X23_4hatGen D N)) ?_ ?_ ?_
  · rintro K ⟨p, rfl⟩
    exact X23_4hatGen_le_cCompSpan D hN.2 p
  · rintro K ⟨p, rfl⟩
    exact cCompSpan_le_normalizer_X23_4hatGen D hN.2 p
  · rintro K ⟨p, rfl⟩
    exact X23_4hatGen_inf_le_centralizer D Ch hin h1930 h208 h2010 hCh c₀ p

private theorem X23_4hat_mul_inf_M (D : Data G) {N : Subgroup G} (h204 : S20_4 D)
    (h1930 : H1930 D) (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) :
    ((X23_4hat D N : Set G) * ((N ⊓ D.M : Subgroup G) : Set G)) = N := by
  have hXleN : X23_4hat D N ≤ N := X23_4hat_le D N
  have hprod := h204 h1930 N (Data.mem_hSet_of_mem_calMOf_ne D hN hNM)
  have hXmono : X23_4 D N ≤ X23_4hat D N := X23_4_le_X23_4hat D N
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact N.mul_mem (hXleN hx) hy.1
  · intro n hn
    have hn' : n ∈ ((⨆ L ∈ calLOf D.T D.M N, L : Subgroup G) : Set G) *
        ((N ⊓ D.M : Subgroup G) : Set G) := by
      rw [hprod]
      exact hn
    obtain ⟨x, hx, y, hy, rfl⟩ := hn'
    exact ⟨x, hXmono hx, y, hy, rfl⟩

theorem exists_hX_of_inputN (D : Data G) (Ch : Choice2011 G) (hin : S23_4_inputN D Ch)
    (h1930 : H1930 D) (h204 : S20_4 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (c₀ : Ctx23L D Ch) {N : Subgroup G} (hN : N ∈ calMOf D.T) (hNM : N ≠ D.M) :
    ∃ X : Subgroup G, X ≤ N ∧ (X.subgroupOf N).Normal ∧
      ((X : Set G) * ((N ⊓ D.M : Subgroup G) : Set G) = N) ∧
      D.T ⊓ (X ⊔ (N ⊓ centralizer (D.U : Set G))) ≤ centralizer (D.U : Set G) := by
  let X : Subgroup G := X23_4hat D N
  have hXleN : X ≤ N := X23_4hat_le D N
  have hNleX : N ≤ normalizer (X : Set G) := le_normalizer_X23_4hat D h204 h1930 hN hNM
  have hXnormal : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXleN).mpr hNleX
  have hXprod : ((X : Set G) * ((N ⊓ D.M : Subgroup G) : Set G)) = N :=
    X23_4hat_mul_inf_M D h204 h1930 hN hNM
  have hTX : D.T ⊓ X ≤ centralizer (D.U : Set G) :=
    X23_4hat_inf_le_centralizer D Ch hin h1930 h208 h2010 hCh c₀ hN
  have hMC : D.M ≤ normalizer (centralizer (D.U : Set G) : Set G) := by
    rw [← Data.normalizer_U_eq D]
    exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (D.U)
  have hCM : centralizer (D.U : Set G) ≤ D.M := by
    rw [← Data.normalizer_U_eq D]
    exact Subgroup.centralizer_le_normalizer (D.U : Set G)
  have hT : IsSylowOf 2 D.T N := D.sylowG.of_le hN.2 le_top
  have hTNM : IsSylowOf 2 D.T (N ⊓ D.M) :=
    hT.of_le (le_inf hN.2 D.sylowM.le) (inf_le_left : N ⊓ D.M ≤ N)
  have hA : IsSylowOf 2 (D.T ⊓ (N ⊓ centralizer (D.U : Set G)))
      (N ⊓ centralizer (D.U : Set G)) :=
    hTNM.inf_of_le_normalizer (inf_le_inf le_rfl hCM)
      ((le_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans hMC)).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hB : IsSylowOf 2 (D.T ⊓ X) X := hT.inf_of_le_normalizer hXleN hNleX
  have hsplit := CFSG.GroupTheory.inf_sup_eq_sup_of_isSylowOf (p := 2) (T := D.T)
    (A := N ⊓ centralizer (D.U : Set G)) (B := X) hT.isPGroup
    (inf_le_left.trans hNleX) hA hB
  have hfourth : D.T ⊓ (X ⊔ (N ⊓ centralizer (D.U : Set G))) ≤
      centralizer (D.U : Set G) := by
    rw [sup_comm, hsplit]
    exact sup_le (inf_le_right.trans inf_le_right) hTX
  exact ⟨X, hXleN, hXnormal, hXprod, hfourth⟩

theorem s23_4_of_inputN (D : Data G) (Ch : Choice2011 G) (hin : S23_4_inputN D Ch)
    (hfus : CFSG.GroupTheory.FamilyControlsFusion (calMOf D.T) D.T)
    (h204 : S20_4 D) (h208 : S20_8 D) (h2010 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M) : S23_4 D Ch := by
  intro h1930 c
  have hU : IsElemAbelian 2 D.U :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2
  have hAcomm : ⁅(X23_4 D c.N ⊓ D.M), (X23_4 D c.N ⊓ D.M)⁆ ≤
      centralizer (D.U : Set G) := (hin h1930 c).1
  have hirr : IrrOn (X23_4 D c.N ⊓ D.M) D.U := (hin h1930 c).2
  have hAnormU : X23_4 D c.N ⊓ D.M ≤ normalizer (D.U : Set G) := by
    rw [Data.normalizer_U_eq D]
    exact inf_le_right
  have hTnormU : D.T ≤ normalizer (D.U : Set G) := by
    rw [Data.normalizer_U_eq D]
    exact D.sylowM.le
  have hTnormX : D.T ≤ normalizer (X23_4 D c.N : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, X23_4]
    rw [Subgroup.map_iSup]
    refine iSup_congr fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hL => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL.1.1 ht)
  have hTnormM : D.T ≤ normalizer (D.M : Set G) :=
    D.sylowM.le.trans Subgroup.le_normalizer
  have hTnormA : D.T ≤ normalizer ((X23_4 D c.N ⊓ D.M : Subgroup G) : Set G) :=
    (le_inf hTnormX hTnormM).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcyc : ∃ x ∈ D.T, ∀ y ∈ D.T, ∃ m : ℕ, y⁻¹ * x ^ m ∈ centralizer (D.U : Set G) :=
    CFSG.GroupTheory.isCyclic_mod_centralizer_of_isPGroup_normalizer
      (p := 2) (U := D.U) (A := X23_4 D c.N ⊓ D.M) (P := D.T)
      hU (Data.U_ne_bot D) hAnormU hAcomm hirr D.sylowM.isPGroup hTnormU hTnormA
  have hX : ∀ N ∈ calMOf D.T, N ≠ D.M → ∃ X : Subgroup G, X ≤ N ∧
      (X.subgroupOf N).Normal ∧
      ((X : Set G) * ((N ⊓ D.M : Subgroup G) : Set G) = N) ∧
      D.T ⊓ (X ⊔ (N ⊓ centralizer (D.U : Set G))) ≤ centralizer (D.U : Set G) :=
    fun N hN hNM => exists_hX_of_inputN D Ch hin h1930 h204 h208 h2010 hCh c hN hNM
  have hUZ : D.U = D.Z := Data.U_eq_Z_of_familyControlsFusion D hfus hcyc hX
  refine ⟨hUZ, ?_, ?_⟩
  · exact ((CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).1.trans inf_le_left).trans (CFSG.openPCoreOf_le 2 D.M)
  · exact (Data.normalizer_U_eq D).ge

end CFSG.LocalAnalysis.UniquenessCase.UC22
