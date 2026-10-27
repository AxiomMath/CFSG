module

public import CFSG.Quasithin.Background.SmithB42G2TenProd
public import CFSG.Quasithin.Background.SmithB42G2IdRoots
public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.Quasithin.Vol2.Ch11G2Q8Borel
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.B42G2Id
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

section Weyl

variable {F : Type} [Field F] [CharP F 2]

@[expose] def sl3C : SL3 F :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [det_fin_three]⟩

@[expose] def sl3S : SL3 F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [det_fin_three, CharTwo.neg_eq]⟩

@[expose] def nW : ↥(cayleyGroup F) := g2Sw * g2A sl3C

@[expose] def wS0 : ↥(cayleyGroup F) := g2Y ![0, 1, 0] * g2X ![0, 1, 0] * g2Y ![0, 1, 0]

@[expose] def wL0 : ↥(cayleyGroup F) := g2A sl3S

theorem g2Act_g2Sw_q6 (a b c d e f : F) :
    g2Act (g2Sw : ↥(cayleyGroup F)) (q6 a b c d e f) = q6 d e f a b c := by
  rw [g2Act_g2Sw]
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem g2Act_sl3C (a b c d e f : F) :
    g2Act (g2A (sl3C : SL3 F)) (q6 a b c d e f) = q6 b c a e f d := by
  rw [g2Act_g2A]
  simp [sl3C, adjugate_fin_three]

theorem g2Act_sl3S (a b c d e f : F) :
    g2Act (g2A (sl3S : SL3 F)) (q6 a b c d e f) = q6 a c b d f e := by
  rw [g2Act_g2A]
  simp [sl3S, adjugate_fin_three, CharTwo.neg_eq]

theorem g2Act_nW (a b c d e f : F) :
    g2Act (nW : ↥(cayleyGroup F)) (q6 a b c d e f) = q6 e f d b c a := by
  rw [nW, g2Act_mul_apply', g2Act_sl3C, g2Act_g2Sw_q6]

local macro "cayley_q" : tactic => `(tactic| (
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  simp only [g2Act_mul_apply', g2Act_nW, g2Act_g2Sw_q6, g2Act_sl3C, g2Act_sl3S, g2Act_sl3P,
    g2Act_gW, g2Act_x0q, g2Act_x1q, g2Act_y1q, g2Act_y2q, g2Act_tv02, g2Act_tv12, g2Act_tv10,
    g2Act_uSL_q6, wS0, wL0, zW, zPos] <;>
  apply q6_congr <;> ring_nf <;> reduce_mod_char!))

theorem nW_mul_y1 (t : F) : nW * g2Y ![0, t, 0] = zPos 0 t * nW := by cayley_q

theorem nW_mul_uSL01 (t : F) : nW * g2A (uSL t 0 0) = zPos 1 t * nW := by cayley_q

theorem nW_mul_x0 (t : F) : nW * g2X ![t, 0, 0] = zPos 2 t * nW := by cayley_q

theorem nW_mul_uSL02 (t : F) : nW * g2A (uSL 0 t 0) = zPos 3 t * nW := by cayley_q

theorem nW_mul_y2 (t : F) : nW * g2Y ![0, 0, t] = zPos 4 t * nW := by cayley_q

theorem nW_mul_uSL12 (t : F) : nW * g2A (uSL 0 0 t) = zPos 5 t * nW := by cayley_q

theorem nW_mul_wS0 : nW * wS0 = zW F 1 * nW := by cayley_q

theorem nW_mul_wL0 : nW * wL0 = zW F 0 * nW := by cayley_q

theorem g2T_mul_nW (s : Fˣ × Fˣ) :
    g2T s * nW = nW * g2T (s.1 * s.2, s.1⁻¹) := by
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  have h2 : (s.2 : F) ≠ 0 := s.2.ne_zero
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  simp only [g2Act_mul_apply', g2Act_nW, g2Act_g2T, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2,
    q6_apply_inr0, q6_apply_inr1, q6_apply_inr2, Units.val_mul, Units.val_inv_eq_inv_val]
  apply q6_congr <;> field_simp

abbrev Uz (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) :=
  Subgroup.closure (⋃ j, Set.range (zPos (F := F) j))

theorem zPos_eq_conj (j : Fin 6) (t : F) :
    ∃ u ∈ U0 F, zPos j t = nW * u * nW⁻¹ := by
  fin_cases j
  · exact ⟨_, g2Y_mem_U0 t 0, by rw [nW_mul_y1, mul_inv_cancel_right]; rfl⟩
  · exact ⟨_, g2A_mem_U0 t 0 0, by rw [nW_mul_uSL01, mul_inv_cancel_right]; rfl⟩
  · exact ⟨_, g2X_mem_U0 t, by rw [nW_mul_x0, mul_inv_cancel_right]; rfl⟩
  · exact ⟨_, g2A_mem_U0 0 t 0, by rw [nW_mul_uSL02, mul_inv_cancel_right]; rfl⟩
  · exact ⟨_, g2Y_mem_U0 0 t, by rw [nW_mul_y2, mul_inv_cancel_right]; rfl⟩
  · exact ⟨_, g2A_mem_U0 0 0 t, by rw [nW_mul_uSL12, mul_inv_cancel_right]; rfl⟩

theorem closure_zPos_eq [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Uz F = (U0 F).map (MulAut.conj (nW : ↥(cayleyGroup F))).toMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, rfl⟩, t, rfl⟩
    obtain ⟨u, hu, e⟩ := zPos_eq_conj j t
    exact ⟨u, hu, by rw [e]; rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨⟨t₁, t₂, t₃, t₄, t₅, t₆⟩, ht⟩ := (uCU_bijective hF).2 ⟨u, hu⟩
    have hu' : u = uC t₁ t₂ t₃ t₄ t₅ t₆ := (congrArg Subtype.val ht).symm
    have mem : ∀ (j : Fin 6) (t : F), zPos j t ∈ Uz F := fun j t =>
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨j, t, rfl⟩)
    have e : (MulAut.conj (nW : ↥(cayleyGroup F))).toMonoidHom u =
        zPos 0 t₁ * zPos 1 t₂ * zPos 2 t₃ * zPos 3 t₄ * zPos 4 t₅ * zPos 5 t₆ := by
      rw [hu', uC]
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulAut.conj_apply]
      rw [nW_mul_y1, nW_mul_uSL01, nW_mul_x0, nW_mul_uSL02, nW_mul_y2, nW_mul_uSL12]
      simp only [mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mem 0 t₁) (mem 1 t₂)) (mem 2 t₃))
      (mem 3 t₄)) (mem 4 t₅)) (mem 5 t₆)

end Weyl

section Fixed

variable {k : Type} [Field k]

theorem fixedSub_map_conj {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (n : G) (P : Subgroup G) :
    fixedSub ρ (P.map (MulAut.conj n).toMonoidHom) = (fixedSub ρ P).map (ρ n) := by
  ext w
  constructor
  · intro hw
    refine ⟨ρ n⁻¹ w, fun u hu => ?_, ?_⟩
    · have h := hw (n * u * n⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩
      calc ρ u (ρ n⁻¹ w) = ρ n⁻¹ (ρ (n * u * n⁻¹) w) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 2
            group
        _ = ρ n⁻¹ w := by rw [h]
    · show ρ n (ρ n⁻¹ w) = w
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rintro ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
    change ρ (n * u * n⁻¹) (ρ n v) = ρ n v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
      hv u hu]

theorem fixSub_eq_fixedSub {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (S : Subgroup G) : SmithCurtis.fixSub ρ S = fixedSub ρ S :=
  Submodule.ext fun _ => Iff.rfl

end Fixed

section Transport

variable (F : Type) [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]
  {f : ℕ}

@[expose] def tHwZ (lab : Fin f → G2L) : TIdx lab → k :=
  (tRep F k lab nW).mulVec (tHw F k lab)

theorem fixSub_zPos_tRep [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    SmithCurtis.fixSub (matRep (tRep F k lab)) (Uz F) = Submodule.span k {tHwZ F k lab} := by
  have hn : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  rw [fixSub_eq_fixedSub, closure_zPos_eq hn, fixedSub_map_conj,
    (tRep_fixed_irreducible F k hF lab).1, Submodule.map_span, Set.image_singleton]
  rfl

theorem isSimpleRep_tRep [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) :
    SmithCurtis.IsSimpleRep (matRep (tRep F k lab)) :=
  (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp (tRep_fixed_irreducible F k hF lab).2

theorem tHwZ_ne_zero (lab : Fin f → G2L) : tHwZ F k lab ≠ 0 := by
  intro h
  apply tHw_ne_zero F k lab
  have e : (tRep F k lab nW⁻¹).mulVec (tHwZ F k lab) = tHw F k lab := by
    rw [tHwZ, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  rw [← e, h, Matrix.mulVec_zero]

end Transport

section RankOne

variable {F : Type} [Field F] [CharP F 2]

@[expose] def xS0 : Fin 2 → F → ↥(cayleyGroup F)
  | 0, c => g2A (uSL 0 0 c)
  | 1, c => g2Y ![0, c, 0]

@[expose] def wN0 : Fin 2 → ↥(cayleyGroup F)
  | 0 => wL0
  | 1 => wS0

theorem single_zero_eq_hexRoot : (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) =
    CFSG.Timmesfeld.RankTwo.hexRoot 5 := by
  funext k
  fin_cases k <;> decide

theorem single_one_eq_hexRoot : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
    CFSG.Timmesfeld.RankTwo.hexRoot 0 := by
  funext k
  fin_cases k <;> decide

theorem zPsi_single (i : Fin 2) (c : F) :
    zPsi (Pi.single i 1) c = if i = 0 then zPos 5 c else zPos 0 c := by
  fin_cases i
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, single_zero_eq_hexRoot, zPsi_pos]
    rfl
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, single_one_eq_hexRoot, zPsi_pos]
    rfl

theorem zPsi_neg_single (i : Fin 2) (c : F) :
    zPsi (-Pi.single i 1) c = if i = 0 then zNeg 5 c else zNeg 0 c := by
  fin_cases i
  · rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, single_zero_eq_hexRoot, zPsi_neg]
    rfl
  · rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, single_one_eq_hexRoot, zPsi_neg]
    rfl

theorem nW_mul_hecke (i : Fin 2) (c : F) :
    nW * (xS0 i c * wN0 i) = zPsi (Pi.single i 1) c * zW F i * nW := by
  rw [zPsi_single]
  fin_cases i
  · change nW * (g2A (uSL 0 0 c) * wL0) = zPos 5 c * zW F 0 * nW
    rw [← mul_assoc, nW_mul_uSL12, mul_assoc, nW_mul_wL0, mul_assoc]
  · change nW * (g2Y ![0, c, 0] * wS0) = zPos 0 c * zW F 1 * nW
    rw [← mul_assoc, nW_mul_y1, mul_assoc, nW_mul_wS0, mul_assoc]

theorem g2Act_x1w (c : F) : g2Act (xS0 1 c * wN0 1) (q6 1 0 0 0 0 0) = q6 c 0 0 0 0 1 ∧
    g2Act (xS0 1 c * wN0 1) (q6 0 0 0 0 0 1) = q6 1 0 0 0 0 0 := by
  constructor <;>
  · simp only [xS0, wN0, wS0, g2Act_mul_apply', g2Act_y1q, g2Act_x1q]
    apply q6_congr <;> ring_nf <;> reduce_mod_char!

theorem g2Act_x0w (c : F) : g2Act (xS0 0 c * wN0 0) (q6 1 0 0 0 0 0) = q6 1 0 0 0 0 0 ∧
    g2Act (xS0 0 c * wN0 0) (q6 0 0 0 0 0 1) = q6 0 0 0 0 1 c := by
  constructor <;>
  · simp only [xS0, wN0, wL0, g2Act_mul_apply', g2Act_sl3S, g2Act_uSL_q6]
    apply q6_congr <;> ring_nf

omit [CharP F 2] in
theorem single_u0 : (Pi.single (.inl 0) (1 : F) : Ix3 → F) = q6 1 0 0 0 0 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

omit [CharP F 2] in
theorem single_v2 : (Pi.single (.inr 2) (1 : F) : Ix3 → F) = q6 0 0 0 0 0 1 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

end RankOne

section HeckeData

variable {F : Type} [Field F] [CharP F 2]

theorem hecke_Q0 (c : F) :
    (repQ (xS0 0 c * wN0 0)).mulVec (Pi.single (.inl 0) 1) = Pi.single (.inl 0) (1 : F) := by
  rw [repQ_mulVec, single_u0, (g2Act_x0w c).1]

theorem hecke_Q1 (c : F) :
    (repQ (xS0 1 c * wN0 1)).mulVec (Pi.single (.inl 0) 1) =
      c • Pi.single (.inl 0) (1 : F) + Pi.single (.inr 2) 1 := by
  rw [repQ_mulVec, single_u0, (g2Act_x1w c).1, single_v2, q6_smul, q6_add]
  apply q6_congr <;> ring

theorem hecke_L0 (c : F) :
    (repLie (xS0 0 c * wN0 0)).mulVec (Pi.single hwL 1) =
      c • Pi.single hwL (1 : F) + Pi.single (3 : LIdx) 1 := by
  funext p
  rw [repLie_single_hwL]
  simp only [repQ_apply, single_u0, single_v2, (g2Act_x0w c).1, (g2Act_x0w c).2]
  fin_cases p <;> simp [lP, hwL, q6]

theorem hecke_L1 (c : F) :
    (repLie (xS0 1 c * wN0 1)).mulVec (Pi.single hwL 1) = Pi.single hwL (1 : F) := by
  funext p
  rw [repLie_single_hwL]
  simp only [repQ_apply, single_u0, single_v2, (g2Act_x1w c).1, (g2Act_x1w c).2]
  fin_cases p <;> simp [lP, hwL, q6]

@[expose] def heckeS0 : SIdx → F :=
  fun π => (if π.1.1 = .inl 0 then 1 else 0) * (if π.1.2 = (3 : LIdx) then 1 else 0)

@[expose] def heckeS1 : SIdx → F :=
  fun π => (if π.1.1 = .inr 2 then 1 else 0) * (if π.1.2 = hwL then 1 else 0)

omit [CharP F 2] in
theorem single_hwS_apply (π : SIdx) :
    (Pi.single hwS (1 : F) : SIdx → F) π =
      (if π.1.1 = .inl 0 then 1 else 0) * (if π.1.2 = hwL then 1 else 0) := by
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  by_cases ha : a = .inl 0 <;> by_cases hp : p = hwL
  · subst ha hp
    simp [hwS]
  · simp [hwS, hp]
  · simp [hwS, ha]
  · simp [hwS, ha]

theorem hecke_S0 (c : F) :
    (repSt (xS0 0 c * wN0 0)).mulVec (Pi.single hwS 1) = c • Pi.single hwS (1 : F) + heckeS0 := by
  funext π
  rw [repSt_hwS, hecke_L0, repQ_apply, single_u0, (g2Act_x0w c).1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_hwS_apply, heckeS0]
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  simp only [Pi.single_apply]
  rcases a with a | a <;> fin_cases a <;> simp [q6]

theorem hecke_S1 (c : F) :
    (repSt (xS0 1 c * wN0 1)).mulVec (Pi.single hwS 1) = c • Pi.single hwS (1 : F) + heckeS1 := by
  funext π
  rw [repSt_hwS, hecke_L1, repQ_apply, single_u0, (g2Act_x1w c).1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_hwS_apply, heckeS1]
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  simp only [Pi.single_apply]
  rcases a with a | a <;> fin_cases a <;> simp [q6]

end HeckeData

namespace G2L

variable {F : Type} [Field F] [CharP F 2]

@[expose] def roots : G2L → Finset (Fin 2)
  | one => ∅
  | nat => {1}
  | lie => {0}
  | st => Finset.univ

theorem rep_hecke (l : G2L) (i : Fin 2) : ∃ C : l.idx → F, ∀ c : F,
    (l.rep (xS0 i c * wN0 i)).mulVec l.hw = c • (if i ∈ l.roots then l.hw else 0) + C := by
  cases l
  · refine ⟨fun _ => (1 : F), fun c => ?_⟩
    rw [ite_eq_right (show i ∉ G2L.one.roots from Finset.notMem_empty i), smul_zero, zero_add]
    exact Matrix.one_mulVec _
  · fin_cases i
    · refine ⟨Pi.single (.inl 0) 1, fun c => ?_⟩
      rw [ite_eq_right (by decide), smul_zero, zero_add]
      exact hecke_Q0 c
    · refine ⟨Pi.single (.inr 2) 1, fun c => ?_⟩
      rw [ite_eq_left (by decide)]
      exact hecke_Q1 c
  · fin_cases i
    · refine ⟨Pi.single (3 : LIdx) 1, fun c => ?_⟩
      rw [ite_eq_left (by decide)]
      exact hecke_L0 c
    · refine ⟨Pi.single hwL 1, fun c => ?_⟩
      rw [ite_eq_right (by decide), smul_zero, zero_add]
      exact hecke_L1 c
  · fin_cases i
    · refine ⟨heckeS0, fun c => ?_⟩
      rw [ite_eq_left (by decide)]
      exact hecke_S0 c
    · refine ⟨heckeS1, fun c => ?_⟩
      rw [ite_eq_left (by decide)]
      exact hecke_S1 c

end G2L

section Hecke

variable (F : Type) [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]
  {f : ℕ}

omit [CharP F 2] [Algebra F k] [CharP k 2] in
theorem sum_two_pow_fin (f : ℕ) : ∑ i : Fin f, 2 ^ (i : ℕ) = 2 ^ f - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) f, Nat.geomSum_eq (le_refl 2)]
  simp

omit [CharP F 2] in
theorem sum_prod_frK_affine [Fintype F] (hF : Fintype.card F = 2 ^ f) (a b : Fin f → k) :
    ∑ c : F, ∏ j : Fin f, (frK k (j : ℕ) c * a j + b j) = ∏ j, a j := by
  classical
  have hpow : ∀ (t : Finset (Fin f)) (c : F),
      ∏ j ∈ t, frK k (j : ℕ) c = algebraMap F k (c ^ ∑ j ∈ t, 2 ^ (j : ℕ)) := fun t c => by
    simp only [frK_apply, map_pow]
    exact Finset.prod_pow_eq_pow_sum t _ _
  simp_rw [Finset.prod_add]
  rw [Finset.sum_comm, Finset.sum_eq_single Finset.univ]
  · simp only [Finset.sdiff_self, Finset.prod_empty, mul_one, Finset.prod_mul_distrib]
    rw [← Finset.sum_mul]
    simp_rw [hpow]
    rw [← map_sum, sum_two_pow_fin, ← hF, CFSG.QuasithinUnique.Setup.X7a.sum_pow_card_sub_one F,
      map_neg, map_one, CharTwo.neg_eq, one_mul]
  · intro t _ ht
    simp only [Finset.prod_mul_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    simp_rw [hpow]
    have hlt : ∑ j ∈ t, 2 ^ (j : ℕ) < Fintype.card F - 1 := by
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ t := by
        by_contra hc
        push Not at hc
        exact ht (Finset.eq_univ_of_forall hc)
      rw [hF, ← sum_two_pow_fin]
      exact Finset.sum_lt_sum_of_subset (Finset.subset_univ t) (Finset.mem_univ j₀) hj₀
        (by positivity) fun _ _ _ => Nat.zero_le _
    rw [← map_sum, FiniteField.sum_pow_lt_card_sub_one F _ hlt, map_zero, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) h

omit [CharP F 2] in
theorem frK_affine (j : ℕ) (c : F) (x y : F) :
    frK k j (c * x + y) = frK k j c * frK k j x + frK k j y := by
  rw [map_add, map_mul]

theorem hecke_tRep_U0 [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L)
    (i : Fin 2) :
    ∑ c : F, (tRep F k lab (xS0 i c * wN0 i)).mulVec (tHw F k lab) =
      (if ∀ j, i ∈ (lab j).roots then (1 : k) else 0) • tHw F k lab := by
  classical
  choose C hC using fun j => G2L.rep_hecke (F := F) (lab j) i
  funext x
  rw [Finset.sum_apply]
  have e : ∀ c : F, (tRep F k lab (xS0 i c * wN0 i)).mulVec (tHw F k lab) x =
      ∏ j : Fin f, (frK k (j : ℕ) c *
        frK k (j : ℕ) ((if i ∈ (lab j).roots then (lab j).hw else 0) (x j)) +
        frK k (j : ℕ) (C j (x j))) := fun c => by
    unfold tHw
    rw [tRep_mulVec_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hC j c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, frK_affine]
  simp_rw [e]
  rw [sum_prod_frK_affine F k hF]
  by_cases hall : ∀ j, i ∈ (lab j).roots
  · rw [ite_eq_left hall, one_smul]
    unfold tHw
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ite_eq_left (hall j)]
  · rw [ite_eq_right hall, zero_smul, Pi.zero_apply]
    push Not at hall
    obtain ⟨j₀, hj₀⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ j₀)
      (by rw [ite_eq_right hj₀, Pi.zero_apply, map_zero])

theorem hecke_tRep [Fintype F] (hF : Fintype.card F = 2 ^ f) (lab : Fin f → G2L) (i : Fin 2) :
    ∑ c : F, matRep (tRep F k lab) (zPsi (Pi.single i 1) c * zW F i) (tHwZ F k lab) =
      (if ∀ j, i ∈ (lab j).roots then (1 : k) else 0) • tHwZ F k lab := by
  have e : ∀ c : F, matRep (tRep F k lab) (zPsi (Pi.single i 1) c * zW F i) (tHwZ F k lab) =
      (tRep F k lab nW).mulVec ((tRep F k lab (xS0 i c * wN0 i)).mulVec (tHw F k lab)) :=
    fun c => by
      rw [matRep_apply, tHwZ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
        nW_mul_hecke]
  simp_rw [e]
  rw [← Matrix.mulVec_sum, hecke_tRep_U0 F k hF lab i, Matrix.mulVec_smul]
  rfl

end Hecke

section TorusData

variable {F : Type} [Field F] [CharP F 2]

theorem g2Act_g2T_u0 (s : Fˣ × Fˣ) :
    g2Act (g2T s) (q6 1 0 0 0 0 0) = q6 (s.1 : F) 0 0 0 0 0 := by
  rw [g2Act_g2T]
  apply q6_congr <;> simp [q6]

theorem g2Act_g2T_v2 (s : Fˣ × Fˣ) :
    g2Act (g2T s) (q6 0 0 0 0 0 1) = q6 0 0 0 0 0 ((s.1 : F) * s.2) := by
  rw [g2Act_g2T]
  apply q6_congr <;> simp [q6]

theorem torus_Q (s : Fˣ × Fˣ) :
    (repQ (g2T s)).mulVec (Pi.single (.inl 0) 1) = (s.1 : F) • Pi.single (.inl 0) (1 : F) := by
  rw [repQ_mulVec, single_u0, g2Act_g2T_u0, q6_smul]
  apply q6_congr <;> ring

theorem torus_L (s : Fˣ × Fˣ) :
    (repLie (g2T s)).mulVec (Pi.single hwL 1) =
      ((s.1 : F) ^ 2 * s.2) • Pi.single hwL (1 : F) := by
  funext p
  rw [repLie_single_hwL]
  simp only [repQ_apply, single_u0, single_v2, g2Act_g2T_u0, g2Act_g2T_v2]
  fin_cases p <;> simp [lP, hwL, q6]
  ring

theorem torus_S (s : Fˣ × Fˣ) :
    (repSt (g2T s)).mulVec (Pi.single hwS 1) =
      ((s.1 : F) ^ 3 * s.2) • Pi.single hwS (1 : F) := by
  funext π
  rw [repSt_hwS, torus_L, repQ_apply, single_u0, g2Act_g2T_u0, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, single_hwS_apply]
  obtain ⟨⟨a, p⟩, hπ⟩ := π
  simp only [Pi.single_apply]
  rcases a with a | a <;> fin_cases a <;> simp [q6]
  congr 1
  ring

end TorusData

namespace G2L

variable {F : Type} [Field F] [CharP F 2]

@[expose] def chi0 : G2L → Fˣ × Fˣ → F
  | one => fun _ => 1
  | nat => fun s => s.1
  | lie => fun s => (s.1 : F) ^ 2 * s.2
  | st => fun s => (s.1 : F) ^ 3 * s.2

@[expose] def chiZ : G2L → Fˣ × Fˣ → F
  | one => fun _ => 1
  | nat => fun s => (s.1 : F) * s.2
  | lie => fun s => (s.1 : F) * s.2 ^ 2
  | st => fun s => (s.1 : F) ^ 2 * s.2 ^ 3

theorem rep_g2T_hw (l : G2L) (s : Fˣ × Fˣ) :
    (l.rep (g2T s)).mulVec l.hw = l.chi0 s • l.hw := by
  cases l
  · funext x
    change (1 : Matrix Unit Unit F).mulVec (fun _ => (1 : F)) x = (1 : F) • (1 : F)
    rw [Matrix.one_mulVec, smul_eq_mul, mul_one]
  · exact torus_Q s
  · exact torus_L s
  · exact torus_S s

omit [CharP F 2] in
theorem chi0_twist (l : G2L) (s : Fˣ × Fˣ) : l.chi0 (s.1 * s.2, s.1⁻¹) = l.chiZ s := by
  have h1 : (s.1 : F) ≠ 0 := s.1.ne_zero
  cases l <;> simp only [chi0, chiZ, Units.val_mul, Units.val_inv_eq_inv_val] <;> field_simp

end G2L

section Torus

variable (F : Type) [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]
  {f : ℕ}

theorem torus_tRep (lab : Fin f → G2L) (s : Fˣ × Fˣ) :
    matRep (tRep F k lab) (g2T s) (tHwZ F k lab) =
      (∏ j : Fin f, frK k (j : ℕ) ((lab j).chiZ s)) • tHwZ F k lab := by
  rw [matRep_apply, tHwZ, Matrix.mulVec_mulVec, ← map_mul, g2T_mul_nW, map_mul,
    ← Matrix.mulVec_mulVec]
  have e : (tRep F k lab (g2T (s.1 * s.2, s.1⁻¹))).mulVec (tHw F k lab) =
      (∏ j : Fin f, frK k (j : ℕ) ((lab j).chiZ s)) • tHw F k lab := by
    unfold tHw
    rw [tRep_mulVec_prod]
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [G2L.rep_g2T_hw, Pi.smul_apply, smul_eq_mul, map_mul, G2L.chi0_twist]
  rw [e, Matrix.mulVec_smul]

end Torus

section RankOneTorus

variable {F : Type} [Field F] [CharP F 2]

theorem zD_eq (i : Fin 2) (t : Fˣ) :
    zPsi (-Pi.single i 1) ((t⁻¹ : Fˣ) : F) * zPsi (Pi.single i 1) (t : F) * zW F i *
      zPsi (Pi.single i 1) ((t⁻¹ : Fˣ) : F) =
        if i = 0 then g2T (t⁻¹, t) else g2T (t * t, t⁻¹) := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [zPsi_neg_single, zPsi_single, zPsi_single]
  fin_cases i
  · simp only [Fin.zero_eta, ite_true, zNeg, zPos, zW]
    refine cayley_ext_Q fun w => ?_
    rw [q6_eta w]
    simp only [g2Act_mul_apply', g2Act_tv01, g2Act_tv10, g2Act_sl3P, g2Act_g2T, q6_apply_inl0,
      q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2,
      Units.val_inv_eq_inv_val]
    apply q6_congr <;> field_simp <;> ring_nf <;> reduce_mod_char!
  · simp only [Fin.mk_one, one_ne_zero, ite_false, zNeg, zPos, zW]
    refine cayley_ext_Q fun w => ?_
    rw [q6_eta w]
    simp only [g2Act_mul_apply', g2Act_y0q, g2Act_x0q, g2Act_gW, g2Act_g2T, q6_apply_inl0,
      q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2,
      Units.val_inv_eq_inv_val, Units.val_mul]
    apply q6_congr <;> field_simp <;> ring_nf <;> reduce_mod_char!

theorem zD_eq' (i : Fin 2) (t : Fˣ) :
    zPsi (Pi.single i 1) (t : F) * zPsi (-Pi.single i 1) ((t⁻¹ : Fˣ) : F) *
      zPsi (Pi.single i 1) (t : F) * zW F i =
        if i = 0 then g2T (t⁻¹, t) else g2T (t * t, t⁻¹) := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [zPsi_neg_single, zPsi_single]
  fin_cases i
  · simp only [Fin.zero_eta, ite_true, zNeg, zPos, zW]
    refine cayley_ext_Q fun w => ?_
    rw [q6_eta w]
    simp only [g2Act_mul_apply', g2Act_tv01, g2Act_tv10, g2Act_sl3P, g2Act_g2T, q6_apply_inl0,
      q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2,
      Units.val_inv_eq_inv_val]
    apply q6_congr <;> field_simp <;> ring_nf <;> reduce_mod_char!
  · simp only [Fin.mk_one, one_ne_zero, ite_false, zNeg, zPos, zW]
    refine cayley_ext_Q fun w => ?_
    rw [q6_eta w]
    simp only [g2Act_mul_apply', g2Act_y0q, g2Act_x0q, g2Act_gW, g2Act_g2T, q6_apply_inl0,
      q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2,
      Units.val_inv_eq_inv_val, Units.val_mul]
    apply q6_congr <;> field_simp <;> ring_nf <;> reduce_mod_char!

end RankOneTorus

namespace G2L

variable {F : Type} [Field F]

omit [Field F] in
theorem chiZ_rankOne [Field F] [CharP F 2] (l : G2L) (i : Fin 2) (t : Fˣ) :
    l.chiZ (if i = 0 then (t⁻¹, t) else (t * t, t⁻¹)) = if i ∈ l.roots then (t : F) else 1 := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  fin_cases i <;> cases l <;> simp [chiZ, roots] <;> field_simp

end G2L

section RankOneTorusT

variable (F : Type) [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]
  {f : ℕ}

@[expose] def eExp (lab : Fin f → G2L) (i : Fin 2) : ℕ :=
  ∑ j : Fin f, if i ∈ (lab j).roots then 2 ^ (j : ℕ) else 0

omit [CharP F 2] in
theorem prod_frK_ite (lab : Fin f → G2L) (i : Fin 2) (t : F) :
    ∏ j : Fin f, frK k (j : ℕ) (if i ∈ (lab j).roots then t else 1) =
      algebraMap F k t ^ eExp lab i := by
  rw [eExp, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [frK_apply]

theorem rankOne_tRep (lab : Fin f → G2L) (i : Fin 2) (t : Fˣ) :
    matRep (tRep F k lab) (zPsi (-Pi.single i 1) ((t⁻¹ : Fˣ) : F) * zPsi (Pi.single i 1) (t : F) *
      zW F i * zPsi (Pi.single i 1) ((t⁻¹ : Fˣ) : F)) (tHwZ F k lab) =
        (algebraMap F k (t : F) ^ eExp lab i) • tHwZ F k lab := by
  rw [zD_eq]
  have e : ∀ s : Fˣ × Fˣ, (if i = 0 then g2T (t⁻¹, t) else g2T (t * t, t⁻¹)) =
      g2T (if i = 0 then (t⁻¹, t) else (t * t, t⁻¹)) := fun _ => by split_ifs <;> rfl
  rw [e 1, torus_tRep]
  congr 1
  simp_rw [G2L.chiZ_rankOne]
  exact prod_frK_ite F k lab i t

theorem rankOne_tRep' (lab : Fin f → G2L) (i : Fin 2) (t : Fˣ) :
    matRep (tRep F k lab) (zPsi (Pi.single i 1) (t : F) * zPsi (-Pi.single i 1) ((t⁻¹ : Fˣ) : F) *
      zPsi (Pi.single i 1) (t : F) * zW F i) (tHwZ F k lab) =
        (algebraMap F k (t : F) ^ eExp lab i) • tHwZ F k lab := by
  rw [zD_eq', ← zD_eq]
  exact rankOne_tRep F k lab i t

end RankOneTorusT

end CFSG.Quasithin.B42G2Ten
