module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomParabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3FourteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3FourteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSL3Thirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup
public import CFSG.Quasithin.EmptyFaithful.S153EB6C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup CFSG.Quasithin CFSG.Quasithin.Vol2
open CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)

private theorem mem_of_phiL_mem_map (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) {A : Subgroup G}
    (hA : CFSG.Open.pCoreOf 2 c.L ≤ A) (x : ↥c.L)
    (hx : c.phiL hV x ∈ (A.subgroupOf c.L).map (c.phiL hV)) : (x : G) ∈ A := by
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hx
  have hφ : c.phiL hV (p⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hpx, inv_mul_cancel]
  have hq : p⁻¹ * x ∈ (c.phiL hV).ker := MonoidHom.mem_ker.mpr hφ
  rw [hker] at hq
  have hcore : ((p⁻¹ * x : ↥c.L) : G) ∈ CFSG.Open.pCoreOf 2 c.L :=
    Subgroup.mem_map_of_mem c.L.subtype hq
  have hxeq : (x : G) = (p : G) * ((p⁻¹ * x : ↥c.L) : G) := by
    simp
  rw [hxeq]
  exact A.mul_mem (Subgroup.mem_subgroupOf.mp hp) (hA hcore)

private theorem T_le_normalizer_W_of_comm (hWT : ⁅c.W, D.T⁆ ≤ D.Z) :
    D.T ≤ Subgroup.normalizer (c.W : Set G) := by
  intro t ht
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hcomm : ⁅w⁻¹, t⁆ ∈ D.Z :=
    hWT (Subgroup.commutator_mem_commutator (c.W.inv_mem hw) ht)
  have hcommW : ⁅w⁻¹, t⁆ ∈ c.W := (uc22p22v_le_conjClosure c.X D.Z) hcomm
  have heq : t * w * t⁻¹ = w * ⁅w⁻¹, t⁆ := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact c.W.mul_mem hw hcommW

private theorem Z_ne_bot_of_sl3 (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z) : D.Z ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (Ctx23L.isElemAbelian_Z c.toCtx23L h4 h1930)
  have h1 : Nat.card D.Z = 1 := by rw [hbot]; simp
  rw [hcard] at h1
  exact (Nat.one_lt_two_pow (n := CFSG.Open.pRank 2 D.Z) (by omega)).ne' h1

private theorem conjSubgroup_Z_le_V' {k : G} (hk : k ∈ c.N) :
    CFSG.Quasithin.conjSubgroup D.Z k ≤ c.V := by
  unfold Ctx23L.V
  exact le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.N D.Z) => K) _
    ⟨k⁻¹, c.N.inv_mem hk, rfl⟩ le_rfl

private theorem conjSubgroup_Z_le_V_of_mem_L {k : G} (hk : k ∈ c.L) :
    CFSG.Quasithin.conjSubgroup D.Z k ≤ c.V :=
  conjSubgroup_Z_le_V' c ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
    (Ctx23L.sup_le_N D Ch c.toCtx23L) hk)

private theorem eq_one_of_mkTil_eq_one {V : Subgroup G} (hV : IsElemAbelian 2 V) (v : ↥V)
    (h : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV v) = 1) : (v : G) = 1 := by
  have h1 : (1 : Vtil (⊥ : Subgroup G) V hV) = mkTil (⊥ : Subgroup G) V hV 1 :=
    (map_one (mkTil (⊥ : Subgroup G) V hV)).symm
  rw [h1, mkTil_eq_iff (⊥ : Subgroup G) V hV (IntMod.mk hV v) 1] at h
  have h' := Subgroup.mem_bot.mp h
  rw [IntMod.val_one, inv_one, mul_one] at h'
  change (v : G) = (1 : G)
  simpa [IntMod.mk, IntMod.val] using h'

theorem exists_mem_conjSubgroup_L_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    ∀ v ∈ c.V, ∃ k ∈ c.L, v ∈ CFSG.Quasithin.conjSubgroup D.Z k := by
  intro v hv
  by_cases hv1 : v = 1
  · exact ⟨1, c.L.one_mem, by rw [hv1, CFSG.Quasithin.conjSubgroup_one]; exact D.Z.one_mem⟩
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_ne_bot_of_sl3 c h4 h1930 hm)
  obtain ⟨K, hfield, hfinite, hKcard, hreal⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  obtain ⟨π, hπ⟩ := hreal
  let qu : c.toCtx23L.W hV :=
    mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨(z : G), hZleV z.2⟩)
  let qw : c.toCtx23L.W hV :=
    mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩)
  have hu1 : qu ≠ 1 := by
    intro hq
    have h2 := eq_one_of_mkTil_eq_one (V := c.V) hV ⟨(z : G), hZleV z.2⟩
      (by simpa [qu] using hq)
    exact hz1 (Subtype.ext h2)
  have hw1 : qw ≠ 1 := by
    intro hq
    exact hv1 (eq_one_of_mkTil_eq_one (V := c.V) hV ⟨v, hv⟩ (by simpa [qw] using hq))
  obtain ⟨g, hg, hgu⟩ := KGNat.exists_apply_eq_of_linModel
    (KGNat.linModelNat (StatedSL 3 K))
    (fun x y hx hy => KGNat.exists_sl3_lin_eq x y hx hy) hπ qu qw hu1 hw1
  obtain ⟨x, hx⟩ := c.phiL_surjective hV ⟨g, hg⟩
  refine ⟨((x : G))⁻¹, c.L.inv_mem x.2, ?_⟩
  have hsmul : (c.phiL hV x : MulAut (c.toCtx23L.W hV)) qu = qw := by
    rw [hx]
    exact hgu
  exact mem_conjSubgroup_of_phiL_smul c.toCtx23L hV
    (v := IntMod.mk hV ⟨(z : G), hZleV z.2⟩) (w := v) z.2 hv
    (by simpa [qu, qw] using hsmul)

theorem card_V_eq_card_Z_pow_three_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    Nat.card c.V = Nat.card D.Z ^ 3 := by
  obtain ⟨K, hfield, hfinite, hKcard, hreal⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  have h1 : Nat.card (c.toCtx23L.W hV) = Nat.card K ^ 3 :=
    CFSG.Quasithin.S153EB6.card_of_realizes_nat 3 (c.H hV) hreal
  have h2 : Nat.card (c.toCtx23L.W hV) = Nat.card c.V := by
    rw [← PartTwo.card_IntMod c.V hV]
    exact (Nat.card_congr (TwelveShort.mkTilEquiv c.V hV).toEquiv).symm
  have h3 : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (Ctx23L.isElemAbelian_Z c.toCtx23L h4 h1930)
  rw [← h2, h1, hKcard, h3]

private theorem geom14_spec (h4 : S23_4 D Ch) (h1930 : H1930 D) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulDistribMulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
      MulAction.compHom (c.toCtx23L.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    (∀ Y : Subgroup ↥(c.H hV), (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Y → Y ≠ ⊤ →
      Y ≤ MulAction.stabilizer ↥(c.H hV) (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) :
        Set (c.toCtx23L.W hV))) ∨ Y ≤ c.Pstar hV) ∧
    (∀ h : ↥(c.H hV), (∀ w ∈ closure (⋃ p ∈ c.Pstar hV,
        p • (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))),
        (h : MulAut (c.toCtx23L.W hV)) w = w) → h ^ 2 = 1) ∧
    ∀ x₁ x₂ : ↥(c.H hV),
      (c.Ztil hV).map (x₁ : MulAut (c.toCtx23L.W hV)).toMonoidHom ≠
        (c.Ztil hV).map (x₂ : MulAut (c.toCtx23L.W hV)).toMonoidHom →
      ∃ y : ↥(c.H hV),
        (c.Ztil hV).map (x₁ : MulAut (c.toCtx23L.W hV)).toMonoidHom ⊔
          (c.Ztil hV).map (x₂ : MulAut (c.toCtx23L.W hV)).toMonoidHom =
          (closure (⋃ p ∈ c.Pstar hV,
            p • (((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) :
              Set (c.toCtx23L.W hV))))).map (y : MulAut (c.toCtx23L.W hV)).toMonoidHom := by
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) = c.Ztil hV :=
    fixedPointSubgroup_sylowStar_eq_Ztil_of_sl3 c.toCtx23L hV hm hSLH hnat
  have h := kSL3Geom14_holds (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hSLH hnat hm
    (c.sylowStar hV) (c.Pstar hV) (normalizer_sylowStar_le_Pstar c hV)
    (Pstar_isCoatom c hV hker) (Pstar_ne_stabilizer c hV h4 h1930 hm hSLH hnat)
  rw [hℓ] at h
  exact h

private theorem C0_le_normalizer_X (hV : IsElemAbelian 2 c.V)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    D.T ⊓ Subgroup.centralizer (c.V : Set G) ≤ Subgroup.normalizer (c.X : Set G) := by
  intro z hz
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rw [Subgroup.mem_inf] at hz
  have hxL : x ∈ c.L := c.hX.1.2.1 hx
  have hzL : z * x * z⁻¹ ∈ c.L :=
    Ctx23L.conj_mem c.toCtx23L ⟨z, hz.1⟩ ⟨x, hxL⟩
  have hcommL : ⁅z, x⁆ ∈ c.L := by
    have h := c.L.mul_mem hzL (c.L.inv_mem hxL)
    simpa [commutatorElement_def] using h
  have hxN : x ∈ Subgroup.normalizer (c.V : Set G) :=
    ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
      (Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L)) hxL
  have hconjC : x * z⁻¹ * x⁻¹ ∈ Subgroup.centralizer (c.V : Set G) :=
    uc22p21b_conj_mem_centralizer hxN (Subgroup.inv_mem _ hz.2)
  have hcommC : ⁅z, x⁆ ∈ Subgroup.centralizer (c.V : Set G) := by
    have h := (Subgroup.centralizer (c.V : Set G)).mul_mem hz.2 hconjC
    simpa [commutatorElement_def, mul_assoc] using h
  have hcommX : ⁅z, x⁆ ∈ c.X := by
    have hmem : ⁅z, x⁆ ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcommL, hcommC⟩
    rw [c.L_inf_centralizer_V_eq_of_ker hV hker] at hmem
    exact c.hX.1.1 hmem
  have heq : z * x * z⁻¹ = ⁅z, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact c.X.mul_mem hcommX hx

private theorem T_le_normalizer_X_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    D.T ≤ Subgroup.normalizer (c.X : Set G) := by
  intro t ht
  obtain ⟨y, hy, hz⟩ := Ctx23L.exists_mem_T_inf_L_mul_inv_mem_centralizer_of_sl3
    c.toCtx23L hV (by omega) hnat t ht
  have hzT : y⁻¹ * t ∈ D.T := D.T.mul_mem (D.T.inv_mem hy.1) ht
  have hyX : y ∈ c.X := c.hTX (Subgroup.mem_inf.mpr ⟨hy.1, hy.2⟩)
  have hC0 : y⁻¹ * t ∈ Subgroup.normalizer (c.X : Set G) :=
    C0_le_normalizer_X c hV hker ⟨hzT, hz⟩
  have heq : t = y * (y⁻¹ * t) := by group
  rw [heq]
  exact (Subgroup.normalizer (c.X : Set G)).mul_mem (Subgroup.le_normalizer hyX) hC0

private theorem sup_inf_centralizer_W_le (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    (c.X ⊔ D.T) ⊓ Subgroup.centralizer (c.W : Set G) ≤
      (c.X ⊓ Subgroup.centralizer (c.W : Set G)) ⊔
        (D.T ⊓ Subgroup.centralizer (c.V : Set G)) := by
  intro y hy
  rw [Subgroup.mem_inf] at hy
  set C0 : Subgroup G := D.T ⊓ Subgroup.centralizer (c.V : Set G) with hC0def
  have hT : D.T = (D.T ⊓ c.L) ⊔ C0 := by
    rw [hC0def]
    exact Ctx23L.T_eq_sup_inf_centralizer_of_sl3 c.toCtx23L hV (by omega) hnat
  have hXT : c.X ⊔ D.T = c.X ⊔ C0 := by
    conv_lhs => rw [hT]
    rw [← sup_assoc, sup_eq_left.mpr c.hTX]
  rw [hXT] at hy
  have hC1 : D.T ≤ Subgroup.normalizer (c.X : Set G) :=
    T_le_normalizer_X_of_sl3 c h4 h1930 hV hm hnat hker
  have hC0N : C0 ≤ Subgroup.normalizer (c.X : Set G) := hC0def ▸ (inf_le_left.trans hC1)
  have hprod : y ∈ (c.X : Set G) * (C0 : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left c.X C0 hC0N]
    exact hy.1
  rcases hprod with ⟨x, hxX, z, hzC0, rfl⟩
  have hzW : z ∈ Subgroup.centralizer (c.W : Set G) :=
    Subgroup.centralizer_le (Ctx2311.W_le_V c) hzC0.2
  have hxW : x ∈ Subgroup.centralizer (c.W : Set G) := by
    have h := (Subgroup.centralizer (c.W : Set G)).mul_mem hy.2 (Subgroup.inv_mem _ hzW)
    rwa [mul_inv_cancel_right] at h
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hxX, hxW⟩) (hC0def ▸ hzC0)

private theorem phiL_fixes_line (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (yL : ↥c.L) (hyW : (yL : G) ∈ Subgroup.centralizer (c.W : Set G)) :
    ∀ w ∈ closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))),
      (c.phiL hV yL : MulAut (c.toCtx23L.W hV)) w = w := by
  intro w hw
  have hπ : closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) =
      imgTil (⊥ : Subgroup G) c.V hV c.W :=
    le_antisymm (line_le_imgTil_W c hV hm hSLH hnat) (imgTil_W_le_line c hV hm hSLH hnat)
  rw [hπ] at hw
  obtain ⟨v, hvW, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV c.W w).1 hw
  rw [Ctx23L.phiL_apply_mkTil c.toCtx23L hV yL v]
  congr 1
  apply IntMod.val_injective
  rw [actStab_apply_val]
  have hcomm : v.val * (yL : G) = (yL : G) * v.val :=
    Subgroup.mem_centralizer_iff.mp hyW v.val hvW
  calc (yL : G) * v.val * (yL : G)⁻¹ = v.val * (yL : G) * (yL : G)⁻¹ := by rw [← hcomm]
    _ = v.val := by group

private theorem isPGroup_X_inf_centralizer_W (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    IsPGroup 2 ↥(c.X ⊓ Subgroup.centralizer (c.W : Set G)) := by
  have hspec := geom14_spec c h4 h1930 hV hm hSLH hnat hker
  rw [isPGroup_iff_exists_pow_pow_eq_one]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
  refine ⟨n + 1, ?_⟩
  intro y
  let yL : ↥c.L := ⟨(y : G), c.hX.1.2.1 y.2.1⟩
  have hfix := phiL_fixes_line c hV hm hSLH hnat yL y.2.2
  have hsq : c.phiL hV yL ^ 2 = 1 := hspec.2.1 (c.phiL hV yL) hfix
  have hy2 : yL ^ 2 ∈ CFSG.pCore 2 ↥c.L := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hsq]
  have hz : (yL ^ 2) ^ (2 ^ n) = 1 := by
    have hdvd : orderOf (⟨yL ^ 2, hy2⟩ : ↥(CFSG.pCore 2 ↥c.L)) ∣ 2 ^ n := by
      rw [← hn]
      exact orderOf_dvd_natCard _
    have h := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val h
  have hpow : yL ^ (2 ^ (n + 1)) = 1 := by
    have htwo : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
    rw [htwo, pow_mul, hz]
  exact Subtype.ext (by simpa using congrArg Subtype.val hpow)

theorem T_inf_centralizer_W_le_pCoreOf_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    D.T ⊓ Subgroup.centralizer (c.W : Set G) ≤ CFSG.Open.pCoreOf 2 (c.X ⊔ D.T) := by
  have hWT : ⁅c.W, D.T⁆ ≤ D.Z :=
    commutator_W_T_le_Z_of_sl3 c h4 h1930 hV hm hSLH hnat kSL3Line_holds hker
  have hN : c.X ⊔ D.T ≤ Subgroup.normalizer (c.W : Set G) :=
    sup_le (uc22p22v_le_normalizer_conjClosure c.X D.Z) (T_le_normalizer_W_of_comm c hWT)
  let B : Subgroup G := (c.X ⊔ D.T) ⊓ Subgroup.centralizer (c.W : Set G)
  have hBn : c.X ⊔ D.T ≤ Subgroup.normalizer (B : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    change b ∈ (c.X ⊔ D.T) ⊓ Subgroup.centralizer (c.W : Set G) at hb
    rw [Subgroup.mem_inf] at hb
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) b).1 hb.1,
        uc22p21b_conj_mem_centralizer (hN hg) hb.2⟩
  have hC0N : D.T ⊓ Subgroup.centralizer (c.V : Set G) ≤
      Subgroup.normalizer ((c.X ⊓ Subgroup.centralizer (c.W : Set G)) : Set G) := by
    intro z hz
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [Subgroup.mem_inf] at hz
    change x ∈ (c.X ⊓ Subgroup.centralizer (c.W : Set G) : Subgroup G) at hx
    rw [Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (C0_le_normalizer_X c hV hker hz) x).1 hx.1, ?_⟩
    have hzW : z ∈ Subgroup.centralizer (c.W : Set G) :=
      Subgroup.centralizer_le (Ctx2311.W_le_V c) hz.2
    exact uc22p21b_conj_mem_centralizer
      (Subgroup.centralizer_le_normalizer (c.W : Set G) hzW) hx.2
  have hB2 : IsPGroup 2 B :=
    (IsPGroup.to_sup_of_normal_left'
      (isPGroup_X_inf_centralizer_W c h4 h1930 hV hm hSLH hnat hker)
      (D.sylowM.isPGroup.to_le inf_le_left) hC0N).to_le
      (sup_inf_centralizer_W_le c h4 h1930 hV hm hnat hker)
  exact (le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans
    (le_pCoreOf_of_le_normalizer inf_le_left hBn hB2)

private theorem imgTil_map_conj {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (x : ↥c.L) {A : Subgroup G} (hA : A ≤ c.V) :
    imgTil (⊥ : Subgroup G) c.V hV (A.map (MulAut.conj (x : G)).toMonoidHom) =
      (imgTil (⊥ : Subgroup G) c.V hV A).map
        (c.phiL hV x : MulAut (c.W hV)).toMonoidHom := by
  ext q
  rw [mem_imgTil, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨a', ha', hval⟩ := Subgroup.mem_map.1 ha
    refine ⟨mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨a', hA ha'⟩), ?_, ?_⟩
    · exact (mem_imgTil (⊥ : Subgroup G) c.V hV A _).2
        ⟨IntMod.mk hV ⟨a', hA ha'⟩, ha', rfl⟩
    · refine (Ctx23L.phiL_apply_mkTil c hV x (IntMod.mk hV ⟨a', hA ha'⟩)).trans ?_
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      simpa [MulAut.conj_apply, IntMod.mk, IntMod.val] using hval
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a', ha', rfl⟩ := (mem_imgTil (⊥ : Subgroup G) c.V hV A y).1 hy
    refine (mem_imgTil (⊥ : Subgroup G) c.V hV
      (A.map (MulAut.conj (x : G)).toMonoidHom) _).2
      ⟨actStab (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩ a', ?_, ?_⟩
    · rw [actStab_apply_val]
      exact Subgroup.mem_map_of_mem (MulAut.conj (x : G)).toMonoidHom ha'
    · exact (Ctx23L.phiL_apply_mkTil c hV x a').symm

private theorem le_of_imgTil_le (V : Subgroup G) (hV : IsElemAbelian 2 V) {U U' : Subgroup G}
    (hU : U ≤ V) (h : imgTil (⊥ : Subgroup G) V hV U ≤ imgTil (⊥ : Subgroup G) V hV U') :
    U ≤ U' := by
  intro u hu
  have hmem : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨u, hU hu⟩) ∈
      imgTil (⊥ : Subgroup G) V hV U :=
    (mem_imgTil (⊥ : Subgroup G) V hV U _).2 ⟨IntMod.mk hV ⟨u, hU hu⟩, hu, rfl⟩
  obtain ⟨x, hx, hxe⟩ := (mem_imgTil (⊥ : Subgroup G) V hV U' _).1 (h hmem)
  have hval : x.val = u := by
    have h1 := mkTil_injective_bot V hV hxe
    simpa [IntMod.mk, IntMod.val] using congrArg IntMod.val h1
  rwa [← hval]

private theorem map_Ztil_ne (hV : IsElemAbelian 2 c.V) {k₁ k₂ : G} (hk₁ : k₁ ∈ c.L)
    (hk₂ : k₂ ∈ c.L) {x₁ x₂ : ↥(c.H hV)}
    (hP₁ : imgTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.conjSubgroup D.Z k₁) =
      (c.Ztil hV).map (x₁ : MulAut (c.toCtx23L.W hV)).toMonoidHom)
    (hP₂ : imgTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.conjSubgroup D.Z k₂) =
      (c.Ztil hV).map (x₂ : MulAut (c.toCtx23L.W hV)).toMonoidHom)
    (hkne : CFSG.Quasithin.conjSubgroup D.Z k₁ ≠ CFSG.Quasithin.conjSubgroup D.Z k₂) :
    (c.Ztil hV).map (x₁ : MulAut (c.toCtx23L.W hV)).toMonoidHom ≠
      (c.Ztil hV).map (x₂ : MulAut (c.toCtx23L.W hV)).toMonoidHom := by
  intro heq
  apply hkne
  refine le_antisymm ?_ ?_
  · refine le_of_imgTil_le c.V hV (conjSubgroup_Z_le_V_of_mem_L c hk₁) ?_
    rw [hP₁, hP₂]
    exact le_of_eq heq
  · refine le_of_imgTil_le c.V hV (conjSubgroup_Z_le_V_of_mem_L c hk₂) ?_
    rw [hP₁, hP₂]
    exact le_of_eq heq.symm

private theorem exists_imgTil_sup_eq (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ c.L) (hk₂ : k₂ ∈ c.L)
    (hkne : CFSG.Quasithin.conjSubgroup D.Z k₁ ≠ CFSG.Quasithin.conjSubgroup D.Z k₂) :
    ∃ x : ↥c.L, imgTil (⊥ : Subgroup G) c.V hV
        (CFSG.Quasithin.conjSubgroup D.Z k₁ ⊔ CFSG.Quasithin.conjSubgroup D.Z k₂) =
      imgTil (⊥ : Subgroup G) c.V hV (c.W.map (MulAut.conj (x : G)).toMonoidHom) := by
  have hspec := geom14_spec c h4 h1930 hV hm hSLH hnat hker
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  let x₁ : ↥(c.H hV) := c.phiL hV ⟨k₁⁻¹, c.L.inv_mem hk₁⟩
  let x₂ : ↥(c.H hV) := c.phiL hV ⟨k₂⁻¹, c.L.inv_mem hk₂⟩
  have hP₁ : imgTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.conjSubgroup D.Z k₁) =
      (c.Ztil hV).map (x₁ : MulAut (c.toCtx23L.W hV)).toMonoidHom := by
    have h := imgTil_map_conj c.toCtx23L hV ⟨k₁⁻¹, c.L.inv_mem hk₁⟩ (A := D.Z) hZleV
    simpa [CFSG.Quasithin.conjSubgroup, Ctx23L.Ztil, x₁] using h
  have hP₂ : imgTil (⊥ : Subgroup G) c.V hV (CFSG.Quasithin.conjSubgroup D.Z k₂) =
      (c.Ztil hV).map (x₂ : MulAut (c.toCtx23L.W hV)).toMonoidHom := by
    have h := imgTil_map_conj c.toCtx23L hV ⟨k₂⁻¹, c.L.inv_mem hk₂⟩ (A := D.Z) hZleV
    simpa [CFSG.Quasithin.conjSubgroup, Ctx23L.Ztil, x₂] using h
  have hne := map_Ztil_ne c hV hk₁ hk₂ hP₁ hP₂ hkne
  obtain ⟨y, hy⟩ := hspec.2.2 x₁ x₂ hne
  obtain ⟨x, rfl⟩ := c.phiL_surjective hV y
  have hπ : closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))) =
      imgTil (⊥ : Subgroup G) c.V hV c.W :=
    le_antisymm (line_le_imgTil_W c hV hm hSLH hnat) (imgTil_W_le_line c hV hm hSLH hnat)
  have hπmap : (closure (⋃ p ∈ c.Pstar hV,
      p • ((c.Ztil hV : Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))).map
        (c.phiL hV x : MulAut (c.toCtx23L.W hV)).toMonoidHom =
      imgTil (⊥ : Subgroup G) c.V hV (c.W.map (MulAut.conj (x : G)).toMonoidHom) := by
    rw [hπ, imgTil_map_conj c.toCtx23L hV x (Ctx2311.W_le_V c)]
  refine ⟨x, ?_⟩
  rw [s15_Core_imgTil_sup hV (conjSubgroup_Z_le_V_of_mem_L c hk₁)
      (conjSubgroup_Z_le_V_of_mem_L c hk₂), hP₁, hP₂, ← hπmap]
  exact hy

theorem conjSubgroup_sup_eq_conjSubgroup_W_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    ∀ k₁ ∈ c.L, ∀ k₂ ∈ c.L,
      CFSG.Quasithin.conjSubgroup D.Z k₁ ≠ CFSG.Quasithin.conjSubgroup D.Z k₂ →
      ∃ k ∈ c.L, CFSG.Quasithin.conjSubgroup D.Z k₁ ⊔
        CFSG.Quasithin.conjSubgroup D.Z k₂ = CFSG.Quasithin.conjSubgroup c.W k := by
  intro k₁ hk₁ k₂ hk₂ hkne
  obtain ⟨x, himg⟩ :=
    exists_imgTil_sup_eq c h4 h1930 hV hm hSLH hnat hker hk₁ hk₂ hkne
  have hWx : c.W.map (MulAut.conj (x : G)).toMonoidHom ≤ c.V := by
    intro w hw
    obtain ⟨v, hvW, rfl⟩ := Subgroup.mem_map.1 hw
    have hxN : (x : G) ∈ Subgroup.normalizer (c.V : Set G) :=
      ((le_sup_left : c.L ≤ c.L ⊔ D.T).trans
        (Ctx23L.sup_le_normalizer_V D Ch c.toCtx23L)) x.2
    exact (Subgroup.mem_normalizer_iff.mp hxN v).1 (Ctx2311.W_le_V c hvW)
  refine ⟨(x : G)⁻¹, c.L.inv_mem x.2, ?_⟩
  have hWconj : CFSG.Quasithin.conjSubgroup c.W ((x : G)⁻¹) =
      c.W.map (MulAut.conj (x : G)).toMonoidHom := by
    simp only [CFSG.Quasithin.conjSubgroup, inv_inv]
  rw [hWconj]
  exact le_antisymm
    (le_of_imgTil_le c.V hV
      (sup_le (conjSubgroup_Z_le_V_of_mem_L c hk₁) (conjSubgroup_Z_le_V_of_mem_L c hk₂))
      (le_of_eq himg))
    (le_of_imgTil_le c.V hV hWx (le_of_eq himg.symm))

private theorem exists_mem_L_point (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    {k : G} (hk : k ∈ c.N) :
    ∃ l ∈ c.L, ∃ v : G, v ∈ CFSG.Quasithin.conjSubgroup D.Z k ∧ v ≠ 1 ∧
      v ∈ CFSG.Quasithin.conjSubgroup D.Z l := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_ne_bot_of_sl3 c h4 h1930 hm)
  have hv : k⁻¹ * (z : G) * k ∈ CFSG.Quasithin.conjSubgroup D.Z k := by
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have h : k * (k⁻¹ * (z : G) * k) * k⁻¹ = (z : G) := by group
    rw [h]
    exact z.2
  have hv1 : k⁻¹ * (z : G) * k ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    have h' : (z : G) = 1 := by
      calc (z : G) = k * (k⁻¹ * (z : G) * k) * k⁻¹ := by group
        _ = k * 1 * k⁻¹ := by rw [h]
        _ = 1 := by group
    simpa using h'
  obtain ⟨l, hlL, hvl⟩ := exists_mem_conjSubgroup_L_of_sl3 c h4 h1930 hV hm hnat
    (k⁻¹ * (z : G) * k) (conjSubgroup_Z_le_V' c hk hv)
  exact ⟨l, hlL, k⁻¹ * (z : G) * k, hv, hv1, hvl⟩

private theorem exists_L_conjSubgroup_eq (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hV : IsElemAbelian 2 c.V) (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    ∀ k ∈ c.N, ∃ l ∈ c.L, CFSG.Quasithin.conjSubgroup D.Z k =
      CFSG.Quasithin.conjSubgroup D.Z l := by
  intro k hk
  obtain ⟨l, hlL, v, hv, hv1, hvl⟩ := exists_mem_L_point c h4 h1930 hV hm hnat hk
  have hmem : v ∈ CFSG.Quasithin.conjSubgroup D.Z k ⊓
      CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) (k⁻¹ * l) := by
    refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
    have hlk : k * (k⁻¹ * l) = l := by group
    rw [hlk]
    exact hvl
  have hne : CFSG.Quasithin.conjSubgroup D.Z k ⊓
      CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) (k⁻¹ * l) ≠ ⊥ := by
    intro hbot
    exact hv1 (Subgroup.mem_bot.mp (hbot ▸ hmem))
  have hTI := Ctx23L.conjSubgroup_TI c.toCtx23L h4 h1930 k (k⁻¹ * l)
  have h1 : CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) (k⁻¹ * l) =
      CFSG.Quasithin.conjSubgroup D.Z l := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
    congr 1
    group
  refine ⟨l, hlL, ?_⟩
  rw [← h1]
  exact (hTI hne).symm

private noncomputable def imagePstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) : Subgroup ↥(c.H hV) :=
  (P.subgroupOf c.L).map (c.phiL hV)

private theorem sylowStar_le_imagePstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ imagePstar c hV P := by
  rw [c.sylowStar_coe hV, imagePstar]
  exact Subgroup.map_mono (Ctx23L.T_subgroupOf_le_P c hV P hP)

private theorem Pstar_P_ne_top (h4 : S23_4 D Ch) (h1930 : H1930 D) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P) :
    imagePstar c.toCtx23L hV P ≠ ⊤ := by
  intro htop
  change (P.subgroupOf c.L).map (c.phiL hV) = ⊤ at htop
  have hLP : c.L ≤ P := by
    intro x hx
    have hxP : c.phiL hV ⟨x, hx⟩ ∈ (P.subgroupOf c.L).map (c.phiL hV) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact mem_of_phiL_mem_map c hV hker hP.1.1.1 ⟨x, hx⟩ hxP
  have hTX : D.T ≤ Subgroup.normalizer (c.X : Set G) :=
    T_le_normalizer_X_of_sl3 c h4 h1930 hV hm hnat hker
  have hPX : P = c.X :=
    hP.eq_of_ge ⟨c.hX.1, hTX, c.hXM⟩ (c.hX.1.2.1.trans hLP)
  exact c.hX.2.1 (le_antisymm c.hX.1.2.1 (hLP.trans (le_of_eq hPX)))

theorem L0_le_X_of_sl3 (h4 : S23_4 D Ch) (h1930 : H1930 D) (hV : IsElemAbelian 2 c.V)
    (hm : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSLH : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    (h209 : S20_9 D) : c.L0 ≤ c.X := by
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hspec := geom14_spec c h4 h1930 hV hm hSLH hnat hker
  have hneTop := Pstar_P_ne_top c h4 h1930 hV hm hSLH hnat hker hP
  rcases hspec.1 (imagePstar c.toCtx23L hV P)
    (sylowStar_le_imagePstar c.toCtx23L hV P hP) hneTop with hst | hX'
  · exfalso
    apply hP.1.2.2
    intro x hx
    have hxL : x ∈ c.L := hP.1.1.2.1 hx
    have hxP : c.phiL hV ⟨x, hxL⟩ ∈ imagePstar c.toCtx23L hV P :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    exact (Ctx23L.phiL_mem_stabilizer_Ztil_iff c.toCtx23L hV h4 h1930 ⟨x, hxL⟩).1
      (hst hxP)
  · rw [hL0P]
    refine (uc22p21c_Hinf_le P).trans ?_
    intro x hx
    have hxL : x ∈ c.L := hP.1.1.2.1 hx
    have hxP : c.phiL hV ⟨x, hxL⟩ ∈ imagePstar c.toCtx23L hV P :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hxA : x ∈ c.X ⊓ c.L :=
      mem_of_phiL_mem_map c hV hker (le_inf c.hX.1.1 (Subgroup.map_subtype_le _))
        ⟨x, hxL⟩ (by simpa [Ctx2311.Pstar] using hX' hxP)
    exact hxA.1

end Ctx2311

private theorem conjSubgroup_sup_eq_conjSubgroup_W_N_of_sl3 (D : Data G) (Ch : Choice2011 G)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (h4 : S23_4 D Ch) (hline : S23_5_line D Ch) (hKN : KNshape)
    (hS : KSchurL2) (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch) :
    H1930 D → ∀ c : Ctx2311 D Ch, ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N,
      CFSG.Quasithin.conjSubgroup D.Z k₁ ≠ CFSG.Quasithin.conjSubgroup D.Z k₂ →
        ∃ k ∈ c.N, CFSG.Quasithin.conjSubgroup D.Z k₁ ⊔
          CFSG.Quasithin.conjSubgroup D.Z k₂ = CFSG.Quasithin.conjSubgroup c.W k := by
  intro h1930 c
  obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
    Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
      hN1 hN2 hN3
  intro k₁ hk₁ k₂ hk₂ hne
  obtain ⟨l₁, hl₁, h₁⟩ :=
    Ctx2311.exists_L_conjSubgroup_eq c h4 h1930 hV hm hnat k₁ hk₁
  obtain ⟨l₂, hl₂, h₂⟩ :=
    Ctx2311.exists_L_conjSubgroup_eq c h4 h1930 hV hm hnat k₂ hk₂
  rw [h₁, h₂] at hne ⊢
  obtain ⟨l, hl, hle⟩ := Ctx2311.conjSubgroup_sup_eq_conjSubgroup_W_of_sl3 c h4 h1930 hV hm
    hSLH hnat hker l₁ hl₁ l₂ hl₂ hne
  exact ⟨l, (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c.toCtx23L) hl, hle⟩

theorem Ctx2311.geom2314_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h209 : S20_9 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (h4 : S23_4 D Ch) (hline : S23_5_line D Ch) (hKN : KNshape)
    (hS : KSchurL2) (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch) :
    (H1930 D → ∀ c : Ctx2311 D Ch, ∀ v ∈ c.V, ∃ k ∈ c.N,
        v ∈ CFSG.Quasithin.conjSubgroup D.Z k) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, ∀ k₁ ∈ c.N, ∀ k₂ ∈ c.N,
        CFSG.Quasithin.conjSubgroup D.Z k₁ ≠ CFSG.Quasithin.conjSubgroup D.Z k₂ →
          ∃ k ∈ c.N, CFSG.Quasithin.conjSubgroup D.Z k₁ ⊔
            CFSG.Quasithin.conjSubgroup D.Z k₂ = CFSG.Quasithin.conjSubgroup c.W k) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, Nat.card c.V = Nat.card D.Z ^ 3) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch,
        D.T ⊓ Subgroup.centralizer (c.W : Set G) ≤ CFSG.Open.pCoreOf 2 (c.X ⊔ D.T)) ∧
      (H1930 D → ∀ c : Ctx2311 D Ch, c.L0 ≤ c.X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
        hN1 hN2 hN3
    intro v hv
    obtain ⟨k, hkL, hkv⟩ :=
      Ctx2311.exists_mem_conjSubgroup_L_of_sl3 c h4 h1930 hV hm hnat v hv
    exact ⟨k, (le_sup_left : c.L ≤ c.L ⊔ D.T).trans
      (Ctx23L.sup_le_N D Ch c.toCtx23L) hkL, hkv⟩
  · exact conjSubgroup_sup_eq_conjSubgroup_W_N_of_sl3 D Ch hE h207 h2 h3 h4 hline hKN hS
      hS3 hN1 hN2 hN3
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
        hN1 hN2 hN3
    exact Ctx2311.card_V_eq_card_Z_pow_three_of_sl3 c h4 h1930 hV hnat
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
        hN1 hN2 hN3
    exact Ctx2311.T_inf_centralizer_W_le_pCoreOf_of_sl3 c h4 h1930 hV hm hSLH hnat hker
  · intro h1930 c
    obtain ⟨hm, hV, hSLH, hnat, hker⟩ :=
      Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
        hN1 hN2 hN3
    exact Ctx2311.L0_le_X_of_sl3 c h4 h1930 hV hm hSLH hnat hker h209

theorem s23_14_of_sl3 (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h209 : S20_9 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (h4 : S23_4 D Ch) (hline : S23_5_line D Ch) (hKN : KNshape)
    (hS : KSchurL2) (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch)
    (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch)
    (h12 : S23_12 D Ch) (h2122 : S21_22Use D Ch) :
    S23_14 D Ch := by
  obtain ⟨hPt, hLine, hCard, hCW, hL0X⟩ :=
    Ctx2311.geom2314_of D Ch hE h207 h209 h2 h3 h4 hline hKN hS hS3 hN1 hN2 hN3
  obtain ⟨hKW, hVK, -, hN4', hWT⟩ :=
    Ctx2311.geom2311_of D Ch hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
      hN1 hN2 hN3 kSL3Span_holds kSL3Line_holds
  have hn : H1930 D → ∀ _ : Ctx2311 D Ch, 2 ≤ CFSG.Open.pRank 2 D.Z := by
    intro h1930 c
    obtain ⟨hm, -, -, -, -⟩ :=
      Ctx2311.sl3Line_of c h1930 hE h207 h2 h3 h4 hline hKN KOrdNat.kOrdNatural_holds hS hS3
        hN1 hN2 hN3
    omega
  have hNW1 : H1930 D → ∀ c : Ctx2311 D Ch,
      ¬ c.X ⊔ D.T ≤ Subgroup.normalizer (E3.wClos c.V 1 D.T : Set G) := by
    intro h1930 c
    exact Ctx2311.not_le_normalizer_wClos_one c h4 h1930 h2122 (hn h1930 c) (hL0X h1930 c)
  have h13 : S23_13 D Ch :=
    s23_13_of D Ch h4 h12 (fun h1930 c w hw => hN4' h1930 c w hw) hKW
  have h14E : S23_14E D Ch :=
    s23_14E_of D Ch h4 h13 hn hNW1 hWT hPt hLine hCard hCW
  exact s23_14_of D Ch h4 h12 hVK h14E

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
