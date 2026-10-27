module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNbr
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section SelfDual

open CFSG.StandardType.ClassicalPosition.Geo

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem tcScalar_of_blockDegree_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (_he : e ∈ A) (hne : e ≠ 0)
    (hd : blockDegree A e = 1) {a : Matrix ι ι F} (ha : a ∈ A) : ∃ c : F, a * e = c • e := by
  unfold blockDegree at hd
  set W := (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) with hW
  have heW : e ∈ W := ⟨1, A.one_mem, by simp⟩
  have haW : a * e ∈ W := ⟨a, ha, rfl⟩
  have hne' : (⟨e, heW⟩ : W) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, heW⟩ hne').mp hd ⟨a * e, haW⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem glBlockCentralizer_eq_PSUYsd_of_scalar {S : Set (GL (Fin n) (PSUF g))}
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (heid : IsIdempotentElem e) (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = e)
    (hsc : ∀ s ∈ S, ∃ c : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) * e = c • e)
    (hcomm : ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) (PSUF g)) * e =
      e * (s : Matrix (Fin n) (Fin n) (PSUF g))) :
    glBlockCentralizer (PSUj n g) S e = PSUYsd n g e := by
  apply le_antisymm (glBlockCentralizer_le_PSUYsd heid.eq)
  intro u hu
  have hU1 : ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - e) =
      1 - e := mem_PSUYsd.mp hu
  have hUe := PSUYsd.comm_T hTa hu
  refine ⟨?_, hU1⟩
  change PSUj n g u ∈ Subgroup.centralizer S
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  obtain ⟨c, hc⟩ := hsc s hs
  have hse := hcomm s hs
  set U : Matrix (Fin n) (Fin n) (PSUF g) :=
    ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) with hUdef
  set sm : Matrix (Fin n) (Fin n) (PSUF g) := (s : Matrix (Fin n) (Fin n) (PSUF g)) with hsm
  have hUdec : U = U * e + (1 - e) := by
    rw [← hU1, Matrix.mul_sub, Matrix.mul_one]
    abel
  have hsdec : sm = sm * e + (1 - e) * sm := by
    have : sm * (1 - e) = (1 - e) * sm := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hse]
    calc sm = sm * e + sm * (1 - e) := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
      _ = sm * e + (1 - e) * sm := by rw [this]
  calc sm * U = sm * (U * e + (1 - e)) := by rw [← hUdec]
    _ = sm * (e * U) + sm * (1 - e) := by rw [hUe, Matrix.mul_add]
    _ = (sm * e) * U + (1 - e) * sm := by
        rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
          hse]
    _ = c • (e * U) + (1 - e) * sm := by rw [hc, Matrix.smul_mul]
    _ = c • (U * e) + (1 - e) * sm := by rw [hUe]
    _ = U * (sm * e) + (U * (1 - e)) * sm := by
        rw [hc, Matrix.mul_smul, hU1]
    _ = U * (sm * e + (1 - e) * sm) := by
        rw [Matrix.mul_add, Matrix.mul_assoc]
    _ = U * sm := by rw [← hsdec]

theorem tcIsSolvable_PSUYsd_of_rank_three_two {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : IsIdempotentElem T) (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    (hr : Matrix.rank T = 3) (hg : g = 0) : Group.IsSolvable ↥(PSUYsd n g T) := by
  obtain ⟨e⟩ := PSUYsd_mulEquiv hT hTa
  have key : ∀ k : ℕ, k = 3 → Group.IsSolvable ↥(Unitary.SU (PSUσ g) k) := by
    rintro k rfl
    subst hg
    have := CFSG.Quasithin.isSolvable_statedSU_one (F := PSUF 0) (card_PSUF 0)
    exact solvable_of_solvable_injective
      (f := (Unitary.equivStatedSU (F := PSUF 0) (p := 2) (f := 1) (card_PSUF 0) 3).toMonoidHom)
      (Unitary.equivStatedSU (F := PSUF 0) (p := 2) (f := 1) (card_PSUF 0) 3).injective
  have := key _ hr
  exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective

theorem PSUBlock.exists_model_of_selfDual_one [Finite X] (hH : PSULiftHyp n g ψ p B)
    {S : Set (GL (Fin n) (PSUF g))} {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hb : PSUBlock ψ B S e e)
    (hd1 : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e = 1)
    {D J : Subgroup X} (hDcard : Nat.card D = p ^ 2)
    (hjc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'g : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S e, glBlockCentralizer (PSUj n g) S e⁆)
    (hJ'm : J'.map ψ = J) :
    3 ≤ Matrix.rank e ∧ CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU (Matrix.rank e) 2
      (g + 1) := by
  classical
  have hblock := hb.three_mul_blockDegree_le_rank hH hDcard hjc hJ'g hJ'm
  have hr3 : 3 ≤ Matrix.rank e := by omega
  have heid : IsIdempotentElem e := hb.e_prim.2.1
  have hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = e := hb.eps_prim.2.2.2.1
  have hsc : ∀ s ∈ S, ∃ c : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) * e = c • e :=
    fun s hs => tcScalar_of_blockDegree_eq_one hb.e_prim.1 hb.e_prim.2.2.1 hd1
      (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
  have hcomm : ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) (PSUF g)) * e =
      e * (s : Matrix (Fin n) (Fin n) (PSUF g)) := fun s hs =>
    (adjoin_commute (hb.S_comm hH) _ (Algebra.subset_adjoin ⟨s, hs, rfl⟩) e hb.e_prim.1).eq
  have hGY : glBlockCentralizer (PSUj n g) S e = PSUYsd n g e :=
    glBlockCentralizer_eq_PSUYsd_of_scalar heid hTa hsc hcomm
  rw [hGY] at hJ'g
  have hJ'perf : ⁅J', J'⁆ = J' := tcCommutator_self_of_isQuasisimple hJ'g.2.2
  have hJ'ne : J' ≠ ⊥ := tcNe_bot_of_isQuasisimple hJ'g.2.2
  have hJ'Y : J' ≤ PSUYsd n g e :=
    hJ'g.1.trans (Subgroup.commutator_le.mpr fun a ha b hb' =>
      (PSUYsd n g e).mul_mem ((PSUYsd n g e).mul_mem ((PSUYsd n g e).mul_mem ha hb')
        ((PSUYsd n g e).inv_mem ha)) ((PSUYsd n g e).inv_mem hb'))
  have hrq : (Matrix.rank e, 2 ^ (g + 1)) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hg0 : g = 0 := by
      have : 2 ^ (g + 1) = 2 ^ 1 := by rw [h2]; norm_num
      have := Nat.pow_right_injective (le_refl 2) this
      omega
    have := tcIsSolvable_PSUYsd_of_rank_three_two heid hTa h1 hg0
    have : Group.IsSolvable ↥J' :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hJ'Y)
    have : Nontrivial ↥J' := (Subgroup.nontrivial_iff_ne_bot J').mpr hJ'ne
    have := IsSolvable.commutator_lt_top_of_nontrivial ↥J'
    rw [hJ'g.2.2.1] at this
    exact lt_irrefl _ this
  have hYq := isQuasisimple_PSUYsd heid hTa hr3 hrq
  have hYY : IsComponentOf (PSUYsd n g e) (PSUYsd n g e) := ⟨le_rfl, IsSubnormal.refl _, hYq⟩
  rw [tcCommutator_self_of_isQuasisimple hYq] at hJ'g
  have hJ'eq : J' = PSUYsd n g e :=
    isComponentOf_eq_of_perfect_le hYY hJ'g hJ'Y le_rfl hJ'perf hJ'ne
  have hJeq : (PSUYsd n g e).map ψ = J := by rw [← hJ'm, hJ'eq]
  refine ⟨hr3, ?_⟩
  have hmodel := lieModel_map_PSUYsd hH.ker heid hTa hr3 hrq
  rw [hJeq] at hmodel
  exact hmodel

end SelfDual

end CFSG.StandardType.TableCRes
