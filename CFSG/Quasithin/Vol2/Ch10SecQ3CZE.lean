module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZD
public import CFSG.Quasithin.Vol2.Ch10SecEBlock
public import CFSG.Quasithin.Background.C1CampbellConnect

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_iSup_le {ι : Type*} {K N : Subgroup G} {B : ι → Subgroup G}
    (h : ∀ i, ⁅K, B i⁆ ≤ N) (hN : ∀ i, B i ≤ Subgroup.normalizer (N : Set G)) :
    ⁅K, ⨆ i, B i⁆ ≤ N := by
  let C : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ N}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, fun k hk => by
        have e : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hx.2 k hk)
          ((Subgroup.mem_normalizer_iff.mp hx.1 _).mp (hy.2 k hk))⟩
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by
        rw [commutatorElement_def]; simp⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, fun k hk => by
        have e : ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx.1) _).mp
          (N.inv_mem (hx.2 k hk))⟩ }
  have hle : (⨆ i, B i) ≤ C := iSup_le fun i x hx =>
    ⟨hN i hx, fun k hk => h i (Subgroup.commutator_mem_commutator hk hx)⟩
  rw [Subgroup.commutator_le]
  intro k hk x hx
  exact (hle hx).2 k hk

variable [Finite G]

theorem isSolvable_of_card_three {L : Subgroup G}
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : Group.IsSolvable ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).isNilpotent
  have hcyc : IsCyclic (↥L ⧸ CFSG.pCore 2 ↥L) := isCyclic_of_prime_card h3
  have : Group.IsSolvable (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.isSolvable_of_comm fun a b => hcyc.commGroup.mul_comm a b
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥L).subtype
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

omit [Finite G] in
theorem isSolvable_conjSub {B : Subgroup G} (hB : Group.IsSolvable ↥B) (t : G) :
    Group.IsSolvable ↥(B6.conjSub t B) :=
  Group.isSolvable_of_surjective (f := (B.equivMapOfInjective (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).toMonoidHom) (MulEquiv.surjective _)

theorem exists_eq_of_mem_cComp (hloc : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X T K : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK : K ∈ cComp X) {r : ℕ}
    {B : Fin r → Subgroup G} (hB : ∀ i, IsChi0Block X (B i))
    (hBT : ∀ i j, ∃ t ∈ T, B6.conjSub t (B i) = B j) (hO : twoResidual X = ⨆ i, B i) :
    ∃ i, B i = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  have hKX : K ≤ twoResidual X := by
    rw [SecE.twoResidual_eq_oTwoUpper, eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hK)]
    exact oTwoUpper_mono (le_of_mem_cComp hK)
  have hKns := not_isSolvable_of_mem_cComp hK
  by_cases hsol : ∀ i, Group.IsSolvable ↥(B i)
  ·
    set R := CFSG.solvableRadical ↥X with hR
    have hBR : ∀ i, B i ≤ R.map X.subtype := by
      intro i x hx
      have hBX : B i ≤ X := (hB i).1.2.1
      have hsol' : Group.IsSolvable ↥((B i).subgroupOf X) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBX).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hBX).symm.surjective
      have hle : (B i).subgroupOf X ≤ R := by
        rw [hR, A3.solvableRadical_eq_solvRad_top]
        exact le_solvRad_of_subnormal (A3.subnormal_top_iff.mpr (hB i).1.2.2) hsol'
      exact ⟨⟨x, hBX hx⟩, hle (show (⟨x, hBX hx⟩ : ↥X) ∈ (B i).subgroupOf X from hx), rfl⟩
    have hKR : K ≤ R.map X.subtype := hKX.trans (hO ▸ iSup_le hBR)
    have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
    have : Group.IsSolvable ↥(R.map X.subtype) :=
      Group.isSolvable_of_surjective (f := (R.equivMapOfInjective X.subtype
        X.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    exact hKns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKR))
  ·
    push Not at hsol
    obtain ⟨i₀, hi₀⟩ := hsol
    have hns : ∀ j, ¬ Group.IsSolvable ↥(B j) := by
      intro j hj
      obtain ⟨t, -, ht⟩ := hBT j i₀
      exact hi₀ (ht ▸ isSolvable_conjSub hj t)
    have hC : ∀ j, B j ∈ cComp X := fun j =>
      C1GN.mem_cComp_of_short (hB j).1.1 ((hB j).1.1.2.2.2.1.resolve_right fun h3 =>
        hns j (isSolvable_of_card_three h3)) (C1GN.isSubnormal_of_isBlock2 (hB j).1)
    have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
    have hcomm : ⁅K, ⨆ j, B j⁆ ≤ pCoreOf 2 X := by
      refine commutator_iSup_le (fun j => ?_) (fun j => (hB j).1.2.1.trans hXN)
      have h := Vol2Native.lemma_1_2_1_two hloc h37 hX hK (hC j) (Ne.symm (hne j))
      exact h.1.trans h.2
    have hKO : K ≤ pCoreOf 2 X := by
      calc K = ⁅K, K⁆ := (perfect_of_mem_cComp hK).symm
        _ ≤ ⁅K, ⨆ j, B j⁆ := Subgroup.commutator_mono le_rfl (hO ▸ hKX)
        _ ≤ pCoreOf 2 X := hcomm
    have hK2 : IsPGroup 2 ↥K := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hKO
    have : Group.IsNilpotent ↥K := hK2.isNilpotent
    exact hKns inferInstance

theorem isSQTKTC_of_pCoreOf_ne_bot {T L I : Subgroup G} (hyp : Hyp10 G T L I) {X : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) : IsSQTKTC X :=
  have := hyp.fsu.simple
  ⟨kGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hX,
    stronglyQuasithin_of_pCoreOf_ne_bot hyp.fsu.qtke hX⟩

namespace Ctx

variable {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem isChi0Block (h118 : TheoremC118) (h126 : TheoremC126) :
    IsChi0Block (fsuL0 T L ⊔ T) L ∨ IsChi0Block H K := by
  have := c.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat c.hyp.fsu.nonabelian c.hyp.fsu.qtke).1
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  have h126' := h126 G C₁ C₂ hC
  have hT2 : IsPGroup 2 T := c.hyp.fsu.sylow.1
  have hT0 : T ≠ ⊥ := fun h =>
    SecA.fsuVM_ne_bot c.hyp.fsu (le_bot_iff.mp (h ▸ SecA.fsuVM_le_T c.hyp))
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, -, -⟩ := hC.pair T hT2 hT0
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1ne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzZ : z ∈ quasithinOmegaOneCenter T := h1Z hz
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo c.hyp.fsu.sylow
  have hmin := SecB.minParabolic_of_isHStar c.h331 c.hyp c.hH
  have hHchar : CharTwo H := charTwo_of_inH c.hyp.fsu.qtke.2.1 S (hS ▸ c.hH.1)
  have hXO := SecA.pCoreOf_L0T_ne_bot c.hyp
  have hXmin := SecA.minParabolic_L0T c.h37 c.h38 c.hyp c.exists_SL_two
  rcases h126' H T (isSQTKTC_of_pCoreOf_ne_bot c.hyp c.hH.1.2) hmin.isSylow hHchar
      (minParabolic_iff.mp hmin).1 with hc1 | hn | ⟨r, B, -, hB, -, hO, -, htr⟩
  · exact absurd (c.eq_one_of_mem_centralizer_H hzZ (hc1 hz).2) hz1'
  · rcases h126' (fsuL0 T L ⊔ T) T (isSQTKTC_of_pCoreOf_ne_bot c.hyp hXO) hXmin.isSylow
        (SecA.charTwo_L0T c.hyp) (minParabolic_iff.mp hXmin).1 with
      hc1 | hn' | ⟨r, B, -, hB, -, hO, -, htr⟩
    · exact absurd (c.eq_one_of_mem_centralizer_L0 hzZ
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) (hc1 hz).2)) hz1'
    · have hle := normalizer_le_fsuM c.h331 c.hyp (hT2.to_le (h2B.trans (B2F.baum_le T))) h2ne
        hn'
      exact absurd (hn.trans hle) c.hH.2.1
    · obtain ⟨i, hi⟩ := exists_eq_of_mem_cComp hloc c.h37 hXO (SecE.mem_cComp_L0T c.hyp)
        (fun i => (hB i).1) htr hO
      exact Or.inl (hi ▸ (hB i).1)
  · obtain ⟨i, hi⟩ := exists_eq_of_mem_cComp hloc c.h37 c.hH.1.2 c.hKc (fun i => (hB i).1) htr hO
    exact Or.inr (hi ▸ (hB i).1)

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
