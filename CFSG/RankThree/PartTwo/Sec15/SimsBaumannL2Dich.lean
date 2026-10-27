module

public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import CFSG.RankThree.PartTwo.KFacts.K71Borel
public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

private theorem sbl2dich_ti_sl2 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {U V : Subgroup SL(2, F)} (hU : Nat.card U = Nat.card F) (hV : Nat.card V = Nat.card F)
    (h : U ⊓ V ≠ ⊥) : U = V := by
  obtain ⟨g, hg⟩ := IVK.Proofs2.exists_conj_of_card_eq Nat.prime_two hF hU
  obtain ⟨g', hg'⟩ := IVK.Proofs2.exists_conj_of_card_eq Nat.prime_two hF hV
  obtain ⟨⟨x, hxUV⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hy : g⁻¹ * x * g ∈ IVK.Proofs2.Qup F := (hg x).mp (Subgroup.mem_inf.mp hxUV).1
  have hk : g'⁻¹ * g ∈ IVK.Proofs2.Bor F := by
    by_contra hk
    have h1 := IVK.Proofs2.eq_one_of_conj_mem hk hy (by
      have : (g'⁻¹ * g) * (g⁻¹ * x * g) * (g'⁻¹ * g)⁻¹ = g'⁻¹ * x * g' := by group
      rw [this]
      exact (hg' x).mp (Subgroup.mem_inf.mp hxUV).2)
    apply hx1'
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hkN : g'⁻¹ * g ∈ Subgroup.normalizer (IVK.Proofs2.Qup F : Set SL(2, F)) :=
    IVK.Proofs2.Bor_le_normalizer hk
  ext z
  rw [hg z, hg' z, Subgroup.mem_normalizer_iff.mp hkN (g⁻¹ * z * g)]
  have : (g'⁻¹ * g) * (g⁻¹ * z * g) * (g'⁻¹ * g)⁻¹ = g'⁻¹ * z * g' := by group
  rw [this]

private theorem sbl2dich_ti_projSL {n : ℕ} (hn : 1 ≤ n) {G : Type} [Group G]
    (e : G ≃* projSL 2 (GaloisField 2 n)) {U V : Subgroup G}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hV : IsPGroup 2 V) (hVi : ¬ 2 ∣ V.index)
    (h : U ⊓ V ≠ ⊥) : U = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨ι⟩ := KFacts.nonempty_sl2_mulEquiv_projSL hF
  let φ : G ≃* SL(2, GaloisField 2 n) := e.trans ι.symm
  have hf : Function.Injective φ.toMonoidHom := φ.injective
  have hUc : Nat.card U = 2 ^ n :=
    (KFacts.sylow_two_of_mulEquiv_projSL hn e (hU.toSylow hUi)).2.1
  have hVc : Nat.card V = 2 ^ n :=
    (KFacts.sylow_two_of_mulEquiv_projSL hn e (hV.toSylow hVi)).2.1
  have hne : U.map φ.toMonoidHom ⊓ V.map φ.toMonoidHom ≠ ⊥ := by
    rw [← Subgroup.map_inf U V _ hf]
    exact fun h0 => h ((Subgroup.map_eq_bot_iff_of_injective _ hf).mp h0)
  exact Subgroup.map_injective hf (sbl2dich_ti_sl2 hF
    ((Subgroup.card_map_of_injective hf).trans (hUc.trans hF.symm))
    ((Subgroup.card_map_of_injective hf).trans (hVc.trans hF.symm)) hne)

private theorem sbl2dich_ti_of_equiv {n : ℕ} (hn : 1 ≤ n) {Y : Type} [Group Y] {N : Subgroup Y}
    (e : ↥N ≃* projSL 2 (GaloisField 2 n)) {U V : Subgroup Y}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U N) (hV : CFSG.QuasithinUnique.IsSylowTwoOf V N)
    (h : U ⊓ V ≠ ⊥) : U = V := by
  obtain ⟨hUN, hU2, hUi⟩ := hU
  obtain ⟨hVN, hV2, hVi⟩ := hV
  have key : U.subgroupOf N = V.subgroupOf N := by
    refine sbl2dich_ti_projSL hn e hU2.comap_subtype hUi hV2.comap_subtype hVi fun h0 => h ?_
    have h1 : (U ⊓ V).subgroupOf N = ⊥ := by
      rw [← h0]
      rfl
    exact (Subgroup.subgroupOf_eq_bot.mp h1).eq_bot_of_le (inf_le_left.trans hUN)
  have := Subgroup.subgroupOf_inj.mp key
  rwa [inf_eq_left.mpr hUN, inf_eq_left.mpr hVN] at this

private theorem sbl2dich_mem_normalizer_inf {Y : Type} [Group Y] {P Q : Subgroup Y} {x : Y}
    (hP : x ∈ Subgroup.normalizer (P : Set Y)) (hQ : x ∈ Subgroup.normalizer (Q : Set Y)) :
    x ∈ Subgroup.normalizer ((P ⊓ Q : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hP hQ ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hP y, hQ y]

private theorem sbl2dich_mem_normalizer_sup {Y : Type} [Group Y] {P Q : Subgroup Y} {x : Y}
    (hP : x ∈ Subgroup.normalizer (P : Set Y)) (hQ : x ∈ Subgroup.normalizer (Q : Set Y)) :
    x ∈ Subgroup.normalizer ((P ⊔ Q : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hP hQ ⊢
  rw [Subgroup.map_sup, hP, hQ]

private theorem sbl2dich_exists_sylow {Y : Type} [Group Y] [Finite Y] {N R : Subgroup Y}
    (hR : IsPGroup 2 R) (hRN : R ≤ N) :
    ∃ U, CFSG.QuasithinUnique.IsSylowTwoOf U N ∧ R ≤ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hR.comap_subtype (K := N)).exists_le_sylow
  refine ⟨(P : Subgroup N).map N.subtype, ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩, ?_⟩
  · have h : ((P : Subgroup N).map N.subtype).subgroupOf N = P :=
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
    rw [h]
    exact P.not_dvd_index
  · intro r hr
    exact ⟨⟨r, hRN hr⟩, hP (show (⟨r, hRN hr⟩ : N) ∈ R.comap N.subtype from hr), rfl⟩

private theorem sbl2dich_isSylowTwoOf_conj {Y : Type} [Group Y] {N U : Subgroup Y} [N.Normal]
    (x : Y) (hU : CFSG.QuasithinUnique.IsSylowTwoOf U N) :
    CFSG.QuasithinUnique.IsSylowTwoOf (U.map (MulAut.conj x).toMonoidHom) N := by
  obtain ⟨hUN, hU2, hUi⟩ := hU
  have hNx : N.map (MulAut.conj x).toMonoidHom = N := Subgroup.Normal.map_conj_eq N x
  refine ⟨(Subgroup.map_mono hUN).trans hNx.le, hU2.map _, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom) U N
    (MulAut.conj x).injective
  rw [hNx] at h
  change ¬ 2 ∣ (U.map (MulAut.conj x).toMonoidHom).relIndex N
  rw [h]
  exact hUi

private theorem sbl2dich_normalizer_sylow {Y : Type} [Group Y] [Finite Y] {N R : Subgroup Y}
    [N.Normal]
    (hTI : ∀ U V : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf U N →
      CFSG.QuasithinUnique.IsSylowTwoOf V N → U ⊓ V ≠ ⊥ → U = V)
    (hR : IsPGroup 2 R) (hRN : R ≤ N) (hR1 : R ≠ ⊥) :
    ∃ U, CFSG.QuasithinUnique.IsSylowTwoOf U N ∧ R ≤ U ∧
      ∀ x ∈ Subgroup.normalizer (R : Set Y), x ∈ Subgroup.normalizer (U : Set Y) := by
  obtain ⟨U, hU, hRU⟩ := sbl2dich_exists_sylow hR hRN
  refine ⟨U, hU, hRU, fun x hx => ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hRU' : R ≤ U.map (MulAut.conj x).toMonoidHom := by
    rw [← hx]
    exact Subgroup.map_mono hRU
  exact (hTI U _ hU (sbl2dich_isSylowTwoOf_conj x hU)
    fun h0 => hR1 (eq_bot_iff.mpr ((le_inf hRU hRU').trans h0.le))).symm

private theorem sbl2dich_main {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (π : X →* Y) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    {N : Subgroup Y} [N.Normal]
    (hTI : ∀ U V : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf U N →
      CFSG.QuasithinUnique.IsSylowTwoOf V N → U ⊓ V ≠ ⊥ → U = V)
    {A S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) (hKS : π.ker ≤ S) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ N.comap π) (N.comap π) ∨
      S ⊓ N.comap π = π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hSA : A ≤ Subgroup.normalizer (S : Set X) := hS.prop.2.2
  have hSb2 : IsPGroup 2 (S.map π) := hS2.map π
  have hcomapS : (S.map π).comap π = S := Subgroup.comap_map_eq_self hKS
  have hT : S ⊓ N.comap π = (S.map π ⊓ N).comap π := by
    rw [Subgroup.comap_inf, hcomapS]
  have hNN : ∀ y : Y, y ∈ Subgroup.normalizer (N : Set Y) := fun y => by
    rw [Subgroup.normalizer_eq_top N]
    exact Subgroup.mem_top y
  by_cases hR : S.map π ⊓ N = ⊥
  · right
    rw [hT, hR, MonoidHom.comap_bot]
  · left
    obtain ⟨U, hU, hRU, hnorm⟩ :=
      sbl2dich_normalizer_sylow hTI (hSb2.to_inf_left) inf_le_right hR
    have hSbN : ∀ s ∈ S.map π, s ∈ Subgroup.normalizer (U : Set Y) := fun s hs =>
      hnorm s (sbl2dich_mem_normalizer_inf (Subgroup.le_normalizer hs) (hNN s))
    have hAbS : ∀ a ∈ A, π a ∈ Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y) :=
      fun a ha => Subgroup.le_normalizer_map π ⟨a, hSA ha, rfl⟩
    have hAbU : ∀ a ∈ A, π a ∈ Subgroup.normalizer (U : Set Y) := fun a ha =>
      hnorm _ (sbl2dich_mem_normalizer_inf (hAbS a ha) (hNN _))
    have hS1 : (S.map π ⊔ U).comap π ∈ invariantPiSubgroups ⊤ A (piOf 2) := by
      refine ⟨le_top, ?_, fun a ha => ?_⟩
      · rw [isPiSubgroup_piOf_iff Nat.prime_two]
        exact (hSb2.to_sup_of_normal_right' hU.2.1 fun s hs => hSbN s hs).comap_of_ker_isPGroup
          π hker
      · exact Subgroup.le_normalizer_comap π
          (sbl2dich_mem_normalizer_sup (hAbS a ha) (hAbU a ha))
    have hS1le : S ≤ (S.map π ⊔ U).comap π := fun s hs =>
      Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π hs))
    have hS1S : (S.map π ⊔ U).comap π ≤ S := hS.2 hS1 hS1le
    have hUle : U ≤ S.map π := by
      intro u hu
      obtain ⟨x, rfl⟩ := hπ u
      exact ⟨x, hS1S (Subgroup.mem_comap.mpr (Subgroup.mem_sup_right hu)), rfl⟩
    have hUR : U = S.map π ⊓ N := le_antisymm (le_inf hUle hU.1) hRU
    rw [hT, ← hUR]
    refine ⟨Subgroup.comap_mono hU.1, hU.2.1.comap_of_ker_isPGroup π hker, ?_⟩
    have h1 : ((U.comap π).subgroupOf (N.comap π)).index = (U.subgroupOf N).index := by
      have h := Subgroup.relIndex_comap U π (N.comap π)
      rw [Subgroup.map_comap_eq_self_of_surjective hπ] at h
      exact h
    rw [h1]
    exact hU.2.2

theorem sylow_or_pCore_of_typeL2 {n : ℕ} (hn : 2 ≤ n)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    {A S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X))
        (oResidual 2 X ⊔ CFSG.pCore 2 X) ∨
      S ⊓ (oResidual 2 X ⊔ CFSG.pCore 2 X) = CFSG.pCore 2 X := by
  have hQS : CFSG.pCore 2 X ≤ S := Push153.pCore_le_of_mem_maxInvariant hS
  have hmap : (oResidual 2 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      oResidual 2 (X ⧸ CFSG.pCore 2 X) :=
    Stage1.Thm6.Prod.map_oResidual _ (QuotientGroup.mk'_surjective _) Nat.prime_two
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 X)).ker = CFSG.pCore 2 X :=
    QuotientGroup.ker_mk' _
  have hM : oResidual 2 X ⊔ CFSG.pCore 2 X =
      (oResidual 2 (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [← hmap, Subgroup.comap_map_eq, hker]
  haveI : (oResidual 2 (X ⧸ CFSG.pCore 2 X)).Normal :=
    Stage1.Thm6.Prod.oResidual_normal 2 _
  have hkerP : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 X)).ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have key := sbl2dich_main (QuotientGroup.mk' (CFSG.pCore 2 X)) (QuotientGroup.mk'_surjective _)
    hkerP (fun U V hU hV h => sbl2dich_ti_of_equiv (by omega) e hU hV h) hS (hker.le.trans hQS)
  rw [hker, ← hM] at key
  exact key

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
