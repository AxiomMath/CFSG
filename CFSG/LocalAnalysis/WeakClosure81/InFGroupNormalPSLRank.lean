module

public import CFSG.Quasithin.EmptyFaithful.E111RFacts
public import CFSG.Quasithin.Vol2.Ch4Sec3L4315
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.Quasithin.Vol2.Ch11SecO1bN
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.Quasithin

private theorem mem_pCoreOf_of_conjModO2_eq_one {G : Type} [Group G] {J : Subgroup G}
    (hJs : IsSimpleGroup (ModO2 J)) (hJnab : ∃ a b : ModO2 J, a * b ≠ b * a)
    {g : G} (hgN : g ∈ Subgroup.normalizer (J : Set G)) (hgJ : g ∈ J)
    (hg : CFSG.Quasithin.H13.Ch4.L4315.conjModO2 J ⟨g, hgN⟩ = 1) :
    g ∈ pCoreOf 2 J := by
  haveI : IsSimpleGroup (ModO2 J) := hJs
  let z : ↥J := ⟨g, hgJ⟩
  have hconj : MulAut.conj (QuotientGroup.mk z : ModO2 J) = 1 := by
    have h1 := CFSG.Quasithin.H13.Ch4.L4315.conjModO2_of_mem J z
    have h2 : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (J : Set G))) =
        ⟨(z : G), Subgroup.le_normalizer z.2⟩ := Subtype.ext rfl
    rw [h2] at hg
    exact h1.symm.trans hg
  have hz : (QuotientGroup.mk z : ModO2 J) ∈ Subgroup.center (ModO2 J) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
    have h := congrArg (fun φ : MulAut (ModO2 J) => φ (QuotientGroup.mk w')) hconj
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have h' : (QuotientGroup.mk z : ModO2 J) * (QuotientGroup.mk w' : ModO2 J) =
        (QuotientGroup.mk w' : ModO2 J) * (QuotientGroup.mk z : ModO2 J) := by
      calc (QuotientGroup.mk z : ModO2 J) * (QuotientGroup.mk w' : ModO2 J)
          = ((QuotientGroup.mk z : ModO2 J) * (QuotientGroup.mk w' : ModO2 J) *
              (QuotientGroup.mk z : ModO2 J)⁻¹) * (QuotientGroup.mk z : ModO2 J) := by
            group
        _ = (QuotientGroup.mk w' : ModO2 J) * (QuotientGroup.mk z : ModO2 J) := by rw [h]
    exact h'.symm
  have hzb : (QuotientGroup.mk z : ModO2 J) = 1 := by
    have h := hz
    rw [CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_nonabelian hJnab] at h
    simpa using h
  have hzmem : z ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff z).mp hzb
  exact Subgroup.mem_map.mpr ⟨z, hzmem, rfl⟩

private theorem isPGroup_of_pow_mem_inf {X : Type} [Group X] {C J : Subgroup X}
    (hJ2 : IsPGroup 2 ↥(C ⊓ J)) (h : ∀ x ∈ C, ∃ k : ℕ, x ^ 2 ^ k ∈ J) :
    IsPGroup 2 ↥C := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro c
  obtain ⟨k, hk⟩ := h c c.2
  obtain ⟨m, hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp hJ2)
    ⟨(c : X) ^ 2 ^ k, C.pow_mem c.2 (2 ^ k), hk⟩
  refine ⟨k + m, ?_⟩
  have hm' : ((c : ↥C) ^ 2 ^ k) ^ 2 ^ m = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hm
  rw [Nat.pow_add, pow_mul]
  exact hm'

theorem mQuot_pCoreOf_le_of_normal_psl {G : Type} [Group G] [Finite G] {n : ℕ}
    {A K J : Subgroup G} (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal)
    (hJs : IsSimpleGroup (ModO2 J)) (hJnab : ∃ a b : ModO2 J, a * b ≠ b * a)
    (hJpsl : IsPSL 2 2 n (ModO2 J)) (hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J) (hAK : A ≤ K)
    (hA2 : IsElemAbelian 2 A) : E3.mQuot A (pCoreOf 2 K) ≤ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (ModO2 J) := hJs
  have hKN : K ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mp hJn
  let ρ : ↥K →* MulAut (ModO2 J) :=
    (CFSG.Quasithin.H13.Ch4.L4315.conjModO2 J).comp (Subgroup.inclusion hKN)
  let C : Subgroup ↥K := ρ.ker
  have hCnorm : C.Normal := MonoidHom.normal_ker ρ
  have hCJ_le : C ⊓ (J.subgroupOf K) ≤ (pCoreOf 2 J).subgroupOf K := by
    intro z hz
    obtain ⟨hzC, hzJ⟩ := Subgroup.mem_inf.mp hz
    have hρz : (CFSG.Quasithin.H13.Ch4.L4315.conjModO2 J) ⟨(z : G), hKN z.2⟩ = 1 :=
      MonoidHom.mem_ker.mp hzC
    exact Subgroup.mem_subgroupOf.mpr
      (mem_pCoreOf_of_conjModO2_eq_one hJs hJnab (hKN z.2) (Subgroup.mem_subgroupOf.mp hzJ)
        hρz)
  have hJ2 : IsPGroup 2 ↥((pCoreOf 2 J).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).comap_subtype
  have hCJ2 : IsPGroup 2 ↥(C ⊓ (J.subgroupOf K)) := hJ2.to_le hCJ_le
  have hC2 : IsPGroup 2 ↥C := by
    refine isPGroup_of_pow_mem_inf hCJ2 fun x hx => ?_
    obtain ⟨k, hk⟩ := hK2 (x : G) x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have hC_le : C ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hCnorm, hC2⟩
  have hA' : IsElemAbelian 2 (A.subgroupOf K) := hA2.subgroupOf K
  have hAρ : IsElemAbelian 2 ((A.subgroupOf K).map ρ) := hA'.map ρ
  have hbound : Nat.card ↥((A.subgroupOf K).map ρ) ≤ 2 ^ n :=
    (CFSG.Quasithin.E2.E22N.autRankLe_of_isPSL22 hJnab hJpsl).2 _ hAρ
  have hrel : E3.mQuot A (pCoreOf 2 K) = E3.mQuot (A.subgroupOf K) (pCore 2 ↥K) := by
    have h1 : (pCoreOf 2 K).relIndex A = (pCore 2 ↥K).relIndex (A.subgroupOf K) := by
      conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hAK]
      exact Subgroup.relIndex_map_map_of_injective (pCore 2 ↥K) (A.subgroupOf K)
        K.subtype_injective
    exact congrArg (padicValNat 2) h1
  rw [hrel]
  refine CFSG.Quasithin.Vol2.Ch11.SecO1b.mQuot_le_of_relIndex_le (fun x hx => hA'.2 x hx) ?_
  calc
    (pCore 2 ↥K).relIndex (A.subgroupOf K)
        ≤ (ρ.ker).relIndex (A.subgroupOf K) :=
          Subgroup.relIndex_le_of_le_left hC_le Subgroup.index_ne_zero_of_finite
    _ = Nat.card ↥((A.subgroupOf K).map ρ) := Subgroup.relIndex_ker _ ρ
    _ ≤ 2 ^ n := hbound

end CFSG.LocalAnalysis.WeakClosure81
