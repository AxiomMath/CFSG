module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410DataA
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Stab
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.RankThree.PartTwo.Sec21.FF84S31Tools
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP4

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {t : ↥S}

theorem sq_S (e : ↥S ≃* Multiplicative F6) (x : ↥S) : x * x = 1 := by
  apply eq_one_of_toAdd_e_zero (e := e)
  rw [toAdd_e_mul]
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simp only [Pi.add_apply, Pi.zero_apply]
  exact h _

theorem mem_Cen_iff_stab (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (n : ↥(Nor S)) :
    (n : G) ∈ Cen (t : G) ↔ ψ n ∈ MulAction.stabilizer OmG tau0 := by
  rw [Subgroup.mem_centralizer_singleton_iff, H.comm_iff, het, MulAction.mem_stabilizer_iff]

@[expose] noncomputable def psiY (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0) :
    ↥(Nor S ⊓ Cen (t : G)) →* ↥(MulAction.stabilizer OmG tau0) :=
  (ψ.comp (Subgroup.inclusion inf_le_left)).codRestrict _
    (fun n => (mem_Cen_iff_stab H het ⟨n.1, (Subgroup.mem_inf.1 n.2).1⟩).1
      (Subgroup.mem_inf.1 n.2).2)

theorem psiY_coe (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (n : ↥(Nor S ⊓ Cen (t : G))) :
    ((psiY H het n : ↥(MulAction.stabilizer OmG tau0)) : OmG) =
      ψ ⟨n.1, (Subgroup.mem_inf.1 n.2).1⟩ := rfl

theorem psiY_surj (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0) :
    Function.Surjective (psiY H het) := by
  intro g
  obtain ⟨n, hn⟩ := H.surj g.1
  have hc : (n : G) ∈ Cen (t : G) := (mem_Cen_iff_stab H het n).2 (by rw [hn]; exact g.2)
  refine ⟨⟨n.1, Subgroup.mem_inf.2 ⟨n.2, hc⟩⟩, Subtype.ext ?_⟩
  rw [psiY_coe]
  exact hn

theorem pow4_of_psi_mem (H : OmSet S e ψ) (hE : Nat.card Eτ = 16) (x : ↥(Nor S))
    (hx : ψ x ∈ Eτ) : (x : G) ^ 4 = 1 := by
  have h1 : ψ x * ψ x = 1 := by
    rw [Eτ_eq_rootGroupOm hE] at hx
    exact mul_self_of_mem_rootGroupOm hx
  have h2 : ψ (x * x) = 1 := by rw [map_mul]; exact h1
  have h3 : ((x * x : ↥(Nor S)) : G) ∈ S := (H.psi_eq_one_iff _).1 h2
  have h4 : ((x : G) * x) * ((x : G) * x) = 1 := by
    have := sq_S e ⟨(x : G) * x, h3⟩
    exact congrArg Subtype.val this
  calc (x : G) ^ 4 = ((x : G) * x) * ((x : G) * x) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := h4

theorem psi_Op_le (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (m : ↥(Nor S)) (hm : (m : G) ∈ Op 2 (Nor S ⊓ Cen (t : G))) : ψ m ∈ Eτ := by
  let N : Subgroup OmG := ((Op 2 (Nor S ⊓ Cen (t : G))).subgroupOf (Nor S)).map ψ
  have hmN : ψ m ∈ N := Subgroup.mem_map.2 ⟨m, hm, rfl⟩
  have hle : N ≤ Eτ := by
    refine le_Op_of_normalized 2 (H := MulAction.stabilizer OmG tau0) (N := N) ?_ ?_ ?_
    · intro g hg
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
      exact (mem_Cen_iff_stab H het n).1 (Subgroup.mem_inf.1 (S3.Op_le 2 _ hn)).2
    · intro g hg h hh
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨y, hy⟩ := psiY_surj H het ⟨h, hh⟩
      have hyh : ψ ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ = h := by
        have := congrArg Subtype.val hy
        exact this
      refine Subgroup.mem_map.2 ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ * n *
        ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact S3.Op_conj_mem 2 (Subgroup.le_normalizer y.2) hn
      · rw [map_mul, map_mul, map_inv, hyh]
    · intro g hg
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨k, hk⟩ := S3.Op_isPGroup 2 (Nor S ⊓ Cen (t : G)) ⟨(n : G), hn⟩
      refine ⟨k, ?_⟩
      have h1 : n ^ (2 ^ k) = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      rw [← map_pow, h1, map_one]
  exact hle hmN

theorem mem_Op_Y (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (hE : Nat.card Eτ = 16) (x : ↥(Nor S ⊓ Cen (t : G))) :
    (x : G) ∈ Op 2 (Nor S ⊓ Cen (t : G)) ↔ ((psiY H het x : ↥(MulAction.stabilizer OmG tau0)) : OmG) ∈ Eτ := by
  constructor
  · intro hx
    exact psi_Op_le H het ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩ hx
  · intro hx
    let K : Subgroup ↥(MulAction.stabilizer OmG tau0) := Eτ.subgroupOf _
    let Nq : Subgroup G := (K.comap (psiY H het)).map (Nor S ⊓ Cen (t : G)).subtype
    have hxN : (x : G) ∈ Nq := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    have hle : Nq ≤ Op 2 (Nor S ⊓ Cen (t : G)) :=
      le_Op_of_normalized 2 (H := Nor S ⊓ Cen (t : G)) (N := Nq) (Subgroup.map_subtype_le _) ?_ ?_
    · exact hle hxN
    · intro g hg h hh
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
      refine Subgroup.mem_map.2 ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hy ⊢
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_Op 2 hy (psiY H het ⟨h, hh⟩).2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hy
      exact ⟨2, pow4_of_psi_mem H hE ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ hy⟩

theorem relIndex_Op_Y (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (hE : Nat.card Eτ = 16) : S.relIndex (Op 2 (Nor S ⊓ Cen (t : G))) = 16 := by
  have hle : Op 2 (Nor S ⊓ Cen (t : G)) ≤ Nor S := (S3.Op_le 2 _).trans inf_le_left
  let ψO : ↥(Op 2 (Nor S ⊓ Cen (t : G))) →* OmG := ψ.comp (Subgroup.inclusion hle)
  have hker : ψO.ker = S.subgroupOf (Op 2 (Nor S ⊓ Cen (t : G))) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact H.psi_eq_one_iff ⟨x.1, hle x.2⟩
  have hrange : ψO.range = Eτ := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact psi_Op_le H het ⟨x.1, hle x.2⟩ x.2
    · intro hg
      obtain ⟨y, hy⟩ := psiY_surj H het ⟨g, S3.Op_le 2 _ hg⟩
      have hyg : ψ ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ = g := by
        have := congrArg Subtype.val hy
        exact this
      have hyO : (y : G) ∈ Op 2 (Nor S ⊓ Cen (t : G)) := by
        rw [mem_Op_Y H het hE y]
        have := congrArg Subtype.val hy
        rw [show ((psiY H het y : ↥(MulAction.stabilizer OmG tau0)) : OmG) = g from this]
        exact hg
      exact ⟨⟨y.1, hyO⟩, hyg⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, hE]

instance Eτ_normal_stab : (Eτ.subgroupOf (MulAction.stabilizer OmG tau0)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_Op 2 hn g.2⟩

theorem quot_equiv_A5 (hE : Nat.card Eτ = 16) (hPair : HypOmPair) :
    Nonempty ((↥(MulAction.stabilizer OmG tau0) ⧸ Eτ.subgroupOf (MulAction.stabilizer OmG tau0)) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨eA0⟩ := hPair qMinus_sig0 qMinus_tau0 qMinus_sig0_add_tau0 tau0_ne_zero
  have eA : ↥P2 ≃* alternatingGroup (Fin 5) := eA0
  let K : Subgroup ↥(MulAction.stabilizer OmG tau0) := Eτ.subgroupOf _
  have hP2 : P2 ≤ MulAction.stabilizer OmG tau0 := fun g hg => hg.2
  let ι : ↥P2 →* ↥(MulAction.stabilizer OmG tau0) ⧸ K :=
    (QuotientGroup.mk' K).comp (Subgroup.inclusion hP2)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : Subgroup.inclusion hP2 g ∈ K := (QuotientGroup.eq_one_iff _).1 hg
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (g : OmG) = 1 :=
      eich_sigma_inj hE h1 (Or.inl (by rw [show (g : OmG) • sig0 = sig0 from g.2.1, sub_self]))
    exact Subtype.ext h2
  have hK : Nat.card K = 16 := by
    rw [← hE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S3.Op_le 2 _)).toEquiv
  have hQ : Nat.card (↥(MulAction.stabilizer OmG tau0) ⧸ K) = 60 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [card_stabilizer_sing qMinus_tau0 tau0_ne_zero, hK] at h1
    omega
  haveI : Finite (↥(MulAction.stabilizer OmG tau0) ⧸ K) := Nat.finite_of_card_ne_zero (by omega)
  have hP : Nat.card ↥P2 = 60 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin]
    decide
  have hbij : Function.Bijective ι :=
    (Nat.bijective_iff_injective_and_card ι).2 ⟨hinj, by rw [hP, hQ]⟩
  exact ⟨(MulEquiv.ofBijective ι hbij).symm.trans eA⟩

theorem data_B (H : OmSet S e ψ)
    (het : Multiplicative.toAdd (e t) = tau0) (hPar : HypOmParabolic) (hPair : HypOmPair) :
    S.relIndex (Op 2 (Nor S ⊓ Cen (t : G))) = 16 ∧
      (∃ (Q : Type) (_ : Group Q) (φ : ↥(Nor S ⊓ Cen (t : G)) →* Q),
        StatedClassicalModel Q .PSL 2 2 2 ∧ Function.Surjective φ ∧
          φ.ker = (Op 2 (Nor S ⊓ Cen (t : G))).subgroupOf (Nor S ⊓ Cen (t : G))) := by
  have hE : Nat.card Eτ = 16 := by
    have := (hPar qMinus_tau0 tau0_ne_zero).1.2
    show Nat.card ↥(Op 2 (MulAction.stabilizer OmG tau0)) = 16
    rw [this]
    norm_num
  refine ⟨relIndex_Op_Y H het hE, ?_⟩
  refine ⟨↥(MulAction.stabilizer OmG tau0) ⧸ Eτ.subgroupOf (MulAction.stabilizer OmG tau0),
    inferInstance, (QuotientGroup.mk' _).comp (psiY H het),
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ (quot_equiv_A5 hE hPair), ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp (psiY_surj H het)
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Op_Y H het hE x]
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
