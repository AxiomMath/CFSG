module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofO2
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofRank
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec18.Rem187
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

namespace Res7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_forall_comm {J : Subgroup G}
    (hJ : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* projSL 3 (GaloisField 2 2))) {y : G} (hy : y ∈ J)
    (hc : ∀ z ∈ J, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 J) : y ∈ CFSG.Open.pCoreOf 2 J := by
  obtain ⟨e⟩ := hJ
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2)) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
    exact e'.isSimpleGroup
  have hperf : Group.IsPerfect (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have : Group.IsPerfect (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2)) := KFacts.KS18.isPerfect_projectiveSL _
    exact Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) (MulEquiv.surjective _)
  exact mem_pCoreOf_of_forall_comm_of_simple hsimple hperf hy hc

theorem le_of_le_sup_of_isPerfect {K Q P : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hK : ⁅K, K⁆ = K) (hP : ⁅P, P⁆ = P) (hPKQ : P ≤ K ⊔ Q) : P ≤ K := by
  have hQs : Group.IsSolvable Q := by
    have := hQ2.isNilpotent
    infer_instance
  have hKn : (K.subgroupOf (K ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQK)
  have hres := Sec18.inSubgroup_perfectResidual_eq_of_isSubnormal le_sup_left le_sup_right
    (sup_le hKQ Subgroup.le_normalizer) hQs hKn.isSubnormal hK rfl
  rw [← hres]
  exact Sec18.le_inSubgroup_perfectResidual hP hPKQ

end Res7

theorem step202KY_of
    (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (h189 : Sec18.Item189) : Step202KY := by
  intro G _ _ A M L N c h X hX hXM hne Y hY S hS hI hcent
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h18 : Sec18Std G A M := sec18Std_of_hyp201 h.1
  set K := kTwenty M c with hKdef
  have hAX : A ≤ X := fun a ha => hX.2 (Subgroup.mem_sup_left ha)
  have hKX : K ≤ X := fun k hk => hX.2 (Subgroup.mem_sup_right hk)
  have hYX : Y ≤ X := le_of_mem_oTwoComponentsIn hY
  have hSX : S ≤ X := hS.le.trans ((Subgroup.map_subtype_le _).trans inf_le_left)
  set I := Y ⊔ A ⊔ S with hIdef
  have hIX : I ≤ X := sup_le (sup_le hYX hAX) hSX
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQ1 : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hX.1
  have hYsn : (Y.subgroupOf X).IsSubnormal := (mem_oTwoComponentsIn_iff.mp hY).2.2.1
  have hYI : Y = inSubgroup perfectResidual I :=
    Sec18.eq_inSubgroup_perfectResidual_of_isSubnormal hI.2.2.1 (le_sup_left.trans le_sup_left)
      (Sec18.isSubnormal_subgroupOf_of_le hYsn hIX) (Sec18.commutator_eq_of_mem_oTwoComponentsIn hY)
      (Sec18.ne_bot_of_mem_oTwoComponentsIn hY)
  have hYq : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 3 (GaloisField 2 2)) := by
    rw [hYI]
    exact (h184 G A M h18 I hI).1
  have hF9 : Nat.card (A ⊓ Y : Subgroup G) = 9 := by
    obtain ⟨eY⟩ := hYq
    have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ Y) Y := by
      rw [hYI]
      exact isSylowOf_three_inf_of_mem_scriptH h1812 h184 h18 hI
    rw [hsyl.card_eq, factorization_three_of_nonempty_quotient eY]
    norm_num
  have hA := isE27_of_mem_partTwoE h.1.mem_partTwoE
  set F := A ⊓ Y with hFdef
  have hFY : F ≤ Y := inf_le_right
  have hF3 : IsPGroup 3 F := hA.isPGroup.to_le inf_le_left
  have hFe : ∀ f ∈ F, f ^ 3 = 1 := fun f hf => hA.1.2 f hf.1
  have hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun f hf f' hf' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨f, hf.1⟩ : A) ⟨f', hf'.1⟩)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hπ1 : ∀ x : X, π x = 1 ↔ (x : G) ∈ Q := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Sec18.mem_pCore_iff_mem_pCoreOf]
  have hcardimg : ∀ E : Subgroup G, E ≤ X → IsPGroup 3 E →
      Nat.card ((E.subgroupOf X).map π) = Nat.card E := by
    intro E hEX hE3
    have h1 := card_eq_card_map_mul_inf_ker π (E.subgroupOf X)
    have h2 : Nat.card ↥(E.subgroupOf X ⊓ π.ker) = 1 := by
      refine card_inf_eq_one_of_isPGroup hE3.comap_subtype ?_
      rw [hπ, QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup
    rw [h2, mul_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv] at h1
    exact h1.symm
  have hnorm : ∀ k ∈ K, Y.map (MulAut.conj k).toMonoidHom = Y := by
    intro k hk
    by_contra hne'
    have hYk : Y.map (MulAut.conj k).toMonoidHom ∈ oTwoComponentsIn X :=
      Sec18.map_conj_mem_oTwoComponentsIn hY (hKX hk)
    set Y' := Y.map (MulAut.conj k).toMonoidHom with hY'
    set F' := F.map (MulAut.conj k).toMonoidHom with hF'
    have hYY' : Y ≠ Y' := Ne.symm hne'
    have hF'Y' : F' ≤ Y' := Subgroup.map_mono hFY
    have hF'X : F' ≤ X := hF'Y'.trans (le_of_mem_oTwoComponentsIn hYk)
    have hFX : F ≤ X := hFY.trans hYX
    set Fs := (F.subgroupOf X).map π with hFs
    set Fs' := (F'.subgroupOf X).map π with hFs'
    have hcomm : ∀ a ∈ Fs, ∀ b ∈ Fs', a * b = b * a := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
      exact Sec19.Step1910Proof.mk_mul_comm_of_ne hY hYk hYY'
        (hFY (Subgroup.mem_subgroupOf.mp hf)) (hF'Y' (Subgroup.mem_subgroupOf.mp hf'))
    have hinf : Fs ⊓ Fs' = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨⟨f, hf, rfl⟩, ⟨f', hf', hff'⟩⟩
      have hfY : (f : G) ∈ Y := hFY (Subgroup.mem_subgroupOf.mp hf)
      have hcY : ∀ y ∈ Y, (f : G) * y * (f : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
        intro y hy
        have h1 : π ⟨y, hYX hy⟩ * π f' = π f' * π ⟨y, hYX hy⟩ :=
          Sec19.Step1910Proof.mk_mul_comm_of_ne hY hYk hYY' hy
            (hF'Y' (Subgroup.mem_subgroupOf.mp hf'))
        rw [hff'] at h1
        have h2 : π (f * ⟨y, hYX hy⟩ * f⁻¹ * (⟨y, hYX hy⟩ : X)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
          group
        have h3 := (hπ1 _).mp h2
        refine Sec19.Step1910Proof.inf_pCoreOf_le hY ⟨?_, ?_⟩
        · exact Y.mul_mem (Y.mul_mem (Y.mul_mem hfY hy) (Y.inv_mem hfY)) (Y.inv_mem hy)
        · simpa using h3
      have hfO : (f : G) ∈ CFSG.Open.pCoreOf 2 Y := Res7.mem_pCoreOf_of_forall_comm hYq hfY hcY
      have hbot : (F ⊓ CFSG.Open.pCoreOf 2 Y : Subgroup G) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _
          (card_inf_eq_one_of_isPGroup hF3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
      have hf1 : (f : G) = 1 := by
        have : (f : G) ∈ (F ⊓ CFSG.Open.pCoreOf 2 Y : Subgroup G) :=
          ⟨Subgroup.mem_subgroupOf.mp hf, hfO⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have hf1' : f = 1 := Subtype.ext hf1
      rw [hf1', map_one]
      exact Subgroup.one_mem _
    have hFsc : Nat.card Fs = 9 := by rw [hFs, hcardimg F hFX hF3, hF9]
    have hFsc' : Nat.card Fs' = 9 := by
      rw [hFs', hcardimg F' hF'X (hF3.map _), hF',
        Subgroup.card_map_of_injective (MulAut.conj k).injective, hF9]
    have hFsN : Fs ≤ Subgroup.normalizer (Fs' : Set (X ⧸ CFSG.pCore 2 ↥X)) := fun a ha =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).symm)
    set V := Fs ⊔ Fs' with hV
    have hVcard : Nat.card V = 81 := by
      have h1 := Sec6.card_sup_mul_card_inf hFsN
      rw [hinf, Subgroup.card_bot, mul_one, hFsc, hFsc'] at h1
      exact h1
    have hVset : ((V : Subgroup (X ⧸ CFSG.pCore 2 ↥X)) : Set (X ⧸ CFSG.pCore 2 ↥X)) =
        (Fs : Set (X ⧸ CFSG.pCore 2 ↥X)) * (Fs' : Set (X ⧸ CFSG.pCore 2 ↥X)) :=
      Subgroup.coe_mul_of_left_le_normalizer_right Fs Fs' hFsN
    have hFsc2 : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFc _ (Subgroup.mem_subgroupOf.mp hf) _ (Subgroup.mem_subgroupOf.mp hg))
    have hFsc2' : ∀ a ∈ Fs', ∀ b ∈ Fs', a * b = b * a := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      obtain ⟨u, hu, hfu⟩ := Subgroup.mem_subgroupOf.mp hf
      obtain ⟨v, hv, hgv⟩ := Subgroup.mem_subgroupOf.mp hg
      change (f : G) * g = g * f
      rw [← hfu, ← hgv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hFc u hu v hv
      calc k * u * k⁻¹ * (k * v * k⁻¹) = k * (u * v) * k⁻¹ := by group
        _ = k * (v * u) * k⁻¹ := by rw [this]
        _ = k * v * k⁻¹ * (k * u * k⁻¹) := by group
    have hFse : ∀ a ∈ Fs, a ^ 3 = 1 := by
      rintro _ ⟨f, hf, rfl⟩
      rw [← map_pow]
      exact (hπ1 _).mpr (by
        rw [show ((f ^ 3 : X) : G) = (f : G) ^ 3 from rfl, hFe _ (Subgroup.mem_subgroupOf.mp hf)]
        exact Q.one_mem)
    have hFse' : ∀ a ∈ Fs', a ^ 3 = 1 := by
      rintro _ ⟨f, hf, rfl⟩
      rw [← map_pow]
      refine (hπ1 _).mpr ?_
      obtain ⟨u, hu, hfu⟩ := Subgroup.mem_subgroupOf.mp hf
      rw [show ((f ^ 3 : X) : G) = (f : G) ^ 3 from rfl, ← hfu, ← map_pow, hFe u hu, map_one]
      exact Q.one_mem
    have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
      intro a ha b hb
      rw [← SetLike.mem_coe, hVset] at ha hb
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ha
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hb
      have e1 := hcomm a₁ ha₁ b₂ hb₂
      have e2 := hcomm b₁ hb₁ a₂ ha₂
      have e3 := hFsc2 a₁ ha₁ b₁ hb₁
      have e4 := hFsc2' a₂ ha₂ b₂ hb₂
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [e2]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
        _ = (b₁ * a₁) * (b₂ * a₂) := by rw [e3, e4]
        _ = b₁ * (a₁ * b₂) * a₂ := by group
        _ = b₁ * (b₂ * a₁) * a₂ := by rw [e1]
        _ = b₁ * b₂ * (a₁ * a₂) := by group
    have hVe : ∀ v ∈ V, v ^ 3 = 1 := by
      intro v hv
      rw [← SetLike.mem_coe, hVset] at hv
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hv
      rw [(Commute.mul_pow (hcomm a₁ ha₁ a₂ ha₂) 3), hFse a₁ ha₁, hFse' a₂ ha₂, one_mul]
    have h4 := Res7.four_le_localRank_of_quotient hQ1 V hVc hVe hVcard.ge
    rw [h.1.toTheoremFourHyp.localRank_three] at h4
    omega
  have hcY : ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ Q := by
    have hc : c ∈ sectionCentralizer A (inSubgroup perfectResidual I)
        (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual I)) := by
      rw [hcent]
      exact Subgroup.mem_zpowers c
    rw [← hYI] at hc
    intro y hy
    exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hY (hc.2 y hy)
  obtain ⟨H, hH18, hH187, -, -⟩ := exists_sec18H_of_hyp201One h
  obtain ⟨⟨hKC, -⟩, -, htype⟩ := h189 G A M H c hH18 hH187
  have hKperf : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hKC
  have hKsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases htype with ⟨n, -, ⟨e⟩, -⟩ | ⟨n, hn, hn0, ⟨e⟩, -⟩
    · have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
          (GaloisField 2 n)) :=
        CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
      exact (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
    · have : IsSimpleGroup ↥(projSL 2 (GaloisField 2 n)) :=
        Sec11.LSSolvableProof.isSimpleGroup_projSL (by obtain ⟨k, hk⟩ := hn; omega)
      exact e.isSimpleGroup
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hc3 : orderOf c = 3 := Res6.orderOf_c_of_hyp201One h184 h
  have hKc : K ≤ normalClosureIn K c := Res6.le_normalClosureIn_self hKperf hKsimple hcK hc3
  have hgen : ∀ z ∈ normalClosureIn K c, z ∈ X ∧ ∀ y ∈ Y, z * y * z⁻¹ * y⁻¹ ∈ Q := by
    intro z hz
    refine Subgroup.closure_induction
      (p := fun z _ => z ∈ X ∧ ∀ y ∈ Y, z * y * z⁻¹ * y⁻¹ ∈ Q) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨k, hk, rfl⟩
      refine ⟨X.mul_mem (X.mul_mem (hKX hk) (hKX hcK)) (X.inv_mem (hKX hk)), fun y hy => ?_⟩
      have hy' : k⁻¹ * y * k ∈ Y := by
        have h1 := hnorm k⁻¹ (K.inv_mem hk)
        rw [← h1]
        exact ⟨y, hy, by simp⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hXQ (hKX hk)) _).mp (hcY _ hy')
      convert h2 using 1
      group
    · exact ⟨X.one_mem, fun y _ => by simp⟩
    · rintro x z - - ⟨hxX, hx⟩ ⟨hzX, hz⟩
      refine ⟨X.mul_mem hxX hzX, fun y hy => ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXQ hxX) _).mp (hz y hy)
      have e : x * z * y * (x * z)⁻¹ * y⁻¹ =
          x * (z * y * z⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact Q.mul_mem h1 (hx y hy)
    · rintro x - ⟨hxX, hx⟩
      refine ⟨X.inv_mem hxX, fun y hy => ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXQ (X.inv_mem hxX)) _).mp
        (Q.inv_mem (hx y hy))
      convert h1 using 1
      group
  have hQM : Q ≤ M := (Sec18.pCoreOf_le_pCoreOf_inf h18 hAX).trans
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hKK : ⁅K, K⁆ = K := (Subgroup.isPerfect_iff).mp hKperf
  intro y hy
  apply Sec20.mem_normalizer_of_map_conj_le
  refine Res7.le_of_le_sup_of_isPerfect hQ2 (hKX.trans hXQ) (hQM.trans hMK) hKK ?_ ?_
  · rw [← Subgroup.map_commutator, hKK]
  · rintro _ ⟨k, hk, rfl⟩
    have hk' := (hgen k (hKc hk)).2 y hy
    have e : (MulAut.conj y).toMonoidHom k = (k * y * k⁻¹ * y⁻¹)⁻¹ * k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact (K ⊔ Q).mul_mem (Subgroup.mem_sup_right (Q.inv_mem hk')) (Subgroup.mem_sup_left hk)

end CFSG.RankThree.PartTwo.Sec20
