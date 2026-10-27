module

public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.WeakClosure81.ElevenSevenAlt
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.CGT.PushingUpLit.EightOneBlocksBasic
public import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_iSup {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g :=
  Subgroup.map_iSup _ _

theorem conjSubgroup_oTwoIn (X : Subgroup G) (g : G) :
    conjSubgroup (oTwoIn X) g = oTwoIn (conjSubgroup X g) := by
  unfold conjSubgroup
  exact (oTwoIn_map_equiv (MulAut.conj g⁻¹) X).symm

theorem conjSubgroup_blockU (X : Subgroup G) (g : G) :
    conjSubgroup (blockU X) g = blockU (conjSubgroup X g) := by
  unfold blockU
  rw [E3.conjSubgroup_commutator, conjSubgroup_oTwoIn]

theorem pCoreOf_le_of_isBlockOfInX {H L : Subgroup G} (hL : IsBlockOfInX H L) :
    pCoreOf 2 L ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal 2 hL.2.1
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 : (CFSG.Open.pCoreOf 2 (L.subgroupOf H)).map H.subtype = pCoreOf 2 L :=
    map_oTwoIn_subgroupOf hL.1
  have h4 : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := rfl
  rw [h3, h4] at h2
  exact h2

theorem eq_one_of_mem_iSup_of_centralizes {ι : Type*} (S : Finset ι) (K Y : ι → Subgroup G)
    (hYK : ∀ i ∈ S, Y i ≤ K i)
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⁅K i, K j⁆ = ⊥)
    (hZ : ∀ i ∈ S, Y i ⊓ Subgroup.centralizer (K i : Set G) = ⊥)
    {z : G} (hz : z ∈ ⨆ i ∈ S, Y i)
    (hzc : ∀ i ∈ S, z ∈ Subgroup.centralizer (K i : Set G)) : z = 1 := by
  classical
  induction S using Finset.induction_on generalizing z with
  | empty =>
      simpa using hz
  | insert j S₀ hj ih =>
      rw [Finset.iSup_insert] at hz
      set T : Subgroup G := ⨆ i ∈ S₀, Y i with hT
      have hT_Cj : T ≤ Subgroup.centralizer (K j : Set G) := by
        rw [hT]
        refine iSup₂_le fun i hi => ?_
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        exact (hYK i (Finset.mem_insert_of_mem hi)).trans
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j S₀) hij))
      have hYj_CT : Y j ≤ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        rw [hT]
        refine iSup₂_le fun i hi => ?_
        rw [Subgroup.le_centralizer_iff]
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        exact (hYK j (Finset.mem_insert_self j S₀)).trans
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (hcomm j (Finset.mem_insert_self j S₀) i (Finset.mem_insert_of_mem hi)
              (Ne.symm hij))).trans
            (Subgroup.centralizer_le (hYK i (Finset.mem_insert_of_mem hi))))
      have hYj_N : Y j ≤ Subgroup.normalizer (T : Set G) :=
        hYj_CT.trans (Subgroup.centralizer_le_normalizer _)
      have hz' : z ∈ (↑(Y j) : Set G) * ↑T := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Y j) T hYj_N]
        exact hz
      obtain ⟨u, hu, y, hy, hz_eq⟩ := hz'
      rw [← hz_eq]
      have hyCj : y ∈ Subgroup.centralizer (K j : Set G) := hT_Cj hy
      have hzCj : z ∈ Subgroup.centralizer (K j : Set G) := hzc j (Finset.mem_insert_self j S₀)
      have huCj : u ∈ Subgroup.centralizer (K j : Set G) := by
        have : u = z * y⁻¹ := by rw [← hz_eq]; group
        rw [this]
        exact Subgroup.mul_mem _ hzCj (Subgroup.inv_mem _ hyCj)
      have hu1 : u = 1 := by
        have hmem : u ∈ Y j ⊓ Subgroup.centralizer (K j : Set G) := ⟨hu, huCj⟩
        rw [hZ j (Finset.mem_insert_self j S₀)] at hmem
        simpa using hmem
      have hyz : y = z := by
        rw [← hz_eq]
        simp [hu1]
      rw [hu1]
      change (1 : G) * y = 1
      rw [one_mul]
      have hy' : y ∈ ⨆ i ∈ S₀, Y i := by rwa [hT] at hy
      exact ih (fun i hi => hYK i (Finset.mem_insert_of_mem hi))
        (fun i hi i' hi' hne => hcomm i (Finset.mem_insert_of_mem hi)
          i' (Finset.mem_insert_of_mem hi') hne)
        (fun i hi => hZ i (Finset.mem_insert_of_mem hi)) hy'
        (fun i hi => by rw [hyz]; exact hzc i (Finset.mem_insert_of_mem hi))

theorem hyperplaneRigid_conjSubgroup {M V Q : Subgroup G} (hset : Setting11 M V Q)
    (hr : 1 < rMV M V) (hm : 1 < mBar M ⊥ V hset.isElemAbelian) (g : G) :
    HyperplaneRigid (conjSubgroup V g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx D hDV hDrel hxD a ha
  obtain ⟨k, hk⟩ := hx
  have hV := hset.isElemAbelian
  have hD'V : conjSubgroup D g⁻¹ ≤ V := by
    rw [E3.conjSubgroup_le_iff_le_inv]
    simpa using hDV
  have hmq : E3.mQuot V (conjSubgroup D g⁻¹) = 1 := by
    have h1 := E3.mQuot_conjSubgroup (conjSubgroup V g) D g⁻¹
    rw [E3.conjSubgroup_conj_inv] at h1
    rw [h1]
    show padicValNat 2 (D.relIndex (conjSubgroup V g)) = 1
    rw [hDrel]
    exact padicValNat_self
  have hlt : (E3.mQuot V (conjSubgroup D g⁻¹) : ℕ∞) < rMV M V := by
    rw [hmq]
    simpa using hr
  have hCD : Subgroup.centralizer (conjSubgroup D g⁻¹ : Set G) ≤ M :=
    centralizer_le_of_mQuot_lt_rMV hD'V hlt
  have hx'C : g * x * g⁻¹ ∈ Subgroup.centralizer (conjSubgroup D g⁻¹ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d' hd'
    have hd'D : g⁻¹ * d' * g ∈ D := by
      simpa using (mem_conjSubgroup_iff.1 hd')
    have h1 := hxD (g⁻¹ * d' * g) hd'D
    calc d' * (g * x * g⁻¹) = g * ((g⁻¹ * d' * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * d' * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * d' := by group
  have hx'M : g * x * g⁻¹ ∈
      M ⊓ Subgroup.centralizer (conjSubgroup D g⁻¹ : Set G) := ⟨hCD hx'C, hx'C⟩
  have hx'ord : orderOf (g * x * g⁻¹) = orderOf x := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply] using this
  have hx'Opp : g * x * g⁻¹ ∈
      Opp 2 (M ⊓ Subgroup.centralizer (conjSubgroup D g⁻¹ : Set G)) :=
    Subgroup.subset_closure ⟨hx'M, k, hx'ord.trans hk⟩
  have hO := eleven_d hV hset.normal hD'V (by rw [hmq]; simpa using hm)
  have hx'CV : g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := hO hx'Opp
  have haV : g * a * g⁻¹ ∈ V := by simpa using (mem_conjSubgroup_iff.1 ha)
  have hcomm' : (g * a * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * a * g⁻¹) :=
    Subgroup.mem_centralizer_iff.1 hx'CV (g * a * g⁻¹) haV
  have h3 : g * (a * x) * g⁻¹ = g * (x * a) * g⁻¹ := by
    calc g * (a * x) * g⁻¹ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (g * x * g⁻¹) * (g * a * g⁻¹) := hcomm'
      _ = g * (x * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

theorem normalizes_of_hyperplaneRigid_of_family {A R : Subgroup G} {Ω : Set (Subgroup G)}
    {Y : Subgroup G → Subgroup G} (hA : IsElemAbelian 2 A) (hrigid : HyperplaneRigid A)
    (hR : IsPGroup 2 ↥R) (hΩ : ∀ X ∈ Ω, ∀ a ∈ A, conjSubgroup X a ∈ Ω)
    (hcomm : ∀ X ∈ Ω, ∀ X' ∈ Ω, X ≠ X' → ⁅X, X'⁆ = ⊥)
    (hYX : ∀ X ∈ Ω, Y X ≤ X) (hYR : ∀ X ∈ Ω, Y X ≤ R) (hY1 : ∀ X ∈ Ω, Y X ≠ ⊥)
    (hZ : ∀ X ∈ Ω, Y X ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hYconj : ∀ X ∈ Ω, ∀ a ∈ A, Y (conjSubgroup X a) = conjSubgroup (Y X) a) :
    ∀ X ∈ Ω, A ≤ Subgroup.normalizer (X : Set G) := by
  classical
  intro X hX
  by_contra hNX
  have hNne : A ⊓ Subgroup.normalizer (X : Set G) ≠ A := by
    intro h
    exact hNX (h ▸ inf_le_right)
  have hNle : A ⊓ Subgroup.normalizer (X : Set G) ≤ A := inf_le_left
  obtain ⟨B, hNB, hBA, hBrel⟩ :=
    exists_relIndex_two_of_lt hA.isPGroup hNle hNne
  have hBneA : B ≠ A := by
    intro h
    rw [h, Subgroup.relIndex_self] at hBrel
    omega
  obtain ⟨a₀, ha₀A, ha₀B⟩ :=
    (SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hBA hBneA)).2
  haveI : Fintype ↥B := Fintype.ofFinite _
  set T : Subgroup G := ⨆ b : ↥B, Y (conjSubgroup X (b : G)) with hT
  have hTΩ : ∀ b : ↥B, conjSubgroup X (b : G) ∈ Ω :=
    fun b => hΩ X hX (b : G) (hBA b.2)
  have hTR : T ≤ R := by
    rw [hT]
    exact iSup_le fun b => hYR _ (hTΩ b)
  have hT2 : IsPGroup 2 T := hR.to_le hTR
  have hYT : Y X ≤ T := by
    rw [hT]
    simpa [conjSubgroup_one] using
      (le_iSup (fun b : ↥B => Y (conjSubgroup X (b : G))) (1 : ↥B))
  have hT0 : T ≠ ⊥ := fun h =>
    hY1 X hX (le_bot_iff.1 (hYT.trans (le_of_eq h)))
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    intro c hc
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hstep : conjSubgroup T c = ⨆ b : ↥B, Y (conjSubgroup X ((b : G) * c)) := by
      rw [hT, conjSubgroup_iSup]
      refine iSup_congr fun b => ?_
      rw [← hYconj (conjSubgroup X (b : G)) (hTΩ b) c (hBA hc), conjSubgroup_conjSubgroup]
    have hreindex : (⨆ b : ↥B, Y (conjSubgroup X ((b : G) * c))) =
        ⨆ b : ↥B, Y (conjSubgroup X (b : G)) := by
      refine Equiv.iSup_congr (Equiv.mulRight ⟨c, hc⟩) ?_
      intro b
      rfl
    rw [hstep, hreindex, hT]
  have hTne : T ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      (hA.isPGroup.to_le hBA) hT2 hT0 hBT
  obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTne
  have hfT : (f : G) ∈ T := (Subgroup.mem_inf.1 f.2).1
  have hfB : (f : G) ∈ Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.1 f.2).2
  have hfR : (f : G) ∈ R := hTR hfT
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR ⟨(f : G), hfR⟩
  have hford : orderOf (f : G) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨(f : G), hfR⟩ : ↥R)).trans hk
  have hf_commA : ∀ a ∈ A, a * (f : G) = (f : G) * a :=
    hrigid (f : G) ⟨k, hford⟩ B hBA hBrel (Subgroup.mem_centralizer_iff.1 hfB)
  let 𝒮 : Finset (Subgroup G) :=
    Finset.univ.image (fun b : ↥B => conjSubgroup X ((b : G) * a₀))
  have h𝒮Ω : ∀ S ∈ 𝒮, S ∈ Ω := by
    intro S hS
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hS
    exact hΩ X hX ((b : G) * a₀) (A.mul_mem (hBA b.2) ha₀A)
  have hf_conjT : (f : G) ∈ conjSubgroup T a₀ := by
    rw [mem_conjSubgroup_iff]
    have hfix : a₀ * (f : G) * a₀⁻¹ = (f : G) := by
      rw [hf_commA a₀ ha₀A]
      group
    rw [hfix]
    exact hfT
  have hconjT_a₀ : conjSubgroup T a₀ = ⨆ S ∈ 𝒮, Y S := by
    have h1 : conjSubgroup T a₀ = ⨆ b : ↥B, Y (conjSubgroup X ((b : G) * a₀)) := by
      rw [hT, conjSubgroup_iSup]
      refine iSup_congr fun b => ?_
      rw [← hYconj (conjSubgroup X (b : G)) (hTΩ b) a₀ ha₀A, conjSubgroup_conjSubgroup]
    rw [h1]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun b => ?_
      exact le_iSup₂ (f := fun S (_ : S ∈ 𝒮) => Y S) (conjSubgroup X ((b : G) * a₀))
        (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
    · refine iSup₂_le fun S hS => ?_
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hS
      exact le_iSup (fun b : ↥B => Y (conjSubgroup X ((b : G) * a₀))) b
  have hz : (f : G) ∈ ⨆ S ∈ 𝒮, Y S := by
    rw [← hconjT_a₀]
    exact hf_conjT
  have hdist : ∀ b b' : ↥B, conjSubgroup X b' ≠ conjSubgroup X ((b : G) * a₀) := by
    intro b b' hEq
    have hmem : (b : G) * a₀ * (b' : G)⁻¹ ∈
        A ⊓ Subgroup.normalizer (X : Set G) := by
      refine ⟨A.mul_mem (A.mul_mem (hBA b.2) ha₀A) (A.inv_mem (hBA b'.2)), ?_⟩
      have h2 : conjSubgroup X ((b : G) * a₀ * (b' : G)⁻¹) = X := by
        rw [← conjSubgroup_conjSubgroup, ← hEq]
        exact E3.conjSubgroup_conj_inv X (b' : G)
      exact conjSubgroup_eq_iff_mem_normalizer.1 h2
    have hmemB : (b : G) * a₀ * (b' : G)⁻¹ ∈ B := hNB hmem
    have ha₀B' : a₀ ∈ B := by
      have h4 : (b : G)⁻¹ * ((b : G) * a₀ * (b' : G)⁻¹) * (b' : G) ∈ B :=
        B.mul_mem (B.mul_mem (B.inv_mem b.2) hmemB) b'.2
      have h5 : (b : G)⁻¹ * ((b : G) * a₀ * (b' : G)⁻¹) * (b' : G) = a₀ := by group
      rwa [h5] at h4
    exact ha₀B ha₀B'
  have hfCS : ∀ S ∈ 𝒮, (f : G) ∈ Subgroup.centralizer (S : Set G) := by
    intro S hS
    have hST : T ≤ Subgroup.centralizer (S : Set G) := by
      rw [hT]
      refine iSup_le fun b => ?_
      have hbΩ : conjSubgroup X (b : G) ∈ Ω := hTΩ b
      have hne : conjSubgroup X (b : G) ≠ S := by
        intro heq
        obtain ⟨b', -, hb'⟩ := Finset.mem_image.1 hS
        exact hdist b' b (heq.trans hb'.symm)
      exact (hYX (conjSubgroup X (b : G)) hbΩ).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (hcomm (conjSubgroup X (b : G)) hbΩ S (h𝒮Ω S hS) hne))
    exact hST hfT
  have hf_eq_one : (f : G) = 1 :=
    eq_one_of_mem_iSup_of_centralizes 𝒮 (fun S => S) Y
      (fun S hS => hYX S (h𝒮Ω S hS))
      (fun S hS S' hS' hne => hcomm S (h𝒮Ω S hS) S' (h𝒮Ω S' hS') hne)
      (fun S hS => hZ S (h𝒮Ω S hS)) hz hfCS
  exact hf1 (Subtype.ext hf_eq_one)

theorem le_normalizer_of_hyperplaneRigid {H L A : Subgroup G} (hH : IsCharacteristicP 2 ↥H)
    (hL : IsBlockOfInX H L) (hnat : ∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule ↥L n)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H) (hrigid : HyperplaneRigid A) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  refine normalizes_of_hyperplaneRigid_of_family (A := A) (R := oTwoIn H)
    (Ω := {X | IsBlockOfInX H X ∧ ∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule ↥X n}) (Y := blockU)
    hA hrigid (isPGroup_oTwoIn H) ?_ ?_ ?_ ?_ ?_ ?_ ?_ L ⟨hL, hnat⟩
  · rintro X ⟨hX, n, hn, hnat⟩ a ha
    exact ⟨isBlockOfInX_conjugate hX (hAH ha), n, hn,
      IsNaturalAltModule.of_mulEquiv ((MulAut.conj a⁻¹).subgroupMap X) hnat⟩
  · rintro X ⟨hX, -⟩ X' ⟨hX', -⟩ hne
    exact distinct_blocks_commute_of_isBlockOfInX hH hX hX' hne
  · rintro X -
    exact blockU_le X
  · rintro X ⟨hX, -⟩
    exact (blockU_le_oTwoIn X).trans (pCoreOf_le_of_isBlockOfInX hX)
  · rintro X ⟨hX, n, hn, hnat⟩
    exact (natAlt_block_facts hX.2.2.1 hn hnat).2.1
  · rintro X ⟨hX, n, hn, hnat⟩
    exact (natAlt_block_facts hX.2.2.1 hn hnat).2.2.1
  · rintro X - a -
    exact (conjSubgroup_blockU X a).symm

theorem normalizer_wClos_le {M V Q : Subgroup G} (hset : Setting11 M V Q) :
    Subgroup.normalizer (E3.wClos V 0 Q : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVcm : V ≤ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hset.isElemAbelian.comm hv hw).symm
  have hVQ : V ≤ Q :=
    Nine.le_of_isSylowOf_of_normal hset.sylowQ hset.isElemAbelian.isPGroup
      (le_inf hset.V_le_M hVcm) (inf_le_left.trans hset.normal)
  have hVmem : V ∈ E3.gammaSet V 0 Q := by
    refine ⟨hVQ, 1, le_of_eq (conjSubgroup_one V).symm, ?_⟩
    rw [conjSubgroup_one]
    exact E3.mQuot_self V
  have hVW : V ≤ E3.wClos V 0 Q := E3.le_wClos hVmem
  have hWne : E3.wClos V 0 Q ≠ ⊥ := fun h =>
    hset.V_ne_bot (le_bot_iff.1 (hVW.trans (le_of_eq h)))
  have hWgrp : IsPGroup 2 (E3.wClos V 0 Q) :=
    hset.sylowQ.2.1.to_le (E3.wClos_le 0 Q)
  refine eleven_b hset.uniqueMax hWne hWgrp ?_
  exact inf_le_left.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) Q)

theorem eleven_seven {M V Q U L : Subgroup G} (hset : Setting11 M V Q)
    (hr : 1 < rMV M V) (hm : 1 < mBar M ⊥ V hset.isElemAbelian) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M) :
    ¬ ∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule ↥L n := by
  rintro ⟨n, hn, hnat⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : IsCharacteristicP 2 ↥(Subgroup.centralizer (U : Set G)) :=
    eleven_e hset.charTwo hU.2.1 (hset.isElemAbelian.isPGroup.to_le hU.1)
  have hQH : IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU
  have hcoreQ : pCoreOf 2 (Subgroup.centralizer (U : Set G)) ≤ Q :=
    Nine.le_of_isSylowOf_of_normal hQH
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer (U : Set G)))
      (Subgroup.map_subtype_le _)
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hkey : ∀ g : G, conjSubgroup V g ≤ Q → ∀ l ∈ L,
      conjSubgroup (conjSubgroup V g) l ≤ Q := by
    intro g hAQ l hl
    have hA : IsElemAbelian 2 (conjSubgroup V g) :=
      E3.isElemAbelian_conjSubgroup hset.isElemAbelian g
    have hAH : conjSubgroup V g ≤ Subgroup.centralizer (U : Set G) := hAQ.trans hQH.1
    have hrigid : HyperplaneRigid (conjSubgroup V g) := hyperplaneRigid_conjSubgroup hset hr hm g
    have hAN : conjSubgroup V g ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_hyperplaneRigid hH hL ⟨n, hn, hnat⟩ hA hAH hrigid
    have hAC : conjSubgroup V g ≤ Subgroup.centralizer (blockU L : Set G) :=
      centralizes_blockU_of_hyperplaneRigid hn hL.2.2.1 hnat hA hAN hrigid
    intro x hx
    have ha : l * x * l⁻¹ ∈ conjSubgroup V g := mem_conjSubgroup_iff.1 hx
    set a : G := l * x * l⁻¹ with ha_def
    set c : G := a⁻¹ * l⁻¹ * a * l with hc_def
    have haA : a ∈ conjSubgroup V g := ha_def ▸ ha
    have hcL : c ∈ L := by
      have h1 : a⁻¹ * l⁻¹ * a ∈ L := by
        have h2 := (Subgroup.mem_normalizer_iff.1
          (hAN ((conjSubgroup V g).inv_mem haA)) l⁻¹).1 (L.inv_mem hl)
        simpa using h2
      have h3 : (a⁻¹ * l⁻¹ * a) * l ∈ L := L.mul_mem h1 hl
      simpa [hc_def] using h3
    have hcC : c ∈ Subgroup.centralizer (blockU L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hlu : l * u * l⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer hl) hu
      have hau : a * (l * u * l⁻¹) = (l * u * l⁻¹) * a :=
        (Subgroup.mem_centralizer_iff.1 (hAC haA) (l * u * l⁻¹) hlu).symm
      have hua : u * a⁻¹ = a⁻¹ * u :=
        Subgroup.mem_centralizer_iff.1 (hAC ((conjSubgroup V g).inv_mem haA)) u hu
      calc u * c = u * (a⁻¹ * l⁻¹ * a * l) := by rw [hc_def]
        _ = (u * a⁻¹) * (l⁻¹ * a * l) := by group
        _ = (a⁻¹ * u) * (l⁻¹ * a * l) := by rw [hua]
        _ = a⁻¹ * u * l⁻¹ * a * l := by group
        _ = a⁻¹ * l⁻¹ * ((l * u * l⁻¹) * a) * l := by group
        _ = a⁻¹ * l⁻¹ * (a * (l * u * l⁻¹)) * l := by rw [hau]
        _ = (a⁻¹ * l⁻¹ * a * l) * u := by group
        _ = c * u := by rw [hc_def]
    have hcCore : c ∈ pCoreOf 2 L :=
      (natAlt_block_facts hL.2.2.1 hn hnat).2.2.2 (Subgroup.mem_inf.2 ⟨hcL, hcC⟩)
    have hcQ : c ∈ Q := hcoreQ ((pCoreOf_le_of_isBlockOfInX hL) hcCore)
    have haQ : a ∈ Q := hAQ haA
    have hxQ : x ∈ Q := by
      have hxac : x = a * c := by rw [hc_def, ha_def]; group
      rw [hxac]
      exact Q.mul_mem haQ hcQ
    exact hxQ
  let W₀ : Subgroup G := E3.wClos V 0 Q
  have hVpg : IsPGroup 2 V := hset.isElemAbelian.isPGroup
  have hWlem : ∀ l ∈ L, W₀ ≤ conjSubgroup W₀ l⁻¹ := by
    intro l hl
    refine E3.wClos_le_of_forall fun A' hA' => ?_
    obtain ⟨hA'Q, g, hA'g, hmq0⟩ := hA'
    have hA'gpg : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup hVpg g
    have hA'eq : A' = conjSubgroup V g := (E3.mQuot_eq_zero_iff hA'gpg hA'g).1 hmq0
    have hkeyg : conjSubgroup (conjSubgroup V g) l ≤ Q := hkey g (hA'eq ▸ hA'Q) l hl
    have hmemγ : conjSubgroup (conjSubgroup V g) l ∈ E3.gammaSet V 0 Q := by
      refine ⟨hkeyg, g * l, ?_, ?_⟩
      · rw [conjSubgroup_conjSubgroup]
      · rw [conjSubgroup_conjSubgroup, E3.mQuot_self]
    have hleW : conjSubgroup (conjSubgroup V g) l ≤ W₀ := E3.le_wClos hmemγ
    refine (E3.conjSubgroup_le_iff_le_inv l).1 ?_
    rwa [hA'eq]
  have hLN : L ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro l hl
    have h1 : conjSubgroup W₀ l ≤ W₀ :=
      (E3.conjSubgroup_le_iff_le_inv l).2 (hWlem l hl)
    have h2 : W₀ ≤ conjSubgroup W₀ l := by
      have := hWlem l⁻¹ (L.inv_mem hl)
      simpa using this
    exact conjSubgroup_eq_iff_mem_normalizer.1 (le_antisymm h1 h2)
  exact hLM (hLN.trans (normalizer_wClos_le hset))

theorem one_lt_rMV_and_one_lt_mBar {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h116 : (mBar M ⊥ V hV : ℕ∞) ≤ 2 * rMV M V) (h2 : 2 < mBar M ⊥ V hV) :
    1 < rMV M V ∧ 1 < mBar M ⊥ V hV := by
  refine ⟨?_, by omega⟩
  by_contra hr
  replace hr := not_lt.mp hr
  have h1 : 2 * rMV M V ≤ 2 * 1 := by gcongr
  have h3 : (mBar M ⊥ V hV : ℕ∞) ≤ 2 := by simpa using h116.trans h1
  have h4 : mBar M ⊥ V hV ≤ 2 := by exact_mod_cast h3
  omega

theorem eleven_eight {M V Q U L : Subgroup G} (hset : Setting11 M V Q)
    (hr : 1 < rMV M V) (hm : 1 < mBar M ⊥ V hset.isElemAbelian) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M) :
    ∃ n : ℕ, 1 < n ∧ IsNaturalSLTwoModule ↥L n := by
  have hX : InClassX ↥L := hL.2.2
  rcases hX.2 with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
  · exact absurd ⟨n, hn, hnat⟩ (eleven_seven hset hr hm hU hL hLM)
  · refine ⟨n, ?_, hnat⟩
    rcases Nat.lt_or_ge 1 n with h | h
    · exact h
    · obtain rfl : n = 1 := by omega
      exact absurd hnat (CFSG.CGT.PushingUp.not_isNaturalSLTwoModule_one hX.1)

end CFSG.LocalAnalysis.WeakClosure81
