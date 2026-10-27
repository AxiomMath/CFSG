module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofRQK
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

omit [Finite G] in
theorem big152_of_le {X K : Subgroup G} (hXK : X ≤ K) (hX : Big152 X) : Big152 K := by
  set φ : ↥X →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hXK) with hφ
  have hker : φ.ker ≤ CFSG.pCore 2 ↥X := by
    intro x hx
    have hxK : Subgroup.inclusion hXK x ∈ CFSG.pCore 2 ↥K := by
      rwa [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
    have hxX : (x : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 K :=
      Subgroup.mem_inf.mpr ⟨x.2, ⟨_, hxK, rfl⟩⟩
    obtain ⟨y, hy, hyx⟩ := CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXK hxX
    rwa [show y = x from Subtype.ext hyx] at hy
  have hdvd : (CFSG.pCore 2 ↥X).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker] at hdvd
  exact hX.trans (hdvd.trans (Subgroup.card_subgroup_dvd_card _))

theorem big152_k {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) (hX : Big152 X) :
    Big152 K :=
  big152_of_le hC.le_k hX

theorem n155_mem_maximalTwoLocalsContaining_big (h153 : Ronan153Big.Item153Big A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K) :
    n155 A K ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) := by
  rw [(h153 K hK hKb).1]
  exact Set.mem_singleton _

theorem normalizer_le_n155w_big (h153 : Ronan153Big.Item153Big A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K) :
    Subgroup.normalizer (K : Set G) ≤ n155 A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : CFSG.Open.pCoreOf 2 K ≠ ⊥ := hK.prop.2.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK.prop.1.1.2
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K) hK2
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle ((sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hAK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))) hx)⟩
  rw [(h153 K hK hKb).1, Set.mem_singleton_iff] at hmem
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K).trans (hle.trans hmem.le)

theorem le_n155_of_isPLocal_big (h153 : Ronan153Big.Item153Big A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K) {H₀ : Subgroup G} (hH : IsPLocal 2 H₀)
    (hKA : K ⊔ A ≤ H₀) : H₀ ≤ n155 A K := by
  obtain ⟨M', hle, hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hH
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hle (hKA hx)⟩
  rw [(h153 K hK hKb).1, Set.mem_singleton_iff] at hmem
  exact hle.trans hmem.le

theorem claim155_of_le_normalizer_big (h153 : Ronan153Big.Item153Big A (lB A))
    {K Y : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K)
    (hKR : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
    (hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) : Claim155 A K Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro C hC1 hCR hCc
  have hNC : Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h' := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := CFSG.Open.pCoreOf 2 Y) (C.subgroupOf (CFSG.Open.pCoreOf 2 Y))
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h'
  have hC2 : IsPGroup 2 C := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y).to_le hCR
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hC2 hC1
  exact (delta_le _).trans (le_n155_of_isPLocal_big h153 hK hKb hloc (sup_le (hKR.trans hNC)
    (hAR.trans hNC)))

theorem le_normalizer_of_isPerfect_of_le_n155_big (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A)) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K) {J : Subgroup G}
    (hJp : Group.IsPerfect ↥J) (hJN : J ≤ n155 A K) : J ≤ Subgroup.normalizer (K : Set G) :=
  Ronan152Six.le_normalizer_of_isPerfect_of_le_big h h152 hK hKb
    (n155_mem_maximalTwoLocalsContaining_big h153 hK hKb) hJp hJN

theorem le_of_le_n155'_big (h : Sec14Std G A c L) (h152 : Item152Big A (lB A))
    (h153 : Ronan153Big.Item153Big A (lB A)) {K X J : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K) (hX4 : X ∈ scriptY4 A (lB A))
    (hJ0 : J ∈ scriptY0 A (lB A)) (hXJ : X ≤ J) (hXK : X ≤ K) (hJN : J ≤ n155 A K) : J ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJNK : J ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_isPerfect_of_le_n155_big h h152 h153 hK hKb
      (isPerfect_of_mem_scriptY4 hJ0.1) hJN
  have hq : IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := hJ0.1.2.2.2
  set O := CFSG.pCore 2 ↥J with hO
  set V := (J ⊓ K).subgroupOf J with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (Late.le_normalizer_inf Subgroup.le_normalizer hJNK)
  have hVmap : (V.map (QuotientGroup.mk' O)).Normal := hVn.map _ (QuotientGroup.mk'_surjective O)
  have hXV : X.subgroupOf J ≤ V := fun x hx => Subgroup.mem_subgroupOf.mpr
    ⟨x.2, hXK (Subgroup.mem_subgroupOf.mp hx)⟩
  have hJle : J ≤ (J ⊓ K) ⊔ CFSG.Open.pCoreOf 2 J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hVmap with htop | hcen
    · have hsup : V ⊔ O = ⊤ := by
        have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) V
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
        exact h1.symm
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥J) ∈ V ⊔ O := hsup ▸ Subgroup.mem_top _
      rw [Subgroup.mem_sup_of_normal_left] at hx'
      obtain ⟨v, hv, o, ho, hvo⟩ := hx'
      have hvG : (v : G) ∈ J ⊓ K := Subgroup.mem_subgroupOf.mp hv
      have hoG : (o : G) ∈ CFSG.Open.pCoreOf 2 J := (mem_pCoreOf_iff155 o).mpr ho
      have hxe : x = (v : G) * (o : G) := by
        have := congrArg Subtype.val hvo
        simpa using this.symm
      rw [hxe]
      exact mul_mem (Subgroup.mem_sup_left hvG) (Subgroup.mem_sup_right hoG)
    · exfalso
      have hNs : Group.IsSolvable O := by
        have := (CFSG.pCore_isPGroup : IsPGroup 2 O).isNilpotent
        infer_instance
      have hKs := isSolvable_comap_center O hNs
      have hVK : V ≤ (Subgroup.center (↥J ⧸ O)).comap (QuotientGroup.mk' O) :=
        fun x hx => hcen (Subgroup.mem_map_of_mem _ hx)
      have hXs : Group.IsSolvable (X.subgroupOf J) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hXV.trans hVK))
          (Subgroup.inclusion_injective _)
      have hXs' : Group.IsSolvable ↥X := Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hXJ).toMonoidHom) (MulEquiv.surjective _)
      have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX4
      have : Nontrivial ↥X :=
        (Subgroup.nontrivial_iff_ne_bot X).mpr (ne_bot_of_mem_scriptY4 hX4)
      exact Group.IsPerfect.not_isSolvable ↥X hXs'
  have hOK : CFSG.Open.pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJNK
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 J)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J)
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  calc J = oPrimeResidualOf 3 J := hJ0.1.2.1
    _ ≤ K := by
      rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
      rintro x ⟨hx, k, hk⟩
      have hle' : (J ⊓ K) ⊔ CFSG.Open.pCoreOf 2 J ≤ K ⊔ CFSG.Open.pCoreOf 2 J :=
        sup_le_sup_right inf_le_right _
      have hx' : x ∈ K ⊔ CFSG.Open.pCoreOf 2 J := hle' (hJle hx)
      exact mem_left_of_pow_prime_pow Nat.prime_three hOK hcop hx' hk

theorem le_normalizer_of_isPGroup_of_le_normalizer_big (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    {K X D : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hKb : Big152 K)
    (hXp : Group.IsPerfect ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K) (hD2 : IsPGroup 2 D)
    (hDN : D ≤ n155 A K) (hXD : X ≤ Subgroup.normalizer (D : Set G)) :
    D ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  set N := n155 A K with hN
  have hXN : X ≤ N :=
    hXK.trans (Subgroup.le_normalizer.trans (normalizer_le_n155w_big h153 hK hKb))
  set Xy := X.map (MulAut.conj y).toMonoidHom with hXy
  have hXyp : Group.IsPerfect ↥Xy := by
    have := hXp
    exact Group.IsPerfect.map (MulAut.conj y).toMonoidHom
  have hXy1 : Xy ≠ ⊥ := fun h0 =>
    hX1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y).injective).mp h0)
  have hyD : y ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hy
  have hXyN : Xy ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (hDN hy) (hXN hx)) (inv_mem (hDN hy))
  have hXyXD : Xy ≤ X ⊔ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hx))
      (inv_mem (Subgroup.mem_sup_right hy))
  have hXyD : Xy ≤ Subgroup.normalizer (D : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hyD (hXD hx)) (inv_mem hyD)
  set W := X ⊔ Xy with hW
  have hWp : Group.IsPerfect ↥W := Proof155w2.isPerfect_sup hXp hXyp
  have hWN : W ≤ N := sup_le hXN hXyN
  have hWK : W ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_isPerfect_of_le_n155_big h h152 h153 hK hKb hWp hWN
  have hWD : W ≤ Subgroup.normalizer (D : Set G) := sup_le hXD hXyD
  have hWXD : W ≤ X ⊔ (W ⊓ D) :=
    Proof155w.le_sup_inf_of_le hXD le_sup_left (sup_le le_sup_left hXyXD)
  have hWDs : Group.IsSolvable ↥(W ⊓ D) := by
    have : Group.IsNilpotent ↥(W ⊓ D) := (hD2.to_le inf_le_right).isNilpotent
    infer_instance
  have hWleK : W ≤ K := Sec17.Proof171Steps.le_of_isPerfect_of_le_sup hWp le_sup_left
    (Late.le_normalizer_inf Subgroup.le_normalizer hWD) hWDs inf_le_left hWXD hXK hWK
  have hXyK : Xy ≤ K := le_sup_right.trans hWleK
  have hK𝓛 : K ∈ thetaComponentsIn N :=
    Ronan152Six.mem_thetaComponentsIn_of_big h h152 hK hKb
      (n155_mem_maximalTwoLocalsContaining_big h153 hK hKb)
  have hyN : y ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer (hDN hy)
  have hKy𝓛 := map_conj_mem_thetaComponentsIn hyN hK𝓛
  have hXyKy : Xy ≤ K.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono hXK
  have heq := Sec6.eq_of_mem_thetaComponentsIn_of_le hK𝓛 hKy𝓛 hXyp hXy1 hXyK hXyKy
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
