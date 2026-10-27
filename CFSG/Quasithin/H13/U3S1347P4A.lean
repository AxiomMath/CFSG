module

public import CFSG.Quasithin.H13.U3S132210B
public import CFSG.Quasithin.H13.U3S1347N
public import CFSG.Quasithin.H13.U3S1347U
public import CFSG.Quasithin.H13.U3S1348K

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

theorem c2_comm_not_inD6 : ∀ σ : Perm (Fin 6), InD6 σ → ¬ InE8 σ →
    ¬ InD6 (c2perm * σ * c2perm⁻¹ * σ⁻¹) := by
  decide +kernel

theorem c2perm_not_inD6 : ¬ InD6 c2perm := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_H2_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) :
    H₂ = oTwoRes H₂ ⊔ T :=
  le_antisymm (le_oTwoRes_sup_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1))
    (sup_le (oTwoRes_le _) h.inH₂.1)

theorem s1347_a6_of_K2 (h1332 : Stmt13_3_2)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂ : oTwoRes H₂ = l2Of S) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  rcases a6_or_hatA6_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) h5 (s134_isA6On S) with
    he | hhat
  · exact he
  exfalso
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcl0
  have hcC : c ∈ centralizer (V : Set G) := s134_o2Z_le_centralizer S hcZ
  have hcN : c ∈ normalizer (V : Set G) := S.frame.L_le (o2Z_le_L hcZ)
  have hcH : c ∈ H₂ := by
    have hcL2 : c ∈ l2Of S := by
      refine A6.oTwoRes_mono (fun y hy => mem_inf.2 ⟨o2Z_le_L hy, ?_⟩) hcl0
      exact centralizer_le_normalizer _ (centralizer_le
        (SetLike.coe_subset_coe.2 (S.pre_le_V _)) (s134_o2Z_le_centralizer S hy))
    rw [← hK₂] at hcL2
    exact oTwoRes_le _ hcL2
  set P : Subgroup G := (D6sub.comap S.frame.ρ).map (normalizer (V : Set G)).subtype with hP
  have hTP : T ≤ P := fun t ht => ⟨⟨t, S.frame.T_le ht⟩, S.frame.T_D _ ht, rfl⟩
  have hcP : c ∈ P := by
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    show S.frame.ρ ⟨c, hcN⟩ ∈ D6sub
    rw [(s134_rho_eq_one_iff S ⟨c, hcN⟩).2 hcC]
    exact one_mem _
  set X := T ⊔ zpowers c with hX
  have hXP : X ≤ P := sup_le hTP (zpowers_le.2 hcP)
  have hXH : X ≤ H₂ := sup_le h.inH₂.1 (zpowers_le.2 hcH)
  have h3 := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hm := relIndex_mul_relIndex T X H₂ le_sup_left hXH
  rw [h3] at hm
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h1 | h1
  ·
    have hcT : c ∈ T := relIndex_eq_one.1 h1 (mem_sup_right (mem_zpowers c))
    apply hcO
    have hco : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.h13.sylow.1) ⟨c, hcT⟩
    have hk' : orderOf c = 2 ^ k := (Subgroup.orderOf_coe ⟨c, hcT⟩).trans hk
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans (hk' ▸ hco)
      omega
    have hc1 : c = 1 := orderOf_eq_one_iff.1 (by rw [hk', hk0, pow_zero])
    rw [hc1]
    exact one_mem _
  ·
    rw [h1] at hm
    have h2 : X.relIndex H₂ = 1 := by omega
    obtain ⟨y, hyL2, hyN, hyρ⟩ := s134_exists_c2_mem_L2 S
    rw [← hK₂] at hyL2
    obtain ⟨y', hy', hyy'⟩ := hXP (relIndex_eq_one.1 h2 (oTwoRes_le _ hyL2))
    have e : y' = ⟨y, hyN⟩ := Subtype.ext hyy'
    have hD : InD6 (S.frame.ρ y') := hy'
    rw [e, hyρ] at hD
    exact c2perm_not_inD6 hD

theorem s1347_not_charNormal (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) : ¬ CharNormal (baum T) (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨C, hCB, hC1, hCchar, hCN⟩
  have hred := s1347_reduced S hH₀
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hJQ : thompsonJ T ≤ pCoreOf 2 (H₁ ⊔ H₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans hH₀.1) hJ
      (S.h13.sylow.1.to_le hJT)
  have hQ := s1347_T_inf_centralizer S h hH₀
  have hbaum : baum T = baum (pCoreOf 2 (H₁ ⊔ H₂)) := by
    rw [← hQ]
    exact baum_eq_baum_centralizer hred.2.2.1 (s1347_V0_le_T S hH₀) (by rw [hQ]; exact hJQ)
  rw [hbaum] at hCB hCchar
  have h2 : normalizer (baum (pCoreOf 2 (H₁ ⊔ H₂)) : Set G) ≤ normalizer (C : Set G) := by
    have h3 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (baum (pCoreOf 2 (H₁ ⊔ H₂))))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCB] at h3
  have hH₀C : H₁ ⊔ H₂ ≤ normalizer (C : Set G) :=
    (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂)).trans ((normalizer_le_normalizer_baum _).trans h2)
  have hCT : C ≤ T := hCB.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl₀))
  exact hH₀M (hH₀C.trans (s134_normalizer_le_M S hC1 (S.h13.sylow.1.to_le hCT) hCN))

theorem s1347_J1_le_centralizer_V2 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hK₂ : oTwoRes H₂ = l2Of S)
    (hJ1 : H₁ ⊔ H₂ ≤ normalizer (thompsonJi T 1 : Set G)) :
    thompsonJi T 1 ≤ centralizer (v2Of S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJi T 1 ≤ T := iSup₂_le fun A hA => hA.1
  have hH2 : H₂ = l2Of S ⊔ T := by rw [← hK₂]; exact s1347_H2_eq S h
  have hJR : thompsonJi T 1 ≤ pCoreOf 2 (l2Of S ⊔ T) := by
    rw [← hH2]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans h.inH₂.1)
      (le_sup_right.trans hJ1) (S.h13.sylow.1.to_le hJT)
  rw [s134_pCoreOf_L2T S he] at hJR
  exact hJR.trans inf_le_right

theorem s1347_comm_J1 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂ : oTwoRes H₂ = l2Of S) (hIII : ¬ thompsonJi T 1 ≤ centralizer (v2Of S : Set G)) :
    ⁅oTwoRes H₂, thompsonJi T 1⁆ = oTwoRes H₂ := by
  set J := thompsonJi T 1 with hJdef
  have hJT : J ≤ T := iSup₂_le fun A hA => hA.1
  have hTK : T ≤ normalizer (oTwoRes H₂ : Set G) := by rw [hK₂]; exact s134_T_le_normalizer_L2 S
  have hTJ : T ≤ normalizer (J : Set G) :=
    le_normalizer_thompsonJi_of le_rfl le_normalizer fun A hA => hA.1
  set N := ⁅oTwoRes H₂, J⁆ with hN
  have hNK : N ≤ oTwoRes H₂ := le_normalizer_iff_commutator_le_left.mp (hJT.trans hTK)
  have hTN : T ≤ normalizer (N : Set G) := A5.le_normalizer_commutator hTK hTJ
  have hNH : N ⊔ T ≤ H₂ := sup_le (hNK.trans (oTwoRes_le _)) h.inH₂.1
  have h3 := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hm := relIndex_mul_relIndex T (N ⊔ T) H₂ le_sup_right hNH
  rw [h3] at hm
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h1 | h1
  ·
    exfalso
    have hNT : N ≤ T := le_sup_left.trans (relIndex_eq_one.1 h1)
    obtain ⟨j, hjJ, hjC⟩ := IsConcreteLE.not_le_iff_exists.1 hIII
    obtain ⟨c, hcK, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
    rw [← hK₂] at hcK
    have hjT := hJT hjJ
    have hjN := S.frame.T_le hjT
    have hcomm : c * j * c⁻¹ * j⁻¹ ∈ T := hNT (commutator_mem_commutator hcK hjJ)
    have hD := S.frame.T_D ⟨_, S.frame.T_le hcomm⟩ hcomm
    have e : (⟨c * j * c⁻¹ * j⁻¹, S.frame.T_le hcomm⟩ : ↥(normalizer (V : Set G))) =
        ⟨c, hcN⟩ * ⟨j, hjN⟩ * (⟨c, hcN⟩)⁻¹ * (⟨j, hjN⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcρ] at hD
    have hjE : ¬ InE8 (S.frame.ρ ⟨j, hjN⟩) := fun hE =>
      hjC (s134_mem_centralizer_V2_of_inE8 S ⟨j, hjN⟩ hE)
    exact c2_comm_not_inD6 _ (S.frame.T_D ⟨j, hjN⟩ hjT) hjE hD
  ·
    rw [h1] at hm
    have h2 : (N ⊔ T).relIndex H₂ = 1 := by omega
    refine le_antisymm hNK ?_
    calc oTwoRes H₂ ≤ oTwoRes (N ⊔ T) := oTwoRes_mono' (relIndex_eq_one.1 h2)
      _ ≤ N := oTwoRes_sup_le' S.h13.sylow.1 hTN

end CFSG.Quasithin.H13.U3
