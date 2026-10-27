module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414
public import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF1418MJProof

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup

@[expose] def KF1418MJModel (X : Type) [Group X] : Prop :=
  ∀ V T : Subgroup X, Nat.card V = 9 → IsPGroup 2 T → T ≠ ⊥ →
    V ≤ normalizer (T : Set X) →
      ∃ v ∈ V, ¬ V ≤ centralizer
        (inSubgroup (CFSG.pCore 2) (centralizer ({v} : Set X)) : Set X)

theorem eq_one_of_sq_of_pow_nine {M : Type*} [Monoid M] {g : M} (h2 : g ^ 2 = 1)
    (h9 : g ^ 9 = 1) : g = 1 := by
  have e : g ^ 9 = (g ^ 2) ^ 4 * g := by
    rw [← pow_mul, ← pow_succ]
  rw [h9, h2, one_pow, one_mul] at e
  exact e.symm

theorem not_le_centralizer_pCore_of_equiv {X : Type} [Group X] [Finite X] {V : Subgroup X}
    (hV : Nat.card V = 9) {a : X} (haV : a ∈ V)
    (ψ : normalizer (zpowers a : Set X) ≃* S3A4) :
    ¬ V ≤ centralizer (inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set X)) : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := normalizer (zpowers a : Set X)
  set C := centralizer ({a} : Set X)
  have hVc : IsMulCommutative V :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hV]; norm_num)
  have hCN : C ≤ N := fun g hg =>
    mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hg)
  have hVC : V ≤ C := fun v hv => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hVc.is_comm.comm ⟨v, hv⟩ ⟨a, haV⟩))
  have hVN : V ≤ N := hVC.trans hCN
  have ha9 : a ^ 9 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard V haV
    rw [hV] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have h4 : Nat.card (Fin 4) = 4 := by simp
  haveI : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4
  set W : Subgroup S3A4 :=
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4))
  have hWn : W.Normal := Subgroup.prod_normal _ _
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hw
    have e1 : w.1 = 1 := Subgroup.mem_bot.mp h1
    have e2 : w.2 ^ 2 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨w.2, h2⟩ : alternatingGroup.kleinFour (Fin 4))
      rw [alternatingGroup.exponent_kleinFour_of_card_eq_four h4] at h
      simpa using congrArg Subtype.val h
    exact Prod.ext (by simp [e1]) (by simpa using e2)
  obtain ⟨⟨k, hk⟩, hk1⟩ : ∃ k : alternatingGroup.kleinFour (Fin 4), k ≠ 1 := by
    have hne : alternatingGroup.kleinFour (Fin 4) ≠ ⊥ := by
      intro h
      have h' := alternatingGroup.kleinFour_card_of_card_eq_four h4
      rw [h, Subgroup.card_bot] at h'
      norm_num at h'
    exact Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  set Q : Subgroup X := (W.comap ψ.toMonoidHom).map N.subtype
  have hQN : Q ≤ N := Subgroup.map_subtype_le _
  have hmemQ : ∀ q ∈ Q, ∃ hq : q ∈ N, ψ ⟨q, hq⟩ ∈ W := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  have hQsq : ∀ q ∈ Q, q ^ 2 = 1 := by
    intro q hq
    obtain ⟨hqN, hqW⟩ := hmemQ q hq
    have h1 : ψ ((⟨q, hqN⟩ : N) ^ 2) = 1 := by
      rw [map_pow]
      exact hW2 _ hqW
    have h2 : (⟨q, hqN⟩ : N) ^ 2 = 1 := ψ.injective (h1.trans (map_one ψ).symm)
    simpa using congrArg Subtype.val h2
  have hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := by
    intro n hn q hq
    obtain ⟨hqN, hqW⟩ := hmemQ q hq
    refine ⟨⟨n, hn⟩ * ⟨q, hqN⟩ * ⟨n, hn⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv]
    exact hWn.conj_mem _ hqW _
  have hNQ' : N ≤ normalizer (Q : Set X) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hNQ n hn q, fun h => ?_⟩
    have h' := hNQ n⁻¹ (inv_mem hn) _ h
    rwa [show n⁻¹ * (n * q * n⁻¹) * n⁻¹⁻¹ = q by group] at h'
  have hQC : Q ≤ C := by
    intro q hq
    have haN : a ∈ N := Subgroup.le_normalizer (Subgroup.mem_zpowers a)
    have hqN := hQN hq
    have hcz : q * a * q⁻¹ * a⁻¹ ∈ zpowers a :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hqN a).mp (Subgroup.mem_zpowers a))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
    have hcQ : q * a * q⁻¹ * a⁻¹ ∈ Q := by
      have h1 := Subgroup.mul_mem _ hq (hNQ a haN _ (Subgroup.inv_mem _ hq))
      rwa [show q * (a * q⁻¹ * a⁻¹) = q * a * q⁻¹ * a⁻¹ by group] at h1
    have hc2 := hQsq _ hcQ
    have hc9 : (q * a * q⁻¹ * a⁻¹) ^ 9 = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha9, one_zpow]
    have hc1 : q * a * q⁻¹ * a⁻¹ = 1 := eq_one_of_sq_of_pow_nine hc2 hc9
    have hqa : q * a * q⁻¹ = a := mul_inv_eq_one.mp hc1
    refine mem_centralizer_singleton_iff.mpr ?_
    calc q * a = q * a * q⁻¹ * q := by group
      _ = a * q := by rw [hqa]
  have hQO : Q ≤ inSubgroup (CFSG.pCore 2) C := by
    intro q hq
    refine ⟨⟨q, hQC hq⟩, ?_, rfl⟩
    have hn : (Q.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr (hCN.trans hNQ')
    have hp : IsPGroup 2 (Q.subgroupOf C) := fun g => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      have h := hQsq _ (Subgroup.mem_subgroupOf.mp g.2)
      simpa using h⟩
    exact (le_sSup (show Q.subgroupOf C ∈ {K : Subgroup C | K.Normal ∧ IsPGroup 2 K} from
      ⟨hn, hp⟩)) (Subgroup.mem_subgroupOf.mpr hq)
  intro hle
  have hVQ : ∀ v ∈ V, ∀ q ∈ Q, q * v = v * q := fun v hv q hq =>
    Subgroup.mem_centralizer_iff.mp (hle hv) q (hQO hq)
  set S : Subgroup S3A4 := (V.subgroupOf N).map ψ.toMonoidHom with hS
  have hS9 : Nat.card S = 9 := by
    rw [hS, Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hV]
  have hWS : W ≤ centralizer (S : Set S3A4) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hq : ((ψ.symm w : N) : X) ∈ Q := ⟨ψ.symm w, by
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      exact hw, rfl⟩
    have h1 := hVQ v (Subgroup.mem_subgroupOf.mp hv) _ hq
    have h2 : ψ.symm w * v = v * ψ.symm w := Subtype.ext h1
    have h3 := congrArg ψ h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  have hWleS : W ≤ S := hWS.trans (centralizer_le_of_card_nine S hS9)
  have hw0 : ((1 : Equiv.Perm (Fin 3)), k) ∈ W :=
    Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hk⟩
  have h9 : ((1 : Equiv.Perm (Fin 3)), k) ^ 9 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard S (hWleS hw0)
    rw [hS9] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have h2 := hW2 _ hw0
  have h1 : ((1 : Equiv.Perm (Fin 3)), k) = 1 := eq_one_of_sq_of_pow_nine h2 h9
  exact hk1' (congrArg Prod.snd h1)

theorem exists_mem_not_mem_of_card_nine {X : Type} [Group X] [Finite X] {B Z : Subgroup X}
    (hB : Nat.card B = 9) (hZ : Nat.card Z = 3) : ∃ a ∈ B, a ∉ Z := by
  by_contra hall
  push Not at hall
  have h := Subgroup.card_le_of_le (show B ≤ Z from hall)
  rw [hB, hZ] at h
  norm_num at h

theorem kf1418MJModel_of_m12
    (X : Type) [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.M12)) : KF1418MJModel X := by
  intro V T hV9 hT2 hT1 hVT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : IsPGroup 3 V := IsPGroup.of_card (n := 2) (by rw [hV9]; norm_num)
  obtain ⟨P, hVP⟩ := hV3.exists_le_sylow
  obtain ⟨hex, -, -, -, -, -, -, E, F, A, A', hset, -, -, -, -, -, ⟨eE⟩, ⟨eF⟩, -, -, -, -,
    hNa, hNa'⟩ := Toolkit.m12ThreeLocalData X hX P
  have hZ3 : Nat.card ((center (P : Subgroup X)).map (P : Subgroup X).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective]
    exact hex.2.2.2
  obtain ⟨a, haV, haZ⟩ := exists_mem_not_mem_of_card_nine hV9 hZ3
  have hVmem : V ∈ ({E, F, A, A'} : Set (Subgroup X)) := hset ▸ ⟨hVP, hV9⟩
  have hsig : ∀ B : Subgroup X, B = V →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* GL (Fin 2) (ZMod 3)) → False := by
    rintro B rfl ⟨eB⟩
    have h := (Sec4.Sporadic.rank3II_4_14_signalizer X hX P B hVP hV9).1
      ⟨(Sec4.Sporadic.automizerEquivAutIn B).symm.trans eB⟩
    have hT : T ∈ invariantPiSubgroups ⊤ B (piOf 2) :=
      ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2, hVT⟩
    rw [h] at hT
    exact hT1 hT
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVmem
  rcases hVmem with h | h | h | h
  · exact (hsig E h.symm ⟨eE⟩).elim
  · exact (hsig F h.symm ⟨eF⟩).elim
  · obtain ⟨ψ⟩ := hNa a (h ▸ haV) haZ
    exact ⟨a, haV, not_le_centralizer_pCore_of_equiv hV9 haV ψ⟩
  · obtain ⟨ψ⟩ := hNa' a (h ▸ haV) haZ
    exact ⟨a, haV, not_le_centralizer_pCore_of_equiv hV9 haV ψ⟩

theorem kf1418MJModel_of_j2
    (X : Type) [Group X]
    [Finite X] (hX : Nonempty (X ≃* NativeSporadic.J2)) : KF1418MJModel X := by
  intro V T hV9 _ _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : IsPGroup 3 V := IsPGroup.of_card (n := 2) (by rw [hV9]; norm_num)
  obtain ⟨P, hVP⟩ := hV3.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  have hZ3 : Nat.card ((P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) :
      Subgroup X) = 3 := by
    rw [Sec4.Sporadic.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective]
    exact hHeis.1.2.2.2
  obtain ⟨a, haV, haZ⟩ := exists_mem_not_mem_of_card_nine hV9 hZ3
  obtain ⟨-, ⟨ψ⟩, -⟩ := h4 V ⟨hVP, hV9⟩ a haV haZ
  exact ⟨a, haV, not_le_centralizer_pCore_of_equiv hV9 haV ψ⟩

end CFSG.RankThree.PartTwo.KFacts.KF1418MJProof
