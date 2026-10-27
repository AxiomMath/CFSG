module

public import CFSG.Quasithin.H13.L32A715a
public import CFSG.Quasithin.H13.NQCoreP134
public import CFSG.Quasithin.H13.L32A714a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem commutator_sup_pCoreOf_eq_o2z {K : Subgroup G}
    (hP : IsPOnePlusTwo 3 (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) :
    ⁅K, K⁆ ⊔ pCoreOf 2 K = o2z K := by
  have hQK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hQZ : pCoreOf 2 K ≤ o2z K := fun q hq => mem_o2z_iff.mpr ⟨hQK hq, fun y hy => by
    have h1 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hy) _).mp (inv_mem hq)
    rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
    exact mul_mem hq h1⟩
  apply le_antisymm
  · refine sup_le ?_ hQZ
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact comm_mem_o2z hP x hx y hy
  · refine o2z_le_of_comm_mem hP le_sup_right fun x hx y hy => ?_
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy)

theorem exists_sylow_three_K
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsPGroup 3 ↥P ∧ Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  have hP := isPOnePlusTwo_K hK
  have hidx : (pCoreOf 2 K).relIndex K = 27 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hP.2.1]
    norm_num
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 K).exists_card_eq
  have hcardK : Nat.card K = 2 ^ a * 27 := by
    have h1 := Subgroup.card_mul_index ((pCoreOf 2 K).subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 K)).toEquiv, ha,
      ← Subgroup.relIndex, hidx] at h1
    exact h1.symm
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥K))
  refine ⟨(S : Subgroup ↥K).map K.subtype, Subgroup.map_subtype_le _,
    (S.isPGroup').map _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity, hcardK]
  have h1 : (2 ^ a * 27).factorization 3 = 3 := by
    rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num),
      show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]
  rw [h1]
  norm_num

theorem isXi_K (h331 : Stmt3_3_1) (hThm : Thm14_5_3) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H)
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    IsXi T (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL1eq, -, hirr, -⟩ := lemma14_7_15_one h331 hThm h1222 h1332 h1334 S hK
  set K := oTwoUpper H with hKdef
  have hP := isPOnePlusTwo_K hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hKH : K ≤ H := oTwoUpper_le H
  have hQK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hQZ : pCoreOf 2 K ≤ o2z K := by
    rw [← commutator_sup_pCoreOf_eq_o2z hP]
    exact le_sup_right
  have hZ3 : ∀ z ∈ o2z K, z ^ 3 ∈ pCoreOf 2 K := fun z hz =>
    pow_three_mem_K hK z (o2z_le K hz)
  have hfrat : ⁅K, K⁆ ⊔ pCoreOf 2 K = l1 T L V ⊔ pCoreOf 2 K := by
    rw [commutator_sup_pCoreOf_eq_o2z hP, hL1eq]
    exact (oTwoUpper_sup_pCoreOf_eq hQZ hZ3).symm
  refine ⟨(oTwoUpper_oTwoUpper H).symm, hTK, ?_, 3, Nat.prime_three, by norm_num,
    pow_three_mem_K hK, Or.inr ⟨?_, ?_⟩, ?_⟩
  ·
    have hQH : pCoreOf 2 H ≤ pCoreOf 2 (K ⊔ T) := by
      exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le S.hyp hTH).trans le_sup_right)
        ((sup_le hKH hTH).trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    intro hb
    exact S.hz.1.2 (eq_bot_iff.mpr (hb ▸ hQH))
  · rw [Subgroup.relIndex, Subgroup.index_eq_card, hP.2.1]
  · intro hle
    obtain ⟨a, b, hab⟩ := Heis.exists_comm_ne_one hP
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_subgroupOf.mpr (hle ?_)
    exact Subgroup.commutator_mem_commutator a'.2 b'.2
  · intro W hW hWK hTW
    rw [hfrat] at hW ⊢
    exact hirr W hW hWK hTW

theorem le_normalizer_K (h331 : Stmt3_3_1) (hThm : Thm14_5_3) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h3x : NQCore.Prop134ThreeExtraspecial)
    (S : Setting147 G T L V H)
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    {X : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hKX : oTwoUpper H ≤ X) (hTX : T ≤ X) :
    X ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hsimple := S.hyp.fsu.simple
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥X :=
    (QuasithinUnique.qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1 _ hX
  have hsyl : QuasithinUnique.IsSylowTwoOf T X :=
    ⟨hTX, S.hyp.fsu.sylow.1, fun h2 =>
      S.hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTX))⟩
  have hP := isPOnePlusTwo_K hK
  obtain ⟨P, hPK, hP3, hP27⟩ := exists_sylow_three_K hK
  have hidx : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 27 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hP.2.1]
    norm_num
  exact h3x G X T (oTwoUpper H) P hsqtk hX hsyl hKX
    (isXi_K h331 hThm h1222 h1332 h1334 S hK) hidx hPK hP3 hP27

end CFSG.Quasithin.H13.L32A
