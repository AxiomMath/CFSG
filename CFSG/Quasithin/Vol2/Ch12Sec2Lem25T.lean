module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25R
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25S
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25O

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem25

variable {G : Type} [Group G]

theorem exists_bar [Finite G] {N K : Subgroup G} (hKN : K ≤ N) :
    ∃ ψ : ↥K →* ↥(modO2Image N K), Function.Surjective ψ ∧
      (∀ k : ↥K, ψ k = 1 ↔ (k : G) ∈ pCoreOf 2 N) ∧
      ∀ B : Subgroup G, B ≤ K →
        Nat.card ↥((B.subgroupOf K).map ψ) = Nat.card ↥(modO2Image N B) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥N) with hπ
  let ψ : ↥K →* ↥(modO2Image N K) := (π.comp (Subgroup.inclusion hKN)).codRestrict _ fun k =>
    ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · intro k
    constructor
    · intro h1
      have h2 : π (Subgroup.inclusion hKN k) = 1 := congrArg Subtype.val h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      rw [A7.pCoreOf_eq_map_cfsgPCore]
      exact ⟨_, h2, rfl⟩
    · intro h1
      rw [A7.pCoreOf_eq_map_cfsgPCore] at h1
      obtain ⟨y, hy, hyk⟩ := h1
      apply Subtype.ext
      show π (Subgroup.inclusion hKN k) = 1
      have : Subgroup.inclusion hKN k = y := Subtype.ext hyk.symm
      rw [this, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
  · intro B hBK
    have hEq : ((B.subgroupOf K).map ψ).map (modO2Image N K).subtype = modO2Image N B := by
      ext x
      constructor
      · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨Subgroup.inclusion hKN b, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨_, ⟨⟨b, hBK hb⟩, hb, rfl⟩, rfl⟩
    rw [← Subgroup.card_map_of_injective (K := (B.subgroupOf K).map ψ)
      (modO2Image N K).subtype_injective, hEq]

theorem not_c6
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) {K : Subgroup G}
    (hYK : YY L U V ≤ K) (hK : K ∈ cComp (NR T U))
    (h6 : A312C6 (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := data_Ybar h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  obtain ⟨hk3, -⟩ := hD.list_c6 h6
  have hn4 : n = 4 := by
    obtain ⟨-, -, hn, -⟩ := hC
    omega
  have hKN : K ≤ NR T U := le_of_mem_cComp hK
  obtain ⟨-, -, hYN, -, -⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  obtain ⟨ψ, hψs, hψ1, hψc⟩ := exists_bar hKN
  have hker : IsPGroup 2 ψ.ker := fun k => by
    obtain ⟨j, hj⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (NR T U)
      ⟨_, (hψ1 k.1).mp (MonoidHom.mem_ker.mp k.2)⟩
    exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩
  have hR2 : IsPGroup 2 (RR T U) := hH.sylow.1.to_le inf_le_left
  have hRc : Nat.card (RR T U) = 2 ^ 6 ∨ Nat.card (RR T U) = 2 ^ 7 := by
    have := card_RR h331 h1222 h323 h1216 h1220 hH hNE hC
    rw [hn4] at this
    norm_num at this
    exact this
  have hR7 : Nat.card (RR T U) ≤ 2 ^ 7 := by
    rcases hRc with h | h
    · rw [h]
      norm_num
    · exact h.le
  have hkerY : ∀ k : ↥K, ψ k = 1 → (k : G) ∈ YY L U V →
      (k : G) ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := by
    intro k hk hkY
    have h1 : (k : G) ∈ YY L U V ⊓ pCoreOf 2 (NR T U) := ⟨hkY, (hψ1 k).mp hk⟩
    have h2 : YY L U V ⊓ pCoreOf 2 (NR T U) ≤ pCoreOf 2 (YY L U V) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
          LieType.BorelTits.le_normalizer_pCoreOf 2 (NR T U) (hYN hj)⟩)
        ((LieType.BorelTits.pCoreOf_isPGroup 2 (NR T U)).to_le inf_le_right)
    have h3 := h2 h1
    rw [A7.pCoreOf_eq_map_cfsgPCore] at h3
    obtain ⟨y, hy, hyk⟩ := h3
    obtain ⟨Q, _, ρ, -, hρk, hρ, -⟩ := exists_Y_rep h1222 h1220 hH hNE hC hn3
    rw [← hρk] at hy
    rw [← hyk]
    exact (hρ y).mp hy
  obtain ⟨hB, hKalt⟩ := h6
  rcases hKalt with hK7 | hhat
  ·
    obtain ⟨e⟩ : Nonempty (↥(modO2Image (NR T U) K) ≃* alternatingGroup (Fin 7)) := hK7
    have hYc : Nat.card ↥(modO2Image (NR T U) (YY L U V)) = 168 := by
      rcases hB with hB | hB
      · exact (hD.false_of_card (card_alt_five hB) (by norm_num)).elim
      · exact Vol2.Ch11.SecB.card_isPSL_three_two_one hB
    have hker' : IsPGroup 2 (e.toMonoidHom.comp ψ).ker := by
      have : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
        ext k
        simp [MonoidHom.mem_ker]
      rw [this]
      exact hker
    refine false_of_alt_seven (K := K) (R := RR T U) (Y := YY L U V) hKN hYK hR2 hRc
      (e.toMonoidHom.comp ψ) (e.surjective.comp hψs) hker' ?_
      (fun y hy hyo => card_RR_centralizer_three h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hy hyo)
      ?_
    · rw [← Subgroup.map_map, Subgroup.card_map_of_injective e.injective, hψc _ hYK, hYc]
    · intro c hcK hco hc4
      obtain ⟨a, haA, ha1, hca⟩ := exists_fix_of_card h331 h1222 h323 h1216 h1220 hH hNE hC hn4
        hc4
      exact (mem_normalizer_Y_of_fix h1222 h323 hH hNE hC (hKN hcK) haA ha1 hca).2.2.2
  ·
    exact false_of_hat_seven_config h331 h1222 h323 h1216 h1220 hH hNE hC hn4 hR7 hKN hYK hhat
      ψ hψs hker hkerY

end Lem25

open Lem25

theorem lem12225YNormal_of
    (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) : Lem12225YNormal := by
  intro G _ _ T L V H P U I h n p hH hNE hC hn3
  obtain ⟨K, hYK, hK, hNK⟩ := exists_K h331 h1222 h323 h1216 h1220 h37 h38 h39 hH hNE hC hn3
  have hKN : K ≤ NR T U := le_of_mem_cComp hK
  rcases cases_K h331 h1222 h323 h1216 h1220 h36 h312 hH hNE hC hn3 hYK hK with heq | hcase | hnq
  · show NR T U ≤ Subgroup.normalizer ((YY L U V : Subgroup G) : Set G)
    rw [heq]
    exact hNK
  · exfalso
    have hD := data_Ybar h331 h1222 h323 h1216 h1220 hH hNE hC hn3
    have hO2 := card_pCore_Ybar_le h331 h1222 h323 h1216 h1220 hH hNE hC hn3
    rcases case_cut h331 h1222 h323 h1216 h1220 hH hNE hC hn3 hKN hcase with h4 | h5 | h6
    · exact not_c4_c5 hD hO2 (Or.inl h4)
    · exact not_c4_c5 hD hO2 (Or.inr h5)
    · exact not_c6 h331 h1222 h323 h1216 h1220 hH hNE hC hn3 hYK hK h6
  · exact (not_nonquasi h331 h1222 h323 h1216 h1220 hH hNE hC hKN hnq).elim

end CFSG.Quasithin.H13
