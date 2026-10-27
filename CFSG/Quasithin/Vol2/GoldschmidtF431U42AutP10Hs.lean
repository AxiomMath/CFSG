module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Nrm
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbD

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

noncomputable def p10Nh : Subgroup Ah := Subgroup.normalizer (A2h : Set Ah)

noncomputable def p10Kh : Subgroup Ah := p10Nh ⊓ Subgroup.centralizer ({fhatA} : Set Ah)

theorem p10Kh_le_Nh : p10Kh ≤ p10Nh := inf_le_left

theorem mem_p10Nh {g : Ah} : g ∈ p10Nh ↔ g ∈ Subgroup.normalizer (A2h : Set Ah) := Iff.rfl

theorem mem_p10Kh {g : Ah} :
    g ∈ p10Kh ↔ g ∈ p10Nh ∧ g ∈ Subgroup.centralizer ({fhatA} : Set Ah) := Iff.rfl

theorem repL_p10fL : RepL p10fL ((fhatA : Ah) : P45) := by
  rw [(p10_lits_check).1]
  exact repL_fhat

theorem repL_eSym (k : ℕ) : RepL (p10eSymL.getD k idL) ((p10eSymA k : Ah) : P45) := by
  rcases lt_or_ge k 6 with hk | hk
  · rw [(p10_lits_check).2]
    interval_cases k
    · exact repL_p10sA 0
    · exact repL_p10sA 2
    · exact repL_p10sA 4
    · exact repL_p10sA 5
    · exact repL_wordSA _
    · exact repL_fhat
  · have hlen : p10eSymL.length = 6 := by decide
    have h1 : p10eSymL.getD k idL = idL := List.getD_eq_default _ _ (by omega)
    have h2 : p10eSymA k = 1 := by
      unfold p10eSymA
      exact List.getD_eq_default _ _ (by simp; omega)
    rw [h1, h2]
    exact repL_one 45

theorem repL_aE (w : List ℕ) : RepL (evalEL w) ((aE w : Ah) : P45) := by
  induction w with
  | nil => exact repL_one 45
  | cons k w ih => exact repL_mul (repL_eSym k) ih

theorem exists_A2h_rep {a : PL} (ha : a ∈ Al2) :
    ∃ g ∈ A2h, RepL a (g : P45) := by
  obtain ⟨g, -, hg⟩ := exists_That_of_mem_Thl (A2_check.2.2.2.1 a ha)
  exact ⟨g, ⟨a, ha, hg⟩, hg⟩

theorem mem_p10Nh_of_norm {g : Ah} {l : PL}
    (hl : RepL l (g : P45)) (h : NormA2 l) : g ∈ p10Nh := by
  refine normalizer_of_conj_le fun s hs => ?_
  obtain ⟨la, hla, hrs⟩ := hs
  obtain ⟨a', ha', heq⟩ := h la hla
  obtain ⟨b, hb, hrb⟩ := exists_A2h_rep ha'
  have h1 : g * s = b * g := by
    refine Subtype.ext (eq_of_repL (l := comp l la) (repL_mul hl hrs) ?_)
    have h' : RepL (comp a' l) ((b * g : Ah) : P45) := repL_mul hrb hl
    rw [← heq] at h'
    exact h'
  have h2 : g * s * g⁻¹ = b := by rw [h1]; group
  rw [h2]
  exact hb

theorem exists_Kh_rep {l : PL} (hl : l ∈ p10Kl) :
    ∃ g ∈ p10Kh, RepL l (g : P45) := by
  have hn : NormA2 l := p10_norm_check.1 l hl
  rw [p10Kl_eq] at hl
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
  refine ⟨aE w, ⟨mem_p10Nh_of_norm (repL_aE w) hn, ?_⟩, repL_aE w⟩
  exact Subgroup.mem_centralizer_singleton_iff.2
    (comm_of_comp_comm (v := fhatA) repL_p10fL (repL_aE w)
      (p10_K_check.2.2.2.1 _ (by rw [p10Kl_eq]; exact List.mem_map.2 ⟨w, hw, rfl⟩)))

theorem fix_points_check :
    ∀ p < 45, (∀ l ∈ Al2, l.getD p 0 = p) → p = 0 ∨ p = 15 ∨ p = 16 := by
  decide +kernel

theorem A2h_le_P1h : A2h ≤ P1h :=
  A2h_le_That.trans (That_le_Bh.trans Bh_le_P1h)

theorem card_Nh_le :
    Nat.card p10Nh ≤ 192 := by
  have horb : MulAction.orbit p10Nh (0 : Fin 45) ⊆ ({0, 15, 16} : Set (Fin 45)) := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    have hfix : ∀ a ∈ A2h, a • (n • (0 : Fin 45)) = n • (0 : Fin 45) := by
      intro a ha
      have h1 : n⁻¹ * a * n ∈ A2h := by
        have := (Subgroup.mem_normalizer_iff.1 (p10Nh.inv_mem hn) a).1 ha
        simpa using this
      have h2 : (n⁻¹ * a * n) • (0 : Fin 45) = 0 := A2h_le_P1h h1
      calc a • (n • (0 : Fin 45)) = (a * n) • (0 : Fin 45) := (mul_smul a n 0).symm
        _ = (n * (n⁻¹ * a * n)) • (0 : Fin 45) := by
          rw [show a * n = n * (n⁻¹ * a * n) by group]
        _ = n • ((n⁻¹ * a * n) • (0 : Fin 45)) := mul_smul _ _ _
        _ = n • (0 : Fin 45) := by rw [h2]
    have hl : ∀ l ∈ Al2,
        l.getD ((n • (0 : Fin 45) : Fin 45) : ℕ) 0 = (n • (0 : Fin 45) : Fin 45) := by
      intro l hl
      obtain ⟨g, hg, hrep⟩ := exists_A2h_rep hl
      have := hrep.2 (n • (0 : Fin 45))
      rw [this]
      exact congrArg Fin.val (hfix g hg)
    have := fix_points_check _ (n • (0 : Fin 45) : Fin 45).2 hl
    rcases this with h | h | h
    · left; exact Fin.ext h
    · right; left; exact Fin.ext h
    · right; right; exact Fin.ext h
  have hidx : (MulAction.stabilizer p10Nh (0 : Fin 45)).index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    refine (Set.ncard_le_ncard horb (Set.toFinite _)).trans ?_
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hcard : Nat.card (MulAction.stabilizer p10Nh (0 : Fin 45)) = 64 := by
    rw [← MulAction.stabilizer_subgroupOf]
    change Nat.card ↥(P1h.subgroupOf p10Nh) = 64
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P1h ⊓ p10Nh ≤ p10Nh)).toEquiv]
    exact card_N1_A2
  rw [← (MulAction.stabilizer p10Nh (0 : Fin 45)).index_mul_card, hcard]
  omega

theorem repL_p10hA : RepL p10hL ((p10hA : Ah) : P45) := by
  rw [(p10_h_check).1]
  exact repL_wordSA _

theorem p10hA_mem_Nh : p10hA ∈ p10Nh :=
  mem_p10Nh_of_norm repL_p10hA p10_norm_check.2

theorem p10hA_not_mem_Kh : p10hA ∉ p10Kh := fun h => by
  have h1 : p10hA * fhatA = fhatA * p10hA := Subgroup.mem_centralizer_singleton_iff.1 h.2
  exact p10_K_check.2.2.2.2.1 (comp_comm_of_comm (v := fhatA) repL_p10fL repL_p10hA h1)

theorem card_le_half {X : Type*} [Group X] [Finite X] {K N : Subgroup X} (hKN : K ≤ N) {x : X}
    (hx : x ∈ N) (hxK : x ∉ K) : 2 * Nat.card K ≤ Nat.card N := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hKN
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hxK ((Subgroup.eq_of_le_of_card_ge hKN (by omega)) ▸ hx)
  calc 2 * Nat.card K ≤ m * Nat.card K := Nat.mul_le_mul_right _ (by omega)
    _ = Nat.card N := by rw [hm, mul_comm]

theorem card_Nh_Kh :
    Nat.card p10Nh = 192 ∧ Nat.card p10Kh = 96 := by
  have h1 : 96 ≤ Nat.card p10Kh := by
    have := length_le_card_of_nodup p10Kh p10_K_check.1 (fun l hl => exists_Kh_rep hl)
    rwa [p10_K_check.2.1] at this
  have h2 := card_le_half p10Kh_le_Nh p10hA_mem_Nh p10hA_not_mem_Kh
  have h3 := card_Nh_le
  constructor <;> omega

theorem rep_mem_Kh :
    ∀ g ∈ p10Kh, ∃ l ∈ p10Kl, RepL l (g : P45) :=
  rep_mem_of_card_le p10Kh p10_K_check.1 (fun l hl => exists_Kh_rep hl)
    (by rw [card_Nh_Kh.2, p10_K_check.2.1])

theorem index_Kh :
    (p10Kh.subgroupOf p10Nh).index = 2 := by
  have h := (p10Kh.subgroupOf p10Nh).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe p10Kh_le_Nh).toEquiv, card_Nh_Kh.1,
    card_Nh_Kh.2] at h
  omega

theorem normal_Kh :
    (p10Kh.subgroupOf p10Nh).Normal := Subgroup.normal_of_index_eq_two index_Kh

theorem fhatA_mem_Kh : fhatA ∈ p10Kh := by
  obtain ⟨g, hg, hrep⟩ := exists_Kh_rep p10_K_check.2.2.2.2.2.1
  have : g = fhatA := Subtype.ext (eq_of_repL hrep repL_p10fL)
  rwa [this] at hg

theorem repL_p10hiL : RepL p10hiL (((p10hA)⁻¹ : Ah) : P45) :=
  repL_inv_of_comp repL_p10hA p10_K_check.2.2.2.2.2.2.2.2.1 p10_K_check.2.2.2.2.2.2.2.2.2.1
    p10_K_check.2.2.2.2.2.2.2.1

end CFSG.Quasithin.H13.F431.U42Aut
