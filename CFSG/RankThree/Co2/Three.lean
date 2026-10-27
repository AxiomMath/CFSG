module

public import CFSG.RankThree.Co2.X9Fuse

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem card_eq_of_center_isolated {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {z : G} {T : Subgroup G} (hTz : T ≤ Subgroup.centralizer {z}) (hzT : z ∈ T)
    (hT : Nat.card T = p ^ (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization p)
    (hcen : ∀ y ∈ T, (∀ s ∈ T, y * s = s * y) → IsConj z y → y = z) :
    Nat.card T = p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hT).exists_le_sylow
  suffices hTP : T = P by rw [hTP]; exact P.card_eq_multiplicity
  by_contra hne
  have hlt : T.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ T.subgroupOf P := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := P)
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  rw [Subgroup.mem_normalizer_iff] at hxN
  have hconj : ∀ w ∈ T, (x : G) * w * (x : G)⁻¹ ∈ T := fun w hw =>
    Subgroup.mem_subgroupOf.1 ((hxN ⟨w, hP hw⟩).1 (Subgroup.mem_subgroupOf.2 hw))
  have hconj' : ∀ w ∈ T, (x : G)⁻¹ * w * (x : G) ∈ T := by
    intro w hw
    have hwP : (x : G)⁻¹ * w * x ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem x.2) (hP hw))
        x.2
    refine Subgroup.mem_subgroupOf.1 ((hxN ⟨_, hwP⟩).2 (Subgroup.mem_subgroupOf.2 ?_))
    have e : (((x * ⟨_, hwP⟩ * x⁻¹ : P)) : G) = w := by
      show (x : G) * ((x : G)⁻¹ * w * x) * (x : G)⁻¹ = w
      group
    rw [e]
    exact hw
  have hxz : (x : G) * z * (x : G)⁻¹ = z := by
    apply hcen _ (hconj z hzT) _ (isConj_iff.2 ⟨(x : G), rfl⟩)
    intro s hs
    have h1 : (x : G)⁻¹ * s * x * z = z * ((x : G)⁻¹ * s * x) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hTz (hconj' s hs))
    calc (x : G) * z * (x : G)⁻¹ * s = (x : G) * (z * ((x : G)⁻¹ * s * x)) * (x : G)⁻¹ := by
          group
      _ = (x : G) * ((x : G)⁻¹ * s * x * z) * (x : G)⁻¹ := by rw [h1]
      _ = s * ((x : G) * z * (x : G)⁻¹) := by group
  have hxC : (x : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * z = (x : G) * z * (x : G)⁻¹ * x := by group
      _ = z * x := by rw [hxz]
  set K := (P : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G)
  have hTK : T < K := by
    refine lt_of_le_of_ne (le_inf hP hTz) ?_
    intro e
    apply hxT
    rw [Subgroup.mem_subgroupOf, e]
    exact Subgroup.mem_inf.2 ⟨x.2, hxC⟩
  have hKp : IsPGroup p (K.subgroupOf (Subgroup.centralizer ({z} : Set G))) := by
    have : IsPGroup p K := P.isPGroup'.to_le inf_le_left
    exact this.comap_of_injective (Subgroup.centralizer ({z} : Set G)).subtype
      (Subgroup.subtype_injective _)
  obtain ⟨Q, hQ⟩ := hKp.exists_le_sylow
  have h1 := Subgroup.card_le_of_le hQ
  rw [card_subgroupOf_eq inf_le_right, Q.card_eq_multiplicity, ← hT] at h1
  exact absurd h1 (not_le.2 (Subgroup.card_lt_of_lt hTK))

theorem rCr_mem_sylT : rCr ∈ subW sylWords := by
  rw [← coe_sylT]
  exact QCr_le_sylow sylT rCr_mem_QCr

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem card_TG : Nat.card (h.liftG (subW sylWords)) = 2 ^ (Nat.card G).factorization 2 := by
  haveI := h.finite
  refine card_eq_of_center_isolated (h.liftG_le_H _) ?_ ?_ ?_
  · rw [← h.rG_zero, rG, rep_zero]
    exact h.φ_symm_mem_liftG rCr_mem_sylT
  · rw [card_liftG, card_sylT, h.card_H,
      factorization_two_eq (by norm_num : 743178240 = 2 ^ 18 * 2835) (by decide)]
    norm_num
  · intro y hy hcen hyz
    obtain ⟨hyH, hyT⟩ := h.mem_liftG.1 hy
    have hc : ∀ s ∈ (sylT : Subgroup Cr), h.φ ⟨y, hyH⟩ * s = s * h.φ ⟨y, hyH⟩ := by
      intro s hs
      have hsT : ((h.φ.symm s : h.H) : G) ∈ h.liftG (subW sylWords) :=
        h.φ_symm_mem_liftG (by rwa [← coe_sylT])
      exact (h.commute_iff ⟨y, hyH⟩ s).1 (hcen _ hsT)
    rcases eq_one_or_eq_rCr_of_central sylT hc with e | e
    · exfalso
      apply h.ne_one_of_isConj_z hyz
      have : (⟨y, hyH⟩ : h.H) = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
      exact congrArg Subtype.val this
    · have : (⟨y, hyH⟩ : h.H) = h.zG := by
        apply h.φ.injective
        rw [e, h.φ_zG]
      exact congrArg Subtype.val this

theorem exists_conj_mem_TG {t : G} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : G, g * t * g⁻¹ ∈ h.liftG (subW sylWords) := by
  haveI := h.finite
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    have ho : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) ht1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (Sylow.ofCard _ h.card_TG)
  refine ⟨g, ?_⟩
  have hmem : g * t * g⁻¹ ∈ ((g • P : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) _
      (hP (Subgroup.mem_zpowers t))
  rw [hg, Sylow.coe_ofCard] at hmem
  exact hmem

theorem isConj_rG_of_lt {c : ℕ} (hc : c < 10) :
    (inA c = true ∧ IsConj h.z (h.rG c)) ∨ (inB c = true ∧ IsConj (h.rG 1) (h.rG c)) ∨
      ((inC c = true ∨ c = 9) ∧ IsConj (h.rG 8) (h.rG c)) := by
  by_cases hc9 : c = 9
  · subst hc9
    exact Or.inr (Or.inr ⟨Or.inr rfl, h.isConj_eight_nine⟩)
  rcases classes_cover hc hc9 with hA | hB | hC
  · exact Or.inl ⟨hA, (h.isConj_z_rG_iff hc).2 hA⟩
  · exact Or.inr (Or.inl ⟨hB, h.isConj_rG_of_inB hB⟩)
  · exact Or.inr (Or.inr ⟨Or.inl hC, h.isConj_rG_of_inC hC⟩)

theorem three_classes {t : G} (ht : t * t = 1) (ht1 : t ≠ 1) :
    IsConj h.z t ∨ IsConj (h.rG 1) t ∨ IsConj (h.rG 8) t := by
  obtain ⟨g, hg⟩ := h.exists_conj_mem_TG ht ht1
  obtain ⟨huH, -⟩ := h.mem_liftG.1 hg
  set u : h.H := ⟨g * t * g⁻¹, huH⟩
  have hu2 : h.φ u * h.φ u = 1 := by
    rw [← map_mul]
    have : u * u = 1 := Subtype.ext (show g * t * g⁻¹ * (g * t * g⁻¹) = 1 by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht]; group)
    rw [this, map_one]
  have hu1 : h.φ u ≠ 1 := by
    intro e
    apply ht1
    have : u = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
    have e' : g * t * g⁻¹ = 1 := congrArg Subtype.val this
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [e']; group
  obtain ⟨c, hc, huc⟩ := exists_isConj_rep (h.φ u) hu2 hu1
  have htc : IsConj (h.rG c) t := by
    have h1 : IsConj ((h.φ.symm (h.φ u) : h.H) : G) (h.rG c) := h.isConj_φ_symm huc
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1.symm.trans (isConj_iff.2 ⟨g⁻¹, show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group⟩)
  rcases h.isConj_rG_of_lt hc with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
  · exact Or.inl (e.trans htc)
  · exact Or.inr (Or.inl (e.trans htc))
  · exact Or.inr (Or.inr (e.trans htc))

theorem three_classes_distinct :
    ¬ IsConj h.z (h.rG 1) ∧ ¬ IsConj h.z (h.rG 8) ∧ ¬ IsConj (h.rG 1) (h.rG 8) :=
  ⟨h.not_isConj_z_one, h.not_isConj_z_eight, h.not_isConj_one_eight⟩

theorem isConj_iff_of_class {t : h.H} {c : ℕ} (hc : c < 10) (htc : IsConj (rep c) (h.φ t)) :
    (IsConj h.z (t : G) ↔ inA c = true) ∧ (IsConj (h.rG 1) (t : G) ↔ inB c = true) ∧
      (IsConj (h.rG 8) (t : G) ↔ inC c = true ∨ c = 9) := by
  have hct : IsConj (h.rG c) (t : G) := by
    have h1 := h.isConj_φ_symm htc
    rwa [MulEquiv.symm_apply_apply] at h1
  have key : ∀ a : G, IsConj a (t : G) ↔ IsConj a (h.rG c) := fun a =>
    ⟨fun h' => h'.trans hct.symm, fun h' => h'.trans hct⟩
  have hd := h.three_classes_distinct
  rw [key, key, key]
  rcases h.isConj_rG_of_lt hc with ⟨hA, e⟩ | ⟨hB, e⟩ | ⟨hC, e⟩
  · refine ⟨iff_of_true e hA, iff_of_false (fun e' => hd.1 (e.trans e'.symm)) ?_,
      iff_of_false (fun e' => hd.2.1 (e.trans e'.symm)) ?_⟩ <;>
    (revert hA; interval_cases c <;> decide)
  · refine ⟨iff_of_false (fun e' => hd.1 (e'.trans e.symm)) ?_, iff_of_true e hB,
      iff_of_false (fun e' => hd.2.2 (e.trans e'.symm)) ?_⟩ <;>
    (revert hB; interval_cases c <;> decide)
  · refine ⟨iff_of_false (fun e' => hd.2.1 (e'.trans e.symm)) ?_,
      iff_of_false (fun e' => hd.2.2 (e'.trans e.symm)) ?_, iff_of_true e hC⟩ <;>
    (revert hC; interval_cases c <;> decide)

end Co2CentHyp

end CFSG.RankThree.Co2
