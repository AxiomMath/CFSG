module

public import CFSG.Quasithin.Vol2.Ch7Lem761End
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Background.HSL3Orb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Stmt7_7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I 1 →
      ∀ θ ∈ L, θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) →
        θ ∉ Subgroup.centralizer (fsuV T I : Set G) →
          Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) :
            Set G) ≤ fsuM T L

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem hypE61_of_pair (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] {n : ℕ}
    (hrow : Row711SL3Pair T L I n) : E6.HypE61 T (fsuM T L) (fsuV T I) := by
  obtain ⟨-, hVM⟩ := fsuM_le_normalizer_of_pair h711n h325 hyp hrow
  exact hypE61_of_ti h37 h38 h39 hmod h3228 hyp fun g hg hgN => absurd (hVM hg) hgN

theorem centralizer_le_of_V0 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h773 : Stmt7_7_3)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711SL3Pair T L I 1) {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hU : Nat.card U * 2 = Nat.card (fsuV T I) ∨ (Nat.card U * 4 = Nat.card (fsuV T I) ∧
      ∃ m ∈ fsuM T L, m ∈ Subgroup.centralizer (U : Set G) ∧
        m ∉ Subgroup.centralizer (fsuV T I : Set G))) :
    Subgroup.centralizer (U : Set G) ≤ fsuM T L := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨hL, hVM⟩ := fsuM_le_normalizer_of_pair h711n h325 hyp hrow
  have hrow' := hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨t, -, φ, hφN, hinf, hsup, hniso, -⟩ := exists_twist_eq hV hN hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  have hcardU' : Nat.card ↥(intSub hV U) = Nat.card U := by
    rw [← Subgroup.card_map_of_injective (valHom_injective hV), map_valHom_intSub hV hUV]
  have hcardV : Nat.card (IntMod (fsuV T I) hV) = Nat.card (fsuV T I) := rfl
  have hU' : Nat.card ↥(intSub hV U) * 2 = Nat.card (IntMod (fsuV T I) hV) ∨
      (Nat.card ↥(intSub hV U) * 4 = Nat.card (IntMod (fsuV T I) hV) ∧
        ∃ p ∈ Subgroup.normalizer
            (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV))),
          p ≠ 1 ∧ ∀ u ∈ intSub hV U, p u = u) := by
    rcases hU with h | ⟨h, m, hmM, hmU, hmV⟩
    · left
      rw [hcardU', hcardV, h]
    · right
      refine ⟨by rw [hcardU', hcardV, h], convI hV ⟨m, hVM hmM⟩,
        autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) _), ?_, ?_⟩
      · intro h1
        exact hmV ((convI_eq_one_iff hV _).mp h1)
      · intro u hu
        apply IntMod.val_injective
        rw [convI_apply_val]
        have h2 := Subgroup.mem_centralizer_iff.mp hmU u.val (mem_intSub.mp hu)
        change m * u.val * m⁻¹ = u.val
        rw [← h2, mul_inv_cancel_right]
  obtain ⟨θ, hθH, hθ3, hθ1, hθfix⟩ := SL3One.H4_SL3One_V0 hL3 hφN hinf hsup hniso hU'
  obtain ⟨g, hgL0, rfl⟩ := (mem_autI hV).1 hθH
  have hgL : (g : G) ∈ L := by
    rw [hL]
    exact hgL0
  have hg3 : (g : G) ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have h1 : convI hV (g ^ 3) = 1 := by rw [map_pow, hθ3]
    have h2 := (convI_eq_one_iff hV (g ^ 3)).mp h1
    simpa using h2
  have hg1 : (g : G) ∉ Subgroup.centralizer (fsuV T I : Set G) := fun h =>
    hθ1 ((convI_eq_one_iff hV g).mpr h)
  have hle : fsuV T I ⊓ Subgroup.centralizer ({(g : G)} : Set G) ≤ U := by
    intro v hv
    have hfix : convI hV g (IntMod.mk hV ⟨v, hv.1⟩) = IntMod.mk hV ⟨v, hv.1⟩ := by
      apply IntMod.val_injective
      rw [convI_apply_val]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hv.2
      change (g : G) * v * (g : G)⁻¹ = v
      rw [← h, mul_inv_cancel_right]
    exact hθfix _ hfix
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)).trans
    (h773 G T L I hyp h731 inferInstance hrow' g hgL hg3 hg1)

theorem stmt7_7_1_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (h3228 : Stmt3_2_2_eight) (h612 : ASInputs.AS_E_6_12) (h773 : Stmt7_7_3) : Stmt7_7_1 := by
  intro G _ _ T L I hyp h731 _ hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨-, hVM⟩ := fsuM_le_normalizer_of_pair h711n h325 hyp hrow
  have hE61 := hypE61_of_pair h37 h38 h39 hmod h711n h325 h3228 hyp hrow
  have hpV : IsPGroup 2 (fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hcV : Nat.card (fsuV T I) = 2 ^ 6 := by
    obtain ⟨htw, hnat⟩ := hrow
    obtain ⟨t, -, φ, hφN, hinf, hsup, hniso, -⟩ := exists_twist_eq hV hN hNM htw
    have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I)
        ⊥ 3 1 := hnat
    exact (SL3One.H4_SL3One hL3 hφN hinf hsup hniso (autI_fsuL0_le hV)
      (autI_top_le_normalizer hV hNM)).1
  have hhyp : ∀ U : Subgroup G, U ≤ fsuV T I → Nat.card U * 2 = Nat.card (fsuV T I) →
      Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun U hUV h =>
    centralizer_le_of_V0 h37 h38 h39 hmod h711n h325 h773 hyp h731 hrow hUV (Or.inl h)
  unfold rParam
  refine lt_of_lt_of_le (show (2 : ℕ∞) < 3 by norm_num) (le_iInf₂ fun U hU => ?_)
  obtain ⟨hUV, hCU⟩ := hU
  suffices h : 3 ≤ mQuot (fsuV T I) U by exact_mod_cast h
  by_contra hlt
  push Not at hlt
  apply hCU
  refine le_trans ?_ hVM
  have hcard := card_eq_two_pow_mul hpV hUV
  obtain ⟨k, hk⟩ : ∃ k, mQuot (fsuV T I) U = k := ⟨_, rfl⟩
  rw [hk] at hcard hlt
  interval_cases k
  ·
    have hUeq : U = fsuV T I :=
      Subgroup.eq_of_le_of_card_ge hUV (le_of_eq (by rw [hcard, pow_zero, one_mul]))
    rw [hUeq]
    exact hE61.centralizer_le
  ·
    exact hhyp U hUV (by rw [hcard, pow_one, mul_comm])
  ·
    by_cases hm : ∃ m ∈ fsuM T L, m ∈ Subgroup.centralizer (U : Set G) ∧
        m ∉ Subgroup.centralizer (fsuV T I : Set G)
    · exact centralizer_le_of_V0 h37 h38 h39 hmod h711n h325 h773 hyp h731 hrow hUV
        (Or.inr ⟨by rw [hcard]; ring, hm⟩)
    · push Not at hm
      have heq : fsuM T L ⊓ Subgroup.centralizer (U : Set G) =
          fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
        le_antisymm (fun x hx => ⟨hx.1, hm x hx.1 hx.2⟩)
          (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV)))
      have hU0 : U ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.card_bot, hcV] at hcard
        norm_num at hcard
      by_contra hCUM
      obtain ⟨⟨U₁, -, hU₁V, hm1, hCU₁⟩, -⟩ :=
        h612 G T (fsuM T L) (fsuV T I) U hE61 hU0 hUV heq hCUM
      have hcard₁ := card_eq_two_pow_mul hpV hU₁V
      rw [hm1, pow_one] at hcard₁
      exact hCU₁ (hhyp U₁ hU₁V (by rw [hcard₁, mul_comm]))

end CFSG.Quasithin.H13
