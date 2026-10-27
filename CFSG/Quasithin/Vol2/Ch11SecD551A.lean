module

public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Vol2.Ch11SecDDirect
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem le_ROf {L₁ N : Subgroup G} (hNT : N ≤ T) (hN2 : IsPGroup 2 N)
    (hL₁ : L₁ ≤ Subgroup.normalizer (N : Set G)) (hT : T ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ pCoreOf 2 (L₁ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNX : N ≤ L₁ ⊔ T := hNT.trans le_sup_right
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hNX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 (sup_le hL₁ hT)) hN2

omit [Finite G] in
theorem le_ROf' {L₁ N : Subgroup G} (hN2 : IsPGroup 2 N) (hNX : N ≤ L₁ ⊔ T)
    (hX : L₁ ⊔ T ≤ Subgroup.normalizer (N : Set G)) : N ≤ pCoreOf 2 (L₁ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hNX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hX) hN2

theorem inf_centralizer_le_ROf (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (SecA.IsVi.le_normalizer hV₁ ht)
  set N := (LOf L V₁ ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) with hN
  have hCV : Subgroup.normalizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  have hXV : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (((perfectCore_le _).trans inf_le_left).trans (SecA.L_le_normalizer_fsuV h))
      (SecA.T_le_normalizer_fsuV T I)
  have hN2 : IsPGroup 2 N := isPGroup_two_of_forall fun x hx => by
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 hTL₁ hx.1
    have hjC : x ^ 2 ^ j ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨(perfectCore_le _).trans inf_le_left hj, Subgroup.pow_mem _ hx.2 _⟩
    rw [SecA.centralizer_eq_pCoreOf h1102 h] at hjC
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hjC
    exact ⟨j + k, by rw [pow_add, pow_mul, hk]⟩
  have hNle : N ≤ ROf T L V₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
        fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx) (hCV (hXV hx))) hN2
  exact fun x hx => hNle ⟨Subgroup.mem_sup_right hx.1, hx.2⟩

theorem inf_sectionCentralizer_le_ROf (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    T ⊓ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := LOf L V₁ with hL₁
  set O := pCoreOf 2 L₁ with hO
  set C := T ⊓ sectionCentralizer L₁ O with hC
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (SecA.IsVi.le_normalizer hV₁ ht)
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hTL₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁)
  have hsylT : QuasithinUnique.IsSylowTwoOf T (L₁ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right
  have hOT : O ≤ T := by
    have hO' : O ≤ pCoreOf 2 (L₁ ⊔ T) :=
      le_ROf' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁) hTO)
    exact hO'.trans (pCoreOf_two_le_of_isSylowTwoOf hsylT)
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hTO
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer ht)
      (mem_normalizer_sectionCentralizer (hTL₁ ht) (hTO ht))
  have hL₁N : L₁ ≤ Subgroup.normalizer ((O ⊔ C : Subgroup G) : Set G) := by
    intro l hl
    refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    all_goals
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O C hCO] at hx
      obtain ⟨o, ho, c, hc, rfl⟩ := hx
    · have hlo := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hl) o).mp ho
      have hlc : l * c * l⁻¹ * c⁻¹ ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hl) _).mp
          (hc.2.2.2 l⁻¹ (L₁.inv_mem hl))
        convert this using 1
        group
      have : l * (o * c) * l⁻¹ = (l * o * l⁻¹) * (l * c * l⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (O ⊔ C).mul_mem ((O ⊔ C).mul_mem (Subgroup.mem_sup_left hlo)
        (Subgroup.mem_sup_left hlc)) (Subgroup.mem_sup_right hc)
    · have hl' := L₁.inv_mem hl
      have hlo := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hl') o).mp ho
      have hlc : l⁻¹ * c * l⁻¹⁻¹ * c⁻¹ ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hl') _).mp
          (hc.2.2.2 l⁻¹⁻¹ (L₁.inv_mem hl'))
        convert this using 1
        group
      have : l⁻¹ * (o * c) * l = (l⁻¹ * o * l⁻¹⁻¹) * (l⁻¹ * c * l⁻¹⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (O ⊔ C).mul_mem ((O ⊔ C).mul_mem (Subgroup.mem_sup_left hlo)
        (Subgroup.mem_sup_left hlc)) (Subgroup.mem_sup_right hc)
  have hOCT : O ⊔ C ≤ T := sup_le hOT inf_le_left
  have hOC := le_ROf' (h.fsu.sylow.1.to_le hOCT) (hOCT.trans le_sup_right)
    (sup_le hL₁N (le_normalizer_sup hTO hTC))
  exact le_sup_right.trans hOC

omit [Finite G] in
theorem wClos_zero_eq_of_le {V R : Subgroup G} (hRT : R ≤ T) (hW : E3.wClos V 0 T ≤ R) :
    E3.wClos V 0 R = E3.wClos V 0 T := by
  refine le_antisymm (E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨hA.1.trans hRT, hA.2⟩)
    (E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨(E3.le_wClos hA).trans hW, hA.2⟩)

omit [Finite G] in
theorem nParam_eq_one_of_le_one {H : Subgroup G} (h1 : E1.nParam H ≤ 1)
    (heven : Even (Nat.card H)) : E1.nParam H = 1 := by
  refine le_antisymm h1 ?_
  unfold E1.nParam
  split_ifs with hodd
  · exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
  · exact le_iInf₂ fun i hi => by exact_mod_cast hi.1

theorem isSylowIn_sup_of_normal {R N : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hodd : ¬ 2 ∣ (R ⊓ N).relIndex N) :
    IsSylowIn 2 R (R ⊔ N) := by
  refine ⟨le_sup_left, hR, fun h2 => hodd ?_⟩
  have e1 : N.relIndex (R ⊔ N) = N.relIndex R := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hRN
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hRN
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient R N hRN).toEquiv.symm
  have c1 := Subgroup.relIndex_mul_card (H := R) (K := R ⊔ N)
  have c2 := Subgroup.relIndex_mul_card (H := N) (K := R ⊔ N)
  have c3 := Subgroup.relIndex_mul_card (H := N) (K := R)
  have c4 := Subgroup.relIndex_mul_card (H := R ⊓ N) (K := N)
  rw [inf_eq_left.mpr le_sup_left] at c1
  rw [inf_eq_left.mpr le_sup_right] at c2
  rw [inf_comm] at c3
  rw [inf_eq_left.mpr inf_le_right] at c4
  have key : R.relIndex (R ⊔ N) = (R ⊓ N).relIndex N := by
    have hpos : 0 < Nat.card ↥(R ⊓ N) := Nat.card_pos
    have hposR : 0 < N.relIndex R := Nat.pos_of_ne_zero (E3.relIndex_ne_zero' R N)
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hposR)
    calc Nat.card ↥(R ⊓ N) * N.relIndex R * R.relIndex (R ⊔ N)
        = R.relIndex (R ⊔ N) * Nat.card R := by rw [← c3]; ring
      _ = N.relIndex R * Nat.card N := by rw [c1, ← c2, e1]
      _ = Nat.card ↥(R ⊓ N) * N.relIndex R * (R ⊓ N).relIndex N := by rw [← c4]; ring
  rw [← key]
  exact h2

end CFSG.Quasithin.Vol2.Ch11.SecD
