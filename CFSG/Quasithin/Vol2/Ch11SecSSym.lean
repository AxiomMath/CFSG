module

public import CFSG.Quasithin.Vol2.Ch10SecDClB
public import CFSG.Quasithin.Vol2.Ch11SecSPGL
public import CFSG.Quasithin.Vol2.Ch11SecSXK3
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_inf_eq_bot {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hAB : B ⊓ A = ⊥) (hAN : A ≤ Subgroup.normalizer (B : Set G)) (hX : Nat.card ↥X = 9)
    (hA : 3 ∣ Nat.card ↥A) (hB : 3 ∣ Nat.card ↥B) : A ⊔ B = X := by
  have h2 := Subgroup.relIndex_mul_card B A
  rw [hAB, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card B (A ⊔ B)
  rw [relIndex_sup_eq' hAN, h2, inf_eq_left.mpr le_sup_right] at h3
  have hle : A ⊔ B ≤ X := sup_le hAX hBX
  have hdvd : Nat.card ↥(A ⊔ B) ∣ 9 := hX ▸ Subgroup.card_dvd_of_le hle
  have h9 : 9 ∣ Nat.card ↥(A ⊔ B) := h3 ▸ Nat.mul_dvd_mul hA hB
  have hcard : Nat.card ↥(A ⊔ B) = 9 := Nat.dvd_antisymm hdvd h9
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hX])

omit [Finite G] in
theorem three_dvd_card_of_le {X B : Subgroup G} (hBX : B ≤ X) (hX : Nat.card ↥X = 9)
    (hB : B ≠ ⊥) : 3 ∣ Nat.card ↥B := by
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hd : Nat.card ↥B ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hBX
    rwa [hX] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  rcases k with _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [hk', pow_zero])) hB
  · rw [hk', pow_succ]
    exact dvd_mul_left _ _

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem isLocal_of_mem_cComp_Y (h : StarHyp G T L I V₁ V₂ X K) {Y J : Subgroup G}
    (hTY : T ≤ Y) (hY : pCoreOf 2 Y ≠ ⊥) (hJ : J ∈ cComp Y) : quasithinIsLocal T J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJY : J ⊔ T ≤ Y := sup_le (le_of_mem_cComp hJ) hTY
  have hSY := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTY
  have hOT : pCoreOf 2 Y ≤ J ⊔ T := (pCoreOf_two_le_of_isSylowTwoOf hSY).trans le_sup_right
  have hle : pCoreOf 2 Y ≤ pCoreOf 2 (J ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOT
      (hJY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  refine Ch10.SecD.quasithinIsLocal_of_mem_cComp hJ rfl hJY
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right) fun hb => hY ?_
  exact eq_bot_iff.mpr (hb ▸ hle)

theorem xOne_k0Of_inf_eq_bot (hLevi : FactL34Levi) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    xOne X (k0Of K P₂) ⊓ K = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    hLevi _ h.psl _ h.isSylowTwoOf_bar P₂ hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
  have hle := le_pCoreOf_of_mem_sectionCentralizer (n := 2) le_rfl (hF.trans (by norm_num)) e
  have hXo : Odd (Nat.card ↥X) := h.cartan.2.1
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨⟨hxX, hxC⟩, hxK⟩ := hx
  have hxS := mk_mem_normalizer_modO2Image hxK (h.cartan_le_normalizer_inf hN h1102 hP hxX)
  have hx2 := (hP.borel hxS).2
  have hxC' := mk_mem_sectionCentralizer (k0Of_le K P₂) hxK hxC
  rw [modO2Image_k0Of K hP.c₂.2.1] at hxC'
  have hxO := hle ⟨hx2, hxC'⟩
  have hodd : Odd (Nat.card ↥(modO2Image K (X ⊓ K))) := by
    rw [card_modO2Image_of_odd inf_le_right (hXo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))]
    exact hXo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P₂) hodd
  have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hxK⟩ ∈
      pCoreOf 2 P₂ ⊓ modO2Image K (X ⊓ K) := ⟨hxO, ⟨⟨x, hxK⟩, ⟨hxX, hxK⟩, rfl⟩⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  have hxO' : x ∈ pCoreOf 2 K := by
    rw [pCoreOf_two_eq_map]
    exact ⟨_, hx1, rfl⟩
  have hbot' := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hXo
  have : x ∈ pCoreOf 2 K ⊓ X := ⟨hxO', hxX⟩
  rwa [hbot'] at this

theorem sup_xOne_k0Of_eq (hLevi : FactL34Levi) (hT : FactPGL34Torus) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) :
    K ⊔ xOne X (k0Of K P₂) = K ⊔ xOne X (LOf L V₁) := by
  have hXK : X ≤ K ⊔ xOne X (LOf L V₁) :=
    cL.a.trans (sup_le le_sup_right (inf_le_right.trans (h.L₁_le_K.trans le_sup_left)))
  refine le_antisymm (sup_le le_sup_left (inf_le_left.trans hXK)) (sup_le le_sup_left ?_)
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun _ hx =>
    cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx
  have hcard := card_cartan cL hXN
    (cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan)
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  have hAN : X ⊓ K ≤ Subgroup.normalizer (xOne X (k0Of K P₂) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hc : a * b * a⁻¹ = b := by
        have := hcomm.is_comm.comm (⟨a, ha.1⟩ : ↥X) ⟨b, hb.1⟩
        have h' := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h'
        rw [h', mul_assoc, mul_inv_cancel, mul_one]
      rwa [hc]
    · intro hb
      have hc : a * b * a⁻¹ = b := by
        have hbX : b ∈ X := by
          have := X.mul_mem (X.mul_mem (X.inv_mem ha.1) hb.1) ha.1
          simpa [mul_assoc] using this
        have := hcomm.is_comm.comm (⟨a, ha.1⟩ : ↥X) ⟨b, hbX⟩
        have h' := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h'
        rw [h', mul_assoc, mul_inv_cancel, mul_one]
      rwa [← hc]
  have hAB : xOne X (k0Of K P₂) ⊓ (X ⊓ K) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← h.xOne_k0Of_inf_eq_bot hLevi hN h1102 hP]
    exact ⟨hx.1, hx.2.2⟩
  have h3A : 3 ∣ Nat.card ↥(X ⊓ K) := by
    rw [← cL.card₁]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left X h.L₁_le_K)
  have h3B := three_dvd_card_of_le inf_le_left hcard (h.xOne_k0Of_ne_bot hT hN h1102 cL hP)
  have hX := sup_eq_of_inf_eq_bot inf_le_left inf_le_left hAB hAN hcard h3A h3B
  calc xOne X (LOf L V₁) ≤ X := inf_le_left
    _ = (X ⊓ K) ⊔ xOne X (k0Of K P₂) := hX.symm
    _ ≤ K ⊔ xOne X (k0Of K P₂) := sup_le_sup_right inf_le_right _

theorem pgl_k0Of (hLevi : FactL34Levi) (hT : FactPGL34Torus) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X)
    (hP : ParData T K (LOf L V₁) P₁ P₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(K ⊔ xOne X (k0Of K P₂)) ⧸ CFSG.pCore 2 ↥(K ⊔ xOne X (k0Of K P₂)) ≃*
        (Matrix.GeneralLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))) := by
  have key : ∀ A : Subgroup G, A = K ⊔ xOne X (LOf L V₁) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥A ⧸ CFSG.pCore 2 ↥A ≃* (Matrix.GeneralLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))) := by
    rintro A rfl
    exact h.pgl
  exact key _ (h.sup_xOne_k0Of_eq hLevi hT hN h1102 cL hP)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
