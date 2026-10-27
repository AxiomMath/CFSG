module

public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch11SecSX1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pCoreOf_of_mem_sectionCentralizer {B : Subgroup G} {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    B ⊓ sectionCentralizer B (pCoreOf 2 B) ≤ pCoreOf 2 B := by
  rintro y ⟨hyB, -, -, hyc⟩
  have hnorm : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  set φ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hz : φ ⟨y, hyB⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := hφs g
    have h2 : (⟨y, hyB⟩ : ↥B) * l * (⟨y, hyB⟩ : ↥B)⁻¹ * l⁻¹ ∈ CFSG.pCore 2 ↥B := by
      have h1 := hyc l l.2
      rw [pCoreOf_two_eq_map] at h1
      obtain ⟨w, hw, hwe⟩ := h1
      have : w = (⟨y, hyB⟩ : ↥B) * l * (⟨y, hyB⟩ : ↥B)⁻¹ * l⁻¹ :=
        Subtype.ext (by simpa using hwe)
      rw [← this]
      exact hw
    have h3 : φ ((⟨y, hyB⟩ : ↥B) * l * (⟨y, hyB⟩ : ↥B)⁻¹ * l⁻¹) = 1 := by
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr h2, map_one]
    simp only [map_mul, map_inv] at h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hsimple := isSimpleGroup_SL2 hn hK
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_SL2 (exists_finset_card_four hn hK)
  have hcbot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := h ▸ Subgroup.mem_top x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hx z)]
  rw [hcbot, Subgroup.mem_bot] at hz
  have hk : (⟨y, hyB⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    exact hz
  rw [pCoreOf_two_eq_map]
  exact ⟨_, hk, rfl⟩

variable {T L I V₁ V₂ X : Subgroup G} {n : ℕ}

theorem cartan_inf_lOf_inf_sectionCentralizer (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    X ⊓ LOf L V₁ ⊓ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
  have hle := le_pCoreOf_of_mem_sectionCentralizer h.one_lt hF e
  have hodd := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₁)) hX.2.1
  refine eq_bot_iff.mpr fun x hx => ?_
  have : x ∈ pCoreOf 2 (LOf L V₁) ⊓ X := ⟨hle ⟨hx.1.2, hx.2⟩, hx.1.1⟩
  rw [hodd] at this
  exact this

omit [Finite G] in
theorem card_cartan (hc : CartanL L V₁ V₂ X)
    (hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G))
    (hbot : X ⊓ LOf L V₁ ⊓ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) = ⊥) :
    Nat.card ↥X = 9 := by
  set N := X ⊓ LOf L V₁
  set A := xOne X (LOf L V₁)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.1, hXN hx.1⟩
  have hX : X = A ⊔ N := le_antisymm hc.a (sup_le inf_le_left inf_le_left)
  have hNA : N ⊓ A = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← hbot]
    exact ⟨hx.1, hx.2.2⟩
  have h2 := Subgroup.relIndex_mul_card N A
  rw [hNA, Subgroup.card_bot, mul_one, hc.cardX₁] at h2
  have h3 := Subgroup.relIndex_mul_card N (A ⊔ N)
  rw [relIndex_sup_eq' hAN, h2, inf_eq_left.mpr le_sup_right, hc.card₁] at h3
  rw [hX, ← h3]

omit [Finite G] in
theorem pow_three_cartan (hc : CartanL L V₁ V₂ X)
    (hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G))
    (hbot : X ⊓ LOf L V₁ ⊓ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) = ⊥)
    {x : G} (hx : x ∈ X) : x ^ 3 = 1 := by
  have hcard := card_cartan hc hXN hbot
  have hcomm : IsMulCommutative ↥X :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  set N := X ⊓ LOf L V₁
  set A := xOne X (LOf L V₁)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy.1, hXN hy.1⟩
  have hx' : x ∈ (↑(N ⊔ A) : Set G) := by
    rw [sup_comm]
    exact hc.a hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N A hAN] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := hx'
  have hu3 : u ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥N) (x := ⟨u, hu⟩)
    rw [hc.card₁] at this
    simpa using congrArg Subtype.val this
  have hv3 : v ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := ⟨v, hv⟩)
    rw [hc.cardX₁] at this
    simpa using congrArg Subtype.val this
  have huv : Commute u v := by
    have := hcomm.is_comm.comm (⟨u, (hu : u ∈ N).1⟩ : ↥X) ⟨v, (hv : v ∈ A).1⟩
    exact congrArg Subtype.val this
  show (u * v) ^ 3 = 1
  rw [huv.mul_pow, hu3, hv3, one_mul]

end CFSG.Quasithin.Vol2.Ch11.SecS
