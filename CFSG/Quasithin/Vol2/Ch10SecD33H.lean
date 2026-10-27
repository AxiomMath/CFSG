module

public import CFSG.Quasithin.Vol2.Ch10SecD33G
public import CFSG.Quasithin.Vol2.Ch10SecD32
public import CFSG.Quasithin.Vol2.Ch10SecD33C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem eq_or_eq_of_mem_cComp_le (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    {L : Subgroup G} (hL : L ∈ cComp X) (hLK : L ≤ K₁ ⊔ CFSG.conjugate K₁ s) :
    L = K₁ ∨ L = CFSG.conjugate K₁ s := by
  by_contra hne
  push Not at hne
  have hK₂ := conjugate_mem_cComp hK₁ hs
  have h31 := (Vol2Native.lemma_1_2_1_two hK h37 hX hL hK₁ hne.1).1
  have h32 := (Vol2Native.lemma_1_2_1_two hK h37 hX hL hK₂ hne.2).1
  have hN : K₁ ⊔ CFSG.conjugate K₁ s ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (le_normalizer_of_mem_cComp hL hK₁) (le_normalizer_of_mem_cComp hL hK₂)
  have hle : L ≤ pCoreOf 2 L := by
    calc L = ⁅L, L⁆ := (perfect_of_mem_cComp hL).symm
      _ ≤ ⁅L, K₁ ⊔ CFSG.conjugate K₁ s⁆ := Subgroup.commutator_mono le_rfl hLK
      _ = ⁅L, K₁⁆ ⊔ ⁅L, CFSG.conjugate K₁ s⁆ :=
        SecA.commutator_sup_left_of_le hLK le_sup_left le_sup_right hN
      _ ≤ pCoreOf 2 L := sup_le (h31.trans inf_le_left) (h32.trans inf_le_left)
  exact not_isSolvable_of_mem_cComp hL
    (E1.isSolvable_of_isPGroup_two ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hle))

theorem card_le_two_mul_card_inf_normalizer (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {X K₁ T : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥)
    (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X) (hTX : T ≤ X)
    (hTK : T ≤ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G)) :
    Nat.card T ≤ 2 * Nat.card ↥(T ⊓ Subgroup.normalizer (K₁ : Set G)) := by
  have key : ∀ a ∈ T, a ∉ Subgroup.normalizer (K₁ : Set G) →
      CFSG.conjugate K₁ a = CFSG.conjugate K₁ s := by
    intro a ha han
    have hL := conjugate_mem_cComp hK₁ (hTX ha)
    have hLK : CFSG.conjugate K₁ a ≤ K₁ ⊔ CFSG.conjugate K₁ s := by
      rw [← SecA.conjugate_eq_self_iff.mpr (hTK ha)]
      exact SecA.conjugate_mono le_sup_left a
    rcases eq_or_eq_of_mem_cComp_le hK h37 hX hK₁ hs hL hLK with h1 | h1
    · exact absurd (SecA.conjugate_eq_self_iff.mp h1) han
    · exact h1
  exact card_le_two_mul_card_inf fun a ha b hb han hbn =>
    SecA.mul_inv_mem_normalizer_of_conjugate_eq ((key a ha han).trans (key b hb hbn).symm)

theorem le_pCoreOf_of_barCent (hW : FactSymFiveWrTwo) {X K₁ K₂ H : Subgroup G}
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hHX : H ≤ X) (hK₁X : IsSubnormal K₁ X)
    (hK₂X : IsSubnormal K₂ X) (h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (hO : oTwoUpper H ≤ K₁ ⊔ K₂) (hX2 : pCoreOf 2 X ≤ H) {u : G} (huH : u ∈ H)
    (hu1 : u ∈ barCent K₁) (hu2 : u ∈ barCent K₂) : u ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : pCoreOf 2 X ≤ pCoreOf 2 H :=
    le_pCoreOf_of_normalizes hX2 (hHX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hK₁H := (A4.pCoreOf_le_of_subnormal 2 hK₁X).trans hXH
  have hK₂H := (A4.pCoreOf_le_of_subnormal 2 hK₂X).trans hXH
  have hcomm : ∀ x ∈ oTwoUpper H, u * x * u⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
    intro x hx
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer h12 (hO hx)
    have hc₁ := (mem_barCent_iff.mp hu1).2 k₁ hk₁
    have hc₂ := (mem_barCent_iff.mp hu2).2 k₂ hk₂
    have hc₂' : k₁ * (u * k₂ * u⁻¹ * k₂⁻¹) * k₁⁻¹ ∈ pCoreOf 2 K₂ :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pCoreOf (h12 hk₁)) _).mp hc₂
    have e1 : u * (k₁ * k₂) * u⁻¹ * (k₁ * k₂)⁻¹ =
        (u * k₁ * u⁻¹ * k₁⁻¹) * (k₁ * (u * k₂ * u⁻¹ * k₂⁻¹) * k₁⁻¹) := by group
    rw [e1]
    exact (pCoreOf 2 H).mul_mem (hK₁H hc₁) (hK₂H hc₂')
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hcent : e (π ⟨u, huH⟩) ∈
      Subgroup.centralizer (oTwoUpper (⊤ : Subgroup SymFiveWrTwo) : Set SymFiveWrTwo) := by
    have hO2 : oTwoUpper (⊤ : Subgroup SymFiveWrTwo) =
        ((oTwoUpper (⊤ : Subgroup ↥H)).map π).map e.toMonoidHom := by
      rw [← oTwoUpper_map, ← oTwoUpper_map, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _), Subgroup.map_top_of_surjective _ e.surjective]
    rw [hO2, Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨h', hh', rfl⟩, rfl⟩
    have hh'G : (h' : G) ∈ oTwoUpper H := by
      have := oTwoUpper_map H.subtype (⊤ : Subgroup ↥H)
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
      rw [this]
      exact ⟨h', hh', rfl⟩
    have hc := hcomm _ hh'G
    have hmk : π (⟨u, huH⟩ * h' * (⟨u, huH⟩ : ↥H)⁻¹ * h'⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hye⟩ := hc
      have : y = ⟨u, huH⟩ * h' * (⟨u, huH⟩ : ↥H)⁻¹ * h'⁻¹ := Subtype.ext hye
      rw [← this]
      exact hy
    simp only [map_mul, map_inv] at hmk
    change e (π h') * e (π ⟨u, huH⟩) = e (π ⟨u, huH⟩) * e (π h')
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmk
    rw [← map_mul e, ← map_mul e, hmk.symm]
  rw [hW.2, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcent
  exact ⟨_, hcent, rfl⟩

theorem relIndex_pCoreOf_eq {H T : Subgroup G} (hT : IsSylowTwoOf T H)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) : (pCoreOf 2 H).relIndex T = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 H ≤ T := IsSylowTwoOf.pCoreOf_le hT
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hT.2.1
  have hH : Nat.card H = 2 ^ 7 * 225 * 2 ^ a := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
    rw [Nat.card_congr e.toEquiv, card_symFiveWrTwo] at h1
    have h2 : Nat.card (CFSG.pCore 2 ↥H) = Nat.card (pCoreOf 2 H) := by
      exact (Subgroup.card_map_of_injective H.subtype_injective).symm
    rw [h1, h2, ha]
    norm_num
  have hTr : Nat.card T * T.relIndex H = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := T) (K := H)
    rw [inf_eq_left.mpr hT.1] at this
    rw [mul_comm, this]
  have hodd : ¬ 2 ∣ T.relIndex H := hT.2.2
  rw [hb, hH] at hTr
  have hr0 : T.relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hv := congrArg (padicValNat 2) hTr
  rw [padicValNat.mul (by positivity) hr0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 225)] at hv
  have hOr : Nat.card (pCoreOf 2 H) * (pCoreOf 2 H).relIndex T = Nat.card T := by
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 H) (K := T)
    rw [inf_eq_left.mpr hOT] at this
    rw [mul_comm, this]
  rw [ha, hb, show b = a + 7 by omega, pow_add] at hOr
  have := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ a) hOr
  rw [this]
  norm_num

omit [Finite G] in
theorem relIndex_barCent_le_four (hA : FactPSL2NormA5) {K₁ H T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTH : T ≤ H) {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hA5 : Nonempty (↥(barSub K₁ (H ⊓ K₁)) ≃* alternatingGroup (Fin 5))) :
    (T ⊓ barCent K₁).relIndex (T ⊓ Subgroup.normalizer (K₁ : Set G)) ≤ 4 := by
  set T₁ := T ⊓ Subgroup.normalizer (K₁ : Set G) with hT₁
  let ψ : ↥T₁ →* MulAut PSL(2, ZMod p) := (MulAut.congr φ).toMonoidHom.comp
    ((barAct K₁).comp (Subgroup.inclusion (inf_le_right : T₁ ≤ _)))
  have hB2 : IsPGroup 2 ψ.range :=
    IsPGroup.of_surjective ((hT2.to_le inf_le_left : IsPGroup 2 T₁)) ψ.rangeRestrict
      ψ.rangeRestrict_surjective
  set A' := (barSub K₁ (H ⊓ K₁)).map φ.toMonoidHom with hA'
  have hA'5 : Nonempty (↥A' ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e5⟩ := hA5
    exact ⟨((barSub K₁ (H ⊓ K₁)).equivMapOfInjective _ φ.injective).symm.trans e5⟩
  have hnorm : ∀ b ∈ ψ.range, A'.map (b : MulAut PSL(2, ZMod p)).toMonoidHom = A' := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    have hmap := map_barSub_barAct (H := H) hu.2 (Subgroup.le_normalizer (hTH hu.1))
    rw [hA', Subgroup.map_map]
    have hcomp : (ψ ⟨u, hu⟩ : MulAut PSL(2, ZMod p)).toMonoidHom.comp φ.toMonoidHom =
        φ.toMonoidHom.comp (barAct K₁ ⟨u, hu.2⟩ : MulAut _).toMonoidHom := by
      ext x
      simp [ψ, MulAut.congr_apply]
      rfl
    rw [hcomp, ← Subgroup.map_map, hmap]
  have hB4 := hA p Fact.out hp7 A' hA'5 ψ.range hB2 hnorm
  have hker : (T ⊓ barCent K₁).subgroupOf T₁ = ψ.ker := by
    ext ⟨u, hu⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hψ : ψ ⟨u, hu⟩ = MulAut.congr φ (barAct K₁ ⟨u, hu.2⟩) := rfl
    rw [hψ, MulEquiv.map_eq_one_iff]
    constructor
    · rintro ⟨-, hu1⟩
      exact (mem_barCent_iff_barAct hu.2).mp hu1
    · intro h1
      exact ⟨hu.1, (mem_barCent_iff_barAct hu.2).mpr h1⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  exact hB4

theorem false_of_alt5 (hW : FactSymFiveWrTwo) (hA : FactPSL2NormA5) (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {X K₁ H T : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥)
    (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ T)
    (hTK : T ≤ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G))
    (hT : IsSylowTwoOf T X) (hTH : T ≤ H) (hHX : H ≤ X)
    (hO : oTwoUpper H ≤ K₁ ⊔ CFSG.conjugate K₁ s) (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo)
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hA5 : Nonempty (↥(barSub K₁ (H ⊓ K₁)) ≃* alternatingGroup (Fin 5))) : False := by
  set K₂ := CFSG.conjugate K₁ s with hK₂def
  have hsX : s ∈ X := hT.1 hs
  have hK₂ : K₂ ∈ cComp X := conjugate_mem_cComp hK₁ hsX
  have h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := le_normalizer_of_mem_cComp hK₂ hK₁
  have hTsH : IsSylowTwoOf T H := A4.isSylowTwoOf_mono hT hTH hHX
  have h128 := relIndex_pCoreOf_eq hTsH e
  have hX2 : pCoreOf 2 X ≤ H := (IsSylowTwoOf.pCoreOf_le hT).trans hTH
  set C₁ := T ⊓ barCent K₁ with hC₁
  set C₂ := T ⊓ barCent K₂ with hC₂
  have hD : C₁ ⊓ C₂ ≤ pCoreOf 2 H := fun u hu =>
    le_pCoreOf_of_barCent hW e hHX (subnormal_of_mem_cComp hK₁) (subnormal_of_mem_cComp hK₂)
      h12 hO hX2 (hTH hu.1.1) hu.1.2 hu.2.2
  set T₁ := T ⊓ Subgroup.normalizer (K₁ : Set G) with hT₁
  have hC₁T₁ : C₁ ≤ T₁ := le_inf inf_le_left fun u hu => (mem_barCent_iff.mp hu.2).1
  have hT₁T : T₁ ≤ T := inf_le_left
  have hT₁2 : T₁.relIndex T ≤ 2 := by
    have h1 : Nat.card ↥T ≤ 2 * Nat.card ↥T₁ :=
      card_le_two_mul_card_inf_normalizer hK h37 hX hK₁ hsX hT.1 hTK
    have h2 := Subgroup.relIndex_mul_card (H := T₁) (K := T)
    rw [inf_eq_left.mpr hT₁T] at h2
    have hpos : 0 < Nat.card ↥T₁ := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : 3 * Nat.card ↥T₁ ≤ Nat.card ↥T := by
      rw [← h2]
      exact Nat.mul_le_mul_right _ hlt
    omega
  have hC₁4 := relIndex_barCent_le_four hA hT.2.1 hTH hp7 φ hA5
  have hC₁8 : C₁.relIndex T ≤ 8 := by
    rw [← Subgroup.relIndex_mul_relIndex C₁ T₁ T hC₁T₁ hT₁T]
    calc C₁.relIndex T₁ * T₁.relIndex T ≤ 4 * 2 := Nat.mul_le_mul hC₁4 hT₁2
      _ = 8 := by norm_num
  have hC₂eq : C₂ = CFSG.conjugate C₁ s := by
    rw [hC₂, hC₁, SecA.conjugate_eq_map, Subgroup.map_inf _ _ _ (MulAut.conj s⁻¹).injective,
      ← SecA.conjugate_eq_map, ← SecA.conjugate_eq_map,
      SecA.conjugate_eq_self_iff.mpr (Subgroup.le_normalizer hs), barCent_conjugate]
  have hC₂8 : C₂.relIndex T ≤ 8 := by
    rw [hC₂eq, ← SecA.conjugate_eq_self_iff.mpr (Subgroup.le_normalizer hs),
      SecA.conjugate_eq_map, SecA.conjugate_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s⁻¹).injective]
    exact hC₁8
  have h1 : (pCoreOf 2 H).relIndex T ≤ (C₁ ⊓ C₂).relIndex T :=
    Subgroup.relIndex_le_of_le_left hD Subgroup.index_ne_zero_of_finite
  have h2 : (C₁ ⊓ C₂).relIndex T ≤ C₁.relIndex T * C₂.relIndex T := Subgroup.relIndex_inf_le
  have h3 : C₁.relIndex T * C₂.relIndex T ≤ 8 * 8 := Nat.mul_le_mul hC₁8 hC₂8
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
