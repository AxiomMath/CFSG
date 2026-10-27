module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZB
public import CFSG.Quasithin.Vol2.Ch10SecE9U
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped MatrixGroups

namespace E9

theorem not_dvd_card_of_sl3 {Y : Type*} [Group Y] [Finite Y]
    (e : Y ⧸ CFSG.pCore 2 Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {r : ℕ}
    (hr : r.Prime) (h24 : r % 24 = 11 ∨ r % 24 = 13 ∨ r = 5) : ¬ r ∣ Nat.card Y := fun h => by
  rcases eq_three_or_seven e hr (by omega) h with h | h <;> omega

theorem inf_oddCore_eq_bot {Q : Type} [Group Q] [Finite Q] {I K : Subgroup Q} (hKI : K ≤ I)
    {p : ℕ} [Fact p.Prime] (h24 : p % 24 = 11 ∨ p % 24 = 13)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* PSL(2, ZMod p)) :
    K.subgroupOf I ⊓ CFSG.oddCore ↥I = ⊥ := by
  have : ((CFSG.oddCore ↥I).comap (Subgroup.inclusion hKI)).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hodd : Odd (Nat.card ((CFSG.oddCore ↥I).comap (Subgroup.inclusion hKI))) :=
    (CFSG.ABGLocalTools.odd_card_oddCore (H := ↥I)).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKI))
  have hbot := eq_bot_of_normal_of_odd h24 e hodd
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxO⟩
  have hx : (⟨(x : Q), hxK⟩ : ↥K) ∈ (CFSG.oddCore ↥I).comap (Subgroup.inclusion hKI) := hxO
  rw [hbot, Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot]
  have h1 : (x : Q) = 1 := congrArg Subtype.val hx
  exact Subtype.ext h1

theorem subgroupOf_sup_eq_top {Q : Type} [Group Q] {B O Y : Subgroup Q} (h : Y = B ⊔ O) :
    B.subgroupOf Y ⊔ O.subgroupOf Y = ⊤ := by
  rw [← Subgroup.subgroupOf_sup (h ▸ le_sup_left) (h ▸ le_sup_right), ← h,
    Subgroup.subgroupOf_self]

end E9

variable {G : Type} [Group G] [Finite G]

theorem false_of_le (hList : Vol2Native.A312ListFactsCat)
    (hSL2 : A312SL2Fact) (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hKG : FactA312L32RankOne) (hK : LocalSQTK G)
    (hqtke : quasithinIsQTKECat G) {H S X K K' I I' : Subgroup G} (hH2 : pCoreOf 2 H ≠ ⊥)
    (hS : IsSylowTwoOf S H) (hXfam : X ∈ lFamily S)
    (eX : ModO2 X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hIc : I ∈ cComp H)
    (hI'c : I' ∈ cComp H) (hII' : I ≠ I') (hXI : X ≤ I) (hKI : K ≤ I) (hK'I' : K' ≤ I')
    {p : ℕ} [hp : Fact p.Prime] (h24 : p % 24 = 11 ∨ p % 24 = 13)
    (e : ModO2 K ≃* PSL(2, ZMod p)) (e' : ModO2 K' ≃* PSL(2, ZMod p)) : False := by
  have hIH : I ≤ H := le_of_mem_cComp hIc
  have hXH := hXI.trans hIH
  have hKH := hKI.trans hIH
  have hK'H : K' ≤ H := hK'I'.trans (le_of_mem_cComp hI'c)
  have hX : ModO2 (modO2Image H X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (nonempty_modO2_modO2Image hXH).some.trans eX
  have eK : ModO2 (modO2Image H K) ≃* PSL(2, ZMod p) :=
    (nonempty_modO2_modO2Image hKH).some.trans e
  have hpK : p ∣ Nat.card (modO2Image H K) :=
    (Dvd.intro_left 12 rfl).trans (E9.twelve_mul_dvd_card_of h24 eK)
  have hpX : ¬ p ∣ Nat.card (modO2Image H X) := E9.not_dvd_card_of_sl3 hX hp.out (by omega)
  have h5X : ¬ 5 ∣ Nat.card (modO2Image H X) := E9.not_dvd_card_of_sl3 hX (by norm_num) (by omega)
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH2
  obtain ⟨L', -, -, huniq, hcases⟩ := a312Refined_of_facts hList hSL2 h36 h37 h39 hQ _
    (isSylowTwoOf_modO2Image hS) _ (modO2Image_mem_lFamily hS hXH hXfam)
  obtain rfl : modO2Image H I = L' :=
    huniq _ (modO2Image_mem_cComp hIc) (modO2Image_mono' hXI)
  have hKI' : modO2Image H K ≤ modO2Image H I := modO2Image_mono' hKI
  have hXI' : modO2Image H X ≤ modO2Image H I := modO2Image_mono' hXI
  rcases hcases with heq | ⟨-, hcase⟩ | ⟨-, hnonq⟩
  ·
    exact hpX (hpK.trans (Subgroup.card_dvd_of_le (heq ▸ hKI')))
  ·
    have := E9.isSimpleGroup_psl2 h24 (p := p)
    have h3K' : 3 ∣ Nat.card (ModO2 K') :=
      (Dvd.intro (4 * p) (by ring)).trans ((Nat.card_congr e'.toEquiv).symm ▸
        E9.twelve_mul_dvd_card h24)
    have hrk := pRank_modO2Image_le_one hqtke hH2 (commutator_le_pCoreOf_H hK h37 hH2 hIc hI'c hII')
      hK'I' hK'H e'.isSimpleGroup (E9.exists_mul_ne_mul_psl2 h24 e') Nat.prime_three (by norm_num)
      h3K'
    have h1 := hKG _ _ _ hcase ⟨hX⟩ hrk p hp.out (hpK.trans (Subgroup.card_dvd_of_le hKI'))
    omega
  · unfold A312Nonquasi at hnonq
    dsimp only at hnonq
    rcases hnonq with ⟨-, h21, -⟩ | ⟨-, -, N, hNn, hNeq, h5⟩
    ·
      have htop := E9.subgroupOf_sup_eq_top h21
      rw [show ((CFSG.oddCore ↥(modO2Image H I)).map (modO2Image H I).subtype).subgroupOf
          (modO2Image H I) = CFSG.oddCore ↥(modO2Image H I) from
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _] at htop
      have h1 := E9.card_quotient_dvd_of_sup_eq_top htop
      have h2 := E9.card_dvd_card_quotient_of_inf_eq_bot (E9.inf_oddCore_eq_bot hKI' h24 eK)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXI').toEquiv] at h1
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKI').toEquiv] at h2
      exact hpX (hpK.trans (h2.trans h1))
    ·
      have htop := E9.subgroupOf_sup_eq_top (Q := ↥H ⧸ CFSG.pCore 2 ↥H)
        (rfl : modO2Image H X ⊔ (CFSG.oddCore ↥(modO2Image H I)).map (modO2Image H I).subtype =
          _)
      rw [← hNeq] at htop
      have h1 := E9.card_quotient_dvd_of_sup_eq_top htop
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h1
      exact h5X ((E9.five_dvd_card_of_isSL2 h5).trans h1)

end CFSG.Quasithin.Vol2.Ch10.SecB
