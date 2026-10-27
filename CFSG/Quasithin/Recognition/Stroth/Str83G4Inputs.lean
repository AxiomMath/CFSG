module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4X1Z1
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Reduction

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem str83G4_exists_d1_of_d2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ δ ∈ d.D2, ∃ x ∈ d.D1,
      ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
  classical
  have hF : F112HypW L1 L2 S := hfr.1
  have ha : 1 ≤ a := hfr.2.2.1
  have hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a) := hfr.2.2.2.1
  have hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) := hfr.2.2.2.2.1
  have hBT2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hcardD2 : Nat.card ↥d.D2 = 2 ^ (2 * a + 1) - 1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h2.sylow d.hD2hall d.hD2sup hBT2).1
  obtain ⟨eSz⟩ := hSz
  have hBT1 : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha
      (eSz.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hcardD1 : Nat.card ↥d.D1 = 2 ^ (2 * a + 1) - 1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow d.hD1hall d.hD1sup hBT1).1
  let f : ↥d.D1 → ↥d.D2 := fun x =>
    ⟨Classical.choose (str83G4_exists_delta_two hfr d x.2),
      (Classical.choose_spec (str83G4_exists_delta_two hfr d x.2)).1⟩
  have hf : ∀ x : ↥d.D1, ∀ l ∈ L2,
      ((x : G) * (f x : G)⁻¹) * l * ((x : G) * (f x : G)⁻¹)⁻¹ * l⁻¹ ∈
        pCoreOf 2 L2 :=
    fun x => (Classical.choose_spec (str83G4_exists_delta_two hfr d x.2)).2
  set H2 : Subgroup G := centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 with hH2
  have hbigBV : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := by
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    exact ((F1.bigB_le_normalizer_left hR).2).trans (normalizer_le_normalizer_pCoreOf 2 L2)
  have hBigB : d.D1 ⊔ d.D2 ≤ bigB L1 L2 S :=
    sup_le (d.hD1hall.1.trans (le_sup_left.trans le_sup_left))
      (d.hD2hall.1.trans (le_sup_right.trans le_sup_left))
  have hmemH2 : ∀ x : ↥d.D1, (x : G) * (f x : G)⁻¹ ∈ H2 := by
    intro x
    have hxD : (x : G) * (f x : G)⁻¹ ∈ d.D1 ⊔ d.D2 :=
      Subgroup.mul_mem_sup x.2 (d.D2.inv_mem (f x).2)
    rw [hH2]
    exact mem_centralizerMod.mpr ⟨hxD, hbigBV (hBigB hxD), hf x⟩
  have hD1infH2 : d.D1 ⊓ H2 = ⊥ := by
    rw [hH2]
    exact str83G4_d1_inf_h2_eq_bot hfr d hX hB
  have hinj : Function.Injective f := by
    intro x y hxy
    have hδ : (f x : G) = (f y : G) := congrArg Subtype.val hxy
    have hmem : (x : G) * (y : G)⁻¹ ∈ H2 := by
      have heq : (x : G) * (y : G)⁻¹ =
          ((x : G) * (f x : G)⁻¹) * ((y : G) * (f y : G)⁻¹)⁻¹ := by
        rw [hδ]
        group
      rw [heq]
      exact H2.mul_mem (hmemH2 x) (H2.inv_mem (hmemH2 y))
    have hmemD : (x : G) * (y : G)⁻¹ ∈ d.D1 :=
      d.D1.mul_mem x.2 (d.D1.inv_mem y.2)
    have hbot : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hD1infH2]
      exact ⟨hmemD, hmem⟩
    exact Subtype.ext (eq_of_mul_inv_eq_one (Subgroup.mem_bot.mp hbot))
  have hsurj : Function.Surjective f := by
    letI : Fintype ↥d.D1 := Fintype.ofFinite _
    letI : Fintype ↥d.D2 := Fintype.ofFinite _
    have hcard : Fintype.card ↥d.D1 = Fintype.card ↥d.D2 := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardD1, hcardD2]
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp hinj
  intro δ hδ
  obtain ⟨x, hx⟩ := hsurj ⟨δ, hδ⟩
  have hfx : (f x : G) = δ := congrArg Subtype.val hx
  refine ⟨x, x.2, fun l hl => ?_⟩
  rw [← hfx]
  exact hf x l hl

theorem str83G4_exists_data_d1_sup_conjugate_d1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∃ d' : Str83G4Data L1 L2 S, d'.D1 = d.D1 ∧ d'.D2 = d.D2 ∧
      ¬ CFSG.conjugate (str83X L1 L2 S) d'.w ≤ Q1 L1 L2 S ∧
      d'.D1 ⊔ CFSG.conjugate d'.D1 d'.w = d'.D1 ⊔ d'.D2 := by
  obtain ⟨d', hD1, hD2, hcent⟩ := str83G4_exists_data_centralizer hfr d
  have hcent' : d'.w ∈ Subgroup.centralizer
      (centralizerMod (pCoreOf 2 L2) (d'.D1 ⊔ d'.D2) L2 : Set G) := by
    rw [hD1, hD2]
    exact hcent
  have hsurj : ∀ δ ∈ d'.D2, ∃ x ∈ d'.D1,
      ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
    intro δ hδ
    obtain ⟨x, hx, hspec⟩ := str83G4_exists_d1_of_d2 hfr d hX hB δ (hD2 ▸ hδ)
    exact ⟨x, hD1.symm ▸ hx, hspec⟩
  refine ⟨d', hD1, hD2, ?_, ?_⟩
  · intro hconj
    have hR : str83R L1 L2 S ≤ Q1 L1 L2 S :=
      (str83G4_str83R_le_q1_iff hfr d').mpr hconj
    exact hB ((str83G4_str83R_le_q1_iff hfr d).mp hR)
  · exact str83G4_d1_sup_conjugate_d1 hfr d' hcent' hsurj

theorem str83G4_mem_z1_of_commutator_mem_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ k ∈ d.D1, k ≠ 1 → ∀ x ∈ str83X L1 L2 S,
      k * x * k⁻¹ * x⁻¹ ∈ Z1 L1 L2 S → x ∈ Z1 L1 L2 S := by
  have hX1 := str83G4_x1_eq_z1 hfr d hX hB
  intro k hk hk1 x hx hcomm
  have hcomm' : k * x * k⁻¹ * x⁻¹ ∈ str83X1 L1 L2 S := le_of_eq hX1.symm hcomm
  have hx1 : x ∈ str83X1 L1 L2 S :=
    str83G4_mem_x1_of_commutator_mem_x1 hfr d hX hB hk hk1 hx hcomm'
  exact le_of_eq hX1 hx1

theorem str83G4_not_x_inf_conjugate_x_le_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ¬ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Z2 L1 L2 S := by
  classical
  have hIX := str83G4_relIndex_x_inf_conjugate_x hfr d hX hB
  have hZ1X := str83G4_relIndex_z1_x hfr d hX hB
  have hZ2 := str83G4_card_z2 hfr d hX hB
  let I : Subgroup G := str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w
  have hIX' : I.relIndex (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := hIX
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwP2 : d.w ∈ P2 L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
  have hwZ : d.w ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hwP2
  have hZ2le : Z2 L1 L2 S ≤ I := by
    refine le_inf (z2_le_str83X L1 L2 S) ?_
    calc Z2 L1 L2 S = CFSG.conjugate (Z2 L1 L2 S) d.w :=
          (CFSG.conjugate_eq_self_of_mem_normalizer hwZ).symm
      _ ≤ CFSG.conjugate (str83X L1 L2 S) d.w := Subgroup.map_mono (z2_le_str83X L1 L2 S)
  have hZ1Xle : Z1 L1 L2 S ≤ str83X L1 L2 S := str83G4_z1_le_x hfr
  have hZ1card : Nat.card (Z1 L1 L2 S) = 2 ^ (2 * a + 1) :=
    str83G4Z1Card_holds G L1 L2 S a hfr
  intro hle
  have hIeq : I = Z2 L1 L2 S := le_antisymm hle hZ2le
  have hIleX : I ≤ str83X L1 L2 S := inf_le_left
  have hIcard : Nat.card ↥I = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hIeq, hZ2]
  have hXcard1 : Nat.card (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4 := by
    have h := Subgroup.relIndex_mul_card (H := I) (K := str83X L1 L2 S)
    rw [inf_of_le_left hIleX] at h
    rw [hIX', hIcard] at h
    rw [← h]
    ring
  have hXcard2 : Nat.card (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 5 := by
    have h := Subgroup.relIndex_mul_card (H := Z1 L1 L2 S) (K := str83X L1 L2 S)
    rw [inf_of_le_left hZ1Xle] at h
    rw [hZ1X, hZ1card] at h
    rw [← h]
    ring
  have h45 : (2 ^ (2 * a + 1)) ^ 4 = (2 ^ (2 * a + 1)) ^ 5 := by
    rw [← hXcard1, hXcard2]
  exact absurd (Nat.pow_right_injective hq2 h45) (by norm_num)

theorem str83G4_eq_one_of_mem_d1_of_commutator_mem_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1 := by
  classical
  have hfpf := str83G4_mem_z1_of_commutator_mem_z1 hfr d hX hB
  have hIZ2 := str83G4_not_x_inf_conjugate_x_le_z2 hfr d hX hB
  have hF : F112HypW L1 L2 S := hfr.1
  have hSn : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := hfr.2.1
  have ha : 1 ≤ a := hfr.2.2.1
  have hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a) := hfr.2.2.2.1
  have hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) := hfr.2.2.2.2.1
  have hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    hfr.2.2.2.2.2
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str83_caseI_basics hF hSn ha hSz hL2 hZI).2.1
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) := isElemAbelian_z2
  have hA : ∀ c ∈ Z2 L1 L2 S, c * c = 1 := by
    intro c hc
    have h := hZ2ea.2 c hc
    rwa [pow_two] at h
  have hAc : ∀ c ∈ Z2 L1 L2 S, ∀ e ∈ Z2 L1 L2 S, c * e = e * c :=
    fun c hc e he => congrArg Subtype.val (hZ2ea.1.is_comm.comm ⟨c, hc⟩ ⟨e, he⟩)
  have hP2NZ2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)
  have hD1P2 : d.D1 ≤ P2 L1 L2 S :=
    d.hD1hall.1.trans ((le_sup_left.trans le_sup_left).trans le_sup_right)
  have hD1sup : d.D1 ≤ L1 ⊔ S :=
    d.hD1hall.1.trans ((F1.borelOf_le L1 S).trans le_sup_left)
  have hXnZ1 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (str83G4_x_le_sup hfr).trans (str83G4_sup_le_normalizer_z1 hfr)
  have hXP2 : str83X L1 L2 S ≤ P2 L1 L2 S :=
    (str83X_le_q1 hfr).trans ((str83G4_q1_le_s hfr).trans
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
  intro x hx hcomm
  by_contra hx1
  apply hIZ2
  intro y hy
  have hxNZ2 : x ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hP2NZ2 (hD1P2 hx)
  have hxNZ1 : x ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (str83G4_sup_le_normalizer_z1 hfr) (hD1sup hx)
  have hzpN2 : Subgroup.zpowers x ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    Subgroup.zpowers_le.mpr hxNZ2
  have hzpN1 : Subgroup.zpowers x ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    Subgroup.zpowers_le.mpr hxNZ1
  have hXA : ∀ g ∈ Subgroup.zpowers x, ∀ c ∈ Z2 L1 L2 S, g * c * g⁻¹ ∈ Z2 L1 L2 S :=
    fun g hg c hc => (Subgroup.mem_normalizer_iff.mp (hzpN2 hg) c).mp hc
  have hXZ : ∀ g ∈ Subgroup.zpowers x, ∀ c ∈ Z1 L1 L2 S, g * c * g⁻¹ ∈ Z1 L1 L2 S :=
    fun g hg c hc => (Subgroup.mem_normalizer_iff.mp (hzpN1 hg) c).mp hc
  have hxcent : x ∈ centralizerMod (Z2 L1 L2 S) ⊤
      (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w) :=
    mem_centralizerMod.mpr ⟨Subgroup.mem_top x, hxNZ2, fun u hu => hcomm u hu⟩
  have hzp : Subgroup.zpowers x ≤ centralizerMod (Z2 L1 L2 S) ⊤
      (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w) :=
    Subgroup.zpowers_le.mpr hxcent
  have hyNZ2 : y ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hP2NZ2 (hXP2 hy.1)
  have hu : ∀ g ∈ Subgroup.zpowers x, y⁻¹ * (g * y * g⁻¹) ∈ Z2 L1 L2 S := by
    intro g hg
    have hgy : g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S := (hzp hg).2.2 y hy
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyNZ2)
      (g * y * g⁻¹ * y⁻¹)).mp hgy
    rwa [show y⁻¹ * (g * y * g⁻¹ * y⁻¹) * (y⁻¹)⁻¹ = y⁻¹ * (g * y * g⁻¹) from by group] at h
  have hS : ∀ s ∈ (⊥ : Subgroup ↥(Subgroup.zpowers x)),
      y⁻¹ * ((s : G) * y * (s : G)⁻¹) ∈ Z1 L1 L2 S := by
    intro s hs
    rw [Subgroup.mem_bot.mp hs]
    simp
  have hodd : Odd (⊥ : Subgroup ↥(Subgroup.zpowers x)).index := by
    rw [Subgroup.index_bot, Nat.card_zpowers]
    exact Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hx)
  obtain ⟨b, hbZ2, hb⟩ :=
    CFSG.GroupTheory.exists_fixed_mod_of_odd_index (X := Subgroup.zpowers x)
      (A := Z2 L1 L2 S) (Z := Z1 L1 L2 S) (u := y) (S := ⊥)
      hA hAc hZ1Z2 hXA hXZ hu hS hodd
  have hybX : y * b ∈ str83X L1 L2 S :=
    (str83X L1 L2 S).mul_mem hy.1 (z2_le_str83X L1 L2 S hbZ2)
  have hmem1 : (y * b)⁻¹ * (x * (y * b) * x⁻¹) ∈ Z1 L1 L2 S :=
    hb x (Subgroup.mem_zpowers x)
  have hmem2 : x * (y * b) * x⁻¹ * (y * b)⁻¹ ∈ Z1 L1 L2 S := by
    have h := (Subgroup.mem_normalizer_iff.mp (hXnZ1 hybX)
      ((y * b)⁻¹ * (x * (y * b) * x⁻¹))).mp hmem1
    rwa [show (y * b) * ((y * b)⁻¹ * (x * (y * b) * x⁻¹)) * (y * b)⁻¹ =
      x * (y * b) * x⁻¹ * (y * b)⁻¹ from by group] at h
  have hybZ1 : y * b ∈ Z1 L1 L2 S := hfpf x hx hx1 (y * b) hybX hmem2
  have hyZ2 : y ∈ Z2 L1 L2 S := by
    have h := (Z2 L1 L2 S).mul_mem (hZ1Z2 hybZ1) ((Z2 L1 L2 S).inv_mem hbZ2)
    rwa [show (y * b) * b⁻¹ = y from by group] at h
  exact hyZ2

end CFSG.Quasithin.Stroth

end
