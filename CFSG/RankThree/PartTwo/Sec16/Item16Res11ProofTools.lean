module

import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsL

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res11Out

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem isElemAbelian_sup_of_commute [Finite G] {B S : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hS : CFSG.Assembly.IsElemAbelian 3 S)
    (hc : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b) (hBS : B ⊓ S = ⊥) :
    CFSG.Assembly.IsElemAbelian 3 (B ⊔ S) ∧
      Nat.card (B ⊔ S : Subgroup G) = Nat.card B * Nat.card S := by
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B S hc
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmem : ∀ u ∈ (B ⊔ S : Subgroup G), ∃ b ∈ B, ∃ s ∈ S, u = b * s := by
    intro u hu
    have hu' : u ∈ ((B ⊔ S : Subgroup G) : Set G) := hu
    rw [hset] at hu'
    obtain ⟨b, hb, s, hs, rfl⟩ := hu'
    exact ⟨b, hb, s, hs, rfl⟩
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩, ?_⟩
  · obtain ⟨b, hb, s, hs, hu⟩ := hmem u u.2
    obtain ⟨b', hb', s', hs', hv⟩ := hmem v v.2
    apply Subtype.ext
    change (u : G) * v = v * u
    rw [hu, hv]
    have h1 : Commute b b' := hBc b hb b' hb'
    have h2 : Commute b s' := hc b hb s' hs'
    have h3 : Commute s b' := (hc b' hb' s hs).symm
    have h4 : Commute s s' := hSc s hs s' hs'
    exact (Commute.mul_left (h1.mul_right h2) (h3.mul_right h4)).eq
  · obtain ⟨b, hb, s, hs, rfl⟩ := hmem u hu
    have hbs : Commute b s := hc b hb s hs
    rw [hbs.mul_pow, hB.2 b hb, hS.2 s hs, one_mul]
  · rw [hBS, Subgroup.card_bot, mul_one] at hcard
    exact hcard

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_pow_three_of_mem {X : Subgroup G} (hX : ¬ 3 ∣ Nat.card X) {x : G}
    (hx3 : x ^ 3 = 1) (hxX : x ∈ X) : x = 1 := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ Nat.card X := by
    have := orderOf_dvd_natCard (⟨x, hxX⟩ : X)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hX

theorem not_three_dvd_card_theta (L : Subgroup G) :
    ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥L).map L.subtype) := by
  obtain ⟨-, -, hc3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hc3

omit [Finite G] in
theorem normalizer_le_normalizer_theta (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (((aschbacherSolvableCore 3 ↥L).map L.subtype : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem sectionCentralizer_eq_zpowers {E L D Y : Subgroup G} {c : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hcE : c ∈ E) (hc1 : c ≠ 1) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hEN : E ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hDE : D ≤ E) (hDY : D ≤ Y) (hD3 : Nat.card D = 3)
    (hYL : Y ≤ L) (hY : CFSG.Assembly.IsElemAbelian 3 Y) (hY9 : Nat.card Y = 9) :
    Late.sectionCentralizer E L ((aschbacherSolvableCore 3 ↥L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : Subgroup G := (aschbacherSolvableCore 3 ↥L).map L.subtype with hθdef
  have hθL : θ ≤ L := Subgroup.map_subtype_le _
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_three_dvd_card_theta L
  have hNθ := normalizer_le_normalizer_theta L
  have hEθ : E ≤ Subgroup.normalizer (θ : Set G) := hEN.trans hNθ
  set X := Sec11.sectionCentralizerSubgroup E L θ hEN hEθ with hXdef
  have hXE : X ≤ E := fun x hx => hx.1
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcX : c ∈ X := by
    refine ⟨hcE, fun y hy => ?_⟩
    have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hLc hy)
    have h1 : c * y * c⁻¹ * y⁻¹ = 1 := by
      rw [← hyc, mul_inv_cancel_right, mul_inv_cancel]
    rw [h1]
    exact θ.one_mem
  have hXL : ∀ x ∈ X, x ∈ L → x = 1 := by
    intro x hx hxL
    have hsub := Sec15.sectionCentralizer_subset_of_center_eq_bot (E := X ⊓ L) inf_le_right
      (fun e he => hE.2 e (hXE he.1)) hZ
    exact hsub ⟨⟨hx, hxL⟩, hx.2⟩
  apply le_antisymm _ (fun x hx => (Subgroup.zpowers_le.mpr hcX) hx)
  intro x hx
  by_contra hxc
  have hxX : x ∈ X := hx
  have hxE : x ∈ E := hXE hxX
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hE.2 c hcE) hc1
  have hCe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
    Sec5.isElemAbelian_of_le hE (Subgroup.zpowers_le.mpr hcE)
  obtain ⟨hX'e, hX'9⟩ := Sec5.isElemAbelian_sup_zpowers hCe hxc (hE.2 x hxE)
    (fun a ha => hEc a ((Subgroup.zpowers_le.mpr hcE) ha) x hxE)
  set X' := Subgroup.zpowers c ⊔ Subgroup.zpowers x with hX'def
  rw [Nat.card_zpowers, hc3] at hX'9
  have hX'X : X' ≤ X := sup_le (Subgroup.zpowers_le.mpr hcX) (Subgroup.zpowers_le.mpr hxX)
  have hX'E : X' ≤ E := hX'X.trans hXE
  have hX'L : ∀ y ∈ X', y ∈ L → y = 1 := fun y hy hyL => hXL y (hX'X hy) hyL
  have hDL : D ≤ L := hDY.trans hYL
  have hX'D : X' ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (hX'L y hy.1 (hDL hy.2))
  have hEeq : X' ⊔ D = E := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X' D
      (fun a ha b hb => hEc a (hX'E ha) b (hDE hb))).1
    rw [hX'D, Subgroup.card_bot, mul_one, hX'9, hD3] at hcard
    exact Subgroup.eq_of_le_of_card_ge (sup_le hX'E hDE) (by rw [hE27, hcard])
  set Yt := Y ⊔ θ with hYtdef
  have hYtL : Yt ≤ L := sup_le hYL hθL
  have hYNθ : Y ≤ Subgroup.normalizer (θ : Set G) :=
    hYL.trans (Subgroup.le_normalizer.trans hNθ)
  have hYθ : Y ⊓ θ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (eq_one_of_pow_three_of_mem hθ3 (hY.2 y hy.1) hy.2)
  have hYtcard : Nat.card Yt = 9 * Nat.card θ := by
    have h := card_sup_mul_card_inf_of_le_normalizer hYNθ
    rw [hYθ, Subgroup.card_bot, mul_one, hY9] at h
    exact h
  have hθ0 : Nat.card θ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card Yt).factorization 3 = 2 := by
    rw [hYtcard, Nat.factorization_mul (by norm_num) hθ0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hYSyl : ABGLocalTools.IsSylowOf 3 Y Yt :=
    ABGLocalTools.isSylowOf_of_card le_sup_left (by rw [hY9, hfac]; norm_num)
  have hX'N : X' ≤ Subgroup.normalizer (Yt : Set G) := by
    intro z hz
    have hzX : z ∈ X := hX'X hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Yt.map (MulAut.conj z).toMonoidHom ≤ Yt := by
      rw [hYtdef, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have h1 : z * y * z⁻¹ * y⁻¹ ∈ θ := hzX.2 y (hYL hy)
        have h2 : (MulAut.conj z).toMonoidHom y = (z * y * z⁻¹ * y⁻¹) * y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [h2]
        exact Yt.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
      · rintro _ ⟨t, ht, rfl⟩
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hEθ (hX'E hz)) t).mp ht)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj z).injective])
  set M := X' ⊔ Yt with hMdef
  have hYtM : Yt ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (Yt : Set G) := sup_le hX'N Subgroup.le_normalizer
  have hEM : E ≤ M := by
    rw [← hEeq]
    exact sup_le le_sup_left ((hDY.trans le_sup_left).trans hYtM)
  obtain ⟨P, hEP⟩ : ∃ P : Sylow 3 ↥M, E.subgroupOf M ≤ P :=
    (Proof1613.isPGroup_three_of_isElemAbelian hE).comap_subtype.exists_le_sylow
  set P' := (P : Subgroup ↥M).map M.subtype with hP'def
  have hP' : ABGLocalTools.IsSylowOf 3 P' M := ⟨P, rfl⟩
  have hEP' : E ≤ P' := fun y hy => ⟨⟨y, hEM hy⟩, hEP (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  set Q := P' ⊓ Yt with hQdef
  have hQ : ABGLocalTools.IsSylowOf 3 Q Yt := hP'.inf_of_le_normalizer hYtM hMN
  obtain ⟨k, -, hk⟩ := Sec15.Proof158Steps.exists_conj_of_isSylowOf hYSyl hQ
  have hQe : CFSG.Assembly.IsElemAbelian 3 Q := by
    rw [hk]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ Y hY
  have hQ9 : Nat.card Q = 9 := by
    rw [hk, Subgroup.card_map_of_injective (MulAut.conj k).injective, hY9]
  have hQL : Q ≤ L := inf_le_right.trans hYtL
  have hDQ : D ≤ Q := le_inf (hDE.trans hEP') (hDY.trans le_sup_left)
  have hθP : θ ⊓ P' = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hP'.card_eq]
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3).symm
  have hcomm : ∀ a ∈ X', ∀ q ∈ Q, a * q = q * a := by
    intro a ha q hq
    have h1 : a * q * a⁻¹ * q⁻¹ ∈ θ := (hX'X ha).2 q (hQL hq)
    have haP : a ∈ P' := hEP' (hX'E ha)
    have hqP : q ∈ P' := hq.1
    have h2 : a * q * a⁻¹ * q⁻¹ ∈ P' :=
      P'.mul_mem (P'.mul_mem (P'.mul_mem haP hqP) (P'.inv_mem haP)) (P'.inv_mem hqP)
    have h3 : a * q * a⁻¹ * q⁻¹ = 1 := by
      have h4 : a * q * a⁻¹ * q⁻¹ ∈ θ ⊓ P' := ⟨h1, h2⟩
      rw [hθP] at h4
      exact h4
    calc a * q = a * q * a⁻¹ * q⁻¹ * (q * a) := by group
      _ = q * a := by rw [h3, one_mul]
  have hX'Q : X' ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (hX'L y hy.1 (hQL hy.2))
  obtain ⟨hZe, hZcard⟩ := isElemAbelian_sup_of_commute hX'e hQe hcomm hX'Q
  have hEZ : E ≤ X' ⊔ Q := by
    rw [← hEeq]
    exact sup_le le_sup_left (hDQ.trans le_sup_right)
  have hZE := hmax _ hZe hEZ
  rw [hZE, hE27, hX'9, hQ9] at hZcard
  omega

omit [Finite G] in
theorem zpowers_mem_image_of_not_mem {A L : Subgroup G} {c x : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hxA : x ∈ A) (hxL : x ∉ L) :
    Subgroup.zpowers x ∈
      (fun a : G => Subgroup.zpowers (c * a)) '' ((A ⊓ L : Subgroup G) : Set G) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact hAc y hy.1 c hcA
  have hx' : x ∈ (Subgroup.zpowers c : Set G) * ((A ⊓ L : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN, ← hAeq]
    exact hxA
  obtain ⟨y, hw, a, ha, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hk : c ^ k = c ^ (k % 3) := by
    rw [zpow_eq_zpow_emod' k hc3]
    rfl
  have hk0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hk3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hca : c * a = a * c := hAc c hcA a ha.1
  have ha3 : a ^ 3 = 1 := hA.2 a ha.1
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · exfalso
    apply hxL
    rw [hk, h, zpow_zero, one_mul]
    exact ha.2
  · refine ⟨a, ha, ?_⟩
    show Subgroup.zpowers (c * a) = Subgroup.zpowers (c ^ k * a)
    rw [hk, h, zpow_one]
  · refine ⟨a ^ 2, Subgroup.pow_mem _ ha 2, ?_⟩
    show Subgroup.zpowers (c * a ^ 2) = Subgroup.zpowers (c ^ k * a)
    rw [hk, h, show c ^ (2 : ℤ) = c ^ 2 from zpow_ofNat c 2]
    set x := c ^ 2 * a with hx
    have hx3 : x ^ 3 = 1 := by
      rw [hx, (Commute.pow_left hca 2).mul_pow, ← pow_mul, ha3, mul_one,
        show 2 * 3 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    have hsq : x ^ 2 = c * a ^ 2 := by
      rw [hx, (Commute.pow_left hca 2).mul_pow, ← pow_mul,
        show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
    rw [← hsq]
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
    · apply Subgroup.zpowers_le.mpr
      have h4 : x = (x ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
      have h5 : (x ^ 2) ^ 2 ∈ Subgroup.zpowers (x ^ 2) :=
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      rwa [← h4] at h5

theorem mem_omegaA_of_orbit {A L : Subgroup G} {c e : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hcL : c ∉ L)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hWAL : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hΩ : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c))
    (hΩ9 : (omegaA A).ncard = 9) (heA : e ∈ A) (heL : e ∉ L) :
    Subgroup.zpowers e ∈ omegaA A := by
  set S := (fun a : G => Subgroup.zpowers (c * a)) '' ((A ⊓ L : Subgroup G) : Set G) with hS
  have hsub : omegaA A ⊆ S := by
    intro X hX
    rw [hΩ] at hX
    obtain ⟨w, hw, rfl⟩ := hX
    rw [MonoidHom.map_zpowers]
    have hwcA : w * c * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw c).mp hcA
    refine zpowers_mem_image_of_not_mem hA hcA hAeq hwcA fun hwcL => hcL ?_
    have h1 : w * c * w⁻¹ ∈ A ⊓ L := ⟨hwcA, hwcL⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (hWAL (inv_mem hw)) _).mp h1
    have h3 : w⁻¹ * (w * c * w⁻¹) * w⁻¹⁻¹ = c := by group
    rw [h3] at h2
    exact h2.2
  have hS9 : S.ncard ≤ 9 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [← Nat.card_coe_set_eq]
    exact hAL9.le
  have heq : omegaA A = S :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  rw [heq]
  exact zpowers_mem_image_of_not_mem hA hcA hAeq heA heL

end CFSG.RankThree.PartTwo.Sec16.Res11Out
