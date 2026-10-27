module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofInU43
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCharThree
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81McL
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81U43
import CFSG.RankThree.PartTwo.Sec4.Item420

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

open Res417Five

namespace Res417Five

section Lift

variable {Y H : Type} [Group Y] [Group H]

theorem isElemAbelian_comap_closure (ρ : Y →* H) (hker : ρ.ker ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {n : ℕ} (x : Fin n → Y)
    (hxc : ∀ i j, x i * x j = x j * x i) (hx3 : ∀ i, x i ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3
      ((Subgroup.closure (Set.range fun i => ρ (x i))).comap ρ) := by
  have hS := isElemAbelian_closure_of_commute (G := Y)
    (S := Set.range x ∪ (ρ.ker : Set Y)) (by
      rintro a (⟨i, rfl⟩ | ha) b (⟨j, rfl⟩ | hb)
      · exact hxc i j
      · exact Subgroup.mem_center_iff.mp (hker hb) (x i)
      · exact (Subgroup.mem_center_iff.mp (hker ha) (x j)).symm
      · exact (Subgroup.mem_center_iff.mp (hker ha) b).symm) (by
      rintro a (⟨i, rfl⟩ | ha)
      · exact hx3 i
      · exact hZ3 a ha)
  refine Sec6.Res611Res4.isElemAbelian_of_le hS ?_
  intro y hy
  rw [Subgroup.mem_comap] at hy
  have hrange : Set.range (fun i => ρ (x i)) = ρ '' Set.range x := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← MonoidHom.map_closure] at hy
  obtain ⟨y', hy', hyy'⟩ := hy
  have hy : y = y' * (y'⁻¹ * y) := by group
  rw [hy]
  refine Subgroup.mul_mem _ (Subgroup.closure_mono Set.subset_union_left hy')
    (Subgroup.subset_closure (Or.inr ?_))
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]

theorem isElemAbelian_comap_map_conj (ρ : Y →* H) (hρ : Function.Surjective ρ)
    {B : Subgroup H} (hB : CFSG.Assembly.IsElemAbelian 3 (B.comap ρ)) (g : H) :
    CFSG.Assembly.IsElemAbelian 3 ((B.map (MulAut.conj g).toMonoidHom).comap ρ) := by
  obtain ⟨g', rfl⟩ := hρ g
  refine Sec6.Res611Res4.isElemAbelian_of_le
    (Sec6.Res611Res4.isElemAbelian_map (MulAut.conj g').toMonoidHom hB) ?_
  intro y hy
  rw [Subgroup.mem_comap] at hy
  obtain ⟨b, hb, hbe⟩ := hy
  refine ⟨g'⁻¹ * y * g', ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  show ρ (g'⁻¹ * y * g') ∈ B
  rw [map_mul, map_mul, map_inv]
  have : ρ y = ρ g' * b * (ρ g')⁻¹ := by
    rw [← hbe]
    rfl
  rw [this]
  simpa [mul_assoc] using hb

end Lift

section McL

open CFSG.Sporadic.Schreier (mclP)

open Item434SporGen


theorem isElemAbelian_comap_mcl {Y : Type} [Group Y] (ρ : Y →* mclP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {B : Subgroup mclP} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (h81 : 81 ≤ Nat.card B) : CFSG.Assembly.IsElemAbelian 3 (B.comap ρ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, t, h, e, heD, hcard, ⟨hs0, hs1, hs2, hs3⟩, ⟨ht0, ht1, ht2, ht3⟩, hh⟩ :=
    Item434SporMcL9.exists_klein_basis
  set D := Subgroup.closure (Set.range e) with hD
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    Sec6.Res611Res4.isElemAbelian_of_le isElemAbelian_mclD
      ((Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr heD))
  have heD' : ∀ i, e i ∈ D := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  set x : Fin 4 → Y := fun i => Function.surjInv hρ (e i) with hx
  have hxe : ∀ i, ρ (x i) = e i := fun i => Function.surjInv_eq hρ _
  set s' := Function.surjInv hρ s
  set t' := Function.surjInv hρ t
  set h' := Function.surjInv hρ h
  have hs' : ρ s' = s := Function.surjInv_eq hρ _
  have ht' : ρ t' = t := Function.surjInv_eq hρ _
  have hh' : ρ h' = h := Function.surjInv_eq hρ _
  obtain ⟨hxc, hx3⟩ := Item434SporMcL9.lift_commute_cube ρ hker hZ3 x s' t' h'
    (fun a b => by
      rw [hxe, hxe]
      exact congrArg Subtype.val (hDe.1.is_comm.comm ⟨e a, heD' a⟩ ⟨e b, heD' b⟩))
    (fun a => by rw [hxe]; exact hDe.2 _ (heD' a))
    (by simpa only [hs', hxe] using hs0) (by simpa only [hs', hxe] using hs1)
    (by simpa only [hs', hxe] using hs2) (by simpa only [hs', hxe] using hs3)
    (by simpa only [ht', hxe] using ht0) (by simpa only [ht', hxe] using ht1)
    (by simpa only [ht', hxe] using ht2) (by simpa only [ht', hxe] using ht3)
    (by simpa only [hh', hxe] using hh)
  have hDc : CFSG.Assembly.IsElemAbelian 3 (D.comap ρ) := by
    have := isElemAbelian_comap_closure ρ hker hZ3 x hxc hx3
    simpa only [hxe] using this
  obtain ⟨x₀, R₀, T, A, -, -, -, -, hL⟩ :=
    CFSG.Sporadic.Recognition.McLAS.threeLocal_of_embedding mclP.subtype mclP.subtype_injective
      (Subgroup.range_subtype mclP) CFSG.Sporadic.Recognition.McLAS.threeFacts_cert'
      CFSG.Sporadic.Recognition.McLAS.threeLocalCheck_eq_true
  have hT : Nat.card T = 3 ^ (Nat.card mclP).factorization 3 := by
    rw [hL.card_T, CFSG.Sporadic.Schreier.card_mclP, Sec6.Res611Res4.factorization_three_mcl]
    norm_num
  have hA : ∀ C : Subgroup mclP, C ≤ T → IsMulCommutative C → 81 ≤ Nat.card C → C = A :=
    fun C hCT hCc h81 =>
      (hL.abelian_subgroups C hCT hCc).2 (le_antisymm (hL.abelian_subgroups C hCT hCc).1 h81)
  obtain ⟨g₁, hg₁⟩ := Sec6.Res611Res4.exists_eq_map_conj hT hA hDe hcard
  obtain ⟨g₂, hg₂⟩ := Sec6.Res611Res4.exists_eq_map_conj hT hA hB h81
  have hBD : B = D.map (MulAut.conj (g₂ * g₁⁻¹)).toMonoidHom := by
    rw [hg₂, hg₁, Subgroup.map_map]
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hBD]
  exact isElemAbelian_comap_map_conj ρ hρ hDc _

end McL

section U43

open Item434RemU43


theorem isElemAbelian_comap_u43 {Y : Type} [Group Y] (ρ : Y →* UX)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {B : Subgroup UX} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (h81 : 81 ≤ Nat.card B) : CFSG.Assembly.IsElemAbelian 3 (B.comap ρ) := by
  have hsyl := uSylCheck_true
  have hrt := (uClassCheck_parts uClassCheck_true).1
  obtain ⟨d₀, -⟩ : ∃ d₀ : Sec6.Res611Res4.U43.Data, True :=
    ⟨Sec6.Res611Res4.U43.data hsyl hrt, trivial⟩
  obtain ⟨d, -, hdcl⟩ := exists_liftData_rt hsyl uClassCheck_true uCoverAll_true
  obtain ⟨y, hyπ, hy3, hyc⟩ := Item434Cover.exists_lift hρ hker d.x d.hx3 d.hxc d.g d.M d.hrel
    d.k₀ d.l₀ d.cs d.hlin d.cs' d.hlin'
  have hRc : CFSG.Assembly.IsElemAbelian 3 ((rtS.map piU).comap ρ) := by
    have := isElemAbelian_comap_closure ρ hker hZ3 y hyc hy3
    simp only [hyπ] at this
    rwa [hdcl] at this
  obtain ⟨g, Pt, hPt, hPte, hPtn, hmap⟩ := exists_conj_elemAbelian hsyl hB rfl
  have hPtR : Pt = d₀.R := d₀.eq_R_of_le hsyl hPt
    (fun x hx y hy => congrArg Subtype.val (hPte.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (hPtn ▸ h81)
  have hRrt : rtS = d₀.R := d₀.eq_R_of_le hsyl (rtS_le_sylS hsyl hrt)
    (fun x hx y hy => congrArg Subtype.val
      ((rtS_isElemAbelian hsyl hrt).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) (card_rtS hsyl hrt)
  rw [hPtR, ← hRrt] at hmap
  have hBeq : B = (rtS.map piU).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hmap, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hBeq]
  exact isElemAbelian_comap_map_conj ρ hρ hRc _

end U43

theorem card_comap_of_surjective {X H : Type} [Group X] [Group H] [Finite X] (ρ : X →* H)
    (hρ : Function.Surjective ρ) (K : Subgroup H) :
    Nat.card (K.comap ρ) = Nat.card K * Nat.card ρ.ker := by
  have : Finite H := Finite.of_surjective ρ hρ
  have h1 := Subgroup.card_mul_index (K.comap ρ)
  have h2 := Subgroup.card_mul_index K
  rw [Subgroup.index_comap_of_surjective K hρ] at h1
  have h3 : Nat.card X = Nat.card H * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
  have hidx : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (K.comap ρ) * K.index = Nat.card K * Nat.card ρ.ker * K.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) h4

theorem exists_cover_data {X H : Type} [Group X] [Finite X] [Group H] (ρ : X →* H)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center X)
    (hZ : Nat.card (Subgroup.center X) = 3) {Pq Eq₀ Tq : Subgroup H}
    (hPe : CFSG.Assembly.IsElemAbelian 3 (Pq.comap ρ)) (hP81 : Nat.card Pq = 3 ^ 4)
    (hEP : Eq₀ ≤ Pq) (hE9 : Nat.card Eq₀ = 9) (hT₀ : IsPGroup 2 Tq)
    (hET : Eq₀ ≤ Subgroup.normalizer (Tq : Set H))
    (hTE : ¬ Tq ≤ Subgroup.centralizer (Eq₀ : Set H)) :
    ∃ P E₀ T₀ : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 5 ∧ E₀ ≤ P ∧
      Nat.card E₀ = 9 ∧ E₀ ⊓ Subgroup.center X = ⊥ ∧ IsPGroup 2 T₀ ∧
      E₀ ≤ Subgroup.normalizer (T₀ : Set X) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite H := Finite.of_surjective ρ hρ
  have hkc : Nat.card ρ.ker = 3 := by rw [hker, hZ]
  set P := Pq.comap ρ with hPdef
  have hP243 : Nat.card P = 3 ^ 5 := by
    rw [hPdef, card_comap_of_surjective ρ hρ, hP81, hkc]
    norm_num
  have hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ρ.ker) (x := ⟨z, hz⟩)
    rw [hkc] at h
    exact congrArg Subtype.val h
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPqe : CFSG.Assembly.IsElemAbelian 3 Pq := by
    have := Sec6.Res611Res4.isElemAbelian_map ρ hPe
    rwa [Subgroup.map_comap_eq_self_of_surjective hρ] at this
  have hEqe : CFSG.Assembly.IsElemAbelian 3 Eq₀ := Sec6.Res611Res4.isElemAbelian_of_le hPqe hEP
  obtain ⟨eq₁, heq₁, heq₁1⟩ : ∃ x ∈ Eq₀, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : Eq₀ = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hall x hx)
    rw [hb, Subgroup.card_bot] at hE9
    omega
  have heq₁3 : orderOf eq₁ = 3 := orderOf_eq_prime (hEqe.2 _ heq₁) heq₁1
  obtain ⟨eq₂, heq₂, heq₂1⟩ : ∃ x ∈ Eq₀, x ∉ Subgroup.zpowers eq₁ := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show Eq₀ ≤ Subgroup.zpowers eq₁ from hall)
    rw [hE9, Nat.card_zpowers, heq₁3] at this
    omega
  have heq₂3 : orderOf eq₂ = 3 :=
    orderOf_eq_prime (hEqe.2 _ heq₂) fun h => heq₂1 (h ▸ Subgroup.one_mem _)
  have hEqc : ∀ a ∈ Eq₀, ∀ b ∈ Eq₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEqe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set e₁ := Function.surjInv hρ eq₁ with he₁def
  set e₂ := Function.surjInv hρ eq₂ with he₂def
  have he₁ : ρ e₁ = eq₁ := Function.surjInv_eq hρ _
  have he₂ : ρ e₂ = eq₂ := Function.surjInv_eq hρ _
  have he₁P : e₁ ∈ P := by rw [hPdef, Subgroup.mem_comap, he₁]; exact hEP heq₁
  have he₂P : e₂ ∈ P := by rw [hPdef, Subgroup.mem_comap, he₂]; exact hEP heq₂
  set E₀ := Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ with hE₀def
  have hE₀P : E₀ ≤ P := sup_le (Subgroup.zpowers_le.mpr he₁P) (Subgroup.zpowers_le.mpr he₂P)
  have hmapE : E₀.map ρ = Eq₀ := by
    rw [hE₀def, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, he₁, he₂]
    have hle : Subgroup.zpowers eq₁ ⊔ Subgroup.zpowers eq₂ ≤ Eq₀ :=
      sup_le (Subgroup.zpowers_le.mpr heq₁) (Subgroup.zpowers_le.mpr heq₂)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_sup_zpowers_eq_three_mul heq₂3 heq₂1 fun a ha b hb =>
      hEqc a ((Subgroup.zpowers_le.mpr heq₁) ha) b ((Subgroup.zpowers_le.mpr heq₂) hb),
      Nat.card_zpowers, heq₁3, hE9]
  have hE₀le : Nat.card E₀ ≤ 9 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers e₁) (Subgroup.zpowers e₂) fun a ha b hb =>
        hPcomm a ((Subgroup.zpowers_le.mpr he₁P) ha) b ((Subgroup.zpowers_le.mpr he₂P) hb)
    have h1 : Nat.card (Subgroup.zpowers e₁) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hPe.2 _ he₁P)
    have h2 : Nat.card (Subgroup.zpowers e₂) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hPe.2 _ he₂P)
    have h3 : 1 ≤ Nat.card (Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ : Subgroup X) :=
      Nat.card_pos
    rw [← hE₀def] at hcard
    nlinarith
  have hE₀ge : 9 ≤ Nat.card E₀ := by
    rw [← hE9, ← hmapE]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd E₀ ρ)
  have hE₀9 : Nat.card E₀ = 9 := le_antisymm hE₀le hE₀ge
  have hE₀Z : E₀ ⊓ Subgroup.center X = ⊥ := by
    set φ := ρ.comp E₀.subtype with hφ
    have hr : φ.range = Eq₀ := by rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hmapE]
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hr, hE9, hE₀9] at h1
    have hk1 : Nat.card φ.ker = 1 := by omega
    have hkb := Subgroup.eq_bot_of_card_eq φ.ker hk1
    rw [eq_bot_iff]
    rintro z ⟨hzE, hzZ⟩
    have hzker : (⟨z, hzE⟩ : E₀) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      change ρ z = 1
      rw [← MonoidHom.mem_ker, hker]
      exact hzZ
    rw [hkb, Subgroup.mem_bot] at hzker
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzker
  have hcop : Nat.Coprime 2 (Nat.card ρ.ker) := by rw [hkc]; norm_num
  obtain ⟨R, hRmap, hRinj⟩ := exists_lift_pGroup ρ hρ hcop Tq hT₀
  have hRcard : Nat.card R = Nat.card Tq := by
    have h1 : (ρ.comp R.subtype).range = Tq := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hRmap]
    rw [← h1]
    exact Nat.card_congr (MonoidHom.ofInjective hRinj).toEquiv
  have hR2 : IsPGroup 2 R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₀
    exact IsPGroup.of_card (n := k) (hRcard.trans hk)
  have hconjR : ∀ e ∈ E₀, ∀ r ∈ R, e * r * e⁻¹ ∈ R := by
    intro e he r hr
    have heEq : ρ e ∈ Eq₀ := hmapE ▸ Subgroup.mem_map_of_mem ρ he
    have hrT : ρ r ∈ Tq := hRmap ▸ Subgroup.mem_map_of_mem ρ hr
    have hw : ρ (e * r * e⁻¹) ∈ Tq := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hET heEq) _).mp hrT
    rw [← hRmap] at hw
    obtain ⟨r', hr', hrr'⟩ := hw
    set z := r'⁻¹ * (e * r * e⁻¹) with hz
    have hzk : z ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hrr', inv_mul_cancel]
    have hzc : z ∈ Subgroup.center X := hker ▸ hzk
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    obtain ⟨k', hk'⟩ := hR2 ⟨r', hr'⟩
    have hrk : r ^ 2 ^ (k + k') = 1 := by
      have h := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [pow_add, pow_mul, h, one_pow]
    have hr'k : r' ^ 2 ^ (k + k') = 1 := by
      have h := congrArg Subtype.val hk'
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [pow_add, pow_mul', h, one_pow]
    have hwk : (e * r * e⁻¹) ^ 2 ^ (k + k') = 1 := by
      rw [conj_pow, hrk, mul_one, mul_inv_cancel]
    have hwz : e * r * e⁻¹ = r' * z := by rw [hz]; group
    have hz2 : z ^ 2 ^ (k + k') = 1 := by
      have hcomm : Commute r' z := Subgroup.mem_center_iff.mp hzc r'
      rw [hwz, hcomm.mul_pow, hr'k, one_mul] at hwk
      exact hwk
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 2 ^ (k + k') := orderOf_dvd_of_pow_eq_one hz2
      have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (hZ3 z hzk)
      have hcp : Nat.Coprime (2 ^ (k + k')) 3 := Nat.Coprime.pow_left _ (by norm_num)
      have : orderOf z ∣ 1 := by
        rw [← hcp]
        exact Nat.dvd_gcd h1 h2
      rwa [Nat.dvd_one, orderOf_eq_one_iff] at this
    rw [hwz, hz1, mul_one]
    exact hr'
  have hER : E₀ ≤ Subgroup.normalizer (R : Set X) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hconjR e he r, fun h => ?_⟩
    have := hconjR e⁻¹ (E₀.inv_mem he) _ h
    simpa [mul_assoc] using this
  refine ⟨P, E₀, R, hPe, hP243, hE₀P, hE₀9, hE₀Z, hR2, hER, fun hRC => hTE ?_⟩
  intro t ht
  rw [← hRmap] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  rw [Subgroup.mem_centralizer_iff]
  intro eq heq
  rw [← hmapE] at heq
  obtain ⟨e, he, rfl⟩ := heq
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hRC hr) e he]

theorem surjective_ker_of_mulEquiv {X H : Type} [Group X] [Group H]
    (e : X ⧸ Subgroup.center X ≃* H) :
    Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) ∧
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker = Subgroup.center X := by
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    exact ⟨x, hq⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem e81_data_map {H₁ H₂ : Type} [Group H₁] [Group H₂] (ψ : H₁ →* H₂)
    (hψ : Function.Injective ψ) {P E₀ T₀ : Subgroup H₁} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP81 : Nat.card P = 3 ^ 4) (hEP : E₀ ≤ P) (hE9 : Nat.card E₀ = 9) (hT₀ : IsPGroup 2 T₀)
    (hET : E₀ ≤ Subgroup.normalizer (T₀ : Set H₁))
    (hTE : ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set H₁)) :
    CFSG.Assembly.IsElemAbelian 3 (P.map ψ) ∧ Nat.card (P.map ψ) = 3 ^ 4 ∧
      E₀.map ψ ≤ P.map ψ ∧ Nat.card (E₀.map ψ) = 9 ∧ IsPGroup 2 (T₀.map ψ) ∧
      E₀.map ψ ≤ Subgroup.normalizer ((T₀.map ψ : Subgroup H₂) : Set H₂) ∧
      ¬ T₀.map ψ ≤ Subgroup.centralizer ((E₀.map ψ : Subgroup H₂) : Set H₂) := by
  refine ⟨Sec6.Res611Res4.isElemAbelian_map ψ hP, by rw [Subgroup.card_map_of_injective hψ, hP81],
    Subgroup.map_mono hEP, by rw [Subgroup.card_map_of_injective hψ, hE9], hT₀.map ψ,
    (Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map ψ), fun hle => hTE ?_⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  apply hψ
  rw [map_mul, map_mul]
  exact Subgroup.mem_centralizer_iff.mp (hle ⟨t, ht, rfl⟩) (ψ e) ⟨e, he, rfl⟩

end Res417Five


section Certs


theorem k417CoverE35_of (hMcL : K417E81McL) (hU : K417E81U43) : K417CoverE35 := by
  intro X _ _ hX hZ hiso
  have hker0 : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
    QuotientGroup.ker_mk' _
  have hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  ·
    obtain ⟨hρ, hker⟩ := surjective_ker_of_mulEquiv (φ.trans Item434RemU43.projSUEquivUX)
    obtain ⟨Pq, Eq₀, Tq, hP, hP81, hEP, hE9, hT₀, hET, hTE⟩ := hU
    obtain ⟨hP', hP81', hEP', hE9', hT₀', hET', hTE'⟩ :=
      e81_data_map Item434RemU43.projSUEquivUX.toMonoidHom Item434RemU43.projSUEquivUX.injective
        hP hP81 hEP hE9 hT₀ hET hTE
    have hPe := isElemAbelian_comap_u43 _ hρ hker.le (fun z hz => hZ3 z (hker ▸ hz)) hP'
      (by rw [hP81']; norm_num)
    exact exists_cover_data _ hρ hker hZ hPe hP81' hEP' hE9' hT₀' hET' hTE'
  ·
    obtain ⟨hρ, hker⟩ := surjective_ker_of_mulEquiv (φ.trans CFSG.Sporadic.Schreier.mclPermEquiv)
    have eX : Nonempty (NativeSporadic.Carrier .McL ≃* NativeSporadic.McL) := ⟨MulEquiv.refl _⟩
    obtain ⟨eX⟩ := eX
    obtain ⟨Pq, Eq₀, Tq, hP, hP81, hEP, hE9, hT₀, hET, hTE⟩ := hMcL
    obtain ⟨hP', hP81', hEP', hE9', hT₀', hET', hTE'⟩ :=
      e81_data_map (eX.trans CFSG.Sporadic.Schreier.mclPermEquiv).toMonoidHom
        (eX.trans CFSG.Sporadic.Schreier.mclPermEquiv).injective hP hP81 hEP hE9 hT₀ hET hTE
    have hPe := isElemAbelian_comap_mcl _ hρ hker.le (fun z hz => hZ3 z (hker ▸ hz)) hP'
      (by rw [hP81']; norm_num)
    exact exists_cover_data _ hρ hker hZ hPe hP81' hEP' hE9' hT₀' hET' hTE'

end Certs

end CFSG.RankThree.PartTwo.Sec4
