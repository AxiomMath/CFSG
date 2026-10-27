module

public import CFSG.RankThree.PartTwo.Sec15.Wales154L3Odd
public import CFSG.RankThree.PartTwo.Sec15.Wales154Five
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem le_of_pow_three_dvd_of_isLThreeEpsAt {Q : Type} [Group Q] {r k f N : ℕ} [Fact r.Prime]
    (hf : 1 ≤ f) (h : IsLThreeEpsAt Q r f) (hk : (r ^ k) ^ 3 ∣ N) (hd : N ∣ Nat.card Q) :
    k ≤ f := by
  have hp : r.Prime := Fact.out
  have hc1 : ∀ x : ℕ, r ∣ x → 1 ≤ x → Nat.Coprime r (x - 1) := fun x hx hx1 => by
    have h1 : Nat.Coprime (x - 1) (x - 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rw [Nat.sub_add_cancel hx1] at h1
    exact (h1.coprime_dvd_right hx).symm
  have hc2 : ∀ x : ℕ, r ∣ x → Nat.Coprime r (x + 1) := fun x hx =>
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _) :
      Nat.Coprime x (x + 1)).coprime_dvd_left hx
  have hr2 : r ∣ (r ^ f) ^ 2 := (dvd_pow_self r (by omega)).trans (dvd_pow_self _ (by norm_num))
  have hr3 : r ∣ (r ^ f) ^ 3 := (dvd_pow_self r (by omega)).trans (dvd_pow_self _ (by norm_num))
  have hpos : ∀ m : ℕ, 1 ≤ (r ^ f) ^ m := fun m => Nat.one_le_pow _ _ (pow_pos hp.pos f)
  obtain ⟨M, hM, hcop⟩ : ∃ M, Nat.card Q ∣ (r ^ f) ^ 3 * M ∧ Nat.Coprime r M := by
    rcases card_eq_of_isLThreeEpsAt hf h with c | ⟨-, c⟩
    · exact ⟨((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 - 1), c ▸ Dvd.intro _ rfl,
        Nat.Coprime.mul_right (hc1 _ hr2 (hpos 2)) (hc1 _ hr3 (hpos 3))⟩
    · exact ⟨((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1), c ▸ Dvd.intro _ rfl,
        Nat.Coprime.mul_right (hc1 _ hr2 (hpos 2)) (hc2 _ hr3)⟩
  have h1 : r ^ (k * 3) ∣ r ^ (f * 3) * M := by
    rw [pow_mul, pow_mul]
    exact (hk.trans hd).trans hM
  have h2 : r ^ (k * 3) ∣ r ^ (f * 3) :=
    (Nat.Coprime.pow_left (k * 3) hcop).dvd_of_dvd_mul_right h1
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
  omega

theorem false_of_isLThreeEpsAt_same {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁]
    {r k : ℕ} [Fact r.Prime] (hk : 1 ≤ k) (h₁ : IsLThreeEpsAt Q₁ r k)
    (h₂ : IsLThreeEpsAt Q₂ r k) (hd : Nat.card Q₁ ∣ Nat.card Q₂)
    (hle : 2 * Nat.card Q₁ ≤ Nat.card Q₂) : False := by
  have hp : r.Prime := Fact.out
  have hq2 : 2 ≤ r ^ k := hp.two_le.trans (Nat.le_self_pow (by omega) r)
  obtain ⟨t, ht⟩ := hd
  have hpos : 0 < Nat.card Q₁ := Nat.card_pos
  have ht2 : 2 ≤ t := by
    by_contra h
    push Not at h
    interval_cases t <;> nlinarith
  have hS : 8 ≤ (r ^ k) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (r ^ k) ^ 3 := Nat.pow_le_pow_left hq2 3
  have hPQ : 0 < (r ^ k) ^ 3 * ((r ^ k) ^ 2 - 1) := by
    have h4 : 4 ≤ (r ^ k) ^ 2 := by nlinarith
    have : 1 ≤ (r ^ k) ^ 2 - 1 := by omega
    positivity
  have hfin : ∀ x y a b : ℕ, x * t * b = y * a → (x = (r ^ k) ^ 3 - 1 ∨ x = (r ^ k) ^ 3 + 1) →
      (y = (r ^ k) ^ 3 - 1 ∨ y = (r ^ k) ^ 3 + 1) → (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) →
      (x = y → a = b) → False := by
    intro x y a b hk' hx hy ha hb hxy
    generalize hu : (r ^ k) ^ 3 = u at hS hx hy
    rcases (show t ≤ 3 ∨ 4 ≤ t by omega) with h4 | h4
    · interval_cases t <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hxy <;> omega
    · have hm := Nat.mul_le_mul_right b (Nat.mul_le_mul_left x h4)
      generalize hw : x * t * b = w at hk' hm
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hxy <;> omega
  have hg : ∀ n : ℕ, Nat.gcd 3 n = 1 ∨ Nat.gcd 3 n = 3 := fun n =>
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 n)
  have hne : (r ^ k) ^ 3 - 1 ≠ (r ^ k) ^ 3 + 1 := by omega
  rcases card_eq_of_isLThreeEpsAt hk h₁ with c₁ | ⟨-, c₁⟩ <;>
    rcases card_eq_of_isLThreeEpsAt hk h₂ with c₂ | ⟨-, c₂⟩ <;> rw [ht] at c₂
  · exact hfin _ _ _ _ (order_key hPQ c₁ c₂) (Or.inl rfl) (Or.inl rfl) (hg _) (hg _) fun _ => rfl
  · exact hfin _ _ _ _ (order_key hPQ c₁ c₂) (Or.inl rfl) (Or.inr rfl) (hg _) (hg _)
      fun h => (hne h).elim
  · exact hfin _ _ _ _ (order_key hPQ c₁ c₂) (Or.inr rfl) (Or.inl rfl) (hg _) (hg _)
      fun h => (hne h.symm).elim
  · exact hfin _ _ _ _ (order_key hPQ c₁ c₂) (Or.inr rfl) (Or.inr rfl) (hg _) (hg _) fun _ => rfl

theorem nonempty_quot_pCore_two_equiv_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty (A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hK : g.ker = CFSG.pCore 2 A := by
    have hk : g.ker = (CFSG.pCore 2 B).comap f := by
      ext a
      simp [g, QuotientGroup.eq_one_iff]
    rw [hk]
    refine le_antisymm ?_ ?_
    · exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (CFSG.pCore_normal.comap f)
        (CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hker)
    · intro a ha
      exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (CFSG.pCore_normal.map f hf)
        (CFSG.pCore_isPGroup.map f) (Subgroup.mem_map_of_mem f ha)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hK.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩

theorem nonempty_quot_pCore_imgX_equiv {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(imgX X Y) ⧸ CFSG.pCore 2 ↥(imgX X Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).subgroupMap (X.subgroupOf Y) with hρ
  have hker : IsPGroup 2 ↥ρ.ker := by
    intro x
    have hx : ((x : ↥(X.subgroupOf Y)) : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ((x : ↥(X.subgroupOf Y)) : ↥Y) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  set e := (Subgroup.subgroupOfEquivOfLe hXY).symm with he
  set f := ρ.comp e.toMonoidHom with hf
  have hfs : Function.Surjective f :=
    ((QuotientGroup.mk' _).subgroupMap_surjective _).comp e.surjective
  have hker' : IsPGroup 2 f.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hker ⟨e x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (e x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    apply e.injective
    simpa using h1
  exact nonempty_quot_pCore_two_equiv_of_surjective f hfs hker'

theorem conj_mul_inv_mem_of_le_sup {Y N D₁ D₂ : Subgroup G} {e : G}
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hle : Y ≤ D₁ ⊔ D₂) (hD₁ : D₁ ≤ Y)
    (hD₂ : D₂ ≤ Y) (h₁ : ∀ d ∈ D₁, e * d * e⁻¹ * d⁻¹ ∈ N)
    (h₂ : ∀ d ∈ D₂, e * d * e⁻¹ * d⁻¹ ∈ N) : ∀ y ∈ Y, e * y * e⁻¹ * y⁻¹ ∈ N := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ e * y * e⁻¹ * y⁻¹ ∈ N}
      one_mem' := ⟨Y.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
        refine ⟨Y.mul_mem haY hbY, ?_⟩
        have e1 : e * (a * b) * e⁻¹ * (a * b)⁻¹ =
            (e * a * e⁻¹ * a⁻¹) * (a * (e * b * e⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1]
        exact N.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hYN haY) _).mp hb)
      inv_mem' := by
        rintro a ⟨haY, ha⟩
        refine ⟨Y.inv_mem haY, ?_⟩
        have e1 : e * a⁻¹ * e⁻¹ * a⁻¹⁻¹ = a⁻¹ * (e * a * e⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem haY)) _).mp (N.inv_mem ha) }
  have hS : D₁ ⊔ D₂ ≤ S :=
    sup_le (fun d hd => ⟨hD₁ hd, h₁ d hd⟩) (fun d hd => ⟨hD₂ hd, h₂ d hd⟩)
  intro y hy
  exact (hS (hle hy)).2

theorem mem_zpowers_and_card_dvd_of_eq_inf_sup
    {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G)) {c' : G}
    (hc'A : c' ∈ A) (htriv : ∀ x ∈ X, c' * x * c'⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 X)
    (heq : L = (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L) :
    c' ∈ Subgroup.zpowers c ∧
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hθc, hθ3, -, -, -, hθr⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hθch : (aschbacherSolvableCore 3 ↥L).Characteristic := hθc
  have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
  have hsimp := Sec16.isSimpleGroup_lBar_of_sec15R hR
  have hLA : A ≤ Subgroup.normalizer (L : Set G) := hR.mem_lA.2.1
  have hθLL : (aschbacherSolvableCore 3 ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hLθ : L ≤ Subgroup.normalizer (((aschbacherSolvableCore 3 ↥L).map L.subtype : Subgroup G) :
      Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hAθ : A ≤ Subgroup.normalizer (((aschbacherSolvableCore 3 ↥L).map L.subtype : Subgroup G) :
      Set G) :=
    hLA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hO2θ : CFSG.Open.pCoreOf 2 L ≤ (aschbacherSolvableCore 3 ↥L).map L.subtype :=
    Subgroup.map_mono (hθr 2 Nat.prime_two (by norm_num))
  have hLle : L ≤ (L ⊓ X) ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype :=
    heq.le.trans (sup_le_sup_left hO2θ _)
  have hsup : (L ⊓ X).subgroupOf L ⊔ aschbacherSolvableCore 3 ↥L = ⊤ := by
    have h1 : ((L ⊓ X) ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype).subgroupOf L = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr hLle
    have h2 : ((aschbacherSolvableCore 3 ↥L).map L.subtype).subgroupOf L =
        aschbacherSolvableCore 3 ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rwa [Subgroup.subgroupOf_sup inf_le_left hθLL, h2] at h1
  have hθbot : (aschbacherSolvableCore 3 ↥L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hDtop : ((L ⊓ X).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) hsup
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      hθbot, sup_bot_eq] at h1
  have h3L : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    have h3 : 3 ∣ Nat.card L := Sec16.Proof1613.three_dvd_card_L hR.toSec14Std
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)] at h3
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3).dvd_of_dvd_mul_right h3
  have hKθ : pPrimeCoreOf 3 X ⊓ (L ⊓ X) ≤ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
    set K' := (pPrimeCoreOf 3 X ⊓ (L ⊓ X)).subgroupOf L with hK'
    have hN : (K'.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ ((L ⊓ X).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :=
        hDtop ▸ Subgroup.mem_top g
      obtain ⟨d, hd, rfl⟩ := hg
      obtain ⟨k, hk, rfl⟩ := hn
      have hd' : (d : G) ∈ L ⊓ X := Subgroup.mem_subgroupOf.mp hd
      have hk' : (k : G) ∈ pPrimeCoreOf 3 X ⊓ (L ⊓ X) := Subgroup.mem_subgroupOf.mp hk
      refine ⟨d * k * d⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 X hd'.2) _).mp hk'.1
      · exact (L ⊓ X).mul_mem ((L ⊓ X).mul_mem hd' hk'.2) ((L ⊓ X).inv_mem hd')
    rcases hN.eq_bot_or_eq_top with h | h
    · intro x hx
      have hxL : x ∈ L := hx.2.1
      have hxK : (⟨x, hxL⟩ : ↥L) ∈ K' := Subgroup.mem_subgroupOf.mpr hx
      have hmem : (⟨x, hxL⟩ : ↥L) ∈ aschbacherSolvableCore 3 ↥L := by
        have h1 := (Subgroup.map_eq_bot_iff _).mp h hxK
        rwa [QuotientGroup.ker_mk'] at h1
      exact ⟨_, hmem, rfl⟩
    · exfalso
      have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card K' := by
        have h2 := Subgroup.card_map_dvd K' (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        rwa [h, Subgroup.card_top] at h2
      have h2 : Nat.card K' = Nat.card ↥(pPrimeCoreOf 3 X ⊓ (L ⊓ X)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans inf_le_left)).toEquiv
      have h3 : Nat.card ↥(pPrimeCoreOf 3 X ⊓ (L ⊓ X)) ∣ Nat.card ↥(pPrimeCoreOf 3 X) :=
        Subgroup.card_dvd_of_le inf_le_left
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
        ((h3L.trans h1).trans (h2 ▸ h3))
  refine ⟨?_, ?_⟩
  ·
    have htrivL : ∀ y ∈ L, c' * y * c'⁻¹ * y⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
      refine conj_mul_inv_mem_of_le_sup hLθ heq.le inf_le_left
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (fun d hd => hKθ ⟨htriv d hd.2, ?_, ?_⟩)
        (fun d hd => ?_)
      · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLA hc'A) d).mp hd.1) (L.inv_mem hd.1)
      · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAX hc'A) d).mp hd.2) (X.inv_mem hd.2)
      · have hdθ := hO2θ hd
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hAθ hc'A) d).mp hdθ)
          (Subgroup.inv_mem _ hdθ)
    have hmem : c' ∈ (Subgroup.zpowers c : Set G) := by
      rw [← hR.mem_lA.2.2.1]
      exact ⟨hc'A, htrivL⟩
    exact hmem
  ·
    set ι : ↥(L ⊓ X) →* ↥X ⧸ CFSG.pPrimeCore 3 ↥X :=
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)).comp (Subgroup.inclusion inf_le_right) with hι
    set κ : ↥(L ⊓ X) →* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp (Subgroup.inclusion inf_le_left)
      with hκ
    have hκs : Function.Surjective κ := by
      intro q
      have hq : q ∈ ((L ⊓ X).subgroupOf L).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :=
        hDtop ▸ Subgroup.mem_top q
      obtain ⟨d, hd, rfl⟩ := hq
      exact ⟨⟨d, Subgroup.mem_subgroupOf.mp hd⟩, rfl⟩
    have hker : ι.ker ≤ κ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker, hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have hxO : (x : G) ∈ pPrimeCoreOf 3 X := ⟨_, hx, rfl⟩
      obtain ⟨t, ht, htx⟩ := hKθ ⟨hxO, x.2⟩
      rw [MonoidHom.mem_ker, hκ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have hxt : Subgroup.inclusion inf_le_left x = t :=
        Subtype.ext (show ((Subgroup.inclusion inf_le_left x : ↥L) : G) = (t : G) from htx.symm)
      rw [hxt]
      exact ht
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = κ.ker.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hκs, Subgroup.card_top]
    rw [h1]
    refine (Subgroup.index_dvd_of_le hker).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _

theorem case154_of_isLThreeEpsAt_two (hKa : KL3a) (hKc : KL3c) {A L Y X R : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X)
    (hRm : R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2))
    {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) (hεY : IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 f)
    (hεX : IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 k)
    (hLcl : ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X := by
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.2.2.2
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  have hsQ : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hεY
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    center_eq_bot_of_isQuasisimple_of_isSimple hq hsQ
  have hinj := conj_injective_of_center_eq_bot hZ
  have hXbp : Group.IsPerfect ↥(imgX X Y) := isPerfect_imgX hXY hXp
  obtain ⟨φX⟩ := nonempty_quot_pCore_imgX_equiv hXY
  have hεXb : IsLThreeEpsAt (↥(imgX X Y) ⧸ CFSG.pCore 2 ↥(imgX X Y)) 2 k :=
    IsLThreeEpsAt.of_mulEquiv φX hεX
  obtain ⟨hO2b, hnormb⟩ := hKa _ f hf hεY (imgX X Y) hXbp k hk hεXb
  have hεXb' : IsLThreeEpsAt ↥(imgX X Y) 2 k :=
    IsLThreeEpsAt.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO2b).trans
      QuotientGroup.quotientBot) hεXb
  rcases trichotomy154 hRm.1 hXY hXR with h1 | h2 | ⟨hne1, hinf, hcomm⟩
  · exact Or.inl h1
  ·
    exfalso
    apply h2
    obtain ⟨hP2, hPX, -⟩ := barR_inf_innQ_facts hRm.1 hR2 hXY hXR hY.1.2
      ((le_sup_left : A ≤ A ⊔ X).trans hRm.2.2)
    have hPbot : (barR Y R ⊓ innQ Y).comap
        (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊥ := by
      refine hnormb _ (hP2.comap_of_injective _ hinj) ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      refine mem_normalizer_comap_conj ?_
      rw [← Sec17.Proof17Res6.actQ_of_mem]
      exact hPX _ hxX
    rw [eq_bot_iff]
    intro σ hσ
    obtain ⟨g, rfl⟩ := hσ.2
    have hg : g ∈ (barR Y R ⊓ innQ Y).comap
        (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) := hσ
    rw [hPbot, Subgroup.mem_bot] at hg
    rw [hg, map_one]
    exact Subgroup.one_mem _
  ·
    rcases hLcl with hLcl | hLcl
    · exact Or.inl hLcl
    right
    have hbar2 : IsPGroup 2 (barR Y R) := isPGroup_barR hRm.1 hR2
    have : Nontrivial ↥(barR Y R) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne1
    have h2dvd : 2 ∣ Nat.card ↥(barR Y R) := by
      rcases hbar2.card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr this).ne'
      · exact h
    obtain ⟨⟨τ, hτ⟩, hτo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barR Y R)) 2 h2dvd
    have hτo' : orderOf τ = 2 := (Subgroup.orderOf_coe ⟨τ, hτ⟩).trans hτo
    have hτ1' : τ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hτo'
      omega
    have hτ2 : τ * τ = 1 := by
      have h1 := pow_orderOf_eq_one τ
      rw [hτo', pow_two] at h1
      exact h1
    have hτout : τ ∉ (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →*
        MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)).range := by
      intro hτr
      have h1 : τ ∈ barR Y R ⊓ innQ Y := ⟨hτ, hτr⟩
      rw [hinf, Subgroup.mem_bot] at h1
      exact hτ1' h1
    have hfix : ∀ x ∈ imgX X Y, τ x = x := by
      rintro _ ⟨x, hx, rfl⟩
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hc := hcomm τ hτ (x : G) hxX
      rw [Sec17.Proof17Res6.actQ_of_mem] at hc
      apply hinj
      rw [← mul_conj_mul_inv_eq τ, hc, mul_inv_cancel_right]
    obtain ⟨⟨φS⟩, hdiv⟩ := hKc _ f k hf hk hεY (imgX X Y) hεXb' τ hτout hτ2 hfix
    obtain ⟨m, hm⟩ := hdiv
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm
        omega
      · exact h0
    refine ⟨k, m, hk, hm1, ?_, hεX, hLcl⟩
    rw [← hm]
    exact ⟨φS⟩

section Two


theorem item154L3Point_two (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKa : KL3a) (hKc : KL3c) : Item154L3Point (· = 2) := by
  intro G _ _ A c L hR hNHJ Y hY X hX hXY hYX c' L' r e f hr hr2 he hf hfe hc' htrivY hL' hπ
    hεY3 R hRm
  subst hr2
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY.1
  have heqY : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop ⟨φ⟩ =>
      Proof1511Steps.eq_bot_of_isLThreeEpsAt _ W hperf hWc hcop hf
        (IsLThreeEpsAt.of_mulEquiv φ.symm hεY3)
  have hεY : IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 f :=
    IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heqY) hεY3
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  have hq3 := card_quot_pPrimeCore_dvd (Z := ↥X)
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
  have hc'1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'3
    omega
  have htrivX := trivial_of_le hXY (hX.1.2 hc'A) htrivY
  have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 hR.toSec14Std hNHJ hB
  have hstd' : Sec14Std G A c' L' :=
    { hR.toSec14Std with zpowers_mem_omegaA := hc', mem_lA := hL' }
  have h3L' : 3 ∣ Nat.card L' := Sec16.Proof1613.three_dvd_card_L hstd'
  have hneX := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hX
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX
  have : Group.IsPerfect (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := QuotientGroup.nontrivial_iff.mpr hneX
  have hlt : ∀ k : ℕ, 1 ≤ k → IsLThreeEpsAt (↥X ⧸ CFSG.pPrimeCore 3 ↥X) 2 k → k < f := by
    intro k hk hεX
    have hd := hq3.trans hdvd
    have hkf := le_of_pow_three_dvd_of_isLThreeEpsAt hf hεY
      (pow_three_dvd_card_of_isLThreeEpsAt hk hεX) hd
    rcases Nat.lt_or_ge k f with h | h
    · exact h
    · have hkf' : k = f := le_antisymm hkf h
      subst hkf'
      exact (false_of_isLThreeEpsAt_same hk hεX hεY hd
        (le_trans (Nat.mul_le_mul_left 2 (Nat.le_of_dvd Nat.card_pos hq3)) hle)).elim
  have hfe' : f ≤ e := Nat.le_of_dvd he hfe
  rcases read154_nhj5 h148 h134 h48 hR hNHJ hX with
    ⟨c'', hc'', htriv'', L'', hL'', h2⟩ | ⟨ψ⟩ | ⟨-, -, -, -, -, -, -, -, -, -, hL4, -⟩
  ·
    obtain ⟨hc''A, hc''3, -⟩ := zpowers_mem_omegaA_iff.mp hc''
    have hc''1 : c'' ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc''3
      omega
    have hmem := mem_zpowers_of_trivial hR.toSec14Std hLB hX hc''A hc''1 hc'A htriv'' htrivX
    have hzz : Subgroup.zpowers c'' = Subgroup.zpowers c' := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_).symm
      rw [hc''3, hc'3]
    have hLc'' : L' ∈ thetaComponentsAt 3 c'' :=
      (Proof1515.thetaComponentsAt_eq_of_zpowers_eq hzz.symm) ▸ hL'.1
    have hL : L' = L'' := (hR.chosen136.2 c'' hc'' L'' hL'').2 L' hLc'' h3L'
    subst hL
    rcases h2 with ⟨⟨ψ⟩⟩ | ⟨hL3, -⟩ | ⟨p, n, e', hp, hn, he', hiso', hεX⟩
    ·
      exfalso
      have := hlt e he
        (Sec14.isLThreeEpsAt_of_isoLThreePi148 (Proof1515.isoLThreePi_congr ψ.symm hπ))
      omega
    ·
      exfalso
      rcases hL3 with ⟨⟨φM⟩⟩ | ⟨_, ⟨φL⟩⟩ | ⟨_, ⟨φU⟩⟩
      · exact KFacts.KS14.not_isoLThreePi_M22 2 e (Proof1515.isoLThreePi_congr φM hπ)
      · have := (Sec14.Ronan148A.isoLThreePi_unique he (by norm_num) hπ
          (Or.inl ⟨by norm_num, ⟨φL⟩⟩)).1
        omega
      · have := (Sec14.Ronan148A.isoLThreePi_unique he (by norm_num) hπ
          (Or.inr ⟨by norm_num, ⟨φU⟩⟩)).1
        omega
    ·
      obtain ⟨rfl, -⟩ := Sec14.Ronan148A.isoLThreePi_unique he (Nat.mul_pos hn he') hπ hiso'
      have hnf := hlt n hn hεX
      have hqX : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := hX.2.2.2
      have heqX : CFSG.pPrimeCore 3 ↥X = CFSG.pCore 2 ↥X :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of hqX hneX fun W _ hWc hcop ⟨φ⟩ =>
          Proof1511Steps.eq_bot_of_isLThreeEpsAt _ W hqX.1 hWc hcop hn
            (IsLThreeEpsAt.of_mulEquiv φ.symm hεX)
      have hεX2 : IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n :=
        IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heqX) hεX
      have hLcl : L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L := by
        intro heq
        obtain ⟨hcc, hcard⟩ := mem_zpowers_and_card_dvd_of_eq_inf_sup hR hX.1.2 hc'A htrivX heq
        have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
          (zpowers_mem_omegaA_iff.mp hR.zpowers_mem_omegaA).2.1
        have hzz' : Subgroup.zpowers c' = Subgroup.zpowers c := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcc) ?_
          rw [hc'3, hc3]
        have hLc' : L ∈ thetaComponentsAt 3 c' :=
          (Proof1515.thetaComponentsAt_eq_of_zpowers_eq hzz'.symm) ▸ hR.mem_lA.1
        have hLL' : L = L' := (hR.chosen136.2 c' hc' L' hL').2 L hLc'
          (Sec16.Proof1613.three_dvd_card_L hR.toSec14Std)
        subst hLL'
        have hen : e ≤ n := le_of_pow_three_dvd_of_isLThreeEpsAt hn hεX
          (pow_three_dvd_card_of_isoLThreePi hπ) hcard
        omega
      rcases case154_of_isLThreeEpsAt_two hKa hKc hY.1 hXY hXp hRm hf hn hεY hεX2 (Or.inr hLcl)
        with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  ·
    exfalso
    obtain ⟨ψ⟩ := ψ
    obtain ⟨φ10⟩ := Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hX ⟨ψ⟩
      Proof1515.multFree_alternatingGroup_ten
    have hZX : Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
      CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating (by norm_num) φ10
    have heqX := pPrimeCore_eq_pCore_of_center_eq_bot hX hZX
    have hOX := Proof1515.pPrimeCoreOf_eq_pCoreOf_two heqX
    obtain ⟨E, hE, hE27⟩ := exists_E27_of_A10 φ10
    exact hc'1 (eq_one_of_trivial_of_E27_of hR.toSec14Std (J := X)
      (U := CFSG.Open.pCoreOf 2 Y) hY.2.2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hZX hc'A (hX.1.2 hc'A)
      (fun x hx => hOX ▸ htrivX x hx) hE hE27)
  ·
    exact (hc'1 (hL4 c' hc'A htrivX)).elim

end Two

theorem item154ProperR_of_five
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14)
    (h142 : Item142R) (hKa : KL3a) (hKc : KL3c) (h5 : Item154L3Five) :
    Item154ProperR :=
  item154ProperR_of_char2 h148 h134 h48 hbot h142 (item154L3Point_two h148 h134 h48 hKa hKc) h5

end CFSG.RankThree.PartTwo.Sec15.Wales154
