module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H56
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHAltSevenThreePlane
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Tools

variable {A : Type} [Group A]

theorem eq_one_of_mul_self_of_odd {N : Subgroup A} (hN : Odd (Nat.card N)) {x : A}
    (hx : x ∈ N) (h2 : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have h3 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h3
    exact absurd (even_iff_two_dvd.mpr h3) (Nat.not_even_iff_odd.mpr hN)

theorem commutatorElement_mem_centralizer_of_isCyclic {E : Subgroup A} [IsCyclic ↥E] {x y : A}
    (hx : x ∈ Subgroup.normalizer (E : Set A)) (hy : y ∈ Subgroup.normalizer (E : Set A)) :
    ⁅x, y⁆ ∈ Subgroup.centralizer (E : Set A) := by
  have hpow : ∀ g ∈ Subgroup.normalizer (E : Set A), ∃ m : ℤ, ∀ e ∈ E, g * e * g⁻¹ = e ^ m := by
    intro g hg
    let σ : ↥E →* ↥E :=
      { toFun := fun e => ⟨g * e * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg e).mp e.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    obtain ⟨m, hm⟩ := σ.map_cyclic
    refine ⟨m, fun e he => ?_⟩
    have h := congrArg Subtype.val (hm ⟨e, he⟩)
    simpa [σ] using h
  obtain ⟨a, ha⟩ := hpow x hx
  obtain ⟨b, hb⟩ := hpow y hy
  have hyx : y * x ∈ Subgroup.normalizer (E : Set A) := Subgroup.mul_mem _ hy hx
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hfE : (y * x)⁻¹ * e * (y * x)⁻¹⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyx) e).mp he
  rw [inv_inv] at hfE
  set f := (y * x)⁻¹ * e * (y * x) with hf
  have hyf : y * f * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hy f).mp hfE
  have hxf : x * f * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hx f).mp hfE
  have h1 : (y * x) * f * (y * x)⁻¹ = e := by rw [hf]; group
  have h2 : (x * y) * f * (x * y)⁻¹ = (y * x) * f * (y * x)⁻¹ := by
    calc (x * y) * f * (x * y)⁻¹ = x * (y * f * y⁻¹) * x⁻¹ := by group
      _ = (y * f * y⁻¹) ^ a := ha _ hyf
      _ = (f ^ b) ^ a := by rw [hb f hfE]
      _ = (f ^ a) ^ b := by rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = (x * f * x⁻¹) ^ b := by rw [ha f hfE]
      _ = y * (x * f * x⁻¹) * y⁻¹ := (hb _ hxf).symm
      _ = (y * x) * f * (y * x)⁻¹ := by group
  have h3 : ⁅x, y⁆ * e * ⁅x, y⁆⁻¹ = e := by
    calc ⁅x, y⁆ * e * ⁅x, y⁆⁻¹ = (x * y) * f * (x * y)⁻¹ := by
          rw [commutatorElement_def, hf]; group
      _ = e := by rw [h2, h1]
  calc e * ⁅x, y⁆ = ⁅x, y⁆ * e * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by rw [h3]
    _ = ⁅x, y⁆ * e := by group

theorem commutator_le_centralizer_of_isCyclic {E P : Subgroup A} [IsCyclic ↥E]
    (hP : P ≤ Subgroup.normalizer (E : Set A)) :
    ⁅P, P⁆ ≤ Subgroup.centralizer (E : Set A) :=
  Subgroup.commutator_le.mpr fun _ hx _ hy =>
    commutatorElement_mem_centralizer_of_isCyclic (hP hx) (hP hy)

theorem le_of_odd_of_le_sup [Finite A] {D S N : Subgroup A} (hDo : Odd (Nat.card D))
    (hS : IsPGroup 2 ↥S) (hperm : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A))
    (hNY : N ≤ D ⊔ S)
    (hDN : D ≤ Subgroup.normalizer (N : Set A)) (hNo : Odd (Nat.card N)) : N ≤ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hDo)
  have hle : Nat.card ↥(D ⊔ S) ≤ Nat.card D * Nat.card S := by
    have hc := congrArg (fun s : Set A => Nat.card s)
      (SteinbergCH.coe_sup_eq_mul_of_mul_comm D S hperm)
    calc Nat.card ↥(D ⊔ S) = Nat.card ((D : Set A) * (S : Set A) : Set A) := hc
      _ ≤ Nat.card (D : Set A) * Nat.card (S : Set A) := Set.natCard_mul_le
      _ = Nat.card D * Nat.card S := rfl
  have hdvd : Nat.card D * Nat.card S ∣ Nat.card ↥(D ⊔ S) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hY : Nat.card ↥(D ⊔ S) = Nat.card D * Nat.card S :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have hM : Odd (Nat.card ↥(D ⊔ N)) := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hDN
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hDN
    have e := (QuotientGroup.quotientInfEquivProdNormalizerQuotient D N hDN).toEquiv
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (D ⊔ N))
    have h2 : Nat.card (N.subgroupOf (D ⊔ N)) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have h3 : Nat.card (↥D ⧸ N.subgroupOf D) ∣ Nat.card D := Subgroup.card_quotient_dvd_card _
    rw [h1, h2, ← Nat.card_congr e]
    exact (hDo.of_dvd_nat h3).mul hNo
  have hMD : Nat.card ↥(D ⊔ N) ∣ Nat.card D := by
    have h1 : Nat.card ↥(D ⊔ N) ∣ Nat.card D * Nat.card S := by
      rw [← hY]
      exact Subgroup.card_dvd_of_le (sup_le le_sup_left hNY)
    have hc2 : Nat.Coprime (Nat.card ↥(D ⊔ N)) (Nat.card S) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hM)
    exact hc2.dvd_of_dvd_mul_right h1
  have heq : D = D ⊔ N :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (Nat.le_of_dvd Nat.card_pos hMD)
  exact le_sup_right.trans heq.ge

theorem commute_of_commutator_mem [Finite A] {D S F P : Subgroup A} {z : A}
    (hDc : IsCyclic ↥D) (hDo : Odd (Nat.card D)) (hS : IsPGroup 2 ↥S)
    (hperm : (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A)) (hFo : Odd (Nat.card F))
    (hDF : D ≤ Subgroup.normalizer (F : Set A)) (hSF : S ≤ Subgroup.normalizer (F : Set A))
    (hPS : P ≤ S) (hzP : z ∈ ⁅P, P⁆) (hz2 : z * z = 1) {d : A} (hd : d ∈ D)
    (hdz : d * z * d⁻¹ * z⁻¹ ∈ F) : d * z = z * d := by
  have hPP : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have hzS : z ∈ S := hPS (hPP hzP)
  set N := F ⊓ (D ⊔ S) with hN
  have hNo : Odd (Nat.card N) := hFo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hND : N ≤ D := le_of_odd_of_le_sup hDo hS hperm inf_le_right
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hDF hx, Subgroup.le_normalizer (le_sup_left (a := D) (b := S) hx)⟩) hNo
  have : IsCyclic ↥D := hDc
  have : IsCyclic ↥N := Subgroup.isCyclic_of_le hND
  have hPN : P ≤ Subgroup.normalizer (N : Set A) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hSF (hPS hx), Subgroup.le_normalizer (le_sup_right (a := D) (b := S) (hPS hx))⟩
  have hzC : z ∈ Subgroup.centralizer (N : Set A) := commutator_le_centralizer_of_isCyclic hPN hzP
  set c := d * z * d⁻¹ * z⁻¹ with hc
  have hcY : c ∈ D ⊔ S :=
    (D ⊔ S).mul_mem ((D ⊔ S).mul_mem ((D ⊔ S).mul_mem (le_sup_left (a := D) (b := S) hd)
      (le_sup_right (a := D) (b := S) hzS)) ((D ⊔ S).inv_mem (le_sup_left (a := D) (b := S) hd)))
      ((D ⊔ S).inv_mem (le_sup_right (a := D) (b := S) hzS))
  have hcN : c ∈ N := ⟨hdz, hcY⟩
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hcz : c * z = z * c := Subgroup.mem_centralizer_iff.mp hzC c hcN
  have hi1 : c⁻¹ = z * d * z⁻¹ * d⁻¹ := by rw [hc]; group
  rw [hzi] at hi1
  have hi2 : z * c * z⁻¹ = z * d * z * d⁻¹ := by
    rw [hc, hzi]
    calc z * (d * z * d⁻¹ * z) * z = z * d * z * d⁻¹ * (z * z) := by group
      _ = z * d * z * d⁻¹ := by rw [hz2, mul_one]
  have hinv : z * c * z⁻¹ = c⁻¹ := hi2.trans hi1.symm
  have hc2 : c * c = 1 := by
    have h1 : z * c * z⁻¹ = c := by rw [← hcz]; group
    rw [h1] at hinv
    calc c * c = c * c⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel c
  have hc1 : c = 1 := eq_one_of_mul_self_of_odd hNo hcN hc2
  calc d * z = c * z * d := by rw [hc]; group
    _ = z * d := by rw [hc1, one_mul]

theorem commutator_le_of_forall_eq_mul {W R C : Subgroup A}
    (hW : ∀ w ∈ W, ∃ r ∈ R, ∃ c ∈ C, w = r * c) (hCR : ∀ c ∈ C, ∀ r ∈ R, c * r = r * c)
    (hCC : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) : ⁅W, W⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨r₁, hr₁, c₁, hc₁, rfl⟩ := hW x hx
  obtain ⟨r₂, hr₂, c₂, hc₂, rfl⟩ := hW y hy
  have e1 : r₁ * c₁ * (r₂ * c₂) = r₁ * r₂ * (c₁ * c₂) := by
    calc r₁ * c₁ * (r₂ * c₂) = r₁ * (c₁ * r₂) * c₂ := by group
      _ = r₁ * (r₂ * c₁) * c₂ := by rw [hCR c₁ hc₁ r₂ hr₂]
      _ = r₁ * r₂ * (c₁ * c₂) := by group
  have e2 : r₂ * c₂ * (r₁ * c₁) = r₂ * r₁ * (c₁ * c₂) := by
    calc r₂ * c₂ * (r₁ * c₁) = r₂ * (c₂ * r₁) * c₁ := by group
      _ = r₂ * (r₁ * c₂) * c₁ := by rw [hCR c₂ hc₂ r₁ hr₁]
      _ = r₂ * r₁ * (c₂ * c₁) := by group
      _ = r₂ * r₁ * (c₁ * c₂) := by rw [hCC c₂ hc₂ c₁ hc₁]
  have e3 : ⁅r₁ * c₁, r₂ * c₂⁆ = r₁ * c₁ * (r₂ * c₂) * (r₂ * c₂ * (r₁ * c₁))⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e3, e1, e2]
  have e4 : r₁ * r₂ * (c₁ * c₂) * (r₂ * r₁ * (c₁ * c₂))⁻¹ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ := by group
  rw [e4]
  exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)

theorem mem_normalizer_of_commutator_le [Finite A] {R W : Subgroup A} {d : A} (hRW : R ≤ W)
    (hWR : ⁅W, W⁆ ≤ R) (hRp : ⁅R, R⁆ = R) (hd : d ∈ Subgroup.normalizer (W : Set A)) :
    d ∈ Subgroup.normalizer (R : Set A) := by
  have hle : ⁅R, R⁆ ≤ R.comap (MulAut.conj d).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    refine hWR (Subgroup.commutator_mem_commutator ?_ ?_)
    · rw [MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.mp hd a).mp (hRW ha)
    · rw [MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.mp hd b).mp (hRW hb)
  rw [hRp] at hle
  have hmap : R.map (MulAut.conj d).toMonoidHom ≤ R := Subgroup.map_le_iff_le_comap.mpr hle
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hmap
    (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective])

end Tools

section SL25

variable {A : Type} [Group A]

theorem not_isSimpleGroup_sl2_of_ringChar {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2) :
    ¬ IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) := by
  intro hs
  have hmem : (-1 : Matrix.SpecialLinearGroup (Fin 2) k) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [mul_neg_one, neg_one_mul]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hk hmem
  · obtain ⟨x, y, hxy, -⟩ := LocalAnalysis.ComponentInitial.sl2_exists_quaternion_subgroup hk
    have hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
      rw [h]; exact Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem oddCore_eq_bot_of_lieModel {R : Type} [Group R] [Finite R]
    (h1 : LieModel (R ⧸ CFSG.pCore 2 R) .PSL 2 2 2) (h2 : IsSL2 5 (R ⧸ CFSG.oddCore R)) :
    CFSG.oddCore R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs : IsSimpleGroup (R ⧸ CFSG.pCore 2 R) := isSimpleGroup_of_lieModel_PSL2 h1
  have hN : ((CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.pCore 2 R))).Normal :=
    (CFSG.oddCore_normal (G := R)).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.pCore 2 R))) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hp : IsPGroup 2 ↥(CFSG.oddCore R) := CFSG.pCore_isPGroup.to_le h
    have ho := CFSG.ABGLocalTools.odd_card_oddCore (H := R)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hk] at ho
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact h0
      · exact absurd (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩) (Nat.not_even_iff_odd.mpr ho)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    have hsup : CFSG.oddCore R ⊔ CFSG.pCore 2 R = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 R)) (CFSG.oddCore R)
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hmap : (CFSG.pCore 2 R).map (QuotientGroup.mk' (CFSG.oddCore R)) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.oddCore R))) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
      have h0 : (CFSG.oddCore R).map (QuotientGroup.mk' (CFSG.oddCore R)) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [h0, bot_sup_eq] at h1
      exact h1
    have hp : IsPGroup 2 (R ⧸ CFSG.oddCore R) := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := R)).map (QuotientGroup.mk' (CFSG.oddCore R))
      rw [hmap] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨e⟩ := h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hp.of_equiv e)
    rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_zmod] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem isSL2_of_oddCore_eq_bot {R : Type} [Group R] {p : ℕ} (hO : CFSG.oddCore R = ⊥)
    (h : IsSL2 p (R ⧸ CFSG.oddCore R)) : IsSL2 p R := by
  obtain ⟨e⟩ := h
  exact ⟨((QuotientGroup.quotientBot (G := R)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans e⟩

theorem exists_central_involution_sl25 [Finite A] {R S : Subgroup A} (hR : IsSL2 5 ↥R)
    (hSR : IsSylowTwoOf (S ⊓ R) R) :
    ∃ z ∈ R, z * z = 1 ∧ z ≠ 1 ∧ (∀ r ∈ R, r * z = z * r) ∧
      (∀ r ∈ R, r * r = 1 → r = 1 ∨ r = z) ∧ z ∈ ⁅S ⊓ R, S ⊓ R⁆ ∧
      ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ringChar (ZMod 5) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  obtain ⟨e⟩ := hR
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) * (-1) = 1 := by
    rw [neg_mul_neg, mul_one]
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ≠ 1 :=
    LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hk
  have hz2 : ((e.symm (-1) : ↥R) : A) * ((e.symm (-1) : ↥R) : A) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hneg, map_one, Subgroup.coe_one]
  have hz1 : ((e.symm (-1) : ↥R) : A) ≠ 1 := by
    intro h
    have h' : e.symm (-1) = 1 := Subtype.ext h
    apply hne
    rw [← e.apply_symm_apply (-1), h', map_one]
  have huniq : ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = ((e.symm (-1) : ↥R) : A) := by
    intro r hr hrr
    have h1 : e ⟨r, hr⟩ ^ 2 = 1 := by
      have : (⟨r, hr⟩ : ↥R) * ⟨r, hr⟩ = 1 := Subtype.ext hrr
      rw [sq, ← map_mul, this, map_one]
    rcases (LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk _).mp h1 with h | h
    · left
      have : (⟨r, hr⟩ : ↥R) = 1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · right
      have : (⟨r, hr⟩ : ↥R) = e.symm (-1) := by rw [← h, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ S ⊓ R, ∃ b ∈ S ⊓ R, a * b ≠ b * a := by
    by_contra hcon'
    have hcon : ∀ a ∈ S ⊓ R, ∀ b ∈ S ⊓ R, a * b = b * a := fun a ha b hb =>
      by_contra fun h => hcon' ⟨a, ha, b, hb, h⟩
    let P : Sylow 2 ↥R := A4.toSylow hSR
    let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
      P.mapSurjective (f := e.toMonoidHom) e.surjective
    apply (LocalAnalysis.ComponentInitial.sl2_odd_field_involution_structure hk).2.2 P'
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨u, x, hx, rfl⟩ := u
    obtain ⟨v, y, hy, rfl⟩ := v
    apply Subtype.ext
    show e.toMonoidHom x * e.toMonoidHom y = e.toMonoidHom y * e.toMonoidHom x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcon _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hCle : ⁅S ⊓ R, S ⊓ R⁆ ≤ S ⊓ R := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact (S ⊓ R).mul_mem ((S ⊓ R).mul_mem ((S ⊓ R).mul_mem hx hy) ((S ⊓ R).inv_mem hx))
      ((S ⊓ R).inv_mem hy)
  have hC2 : IsPGroup 2 ↥⁅S ⊓ R, S ⊓ R⁆ := hSR.2.1.to_le hCle
  have hc1 : ⁅a, b⁆ ∈ ⁅S ⊓ R, S ⊓ R⁆ := Subgroup.commutator_mem_commutator ha hb
  have hcne : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hdvd : 2 ∣ Nat.card ↥⁅S ⊓ R, S ⊓ R⁆ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hC2
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hn
      have hbot := Subgroup.eq_bot_of_card_eq _ hn
      rw [hbot, Subgroup.mem_bot] at hc1
      exact hcne hc1
    · rw [hn]
      exact dvd_pow_self 2 h0.ne'
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hg2 : (g : A) * g = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg, sq] at h
    exact congrArg Subtype.val h
  have hg1 : (g : A) ≠ 1 := by
    intro h
    have h' : g = 1 := Subtype.ext h
    rw [h', orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hgR : (g : A) ∈ R := (hCle g.2).2
  refine ⟨_, (e.symm (-1)).2, hz2, hz1, fun r hr => ?_, huniq, ?_, a, ha.2, b, hb.2, hab⟩
  · have h : (⟨r, hr⟩ : ↥R) * e.symm (-1) = e.symm (-1) * ⟨r, hr⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
    exact congrArg Subtype.val h
  · rcases huniq _ hgR hg2 with h | h
    · exact absurd h hg1
    · rw [← h]
      exact g.2

end SL25

section Case3

variable {Y : Type} [Group Y]

theorem conj_eq_inv_of_case_three (h3 : A36Case3 Y) {w : Y} (hw2 : w * w = 1)
    (hwF : w ∉ CFSG.fittingSubgroup Y) {f : Y} (hf : f ∈ CFSG.fittingSubgroup Y) :
    w * f * w⁻¹ = f⁻¹ := by
  obtain ⟨p, hp, hp3, -, -, e, ψ, -, hker, hact⟩ := h3
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
      omega
    exact_mod_cast h
  have hψ1 : ψ w ≠ 1 := fun h => hwF (hker ▸ MonoidHom.mem_ker.mpr h)
  have hψ2 : ψ w ^ 2 = 1 := by rw [pow_two, ← map_mul, hw2, map_one]
  have hm := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (ψ w) hψ2 hψ1
  have h := hact w ⟨f, hf⟩
  rw [hm, Matrix.neg_mulVec, Matrix.one_mulVec, ofAdd_neg, ofAdd_toAdd] at h
  have h0 : e (MulAut.conjNormal w ⟨f, hf⟩) = e (⟨f, hf⟩⁻¹) := by
    rw [map_inv]
    exact h
  have h' := congrArg Subtype.val (e.injective h0)
  rw [MulAut.conjNormal_apply] at h'
  exact h'

theorem centralizer_bijective_of_case_three [Finite Y] (h3 : A36Case3 Y)
    (hFo : Odd (Nat.card (CFSG.fittingSubgroup Y))) {w : Y} (hw2 : w * w = 1)
    (hwF : w ∉ CFSG.fittingSubgroup Y) :
    Function.Bijective ((QuotientGroup.mk' (CFSG.fittingSubgroup Y)).comp
      (Subgroup.centralizer ({w} : Set Y)).subtype) := by
  set F := CFSG.fittingSubgroup Y with hFdef
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro k hk
    have hkF : (k : Y) ∈ F := by
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact hk
    have hkw : w * k = k * w := (Subgroup.mem_centralizer_singleton_iff.mp k.2).symm
    exact Subtype.ext (Vol2.Ch10.SecB.SL2Inv.eq_one_of_case_three h3 hw2 hwF hkF hkw)
  · intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective F y
    have hc : q * w * q⁻¹ * w⁻¹ ∈ F := by
      obtain ⟨p, hp, hp3, -, -, -, ψ, -, hker, -⟩ := h3
      have : Fact p.Prime := ⟨hp⟩
      have h2 : (2 : ZMod p) ≠ 0 := by
        have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
          omega
        exact_mod_cast h
      have hψ1 : ψ w ≠ 1 := fun h => hwF (by rw [hFdef, ← hker]; exact MonoidHom.mem_ker.mpr h)
      have hψ2 : ψ w ^ 2 = 1 := by rw [pow_two, ← map_mul, hw2, map_one]
      have hm := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (ψ w) hψ2 hψ1
      have hψw : ψ w = -1 := Subtype.ext (by rw [hm, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one])
      rw [hFdef, ← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hψw]
      have hcomm : ψ q * -1 = -1 * ψ q := by rw [mul_neg_one, neg_one_mul]
      rw [hcomm]
      group
    set c := q * w * q⁻¹ * w⁻¹ with hcdef
    obtain ⟨j, hj⟩ := hFo
    set f := c ^ (j + 1) with hfdef
    have hfF : f ∈ F := F.pow_mem hc _
    have hcm : c ^ Nat.card F = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard F hc)
    have hff : f * f = c := by
      rw [hfdef, ← pow_add, show j + 1 + (j + 1) = Nat.card F + 1 by omega, pow_succ, hcm,
        one_mul]
    have e1 : q * w * q⁻¹ = c * w := by rw [hcdef]; group
    have e2 : w * f = f⁻¹ * w := by
      calc w * f = (w * f * w⁻¹) * w := by group
        _ = f⁻¹ * w := by rw [conj_eq_inv_of_case_three h3 hw2 hwF hfF]
    have e3 : f * w = w * f⁻¹ := by
      calc f * w = f * (w * f) * f⁻¹ := by group
        _ = f * (f⁻¹ * w) * f⁻¹ := by rw [e2]
        _ = w * f⁻¹ := by group
    have hk : f⁻¹ * q ∈ Subgroup.centralizer ({w} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc f⁻¹ * q * w = f⁻¹ * (q * w * q⁻¹) * q := by group
        _ = f⁻¹ * (c * w) * q := by rw [e1]
        _ = f⁻¹ * (f * f * w) * q := by rw [hff]
        _ = f * w * q := by group
        _ = w * f⁻¹ * q := by rw [e3]
        _ = w * (f⁻¹ * q) := by group
    refine ⟨⟨f⁻¹ * q, hk⟩, ?_⟩
    have h1 : QuotientGroup.mk' F f⁻¹ = 1 := (QuotientGroup.eq_one_iff f⁻¹).mpr (F.inv_mem hfF)
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, h1, one_mul]

end Case3

end CFSG.Quasithin.H13
