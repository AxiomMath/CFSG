module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S2a
public import CFSG.Quasithin.Vol2.Ch3Sec3InputsA131

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {z w : Z}
    (hz : z ^ 3 = 1) (hz1 : z ≠ 1) (hw : w ^ 3 = 1) : ∃ j : ℕ, w = z ^ j := by
  classical
  have : Fintype Z := Fintype.ofFinite Z
  by_contra hcon
  push Not at hcon
  have h3 : Fintype.card {a : Z // a ^ 3 = 1} ≤ 3 := by
    rw [Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  have hz2 : (z ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have e1 : z ≠ z ^ 2 := fun h => hz1 (mul_left_cancel (a := z) (b := z) (c := 1)
    (by rw [mul_one, ← pow_two, ← h]))
  have e2 : (1 : Z) ≠ z ^ 2 := fun h => hz1 (by rw [← hz, pow_succ, ← h, one_mul])
  have w0 : w ≠ 1 := by simpa using hcon 0
  have w1 : w ≠ z := by simpa using hcon 1
  have w2 : w ≠ z ^ 2 := hcon 2
  let f : Fin 4 → {a : Z // a ^ 3 = 1} :=
    ![⟨1, one_pow 3⟩, ⟨z, hz⟩, ⟨z ^ 2, hz2⟩, ⟨w, hw⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, eq_comm]
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at this
  omega

omit [Finite G] in
theorem le_pRank_of_elemAb {p : ℕ} (hp : 1 < p) {Q : Type*} [Group Q] [Finite Q]
    {E : Subgroup Q} (hE : CFSG.IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p Q := by
  refine le_csSup ⟨Nat.card Q, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨A, -, hA⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card A := hA.symm
    _ ≤ Nat.card Q := Subgroup.card_le_card_group A

omit [Finite G] in
theorem mk_eq_one_iff {B N : Subgroup G} [(N.subgroupOf B).Normal] {g : G} (hg : g ∈ B) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨g, hg⟩ = 1 ↔ g ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem mk_comm_iff {B N : Subgroup G} [(N.subgroupOf B).Normal] {a b : G} (ha : a ∈ B)
    (hb : b ∈ B) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨a, ha⟩ * QuotientGroup.mk' (N.subgroupOf B) ⟨b, hb⟩ =
      QuotientGroup.mk' (N.subgroupOf B) ⟨b, hb⟩ * QuotientGroup.mk' (N.subgroupOf B) ⟨a, ha⟩ ↔
      ⁅a, b⁆ ∈ N := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

omit [Finite G] H in
theorem Y_le_B : conjClosure X D ≤ X ⊔ T ⊔ D :=
  conjClosure_le fun _ hd _ hx => (X ⊔ T ⊔ D).mul_mem ((X ⊔ T ⊔ D).mul_mem
    (Subgroup.mem_sup_right hd) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
    ((X ⊔ T ⊔ D).inv_mem (Subgroup.mem_sup_right hd))

theorem mem_Y_TD {b : G} (hb : b ∈ X ⊔ T ⊔ D) :
    ∃ y ∈ conjClosure X D, ∃ k ∈ T ⊔ D, y * k = b := by
  have hTD : T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G) := fun g hg =>
    H.hBY ((sup_le (le_sup_right.trans le_sup_left) le_sup_right : T ⊔ D ≤ X ⊔ T ⊔ D) hg)
  rw [H.hBeq, sup_assoc] at hb
  obtain ⟨y, hy, k, hk, e⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTD).mp hb
  exact ⟨y, hy, k, hk, e.symm⟩

theorem commutator_le_or (hB : IsB₀ X T D B₀) :
    ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀ ∨
      conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀ := by
  set Y := conjClosure X D with hY
  by_cases h : ⁅Y, Y⁆ ≤ B₀
  · exact Or.inl h
  right
  have hcomm : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((⁅Y, Y⁆ : Subgroup G) : Set G) := by
    refine Main3324.le_normalizer_of_conj fun g hg c hc => ?_
    have hle : ⁅Y, Y⁆ ≤ ⁅Y, Y⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (H.hBY hg) a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp (H.hBY hg) b).mp hb)
    have := hle hc
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hN : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((⁅Y, Y⁆ ⊔ B₀ : Subgroup G) : Set G) :=
    fun g hg => ChiefCount.mem_normalizer_sup (hcomm hg) (hB.nor hg)
  have hlt : B₀ < ⁅Y, Y⁆ ⊔ B₀ :=
    lt_of_le_of_ne le_sup_right fun heq => h (le_sup_left.trans heq.symm.le)
  have hYY : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  have hle : ⁅Y, Y⁆ ⊔ B₀ ≤ X ⊔ T ⊔ D := sup_le (hYY.trans Y_le_B) hB.le
  exact (H.X_le_of_normal hN (hB.max _ hlt hle hN)).2

theorem mem_of_centralizes_TD (hB : IsB₀ X T D B₀) {c : G} (hc : c ∈ T ⊔ D)
    (hcY : ∀ y ∈ conjClosure X D, ⁅c, y⁆ ∈ B₀) : c ∈ B₀ := by
  set Y := conjClosure X D with hY
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hTDB : T ⊔ D ≤ X ⊔ T ⊔ D := sup_le hTB le_sup_right
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  have hYn : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {y : G}, y ∈ Y → g * y * g⁻¹ ∈ Y :=
    fun hg y hy => (Subgroup.mem_normalizer_iff.mp (H.hBY hg) y).mp hy
  have hTn : ∀ {g : G}, g ∈ T ⊔ D → ∀ {t : G}, t ∈ T → g * t * g⁻¹ ∈ T := fun hg t ht =>
    (Subgroup.mem_normalizer_iff.mp (sup_le Subgroup.le_normalizer H.h.DN hg) t).mp ht
  let C : Subgroup G :=
    { carrier := {k | k ∈ T ⊔ D ∧ ∀ y ∈ Y, ⁅k, y⁆ ∈ B₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(T ⊔ D).mul_mem ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact B₀.mul_mem (hconjB₀ (hTDB ha) (hb' y hy)) (ha' y hy)
      one_mem' := ⟨(T ⊔ D).one_mem, fun y _ => by
        rw [commutatorElement_one_left]; exact B₀.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(T ⊔ D).inv_mem ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hconjB₀ (hTDB ((T ⊔ D).inv_mem ha)) (B₀.inv_mem (ha' y hy)) }
  have hCT : ∀ k ∈ C, ∀ t ∈ T, ⁅k, t⁆ ∈ B₀ := by
    intro k hk t ht
    have hs : ⁅k, t⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (hTn hk.1 ht) (T.inv_mem ht)
    refine H.faithful hB.le hB.nor hB.inf hB.max hs fun y hy => ?_
    have hy₁ : t⁻¹ * y * t⁻¹⁻¹ ∈ Y := hYn (hTB (T.inv_mem ht)) hy
    have hk' : k⁻¹ ∈ C := C.inv_mem hk
    have e : ⁅⁅k, t⁆, y⁆ = (k * t) * ⁅k⁻¹, t⁻¹ * y * t⁻¹⁻¹⁆ * (k * t)⁻¹ * ⁅k, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact B₀.mul_mem (hconjB₀ ((X ⊔ T ⊔ D).mul_mem (hTDB hk.1) (hTB ht)) (hk'.2 _ hy₁))
      (hk.2 y hy)
  have hCB₀ : C ≤ Subgroup.normalizer (B₀ : Set G) := fun k hk => hB.nor (hTDB hk.1)
  have hconjN : ∀ g ∈ X ⊔ T ⊔ D, (∀ k ∈ C, g * k * g⁻¹ ∈ B₀ ⊔ C) →
      ∀ n ∈ B₀ ⊔ C, g * n * g⁻¹ ∈ B₀ ⊔ C := by
    intro g hg hgC n hn
    obtain ⟨b, hb, k, hk, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCB₀).mp hn
    have e : g * (b * k) * g⁻¹ = (g * b * g⁻¹) * (g * k * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hconjB₀ hg hb)) (hgC k hk)
  have hYT : ∀ g : G, (∀ k ∈ C, ⁅k⁻¹, g⁆ ∈ B₀) → ∀ k ∈ C, g * k * g⁻¹ ∈ B₀ ⊔ C := by
    intro g hgk k hk
    have e : g * k * g⁻¹ = k * ⁅k⁻¹, g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left (hgk k hk))
  have hXn : X ≤ Subgroup.normalizer ((B₀ ⊔ C : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun x hx => hconjN x (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left hx)) (hYT x fun k hk => (C.inv_mem hk).2 x (le_conjClosure X D hx))
  have hTn' : T ≤ Subgroup.normalizer ((B₀ ⊔ C : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun t ht => hconjN t (hTB ht)
      (hYT t fun k hk => hCT _ (C.inv_mem hk) t ht)
  have hDn : D ≤ Subgroup.normalizer ((B₀ ⊔ C : Subgroup G) : Set G) := by
    refine Main3324.le_normalizer_of_conj fun d hd => hconjN d (Subgroup.mem_sup_right hd)
      fun k hk => Subgroup.mem_sup_right ⟨?_, fun y hy => ?_⟩
    · exact (T ⊔ D).mul_mem ((T ⊔ D).mul_mem (Subgroup.mem_sup_right hd) hk.1)
        ((T ⊔ D).inv_mem (Subgroup.mem_sup_right hd))
    · have hy' : d⁻¹ * y * d⁻¹⁻¹ ∈ Y := hYn (Subgroup.mem_sup_right (D.inv_mem hd)) hy
      have e : ⁅d * k * d⁻¹, y⁆ = d * ⁅k, d⁻¹ * y * d⁻¹⁻¹⁆ * d⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconjB₀ (Subgroup.mem_sup_right hd) (hk.2 _ hy')
  have hNn : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((B₀ ⊔ C : Subgroup G) : Set G) :=
    sup_le (sup_le hXn hTn') hDn
  have hCle : C ≤ B₀ := by
    by_contra hcon
    have hlt : B₀ < B₀ ⊔ C := lt_of_le_of_ne le_sup_left fun h => hcon (h ▸ le_sup_right)
    have hNB : B₀ ⊔ C ≤ X ⊔ T ⊔ D := sup_le hB.le fun k hk => hTDB hk.1
    have hYN := (H.X_le_of_normal hNn (hB.max _ hlt hNB hNn)).2
    have hTY : ∀ t ∈ T, ∀ y ∈ Y, ⁅t, y⁆ ∈ B₀ := by
      intro t ht y hy
      obtain ⟨b, hb, k, hk, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCB₀).mp (hYN hy)
      have e : ⁅t, b * k⁆ = (t * b) * ⁅k, t⁻¹⁆ * (t * b)⁻¹ * ⁅t, b⁆ := by
        simp only [commutatorElement_def]
        group
      have htb : ⁅t, b⁆ ∈ B₀ := by
        rw [commutatorElement_def]
        exact B₀.mul_mem (hconjB₀ (hTB ht) hb) (B₀.inv_mem hb)
      rw [e]
      exact B₀.mul_mem (hconjB₀ ((X ⊔ T ⊔ D).mul_mem (hTB ht) (hB.le hb))
        (hCT k hk _ (T.inv_mem ht))) htb
    have hTB₀ : T ≤ B₀ := fun t ht => H.faithful hB.le hB.nor hB.inf hB.max ht (hTY t ht)
    obtain ⟨-, hT₀, hlt'⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
    exact H.not_R_le_B₀ hT₀ hlt' (H.R_le_T.trans hTB₀)
  exact hCle ⟨hc, hcY⟩

theorem mem_of_centralizes (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) {c : G} (hc : c ∈ X ⊔ T ⊔ D)
    (hcY : ∀ y ∈ conjClosure X D, ⁅c, y⁆ ∈ B₀) : c ∈ conjClosure X D ⊔ B₀ := by
  set Y := conjClosure X D with hY
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  obtain ⟨y, hy, k, hk, rfl⟩ := H.mem_Y_TD hc
  refine Subgroup.mul_mem_sup hy (H.mem_of_centralizes_TD hB hk fun y' hy' => ?_)
  have e : ⁅k, y'⁆ = y⁻¹ * ⁅y * k, y'⁆ * y⁻¹⁻¹ * ⁅y⁻¹, y'⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact B₀.mul_mem (hconjB₀ (Y_le_B (Y.inv_mem hy)) (hcY y' hy'))
    (habel (Subgroup.commutator_mem_commutator (Y.inv_mem hy) hy'))

theorem pRank_three_le : CFSG.pRank 3 ↥(X ⊔ T ⊔ D) ≤ 2 :=
  isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank H.h.qtke.2.2 H.hB.2 3 Nat.prime_three
    (by norm_num)

theorem map_le_pCore (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).map
        (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))) ≤
      CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) := by
  have hY3 := (H.cube_mem hB habel).1
  refine le_sSup ⟨?_, ?_⟩
  · have hn : ((conjClosure X D).subgroupOf (X ⊔ T ⊔ D)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer H.hBY
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  · rintro ⟨q, hq⟩
    obtain ⟨⟨y, hyB⟩, hy, rfl⟩ := Subgroup.mem_map.mp hq
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    have e : (⟨y, hyB⟩ : ↥(X ⊔ T ⊔ D)) ^ 3 = ⟨y ^ 3, (X ⊔ T ⊔ D).pow_mem hyB 3⟩ := rfl
    rw [e]
    exact (mk_eq_one_iff _).mpr (hY3 y (Subgroup.mem_subgroupOf.mp hy))

theorem fStar_eq (hB : IsB₀ X T D B₀) (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    CFSG.generalizedFitting (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) =
      CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore _ 3).mp ?_
  have hYP := H.map_le_pCore hB habel
  unfold CFSG.IsCharacteristicP
  intro q hq
  apply hYP
  have hqY := Subgroup.centralizer_le (fun z hz => hYP hz) hq
  obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hcY : ∀ y ∈ conjClosure X D, ⁅c, y⁆ ∈ B₀ := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hqY _ (Subgroup.mem_map.mpr ⟨⟨y, Y_le_B hy⟩,
      Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    exact (mk_comm_iff hc (Y_le_B hy)).mp h1.symm
  obtain ⟨y, hy, b, hb, e⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
    (hB.le.trans H.hBY)).mp (H.mem_of_centralizes hB habel hc hcY)
  refine Subgroup.mem_map.mpr ⟨⟨y, Y_le_B hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e2 : y⁻¹ * c = b := by rw [e]; group
  show y⁻¹ * c ∈ B₀
  rw [e2]
  exact hb

theorem exists_pow_of_comm (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    (habel : ⁅conjClosure X D, conjClosure X D⁆ ≤ B₀) {s : G} (hs : s ∈ T) (hsB : s ∉ B₀)
    {u v : G} (hu : u ∈ conjClosure X D) (hv : v ∈ conjClosure X D) (huB : u ∉ B₀)
    (hsu : ⁅s, u⁆ ∈ B₀) (hsv : ⁅s, v⁆ ∈ B₀) : ∃ j : ℕ, v * (u ^ j)⁻¹ ∈ B₀ := by
  have hY3 := (H.cube_mem hB habel).1
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  set π := QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) with hπ
  have hsB' : s ∈ X ⊔ T ⊔ D := (le_sup_right.trans le_sup_left : T ≤ X ⊔ T ⊔ D) hs
  obtain ⟨h1, -, -⟩ := hA _ 3 Nat.prime_three (by norm_num) H.pRank_three_le
    (B₀.subgroupOf (X ⊔ T ⊔ D)) (H.fStar_eq hB habel)
  obtain ⟨k, hk⟩ := H.h.sylow.1 ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hS2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsB'⟩)) := by
    have hpow : π ⟨s, hsB'⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨s, hsB'⟩ : ↥(X ⊔ T ⊔ D)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hS1 : Subgroup.zpowers (π ⟨s, hsB'⟩) ≠ ⊥ := by
    intro h
    apply hsB
    have h2 : π ⟨s, hsB'⟩ = 1 := by
      have := Subgroup.mem_zpowers (π ⟨s, hsB'⟩)
      rwa [h, Subgroup.mem_bot] at this
    exact (mk_eq_one_iff hsB').mp h2
  have hcyc := h1 _ hS2 hS1
  have hmem : ∀ {w : G} (hw : w ∈ conjClosure X D), ⁅s, w⁆ ∈ B₀ →
      π ⟨w, Y_le_B hw⟩ ∈ CFSG.pCore 3 (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ⊓
        Subgroup.centralizer (Subgroup.zpowers (π ⟨s, hsB'⟩) : Set _) := by
    intro w hw hsw
    refine Subgroup.mem_inf.mpr ⟨H.map_le_pCore hB habel (Subgroup.mem_map.mpr ⟨⟨w, Y_le_B hw⟩,
      Subgroup.mem_subgroupOf.mpr hw, rfl⟩), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hc : Commute (π ⟨s, hsB'⟩) (π ⟨w, Y_le_B hw⟩) :=
      (mk_comm_iff hsB' (Y_le_B hw)).mpr hsw
    exact (hc.zpow_left n).eq
  have hcube : ∀ {w : G} (hw : w ∈ conjClosure X D), π ⟨w, Y_le_B hw⟩ ^ 3 = 1 := by
    intro w hw
    rw [← map_pow]
    exact (mk_eq_one_iff ((X ⊔ T ⊔ D).pow_mem (Y_le_B hw) 3)).mpr (hY3 w hw)
  obtain ⟨j, hj⟩ := exists_pow_of_isCyclic (z := ⟨_, hmem hu hsu⟩) (w := ⟨_, hmem hv hsv⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hcube hu))
    (fun h => huB ((mk_eq_one_iff (Y_le_B hu)).mp (congrArg Subtype.val h)))
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hcube hv))
  refine ⟨j, (mk_eq_one_iff ((X ⊔ T ⊔ D).mul_mem (Y_le_B hv)
    ((X ⊔ T ⊔ D).inv_mem ((X ⊔ T ⊔ D).pow_mem (Y_le_B hu) j)))).mp ?_⟩
  have hj' : π ⟨v, Y_le_B hv⟩ = π ⟨u, Y_le_B hu⟩ ^ j := by
    have := congrArg Subtype.val hj
    rwa [Subgroup.coe_pow] at this
  have e : (⟨v * (u ^ j)⁻¹, (X ⊔ T ⊔ D).mul_mem (Y_le_B hv)
      ((X ⊔ T ⊔ D).inv_mem ((X ⊔ T ⊔ D).pow_mem (Y_le_B hu) j))⟩ : ↥(X ⊔ T ⊔ D)) =
      ⟨v, Y_le_B hv⟩ * (⟨u, Y_le_B hu⟩ ^ j)⁻¹ := rfl
  rw [e, map_mul, map_inv, map_pow, hj', mul_inv_cancel]

end Hyp3320

end S3320

end CFSG.Quasithin.H13
