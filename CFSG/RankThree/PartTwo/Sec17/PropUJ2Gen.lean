module

public import CFSG.RankThree.PartTwo.Sec17.PropUGFree
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import Certificates.Certificate39860

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU.J2Gen

open CFSG CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Certificates.ChainArrays
open scoped Pointwise

theorem card_zpowers_sup_eq_nine {G : Type} [Group G] [Finite G] {e₁ e₂ : G}
    (h1 : e₁ * (e₁ * e₁) = 1) (h2 : e₂ * (e₂ * e₂) = 1) (hc : e₁ * e₂ = e₂ * e₁) (hne1 : e₁ ≠ 1)
    (hne2 : e₂ ≠ 1) (hne12 : e₂ ≠ e₁) (hne12' : e₂ ≠ e₁ * e₁) :
    Nat.card ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) = 9 := by
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : Commute e₁ e₂ := hc
  have hpow1 : e₁ ^ 3 = 1 := by rw [pow_three]; exact h1
  have hpow2 : e₂ ^ 3 = 1 := by rw [pow_three]; exact h2
  have ho1 : orderOf e₁ = 3 := orderOf_eq_prime hpow1 hne1
  have ho2 : orderOf e₂ = 3 := orderOf_eq_prime hpow2 hne2
  have hcardA : Nat.card (Subgroup.zpowers e₁) = 3 := by rw [Nat.card_zpowers, ho1]
  have hcardB : Nat.card (Subgroup.zpowers e₂) = 3 := by rw [Nat.card_zpowers, ho2]
  have hA_mem : ∀ x ∈ Subgroup.zpowers e₁, x = 1 ∨ x = e₁ ∨ x = e₁ * e₁ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : e₁ ^ k = e₁ ^ (k % 3) := by
      have := zpow_mod_orderOf e₁ k
      rw [ho1] at this
      simpa using this.symm
    rw [hk]
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · left; rw [hr, zpow_zero]
    · right; left; rw [hr, zpow_one]
    · right; right; rw [hr, zpow_two]
  have he₂A : e₂ ∉ Subgroup.zpowers e₁ := by
    intro h
    rcases hA_mem e₂ h with h' | h' | h'
    · exact hne2 h'
    · exact hne12 h'
    · exact hne12' h'
  have hK : Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂) ∣ 3 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ ≤ Subgroup.zpowers e₁)
      rwa [hcardA] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1' | h3
    · exact Subgroup.eq_bot_of_card_eq (H := Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂) h1'
    · exfalso
      have hKA : Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ = Subgroup.zpowers e₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hcardA, h3]))
      have hKB : Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ = Subgroup.zpowers e₂ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hcardB, h3]))
      have hAB : Subgroup.zpowers e₁ = Subgroup.zpowers e₂ := hKA.symm.trans hKB
      exact he₂A (by rw [hAB]; exact Subgroup.mem_zpowers e₂)
  have hBN : Subgroup.zpowers e₂ ≤ Subgroup.normalizer (Subgroup.zpowers e₁) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    have key : ∀ a ∈ Subgroup.zpowers e₁, e₂ * a * e₂⁻¹ = a := by
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hk : Commute e₂ (e₁ ^ k) := hcomm.symm.zpow_right k
      rw [hk.eq, mul_inv_cancel_right]
    have key' : ∀ a ∈ Subgroup.zpowers e₁, e₂⁻¹ * a * e₂ = a := by
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hk : Commute e₂⁻¹ (e₁ ^ k) := (hcomm.symm.inv_left).zpow_right k
      rw [hk.eq, inv_mul_cancel_right]
    intro h
    constructor
    · intro hh
      rw [key h hh]
      exact hh
    · intro hh
      have ha := key' (e₂ * h * e₂⁻¹) hh
      have hh2 : h = e₂ * h * e₂⁻¹ := by
        calc h = e₂⁻¹ * (e₂ * h * e₂⁻¹) * e₂ := by simp [mul_assoc]
          _ = e₂ * h * e₂⁻¹ := ha
      rw [hh2]
      exact hh
  have hE : (↑(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) : Set G) =
      (↑(Subgroup.zpowers e₁) : Set G) * ↑(Subgroup.zpowers e₂) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN
  have hAE : Subgroup.zpowers e₁ ≤ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := le_sup_left
  have hBE : Subgroup.zpowers e₂ ≤ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := le_sup_right
  have hA'card : Nat.card ↥((Subgroup.zpowers e₁).subgroupOf
      (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv, hcardA]
  have hB'card : Nat.card ↥((Subgroup.zpowers e₂).subgroupOf
      (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv, hcardB]
  have hdisj' : Disjoint ((Subgroup.zpowers e₁).subgroupOf (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂))
      ((Subgroup.zpowers e₂).subgroupOf (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) := by
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    have hx : (x : G) ∈ Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ :=
      Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [hK, Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  have hmul : (↑((Subgroup.zpowers e₁).subgroupOf (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) :
      Set ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) *
      (↑((Subgroup.zpowers e₂).subgroupOf (Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) :
        Set ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : (x : G) ∈ (↑(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) : Set G) := x.2
    rw [hE, Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    rw [Set.mem_mul]
    exact ⟨⟨a, hAE ha⟩, Subgroup.mem_subgroupOf.mpr ha, ⟨b, hBE hb⟩,
      Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hmul
  have hcard := hcompl.card_mul_card
  rw [hA'card, hB'card] at hcard
  omega

theorem mem_normalizer_kleinSub {G : Type} [Group G] [Finite G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {ε : G} (h1 : ε * a * ε⁻¹ ∈ kleinSub ha hb hab)
    (h2 : ε * b * ε⁻¹ ∈ kleinSub ha hb hab) :
    ε ∈ Subgroup.normalizer ((kleinSub ha hb hab : Subgroup G) : Set G) := by
  refine CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.mem_normalizer_of_conj_mem ?_
  intro v hv
  rcases CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.mem_kleinSub.1 hv with h | h | h | h
  · rw [h, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h]
    exact h1
  · rw [h]
    exact h2
  · have e : ε * (a * b) * ε⁻¹ = ε * a * ε⁻¹ * (ε * b * ε⁻¹) := by group
    rw [h, e]
    exact Subgroup.mul_mem _ h1 h2

theorem ne_of_eqA_false {t u : Array ℕ} {g h : GJ} (ht : Rep 315 t g.1) (hu : Rep 315 u h.1)
    (he : eqA 315 t u = false) : g ≠ h := fun hgh => by
  have := (eqA_iff ht hu).2 (congrArg Subtype.val hgh)
  rw [he] at this
  exact absurd this (by decide)

theorem klein_of_check (hV : chkV = true) (k : ℕ) (hk : k < 3) :
    ∃ (a b : GJ) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a),
      Rep 315 vGens[2 * k]! a.1 ∧ Rep 315 vGens[2 * k + 1]! b.1 ∧
      ∀ e : Array ℕ, (e = xArr ∨ e = zArr) → okA e = true → ∀ ε : GJ, Rep 315 e ε.1 →
        ε * a * ε⁻¹ ∈ kleinSub ha hb hab ∧ ε * b * ε⁻¹ ∈ kleinSub ha hb hab := by
  simp only [chkV, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hV
  obtain ⟨hV1, hV2⟩ := hV
  obtain ⟨hcomm, ⟨hxa, hxb⟩, hza, hzb⟩ := hV2 k hk
  obtain ⟨hoka, hsqa⟩ := hV1 (2 * k) (by omega)
  obtain ⟨hokb, hsqb⟩ := hV1 (2 * k + 1) (by omega)
  have ra : Rep 315 vGens[2 * k]! (eltOf vGens[2 * k]! hoka).1 := rep_eltOf hoka
  have rb : Rep 315 vGens[2 * k + 1]! (eltOf vGens[2 * k + 1]! hokb).1 := rep_eltOf hokb
  have ha2 : eltOf vGens[2 * k]! hoka * eltOf vGens[2 * k]! hoka = 1 :=
    eq_of_rep (rep_mul ra ra) rep_one hsqa
  have hb2 : eltOf vGens[2 * k + 1]! hokb * eltOf vGens[2 * k + 1]! hokb = 1 :=
    eq_of_rep (rep_mul rb rb) rep_one hsqb
  have hab : eltOf vGens[2 * k]! hoka * eltOf vGens[2 * k + 1]! hokb =
      eltOf vGens[2 * k + 1]! hokb * eltOf vGens[2 * k]! hoka :=
    (commute_of_commA ra rb hcomm).eq
  refine ⟨_, _, ha2, hb2, hab, ra, rb, ?_⟩
  intro e he hoke ε rε
  have hv := (okA_spec hoke).1
  have c1 := rep_conj rε hv ra
  have c2 := rep_conj rε hv rb
  have key : ∀ (t : Array ℕ) (x : GJ), Rep 315 t x.1 →
      inKlein vGens[2 * k]! vGens[2 * k + 1]! t = true → x ∈ kleinSub ha2 hb2 hab := by
    intro t x rt hin
    simp only [inKlein, Bool.or_eq_true] at hin
    rw [mem_kleinSub]
    rcases hin with ((h | h) | h) | h
    · exact Or.inl (eq_of_rep rt rep_one h)
    · exact Or.inr (Or.inl (eq_of_rep rt ra h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_rep rt rb h)))
    · exact Or.inr (Or.inr (Or.inr (eq_of_rep rt (rep_mul ra rb) h)))
  rcases he with rfl | rfl
  · exact ⟨key _ _ c1 hxa, key _ _ c2 hxb⟩
  · exact ⟨key _ _ c1 hza, key _ _ c2 hzb⟩

theorem rep_evalWord_aux (G : ℕ → GJ)
    (hG : ∀ i, i < 6 → Rep 315 vGens[i]! (G i).1) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < 6) → ∀ (t : Array ℕ) (g : GJ), Rep 315 t g.1 →
      Rep 315 (w.foldl (fun t i => compA 315 t vGens[i]!) t) (w.foldl (fun g i => g * G i) g).1 := by
  intro w
  induction w with
  | nil => intro _ t g h; simpa using h
  | cons i w ih =>
    intro hw t g h
    simp only [List.foldl_cons]
    exact ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _ _
      (rep_mul h (hG i (hw i (List.mem_cons_self))))

theorem foldl_mem {W : Subgroup GJ} (G : ℕ → GJ) (hW : ∀ i, i < 6 → G i ∈ W) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < 6) → ∀ g : GJ, g ∈ W → (w.foldl (fun g i => g * G i) g) ∈ W := by
  intro w
  induction w with
  | nil => intro _ g hg; simpa using hg
  | cons i w ih =>
    intro hw g hg
    simp only [List.foldl_cons]
    exact ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _
      (W.mul_mem hg (hW i (hw i (List.mem_cons_self))))

theorem exists_model :
    ∃ (E V₀ V₁ V₂ : Subgroup GJ), Nat.card E = 9 ∧ IsPGroup 2 V₀ ∧ IsPGroup 2 V₁ ∧
      IsPGroup 2 V₂ ∧ E ≤ Subgroup.normalizer (V₀ : Set GJ) ∧
      E ≤ Subgroup.normalizer (V₁ : Set GJ) ∧ E ≤ Subgroup.normalizer (V₂ : Set GJ) ∧
      V₀ ⊔ V₁ ⊔ V₂ = ⊤ := by
  classical
  have h := Certificates.certificate39860
  simp only [j2GenCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hE, hV⟩, hG⟩ := h
  simp only [chkE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hE
  obtain ⟨hx, hz, hx3, hz3, hcomm, hx1, hz1, hzx, hzxx⟩ := hE
  have rx := rep_eltOf hx
  have rz := rep_eltOf hz
  have h1 : eltOf xArr hx * (eltOf xArr hx * eltOf xArr hx) = 1 :=
    eq_of_rep (rep_mul rx (rep_mul rx rx)) rep_one hx3
  have h2 : eltOf zArr hz * (eltOf zArr hz * eltOf zArr hz) = 1 :=
    eq_of_rep (rep_mul rz (rep_mul rz rz)) rep_one hz3
  have hc : eltOf xArr hx * eltOf zArr hz = eltOf zArr hz * eltOf xArr hx :=
    (commute_of_commA rx rz hcomm).eq
  have hne1 : eltOf xArr hx ≠ 1 := ne_of_eqA_false rx rep_one hx1
  have hne2 : eltOf zArr hz ≠ 1 := ne_of_eqA_false rz rep_one hz1
  have hne12 : eltOf zArr hz ≠ eltOf xArr hx := ne_of_eqA_false rz rx hzx
  have hne12' : eltOf zArr hz ≠ eltOf xArr hx * eltOf xArr hx :=
    ne_of_eqA_false rz (rep_mul rx rx) hzxx
  have hcard := card_zpowers_sup_eq_nine h1 h2 hc hne1 hne2 hne12 hne12'
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀, ra₀, rb₀, hk₀⟩ := klein_of_check hV 0 (by norm_num)
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, ra₁, rb₁, hk₁⟩ := klein_of_check hV 1 (by norm_num)
  obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, ra₂, rb₂, hk₂⟩ := klein_of_check hV 2 (by norm_num)
  have hnorm : ∀ (a b : GJ) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a),
      (∀ e : Array ℕ, (e = xArr ∨ e = zArr) → okA e = true → ∀ ε : GJ, Rep 315 e ε.1 →
        ε * a * ε⁻¹ ∈ kleinSub ha hb hab ∧ ε * b * ε⁻¹ ∈ kleinSub ha hb hab) →
      Subgroup.zpowers (eltOf xArr hx) ⊔ Subgroup.zpowers (eltOf zArr hz) ≤
        Subgroup.normalizer ((kleinSub ha hb hab : Subgroup GJ) : Set GJ) := by
    intro a b ha hb hab hk
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · obtain ⟨c1, c2⟩ := hk xArr (Or.inl rfl) hx _ rx
      exact mem_normalizer_kleinSub ha hb hab c1 c2
    · obtain ⟨c1, c2⟩ := hk zArr (Or.inr rfl) hz _ rz
      exact mem_normalizer_kleinSub ha hb hab c1 c2
  refine ⟨Subgroup.zpowers (eltOf xArr hx) ⊔ Subgroup.zpowers (eltOf zArr hz),
    kleinSub ha₀ hb₀ hab₀, kleinSub ha₁ hb₁ hab₁, kleinSub ha₂ hb₂ hab₂, hcard,
    isPGroup_kleinSub, isPGroup_kleinSub, isPGroup_kleinSub, hnorm _ _ ha₀ hb₀ hab₀ hk₀,
    hnorm _ _ ha₁ hb₁ hab₁ hk₁, hnorm _ _ ha₂ hb₂ hab₂ hk₂, ?_⟩
  simp only [chkGen, Bool.and_eq_true] at hG
  obtain ⟨hGa, hGb⟩ := hG
  set W : Subgroup GJ := kleinSub ha₀ hb₀ hab₀ ⊔ kleinSub ha₁ hb₁ hab₁ ⊔ kleinSub ha₂ hb₂ hab₂
    with hW
  let Gel : ℕ → GJ := fun i =>
    if i = 0 then a₀ else if i = 1 then b₀ else if i = 2 then a₁ else if i = 3 then b₁
    else if i = 4 then a₂ else if i = 5 then b₂ else 1
  have hGrep : ∀ i, i < 6 → Rep 315 vGens[i]! (Gel i).1 := by
    intro i hi
    interval_cases i
    · exact ra₀
    · exact rb₀
    · exact ra₁
    · exact rb₁
    · exact ra₂
    · exact rb₂
  have hA : ∀ {a b : GJ} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a),
      a ∈ kleinSub ha hb hab ∧ b ∈ kleinSub ha hb hab :=
    fun ha hb hab => ⟨mem_kleinSub.2 (Or.inr (Or.inl rfl)),
      mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))⟩
  have m0 := hA ha₀ hb₀ hab₀
  have m1 := hA ha₁ hb₁ hab₁
  have m2 := hA ha₂ hb₂ hab₂
  have hGW : ∀ i, i < 6 → Gel i ∈ W := by
    intro i hi
    interval_cases i
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left m0.1)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left m0.2)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right m1.1)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right m1.2)
    · exact Subgroup.mem_sup_right m2.1
    · exact Subgroup.mem_sup_right m2.2
  have hwA : ∀ i ∈ wordA, i < 6 := by decide
  have hwB : ∀ i ∈ wordB, i < 6 := by decide
  have repA := rep_evalWord_aux Gel hGrep wordA hwA (idA 315) 1 rep_one
  have repB := rep_evalWord_aux Gel hGrep wordB hwB (idA 315) 1 rep_one
  have pa := eq_of_eqA repA (rep_strong (j := 0) (by norm_num)) hGa
  have pb := eq_of_eqA repB (rep_strong (j := 1) (by norm_num)) hGb
  have hcl : Subgroup.closure (((↑) : GJ → Equiv.Perm (Fin 315)) ⁻¹'
      ({permA, permB} : Set (Equiv.Perm (Fin 315)))) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  intro x hx'
  rcases hx' with hxa | hxb
  · have : x = wordA.foldl (fun g i => g * Gel i) 1 := Subtype.ext (hxa.trans pa.symm)
    rw [this]
    exact foldl_mem Gel hGW wordA hwA 1 (Subgroup.one_mem _)
  · have : x = wordB.foldl (fun g i => g * Gel i) 1 := Subtype.ext (hxb.trans pb.symm)
    rw [this]
    exact foldl_mem Gel hGW wordB hwB 1 (Subgroup.one_mem _)

theorem map_le_normalizer {X Y : Type} [Group X] [Group Y] (θ : Y ≃* X) {E₀ V : Subgroup Y}
    (h : E₀ ≤ Subgroup.normalizer (V : Set Y)) :
    E₀.map θ.toMonoidHom ≤ Subgroup.normalizer ((V.map θ.toMonoidHom : Subgroup X) : Set X) := by
  rintro _ ⟨e, he, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  obtain ⟨y, rfl⟩ := θ.surjective x
  have key : θ.toMonoidHom e * θ y * (θ.toMonoidHom e)⁻¹ = θ (e * y * e⁻¹) := by
    simp [map_mul, map_inv]
  rw [key]
  have h1 : θ y ∈ V.map θ.toMonoidHom ↔ y ∈ V := by
    constructor
    · rintro ⟨v, hv, hvy⟩
      have : v = y := θ.injective hvy
      rwa [← this]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have h2 : θ (e * y * e⁻¹) ∈ V.map θ.toMonoidHom ↔ e * y * e⁻¹ ∈ V := by
    constructor
    · rintro ⟨v, hv, hvy⟩
      have : v = e * y * e⁻¹ := θ.injective hvy
      rwa [← this]
    · intro hy
      exact ⟨_, hy, rfl⟩
  rw [h1, h2]
  exact Subgroup.mem_normalizer_iff.mp (h he) y

theorem j2GenByTwoSubgroups :
    CFSG.RankThree.PartTwo.Sec17.J2GenByTwoSubgroups := by
  intro X _ _ hX E hE
  obtain ⟨ψ⟩ := hX
  let f : X ≃* GJ := ψ.trans nativeEquivP
  obtain ⟨E₀, V₀, V₁, V₂, hE₀, hp₀, hp₁, hp₂, hn₀, hn₁, hn₂, htop⟩ := exists_model
  have hE' : Nat.card (E.map f.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hE
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_exists_conjugate_of_card_nine
    ⟨nativeEquivP.symm⟩ hE₀ hE'
  let θ : GJ ≃* X := (MulAut.conj g⁻¹).trans f.symm
  have hEθ : E₀.map θ.toMonoidHom = E := by
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    have h1 : (E₀.map θ.toMonoidHom).map f.toMonoidHom = E₀.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [θ]
    rw [h1]
    exact hg.symm
  have hn : ∀ V : Subgroup GJ, E₀ ≤ Subgroup.normalizer (V : Set GJ) →
      E ≤ Subgroup.normalizer ((V.map θ.toMonoidHom : Subgroup X) : Set X) := by
    intro V hV
    rw [← hEθ]
    exact map_le_normalizer θ hV
  have hP : ∀ V : Subgroup GJ, IsPGroup 2 V → IsPGroup 2 (V.map θ.toMonoidHom) :=
    fun V hV => hV.map θ.toMonoidHom
  apply top_le_iff.1
  calc (⊤ : Subgroup X) = (⊤ : Subgroup GJ).map θ.toMonoidHom := by
        rw [Subgroup.map_top_of_surjective _ θ.surjective]
    _ = (V₀ ⊔ V₁ ⊔ V₂).map θ.toMonoidHom := by rw [htop]
    _ = V₀.map θ.toMonoidHom ⊔ V₁.map θ.toMonoidHom ⊔ V₂.map θ.toMonoidHom := by
        rw [Subgroup.map_sup, Subgroup.map_sup]
    _ ≤ sSup {S : Subgroup X | IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X)} :=
        sup_le (sup_le (le_sSup ⟨hP _ hp₀, hn _ hn₀⟩) (le_sSup ⟨hP _ hp₁, hn _ hn₁⟩))
          (le_sSup ⟨hP _ hp₂, hn _ hn₂⟩)

end CFSG.RankThree.PartTwo.Sec17.PropU.J2Gen
