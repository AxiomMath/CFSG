module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotW
public import CFSG.Quasithin.Recognition.J2RecLines
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotA
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotList

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

section Q8D8

theorem isQ8D8_central_facts {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) :
    ∃ z : P, z ∈ Subgroup.center P ∧ z ≠ 1 ∧ z * z = 1 ∧
      (∀ c ∈ Subgroup.center P, c = 1 ∨ c = z) ∧ ∀ x : P, x * x = 1 ∨ x * x = z := by
  obtain ⟨φ, hφs, hφeq, hφne, hcenter⟩ := h.exists_hom
  refine ⟨φ (QuaternionGroup.a 2, 1), ?_, hφne, ?_, hcenter, fun x => ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := hφs g
    rw [← map_mul, ← map_mul]
    congr 1
    revert u
    decide
  · rw [← map_mul]
    have : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        (QuaternionGroup.a 2, 1) = 1 := by decide
    rw [this, map_one]
  · obtain ⟨u, rfl⟩ := hφs x
    rw [← map_mul]
    have hsq : ∀ u : QuaternionGroup 2 × DihedralGroup 4, u * u = 1 ∨
        u * u = (QuaternionGroup.a 2, 1) ∨ u * u = (1, DihedralGroup.r 2) ∨
        u * u = (QuaternionGroup.a 2, DihedralGroup.r 2) := by decide
    have hprod : ((QuaternionGroup.a 2, DihedralGroup.r 2) : QuaternionGroup 2 × DihedralGroup 4) =
        (QuaternionGroup.a 2, 1) * (1, DihedralGroup.r 2) := by decide
    have hzz : φ (QuaternionGroup.a 2, 1) * φ (QuaternionGroup.a 2, 1) = 1 := by
      rw [← map_mul]
      have : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) *
          (QuaternionGroup.a 2, 1) = 1 := by decide
      rw [this, map_one]
    rcases hsq u with h1 | h1 | h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1]
    · right; rw [h1, ← hφeq]
    · left; rw [h1, hprod, map_mul, ← hφeq, hzz]

theorem card_le_four_of_isQ8D8 {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P)
    (A : Subgroup P) (hA2 : ∀ x ∈ A, x * x = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 4 := by
  classical
  obtain ⟨z, hz, hz1, -, -, -⟩ := isQ8D8_central_facts h
  obtain ⟨x, hx2, -, hxx, -⟩ := h.exists_fiveLines hz hz1
  have hzc : ∀ g : P, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have hline : ∀ a ∈ A, a ≠ 1 → a ≠ z → ∃ i, a = x i ∨ a = z * x i := fun a ha ha1 haz =>
    h.eq_line_of_involution hz hz1 hx2 hxx (hA2 a ha) ha1 haz
  have hcomm : ∀ i j : Fin 5, x i * x j = x j * x i → i = j := by
    intro i j hij
    by_contra hne
    have h1 := hxx i j hne
    have h2 : (x i * x j) ^ 2 = 1 := by
      rw [sq]
      calc x i * x j * (x i * x j) = x i * (x j * x i) * x j := by group
        _ = x i * (x i * x j) * x j := by rw [← hij]
        _ = (x i * x i) * (x j * x j) := by group
        _ = 1 := by rw [hx2, hx2, one_mul]
    exact hz1 (h1.symm.trans h2)
  have hzl : ∀ u v : P, u * (z * v) = z * (u * v) := fun u v => by
    rw [← mul_assoc, hzc u, mul_assoc]
  have hcomm' : ∀ i j : Fin 5, ∀ a b : P, (a = x i ∨ a = z * x i) → (b = x j ∨ b = z * x j) →
      a * b = b * a → i = j := by
    intro i j a b ha hb hab
    apply hcomm i j
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab
    · rw [hzl, mul_assoc] at hab
      exact mul_left_cancel hab
    · rw [hzl, mul_assoc] at hab
      exact mul_left_cancel hab
    · have e1 : z * x i * (z * x j) = z * (z * (x i * x j)) := by rw [mul_assoc, hzl]
      have e2 : z * x j * (z * x i) = z * (z * (x j * x i)) := by rw [mul_assoc, hzl]
      rw [e1, e2] at hab
      exact mul_left_cancel (mul_left_cancel hab)
  by_cases hex : ∃ a ∈ A, a ≠ 1 ∧ a ≠ z
  · obtain ⟨a₀, ha₀, ha₀1, ha₀z⟩ := hex
    obtain ⟨i₀, hi₀⟩ := hline a₀ ha₀ ha₀1 ha₀z
    have hsub : (A : Set P) ⊆ ({1, z, x i₀, z * x i₀} : Set P) := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]; exact Set.mem_insert _ _
      by_cases haz : a = z
      · rw [haz]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      obtain ⟨j, hj⟩ := hline a ha ha1 haz
      have hji : j = i₀ := hcomm' j i₀ a a₀ hj hi₀ (hAc a ha a₀ ha₀)
      subst hji
      rcases hj with rfl | rfl
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    calc Nat.card A = Nat.card (A : Set P) := rfl
      _ ≤ Nat.card ({1, z, x i₀, z * x i₀} : Set P) := Nat.card_mono (Set.toFinite _) hsub
      _ = ({1, z, x i₀, z * x i₀} : Set P).ncard := Nat.card_coe_set_eq _
      _ ≤ ({z, x i₀, z * x i₀} : Set P).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({x i₀, z * x i₀} : Set P).ncard + 1) + 1 := by
          gcongr; exact Set.ncard_insert_le _ _
      _ ≤ ((({z * x i₀} : Set P).ncard + 1) + 1) + 1 := by
          gcongr; exact Set.ncard_insert_le _ _
      _ = 4 := by rw [Set.ncard_singleton]
  · push Not at hex
    have hsub : (A : Set P) ⊆ ({1, z} : Set P) := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]; exact Set.mem_insert _ _
      · rw [hex a ha ha1]; exact Set.mem_insert_of_mem _ rfl
    calc Nat.card A = Nat.card (A : Set P) := rfl
      _ ≤ Nat.card ({1, z} : Set P) := Nat.card_mono (Set.toFinite _) hsub
      _ = ({1, z} : Set P).ncard := Nat.card_coe_set_eq _
      _ ≤ ({z} : Set P).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ 4 := by rw [Set.ncard_singleton]; norm_num

theorem eq_or_eq_mul_of_commute_isQ8D8 {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) {z : P}
    (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) (hzz : z * z = 1) {a b : P} (ha2 : a * a = 1)
    (hb2 : b * b = 1) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hab : a * b = b * a) : b = a ∨ b = z * a := by
  obtain ⟨x, hx2, -, hxx, -⟩ := h.exists_fiveLines hz hz1
  have hzc : ∀ g : P, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have hzl : ∀ u v : P, u * (z * v) = z * (u * v) := fun u v => by
    rw [← mul_assoc, hzc u, mul_assoc]
  obtain ⟨i, hi⟩ := h.eq_line_of_involution hz hz1 hx2 hxx ha2 ha1 haz
  obtain ⟨j, hj⟩ := h.eq_line_of_involution hz hz1 hx2 hxx hb2 hb1 hbz
  have hij : i = j := by
    have hcomm : x i * x j = x j * x i := by
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact hab
      · rw [hzl, mul_assoc] at hab
        exact mul_left_cancel hab
      · rw [hzl, mul_assoc] at hab
        exact mul_left_cancel hab
      · have e1 : z * x i * (z * x j) = z * (z * (x i * x j)) := by rw [mul_assoc, hzl]
        have e2 : z * x j * (z * x i) = z * (z * (x j * x i)) := by rw [mul_assoc, hzl]
        rw [e1, e2] at hab
        exact mul_left_cancel (mul_left_cancel hab)
    by_contra hne
    have h1 := hxx i j hne
    have h2 : (x i * x j) ^ 2 = 1 := by
      rw [sq]
      calc x i * x j * (x i * x j) = x i * (x j * x i) * x j := by group
        _ = x i * (x i * x j) * x j := by rw [← hcomm]
        _ = (x i * x i) * (x j * x j) := by group
        _ = 1 := by rw [hx2, hx2, one_mul]
    exact hz1 (h1.symm.trans h2)
  subst hij
  have hzz' : ∀ v : P, z * (z * v) = v := fun v => by rw [← mul_assoc, hzz, one_mul]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (hzz' _).symm
  · exact Or.inl rfl

end Q8D8

section Action

variable {G : Type} [Group G] [Finite G]

theorem mem_pair_of_normal_elemAbelian {Q S E : Subgroup G} (hQ : IsQ8D8 ↥Q) {z : G}
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hzz : z * z = 1) (hzS : ∀ s ∈ S, s * z = z * s)
    (hcen : ∀ c ∈ Q, (∀ q ∈ Q, q * c = c * q) → c = 1 ∨ c = z)
    (hsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z) (hQS : Q ≤ S)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (hES : E ≤ S)
    (hSE : S ≤ Subgroup.normalizer (E : Set G)) (hE2 : ∀ x ∈ E, x * x = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e : G} (he : e ∈ E) {q : G} (hq : q ∈ Q) :
    q⁻¹ * (e * q * e⁻¹) = 1 ∨ q⁻¹ * (e * q * e⁻¹) = z := by
  have hzcQ : ∀ g ∈ Q, g * z = z * g := fun g hg => hzS g (hQS hg)
  have hzc' : ∀ g ∈ Q, ∀ t : G, (t = 1 ∨ t = z) → g * t = t * g := by
    rintro g hg t (rfl | rfl)
    · rw [one_mul, mul_one]
    · exact hzcQ g hg
  set d : G → G := fun q => q⁻¹ * (e * q * e⁻¹) with hd
  have hdQ : ∀ q ∈ Q, d q ∈ Q := fun q hq =>
    Q.mul_mem (Q.inv_mem hq) ((Subgroup.mem_normalizer_iff.mp (hSQ (hES he)) q).mp hq)
  have hdE : ∀ q ∈ Q, d q ∈ E := by
    intro q hq
    have h1 : q⁻¹ * e * q⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp
      (hSE (S.inv_mem (hQS hq))) e).mp he
    rw [inv_inv] at h1
    have : d q = q⁻¹ * e * q * e⁻¹ := by simp only [hd]; group
    rw [this]
    exact E.mul_mem h1 (E.inv_mem he)
  have hconj : ∀ q, e * q * e⁻¹ = q * d q := fun q => by simp only [hd]; group
  have hdq : ∀ q ∈ Q, q * d q = d q * q := by
    intro q hq
    have hq2 : (e * q * e⁻¹) * (e * q * e⁻¹) = q * q := by
      have : (e * q * e⁻¹) * (e * q * e⁻¹) = e * (q * q) * e⁻¹ := by group
      rw [this]
      rcases hsq q hq with h | h
      · rw [h]; group
      · rw [h, mul_assoc, ← hzS e⁻¹ (S.inv_mem (hES he)), mul_inv_cancel_left]
    rw [hconj] at hq2
    have hd2 := hE2 _ (hdE q hq)
    have : q * d q * (q * d q) = q * q := hq2
    have h3 : d q * (q * d q) = q := by
      have h4 : q * (d q * (q * d q)) = q * q := by rw [← mul_assoc]; exact this
      exact mul_left_cancel h4
    calc q * d q = d q * d q * (q * d q) := by rw [hd2, one_mul]
      _ = d q * (d q * (q * d q)) := by group
      _ = d q * q := by rw [h3]
  by_contra hcon
  push Not at hcon
  set w := d q with hw
  have hwQ : w ∈ Q := hdQ q hq
  have hwE : w ∈ E := hdE q hq
  let K : Subgroup G :=
    { carrier := {g | g ∈ Q ∧ (d g = 1 ∨ d g = z)}
      one_mem' := ⟨Q.one_mem, Or.inl (by simp [hd])⟩
      mul_mem' := by
        rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
        refine ⟨Q.mul_mem haQ hbQ, ?_⟩
        have e1 : d (a * b) = b⁻¹ * d a * b * d b := by
          have h1 := hconj a
          have h2 := hconj b
          calc d (a * b) = (a * b)⁻¹ * ((e * a * e⁻¹) * (e * b * e⁻¹)) := by simp only [hd]; group
            _ = b⁻¹ * d a * b * d b := by rw [h1, h2]; group
        have e2 : b⁻¹ * d a * b = d a := by
          rw [mul_assoc, ← hzc' b hbQ _ ha]; group
        rw [e1, e2]
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · left; group
        · right; group
        · right; group
        · left; exact hzz
      inv_mem' := by
        rintro a ⟨haQ, ha⟩
        refine ⟨Q.inv_mem haQ, ?_⟩
        have e1 : d a⁻¹ = a * (d a)⁻¹ * a⁻¹ := by
          have h1 := hconj a
          have h2 : e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ := by group
          calc d a⁻¹ = a * (e * a⁻¹ * e⁻¹) := by simp only [hd, inv_inv]
            _ = a * (d a)⁻¹ * a⁻¹ := by rw [h2, h1]; group
        rw [e1]
        rcases ha with ha | ha <;> rw [ha]
        · left; group
        · right
          rw [inv_eq_of_mul_eq_one_right hzz, mul_assoc, ← hzcQ a⁻¹ (Q.inv_mem haQ),
            ← mul_assoc, mul_inv_cancel, one_mul] }
  have hcover : ∀ g ∈ Q, g ∈ K ∨ g * w = w * g := by
    intro g hg
    by_cases hgK : d g = 1 ∨ d g = z
    · exact Or.inl ⟨hg, hgK⟩
    · right
      push Not at hgK
      have hzcen : (⟨z, hzQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hzcQ y y.2)
      have hzne : (⟨z, hzQ⟩ : ↥Q) ≠ 1 := fun h0 => hz1 (congrArg Subtype.val h0)
      have hline := eq_or_eq_mul_of_commute_isQ8D8 hQ hzcen hzne (Subtype.ext hzz)
        (a := ⟨w, hwQ⟩) (b := ⟨d g, hdQ g hg⟩) (Subtype.ext (hE2 w hwE))
        (Subtype.ext (hE2 _ (hdE g hg))) (fun h0 => hcon.1 (congrArg Subtype.val h0))
        (fun h0 => hcon.2 (congrArg Subtype.val h0))
        (fun h0 => hgK.1 (congrArg Subtype.val h0)) (fun h0 => hgK.2 (congrArg Subtype.val h0))
        (Subtype.ext (hEc w hwE _ (hdE g hg)))
      have hgd := hdq g hg
      rcases hline with h1 | h1
      · have h1' : d g = w := congrArg Subtype.val h1
        rw [h1'] at hgd
        exact hgd
      · have h1' : d g = z * w := congrArg Subtype.val h1
        rw [h1', mul_assoc z w g, ← mul_assoc g z w, hzcQ g hg, mul_assoc] at hgd
        exact mul_left_cancel hgd
  have hqK : q ∉ K := fun h0 => hcon.1 (h0.2.resolve_right hcon.2)
  obtain ⟨b, hbQ, hbw⟩ : ∃ b ∈ Q, b * w ≠ w * b := by
    by_contra hall
    push Not at hall
    rcases hcen w hwQ hall with h0 | h0
    · exact hcon.1 h0
    · exact hcon.2 h0
  have hqw : q * w = w * q := hdq q hq
  rcases hcover (q * b) (Q.mul_mem hq hbQ) with hqb | hqb
  ·
    have hbK : b ∈ K := (hcover b hbQ).resolve_right hbw
    exact hqK (by have := K.mul_mem hqb (K.inv_mem hbK); rwa [mul_inv_cancel_right] at this)
  · apply hbw
    calc b * w = q⁻¹ * ((q * b) * w) := by group
      _ = q⁻¹ * (w * (q * b)) := by rw [hqb]
      _ = q⁻¹ * (w * q) * b := by group
      _ = q⁻¹ * (q * w) * b := by rw [hqw]
      _ = w * b := by group

theorem le_of_forall_mem_pair {L₂ E : Subgroup G} (hchar : CharTwo L₂) {z : G}
    (hzQ : z ∈ pCoreOf 2 L₂) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzL : ∀ l ∈ L₂, l * z = z * l) (hEL : E ≤ L₂)
    (h : ∀ e ∈ E, ∀ q ∈ pCoreOf 2 L₂, q⁻¹ * (e * q * e⁻¹) = 1 ∨ q⁻¹ * (e * q * e⁻¹) = z) :
    E ≤ pCoreOf 2 L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L₂ with hQdef
  have hLQ : L₂ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L₂
  have hzt : ∀ l ∈ L₂, ∀ t : G, (t = 1 ∨ t = z) → l * t * l⁻¹ = t := by
    rintro l hl t (rfl | rfl)
    · group
    · rw [hzL l hl, mul_inv_cancel_right]
  let C : Subgroup G :=
    { carrier := {x | x ∈ L₂ ∧ ∀ q ∈ Q, q⁻¹ * (x * q * x⁻¹) = 1 ∨ q⁻¹ * (x * q * x⁻¹) = z}
      one_mem' := ⟨L₂.one_mem, fun q _ => Or.inl (by group)⟩
      mul_mem' := by
        rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
        refine ⟨L₂.mul_mem hxL hyL, fun q hq => ?_⟩
        have hyq := hy q hq
        set ty := q⁻¹ * (y * q * y⁻¹) with hty
        have hxq := hx q hq
        set tx := q⁻¹ * (x * q * x⁻¹) with htx
        have e1 : q⁻¹ * (x * y * q * (x * y)⁻¹) = tx * (x * ty * x⁻¹) := by
          simp only [htx, hty]; group
        rw [e1, hzt x hxL ty hyq]
        rcases hxq with h1 | h1 <;> rcases hyq with h2 | h2 <;> rw [h1, h2]
        · left; group
        · right; group
        · right; group
        · left; exact hzz
      inv_mem' := by
        rintro x ⟨hxL, hx⟩
        refine ⟨L₂.inv_mem hxL, fun q hq => ?_⟩
        have hq' : x⁻¹ * q * x⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hLQ (L₂.inv_mem hxL)) q).mp hq
        rw [inv_inv] at hq'
        have ht := hx _ hq'
        set t := (x⁻¹ * q * x)⁻¹ * (x * (x⁻¹ * q * x) * x⁻¹) with htdef
        have e1 : q⁻¹ * (x⁻¹ * q * x⁻¹⁻¹) = t⁻¹ := by
          simp only [htdef]; group
        rw [e1]
        rcases ht with h1 | h1 <;> rw [h1]
        · left; exact inv_one
        · right; exact inv_eq_of_mul_eq_one_right hzz }
  have hCL : C ≤ L₂ := fun x hx => hx.1
  have hconjC : ∀ l ∈ L₂, ∀ c ∈ C, l * c * l⁻¹ ∈ C := by
    intro l hl c ⟨hcL, hc⟩
    refine ⟨L₂.mul_mem (L₂.mul_mem hl hcL) (L₂.inv_mem hl), fun q hq => ?_⟩
    have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ (L₂.inv_mem hl)) q).mp hq
    rw [inv_inv] at hq'
    have ht := hc _ hq'
    have e1 : q⁻¹ * (l * c * l⁻¹ * q * (l * c * l⁻¹)⁻¹) =
        l * ((l⁻¹ * q * l)⁻¹ * (c * (l⁻¹ * q * l) * c⁻¹)) * l⁻¹ := by group
    rw [e1, hzt l hl _ ht]
    exact ht
  have hLC : L₂ ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconjC l hl c hc, fun hc => ?_⟩
    have := hconjC l⁻¹ (L₂.inv_mem hl) _ hc
    rwa [show l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ = c by group] at this
  have hodd : ∀ c ∈ C, Odd (orderOf c) → c = 1 := by
    intro c hc hmo
    have hcQ : c ∈ L₂ ⊓ Subgroup.centralizer (Q : Set G) := by
      refine ⟨hc.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      have ht := hc.2 q hq
      set t := q⁻¹ * (c * q * c⁻¹) with htdef
      have hct : c * q * c⁻¹ = q * t := by simp only [htdef]; group
      have hpow : ∀ k : ℕ, c ^ k * q * (c ^ k)⁻¹ = q * t ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc c ^ (k + 1) * q * (c ^ (k + 1))⁻¹ = c * (c ^ k * q * (c ^ k)⁻¹) * c⁻¹ := by
                rw [pow_succ']; group
            _ = c * (q * t ^ k) * c⁻¹ := by rw [ih]
            _ = (c * q * c⁻¹) * (c * t ^ k * c⁻¹) := by group
            _ = (q * t) * t ^ k := by
                rw [hct, ← conj_pow, hzt c hc.1 t ht]
            _ = q * t ^ (k + 1) := by rw [pow_succ']; group
      have hm := hpow (orderOf c)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
      have htm : t ^ orderOf c = 1 := by
        have := congrArg (fun g => q⁻¹ * g) hm
        simp only [inv_mul_cancel, ← mul_assoc, one_mul] at this
        exact this.symm
      have ht1 : t = 1 := by
        rcases ht with ht | ht
        · exact ht
        · exfalso
          obtain ⟨k, hk⟩ := hmo
          rw [ht, hk, pow_succ, pow_mul, sq, hzz, one_pow, one_mul] at htm
          exact hz1 htm
      have : c * q * c⁻¹ = q := by rw [hct, ht1, mul_one]
      calc q * c = c * q * c⁻¹ * c := by rw [this]
        _ = c * q := by group
    have hcQ' := hchar hcQ
    have h2 : IsPGroup 2 ↥Q := pCoreOf_isPGroup 2 L₂
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨c, hcQ'⟩
    have hk' : orderOf c = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
    rw [hk'] at hmo
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk'
      exact orderOf_eq_one_iff.mp hk'
    · exact absurd hmo (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩))
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    have hn : orderOf (c : G) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd hn
    refine ⟨a, Subtype.ext ?_⟩
    have hca : (c : G) ^ 2 ^ a ∈ C := C.pow_mem c.2 _
    have hord : orderOf ((c : G) ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hcm]; exact Dvd.intro m rfl), hcm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have := hodd _ hca (hord ▸ hm)
    simpa using this
  have hCQ : C ≤ Q := le_pCoreOf_of_le_normalizer 2 hCL hLC hC2
  exact fun e he => hCQ ⟨hEL he, h e he⟩

end Action

theorem stmt5_2_2_bot_J2_of (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    Stmt5_2_2_bot_J2 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp _ hS3 h111 _ _ hL2 hQ8 hO6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec52S M H with hSdef
  set Q := pCoreOf 2 L₂ with hQdef
  have hSY : IsSylowTwoOf S (Dp ⊔ S) := by
    have h := h111.h2.sylow
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hS7 : Nat.card ↥S = 2 ^ 7 := by
    rw [card_eq_two_mul_of_perm_three hSY hS3, hO6]
    norm_num
  have hSL7 : Nat.card ↥(S ⊓ L₂) = 2 ^ 7 := by
    rw [card_inf_of_card_oTwoQuot h111.h1.sylow (j := 2) (m := 15) (by norm_num)
      (by rw [hL2.card (by norm_num)]; norm_num), hQ8.1]
    norm_num
  have hSL : S ≤ L₂ := le_of_card_le_card_inf (hS7.trans hSL7.symm).le
  have hchar : CharTwo L₂ := by
    have hle : L₂ ≤ L₂ ⊔ S ⊔ borelOf (Dp ⊔ S) S := le_sup_left.trans le_sup_left
    refine CT.CharTwo.of_normal h111.h1.charTwo hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_)
    exact sup_le (sup_le Subgroup.le_normalizer h111.h1.normalizes) h111.h1.borel_le
  obtain ⟨z, hz, hz1, hzz, hcenQ, hsqQ⟩ := isQ8D8_central_facts hQ8
  have hz1' : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hzz' : (z : G) * z = 1 := congrArg Subtype.val hzz
  have hzQc : ∀ q ∈ Q, q * (z : G) = z * q := fun q hq =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
  have hLQ : L₂ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L₂
  have hcen : ∀ c ∈ Q, (∀ q ∈ Q, q * c = c * q) → c = 1 ∨ c = z := by
    intro c hc hcq
    rcases hcenQ ⟨c, hc⟩ (Subgroup.mem_center_iff.mpr fun q => Subtype.ext (hcq q q.2)) with
      h0 | h0
    · exact Or.inl (congrArg Subtype.val h0)
    · exact Or.inr (congrArg Subtype.val h0)
  have hsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = z := by
    intro q hq
    rcases hsqQ ⟨q, hq⟩ with h0 | h0
    · exact Or.inl (congrArg Subtype.val h0)
    · exact Or.inr (congrArg Subtype.val h0)
  have hzL : ∀ l ∈ L₂, l * (z : G) = z * l := by
    intro l hl
    have hlz : l * (z : G) * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl) z).mp z.2
    have hc : l * (z : G) * l⁻¹ = 1 ∨ l * (z : G) * l⁻¹ = z := by
      refine hcen _ hlz fun q hq => ?_
      have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLQ (L₂.inv_mem hl)) q).mp hq
      rw [inv_inv] at hq'
      have h1 := hzQc _ hq'
      calc q * (l * z * l⁻¹) = l * ((l⁻¹ * q * l) * z) * l⁻¹ := by group
        _ = l * (z * (l⁻¹ * q * l)) * l⁻¹ := by rw [h1]
        _ = l * z * l⁻¹ * q := by group
    rcases hc with h0 | h0
    · exfalso
      apply hz1'
      calc (z : G) = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h0]; group
    · calc l * (z : G) = l * z * l⁻¹ * l := by group
        _ = z * l := by rw [h0]
  have hSL' : IsSylowTwoOf S L₂ := by
    have h := h111.h1.sylow
    rwa [inf_eq_left.mpr hSL] at h
  have hQS : Q ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSL'
  obtain ⟨hWS, hW2, hWc, hWN, hW16⟩ := hyp.commutator_facts h510 h331 hR
  obtain ⟨hST, -, -, -, -, -, -, -⟩ := hyp.S_facts h510 h331 hR
  have hSW : S ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    hST.trans (le_sup_right.trans hWN)
  have hW2' : ∀ x ∈ ⁅V, L⁆, x * x = 1 := fun x hx => by rw [← sq]; exact hW2 x hx
  have hWQ : ⁅V, L⁆ ≤ Q := le_of_forall_mem_pair hchar z.2 hz1' hzz' hzL (hWS.trans hSL)
    fun e he q hq => mem_pair_of_normal_elemAbelian hQ8 z.2 hz1' hzz'
      (fun s hs => hzL s (hSL hs)) hcen hsq hQS (hSL.trans hLQ) hWS hSW hW2' hWc he hq
  have h4 := card_le_four_of_isQ8D8 hQ8 (⁅V, L⁆.subgroupOf Q)
    (fun x hx => Subtype.ext (hW2' _ (Subgroup.mem_subgroupOf.mp hx)))
    (fun a ha b hb => Subtype.ext (hWc _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv] at h4
  omega

end CFSG.Quasithin.H13
