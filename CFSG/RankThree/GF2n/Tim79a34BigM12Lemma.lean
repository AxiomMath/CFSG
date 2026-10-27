module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open CFSG.Blueprint
open scoped commutatorElement

section Aux

variable {G : Type*} [Group G]

theorem exists_mem_pow_mul_eq_mul_pow {B : Subgroup G} {b k : G} (hb : b ∈ B)
    (hk : k ∈ Subgroup.normalizer (B : Set G)) (n : ℕ) :
    ∃ b' ∈ B, (b * k) ^ n = b' * k ^ n := by
  induction n with
  | zero => exact ⟨1, B.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨b', hb', h⟩ := ih
    have hkn : k ^ n ∈ Subgroup.normalizer (B : Set G) := pow_mem hk n
    refine ⟨b' * (k ^ n * b * (k ^ n)⁻¹),
      B.mul_mem hb' ((Subgroup.mem_normalizer_iff.1 hkn b).1 hb), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_of_sq_eq_one_of_mem_sup_of_odd {B K : Subgroup G} [Finite K]
    (hK : K ≤ Subgroup.normalizer (B : Set G)) (hodd : Odd (Nat.card K)) {x : G}
    (hx : x ∈ B ⊔ K) (hx2 : x ^ 2 = 1) : x ∈ B := by
  have hx' : x ∈ ((B ⊔ K : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B K hK] at hx'
  obtain ⟨b, hb, k, hk, rfl⟩ := hx'
  obtain ⟨b', hb', h⟩ := exists_mem_pow_mul_eq_mul_pow hb (hK hk) (Nat.card K)
  have hkm : k ^ Nat.card K = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard K hk)
  obtain ⟨j, hj⟩ := hodd
  have hxm : (b * k) ^ Nat.card K = b * k := by
    rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [hkm, mul_one, hxm] at h
  show b * k ∈ B
  rw [h]
  exact hb'

theorem eq_bot_or_eq_of_conj_closed {B S : Subgroup G} (hSB : S ≤ B) {h : G}
    (hS : ∀ s ∈ S, h * s * h⁻¹ ∈ S)
    (htrans : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ k : ℕ, h ^ k * b * (h ^ k)⁻¹ = b') :
    S = ⊥ ∨ S = B := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have hpow : ∀ k : ℕ, h ^ k * (s : G) * (h ^ k)⁻¹ ∈ S := by
      intro k
      induction k with
      | zero => simpa using s.2
      | succ k ih =>
        have := hS _ ih
        convert this using 1
        group
    refine le_antisymm hSB fun b' hb' => ?_
    by_cases hb1 : b' = 1
    · rw [hb1]; exact S.one_mem
    · have hs1' : (s : G) ≠ 1 := fun h' => hs1 (Subtype.ext h')
      obtain ⟨k, hk⟩ := htrans (s : G) (hSB s.2) hs1' b' hb' hb1
      rw [← hk]
      exact hpow k

theorem conj_mem_centralizer_of_mem_normalizer {S : Set G} {h c : G}
    (hh : h ∈ Subgroup.normalizer S) (hc : c ∈ Subgroup.centralizer S) :
    h * c * h⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro r hr
  have hr' : h⁻¹ * r * h ∈ S := by
    simpa using (Subgroup.mem_set_normalizer_iff.1 (inv_mem hh) r).1 hr
  have key := hc _ hr'
  calc r * (h * c * h⁻¹) = h * ((h⁻¹ * r * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * r * h)) * h⁻¹ := by rw [key]
    _ = (h * c * h⁻¹) * r := by group

end Aux

section Transport

variable {Mb N : Type*} [Group Mb] [Group N]

@[expose] def transportSub (L R : Subgroup Mb) (e : L ≃* N) : Subgroup N :=
  (R.subgroupOf L).map (e : L →* N)

theorem mem_transportSub {L R : Subgroup Mb} {e : L ≃* N} {y : N} :
    y ∈ transportSub L R e ↔ ∃ r : L, (r : Mb) ∈ R ∧ e r = y := by
  simp [transportSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_transportSub {L R : Subgroup Mb} (hRL : R ≤ L) (e : L ≃* N) :
    Nat.card (transportSub L R e) = Nat.card R := by
  have h1 : Nat.card (transportSub L R e) = Nat.card (R.subgroupOf L) :=
    Nat.card_congr (e.subgroupMap (R.subgroupOf L)).symm.toEquiv
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv

theorem commutator_transportSub_eq_top {L R : Subgroup Mb} (hRL : R ≤ L) (e : L ≃* N)
    (h : commutator R = ⊤) : commutator (transportSub L R e) = ⊤ := by
  haveI : Group.IsPerfect R := Group.isPerfect_def.2 h
  let φ : R ≃* transportSub L R e :=
    (Subgroup.subgroupOfEquivOfLe hRL).symm.trans (e.subgroupMap (R.subgroupOf L))
  haveI : Group.IsPerfect (transportSub L R e) :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
  exact Group.isPerfect_def.1 this

theorem mem_centralizer_transportSub {L R : Subgroup Mb} (e : L ≃* N) (z : L)
    (hz : (z : Mb) ∈ Subgroup.centralizer (R : Set Mb)) :
    e z ∈ Subgroup.centralizer (transportSub L R e : Set N) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨r, hr, rfl⟩ := mem_transportSub.1 hy
  have hcomm : (r : Mb) * z = z * r := Subgroup.mem_centralizer_iff.1 hz r hr
  rw [← map_mul, ← map_mul]
  exact congrArg e (Subtype.ext hcomm)

theorem card_centralizer_inf_le_transportSub [Finite N] {L R : Subgroup Mb} (e : L ≃* N) :
    Nat.card ↥(Subgroup.centralizer (R : Set Mb) ⊓ L) ≤
      Nat.card ↥(Subgroup.centralizer (transportSub L R e : Set N)) := by
  let f : ↥(Subgroup.centralizer (R : Set Mb) ⊓ L) →
      ↥(Subgroup.centralizer (transportSub L R e : Set N)) :=
    fun z => ⟨e ⟨z.1, z.2.2⟩, mem_centralizer_transportSub e ⟨z.1, z.2.2⟩ z.2.1⟩
  refine Nat.card_le_card_of_injective f ?_
  intro z z' hzz'
  have h1 : e ⟨z.1, z.2.2⟩ = e ⟨z'.1, z'.2.2⟩ := congrArg Subtype.val hzz'
  exact Subtype.ext (Subtype.mk.inj (e.injective h1))

theorem normal_transportSub {L R : Subgroup Mb} (e : L ≃* N)
    (h : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) : (transportSub L R e).Normal := by
  have hn : (R.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h g.1 g.2 n hn
  exact hn.map (e : L →* N) e.surjective

end Transport

section Counting

variable {Mb : Type*} [Group Mb]

private theorem conj_mul_eq_conj_of_comm {l b r : Mb} (hbr : r * b = b * r) :
    l * b * r * (l * b)⁻¹ = l * r * l⁻¹ := by
  calc l * b * r * (l * b)⁻¹ = l * (b * r) * b⁻¹ * l⁻¹ := by group
    _ = l * (r * b) * b⁻¹ * l⁻¹ := by rw [← hbr]
    _ = l * r * l⁻¹ := by group

private theorem inv_mul_comm_of_conj_eq {A A' x : Mb} (H : A * x * A⁻¹ = A' * x * A'⁻¹) :
    A'⁻¹ * A * x = x * (A'⁻¹ * A) := by
  calc A'⁻¹ * A * x = A'⁻¹ * (A * x * A⁻¹) * A := by group
    _ = A'⁻¹ * (A' * x * A'⁻¹) * A := by rw [H]
    _ = x * (A'⁻¹ * A) := by group

theorem card_mul_card_le_card_mulAut [Finite Mb] {L B R : Subgroup Mb} [L.Normal] (hRL : R ≤ L)
    (hBR : B ≤ Subgroup.centralizer (R : Set Mb))
    (hZ : ∀ z ∈ L, z ∈ Subgroup.centralizer (R : Set Mb) → z = 1)
    (hB0 : ∀ b ∈ B, (∀ l ∈ L, b * l = l * b) → b = 1) :
    Nat.card L * Nat.card B ≤ Nat.card (MulAut L) := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) fun f g h => DFunLike.coe_injective h
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : L × B => (MulAut.conjNormal ((p.1 : Mb) * (p.2 : Mb)) : MulAut L)) ?_
  rintro ⟨l, b⟩ ⟨l', b'⟩ h
  have hx : ∀ x : L, (l : Mb) * b * x * ((l : Mb) * b)⁻¹ =
      (l' : Mb) * b' * x * ((l' : Mb) * b')⁻¹ := fun x => by
    have h' : (MulAut.conjNormal ((l : Mb) * b) : MulAut L) =
        MulAut.conjNormal ((l' : Mb) * b') := h
    have := congrArg (fun φ : MulAut L => ((φ x : L) : Mb)) h'
    simp only [MulAut.conjNormal_apply] at this
    exact this
  have hr : ∀ r ∈ R, (l : Mb) * r * (l : Mb)⁻¹ = (l' : Mb) * r * (l' : Mb)⁻¹ := by
    intro r hr
    have h1 := hx ⟨r, hRL hr⟩
    simp only at h1
    have hb : r * (b : Mb) = b * r := Subgroup.mem_centralizer_iff.1 (hBR b.2) r hr
    have hb' : r * (b' : Mb) = b' * r := Subgroup.mem_centralizer_iff.1 (hBR b'.2) r hr
    have e1 := conj_mul_eq_conj_of_comm (l := (l : Mb)) hb
    have e2 := conj_mul_eq_conj_of_comm (l := (l' : Mb)) hb'
    rw [e1, e2] at h1
    exact h1
  have hm : (l' : Mb)⁻¹ * l ∈ Subgroup.centralizer (R : Set Mb) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr'
    exact (inv_mul_comm_of_conj_eq (hr r hr')).symm
  have hmL : (l' : Mb)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem l'.2) l.2
  have hll : (l : Mb) = l' := (inv_mul_eq_one.1 (hZ _ hmL hm)).symm
  have hcomm : ∀ x ∈ L, ((b' : Mb)⁻¹ * b) * x = x * ((b' : Mb)⁻¹ * b) := by
    intro x hxL
    have h1 := inv_mul_comm_of_conj_eq (hx ⟨x, hxL⟩)
    rw [← hll] at h1
    have : ((l : Mb) * b')⁻¹ * ((l : Mb) * b) = (b' : Mb)⁻¹ * b := by group
    rw [this] at h1
    exact h1
  have hbb : (b' : Mb)⁻¹ * b = 1 := hB0 _ (B.mul_mem (B.inv_mem b'.2) b.2) hcomm
  have hbb' : (b : Mb) = b' := (inv_mul_eq_one.1 hbb).symm
  exact Prod.ext (Subtype.ext hll) (Subtype.ext hbb')

end Counting

theorem false_of_m12_data {Mb : Type} [Group Mb] [Finite Mb] (L R B : Subgroup Mb) [L.Normal]
    (e : L ≃* ↥NativeSporadic.M12) [IsSimpleGroup ↥NativeSporadic.M12]
    (hM12 : Nat.card ↥NativeSporadic.M12 = 95040)
    (hF1 : ∀ R' : Subgroup ↥NativeSporadic.M12, Nat.card R' = 60 → commutator R' = ⊤ →
      Nat.card (Subgroup.centralizer (R' : Set ↥NativeSporadic.M12)) ≤ 2)
    (hF2 : Nat.card (MulAut ↥NativeSporadic.M12) ≤ 2 * Nat.card ↥NativeSporadic.M12)
    (hRL : R ≤ L) (hR60 : Nat.card R = 60) (hRperf : commutator R = ⊤)
    (hBe : IsElemAbelian 2 B) (hB4 : Nat.card B = 4)
    (hBR : B ≤ Subgroup.centralizer (R : Set Mb))
    (hN : Subgroup.normalizer (R : Set Mb) = Subgroup.normalizer (B : Set Mb))
    (hK : ∃ K : Subgroup Mb, Odd (Nat.card K) ∧
      Subgroup.centralizer (R : Set Mb) = B ⊔ K)
    (hreg : ∃ h : Mb, h ∈ Subgroup.normalizer (R : Set Mb) ∧
      ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ k : ℕ, h ^ k * b * (h ^ k)⁻¹ = b') : False := by
  have _ := hBe
  obtain ⟨K, hKodd, hCK⟩ := hK
  obtain ⟨h, hhN, hhreg⟩ := hreg
  have hhB : h ∈ Subgroup.normalizer (B : Set Mb) := by rw [← hN]; exact hhN
  have hhL : h ∈ Subgroup.normalizer (L : Set Mb) := by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top h
  have hKC : K ≤ Subgroup.centralizer (R : Set Mb) := by rw [hCK]; exact le_sup_right
  have hKN : K ≤ Subgroup.normalizer (B : Set Mb) :=
    hKC.trans ((Subgroup.centralizer_le_normalizer _).trans hN.le)
  have hinv : ∀ x ∈ Subgroup.centralizer (R : Set Mb), x ^ 2 = 1 → x ∈ B := fun x hx hx2 =>
    mem_of_sq_eq_one_of_mem_sup_of_odd hKN hKodd (by rw [← hCK]; exact hx) hx2
  have hZ2 : Nat.card ↥(Subgroup.centralizer (R : Set Mb) ⊓ L) ≤ 2 := by
    refine (card_centralizer_inf_le_transportSub e).trans (hF1 _ ?_ ?_)
    · rw [card_transportSub hRL e, hR60]
    · exact commutator_transportSub_eq_top hRL e hRperf
  have hS : (Subgroup.centralizer (R : Set Mb) ⊓ L) ⊓ B = ⊥ := by
    have hclosed : ∀ s ∈ (Subgroup.centralizer (R : Set Mb) ⊓ L) ⊓ B,
        h * s * h⁻¹ ∈ (Subgroup.centralizer (R : Set Mb) ⊓ L) ⊓ B := by
      rintro s ⟨⟨hsC, hsL⟩, hsB⟩
      exact ⟨⟨conj_mem_centralizer_of_mem_normalizer hhN hsC,
        (inferInstance : L.Normal).conj_mem s hsL h⟩, (Subgroup.mem_normalizer_iff.1 hhB s).1 hsB⟩
    rcases eq_bot_or_eq_of_conj_closed inf_le_right hclosed hhreg with hbot | hB
    · exact hbot
    · exfalso
      have hle : B ≤ Subgroup.centralizer (R : Set Mb) ⊓ L :=
        (hB.ge : B ≤ (Subgroup.centralizer (R : Set Mb) ⊓ L) ⊓ B).trans inf_le_left
      have := Subgroup.card_le_of_le hle
      omega
  have hZ : ∀ z ∈ L, z ∈ Subgroup.centralizer (R : Set Mb) → z = 1 := by
    intro z hzL hzC
    by_contra hz1
    have hzmem : z ∈ Subgroup.centralizer (R : Set Mb) ⊓ L := ⟨hzC, hzL⟩
    have hord : orderOf z ∣ Nat.card ↥(Subgroup.centralizer (R : Set Mb) ⊓ L) :=
      Subgroup.orderOf_dvd_natCard _ hzmem
    have hpos : 0 < Nat.card ↥(Subgroup.centralizer (R : Set Mb) ⊓ L) := Nat.card_pos
    have hle := Nat.le_of_dvd hpos hord
    have hord1 : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.1 h1)
    have hord0 : 0 < orderOf z := orderOf_pos z
    have hord2 : orderOf z = 2 := by omega
    have hz2 : z ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one z
    have hzB : z ∈ B := hinv z hzC hz2
    have hzS : z ∈ (Subgroup.centralizer (R : Set Mb) ⊓ L) ⊓ B := ⟨hzmem, hzB⟩
    rw [hS] at hzS
    exact hz1 (Subgroup.mem_bot.1 hzS)
  have hB0 : ∀ b ∈ B, (∀ l ∈ L, b * l = l * b) → b = 1 := by
    have hclosed : ∀ s ∈ B ⊓ Subgroup.centralizer (L : Set Mb),
        h * s * h⁻¹ ∈ B ⊓ Subgroup.centralizer (L : Set Mb) := by
      rintro s ⟨hsB, hsC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hhB s).1 hsB,
        conj_mem_centralizer_of_mem_normalizer hhL hsC⟩
    rcases eq_bot_or_eq_of_conj_closed inf_le_left hclosed hhreg with hbot | hB
    · intro b hb hbc
      have hmem : b ∈ B ⊓ Subgroup.centralizer (L : Set Mb) :=
        ⟨hb, Subgroup.mem_centralizer_iff.2 fun l hl => (hbc l hl).symm⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    · exfalso
      have hBL : B ≤ Subgroup.centralizer (L : Set Mb) := inf_eq_left.1 hB
      have hLB : L ≤ Subgroup.centralizer (B : Set Mb) := Subgroup.le_centralizer_iff.1 hBL
      have hLR : L ≤ Subgroup.normalizer (R : Set Mb) :=
        hLB.trans ((Subgroup.centralizer_le_normalizer _).trans hN.ge)
      haveI := normal_transportSub e (Subgroup.le_normalizer_iff.1 hLR)
      have hcard := card_transportSub hRL e
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (transportSub L R e) with hbot | htop
      · rw [hbot, Subgroup.card_bot] at hcard
        omega
      · rw [htop, Subgroup.card_top] at hcard
        omega
  have hcount := card_mul_card_le_card_mulAut (L := L) (B := B) (R := R) hRL hBR hZ hB0
  have hL : Nat.card L = Nat.card ↥NativeSporadic.M12 := Nat.card_congr e.toEquiv
  have hAut : Nat.card (MulAut L) = Nat.card (MulAut ↥NativeSporadic.M12) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hpos : 0 < Nat.card L := Nat.card_pos
  rw [hB4] at hcount
  omega

end CFSG.RankThree.GF2n.Tim79a
