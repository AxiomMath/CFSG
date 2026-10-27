module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

theorem rankOne_L2_extra {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsPSL 2 2 n X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    centerSub S = S ∧ ∀ x : X, (∀ s ∈ S, x * s = s * x) → x ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : RankOneSyl (⊤ : Subgroup X) S (2 ^ n) :=
    rankOneSyl_top_of_isPSL_two_cs5 hn hX hS
  obtain ⟨P, hPS⟩ := exists_sylow_of_isSylowTwoOf_top_cs5 hS
  have hidx : (⊤ ⊓ Subgroup.normalizer (S : Set X)).relIndex ⊤ =
      (Subgroup.normalizer (S : Set X)).index := by
    rw [top_inf_eq, Subgroup.relIndex_top_right]
  have hsyl : Nat.card (Sylow 2 X) = (Subgroup.normalizer (S : Set X)).index := by
    have h : Nat.card (Sylow 2 X) = (Subgroup.normalizer ((P : Subgroup X) : Set X)).index :=
      P.card_eq_index_normalizer
    rw [hPS] at h
    exact h
  have hsylN := CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 X 2 n hX
  have hNidx : (Subgroup.normalizer (S : Set X)).index = 2 ^ n + 1 := by
    rw [← hsyl, hsylN]
  have hcS : Nat.card S = 2 ^ n := by
    have h1 := hR.index
    rw [hidx, hNidx] at h1
    omega
  have hZS : centerSub S = S :=
    Subgroup.eq_of_le_of_card_ge (centerSub_le_cs5 S) (le_of_eq (by rw [hR.zcard, hcS]))
  have hXcard : Nat.card X = 2 ^ n * (4 ^ n - 1) := by
    obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hX
    rw [Nat.card_congr
        (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
      CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
    have hodd : Odd (2 ^ n - 1) := by
      have h1 : 2 ^ n % 2 = 0 := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
        rw [pow_succ]; omega
      have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [Nat.odd_iff]; omega
    have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := (Nat.coprime_two_left.mpr hodd)
    rw [hg]
    have : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    simp [this]
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  have h4le : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hNpos : 0 < 2 ^ n - 1 := by omega
  have hNcard : Nat.card (Subgroup.normalizer (S : Set X)) = 2 ^ n * (2 ^ n - 1) := by
    have hm := Subgroup.index_mul_card (H := Subgroup.normalizer (S : Set X))
    rw [hNidx, hXcard, h4] at hm
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ n = s + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hs] at hm ⊢
    have e1 : (s + 1) * (s + 1) - 1 = s * (s + 2) := by
      have : (s + 1) * (s + 1) = s * (s + 2) + 1 := by ring
      exact Nat.sub_eq_of_eq_add this
    have e2 : s + 1 - 1 = s := by omega
    rw [e1] at hm
    rw [e2]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < s + 2 by omega)
    calc (s + 2) * Nat.card (Subgroup.normalizer (S : Set X))
        = (s + 1 + 1) * Nat.card (Subgroup.normalizer (S : Set X)) := by ring
      _ = (s + 1) * (s * (s + 2)) := hm
      _ = (s + 2) * ((s + 1) * s) := by ring
  have hSbot : S ≠ ⊥ := by
    rw [← hZS]
    exact centerSub_ne_bot_cs5 hR
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSbot
  obtain ⟨z, hzS, hz1⟩ : ∃ z ∈ S, z ≠ 1 :=
    ⟨(c : X), c.2, fun h => hc1 (Subtype.ext (by simpa using h))⟩
  have hzZ : z ∈ centerSub S := by rw [hZS]; exact hzS
  obtain ⟨z', hz'⟩ : ∃ z' : ↥(Subgroup.normalizer (S : Set X)), (z' : X) = z :=
    ⟨⟨z, Subgroup.le_normalizer hzS⟩, rfl⟩
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    simp [← hz', h]
  have hconj : (conjugatesOf z').ncard = 2 ^ n - 1 := by
    have himg : Subtype.val '' conjugatesOf z' = (S : Set X) \ {1} := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨c', hc'⟩ := isConj_iff.mp hx
        have hxeq : (x : X) = (c' : X) * z * (c' : X)⁻¹ := by
          rw [← hz', ← hc']
          simp
        refine ⟨?_, ?_⟩
        · rw [hxeq]
          exact (Subgroup.mem_normalizer_iff.mp c'.2 z).mp hzS
        · intro h1
          rw [Set.mem_singleton_iff] at h1
          have hx1 : x = 1 := Subtype.ext (by simpa using h1)
          have hx' : IsConj z' x := hx
          rw [hx1] at hx'
          have hz'eq : z' = 1 := isConj_one_left.mp hx'
          apply hz1
          simp [← hz', hz'eq]
      · rintro ⟨hwS, hw1⟩
        have hw1' : w ≠ 1 := fun h => hw1 (Set.mem_singleton_iff.mpr h)
        have hwZ : w ∈ centerSub S := by rw [hZS]; exact hwS
        obtain ⟨b, hb, hbeq⟩ := hR.ztrans z hzZ hz1 w hwZ hw1'
        have hwN : w ∈ Subgroup.normalizer (S : Set X) := Subgroup.le_normalizer hwS
        refine ⟨⟨w, hwN⟩, ?_, rfl⟩
        exact isConj_iff.mpr ⟨⟨b, hb.2⟩, Subtype.ext (by simp [hz', hbeq])⟩
    rw [← Set.ncard_image_of_injective (conjugatesOf z') Subtype.val_injective, himg,
      Set.ncard_sdiff_singleton_of_mem (show (1 : X) ∈ (S : Set X) from S.one_mem)]
    have hScard : (S : Set X).ncard = 2 ^ n := (Nat.card_coe_set_eq (S : Set X)).symm.trans hcS
    rw [hScard]
  have hCzidx : (Subgroup.centralizer ({z'} : Set ↥(Subgroup.normalizer (S : Set X)))).index
      = 2 ^ n - 1 := by
    rw [Subgroup.index_centralizer_eq_ncard, hconj]
  have hCzcard : Nat.card (Subgroup.centralizer
      ({z'} : Set ↥(Subgroup.normalizer (S : Set X)))) = 2 ^ n := by
    have hm := Subgroup.index_mul_card
      (H := Subgroup.centralizer ({z'} : Set ↥(Subgroup.normalizer (S : Set X))))
    rw [hCzidx, hNcard] at hm
    exact Nat.eq_of_mul_eq_mul_left hNpos (hm.trans (mul_comm _ _))
  have hCXle : Subgroup.centralizer (S : Set X) ≤ Subgroup.normalizer (S : Set X) :=
    Subgroup.centralizer_le_normalizer _
  have hCcard : Nat.card (Subgroup.centralizer (S : Set X)) ≤ 2 ^ n := by
    have hle : (Subgroup.centralizer (S : Set X)).subgroupOf (Subgroup.normalizer (S : Set X)) ≤
        Subgroup.centralizer ({z'} : Set ↥(Subgroup.normalizer (S : Set X))) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hz']
      exact (hx z hzS).symm
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ((Subgroup.centralizer (S : Set X)).subgroupOf
        (Subgroup.normalizer (S : Set X))) = Nat.card (Subgroup.centralizer (S : Set X)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCXle).toEquiv
    rw [h2, hCzcard] at h1
    exact h1
  have hSC : S ≤ Subgroup.centralizer (S : Set X) := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (mem_centerSub_cs5.mp (show s ∈ centerSub S by rw [hZS]; exact hs)).2 h hh
  have hEq : S = Subgroup.centralizer (S : Set X) :=
    Subgroup.eq_of_le_of_card_ge hSC (by rw [hcS]; exact hCcard)
  refine ⟨hZS, fun x hx => ?_⟩
  have hxC : x ∈ Subgroup.centralizer (S : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => (hx h hh).symm
  rw [hEq]
  exact hxC

section

variable {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ}

theorem rk1_dih [Finite Y] [X.Normal] {E : Subgroup Y} {h : Y} {N : Subgroup Y} {m : ℕ}
    (hR : RankOneSyl X S q)
    (hC : ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1)
    (hYX : IsPGroup 2 (Y ⧸ X))
    (hBsol : Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (S : Set Y)))
    (hSab : centerSub S = S)
    (hCS : ∀ x ∈ X, (∀ s ∈ S, x * s = s * x) → x ∈ S)
    (hE : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hEB : X ⊓ Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (E : Set Y))
    (hNnorm : ∀ i ∈ E ⊔ B6.conjSub h E, ∀ n ∈ N, i * n * i⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N)
    (hm : Nat.card (↥(E ⊔ B6.conjSub h E) ⧸ N.subgroupOf (E ⊔ B6.conjSub h E)) ≤ m)
    (hmq : m < q * q)
    (hnot2 : ¬ @IsPGroup 2 (↥(E ⊔ B6.conjSub h E) ⧸ N.subgroupOf (E ⊔ B6.conjSub h E))
      (@QuotientGroup.Quotient.group _ _ (N.subgroupOf (E ⊔ B6.conjSub h E))
        ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
          (hNnorm (g : Y) g.2 (n : Y) (Subgroup.mem_subgroupOf.mp hn))⟩)) :
    False := by
  have hSX : S ≤ X := hR.le
  have hSB : S ≤ X ⊓ Subgroup.normalizer (S : Set Y) := le_inf hSX Subgroup.le_normalizer
  have hZS : centerSub S ≤ S := centerSub_le_cs5 S
  have hEX : E ⊓ X ≠ ⊥ := by
    intro hbot
    apply hE1
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    refine hR.rigidity hC fun b hb => ?_
    have h1 : e * b * e⁻¹ * b⁻¹ ∈ E ⊓ X := by
      refine ⟨?_, X.mul_mem (Subgroup.Normal.conj_mem inferInstance b hb.1 e) (X.inv_mem hb.1)⟩
      have : b * e⁻¹ * b⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (hEB hb) e⁻¹).mp (E.inv_mem he)
      have h2 := E.mul_mem he this
      simpa [mul_assoc] using h2
    rw [hbot] at h1
    have h2 : e * b * e⁻¹ * b⁻¹ = 1 := h1
    calc e * b = (e * b * e⁻¹ * b⁻¹) * (b * e) := by group
      _ = b * e := by rw [h2]; simp
  have hD₀2 : IsPGroup 2 (E ⊓ X : Subgroup Y) :=
    isPGroup_of_sq_eq_one_cs5 fun x hx => hE.2 x hx.1
  have hSnormD₀ : S ≤ Subgroup.normalizer ((E ⊓ X : Subgroup Y) : Set Y) := by
    intro s hs
    have hsB := hSB hs
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨hdE, hdX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hEB hsB) d).mp hdE,
        X.mul_mem (X.mul_mem hsB.1 hdX) (X.inv_mem hsB.1)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hEB hsB) d).mpr h1, ?_⟩
      have := X.mul_mem (X.mul_mem (X.inv_mem hsB.1) h2) hsB.1
      simpa [mul_assoc] using this
  have hD₀S : E ⊓ X ≤ S := by
    have hP2 : IsPGroup 2 (S ⊔ (E ⊓ X) : Subgroup Y) :=
      IsPGroup.to_sup_of_normal_right' hR.isPGroup hD₀2 hSnormD₀
    exact le_sup_right.trans
      (le_of_isPGroup_of_sylow_le_cs5 hR.sylow hP2 le_sup_left (sup_le hSX inf_le_right))
  have hZE : centerSub S ≤ E := by
    haveI : Group.IsNilpotent ↥S := hR.isPGroup.isNilpotent
    have hnorm : ((E ⊓ X).subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hD₀S).mpr hSnormD₀
    have hD₁ne : (E ⊓ X).subgroupOf S ≠ ⊥ := by
      intro hb
      apply hEX
      rw [Subgroup.eq_bot_iff_forall] at hb ⊢
      intro x hx
      have := hb ⟨x, hD₀S hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa using congrArg Subtype.val this
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hD₁ne
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
    obtain ⟨hcD, hcZ⟩ := c.2
    have hz₁E : ((c : ↥S) : Y) ∈ E ⊓ X := by simpa [Subgroup.mem_subgroupOf] using hcD
    have hz₁Z : ((c : ↥S) : Y) ∈ centerSub S := by
      rw [mem_centerSub_cs5]
      refine ⟨(c : ↥S).2, fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.mp hcZ ⟨s, hs⟩
      exact congrArg Subtype.val this
    have hz₁ne : ((c : ↥S) : Y) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext (by simpa using h')))
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact E.one_mem
    · obtain ⟨b, hb, hbz⟩ := hR.ztrans _ hz₁Z hz₁ne z hz hz1
      rw [← hbz]
      exact (Subgroup.mem_normalizer_iff.mp (hEB hb) _).mp hz₁E.1
  by_cases hSh : B6.conjSub h S = S
  ·
    have hSE : S ≤ E := fun s hs => hZE (show s ∈ centerSub S by rw [hSab]; exact hs)
    have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
    have hcentE : E ≤ Subgroup.centralizer (S : Set Y) := fun e he =>
      Subgroup.mem_centralizer_iff.mpr fun s hs => (hEcomm e he s (hSE hs)).symm
    have hcentEh : B6.conjSub h E ≤ Subgroup.centralizer (S : Set Y) := by
      intro f hf
      rw [B6.mem_conjSub] at hf
      refine Subgroup.mem_centralizer_iff.mpr (fun s hs => ?_)
      have hs' : h⁻¹ * s * h ∈ S := B6.mem_conjSub.mp (by rw [hSh]; exact hs)
      have hc := hEcomm _ hf _ (hSE hs')
      calc s * f = h * ((h⁻¹ * s * h) * (h⁻¹ * f * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * f * h) * (h⁻¹ * s * h)) * h⁻¹ := by rw [hc]
        _ = f * s := by group
    have hclaim : ∀ y : Y, y ∈ Subgroup.centralizer (S : Set Y) → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
      intro y hy
      have hyc : ∀ s ∈ S, s * y = y * s := fun s hs => Subgroup.mem_centralizer_iff.mp hy s hs
      obtain ⟨k, hk⟩ := hYX (y : Y ⧸ X)
      have hwX : y ^ 2 ^ k ∈ X := by
        have h1 : ((y ^ 2 ^ k : Y) : Y ⧸ X) = 1 := by
          rw [QuotientGroup.mk_pow]
          exact hk
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hwS : y ^ 2 ^ k ∈ S := hCS _ hwX fun s hs => by
        have hc : Commute y s := (hyc s hs).symm
        exact (hc.pow_left (2 ^ k)).eq
      obtain ⟨j, hj⟩ := hR.isPGroup ⟨y ^ 2 ^ k, hwS⟩
      have hj' : (y ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      refine ⟨k + j, ?_⟩
      rw [pow_add, pow_mul, hj']
    have hI2 : IsPGroup 2 ↥(E ⊔ B6.conjSub h E) := by
      intro x
      obtain ⟨k, hk⟩ := hclaim x.1 (sup_le hcentE hcentEh x.2)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    haveI : (N.subgroupOf (E ⊔ B6.conjSub h E)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNnorm (g : Y) g.2 (n : Y) hn⟩
    exact hnot2 (hI2.to_quotient _)
  ·
    have hne : B6.conjSub h S ≠ S := hSh
    have hSS' : S ⊓ B6.conjSub h S = ⊥ := by
      have hsyl := isSylowTwoOf_conjSub_cs5 hR.sylow h
      obtain ⟨g, hg, hgeq⟩ := exists_conj_eq_of_isSylowTwoOf_cs5 hR.sylow hsyl
      have hgN : g ∉ Subgroup.normalizer (S : Set Y) := by
        intro hgN
        apply hne
        rw [hgeq]
        exact B6.conjSub_eq_self hgN
      rw [hgeq]
      exact hR.ti g hg hgN
    set W : Subgroup Y := centerSub S ⊔ B6.conjSub h (centerSub S) with hW
    have hZ'S' : B6.conjSub h (centerSub S) ≤ B6.conjSub h S := (B6.conjSub h).monotone hZS
    have hZ'E' : B6.conjSub h (centerSub S) ≤ B6.conjSub h E := (B6.conjSub h).monotone hZE
    have hZ'X : B6.conjSub h (centerSub S) ≤ X :=
      conjSub_le_of_normal_cs5 (hZS.trans hSX) h
    have hWX : W ≤ X := sup_le (hZS.trans hSX) hZ'X
    have hWI : W ≤ E ⊔ B6.conjSub h E :=
      sup_le (hZE.trans le_sup_left) (hZ'E'.trans le_sup_right)
    have hZZ' : centerSub S ⊓ B6.conjSub h (centerSub S) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc centerSub S ⊓ B6.conjSub h (centerSub S) ≤ S ⊓ B6.conjSub h S :=
            inf_le_inf hZS hZ'S'
        _ = ⊥ := hSS'
    have hcardZ' : Nat.card ↥(B6.conjSub h (centerSub S)) = q := by
      rw [← hR.zcard]
      exact Subgroup.card_map_of_injective (MulAut.conj h).injective
    have hqq : q * q ≤ Nat.card ↥W := by
      have := card_mul_le_card_sup_cs5 hZZ'
      rw [hcardZ', hR.zcard] at this
      exact this
    have hD'2 : IsPGroup 2 (W ⊓ N : Subgroup Y) := hN2.to_le inf_le_right
    have hZnorm : centerSub S ≤ Subgroup.normalizer ((W ⊓ N : Subgroup Y) : Set Y) :=
      le_normalizer_inf_cs5 le_sup_left fun w hw n hn => hNnorm w (hWI hw) n hn
    have hZ'norm : B6.conjSub h (centerSub S) ≤
        Subgroup.normalizer ((W ⊓ N : Subgroup Y) : Set Y) :=
      le_normalizer_inf_cs5 le_sup_right fun w hw n hn => hNnorm w (hWI hw) n hn
    have hZ2 : IsPGroup 2 (centerSub S) := hR.isPGroup.to_le hZS
    have hZ'2 : IsPGroup 2 (B6.conjSub h (centerSub S)) := hZ2.map _
    have hDS : W ⊓ N ≤ S := by
      have hP2 : IsPGroup 2 ((W ⊓ N) ⊔ centerSub S : Subgroup Y) :=
        IsPGroup.to_sup_of_normal_left' hD'2 hZ2 hZnorm
      exact le_sup_left.trans (hR.le_of_centerSub_le (sup_le (inf_le_left.trans hWX)
        (hZS.trans hSX)) hP2 le_sup_right)
    have hDS' : W ⊓ N ≤ B6.conjSub h S := by
      have hP2 : IsPGroup 2 ((W ⊓ N) ⊔ B6.conjSub h (centerSub S) : Subgroup Y) :=
        IsPGroup.to_sup_of_normal_left' hD'2 hZ'2 hZ'norm
      have hP'X : (W ⊓ N) ⊔ B6.conjSub h (centerSub S) ≤ X :=
        sup_le (inf_le_left.trans hWX) hZ'X
      have h1 : B6.conjSub h⁻¹ ((W ⊓ N) ⊔ B6.conjSub h (centerSub S)) ≤ S := by
        refine hR.le_of_centerSub_le (conjSub_le_of_normal_cs5 hP'X h⁻¹) (hP2.map _) ?_
        intro z hz
        rw [B6.mem_conjSub]
        have hmem : h * z * h⁻¹ ∈ B6.conjSub h (centerSub S) := by
          rw [B6.mem_conjSub]
          have e : h⁻¹ * (h * z * h⁻¹) * h = z := by group
          rw [e]
          exact hz
        have := (le_sup_right : B6.conjSub h (centerSub S) ≤
          (W ⊓ N) ⊔ B6.conjSub h (centerSub S)) hmem
        simpa using this
      intro x hx
      have hx' : x ∈ (W ⊓ N) ⊔ B6.conjSub h (centerSub S) := Subgroup.mem_sup_left hx
      have h2 : h⁻¹ * x * h ∈ B6.conjSub h⁻¹ ((W ⊓ N) ⊔ B6.conjSub h (centerSub S)) := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hx'
      rw [B6.mem_conjSub]
      exact h1 h2
    have hD' : W ⊓ N = ⊥ := by
      refine le_bot_iff.mp ?_
      calc W ⊓ N ≤ S ⊓ B6.conjSub h S := le_inf hDS hDS'
        _ = ⊥ := hSS'
    have hinj : Function.Injective (fun w : ↥W =>
        (QuotientGroup.mk (⟨(w : Y), hWI w.2⟩ : ↥(E ⊔ B6.conjSub h E)) :
          ↥(E ⊔ B6.conjSub h E) ⧸ N.subgroupOf (E ⊔ B6.conjSub h E))) := by
      intro w₁ w₂ hw
      have h1 := QuotientGroup.eq.mp hw
      have h2 : (w₁ : Y)⁻¹ * w₂ ∈ N := by simpa [Subgroup.mem_subgroupOf] using h1
      have h3 : (w₁ : Y)⁻¹ * w₂ ∈ W ⊓ N := ⟨W.mul_mem (W.inv_mem w₁.2) w₂.2, h2⟩
      rw [hD'] at h3
      have h4 : (w₁ : Y)⁻¹ * w₂ = 1 := h3
      exact Subtype.ext (inv_mul_eq_one.mp h4)
    have hcardW : Nat.card ↥W ≤ m := (Nat.card_le_card_of_injective _ hinj).trans hm
    exact absurd (le_trans hqq hcardW) (not_le.mpr hmq)

end

end CFSG.Quasithin.H13.L829N
