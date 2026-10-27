module

public import CFSG.RankThree.PartTwo.Sec4.Wales430Aut
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Proof430

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_forall_conj_eq {L : Subgroup G} (hcen : Subgroup.center ↥L = ⊥) {z : G}
    (hzL : z ∈ L) (hz : ∀ l ∈ L, z * l * z⁻¹ = l) : z = 1 := by
  have hmem : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := hz g g.2
    show (g : G) * z = z * g
    calc (g : G) * z = z * g * z⁻¹ * z := by rw [h]
      _ = z * g := by group
  rw [hcen, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_inner {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hinn : ∀ σ : MulAut ↥L, orderOf σ = 3 → σ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range)
    {x : G} (hxA : x ∈ A) (hx3 : x ^ 3 = 1) :
    ∃ v ∈ L, ∀ l ∈ L, x * l * x⁻¹ = v * l * v⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ := L.normalizerMonoidHom ⟨x, hAL hxA⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨x, hAL hxA⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ3) with h1 | h3
  · refine ⟨1, L.one_mem, fun l hl => ?_⟩
    have hσ1 : σ = 1 := orderOf_eq_one_iff.mp h1
    have h := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : G)) hσ1
    simp only [hσ, MulAut.one_apply] at h
    rw [normalizerMonoidHom_apply_coe] at h
    rw [h]
    group
  · obtain ⟨v, hv⟩ := hinn σ h3
    refine ⟨v, v.2, fun l hl => ?_⟩
    have h := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : G)) hv
    simp only [hσ, MulAut.conj_apply] at h
    rw [normalizerMonoidHom_apply_coe] at h
    simpa using h.symm

theorem card_inf_eq_nine_of_inner {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27)
    (hAmax : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {a : G}
    (hCA : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a) (ha3 : orderOf a = 3)
    (haL : a ∉ L) (hcen : Subgroup.center ↥L = ⊥)
    (hinn : ∀ σ : MulAut ↥L, orderOf σ = 3 → σ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range) :
    (A ⊓ L) ⊔ Subgroup.zpowers a = A ∧ Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have haA : a ∈ A := (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have hdecomp : ∀ x ∈ A, ∃ v ∈ A ⊓ L, x * v⁻¹ ∈ Subgroup.zpowers a := by
    intro x hxA
    obtain ⟨v, hvL, hv⟩ := exists_inner hAL hinn hxA (hA.2 x hxA)
    have hzC : x * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hv (v⁻¹ * l * v) (L.mul_mem (L.mul_mem (L.inv_mem hvL) hl) hvL)
      have h2 : v * (v⁻¹ * l * v) * v⁻¹ = l := by group
      rw [h2] at h1
      calc l * (x * v⁻¹) = x * (v⁻¹ * l * v) * x⁻¹ * (x * v⁻¹) := by rw [h1]
        _ = x * v⁻¹ * l := by group
    have hv3 : v ^ 3 = 1 := by
      refine eq_one_of_forall_conj_eq hcen (L.pow_mem hvL 3) fun l hl => ?_
      have hx3 : x ^ 3 = 1 := hA.2 x hxA
      have key : ∀ k : ℕ, x ^ k * l * (x ^ k)⁻¹ = v ^ k * l * (v ^ k)⁻¹ := by
        intro k
        induction k generalizing l with
        | zero => simp
        | succ k ih =>
          have hlk : v ^ k * l * (v ^ k)⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (L.pow_mem hvL k) hl) (L.inv_mem (L.pow_mem hvL k))
          calc x ^ (k + 1) * l * (x ^ (k + 1))⁻¹ = x * (x ^ k * l * (x ^ k)⁻¹) * x⁻¹ := by
                rw [pow_succ']
                group
            _ = x * (v ^ k * l * (v ^ k)⁻¹) * x⁻¹ := by rw [ih l hl]
            _ = v * (v ^ k * l * (v ^ k)⁻¹) * v⁻¹ := hv _ hlk
            _ = v ^ (k + 1) * l * (v ^ (k + 1))⁻¹ := by
                rw [pow_succ']
                group
      have := key 3
      rw [hx3] at this
      simpa using this.symm
    have hvA : ∀ y ∈ A, v * y = y * v := by
      intro y hyA
      obtain ⟨w, hwL, hw⟩ := exists_inner hAL hinn hyA (hA.2 y hyA)
      have hvw : v * w = w * v := by
        have h0 : (w * v)⁻¹ * (v * w) = 1 := by
          refine eq_one_of_forall_conj_eq hcen
            (L.mul_mem (L.inv_mem (L.mul_mem hwL hvL)) (L.mul_mem hvL hwL)) fun l hl => ?_
          have hl1 : w * l * w⁻¹ ∈ L := L.mul_mem (L.mul_mem hwL hl) (L.inv_mem hwL)
          have hl2 : v * l * v⁻¹ ∈ L := L.mul_mem (L.mul_mem hvL hl) (L.inv_mem hvL)
          have e1 : v * (w * l * w⁻¹) * v⁻¹ = x * (y * l * y⁻¹) * x⁻¹ := by
            rw [← hw l hl, hv _ (by rw [hw l hl]; exact hl1)]
          have e2 : w * (v * l * v⁻¹) * w⁻¹ = y * (x * l * x⁻¹) * y⁻¹ := by
            rw [← hv l hl, hw _ (by rw [hv l hl]; exact hl2)]
          have hxy : x * y = y * x := hcomm x hxA y hyA
          have e3 : x * (y * l * y⁻¹) * x⁻¹ = y * (x * l * x⁻¹) * y⁻¹ := by
            calc x * (y * l * y⁻¹) * x⁻¹ = (x * y) * l * (x * y)⁻¹ := by group
              _ = (y * x) * l * (y * x)⁻¹ := by rw [hxy]
              _ = y * (x * l * x⁻¹) * y⁻¹ := by group
          have e4 : v * (w * l * w⁻¹) * v⁻¹ = w * (v * l * v⁻¹) * w⁻¹ := by rw [e1, e2, e3]
          calc (w * v)⁻¹ * (v * w) * l * ((w * v)⁻¹ * (v * w))⁻¹
              = (w * v)⁻¹ * (v * (w * l * w⁻¹) * v⁻¹) * (w * v) := by group
            _ = (w * v)⁻¹ * (w * (v * l * v⁻¹) * w⁻¹) * (w * v) := by rw [e4]
            _ = l := by group
        calc v * w = (w * v) * ((w * v)⁻¹ * (v * w)) := by group
          _ = w * v := by rw [h0, mul_one]
      have hyC : y * w⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 := hw (w⁻¹ * l * w) (L.mul_mem (L.mul_mem (L.inv_mem hwL) hl) hwL)
        have h2 : w * (w⁻¹ * l * w) * w⁻¹ = l := by group
        rw [h2] at h1
        calc l * (y * w⁻¹) = y * (w⁻¹ * l * w) * y⁻¹ * (y * w⁻¹) := by rw [h1]
          _ = y * w⁻¹ * l := by group
      have hvz : v * (y * w⁻¹) = (y * w⁻¹) * v :=
        (Subgroup.mem_centralizer_iff.mp hyC v hvL)
      calc v * y = v * ((y * w⁻¹) * w) := by group
        _ = (y * w⁻¹) * (v * w) := by rw [← mul_assoc, hvz, mul_assoc]
        _ = (y * w⁻¹) * (w * v) := by rw [hvw]
        _ = y * v := by group
    have hvAm : v ∈ A := hAmax v hv3 hvA
    refine ⟨v, ⟨hvAm, hvL⟩, ?_⟩
    rw [← hCA]
    exact ⟨A.mul_mem hxA (A.inv_mem hvAm), hzC⟩
  have hsup : (A ⊓ L) ⊔ Subgroup.zpowers a = A := by
    refine le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)) fun x hxA => ?_
    obtain ⟨v, hv, hz⟩ := hdecomp x hxA
    have e : x = (x * v⁻¹) * v := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hv)
  refine ⟨hsup, ?_⟩
  have hc : ∀ u ∈ A ⊓ L, ∀ w ∈ Subgroup.zpowers a, u * w = w * u := fun u hu w hw =>
    hcomm u hu.1 w (Subgroup.zpowers_le.mpr haA hw)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
  have hinf : A ⊓ L ⊓ Subgroup.zpowers a = ⊥ := by
    rw [inf_comm]
    exact Sec13.zpowers_inf_eq_bot (by rw [← ha3]; exact pow_orderOf_eq_one a)
      (fun h => haL h.2)
  rw [hsup, h27, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, ha3] at hcard
  omega

theorem false_of_inner_of_automizer {A L B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27)
    (hAmax : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {a c : G} (hcA : c ∈ A)
    (hCA : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a) (ha3 : orderOf a = 3)
    (hca : c ∉ Subgroup.zpowers a)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hcB : c ∉ B) (haL : a ∉ L) (hcen : Subgroup.center ↥L = ⊥)
    (hinn : ∀ σ : MulAut ↥L, orderOf σ = 3 → σ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range)
    (hV : ∀ V : Subgroup ↥L, CFSG.Assembly.IsElemAbelian 3 V → Nat.card V = 9 →
      ∃ n ∈ Subgroup.normalizer (V : Set ↥L),
        (∃ x ∈ V, n ^ 2 * x * (n ^ 2)⁻¹ ≠ x) ∧ (∃ x ∈ V, n ^ 3 * x * (n ^ 3)⁻¹ ≠ x)) :
    False := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have haA : a ∈ A := (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have haC : a ∈ Subgroup.centralizer (L : Set G) :=
    (hCA ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    omega
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  obtain ⟨hsup, h9⟩ := card_inf_eq_nine_of_inner hA h27 hAmax hAL hCA ha3 haL hcen hinn
  set V : Subgroup ↥L := (A ⊓ L).subgroupOf L with hVdef
  have hV9 : Nat.card V = 9 := by
    rw [hVdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
      h9]
  have hVe : CFSG.Assembly.IsElemAbelian 3 V := by
    refine ⟨⟨⟨fun u v => Subtype.ext (Subtype.ext ?_)⟩⟩, fun u hu => Subtype.ext ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp u.2).1 _ (Subgroup.mem_subgroupOf.mp v.2).1
    · simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hu).1
  obtain ⟨n, hnN, ⟨x, hxV, hx2⟩, ⟨y, hyV, hy3⟩⟩ := hV V hVe hV9
  have hconj : ∀ m : ↥L, m ∈ Subgroup.normalizer (V : Set ↥L) → ∀ z ∈ A,
      (m : G) * z * (m : G)⁻¹ ∈ A := by
    intro m hm z hz
    have hzs : z ∈ (A ⊓ L) ⊔ Subgroup.zpowers a := by rw [hsup]; exact hz
    have hc : ∀ u ∈ A ⊓ L, ∀ w ∈ Subgroup.zpowers a, u * w = w * u := fun u hu w hw =>
      hcomm u hu.1 w (Subgroup.zpowers_le.mpr haA hw)
    obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
    have hz' : z ∈ (((A ⊓ L) ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := hzs
    rw [hset] at hz'
    obtain ⟨u, hu, w, hw, rfl⟩ := hz'
    have hmw : (m : G) * w = w * m := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp haC m m.2) k).eq
    have hmu : (m : G) * u * (m : G)⁻¹ ∈ A := by
      have huV : (⟨u, hu.2⟩ : ↥L) ∈ V := Subgroup.mem_subgroupOf.mpr hu
      have h1 := (Subgroup.mem_normalizer_iff.mp hm _).mp huV
      simpa using (Subgroup.mem_subgroupOf.mp h1).1
    have e : (m : G) * (u * w) * (m : G)⁻¹ = ((m : G) * u * (m : G)⁻¹) * w := by
      calc (m : G) * (u * w) * (m : G)⁻¹ = ((m : G) * u * (m : G)⁻¹) * ((m : G) * w * (m : G)⁻¹) :=
            by group
        _ = ((m : G) * u * (m : G)⁻¹) * w := by rw [hmw, mul_inv_cancel_right]
    rw [e]
    exact A.mul_mem hmu (Subgroup.zpowers_le.mpr haA hw)
  have hnA : (n : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hconj n hnN z, fun h => ?_⟩
    have h1 := hconj n⁻¹ (Subgroup.inv_mem _ hnN) _ h
    have e : ((n⁻¹ : ↥L) : G) * ((n : G) * z * (n : G)⁻¹) * ((n⁻¹ : ↥L) : G)⁻¹ = z := by
      simp only [InvMemClass.coe_inv, inv_inv]
      group
    rwa [e] at h1
  set σ := A.normalizerMonoidHom ⟨(n : G), hnA⟩ with hσdef
  have hσpow : ∀ k : ℕ, ∀ z : A, ((σ ^ k) z : G) = (n : G) ^ k * z * ((n : G) ^ k)⁻¹ := by
    intro k z
    rw [hσdef, ← map_pow, normalizerMonoidHom_apply_coe]
    rfl
  have hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩ := by
    apply Subtype.ext
    rw [hσdef, normalizerMonoidHom_apply_coe]
    show (n : G) * a * (n : G)⁻¹ = a
    rw [Subgroup.mem_centralizer_iff.mp haC n n.2, mul_inv_cancel_right]
  have hσc : ((σ ⟨c, hcA⟩ : A) : G) ∈ Subgroup.zpowers c := by
    rw [hσdef, normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hW hnA) c).mp (Subgroup.mem_zpowers c)
  have hσB : ∀ z : A, (z : G) ∈ B → ((σ z : A) : G) ∈ B := fun z hz => by
    rw [hσdef, normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hWB hnA) z).mp hz
  have hσL : ∀ z : A, ((σ z : A) : G) * (z : G)⁻¹ ∈ L := fun z => by
    rw [hσdef, normalizerMonoidHom_apply_coe]
    have hz : (z : G) * (n : G)⁻¹ * (z : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL z.2) _).mp (L.inv_mem n.2)
    have e : (n : G) * (z : G) * (n : G)⁻¹ * (z : G)⁻¹ =
        (n : G) * ((z : G) * (n : G)⁻¹ * (z : G)⁻¹) := by group
    rw [e]
    exact L.mul_mem n.2 hz
  have hor := sq_eq_one_or_pow_three_eq_one_of_le hA h27 haA hcA ha1 hc1 hca hBA hB9 hcB haL hσa
    hσc hσB hσL
  have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.mp hxV).1
  have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hyV).1
  rcases hor with h | h
  · apply hx2
    apply Subtype.ext
    have h1 := hσpow 2 ⟨x, hxA⟩
    rw [h, MulAut.one_apply] at h1
    simpa using h1.symm
  · apply hy3
    apply Subtype.ext
    have h1 := hσpow 3 ⟨y, hyA⟩
    rw [h, MulAut.one_apply] at h1
    simpa using h1.symm

end CFSG.RankThree.PartTwo.Sec4.Proof430
