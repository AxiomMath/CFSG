module

public import CFSG.GroupTheory.WreathThreeIso
public import CFSG.LargeExtraspecial.AS35QThXa
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
public import CFSG.GH74.M12.HypGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped IsMulCommutative Pointwise

namespace W16GTwoCB

private noncomputable def w16g_zmod3Pow {G : Type*} [Group G] {y : G} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) : Multiplicative (ZMod 3) →* Subgroup.zpowers y where
  toFun q := ⟨y ^ q.toAdd.val, (Subgroup.zpowers y).pow_mem (Subgroup.mem_zpowers y) _⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' q r := by
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hval : (q * r).toAdd.val = (q.toAdd.val + r.toAdd.val) % 3 := by
      change (q.toAdd + r.toAdd).val = _
      rw [ZMod.val_add]
    have hpow : y ^ ((q.toAdd.val + r.toAdd.val) % 3) =
        y ^ (q.toAdd.val + r.toAdd.val) := by
      have := pow_mod_orderOf y (q.toAdd.val + r.toAdd.val)
      rwa [hord] at this
    apply Subtype.ext
    show y ^ (q * r).toAdd.val = y ^ q.toAdd.val * y ^ r.toAdd.val
    rw [hval, hpow, pow_add]

@[simp] private theorem w16g_zmod3Pow_apply {G : Type*} [Group G] {y : G} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (q : Multiplicative (ZMod 3)) :
    ((w16g_zmod3Pow hy3 hy1) q : G) = y ^ q.toAdd.val := rfl

@[simp] private theorem w16g_zmod3Pow_ofAdd_one {G : Type*} [Group G] {y : G}
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    w16g_zmod3Pow hy3 hy1 (Multiplicative.ofAdd 1) = ⟨y, Subgroup.mem_zpowers y⟩ := by
  apply Subtype.ext
  rw [w16g_zmod3Pow_apply]
  simp [ZMod.val_one]

private theorem w16g_zmod3Pow_mem {G : Type*} [Group G] {E : Subgroup G} {y : G} (hyE : y ∈ E)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (q : Multiplicative (ZMod 3)) :
    ((Subgroup.zpowers y).subtype.comp (w16g_zmod3Pow hy3 hy1)) q ∈ E := by
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, w16g_zmod3Pow_apply]
  exact E.pow_mem hyE _

theorem w16g_nonempty_mulEquiv_zwr_one {X : Type} [Group X] (hX : IsZ3WrZ3 X) :
    Nonempty (X ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, z, b, hz3, hcomm, hb3, hconj, hgen⟩ := hX
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h01 : (0 : Fin 3) + 1 = 1 := by decide
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have hm01 : (0 : Fin 3) - 1 = 2 := by decide
  have hm11 : (1 : Fin 3) - 1 = 0 := by decide
  have hm21 : (2 : Fin 3) - 1 = 1 := by decide
  have hz0 : z 0 ≠ 1 := by
    intro hzi
    have h1 : z 1 = 1 := by
      have h := hconj 0
      rw [h01] at h
      rw [← h, hzi]
      group
    have hh : b * z 1 * b⁻¹ = z 2 := by
      have h := hconj 1
      rw [h11] at h
      exact h
    have h2 : z 2 = 1 := by
      rw [← hh, h1]
      group
    have hall : ∀ j, z j = 1 := by
      intro j
      fin_cases j
      · exact hzi
      · exact h1
      · exact h2
    have htop : (⊤ : Subgroup X) = Subgroup.zpowers b := by
      rw [← hgen]
      apply le_antisymm
      · refine (Subgroup.closure_le (Subgroup.zpowers b)).mpr ?_
        intro x hx
        rcases hx with ⟨j, rfl⟩ | hx
        · rw [hall j]; exact (Subgroup.zpowers b).one_mem
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]; exact Subgroup.mem_zpowers b
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl))
    have hcardeq : Nat.card X = Nat.card (Subgroup.zpowers b) := by
      rw [← Subgroup.card_top, htop]
    have hb1 : b ≠ 1 := by
      intro hb
      rw [hb, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcardeq
      omega
    have hord : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
    rw [hcard, hord] at hcardeq
    norm_num at hcardeq
  have hzne : ∀ i, z i ≠ 1 := by
    intro i hzi
    apply hz0
    fin_cases i
    · exact hzi
    · have h := hconj 0
      rw [h01] at h
      have hzi1 : z 1 = 1 := hzi
      calc z 0 = b⁻¹ * (b * z 0 * b⁻¹) * b := by group
        _ = b⁻¹ * z 1 * b := by rw [h]
        _ = 1 := by rw [hzi1]; group
    · have h2 : b * z 1 * b⁻¹ = z 2 := by
        have := hconj 1
        rwa [h11] at this
      have hz1 : z 1 = 1 := by
        have hzi2 : z 2 = 1 := hzi
        have := h2
        rw [hzi2] at this
        calc z 1 = b⁻¹ * (b * z 1 * b⁻¹) * b := by group
          _ = 1 := by rw [this]; group
      have h0 := hconj 0
      rw [h01] at h0
      calc z 0 = b⁻¹ * (b * z 0 * b⁻¹) * b := by group
        _ = b⁻¹ * z 1 * b := by rw [h0]
        _ = 1 := by rw [hz1]; group
  have hzord : ∀ i, orderOf (z i) = 3 := fun i => orderOf_eq_prime (hz3 i) (hzne i)
  let E : Subgroup X := Subgroup.closure (Set.range z)
  have hzE : ∀ i, z i ∈ E := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hEcomm : IsMulCommutative ↥E := by
    apply Subgroup.isMulCommutative_closure
    intro a ha c hc _
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hc
    exact hcomm i j
  let emb : ∀ i, Multiplicative (ZMod 3) →* ↥E := fun i =>
    ((Subgroup.zpowers (z i)).subtype.comp (w16g_zmod3Pow (hz3 i) (hzne i))).codRestrict E
      (fun q => w16g_zmod3Pow_mem (hzE i) (hz3 i) (hzne i) q)
  let φ : (Fin 3 → Multiplicative (ZMod 3)) →* ↥E :=
    { toFun := fun v => ∏ i, emb i (v i)
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [Pi.mul_apply, map_mul]
        exact Finset.prod_mul_distrib }
  have emb_one : ∀ i, emb i (Multiplicative.ofAdd 1) = ⟨z i, hzE i⟩ := by
    intro i
    apply Subtype.ext
    simp only [emb]
    rw [MonoidHom.codRestrict_apply]
    change ((Subgroup.zpowers (z i)).subtype.comp (w16g_zmod3Pow (hz3 i) (hzne i)))
      (Multiplicative.ofAdd 1) = z i
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, w16g_zmod3Pow_ofAdd_one]
  have hφsurj : Function.Surjective φ := by
    have hgenmem : ∀ i, (⟨z i, hzE i⟩ : ↥E) ∈ φ.range := by
      intro i
      refine ⟨fun j => if j = i then Multiplicative.ofAdd 1 else 1, ?_⟩
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Fin.prod_univ_three]
      apply Subtype.ext
      fin_cases i <;> simp [emb_one]
    have hpre : ((↑) : ↥E → X) ⁻¹' Set.range z =
        Set.range (fun i => (⟨z i, hzE i⟩ : ↥E)) := by
      ext y
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    have htopcl : Subgroup.closure (Set.range (fun i => (⟨z i, hzE i⟩ : ↥E))) = ⊤ := by
      rw [← hpre]
      exact Subgroup.closure_closure_coe_preimage
    have hclosure : (⊤ : Subgroup ↥E) ≤ φ.range := by
      rw [← htopcl]
      refine (Subgroup.closure_le φ.range).mpr ?_
      rintro y ⟨i, rfl⟩
      exact hgenmem i
    exact MonoidHom.range_eq_top.mp (le_antisymm le_top hclosure)
  have hEcard_le : Nat.card ↥E ≤ 27 := by
    have h := Nat.card_le_card_of_surjective φ hφsurj
    calc Nat.card ↥E ≤ Nat.card (Fin 3 → Multiplicative (ZMod 3)) := h
      _ = 27 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_pi]
        simp [ZMod.card]
  have hXsup : E ⊔ Subgroup.zpowers b = ⊤ := by
    change Subgroup.closure (Set.range z) ⊔ Subgroup.zpowers b = ⊤
    rw [← hgen, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  have hbne : b ≠ 1 := by
    intro hb1
    rw [hb1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hXsup
    have hc : Nat.card X = Nat.card ↥E := by rw [hXsup, Subgroup.card_top]
    rw [hcard] at hc
    omega
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hbne
  have hzpbcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hbord]
  have hbE : b ∉ E := by
    intro hbEl
    have hsup : E ⊔ Subgroup.zpowers b = E :=
      sup_eq_left.mpr (Subgroup.zpowers_le.mpr hbEl)
    rw [hsup] at hXsup
    have hc : Nat.card X = Nat.card ↥E := by rw [hXsup, Subgroup.card_top]
    rw [hcard] at hc
    omega
  have hdisj : Disjoint E (Subgroup.zpowers b) := by
    haveI : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hzpbcard]; norm_num⟩
    rw [disjoint_iff]
    have hsub := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((E ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases hsub with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' : (E ⊓ Subgroup.zpowers b) ⊓ Subgroup.zpowers b = ⊥ := h.eq_bot
      rwa [inf_eq_left.mpr inf_le_right] at h'
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact absurd (h (Subgroup.mem_zpowers b)).1 hbE
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq]
    have hEeq : E = Subgroup.closure (Set.range z) := rfl
    rw [hEeq, MonoidHom.map_closure]
    change Subgroup.closure (((MulAut.conj b).toMonoidHom : X → X) '' Set.range z) =
      Subgroup.closure (Set.range z)
    have himg : ((MulAut.conj b).toMonoidHom : X → X) '' Set.range z = Set.range z := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        refine ⟨i + 1, ?_⟩
        show z (i + 1) = b * z i * b⁻¹
        exact (hconj i).symm
      · rintro ⟨i, rfl⟩
        refine ⟨z (i - 1), ⟨i - 1, rfl⟩, ?_⟩
        show b * z (i - 1) * b⁻¹ = z i
        have h := hconj (i - 1)
        have hi : (i - 1) + 1 = i := by
          apply Fin.ext
          simp [Fin.add_def]
        rwa [hi] at h
    rw [himg]
  have hEcard : Nat.card ↥E = 27 := by
    have hsupcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
      (Subgroup.zpowers b) hnorm hdisj
    rw [hXsup, Subgroup.card_top, hzpbcard, hcard] at hsupcard
    omega
  let S : Subgroup X := Subgroup.zpowers (z 0)
  have hbase : CFSG.GroupTheory.WreathThree.base S b = E := by
    change S ⊔ S.map (MulAut.conj b).toMonoidHom ⊔
      S.map (MulAut.conj (b ^ 2)).toMonoidHom = Subgroup.closure (Set.range z)
    have hSb : S.map (MulAut.conj b).toMonoidHom = Subgroup.zpowers (z 1) := by
      change (Subgroup.zpowers (z 0)).map (MulAut.conj b).toMonoidHom = Subgroup.zpowers (z 1)
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (b * z 0 * b⁻¹) = Subgroup.zpowers (z 1)
      have h : b * z 0 * b⁻¹ = z 1 := by
        have := hconj 0
        rwa [h01] at this
      rw [h]
    have hSb2 : S.map (MulAut.conj (b ^ 2)).toMonoidHom = Subgroup.zpowers (z 2) := by
      change (Subgroup.zpowers (z 0)).map (MulAut.conj (b ^ 2)).toMonoidHom =
        Subgroup.zpowers (z 2)
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (b ^ 2 * z 0 * (b ^ 2)⁻¹) = Subgroup.zpowers (z 2)
      have hb2 : b ^ 2 * z 0 * (b ^ 2)⁻¹ = z 2 := by
        calc b ^ 2 * z 0 * (b ^ 2)⁻¹ = b * (b * z 0 * b⁻¹) * b⁻¹ := by
              rw [pow_two]; group
          _ = b * z 1 * b⁻¹ := by rw [hconj 0, h01]
          _ = z 2 := by simpa [h11] using hconj 1
      rw [hb2]
    rw [hSb, hSb2]
    have hrange : Set.range z = ({z 0, z 1, z 2} : Set X) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    rw [hrange]
    have hset : ({z 0, z 1, z 2} : Set X) = {z 0} ∪ {z 1} ∪ {z 2} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [hset, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure (z 0), ← Subgroup.zpowers_eq_closure (z 1),
      ← Subgroup.zpowers_eq_closure (z 2)]
  have hcommBase : ∀ a ∈ CFSG.GroupTheory.WreathThree.base S b,
      ∀ c ∈ CFSG.GroupTheory.WreathThree.base S b, a * c = c * a := by
    intro a ha c hc
    rw [hbase] at ha hc
    exact congrArg Subtype.val (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  have hScard : Nat.card S = 3 := by
    change Nat.card ↥(Subgroup.zpowers (z 0)) = 3
    rw [Nat.card_zpowers, hzord 0]
  have hw : CFSG.GroupTheory.WreathThree.IsWreathThree S b := by
    refine ⟨?_, inferInstance, ?_, hcommBase, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 1) (by rw [hScard]; norm_num)
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hScard
      omega
    · rw [hbase, hEcard, hScard]; norm_num
    · rw [hb3]; exact (CFSG.GroupTheory.WreathThree.base S b).one_mem
  obtain ⟨n, hn1, hSn, ⟨e⟩⟩ :=
    CFSG.GroupTheory.WreathThree.exists_mulEquiv_regularWreathProduct hw hb3
  have hn : n = 1 := by
    have h3 : (3 : ℕ) ^ n = 3 ^ 1 := by rw [← hSn, hScard]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have htop : CFSG.GroupTheory.WreathThree.base S b ⊔ Subgroup.zpowers b = ⊤ := by
    rw [hbase]; exact hXsup
  rw [htop] at e
  rw [hn] at e
  exact ⟨(Subgroup.topEquiv (G := X)).symm.trans e⟩

open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

private abbrev w16g_ZWr1 : Type := ZWr 1

private def w16g_b0 : w16g_ZWr1 := el 1 0 0 0 1

private def w16g_D : Subgroup w16g_ZWr1 where
  carrier := {w | ∃ a b c : ZMod 3, a + b + c = 0 ∧ w = el 1 a b c 0}
  one_mem' := ⟨0, 0, 0, by norm_num, by rw [el_zero_zero]⟩
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, b, c, hs, hx⟩
    rcases hy with ⟨a', b', c', hs', hy⟩
    refine ⟨a + a', b + b', c + c', ?_, ?_⟩
    · have h : a + a' + (b + b') + (c + c') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [hx, hy, el_mul_zero]
  inv_mem' := by
    intro x hx
    rcases hx with ⟨a, b, c, hs, hx⟩
    refine ⟨-a, -b, -c, ?_, ?_⟩
    · have h : -a + -b + -c = -(a + b + c) := by abel
      rw [h, hs]
      exact neg_zero
    · have hmul : el 1 (-a) (-b) (-c) 0 * el 1 a b c 0 = 1 := by
        rw [el_mul_zero]
        rw [show -a + a = 0 by abel, show -b + b = 0 by abel,
          show -c + c = 0 by abel, el_zero_zero]
      rw [hx]
      exact inv_eq_of_mul_eq_one_left hmul

private theorem w16g_el_cube_zero (a b c : ZMod 3) : (el 1 a b c 0) ^ 3 = 1 := by
  have h3 : (el 1 a b c 0) ^ 3 = el 1 a b c 0 * el 1 a b c 0 * el 1 a b c 0 := by
    simp [pow_succ, pow_two]
  rw [h3, el_mul_zero, el_mul_zero]
  have h3a : a + a + a = 0 := by
    have h : (3 : ZMod 3) = 0 := by decide
    rw [show a + a + a = a * 3 by ring, h, mul_zero]
  have h3b : b + b + b = 0 := by
    have h : (3 : ZMod 3) = 0 := by decide
    rw [show b + b + b = b * 3 by ring, h, mul_zero]
  have h3c : c + c + c = 0 := by
    have h : (3 : ZMod 3) = 0 := by decide
    rw [show c + c + c = c * 3 by ring, h, mul_zero]
  rw [h3a, h3b, h3c, el_zero_zero]

private theorem w16g_el_cube_one (a b c : ZMod 3) :
    (el 1 a b c 1) ^ 3 = el 1 (a + b + c) (a + b + c) (a + b + c) 0 := by
  have h3 : (el 1 a b c 1) ^ 3 = el 1 a b c 1 * el 1 a b c 1 * el 1 a b c 1 := by
    simp [pow_succ, pow_two]
  rw [h3]
  have hsq : el 1 a b c 1 * el 1 a b c 1 = el 1 (a + c) (b + a) (c + b) 2 := by
    rw [el_mul_one, show (1 : ZMod 3) + 1 = 2 by decide]
  rw [hsq]
  have hcb : el 1 (a + c) (b + a) (c + b) 2 * el 1 a b c 1 =
      el 1 (a + b + c) (a + b + c) (a + b + c) 0 := by
    rw [el_mul_two, show (2 : ZMod 3) + 1 = 0 by decide]
    rw [show (a + c) + b = a + b + c by abel,
      show (b + a) + c = a + b + c by abel,
      show (c + b) + a = a + b + c by abel]
  rw [hcb]

private theorem w16g_el_cube_two (a b c : ZMod 3) :
    (el 1 a b c 2) ^ 3 = el 1 (a + b + c) (a + b + c) (a + b + c) 0 := by
  have h3 : (el 1 a b c 2) ^ 3 = el 1 a b c 2 * el 1 a b c 2 * el 1 a b c 2 := by
    simp [pow_succ, pow_two]
  rw [h3]
  have hsq : el 1 a b c 2 * el 1 a b c 2 = el 1 (a + b) (b + c) (c + a) 1 := by
    rw [el_mul_two, show (2 : ZMod 3) + 2 = 1 by decide]
  rw [hsq]
  have hcb : el 1 (a + b) (b + c) (c + a) 1 * el 1 a b c 2 =
      el 1 (a + b + c) (a + b + c) (a + b + c) 0 := by
    rw [el_mul_one, show (1 : ZMod 3) + 2 = 0 by decide]
    rw [show (a + b) + c = a + b + c by abel,
      show (b + c) + a = a + b + c by abel,
      show (c + a) + b = a + b + c by abel]
  rw [hcb]

private def w16g_hfun : ZMod 3 × ZMod 3 → w16g_D := fun p =>
  ⟨el 1 p.1 p.2 (-(p.1 + p.2)) 0,
    ⟨p.1, p.2, -(p.1 + p.2), by abel, rfl⟩⟩

private theorem w16g_card_D : Nat.card w16g_D = 9 := by
  have hinj : Function.Injective w16g_hfun := by
    intro p q h
    have h'2 : (w16g_hfun p : w16g_ZWr1) = (w16g_hfun q : w16g_ZWr1) :=
      Subtype.ext_iff.mp h
    have h'3 : el 1 p.1 p.2 (-(p.1 + p.2)) 0 =
        el 1 q.1 q.2 (-(q.1 + q.2)) 0 := by
      simpa [w16g_hfun] using h'2
    have hh : (fun p : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 =>
        el 1 p.1 p.2.1 p.2.2.1 p.2.2.2)
        (p.1, p.2, -(p.1 + p.2), (0 : ZMod 3)) =
        (fun p : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 =>
        el 1 p.1 p.2.1 p.2.2.1 p.2.2.2)
        (q.1, q.2, -(q.1 + q.2), (0 : ZMod 3)) := h'3
    have h'' := el_injective (n := 1) hh
    exact Prod.ext
      (congrArg (fun x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 => x.1) h'')
      (congrArg (fun x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 => x.2.1) h'')
  have hsurj : Function.Surjective w16g_hfun := by
    rintro ⟨w, a, b, c, hs, rfl⟩
    refine ⟨(a, b), ?_⟩
    have hs' : c + (a + b) = 0 := by
      rw [show c + (a + b) = a + b + c by abel, hs]
    have hc : c = -(a + b) := eq_neg_of_add_eq_zero_left hs'
    apply Subtype.ext
    simp only [w16g_hfun, Subtype.coe_mk]
    rw [hc]
  have hle : Nat.card (ZMod 3 × ZMod 3) ≤ Nat.card w16g_D :=
    Nat.card_le_card_of_injective w16g_hfun hinj
  have hge : Nat.card w16g_D ≤ Nat.card (ZMod 3 × ZMod 3) :=
    Nat.card_le_card_of_surjective w16g_hfun hsurj
  have hcard : Nat.card (ZMod 3 × ZMod 3) = 9 := by
    rw [Nat.card_prod, Nat.card_zmod]
  omega

private def w16g_Mcarrier : Set w16g_ZWr1 :=
  {w | ∃ a b c e : ZMod 3, a + b + c = 0 ∧ w = el 1 a b c e}

private theorem w16g_mul_mem_Mcarrier {x y : w16g_ZWr1}
    (hx : x ∈ w16g_Mcarrier) (hy : y ∈ w16g_Mcarrier) : x * y ∈ w16g_Mcarrier := by
  rcases hx with ⟨a, b, c, e, hs, hx⟩
  rcases hy with ⟨a', b', c', e', hs', hy⟩
  rw [hx, hy]
  rcases zmod3_cases e with rfl | rfl | rfl <;>
    rcases zmod3_cases e' with rfl | rfl | rfl
  · refine ⟨a + a', b + b', c + c', 0, ?_, by rw [el_mul_zero]⟩
    have h : a + a' + (b + b') + (c + c') = (a + b + c) + (a' + b' + c') := by abel
    rw [h, hs, hs', add_zero]
  · refine ⟨a + a', b + b', c + c', 1, ?_, ?_⟩
    · have h : a + a' + (b + b') + (c + c') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_zero]
  · refine ⟨a + a', b + b', c + c', 2, ?_, ?_⟩
    · have h : a + a' + (b + b') + (c + c') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_zero]
  · refine ⟨a + c', b + a', c + b', 1, ?_, ?_⟩
    · have h : a + c' + (b + a') + (c + b') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_one, show (1 : ZMod 3) + 0 = 1 by decide]
  · refine ⟨a + c', b + a', c + b', 2, ?_, ?_⟩
    · have h : a + c' + (b + a') + (c + b') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_one, show (1 : ZMod 3) + 1 = 2 by decide]
  · refine ⟨a + c', b + a', c + b', 0, ?_, ?_⟩
    · have h : a + c' + (b + a') + (c + b') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_one, show (1 : ZMod 3) + 2 = 0 by decide]
  · refine ⟨a + b', b + c', c + a', 2, ?_, ?_⟩
    · have h : a + b' + (b + c') + (c + a') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_two, show (2 : ZMod 3) + 0 = 2 by decide]
  · refine ⟨a + b', b + c', c + a', 0, ?_, ?_⟩
    · have h : a + b' + (b + c') + (c + a') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_two, show (2 : ZMod 3) + 1 = 0 by decide]
  · refine ⟨a + b', b + c', c + a', 1, ?_, ?_⟩
    · have h : a + b' + (b + c') + (c + a') = (a + b + c) + (a' + b' + c') := by abel
      rw [h, hs, hs', add_zero]
    · rw [el_mul_two, show (2 : ZMod 3) + 2 = 1 by decide]

private theorem w16g_cube_eq_one_of_mem_Mcarrier {x : w16g_ZWr1}
    (hx : x ∈ w16g_Mcarrier) : x ^ 3 = 1 := by
  rcases hx with ⟨a, b, c, e, hs, rfl⟩
  rcases zmod3_cases e with rfl | rfl | rfl
  · exact w16g_el_cube_zero a b c
  · rw [w16g_el_cube_one]
    have h : el 1 (a + b + c) (a + b + c) (a + b + c) 0 = 1 := by
      rw [hs, el_zero_zero]
    exact h
  · rw [w16g_el_cube_two]
    have h : el 1 (a + b + c) (a + b + c) (a + b + c) 0 = 1 := by
      rw [hs, el_zero_zero]
    exact h

private theorem w16g_inv_mem_Mcarrier {x : w16g_ZWr1}
    (hx : x ∈ w16g_Mcarrier) : x⁻¹ ∈ w16g_Mcarrier := by
  have hx3 : x ^ 3 = 1 := w16g_cube_eq_one_of_mem_Mcarrier hx
  have hsq : x * x ∈ w16g_Mcarrier := w16g_mul_mem_Mcarrier hx hx
  have h : x * (x * x) = 1 := by
    rw [← pow_two, ← pow_succ']
    exact hx3
  rw [inv_eq_of_mul_eq_one_right h]
  exact hsq

private def w16g_M : Subgroup w16g_ZWr1 where
  carrier := w16g_Mcarrier
  one_mem' := ⟨0, 0, 0, 0, by norm_num, by rw [el_zero_zero]⟩
  mul_mem' := w16g_mul_mem_Mcarrier
  inv_mem' := w16g_inv_mem_Mcarrier

private theorem w16g_mem_M {w : w16g_ZWr1} :
    w ∈ w16g_M ↔ ∃ a b c e : ZMod 3, a + b + c = 0 ∧ w = el 1 a b c e := Iff.rfl

private abbrev w16g_B : Subgroup w16g_ZWr1 := base 1

private theorem w16g_b0_cube : w16g_b0 ^ 3 = 1 := by
  have h := w16g_el_cube_one 0 0 0
  simpa [w16g_b0, el_zero_zero] using h

private def w16g_kfun : (ZMod 3 × ZMod 3) × ZMod 3 → w16g_M := fun p =>
  ⟨el 1 p.1.1 p.1.2 (-(p.1.1 + p.1.2)) p.2,
    ⟨p.1.1, p.1.2, -(p.1.1 + p.1.2), p.2, by abel, rfl⟩⟩

private theorem w16g_card_M : Nat.card w16g_M = 27 := by
  have hinj : Function.Injective w16g_kfun := by
    intro p q h
    have h'2 : (w16g_kfun p : w16g_ZWr1) = (w16g_kfun q : w16g_ZWr1) :=
      Subtype.ext_iff.mp h
    have h'3 : el 1 p.1.1 p.1.2 (-(p.1.1 + p.1.2)) p.2 =
        el 1 q.1.1 q.1.2 (-(q.1.1 + q.1.2)) q.2 := by
      simpa [w16g_kfun] using h'2
    have ha : p.1.1 = q.1.1 := by
      have h := congrArg (fun w : w16g_ZWr1 => w.left (Multiplicative.ofAdd 0)) h'3
      rw [el_left_zero] at h
      exact Multiplicative.ofAdd.injective h
    have hb : p.1.2 = q.1.2 := by
      have h := congrArg (fun w : w16g_ZWr1 => w.left (Multiplicative.ofAdd 1)) h'3
      rw [el_left_one] at h
      exact Multiplicative.ofAdd.injective h
    have he : p.2 = q.2 := by
      have h := congrArg (fun w : w16g_ZWr1 => w.right) h'3
      rw [el_right] at h
      exact Multiplicative.ofAdd.injective h
    exact Prod.ext (Prod.ext ha hb) he
  have hsurj : Function.Surjective w16g_kfun := by
    rintro ⟨w, a, b, c, e, hs, rfl⟩
    refine ⟨((a, b), e), ?_⟩
    have hs' : c + (a + b) = 0 := by
      rw [show c + (a + b) = a + b + c by abel, hs]
    have hc : c = -(a + b) := eq_neg_of_add_eq_zero_left hs'
    apply Subtype.ext
    simp only [w16g_kfun, Subtype.coe_mk]
    rw [hc]
  have hle : Nat.card ((ZMod 3 × ZMod 3) × ZMod 3) ≤ Nat.card w16g_M :=
    Nat.card_le_card_of_injective w16g_kfun hinj
  have hge : Nat.card w16g_M ≤ Nat.card ((ZMod 3 × ZMod 3) × ZMod 3) :=
    Nat.card_le_card_of_surjective w16g_kfun hsurj
  have hcard : Nat.card ((ZMod 3 × ZMod 3) × ZMod 3) = 27 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  omega

private theorem w16g_D_le_M : w16g_D ≤ w16g_M := by
  rintro w ⟨a, b, c, hs, rfl⟩
  exact ⟨a, b, c, 0, hs, rfl⟩

private theorem w16g_b0_mem_M : w16g_b0 ∈ w16g_M :=
  ⟨0, 0, 0, 1, by norm_num, rfl⟩

private theorem w16g_M_le_sup : w16g_M ≤ w16g_D ⊔ Subgroup.zpowers w16g_b0 := by
  rintro w ⟨a, b, c, e, hs, rfl⟩
  have hd : el 1 a b c 0 ∈ w16g_D := ⟨a, b, c, hs, rfl⟩
  have hb0sq : w16g_b0 ^ 2 = el 1 0 0 0 2 := by
    rw [pow_two, w16g_b0, el_mul_one, show (1 : ZMod 3) + 1 = 2 by decide]
    congr 2 <;> abel
  have hpow : el 1 0 0 0 e ∈ Subgroup.zpowers w16g_b0 := by
    rcases zmod3_cases e with rfl | rfl | rfl
    · rw [el_zero_zero]
      exact (Subgroup.zpowers w16g_b0).one_mem
    · rw [show el 1 0 0 0 1 = w16g_b0 from rfl]
      exact Subgroup.mem_zpowers w16g_b0
    · rw [← hb0sq]
      exact (Subgroup.zpowers w16g_b0).pow_mem (Subgroup.mem_zpowers w16g_b0) 2
  have hmul : el 1 a b c e = el 1 a b c 0 * el 1 0 0 0 e := by
    rcases zmod3_cases e with rfl | rfl | rfl
    · rw [el_zero_zero, mul_one]
    · rw [show el 1 a b c 0 * el 1 0 0 0 1 = el 1 a b c 1 by
        rw [el_mul_zero]
        rw [show a + 0 = a by abel, show b + 0 = b by abel, show c + 0 = c by abel]]
    · rw [show el 1 a b c 0 * el 1 0 0 0 2 = el 1 a b c 2 by
        rw [el_mul_zero]
        rw [show a + 0 = a by abel, show b + 0 = b by abel, show c + 0 = c by abel]]
  rw [hmul]
  exact Subgroup.mul_mem_sup hd hpow

private theorem w16g_M_eq_sup : w16g_M = w16g_D ⊔ Subgroup.zpowers w16g_b0 := by
  apply le_antisymm w16g_M_le_sup
  exact sup_le w16g_D_le_M (Subgroup.zpowers_le.mpr w16g_b0_mem_M)

private theorem w16g_M_noncomm : ∃ x y : w16g_M, x * y ≠ y * x := by
  refine ⟨⟨w16g_b0, w16g_b0_mem_M⟩,
    ⟨el 1 1 (-1) 0 0, ⟨1, -1, 0, 0, by abel, rfl⟩⟩, ?_⟩
  intro h
  have h' := congrArg (fun z : w16g_M => (z : w16g_ZWr1)) h
  have hb0d : (w16g_b0 : w16g_ZWr1) * el 1 1 (-1) 0 0 = el 1 0 1 (-1) 1 := by
    rw [w16g_b0, el_mul_one, show (1 : ZMod 3) + 0 = 1 by decide]
    congr 2 <;> abel
  have hdb0 : el 1 1 (-1) 0 0 * (w16g_b0 : w16g_ZWr1) = el 1 1 (-1) 0 1 := by
    rw [w16g_b0, el_mul_zero]
    congr 2 <;> abel
  change (w16g_b0 : w16g_ZWr1) * el 1 1 (-1) 0 0 =
    el 1 1 (-1) 0 0 * (w16g_b0 : w16g_ZWr1) at h'
  rw [hb0d, hdb0] at h'
  have hcoord := congrArg (fun w : w16g_ZWr1 => w.left (Multiplicative.ofAdd 0)) h'
  rw [el_left_zero, el_left_zero] at hcoord
  exact (by decide : (0 : ZMod 3) ≠ 1) (Multiplicative.ofAdd.injective hcoord)

private theorem w16g_M_isPOnePlusTwo : IsPOnePlusTwo 3 ↥w16g_M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥w16g_M = 27 := w16g_card_M
  haveI : Finite ↥w16g_M := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hexp : ∀ x : ↥w16g_M, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    exact w16g_cube_eq_one_of_mem_Mcarrier x.2
  have hcenter : Nat.card (Subgroup.center ↥w16g_M) = 3 :=
    CFSG.LargeExtraspecial.AS35QTh.card_center_eq_three hcard w16g_M_noncomm
  have hqcard : Nat.card (↥w16g_M ⧸ Subgroup.center ↥w16g_M) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥w16g_M)
    rw [hcard, hcenter] at h
    omega
  refine ⟨⟨hcenter, ?_, ?_⟩, by rw [hcard]; norm_num, hexp⟩
  · refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        (G := ↥w16g_M ⧸ Subgroup.center ↥w16g_M) (by rw [hqcard]; norm_num)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
      intro x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_pow, hexp m]
      exact QuotientGroup.mk_one _
  · rw [QuotientGroup.nontrivial_iff]
    intro htop
    obtain ⟨x, y, hxy⟩ := w16g_M_noncomm
    exact hxy ((Subgroup.center_eq_top_iff.mp htop).is_comm.comm x y)

private theorem w16g_sum_coord_eq_zero_of_cube {w : w16g_ZWr1} (hw3 : w ^ 3 = 1)
    (hw : w ∉ w16g_B) :
    Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0)) +
      Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1)) +
      Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2)) = 0 := by
  have he : Multiplicative.toAdd w.right ≠ 0 := by
    intro h
    apply hw
    rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker
      from rfl, MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by simpa using h)
  set a := Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))
  set b := Multiplicative.toAdd (w.left (Multiplicative.ofAdd 1))
  set c := Multiplicative.toAdd (w.left (Multiplicative.ofAdd 2))
  set e := Multiplicative.toAdd w.right
  have hw' : w = el 1 a b c e := el_eta w
  rw [hw'] at hw3
  clear_value e
  rcases zmod3_cases e with rfl | rfl | rfl
  · exact absurd rfl he
  · rw [w16g_el_cube_one] at hw3
    have h := congrArg (fun z : w16g_ZWr1 => z.left (Multiplicative.ofAdd 0)) hw3
    rw [el_left_zero] at h
    have h' : Multiplicative.ofAdd (a + b + c) = 1 := by simpa using h
    exact Multiplicative.ofAdd.injective (by simpa using h')
  · rw [w16g_el_cube_two] at hw3
    have h := congrArg (fun z : w16g_ZWr1 => z.left (Multiplicative.ofAdd 0)) hw3
    rw [el_left_zero] at h
    have h' : Multiplicative.ofAdd (a + b + c) = 1 := by simpa using h
    exact Multiplicative.ofAdd.injective (by simpa using h')

private theorem w16g_B_comm {a b : w16g_ZWr1} (ha : a ∈ w16g_B) (hb : b ∈ w16g_B) :
    a * b = b * a := by
  have hra : a.right = 1 := MonoidHom.mem_ker.mp ha
  have hrb : b.right = 1 := MonoidHom.mem_ker.mp hb
  have hae : a = el 1 (Multiplicative.toAdd (a.left (Multiplicative.ofAdd 0)))
      (Multiplicative.toAdd (a.left (Multiplicative.ofAdd 1)))
      (Multiplicative.toAdd (a.left (Multiplicative.ofAdd 2))) 0 := by
    nth_rewrite 1 [el_eta a]
    have : Multiplicative.toAdd a.right = 0 := by rw [hra]; simp
    rw [this]
  have hbe : b = el 1 (Multiplicative.toAdd (b.left (Multiplicative.ofAdd 0)))
      (Multiplicative.toAdd (b.left (Multiplicative.ofAdd 1)))
      (Multiplicative.toAdd (b.left (Multiplicative.ofAdd 2))) 0 := by
    nth_rewrite 1 [el_eta b]
    have : Multiplicative.toAdd b.right = 0 := by rw [hrb]; simp
    rw [this]
  rw [hae, hbe, el_mul_zero, el_mul_zero]
  have hc0 : Multiplicative.toAdd (a.left (Multiplicative.ofAdd 0)) +
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 0)) =
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 0)) +
        Multiplicative.toAdd (a.left (Multiplicative.ofAdd 0)) := add_comm _ _
  have hc1 : Multiplicative.toAdd (a.left (Multiplicative.ofAdd 1)) +
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 1)) =
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 1)) +
        Multiplicative.toAdd (a.left (Multiplicative.ofAdd 1)) := add_comm _ _
  have hc2 : Multiplicative.toAdd (a.left (Multiplicative.ofAdd 2)) +
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 2)) =
      Multiplicative.toAdd (b.left (Multiplicative.ofAdd 2)) +
        Multiplicative.toAdd (a.left (Multiplicative.ofAdd 2)) := add_comm _ _
  rw [hc0, hc1, hc2]

private theorem w16g_inf_B_le_D (Q : Subgroup w16g_ZWr1) (hQ : IsPOnePlusTwo 3 ↥Q) :
    Q ⊓ w16g_B ≤ w16g_D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQext, hQcard, hQexp⟩ := hQ
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hQcomm : ¬ IsMulCommutative ↥Q := by
    intro hcomm
    have htop : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have hnontriv := hQext.quotient_nontrivial
    rw [QuotientGroup.nontrivial_iff, htop] at hnontriv
    exact hnontriv rfl
  have hQnotleB : ¬ Q ≤ w16g_B := by
    intro hQB
    apply hQcomm
    refine IsMulCommutative.of_setLike_mul_comm (s := Q) ?_
    intro x hx y hy
    exact w16g_B_comm (hQB hx) (hQB hy)
  have hex : ∃ x, x ∈ Q ∧ x ∉ w16g_B := by
    by_contra h
    apply hQnotleB
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  obtain ⟨q, hqQ, hqB⟩ := hex
  have hqne : Multiplicative.toAdd q.right ≠ 0 := by
    intro h
    apply hqB
    rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker
      from rfl, MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by simpa using h)
  have hq3 : q ^ 3 = 1 := by simpa using hQexp ⟨q, hqQ⟩
  have hqsum : Multiplicative.toAdd (q.left (Multiplicative.ofAdd 0)) +
      Multiplicative.toAdd (q.left (Multiplicative.ofAdd 1)) +
      Multiplicative.toAdd (q.left (Multiplicative.ofAdd 2)) = 0 :=
    w16g_sum_coord_eq_zero_of_cube hq3 hqB
  intro x hx
  rcases hx with ⟨hxQ, hxB⟩
  have hxr : x.right = 1 := by
    have h : x ∈ (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker := hxB
    exact MonoidHom.mem_ker.mp h
  have hqxB : q * x ∉ w16g_B := by
    intro h
    rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker
      from rfl, MonoidHom.mem_ker] at h
    have hright : (q * x).right = 1 := h
    rw [RegularWreathProduct.mul_right, hxr, mul_one] at hright
    exact hqne (by simpa using congrArg Multiplicative.toAdd hright)
  have hqx3 : (q * x) ^ 3 = 1 := by
    simpa using hQexp ⟨q * x, Q.mul_mem hqQ hxQ⟩
  have hqxsum : Multiplicative.toAdd ((q * x).left (Multiplicative.ofAdd 0)) +
      Multiplicative.toAdd ((q * x).left (Multiplicative.ofAdd 1)) +
      Multiplicative.toAdd ((q * x).left (Multiplicative.ofAdd 2)) = 0 :=
    w16g_sum_coord_eq_zero_of_cube hqx3 hqxB
  set aq := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 0))
  set bq := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 1))
  set cq := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 2))
  set eq := Multiplicative.toAdd q.right
  set ax := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 0))
  set bx := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 1))
  set cx := Multiplicative.toAdd (x.left (Multiplicative.ofAdd 2))
  have hqe : q = el 1 aq bq cq eq := el_eta q
  have hx0 : Multiplicative.toAdd x.right = 0 := by rw [hxr]; simp
  have hxe : x = el 1 ax bx cx 0 := by rw [el_eta x, hx0]
  clear_value eq
  rcases zmod3_cases eq with heq | heq | heq
  · subst eq
    exact absurd rfl hqne
  · subst eq
    refine ⟨ax, bx, cx, ?_, hxe⟩
    have hprod : q * x = el 1 (aq + cx) (bq + ax) (cq + bx) 1 := by
      rw [hqe, hxe, el_mul_one, add_zero]
    have hsum' : (aq + cx) + (bq + ax) + (cq + bx) = 0 := by
      have h := hqxsum
      rw [hprod] at h
      have h0 : Multiplicative.toAdd ((el 1 (aq + cx) (bq + ax) (cq + bx) 1).left
          (Multiplicative.ofAdd 0)) = aq + cx := by rw [el_left_zero]; rfl
      have h1 : Multiplicative.toAdd ((el 1 (aq + cx) (bq + ax) (cq + bx) 1).left
          (Multiplicative.ofAdd 1)) = bq + ax := by rw [el_left_one]; rfl
      have h2 : Multiplicative.toAdd ((el 1 (aq + cx) (bq + ax) (cq + bx) 1).left
          (Multiplicative.ofAdd 2)) = cq + bx := by rw [el_left_two]; rfl
      rw [h0, h1, h2] at h
      exact h
    have hqsum' : aq + bq + cq = 0 := by
      simpa [aq, bq, cq] using hqsum
    have h1 : (aq + cx) + (bq + ax) + (cq + bx) = (aq + bq + cq) + (ax + bx + cx) := by abel
    rw [h1, hqsum', zero_add] at hsum'
    exact hsum'
  · subst eq
    refine ⟨ax, bx, cx, ?_, hxe⟩
    have hprod : q * x = el 1 (aq + bx) (bq + cx) (cq + ax) 2 := by
      rw [hqe, hxe, el_mul_two, add_zero]
    have hsum' : (aq + bx) + (bq + cx) + (cq + ax) = 0 := by
      have h := hqxsum
      rw [hprod] at h
      have h0 : Multiplicative.toAdd ((el 1 (aq + bx) (bq + cx) (cq + ax) 2).left
          (Multiplicative.ofAdd 0)) = aq + bx := by rw [el_left_zero]; rfl
      have h1 : Multiplicative.toAdd ((el 1 (aq + bx) (bq + cx) (cq + ax) 2).left
          (Multiplicative.ofAdd 1)) = bq + cx := by rw [el_left_one]; rfl
      have h2 : Multiplicative.toAdd ((el 1 (aq + bx) (bq + cx) (cq + ax) 2).left
          (Multiplicative.ofAdd 2)) = cq + ax := by rw [el_left_two]; rfl
      rw [h0, h1, h2] at h
      exact h
    have hqsum' : aq + bq + cq = 0 := by
      simpa [aq, bq, cq] using hqsum
    have h1 : (aq + bx) + (bq + cx) + (cq + ax) = (aq + bq + cq) + (ax + bx + cx) := by abel
    rw [h1, hqsum', zero_add] at hsum'
    exact hsum'

private theorem w16g_card_inf_B (Q : Subgroup w16g_ZWr1) (hQ : IsPOnePlusTwo 3 ↥Q) :
    Nat.card ↥(Q ⊓ w16g_B) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQext, hQcard, hQexp⟩ := hQ
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hQcomm : ¬ IsMulCommutative ↥Q := by
    intro hcomm
    have htop : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have hnontriv := hQext.quotient_nontrivial
    rw [QuotientGroup.nontrivial_iff, htop] at hnontriv
    exact hnontriv rfl
  have hQnotleB : ¬ Q ≤ w16g_B := by
    intro hQB
    apply hQcomm
    refine IsMulCommutative.of_setLike_mul_comm (s := Q) ?_
    intro x hx y hy
    exact w16g_B_comm (hQB hx) (hQB hy)
  have hex : ∃ x, x ∈ Q ∧ x ∉ w16g_B := by
    by_contra h
    apply hQnotleB
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  obtain ⟨q, hqQ, hqB⟩ := hex
  let ρ : ↥Q →* Multiplicative (ZMod 3) :=
    (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).comp Q.subtype
  have hρq : ρ ⟨q, hqQ⟩ ≠ 1 := by
    intro h
    apply hqB
    rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker
      from rfl, MonoidHom.mem_ker]
    simpa [ρ] using h
  have hM3card : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  haveI : Fact (Nat.card (Multiplicative (ZMod 3))).Prime :=
    ⟨by rw [hM3card]; norm_num⟩
  have hrange : Nat.card ↥ρ.range = 3 := by
    have hne : ρ.range ≠ ⊥ := by
      intro hbot
      have hmem : ρ ⟨q, hqQ⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hbot] at hmem
      exact hρq (Subgroup.mem_bot.mp hmem)
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ρ.range with h | h
    · exact absurd h hne
    · rw [h, Subgroup.card_top, hM3card]
  have hker : ρ.ker = (Q ⊓ w16g_B).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →*
        Multiplicative (ZMod 3)).ker from rfl, MonoidHom.mem_ker]
      simpa [ρ] using h
    · rintro ⟨-, hB⟩
      rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →*
        Multiplicative (ZMod 3)).ker from rfl, MonoidHom.mem_ker] at hB
      simpa [ρ] using hB
  have hker_card : Nat.card ↥ρ.ker = 9 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hQcard, hrange] at h
    omega
  have h1 : Nat.card ↥(Q ⊓ w16g_B) = Nat.card ↥((Q ⊓ w16g_B).subgroupOf Q) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [h1, ← hker]
  exact hker_card

private theorem w16g_inf_B_eq_D (Q : Subgroup w16g_ZWr1) (hQ : IsPOnePlusTwo 3 ↥Q) :
    Q ⊓ w16g_B = w16g_D := by
  have hle : Q ⊓ w16g_B ≤ w16g_D := w16g_inf_B_le_D Q hQ
  have hcard : Nat.card ↥w16g_D ≤ Nat.card ↥(Q ⊓ w16g_B) := by
    rw [w16g_card_D, w16g_card_inf_B Q hQ]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

private theorem w16g_b0_mem_of_isPOnePlusTwo (Q : Subgroup w16g_ZWr1)
    (hQ : IsPOnePlusTwo 3 ↥Q) : w16g_b0 ∈ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ0 : IsPOnePlusTwo 3 ↥Q := hQ
  obtain ⟨hQext, hQcard, hQexp⟩ := hQ
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hQcomm : ¬ IsMulCommutative ↥Q := by
    intro hcomm
    have htop : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have hnontriv := hQext.quotient_nontrivial
    rw [QuotientGroup.nontrivial_iff, htop] at hnontriv
    exact hnontriv rfl
  have hQnotleB : ¬ Q ≤ w16g_B := by
    intro hQB
    apply hQcomm
    refine IsMulCommutative.of_setLike_mul_comm (s := Q) ?_
    intro x hx y hy
    exact w16g_B_comm (hQB hx) (hQB hy)
  have hex : ∃ x, x ∈ Q ∧ x ∉ w16g_B := by
    by_contra h
    apply hQnotleB
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  obtain ⟨q, hqQ, hqB⟩ := hex
  have hqne : Multiplicative.toAdd q.right ≠ 0 := by
    intro h
    apply hqB
    rw [show w16g_B = (RegularWreathProduct.rightHom : w16g_ZWr1 →* Multiplicative (ZMod 3)).ker
      from rfl, MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by simpa using h)
  have hq3 : q ^ 3 = 1 := by simpa using hQexp ⟨q, hqQ⟩
  have hqsum : Multiplicative.toAdd (q.left (Multiplicative.ofAdd 0)) +
      Multiplicative.toAdd (q.left (Multiplicative.ofAdd 1)) +
      Multiplicative.toAdd (q.left (Multiplicative.ofAdd 2)) = 0 :=
    w16g_sum_coord_eq_zero_of_cube hq3 hqB
  set a := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 0))
  set b := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 1))
  set c := Multiplicative.toAdd (q.left (Multiplicative.ofAdd 2))
  set e := Multiplicative.toAdd q.right
  have hqe : q = el 1 a b c e := el_eta q
  have hqsum' : a + b + c = 0 := by simpa [a, b, c] using hqsum
  have hinf : Q ⊓ w16g_B = w16g_D := w16g_inf_B_eq_D Q hQ0
  have hD_le_Q : w16g_D ≤ Q := by
    rw [← hinf]
    exact inf_le_left
  clear_value e
  rcases zmod3_cases e with he | he | he
  · exact absurd he hqne
  · subst e
    have hs : -b + -c + -a = 0 := by
      have h : -b + -c + -a = -(a + b + c) := by abel
      rw [h, hqsum']
      exact neg_zero
    have hd : el 1 (-b) (-c) (-a) 0 ∈ w16g_D := ⟨-b, -c, -a, hs, rfl⟩
    have hdQ : el 1 (-b) (-c) (-a) 0 ∈ Q := hD_le_Q hd
    have hprod : q * el 1 (-b) (-c) (-a) 0 = w16g_b0 := by
      rw [hqe, show w16g_b0 = el 1 0 0 0 1 from rfl, el_mul_one, add_zero,
        show a + -a = 0 by abel, show b + -b = 0 by abel, show c + -c = 0 by abel]
    rw [← hprod]
    exact Q.mul_mem hqQ hdQ
  · subst e
    have hs : -c + -a + -b = 0 := by
      have h : -c + -a + -b = -(a + b + c) := by abel
      rw [h, hqsum']
      exact neg_zero
    have hd : el 1 (-c) (-a) (-b) 0 ∈ w16g_D := ⟨-c, -a, -b, hs, rfl⟩
    have hdQ : el 1 (-c) (-a) (-b) 0 ∈ Q := hD_le_Q hd
    have hprod : q * el 1 (-c) (-a) (-b) 0 = el 1 0 0 0 2 := by
      rw [hqe, el_mul_two, add_zero,
        show a + -a = 0 by abel, show b + -b = 0 by abel, show c + -c = 0 by abel]
    have hq2 : el 1 0 0 0 2 ∈ Q := by
      rw [← hprod]
      exact Q.mul_mem hqQ hdQ
    have hb0sq : w16g_b0 ^ 2 = el 1 0 0 0 2 := by
      rw [pow_two, w16g_b0, el_mul_one, add_zero]
      congr 2 <;> abel
    have hsq2 : (el 1 0 0 0 2) ^ 2 = w16g_b0 := by
      rw [← hb0sq]
      have h4 : w16g_b0 ^ 4 = w16g_b0 := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, w16g_b0_cube, one_mul]
      calc (w16g_b0 ^ 2) ^ 2 = w16g_b0 ^ (2 * 2) := by rw [pow_mul]
        _ = w16g_b0 ^ 4 := by norm_num
        _ = w16g_b0 := h4
    rw [← hsq2]
    exact Q.pow_mem hq2 2

private theorem w16g_isPOnePlusTwo_of_iso {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (f : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨CFSG.GH74.M12.Hyp.isExtraspecial_of_mulEquiv f hX, ?_, ?_⟩
  · rw [← Nat.card_congr f.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_eq_M_of_isPOnePlusTwo (Q : Subgroup w16g_ZWr1)
    (hQ : IsPOnePlusTwo 3 ↥Q) : Q = w16g_M := by
  have hinf : Q ⊓ w16g_B = w16g_D := w16g_inf_B_eq_D Q hQ
  have hb0Q : w16g_b0 ∈ Q := w16g_b0_mem_of_isPOnePlusTwo Q hQ
  have hD_le_Q : w16g_D ≤ Q := by
    rw [← hinf]
    exact inf_le_left
  have hMQ : w16g_M ≤ Q := by
    rw [w16g_M_eq_sup]
    exact sup_le hD_le_Q (Subgroup.zpowers_le.mpr hb0Q)
  have hcard : Nat.card ↥Q ≤ Nat.card ↥w16g_M := by
    rw [w16g_card_M, hQ.2.1]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hMQ hcard).symm

private theorem w16g_center_le_M : Subgroup.center w16g_ZWr1 ≤ w16g_M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [center_eq_diag (n := 1) (by norm_num)]
  rintro c ⟨d, rfl⟩
  rw [w16g_mem_M]
  refine ⟨Multiplicative.toAdd d, Multiplicative.toAdd d, Multiplicative.toAdd d, 0, ?_, ?_⟩
  · have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    calc Multiplicative.toAdd d + Multiplicative.toAdd d + Multiplicative.toAdd d =
        Multiplicative.toAdd d * 3 := by ring
      _ = 0 := by rw [h3, mul_zero]
  · rw [diagHom_apply]

theorem w16g_wr_unique_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr 1) :
    ∃ M : Subgroup X, IsPOnePlusTwo 3 ↥M ∧
      (∀ Q : Subgroup X, IsPOnePlusTwo 3 ↥Q → Q = M) ∧
      (∀ c ∈ Subgroup.center X, c ∈ M) := by
  let M : Subgroup X := w16g_M.map e.symm.toMonoidHom
  have hMext : IsPOnePlusTwo 3 ↥M := w16g_isPOnePlusTwo_of_iso
    (Subgroup.equivMapOfInjective w16g_M e.symm.toMonoidHom e.symm.injective)
    w16g_M_isPOnePlusTwo
  have hMun : ∀ Q : Subgroup X, IsPOnePlusTwo 3 ↥Q → Q = M := by
    intro Q hQ
    have hQ' : IsPOnePlusTwo 3 ↥(Q.map e.toMonoidHom) :=
      w16g_isPOnePlusTwo_of_iso
        (Subgroup.equivMapOfInjective Q e.toMonoidHom e.injective) hQ
    have huniq : Q.map e.toMonoidHom = w16g_M := w16g_eq_M_of_isPOnePlusTwo _ hQ'
    have hmapM : M.map e.toMonoidHom = w16g_M := by
      dsimp [M]
      have hcomp : ((e : X →* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr 1).comp
          (e.symm : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr 1 →* X)) =
          MonoidHom.id _ := by
        ext x <;> simp
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [huniq, hmapM]
  refine ⟨M, hMext, hMun, ?_⟩
  intro c hc
  have hce : e c ∈ Subgroup.center w16g_ZWr1 := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hc x]
  exact ⟨e c, w16g_center_le_M hce, by simp [M]⟩

end W16GTwoCB

end CFSG.LocalAnalysis.WeakClosure81
