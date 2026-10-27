module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open Subgroup
open scoped commutatorElement Pointwise

section Transfer

variable {E : Type*} [Group E]

theorem commutatorElement_mul_right_of_mem_center {x y n : E} (hn : n ∈ center E) :
    ⁅x * n, y⁆ = ⁅x, y⁆ := by
  have h : y * n = n * y := mem_center_iff.mp hn y
  rw [commutatorElement_def, commutatorElement_def]
  calc x * n * y * (x * n)⁻¹ * y⁻¹ = x * (n * y) * n⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * n) * n⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_left_of_mem_center {x y n : E} (hn : n ∈ center E) :
    ⁅x, y * n⁆ = ⁅x, y⁆ := by
  have h : x⁻¹ * n = n * x⁻¹ := mem_center_iff.mp hn x⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * n) * x⁻¹ * (y * n)⁻¹ = x * y * (n * x⁻¹) * n⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * n) * n⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mem_zpowers {a b : E} (hc : ⁅a, b⁆ ∈ center E) {x y : E}
    (hx : x ∈ closure {a, b}) (hy : y ∈ closure {a, b}) : ⁅x, y⁆ ∈ zpowers ⁅a, b⁆ := by
  set c := ⁅a, b⁆ with hcdef
  have hn : (zpowers c).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hk : c ^ k ∈ center E := zpow_mem hc k
    rw [mem_center_iff.mp hk g, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers c) k
  set q := QuotientGroup.mk' (zpowers c)
  have hab : q a * q b = q b * q a := by
    have h1 : q c = 1 := (QuotientGroup.eq_one_iff c).mpr (mem_zpowers c)
    have h2 : a * b = c * (b * a) := by rw [hcdef, commutatorElement_def]; group
    rw [← map_mul, ← map_mul, h2, map_mul, h1, one_mul]
  have hpair : ({q a, q b} : Set (E ⧸ zpowers c)).Pairwise Commute := by
    intro u hu w hw _
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have := Subgroup.isMulCommutative_closure hpair
  have hmap : (closure ({a, b} : Set E)).map q = closure {q a, q b} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hxq : q x ∈ closure ({q a, q b} : Set (E ⧸ zpowers c)) := hmap ▸ mem_map_of_mem q hx
  have hyq : q y ∈ closure ({q a, q b} : Set (E ⧸ zpowers c)) := hmap ▸ mem_map_of_mem q hy
  have hcomm : q x * q y = q y * q x :=
    congrArg Subtype.val (mul_comm' (⟨q x, hxq⟩ : closure ({q a, q b} : Set (E ⧸ zpowers c)))
      ⟨q y, hyq⟩)
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  change q (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
  group

theorem commutator_ne_top_of_center [Finite E] {N H : Subgroup E} (hNc : N ≤ center E)
    (hN9 : Nat.card N = 9) (hN3 : ∀ n ∈ N, n ^ 3 = 1) (hNH : N ≤ H) (hidx : ¬ 3 ∣ H.index)
    {a b : E} (hgen : ∀ h ∈ H, ∃ w ∈ closure {a, b}, ∃ n ∈ N, h = w * n) (hab : ⁅a, b⁆ ∈ N) :
    commutator E ≠ ⊤ := by
  intro hperf
  set c := ⁅a, b⁆ with hcdef
  have hcc : c ∈ center E := hNc hab
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ zpowers c := by
    intro x hx y hy
    obtain ⟨w₁, hw₁, n₁, hn₁, rfl⟩ := hgen x hx
    obtain ⟨w₂, hw₂, n₂, hn₂, rfl⟩ := hgen y hy
    rw [commutatorElement_mul_right_of_mem_center (hNc hn₁),
      commutatorElement_mul_left_of_mem_center (hNc hn₂)]
    exact commutatorElement_mem_zpowers hcc hw₁ hw₂
  have hHc : (commutator H).map H.subtype ≤ zpowers c := by
    change (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ : Subgroup H).map H.subtype ≤ zpowers c
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype, commutator_le]
    exact fun x hx y hy => hcomm x hx y hy
  have : Group.IsPerfect E := ⟨hperf⟩
  let ϕ : H →* Abelianization H := Abelianization.of
  have hτ : ∀ g, MonoidHom.transfer ϕ g = 1 := by
    intro g
    have hg : g ∈ commutator E := by rw [hperf]; exact mem_top g
    exact Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hg
  have hNcomm : N ≤ (commutator H).map H.subtype := by
    intro n hn
    have hcen : n ∈ center E := hNc hn
    have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * n ^ k * g₀ ∈ H → g₀⁻¹ * n ^ k * g₀ = n ^ k := by
      intro k g₀ _
      have h1 := mem_center_iff.mp (pow_mem hcen k) g₀
      rw [mul_assoc, ← h1, inv_mul_cancel_left]
    have h1 := MonoidHom.transfer_eq_pow ϕ n key
    rw [hτ] at h1
    have h2 : (⟨n ^ H.index, pow_mem (hNH hn) _⟩ : H) ∈ commutator H := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h1.symm
    have h3 : n ^ H.index ∈ (commutator H).map H.subtype := ⟨_, h2, rfl⟩
    have hcop : Nat.Coprime H.index 3 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx))
    obtain ⟨k, hk⟩ : ∃ k : ℕ, H.index * k % 3 = 1 := by
      refine ⟨H.index % 3 , ?_⟩
      have h0 : H.index % 3 ≠ 0 := fun h => hidx (Nat.dvd_of_mod_eq_zero h)
      have hlt : H.index % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [Nat.mul_mod, Nat.mod_mod]
      interval_cases h : H.index % 3 <;> simp_all
    have e : n = (n ^ H.index) ^ k := by
      rw [← pow_mul, ← Nat.div_add_mod (H.index * k) 3, hk, pow_add, pow_mul, hN3 n hn, one_pow,
        one_mul, pow_one]
    rw [e]
    exact pow_mem h3 k
  have hle : N ≤ zpowers c := hNcomm.trans hHc
  have hcard : Nat.card N ≤ Nat.card (zpowers c) := card_le_of_le hle
  rw [Nat.card_zpowers, hN9] at hcard
  have hc3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (hN3 c hab)
  have := Nat.le_of_dvd (by norm_num) hc3
  omega

end Transfer

theorem card_eq_card_range_mul_card_ker {K B : Type*} [Group K] [Group B] (f : K →* B) :
    Nat.card K = Nat.card f.range * Nat.card f.ker := by
  rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

section Fibre

variable {X Y B : Type*} [Group X] [Group Y] [Group B]

def fibre (ψ : X →* B) (π : Y →* B) (G : Subgroup Y) : Subgroup (X × Y) where
  carrier := {q | q.2 ∈ G ∧ ψ q.1 = π q.2}
  mul_mem' := fun ha hb => ⟨G.mul_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩
  one_mem' := ⟨G.one_mem, by simp⟩
  inv_mem' := fun ha => ⟨G.inv_mem ha.1, by simp [ha.2]⟩

variable [Finite X] [Finite Y] [Finite B]

theorem exists_mulEquiv_of_fibre (ψ : X →* B) (π : Y →* B)
    {L T : Subgroup X} {ML G TM : Subgroup Y} {u v : B}
    (hLn : L.Normal) (hLperf : ⁅L, L⁆ = L) (hMperf : ⁅ML, ML⁆ = ML)
    (hψL : L.map ψ = ML.map π)
    (hkL : ψ.ker ≤ L) (hkLc : ∀ z ∈ ψ.ker, ∀ l ∈ L, z * l = l * z) (hk3 : Nat.card ψ.ker = 3)
    (hMG : ML ≤ G) (hkM : G ⊓ π.ker ≤ ML) (hkMc : ∀ z ∈ G ⊓ π.ker, ∀ m ∈ ML, z * m = m * z)
    (hkM3 : Nat.card (G ⊓ π.ker : Subgroup Y) = 3)
    (hu : u ∈ L.map ψ) (hv : v ∈ L.map ψ) (huv : u * v = v * u)
    (hidx : ¬ 3 ∣ (closure {u, v}).relIndex (L.map ψ))
    (hT : IsPGroup 2 T) (hTM : IsPGroup 2 TM) (hTMG : TM ≤ G) (hψT : T.map ψ = TM.map π)
    (hLT : L ⊔ T = ⊤) (hMT : ML ⊔ TM = G) :
    ∃ φ : X ≃* G, (∀ x, π (φ x) = ψ x) ∧ L.map (G.subtype.comp φ.toMonoidHom) = ML ∧
      T.map (G.subtype.comp φ.toMonoidHom) = TM := by
  classical
  have hGML : ∀ y ∈ G, π y ∈ L.map ψ → y ∈ ML := by
    intro y hy hyB
    rw [hψL] at hyB
    obtain ⟨m, hm, hmy⟩ := hyB
    have h1 : y * m⁻¹ ∈ G ⊓ π.ker := ⟨G.mul_mem hy (G.inv_mem (hMG hm)),
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hmy, mul_inv_cancel])⟩
    have h2 := ML.mul_mem (hkM h1) hm
    rwa [inv_mul_cancel_right] at h2
  have hexp3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥ψ.ker) (x := ⟨z, hz⟩)
    rw [hk3] at h
    exact congrArg Subtype.val h
  have hexpM3 : ∀ z ∈ G ⊓ π.ker, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥(G ⊓ π.ker)) (x := ⟨z, hz⟩)
    rw [hkM3] at h
    exact congrArg Subtype.val h
  set P := fibre ψ π G with hP
  set PL := P ⊓ L.prod ML with hPL
  set N := ψ.ker.prod (G ⊓ π.ker) with hN
  set Q := P ⊓ T.prod TM with hQ
  have hNPL : N ≤ PL := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    refine ⟨⟨hw.1, ?_⟩, hkL hz, hkM hw⟩
    rw [(MonoidHom.mem_ker).mp hz, (MonoidHom.mem_ker).mp hw.2]
  have hcardN : Nat.card N = 9 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hk3, hkM3]
  have hN3 : ∀ n ∈ N, n ^ 3 = 1 := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    exact Prod.ext (hexp3 z hz) (hexpM3 w hw)
  let f : PL →* B := ψ.comp ((MonoidHom.fst X Y).comp PL.subtype)
  let g₁ : PL →* X := (MonoidHom.fst X Y).comp PL.subtype
  let g₂ : PL →* Y := (MonoidHom.snd X Y).comp PL.subtype
  have hf2 : ∀ q : PL, f q = π (q : X × Y).2 := fun q => q.2.1.2
  have hrf : f.range = L.map ψ := by
    ext b
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q : X × Y).1, q.2.2.1, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      have hb : ψ l ∈ ML.map π := hψL ▸ mem_map_of_mem ψ hl
      obtain ⟨m, hm, hmb⟩ := hb
      exact ⟨⟨(l, m), ⟨hMG hm, hmb.symm⟩, hl, hm⟩, rfl⟩
  have hkf : f.ker = N.subgroupOf PL := by
    ext q
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact ⟨h, q.2.1.1, MonoidHom.mem_ker.mpr ((hf2 q).symm.trans h)⟩
    · intro h
      exact h.1
  have hr1 : g₁.range = L := by
    ext l
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.2.1
    · intro hl
      have hb : ψ l ∈ ML.map π := hψL ▸ mem_map_of_mem ψ hl
      obtain ⟨m, hm, hmb⟩ := hb
      exact ⟨⟨(l, m), ⟨hMG hm, hmb.symm⟩, hl, hm⟩, rfl⟩
  have hr2 : g₂.range = ML := by
    ext m
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.2.2
    · intro hm
      have hb : π m ∈ L.map ψ := hψL.symm ▸ mem_map_of_mem π hm
      obtain ⟨l, hl, hlb⟩ := hb
      exact ⟨⟨(l, m), ⟨hMG hm, hlb⟩, hl, hm⟩, rfl⟩
  have huf : u ∈ f.range := hrf ▸ hu
  have hvf : v ∈ f.range := hrf ▸ hv
  obtain ⟨a, ha⟩ := huf
  obtain ⟨b, hb⟩ := hvf
  have hnp : commutator PL ≠ ⊤ := by
    refine commutator_ne_top_of_center (N := N.subgroupOf PL) (H := (closure {u, v}).comap f)
      ?_ ?_ ?_ ?_ ?_ (a := a) (b := b) ?_ ?_
    · intro n hn
      rw [mem_center_iff]
      intro e
      have hn' : (n : X × Y) ∈ N := hn
      apply Subtype.ext
      apply Prod.ext
      · exact (hkLc _ hn'.1 _ e.2.2.1).symm
      · exact (hkMc _ hn'.2 _ e.2.2.2).symm
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNPL).toEquiv, hcardN]
    · intro n hn
      exact Subtype.ext (hN3 _ hn)
    · intro n hn
      have h1 : n ∈ f.ker := hkf ▸ hn
      rw [mem_comap, (MonoidHom.mem_ker).mp h1]
      exact one_mem _
    · rw [index_comap, hrf]
      exact hidx
    · intro h hh
      have h1 : f h ∈ (closure ({a, b} : Set PL)).map f := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb]
        exact hh
      obtain ⟨w, hw, hwh⟩ := h1
      refine ⟨w, hw, w⁻¹ * h, ?_, by group⟩
      rw [← hkf, MonoidHom.mem_ker, map_mul, map_inv, hwh, inv_mul_cancel]
    · rw [← hkf, MonoidHom.mem_ker, map_commutatorElement, ha, hb, commutatorElement_def, huv,
        mul_inv_cancel_right, mul_inv_cancel]
  set DE := commutator PL with hDE
  set D := ⁅PL, PL⁆ with hD
  have hDDE : DE.map PL.subtype = D := Subgroup.map_subtype_commutator PL
  have hLψperf : ⁅L.map ψ, L.map ψ⁆ = L.map ψ := by rw [← map_commutator, hLperf]
  have hfD : DE.map f = L.map ψ := by
    rw [hDE, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, hrf, hLψperf]
  have hg₁D : DE.map g₁ = L := by
    rw [hDE, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, hr1, hLperf]
  have hg₂D : DE.map g₂ = ML := by
    rw [hDE, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, hr2, hMperf]
  have hB0 : 0 < Nat.card (L.map ψ) := Nat.card_pos
  have hcL : Nat.card L = Nat.card (L.map ψ) * 3 := by
    rw [card_eq_card_range_mul_card_ker (ψ.comp L.subtype), MonoidHom.range_comp,
      range_subtype, ← hk3]
    congr 1
    have h1 : (ψ.comp L.subtype).ker = ψ.ker.subgroupOf L := by ext x; exact Iff.rfl
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkL).toEquiv
  have hcML : Nat.card ML = Nat.card (L.map ψ) * 3 := by
    rw [card_eq_card_range_mul_card_ker (π.comp ML.subtype), MonoidHom.range_comp,
      range_subtype, ← hψL, ← hkM3]
    congr 1
    have h0 : (π.comp ML.subtype).ker = π.ker.subgroupOf ML := by ext x; exact Iff.rfl
    rw [h0]
    have h1 : π.ker.subgroupOf ML = (G ⊓ π.ker).subgroupOf ML := by
      ext m
      rw [mem_subgroupOf, mem_subgroupOf]
      exact ⟨fun h => ⟨hMG m.2, h⟩, fun h => h.2⟩
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkM).toEquiv
  have hcPL : Nat.card PL = Nat.card (L.map ψ) * 9 := by
    rw [card_eq_card_range_mul_card_ker f, hrf, hkf, ← hcardN]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNPL).toEquiv)
  set kD := (f.comp DE.subtype).ker with hkD
  have hcDE : Nat.card DE = Nat.card (L.map ψ) * Nat.card kD := by
    rw [card_eq_card_range_mul_card_ker (f.comp DE.subtype), MonoidHom.range_comp,
      range_subtype, hfD]
  have hkD9 : Nat.card kD ∣ 9 := by
    have h1 : kD.map DE.subtype ≤ f.ker := by
      rintro _ ⟨d, hd, rfl⟩
      exact hd
    have h2 := card_dvd_of_le h1
    rw [card_map_of_injective DE.subtype_injective, hkf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNPL).toEquiv, hcardN] at h2
    exact h2
  have hLle : Nat.card L ≤ Nat.card DE := by
    rw [← hg₁D]
    exact Nat.card_le_card_of_surjective _ (g₁.subgroupMap_surjective DE)
  have hDlt : Nat.card DE < Nat.card PL := by
    refine lt_of_le_of_ne (card_le_of_le le_top |>.trans_eq card_top) ?_
    intro h
    exact hnp ((card_eq_iff_eq_top DE).mp h)
  have hk3' : Nat.card kD = 3 := by
    have h1 : 3 ≤ Nat.card kD := by
      rw [hcL, hcDE] at hLle
      exact Nat.le_of_mul_le_mul_left hLle hB0
    have h2 : Nat.card kD < 9 := by
      rw [hcDE, hcPL] at hDlt
      exact Nat.lt_of_mul_lt_mul_left hDlt
    have h3 : Nat.card kD ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hkD9, by norm_num⟩
    have h4 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h4] at h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    omega
  have hcD : Nat.card DE = Nat.card (L.map ψ) * 3 := by rw [hcDE, hk3']
  have hinj₁ : ∀ d ∈ DE, g₁ d = 1 → d = 1 := by
    have hbij := (g₁.subgroupMap_surjective DE).bijective_of_nat_card_le
      (by rw [hg₁D, hcL, hcD])
    intro d hd hd1
    have h1 : g₁.subgroupMap DE ⟨d, hd⟩ = g₁.subgroupMap DE 1 :=
      Subtype.ext (by simpa using hd1)
    exact congrArg Subtype.val (hbij.1 h1)
  have hinj₂ : ∀ d ∈ DE, g₂ d = 1 → d = 1 := by
    have hbij := (g₂.subgroupMap_surjective DE).bijective_of_nat_card_le
      (by rw [hg₂D, hcML, hcD])
    intro d hd hd1
    have h1 : g₂.subgroupMap DE ⟨d, hd⟩ = g₂.subgroupMap DE 1 :=
      Subtype.ext (by simpa using hd1)
    exact congrArg Subtype.val (hbij.1 h1)
  have hD₁ : ∀ q ∈ D, q.1 = 1 → q = 1 := by
    rw [← hDDE]
    rintro _ ⟨d, hd, rfl⟩ h1
    rw [hinj₁ d hd h1]
    rfl
  have hD₂ : ∀ q ∈ D, q.2 = 1 → q = 1 := by
    rw [← hDDE]
    rintro _ ⟨d, hd, rfl⟩ h1
    rw [hinj₂ d hd h1]
    rfl
  have hPLconj : ∀ q ∈ P, ∀ x ∈ PL, q * x * q⁻¹ ∈ PL := by
    intro q hq x hx
    have hxP : x ∈ P := hx.1
    refine ⟨P.mul_mem (P.mul_mem hq hxP) (P.inv_mem hq), hLn.conj_mem _ hx.2.1 _, ?_⟩
    have h1 : (q * x * q⁻¹).2 ∈ G := (P.mul_mem (P.mul_mem hq hxP) (P.inv_mem hq)).1
    refine hGML _ h1 ?_
    have h2 : ψ (q * x * q⁻¹).1 = π (q * x * q⁻¹).2 :=
      (P.mul_mem (P.mul_mem hq hxP) (P.inv_mem hq)).2
    rw [← h2]
    exact mem_map_of_mem ψ (hLn.conj_mem _ hx.2.1 _)
  have hDconj : ∀ q ∈ P, ∀ d ∈ D, q * d * q⁻¹ ∈ D := by
    intro q hq d hd
    have hle : PL.map (MulAut.conj q).toMonoidHom ≤ PL := by
      rintro _ ⟨x, hx, rfl⟩
      exact hPLconj q hq x hx
    have h1 : D.map (MulAut.conj q).toMonoidHom ≤ D := by
      rw [hD, map_commutator]
      exact commutator_mono hle hle
    exact h1 ⟨d, hd, rfl⟩
  have hQP : Q ≤ P := inf_le_left
  have hDPL : D ≤ PL := commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact PL.mul_mem (PL.mul_mem (PL.mul_mem hx hy) (PL.inv_mem hx)) (PL.inv_mem hy)
  have hDP : D ≤ P := hDPL.trans inf_le_left
  have hQN : Q ≤ normalizer (D : Set (X × Y)) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro d
    constructor
    · exact hDconj q (hQP hq) d
    · intro h
      have := hDconj q⁻¹ (P.inv_mem (hQP hq)) _ h
      simpa [mul_assoc] using this
  set Δ := D ⊔ Q with hΔ
  have hΔP : Δ ≤ P := sup_le hDP hQP
  have hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1 := by
    intro q hq
    obtain ⟨m₁, hm₁⟩ := hT ⟨q.1, hq.2.1⟩
    obtain ⟨m₂, hm₂⟩ := hTM ⟨q.2, hq.2.2⟩
    refine ⟨m₁ + m₂, Prod.ext ?_ ?_⟩
    · have h := congrArg Subtype.val hm₁
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [Prod.pow_fst, pow_add, pow_mul, h, one_pow, Prod.fst_one]
    · have h := congrArg Subtype.val hm₂
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [Prod.pow_snd, pow_add, mul_comm, pow_mul, h, one_pow, Prod.snd_one]
  have hΔN : ∀ δ ∈ Δ, δ ∈ N → δ ∈ D := by
    intro δ hδ hδN
    have hset := coe_mul_of_right_le_normalizer_left D Q hQN
    have hδ' : δ ∈ ((D : Set (X × Y)) * (Q : Set (X × Y))) := by
      rw [← hset]
      exact hδ
    obtain ⟨d, hd, q, hq, rfl⟩ := hδ'
    have hdN : d ∈ normalizer (D : Set (X × Y)) := le_normalizer hd
    have hqN : q ∈ normalizer (D : Set (X × Y)) := hQN hq
    let mk := QuotientGroup.mk' (D.subgroupOf (normalizer (D : Set (X × Y))))
    have hmkd : mk ⟨d, hdN⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    have hdq : mk ⟨d * q, mul_mem hdN hqN⟩ = mk ⟨q, hqN⟩ := by
      rw [show (⟨d * q, mul_mem hdN hqN⟩ : normalizer (D : Set (X × Y))) =
        ⟨d, hdN⟩ * ⟨q, hqN⟩ from rfl, map_mul, hmkd, one_mul]
    obtain ⟨m, hm⟩ := hQ2 q hq
    have h2 : (mk ⟨d * q, mul_mem hdN hqN⟩) ^ 2 ^ m = 1 := by
      rw [hdq, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (by
        change q ^ 2 ^ m ∈ D
        rw [hm]
        exact one_mem D)
    have h3 : (mk ⟨d * q, mul_mem hdN hqN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (by
        change (d * q) ^ 3 ∈ D
        rw [hN3 _ hδN]
        exact one_mem D)
    have hcop : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
    have h4 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    rw [hcop, pow_one] at h4
    have h5 : (⟨d * q, mul_mem hdN hqN⟩ : normalizer (D : Set (X × Y))) ∈
        D.subgroupOf (normalizer (D : Set (X × Y))) := (QuotientGroup.eq_one_iff _).mp h4
    exact h5
  have hΔ₁ : ∀ δ ∈ Δ, δ.1 = 1 → δ = 1 := by
    intro δ hδ h1
    have hδP := hΔP hδ
    have hδN : δ ∈ N := by
      refine ⟨MonoidHom.mem_ker.mpr (by rw [h1, map_one]), hδP.1,
        MonoidHom.mem_ker.mpr (by rw [← hδP.2, h1, map_one])⟩
    exact hD₁ δ (hΔN δ hδ hδN) h1
  have hΔ₂ : ∀ δ ∈ Δ, δ.2 = 1 → δ = 1 := by
    intro δ hδ h2
    have hδP := hΔP hδ
    have hδN : δ ∈ N := by
      refine ⟨MonoidHom.mem_ker.mpr (by rw [hδP.2, h2, map_one]), by rw [h2]; exact G.one_mem,
        MonoidHom.mem_ker.mpr (by rw [h2, map_one])⟩
    exact hD₂ δ (hΔN δ hδ hδN) h2
  have hDΔ : D ≤ Δ := le_sup_left
  have hQΔ : Q ≤ Δ := le_sup_right
  have hD1 : ∀ l ∈ L, ∃ d ∈ D, d.1 = l := by
    intro l hl
    rw [← hg₁D] at hl
    obtain ⟨d, hd, rfl⟩ := hl
    exact ⟨d, hDDE ▸ mem_map_of_mem PL.subtype hd, rfl⟩
  have hD2 : ∀ m ∈ ML, ∃ d ∈ D, d.2 = m := by
    intro m hm
    rw [← hg₂D] at hm
    obtain ⟨d, hd, rfl⟩ := hm
    exact ⟨d, hDDE ▸ mem_map_of_mem PL.subtype hd, rfl⟩
  have hQ1 : ∀ t ∈ T, ∃ s ∈ TM, (t, s) ∈ Q := by
    intro t ht
    have h1 : ψ t ∈ TM.map π := hψT ▸ mem_map_of_mem ψ ht
    obtain ⟨s, hs, hst⟩ := h1
    exact ⟨s, hs, ⟨hTMG hs, hst.symm⟩, ht, hs⟩
  have hQ2' : ∀ s ∈ TM, ∃ t ∈ T, (t, s) ∈ Q := by
    intro s hs
    have h1 : π s ∈ T.map ψ := hψT.symm ▸ mem_map_of_mem π hs
    obtain ⟨t, ht, hts⟩ := h1
    exact ⟨t, ht, ⟨hTMG hs, hts⟩, ht, hs⟩
  let e₁ : Δ →* X := (MonoidHom.fst X Y).comp Δ.subtype
  let e₂ : Δ →* G := ((MonoidHom.snd X Y).comp Δ.subtype).codRestrict G fun δ => (hΔP δ.2).1
  have he₁i : Function.Injective e₁ := by
    rw [injective_iff_map_eq_one]
    intro δ h
    exact Subtype.ext (hΔ₁ δ δ.2 h)
  have he₂i : Function.Injective e₂ := by
    rw [injective_iff_map_eq_one]
    intro δ h
    exact Subtype.ext (hΔ₂ δ δ.2 (congrArg Subtype.val h))
  have he₁s : Function.Surjective e₁ := by
    have hr : e₁.range = ⊤ := by
      rw [eq_top_iff, ← hLT, sup_le_iff]
      constructor
      · intro l hl
        obtain ⟨d, hd, rfl⟩ := hD1 l hl
        exact ⟨⟨d, hDΔ hd⟩, rfl⟩
      · intro t ht
        obtain ⟨s, -, hq⟩ := hQ1 t ht
        exact ⟨⟨(t, s), hQΔ hq⟩, rfl⟩
    exact MonoidHom.range_eq_top.mp hr
  have he₂s : Function.Surjective e₂ := by
    intro g
    have hg : (g : Y) ∈ ML ⊔ TM := hMT.symm ▸ g.2
    have hle : ML ⊔ TM ≤ (e₂.range).map G.subtype := by
      rw [sup_le_iff]
      constructor
      · intro m hm
        obtain ⟨d, hd, rfl⟩ := hD2 m hm
        exact ⟨e₂ ⟨d, hDΔ hd⟩, ⟨⟨d, hDΔ hd⟩, rfl⟩, rfl⟩
      · intro s hs
        obtain ⟨t, -, hq⟩ := hQ2' s hs
        exact ⟨e₂ ⟨(t, s), hQΔ hq⟩, ⟨⟨(t, s), hQΔ hq⟩, rfl⟩, rfl⟩
    obtain ⟨_, ⟨δ, rfl⟩, h⟩ := hle hg
    exact ⟨δ, Subtype.ext h⟩
  let E₁ : Δ ≃* X := MulEquiv.ofBijective e₁ ⟨he₁i, he₁s⟩
  let E₂ : Δ ≃* G := MulEquiv.ofBijective e₂ ⟨he₂i, he₂s⟩
  have hφ : ∀ δ (hδ : δ ∈ Δ), (E₁.symm.trans E₂) δ.1 = ⟨δ.2, (hΔP hδ).1⟩ := by
    intro δ hδ
    have h1 : E₁.symm δ.1 = ⟨δ, hδ⟩ := E₁.symm_apply_eq.mpr rfl
    rw [MulEquiv.trans_apply, h1]
    rfl
  refine ⟨E₁.symm.trans E₂, fun x => ?_, ?_, ?_⟩
  · obtain ⟨δ, rfl⟩ := he₁s x
    have h := hφ δ δ.2
    change π (((E₁.symm.trans E₂) (e₁ δ) : G) : Y) = ψ (e₁ δ)
    change π (((E₁.symm.trans E₂) (δ : X × Y).1 : G) : Y) = ψ (δ : X × Y).1
    rw [h]
    exact ((hΔP δ.2).2).symm
  · ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨δ, rfl⟩ := he₁s x
      change (((E₁.symm.trans E₂) (δ : X × Y).1 : G) : Y) ∈ ML
      rw [hφ δ δ.2]
      refine hGML _ (hΔP δ.2).1 ?_
      rw [← (hΔP δ.2).2]
      exact mem_map_of_mem ψ hx
    · intro hm
      obtain ⟨d, hd, rfl⟩ := hD2 m hm
      refine ⟨d.1, ?_, ?_⟩
      · exact (hDPL hd).2.1
      · change (((E₁.symm.trans E₂) d.1 : G) : Y) = d.2
        rw [hφ d (hDΔ hd)]
  · ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hq⟩ := hQ1 x hx
      change (((E₁.symm.trans E₂) ((x, s) : X × Y).1 : G) : Y) ∈ TM
      rw [hφ (x, s) (hQΔ hq)]
      exact hs
    · intro hs
      obtain ⟨t, ht, hq⟩ := hQ2' s hs
      refine ⟨t, ht, ?_⟩
      change (((E₁.symm.trans E₂) ((t, s) : X × Y).1 : G) : Y) = s
      rw [hφ (t, s) (hQΔ hq)]

end Fibre

end CFSG.LocalAnalysis.WeakClosure81.NF3C
