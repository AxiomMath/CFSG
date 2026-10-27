module

public import CFSG.Walter.W67.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Walter.W67

open scoped Pointwise

variable {G : Type*} [Group G]

theorem oddPart_le (Y : Subgroup G) : oddPart Y ≤ Y := Subgroup.map_subtype_le _

theorem orderOf_conj_mul (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem card_oddPart (Y : Subgroup G) :
    Nat.card (oddPart Y) = Nat.card (CFSG.pPrimeCore 2 Y) :=
  Subgroup.card_map_of_injective Y.subtype_injective

variable [Finite G]

theorem coprime_card_oddPart (Y : Subgroup G) : Nat.Coprime 2 (Nat.card (oddPart Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_oddPart]
  exact CFSG.pPrimeCore_coprime_card

theorem odd_card_oddPart (Y : Subgroup G) : Odd (Nat.card (oddPart Y)) := by
  have h := coprime_card_oddPart Y
  rw [Nat.coprime_two_left] at h
  exact h

omit [Finite G] in
theorem conj_mem_oddPart {Y : Subgroup G} {y x : G} (hy : y ∈ Y) (hx : x ∈ oddPart Y) :
    y * x * y⁻¹ ∈ oddPart Y := by
  obtain ⟨x', hx', rfl⟩ := hx
  have hN : (CFSG.pPrimeCore 2 Y).Normal := CFSG.pPrimeCore_normal (p := 2) (G := Y)
  exact ⟨⟨y, hy⟩ * x' * ⟨y, hy⟩⁻¹, hN.conj_mem _ hx' _, rfl⟩

theorem odd_orderOf_of_mem_oddPart {Y : Subgroup G} {x : G} (hx : x ∈ oddPart Y) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat (odd_card_oddPart Y) (Subgroup.orderOf_dvd_natCard _ hx)

omit [Finite G] in
theorem eq_one_of_odd_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exact absurd (Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)

theorem isInternalDirectProduct_oddPart {Y P : Subgroup G} (hPY : P ≤ Y) (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ (P.subgroupOf Y).index) (hPc : P ≤ Subgroup.centralizer (Y : Set G)) :
    JT.IsInternalDirectProduct P (oddPart Y) Y ∧
      ∀ y ∈ Y, Odd (orderOf y) → y ∈ oddPart Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup Y := P.subgroupOf Y with hP'
  have eP : P' ≃* P := Subgroup.subgroupOfEquivOfLe hPY
  have hP'2 : IsPGroup 2 P' := hP.of_equiv eP.symm
  let S : Sylow 2 Y := hP'2.toSylow hidx
  have hS : (S : Subgroup Y) = P' := hP'2.toSylow_coe hidx
  have hPcen : ∀ a ∈ P', ∀ b : Y, a * b = b * a := by
    intro a ha b
    have ha' : (a : G) ∈ P := Subgroup.mem_subgroupOf.mp ha
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hPc ha') b b.2).symm)
  have hNC : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤
      Subgroup.centralizer ((S : Subgroup Y) : Set Y) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [hS] at hm
    exact hPcen m hm n
  set N := (MonoidHom.transferSylow S hNC).ker with hNdef
  have hcomp : Subgroup.IsComplement' N S := MonoidHom.ker_transferSylow_isComplement' S hNC
  have hcardY : Nat.card N * Nat.card (S : Subgroup Y) = Nat.card Y := hcomp.card_mul_card
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N = (S : Subgroup Y).index := by
      have := (S : Subgroup Y).card_mul_index
      rw [← hcardY, mul_comm (Nat.card N)] at this
      exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos this).symm
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hNO : N ≤ CFSG.pPrimeCore 2 Y := le_sSup ⟨hNn, hNodd⟩
  have hON : CFSG.pPrimeCore 2 Y = N := by
    refine (Subgroup.eq_of_le_of_card_ge hNO (Nat.le_of_dvd Nat.card_pos ?_)).symm
    have h1 : Nat.card (CFSG.pPrimeCore 2 Y) ∣ Nat.card N * 2 ^ k := by
      rw [← hk, hcardY]
      exact Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore 2 Y)) (2 ^ k) :=
      Nat.Coprime.pow_right k (CFSG.pPrimeCore_coprime_card (p := 2) (G := Y)).symm
    exact hcop.dvd_of_dvd_mul_right h1
  have hOdef : oddPart Y = N.map Y.subtype := by rw [oddPart, hON]
  have hoddN : ∀ y ∈ Y, Odd (orderOf y) → y ∈ oddPart Y := by
    intro y hy hodd
    rw [hOdef]
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have h1 : orderOf (QuotientGroup.mk ⟨y, hy⟩ : Y ⧸ N) ∣ orderOf (⟨y, hy⟩ : Y) :=
      orderOf_map_dvd (QuotientGroup.mk' N) _
    have h2 : orderOf (QuotientGroup.mk ⟨y, hy⟩ : Y ⧸ N) ∣ 2 ^ k := by
      rw [← hk]
      have hq : Nat.card (Y ⧸ N) = Nat.card (S : Subgroup Y) := by
        have := N.card_mul_index
        rw [← hcardY, Subgroup.index] at this
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
      rw [← hq]
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    have h3 : Nat.Coprime (orderOf (QuotientGroup.mk ⟨y, hy⟩ : Y ⧸ N)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd h1))
    have h4 := Nat.Coprime.eq_one_of_dvd h3 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    exact h4
  refine ⟨⟨?_, ?_, ?_⟩, hoddN⟩
  ·
    have hsup : (S : Subgroup Y) ⊔ N = ⊤ := hcomp.symm.sup_eq_top
    have := congrArg (Subgroup.map Y.subtype) hsup
    rw [Subgroup.map_sup, ← hOdef, hS, hP', Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPY, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact this
  ·
    rw [Subgroup.disjoint_def]
    intro x hxP hxO
    exact eq_one_of_odd_of_isPGroup hP hxP (odd_orderOf_of_mem_oddPart hxO)
  · exact hPc.trans (Subgroup.centralizer_le (oddPart_le Y))

omit [Finite G] in
theorem card_eq_card_map_mul_card_inf_ker {N : Type*} [Group N] (f : G →* N) (A : Subgroup G) :
    Nat.card A = Nat.card (A.map f) * Nat.card (A ⊓ f.ker : Subgroup G) := by
  have h1 := Subgroup.card_ker_mul_card_range (f.comp A.subtype)
  have hrange : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card (f.comp A.subtype).ker = Nat.card (A ⊓ f.ker : Subgroup G) := by
    have hk : (f.comp A.subtype).ker = f.ker.subgroupOf A := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hk, ← Subgroup.inf_subgroupOf_right, inf_comm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  rw [hrange, hker] at h1
  rw [← h1, mul_comm]

omit [Finite G] in
theorem eq_or_eq_of_relIndex_prime {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (hp : (A.relIndex C).Prime) : B = A ∨ B = C := by
  have hmul := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  rw [← hmul] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr (le_antisymm hBC (Subgroup.relIndex_eq_one.mp h1))
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB)

omit [Finite G] in
theorem mem_sup_iff_of_le_normalizer {K E : Subgroup G} (hE : E ≤ Subgroup.normalizer (K : Set G))
    {x : G} : x ∈ K ⊔ E ↔ ∃ k ∈ K, ∃ e ∈ E, k * e = x := by
  let M : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ e ∈ E, k * e = x}
      one_mem' := ⟨1, K.one_mem, 1, E.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, e₁, he₁, rfl⟩ ⟨k₂, hk₂, e₂, he₂, rfl⟩
        refine ⟨k₁ * (e₁ * k₂ * e₁⁻¹), K.mul_mem hk₁
          ((Subgroup.mem_normalizer_iff.mp (hE he₁) k₂).mp hk₂), e₁ * e₂, E.mul_mem he₁ he₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨k, hk, e, he, rfl⟩
        refine ⟨e⁻¹ * k⁻¹ * e⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hE (E.inv_mem he)) k⁻¹).mp
          (K.inv_mem hk), e⁻¹, E.inv_mem he, ?_⟩
        group }
  constructor
  · intro hx
    have hle : K ⊔ E ≤ M := sup_le (fun k hk => ⟨k, hk, 1, E.one_mem, mul_one k⟩)
      (fun e he => ⟨1, K.one_mem, e, he, one_mul e⟩)
    exact hle hx
  · rintro ⟨k, hk, e, he, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he)

omit [Finite G] in
theorem card_sup_mul_card_inf_of_commute (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R ∧
    ((L ⊔ R : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hset : ((L ⊔ R : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
    rw [← hrange]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩
    · rintro ⟨l, hl, r, hr, rfl⟩
      exact ⟨(⟨l, hl⟩, ⟨r, hr⟩), rfl⟩
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  exact ⟨by rw [mul_comm]; exact this, hset⟩

end CFSG.Walter.W67
