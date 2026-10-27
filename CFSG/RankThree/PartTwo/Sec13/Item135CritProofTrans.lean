module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofThree
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace TransProof

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) := fun m n =>
    hcomm m m.2 n n.2
  rw [← H.range_subtype, ← K.range_subtype, ← MonoidHom.noncommCoprod_range _ _ comm] at hx
  obtain ⟨⟨h, k⟩, rfl⟩ := hx
  exact ⟨h, h.2, k, k.2, rfl⟩

theorem mem_of_mem_wStar {A L : Subgroup G}
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    {φ : MulAut A} (hφ : φ ∈ wStar A) {x : A} (hx : (x : G) ∈ L) : ((φ x : A) : G) ∈ L := by
  obtain ⟨h, hhN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
  rw [Sec4.normalizerMonoidHom_apply_coe]
  have := (Subgroup.mem_normalizer_iff.mp (hN hhN) x).mp ⟨x.2, hx⟩
  exact this.2

theorem conj_mem_oThreeWStar {A : Subgroup G} {φ ψ : MulAut A} (hφ : φ ∈ oThreeWStar A)
    (hψ : ψ ∈ wStar A) : ψ⁻¹ * φ * ψ ∈ oThreeWStar A := by
  obtain ⟨φ', hφ', rfl⟩ := hφ
  have hN : (CFSG.pCore 3 (wStar A)).Normal := CFSG.pCore_normal
  refine ⟨⟨ψ, hψ⟩⁻¹ * φ' * ⟨ψ, hψ⟩, ?_, rfl⟩
  have := hN.conj_mem φ' hφ' (⟨ψ, hψ⟩⁻¹)
  simpa using this

@[expose] def fixLA (A L : Subgroup G) : Subgroup ↥(A ⊓ L) where
  carrier := {y | ∀ ψ ∈ oThreeWStar A, ψ ⟨y, y.2.1⟩ = ⟨y, y.2.1⟩}
  mul_mem' := by
    intro y₁ y₂ h₁ h₂ ψ hψ
    have e : (⟨((y₁ * y₂ : ↥(A ⊓ L)) : G), (y₁ * y₂).2.1⟩ : A) = ⟨y₁, y₁.2.1⟩ * ⟨y₂, y₂.2.1⟩ :=
      rfl
    rw [e, map_mul, h₁ ψ hψ, h₂ ψ hψ]
  one_mem' := by
    intro ψ hψ
    have e : (⟨((1 : ↥(A ⊓ L)) : G), (1 : ↥(A ⊓ L)).2.1⟩ : A) = 1 := rfl
    rw [e, map_one]
  inv_mem' := by
    intro y h ψ hψ
    have e : (⟨((y⁻¹ : ↥(A ⊓ L)) : G), y⁻¹.2.1⟩ : A) = (⟨y, y.2.1⟩ : A)⁻¹ := rfl
    rw [e, map_inv, h ψ hψ]

theorem mem_fixLA {A L : Subgroup G} {y : ↥(A ⊓ L)} :
    y ∈ fixLA A L ↔ ∀ ψ ∈ oThreeWStar A, ψ ⟨y, y.2.1⟩ = ⟨y, y.2.1⟩ := Iff.rfl

theorem fix_of_mem [Finite G] {A L : Subgroup G}
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (hP : IsPGroup 3 (oThreeWStar A)) (h3 : 3 ∣ Nat.card (A ⊓ L : Subgroup G))
    {φ : MulAut A} (hφ : φ ∈ oThreeWStar A) {x : A} (hx : (x : G) ∈ L) : φ x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPW : oThreeWStar A ≤ wStar A := Subgroup.map_subtype_le _
  let act : MulAction (oThreeWStar A) ↥(A ⊓ L) :=
    { smul := fun ψ y => ⟨(((ψ : MulAut A) ⟨y, y.2.1⟩ : A) : G),
        ⟨((ψ : MulAut A) ⟨y, y.2.1⟩).2, mem_of_mem_wStar hN (hPW ψ.2) y.2.2⟩⟩
      one_smul := fun y => rfl
      mul_smul := fun ψ₁ ψ₂ y => rfl }
  have hsmul : ∀ (ψ : oThreeWStar A) (y : ↥(A ⊓ L)),
      ((ψ • y : ↥(A ⊓ L)) : G) = (((ψ : MulAut A) ⟨y, y.2.1⟩ : A) : G) := fun _ _ => rfl
  have hfix : ∀ y : ↥(A ⊓ L), y ∈ MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L) ↔
      y ∈ fixLA A L := by
    intro y
    rw [MulAction.mem_fixedPoints, mem_fixLA]
    constructor
    · intro h ψ hψ
      apply Subtype.ext
      have := congrArg Subtype.val (h ⟨ψ, hψ⟩)
      rw [hsmul] at this
      exact this
    · intro h ψ
      apply Subtype.ext
      rw [hsmul, h ψ ψ.2]
  have hne : fixLA A L ≠ ⊥ := by
    have hmod := hP.card_modEq_card_fixedPoints ↥(A ⊓ L)
    have h0 : 3 ∣ Nat.card (MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L)) :=
      (Nat.modEq_zero_iff_dvd.mp ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))))
    have h1 : (1 : ↥(A ⊓ L)) ∈ MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L) :=
      (hfix 1).mpr (fixLA A L).one_mem
    have hpos : 0 < Nat.card (MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L)) :=
      Nat.card_pos_iff.mpr ⟨⟨1, h1⟩, inferInstance⟩
    have hgt : 1 < Nat.card (MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L)) := by
      obtain ⟨k, hk⟩ := h0
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hgt
    obtain ⟨⟨y, hy⟩, hy1⟩ :=
      exists_ne (⟨1, h1⟩ : MulAction.fixedPoints (oThreeWStar A) ↥(A ⊓ L))
    intro hbot
    have hyC : y ∈ fixLA A L := (hfix y).mp hy
    rw [hbot, Subgroup.mem_bot] at hyC
    exact hy1 (Subtype.ext hyC)
  have hinv : ∀ σ ∈ Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L),
      (fixLA A L).map σ.toMonoidHom = fixLA A L := by
    intro σ hσ
    obtain ⟨l, hlN, hl, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hle : (fixLA A L).map ((A ⊓ L).normalizerMonoidHom ⟨l, hlN⟩).toMonoidHom ≤
        fixLA A L := by
      rintro _ ⟨y, hy, rfl⟩
      intro ψ hψ
      set μ : MulAut A := A.normalizerMonoidHom ⟨l, hl.2⟩ with hμ
      have hμW : μ ∈ wStar A := Sec4.mem_autIn_iff.mpr ⟨l, hl.2, Subgroup.mem_top l, rfl⟩
      have hconj := (mem_fixLA.mp hy) _ (conj_mem_oThreeWStar hψ hμW)
      have h1 : ψ (μ ⟨y, y.2.1⟩) = μ ⟨y, y.2.1⟩ := by
        have := congrArg μ hconj
        simpa [MulAut.mul_apply] using this
      have h2 : (μ ⟨y, y.2.1⟩ : A) =
          ⟨((((A ⊓ L).normalizerMonoidHom ⟨l, hlN⟩).toMonoidHom y : ↥(A ⊓ L)) : G),
            (((A ⊓ L).normalizerMonoidHom ⟨l, hlN⟩).toMonoidHom y).2.1⟩ := rfl
      rw [← h2]
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rcases hirr (fixLA A L) hinv with h | h
  · exact absurd h hne
  · have hmem : (⟨x, ⟨x.2, hx⟩⟩ : ↥(A ⊓ L)) ∈ fixLA A L := h ▸ Subgroup.mem_top _
    exact (mem_fixLA.mp hmem) φ hφ

theorem exists_pow_mul_of_mem_sup' {K : Subgroup G} {c : G} (hc3 : c ^ 3 = 1)
    (hcomm : ∀ k ∈ K, c * k = k * c) {x : G} (hx : x ∈ Subgroup.zpowers c ⊔ K) :
    ∃ n < 3, ∃ k ∈ K, x = c ^ n * k := by
  have hcomm' : ∀ h ∈ Subgroup.zpowers c, ∀ k ∈ K, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hcomm k hk : Commute c k) i)).eq
  obtain ⟨h, hh, k, hk, rfl⟩ := exists_mul_of_mem_sup hcomm' hx
  have hfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hc3⟩
  obtain ⟨m, hm⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hh
  have hm : c ^ m = h := hm
  refine ⟨m % 3, Nat.mod_lt _ (by norm_num), k, hk, ?_⟩
  have hm' : c ^ m = c ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  rw [← hm, hm']

theorem sup_eq_of_card [Finite G] {A L : Subgroup G} {c : G} (hA27 : Nat.card A = 27)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcA : c ∈ A) (hcL : c ∉ L) :
    Subgroup.zpowers c ⊔ (A ⊓ L) = A := by
  set M := Subgroup.zpowers c ⊔ (A ⊓ L) with hM
  have hle : M ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
  have hd1 : 9 ∣ Nat.card M := h9 ▸ Subgroup.card_dvd_of_le le_sup_right
  have hd2 : Nat.card M ∣ 27 := hA27 ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card M ≠ 9 := by
    intro h
    have hMeq : A ⊓ L = M := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, h9])
    have hcM : c ∈ M := le_sup_left (a := Subgroup.zpowers c) (Subgroup.mem_zpowers c)
    rw [← hMeq] at hcM
    exact hcL hcM.2
  have h27 : Nat.card M = 27 := by
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hle27 : Nat.card M ≤ 27 := Nat.le_of_dvd (by norm_num) hd2
    interval_cases h : Nat.card M <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h27, hA27])

theorem mul_inv_mem_of_mem [Finite G] {A L : Subgroup G} {c : G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA3 : ∀ x ∈ A, x ^ 3 = 1) (hA27 : Nat.card A = 27)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcA : c ∈ A) (hcL : c ∉ L)
    (hexp : ∀ φ ∈ oThreeWStar A, φ ^ 3 = 1)
    (hfix : ∀ φ ∈ oThreeWStar A, ∀ x : A, (x : G) ∈ L → φ x = x) {φ : MulAut A}
    (hφ : φ ∈ oThreeWStar A) : ((φ ⟨c, hcA⟩ : A) : G) * c⁻¹ ∈ A ⊓ L := by
  have hsup := sup_eq_of_card hA27 h9 hcA hcL
  set y : G := ((φ ⟨c, hcA⟩ : A) : G) with hy
  have hyA : y ∈ A := (φ ⟨c, hcA⟩).2
  obtain ⟨n, hn, a, ha, hya⟩ := exists_pow_mul_of_mem_sup' (hA3 c hcA)
    (fun k (hk : k ∈ A ⊓ L) => hAab c hcA k (Subgroup.mem_inf.mp hk).1) (hsup.symm ▸ hyA)
  have hca : c * a = a * c := hAab c hcA a ha.1
  have hfa : φ ⟨a, ha.1⟩ = ⟨a, ha.1⟩ := hfix φ hφ ⟨a, ha.1⟩ ha.2
  interval_cases n
  ·
    exfalso
    have hy' : φ ⟨c, hcA⟩ = ⟨a, ha.1⟩ := Subtype.ext (by rw [← hy, hya, pow_zero, one_mul])
    have h1 := hfix φ⁻¹ (inv_mem hφ) ⟨a, ha.1⟩ ha.2
    have h2 : (⟨c, hcA⟩ : A) = φ⁻¹ ⟨a, ha.1⟩ := by
      rw [← hy', MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [h1] at h2
    have hca' : c = a := congrArg Subtype.val h2
    apply hcL
    rw [hca']
    exact ha.2
  · rw [hya, pow_one, hca, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  ·
    exfalso
    have hy' : φ ⟨c, hcA⟩ = ⟨c, hcA⟩ ^ 2 * ⟨a, ha.1⟩ := Subtype.ext (by rw [← hy, hya]; rfl)
    have hca2 : a * c ^ 2 = c ^ 2 * a := (Commute.pow_right (hca.symm : Commute a c) 2).eq
    have ha3 := hA3 a ha.1
    have hc3 := hA3 c hcA
    have h2 : φ (φ ⟨c, hcA⟩) = ⟨c, hcA⟩ := by
      rw [hy', map_mul, map_pow, hy', hfa]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
      calc (c ^ 2 * a) ^ 2 * a = c ^ 2 * (a * c ^ 2) * a * a := by
            rw [pow_two (c ^ 2 * a)]; group
        _ = c ^ 2 * (c ^ 2 * a) * a * a := by rw [hca2]
        _ = c * c ^ 3 * a ^ 3 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = c := by rw [hc3, ha3, mul_one, mul_one]
    have h3 : (φ ^ 3) ⟨c, hcA⟩ = φ ⟨c, hcA⟩ := by
      rw [pow_succ, MulAut.mul_apply, pow_two, MulAut.mul_apply, h2]
    rw [hexp φ hφ, MulAut.one_apply] at h3
    have h4 : c = c ^ 2 * a := by
      have := congrArg Subtype.val h3
      rw [hy'] at this
      exact this
    have haL : c⁻¹ = a := by
      calc c⁻¹ = c⁻¹ * c⁻¹ * c := by group
        _ = c⁻¹ * c⁻¹ * (c ^ 2 * a) := by rw [← h4]
        _ = a := by group
    exact hcL (inv_inv c ▸ L.inv_mem (haL ▸ ha.2))

end TransProof

open TransProof in
theorem item135A7ThreeTrans : Item135A7ThreeTrans := by
  intro G _ _ A c L hD hcL h9 hirr hN hO3 hO9 _ _ _ B hBA hcB hB9 F hFB hF3 hFL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA := hD.mem_A
  have hA27 := hD.card_eq
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hD.isElemAbelian.2
  have hP3 : IsPGroup 3 (oThreeWStar A) := IsPGroup.of_card (n := 2) (by rw [hO9]; norm_num)
  have h3 : 3 ∣ Nat.card (A ⊓ L : Subgroup G) := by rw [h9]; norm_num
  have hPW : oThreeWStar A ≤ wStar A := Subgroup.map_subtype_le _
  have hfix : ∀ φ ∈ oThreeWStar A, ∀ x : A, (x : G) ∈ L → φ x = x :=
    fun φ hφ x hx => fix_of_mem hN hirr hP3 h3 hφ hx
  have hexp : ∀ φ ∈ oThreeWStar A, φ ^ 3 = 1 := hO3.2
  have hsupA := sup_eq_of_card hA27 h9 hcA hcL
  have hfmem := fun (φ : oThreeWStar A) =>
    mul_inv_mem_of_mem hAab hA3 hA27 h9 hcA hcL hexp hfix φ.2
  set f : oThreeWStar A → ↥(A ⊓ L) := fun φ => ⟨_, hfmem φ⟩ with hfdef
  have hfinj : Function.Injective f := by
    intro φ ψ hφψ
    have hc' : (φ : MulAut A) ⟨c, hcA⟩ = (ψ : MulAut A) ⟨c, hcA⟩ := by
      apply Subtype.ext
      have h1 := congrArg Subtype.val hφψ
      simp only [hfdef] at h1
      exact mul_right_cancel h1
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hxM : (x : G) ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [hsupA]; exact x.2
    obtain ⟨n, -, a, ha, hxe⟩ := exists_pow_mul_of_mem_sup' (hA3 c hcA)
      (fun k (hk : k ∈ A ⊓ L) => hAab c hcA k (Subgroup.mem_inf.mp hk).1) hxM
    have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
    have haL : a ∈ L := (Subgroup.mem_inf.mp ha).2
    have hx' : x = ⟨c, hcA⟩ ^ n * ⟨a, haA⟩ := Subtype.ext (by rw [hxe]; rfl)
    rw [hx', map_mul, map_mul, map_pow, map_pow, hc', hfix φ φ.2 ⟨a, haA⟩ haL,
      hfix ψ ψ.2 ⟨a, haA⟩ haL]
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by rw [h9, hO9])
  obtain ⟨hBL3, hBsup⟩ := ThreeProof.card_inf_eq_three_and_sup_eq hA27 h9 hBA hB9 hcB hcL
  have hFnt : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF3]; norm_num)
  obtain ⟨⟨g, hgF⟩, hg1⟩ := exists_ne (1 : F)
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hg3 : g ^ 3 = 1 := hA3 g (hBA (hFB hgF))
  have hgcard : Nat.card (Subgroup.zpowers g) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hg3 hg1'
  have hFg : F = Subgroup.zpowers g :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgF) (by rw [hF3, hgcard])).symm
  have hgL : g ∉ L := fun h => hFL (hFg ▸ Subgroup.zpowers_le.mpr h)
  obtain ⟨n, hn, a₀, ha₀, hge⟩ := exists_pow_mul_of_mem_sup' (hA3 c hcA)
    (fun k (hk : k ∈ B ⊓ L) => hAab c hcA k (hBA (Subgroup.mem_inf.mp hk).1))
    (hBsup.symm ▸ hFB hgF)
  have hca₀ : c * a₀ = a₀ * c := hAab c hcA a₀ (hBA ha₀.1)
  obtain ⟨a, ha, hFa⟩ : ∃ a ∈ B ⊓ L, F = Subgroup.zpowers (c * a) := by
    interval_cases n
    · exact absurd (by rw [hge, pow_zero, one_mul]; exact ha₀.2) hgL
    · exact ⟨a₀, ha₀, by rw [hFg, hge, pow_one]⟩
    · refine ⟨a₀ ^ 2, pow_mem ha₀ 2, ?_⟩
      have hg2 : g ^ 2 = c * a₀ ^ 2 := by
        have hc3 := hA3 c hcA
        have hca₀2 : a₀ * c ^ 2 = c ^ 2 * a₀ := (Commute.pow_right (hca₀.symm : Commute a₀ c) 2).eq
        rw [hge]
        calc (c ^ 2 * a₀) ^ 2 = c ^ 2 * (a₀ * c ^ 2) * a₀ := by rw [pow_two]; group
          _ = c ^ 2 * (c ^ 2 * a₀) * a₀ := by rw [hca₀2]
          _ = c * c ^ 3 * a₀ ^ 2 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = c * a₀ ^ 2 := by rw [hc3, mul_one]
      rw [hFg, ← hg2]
      have heq : (g ^ 2) ^ 2 = g := by
        rw [← pow_mul]
        calc g ^ (2 * 2) = g * g ^ 3 := by group
          _ = g := by rw [hg3, mul_one]
      apply le_antisymm
      · rw [Subgroup.zpowers_le]
        have h := Subgroup.pow_mem (Subgroup.zpowers (g ^ 2)) (Subgroup.mem_zpowers (g ^ 2)) 2
        rw [heq] at h
        exact h
      · rw [Subgroup.zpowers_le]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have haL : a ∈ A ⊓ L := ⟨hBA ha.1, ha.2⟩
  obtain ⟨φ, hφ⟩ := hfbij.2 ⟨a, haL⟩
  have hφc : (((φ : MulAut A) ⟨c, hcA⟩ : A) : G) = c * a := by
    have h1 := congrArg Subtype.val hφ
    simp only [hfdef] at h1
    calc (((φ : MulAut A) ⟨c, hcA⟩ : A) : G) =
        ((((φ : MulAut A) ⟨c, hcA⟩ : A) : G) * c⁻¹) * c := by group
      _ = a * c := by rw [h1]
      _ = c * a := (hAab c hcA a haL.1).symm
  obtain ⟨w, hwN, -, hwφ⟩ := Sec4.mem_autIn_iff.mp (hPW φ.2)
  have hwx : ∀ x : A, w * (x : G) * w⁻¹ = (((φ : MulAut A) x : A) : G) := by
    intro x
    rw [← hwφ, Sec4.normalizerMonoidHom_apply_coe]
  have hwc : w * c * w⁻¹ = c * a := (hwx ⟨c, hcA⟩).trans hφc
  have hwa : ∀ x ∈ A ⊓ L, w * x * w⁻¹ = x := fun x hx =>
    (hwx ⟨x, hx.1⟩).trans (congrArg Subtype.val (hfix φ φ.2 ⟨x, hx.1⟩ hx.2))
  have hwB : w ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨m, -, a', ha', hxe⟩ := exists_pow_mul_of_mem_sup' (hA3 c hcA)
      (fun k (hk : k ∈ B ⊓ L) => hAab c hcA k (hBA (Subgroup.mem_inf.mp hk).1))
      (hBsup.symm ▸ hx)
    have h1 : w * x * w⁻¹ = (w * c * w⁻¹) ^ m * (w * a' * w⁻¹) := by
      rw [hxe, ← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
    rw [h1, hwc, hwa a' ⟨hBA ha'.1, ha'.2⟩]
    exact B.mul_mem (B.pow_mem (B.mul_mem hcB ha.1) m) ha'.1
  refine ⟨w, hwN, hwB, ?_⟩
  rw [MonoidHom.map_zpowers, hFa]
  congr 1
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc]

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13

theorem item135A7Three_of_twoLocal (hR : KS135A7TwoLocal) : Item135A7Three :=
  item135A7Three_of_inputs hR item135A7ThreeTrans

end CFSG.RankThree.PartTwo.Sec13
