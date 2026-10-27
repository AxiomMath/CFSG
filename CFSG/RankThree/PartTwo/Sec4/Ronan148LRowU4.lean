module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4OddDiag

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.RankThree.PartOne.KFU (diagU diagU_one torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.Assembly.RankThreeEven (projSU)

section NCP

theorem isSimpleGroup_projSU_of_odd {m : ℕ} (hm1 : 1 < m) : IsSimpleGroup (projSU 3 2 m) :=
  Item462AltProof.isSimpleGroup_projSU_three 2 m (by omega) (by
    intro h
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)

theorem noCommNormalPair3_of_cover {Y : Type*} [Group Y] [Finite Y] {m : ℕ} (hmo : Odd m)
    (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : NoCommNormalPair3 Y := by
  intro N₁ N₂ h₁ h₂ hc a ha ha1 ha3 b hb hb1 hb3
  haveI : IsSimpleGroup (projSU 3 2 m) := isSimpleGroup_projSU_of_odd hm1
  have hM : ∀ M : Subgroup Y, M.Normal → ∀ c ∈ M, c ≠ 1 → c ^ 3 = 1 → M.map π = ⊤ := by
    intro M hMn c hc hc1 hc3
    haveI : (M.map π).Normal := hMn.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with h | h
    · exfalso
      have hmem : π c ∈ M.map π := Subgroup.mem_map_of_mem _ hc
      rw [h, Subgroup.mem_bot] at hmem
      have hck : c ∈ π.ker := hmem
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
      have h3 : orderOf c ∣ Nat.card π.ker := by
        rw [← Subgroup.orderOf_mk c hck]
        exact orderOf_dvd_natCard _
      rw [ho] at h3
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hker) h3
      omega
    · exact h
  have hT₁ := hM N₁ h₁ a ha ha1 ha3
  have hT₂ := hM N₂ h₂ b hb hb1 hb3
  obtain ⟨u, w, huw⟩ := exists_not_commute_projSU hmo
  apply huw
  have hu : u ∈ N₁.map π := hT₁ ▸ Subgroup.mem_top u
  have hw : w ∈ N₂.map π := hT₂ ▸ Subgroup.mem_top w
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨w', hw', rfl⟩ := hw
  rw [← map_mul, ← map_mul, hc u' hu' w' hw']

end NCP

section SU4

theorem isSimpleGroup_unitarySU_four' {k : ℕ} {F : Type} [Field F]
    (h₀ : UnitaryFieldData 2 k F) : IsSimpleGroup (unitarySU 2 k F 4) := by
  have := h₀.finite
  have hbot : unitaryScalars h₀ 4 = ⊥ := by
    rw [unitaryScalars_eq h₀ (by norm_num)]
    have hodd : Odd (2 ^ k + 1) :=
      (Nat.even_pow.mpr ⟨even_two, by have := h₀.one_le; omega⟩).add_one
    have hcop : Nat.Coprime 4 (2 ^ k + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    exact CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot
      (by rw [h₀.card, ← pow_mul, mul_comm]) (by norm_num) hcop
  haveI := CFSG.SeitzReduction.UnitaryPilot.isSimpleGroup_unitaryPSU_of_three_le h₀
    (n := 4) (by norm_num) (by simp)
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem padicValNat_ordSU4_two_pow {k : ℕ} (hk : 1 ≤ k) :
    padicValNat 2 ((2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1))) =
      6 * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  have h1 : Odd ((2 ^ k) ^ 2 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have h2 : Odd ((2 ^ k) ^ 3 + 1) := ((Nat.even_pow' (by norm_num)).mpr hq).add_one
  have h3 : Odd ((2 ^ k) ^ 4 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have hodd := (h1.mul h2).mul h3
  rw [padicValNat.mul (by positivity) hodd.pos.ne',
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero, ← pow_mul,
    padicValNat.prime_pow, mul_comm]

theorem false_of_su4_cover {k : ℕ} {F : Type} [Field F] (h₀ : UnitaryFieldData 2 k F)
    {G : Type*} [Group G] {C Y : Subgroup G} (eC : C ≃* unitarySU 2 k F 4) (hYC : Y ≤ C)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf C).IsSubnormal) {m : ℕ} (hmo : Odd m)
    (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π) : False := by
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have hU1 := one_lt_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  haveI : IsSimpleGroup (unitarySU 2 k F 4) := isSimpleGroup_unitarySU_four' h₀
  haveI hCs : IsSimpleGroup C := eC.isSimpleGroup
  have hcardC : Nat.card C =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
    rw [Nat.card_congr eC.toEquiv, Item419Res3.card_unitarySU_four h₀]
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hCs hsub with h | h
  ·
    have hY1 : Y = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : (⟨y, hYC hy⟩ : C) ∈ Y.subgroupOf C := hy
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    rw [hY1, Subgroup.card_bot] at hdU
    have := Nat.le_of_dvd (by norm_num) hdU
    omega
  ·
    have hYeq : Y = C := by
      refine le_antisymm hYC fun y hy => ?_
      have : (⟨y, hy⟩ : C) ∈ Y.subgroupOf C := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
    have eY : Y ≃* C := MulEquiv.subgroupCongr hYeq
    haveI : IsSimpleGroup Y := eY.isSimpleGroup
    have hcY := card_eq_of_isSimpleGroup_surj π hπ hU1
    have hv := padicValNat_ordSU4_two_pow h₀.one_le
    rw [← hcardC, ← Nat.card_congr eY.toEquiv, hcY, hU] at hv
    obtain ⟨j, rfl⟩ := hmo
    omega

end SU4

section Inner

theorem false_of_u4OddInner {n : ℕ} (hn : Odd n) {S : Type} [Group S] [Finite S]
    (eS : S ≃* projSU 4 2 n) {x : S} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {K : Subgroup S}
    (hxK : ∀ k ∈ K, x * k = k * x) [Group.IsPerfect K] {E : Subgroup S} (hEK : E ≤ K)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hEZ : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) (hNCP : NoCommNormalPair3 K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  have hxKc : ∀ k ∈ K, Commute x k := hxK
  have hxE : ∀ a ∈ E, ∀ i : ℤ, a * x ^ i = x ^ i * a := fun a ha i =>
    ((hxKc a (hEK ha)).zpow_left i).symm.eq
  have hxi3 : ∀ i : ℤ, (x ^ i) ^ 3 = 1 := by
    intro i
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  have hcomm : ∀ (a : E) (b : Subgroup.zpowers x),
      Commute (E.subtype a) ((Subgroup.zpowers x).subtype b) := by
    rintro ⟨a, ha⟩ ⟨_, i, rfl⟩
    exact ((hxKc a (hEK ha)).zpow_left i).symm
  set F : Subgroup S := (E.subtype.noncommCoprod (Subgroup.zpowers x).subtype hcomm).range
    with hF
  have hFmem : ∀ y ∈ F, ∃ a ∈ E, ∃ i : ℤ, a * x ^ i = y := by
    rintro y ⟨⟨⟨a, ha⟩, ⟨_, i, rfl⟩⟩, rfl⟩
    exact ⟨a, ha, i, rfl⟩
  have hEF : E ≤ F := fun a ha => ⟨(⟨a, ha⟩, 1), by simp⟩
  have hxF : x ∈ F := ⟨(1, ⟨x, Subgroup.mem_zpowers x⟩), by simp⟩
  have hFexp : ∀ y ∈ F, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨a, ha, i, rfl⟩ := hFmem y hy
    rw [((hxKc a (hEK ha)).zpow_left i).symm.mul_pow, hE3 a ha, hxi3 i, one_mul]
  have hFcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := by
    intro y hy z hz
    obtain ⟨a, ha, i, rfl⟩ := hFmem y hy
    obtain ⟨b, hb, j, rfl⟩ := hFmem z hz
    have h1 : x ^ i * b = b * x ^ i := (hxE b hb i).symm
    have h2 : x ^ j * a = a * x ^ j := (hxE a ha j).symm
    have h3 : a * b = b * a := hEc a ha b hb
    have h4 : x ^ i * x ^ j = x ^ j * x ^ i := (Commute.zpow_zpow_self x i j).eq
    calc a * x ^ i * (b * x ^ j) = a * (x ^ i * b) * x ^ j := by group
      _ = a * b * (x ^ i * x ^ j) := by rw [h1]; group
      _ = b * a * (x ^ j * x ^ i) := by rw [h3, h4]
      _ = b * (x ^ j * a) * x ^ i := by rw [h2]; group
      _ = b * x ^ j * (a * x ^ i) := by group
  set Lf := GaloisField 2 (2 * n) with hLf
  have hU : UnitaryFieldData 2 n Lf := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eS.symm) F hFexp hFcomm
  have hFT : ∀ y ∈ F, ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) ∈ torusSU 3 4 Lf :=
    fun y hy => hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hy)
  obtain ⟨v, hv3, hvp, hvx⟩ := mem_torusSU_iff.mp (hFT x hxF)
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : ψ.symm x = 1 := Subtype.ext (by rw [← hvx, diagU_one]; rfl)
    rw [← ψ.apply_symm_apply x, h1, map_one]
  have hdvd : 3 ∣ Nat.card Lf - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨π, ω, hω3, hω1, hnf⟩ := Item419Res3.exists_perm_normal_form hζ hv3 hvp hv1
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  set P : GL (Fin 4) Lf := permGL π with hP
  have hPU : P ∈ unitarySU 2 n Lf 4 := permGL_mem_unitarySU hU π
  set ρ : S →* GL (Fin 4) Lf := (MulAut.conj P).toMonoidHom.comp
    ((unitarySU 2 n Lf 4).subtype.comp ψ.symm.toMonoidHom) with hρ
  have hρapp : ∀ y, ρ y = P * ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) * P⁻¹ :=
    fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y z h
    rw [hρapp, hρapp] at h
    exact ψ.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h)))
  have hρU : ∀ y, ρ y ∈ unitarySU 2 n Lf 4 := fun y =>
    mul_mem (mul_mem hPU (ψ.symm y).2) (inv_mem hPU)
  have hρx : ρ x = diagU (v ∘ π.symm) := by
    rw [hρapp, ← hvx]
    exact permGL_conj_diagU π v
  have hρT : ∀ y ∈ F, ρ y ∈ torusSU 3 4 Lf := by
    intro y hy
    obtain ⟨d, hd3, hdp, hdy⟩ := mem_torusSU_iff.mp (hFT y hy)
    refine mem_torusSU_iff.mpr ⟨d ∘ π.symm, fun i => hd3 _, ?_, ?_⟩
    · rw [← hdp]
      exact Equiv.prod_comp π.symm d
    · rw [hρapp, ← hdy]
      exact (permGL_conj_diagU π d).symm
  set K₂ : Subgroup (GL (Fin 4) Lf) := K.map ρ with hK₂
  set E₂ : Subgroup (GL (Fin 4) Lf) := E.map ρ with hE₂
  have hK₂U : K₂ ≤ unitarySU 2 n Lf 4 := by
    rintro _ ⟨k, -, rfl⟩
    exact hρU k
  have hK₂C : K₂ ≤ Subgroup.centralizer {ρ x} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxK k hk]
  have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hE₂K : E₂ ≤ K₂ := Subgroup.map_mono hEK
  have hE₂9 : Nat.card E₂ = 9 := by rw [hE₂, Subgroup.card_map_of_injective hρinj, hE9]
  have hE₂T : E₂ ≤ torusSU 3 4 Lf := by
    rintro _ ⟨e, he, rfl⟩
    exact hρT e (hEF he)
  have hE₂Z : ∀ z ∈ E₂, (∀ k ∈ K₂, z * k = k * z) → z = 1 := by
    rintro _ ⟨e, he, rfl⟩ hc
    have : e = 1 := hEZ e he (fun k hk => hρinj (by
      rw [map_mul, map_mul]
      exact hc _ ⟨k, hk, rfl⟩))
    rw [this, map_one]
  have hNCP₂ : NoCommNormalPair3 K₂ :=
    noCommNormalPair3_of_mulEquiv (K.equivMapOfInjective ρ hρinj) hNCP
  rw [hρx] at hK₂C
  rcases hnf with hA | hB | hC
  · rw [hA] at hK₂C
    exact falseA hω3 hω1 hK₂C hK₂p hE₂K hE₂9 hE₂T hE₂Z
  · rw [hB] at hK₂C
    exact falseB hω1 hω2 hK₂C hK₂p hE₂K hE₂9 hE₂T
  · rw [hC] at hK₂C
    exact falseC hU hω2 (le_inf hK₂U hK₂C) hK₂p hE₂K hE₂9 hE₂T hNCP₂

end Inner

section Row


theorem rowU3_U4 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n) (eS : S ≃* projSU 4 2 n)
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, σ k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  have hZ := center_trivial_of_isSimpleGroup hs hna
  set α := MulAut.congr eS σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut σ
  · rcases Nat.even_or_odd n with hev | hodd
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hmod : 2 ^ n % 3 = 1 := by
        obtain ⟨j, rfl⟩ := hev
        rw [← two_mul, pow_mul]
        norm_num [Nat.pow_mod]
      have hrank := Sec4.HeringUnitary.pRank_projSU_four_le_two (p := 2) (by norm_num) hn hmod
      have hcen := Sec4.RonanK432.center_projSU_four_two_eq_bot hn
      refine false_of_fix_e9 (MulAut.conj : S →* MulAut S).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
        hσ3 hσ1 hEY hEc hE3 hE9 hfix hEZ
      intro B hB h3B hcB
      refine card_le_nine_inn (fun E' hE' h27 => ?_) hZ hB h3B hcB
      set ψ : S →* projSU 4 2 n ⧸ Subgroup.center (projSU 4 2 n) :=
        (QuotientGroup.mk' (Subgroup.center (projSU 4 2 n))).comp eS.toMonoidHom with hψ
      have hψinj : Function.Injective ψ := by
        intro x y hxy
        have h1 := QuotientGroup.eq.mp hxy
        rw [hcen, Subgroup.mem_bot] at h1
        exact eS.injective (inv_mul_eq_one.mp h1)
      refine Sec4.Item434Spor.noE27_of_pRank_le_two hrank (E'.map ψ) ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩ ?_
      · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, ← map_mul]
        exact congrArg ψ (congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hE'.2 x hx, map_one]
      · rw [Subgroup.card_map_of_injective hψinj, h27]
    ·
      obtain ⟨x, rfl⟩ := hin
      have hx3 : x ^ 3 = 1 := by
        apply hZ
        intro t
        have h2 := congrArg (fun φ : MulAut S => φ t) (show MulAut.conj (x ^ 3) = 1 by
          rw [map_pow]; exact hσ3)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc x ^ 3 * t = x ^ 3 * t * (x ^ 3)⁻¹ * x ^ 3 := by group
          _ = t * x ^ 3 := by rw [h2]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hσ1 (map_one _)
      have hxY : ∀ k ∈ Y, x * k = k * x := by
        intro k hk
        have h1 : MulAut.conj x k = k := hfix k hk
        rw [MulAut.conj_apply] at h1
        calc x * k = x * k * x⁻¹ * x := by group
          _ = k * x := by rw [h1]
      exact false_of_u4OddInner hodd eS hx3 hx1 hxY hEY hEc hE3 hE9 hEZ
        (noCommNormalPair3_of_cover hmo hm1 π hπ hker)
  ·
    have hαout : ¬ IsInnerAut α := fun h => hin ((isInnerAut_congr eS σ).mp h)
    obtain ⟨k, -, -, F, _, h₀, ⟨eα⟩⟩ := exists_autFix_mulEquiv_unitarySU_four hn hα3 hαout
    exact false_of_su4_cover h₀ ((Sec4.autFixCongrEquiv eS σ).symm.trans eα) hYC hsub hmo hm1
      π hπ

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
