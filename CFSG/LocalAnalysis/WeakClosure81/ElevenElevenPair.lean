module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenBlock

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_exists_conj_point {M V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (h21 : Nat.card (autI hV M) = 21)
    (h8 : Nat.card V = 8) (hA : A ≤ V) (hB : B ≤ V) (hA2 : Nat.card A = 2)
    (hB2 : Nat.card B = 2) : ∃ m ∈ M, conjSubgroup A m = B := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite (MulAut (IntMod V hV)) :=
    Finite.of_injective (fun φ : MulAut (IntMod V hV) => (φ : IntMod V hV → IntMod V hV))
      DFunLike.coe_injective
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' (G := autI hV M) 7 (by rw [h21]; norm_num)
  let ψ : MulAut (IntMod V hV) := φ
  have hψ7 : orderOf ψ = 7 := by rw [Subgroup.orderOf_coe, hφ]
  let H : Subgroup (MulAut (IntMod V hV)) := Subgroup.zpowers ψ
  have hHcard : Nat.card H = 7 := by rw [Nat.card_zpowers, hψ7]
  have hHpg : IsPGroup 7 H := IsPGroup.of_card (n := 1) (by rw [hHcard]; norm_num)
  have hXcard : Nat.card (IntMod V hV) = 8 := h8
  have hmod := hHpg.card_modEq_card_fixedPoints (IntMod V hV)
  set fp := Nat.card (MulAction.fixedPoints H (IntMod V hV)) with hfpdef
  have hfp_mod : fp % 7 = 1 := by
    have h := hmod
    rw [hXcard] at h
    change 8 % 7 = fp % 7 at h
    norm_num at h
    exact h.symm
  have hfp_le : fp ≤ 8 := by
    rw [hfpdef]
    calc Nat.card (MulAction.fixedPoints H (IntMod V hV))
        ≤ Nat.card (IntMod V hV) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 8 := hXcard
  have hfp_cases : fp = 1 ∨ fp = 8 := by
    have hle : fp < 9 := by omega
    interval_cases fp <;> omega
  have hnot8 : fp ≠ 8 := by
    intro hfp8
    have hcard8 : Nat.card (MulAction.fixedPoints H (IntMod V hV)) = 8 := by
      rw [← hfpdef]; exact hfp8
    have hbij : Function.Bijective
        (Subtype.val : MulAction.fixedPoints H (IntMod V hV) → IntMod V hV) :=
      Subtype.val_injective.bijective_of_nat_card_le (by rw [hcard8, hXcard])
    have hψ1 : ψ = 1 := by
      ext v
      obtain ⟨w, hw⟩ := hbij.2 v
      have hv : v ∈ MulAction.fixedPoints H (IntMod V hV) := hw ▸ w.2
      have hfix := (MulAction.mem_fixedPoints.1 hv) ⟨ψ, Subgroup.mem_zpowers ψ⟩
      simpa [Subgroup.smul_def, MulAut.smul_def] using hfix
    rw [hψ1] at hψ7
    simp at hψ7
  have hfp1 : fp = 1 := by
    rcases hfp_cases with h | h
    · exact h
    · exact absurd h hnot8
  have hfixed_one : ∀ v : IntMod V hV,
      v ∈ MulAction.fixedPoints H (IntMod V hV) → v = 1 := by
    intro v hv
    have hcard1 : Nat.card (MulAction.fixedPoints H (IntMod V hV)) = 1 := by
      rw [← hfpdef]; exact hfp1
    haveI : Subsingleton (MulAction.fixedPoints H (IntMod V hV)) :=
      (Nat.card_eq_one_iff_unique.1 hcard1).1
    have h1 : (1 : IntMod V hV) ∈ MulAction.fixedPoints H (IntMod V hV) := by
      rw [MulAction.mem_fixedPoints]
      intro h
      simp [Subgroup.smul_def, MulAut.smul_def]
    have := Subsingleton.elim (⟨v, hv⟩ : MulAction.fixedPoints H (IntMod V hV)) ⟨1, h1⟩
    exact congrArg Subtype.val this
  have horbit : ∀ a : IntMod V hV, a ≠ 1 →
      Nat.card (MulAction.orbit H a) = 7 := by
    intro a ha
    have hnotfix : a ∉ MulAction.fixedPoints H (IntMod V hV) :=
      fun h => ha (hfixed_one a h)
    have hne1 : Nat.card (MulAction.orbit H a) ≠ 1 := by
      intro h1
      apply hnotfix
      rw [MulAction.mem_fixedPoints]
      intro h
      haveI : Subsingleton (MulAction.orbit H a) := (Nat.card_eq_one_iff_unique.1 h1).1
      have h2 := Subsingleton.elim
        (⟨h • a, MulAction.mem_orbit a h⟩ : MulAction.orbit H a)
        (⟨a, MulAction.mem_orbit_self a⟩ : MulAction.orbit H a)
      exact congrArg Subtype.val h2
    have hdvd : Nat.card (MulAction.orbit H a) ∣ 7 := by
      have heq : Nat.card (MulAction.orbit H a) =
          Nat.card (H ⧸ MulAction.stabilizer H a) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H a)
      rw [heq, ← hHcard]
      exact Subgroup.card_quotient_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h1 | h7
    · exact absurd h1 hne1
    · exact h7
  have hAne : A ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hA2; norm_num at hA2
  have hBne : B ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hB2; norm_num at hB2
  obtain ⟨a₀, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  obtain ⟨b₀, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have ha₀A : (a₀ : G) ∈ A := a₀.2
  have hb₀B : (b₀ : G) ∈ B := b₀.2
  have ha₀V : (a₀ : G) ∈ V := hA ha₀A
  have hb₀V : (b₀ : G) ∈ V := hB hb₀B
  have ha₀1' : (a₀ : G) ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hb₀1' : (b₀ : G) ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  let a : IntMod V hV := IntMod.mk hV ⟨(a₀ : G), ha₀V⟩
  let b : IntMod V hV := IntMod.mk hV ⟨(b₀ : G), hb₀V⟩
  have ha_ne1 : a ≠ 1 := by
    intro h
    exact ha₀1' (congrArg IntMod.val h)
  have hb_ne1 : b ≠ 1 := by
    intro h
    exact hb₀1' (congrArg IntMod.val h)
  have hOcard : Nat.card (MulAction.orbit H a) = 7 := horbit a ha_ne1
  have h1notmem : (1 : IntMod V hV) ∉ MulAction.orbit H a := by
    intro hmem
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 hmem
    apply ha_ne1
    have h' : a = h⁻¹ • (1 : IntMod V hV) := by
      rw [← hh]
      exact (inv_smul_smul h a).symm
    simpa [Subgroup.smul_def, MulAut.smul_def] using h'
  have huniv : insert (1 : IntMod V hV) (MulAction.orbit H a) = Set.univ := by
    rw [Set.eq_univ_iff_ncard, Set.ncard_insert_of_notMem h1notmem, ← Nat.card_coe_set_eq,
      hOcard]
    exact hXcard.symm
  have hbmem : b ∈ MulAction.orbit H a := by
    have : b ∈ insert (1 : IntMod V hV) (MulAction.orbit H a) := by
      rw [huniv]; exact Set.mem_univ b
    rcases Set.mem_insert_iff.1 this with h | h
    · exact absurd h hb_ne1
    · exact h
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 hbmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h.2
  obtain ⟨g₀, hg₀M, hg₀conv⟩ := (mem_autI hV).1 φ.2
  let g : G := (g₀ : G) ^ k
  have hgM : g ∈ M := M.zpow_mem hg₀M k
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).zpow_mem g₀.2 k
  have hconv : convI hV ⟨g, hgN⟩ = (h : MulAut (IntMod V hV)) := by
    have hsub : (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G)) = g₀ ^ k := Subtype.ext rfl
    rw [hsub, map_zpow, hg₀conv, hk]
  have hconvab : convI hV ⟨g, hgN⟩ a = b := by
    rw [hconv]
    simpa [Subgroup.smul_def, MulAut.smul_def] using hh
  have hval : g * (a₀ : G) * g⁻¹ = (b₀ : G) := by
    have := congrArg IntMod.val hconvab
    rw [convI_apply_val] at this
    simpa [a, b, IntMod.mk, IntMod.val] using this
  have hzpA : Subgroup.zpowers (a₀ : G) = A := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha₀A) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (hV.2 (a₀ : G) ha₀V) ha₀1', hA2]
  have hzpB : Subgroup.zpowers (b₀ : G) = B := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hb₀B) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (hV.2 (b₀ : G) hb₀V) hb₀1', hB2]
  have hb₀conj : (b₀ : G) ∈ conjSubgroup A g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have hgba : g⁻¹ * (b₀ : G) * (g⁻¹)⁻¹ = (a₀ : G) := by
      rw [inv_inv, ← hval]
      group
    rw [hgba]
    exact ha₀A
  have hle : Subgroup.zpowers (b₀ : G) ≤ conjSubgroup A g⁻¹ :=
    Subgroup.zpowers_le.2 hb₀conj
  have hcardeq : Nat.card (conjSubgroup A g⁻¹) = Nat.card (Subgroup.zpowers (b₀ : G)) := by
    rw [E3.card_conjSubgroup, hA2, Nat.card_zpowers,
      orderOf_eq_prime (hV.2 (b₀ : G) hb₀V) hb₀1']
  have heq : Subgroup.zpowers (b₀ : G) = conjSubgroup A g⁻¹ :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardeq)
  exact ⟨g⁻¹, M.inv_mem hgM, heq.symm.trans hzpB⟩

theorem eleven11_exists_data_point {M V Q U L X B : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8)
    (hB : B ≤ V) (hB2 : Nat.card B = 2) :
    ∃ L' X' : Subgroup G, ∃ hd' : Eleven11Data M V Q B L' X',
      Nat.card (autI hd'.setting.isElemAbelian X') = 3 := by
  have hV := hd.setting.isElemAbelian
  have hU2 : Nat.card U = 2 := eleven11_card_U hd h8
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  obtain ⟨m, hmM, hmU⟩ :=
    eleven11_exists_conj_point hV hd.setting.normal h21 h8 hUV hB hU2 hB2
  have hUΓ : U ∈ gammaEleven M V := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hBΓ : B ∈ gammaEleven M V := by
    have := eleven_c_gamma hd.setting.normal hUΓ hmM
    rwa [hmU] at this
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hcardU := E3.card_eq_two_pow_mul hVpg hUV
  have hcardB := E3.card_eq_two_pow_mul hVpg hB
  have hpow : E3.mQuot V B = E3.mQuot V U := by
    have h1 : 2 ^ E3.mQuot V B * Nat.card B = 2 ^ E3.mQuot V U * Nat.card U := by
      rw [← hcardB, ← hcardU]
    rw [hB2, hU2] at h1
    exact Nat.pow_right_injective (le_refl 2) (Nat.mul_right_cancel (by norm_num) h1)
  have hBΔ : B ∈ deltaEleven M V := by
    refine mem_deltaEleven.2 ⟨hBΓ, ?_⟩
    rw [hpow]
    exact hd.mem_delta.2
  have hm : 1 < mBar M ⊥ V hV := by have := hd.two_lt_m; omega
  obtain ⟨L', hL'⟩ := exists_mem_elevenBlocksB hd.setting hBΓ
  have hLb' := isBlockOfInX_of_mem_elevenBlocksB hd.setting hBΓ hL'
  have hL'M : ¬ L' ≤ M := (mem_elevenBlocksB_iff.1 hL').2
  obtain ⟨-, -, -, -, -, -, -, ⟨X', hX'⟩, -⟩ :=
    eleven_ten_of_one_lt hd.setting hd.one_lt_r hm hBΔ hLb' hL'M
  let hd' : Eleven11Data M V Q B L' X' :=
    ⟨hd.setting, hd.two_lt_m, hd.one_lt_r, hd.r_lt_m, hBΔ, hL', hX'⟩
  refine ⟨L', X', hd', ?_⟩
  obtain ⟨n, -, hrn, hXn⟩ := eleven11_card_autI hd
  obtain ⟨n', -, hrn', hXn'⟩ := eleven11_card_autI hd'
  have hnn : n = n' := by
    have : (n : ℕ∞) = (n' : ℕ∞) := hrn.symm.trans hrn'
    exact_mod_cast this
  rw [hXn', ← hnn, ← hXn]
  exact h3

private theorem eleven11_inf_centralizer_congr {M V X X' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hXM : X ≤ M) (hX'M : X' ≤ M) (heq : autI hV X = autI hV X') :
    V ⊓ Subgroup.centralizer (X : Set G) = V ⊓ Subgroup.centralizer (X' : Set G) := by
  have key : ∀ v ∈ V, v ∈ Subgroup.centralizer (X : Set G) →
      v ∈ Subgroup.centralizer (X' : Set G) := by
    intro v hvV hvC
    rw [Subgroup.mem_centralizer_iff] at hvC ⊢
    intro x' hx'
    have hx'N : x' ∈ Subgroup.normalizer (V : Set G) := hMV (hX'M hx')
    have hmem : convI hV ⟨x', hx'N⟩ ∈ autI hV X' := convI_mem_autI hV hx' hx'N
    rw [← heq] at hmem
    obtain ⟨x, hxX, hxconv⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV x (IntMod.mk hV ⟨v, hvV⟩) =
        convI hV ⟨x', hx'N⟩ (IntMod.mk hV ⟨v, hvV⟩) := by rw [hxconv]
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val, convI_apply_val] at h2
    change (x : G) * v * (x : G)⁻¹ = x' * v * x'⁻¹ at h2
    have h3 : (x : G) * v * (x : G)⁻¹ = v := by
      rw [hvC (x : G) hxX]; group
    rw [h3] at h2
    exact (mul_inv_eq_iff_eq_mul).1 h2.symm
  have key' : ∀ v ∈ V, v ∈ Subgroup.centralizer (X' : Set G) →
      v ∈ Subgroup.centralizer (X : Set G) := by
    intro v hvV hvC
    rw [Subgroup.mem_centralizer_iff] at hvC ⊢
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hMV (hXM hx)
    have hmem : convI hV ⟨x, hxN⟩ ∈ autI hV X := convI_mem_autI hV hx hxN
    rw [heq] at hmem
    obtain ⟨x', hx'X, hx'conv⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV x' (IntMod.mk hV ⟨v, hvV⟩) =
        convI hV ⟨x, hxN⟩ (IntMod.mk hV ⟨v, hvV⟩) := by rw [hx'conv]
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val, convI_apply_val] at h2
    change (x' : G) * v * (x' : G)⁻¹ = x * v * x⁻¹ at h2
    have h3 : (x' : G) * v * (x' : G)⁻¹ = v := by
      rw [hvC (x' : G) hx'X]; group
    rw [h3] at h2
    exact (mul_inv_eq_iff_eq_mul).1 h2.symm
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
    exact Subgroup.mem_inf.2 ⟨hvV, key v hvV hvC⟩
  · intro v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
    exact Subgroup.mem_inf.2 ⟨hvV, key' v hvV hvC⟩

theorem eleven11_normalizes_join
    {M V Q U L X U' L' X' : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (hne : U ≠ U') :
    M ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := by
  have hV := hd.setting.isElemAbelian
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  have hX'M : X' ≤ M := hd'.isHall.1.trans inf_le_right
  have hXL : X ≤ L := hd.isHall.1.trans inf_le_left
  have hX'L' : X' ≤ L' := hd'.isHall.1.trans inf_le_left
  have hXU : V ⊓ Subgroup.centralizer (X : Set G) = U := by
    obtain ⟨n, hn, h78, hr, huniq, hD⟩ := hd.ten
    exact (hD X hd.isHall).2.2.1
  have hX'U' : V ⊓ Subgroup.centralizer (X' : Set G) = U' := by
    obtain ⟨n, hn, h78, hr, huniq, hD⟩ := hd'.ten
    exact (hD X' hd'.isHall).2.2.1
  have haut_ne : autI hV X ≠ autI hV X' := by
    intro heq
    apply hne
    rw [← hXU, ← hX'U']
    exact eleven11_inf_centralizer_congr hV hd.setting.normal hXM hX'M heq
  have hsup : autI hV X ⊔ autI hV X' = autI hV M := by
    have hle : autI hV X ⊔ autI hV X' ≤ autI hV M :=
      sup_le (autI_mono hV hXM) (autI_mono hV hX'M)
    have hdvd : Nat.card ↥(autI hV X ⊔ autI hV X') ∣ 21 := by
      rw [← h21]
      exact Subgroup.card_dvd_of_le hle
    have h3dvd : 3 ∣ Nat.card ↥(autI hV X ⊔ autI hV X') := by
      rw [← h3]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hne3 : Nat.card ↥(autI hV X ⊔ autI hV X') ≠ 3 := by
      intro hc
      apply haut_ne
      have h1 : autI hV X = autI hV X ⊔ autI hV X' :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [h3, hc]))
      have h2 : autI hV X' ≤ autI hV X := by rw [h1]; exact le_sup_right
      exact (Subgroup.eq_of_le_of_card_ge h2 (le_of_eq (by rw [h3, h3']))).symm
    have hcard21 : Nat.card ↥(autI hV X ⊔ autI hV X') = 21 := by
      obtain ⟨k, hk⟩ := h3dvd
      have hk7 : k ∣ 7 := by
        have h : 3 * k ∣ 3 * 7 := by rw [← hk]; simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).1 h
      rcases (Nat.dvd_prime Nat.prime_seven).1 hk7 with hk1 | hk7
      · exact absurd (by rw [hk, hk1, mul_one]) hne3
      · rw [hk, hk7]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard21, h21]))
  intro m hmM
  have hmN : m ∈ Subgroup.normalizer (V : Set G) := hd.setting.normal hmM
  have hXsupM : X ⊔ X' ≤ M := sup_le hXM hX'M
  have hmemM : convI hV ⟨m, hmN⟩ ∈ autI hV (X ⊔ X') := by
    have h1 : convI hV ⟨m, hmN⟩ ∈ autI hV M := convI_mem_autI hV hmM hmN
    rw [← hsup] at h1
    exact (sup_le (autI_mono hV le_sup_left) (autI_mono hV le_sup_right)) h1
  obtain ⟨g, hgX, hgconv⟩ := (mem_autI hV).1 hmemM
  have hgM : (g : G) ∈ M := hXsupM hgX
  let c : G := (g : G)⁻¹ * m
  have hcM : c ∈ M := M.mul_mem (M.inv_mem hgM) hmM
  have hcN : c ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).inv_mem g.2) hmN
  have hcCent : c ∈ Subgroup.centralizer (V : Set G) := by
    refine (convI_eq_one_iff hV ⟨c, hcN⟩).1 ?_
    have hsub : (⟨c, hcN⟩ : Subgroup.normalizer (V : Set G)) =
        g⁻¹ * ⟨m, hmN⟩ := by ext; rfl
    rw [hsub, map_mul, map_inv, hgconv, inv_mul_cancel]
  have hcInf : c ∈ M ⊓ Subgroup.centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨hcM, hcCent⟩
  have hgN : (g : G) ∈ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) :=
    (Subgroup.le_normalizer (H := L ⊔ L'))
      ((sup_le (hXL.trans le_sup_left) (hX'L'.trans le_sup_right)) hgX)
  have hcNsup : c ∈ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have h1 : conjSubgroup (L ⊔ L') c = conjSubgroup L c ⊔ conjSubgroup L' c := by
      unfold conjSubgroup
      rw [Subgroup.map_sup]
    rw [h1, conjSubgroup_eq_iff_mem_normalizer.2 (eleven11_cent_le_normalizer hd hcInf),
      conjSubgroup_eq_iff_mem_normalizer.2 (eleven11_cent_le_normalizer hd' hcInf)]
  have hm_eq : m = (g : G) * c := by
    rw [show c = (g : G)⁻¹ * m from rfl]
    group
  rw [hm_eq]
  exact (Subgroup.normalizer _).mul_mem hgN hcNsup

theorem eleven11_cent_join_eq_bot
    {M V Q U L X U' L' X' : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (hne : U ≠ U') :
    M ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) = ⊥ := by
  have hV := hd.setting.isElemAbelian
  set E : Subgroup G := L ⊔ L' with hE
  set R : Subgroup G := M ⊓ Subgroup.centralizer (E : Set G) with hR
  set O : Subgroup G := pCoreOf 2 M with hO
  set D : Subgroup G := pCoreOf 2 R with hD
  have hME : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]
    exact eleven11_normalizes_join hd hd' h21 h3 h3' hne
  have hRleM : R ≤ M := by rw [hR]; exact inf_le_left
  have hRleC : R ≤ Subgroup.centralizer (E : Set G) := by rw [hR]; exact inf_le_right
  have hRnormal : M ≤ Subgroup.normalizer (R : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [hR, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hm),
      conjSubgroup_eq_iff_mem_normalizer.2 (hME hm)]
  have hOleM : O ≤ M := by
    rw [hO]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hM_le_NGO : M ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hE_le_CR : E ≤ Subgroup.centralizer (R : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.1 (hRleC hr) e he).symm
  have hDpg : IsPGroup 2 D := by
    rw [hD]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 R
  have hOpg : IsPGroup 2 O := by
    rw [hO]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hM_le_NGD : M ≤ Subgroup.normalizer (D : Set G) := by
    rw [hD]
    exact hRnormal.trans (normalizer_le_normalizer_oTwoIn R)
  have hE_le_NGD : E ≤ Subgroup.normalizer (D : Set G) := by
    rw [hD]
    exact (hE_le_CR.trans (Subgroup.centralizer_le_normalizer (R : Set G))).trans
      (normalizer_le_normalizer_oTwoIn R)
  have hDbot : D = ⊥ := by
    by_contra hDne
    have hle : Subgroup.normalizer (D : Set G) ≤ M :=
      eleven_b hd.setting.uniqueMax hDne hDpg (inf_le_right.trans hM_le_NGD)
    exact (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
      ((le_sup_left.trans hE.ge).trans (hE_le_NGD.trans hle))
  have hROnormal : ((R ⊓ O).subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    obtain ⟨hhR, hhO⟩ := Subgroup.mem_inf.1 hh
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact R.mul_mem (R.mul_mem hk hhR) (R.inv_mem hk)
    · exact (Subgroup.mem_normalizer_iff.1 (hM_le_NGO (hRleM hk)) h).1 hhO
  have hRObot : R ⊓ O = ⊥ := by
    have hle : R ⊓ O ≤ D := by
      rw [hD]
      refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (R ⊓ O) R
        inf_le_left hROnormal ?_
      exact hOpg.to_le inf_le_right
    rw [hDbot] at hle
    exact le_bot_iff.1 hle
  have hcomm_le : ⁅R, O⁆ ≤ R ⊓ O := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro r hr o ho
      have hoN : o ∈ Subgroup.normalizer (R : Set G) := hOleM.trans hRnormal ho
      have h1 : o * r * o⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hoN r).1 hr
      have h3 : ⁅r, o⁆ = r * (o * r * o⁻¹)⁻¹ := by group
      rw [h3]
      exact R.mul_mem hr (R.inv_mem h1)
    · rw [Subgroup.commutator_le]
      intro r hr o ho
      have hrN : r ∈ Subgroup.normalizer (O : Set G) := hRleM.trans hM_le_NGO hr
      have h1 : r * o * r⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hrN o).1 ho
      have h3 : ⁅r, o⁆ = r * o * r⁻¹ * o⁻¹ := rfl
      rw [h3]
      exact O.mul_mem h1 (O.inv_mem ho)
  have hRbot : R = ⊥ := by
    have hcomm_bot : ⁅R, O⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact hcomm_le.trans (le_of_eq hRObot)
    have hR_le_CO : R ≤ Subgroup.centralizer (O : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm_bot
    have hR_le_inf : R ≤ M ⊓ Subgroup.centralizer (O : Set G) := le_inf hRleM hR_le_CO
    have hchar : M ⊓ Subgroup.centralizer (O : Set G) ≤ O := by
      rw [hO]
      exact hd.setting.charTwo M hd.setting.maxLocal.1
    have hR_le_O : R ≤ O := hR_le_inf.trans hchar
    calc R = R ⊓ O := (inf_eq_left.2 hR_le_O).symm
      _ = ⊥ := hRObot
  exact hRbot

theorem eleven11_cent_inf_cent_eq_bot
    {M V Q U L X U' L' X' : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (hd' : Eleven11Data M V Q U' L' X')
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3)
    (h3' : Nat.card (autI hd.setting.isElemAbelian X') = 3) (hne : U ≠ U') :
    (Q ⊓ Subgroup.centralizer (L : Set G)) ⊓ (Q ⊓ Subgroup.centralizer (L' : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxQ, hxL⟩ := Subgroup.mem_inf.1 hx1
  obtain ⟨-, hxL'⟩ := Subgroup.mem_inf.1 hx2
  have hxM : x ∈ M := (Subgroup.mem_inf.1 (hd.setting.sylowQ.1 hxQ)).1
  have hxSup : x ∈ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) := by
    have hL : L ≤ Subgroup.centralizer ({x} : Set G) := by
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxL l hl)
    have hL' : L' ≤ Subgroup.centralizer ({x} : Set G) := by
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxL' l hl)
    have hsup : (L ⊔ L' : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := sup_le hL hL'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy)
  have hxinf : x ∈ M ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨hxM, hxSup⟩
  rw [eleven11_cent_join_eq_bot hd hd' h21 h3 h3' hne] at hxinf
  exact hxinf

end CFSG.LocalAnalysis.WeakClosure81
