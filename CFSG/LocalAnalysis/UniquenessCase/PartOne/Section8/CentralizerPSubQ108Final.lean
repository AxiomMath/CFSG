module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.GammaQ108Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.L34SylowExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Q8108
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69Setup4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_center_map_of_mem_normalizer {R : Subgroup G} {a z : G}
    (han : a ∈ Subgroup.normalizer (R : Set G))
    (hz : z ∈ (Subgroup.center ↥R).map R.subtype) :
    a * z * a⁻¹ ∈ (Subgroup.center ↥R).map R.subtype := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
  have hazR : a * (c : G) * a⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp han (c : G)).1 c.2
  refine Subgroup.mem_map.mpr ⟨⟨a * (c : G) * a⁻¹, hazR⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro s
  apply Subtype.ext
  have h1 : a⁻¹ * (s : G) * a ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (R : Set G)).inv_mem han) (s : G)).1 s.2
    simpa using h
  have h2 : (a⁻¹ * (s : G) * a) * (c : G) = (c : G) * (a⁻¹ * (s : G) * a) := by
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hc ⟨a⁻¹ * (s : G) * a, h1⟩)
    simpa using h
  show (s : G) * (a * (c : G) * a⁻¹) = (a * (c : G) * a⁻¹) * (s : G)
  calc (s : G) * (a * (c : G) * a⁻¹)
      = a * ((a⁻¹ * (s : G) * a) * (c : G)) * a⁻¹ := by group
    _ = a * ((c : G) * (a⁻¹ * (s : G) * a)) * a⁻¹ := by rw [h2]
    _ = (a * (c : G) * a⁻¹) * (s : G) := by group

theorem le_normalizer_center_map (R : Subgroup G) :
    R ≤ Subgroup.normalizer ((Subgroup.center ↥R).map R.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro r hr k hk
  exact conj_mem_center_map_of_mem_normalizer (Subgroup.le_normalizer hr) hk

theorem le_normalizer_center_map_of_le_normalizer {R A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (R : Set G)) :
    A ≤ Subgroup.normalizer ((Subgroup.center ↥R).map R.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha k hk
  exact conj_mem_center_map_of_mem_normalizer (hAN ha) hk

theorem exists_elemAbelian_27_and_nine_le_centralizer_of_two_extraspecial_order_three
    {R R' A : Subgroup G}
    (hR : CFSG.IsExtraspecial 3 R) (hR' : CFSG.IsExtraspecial 3 R')
    (hRcard : Nat.card R = 27) (hR'card : Nat.card R' = 27)
    (hRexp : ∀ x : ↥R, x ^ 3 = 1) (hR'exp : ∀ x : ↥R', x ^ 3 = 1)
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r)
    (hZeq : (Subgroup.center ↥R).map R.subtype = (Subgroup.center ↥R').map R'.subtype)
    (hAcard : Nat.card A = 3)
    (hAN : A ≤ Subgroup.normalizer (R : Set G))
    (hAN' : A ≤ Subgroup.normalizer (R' : Set G)) :
    ∃ B E : Subgroup G, B ≤ R ⊔ R' ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 27 ∧
      (Subgroup.center ↥R).map R.subtype ≤ B ∧
      E ≤ B ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ a ∈ A, ∀ z ∈ (Subgroup.center ↥R).map R.subtype, a * z = z * a) ∧
      (∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ (Subgroup.center ↥R).map R.subtype) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup G := (Subgroup.center ↥R).map R.subtype with hZdef
  have hZ' : Z = (Subgroup.center ↥R').map R'.subtype := hZdef.trans hZeq
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective R.subtype_injective]
    exact hR.center_order_p
  have hZR : Z ≤ R := hZdef ▸ Subgroup.map_subtype_le _
  have hZR' : Z ≤ R' := by rw [hZ']; exact Subgroup.map_subtype_le _
  have hZlt : Z < R := by
    refine lt_of_le_of_ne hZR ?_
    intro h
    have hc : Nat.card ↥Z = Nat.card ↥R := by rw [h]
    rw [hZcard, hRcard] at hc
    norm_num at hc
  have hZ'lt : Z < R' := by
    refine lt_of_le_of_ne hZR' ?_
    intro h
    have hc : Nat.card ↥Z = Nat.card ↥R' := by rw [h]
    rw [hZcard, hR'card] at hc
    norm_num at hc
  have hRinfR' : R ⊓ R' = Z := by
    apply le_antisymm
    · intro y hy
      have hycent : (⟨y, hy.1⟩ : ↥R) ∈ Subgroup.center ↥R := by
        rw [Subgroup.mem_center_iff]
        intro s
        apply Subtype.ext
        show (s : G) * y = y * (s : G)
        exact hcomm (s : G) s.property y hy.2
      exact hZdef ▸ Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hycent, rfl⟩
    · exact le_inf hZR hZR'
  have hApg : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
  have hRpg : IsPGroup 3 R := hR.isPGroup
  have hR'pg : IsPGroup 3 R' := hR'.isPGroup
  have hQK : R ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]; exact le_normalizer_center_map R
  have hQK' : R' ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ']; exact le_normalizer_center_map R'
  obtain ⟨x, hxR, hxZ, hxcomm⟩ :=
    CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
      (p := 3) (P := A) (Q := R) (K₀ := Z) hApg hRpg hZlt hQK hAN
      (le_normalizer_center_map_of_le_normalizer (R := R) hAN)
  obtain ⟨x', hx'R', hx'Z, hx'comm⟩ :=
    CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
      (p := 3) (P := A) (Q := R') (K₀ := Z) hApg hR'pg hZ'lt hQK' hAN'
      (by rw [hZ']; exact le_normalizer_center_map_of_le_normalizer (R := R') hAN')
  have hx3 : x ^ 3 = 1 := by
    have h := hRexp ⟨x, hxR⟩
    simpa using congrArg Subtype.val h
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hx'3 : x' ^ 3 = 1 := by
    have h := hR'exp ⟨x', hx'R'⟩
    simpa using congrArg Subtype.val h
  have hx'1 : x' ≠ 1 := fun h => hx'Z (h ▸ Z.one_mem)
  have hx'ord : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have hZx_inf : Z ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers x) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have hle : Z ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (by rw [h, Nat.card_zpowers, hxord])
      have hxmem : x ∈ Z ⊓ Subgroup.zpowers x := by
        rw [hle]; exact Subgroup.mem_zpowers x
      exact hxZ hxmem.1
  have hZx_comm : ∀ z ∈ Z, z * x = x * z := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp (hZdef ▸ hz)
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hxR⟩)
    simpa using h.symm
  obtain ⟨hW_ea, hWcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3) hZcard hxord hxZ hZx_comm
  have hWleR : Z ⊔ Subgroup.zpowers x ≤ R :=
    sup_le hZR (Subgroup.zpowers_le.mpr hxR)
  have hx'W : x' ∉ Z ⊔ Subgroup.zpowers x := by
    intro hmem
    have hx'R : x' ∈ R := hWleR hmem
    have hmemZ : x' ∈ R ⊓ R' := ⟨hx'R, hx'R'⟩
    rw [hRinfR'] at hmemZ
    exact hx'Z hmemZ
  have hWcomm_x' : ∀ b ∈ Z ⊔ Subgroup.zpowers x, ∀ w ∈ Subgroup.zpowers x',
      b * w = w * b := by
    intro b hb w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (hcomm b (hWleR hb) x' hx'R') n).eq
  set B : Subgroup G := Z ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers x' with hBdef
  have hB_ea : CFSG.Open.IsElemAbelian 3 B := by
    rw [hBdef]
    exact CFSG.Open.IsElemAbelian.sup_of_commute hW_ea
      (CFSG.Open.isElemAbelian_zpowers hx'3) hWcomm_x'
  have hBcard : Nat.card B = 27 := by
    have hBinf : (Z ⊔ Subgroup.zpowers x) ⊓ Subgroup.zpowers x' = ⊥ := by
      have hdvd : Nat.card ↥((Z ⊔ Subgroup.zpowers x) ⊓ Subgroup.zpowers x') ∣ 3 := by
        have hZc : Nat.card (Subgroup.zpowers x') = 3 := by rw [Nat.card_zpowers, hx'ord]
        rw [← hZc]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exfalso
        have hle : (Z ⊔ Subgroup.zpowers x) ⊓ Subgroup.zpowers x' = Subgroup.zpowers x' :=
          Subgroup.eq_of_le_of_card_ge inf_le_right
            (by rw [h, Nat.card_zpowers, hx'ord])
        have hx'mem : x' ∈ (Z ⊔ Subgroup.zpowers x) ⊓ Subgroup.zpowers x' := by
          rw [hle]; exact Subgroup.mem_zpowers x'
        exact hx'W hx'mem.1
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := Z ⊔ Subgroup.zpowers x) (B := Subgroup.zpowers x') hWcomm_x'
    rw [hBinf, Subgroup.card_bot, hWcard, Nat.card_zpowers, hx'ord] at h
    rw [hBdef]
    simpa using h
  have hBabel : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hB_ea.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hZleB : Z ≤ B := by
    rw [hBdef]; exact le_sup_left.trans le_sup_left
  have hxleB : Subgroup.zpowers x ≤ B := by
    rw [hBdef]; exact le_sup_right.trans le_sup_left
  have hx'leB : Subgroup.zpowers x' ≤ B := by
    rw [hBdef]; exact le_sup_right
  have hxS : x ∈ B := hxleB (Subgroup.mem_zpowers x)
  have hx'S : x' ∈ B := hx'leB (Subgroup.mem_zpowers x')
  have hBle : B ≤ R ⊔ R' := by
    rw [hBdef]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hZR.trans le_sup_left
    · exact (Subgroup.zpowers_le.mpr hxR).trans le_sup_left
    · exact (Subgroup.zpowers_le.mpr hx'R').trans le_sup_right
  have hANZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_center_map_of_le_normalizer (R := R) hAN
  have hZabel : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := by
    intro u hu v hv
    obtain ⟨cu, hcu, rfl⟩ := Subgroup.mem_map.mp (hZdef ▸ hu)
    obtain ⟨cv, hcv, rfl⟩ := Subgroup.mem_map.mp (hZdef ▸ hv)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcv ⟨cu, cu.2⟩)
  have hcardAZ := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf
    (A := Z) (B := A) hANZ
  rw [hZcard, hAcard] at hcardAZ
  have hinf_dvd : Nat.card ↥(Z ⊓ A) ∣ 3 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcardAZ_cases : Nat.card ↥(Z ⊔ A) = 3 ∨ Nat.card ↥(Z ⊔ A) = 9 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hinf_dvd with h1 | h3
    · have := hcardAZ; rw [h1, mul_one] at this; omega
    · have := hcardAZ; rw [h3] at this; omega
  have hAZ_comm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := by
    intro a ha z hz
    have hcomm_sup : IsMulCommutative ↥(Z ⊔ A) := by
      rcases hcardAZ_cases with h3 | h9
      · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact (isCyclic_of_card_dvd_prime (p := 3) (by rw [h3])).isMulCommutative
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [h9]; norm_num)
    exact congrArg Subtype.val (hcomm_sup.is_comm.comm
      ⟨a, Subgroup.mem_sup_right ha⟩ ⟨z, Subgroup.mem_sup_left hz⟩)
  have hAne : ∃ a ∈ A, a ≠ 1 := by
    haveI : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAcard]; norm_num)
    obtain ⟨⟨a, ha⟩, hane⟩ := exists_ne (1 : ↥A)
    exact ⟨a, ha, fun h => hane (Subtype.ext h)⟩
  obtain ⟨a, ha, ha1⟩ := hAne
  have ha3 : a ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
    simpa [hAcard] using congrArg Subtype.val h
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hagen : A = Subgroup.zpowers a := by
    symm
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
      (by rw [Nat.card_zpowers, haord, hAcard])
  have hacent : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer (A : Set G) := by
    rw [hagen]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hZ_mem_S : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := by
    intro z hz
    exact conj_mem_center_map_of_mem_normalizer (R := R) (hAN ha) (hZdef ▸ hz)
  let S : Subgroup G :=
    { carrier := {b | b ∈ B ∧ ⁅a, b⁆ ∈ Z}
      one_mem' := ⟨B.one_mem, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, hz₁⟩ ⟨hb₂, hz₂⟩
        have hz₂B : ⁅a, b₂⁆ ∈ B := hZleB hz₂
        refine ⟨B.mul_mem hb₁ hb₂, ?_⟩
        have h1 : a * b₁ * a⁻¹ = ⁅a, b₁⁆ * b₁ := by
          simp only [commutatorElement_def]; group
        have h2 : a * b₂ * a⁻¹ = ⁅a, b₂⁆ * b₂ := by
          simp only [commutatorElement_def]; group
        have h3 : a * (b₁ * b₂) * a⁻¹ = ⁅a, b₁⁆ * ⁅a, b₂⁆ * (b₁ * b₂) := by
          calc a * (b₁ * b₂) * a⁻¹ = (a * b₁ * a⁻¹) * (a * b₂ * a⁻¹) := by group
            _ = (⁅a, b₁⁆ * b₁) * (⁅a, b₂⁆ * b₂) := by rw [h1, h2]
            _ = ⁅a, b₁⁆ * ⁅a, b₂⁆ * (b₁ * b₂) := by
                rw [mul_assoc (⁅a, b₁⁆), mul_assoc (⁅a, b₁⁆), ← mul_assoc b₁,
                  hBabel b₁ hb₁ ⁅a, b₂⁆ hz₂B, mul_assoc]
        have h4 : (⁅a, b₁⁆ * ⁅a, b₂⁆ * (b₁ * b₂)) * (b₁ * b₂)⁻¹ =
            ⁅a, b₁⁆ * ⁅a, b₂⁆ := by group
        rw [commutatorElement_def, h3, h4]
        exact Z.mul_mem hz₁ hz₂
      inv_mem' := by
        rintro b ⟨hb, hz⟩
        have hzB : ⁅a, b⁆ ∈ B := hZleB hz
        refine ⟨B.inv_mem hb, ?_⟩
        have h1 : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅b, a⁆ * b := commutatorElement_inv_right a b
        have h2 : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := (commutatorElement_inv a b).symm
        rw [h1, h2]
        have h3 : b⁻¹ * ⁅a, b⁆⁻¹ * b = ⁅a, b⁆⁻¹ := by
          rw [hBabel b⁻¹ (B.inv_mem hb) ⁅a, b⁆⁻¹ (B.inv_mem hzB)]
          group
        rw [h3]
        exact Z.inv_mem hz }
  have hleS : B ≤ S := by
    rw [hBdef]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · intro z hz
        exact ⟨hZleB hz, by
          rw [commutatorElement_def]
          exact Z.mul_mem (hZ_mem_S z hz) (Z.inv_mem hz)⟩
      · exact Subgroup.zpowers_le.mpr ⟨hxS, hxcomm a ha⟩
    · exact Subgroup.zpowers_le.mpr ⟨hx'S, hx'comm a ha⟩
  have hSB : ∀ b ∈ B, ⁅a, b⁆ ∈ Z := fun b hb => (hleS hb).2
  have hABZ : ∀ a' ∈ A, ∀ b ∈ B, ⁅a', b⁆ ∈ Z := by
    intro a' ha' b hb
    have hab : ⁅a, b⁆ ∈ Z := hSB b hb
    have hcomm_a : Commute a ⁅a, b⁆ := by
      show a * ⁅a, b⁆ = ⁅a, b⁆ * a
      exact hAZ_comm a ha ⁅a, b⁆ hab
    have ha2 : a ^ 2 = a⁻¹ := by
      have h : a * a ^ 2 = 1 := by rw [← pow_succ']; exact ha3
      exact eq_inv_of_mul_eq_one_right h
    by_cases ha'1 : a' = 1
    · subst ha'1
      simp [commutatorElement_def]
    · rcases CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
        haord (hagen ▸ ha') ha'1 with h | h
      · subst h
        exact hab
      · subst h
        have hpow := hcomm_a.commutatorElement_pow_left 2
        rw [ha2] at hpow
        rw [← hpow]
        exact Z.pow_mem hab 2
  let φ : ↥B →* ↥Z :=
    { toFun := fun b => ⟨⁅a, (b : G)⁆, hSB b b.2⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro b₁ b₂
        apply Subtype.ext
        change a * ((b₁ : G) * (b₂ : G)) * a⁻¹ * ((b₁ : G) * (b₂ : G))⁻¹ =
          ⁅a, (b₁ : G)⁆ * ⁅a, (b₂ : G)⁆
        have hz₂B : ⁅a, (b₂ : G)⁆ ∈ B := hZleB (hSB b₂ b₂.2)
        have h1 : a * (b₁ : G) * a⁻¹ = ⁅a, (b₁ : G)⁆ * b₁ := by
          simp only [commutatorElement_def]; group
        have h2 : a * (b₂ : G) * a⁻¹ = ⁅a, (b₂ : G)⁆ * b₂ := by
          simp only [commutatorElement_def]; group
        have h3 : a * ((b₁ : G) * b₂) * a⁻¹ =
            ⁅a, (b₁ : G)⁆ * ⁅a, (b₂ : G)⁆ * ((b₁ : G) * b₂) := by
          calc a * ((b₁ : G) * b₂) * a⁻¹ =
              (a * (b₁ : G) * a⁻¹) * (a * (b₂ : G) * a⁻¹) := by group
            _ = (⁅a, (b₁ : G)⁆ * b₁) * (⁅a, (b₂ : G)⁆ * b₂) := by rw [h1, h2]
            _ = ⁅a, (b₁ : G)⁆ * ⁅a, (b₂ : G)⁆ * ((b₁ : G) * b₂) := by
                rw [mul_assoc (⁅a, (b₁ : G)⁆), mul_assoc (⁅a, (b₁ : G)⁆),
                  ← mul_assoc (b₁ : G), hBabel b₁ b₁.2 ⁅a, (b₂ : G)⁆ hz₂B, mul_assoc]
        have h4 : (⁅a, (b₁ : G)⁆ * ⁅a, (b₂ : G)⁆ * ((b₁ : G) * b₂)) *
            ((b₁ : G) * b₂)⁻¹ = ⁅a, (b₁ : G)⁆ * ⁅a, (b₂ : G)⁆ := by group
        rw [h3, h4] }
  have hφcard : Nat.card φ.ker * Nat.card φ.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rwa [show Nat.card ↥B = 27 from hBcard] at h
  have hrange_le : Nat.card φ.range ≤ 3 := by
    have hdvd : Nat.card φ.range ∣ Nat.card (⊤ : Subgroup ↥Z) :=
      Subgroup.card_dvd_of_le (H := φ.range) (K := ⊤) le_top
    rw [Subgroup.card_top, show Nat.card ↥Z = 3 from hZcard] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hker_ge : 9 ≤ Nat.card φ.ker := by
    by_contra h
    have h8 : Nat.card φ.ker ≤ 8 := by omega
    have hprod : Nat.card φ.ker * Nat.card φ.range ≤ 8 * 3 :=
      Nat.mul_le_mul h8 hrange_le
    rw [hφcard] at hprod
    norm_num at hprod
  let K : Subgroup G := φ.ker.map B.subtype
  have hKcard : Nat.card K = Nat.card φ.ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hKleB : K ≤ B := Subgroup.map_subtype_le _
  have hKcent : K ≤ Subgroup.centralizer ({a} : Set G) := by
    intro k hk
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : φ b = 1 := hb
    have h2 : ⁅a, (b : G)⁆ = 1 := congrArg Subtype.val h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hK_ea : CFSG.Open.IsElemAbelian 3 K := by
    refine ⟨IsMulCommutative.of_comm fun u v => Subtype.ext ?_, fun u hu => ?_⟩
    · exact hBabel (u : G) (hKleB u.2) (v : G) (hKleB v.2)
    · exact hB_ea.2 (u : G) (hKleB hu)
  have hKcard_ge : 9 ≤ Nat.card K := by rw [hKcard]; exact hker_ge
  have hKne : ∃ y ∈ K, y ≠ 1 := by
    haveI : Nontrivial ↥K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ↥K)
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  obtain ⟨y, hyK, hy1⟩ := hKne
  have hy3 : y ^ 3 = 1 := hK_ea.2 y hyK
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hnotsub : ¬ K ≤ Subgroup.zpowers y := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hyord] at hc
    omega
  obtain ⟨z, hzK, hzy⟩ := Set.not_subset.mp hnotsub
  have hz1 : z ≠ 1 := by
    intro h
    apply hzy
    rw [h]
    exact Subgroup.one_mem _
  have hz3 : z ^ 3 = 1 := hK_ea.2 z hzK
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzy_comm : ∀ w ∈ Subgroup.zpowers y, w * z = z * w := by
    intro w hw
    exact hBabel w (hKleB (Subgroup.zpowers_le.mpr hyK hw)) z (hKleB hzK)
  obtain ⟨hEea, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := Subgroup.zpowers y) (v := z)
      (by rw [Nat.card_zpowers, hyord]) hzord hzy hzy_comm
  refine ⟨B, Subgroup.zpowers y ⊔ Subgroup.zpowers z, hBle, hB_ea, hBcard, hZleB,
    ?_, hEea, hEcard, ?_, hAZ_comm, hABZ⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hyK) (Subgroup.zpowers_le.mpr hzK) |>.trans hKleB
  · refine sup_le ?_ ?_
    · exact (Subgroup.zpowers_le.mpr hyK).trans (hKcent.trans (le_of_eq hacent))
    · exact (Subgroup.zpowers_le.mpr hzK).trans (hKcent.trans (le_of_eq hacent))



theorem exists_two_extraspecial_and_abelian_data
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M)
    {A : Subgroup G} (hAP : A ≤ P) (hAcard : Nat.card A = 3)
    (hAQ : A ⊓ ((P ⊓ L) ⊔ (P ⊓ L')) = ⊥)
    (hLL' : L ≠ L') :
    ∃ R R' B E : Subgroup G,
      R = P ⊓ L ∧ R' = P ⊓ L' ∧
      B ≤ R ⊔ R' ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 27 ∧
      (Subgroup.center ↥R).map R.subtype ≤ B ∧
      E ≤ B ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ a ∈ A, ∀ z ∈ (Subgroup.center ↥R).map R.subtype, a * z = z * a) ∧
      (∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ (Subgroup.center ↥R).map R.subtype) ∧
      E ≤ conjClosure S.M L ∧
      CFSG.Open.rankThreeGamma 1 3 E ≤ S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup G := P ⊓ L with hRdef
  set R' : Subgroup G := P ⊓ L' with hR'def
  set Q : Subgroup G := R ⊔ R' with hQdef
  have hL'conj : L' ∈ conjSetOf S.M L := by
    rw [hset]
    simp
  have hL'calC : L' ∈ calC S.M := by
    obtain ⟨g, hgM, hL'map⟩ := hL'conj
    rw [hL'map]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map S.M (MulAut.conj g)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
        (Subgroup.le_normalizer hgM)) hL
  have hSL' : IsSL3Four (Bar2 L') := by
    obtain ⟨g, -, hL'map⟩ := hL'conj
    obtain ⟨eBar⟩ := uc22p20d_bar2_conj g L
    have hL'map' : L' = uc22p20bCj g L := by
      simpa [uc22p20bCj] using hL'map
    have e : Bar2 L ≃* Bar2 L' := by
      rw [hL'map']
      exact eBar
    exact isSL3Four_of_mulEquiv e hSL
  have hLM : L ≤ S.M := hL.1.le
  have hL'M : L' ≤ S.M := hL'calC.1.le
  have hRP : R ≤ P := by rw [hRdef]; exact inf_le_left
  have hR'P : R' ≤ P := by rw [hR'def]; exact inf_le_left
  have hRL : R ≤ L := by rw [hRdef]; exact inf_le_right
  have hR'L' : R' ≤ L' := by rw [hR'def]; exact inf_le_right
  have hRM : R ≤ S.M := hRP.trans hP.le
  have hR'M : R' ≤ S.M := hR'P.trans hP.le
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R L := by
    rw [hRdef]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hLM hL.1.subgroupOf
  have hR'_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R' L' := by
    rw [hR'def]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hL'M hL'calC.1.subgroupOf
  set A_bar : Subgroup (Bar2 S.M) := barImage S.M L with hAdef
  set B_bar : Subgroup (Bar2 S.M) := barImage S.M L' with hBdef
  set PA : Subgroup (Bar2 S.M) := barImage S.M R with hPAdef
  set PB : Subgroup (Bar2 S.M) := barImage S.M R' with hPBdef
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv (L := S.M) (K := L) hL
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv (L := S.M) (K := L') hL'calC
  have hSL_A : IsSL3Four ↥A_bar := isSL3Four_of_mulEquiv eA hSL
  have hSL_B : IsSL3Four ↥B_bar := isSL3Four_of_mulEquiv eB hSL'
  have hPA_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PA A_bar := by
    rw [hPAdef, hAdef]
    exact isSylowOf_barImage_of_isSylowOf hLM hR_sylow eA
  have hPB_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PB B_bar := by
    rw [hPBdef, hBdef]
    exact isSylowOf_barImage_of_isSylowOf hL'M hR'_sylow eB
  have hPA_le : PA ≤ A_bar := hPA_sylow.le
  have hPB_le : PB ≤ B_bar := hPB_sylow.le
  have hPA_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PA.subgroupOf A_bar) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) A_bar
      (A := PA.subgroupOf A_bar) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPA_le] using hPA_sylow
  have hPB_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PB.subgroupOf B_bar) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) B_bar
      (A := PB.subgroupOf B_bar) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPB_le] using hPB_sylow
  obtain ⟨hPA_ext, hPA_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_A hPA_abs
  obtain ⟨hPB_ext, hPB_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_B hPB_abs
  have hPAexp_abs : ∀ x : PA.subgroupOf A_bar, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_A hPA_abs
  have hPBexp_abs : ∀ x : PB.subgroupOf B_bar, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_B hPB_abs
  have hPAexp : ∀ x : PA, x ^ 3 = 1 := by
    intro x
    have h := hPAexp_abs ((Subgroup.subgroupOfEquivOfLe hPA_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPA_le) h
    simpa using h'
  have hPBexp : ∀ x : PB, x ^ 3 = 1 := by
    intro x
    have h := hPBexp_abs ((Subgroup.subgroupOfEquivOfLe hPB_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPB_le) h
    simpa using h'
  have hPA_ext' : CFSG.IsExtraspecial 3 ↥PA := by
    haveI : CFSG.IsExtraspecial 3 ↥(PA.subgroupOf A_bar) := hPA_ext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPA_le).symm
  have hPB_ext' : CFSG.IsExtraspecial 3 ↥PB := by
    haveI : CFSG.IsExtraspecial 3 ↥(PB.subgroupOf B_bar) := hPB_ext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPB_le).symm
  have hPA_card' : Nat.card PA = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA_le).toEquiv, hPA_card]
  have hPB_card' : Nat.card PB = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPB_le).toEquiv, hPB_card]
  have hR_iso : ↥R ≃* ↥PA :=
    equiv_barImage_of_isPGroup (hRP.trans hP.le) hR_sylow.isPGroup
  have hR'_iso : ↥R' ≃* ↥PB :=
    equiv_barImage_of_isPGroup (hR'P.trans hP.le) hR'_sylow.isPGroup
  have hR_ext : CFSG.IsExtraspecial 3 R := by
    haveI : CFSG.IsExtraspecial 3 ↥PA := hPA_ext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv hR_iso
  have hR'_ext : CFSG.IsExtraspecial 3 R' := by
    haveI : CFSG.IsExtraspecial 3 ↥PB := hPB_ext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv hR'_iso
  have hRcard : Nat.card R = 27 := by
    rw [Nat.card_congr hR_iso.toEquiv, hPA_card']
  have hR'card : Nat.card R' = 27 := by
    rw [Nat.card_congr hR'_iso.toEquiv, hPB_card']
  have hRexp : ∀ x : R, x ^ 3 = 1 := by
    intro x
    have h := hPAexp (hR_iso x)
    exact hR_iso.injective (by simpa [map_pow] using h)
  have hR'exp : ∀ x : R', x ^ 3 = 1 := by
    intro x
    have h := hPBexp (hR'_iso x)
    exact hR'_iso.injective (by simpa [map_pow] using h)
  have hcomm_bar : ∀ a ∈ barImage S.M L, ∀ b ∈ barImage S.M L', a * b = b * a :=
    uc22p22l_barImage_commute (L := S.M) hL hL'calC hLL'
  have hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r := by
    intro r hr r' hr'
    have hrM : r ∈ S.M := hRM hr
    have hr'M : r' ∈ S.M := hR'M hr'
    have hbar : uc22p21cPi S.M ⟨r, hrM⟩ * uc22p21cPi S.M ⟨r', hr'M⟩ =
        uc22p21cPi S.M ⟨r', hr'M⟩ * uc22p21cPi S.M ⟨r, hrM⟩ :=
      hcomm_bar _ (uc22p21c_mem_barImage.2 ⟨⟨r, hrM⟩, hRL hr, rfl⟩)
        _ (uc22p21c_mem_barImage.2 ⟨⟨r', hr'M⟩, hR'L' hr', rfl⟩)
    have hmem : ⁅r, r'⁆ ∈ CFSG.Open.pCoreOf 2 S.M :=
      uc22p22u_commutator_mem_pCoreOf (X := S.M) hrM hr'M hbar
    have hPcomm : ⁅r, r'⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem (hRP hr) (hR'P hr')) (P.inv_mem (hRP hr))) (P.inv_mem (hR'P hr'))
    have hdisj : Disjoint P (CFSG.Open.pCoreOf 2 S.M) :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (CFSG.Open.pCoreOf 2 S.M) hP.isPGroup
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥S.M)).map S.M.subtype)
    have hone : ⁅r, r'⁆ = 1 := by
      have hbot : ⁅r, r'⁆ ∈ (⊥ : Subgroup G) := hdisj.le_bot ⟨hPcomm, hmem⟩
      exact Subgroup.mem_bot.mp hbot
    rw [commutatorElement_eq_one_iff_mul_comm] at hone
    exact hone
  have hRinfR'_le_Z : R ⊓ R' ≤ (Subgroup.center ↥R).map R.subtype := by
    intro y hy
    have hycent : (⟨y, hy.1⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      show (s : G) * y = y * (s : G)
      exact hcomm (s : G) s.property y hy.2
    exact Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hycent, rfl⟩
  have hRinfR'_le_Z' : R ⊓ R' ≤ (Subgroup.center ↥R').map R'.subtype := by
    intro y hy
    have hycent : (⟨y, hy.2⟩ : ↥R') ∈ Subgroup.center ↥R' := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      show (s : G) * y = y * (s : G)
      exact (hcomm y hy.1 (s : G) s.property).symm
    exact Subgroup.mem_map.mpr ⟨⟨y, hy.2⟩, hycent, rfl⟩
  have hZcard : Nat.card ↥((Subgroup.center ↥R).map R.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hR_ext.center_order_p
  have hZ'card : Nat.card ↥((Subgroup.center ↥R').map R'.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective R'.subtype_injective]
    exact hR'_ext.center_order_p
  have hRinfR'_ne_bot : R ⊓ R' ≠ ⊥ := by
    intro hbot
    obtain ⟨ER, -, hERle, hERea, hERcard⟩ :=
      exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hR_ext hRexp
        (x := (1 : G)) R.one_mem
    obtain ⟨ER', -, hER'le, hER'ea, hER'card⟩ :=
      exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hR'_ext hR'exp
        (x := (1 : G)) R'.one_mem
    have hEcomm : ∀ a ∈ ER, ∀ b ∈ ER', a * b = b * a :=
      fun a ha b hb => hcomm a (hERle ha) b (hER'le hb)
    have hEinf : ER ⊓ ER' = ⊥ := by
      apply le_antisymm _ bot_le
      calc ER ⊓ ER' ≤ R ⊓ R' := inf_le_inf hERle hER'le
        _ = ⊥ := hbot
    have hE81card : Nat.card ↥(ER ⊔ ER') = 81 := by
      have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
        (A := ER) (B := ER') hEcomm
      rw [hEinf, Subgroup.card_bot, hERcard, hER'card] at h
      omega
    have hE81ea : CFSG.Open.IsElemAbelian 3 (ER ⊔ ER') :=
      CFSG.Open.IsElemAbelian.sup_of_commute hERea hER'ea hEcomm
    have hE81M : ER ⊔ ER' ≤ S.M :=
      sup_le (hERle.trans hRM) (hER'le.trans hR'M)
    have h4 : 4 ≤ CFSG.Open.pRank 3 S.M :=
      CFSG.SectionRank.le_pRank (p := 3) (H := S.M) (k := 4)
        (by norm_num) hE81M hE81ea (by rw [hE81card]; norm_num)
    have hbound : CFSG.Open.pRank 3 S.M ≤ 3 :=
      pRank_three_le_three_of_not_strong hS hU S hMS hnot
    omega
  have hRinfR'_card : Nat.card ↥(R ⊓ R') = 3 := by
    have hdvd : Nat.card ↥(R ⊓ R') ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le hRinfR'_le_Z
    have hne1 : Nat.card ↥(R ⊓ R') ≠ 1 := by
      intro h1
      exact hRinfR'_ne_bot (Subgroup.eq_bot_of_card_eq (R ⊓ R') h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hRinfR'_eq_Z : R ⊓ R' = (Subgroup.center ↥R).map R.subtype :=
    Subgroup.eq_of_le_of_card_ge hRinfR'_le_Z (by rw [hZcard, hRinfR'_card])
  have hRinfR'_eq_Z' : R ⊓ R' = (Subgroup.center ↥R').map R'.subtype :=
    Subgroup.eq_of_le_of_card_ge hRinfR'_le_Z' (by rw [hZ'card, hRinfR'_card])
  have hZeq : (Subgroup.center ↥R).map R.subtype =
      (Subgroup.center ↥R').map R'.subtype := hRinfR'_eq_Z.symm.trans hRinfR'_eq_Z'
  have h2 : (conjSetOf S.M L).ncard ≤ 2 := by
    rw [hset, Set.ncard_pair hLL']
  have h2' : (conjSetOf S.M L').ncard ≤ 2 := by
    rwa [uc22p2214_conjSetOf_eq hL'conj]
  have hPNL : P ≤ Subgroup.normalizer (L : Set G) := by
    intro p hp
    have hpM : p ∈ S.M := hP.le hp
    have hpodd : Odd (orderOf p) := by
      obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥P)
      have hkG : orderOf p = 3 ^ k := by
        simpa using (Subgroup.orderOf_coe (⟨p, hp⟩ : ↥P)).trans hk
      rw [hkG]
      exact Odd.pow (by norm_num : Odd 3)
    exact mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2 hpM hpodd
  have hPNL' : P ≤ Subgroup.normalizer (L' : Set G) := by
    intro p hp
    have hpM : p ∈ S.M := hP.le hp
    have hpodd : Odd (orderOf p) := by
      obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥P)
      have hkG : orderOf p = 3 ^ k := by
        simpa using (Subgroup.orderOf_coe (⟨p, hp⟩ : ↥P)).trans hk
      rw [hkG]
      exact Odd.pow (by norm_num : Odd 3)
    exact mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2' hpM hpodd
  have hPNR : P ≤ Subgroup.normalizer (R : Set G) := by
    intro p hp
    rw [hRdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := L)
      ⟨Subgroup.le_normalizer hp, hPNL hp⟩
  have hPNR' : P ≤ Subgroup.normalizer (R' : Set G) := by
    intro p hp
    rw [hR'def]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := L')
      ⟨Subgroup.le_normalizer hp, hPNL' hp⟩
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := hAP.trans hPNR
  have hAN' : A ≤ Subgroup.normalizer (R' : Set G) := hAP.trans hPNR'
  set Z : Subgroup G := (Subgroup.center ↥R).map R.subtype with hZdef
  obtain ⟨B, E, hBle, hBea, hBcard, hZleB, hEleB, hEea, hEcard, hEcent, hAZ_comm, hABZ⟩ :=
    exists_elemAbelian_27_and_nine_le_centralizer_of_two_extraspecial_order_three
      hR_ext hR'_ext hRcard hR'card hRexp hR'exp hcomm hZeq hAcard hAN hAN'
  have hZleB' : Z ≤ B := by simpa [hZdef] using hZleB
  have hAZ_comm' : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := by simpa [hZdef] using hAZ_comm
  have hABZ' : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Z := by simpa [hZdef] using hABZ
  have hBabel : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hBea.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hQP : Q ≤ P := by
    rw [hQdef]
    exact sup_le hRP hR'P
  have hQM : Q ≤ S.M := hQP.trans hP.le
  have hBQ : B ≤ Q := by
    rw [hQdef]
    exact hBle
  have hEQ : E ≤ Q := hEleB.trans hBQ
  have hEM : E ≤ S.M := hEQ.trans hQM
  have hAQ' : A ⊓ Q = ⊥ := by
    simpa [hQdef, hRdef, hR'def] using hAQ
  have hAinfB : A ⊓ B = ⊥ := by
    apply le_antisymm _ bot_le
    calc A ⊓ B ≤ A ⊓ Q := inf_le_inf le_rfl hBQ
      _ = ⊥ := hAQ'
  have hLX : L ≤ conjClosure S.M L :=
    uc22s217u3a_le_conjClosure ⟨1, S.M.one_mem, by ext x; simp⟩
  have hL'X : L' ≤ conjClosure S.M L := uc22s217u3a_le_conjClosure hL'conj
  have hQX : Q ≤ conjClosure S.M L := by
    rw [hQdef]
    exact sup_le (hRL.trans hLX) (hR'L'.trans hL'X)
  have hEX : E ≤ conjClosure S.M L := hEQ.trans hQX
  have hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ S.M :=
    rankThreeGamma_le_of_e9_le_X hS hU S hMS hC hnot hSE hL hset hSL
      hEX hEea hEcard
  exact ⟨R, R', B, E, hRdef, hR'def, hBle, hBea, hBcard, hZleB, hEleB, hEea, hEcard,
    hEcent, hAZ_comm, hABZ, hEX, hΓ⟩

theorem centralizer_le_of_order_three_of_P_sub_Q_of_ne
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M)
    {A : Subgroup G} (hAP : A ≤ P) (hAcard : Nat.card A = 3)
    (hAQ : A ⊓ ((P ⊓ L) ⊔ (P ⊓ L')) = ⊥)
    (hLL' : L ≠ L') :
    Subgroup.centralizer (A : Set G) ≤ S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, R', B, E, hRdef, hR'def, hBle, hBea, hBcard, hZleB, hEleB, hEea, hEcard,
    hEcent, hAZ_comm, hABZ, hEX, hΓ⟩ :=
    exists_two_extraspecial_and_abelian_data hS hU S hMS hC hnot hSE hL hset hSL hP hAP hAcard hAQ hLL'
  set Q : Subgroup G := R ⊔ R' with hQdef
  have hRP : R ≤ P := by rw [hRdef]; exact inf_le_left
  have hR'P : R' ≤ P := by rw [hR'def]; exact inf_le_left
  have hQP : Q ≤ P := by
    rw [hQdef]
    exact sup_le hRP hR'P
  have hQM : Q ≤ S.M := hQP.trans hP.le
  have hBQ : B ≤ Q := by
    rw [hQdef]
    exact hBle
  have hEQ : E ≤ Q := hEleB.trans hBQ
  have hEM : E ≤ S.M := hEQ.trans hQM
  have hAQ' : A ⊓ Q = ⊥ := by
    simpa [hQdef, hRdef, hR'def] using hAQ
  have hAinfB : A ⊓ B = ⊥ := by
    apply le_antisymm _ bot_le
    calc A ⊓ B ≤ A ⊓ Q := inf_le_inf le_rfl hBQ
      _ = ⊥ := hAQ'
  have hP0M : A ⊔ B ≤ S.M := sup_le (hAP.trans hP.le) (hBQ.trans hQM)
  have hP0P : A ⊔ B ≤ P := sup_le hAP (hBQ.trans hQP)
  have hP0p : IsPGroup 3 (A ⊔ B : Subgroup G) := hP.isPGroup.to_le hP0P
  have hE_norm : E ≤ Subgroup.normalizer (A : Set G) :=
    hEcent.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have h69 : R6_9 (dataOfSetup4 hS hU S) :=
    r6_9_dataOfSetup4 hS hU S hMS hC
  have hsub : (dataOfSetup4 hS hU S).sig ⊆ (dataOfSetup4 hS hU S).sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sigmaStd_dataOfSetup4 hS hU S)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hL)
  by_contra hCnot
  have hN : ¬ Subgroup.normalizer (A : Set G) ≤ S.M := by
    intro hNle
    exact hCnot ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNle)
  have hstep := h69 hsub 3 Nat.prime_three (by norm_num) E hEM hEea
    (by rw [hEcard]; norm_num) hΓ 3 A Nat.prime_three (hAP.trans hP.le) hAcard
    hE_norm hN (A ⊔ B) hP0M hP0p le_sup_left
  have hcomm69 : ∀ y ∈ (Subgroup.upperCentralSeries ↥(A ⊔ B) 2).map (A ⊔ B).subtype,
      ∀ x ∈ A, x * y = y * x := hstep.2.1
  set Z : Subgroup G := (Subgroup.center ↥R).map R.subtype with hZdef
  have hZleB' : Z ≤ B := by simpa [hZdef] using hZleB
  have hAZ_comm' : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := by simpa [hZdef] using hAZ_comm
  have hABZ' : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Z := by simpa [hZdef] using hABZ
  have hBabel : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hBea.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hANB : A ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have h1 : a * b * a⁻¹ = ⁅a, b⁆ * b := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact B.mul_mem (hZleB' (hABZ' a ha b hb)) hb
  have hZcentral : ∀ z ∈ Z, ∀ y ∈ A ⊔ B, z * y = y * z := by
    intro z hz y hy
    obtain ⟨a, ha, b, hb, hxy⟩ := CFSG.Walter.mem_sup_of_le_normalizer hANB hy
    rw [← hxy]
    have hzB : z ∈ B := hZleB' hz
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [(hAZ_comm' a ha z hz).symm]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [hBabel z hzB b hb]
      _ = (a * b) * z := by group
  have hcenter_Z : Z.subgroupOf (A ⊔ B) ≤ Subgroup.center ↥(A ⊔ B) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hZcentral (z : G) (Subgroup.mem_subgroupOf.mp hz) (y : G) y.2).symm
  have hbZ : ∀ b ∈ B, ∀ y ∈ A ⊔ B, ⁅b, y⁆ ∈ Z := by
    intro b hb y hy
    obtain ⟨a, ha, b', hb', hxy⟩ := CFSG.Walter.mem_sup_of_le_normalizer hANB hy
    rw [← hxy]
    have hbb' : ⁅b, b'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hBabel b hb b' hb'
    have h1 : ⁅b, a * b'⁆ = ⁅b, a⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hbb']
      group
    rw [h1, (commutatorElement_inv a b).symm]
    exact Z.inv_mem (hABZ' a ha b hb)
  have hB_up : ∀ (b : G) (hb : b ∈ B), (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B)) ∈
      Subgroup.upperCentralSeries ↥(A ⊔ B) 2 := by
    intro b hb
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    apply hcenter_Z
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using
      hbZ b hb (y : G) y.2
  have hB_Z2 : B ≤ (Subgroup.upperCentralSeries ↥(A ⊔ B) 2).map (A ⊔ B).subtype := by
    intro b hb
    exact Subgroup.mem_map.mpr
      ⟨⟨b, Subgroup.mem_sup_right hb⟩, hB_up b hb, rfl⟩
  have hAB_comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact hcomm69 b (hB_Z2 hb) a ha
  have hAea : CFSG.Open.IsElemAbelian 3 A := by
    refine ⟨(isCyclic_of_card_dvd_prime (p := 3) (by rw [hAcard])).isMulCommutative, ?_⟩
    intro x hx
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨x, hx⟩)
    simpa [hAcard] using congrArg Subtype.val h
  have hcardAUB : Nat.card ↥(A ⊔ B) = 81 := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := A) (B := B) hAB_comm
    rw [hAinfB, Subgroup.card_bot, hAcard, hBcard] at h
    omega
  have hP0ea : CFSG.Open.IsElemAbelian 3 (A ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAea hBea hAB_comm
  have h4 : 4 ≤ CFSG.Open.pRank 3 S.M :=
    CFSG.SectionRank.le_pRank (p := 3) (H := S.M) (k := 4)
      (by norm_num) hP0M hP0ea (by rw [hcardAUB]; norm_num)
  have hbound : CFSG.Open.pRank 3 S.M ≤ 3 :=
    pRank_three_le_three_of_not_strong hS hU S hMS hnot
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
