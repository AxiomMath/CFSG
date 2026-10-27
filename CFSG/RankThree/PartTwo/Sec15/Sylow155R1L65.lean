module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Comp
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofCS
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem res1_conj_mem_pCoreOf {M : Subgroup G} {m v : G} (hm : m ∈ M)
    (hv : v ∈ CFSG.Open.pCoreOf 2 M) : m * v * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  refine ⟨⟨m, hm⟩ * v₀ * ⟨m, hm⟩⁻¹, CFSG.pCore_normal.conj_mem v₀ hv₀ ⟨m, hm⟩, ?_⟩
  simp

private theorem res1_isPGroup_pCoreOf (M : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
  CFSG.pCore_isPGroup.map M.subtype

private theorem le_res1C {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (L : Subgroup G) : A ≤ Res1C A L := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, (Subgroup.mem_inf.mp hb).1⟩ ⟨a, ha⟩)

theorem res1_card_inf {A : Subgroup G} {c : G} {L : Subgroup G} (hS : Sec14Std G A c L)
    (hhyp : IsHyperplane A (A ⊓ L)) : Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hA27 : Nat.card A = 27 := hS.toSec13Data.mem_partTwoE.2.1
  have h := hhyp.2
  rw [hA27] at h
  omega

theorem res1_isComponent_unique {A : Subgroup G} {c : G} {L : Subgroup G}
    (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L)) {Y₁ Y₂ : Subgroup (Res1Q A L)}
    (h₁ : CFSG.IsComponent Y₁) (h₂ : CFSG.IsComponent Y₂) : Y₁ = Y₂ := by
  classical
  have hFE := (hS.toTheoremFourHyp.partTwoF_eq_partTwoE hS.partTwoS_eq).1
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hS.mem_partTwoF.1
  have hB9 := res1_card_inf hS hhyp
  set C : Subgroup G := Res1C A L with hCdef
  have hAC : A ≤ C := le_res1C hAab L
  have hBA : A ⊓ L ≤ A := inf_le_left
  have hBC : A ⊓ L ≤ C := hBA.trans hAC
  have hB'ab : CFSG.Assembly.IsElemAbelian 3 ((A ⊓ L).subgroupOf C) :=
    (hAab.mono hBA).subgroupOf C
  have hB'9 : Nat.card ((A ⊓ L).subgroupOf C) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv).trans hB9
  have hBZ : (A ⊓ L).subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp y.2 (x : G) hx).symm)
  have hmaxC : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ U : Subgroup C, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set C)) →
      ∀ E' : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E := by
    rintro E hE hE27 ⟨U, hU1, hU2, hEU⟩ E' hE' hEE'
    have hmem : E.map C.subtype ∈ partTwoF G := by
      rw [hFE]
      refine ⟨hE.map _, ?_, U.map C.subtype, ?_, hU2.map _,
        (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)⟩
      · rw [Subgroup.card_map_of_injective C.subtype_injective, hE27]
      · exact fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U C.subtype_injective).mp h)
    exact Subgroup.map_injective C.subtype_injective
      (hmem.2.1 _ (hE'.map _) (Subgroup.map_mono hEE'))
  exact Sylow155T51.eq_of_isComponent hB'ab hB'9 hBZ hmaxC h₁ h₂

theorem res1_isComponent_normal {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hYc : CFSG.IsComponent Yc) : Yc.Normal := by
  refine ⟨fun n hn q => ?_⟩
  have h := res1_isComponent_unique hS hhyp
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj q) hYc) hYc
  have hmem : q * n * q⁻¹ ∈ Yc.map (MulAut.conj q).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [h] at hmem

private theorem lemma56_aux {A M C : Subgroup G} {Y : Subgroup (↥C ⧸ CFSG.pPrimeCore 3 ↥C)}
    (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ x : G, x ^ 3 = 1 → A ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A)
    (hAM : A ≤ M) (hAC : A ≤ C)
    (hlayer : CFSG.layer (↥C ⧸ CFSG.pPrimeCore 3 ↥C) ≤ Y) {w : ↥C}
    (hw : (w : G) ∈ CFSG.Open.pCoreOf 2 M)
    (hcomm : ∀ y ∈ Y, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) w * y =
      y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) w) :
    w ∈ CFSG.pPrimeCore 3 ↥C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  set Q₀ : Subgroup ↥C := (CFSG.Open.pCoreOf 2 M ⊓ C).subgroupOf C with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := ((res1_isPGroup_pCoreOf M).to_le inf_le_left).comap_subtype
  have hQ₀3 : ¬ 3 ∣ Nat.card Q₀ := by
    obtain ⟨n, hn⟩ := hQ₀2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hQ₀conj : ∀ m : ↥C, (m : G) ∈ M → ∀ q ∈ Q₀, m * q * m⁻¹ ∈ Q₀ := by
    intro m hm q hq
    rw [hQ₀, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hq ⊢
    refine ⟨?_, (m * q * m⁻¹).2⟩
    have := res1_conj_mem_pCoreOf hm hq.1
    simpa using this
  have hAQ₀ : A.subgroupOf C ≤ Subgroup.normalizer (Q₀ : Set ↥C) := by
    intro a ha
    have haM : (a : G) ∈ M := hAM (Subgroup.mem_subgroupOf.mp ha)
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQ₀conj a haM q hq, fun hq => ?_⟩
    have h := hQ₀conj a⁻¹ (by simpa using M.inv_mem haM) _ hq
    have e : a⁻¹ * (a * q * a⁻¹) * a⁻¹⁻¹ = q := by group
    rwa [e] at h
  have hA3' : ∀ x ∈ Subgroup.centralizer ((A.subgroupOf C : Subgroup ↥C) : Set ↥C), x ^ 3 = 1 →
      x ∈ A.subgroupOf C := by
    intro x hx hx3
    have hx3' : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    refine Subgroup.mem_subgroupOf.mpr (hA3 x hx3' fun a ha => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.mp hx ⟨a, hAC ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h
  have hP : π w ∈ Subgroup.centralizer
      (CFSG.pCore 3 (↥C ⧸ CFSG.pPrimeCore 3 ↥C) : Set (↥C ⧸ CFSG.pPrimeCore 3 ↥C)) :=
    Sec4.map_le_centralizer_pCore_of_bender (hAab.subgroupOf C) hA3' hQ₀3 hAQ₀
      ⟨w, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hw, w.2⟩), rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (π w) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := res1_isPGroup_pCoreOf M ⟨(w : G), hw⟩
    have hk' : (w : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : w ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hE : π w ∈ Subgroup.centralizer
      (CFSG.layer (↥C ⧸ CFSG.pPrimeCore 3 ↥C) : Set (↥C ⧸ CFSG.pPrimeCore 3 ↥C)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hcomm e (hlayer he)).symm
  have h1 := Proof1418Res3.eq_one_of_mem_centralizer_layer
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) hk hE hP
  exact (QuotientGroup.eq_one_iff w).mp h1

private theorem lemma65_aux {A M C : Subgroup G}
    {Y : Subgroup (↥C ⧸ CFSG.pPrimeCore 3 ↥C)} [hYn : Y.Normal]
    (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ x : G, x ^ 3 = 1 → A ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A)
    (hAM : A ≤ M) (hAC : A ≤ C)
    (hlayer : CFSG.layer (↥C ⧸ CFSG.pPrimeCore 3 ↥C) ≤ Y)
    {c : G} (hcA : c ∈ A) (hc3 : orderOf c = 3)
    (hcY : c ∈ (Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype)
    {g : G} (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hgM : g ∈ M) (hgC : g ∈ C)
    (hgcop : Nat.Coprime (orderOf g) 6) (hcent : Res1AutCent ↥Y) :
    ⁅CFSG.Open.pCoreOf 2 M ⊓ C, Subgroup.zpowers g⁆ ≤
      (CFSG.pPrimeCore 3 ↥C).map C.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  let ρ : (↥C ⧸ CFSG.pPrimeCore 3 ↥C) →* MulAut ↥Y := MulAut.conjNormal
  set W : Subgroup ↥C := (CFSG.Open.pCoreOf 2 M ⊓ C).subgroupOf C with hWdef
  have hW2 : IsPGroup 2 W := ((res1_isPGroup_pCoreOf M).to_le inf_le_left).comap_subtype
  have hWconj : ∀ m : ↥C, (m : G) ∈ M → ∀ q ∈ W, m * q * m⁻¹ ∈ W := by
    intro m hm q hq
    rw [hWdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hq ⊢
    refine ⟨?_, (m * q * m⁻¹).2⟩
    have := res1_conj_mem_pCoreOf hm hq.1
    simpa using this
  have hVtconj : ∀ m : ↥C, (m : G) ∈ M → ∀ q ∈ W.map π, π m * q * (π m)⁻¹ ∈ W.map π := by
    rintro m hm _ ⟨w, hw, rfl⟩
    exact ⟨m * w * m⁻¹, hWconj m hm w hw, by simp⟩
  obtain ⟨c', hc'Y, hc'⟩ := hcY
  have hc'val : (c' : G) = c := hc'
  let g' : ↥C := ⟨g, hgC⟩
  have hgc : g' * c' = c' * g' := by
    apply Subtype.ext
    show g * (c' : G) = (c' : G) * g
    rw [hc'val]
    exact (Subgroup.mem_centralizer_iff.mp hgA c hcA).symm
  have hcc : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'val] using hcc)
  have hcM : (c' : G) ∈ M := by rw [hc'val]; exact hAM hcA
  let y : ↥Y := ⟨π c', hc'Y⟩
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    show π c' ^ 3 = 1
    rw [← map_pow, hc'3, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : π c' = 1 := congrArg Subtype.val h
    have hcN : c' ∈ CFSG.pPrimeCore 3 ↥C := (QuotientGroup.eq_one_iff c').mp h1
    have hc'1 : c' = 1 :=
      Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hN hcN (a := 1) (by simpa using hc'3)
    have hc1 : c = 1 := by rw [← hc'val, hc'1]; rfl
    rw [hc1, orderOf_one] at hc3
    omega
  have hy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  set α : MulAut ↥Y := ρ (π g') with hαdef
  set Vh : Subgroup (MulAut ↥Y) := (W.map π).map ρ with hVhdef
  have hα : Nat.Coprime (orderOf α) 6 := by
    refine Nat.Coprime.coprime_dvd_left ?_ hgcop
    have h1 : orderOf g' = orderOf g := (Subgroup.orderOf_coe g').symm
    rw [← h1]
    exact (orderOf_map_dvd ρ (π g')).trans (orderOf_map_dvd π g')
  have hαy : α y = y := by
    apply Subtype.ext
    show π g' * π c' * (π g')⁻¹ = π c'
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hgc]
  have hVh2 : IsPGroup 2 Vh := (hW2.map π).map ρ
  have hαV : ∀ v ∈ Vh, α * v * α⁻¹ ∈ Vh := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨π g' * q * (π g')⁻¹, hVtconj g' hgM q hq, ?_⟩
    simp [hαdef]
  have hcy : MulAut.conj y = ρ (π c') := (MulAut.conjNormal_val (H := Y) (h := y)).symm
  have hyV : ∀ v ∈ Vh, MulAut.conj y * v * (MulAut.conj y)⁻¹ ∈ Vh := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨π c' * q * (π c')⁻¹, hVtconj c' hcM q hq, ?_⟩
    rw [hcy]
    simp
  have hcomm : ∀ v ∈ Vh, α * v = v * α := hcent α Vh y hy hα hαy hVh2 hαV hyV
  rw [Subgroup.commutator_le]
  intro h hh x hx
  obtain ⟨hhV, hhC⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hgkM : g ^ k ∈ M := zpow_mem hgM k
  let h' : ↥C := ⟨h, hhC⟩
  let x' : ↥C := g' ^ k
  have hx'val : (x' : G) = g ^ k := rfl
  have hh'W : h' ∈ W := Subgroup.mem_subgroupOf.mpr ⟨hhV, hhC⟩
  have hρ1 : ρ (π ⁅h', x'⁆) = 1 := by
    have e1 : ρ (π ⁅h', x'⁆) = ⁅ρ (π h'), α ^ k⁆ := by
      simp [x', hαdef, commutatorElement_def]
    rw [e1, commutatorElement_eq_one_iff_mul_comm]
    exact ((Commute.zpow_left (hcomm _ ⟨π h', ⟨h', hh'W, rfl⟩, rfl⟩) k).eq).symm
  have hw : ⁅h', x'⁆ ∈ CFSG.pPrimeCore 3 ↥C := by
    refine lemma56_aux hAab hA3 hAM hAC hlayer ?_ ?_
    · show ⁅h, g ^ k⁆ ∈ CFSG.Open.pCoreOf 2 M
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      have hinv := res1_conj_mem_pCoreOf hgkM ((CFSG.Open.pCoreOf 2 M).inv_mem hhV)
      exact (CFSG.Open.pCoreOf 2 M).mul_mem hhV (by simpa [mul_assoc] using hinv)
    · intro z hz
      have h1 : ρ (π ⁅h', x'⁆) ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hρ1]; rfl
      have h2 := congrArg Subtype.val h1
      simp only [ρ, MulAut.conjNormal_apply] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
  exact ⟨⁅h', x'⁆, hw, rfl⟩

theorem false_of_res1AutCent {A : Subgroup G} {c : G}
    {L M : Subgroup G} {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (hY : Res1AtOf A c L M Yc) (hcent : Res1AutCent ↥Yc) :
    False := by
  classical
  obtain ⟨hhyp, -, -, ⟨hYcomp, hcY, -⟩, g, hg, -, hgodd, hgnot⟩ := hY
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hS.mem_partTwoF.1
  have hA3 : ∀ x : G, x ^ 3 = 1 → A ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A :=
    fun _ hx3 hAx => mem_of_mem_partTwoF hS.mem_partTwoF hx3 hAx
  have hAC : A ≤ Res1C A L := le_res1C hAab L
  have hlayer : CFSG.layer (Res1Q A L) ≤ Yc :=
    sSup_le fun _ hK => (res1_isComponent_unique hS hhyp hK hYcomp).le
  have hcmem := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcmem.2.1
  obtain ⟨hg1, hgM⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨g₀, hg₀N, hg₀⟩ := hg1
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := by
    rw [← hg₀]
    exact g₀.2
  have hgC : g ∈ Res1C A L := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp hgA b (Subgroup.mem_inf.mp hb).1
  have hN₀ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (A : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hg3 : ¬ 3 ∣ orderOf g := by
    intro h3
    apply hN₀
    refine h3.trans ?_
    have h1 : orderOf g = orderOf
        (⟨g₀, hg₀N⟩ : ↥(CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (A : Set G)))) := by
      rw [Subgroup.orderOf_mk, ← hg₀]
      exact Subgroup.orderOf_coe g₀
    rw [h1]
    exact orderOf_dvd_natCard _
  have hgcop : Nat.Coprime (orderOf g) 6 := by
    have h2 : Nat.Coprime (orderOf g) 2 := by
      have := Nat.odd_iff.mp hgodd
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
    have h3 : Nat.Coprime (orderOf g) 3 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hg3)
    exact Nat.Coprime.mul_right h2 h3
  exact hgnot (lemma65_aux hAab hA3 hAM hAC hlayer hcmem.1 hc3 hcY hgA hgM hgC hgcop hcent)

theorem step155HostE0WRes1Type_of_autCent {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → P Y → Res1AutCent Y) :
    Step155HostE0WRes1Type P := by
  intro G _ _ A c L hR hN hS X K Y M T P' hctx hmax habove hend h146 hYP hdelta Yc hY hsimple hP'
  have hAM : A ≤ M := fun a ha => hctx.mem_m.2 (Subgroup.mem_sup_left ha)
  exact (false_of_res1AutCent hS hAM hY (hP ↥Yc hsimple hP')).elim

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
