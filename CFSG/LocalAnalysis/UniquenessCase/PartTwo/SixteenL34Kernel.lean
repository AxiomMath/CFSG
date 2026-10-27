module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34FixHolds
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2FourL34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem s168e3_kernel_of_l34_point_fixers
    {T : Type} [CommGroup T] [Finite T]
    {H A : Subgroup (MulAut T)}
    (hHA : H ≤ A)
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut T)))
    (hC : A ⊓ Subgroup.centralizer (H : Set (MulAut T)) = ⊥)
    (hH : IsLn ↥H 3 2)
    (hfix : ∀ x : T, x ≠ 1 →
      ∃ b ∈ H, orderOf b = 3 ∧ (b : MulAut T) x = x) :
    S168e3Kernel A 3 := by
  let Φ : ↥A →* MulAut ↥H :=
    (Subgroup.normalizerMonoidHom (H := H)).comp (Subgroup.inclusion hAN)
  have hΦ_apply : ∀ (a : ↥A) (h : ↥H),
      ((Φ a) h : MulAut T) = (a : MulAut T) * (h : MulAut T) * (a : MulAut T)⁻¹ := by
    intro a h
    have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe H (Subgroup.inclusion hAN a) h
    rw [Subgroup.coe_inclusion] at h1
    exact h1
  have hΦker : Φ.ker = (A ⊓ Subgroup.centralizer (H : Set (MulAut T))).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro ha
      refine ⟨a.2, ?_⟩
      have hmem : Subgroup.inclusion hAN a ∈ H.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact ha
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion] at hmem
      exact hmem
    · rintro ⟨-, hc⟩
      refine MulEquiv.ext fun h => ?_
      apply Subtype.ext
      rw [hΦ_apply]
      rw [Subgroup.mem_centralizer_iff] at hc
      show (a : MulAut T) * (h : MulAut T) * (a : MulAut T)⁻¹ = (h : MulAut T)
      calc (a : MulAut T) * (h : MulAut T) * (a : MulAut T)⁻¹
          = ((h : MulAut T) * (a : MulAut T)) * (a : MulAut T)⁻¹ := by rw [← hc h h.2]
        _ = (h : MulAut T) := by group
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff Φ, hΦker, hC]
    ext a
    simp
  have hprank : CFSG.Open.pRank 3 A ≤ 2 := by
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥A) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥H)) :=
      CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) Φ hΦinj
    have h2 : CFSG.Open.pRank 3 A = CFSG.Open.pRank 3 (⊤ : Subgroup ↥A) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup A
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥H)) ≤ 2 := by
      simpa using s16k_pRank_aut_l34 (X := ↥H) hH (p := 3) Nat.prime_three (by decide)
    rw [h2]
    exact h1.trans h3
  refine ⟨hprank, ?_⟩
  intro x hx1 E hEA hEel
  have hEpow : ∀ a : ↥E, a ^ 3 = 1 :=
    (CFSG.Quasithin.A36B.IsElemAbelianOfRank.comm_pow hEel).2
  have hEcard : Nat.card ↥E = 9 := by
    obtain ⟨eE⟩ := hEel
    rw [Nat.card_congr eE.toEquiv]
    change Nat.card (Fin 2 → ZMod 3) = 9
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  let EA : Subgroup ↥A := E.subgroupOf A
  have hEAcard : Nat.card ↥EA = 9 := by
    change Nat.card ↥(E.subgroupOf A) = 9
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hEcard]
  have hEApow : ∀ a : ↥EA, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((⟨(a : MulAut T), Subgroup.mem_subgroupOf.mp a.2⟩ : ↥E) ^ 3 : MulAut T) = 1 :=
      congrArg (fun z : ↥E => (z : MulAut T))
        (hEpow ⟨(a : MulAut T), Subgroup.mem_subgroupOf.mp a.2⟩)
    simpa using h1
  obtain ⟨k, hfield, hfin, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) (p := 2) (f := 2) hH
  letI : Field k := hfield
  letI : Finite k := hfin
  have hk4 : Nat.card k = 4 := by
    rw [hk]
    norm_num
  let Ψ : ↥A →* MulAut (projectiveSL 3 k) :=
    (MulAut.congr e).toMonoidHom.comp Φ
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    apply hΦinj
    apply (MulAut.congr e).injective
    simpa [Ψ] using hab
  let Pb : Subgroup (MulAut (projectiveSL 3 k)) := EA.map Ψ
  have hPcard : Nat.card ↥Pb = 9 := by
    change Nat.card ↥(EA.map Ψ) = 9
    rw [Subgroup.card_map_of_injective hΨinj, hEAcard]
  have hPe : ∀ q ∈ Pb, q ^ 3 = 1 := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    have h3 : (⟨a, ha⟩ : ↥EA) ^ 3 = 1 := hEApow ⟨a, ha⟩
    have h4 : a ^ 3 = 1 := by
      simpa using congrArg (fun z : ↥EA => (z : ↥A)) h3
    rw [← map_pow, h4, map_one]
  obtain ⟨c, hc1, hcP⟩ :=
    CFSG.Quasithin.H13.S126C.exists_conj_mem_l34 (F := k) hk4 hPe hPcard
  obtain ⟨a, ha, hΨa⟩ := Subgroup.mem_map.mp hcP
  let h0 : ↥H := e.symm c
  have hconj : (MulAut.congr e) (MulAut.conj h0) = MulAut.conj c := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply, h0]
  have hΦa : Φ a = MulAut.conj h0 := by
    apply (MulAut.congr e).injective
    rw [hconj, ← hΨa]
    rfl
  let h0A : ↥A := ⟨(h0 : MulAut T), hHA h0.2⟩
  have hΦh0 : Φ h0A = MulAut.conj h0 := by
    refine MulEquiv.ext fun h => ?_
    apply Subtype.ext
    rw [hΦ_apply]
    simp [MulAut.conj_apply, h0A]
  have ha_eq_h0A : a = h0A := hΦinj (hΦa.trans hΦh0.symm)
  have ha_eq_h0 : (a : MulAut T) = (h0 : MulAut T) :=
    congrArg (fun z : ↥A => (z : MulAut T)) ha_eq_h0A
  have hbE : (a : MulAut T) ∈ E := Subgroup.mem_subgroupOf.mp ha
  have hbH : (a : MulAut T) ∈ H := by
    rw [ha_eq_h0]
    exact h0.2
  have hbne : (a : MulAut T) ≠ 1 := by
    intro h1
    apply hc1
    have h2 : c = e (⟨(a : MulAut T), hbH⟩ : ↥H) := by
      rw [show (⟨(a : MulAut T), hbH⟩ : ↥H) = h0 from Subtype.ext ha_eq_h0]
      exact (e.apply_symm_apply c).symm
    rw [h2, show (⟨(a : MulAut T), hbH⟩ : ↥H) = 1 from Subtype.ext h1, map_one]
  have hborder : orderOf (a : MulAut T) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (⟨(a : MulAut T), hbE⟩ : ↥E) ^ 3 = 1 := hEpow _
    have hne : (⟨(a : MulAut T), hbE⟩ : ↥E) ≠ 1 := by
      intro h
      apply hbne
      simpa using congrArg Subtype.val h
    have h3 : orderOf (⟨(a : MulAut T), hbE⟩ : ↥E) = 3 := orderOf_eq_prime h1 hne
    have h4 : orderOf ((⟨(a : MulAut T), hbE⟩ : ↥E) : MulAut T) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact h3
    simpa using h4
  obtain ⟨y, hyH, hyord, hyfix⟩ := hfix x hx1
  have hyHord : orderOf (⟨y, hyH⟩ : ↥H) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨y, hyH⟩ : ↥H)]
    simpa using hyord
  have hbHord : orderOf (⟨(a : MulAut T), hbH⟩ : ↥H) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨(a : MulAut T), hbH⟩ : ↥H)]
    simpa using hborder
  obtain ⟨gH, hgH⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_eq_conj_of_orderOf_three
      (X := ↥H) hH hbHord hyHord
  refine ⟨(gH : MulAut T), hHA gH.2, (a : MulAut T), hbE, hbne, ?_⟩
  have hgH' : (y : MulAut T) = (gH : MulAut T) * (a : MulAut T) * (gH : MulAut T)⁻¹ := by
    simpa using congrArg (fun z : ↥H => (z : MulAut T)) hgH
  calc ((gH : MulAut T) * (a : MulAut T) * (gH : MulAut T)⁻¹) x
      = y x := by rw [← hgH']
    _ = x := hyfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
