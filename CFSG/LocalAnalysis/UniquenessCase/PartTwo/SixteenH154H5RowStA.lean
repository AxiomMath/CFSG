module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.LargeExtraspecial.S63AAut
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.SimsE214SevenSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_relIndex_eq_eight_of_binaryNaturalSL [Finite W]
    {L : Subgroup (MulAut W)} {Z I : Subgroup W}
    (h : BinaryNaturalSL L I Z 3 1) (hZI : Z ≤ I) :
    Z.relIndex I = 8 := by
  obtain ⟨K, hF, hfin, hcard, hreal⟩ := h
  letI : Field K := hF
  letI : Finite K := hfin
  obtain ⟨π, hπ⟩ := hreal
  have h1 : Nat.card I = Nat.card (FFModel.nat (StatedSL 3 K)).Mod * Nat.card Z :=
    CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  have h2 : Nat.card (FFModel.nat (StatedSL 3 K)).Mod = Nat.card K ^ 3 :=
    CFSG.Quasithin.G64.card_natMod (StatedSL 3 K)
  have h3 : Z.relIndex I * Nat.card Z = Nat.card I := by
    have h := Subgroup.relIndex_mul_card Z I
    rwa [inf_eq_left.mpr hZI] at h
  have hI : Nat.card I = 8 * Nat.card Z := by
    rw [h1, h2, hcard]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h3, hI])

private theorem s16h_top_le_normalizer {Z : Subgroup W} :
    (⊤ : Subgroup W) ≤ Subgroup.normalizer (Z : Set W) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [show x * y * x⁻¹ = y by rw [mul_comm x y, mul_assoc, mul_inv_cancel, mul_one]]

theorem s16h_H5_rowL3_mQuot_three_dvd [Finite W] {L : Subgroup (MulAut W)}
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    3 ∣ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) := by
  obtain ⟨k, -, -, hsum⟩ := h
  obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
  by_cases hk0 : k = 0
  · subst hk0
    have hbot : (⨆ i : Fin 0, I i) = ⊥ := by simp
    have hUZ : commSub ⊤ L = commSub ⊤ L ⊓ fixV L := by
      nth_rewrite 1 [← hsup]
      rw [hbot, sup_bot_eq]
    have hgoal : E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 0 := by
      nth_rewrite 1 [hUZ]
      exact E3.mQuot_self _
    rw [hgoal]
    exact dvd_zero 3
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hc : ∀ i, (commSub ⊤ L ⊓ fixV L).relIndex (I i) = 8 :=
      fun i => s16h_relIndex_eq_eight_of_binaryNaturalSL (hN i) (hZI i)
    have hZle : commSub ⊤ L ⊓ fixV L ≤ ⨆ i, I i :=
      (hZI ⟨0, hkpos⟩).trans (le_iSup I ⟨0, hkpos⟩)
    have hUeq : commSub ⊤ L = ⨆ i, I i := by
      rw [← hsup, sup_eq_right.mpr hZle]
    have hres := CFSG.Quasithin.SimsE2.E214S.relIndex_iSup_eq_pow
      (r := k) (hr := hkpos) (I := (⊤ : Subgroup W)) (Z := commSub ⊤ L ⊓ fixV L)
      (W := I) (c := 8) hZI (fun _ => le_top) (fun _ => s16h_top_le_normalizer) hc
      (fun i => (inf_le_inf_left (I i) le_sup_right).trans (hind i))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmq : E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 3 * k := by
      have hfact : (commSub ⊤ L ⊓ fixV L).relIndex (commSub ⊤ L) = 2 ^ (3 * k) := by
        nth_rewrite 2 [hUeq]
        rw [hres, show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul]
      unfold E3.mQuot
      rw [hfact]
      exact padicValNat.prime_pow (p := 2) (3 * k)
    rw [hmq]
    exact dvd_mul_right 3 k

theorem s16h_H5_rowSt8_irrSet [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    commSub ⊤ L ∈ irrSet L := by
  classical
  haveI : Finite (MulAut W) := s16h_finite_mulAut (W := W)
  have hnot : ¬ (IsAlt ↥L 5 ∧ IsL3 ↥L 1) := by
    rintro ⟨hAlt, hL3⟩
    have h60 : Nat.card ↥L = 60 := by
      rw [s15k_six_alt_card hAlt (by norm_num)]
      norm_num [Nat.factorial]
    have h168 : Nat.card ↥L = 168 := card_eq_of_isL3 hL3
    omega
  rcases hc.conc.2.2 with h1 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h1).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · obtain ⟨-, hsum, -⟩ := h3
    rcases s16h_H5_thin_sum hc hsum with hL3 | hA5
    · have hdvd := s16h_H5_rowL3_mQuot_three_dvd (L := L) hL3
      have h8 : E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 8 := h.2
      rw [h8] at hdvd
      norm_num at hdvd
    · rcases hA5 with ⟨k, hk, hOM | hAlt⟩
      · exact (hnot ⟨s16k_isAlt_five_of_isOmegaMinus_four hOM.1, h.1⟩).elim
      · exact (hnot ⟨hAlt.1, h.1⟩).elim
  · exact h4.1

private theorem s16h_normalizer_le_stabSub_commSub {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private theorem s16h_isElemAbelian_top {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) : IsElemAbelian p (⊤ : Subgroup ↥E) := by
  haveI : IsMulCommutative ↥E := h.1
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : ↥E) (b : ↥E))⟩⟩,
    fun x _ => Subtype.ext (h.2 (x : ↥E) (x : ↥E).2)⟩

private theorem s16h_not_sq_dvd_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 336 := by
  intro h
  have hmem : p ∈ (336 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_trans (dvd_pow_self p two_ne_zero) h, by norm_num⟩
  have hpf : (336 : ℕ).primeFactors = {2, 3, 7} := by norm_num [Nat.primeFactors]
  rw [hpf] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hp2 rfl
  · norm_num at h
  · norm_num at h

theorem s16h_H5_rowSt8_autSub_le [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  classical
  haveI : Finite (MulAut W) := s16h_finite_mulAut (W := W)
  set U : Subgroup W := commSub ⊤ L with hU
  set Λ : Subgroup (MulAut U) := autSub L U with hΛ
  set Ē : Subgroup (MulAut U) := autSub E U with hĒ
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (Subgroup.mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_normalizer_le_stabSub_commSub (L := L) (hEN he)
  have hLU : L ≤ stabSub U := by
    rw [hU]
    intro l hl
    exact s16h_normalizer_le_stabSub_commSub (L := L) (Subgroup.le_normalizer hl)
  have hEab_aut : IsElemAbelian q Ē := by
    have h := hEab.subgroupOf (stabSub U)
    have h2 := h.map (resHom U)
    simpa [hĒ, hU, autSub] using h2
  have hENorm : Ē ≤ Subgroup.normalizer (Λ : Set (MulAut U)) :=
    CFSG.CGT.PushingUpLit.BHS.autSub_le_normalizer (E := L) (A := E) (U := U) hEN
  let incl : ↥Ē →* ↥(Subgroup.normalizer (Λ : Set (MulAut U))) := Subgroup.inclusion hENorm
  let ρ : ↥Ē →* MulAut Λ := (Subgroup.normalizerMonoidHom Λ).comp incl
  have hmem_ker : ∀ y : ↥Ē,
      y ∈ ρ.ker ↔ (y : MulAut U) ∈ Subgroup.centralizer (Λ : Set (MulAut U)) := by
    intro y
    rw [MonoidHom.mem_ker]
    change (Subgroup.normalizerMonoidHom Λ) (incl y) = 1 ↔
      (y : MulAut U) ∈ Subgroup.centralizer (Λ : Set (MulAut U))
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hker_map : ρ.ker.map (Subgroup.subtype Ē) =
      Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U)) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hmem_ker y).mp hy⟩
    · rintro ⟨hxĒ, hxcent⟩
      exact ⟨⟨x, hxĒ⟩, (hmem_ker ⟨x, hxĒ⟩).mpr hxcent, rfl⟩
  have hcard_ker : Nat.card ↥ρ.ker =
      Nat.card ↥(Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U))) := by
    have h := Subgroup.card_map_of_injective (K := ρ.ker) (f := Subgroup.subtype Ē)
      (Subgroup.subtype_injective Ē)
    rw [hker_map] at h
    exact h.symm
  have hC : IsElemAbelian q (Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U))) :=
    hEab_aut.mono inf_le_left
  have hCcard_le : Nat.card ↥(Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U))) ≤ q := by
    have hcyc := (s16h_H5_bridge_cent_cyclic_odd (W := W) hc hirr
      (E := E) hE).1
    haveI : IsCyclic ↥(Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U))) := hcyc
    have hdvd : Nat.card ↥(Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U))) ∣ q := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hC.2 (x : MulAut U) x.2)
    exact Nat.le_of_dvd hq.pos hdvd
  have hker_le : Nat.card ↥ρ.ker ≤ q := by
    rw [hcard_ker]; exact hCcard_le
  have hρab : IsElemAbelian q ρ.range := by
    have htop : IsElemAbelian q (⊤ : Subgroup ↥Ē) := s16h_isElemAbelian_top hEab_aut
    have h := htop.map ρ
    rw [← MonoidHom.range_eq_map] at h
    exact h
  have hkerL : ((resHom U).comp (Subgroup.inclusion hLU)).ker = ⊥ := by
    haveI : IsSimpleGroup ↥L := isSimpleGroup_of_isL3 h.1
    by_contra hne
    have hker_top : ((resHom U).comp (Subgroup.inclusion hLU)).ker = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top
        ((resHom U).comp (Subgroup.inclusion hLU)).ker with hbot | htop
      · exact absurd hbot hne
      · exact htop
    have hfix : ∀ u ∈ U, ∀ l ∈ L, l u = u := by
      intro u hu l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ ((resHom U).comp (Subgroup.inclusion hLU)).ker := by
        rw [hker_top]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have h := congrArg (fun g : MulAut U => ((g ⟨u, hu⟩ : U) : W)) hmem
      simpa [MonoidHom.comp_apply, resHom_apply, Subgroup.coe_inclusion] using h
    have hZeq : U ⊓ fixV L = U := by
      refine le_antisymm inf_le_left ?_
      intro u hu
      exact ⟨hu, fun l hl => hfix u hu l hl⟩
    have hzero : E3.mQuot U (U ⊓ fixV L) = 0 := by rw [hZeq, E3.mQuot_self]
    have h8 : E3.mQuot U (U ⊓ fixV L) = 8 := by
      rw [hU]; exact h.2
    omega
  have hrange_eq : ((resHom U).comp (Subgroup.inclusion hLU)).range = Λ := by
    rw [hΛ, autSub, MonoidHom.range_comp, Subgroup.inclusion_range]
  let eL : ↥L ≃* ↥Λ := (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).mp hkerL)).trans
    (MulEquiv.subgroupCongr hrange_eq)
  have hL3Λ : IsL3 ↥Λ 1 := CFSG.Blueprint.LieModel.of_mulEquiv eL h.1
  have hcard_aut : Nat.card (MulAut Λ) = 336 := by
    obtain ⟨e2⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3Λ
    rw [Nat.card_congr (MulAut.congr e2).toEquiv,
      CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  have hq2not : ¬ q ^ 2 ∣ Nat.card (MulAut Λ) := by
    rw [hcard_aut]; exact s16h_not_sq_dvd_336 hq hq2
  have hrange_le : Nat.card ρ.range ≤ q := by
    haveI : Fact q.Prime := ⟨hq⟩
    have h := CFSG.LargeExtraspecial.S63.card_le_of_isPGroup_of_not_dvd
      (G := MulAut Λ) (p := q) (k := 1) hq2not ρ.range hρab.isPGroup
    simpa using h
  have hcard := card_ker_mul_card_range ρ
  have hmain : Nat.card ↥Ē = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hcard.symm
  calc Nat.card ↥(autSub E (commSub ⊤ L)) = Nat.card ↥Ē := rfl
    _ = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hmain
    _ ≤ q * q := Nat.mul_le_mul hker_le hrange_le
    _ = q ^ 2 := by ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
