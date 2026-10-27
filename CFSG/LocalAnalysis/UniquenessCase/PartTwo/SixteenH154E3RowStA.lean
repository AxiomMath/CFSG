module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowStAA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.LargeExtraspecial.S63AAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_e3_finite_mulAut {X : Type*} [Mul X] [Finite X] : Finite (MulAut X) := by
  classical
  exact Finite.of_injective (fun f : MulAut X => (f : X → X))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_e3_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16h_e3_normalizer_le_stabSub_fixV {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) := by
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h1 : (g * x * g⁻¹) (g z) = g z := hz _ hx'
    have h2 : (g * x * g⁻¹) (g z) = g (x z) := by simp [MulAut.mul_apply]
    exact g.injective (by rw [← h2, h1])
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hg) x).mp hx
    have h1 : (g⁻¹ * x * g) z = z := hz _ hx'
    have h2 : g ((g⁻¹ * x * g) z) = g z := by rw [h1]
    have h3 : x (g z) = g ((g⁻¹ * x * g) z) := by simp [MulAut.mul_apply]
    rw [h3, h2]

private theorem s16h_e3_not_sq_dvd_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
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

private theorem s16h_e3_isElemAbelian_top {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) : IsElemAbelian p (⊤ : Subgroup ↥E) := by
  haveI : IsMulCommutative ↥E := h.1
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : ↥E) (b : ↥E))⟩⟩,
    fun x _ => Subtype.ext (h.2 (x : ↥E) (x : ↥E).2)⟩

theorem s16h_H5_blockBound_one_of_autSub {A L : Subgroup (MulAut W)} {q : ℕ}
    (h : ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian q E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q) :
    s16h_BlockBound A L q 1 := by
  intro E hE hEab
  have hU : E ≤ stabSub (commSub ⊤ L) := by
    intro g hg
    exact s16h_e3_commSub_stab (L := L) (g := g) (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  rw [← hcard]
  exact Nat.mul_le_mul_right _ (by simpa using h E hE hEab)

theorem s16h_H5_rowSt8_autSub_inf_centralizer_eq_bot [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    autSub E (commSub ⊤ L) ⊓
      Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) = ⊥ := by
  classical
  haveI : Finite (MulAut W) := s16h_e3_finite_mulAut (X := W)
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  have hEN : E ≤ normalizer (L : Set (MulAut W)) :=
    fun e he => (Subgroup.mem_inf.mp (hE he)).2
  have hLU : L ≤ stabSub U := by
    rw [hU]
    intro l hl
    exact s16h_e3_commSub_stab (L := L) (Subgroup.le_normalizer hl)
  have hLfix : L ≤ stabSub (fixV L) := fun l hl =>
    s16h_e3_normalizer_le_stabSub_fixV (L := L) (Subgroup.le_normalizer hl)
  have hLZ : L ≤ stabSub Z := by
    intro l hl
    rw [hZ, mem_stabSub]
    intro w
    exact ⟨fun hw => ⟨(hLU hl w).1 hw.1, (hLfix hl w).1 hw.2⟩,
      fun hw => ⟨(hLU hl w).2 hw.1, (hLfix hl w).2 hw.2⟩⟩
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_e3_commSub_stab (L := L) (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_e3_normalizer_le_stabSub_fixV (L := L) (hEN he)
  have hEZ : E ≤ stabSub Z := by
    intro e he
    rw [hZ, mem_stabSub]
    intro w
    exact ⟨fun hw => ⟨(hEU he w).1 hw.1, (hEfix he w).1 hw.2⟩,
      fun hw => ⟨(hEU he w).2 hw.1, (hEfix he w).2 hw.2⟩⟩
  have hsec := s16h_H5_rowSt8_sec_centralizer_eq_bot hc h hirr
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxE, hxcent⟩
  obtain ⟨e, he, rfl⟩ := mem_autSub.mp hxE
  have hstab : resHom U e ∈ stabSub (Z.subgroupOf U) := by
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      show (z : W) ∈ Z
      have hz' : ((e : MulAut W)⁻¹) ((e : MulAut W) (z : W)) ∈ Z :=
        (hEZ (E.inv_mem he) ((e : MulAut W) (z : W))).2 (by simpa [resHom_apply] using hz)
      simpa using hz'
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact (hEZ he (z : W)).2 hz
  let xbar : MulAut (Sec U Z) := quotHom (Z.subgroupOf U) ⟨resHom U e, hstab⟩
  have hcent_bar : xbar ∈ Subgroup.centralizer (autSec L U Z : Set (MulAut (Sec U Z))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ (B5.secHom L hLU hLZ).range := by
      rwa [B5.range_secHom L hLU hLZ]
    obtain ⟨l, rfl⟩ := ha'
    have hcommU : resHom U e * resHom U ⟨l, hLU l.2⟩ =
        resHom U ⟨l, hLU l.2⟩ * resHom U e := by
      have hl : resHom U ⟨l, hLU l.2⟩ ∈ autSub L U :=
        mem_autSub.mpr ⟨⟨l, hLU l.2⟩, l.2, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hxcent (resHom U ⟨l, hLU l.2⟩) hl).symm
    have hcommV : (⟨resHom U e, hstab⟩ : stabSub (Z.subgroupOf U)) *
        B5.secRho L hLU hLZ l =
        B5.secRho L hLU hLZ l * ⟨resHom U e, hstab⟩ := by
      apply Subtype.ext
      exact hcommU
    calc B5.secHom L hLU hLZ l * xbar
        = quotHom (Z.subgroupOf U) (B5.secRho L hLU hLZ l) *
            quotHom (Z.subgroupOf U) ⟨resHom U e, hstab⟩ := rfl
      _ = quotHom (Z.subgroupOf U) (B5.secRho L hLU hLZ l * ⟨resHom U e, hstab⟩) := by
            rw [map_mul]
      _ = quotHom (Z.subgroupOf U) (⟨resHom U e, hstab⟩ * B5.secRho L hLU hLZ l) := by
            rw [← hcommV]
      _ = quotHom (Z.subgroupOf U) ⟨resHom U e, hstab⟩ *
            quotHom (Z.subgroupOf U) (B5.secRho L hLU hLZ l) := by rw [map_mul]
      _ = xbar * B5.secHom L hLU hLZ l := rfl
  have hxbar1 : xbar = 1 := by
    rw [hsec] at hcent_bar
    exact Subgroup.mem_bot.mp hcent_bar
  have htriv : ∀ v : ↥U, ((resHom U e) v * v⁻¹ : ↥U) ∈ Z.subgroupOf U := by
    intro v
    have h := congrArg (fun f : MulAut (Sec U Z) => f (QuotientGroup.mk v)) hxbar1
    have h2 : (QuotientGroup.mk ((resHom U e) v) : Sec U Z) = QuotientGroup.mk v := by
      simpa [xbar, quotHom_mk] using h
    exact (mk_eq_mk_iff (U := Z.subgroupOf U) _ _).1 h2
  have htriv' : ∀ w ∈ commSub ⊤ L, (e : MulAut W) w = w :=
    s16h_H5_triv_of_triv_quot hc.comp (hEN he) (fun w hw => by
      have h := htriv ⟨w, hw⟩
      rw [Subgroup.mem_subgroupOf] at h
      show (e : MulAut W) w * w⁻¹ ∈ Z
      simpa [resHom_apply] using h)
  refine MulEquiv.ext fun v => ?_
  exact Subtype.ext (htriv' (v : W) v.2)

theorem s16h_H5_rowSt8_autSub_le_one [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q := by
  classical
  haveI : Finite (MulAut W) := s16h_e3_finite_mulAut (X := W)
  set U : Subgroup W := commSub ⊤ L with hU
  set Λ : Subgroup (MulAut U) := autSub L U with hΛ
  set Ē : Subgroup (MulAut U) := autSub E U with hĒ
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (Subgroup.mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_e3_commSub_stab (L := L) (hEN he)
  have hLU : L ≤ stabSub U := by
    rw [hU]
    intro l hl
    exact s16h_e3_commSub_stab (L := L) (Subgroup.le_normalizer hl)
  have hEab_aut : IsElemAbelian q Ē := by
    have h := hEab.subgroupOf (stabSub U)
    have h2 := h.map (resHom U)
    simpa [hĒ, hU, autSub] using h2
  have hcent : Ē ⊓ Subgroup.centralizer (Λ : Set (MulAut U)) = ⊥ := by
    rw [hĒ, hΛ, hU]
    exact s16h_H5_rowSt8_autSub_inf_centralizer_eq_bot hc h hirr hq hq2 hE hEab
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
  have hker_bot : ρ.ker = ⊥ :=
    Subgroup.map_injective (Subgroup.subtype_injective Ē)
      (by rw [hker_map, hcent, Subgroup.map_bot])
  have hρab : IsElemAbelian q ρ.range := by
    have htop : IsElemAbelian q (⊤ : Subgroup ↥Ē) := s16h_e3_isElemAbelian_top hEab_aut
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
    rw [hcard_aut]; exact s16h_e3_not_sq_dvd_336 hq hq2
  have hrange_le : Nat.card ρ.range ≤ q := by
    haveI : Fact q.Prime := ⟨hq⟩
    have h := CFSG.LargeExtraspecial.S63.card_le_of_isPGroup_of_not_dvd
      (G := MulAut Λ) (p := q) (k := 1) hq2not ρ.range hρab.isPGroup
    simpa using h
  have hcard := card_ker_mul_card_range ρ
  have hmain : Nat.card ↥Ē = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hcard.symm
  calc Nat.card ↥(autSub E (commSub ⊤ L)) = Nat.card ↥Ē := by rw [hĒ, hU]
    _ = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hmain
    _ = 1 * Nat.card ↥ρ.range := by rw [hker_bot, Subgroup.card_bot]
    _ = Nat.card ↥ρ.range := one_mul _
    _ ≤ q := hrange_le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
