module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenA
public import CFSG.GroupTheory.SolvableTransport
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenB
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.E3Restrict
public import CFSG.Quasithin.Background.SmithD321SzK

public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

namespace SevenSevenA

variable {W : Type} [CommGroup W] [Finite W]

theorem inf_conjSub_le_center {K : Subgroup (MulAut W)} {Y : Subgroup (MulAut W)}
    (hK : IsComponentOf K Y) {a : MulAut W} (ha : a ∈ Y) (hne : conjSub77 K a ≠ K) :
    K ⊓ conjSub77 K a ≤ (Subgroup.center ↥K).map K.subtype := by
  have hKa : IsComponentOf (conjSub77 K a) Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK ha
  have hcomm : ⁅conjSub77 K a, K⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hKa hK hne
  have hcent : conjSub77 K a ≤ Subgroup.centralizer (K : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  calc K ⊓ conjSub77 K a ≤ K ⊓ Subgroup.centralizer (K : Set (MulAut W)) :=
        inf_le_inf_left _ hcent
    _ = (Subgroup.center ↥K).map K.subtype := CFSG.GroupTheory.inf_centralizer_eq_map_center K

theorem actOnSub_mul_conj {A X : Subgroup (MulAut W)} {U : Subgroup W}
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (a : ↥A) (x : ↥X) :
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hAU a *
        CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hXU x *
        (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hAU a)⁻¹ =
      CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hXU
        ⟨a * (x : MulAut W) * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hAX a.2) (x : MulAut W)).mp x.2⟩ := by
  ext u
  simp only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom,
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
  rfl

theorem w4Lem7_7_of_normalizer_le_centralizer_aux (hW : ∀ w : W, w ^ 2 = 1)
    {Y K A : Subgroup (MulAut W)} {k : ℕ} [Finite ↥K]
    (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hlt : ∀ n, Nonempty (ACandidate ↥K n) → n < k)
    (hNC : A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W))) : ⁅A, K⁆ = ⊥ := by
  classical
  by_contra hne
  have hk2 : 2 ≤ k := w4Lem7_7_two_le hW hK hA hlt
  have hAY : A ≤ Y := hA.1
  have hAnC : ¬ A ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    intro h
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  let B : Subgroup (MulAut W) := SevenSevenB.centralizerInA A K
  have hBN : A ⊓ Subgroup.normalizer (K : Set (MulAut W)) = B := by
    change A ⊓ Subgroup.normalizer (K : Set (MulAut W)) =
      A ⊓ Subgroup.centralizer (K : Set (MulAut W))
    exact le_antisymm (le_inf inf_le_left hNC)
      (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
  have hBleA : B ≤ A := inf_le_left
  have hBleC : B ≤ Subgroup.centralizer (K : Set (MulAut W)) := inf_le_right
  have hBleN : B ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    hBleC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, haA, haC⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (K : Set (MulAut W)) := by
    by_contra h
    push Not at h
    exact hAnC h
  have hAel : CFSG.IsElementaryAbelian 2 ↥A :=
    CFSG.Quasithin.B1.isElementaryAbelian_of_isElemAbelian2 hA.2.2.1
  obtain ⟨D, hDleA, hDinf, hDsup⟩ :=
    SevenSevenB.exists_compl_normalizerInA_77 (K := K) hA
  have hinf : B ⊓ D = ⊥ := by
    rw [inf_comm, ← hBN]
    exact hDinf
  have hsup : B ⊔ D = A := by
    rw [← hBN]
    simpa [SevenSevenB.normalizerInA] using hDsup
  have hDne : D ≠ ⊥ := by
    intro hbot
    apply hAnC
    intro x hx
    have hx' : x ∈ B ⊔ D := by rw [hsup]; exact hx
    rw [hbot, sup_bot_eq] at hx'
    exact hBleC hx'
  have hDN : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥ := by
    calc D ⊓ Subgroup.normalizer (K : Set (MulAut W))
        = D ⊓ (A ⊓ Subgroup.normalizer (K : Set (MulAut W))) := by
          rw [← inf_assoc, inf_eq_left.mpr hDleA]
      _ = D ⊓ B := by rw [hBN]
      _ = ⊥ := by rw [inf_comm]; exact hinf
  have hDY : D ≤ Y := hDleA.trans hAY
  have hq' : CFSG.IsQuasisimple ↥K :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  obtain ⟨x₀, hx₀odd, hx₀nz⟩ :=
    CFSG.Quasithin.SmithD321.exists_odd_not_mem_center hq'
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' _
  have hxbar : π x₀ ≠ 1 := by
    intro h
    exact hx₀nz ((QuotientGroup.eq_one_iff x₀).mp h)
  have hoddbar : Odd (orderOf (π x₀)) :=
    hx₀odd.of_dvd_nat (orderOf_map_dvd π x₀)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by
    intro h
    exact hxbar ((orderOf_eq_one_iff (x := π x₀)).mp h))
  have hpodd : Odd p := hoddbar.of_dvd_nat hpdvd
  have hpne2 : p ≠ 2 := hoddbar.ne_two_of_dvd_nat hpdvd
  have hpFact : Fact p.Prime := ⟨hp⟩
  let P : Sylow p ↥K := Classical.choice Sylow.nonempty
  let Pbar : Sylow p (↥K ⧸ Subgroup.center ↥K) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hpbar : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    hpdvd.trans (orderOf_dvd_natCard (π x₀))
  have hpPbar : p ∣ Nat.card ↥(Pbar : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    Sylow.dvd_card_of_dvd_card Pbar hpbar
  have hPnotZ : ¬ (P : Subgroup ↥K) ≤ Subgroup.center ↥K := by
    intro hle
    have hmapbot : (P : Subgroup ↥K).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff x).mpr (hle hx)
    have hPbar_eq : (Pbar : Subgroup (↥K ⧸ Subgroup.center ↥K)) = ⊥ := by
      rw [Sylow.coe_mapSurjective]
      exact hmapbot
    rw [hPbar_eq, Subgroup.card_bot] at hpPbar
    exact hp.ne_one (Nat.dvd_one.mp hpPbar)
  let Pamb : Subgroup (MulAut W) := (P : Subgroup ↥K).map K.subtype
  have hPamb_p : IsPGroup p Pamb := P.isPGroup'.map K.subtype
  have hPambZ : ¬ Pamb ≤ (Subgroup.center ↥K).map K.subtype := by
    intro hle
    apply hPnotZ
    intro x hx
    have hxP : (x : MulAut W) ∈ Pamb := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxcenter : x ∈ ((Subgroup.center ↥K).map K.subtype).subgroupOf K := hle hxP
    simpa [CFSG.subgroupOf_map_subtype_eq] using hxcenter
  let X : Subgroup (MulAut W) := orbitJoin77 Pamb D
  haveI : Fintype ↥D := Fintype.ofFinite _
  haveI : DecidableEq ↥D := Classical.decEq _
  have hXp : IsPGroup p X := by
    have hPc : ∀ d : ↥D, IsPGroup p (conjSub77 Pamb (d : MulAut W)) := fun d =>
      hPamb_p.map (MulAut.conj (d : MulAut W)).toMonoidHom
    have hc : ∀ d e : ↥D, d ≠ e →
        ⁅conjSub77 Pamb (d : MulAut W), conjSub77 Pamb (e : MulAut W)⁆ = ⊥ := by
      intro d e hde
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hle_d : conjSub77 Pamb (d : MulAut W) ≤ conjSub77 K (d : MulAut W) :=
        Subgroup.map_mono (Subgroup.map_subtype_le (P : Subgroup ↥K))
      have hle_e : conjSub77 Pamb (e : MulAut W) ≤ conjSub77 K (e : MulAut W) :=
        Subgroup.map_mono (Subgroup.map_subtype_le (P : Subgroup ↥K))
      have hbot := conjSub_commute_of_ne hK hDY hDN hde
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot (hle_d hx)) y (hle_e hy)
    have h := CFSG.Quasithin.C2Push.isPGroup_iSup_of_pairwise_commute
      (A := fun d : ↥D => conjSub77 Pamb (d : MulAut W)) hPc hc
    change IsPGroup p (orbitJoin77 Pamb D) at h ⊢
    exact h
  have hBcentX : B ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    symm
    change x ∈ orbitJoin77 Pamb D at hx
    rw [orbitJoin77] at hx
    refine Subgroup.iSup_induction (fun d : ↥D => conjSub77 Pamb (d : MulAut W))
      (C := fun x => b * x = x * b) hx ?_ ?_ ?_
    · intro d x hx
      obtain ⟨p, hpP, hpx⟩ := Subgroup.mem_map.mp hx
      have hpK : p ∈ K := Subgroup.map_subtype_le (P : Subgroup ↥K) hpP
      have hbp : b * p = p * b := (hBleC hb p hpK).symm
      have hbd : b * (d : MulAut W) = (d : MulAut W) * b :=
        hA.2.2.1.1 b (hBleA hb) (d : MulAut W) (hDleA d.2)
      have hbd' : b * (d : MulAut W)⁻¹ = (d : MulAut W)⁻¹ * b := by
        calc b * (d : MulAut W)⁻¹
            = (d : MulAut W)⁻¹ * ((d : MulAut W) * b) * (d : MulAut W)⁻¹ := by group
          _ = (d : MulAut W)⁻¹ * (b * (d : MulAut W)) * (d : MulAut W)⁻¹ := by rw [← hbd]
          _ = (d : MulAut W)⁻¹ * b := by group
      rw [← hpx]
      change b * ((MulAut.conj (d : MulAut W)) p) = (MulAut.conj (d : MulAut W)) p * b
      rw [MulAut.conj_apply]
      calc b * ((d : MulAut W) * p * (d : MulAut W)⁻¹)
          = (b * (d : MulAut W)) * p * (d : MulAut W)⁻¹ := by group
        _ = ((d : MulAut W) * b) * p * (d : MulAut W)⁻¹ := by rw [hbd]
        _ = (d : MulAut W) * (b * p) * (d : MulAut W)⁻¹ := by group
        _ = (d : MulAut W) * (p * b) * (d : MulAut W)⁻¹ := by rw [hbp]
        _ = (d : MulAut W) * p * (b * (d : MulAut W)⁻¹) := by group
        _ = (d : MulAut W) * p * ((d : MulAut W)⁻¹ * b) := by rw [hbd']
        _ = ((d : MulAut W) * p * (d : MulAut W)⁻¹) * b := by group
    · simp
    · intro x y hx hy
      calc b * (x * y) = (b * x) * y := by group
        _ = (x * b) * y := by rw [hx]
        _ = x * (b * y) := by group
        _ = x * (y * b) := by rw [hy]
        _ = (x * y) * b := by group
  have hBnormX : B ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    hBcentX.trans (Subgroup.centralizer_le_normalizer _)
  have hDnormX : D ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    intro d0 hd0
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (orbitJoin77 Pamb D).map (MulAut.conj d0).toMonoidHom = orbitJoin77 Pamb D
    rw [orbitJoin77, Subgroup.map_iSup]
    have hcomp : ∀ d : ↥D,
        (conjSub77 Pamb (d : MulAut W)).map (MulAut.conj d0).toMonoidHom =
          conjSub77 Pamb (d0 * (d : MulAut W)) := by
      intro d
      rw [conjSub77, Subgroup.map_map, conjSub77, mulAut_conj_comp]
    calc ⨆ d : ↥D, (conjSub77 Pamb (d : MulAut W)).map (MulAut.conj d0).toMonoidHom
        = ⨆ d : ↥D, conjSub77 Pamb (d0 * (d : MulAut W)) := iSup_congr hcomp
      _ = ⨆ d : ↥D, conjSub77 Pamb (d : MulAut W) :=
          Equiv.iSup_comp (g := fun d : ↥D => conjSub77 Pamb (d : MulAut W))
            (e := Equiv.mulLeft ⟨d0, hd0⟩)
  have hAnormX : A ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    rw [← hsup]
    exact sup_le hBnormX hDnormX
  have hDfaithX : ∀ d ∈ D, (∀ x ∈ X, d * x * d⁻¹ = x) → d = 1 := by
    intro d hd hfix
    by_cases hdN : d ∈ Subgroup.normalizer (K : Set (MulAut W))
    · have hdB : d ∈ B := by
        rw [← hBN]
        exact ⟨hDleA hd, hdN⟩
      have hDB : d ∈ B ⊓ D := ⟨hdB, hd⟩
      rw [hinf] at hDB
      exact Subgroup.mem_bot.mp hDB
    · exfalso
      apply hPambZ
      have hdY : d ∈ Y := hAY (hDleA hd)
      have hne : conjSub77 K d ≠ K := by
        intro h
        exact hdN ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr h)
      have hle1 : Pamb ≤ K ⊓ conjSub77 K d := by
        intro p hp
        refine ⟨Subgroup.map_subtype_le (P : Subgroup ↥K) hp, ?_⟩
        refine Subgroup.mem_map.mpr ⟨p, Subgroup.map_subtype_le (P : Subgroup ↥K) hp, ?_⟩
        have hconj : (MulAut.conj d) p = d * p * d⁻¹ := by
          ext w
          rw [MulAut.conj_apply]
        rw [show (MulEquiv.toMonoidHom (MulAut.conj d)) p = (MulAut.conj d) p from rfl, hconj]
        exact hfix p (by
            change p ∈ orbitJoin77 Pamb D
            rw [orbitJoin77]
            exact Subgroup.mem_iSup_of_mem (1 : ↥D)
              (Subgroup.mem_map.mpr ⟨p, hp, by simp [conjSub77]⟩))
      exact hle1.trans (inf_conjSub_le_center hK hdY hne)
  let U : Subgroup W := fixV B
  have hAU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
    intro a ha u hu
    change u ∈ fixV B at hu
    change a u ∈ fixV B
    rw [mem_fixV] at hu ⊢
    intro b hb
    calc b (a u) = (b * a) u := rfl
      _ = (a * b) u := by rw [hA.2.2.1.1 b (hBleA hb) a ha]
      _ = a (b u) := rfl
      _ = a u := by rw [hu b hb]
  have hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U := by
    intro x hx u hu
    change u ∈ fixV B at hu
    change x u ∈ fixV B
    rw [mem_fixV] at hu ⊢
    intro b hb
    have hxb : x * b = b * x :=
      Subgroup.mem_centralizer_iff.mp (hBcentX hb) x hx
    calc b (x u) = (b * x) u := rfl
      _ = (x * b) u := by rw [hxb]
      _ = x (b u) := rfl
      _ = x u := by rw [hu b hb]
  let f : ↥A →* MulAut ↥U :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hAU
  let g : ↥X →* MulAut ↥U :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hXU
  let Astar : Subgroup (MulAut ↥U) := f.range
  let Xstar : Subgroup (MulAut ↥U) := g.range
  have hXodd : Odd (Nat.card ↥X) := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hB2 : IsPGroup 2 B := (E3.isPGroup_of_isElemAbelian2 hA.2.2.1).to_le hBleA
  have hker_g : ∀ x : ↥X, g x = 1 → x = 1 := by
    intro x hx
    apply Subtype.ext
    exact CFSG.Quasithin.B1.eq_one_of_fixes_fixV hW hXodd hB2
      (fun y hy e he => Subgroup.mem_centralizer_iff.mp (hBcentX he) y hy)
      x.2 (fun u hu => by
        have h := congrArg (fun φ : MulAut ↥U => (φ ⟨u, hu⟩ : W)) hx
        simpa [g, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply] using h)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 : x * y⁻¹ = 1 := hker_g (x * y⁻¹) (by
      rw [map_mul, map_inv, hxy, mul_inv_cancel])
    calc x = x * y⁻¹ * y := by group
      _ = y := by rw [h1]; group
  have hAstarN : Astar ≤ Subgroup.normalizer (Xstar : Set (MulAut ↥U)) :=
    CFSG.Quasithin.E3.actOnSub_range_le_normalizer hXU hAU hAnormX
  have hAstar_faithful : ∀ a : ↥A, (∀ y ∈ Xstar, f a * y * (f a)⁻¹ = y) → f a = 1 := by
    intro a htriv
    have hacentX : ∀ x ∈ X, (a : MulAut W) * x * (a : MulAut W)⁻¹ = x := by
      intro x hx
      have h1 := htriv (g ⟨x, hx⟩) (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
      rw [actOnSub_mul_conj hAU hXU hAnormX a ⟨x, hx⟩] at h1
      exact congrArg Subtype.val (hg_inj h1)
    have haN : (a : MulAut W) ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
      by_contra haN
      apply hPambZ
      have hne : conjSub77 K (a : MulAut W) ≠ K := by
        intro h
        exact haN ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr h)
      have hle1 : Pamb ≤ K ⊓ conjSub77 K (a : MulAut W) := by
        intro p hp
        refine ⟨Subgroup.map_subtype_le (P : Subgroup ↥K) hp, ?_⟩
        refine Subgroup.mem_map.mpr ⟨p, Subgroup.map_subtype_le (P : Subgroup ↥K) hp, ?_⟩
        have hpX : p ∈ X := by
          change p ∈ orbitJoin77 Pamb D
          rw [orbitJoin77]
          exact Subgroup.mem_iSup_of_mem (1 : ↥D)
            (Subgroup.mem_map.mpr ⟨p, hp, by simp [conjSub77]⟩)
        have hap := hacentX p hpX
        have hconj : (MulAut.conj (a : MulAut W)) p =
            (a : MulAut W) * p * (a : MulAut W)⁻¹ := by
          ext w
          rw [MulAut.conj_apply]
        rw [show (MulEquiv.toMonoidHom (MulAut.conj (a : MulAut W))) p =
          (MulAut.conj (a : MulAut W)) p from rfl, hconj]
        exact hap
      exact hle1.trans (inf_conjSub_le_center hK (hAY a.2) hne)
    have haB : (a : MulAut W) ∈ B := by
      rw [← hBN]
      exact ⟨a.2, haN⟩
    ext u
    rw [MulAut.one_apply, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
    exact (mem_fixV.mp u.2) a haB
  have hAstar_faithful' : ∀ y ∈ Astar,
      (∀ z ∈ Xstar, y * z * y⁻¹ = z) → y = 1 := by
    rintro y ⟨a, rfl⟩ h
    exact hAstar_faithful a h
  have hAstar_ne : Astar ≠ ⊥ := by
    intro hbot
    apply hDne
    rw [eq_bot_iff]
    intro d hd
    have hfd : f ⟨d, hDleA hd⟩ = 1 := by
      have hmem : f ⟨d, hDleA hd⟩ ∈ Astar := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hd1 : d = 1 := hDfaithX d hd (by
      intro x hx
      have h1 : g ⟨d * x * d⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hAnormX (hDleA hd)) x).mp hx⟩ = g ⟨x, hx⟩ := by
        have h := actOnSub_mul_conj hAU hXU hAnormX ⟨d, hDleA hd⟩ ⟨x, hx⟩
        have h2 : f ⟨d, hDleA hd⟩ * g ⟨x, hx⟩ * (f ⟨d, hDleA hd⟩)⁻¹ = g ⟨x, hx⟩ := by
          rw [hfd]; group
        rw [h] at h2
        exact h2
      exact congrArg Subtype.val (hg_inj h1))
    simpa using hd1
  have hAstar_mem : Astar ∈ E3.aSet k (Xstar ⊔ Astar) := by
    have h := E3.mem_aSet_actOnSub (X := Y) (A := A) (k := k) hA hAU
      (Y := Xstar ⊔ Astar) le_sup_right hAstar_ne
    simpa only [Astar, f] using h
  have hXstar_p : IsPGroup p Xstar := by
    have htop : IsPGroup p (⊤ : Subgroup ↥X) := hXp.of_equiv Subgroup.topEquiv.symm
    have h := htop.map g
    rwa [Subgroup.map_top] at h
  have hXstar_odd : Odd (Nat.card ↥Xstar) := by
    obtain ⟨n, hn⟩ := hXstar_p.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hAstar_2 : IsPGroup 2 Astar := by
    have htop : IsPGroup 2 (⊤ : Subgroup ↥A) :=
      (E3.isPGroup_of_isElemAbelian2 hA.2.2.1).of_equiv Subgroup.topEquiv.symm
    have h := htop.map f
    rwa [Subgroup.map_top] at h
  have hYsolv : Group.IsSolvable ↥(Xstar ⊔ Astar) := by
    apply CFSG.GroupTheory.isSolvable_sup_of_isPGroup_of_le_normalizer
    · have hNilp : Group.IsNilpotent ↥Xstar := hXstar_p.isNilpotent
      exact IsNilpotent.to_isSolvable
    · exact hAstar_2
    · exact hAstarN
  have hY'O2 : CFSG.pCore 2 ↥(Xstar ⊔ Astar) = ⊥ := by
    apply CFSG.SignalizerFunctor.Helpers.corefree_hall_product_normalized_complement_trivial
      (GroupType := ↥(Xstar ⊔ Astar)) p hp
      (complement := Astar.subgroupOf (Xstar ⊔ Astar))
      (factor := Xstar.subgroupOf (Xstar ⊔ Astar))
      (target := CFSG.pCore 2 ↥(Xstar ⊔ Astar))
    · have hcard : Nat.card ↥(Astar.subgroupOf (Xstar ⊔ Astar)) = Nat.card ↥Astar :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rw [hcard]
      obtain ⟨n, hn⟩ := hAstar_2.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_right.mpr hpodd).pow_right n
    · exact hXstar_p.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
    · have hsupY : Astar.subgroupOf (Xstar ⊔ Astar) ⊔
          Xstar.subgroupOf (Xstar ⊔ Astar) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup le_sup_right le_sup_left, sup_comm]
        exact Subgroup.subgroupOf_self _
      have hN : Astar.subgroupOf (Xstar ⊔ Astar) ≤
          Subgroup.normalizer (Xstar.subgroupOf (Xstar ⊔ Astar) :
            Set ↥(Xstar ⊔ Astar)) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp (hAstarN ha) (y : MulAut ↥U)
      have h := Subgroup.coe_mul_of_left_le_normalizer_right
        (Astar.subgroupOf (Xstar ⊔ Astar)) (Xstar.subgroupOf (Xstar ⊔ Astar)) hN
      rw [hsupY] at h
      exact h.symm
    ·
      rw [eq_bot_iff]
      intro m hm
      let M : Subgroup ↥(Xstar ⊔ Astar) := (Astar.subgroupOf (Xstar ⊔ Astar)).normalCore
      have hMne : M.Normal := Subgroup.normalCore_normal _
      have hMle : M ≤ Astar.subgroupOf (Xstar ⊔ Astar) := Subgroup.normalCore_le _
      have hM2 : IsPGroup 2 M :=
        hAstar_2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm |>.to_le hMle
      have hX'odd : Odd (Nat.card ↥(Xstar.subgroupOf (Xstar ⊔ Astar))) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
        exact hXstar_odd
      have hdisj : M ⊓ Xstar.subgroupOf (Xstar ⊔ Astar) = ⊥ :=
        CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hM2 hX'odd
      have hXn : (Xstar.subgroupOf (Xstar ⊔ Astar)).Normal := by
        refine Subgroup.normal_subgroupOf_of_le_normalizer (H := Xstar ⊔ Astar)
          (N := Xstar) (sup_le Subgroup.le_normalizer hAstarN)
      have hcomm : ⁅M, Xstar.subgroupOf (Xstar ⊔ Astar)⁆ = ⊥ := by
        rw [eq_bot_iff]
        exact (Subgroup.commutator_le_inf M _).trans (le_of_eq hdisj)
      have hcent : M ≤ Subgroup.centralizer
          (Xstar.subgroupOf (Xstar ⊔ Astar) : Set ↥(Xstar ⊔ Astar)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hmA : m ∈ Astar.subgroupOf (Xstar ⊔ Astar) := hMle hm
      have htriv : ∀ z ∈ Xstar,
          (m : MulAut ↥U) * z * (m : MulAut ↥U)⁻¹ = z := by
        intro z hz
        have hz' : (⟨z, Subgroup.mem_sup_left hz⟩ : ↥(Xstar ⊔ Astar)) ∈
            Xstar.subgroupOf (Xstar ⊔ Astar) := hz
        have h := Subgroup.mem_centralizer_iff.mp (hcent hm)
          ⟨z, Subgroup.mem_sup_left hz⟩ hz'
        have h' : (m : MulAut ↥U) * z = z * (m : MulAut ↥U) := by
          simpa using (congrArg Subtype.val h).symm
        rw [h']
        group
      have h1 : (m : MulAut ↥U) = 1 := hAstar_faithful' (m : MulAut ↥U) hmA htriv
      exact Subtype.ext h1
    · have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥(Xstar ⊔ Astar)) :=
        CFSG.pCore_isPGroup (p := 2) (G := ↥(Xstar ⊔ Astar))
      obtain ⟨n, hn⟩ := hP2.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_right.mpr hpodd).pow_right n
    · rw [Subgroup.normalizer_eq_top (H := CFSG.pCore 2 ↥(Xstar ⊔ Astar))]
      exact le_top
  have hAstar_mem2 : Astar ∈ E3.aSet 2 (Xstar ⊔ Astar) :=
    E3.aSet_anti hk2 (Xstar ⊔ Astar) hAstar_mem
  have hempty := E3.aSet_two_eq_empty (W := ↥U)
    (fun u => Subtype.ext (hW (u : W))) hYsolv hY'O2
  rw [hempty] at hAstar_mem2
  exact hAstar_mem2

end SevenSevenA

open SevenSevenA in
theorem w4Lem7_7_of_normalizer_le_centralizer {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y K A : Subgroup (MulAut W)} {k : ℕ} [Finite ↥K]
    (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hlt : ∀ n, Nonempty (ACandidate ↥K n) → n < k)
    (hNC : A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W))) : ⁅A, K⁆ = ⊥ :=
  w4Lem7_7_of_normalizer_le_centralizer_aux hW hK hA hlt hNC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
