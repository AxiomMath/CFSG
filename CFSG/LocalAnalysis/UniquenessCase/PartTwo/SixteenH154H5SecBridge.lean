module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Quot
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_hom_eq_one_of_perfect {G M : Type*} [Group G] [Group M]
    [IsMulCommutative M] (hG : commutator G = ⊤) (f : G →* M) : f = 1 := by
  have hle : commutator G ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' (f a) (f b)
  rw [hG] at hle
  ext g
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

private theorem s16h_H5_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
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

private theorem s16h_le_stabSub_commSub_fixV {L : Subgroup (MulAut W)} :
    normalizer (L : Set (MulAut W)) ≤ stabSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hx
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxnorm u hu.1, ?_⟩
    intro l hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.mp hu.2 (x⁻¹ * l * x) (by simpa using hxinvnorm l hl)]
  have hxinvZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x⁻¹ u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxinvnorm u hu.1, ?_⟩
    intro l hl
    calc l (x⁻¹ u) = x⁻¹ ((x * l * x⁻¹) u) := by simp [MulAut.mul_apply]
      _ = x⁻¹ u := by rw [mem_fixV.mp hu.2 (x * l * x⁻¹) (hxnorm l hl)]
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by have := hxinvZ (x u) hu; simpa using this, hxZ u⟩

private theorem s16h_commSub_commSub_eq (L : Subgroup (MulAut W))
    (hperf : commutator ↥L = ⊤) :
    commSub (commSub ⊤ L) L = commSub ⊤ L := by
  set U : Subgroup W := commSub ⊤ L with hU
  set K4 : Subgroup W := commSub U L with hK4
  have hLstab : ∀ l ∈ L, ∀ w ∈ U, l w ∈ U := by
    intro l hl w hw
    rw [hU] at hw ⊢
    exact commSub_top_stable151b
      (fun l' hl' => L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) w hw
  have hle : K4 ≤ U := by
    rw [hK4]
    exact commSub_le_of_invariant (fun l hl w hw => hLstab l hl w hw)
  have key : ∀ w : W, ∀ l ∈ L, l w * w⁻¹ ∈ K4 := by
    intro w l hl
    let g : ↥L →* W ⧸ K4 :=
      { toFun := fun a => QuotientGroup.mk' K4 ((a : MulAut W) w * w⁻¹)
        map_one' := by simp
        map_mul' := fun a b => by
          have hgen : (a : MulAut W) ((b : MulAut W) w * w⁻¹) *
              ((b : MulAut W) w * w⁻¹)⁻¹ ∈ K4 :=
            Subgroup.subset_closure ⟨(a : MulAut W), a.2,
              (b : MulAut W) w * w⁻¹,
              Subgroup.subset_closure ⟨(b : MulAut W), b.2, w, Subgroup.mem_top w, rfl⟩, rfl⟩
          have hstep : QuotientGroup.mk' K4 ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) =
              QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹) := by
            have h1 : QuotientGroup.mk' K4 ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) *
                (QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹))⁻¹ = 1 := by
              rw [← map_inv, ← map_mul]
              exact (QuotientGroup.eq_one_iff _).mpr hgen
            exact mul_inv_eq_one.mp h1
          have hid : ((a : MulAut W) * (b : MulAut W)) w * w⁻¹ =
              ((a : MulAut W) w * w⁻¹) *
                ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) := by
            have ha : (a : MulAut W) ((b : MulAut W) w * w⁻¹) =
                (a : MulAut W) ((b : MulAut W) w) * ((a : MulAut W) w)⁻¹ := by
              rw [map_mul, map_inv]
            rw [ha]
            simp only [MulAut.mul_apply]
            calc (a : MulAut W) ((b : MulAut W) w) * w⁻¹ =
                (((a : MulAut W) w) * ((a : MulAut W) w)⁻¹) *
                  ((a : MulAut W) ((b : MulAut W) w) * w⁻¹) := by
                  rw [mul_inv_cancel, one_mul]
              _ = ((a : MulAut W) w * w⁻¹) *
                  ((a : MulAut W) ((b : MulAut W) w) * ((a : MulAut W) w)⁻¹) := by ac_rfl
          change QuotientGroup.mk' K4 (((a : MulAut W) * (b : MulAut W)) w * w⁻¹) =
              QuotientGroup.mk' K4 ((a : MulAut W) w * w⁻¹) *
                QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹)
          rw [hid, map_mul, hstep] }
    have hg : g = 1 := s16h_hom_eq_one_of_perfect hperf g
    have happ : g ⟨l, hl⟩ = 1 := by rw [hg]; rfl
    exact (QuotientGroup.eq_one_iff _).mp happ
  have hge : U ≤ K4 := by
    rw [hU, commSub, Subgroup.closure_le]
    rintro c ⟨l, hl, w, -, rfl⟩
    exact key w l hl
  exact le_antisymm hle hge

theorem s16h_realizes_autSec_of_realizes [Finite W] {U Z : Subgroup W} {L : Subgroup (MulAut W)}
    (hZU : Z ≤ U) (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hfaith : L ⊓ centSec U Z = ⊥) {D : FFModel} (h : D.Realizes L U Z) :
    D.Realizes (autSec L U Z) (⊤ : Subgroup (Sec U Z)) ⊥ := by
  obtain ⟨π, hsurj, -, hkersec, -, -, hsecinv, hkerinv, β, hβsurj, hβker, hβeq⟩ := h
  let e : ↥L ≃* ↥(autSec L U Z) := CFSG.Quasithin.B5.secEquiv L hLU hLZ hfaith
  refine ⟨e.toMonoidHom.comp π, e.surjective.comp hsurj, bot_le, hkersec, ?_, ?_,
    hsecinv, hkerinv, ?_⟩
  · exact fun _ _ _ => Subgroup.mem_top _
  · intro hh z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hle : Z.subgroupOf U ≤ β.ker := by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact (hβker u).mpr (Subgroup.mem_subgroupOf.mp hu)
    let β₀ : Sec U Z →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
      QuotientGroup.lift (Z.subgroupOf U) β hle
    let β' : ↥(⊤ : Subgroup (Sec U Z)) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
      β₀.comp (Subgroup.topEquiv (G := Sec U Z)).toMonoidHom
    refine ⟨β', ?_, ?_, ?_⟩
    · intro y
      obtain ⟨u, hu⟩ := hβsurj y
      refine ⟨⟨QuotientGroup.mk u, Subgroup.mem_top _⟩, ?_⟩
      change β₀ (QuotientGroup.mk u) = y
      rw [QuotientGroup.lift_mk' (Z.subgroupOf U) hle u]
      exact hu
    · intro u
      have hβ₀inj : ∀ x : Sec U Z, β₀ x = 1 → x = 1 := by
        intro x hx
        induction x using QuotientGroup.induction_on with
        | H v =>
          rw [QuotientGroup.lift_mk' (Z.subgroupOf U) hle v] at hx
          have hvZ : (v : W) ∈ Z := (hβker v).mp hx
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hvZ
      constructor
      · intro h1
        rw [Subgroup.mem_bot]
        change β₀ (u : Sec U Z) = 1 at h1
        exact hβ₀inj _ h1
      · intro h1
        rw [Subgroup.mem_bot] at h1
        rw [show u = 1 from Subtype.ext h1, map_one]
    · intro γ u m hu hm hum
      obtain ⟨u0, hu0⟩ := QuotientGroup.mk_surjective (u : Sec U Z)
      have hum' : β u0 = QuotientGroup.mk m := by
        change β₀ (u : Sec U Z) = QuotientGroup.mk m at hum
        rw [← hu0] at hum
        rwa [QuotientGroup.lift_mk' (Z.subgroupOf U) hle u0] at hum
      have huU : ((π γ : ↥L) : MulAut W) (u0 : W) ∈ U :=
        (hLU (π γ).2 (u0 : W)).2 u0.2
      have key := hβeq γ u0 m huU hm hum'
      have hπγ : (((e.toMonoidHom.comp π) γ : ↥(autSec L U Z)) : MulAut (Sec U Z))
          = CFSG.Quasithin.B5.secHom L hLU hLZ (π γ) :=
        CFSG.Quasithin.B5.secEquiv_apply L hLU hLZ hfaith (π γ)
      have hact : (((e.toMonoidHom.comp π) γ : ↥(autSec L U Z)) : MulAut (Sec U Z))
            (u : Sec U Z)
          = QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u0 : W), huU⟩ := by
        rw [← hu0, hπγ]
        exact CFSG.Quasithin.B5.secHom_mk L hLU hLZ (π γ) u0
      rw [show β' ⟨(((e.toMonoidHom.comp π) γ : ↥(autSec L U Z)) : MulAut (Sec U Z))
            (u : Sec U Z), hu⟩
          = β₀ ((((e.toMonoidHom.comp π) γ : ↥(autSec L U Z)) : MulAut (Sec U Z))
            (u : Sec U Z)) from rfl]
      rw [hact]
      rw [QuotientGroup.lift_mk' (Z.subgroupOf U) hle
        ⟨((π γ : ↥L) : MulAut W) (u0 : W), huU⟩]
      exact key

theorem s16h_H5_card_autSub_eq_autSec [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) :
    Nat.card ↥(autSub E (commSub ⊤ L)) =
      Nat.card ↥(autSec E (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) := by
  haveI : Finite (MulAut W) := s16h_finite_mulAut
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hEN : E ≤ normalizer (L : Set (MulAut W)) :=
    fun e he => (Subgroup.mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_H5_commSub_stab (L := L) (hEN he)
  have hEZ : E ≤ stabSub Z := by
    rw [hZ]
    exact fun e he => s16h_le_stabSub_commSub_fixV (L := L) (hEN he)
  have hcent : E ⊓ centSec U Z = E ⊓ centSub U := by
    refine le_antisymm ?_ ?_
    · intro e he
      rw [Subgroup.mem_inf] at he ⊢
      refine ⟨he.1, ?_⟩
      rw [mem_centSub]
      intro w hw
      exact s16h_H5_triv_of_triv_quot hc.comp (hEN he.1) (mem_centSec.mp he.2).2 w hw
    · intro e he
      rw [Subgroup.mem_inf] at he ⊢
      exact ⟨he.1, centSub_le_centSec U Z he.2⟩
  have h1 := card_autSub_mul (A := E) (U := U) hEU
  have h2 := card_autSec_mul (A := E) (W := U) (U := Z) hEU hEZ
  rw [hcent] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem s16h_H5_faithful_on_quotient [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hcenter : Subgroup.center ↥L = ⊥) :
    L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ := by
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hLq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  have hLperf : commutator ↥L = ⊤ := hLq.1
  have hLU : L ≤ stabSub U := by
    rw [hU]
    intro l hl
    exact s16h_H5_commSub_stab (L := L) (Subgroup.le_normalizer hl)
  let φ : ↥L →* MulAut U := (resHom U).comp (Subgroup.inclusion hLU)
  have hKmem : ∀ l : ↥L, l ∈ φ.ker ↔ ∀ u : U, (l : MulAut W) (u : W) = u := by
    intro l
    rw [MonoidHom.mem_ker]
    constructor
    · intro h u
      have h' : resHom U (Subgroup.inclusion hLU l) = 1 := h
      have hh := congrArg (fun g : MulAut U => ((g u : U) : W)) h'
      rw [resHom_apply] at hh
      simpa [Subgroup.coe_inclusion] using hh
    · intro h
      ext u
      change (((resHom U (Subgroup.inclusion hLU l)) u : U) : W) = (u : W)
      rw [resHom_apply]
      simpa [Subgroup.coe_inclusion] using h u
  have hKne : φ.ker ≠ ⊤ := by
    intro hKtop
    have hfixU : ∀ l : ↥L, ∀ u : U, (l : MulAut W) (u : W) = u := fun l u =>
      (hKmem l).mp (by rw [hKtop]; exact Subgroup.mem_top l) u
    have hcomm_bot : commSub U L = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro u hu
      rw [mem_fixV]
      intro l hl
      exact hfixU ⟨l, hl⟩ ⟨u, hu⟩
    have h4 : commSub U L = U := s16h_commSub_commSub_eq L hLperf
    have hUbot : U = ⊥ := by rw [← h4, hcomm_bot]
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext (fun w =>
        mem_fixV.mp ((commSub_eq_bot_iff.mp (by rw [← hU]; exact hUbot))
          (Subgroup.mem_top w)) l hl)
    haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hLq.2.toNontrivial
    haveI hnt : Nontrivial ↥L :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt hLbot
  have hKcenter : φ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq φ.ker hKne
  have hKbot : φ.ker = ⊥ := le_bot_iff.mp (hcenter ▸ hKcenter)
  rw [eq_bot_iff]
  intro l hl
  rw [Subgroup.mem_inf] at hl
  rw [Subgroup.mem_bot]
  have htriv : ∀ w ∈ U, l w = w :=
    s16h_H5_triv_of_triv_quot hc.comp (Subgroup.le_normalizer hl.1) (mem_centSec.mp hl.2).2
  have hKl : (⟨l, hl.1⟩ : ↥L) ∈ φ.ker := (hKmem ⟨l, hl.1⟩).mpr (fun u => htriv u.1 u.2)
  rw [hKbot, Subgroup.mem_bot] at hKl
  simpa using congrArg Subtype.val hKl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
