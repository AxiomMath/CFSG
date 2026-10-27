module

public import CFSG.Quasithin.Background.F918Z8Sz7Gc
public import CFSG.Quasithin.Background.F918Z8Sz6Fe

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Assembly

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem xk_eq_of_single {A X K : Subgroup (MulAut Y)} (hXK : X = ⨆ a ∈ A, conjAutSub a K)
    (h : ∀ a ∈ A, conjAutSub a K = K) : X = K := by
  rw [hXK]
  refine le_antisymm (iSup₂_le fun a ha => (h a ha).le) ?_
  exact le_iSup₂_of_le 1 A.one_mem (h 1 A.one_mem).ge

omit [Finite Y] in
theorem quarter_stable {W : Subgroup Y} {P Ξ : Subgroup (MulAut Y)}
    (hΞ : ∀ ξ ∈ Ξ, ∀ x ∈ P, ξ * x = x * ξ) (hΞW : Ξ ≤ stabSub W) :
    Ξ ≤ stabSub (W ⊓ fixV P) :=
  CFSG.Quasithin.chief_quarter_stable hΞ hΞW

theorem trivial_of_trivial_quarter {W : Subgroup Y} {P : Subgroup (MulAut Y)}
    (hfix : ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
      Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4)
    (hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W) {a : MulAut Y} (haΛ : ∀ l ∈ Λ, a * l = l * a)
    (haM : ∀ u ∈ W ⊓ fixV P, a u = u) : ∀ w ∈ W, a w = w :=
  CFSG.Quasithin.chief_trivial_of_quarter hfix hWΛ haΛ haM

omit [Finite Y] in
theorem X_trivial_of_A_trivial {A X : Subgroup (MulAut Y)} {I J : Subgroup Y}
    (hXA : ⁅X, A⁆ = X) (hXI : X ≤ stabSub I) (hXJ : X ≤ stabSub J) (hAc : A ≤ centSec I J) :
    X ≤ centSec I J := by
  rw [← hXA, Subgroup.commutator_le]
  intro x hx a ha
  rw [commutatorElement_def]
  have hx1 : x ∈ stabSub I := hXI hx
  have hx2 : x ∈ stabSub J := hXJ hx
  refine ⟨(stabSub I).mul_mem ((stabSub I).mul_mem ((stabSub I).mul_mem hx1 (hAc ha).1)
    ((stabSub I).inv_mem hx1)) ((stabSub I).inv_mem (hAc ha).1), fun w hw => ?_⟩
  have ha' : a⁻¹ ∈ centSec I J := (centSec I J).inv_mem (hAc ha)
  have hw1 : a⁻¹ w ∈ I := (((stabSub I).inv_mem (hAc ha).1) w).2 hw
  have hw2 : x⁻¹ (a⁻¹ w) ∈ I := (((stabSub I).inv_mem hx1) (a⁻¹ w)).2 hw1
  set w₂ : Y := x⁻¹ (a⁻¹ w) with hw₂
  have hj : a w₂ * w₂⁻¹ ∈ J := (hAc ha).2 w₂ hw2
  have hj' : x (a w₂ * w₂⁻¹) ∈ J := (hx2 _).2 hj
  have h3 : a⁻¹ w * w⁻¹ ∈ J := ha'.2 w hw
  have e1 : (x * a * x⁻¹ * a⁻¹ : MulAut Y) w = x (a w₂) := rfl
  have e2 : x w₂ = a⁻¹ w := by simp [hw₂]
  have e3 : x (a w₂ * w₂⁻¹) = x (a w₂) * (a⁻¹ w)⁻¹ := by rw [map_mul, map_inv, e2]
  have : (x * a * x⁻¹ * a⁻¹ : MulAut Y) w * w⁻¹ = x (a w₂ * w₂⁻¹) * (a⁻¹ w * w⁻¹) := by
    rw [e1, e3]; group
  rw [this]
  exact J.mul_mem hj' h3

theorem suz_sec_exists
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (hS : SuzSingle) (hI : SuzXirr) {A X K : Subgroup (MulAut Y)}
    {W : Subgroup Y} (d : SuzData Γ Λ S V A X K W) : ∃ I J : Subgroup Y, SuzSec Λ X A I J := by
  obtain ⟨n, hn⟩ := d.sz
  obtain ⟨P, t, hP, htΛ, htN, htord, hfix⟩ := suz_torus_fix_proved hB45 hA21 hF hX d.loc hn
  obtain ⟨-, a, ha, K', _, _, hn', hK', ⟨e⟩⟩ := hn
  subst hn'
  have hXK : X = K := xk_eq_of_single d.hXK (suz_single hS d)
  have hXq : CFSG.IsQuasisimple ↥X := hXK ▸ B1Red.isQuasisimple_of_open d.hKc.2.2
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec d.hA
  have hAΓ : A ≤ Γ := hA2.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  have hPΛ : P ≤ Λ := hP.1
  have hcomm : ∀ ξ ∈ X ⊔ A, ∀ x ∈ Λ, ξ * x = x * ξ := by
    have hX : X ≤ Subgroup.centralizer (Λ : Set (MulAut Y)) := fun x hx =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (d.hXc x hx y hy).symm
    have hA' : A ≤ Subgroup.centralizer (Λ : Set (MulAut Y)) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun y hy => (d.hAc a ha y hy).symm
    intro ξ hξ x hx
    exact (Subgroup.mem_centralizer_iff.1 (sup_le hX hA' hξ) x hx).symm
  have hΞW : X ⊔ A ≤ stabSub W := sup_le d.hWX d.hWA
  have hΞM : X ⊔ A ≤ stabSub (W ⊓ fixV P) :=
    quarter_stable (fun ξ hξ x hx => hcomm ξ hξ x (hPΛ hx)) hΞW
  have hAM : A ≤ stabSub (W ⊓ fixV P) := le_sup_right.trans hΞM
  have hW4 : Nat.card ↥W = Nat.card ↥(W ⊓ fixV P) ^ 4 := (hfix W d.hWΛ).1
  have hC : Nat.card ↥(W ⊓ fixV A) = Nat.card ↥((W ⊓ fixV P) ⊓ fixV A) ^ 4 := by
    have hU : ∀ l ∈ Λ, ∀ u ∈ W ⊓ fixV A, l u ∈ W ⊓ fixV A := by
      intro l hl u hu
      refine ⟨d.hWΛ l hl u hu.1, fun a ha => ?_⟩
      have := d.hAc a ha l hl
      calc a (l u) = (a * l) u := rfl
        _ = (l * a) u := by rw [this]
        _ = l (a u) := rfl
        _ = l u := by rw [hu.2 a ha]
    have := (hfix _ hU).1
    rwa [inf_right_comm] at this
  have hker : A ⊓ centSub (W ⊓ fixV P) = A ⊓ centSub W := by
    refine le_antisymm (fun a ha => ⟨ha.1, ?_⟩) (fun a ha => ⟨ha.1, fun u hu => ha.2 u hu.1⟩)
    exact trivial_of_trivial_quarter (fun U hU => (hfix U hU).1) d.hWΛ
      (fun l hl => d.hAc a ha.1 l hl) (fun u hu => ha.2 u hu)
  have h4 := rAV_quarter d.hWA hAM hW4 hC hker
  have hrat : rAV (autSub A (W ⊓ fixV P)) ≤ ((1 / 2 : ℚ)) := by
    have := d.hrAU
    linarith
  obtain ⟨I, J, hJI, hIM, hXI, hXJ, hAI, hAJ, htI, htJ, hirr, hnt, hfaith⟩ :=
    suz_chief_proved hI d hXK (by omega : 3 ≤ 2 * a + 1) (by omega : (2 * a + 1) % 2 = 1) hP htΛ
      htN htord (fun k hk => (hfix W d.hWΛ).2 k hk) (fun U hU => (hfix U hU).1) hrat
  have hnotA : ¬ A ≤ centSec I J := by
    intro hAc
    have hXc := X_trivial_of_A_trivial d.hXA hXI hXJ hAc
    obtain ⟨x, hx, w, hw, hne⟩ := hnt
    exact hne ((hXc hx).2 w hw)
  refine ⟨I, J, ?_⟩
  have hΛcard : Nat.card ↥Λ =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hK')
  have hn3 : 3 ≤ 2 * a + 1 := by omega
  have hXt : ∀ x ∈ X, t * x = x * t := fun x hx => (d.hXc x hx t htΛ).symm
  exact
    { hJI := hJI.le, hXI := hXI, hXJ := hXJ, hAI := hAI, hAJ := hAJ
      hyp := suz_b4hyp hA21 d.loc.std.hyp.qsqtk d.loc.std.hyp.exp d.hXΓ hAΓ hXq hAel d.hAX
        hJI.le hXI hXJ hAI hAJ hirr hnt
      hq := suz_off_sec hAel hJI.le hIM hAM hAI hAJ hA3 hrat hfaith hnotA
      field := fun m hnat => suz_field hΛcard hn3 htord (fun k hk => (hfix W d.hWΛ).2 k hk) hJI
        hIM htI htJ hXI hXJ hXt hnat }

end Assembly

theorem suzFFClass_of_b42
    (hB42 : AsB42) (hB45 : AsB45) (hA21 : AsA21SQTKSection)
    (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape) (hS : SuzSingle) (hI : SuzXirr) :
    SuzFFClass := by
  refine suzFFClass_of_data fun Y _ _ Γ Λ S V A X K W d => ?_
  obtain ⟨I, J, hs⟩ := suz_sec_exists hB45 hA21 hF hX hS hI d
  exact suz_close (asB42Half_of_asB42 hB42) d.loc.std.hyp.exp hs

end CFSG.Quasithin
