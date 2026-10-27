module

public import CFSG.Quasithin.Background.SmithB51SL3D
public import CFSG.Quasithin.Background.SmithB51SL3C

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section NatSecOps

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem NatSec.axis_triv {W U : Subgroup V} (c : NatSec L W U K) (hLW : L ≤ stabSub W)
    {A : Subgroup (MulAut V)} {Wst : Submodule K (Fin 3 → K)} (hWst : Module.finrank K Wst = 2)
    (hpre : c.pre A = axisSub Wst) {Y₀ : Subgroup V} (hLY₀ : L ≤ stabSub Y₀)
    (hbase : ∀ x : ↥W, Multiplicative.toAdd (c.f x) ∈ Wst → ∀ a ∈ A, a x * (x : V)⁻¹ ∈ Y₀)
    {W' : Submodule K (Fin 3 → K)} (hW' : Module.finrank K W' = 2) {g : ↥(StatedSL 3 K)}
    (hg : g ∈ axisSub W') (x : ↥W) (hx : Multiplicative.toAdd (c.f x) ∈ W') :
    ((c.π g : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ Y₀ := by
  obtain ⟨h, hh⟩ := exists_slMap_eq hWst hW'
  rw [← hh, ← map_conj_axisSub] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have hg₀A : ((c.π g₀ : ↥L) : MulAut V) ∈ A := by
    have : g₀ ∈ c.pre A := hpre ▸ hg₀
    exact this
  have hx₀ : ((c.π h⁻¹ : ↥L) : MulAut V) (x : V) ∈ W := ((hLW (c.π h⁻¹).2) x).2 x.2
  set x₀ : ↥W := ⟨_, hx₀⟩ with hx₀def
  have hfx₀ : Multiplicative.toAdd (c.f x₀) ∈ Wst := by
    rw [hx₀def, c.hfe h⁻¹ x hx₀]
    show slAct h⁻¹ (Multiplicative.toAdd (c.f x)) ∈ Wst
    rw [← mem_slMap, hh]
    exact hx
  have h1 := hbase x₀ hfx₀ _ hg₀A
  have hconj : ((c.π ((MulAut.conj h).toMonoidHom g₀) : ↥L) : MulAut V) =
      ((c.π h : ↥L) : MulAut V) * ((c.π g₀ : ↥L) : MulAut V) * ((c.π h⁻¹ : ↥L) : MulAut V) := by
    simp [map_mul, map_inv]
  have hxx : (x : V) = ((c.π h : ↥L) : MulAut V) (x₀ : V) := by
    rw [hx₀def]
    show (x : V) = ((c.π h : ↥L) : MulAut V) (((c.π h⁻¹ : ↥L) : MulAut V) (x : V))
    rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have h2 := (hLY₀ (c.π h).2 _).2 h1
  rw [map_mul, map_inv, ← hxx] at h2
  rw [hconj, MulAut.mul_apply, MulAut.mul_apply]
  convert h2 using 2

@[expose] def NatSec.restrict {W U X : Subgroup V} (c : NatSec L W U K) (hXW : X ≤ W)
    (hsup : X ⊔ U = W) : NatSec L X (X ⊓ U) K where
  π := c.π
  hπ := c.hπ
  f := c.f.comp (Subgroup.inclusion hXW)
  hfs y := by
    obtain ⟨w, hw⟩ := c.hfs y
    have hwXU : (w : V) ∈ X ⊔ U := hsup ▸ w.2
    obtain ⟨x, hx, u, hu, hxu⟩ := Subgroup.mem_sup.1 hwXU
    refine ⟨⟨x, hx⟩, ?_⟩
    have huW : u ∈ W := hsup ▸ Subgroup.mem_sup_right hu
    have hsplit : w = Subgroup.inclusion hXW ⟨x, hx⟩ * ⟨u, huW⟩ := Subtype.ext hxu.symm
    have hfu : c.f ⟨u, huW⟩ = 1 := (c.hfk _).2 hu
    rw [MonoidHom.comp_apply, ← hw, hsplit, map_mul, hfu, mul_one]
  hfk x := by
    rw [MonoidHom.comp_apply, c.hfk]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  hfe γ x hx := by
    have hw : ((c.π γ : ↥L) : MulAut V) (Subgroup.inclusion hXW x : V) ∈ W := hXW hx
    show c.f ⟨_, hw⟩ = _
    exact c.hfe γ (Subgroup.inclusion hXW x) hw

@[expose] def NatSec.ofEq {W U U' : Subgroup V} (c : NatSec L W U K) (h : U = U') :
    NatSec L W U' K :=
  h ▸ c

theorem NatSec.ofEq_pre {W U U' : Subgroup V} (c : NatSec L W U K) (h : U = U')
    (B : Subgroup (MulAut V)) : (c.ofEq h).pre B = c.pre B := by
  subst h; rfl

theorem NatSec.ofEq_f {W U U' : Subgroup V} (c : NatSec L W U K) (h : U = U') (w : ↥W) :
    (c.ofEq h).f w = c.f w := by
  subst h; rfl

theorem NatSec.ofEq_π {W U U' : Subgroup V} (c : NatSec L W U K) (h : U = U')
    (γ : ↥(StatedSL 3 K)) : (c.ofEq h).π γ = c.π γ := by
  subst h; rfl

theorem NatSec.restrict_pre {W U X : Subgroup V} (c : NatSec L W U K) (hXW : X ≤ W)
    (hsup : X ⊔ U = W) (B : Subgroup (MulAut V)) :
    (c.restrict hXW hsup).pre B = c.pre B := rfl

end NatSecOps

section Mod

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem le_stabSub_sup {X : Subgroup (MulAut V)} {P Q : Subgroup V} (hP : X ≤ stabSub P)
    (hQ : X ≤ stabSub Q) : X ≤ stabSub (P ⊔ Q) := by
  intro g hg
  have key : ∀ g : MulAut V, g ∈ stabSub P → g ∈ stabSub Q → ∀ w ∈ P ⊔ Q, g w ∈ P ⊔ Q := by
    intro g hgP hgQ w hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hgP p).2 hp))
      (Subgroup.mem_sup_right ((hgQ q).2 hq))
  exact mem_stabSub_of_inv (key g (hP hg) (hQ hg))
    (key g⁻¹ ((stabSub P).inv_mem (hP hg)) ((stabSub Q).inv_mem (hQ hg)))

structure SL3Mod (G L : Subgroup (MulAut V)) : Type 1 where
  A : Subgroup (MulAut V)
  I : Subgroup V
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  n : ℕ
  hK : Nat.card K = 2 ^ n
  hmin : IsFFStarMin G A
  hAL : A ≤ L
  hquad : IsQuadratic A
  hIU : I ≤ commV L
  hLI : L ≤ stabSub I
  e₁ : NatSec L I ⊥ K
  e₂ : NatSec L (commV L) I K
  hax₁ : Module.finrank K (fixK (e₁.pre A)) = 2 ∧ e₁.pre A = axisSub (fixK (e₁.pre A))
  hax₂ : Module.finrank K (fixK (e₂.pre A)) = 2 ∧ e₂.pre A = axisSub (fixK (e₂.pre A))
  hcardA : Nat.card A = Nat.card K ^ 2
  hlift : ∀ u ∈ commV L, (∀ a ∈ A, a u * u⁻¹ ∈ I) →
    ∃ u' ∈ commV L, u' ∈ fixV A ∧ u' * u⁻¹ ∈ I

attribute [instance] SL3Mod.instField SL3Mod.instFinite

theorem exists_sl3Mod (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) : Nonempty (SL3Mod G L) := by
  classical
  obtain ⟨c⟩ := exists_sl3Coords hA21 hB42 hA36 hIH hV h hU hK eL
  set d := c.d with hd
  have hAel : IsElemAbelian2 d.A := d.hmin.1.2.2.1
  have hAne : d.A ≠ ⊥ := d.hmin.1.2.1
  have hA2 : IsPGroup 2 d.A := hAel.isPGroup
  have hAI : d.A ≤ stabSub d.I := d.hAL.trans d.hLI
  have hAY₂ : d.A ≤ stabSub d.Y₂ := d.hAL.trans d.hLY₂
  have hAW₂ : d.A ≤ stabSub d.W₂ := d.hAL.trans d.hLW₂
  have hsum : rk d.A ≤ rkIdx (fixV (autSec d.A d.I (d.I ⊓ fixV L))) +
      rkIdx (fixV (autSec d.A d.W₂ d.Y₂)) := by
    have := d.hr₁; have := d.hr₂; omega
  obtain ⟨-, hY₂A, hVA, -, hl₁, hl₂, hl₃, -⟩ :=
    chain_extremal hV d.hmin.1 inf_le_left d.hIY₂ d.hY₂W₂ hAI hAY₂ hAW₂ hsum
  have hY₂L := L_comm_mem_of_A h d.hAL hA2 hAne d.hLY₂ d.hLI hY₂A
  have hLtop : L ≤ stabSub (⊤ : Subgroup V) := fun g _ u => by simp
  have hVL := L_comm_mem_of_A h d.hAL hA2 hAne hLtop d.hLW₂ (fun a ha w _ => hVA a ha w)
  have hLU : L ≤ stabSub (commV L) :=
    le_stabSub_commV (fun g hg l hl => L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg))
      (fun g hg => L.inv_mem hg)
  have hUW₂ : commV L ≤ d.W₂ := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, v, rfl⟩
    exact hVL l hl v trivial
  obtain ⟨hIL, hIcomm, -, -⟩ := irr_data d.hI
  have hIU : d.I ≤ commV L := by
    rw [commV_eq_commSub, ← hIcomm]
    exact commSub_mono le_top le_rfl
  have hUcomm : commSub (commV L) L = commV L :=
    commSub_commV_eq (commutator_L_perfect (quasi_L h))
  have hW₂eq : commV L ⊔ d.Y₂ = d.W₂ := by
    rcases d.hch (commV L ⊔ d.Y₂) (le_stabSub_sup hLU d.hLY₂) le_sup_right
      (sup_le hUW₂ d.hY₂W₂) with h1 | h1
    · exfalso
      apply d.hnc
      calc commSub d.W₂ L ≤ commSub ⊤ L := commSub_mono le_top le_rfl
        _ = commV L := (commV_eq_commSub L).symm
        _ ≤ commV L ⊔ d.Y₂ := le_sup_left
        _ = d.Y₂ := h1
    · exact h1
  have base₁ : ∀ x : ↥d.I, Multiplicative.toAdd (c.c₁.f x) ∈ fixK (c.c₁.pre d.A) →
      ∀ a ∈ d.A, a x * (x : V)⁻¹ ∈ (⊥ : Subgroup V) := by
    intro x hx a ha
    have hfix := (mem_fixSec_iff_nat c.c₁.hπ.2 c.c₁.f c.c₁.hfk c.c₁.hfe d.hLI d.hAL x).2 hx
    obtain ⟨x', hx'A, hx'⟩ := exists_lift_sec inf_le_left hAI hl₁ _ (mk_mem_fixV_autSec hfix)
    have hy : (x' : V)⁻¹ * x ∈ d.I ⊓ fixV L := by
      have := QuotientGroup.eq.1 hx'
      simpa using Subgroup.mem_subgroupOf.1 this
    have hxx : (x : V) = x' * ((x' : V)⁻¹ * x) := by group
    rw [hxx, map_mul, hx'A a ha, hy.2 a (d.hAL ha), Subgroup.mem_bot]
    group
  have base₂ : ∀ x : ↥d.W₂, Multiplicative.toAdd (c.c₂.f x) ∈ fixK (c.c₂.pre d.A) →
      ∀ a ∈ d.A, a x * (x : V)⁻¹ ∈ d.I := by
    intro x hx a ha
    have hfix := (mem_fixSec_iff_nat c.c₂.hπ.2 c.c₂.f c.c₂.hfk c.c₂.hfe d.hLW₂ d.hAL x).2 hx
    obtain ⟨w, hwA, hw⟩ := exists_lift_sec d.hY₂W₂ hAW₂ hl₃ _ (mk_mem_fixV_autSec hfix)
    have hy : (w : V)⁻¹ * x ∈ d.Y₂ := by
      have := QuotientGroup.eq.1 hw
      simpa using Subgroup.mem_subgroupOf.1 this
    have hxx : (x : V) = w * ((w : V)⁻¹ * x) := by group
    have h1 := hY₂A a ha _ hy
    have e : a (x : V) * (x : V)⁻¹ = a ((w : V)⁻¹ * x) * ((w : V)⁻¹ * x)⁻¹ := by
      conv_lhs => rw [hxx]
      rw [map_mul, hwA a ha, mul_inv_rev]
      calc (w : V) * a ((w : V)⁻¹ * x) * (((w : V)⁻¹ * x)⁻¹ * (w : V)⁻¹)
          = ((w : V) * (w : V)⁻¹) * (a ((w : V)⁻¹ * x) * ((w : V)⁻¹ * x)⁻¹) := by ac_rfl
        _ = a ((w : V)⁻¹ * x) * ((w : V)⁻¹ * x)⁻¹ := by rw [mul_inv_cancel, one_mul]
    rw [e]
    exact h1
  have hLbot : L ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by simp
  have ax₁ := fun {W'} hW' {g} hg x hx =>
    c.c₁.axis_triv d.hLI c.hax₁.1 c.hax₁.2 hLbot base₁ (W' := W') hW' (g := g) hg x hx
  have ax₂ := fun {W'} hW' {g} hg x hx =>
    c.c₂.axis_triv d.hLW₂ c.hax₂.1 c.hax₂.2 d.hLI base₂ (W' := W') hW' (g := g) hg x hx
  have hn1 : 1 ≤ c.n := by
    rcases Nat.eq_zero_or_pos c.n with h0 | h0
    · have : (1 : ℕ) < Nat.card c.K := Finite.one_lt_card
      rw [c.hK, h0] at this
      norm_num at this
    · exact h0
  have hYbot : d.I ⊓ fixV L = ⊥ := by
    have hcommI : d.I ≤ commSub d.I L ⊔ ⊥ := by rw [hIcomm, sup_bot_eq]
    rcases Nat.lt_or_ge 1 c.n with hn | hn
    · exact eq_of_sl3_cover hV bot_le inf_le_left d.hLI hLbot
        (fun l hl z hz => by rw [hz.2 l hl, mul_inv_cancel]; exact Subgroup.one_mem _)
        hcommI hn c.hK c.c₁
    · have hK2 : Nat.card c.K = 2 := by rw [c.hK, show c.n = 1 by omega, pow_one]
      exact eq_of_axis_two hV bot_le inf_le_left d.hLI hcommI hK2 c.c₁
        (fun i g hg x hx => ax₁ (finrank_coordHyp (i + 1))
          (mem_axisSub_coordHyp (by fin_cases i <;> decide) hg) x hx)
  set e₂' := c.c₂.restrict hUW₂ hW₂eq with he₂'
  have hUY₂ : commV L ⊓ d.Y₂ = d.I := by
    have hcommU : commV L ≤ commSub (commV L) L ⊔ d.I := by rw [hUcomm]; exact le_sup_left
    rcases Nat.lt_or_ge 1 c.n with hn | hn
    · exact eq_of_sl3_cover hV (le_inf hIU d.hIY₂) inf_le_left hLU d.hLI
        (fun l hl z hz => hY₂L l hl z hz.2) hcommU hn c.hK e₂'
    · have hK2 : Nat.card c.K = 2 := by rw [c.hK, show c.n = 1 by omega, pow_one]
      exact eq_of_axis_two hV (le_inf hIU d.hIY₂) inf_le_left hLU hcommU hK2 e₂'
        (fun i g hg x hx => ax₂ (finrank_coordHyp (i + 1))
          (mem_axisSub_coordHyp (by fin_cases i <;> decide) hg)
          (Subgroup.inclusion hUW₂ x) hx)
  have hlift : ∀ u ∈ commV L, (∀ a ∈ d.A, a u * u⁻¹ ∈ d.I) →
      ∃ u' ∈ commV L, u' ∈ fixV d.A ∧ u' * u⁻¹ ∈ d.I := by
    intro u hu hA
    have huW : u ∈ d.W₂ := hUW₂ hu
    have hfix : ((⟨u, huW⟩ : ↥d.W₂) : V) ∈ fixSec d.A d.W₂ d.Y₂ :=
      ⟨huW, fun a ha => d.hIY₂ (hA a ha)⟩
    obtain ⟨w, hwA, hw⟩ := exists_lift_sec d.hY₂W₂ hAW₂ hl₃ _ (mk_mem_fixV_autSec hfix)
    have hy : (w : V)⁻¹ * u ∈ d.Y₂ := by
      have := QuotientGroup.eq.1 hw
      simpa using Subgroup.mem_subgroupOf.1 this
    have hfixy : ((⟨_, hy⟩ : ↥d.Y₂) : V) ∈ fixSec d.A d.Y₂ d.I :=
      ⟨hy, fun a ha => hY₂A a ha _ hy⟩
    obtain ⟨y', hy'A, hy'⟩ := exists_lift_sec d.hIY₂ hAY₂ hl₂ _ (mk_mem_fixV_autSec hfixy)
    have hi : (y' : V)⁻¹ * ((w : V)⁻¹ * u) ∈ d.I := by
      have := QuotientGroup.eq.1 hy'
      simpa using Subgroup.mem_subgroupOf.1 this
    refine ⟨w * y', ?_, ?_, ?_⟩
    · have : (w : V) * y' = u * ((y' : V)⁻¹ * ((w : V)⁻¹ * u))⁻¹ := by group
      rw [this]
      exact (commV L).mul_mem hu ((commV L).inv_mem (hIU hi))
    · intro a ha
      rw [map_mul, hwA a ha, hy'A a ha]
    · have : (w : V) * y' * u⁻¹ = ((y' : V)⁻¹ * ((w : V)⁻¹ * u))⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
        ac_rfl
      rw [this]
      exact d.I.inv_mem hi
  exact ⟨⟨d.A, d.I, c.K, c.n, c.hK, d.hmin, d.hAL, d.hquad, hIU, d.hLI, c.c₁.ofEq hYbot,
    e₂'.ofEq hUY₂, by rw [NatSec.ofEq_pre]; exact c.hax₁,
    by rw [NatSec.ofEq_pre, he₂', NatSec.restrict_pre]; exact c.hax₂, c.hcardA, hlift⟩⟩

end Mod

end B5

end CFSG.Quasithin
