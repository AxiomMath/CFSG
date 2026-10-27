module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Quot
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.A1cModuleUnits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut {X : Type*} [Mul X] [Finite X] : Finite (MulAut X) := by
  classical
  exact Finite.of_injective (fun f : MulAut X => (f : X → X))
    (fun f g h => MulEquiv.ext (congrFun h))

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

private theorem s16h_le_stabSub_of_stableUnder {K : Subgroup (MulAut W)} {V : Subgroup W}
    (h : StableUnder K V) : K ≤ stabSub V := by
  intro k hk
  rw [mem_stabSub]
  intro v
  exact ⟨fun hv => by
      have h1 := h (k⁻¹) (K.inv_mem hk) (k v) hv
      simpa using h1,
    fun hv => h k hk v hv⟩

private theorem s16h_centralizer_le_stabSub_fixV {X : Subgroup (MulAut W)}
    (U : Subgroup W) (hXU : X ≤ stabSub U) :
    Subgroup.centralizer (autSub X U : Set (MulAut ↥U)) ≤ stabSub (fixV (autSub X U)) := by
  intro φ hφ
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have hφinv : φ⁻¹ ∈ Subgroup.centralizer (autSub X U : Set (MulAut ↥U)) :=
      (Subgroup.centralizer (autSub X U : Set (MulAut ↥U))).inv_mem hφ
    rw [mem_fixV] at hu ⊢
    intro ψ hψ
    have hcomm : ψ * φ⁻¹ = φ⁻¹ * ψ := Subgroup.mem_centralizer_iff.mp hφinv ψ hψ
    calc ψ u = ψ (φ⁻¹ (φ u)) := by simp
      _ = (ψ * φ⁻¹) (φ u) := rfl
      _ = (φ⁻¹ * ψ) (φ u) := by rw [hcomm]
      _ = φ⁻¹ (ψ (φ u)) := rfl
      _ = φ⁻¹ (φ u) := by rw [hu ψ hψ]
      _ = u := by simp
  · intro hu
    rw [mem_fixV] at hu ⊢
    intro ψ hψ
    have hcomm : ψ * φ = φ * ψ := Subgroup.mem_centralizer_iff.mp hφ ψ hψ
    calc ψ (φ u) = (ψ * φ) u := rfl
      _ = (φ * ψ) u := by rw [hcomm]
      _ = φ (ψ u) := rfl
      _ = φ u := by rw [hu ψ hψ]

theorem s16h_H5_bridge_cent_cyclic_odd [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (hirr : commSub ⊤ L ∈ irrSet L)
    {E : Subgroup (MulAut W)} (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) :
    IsCyclic ↥(autSub E (commSub ⊤ L) ⊓
        Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L)))) ∧
      Odd (Nat.card ↥(autSub E (commSub ⊤ L) ⊓
        Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))))) := by
  classical
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  rw [irrSet, Set.mem_setOf_eq] at hirr
  obtain ⟨hcomm, hIrr⟩ := hirr
  rw [IsIrrOn] at hIrr
  obtain ⟨hZU, hstU, hstZ, hirrCond⟩ := hIrr
  have hLU : L ≤ stabSub U := s16h_le_stabSub_of_stableUnder hstU
  have hLZ : L ≤ stabSub Z := s16h_le_stabSub_of_stableUnder hstZ
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (Subgroup.mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := fun e he => s16h_H5_commSub_stab (L := L) (hEN he)
  have hEZ : E ≤ stabSub Z := fun e he => s16h_le_stabSub_commSub_fixV (L := L) (hEN he)
  set CL : Subgroup (MulAut ↥U) :=
    Subgroup.centralizer (autSub L U : Set (MulAut ↥U)) with hCL
  set C : Subgroup (MulAut ↥U) := autSub E U ⊓ CL with hC
  have hZsub : Z.subgroupOf U = fixV (autSub L U) := by
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZU.le, map_subtype_fixV_autSub hLU, ← hZ]
  have hCLstab : CL ≤ stabSub (Z.subgroupOf U) := by
    rw [hZsub]
    exact s16h_centralizer_le_stabSub_fixV (W := W) U hLU
  have hCstab : C ≤ stabSub (Z.subgroupOf U) :=
    fun c hc => hCLstab (Subgroup.mem_inf.mp hc).2
  set Λ : Subgroup (MulAut (Sec U Z)) := autSec L U Z with hΛ
  have hsimple : XMod.IsIrrSec ↥Λ (⊥ : Subgroup (Sec U Z)) ⊤ := by
    rw [hΛ]
    exact B5.isIrrSec_autSec hZU hirrCond hLU hLZ
  have hQ : ∀ q : Sec U Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : (w ^ 2 : ↥U) = 1 := Subtype.ext (by simpa using hc.elem (w : W))
      rw [h2]
      rfl
  have hfield := XMod.eqvEnd_isField_charTwo (A := ↥Λ) (P := Sec U Z) hQ hsimple
  obtain ⟨hfinE, hisfield, hcharE⟩ := hfield
  let α : Type := XMod.eqvEnd ↥Λ (Sec U Z)
  let Γ : Type := ↥(XMod.eqvAut ↥Λ (Sec U Z))
  letI : Field α := hisfield.toField
  haveI : CharP α 2 := hcharE
  haveI : Fintype α := Fintype.ofFinite _
  haveI : Finite (MulAut (Sec U Z)) := s16h_finite_mulAut
  have hcycΓ : IsCyclic Γ :=
    XMod.isCyclic_of_injective_eqvEnd hsimple (XMod.toEqvEnd ↥Λ (Sec U Z))
      (XMod.toEqvEnd_injective (A := ↥Λ) (P := Sec U Z))
  have hunits_odd : Odd (Nat.card αˣ) := by
    obtain ⟨n, -, hcard⟩ := FiniteField.card α 2
    have hcardα : Nat.card α = 2 ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card, hcard]
    rw [Nat.card_units, hcardα]
    refine ⟨2 ^ ((n : ℕ) - 1) - 1, ?_⟩
    have hn : 0 < (n : ℕ) := n.2
    have hpow : 2 ^ (n : ℕ) = 2 * 2 ^ ((n : ℕ) - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hm : 0 < 2 ^ ((n : ℕ) - 1) := pow_pos (by norm_num) _
    omega
  let toUnits : Γ →* αˣ :=
    { toFun := fun φ =>
        ⟨XMod.toEqvEnd ↥Λ (Sec U Z) φ, XMod.toEqvEnd ↥Λ (Sec U Z) φ⁻¹,
          by rw [← map_mul, mul_inv_cancel, map_one],
          by rw [← map_mul, inv_mul_cancel, map_one]⟩
      map_one' := Units.ext (map_one (XMod.toEqvEnd ↥Λ (Sec U Z)))
      map_mul' := fun φ ψ => Units.ext (map_mul (XMod.toEqvEnd ↥Λ (Sec U Z)) φ ψ) }
  have toUnits_inj : Function.Injective toUnits := by
    intro φ ψ h
    exact XMod.toEqvEnd_injective (A := ↥Λ) (P := Sec U Z) (Units.ext_iff.mp h)
  have hdvd : Nat.card Γ ∣ Nat.card αˣ := by
    have heq : Nat.card Γ = Nat.card ↥(toUnits.range) :=
      Nat.card_congr (MonoidHom.ofInjective toUnits_inj).toEquiv
    rw [heq]
    exact Subgroup.card_subgroup_dvd_card toUnits.range
  have hoddΓ : Odd (Nat.card Γ) :=
    hunits_odd.of_dvd_nat hdvd
  have hmem : ∀ c : ↥C,
      (quotHom (Z.subgroupOf U)).comp (Subgroup.inclusion hCstab) c ∈
        XMod.eqvAut ↥Λ (Sec U Z) := by
    intro c
    rw [XMod.mem_eqvAut_iff]
    intro a p
    obtain ⟨h, hhL, hU, hEq⟩ :=
      (CFSG.Quasithin.B1Red.mem_autSec_iff (X := L) (W := U) (U' := Z)).1 a.2
    have hmemL : resHom U h ∈ autSub L U := mem_autSub.mpr ⟨h, hhL, rfl⟩
    have hccomm : resHom U h * (c : MulAut ↥U) = (c : MulAut ↥U) * resHom U h :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 _ hmemL
    have hsub : (⟨resHom U h, hU⟩ : stabSub (Z.subgroupOf U)) *
        (⟨(c : MulAut ↥U), hCstab c.2⟩ : stabSub (Z.subgroupOf U)) =
        (⟨(c : MulAut ↥U), hCstab c.2⟩ : stabSub (Z.subgroupOf U)) *
        (⟨resHom U h, hU⟩ : stabSub (Z.subgroupOf U)) :=
      Subtype.ext hccomm
    have hx : (quotHom (Z.subgroupOf U)).comp (Subgroup.inclusion hCstab) c =
        quotHom (Z.subgroupOf U) ⟨(c : MulAut ↥U), hCstab c.2⟩ := rfl
    have ha : (a : MulAut (Sec U Z)) = quotHom (Z.subgroupOf U) ⟨resHom U h, hU⟩ := hEq.symm
    rw [hx]
    change (quotHom (Z.subgroupOf U) ⟨(c : MulAut ↥U), hCstab c.2⟩)
        ((a : MulAut (Sec U Z)) p) =
      (a : MulAut (Sec U Z))
        ((quotHom (Z.subgroupOf U) ⟨(c : MulAut ↥U), hCstab c.2⟩) p)
    rw [ha]
    have hqmul : quotHom (Z.subgroupOf U) ⟨(c : MulAut ↥U), hCstab c.2⟩ *
        quotHom (Z.subgroupOf U) ⟨resHom U h, hU⟩ =
        quotHom (Z.subgroupOf U) ⟨resHom U h, hU⟩ *
        quotHom (Z.subgroupOf U) ⟨(c : MulAut ↥U), hCstab c.2⟩ := by
      rw [← map_mul, ← map_mul, hsub]
    exact congrArg (fun f : MulAut (Sec U Z) => f p) hqmul
  let Φ : ↥C →* ↥(XMod.eqvAut ↥Λ (Sec U Z)) :=
    ((quotHom (Z.subgroupOf U)).comp (Subgroup.inclusion hCstab)).codRestrict _ hmem
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have hker : (⟨(c : MulAut ↥U), hCstab c.2⟩ : stabSub (Z.subgroupOf U)) ∈
        (quotHom (Z.subgroupOf U)).ker := by
      rw [MonoidHom.mem_ker]
      have h2 := congrArg (fun x : ↥(XMod.eqvAut ↥Λ (Sec U Z)) => (x : MulAut (Sec U Z))) hc1
      change (quotHom (Z.subgroupOf U))
        (⟨(c : MulAut ↥U), hCstab c.2⟩ : stabSub (Z.subgroupOf U)) = 1
      exact h2
    rw [ker_quotHom, Subgroup.mem_subgroupOf, mem_centQuot] at hker
    obtain ⟨g, hgE, hgres⟩ := mem_autSub.mp (Subgroup.mem_inf.mp c.2).1
    have hgq : ∀ w ∈ U, (g : MulAut W) w * w⁻¹ ∈ U ⊓ fixV L := by
      intro w hw
      have h1 : (g : MulAut W) w * w⁻¹ ∈ Z := by
        have h2 := hker ⟨w, hw⟩
        rw [Subgroup.mem_subgroupOf] at h2
        change ((c : MulAut ↥U) ⟨w, hw⟩ : W) * w⁻¹ ∈ Z at h2
        rw [← hgres] at h2
        rwa [resHom_apply] at h2
      exact h1
    have htriv : ∀ w ∈ U, (g : MulAut W) w = w :=
      s16h_H5_triv_of_triv_quot hc.comp (Subgroup.mem_inf.mp (hE hgE)).2 hgq
    apply Subtype.ext
    rw [← hgres]
    ext u
    change (g : MulAut W) (u : W) = (u : W)
    exact htriv (u : W) u.2
  haveI : IsCyclic ↥(XMod.eqvAut ↥Λ (Sec U Z)) := hcycΓ
  refine ⟨isCyclic_of_injective Φ hΦinj, ?_⟩
  have hdvdC : Nat.card ↥C ∣ Nat.card ↥(XMod.eqvAut ↥Λ (Sec U Z)) := by
    have heq : Nat.card ↥C = Nat.card ↥(Φ.range) :=
      Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv
    rw [heq]
    exact Subgroup.card_subgroup_dvd_card Φ.range
  exact hoddΓ.of_dvd_nat hdvdC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
