module

public import CFSG.Quasithin.Vol2.Ch3T326PD

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

section Side

variable {M Mp X : Subgroup (MulAut W)} {V : Subgroup W}
  {hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))}

theorem fix_eq_one_of_side (hW : ∀ w : W, w ^ 2 = 1) (hS : SideHyp hMp X V) {P : Subgroup ↥M}
    (hP5 : IsPGroup 5 ↥P)
    (hPX : ∀ g ∈ P, ∀ l ∈ X, ((g : ↥M) : MulAut W) * l = l * ((g : ↥M) : MulAut W))
    (hPY : letI := qAct hMp; ∀ g ∈ P, ∀ q ∈ tilde Mp ⊤ (commV X), g • q ∈ tilde Mp ⊤ (commV X))
    {g : ↥M} (hg : g ∈ P) (hne : letI := qAct hMp; resJ P (tilde Mp ⊤ (commV X)) hPY ⟨g, hg⟩ ≠ 1) :
    letI := qAct hMp; ∀ q ∈ tilde Mp ⊤ (commV X), g • q = q → q = 1 := by
  let _i := qAct hMp
  set ρ := resJ P (tilde Mp ⊤ (commV X)) hPY with hρ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hP5 ⟨g, hg⟩
  have hσn : ρ ⟨g, hg⟩ ^ 5 ^ n = 1 := by rw [← map_pow, hn, map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
    (orderOf_dvd_of_pow_eq_one hσn)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hne hk
  set g' : ↥M := g ^ 5 ^ (k - 1) with hg'
  have hg'P : g' ∈ P := P.pow_mem hg _
  have hρg' : ρ ⟨g', hg'P⟩ = ρ ⟨g, hg⟩ ^ 5 ^ (k - 1) := by
    rw [← map_pow]
    rfl
  have h5 : (ρ ⟨g', hg'P⟩) ^ 5 = 1 := by
    rw [hρg', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), ← hk,
      pow_orderOf_eq_one]
  have hne' : ρ ⟨g', hg'P⟩ ≠ 1 := by
    rw [hρg']
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ (by norm_num)) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
  have h5' : ρ (⟨g', hg'P⟩ ^ 5) = 1 := by rw [map_pow]; exact h5
  have hyp : ∀ q ∈ tilde Mp ⊤ (commV X), g' ^ 5 • q = q := fun q hq =>
    congrArg (fun e : MulAut ↥(tilde Mp ⊤ (commV X)) =>
      ((e ⟨q, hq⟩ : ↥(tilde Mp ⊤ (commV X))) : W ⧸ modFix Mp (⊤ : Subgroup W))) h5'
  have hmove : ∃ q ∈ tilde Mp ⊤ (commV X), (⟨(g' : MulAut W), g'.2⟩ : ↥M) • q ≠ q := by
    by_contra hcon
    push Not at hcon
    exact hne' (MulEquiv.ext fun q => Subtype.ext (hcon q.1 q.2))
  have hcomm : ∀ l ∈ X, (g' : MulAut W) * l = l * (g' : MulAut W) := hPX g' hg'P
  rcases prime_of_side hW hS g'.2 hcomm (by norm_num) (by norm_num) hyp hmove with
    h3 | h7 | ⟨-, hfree⟩
  · norm_num at h3
  · norm_num at h7
  · intro q hq hgq
    have key : ∀ m : ℕ, g ^ m • q = q := fun m => by
      induction m with
      | zero => rw [pow_zero, one_smul]
      | succ m ih => rw [pow_succ, mul_smul, hgq, ih]
    exact hfree q hq (key _)

theorem card_range_le_sixteen (hW : ∀ w : W, w ^ 2 = 1) (hS : SideHyp hMp X V)
    {P : Subgroup ↥M} (hP5 : IsPGroup 5 ↥P)
    (hPX : ∀ g ∈ P, ∀ l ∈ X, ((g : ↥M) : MulAut W) * l = l * ((g : ↥M) : MulAut W))
    (hPY : letI := qAct hMp; ∀ g ∈ P, ∀ q ∈ tilde Mp ⊤ (commV X), g • q ∈ tilde Mp ⊤ (commV X)) :
    letI := qAct hMp
    Nat.card ↥(resJ P (tilde Mp ⊤ (commV X)) hPY).range ≤ 16 := by
  let _i := qAct hMp
  set Λ := X.subgroupOf M with hΛ
  set Y := tilde Mp ⊤ (commV X) with hYdef
  set I := tilde Mp ⊤ V with hIdef
  set ρ := resJ P Y hPY with hρ
  have hQ : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), q ^ 2 = 1 := quot_sq_of hW _
  have hI := hS.irr
  have hY := hS.homog
  obtain ⟨K, hKf, hKfin, π, hK, hR⟩ := hS.nat
  have hE := card_end_eq_two_of_nat hMp hS.le hK hR hI
  have := (XMod.isIrr_iff hI.1).1 hI
  have hIle : I ≤ isoComp ↥Λ I := le_isoComp hI (XMod.Iso.refl I)
  have := isSemisimpleModule_toSubmod hI hI.1 hIle
  have := isSemisimpleModule_toSubmod hI hY.1 hY.2.1
  have hIiso := isIsotypicOfType_toSubmod hI hI.1 hIle
  have hYiso := isIsotypicOfType_toSubmod hI hY.1 hY.2.1
  have hH := card_linearMap_eq hIiso hYiso (pow_one _).symm (card_toSubmod_eq_pow hQ hI hY)
  rw [one_mul, hE] at hH
  set MI := XMod.toSubmod hI.1 with hMI
  set MY := XMod.toSubmod hY.1 with hMY
  have hfinH : Finite (↥MI →ₗ[↥(XMod.opRing ↥Λ (W ⧸ modFix Mp (⊤ : Subgroup W)))] ↥MY) :=
    Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : ↥MI →ₗ[↥(XMod.opRing ↥Λ (W ⧸ modFix Mp (⊤ : Subgroup W)))] ↥MY,
      φ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card (↥MI →ₗ[↥(XMod.opRing ↥Λ (W ⧸ modFix Mp (⊤ : Subgroup W)))] ↥MY) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    rw [hH] at h1
    norm_num at h1
  obtain ⟨s₀, hs₀⟩ : ∃ s, φ₀ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ₀ (LinearMap.ext hcon)
  have hgΛ : ∀ g ∈ P, ∀ l ∈ Λ, l * g = g * l := fun g hg l hl =>
    Subtype.ext (hPX g hg _ (Subgroup.mem_subgroupOf.1 hl)).symm
  set q₀ : W ⧸ modFix Mp (⊤ : Subgroup W) := Additive.toMul ((φ₀ s₀ : ↥MY) : Additive _)
    with hq₀
  have hq₀Y : q₀ ∈ Y := (φ₀ s₀).2
  have hq₀1 : q₀ ≠ 1 := by
    intro h1
    apply hs₀
    apply Subtype.ext
    show ((φ₀ s₀ : ↥MY) : Additive (W ⧸ modFix Mp (⊤ : Subgroup W))) = 0
    have e : ((φ₀ s₀ : ↥MY) : Additive (W ⧸ modFix Mp (⊤ : Subgroup W))) = Additive.ofMul q₀ :=
      rfl
    rw [e, h1, ofMul_one]
  have hkey : ∀ g g' : ↥P, (g : ↥M) • q₀ = (g' : ↥M) • q₀ → ρ g = ρ g' := by
    intro g g' heq
    have hh : (g' : ↥M)⁻¹ * g ∈ P := P.mul_mem (P.inv_mem g'.2) g.2
    have hfix : ((g' : ↥M)⁻¹ * g) • q₀ = q₀ := by rw [mul_smul, heq, inv_smul_smul]
    by_contra hne
    have hne' : ρ ⟨(g' : ↥M)⁻¹ * g, hh⟩ ≠ 1 := by
      intro h1
      apply hne
      have h2 : ρ ⟨(g' : ↥M)⁻¹ * g, hh⟩ = (ρ g')⁻¹ * ρ g := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [h2, inv_mul_eq_one] at h1
      exact h1.symm
    exact hq₀1 (fix_eq_one_of_side hW hS hP5 hPX hPY hh hne' q₀ hq₀Y hfix)
  let Φ : ↥P → (↥MI →ₗ[↥(XMod.opRing ↥Λ (W ⧸ modFix Mp (⊤ : Subgroup W)))] ↥MY) :=
    fun g => (smulLin (hgΛ g g.2) hY.1 (hPY g g.2)) ∘ₗ φ₀
  have hΦ : ∀ g g' : ↥P, Φ g = Φ g' → ρ g = ρ g' := by
    intro g g' hgg
    have h1 : Additive.ofMul ((g : ↥M) • q₀) = Additive.ofMul ((g' : ↥M) • q₀) :=
      congrArg (fun ψ => ((ψ s₀ : ↥MY) : Additive (W ⧸ modFix Mp (⊤ : Subgroup W)))) hgg
    exact hkey g g' (Additive.ofMul.injective h1)
  have hinj : Function.Injective
      (fun x : ↥ρ.range => Φ (MonoidHom.mem_range.1 x.2).choose) := by
    intro x₁ x₂ hx
    have h1 := hΦ _ _ hx
    rw [(MonoidHom.mem_range.1 x₁.2).choose_spec, (MonoidHom.mem_range.1 x₂.2).choose_spec] at h1
    exact Subtype.ext h1
  calc Nat.card ↥ρ.range
      ≤ Nat.card (↥MI →ₗ[↥(XMod.opRing ↥Λ (W ⧸ modFix Mp (⊤ : Subgroup W)))] ↥MY) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 16 := by rw [hH]; norm_num

end Side

end CFSG.Quasithin.H13.T326
