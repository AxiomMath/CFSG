module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley TableB Matrix

theorem ggNoTransvectionSCr_of_frameTorus_sim {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R : Type}
    [Group R] {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R) {t : Multiplicative (Fin n → ZMod p) →* R}
    (ht : Function.Injective t)
    (hT : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom)
    {S : Matrix (Fin n) (Fin n) (ZMod p)} (hS : Sᵀ = S) (hdet : S.det ≠ 0)
    (hK : ∀ φ : MulAut R, (∀ x ∈ t.range, φ x ∈ t.range) →
      ∃ (M : (Fin n → ZMod p) →+ (Fin n → ZMod p)) (μ : ZMod p),
        (∀ v, φ (t (Multiplicative.ofAdd v)) = t (Multiplicative.ofAdd (M v))) ∧
          ∀ v w, M v ⬝ᵥ (S *ᵥ M w) = μ * (v ⬝ᵥ (S *ᵥ w))) :
    GGNoTransvectionSCr p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc α hα htv
  obtain ⟨φ, hφ⟩ := hα
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hEab, hcardE, hscE⟩ :=
    exists_innerModel (Fact.out) hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  let Φ : A.comap Λ →* A :=
    { toFun := fun e => ⟨Λ e, e.2⟩
      map_one' := Subtype.ext (map_one Λ)
      map_mul' := fun e₁ e₂ => Subtype.ext (map_mul Λ (e₁ : R) (e₂ : R)) }
  have hΦbij : Function.Bijective Φ := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  let Φe : A.comap Λ ≃* A := MulEquiv.ofBijective Φ hΦbij
  let χ : A →* R := (A.comap Λ).subtype.comp Φe.symm.toMonoidHom
  have hχΛ : ∀ a : A, Λ (χ a) = (a : MulAut L') := fun a =>
    congrArg Subtype.val (Φe.apply_symm_apply a)
  have hχrange : χ.range = A.comap Λ := by
    ext e
    constructor
    · rintro ⟨a, rfl⟩
      show Λ (χ a) ∈ A
      rw [hχΛ a]
      exact a.2
    · intro he
      refine ⟨Φ ⟨e, he⟩, hΛinj ?_⟩
      rw [hχΛ (Φ ⟨e, he⟩)]
      rfl
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := by
    intro a l
    have h := hΛmap (χ a) l
    rw [hχΛ a] at h
    exact h
  have huniq : ∀ (a : MulAut L') (g g' : R), (∀ l, ψ (a l) = g * ψ l * g⁻¹) →
      (∀ l, ψ (a l) = g' * ψ l * g'⁻¹) → g = g' := by
    intro a g g' hg hg'
    have hc : g'⁻¹ * g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨l, rfl⟩ := hψ x
      have e := (hg l).symm.trans (hg' l)
      calc ψ l * (g'⁻¹ * g) = g'⁻¹ * (g' * ψ l * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * ψ l * g⁻¹) * g := by rw [e]
        _ = (g'⁻¹ * g) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext ?_
    rw [← hχΛ a, ha, map_one]
    rfl
  have hEA : IsElemAbelian p χ.range := hχrange ▸ hEab
  have hcard : Nat.card χ.range = Nat.card A := by rw [hχrange, hcardE]
  have hSCE : ∀ g : R, (∀ e ∈ χ.range, g * e = e * g) → g ^ p = 1 → g ∈ χ.range := by
    intro g hgc hgp
    rw [hχrange] at hgc ⊢
    exact hscE g hgc hgp
  obtain ⟨c, hc⟩ := hT χ.range hEA (hcard ▸ hr) hSCE
  set J : Multiplicative (Fin n → ZMod p) →* R := (MulAut.conj c).toMonoidHom.comp t with hJdef
  have hJmem : ∀ s, J s ∈ χ.range := fun s => by
    rw [hc]
    exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  have hJinj : Function.Injective J := (MulAut.conj c).injective.comp ht
  set e : A ≃* χ.range := MonoidHom.ofInjective hχinj with hedef
  set κ : Multiplicative (Fin n → ZMod p) →* A :=
    e.symm.toMonoidHom.comp (J.codRestrict χ.range hJmem) with hκdef
  have hκ : ∀ s, χ (κ s) = J s := fun s =>
    MonoidHom.apply_ofInjective_symm hχinj (J.codRestrict χ.range hJmem s)
  have hκinj : Function.Injective κ := fun s s' h => hJinj (by rw [← hκ s, ← hκ s', h])
  have hκsurj : ∀ a : A, ∃ s, κ s = a := by
    intro a
    have ha : χ a ∈ χ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
    rw [hc] at ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    refine ⟨s, hχinj ?_⟩
    rw [hκ s]
    exact hxa
  set ι : Multiplicative (Fin n → ZMod p) →* MulAut L' := A.subtype.comp κ with hιdef
  have hι : Function.Injective ι := fun s s' h => hκinj (Subtype.ext h)
  have hιrange : ι.range = A := by
    ext a
    constructor
    · rintro ⟨s, rfl⟩
      exact (κ s).2
    · intro ha
      obtain ⟨s, hs⟩ := hκsurj ⟨a, ha⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  set αA : MulAut A := A.normalizerMonoidHom α with hαAdef
  have hαAcoe : ∀ b : A, ((αA b : A) : MulAut L') =
      (α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹ := fun b => rfl
  have hαinv : ∀ l, (α : MulAut L') ((α : MulAut L')⁻¹ l) = l := fun l => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hφinv : ∀ l, φ (ψ ((α : MulAut L')⁻¹ l)) = ψ l := fun l => by
    rw [hφ, hαinv]
  have hequiv : ∀ b : A, χ (αA b) = φ (χ b) := by
    intro b
    refine huniq _ _ _ (hχ (αA b)) (fun l => ?_)
    calc ψ (((αA b : A) : MulAut L') l)
        = ψ ((α : MulAut L') (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := by
          rw [hαAcoe, MulAut.mul_apply, MulAut.mul_apply]
      _ = φ (ψ (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := (hφ _).symm
      _ = φ (χ b * ψ ((α : MulAut L')⁻¹ l) * (χ b)⁻¹) := by rw [hχ b]
      _ = φ (χ b) * φ (ψ ((α : MulAut L')⁻¹ l)) * (φ (χ b))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = φ (χ b) * ψ l * (φ (χ b))⁻¹ := by rw [hφinv l]
  have hφE : ∀ y ∈ χ.range, φ y ∈ χ.range := by
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← hequiv a]
    exact MonoidHom.mem_range.mpr ⟨αA a, rfl⟩
  set ψ' : MulAut R := (MulAut.conj c)⁻¹ * φ * MulAut.conj c with hψ'def
  have hψ'app : ∀ x : R, ψ' x = c⁻¹ * φ (c * x * c⁻¹) * c := fun x => rfl
  have hψ'T : ∀ x ∈ t.range, ψ' x ∈ t.range := by
    intro x hx
    have h1 : c * x * c⁻¹ ∈ χ.range := by
      rw [hc]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 : φ (c * x * c⁻¹) ∈ χ.range := hφE _ h1
    rw [hc] at h2
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp h2
    have hψz : ψ' x = z := by
      rw [hψ'app, ← hzeq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hψz]
    exact hz
  obtain ⟨M, μ, hMψ, hMiso⟩ := hK ψ' hψ'T
  have hφJ : ∀ s : Fin n → ZMod p,
      φ (J (Multiplicative.ofAdd s)) = J (Multiplicative.ofAdd (M s)) := by
    intro s
    have h1 := hMψ s
    rw [hψ'app] at h1
    show φ (c * t (Multiplicative.ofAdd s) * c⁻¹) = c * t (Multiplicative.ofAdd (M s)) * c⁻¹
    rw [← h1]
    group
  have hrel : ∀ (b : A) (s : Fin n → ZMod p), (b : MulAut L') = ι (Multiplicative.ofAdd s) →
      ((αA b : A) : MulAut L') = ι (Multiplicative.ofAdd (M s)) := by
    intro b s hb
    have hbκ : b = κ (Multiplicative.ofAdd s) := Subtype.ext hb
    have hχb : χ b = J (Multiplicative.ofAdd s) := by rw [hbκ, hκ]
    have hχα : χ (αA b) = J (Multiplicative.ofAdd (M s)) := by
      rw [hequiv b, hχb, hφJ]
    have hαAκ : αA b = κ (Multiplicative.ofAdd (M s)) := hχinj (hχα.trans (hκ _).symm)
    show ((αA b : A) : MulAut L') = ((κ (Multiplicative.ofAdd (M s)) : A) : MulAut L')
    rw [hαAκ]
  obtain ⟨hcardfix, hNfix⟩ := NoTvAut.transvection_coords (p := p) hι hιrange (t := ⇑M) hrel htv
  exact NoTvAut.false_of_isTransvection_similitude (p := p) hp2 hS hdet M μ hMiso hcardfix hNfix

section FramePackage


theorem ggNoTransvectionSCr_of_framePackage {p r : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hr : 4 ≤ r) {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I) (hcp : GGCenterPrime p R)
    (h : GGTwE6FramePackage p R) : GGNoTransvectionSCr p r R I := by
  obtain ⟨t, m, ht, hm, hTpkg, hAutpkg⟩ := h
  have hp4r : p ^ 4 ≤ p ^ r := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne p)) hr
  refine ggNoTransvectionSCr_of_frameTorus_sim (p := p) (n := 6) (r := r)
    (S := NoTvAut.cartanMod TwistTag.E6.tag p) hp2 hZ hIp hcp ht ?_ ?_ ?_ ?_
  · intro E hE hrE hsc
    exact hTpkg E hE (le_trans hp4r hrE) hsc
  · exact NoTvAut.cartanMod_transpose
  · have h1 : (NoTvAut.cartanMod TwistTag.E6.tag p).det =
        ((TwistTag.E6.tag.symmetrizedCartan.det : ℤ) : ZMod p) :=
      NoTvAut.det_cartanMod
    intro h0
    exact (StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := p) hp3).ne_zero
      (h1.symm.trans h0)
  · intro φ hφT
    obtain ⟨w, c, hc, hβw⟩ := hAutpkg φ hφT
    let M : (Fin 6 → ZMod p) →+ (Fin 6 → ZMod p) :=
      c • NoTvAut.torusActHom TwistTag.E6.tag p w
    have hMapply : ∀ x, M x = c • TableBExc.torusAct TwistTag.E6.tag p w x := fun x =>
      congrArg (fun y => c • y) (NoTvAut.torusActHom_apply w x)
    refine ⟨M, c ^ 2, ?_, ?_⟩
    · intro v
      rw [hβw v, hMapply]
    · intro v v'
      have hform : TableBExc.torusAct TwistTag.E6.tag p w v ⬝ᵥ
          (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ TableBExc.torusAct TwistTag.E6.tag p w v') =
          v ⬝ᵥ (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ v') :=
        NoTvAut.torusAct_form w v v'
      calc c • TableBExc.torusAct TwistTag.E6.tag p w v ⬝ᵥ
              (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ
                (c • TableBExc.torusAct TwistTag.E6.tag p w v'))
            = c • TableBExc.torusAct TwistTag.E6.tag p w v ⬝ᵥ
                (c • (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ
                  TableBExc.torusAct TwistTag.E6.tag p w v')) := by rw [Matrix.mulVec_smul]
        _ = c • (c • (TableBExc.torusAct TwistTag.E6.tag p w v ⬝ᵥ
                (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ
                  TableBExc.torusAct TwistTag.E6.tag p w v'))) := by
              rw [smul_dotProduct, dotProduct_smul]
        _ = c • (c • (v ⬝ᵥ (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ v'))) := by rw [hform]
        _ = c ^ 2 * (v ⬝ᵥ (NoTvAut.cartanMod TwistTag.E6.tag p *ᵥ v')) := by
              rw [smul_eq_mul, smul_eq_mul, pow_two]
              ring

end FramePackage

end TwE6TB

end CFSG.StandardType
