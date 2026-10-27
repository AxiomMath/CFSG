module

public import CFSG.Quasithin.Background.SmithB51SL3E
public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section Conj

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem matAut_eq_natAct (γ : ↥(StatedSL 3 K)) (x : Multiplicative (Fin 3 → K)) :
    H.matAut (γ : GL (Fin 3) K) x = natAct (StatedSL 3 K) γ x := rfl

@[expose] noncomputable def NatSec.conj {W U : Subgroup V} (c : NatSec L W U K)
    (g : ↥(StatedSL 3 K)) : NatSec L W U K where
  π := c.π.comp (MulAut.conj g).toMonoidHom
  hπ := c.hπ.comp (MulAut.conj g).bijective
  f := (H.matAut ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K)).toMonoidHom.comp c.f
  hfs := (H.matAut _).surjective.comp c.hfs
  hfk w := by
    rw [← c.hfk w]
    exact (H.matAut ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K)).map_eq_one_iff
  hfe γ w hw := by
    have hw' : ((c.π (g * γ * g⁻¹) : ↥L) : MulAut V) w ∈ W := hw
    show H.matAut _ (c.f ⟨_, hw'⟩) = _
    rw [c.hfe _ w hw']
    apply Multiplicative.toAdd.injective
    show slAct g⁻¹ (slAct (g * γ * g⁻¹) (Multiplicative.toAdd (c.f w))) =
      slAct γ (slAct g⁻¹ (Multiplicative.toAdd (c.f w)))
    rw [← slAct_mul, ← slAct_mul]
    congr 1
    group

theorem NatSec.conj_pre {W U : Subgroup V} (c : NatSec L W U K) (g : ↥(StatedSL 3 K))
    (B : Subgroup (MulAut V)) :
    (c.conj g).pre B = (c.pre B).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext γ
  constructor
  · intro hγ
    refine ⟨g * γ * g⁻¹, (show g * γ * g⁻¹ ∈ c.pre B from hγ), ?_⟩
    simp [mul_assoc]
  · rintro ⟨δ, hδ, rfl⟩
    show c.π (g * (g⁻¹ * δ * g⁻¹⁻¹) * g⁻¹) ∈ B.subgroupOf L
    have : g * (g⁻¹ * δ * g⁻¹⁻¹) * g⁻¹ = δ := by group
    rw [this]
    exact hδ

abbrev stdAxis (K : Type) [Field K] : Submodule K (Fin 3 → K) := coordHyp 2

theorem NatSec.standardize {W U : Subgroup V} (c : NatSec L W U K) {A : Subgroup (MulAut V)}
    (h : Module.finrank K (fixK (c.pre A)) = 2 ∧ c.pre A = axisSub (fixK (c.pre A))) :
    ∃ c' : NatSec L W U K, c'.pre A = axisSub (stdAxis K) ∧ ∀ w, c'.f w = 1 ↔ c.f w = 1 := by
  obtain ⟨g, hg⟩ := exists_slMap_eq (finrank_coordHyp (K := K) 2) h.1
  refine ⟨c.conj g, ?_, fun w => ?_⟩
  · rw [NatSec.conj_pre, h.2, map_conj_axisSub g⁻¹ (fixK (c.pre A)), ← hg]
    congr 1
    ext v
    rw [mem_slMap, mem_slMap, inv_inv, slAct_inv_slAct]
  · exact (H.matAut ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K)).map_eq_one_iff

end Conj

section SamePi

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

open H.SL3Pair
open scoped Matrix

theorem slAct_slEquiv_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    slAct (slEquiv K (Matrix.SpecialLinearGroup.transvection hij c)) v =
      v + Pi.single i (c * v j) := by
  show (((slEquiv K _ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = _
  rw [coe_slEquiv, Matrix.SpecialLinearGroup.transvection_coe]
  exact H.transvection_mulVec i j c v

theorem mem_of_slAct_eq {W : Submodule K (Fin 3 → K)} (hW : Module.finrank K W = 2)
    {g : ↥(StatedSL 3 K)} (hg : g ∈ axisSub W) (hne : g ≠ 1) {v : Fin 3 → K}
    (hv : slAct g v = v) : v ∈ W := by
  have hle : Subgroup.zpowers g ≤ axisSub W := (Subgroup.zpowers_le).2 hg
  have hbot : Subgroup.zpowers g ≠ ⊥ := by
    intro h
    exact hne (Subgroup.zpowers_eq_bot.1 h)
  rw [← fixK_eq_of_le_axisSub hW hle hbot]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have key : ∀ m : ℕ, slAct (g ^ m) v = v := by
    intro m
    induction m with
    | zero => rw [pow_zero, slAct_one]
    | succ m ih => rw [pow_succ, slAct_mul, hv, ih]
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, key]
  · rw [zpow_neg, zpow_natCast]
    have := slAct_inv_slAct (g ^ m) v
    rwa [key] at this

theorem exists_natSec_samePi [Finite K] [CharP K 2] {W₁ U₁ W₂ U₂ : Subgroup V}
    (c₁ : NatSec L W₁ U₁ K) (c₂ : NatSec L W₂ U₂ K) {A : Subgroup (MulAut V)}
    (h₁ : c₁.pre A = axisSub (stdAxis K)) (h₂ : c₂.pre A = axisSub (stdAxis K)) :
    ∃ c₂' : NatSec L W₂ U₂ K, c₂'.π = c₁.π := by
  classical
  set e₁ := MulEquiv.ofBijective c₁.π c₁.hπ with he₁
  set e₂ := MulEquiv.ofBijective c₂.π c₂.hπ with he₂
  set α : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K) := e₁.trans e₂.symm with hαdef
  have hα : ∀ γ, c₂.π (α γ) = c₁.π γ := fun γ => e₂.apply_symm_apply (e₁ γ)
  have hαT : ∀ γ ∈ axisSub (stdAxis K), α γ ∈ axisSub (stdAxis K) := by
    intro γ hγ
    rw [← h₂]
    show ((c₂.π (α γ) : ↥L) : MulAut V) ∈ A
    rw [hα]
    have : γ ∈ c₁.pre A := by rw [h₁]; exact hγ
    exact this
  set α'' : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
    ((slEquiv K).trans α).trans (slEquiv K).symm with hα''
  obtain ⟨M, σ, ε, hε, hstd⟩ := exists_eq_stdAut α''
  have hαmat : ∀ γ : ↥(StatedSL 3 K), α γ = slEquiv K (CFSG.QuasithinUnique.K1.stdAut M σ ε
      ((slEquiv K).symm γ)) := by
    intro γ
    rw [← hstd, hα'']
    simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with h0 | h1
  ·
    subst h0
    have hform : ∀ γ : ↥(StatedSL 3 K),
        ((α γ : ↥(StatedSL 3 K)) : GL (Fin 3) K) = M * mapGL σ (γ : GL (Fin 3) K) * M⁻¹ := by
      intro γ
      apply Units.ext
      rw [hαmat, Units.val_mul, Units.val_mul, coe_mapGL, coe_slEquiv,
        CFSG.QuasithinUnique.K1.coe_stdAut_zero]
      conv_rhs => rw [← MulEquiv.apply_symm_apply (slEquiv K) γ, coe_slEquiv]
    refine ⟨⟨c₁.π, c₁.hπ, (twistAut M σ).toMonoidHom.comp c₂.f,
      (twistAut M σ).surjective.comp c₂.hfs, fun w => ?_, fun γ w hw => ?_⟩, rfl⟩
    · rw [← c₂.hfk w]
      exact (twistAut M σ).map_eq_one_iff
    · have hw2 : ((c₂.π (α γ) : ↥L) : MulAut V) w ∈ W₂ := by rw [hα]; exact hw
      have hsub : (⟨_, hw⟩ : ↥W₂) = ⟨_, hw2⟩ := by
        apply Subtype.ext
        show ((c₁.π γ : ↥L) : MulAut V) w = ((c₂.π (α γ) : ↥L) : MulAut V) w
        rw [hα]
      show twistAut M σ (c₂.f ⟨_, hw⟩) = natAct (StatedSL 3 K) γ (twistAut M σ (c₂.f w))
      rw [hsub, c₂.hfe _ w hw2, ← matAut_eq_natAct, ← matAut_eq_natAct, hform,
        ← MulAut.mul_apply, twistAut_mul, MulAut.mul_apply]
  ·
    subst h1
    exfalso
    have key : ∀ j : Fin 3, (hj : j ≠ 2) → ∀ v : Fin 3 → K, v j = 0 →
        ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = 0 := by
      intro j hj v hv
      set t := slEquiv K (Matrix.SpecialLinearGroup.transvection hj (1 : K)) with ht
      have htT : t ∈ axisSub (stdAxis K) := by
        apply mem_axisSub_coordHyp hj
        intro x
        rw [ht, slAct_slEquiv_transvection, one_mul]
      have hαt := hαT t htT
      have hne : α t ≠ 1 := by
        intro h
        have : t = 1 := α.injective (h.trans (map_one α).symm)
        have h2 := congrArg (fun g => slAct g (Pi.single 2 1)) this
        simp only [ht, slAct_slEquiv_transvection, slAct_one, Pi.single_eq_same, one_mul] at h2
        have h3 := congrFun h2 j
        simp [hj] at h3
      have hmat : (((α t : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (M : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single 2 j (-1)) *
            ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hαmat, coe_slEquiv, CFSG.QuasithinUnique.K1.coe_stdAut_one, ht,
          MulEquiv.symm_apply_apply, Matrix.SpecialLinearGroup.transvection_inv,
          Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
          Matrix.transpose_single, CFSG.QuasithinUnique.K1.map_one_add_single, map_neg, map_one]
      have hfix : slAct (α t) ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
        show (((α t : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
        have hMM : ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, CFSG.QuasithinUnique.K1.coe_inv_mul_coe, Matrix.one_mulVec]
        rw [hmat, ← Matrix.mulVec_mulVec, hMM, ← Matrix.mulVec_mulVec]
        congr 1
        have := H.transvection_mulVec 2 j (-1 : K) v
        rw [hv, mul_zero, Pi.single_zero, add_zero] at this
        exact this
      exact mem_coordHyp.1 (mem_of_slAct_eq (finrank_coordHyp 2) hαt hne hfix)
    have hall : ∀ v : Fin 3 → K, ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = 0 := by
      intro v
      have hv : v = (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1) + v 2 • Pi.single 2 1 := by
        ext k
        fin_cases k <;> simp
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, Pi.add_apply, Pi.add_apply,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply,
        Pi.smul_apply, Pi.smul_apply,
        key 1 (by decide) (Pi.single 0 1) (by simp),
        key 0 (by decide) (Pi.single 1 1) (by simp),
        key 0 (by decide) (Pi.single 2 1) (by simp)]
      simp
    have h1 := hall (((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1)
    rw [Matrix.mulVec_mulVec, CFSG.QuasithinUnique.K1.coe_mul_coe_inv, Matrix.one_mulVec,
      Pi.single_eq_same] at h1
    exact one_ne_zero h1

end SamePi

section Std

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

structure SL3Std (G L : Subgroup (MulAut V)) : Type 1 where
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
  hπ : e₂.π = e₁.π
  hpre : e₁.pre A = axisSub (stdAxis K)
  hcardA : Nat.card A = Nat.card K ^ 2
  hlift : ∀ u ∈ commV L, (∀ a ∈ A, a u * u⁻¹ ∈ I) →
    ∃ u' ∈ commV L, u' ∈ fixV A ∧ u' * u⁻¹ ∈ I

attribute [instance] SL3Std.instField SL3Std.instFinite

theorem exists_sl3Std (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) : Nonempty (SL3Std G L) := by
  obtain ⟨m⟩ := exists_sl3Mod hA21 hB42 hA36 hIH hV h hU hK eL
  have : CharP m.K 2 := charP_two_of_card_eq m.hK
  obtain ⟨e₁, he₁, -⟩ := m.e₁.standardize m.hax₁
  obtain ⟨e₂, he₂, he₂f⟩ := m.e₂.standardize m.hax₂
  obtain ⟨e₂', hπ⟩ := exists_natSec_samePi e₁ e₂ he₁ he₂
  exact ⟨⟨m.A, m.I, m.K, m.n, m.hK, m.hmin, m.hAL, m.hquad, m.hIU, m.hLI, e₁, e₂', hπ, he₁,
    m.hcardA, m.hlift⟩⟩

end Std

end B5

end CFSG.Quasithin
