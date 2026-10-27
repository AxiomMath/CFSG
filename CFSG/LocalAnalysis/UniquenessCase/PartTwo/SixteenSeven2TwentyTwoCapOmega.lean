module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitModel
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
open CFSG.LargeExtraspecial.O62
open CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem s16c167_commSpace_one :
    commSpace (1 : V₀ ≃ₗ[ZMod 2] V₀) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [commSpace, LinearMap.mem_range] at hw
  obtain ⟨v, hv⟩ := hw
  simpa using hv.symm

theorem s16c167_transv_unique_omega {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {E : Subgroup W} (hE : NatOmegaMinus L E ⊥ 6 1) {x y : MulAut W}
    (hxL : L.map (MulAut.conj x).toMonoidHom = L) (hyL : L.map (MulAut.conj y).toMonoidHom = L)
    (hxE : E.map x.toMonoidHom = E) (hyE : E.map y.toMonoidHom = E)
    {H : Subgroup W} (hHE : H ≤ E) (hH : E3.mQuot E H = 1)
    (hxH : ∀ e ∈ H, x e = e) (hyH : ∀ e ∈ H, y e = e)
    (hxT : ∀ e ∈ E, x e * e⁻¹ ∈ H) (hyT : ∀ e ∈ E, y e * e⁻¹ ∈ H) :
    (∀ e ∈ E, x e = e) ∨ (∀ e ∈ E, y e = e) ∨ (∀ e ∈ E, x e = y e) := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, hReal⟩ := hE
  letI := hK
  haveI : Finite K := hKf
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  rw [hdiv] at hReal
  obtain ⟨π, hπ⟩ := hReal
  let π' : ↥(StatedOmega (StatedQuadMinus 3 K b c)) →* ↥L := π
  have hπ' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))).RealizesVia L E ⊥ π' := hπ
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ'
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ l : ↥L, ∀ u ∈ E, (l : MulAut W) u ∈ E := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥E) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let βe : ↥E ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  obtain ⟨θ, ψ, hψθ, hψΩ⟩ := s16c1_statedOmega_minus_model (K := K) (b := b) (c := c)
    (by simpa using hK2) hpoly
  let Φ : ↥E ≃* Multiplicative V₀ := βe.trans (AddEquiv.toMultiplicative θ)
  have hΦγ : ∀ (γ : ↥(StatedOmega (StatedQuadMinus 3 K b c))) (u : ↥E),
      Φ ⟨((π' γ : ↥L) : MulAut W) u.1, hstab (π' γ) u u.2⟩ =
        Multiplicative.ofAdd ((ψ (γ : GL _ K)) (Multiplicative.toAdd (Φ u))) := by
    intro γ u
    have h := hβe γ u (hstab (π' γ) u u.2)
    have h1 : Multiplicative.toAdd (β ⟨((π' γ : ↥L) : MulAut W) u.1,
          hstab (π' γ) u u.2⟩) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K (γ : GL _ K)
          (Multiplicative.toAdd (β u)) := by
      rw [h, CFSG.Quasithin.natAct, toAdd_ofAdd,
        ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    have hΦapp : Φ ⟨((π' γ : ↥L) : MulAut W) u.1, hstab (π' γ) u u.2⟩ =
        Multiplicative.ofAdd (θ (Multiplicative.toAdd (β ⟨((π' γ : ↥L) : MulAut W) u.1,
          hstab (π' γ) u u.2⟩))) := rfl
    have hΦu : Multiplicative.toAdd (Φ u) = θ (Multiplicative.toAdd (β u)) := rfl
    rw [hΦapp, h1, hψθ (γ : GL _ K), ← hΦu]
  have hHisP : IsPGroup 2 ↥E :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by
      rw [pow_one, Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      exact Subtype.ext (by simpa using hW (g : W)))
  have hcardEH := E3.card_eq_two_pow_mul hHisP hHE
  have hcardι : Nat.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  have hK2' : Nat.card K = 2 := by simpa using hK2
  have hcardE : Nat.card ↥E = 64 := by
    rw [Nat.card_congr βe.toEquiv, (Nat.card_congr Multiplicative.ofAdd).symm,
      Nat.card_fun, hcardι, hK2']
    norm_num
  have hcardH : Nat.card ↥H = 32 := by
    rw [hH, pow_one] at hcardEH
    omega
  let H' : Submodule (ZMod 2) V₀ :=
    { carrier := {v | Φ.symm (Multiplicative.ofAdd v) ∈ (H.subgroupOf E : Subgroup ↥E)}
      zero_mem' := by
        show Φ.symm (Multiplicative.ofAdd (0 : V₀)) ∈ (H.subgroupOf E : Subgroup ↥E)
        simp
      add_mem' := by
        intro a b ha hb
        show Φ.symm (Multiplicative.ofAdd (a + b)) ∈ (H.subgroupOf E : Subgroup ↥E)
        rw [ofAdd_add, map_mul]
        exact (H.subgroupOf E).mul_mem ha hb
      smul_mem' := by
        intro m v hv
        rcases CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one m with rfl | rfl
        · show Φ.symm (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ (H.subgroupOf E : Subgroup ↥E)
          rw [zero_smul]
          simp
        · simpa using hv }
  have hcardH' : Nat.card ↥H' = Nat.card ↥H := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun v : ↥H' => (⟨(Φ.symm (Multiplicative.ofAdd (v : V₀))).1,
          Subgroup.mem_subgroupOf.mp v.2⟩ : ↥H)) ?_)
    constructor
    · intro a b hab
      apply Subtype.ext
      have h := congrArg (fun x : ↥H => (x : W)) hab
      have h2 : Φ.symm (Multiplicative.ofAdd (a : V₀)) =
          Φ.symm (Multiplicative.ofAdd (b : V₀)) := Subtype.ext h
      exact Multiplicative.ofAdd.injective (Φ.symm.injective h2)
    · intro h
      refine ⟨⟨Multiplicative.toAdd (Φ ⟨h.1, hHE h.2⟩), ?_⟩, ?_⟩
      · show Φ.symm (Multiplicative.ofAdd
            (Multiplicative.toAdd (Φ ⟨h.1, hHE h.2⟩))) ∈ (H.subgroupOf E : Subgroup ↥E)
        rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
        exact Subgroup.mem_subgroupOf.mpr h.2
      · apply Subtype.ext
        show (Φ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (Φ ⟨h.1, hHE h.2⟩)))).1 = h.1
        rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hH'fin : Module.finrank (ZMod 2) ↥H' = 5 := by
    have h1 : Nat.card ↥H' = 2 ^ 5 := by rw [hcardH', hcardH]; norm_num
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥H')
    rw [h1, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  have hV0fin : Module.finrank (ZMod 2) V₀ = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    norm_num
  have mkXV : ∀ (z : MulAut W), L.map (MulAut.conj z).toMonoidHom = L →
      (hzE : E.map z.toMonoidHom = E) → (hzH : ∀ e ∈ H, z e = e) →
      ∃ zV : V₀ ≃ₗ[ZMod 2] V₀, ∃ m : ∀ u : ↥E, z u.1 ∈ E,
        zV ∈ TauCeti.QuadraticMap.orthogonalGroup (qModel true) ∧
        H' ≤ fixSpace zV ∧
        (∀ u : ↥E, Φ ⟨z u.1, m u⟩ =
          Multiplicative.ofAdd (zV (Multiplicative.toAdd (Φ u)))) := by
    intro z hzL hzE hzH
    have hzEmem : ∀ e : ↥E, z e.1 ∈ E := fun e => by
      have h : z e.1 ∈ E.map z.toMonoidHom := Subgroup.mem_map.mpr ⟨e.1, e.2, rfl⟩
      rwa [hzE] at h
    let zE : ↥E ≃* ↥E := MulEquiv.ofBijective
      ({ toFun := fun e => ⟨z e.1, hzEmem e⟩
         map_one' := by ext; simp
         map_mul' := by intro a b; ext; simp [map_mul] } : ↥E →* ↥E)
      ⟨fun a b hab => Subtype.ext (z.injective (congrArg Subtype.val hab)), fun e => by
        have h : e.1 ∈ E.map z.toMonoidHom := by rw [hzE]; exact e.2
        obtain ⟨e', he', hze'⟩ := Subgroup.mem_map.mp h
        exact ⟨⟨e', he'⟩, Subtype.ext hze'⟩⟩
    have hzE_apply : ∀ u : ↥E, (zE u : W) = z u.1 := fun u => rfl
    let zM : Multiplicative V₀ ≃* Multiplicative V₀ := Φ.symm.trans (zE.trans Φ)
    have hzM_apply : ∀ u : ↥E, zM (Φ u) = Φ (zE u) := by
      intro u
      simp only [zM, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    let zAdd : V₀ ≃+ V₀ :=
      { toFun := fun v => Multiplicative.toAdd (zM (Multiplicative.ofAdd v))
        invFun := fun v => Multiplicative.toAdd (zM.symm (Multiplicative.ofAdd v))
        left_inv := fun v => by simp
        right_inv := fun v => by simp
        map_add' := fun a b => by
          simp only [ofAdd_add, map_mul, toAdd_mul] }
    let zV : V₀ ≃ₗ[ZMod 2] V₀ := zAdd.toLinearEquiv (fun m v =>
      (zAdd.toAddMonoidHom.toZModLinearMap 2).map_smul m v)
    have hzV_apply : ∀ v : V₀, zV v = Multiplicative.toAdd (zM (Multiplicative.ofAdd v)) :=
      fun v => rfl
    have hzV_symm : ∀ v : V₀, zV.symm v =
        Multiplicative.toAdd (zM.symm (Multiplicative.ofAdd v)) := fun v => rfl
    have hzVprop : ∀ u : ↥E, Φ ⟨z u.1, hzEmem u⟩ =
        Multiplicative.ofAdd (zV (Multiplicative.toAdd (Φ u))) := by
      intro u
      have h1 : zM (Φ u) = Φ (zE u) := hzM_apply u
      show Φ (zE u) = Multiplicative.ofAdd (zV (Multiplicative.toAdd (Φ u)))
      rw [← h1, hzV_apply]
      simp
    have hconj_mem : ∀ l : ↥L, (MulAut.conj z) (l : MulAut W) ∈ L := by
      intro l
      have h : (MulAut.conj z) (l : MulAut W) ∈ L.map (MulAut.conj z).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(l : MulAut W), l.2, rfl⟩
      rwa [hzL] at h
    have hzE_conj : ∀ (γ : ↥(StatedOmega (StatedQuadMinus 3 K b c))) (w : ↥E),
        zE ⟨((π' γ : ↥L) : MulAut W) w.1, hstab (π' γ) w w.2⟩ =
          ⟨(MulAut.conj z ((π' γ : ↥L) : MulAut W)) (zE w).1,
            hstab ⟨MulAut.conj z ((π' γ : ↥L) : MulAut W), hconj_mem (π' γ)⟩
              (zE w) (zE w).2⟩ := by
      intro γ w
      apply Subtype.ext
      show z (((π' γ : ↥L) : MulAut W) w.1) =
        (MulAut.conj z ((π' γ : ↥L) : MulAut W)) (zE w).1
      rw [hzE_apply, MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply]
      simp
    have hzV_norm : ∀ g ∈ Ω₀ true, zV * g * zV⁻¹ ∈ Ω₀ true := by
      intro g hg
      obtain ⟨γ, hγS, hγeq⟩ := (hψΩ g).1 hg
      rw [← hγeq]
      let γs : ↥(StatedOmega (StatedQuadMinus 3 K b c)) := ⟨γ, hγS⟩
      change zV * ψ (γs : GL _ K) * zV⁻¹ ∈ Ω₀ true
      let lz : ↥L := ⟨(MulAut.conj z) ((π' γs : ↥L) : MulAut W), hconj_mem (π' γs)⟩
      let γ' : ↥(StatedOmega (StatedQuadMinus 3 K b c)) := Classical.choose (hπ'.1 lz)
      have hγ' : π' γ' = lz := Classical.choose_spec (hπ'.1 lz)
      have hγ'1 : ((π' γ' : ↥L) : MulAut W) =
          MulAut.conj z ((π' γs : ↥L) : MulAut W) := by rw [hγ']
      have hpoint : ∀ u : ↥E,
          zV (ψ (γs : GL _ K) (zV.symm (Multiplicative.toAdd (Φ u)))) =
            ψ (γ' : GL _ K) (Multiplicative.toAdd (Φ u)) := by
        intro u
        have hsymm_inner : zM.symm (Φ u) = Φ (zE.symm u) := by
          apply zM.injective
          rw [MulEquiv.apply_symm_apply, hzM_apply, MulEquiv.apply_symm_apply]
        have hsymm : zV.symm (Multiplicative.toAdd (Φ u)) =
            Multiplicative.toAdd (Φ (zE.symm u)) := by
          rw [hzV_symm, ofAdd_toAdd, hsymm_inner]
        rw [hsymm]
        have hψ : ψ (γs : GL _ K) (Multiplicative.toAdd (Φ (zE.symm u))) =
            Multiplicative.toAdd (Φ ⟨((π' γs : ↥L) : MulAut W) (zE.symm u).1,
              hstab (π' γs) (zE.symm u) (zE.symm u).2⟩) := by
          rw [← toAdd_ofAdd (ψ (γs : GL _ K) (Multiplicative.toAdd (Φ (zE.symm u)))),
            ← hΦγ γs (zE.symm u)]
        rw [hψ, hzV_apply, ofAdd_toAdd, hzM_apply, hzE_conj γs]
        simp only [MulEquiv.apply_symm_apply]
        have hsub : (⟨(MulAut.conj z ((π' γs : ↥L) : MulAut W)) u.1,
            hstab ⟨MulAut.conj z ((π' γs : ↥L) : MulAut W), hconj_mem (π' γs)⟩
              u u.2⟩ : ↥E) =
            ⟨((π' γ' : ↥L) : MulAut W) u.1, hstab (π' γ') u u.2⟩ := by
          apply Subtype.ext
          show (MulAut.conj z ((π' γs : ↥L) : MulAut W)) u.1 =
            ((π' γ' : ↥L) : MulAut W) u.1
          rw [← hγ'1]
        rw [hsub]
        rw [hΦγ γ' u, toAdd_ofAdd]
      have hconj : zV * ψ (γs : GL _ K) * zV⁻¹ = ψ (γ' : GL _ K) := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        have hv : v = Multiplicative.toAdd (Φ (Φ.symm (Multiplicative.ofAdd v))) := by
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        rw [hv]
        exact hpoint _
      rw [hconj]
      exact (hψΩ (ψ (γ' : GL _ K))).2 ⟨(γ' : GL _ K), γ'.2, rfl⟩
    refine ⟨zV, hzEmem, ?_, ?_, ?_⟩
    · refine CFSG.LargeExtraspecial.O62.mem_orthogonalGroup_of_normalizes hV0fin
        (qModel_nondegenerate true) ?_
      intro g hg
      exact hzV_norm g hg
    · intro v hv
      rw [mem_fixSpace]
      have huH : ((Φ.symm (Multiplicative.ofAdd v) : ↥E) : W) ∈ H :=
        Subgroup.mem_subgroupOf.mp hv
      have hprop := hzVprop (Φ.symm (Multiplicative.ofAdd v))
      have hzfix : z ((Φ.symm (Multiplicative.ofAdd v)).1) =
          (Φ.symm (Multiplicative.ofAdd v)).1 := hzH _ huH
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hprop
      have heq : Φ (⟨z ((Φ.symm (Multiplicative.ofAdd v)).1), hzEmem _⟩ : ↥E) =
          Φ (Φ.symm (Multiplicative.ofAdd v)) := by
        congr 1
        exact Subtype.ext hzfix
      rw [heq, MulEquiv.apply_symm_apply] at hprop
      exact (Multiplicative.ofAdd.injective hprop).symm
    · intro u
      exact hzVprop u
  obtain ⟨xV, mx, hxVorth, hxVfix, hxVprop⟩ := mkXV x hxL hxE hxH
  obtain ⟨yV, my, hyVorth, hyVfix, hyVprop⟩ := mkXV y hyL hyE hyH
  have hxVcond : Module.finrank (ZMod 2) V₀ - 1 ≤
      Module.finrank (ZMod 2) ↥(fixSpace xV) := by
    have h := Submodule.finrank_mono hxVfix
    rw [hH'fin] at h
    rw [hV0fin]
    omega
  have hyVcond : Module.finrank (ZMod 2) V₀ - 1 ≤
      Module.finrank (ZMod 2) ↥(fixSpace yV) := by
    have h := Submodule.finrank_mono hyVfix
    rw [hH'fin] at h
    rw [hV0fin]
    omega
  rcases CFSG.LargeExtraspecial.eq_one_or_eq_transvection_of_finrank_fixSpace
      (q := qModel true) (qModel_nondegenerate true) hxVorth hxVcond with
    hxV1 | ⟨c, hcq, hcform, hccomm, -⟩
  · left
    intro e he
    have hprop := hxVprop ⟨e, he⟩
    have : Φ ⟨x e, mx ⟨e, he⟩⟩ = Φ (⟨e, he⟩ : ↥E) := by
      rw [hprop, hxV1]
      simp
    exact congrArg Subtype.val (Φ.injective this)
  · rcases CFSG.LargeExtraspecial.eq_one_or_eq_transvection_of_finrank_fixSpace
        (q := qModel true) (qModel_nondegenerate true) hyVorth hyVcond with
      hyV1 | ⟨d, hdq, hdform, hdcomm, -⟩
    · right; left
      intro e he
      have hprop := hyVprop ⟨e, he⟩
      have : Φ ⟨y e, my ⟨e, he⟩⟩ = Φ (⟨e, he⟩ : ↥E) := by
        rw [hprop, hyV1]
        simp
      exact congrArg Subtype.val (Φ.injective this)
    · right; right
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, QuadraticMap.map_zero] at hcq
        exact zero_ne_one hcq
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0, QuadraticMap.map_zero] at hdq
        exact zero_ne_one hdq
      have hxVne : xV ≠ 1 := by
        intro h1
        have hbot : commSpace xV = ⊥ := by rw [h1]; exact s16c167_commSpace_one
        rw [hccomm] at hbot
        have hcbot : c ∈ (⊥ : Submodule (ZMod 2) V₀) := by
          rw [← hbot]
          exact Submodule.mem_span_singleton_self c
        exact hc0 (by simpa using hcbot)
      have hyVne : yV ≠ 1 := by
        intro h1
        have hbot : commSpace yV = ⊥ := by rw [h1]; exact s16c167_commSpace_one
        rw [hdcomm] at hbot
        have hdbot : d ∈ (⊥ : Submodule (ZMod 2) V₀) := by
          rw [← hbot]
          exact Submodule.mem_span_singleton_self d
        exact hd0 (by simpa using hdbot)
      have hxfixfin : Module.finrank (ZMod 2) ↥(fixSpace xV) = 5 := by
        have hle : Module.finrank (ZMod 2) ↥(fixSpace xV) ≤ 6 := by
          have h := Submodule.finrank_le (fixSpace xV)
          rwa [hV0fin] at h
        have hne : Module.finrank (ZMod 2) ↥(fixSpace xV) ≠ 6 := by
          have hlt := Submodule.finrank_lt (s := fixSpace xV) (by
            intro htop
            exact hxVne (CFSG.LargeExtraspecial.OrthoF2.eq_one_of_forall_apply_eq
              fun v => mem_fixSpace.mp (htop ▸ Submodule.mem_top)))
          rw [hV0fin] at hlt
          omega
        have hge : 5 ≤ Module.finrank (ZMod 2) ↥(fixSpace xV) := by
          have h := Submodule.finrank_mono hxVfix
          rw [hH'fin] at h
          exact h
        omega
      have hyfixfin : Module.finrank (ZMod 2) ↥(fixSpace yV) = 5 := by
        have hle : Module.finrank (ZMod 2) ↥(fixSpace yV) ≤ 6 := by
          have h := Submodule.finrank_le (fixSpace yV)
          rwa [hV0fin] at h
        have hne : Module.finrank (ZMod 2) ↥(fixSpace yV) ≠ 6 := by
          have hlt := Submodule.finrank_lt (s := fixSpace yV) (by
            intro htop
            exact hyVne (CFSG.LargeExtraspecial.OrthoF2.eq_one_of_forall_apply_eq
              fun v => mem_fixSpace.mp (htop ▸ Submodule.mem_top)))
          rw [hV0fin] at hlt
          omega
        have hge : 5 ≤ Module.finrank (ZMod 2) ↥(fixSpace yV) := by
          have h := Submodule.finrank_mono hyVfix
          rw [hH'fin] at h
          exact h
        omega
      have hfixEq : fixSpace xV = fixSpace yV := by
        have hxH' : fixSpace xV = H' := (Submodule.eq_of_le_of_finrank_eq hxVfix
          (by rw [hH'fin, hxfixfin])).symm
        have hyH' : fixSpace yV = H' := (Submodule.eq_of_le_of_finrank_eq hyVfix
          (by rw [hH'fin, hyfixfin])).symm
        rw [hxH', hyH']
      have hcommEq : commSpace xV = commSpace yV := by
        rw [CFSG.LargeExtraspecial.commSpace_eq_orthogonal_fixSpace_of_mem
              (Q := qModel true) (qModel_nondegenerate true) hxVorth,
          CFSG.LargeExtraspecial.commSpace_eq_orthogonal_fixSpace_of_mem
              (Q := qModel true) (qModel_nondegenerate true) hyVorth,
          hfixEq]
      have hspanEq : (ZMod 2) ∙ c = (ZMod 2) ∙ d := by
        rw [← hccomm, ← hdcomm, hcommEq]
      have hdc : d ∈ (ZMod 2) ∙ c := by
        rw [hspanEq]
        exact Submodule.mem_span_singleton_self d
      have hcd : c = d := by
        rcases CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mp hdc with h0 | hcd
        · exact absurd h0 hd0
        · exact hcd.symm
      have hxyV : xV = yV := by
        apply LinearEquiv.ext
        intro v
        rw [hcform v, hdform v, hcd]
      intro e he
      have h1p := hxVprop ⟨e, he⟩
      have h2p := hyVprop ⟨e, he⟩
      have hΦeq : Φ ⟨x e, mx ⟨e, he⟩⟩ = Φ ⟨y e, my ⟨e, he⟩⟩ := by
        rw [h1p, h2p, hxyV]
      exact congrArg Subtype.val (Φ.injective hΦeq)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
