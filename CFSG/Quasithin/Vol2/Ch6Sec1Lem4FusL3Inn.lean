module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3C2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Mx
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section LocFusL3Inn

private theorem ker_conj_eq_center614Inn (Q : Type) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h z
    have hz := congrArg (fun σ : MulAut Q => σ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc z * g = g * z * g⁻¹ * g := by rw [hz]
      _ = g * z := by group
  · intro h
    ext z
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h z, mul_inv_cancel_right]

private theorem card_conj_range614Inn (Q : Type) [Group Q] :
    Nat.card (MulAut.conj : Q →* MulAut Q).range = Nat.card (Q ⧸ Subgroup.center Q) := by
  rw [← ker_conj_eq_center614Inn Q]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : Q →* MulAut Q)).toEquiv).symm

private theorem finite_mulAut614Inn (Q : Type) [Group Q] [Finite Q] : Finite (MulAut Q) :=
  Finite.of_injective (fun σ : MulAut Q => (σ : Q → Q)) fun _ _ h => MulEquiv.ext (congrFun h)

private theorem conj_range_normal614Inn (Q : Type) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).range.Normal := by
  constructor
  rintro _ ⟨q, rfl⟩ g
  refine ⟨g q, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv]

private theorem exists_surj_ker614Inn {Q : Type} [Group Q] {F : Type} [Field F]
    (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F))
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj S) :
    ∃ φ : ↥S →* Q ⧸ Subgroup.center Q, Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S := by
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf S)),
    ?_, ?_⟩
  · intro y
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 3) F).subgroupOf S) (e y)
    refine ⟨s, ?_⟩
    show e.symm (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf S) s) = y
    rw [hs, MulEquiv.symm_apply_apply]
  · intro s hs
    have h2 : e.symm (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf S) s) = 1 :=
      MonoidHom.mem_ker.mp hs
    have h1 : QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf S) s = 1 :=
      e.symm.map_eq_one_iff.mp h2
    have h3 : s ∈ (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf S) :
        ↥S →* StatedProj S).ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h3

private theorem locFusL3_inn_bridge614 {Q : Type} [Group Q] [Finite Q]
    (hq : CFSG.IsQuasisimple Q) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {F : Type} [Field F]
    (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F))
    (φ : ↥S →* Q ⧸ Subgroup.center Q) (hφsurj : Function.Surjective φ)
    (hφK : φ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S)
    (hfacts : ∀ ψ : ↥S →* MulAut Q, ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S →
      ψ.range.Normal → (∀ v : MulAut Q, (∀ n ∈ ψ.range, v * n = n * v) → v = 1) →
      L3FusFacts ψ.range p) :
    LocFusL3 (MulAut Q) (MulAut.conj : Q →* MulAut Q).range := by
  haveI : Finite (MulAut Q) := finite_mulAut614Inn Q
  have hZ : Subgroup.center Q ≤ (MulAut.conj : Q →* MulAut Q).ker := by
    rw [ker_conj_eq_center614Inn Q]
  let innEmb : Q ⧸ Subgroup.center Q →* MulAut Q :=
    QuotientGroup.lift (Subgroup.center Q) (MulAut.conj : Q →* MulAut Q) hZ
  have hinnEmb : ∀ q : Q, innEmb (q : Q ⧸ Subgroup.center Q) = MulAut.conj q :=
    fun q => rfl
  have hinj : Function.Injective innEmb := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hinnEmb] at hx
    rw [QuotientGroup.eq_one_iff]
    have hq' : q ∈ (MulAut.conj : Q →* MulAut Q).ker := MonoidHom.mem_ker.mpr hx
    rwa [ker_conj_eq_center614Inn Q] at hq'
  let ψ : ↥S →* MulAut Q := innEmb.comp φ
  have hψK : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S := by
    intro s hs
    apply hφK
    rw [MonoidHom.mem_ker]
    apply hinj
    rw [map_one]
    exact MonoidHom.mem_ker.mp hs
  have hrange : ψ.range = (MulAut.conj : Q →* MulAut Q).range := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨q, hq'⟩ := QuotientGroup.mk_surjective (φ s)
      refine ⟨q, ?_⟩
      show MulAut.conj q = innEmb (φ s)
      rw [← hq', hinnEmb]
    · rintro ⟨q, rfl⟩
      obtain ⟨s, hs⟩ := hφsurj (q : Q ⧸ Subgroup.center Q)
      refine ⟨s, ?_⟩
      show innEmb (φ s) = MulAut.conj q
      rw [hs, hinnEmb]
  have hconjN : (MulAut.conj : Q →* MulAut Q).range.Normal := conj_range_normal614Inn Q
  have hN : ψ.range.Normal := by
    rw [hrange]
    exact hconjN
  have hC : ∀ v : MulAut Q, (∀ n ∈ ψ.range, v * n = n * v) → v = 1 := by
    intro v hv
    have hmem : ∀ y : Q, MulAut.conj y ∈ ψ.range := fun y => by
      rw [hrange]
      exact ⟨y, rfl⟩
    have key : ∀ y x : Q, v y * v x * (v y)⁻¹ = y * v x * y⁻¹ := by
      intro y x
      have h := congrArg (fun σ : MulAut Q => σ x) (hv (MulAut.conj y) (hmem y))
      simpa [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] using h
    have hcen : ∀ y : Q, (v y)⁻¹ * y ∈ Subgroup.center Q := by
      intro y
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := MulEquiv.surjective v g
      calc v x * ((v y)⁻¹ * y) = (v y)⁻¹ * (v y * v x * (v y)⁻¹) * y := by group
        _ = (v y)⁻¹ * (y * v x * y⁻¹) * y := by rw [key y x]
        _ = (v y)⁻¹ * y * v x := by group
    have hσ : quotCenterAut614 Q v = 1 := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [quotCenterAut614_mk, MulAut.one_apply, QuotientGroup.eq]
        exact hcen y
    exact eq_one_of_quotCenterAut614_eq_one (Group.isPerfect_def.mp hq.1) hσ
  have hfact := hfacts ψ hψK hN hC
  rw [hrange] at hfact
  exact locFusL3_of_facts hconjN hp hp5 hfact

private theorem not_five_dvd_quot_center614Inn {Q : Type} [Group Q] (δ : Bool)
    (hL : IsPSLEps3 δ 3 1 (Q ⧸ Subgroup.center Q)) :
    ¬ 5 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  cases δ with
  | true =>
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 3) (by norm_num), hK]
    decide
  | false =>
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
        (by norm_num : 2 ≤ 3)]
    decide

end LocFusL3Inn

theorem locFusL3_inn {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (h : ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 δ p 1 (Q ⧸ Subgroup.center Q)) :
    LocFusL3 (MulAut Q) (MulAut.conj : Q →* MulAut Q).range := by
  obtain ⟨δ, p, hp, hp2, hL⟩ := h
  by_cases h3 : p = 3
  ·
    subst h3
    intro T X _ _ hXN _ hX5
    exfalso
    have h1 : (X ⊓ T).relIndex X ∣ Nat.card X := Subgroup.relIndex_dvd_card (X ⊓ T) X
    rw [hX5] at h1
    have h5 : 5 ∣ Nat.card (MulAut.conj : Q →* MulAut Q).range :=
      h1.trans (Subgroup.card_dvd_of_le hXN)
    rw [card_conj_range614Inn] at h5
    exact not_five_dvd_quot_center614Inn δ hL h5
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have hlt' : p < 5 := not_le.mp hlt
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    cases δ with
    | true =>
      obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hL
      obtain ⟨φ, hφsurj, hφK⟩ := exists_surj_ker614Inn (StatedSL 3 F) e
      exact locFusL3_inn_bridge614 hq hp hp5 (StatedSL 3 F) φ hφsurj hφK
        (fun ψ h1 h2 h3 => l3FusFacts_of_statedSL (F := F) hp hp5 (by rw [hF, pow_one]) ψ h1 h2 h3)
    | false =>
      obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := hL
      obtain ⟨φ, hφsurj, hφK⟩ := exists_surj_ker614Inn (StatedSU 3 (p ^ 1) F) e
      exact locFusL3_inn_bridge614 hq hp hp5 (StatedSU 3 (p ^ 1) F) φ hφsurj hφK
        (fun ψ h1 h2 h3 => l3FusFacts_of_statedSU (F := F) hp hp5 hF ψ h1 h2 h3)

end CFSG.Quasithin.H13
