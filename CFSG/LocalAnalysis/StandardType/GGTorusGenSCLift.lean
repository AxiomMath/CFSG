module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoTransfer
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace TorusSCLift

private noncomputable def conjPreimage {R : Type*} [Group R] (φ : MulAut R)
    (hφ : φ ∈ Set.range (MulAut.conj : R →* MulAut R)) : R :=
  Classical.choose hφ

private theorem conj_conjPreimage {R : Type*} [Group R] {φ : MulAut R}
    (hφ : φ ∈ Set.range (MulAut.conj : R →* MulAut R)) :
    MulAut.conj (conjPreimage φ hφ) = φ :=
  Classical.choose_spec hφ

theorem exists_rho {p : ℕ} {M : Type} {R : Type} [Group M] [Group R]
    {L' E : Subgroup M} {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hEA : IsElemAbelian p E)
    (h4 : ∀ e : E, ggLAut L' θ ⟨e, hE e.2⟩ ∈ I)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hL : commutator L' = ⊤) :
    ∃ ρ : E →* R,
      (∀ e : E, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩) ∧
      (∀ e : E, ρ e = 1 ↔ (e : M) ∈ Subgroup.centralizer (L' : Set M)) ∧
      (∀ (e : E) (he : (e : M) ∈ L'), ρ e = ggQuotHom θ ⟨(e : M), he⟩) := by
  let φ : E →* MulAut R := (ggLAut L' θ).comp (Subgroup.inclusion hE)
  have hφapply : ∀ e : E, φ e = ggLAut L' θ ⟨e, hE e.2⟩ := fun _ => rfl
  have hφp : ∀ e : E, φ e ^ p = 1 := by
    intro e
    rw [hφapply]
    exact ggLAut_pow_eq_one L' θ (hE e.2) (hEA.2 e e.2)
  have hφrange : ∀ e : E, φ e ∈ Set.range (MulAut.conj : R →* MulAut R) :=
    fun e => hI _ (h4 e) (hφp e)
  let ρ : E →* R :=
    { toFun := fun e => conjPreimage (φ e) (hφrange e)
      map_one' := by
        apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
        conv_rhs => rw [map_one]
        rw [conj_conjPreimage]
        exact map_one φ
      map_mul' := by
        intro e f
        apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
        conv_rhs => rw [map_mul]
        rw [conj_conjPreimage, conj_conjPreimage, conj_conjPreimage]
        exact map_mul φ e f }
  have hρ : ∀ e : E, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩ := fun e =>
    conj_conjPreimage (hφrange e)
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      refine mem_centralizer_of_ggLAut_eq_one L' θ hL (g := ⟨e, hE e.2⟩) ?_
      rw [← hρ e, he, map_one]
    · intro he
      apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
      rw [hρ e, map_one]
      apply DFunLike.ext _ _
      intro r
      obtain ⟨q, rfl⟩ := θ.surjective r
      induction q using QuotientGroup.induction_on with
      | H l =>
        have hl : L'.normalizerMonoidHom ⟨e, hE e.2⟩ l = l := by
          apply Subtype.ext
          rw [normalizerMonoidHom_coe L' ⟨e, hE e.2⟩ l]
          calc (e : M) * l * (e : M)⁻¹ = l * (e : M) * (e : M)⁻¹ := by
                rw [(Subgroup.mem_centralizer_iff.mp he l l.2).symm]
            _ = l := by group
        rw [ggLAut_apply, hl, MulAut.one_apply]
  · intro e he
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [hρ e, ggLAut_of_mem θ ⟨(e : M), he⟩ (hE e.2)]

theorem center_not_dvd {p : ℕ} {M : Type} {R : Type} [Group M] [Finite M] [Group R]
    {L' : Subgroup M} (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hcp : GGCenterPrime p R) (hL : commutator L' = ⊤) :
    ¬ p ∣ Nat.card (Subgroup.center (↥L')) :=
  hcp L' (ggQuotHom θ) (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hL

theorem exists_lambda {p : ℕ} (hp : p.Prime) {M : Type} {R : Type} [Group M] [Finite M]
    [Group R] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hEA : IsElemAbelian p E) (hcp : GGCenterPrime p R) (hL : commutator L' = ⊤)
    (ρ : E →* R) :
    ∃ lam : E →* L',
      (∀ e, ggQuotHom θ (lam e) = ρ e) ∧ (∀ e, (lam e) ^ p = 1) := by
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center (↥L') := (ker_ggQuotHom θ).le
  have hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')) := center_not_dvd θ hcp hL
  choose lam hlamψ hlamp using fun v : E =>
    exists_lift_pow_eq_one hp hψ hker hcpZ (g := ρ v)
      (by rw [← map_pow, show v ^ p = 1 from Subtype.ext (hEA.2 v v.2), map_one])
  have hmul : ∀ v w : E, lam (v * w) = lam v * lam w := by
    intro v w
    have hc : lam v * lam w = lam w * lam v :=
      commute_of_lift_pow_eq_one hp hker hcpZ
        (by rw [hlamψ, hlamψ, ← map_mul, ← map_mul, hEA.1.is_comm.comm v w]) (hlamp w)
    refine eq_of_lift_pow_eq_one hp hker hcpZ ?_ (hlamp _) ?_
    · rw [map_mul, hlamψ, hlamψ, hlamψ, map_mul]
    · rw [(show Commute (lam v) (lam w) from hc).mul_pow, hlamp, hlamp, one_mul]
  exact ⟨MonoidHom.mk' lam hmul, hlamψ, hlamp⟩

private theorem lambda_centralizes {p : ℕ} (hp : p.Prime) {M : Type} {R : Type}
    [Group M] [Finite M] [Group R] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hcp : GGCenterPrime p R) (hL : commutator L' = ⊤) (hEA : IsElemAbelian p E)
    {ρ : E →* R} (hρ : ∀ e, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩)
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e)
    (hlamp : ∀ e, (lam e) ^ p = 1) :
    ∀ e, ((lam e : L') : M) ∈ Subgroup.centralizer (E : Set M) := by
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center (↥L') := (ker_ggQuotHom θ).le
  have hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')) := center_not_dvd θ hcp hL
  intro e
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hmem : x * ((lam e : L') : M) * x⁻¹ ∈ L' :=
    (Subgroup.mem_normalizer_iff.mp (hE hx) ((lam e : L') : M)).mp (lam e).2
  let y : L' := ⟨x * ((lam e : L') : M) * x⁻¹, hmem⟩
  have hyψ : ggQuotHom θ y = ggQuotHom θ (lam e) := by
    have hconj := L45KG.ggQuotHom_conj (K := L') (θ := θ) (g := x) (hE hx) (lam e).2 hmem
    rw [hconj]
    rw [hlamψ]
    rw [show (ggLAut L' θ) ⟨x, hE hx⟩ = MulAut.conj (ρ ⟨x, hx⟩) from
      (hρ ⟨x, hx⟩).symm]
    rw [MulAut.conj_apply]
    have hcomm : ρ ⟨x, hx⟩ * ρ e = ρ e * ρ ⟨x, hx⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact hEA.1.is_comm.comm ⟨x, hx⟩ e
    rw [hcomm]
    group
  have hyp : y ^ p = 1 := by
    apply Subtype.ext
    change (x * ((lam e : L') : M) * x⁻¹) ^ p = 1
    have hp1 : ((lam e : L') : M) ^ p = 1 := by
      simpa using congrArg Subtype.val (hlamp e)
    rw [conj_pow, hp1]
    group
  have hy_eq : y = lam e := eq_of_lift_pow_eq_one hp hker hcpZ hyψ hyp (hlamp e)
  have hval : x * ((lam e : L') : M) * x⁻¹ = ((lam e : L') : M) := congrArg Subtype.val hy_eq
  calc x * ((lam e : L') : M) = (x * ((lam e : L') : M) * x⁻¹) * x := by group
    _ = ((lam e : L') : M) * x := by rw [hval]

theorem lambda_mem {p : ℕ} (hp : p.Prime) {M : Type} {R : Type}
    [Group M] [Finite M] [Group R] {L' E : Subgroup M} {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) (hcp : GGCenterPrime p R) {ρ : E →* R}
    (hρ : ∀ e, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩)
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e)
    (hlamp : ∀ e, (lam e) ^ p = 1) :
    ∀ e, ((lam e : L') : M) ∈ E := by
  obtain ⟨hL, hEA, -, -, -, h6, -⟩ := hpos
  intro e
  exact h6 _ (Subgroup.mem_sup_right (lam e).2)
    (lambda_centralizes hp hcp hL hEA hρ hlamψ hlamp e)
    (by simpa using congrArg Subtype.val (hlamp e))

theorem eq_lambda_of_lift {p : ℕ} (hp : p.Prime) {M : Type} {R : Type}
    [Group M] [Finite M] [Group R] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hcp : GGCenterPrime p R) (hL : commutator L' = ⊤) {ρ : E →* R}
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e)
    (hlamp : ∀ e, (lam e) ^ p = 1) (e : E) {n : L'}
    (hnψ : ggQuotHom θ n = ρ e) (hnp : n ^ p = 1) : n = lam e :=
  eq_of_lift_pow_eq_one hp (ker_ggQuotHom θ).le (center_not_dvd θ hcp hL)
    (by rw [hnψ, hlamψ]) hnp (hlamp e)

theorem card_range_rho {p r : ℕ} (hp : p.Prime) {M : Type} {R : Type} [Group M]
    [Finite M] [Group R] {L' E E₁ : Subgroup M} {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) (hr : p ^ (r + 1) ≤ Nat.card E)
    (hne : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥)
    (hE₁ : E₁ ≤ E) (hE₁C : E₁ ⊓ Subgroup.centralizer (L' : Set M) = ⊥)
    (hcard : Nat.card E = p * Nat.card E₁) {ρ : E →* R}
    (hρker : ∀ e : E, ρ e = 1 ↔ (e : M) ∈ Subgroup.centralizer (L' : Set M)) :
    Nat.card ρ.range = Nat.card E₁ ∧ p ^ r ≤ Nat.card ρ.range ∧
      (E₁.subgroupOf E).map ρ = ρ.range := by
  obtain ⟨hdec, -⟩ := exists_mul_of_complement_position hp hpos hne hE₁ hE₁C hcard
  have hmap : (E₁.subgroupOf E).map ρ = ρ.range := by
    apply le_antisymm
    · intro r hr
      obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hr
      exact ⟨e, rfl⟩
    · intro r hr
      obtain ⟨e, rfl⟩ := hr
      obtain ⟨e₁, he₁, z, hz, hxz⟩ := hdec e e.2
      have hz1 : ρ ⟨z, hz.1⟩ = 1 := (hρker ⟨z, hz.1⟩).mpr hz.2
      refine ⟨⟨e₁, hE₁ he₁⟩, he₁, ?_⟩
      have heq : e = ⟨e₁, hE₁ he₁⟩ * ⟨z, hz.1⟩ := Subtype.ext hxz
      rw [heq, map_mul, hz1, mul_one]
  have hinj : Function.Injective fun e : E₁.subgroupOf E => ρ e := by
    intro a b hab
    have h1 : ρ (a⁻¹ * b) = 1 := by
      change ρ ((a : E)⁻¹ * (b : E)) = 1
      rw [map_mul, map_inv, show ρ (a : E) = ρ (b : E) from hab, inv_mul_cancel]
    have h2 : ((a⁻¹ * b : E₁.subgroupOf E) : E) = 1 := by
      have h3 := (hρker (a⁻¹ * b)).mp h1
      have h4 : ((a⁻¹ * b : E₁.subgroupOf E) : M) ∈ E₁ := (a⁻¹ * b).2
      have h5 : ((a⁻¹ * b : E₁.subgroupOf E) : M) ∈ E₁ ⊓
          Subgroup.centralizer (L' : Set M) := ⟨h4, h3⟩
      rw [hE₁C] at h5
      exact Subtype.ext (Subgroup.mem_bot.mp h5)
    exact inv_mul_eq_one.mp (Subtype.ext h2)
  let φ : (E₁.subgroupOf E) →* R := ρ.comp (E₁.subgroupOf E).subtype
  have hφinj : Function.Injective φ := hinj
  have hφrange : φ.range = ρ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hbij : Function.Bijective φ.rangeRestrict :=
    ⟨fun a b h => hφinj (by simpa [MonoidHom.coe_rangeRestrict] using congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective φ⟩
  have hcardmap : Nat.card ρ.range = Nat.card (E₁.subgroupOf E) := by
    rw [← hφrange]
    exact (Nat.card_congr (Equiv.ofBijective φ.rangeRestrict hbij)).symm
  have hcardsub : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁).toEquiv
  have hbig : p ^ (r + 1) ≤ p * Nat.card E₁ := by
    rwa [← hcard]
  have hbig' : p * p ^ r ≤ p * Nat.card E₁ := by
    rwa [pow_succ, mul_comm] at hbig
  have hpr : p ^ r ≤ Nat.card E₁ := Nat.le_of_mul_le_mul_left hbig' hp.pos
  exact ⟨hcardmap.trans hcardsub, hpr.trans_eq (hcardmap.trans hcardsub).symm, hmap⟩

theorem image_self_centralizing {p : ℕ} (hp : p.Prime) {M : Type} {R : Type}
    [Group M] [Finite M] [Group R] {L' E : Subgroup M} {I : Set (MulAut R)}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) (hcp : GGCenterPrime p R) {ρ : E →* R}
    (hρ : ∀ e : E, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩)
    (hρψ : ∀ (e : E) (he : (e : M) ∈ L'), ρ e = ggQuotHom θ ⟨(e : M), he⟩) :
    ∀ g : R, (∀ e ∈ ρ.range, g * e = e * g) → g ^ p = 1 → g ∈ ρ.range := by
  obtain ⟨hL, -, -, -, -, h6, -⟩ := hpos
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center (↥L') := (ker_ggQuotHom θ).le
  have hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')) := center_not_dvd θ hcp hL
  intro g hg hgp
  obtain ⟨n, hnψ, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpZ hgp
  have hnC : (n : M) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hmem : x * ((n : L') : M) * x⁻¹ ∈ L' :=
      (Subgroup.mem_normalizer_iff.mp (hE hx) ((n : L') : M)).mp n.2
    let y : L' := ⟨x * ((n : L') : M) * x⁻¹, hmem⟩
    have hyψ : ggQuotHom θ y = ggQuotHom θ n := by
      have hconj := L45KG.ggQuotHom_conj (K := L') (θ := θ) (g := x) (hE hx) n.2 hmem
      rw [hconj, hnψ]
      rw [show (ggLAut L' θ) ⟨x, hE hx⟩ = MulAut.conj (ρ ⟨x, hx⟩) from (hρ ⟨x, hx⟩).symm]
      rw [MulAut.conj_apply]
      have hcomm : g * ρ ⟨x, hx⟩ = ρ ⟨x, hx⟩ * g :=
        hg (ρ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
      rw [← hcomm]
      group
    have hyp : y ^ p = 1 := by
      apply Subtype.ext
      change (x * ((n : L') : M) * x⁻¹) ^ p = 1
      have hp1 : ((n : L') : M) ^ p = 1 := by
        simpa using congrArg Subtype.val hnp
      rw [conj_pow, hp1]
      group
    have hy_eq : y = n := eq_of_lift_pow_eq_one hp hker hcpZ hyψ hyp hnp
    have hval : x * ((n : L') : M) * x⁻¹ = ((n : L') : M) := congrArg Subtype.val hy_eq
    calc x * ((n : L') : M) = (x * ((n : L') : M) * x⁻¹) * x := by group
      _ = ((n : L') : M) * x := by rw [hval]
  have hnE : (n : M) ∈ E :=
    h6 _ (Subgroup.mem_sup_right n.2) hnC (by simpa using congrArg Subtype.val hnp)
  refine ⟨⟨(n : M), hnE⟩, ?_⟩
  rw [hρψ ⟨(n : M), hnE⟩ n.2]
  exact hnψ

theorem component_image {p : ℕ} {M : Type} {R : Type}
    [Group M] [Finite M] [Group R] {L' E E₁ D' J' : Subgroup M} {d : M}
    {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) (hdE : d ∈ E)
    (hdec : ∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = e₁ * z)
    (hD'E : D' ≤ E) (hCD' : E ⊓ Subgroup.centralizer (L' : Set M) ≤ D')
    (hD'E₁ : D' ⊓ E₁ = Subgroup.zpowers d)
    (hJ : IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M)))
    {ρ : E →* R} (hρ : ∀ e : E, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩) :
    IsComponentOf ((J'.subgroupOf L').map (ggQuotHom θ))
      (Subgroup.centralizer ({ρ ⟨d, hdE⟩} : Set R)) := by
  obtain ⟨hL, -, -, -, -, -, -⟩ := hpos
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center (↥L') := (ker_ggQuotHom θ).le
  have hcomp : IsComponentOf (J'.subgroupOf L')
      (ggFix (L'.normalizerMonoidHom ⟨d, hE hdE⟩)) :=
    isComponentOf_subgroupOf_ggFix_of_decomp hE hdE hdec hD'E hCD' hD'E₁ hJ
  have hαβ : ∀ x : L', ggQuotHom θ (L'.normalizerMonoidHom ⟨d, hE hdE⟩ x) =
      MulAut.conj (ρ ⟨d, hdE⟩) (ggQuotHom θ x) := by
    intro x
    have hmem : d * (x : M) * d⁻¹ ∈ L' :=
      (Subgroup.mem_normalizer_iff.mp (hE hdE) (x : M)).mp x.2
    have hx' : L'.normalizerMonoidHom ⟨d, hE hdE⟩ x = ⟨d * (x : M) * d⁻¹, hmem⟩ :=
      Subtype.ext (normalizerMonoidHom_coe L' ⟨d, hE hdE⟩ x)
    rw [hx', L45KG.ggQuotHom_conj (K := L') (θ := θ) (g := d) (hE hdE) x.2 hmem]
    rw [show (ggLAut L' θ) ⟨d, hE hdE⟩ = MulAut.conj (ρ ⟨d, hdE⟩) from (hρ ⟨d, hdE⟩).symm]
  have hJbar := LayerCC.isComponentOf_map_ggFix hψ hker hαβ hcomp
  rwa [OPlusEight.ggFix_conj] at hJbar

theorem decomp_inf_centralizer {M : Type} {R : Type}
    [Group M] [Group R] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R}
    {ρ : E →* R}
    (hρker : ∀ e : E, ρ e = 1 ↔ (e : M) ∈ Subgroup.centralizer (L' : Set M))
    (hρψ : ∀ (e : E) (he : (e : M) ∈ L'), ρ e = ggQuotHom θ ⟨(e : M), he⟩)
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e)
    (hlamE : ∀ e, ((lam e : L') : M) ∈ E) :
    ∀ x ∈ E, ∃ a ∈ E ⊓ L', ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = a * z := by
  intro x hx
  let ex : E := ⟨x, hx⟩
  have hmem : ((lam ex : L') : M)⁻¹ * x ∈ E :=
    E.mul_mem (E.inv_mem (hlamE ex)) hx
  refine ⟨((lam ex : L') : M), ⟨hlamE ex, (lam ex).2⟩,
    ((lam ex : L') : M)⁻¹ * x, ⟨hmem, ?_⟩, by group⟩
  apply (hρker ⟨((lam ex : L') : M)⁻¹ * x, hmem⟩).mp
  change ρ (⟨((lam ex : L') : M), hlamE ex⟩⁻¹ * ex) = 1
  rw [map_mul, map_inv]
  have h1 : ρ ⟨((lam ex : L') : M), hlamE ex⟩ = ρ ex := by
    rw [hρψ ⟨((lam ex : L') : M), hlamE ex⟩ (lam ex).2, hlamψ ex]
  rw [h1]
  exact inv_mul_cancel (ρ ex)

theorem eq_one_of_mem_center_of_pow {p : ℕ} (hp : p.Prime) {M : Type} [Group M]
    {L' : Subgroup M}
    (hcpZ : ¬ p ∣ Nat.card (Subgroup.center (↥L')))
    {z : ↥L'} (hz : z ∈ Subgroup.center (↥L')) (hpow : ∃ k : ℕ, z ^ p ^ k = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hpow
  have : Finite (Subgroup.center (↥L')) := by
    by_contra h
    have : Infinite (Subgroup.center (↥L')) := not_finite_iff_infinite.mp h
    exact hcpZ (by rw [Nat.card_eq_zero_of_infinite]; exact dvd_zero p)
  have hdvd1 : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hdvd2 : orderOf z ∣ Nat.card (Subgroup.center (↥L')) := by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center (↥L'))
    rwa [Subgroup.orderOf_mk] at h1
  have hpa : ¬ p ∣ orderOf z := fun h => hcpZ (h.trans hdvd2)
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow hp).mp hdvd1
  cases t with
  | zero => exact orderOf_eq_one_iff.mp (by rw [ht, pow_zero])
  | succ t =>
      exfalso
      apply hpa
      rw [ht]
      exact dvd_pow_self p (Nat.succ_ne_zero t)

end TorusSCLift

end CFSG.StandardType
