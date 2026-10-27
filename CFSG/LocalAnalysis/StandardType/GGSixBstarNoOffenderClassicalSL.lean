module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSum
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSp
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelMono

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace NoOffenderClassical

namespace SL

section Aut

variable {F : Type} [Field F] {G : Type} [Group G] {m : ℕ}

theorem exists_semilinear [Finite F] [CharP F 2] (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1) :
    ∃ (A : GL (Fin (m + 1)) F) (σ : F ≃+* F), ∀ u,
      y * ψ u * y⁻¹ = ψ (InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom u)) := by
  set N := Subgroup.normalizer (ψ.range : Set G)
  set φN := ψ.range.normalizerMonoidHom
  set Θ := AutPSL.projEquiv (m := m) (K := F) hker hC
  set χ : N →* MulAut (projectiveSL (m + 1) F) := (MulAut.congr Θ).symm.toMonoidHom.comp φN
  set α := χ ⟨y, hy⟩ with hαdef
  have hαp : α ^ p = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨y, hy⟩ : N) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := m + 1) (by omega)).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero (n := m + 1) (by omega)
    (hp.odd_of_ne_two hp2) hε (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  refine ⟨A, σ, fun u => ?_⟩
  have h2 : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F A
      (SpecialLinearGroup.map σ.toRingHom u) =
      InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom u) :=
    Subtype.ext (by rw [coe_slConjugation, InnerDiagA.coe_conjSL])
  have key : Θ.symm (φN ⟨y, hy⟩ (Θ (proj (m + 1) F u))) =
      proj (m + 1) F (InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom u)) := by
    rw [← h2, ← conjAut_proj, ← fieldAut_proj, ← MulAut.mul_apply, ← hαeq]
    rfl
  rw [MulEquiv.symm_apply_eq] at key
  exact congrArg Subtype.val key

end Aut

section Coord

variable {F : Type} [Field F] {G : Type} [Group G] {m : ℕ}

theorem entry_of_diagGL_eq {t t' : Fin (m + 1) → Fˣ} {c : Fˣ}
    (h : InnerDiagA.diagGL t' = GeneralLinearGroup.scalar (Fin (m + 1)) c * InnerDiagA.diagGL t)
    (i : Fin (m + 1)) : t' i = c * t i := by
  rw [LinModel.scalar_mul_diagGL] at h
  have h1 := congrArg (fun A : GL (Fin (m + 1)) F =>
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) h
  simp only [InnerDiagA.coe_diagGL, diagonal_apply_eq] at h1
  exact Units.ext (by rw [Units.val_mul]; exact h1)

theorem eq_one_of_pow {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ m + 1) {c : Fˣ} (hcp : c ^ p = 1)
    (hcn : c ^ (m + 1) = 1) : c = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨hcp, hcn⟩
  rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn), pow_one] at h

theorem eq_of_normalized [CharP F 2] {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ m + 1)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    {t t' : Fin (m + 1) → Fˣ} (ht : ∀ i, t i ^ p = 1) (htp : ∏ i, t i = 1)
    (hbt : (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ) (ht' : ∀ i, t' i ^ p = 1)
    (htp' : ∏ i, t' i = 1) (hbt' : (b, InnerDiagA.diagGL t') ∈ LinFusion.ggInducedPairs ψ) :
    t' = t := by
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hbt hbt'
  have hentry := entry_of_diagGL_eq hc
  have hcp : c ^ p = 1 := by
    have h1 := ht' 0
    rwa [hentry 0, mul_pow, ht 0, mul_one] at h1
  have hcn : c ^ (m + 1) = 1 := by
    have h1 := htp'
    rwa [Finset.prod_congr rfl (fun i _ => hentry i), Finset.prod_mul_distrib, htp, mul_one,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  funext i
  rw [hentry i, eq_one_of_pow hp hpn hcp hcn, one_mul]

@[expose] noncomputable def torusCoord (p : ℕ) (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (b : G) : Fin (m + 1) → Fˣ :=
  open Classical in
  if h : ∃ t : Fin (m + 1) → Fˣ, (∀ i, t i ^ p = 1) ∧ ∏ i, t i = 1 ∧
      (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ then Classical.choose h else 1

theorem torusCoord_eq [CharP F 2] {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ m + 1)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    {t : Fin (m + 1) → Fˣ} (ht : ∀ i, t i ^ p = 1) (htp : ∏ i, t i = 1)
    (hbt : (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ) : torusCoord p ψ b = t := by
  have h : ∃ t : Fin (m + 1) → Fˣ, (∀ i, t i ^ p = 1) ∧ ∏ i, t i = 1 ∧
      (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ := ⟨t, ht, htp, hbt⟩
  rw [torusCoord, dite_eq_left h]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  exact eq_of_normalized hp hpn hker ht htp hbt h1 h2 h3

theorem exists_normalized {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ m + 1)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {b : G} {d : Fin (m + 1) → Fˣ}
    (hd : ∀ i, d i ^ p = 1) (hbd : (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ t : Fin (m + 1) → Fˣ, (∀ i, t i ^ p = 1) ∧ ∏ i, t i = 1 ∧
      (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ := by
  set π₀ : Fˣ := ∏ i, d i with hπ₀
  have hπp : π₀ ^ p = 1 := by
    rw [hπ₀, ← Finset.prod_pow, Finset.prod_eq_one fun i _ => hd i]
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm hp.one_lt
  set ν : Fˣ := π₀⁻¹ ^ k with hν
  have hνp : ν ^ p = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, inv_pow, hπp, inv_one, one_pow]
  have hνn : ν ^ (m + 1) = π₀⁻¹ := by
    have hmod : (m + 1) * k = p * ((m + 1) * k / p) + 1 := by
      have := Nat.div_add_mod ((m + 1) * k) p
      rw [hk] at this
      omega
    rw [hν, ← pow_mul, mul_comm k, hmod, pow_add, pow_mul, inv_pow, hπp, inv_one, one_pow,
      one_mul, pow_one]
  refine ⟨fun i => ν * d i, fun i => by rw [mul_pow, hνp, hd i, one_mul], ?_, ?_⟩
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hνn,
      ← hπ₀, inv_mul_cancel]
  · have h1 := LinModel.scalar_mul_mem_ggInducedPairs hbd ν
    rwa [LinModel.scalar_mul_diagGL] at h1

theorem coordsOne [CharP F 2] {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ m + 1)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hnorm : ∀ b ∈ Bs, ∃ t : Fin (m + 1) → Fˣ, (∀ i, t i ^ p = 1) ∧ ∏ i, t i = 1 ∧
      (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ)
    (hreal : ∀ (t : Fin (m + 1) → Fˣ) (ht : ∏ i, t i = 1), (∀ i, t i ^ p = 1) →
      ψ (LinModel.diagSL t ht) ∈ Bs) :
    CoordsOne p Bs (torusCoord p ψ) where
  mul a ha b hb := by
    obtain ⟨s, hs, hsp, has⟩ := hnorm a ha
    obtain ⟨t, ht, htp, hbt⟩ := hnorm b hb
    have hab := (LinFusion.ggInducedPairs ψ).mul_mem has hbt
    rw [Prod.mk_mul_mk, ← LinFusion.diagGL_mul] at hab
    rw [torusCoord_eq hp hpn hker hs hsp has, torusCoord_eq hp hpn hker ht htp hbt,
      torusCoord_eq hp hpn hker (fun i => by rw [Pi.mul_apply, mul_pow, hs, ht, one_mul])
        (by rw [Finset.prod_congr rfl fun i _ => Pi.mul_apply s t i, Finset.prod_mul_distrib,
          hsp, htp, one_mul]) hab]
  inj a ha b hb hab := by
    obtain ⟨s, hs, hsp, has⟩ := hnorm a ha
    obtain ⟨t, ht, htp, hbt⟩ := hnorm b hb
    rw [torusCoord_eq hp hpn hker hs hsp has, torusCoord_eq hp hpn hker ht htp hbt] at hab
    subst hab
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem has ((LinFusion.ggInducedPairs ψ).inv_mem hbt)
    rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h1
    have h2 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h1
    rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  prod b hb := by
    obtain ⟨t, ht, htp, hbt⟩ := hnorm b hb
    rw [torusCoord_eq hp hpn hker ht htp hbt]
    exact htp
  surj t ht htp := ⟨_, hreal t htp ht,
    torusCoord_eq hp hpn hker ht htp (LinModel.exists_mem_of_prod_eq_one ψ t htp)⟩

end Coord

section Transport

variable {F : Type} [Field F] {G : Type} [Group G] {m : ℕ}

theorem map_conjSL (σ : F ≃+* F) (A : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    SpecialLinearGroup.map σ.toRingHom (InnerDiagA.conjSL A u) =
      InnerDiagA.conjSL (GeneralLinearGroup.map (σ : F →+* F) A)
        (SpecialLinearGroup.map σ.toRingHom u) := by
  apply Subtype.ext
  change ((InnerDiagA.conjSL A u : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ = _
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_conjSL, Matrix.map_mul, Matrix.map_mul, ← map_inv]
  rfl

theorem map_map_symm (σ : F ≃+* F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map σ.symm.toRingHom u) = u := by
  apply Subtype.ext
  ext i j
  change σ (σ.symm _) = _
  rw [RingEquiv.apply_symm_apply]

theorem map_diagGL (σ : F ≃+* F) (d : Fin (m + 1) → Fˣ) :
    GeneralLinearGroup.map (σ : F →+* F) (InnerDiagA.diagGL d) =
      InnerDiagA.diagGL (fun k => Units.map (σ : F →* F) (d k)) := by
  apply Units.ext
  change ((InnerDiagA.diagGL d : GL (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ = _
  rw [InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL, diagonal_map (map_zero σ)]
  rfl

theorem conj_mem_ggInducedPairs {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {e b : G}
    {A D : GL (Fin (m + 1)) F} {σ : F ≃+* F}
    (hAσ : ∀ u, e * ψ u * e⁻¹ = ψ (InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom u)))
    (hD : (b, D) ∈ LinFusion.ggInducedPairs ψ) :
    (e * b * e⁻¹, A * GeneralLinearGroup.map (σ : F →+* F) D * A⁻¹) ∈
      LinFusion.ggInducedPairs ψ := by
  intro u
  set v := SpecialLinearGroup.map σ.symm.toRingHom (InnerDiagA.conjSL A⁻¹ u) with hv
  have hu : InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom v) = u := by
    rw [hv, map_map_symm, ← LinFusion.conjSL_mul, mul_inv_cancel, LinFusion.conjSL_one]
  have h1 : e⁻¹ * ψ u * e = ψ v := by
    have h2 := hAσ v
    rw [hu] at h2
    rw [← h2]
    group
  change e * b * e⁻¹ * ψ u * (e * b * e⁻¹)⁻¹ = _
  calc e * b * e⁻¹ * ψ u * (e * b * e⁻¹)⁻¹ = e * (b * (e⁻¹ * ψ u * e) * b⁻¹) * e⁻¹ := by group
    _ = e * ψ (InnerDiagA.conjSL D v) * e⁻¹ := by rw [h1, LinFusion.mem_ggInducedPairs.mp hD v]
    _ = ψ (InnerDiagA.conjSL A (SpecialLinearGroup.map σ.toRingHom (InnerDiagA.conjSL D v))) :=
        hAσ _
    _ = ψ (InnerDiagA.conjSL (A * GeneralLinearGroup.map (σ : F →+* F) D * A⁻¹) u) := by
        rw [map_conjSL, ← hu, ← LinFusion.conjSL_mul, ← LinFusion.conjSL_mul,
          inv_mul_cancel_right]

theorem exists_supp_perm [Finite F] [CharP F 2] (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : ¬ p ∣ m + 1) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hnorm : ∀ b ∈ Bs, ∃ t : Fin (m + 1) → Fˣ, (∀ i, t i ^ p = 1) ∧ ∏ i, t i = 1 ∧
      (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ)
    (hκ : CoordsOne p Bs (torusCoord p ψ)) {e : G}
    (heM : e ∈ Subgroup.normalizer (ψ.range : Set G))
    (heB : e ∈ Subgroup.normalizer (Bs : Set G)) (hep : e ^ p = 1) :
    ∃ τ : Equiv.Perm (Fin (m + 1)), ∀ b ∈ Bs, ∀ i,
      torusCoord p ψ (e * b * e⁻¹) (τ i) = 1 ↔ torusCoord p ψ b i = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, σ, hAσ⟩ := exists_semilinear hm hp hp2 hker hC heM hep
  set κ := torusCoord p ψ with hκdef
  have hconj : ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp heB b).mp hb
  set σu : Fˣ →* Fˣ := Units.map (σ : F →* F) with hσu
  have hσu1 : ∀ x : Fˣ, σu x = 1 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply Units.ext
      have h1 := congrArg Units.val h
      rw [hσu, Units.coe_map, Units.val_one] at h1
      rw [Units.val_one]
      exact σ.injective (h1.trans (map_one σ).symm)
    · rintro rfl
      exact map_one σu
  have hcoord : ∀ b ∈ Bs, (∀ i, κ b i ^ p = 1) ∧
      (b, InnerDiagA.diagGL (κ b)) ∈ LinFusion.ggInducedPairs ψ := fun b hb => by
    obtain ⟨t, ht, htp, hbt⟩ := hnorm b hb
    rw [hκdef, torusCoord_eq hp hpn hker ht htp hbt]
    exact ⟨ht, hbt⟩
  have hmat : ∀ b ∈ Bs, ∃ c : Fˣ, A * InnerDiagA.diagGL (fun k => σu (κ b k)) =
      InnerDiagA.diagGL (fun k => c * κ (e * b * e⁻¹) k) * A := by
    intro b hb
    have h1 := conj_mem_ggInducedPairs hAσ (hcoord b hb).2
    obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker h1
      (hcoord _ (hconj b hb)).2
    refine ⟨c⁻¹, ?_⟩
    rw [← LinModel.scalar_mul_diagGL, hc, map_diagGL, ← hσu]
    have hz : GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ *
        GeneralLinearGroup.scalar (Fin (m + 1)) c = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc A * InnerDiagA.diagGL (fun k => σu (κ b k)) =
        (GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * GeneralLinearGroup.scalar (Fin (m + 1)) c) *
          (A * InnerDiagA.diagGL (fun k => σu (κ b k)) * A⁻¹) * A := by rw [hz]; group
      _ = _ := by group
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hζu1 : ζu ≠ 1 := fun h1 => hζ.ne_one hp.one_lt (by rw [← hζu, h1, Units.val_one])
  set δ : ↥Bs → Fin (m + 1) → F := fun b k => ((σu (κ b k) : Fˣ) : F) with hδ
  have hsep : ∀ l l', l ≠ l' → ∃ b, δ b l ≠ δ b l' := by
    intro l l' hll'
    obtain ⟨b, hb, hbt⟩ := hκ.surj (twoPoint ζu l l') (twoPoint_pow hζup l l')
      (twoPoint_prod ζu hll')
    refine ⟨⟨b, hb⟩, fun heq => ?_⟩
    have h1 : σu (κ b l) = σu (κ b l') := Units.ext heq
    rw [hbt] at h1
    simp only [twoPoint, ite_true, Ne.symm hll', ite_false] at h1
    have h3 : ζu ^ 2 = 1 := by
      have h4 : σu (ζu * ζu) = 1 := by
        rw [map_mul]
        nth_rewrite 2 [h1]
        rw [map_inv, mul_inv_cancel]
      rw [pow_two]
      exact (hσu1 _).mp h4
    have hg := pow_gcd_eq_one.mpr ⟨hζup, h3⟩
    rw [(Nat.coprime_primes hp Nat.prime_two).mpr hp2, pow_one] at hg
    exact hζu1 hg
  obtain ⟨ρ, hρ⟩ := exists_perm_of_separating A hsep fun b => by
    obtain ⟨c, hc⟩ := hmat b b.2
    refine ⟨fun k => ((c * κ (e * b * e⁻¹) k : Fˣ) : F), ?_⟩
    have h1 := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL] at h1
    exact h1
  have hcoord' : ∀ b ∈ Bs, ∀ k, κ (e * b * e⁻¹) k = σu (κ b (ρ k)) := by
    intro b hb
    obtain ⟨c, hc⟩ := hmat b hb
    have h1 := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL] at h1
    have h2 := hρ fun k => ((σu (κ b k) : Fˣ) : F)
    rw [h1] at h2
    have h3 := congrArg (· * ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      h2
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at h3
    have hent : ∀ k, c * κ (e * b * e⁻¹) k = σu (κ b (ρ k)) := fun k => by
      have h4 := congrFun (congrFun h3 k) k
      rw [diagonal_apply_eq, diagonal_apply_eq] at h4
      exact Units.ext h4
    have hcp : c ^ p = 1 := by
      have h5 := hent 0
      have h6 : (c * κ (e * b * e⁻¹) 0) ^ p = 1 := by
        rw [h5, ← map_pow, (hcoord b hb).1, map_one]
      rwa [mul_pow, (hcoord _ (hconj b hb)).1 0, mul_one] at h6
    have hcn : c ^ (m + 1) = 1 := by
      have h5 : ∏ k, c * κ (e * b * e⁻¹) k = 1 := by
        rw [Finset.prod_congr rfl fun k _ => hent k, ← map_prod,
          Equiv.prod_comp ρ (fun i => κ b i), hκ.prod b hb, map_one]
      rwa [Finset.prod_mul_distrib, hκ.prod _ (hconj b hb), mul_one, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin] at h5
    intro k
    rw [← hent k, eq_one_of_pow hp hpn hcp hcn, one_mul]
  refine ⟨ρ.symm, fun b hb i => ?_⟩
  rw [hcoord' b hb, Equiv.apply_symm_apply, hσu1]

end Transport

end SL

end NoOffenderClassical

section Family

theorem ggSixBstarNoOffenderOn_PSLSplitCoprime : GGSixBstarNoOffenderOn GGPSLSplitCoprime := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hpn⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hctx.2.2.2.1.1.2.2.1; omega⟩
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  obtain ⟨A₀, hA₀⟩ := ggBstarToralPSLInput_holds G p B Bs x L D J m f ψ hctx hC hpq
  set ψ' := ψ.comp (InnerDiagA.conjSL A₀⁻¹) with hψ'
  have hker' := LinTorus.ker_comp_conjSL_le hker A₀⁻¹
  have hrange' : ψ'.range = ψ.range := LinTorus.range_comp_conjSL ψ A₀⁻¹
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [hrange']
    exact hCψ
  have hBsD : ∀ b ∈ Bs, ∃ d : Fin (m + 1) → (GaloisField 2 f)ˣ,
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ' := by
    intro b hb
    obtain ⟨Ab, hAb⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hctx.2.2.2.2.2.2.1.2 b hb)
    obtain ⟨d, hd⟩ := LinTorus.exists_eq_diagGL fun i j hij => hA₀ b hb Ab hAb hij
    have h1 : (b⁻¹, Ab) ∈ LinFusion.ggInducedPairs ψ := fun u => by
      change b⁻¹ * ψ u * b⁻¹⁻¹ = _
      rw [inv_inv]
      exact hAb u
    have h2 := (LinFusion.ggInducedPairs ψ).inv_mem h1
    rw [Prod.inv_mk, inv_inv] at h2
    have h3 := LinModel.mem_ggInducedPairs_comp_conjSL_inv h2 A₀
    refine ⟨d⁻¹, ?_⟩
    rw [LinFusion.diagGL_inv, ← hd]
    convert h3 using 2
    group
  have hle : Bs ≤ LinModel.rootTorus p ψ' :=
    LinModel.le_rootTorus hker' hBsD hctx.bstar.2.1.2
  have hge : LinModel.rootTorus p ψ' ≤ Bs := LinModel.rootTorus_le hC' hBsD hctx.bstar.2.2.2
  have hnorm : ∀ b ∈ Bs, ∃ t : Fin (m + 1) → (GaloisField 2 f)ˣ, (∀ i, t i ^ p = 1) ∧
      ∏ i, t i = 1 ∧ (b, InnerDiagA.diagGL t) ∈ LinFusion.ggInducedPairs ψ' := fun b hb => by
    obtain ⟨d, hd, hbd⟩ := hle hb
    exact NoOffenderClassical.SL.exists_normalized hpp hpn hd hbd
  have hreal : ∀ (t : Fin (m + 1) → (GaloisField 2 f)ˣ) (ht : ∏ i, t i = 1),
      (∀ i, t i ^ p = 1) → ψ' (LinModel.diagSL t ht) ∈ Bs := fun t ht htp =>
    hge ⟨t, htp, LinModel.exists_mem_of_prod_eq_one ψ' t ht⟩
  have hκ := NoOffenderClassical.SL.coordsOne hpp hpn hker' hC' hnorm hreal
  have : Fact p.Prime := ⟨hpp⟩
  have hpK : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    exact hpq
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p hpK
  have hζ : IsPrimitiveRoot (u : GaloisField 2 f) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
  intro E hEM hEN hE
  by_cases hEC : E ≤ Subgroup.centralizer (Bs : Set G)
  · exact Or.inl hEC
  right
  refine NoOffenderClassical.card_mul_lt_of_coordsOne hpp hp2 hζ hκ
    (by rw [Fintype.card_fin]; omega) (by rwa [Fintype.card_fin]) hctx.bstar.2.1 hE hEN
    (fun e he => ?_) hEC
  have heM : e ∈ Subgroup.normalizer (ψ'.range : Set G) := by
    rw [hrange', hctx.range_eq]
    exact hEM he
  exact NoOffenderClassical.SL.exists_supp_perm hm hpp hp2 hpn hζ hker' hC' hnorm hκ heM (hEN he)
    (hE.2 e he)

end Family

end CFSG.StandardType
