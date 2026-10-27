module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

namespace SevOm

open Matrix Module Multiplicative NoOffOm SUTB

section RichFrame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem exists_richFrame (hA : GenMax B Γ p A) :
    ∃ (r : ℕ) (ι₀ : Multiplicative (Fin r → ZMod p) →* GL (Fin d) K)
      (U : Fin r → Submodule K (Fin d → K)),
      Function.Injective ι₀ ∧ ι₀.range = A ∧ (∀ i, U i ≠ ⊥) ∧ (∀ i, NondegOn B (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0) ∧
      (∀ (s : Multiplicative (Fin r → ZMod p)) j, ∀ u ∈ U j, glin (ι₀ s) u ∈ U j) ∧
      (∀ (s : Multiplicative (Fin r → ZMod p)) j, toAdd s j = 0 → ∀ u ∈ U j,
        glin (ι₀ s) u = u) ∧
      (∀ (s : Multiplicative (Fin r → ZMod p)) j, toAdd s j ≠ 0 → ∀ u ∈ U j,
        glin (ι₀ s) u = u → u = 0) ∧
      ∀ (s : Multiplicative (Fin r → ZMod p)) v, glin (ι₀ s) v = v ↔
        ∀ j, toAdd s j ≠ 0 → v ∈ (U j).orthogonalBilin B := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  set r := S.card with hr
  set e : Fin r ≃ ↥S := S.equivFin.symm with he
  set y : Fin r → GL (Fin d) K := fun i => (e i : GL (Fin d) K) with hy
  have hyS : ∀ i, y i ∈ S := fun i => (e i).2
  have hyA : ∀ i, y i ∈ A := fun i => hS.mem _ (hyS i)
  have hyinj : Function.Injective y := fun i j hij => e.injective (Subtype.ext hij)
  have hyS' : ∀ z ∈ S, ∃ i, y i = z := fun z hz =>
    ⟨e.symm ⟨z, hz⟩, by simp only [hy, Equiv.apply_symm_apply]⟩
  set U : Fin r → Submodule K (Fin d → K) := fun i => grng (y i) with hU
  have hUnd : ∀ i, NondegOn (B) (U i) := fun i => nondegOn_grng hA (hyA i)
  have hUA : ∀ i, ∀ a ∈ A, ∀ u ∈ U i, glin a u ∈ U i := fun i a ha => grng_inv hA (hyA i) ha
  have hUorth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0 :=
    fun i j hij => hS.orth _ (hyS i) _ (hyS j) (fun e' => hij (hyinj e'))
  have hUne : ∀ i, ∃ u ∈ U i, u ≠ 0 := fun i =>
    (Submodule.ne_bot_iff _).mp (grng_ne_bot (hS.ne_one _ (hyS i)))
  have hUperp : ∀ j, ∀ u ∈ U j, u ∈ (U j).orthogonalBilin (B) → u = 0 :=
    fun j u hu hu' => hUnd j u hu fun m hm => (Submodule.mem_orthogonalBilin.mp hu') m hm
  have hUsub : ∀ i j, i ≠ j → ∀ u ∈ U j, u ∈ (U i).orthogonalBilin (B) :=
    fun i j hij u hu => Submodule.mem_orthogonalBilin.mpr fun m hm => hUorth i j hij m hm u hu
  have hb : ∀ i, ∃ g ∈ A, (∀ w ∈ U i, glin g w = glin (y i) w) ∧
      ∀ v ∈ (U i).orthogonalBilin (B), glin g v = v :=
    fun i => hA.exists_mem_restrict (hUnd i) (hUA i) (hyA i)
  choose b hbA hbon hboff using hb
  have hbpow : ∀ j (k : ℕ), ∀ u ∈ U j, glin (b j ^ k) u = glin (y j ^ k) u := by
    intro j k
    induction k with
    | zero => intro u _; rw [pow_zero, pow_zero]
    | succ k ih =>
      intro u hu
      have hyk : glin (y j ^ k) u ∈ U j := hUA j _ (A.pow_mem (hyA j) k) u hu
      rw [pow_succ', glin_mul, Module.End.mul_apply, ih u hu, hbon j _ hyk, ← Module.End.mul_apply,
        ← glin_mul, ← pow_succ']
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a c => Subtype.ext (hA.comm _ a.2 _ c.2) }
  set bA : Fin r → A := fun i => ⟨b i, hbA i⟩ with hbA'
  have hbAp : ∀ i, bA i ^ p = 1 := fun i => Subtype.ext (hA.pow _ (hbA i))
  set ι₁ : Multiplicative (Fin r → ZMod p) →* A :=
    { toFun := fun s => ∏ i, bA i ^ (toAdd s i).val
      map_one' := by simp
      map_mul' := fun s s' => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [ZMod.val_add, ← pow_eq_pow_mod _ (hbAp i), pow_add] } with hι₁
  have hι₁_apply : ∀ s, ι₁ s = ∏ i, bA i ^ (toAdd s i).val := fun s => rfl
  have hact : ∀ (s : Multiplicative (Fin r → ZMod p)) j, ∀ u ∈ U j,
      glin ((ι₁ s : A) : GL (Fin d) K) u = glin (y j ^ (toAdd s j).val) u := by
    intro s j u hu
    have hrest : (∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val) ∈
        (genFixOn d K (U j : Set (Fin d → K))).comap A.subtype := by
      refine Subgroup.prod_mem _ fun i hi => Subgroup.pow_mem _ ?_ _
      exact fun w hw => hboff i w (hUsub i j (Finset.ne_of_mem_erase hi) w hw)
    have hrest' : glin ((∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val : A) :
        GL (Fin d) K) u = u := hrest u hu
    rw [hι₁_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Subgroup.coe_mul, glin_mul,
      Module.End.mul_apply, hrest', SubgroupClass.coe_pow, hbpow j _ u hu]
  have hnd : ∀ (s : Multiplicative (Fin r → ZMod p)) j, toAdd s j ≠ 0 →
      ¬ p ∣ (toAdd s j).val := by
    intro s j hj hdvd
    apply hj
    rw [← ZMod.natCast_zmod_val (toAdd s j)]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  have hfix : ∀ (s : Multiplicative (Fin r → ZMod p)) (v : Fin d → K),
      glin ((ι₁ s : A) : GL (Fin d) K) v = v ↔
        ∀ j, toAdd s j ≠ 0 → v ∈ (U j).orthogonalBilin (B) := by
    intro s v
    constructor
    · intro hv j hj
      set g : GL (Fin d) K := ((ι₁ s : A) : GL (Fin d) K) with hg
      set k := (toAdd s j).val with hk
      have hkp : ¬ p ∣ k := hnd s j hj
      have hmaps : ∀ x ∈ U j, (glin (y j ^ k) - 1) x ∈ U j := fun x hx =>
        (U j).sub_mem (hUA j _ (A.pow_mem (hyA j) k) x hx) hx
      set φ : Module.End K ↥(U j) := (glin (y j ^ k) - 1).restrict hmaps with hφ
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨x, hx⟩ hx0
        have h1 : (glin (y j ^ k) - 1) x = 0 := congrArg Subtype.val hx0
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
        exact Subtype.ext (eq_zero_of_pow_fix' hA (hyA j) hkp hx h1)
      have hφsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφinj
      refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
      obtain ⟨⟨x, hx⟩, hxm⟩ := hφsurj ⟨m, hm⟩
      have hm' : m = glin g x - x := by
        have h1 : (glin (y j ^ k) - 1) x = m := by
          have h2 := congrArg Subtype.val hxm
          simpa only [hφ, LinearMap.restrict_apply] using h2
        rw [← h1, LinearMap.sub_apply, Module.End.one_apply, hg, hact s j x hx]
      change B m v = 0
      rw [hm', map_sub, LinearMap.sub_apply, ← hA.iso g (ι₁ s).2 x v, hv, sub_self]
    · intro hv
      have hmem : ∀ i, bA i ^ (toAdd s i).val ∈ (genFixOn d K {v}).comap A.subtype := by
        intro i
        by_cases hi : toAdd s i = 0
        · rw [hi, ZMod.val_zero, pow_zero]
          exact Subgroup.one_mem _
        · refine Subgroup.pow_mem _ ?_ _
          intro w hw
          rw [Set.mem_singleton_iff.mp hw]
          exact hboff i v (hv i hi)
      have h1 := Subgroup.prod_mem _ fun i (_ : i ∈ Finset.univ) => hmem i
      rw [← hι₁_apply] at h1
      exact h1 v rfl
  have hinj₁ : Function.Injective ι₁ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, toAdd s j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (toAdd.injective (funext hcon))
    obtain ⟨u, hu, hu0⟩ := hUne j
    have h1 : glin ((ι₁ s : A) : GL (Fin d) K) u = u := by
      rw [hs, OneMemClass.coe_one, glin_one]
      rfl
    exact hu0 (hUperp j u hu ((hfix s u).mp h1 j hj))
  have hrange₁ : ∀ c ∈ A, ∃ s, ((ι₁ s : A) : GL (Fin d) K) = c := by
    intro c hc
    have hk : ∀ j, ∃ k : ℕ, ∀ u ∈ U j, glin c u = glin (y j ^ k) u :=
      fun j => hS.cyc _ (hyS j) c hc
    choose k hk using hk
    refine ⟨ofAdd fun j => (k j : ZMod p), ?_⟩
    set g : GL (Fin d) K := ((ι₁ (ofAdd fun j => (k j : ZMod p)) : A) :
      GL (Fin d) K) with hg
    have hgA : g ∈ A := (ι₁ _).2
    have hag : ∀ j, ∀ u ∈ U j, glin g u = glin c u := by
      intro j u hu
      rw [hg, hact _ j u hu, hk j u hu, toAdd_ofAdd, ZMod.val_natCast,
        ← pow_eq_pow_mod _ (hA.pow _ (hyA j))]
    have hle : genPieceSpan S ≤ LinearMap.ker (glin (g⁻¹ * c) - 1) := by
      refine iSup₂_le fun z hz => ?_
      obtain ⟨j, rfl⟩ := hyS' z hz
      intro u hu
      have h1 : glin g⁻¹ (glin g u) = u := by
        rw [← Module.End.mul_apply, ← glin_mul, inv_mul_cancel, glin_one]
        rfl
      rw [LinearMap.mem_ker, LinearMap.sub_apply, glin_mul, Module.End.mul_apply, ← hag j u hu, h1,
        Module.End.one_apply, sub_self]
    have hc1 : g⁻¹ * c = 1 := hterm _ (A.mul_mem (A.inv_mem hgA) hc) fun v hv =>
      sub_eq_zero.mp (hle hv)
    exact (inv_mul_eq_one.mp hc1)
  refine ⟨r, A.subtype.comp ι₁, U, fun s t hst => hinj₁ (Subtype.ext hst), ?_,
    fun i => (Submodule.ne_bot_iff _).mpr (hUne i), hUnd, hUorth,
    fun s j u hu => hUA j _ (ι₁ s).2 u hu, ?_, ?_, fun s v => hfix s v⟩
  · ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact (ι₁ s).2
    · intro hc
      obtain ⟨s, hs⟩ := hrange₁ c hc
      exact ⟨s, hs⟩
  · intro s j hj u hu
    change glin ((ι₁ s : A) : GL (Fin d) K) u = u
    rw [hact s j u hu, hj, ZMod.val_zero, pow_zero, glin_one]
    rfl
  · intro s j hj u hu h1
    change glin ((ι₁ s : A) : GL (Fin d) K) u = u at h1
    rw [hact s j u hu] at h1
    exact eq_zero_of_pow_fix' hA (hyA j) (hnd s j hj) hu h1

end RichFrame

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

structure Frame (Q : QuadraticForm K V) (p : ℕ) (A : Subgroup (V ≃ₗ[K] V)) (r : ℕ) where
  ι : Multiplicative (Fin r → ZMod p) →* (V ≃ₗ[K] V)
  U : Fin r → Submodule K V
  inj : Function.Injective ι
  range : ι.range = A
  ne_bot : ∀ i, U i ≠ ⊥
  nondeg : ∀ i, ∀ u ∈ U i, (∀ v ∈ U i, QuadraticMap.polar Q v u = 0) → u = 0
  orth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, QuadraticMap.polar Q u v = 0
  mapsTo : ∀ (s : Multiplicative (Fin r → ZMod p)) j, ∀ u ∈ U j, ι s u ∈ U j
  triv : ∀ (s : Multiplicative (Fin r → ZMod p)) j, toAdd s j = 0 → ∀ u ∈ U j, ι s u = u
  fpf : ∀ (s : Multiplicative (Fin r → ZMod p)) j, toAdd s j ≠ 0 → ∀ u ∈ U j, ι s u = u → u = 0
  fix : ∀ (s : Multiplicative (Fin r → ZMod p)) v, ι s v = v ↔
    ∀ j, toAdd s j ≠ 0 → ∀ u ∈ U j, QuadraticMap.polar Q u v = 0

end Frame

section Transport

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ} {A : Subgroup (GL (Fin d) K)}

omit [Finite K] [CharP K 2] in
theorem matrixLinearIso_apply_eq_glin (g : GL (Fin d) K) (v : Fin d → K) :
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso g v =
      glin g v := by
  rw [glin_apply]
  rfl

theorem exists_frame_of_genMax
    (hA : GenMax (polB Q) (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
      Q) p A) :
    ∃ r, Nonempty (Frame Q p (A.map
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso.toMonoidHom)
        r) := by
  classical
  obtain ⟨r, ι₀, U, hinj, hrange, hne, hnd, horth, hmaps, htriv, hfpf, hfix⟩ := exists_richFrame hA
  set m := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso
    (d := d) (K := K) with hm
  have hm' : ∀ (g : GL (Fin d) K) (v : Fin d → K), m g v = glin g v :=
    matrixLinearIso_apply_eq_glin
  refine ⟨r, ⟨{
    ι := m.toMonoidHom.comp ι₀
    U := U
    inj := m.injective.comp hinj
    range := by rw [MonoidHom.range_comp, hrange]
    ne_bot := hne
    nondeg := fun i u hu h => hnd i u hu fun v hv => by rw [polB_apply]; exact h v hv
    orth := fun i j hij u hu v hv => by rw [← polB_apply]; exact horth i j hij u hu v hv
    mapsTo := fun s j u hu => by
      change m (ι₀ s) u ∈ U j
      rw [hm']
      exact hmaps s j u hu
    triv := fun s j hj u hu => by
      change m (ι₀ s) u = u
      rw [hm']
      exact htriv s j hj u hu
    fpf := fun s j hj u hu h => hfpf s j hj u hu (by rw [← hm']; exact h)
    fix := fun s v => by
      change m (ι₀ s) v = v ↔ _
      rw [hm', hfix]
      refine forall_congr' fun j => imp_congr_right fun _ => ?_
      rw [Submodule.mem_orthogonalBilin]
      rfl }⟩⟩

end Transport

end SevOm

end CFSG.StandardType
