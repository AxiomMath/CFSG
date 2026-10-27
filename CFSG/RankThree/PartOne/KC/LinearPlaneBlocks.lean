module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks

public section

namespace CFSG.RankThree.PartOne.KCLinPlane

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem eq_zero_of_mem_primaryComponent_ne {x : Module.End K V} {a b : K[X]}
    (ha : a ∈ primaryFactors x) (hb : b ∈ primaryFactors x) (hab : a ≠ b) {v : V}
    (hva : v ∈ primaryComponent x a) (hvb : v ∈ primaryComponent x b) : v = 0 := by
  obtain ⟨u, w, h⟩ := isCoprime_of_mem_primaryFactors ha hb hab
  have h1 := congrArg (fun f : K[X] => aeval x f v) h
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply, mem_primaryComponent.mp hva, mem_primaryComponent.mp hvb, map_zero,
    add_zero] at h1
  exact h1.symm

theorem mem_primaryFactors_of_ne_zero {x : Module.End K V} {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) {v : V} (hv0 : v ≠ 0) (hv : v ∈ primaryComponent x h) :
    h ∈ primaryFactors x := by
  rw [mem_primaryFactors]
  refine ⟨hirr, hmon, ?_⟩
  by_contra hnd
  have hcop : IsCoprime h (minpoly K x) := (hirr.coprime_iff_not_dvd).mpr hnd
  obtain ⟨u, w, huw⟩ := hcop
  have h1 := congrArg (fun f : K[X] => aeval x f v) huw
  simp [mem_primaryComponent.mp hv, minpoly.aeval] at h1
  exact hv0 h1.symm

omit [FiniteDimensional K V] in
theorem aeval_mem_of_stable {x : Module.End K V} {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U)
    (f : K[X]) {y : V} (hy : y ∈ U) : aeval x f y ∈ U := by
  have hpow : ∀ n : ℕ, (x ^ n) y ∈ U := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hU _ ih
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem c (hpow n)

omit [FiniteDimensional K V] in
theorem aeval_apply_eq_of_agree {x y : Module.End K V} {U : Submodule K V}
    (hx : ∀ u ∈ U, x u ∈ U) (hxy : ∀ u ∈ U, x u = y u) (f : K[X]) {u : V} (hu : u ∈ U) :
    aeval x f u = aeval y f u := by
  have hpow : ∀ n : ℕ, ∀ w ∈ U, (x ^ n) w = (y ^ n) w ∧ (x ^ n) w ∈ U := by
    intro n
    induction n with
    | zero =>
      intro w hw
      simpa using hw
    | succ n ih =>
      intro w hw
      obtain ⟨h1, h2⟩ := ih w hw
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← h1]
      exact ⟨hxy _ h2, hx _ h2⟩
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, (hpow n u hu).1]

theorem natDegree_le_finrank_of_stable {x : Module.End K V} {a : K[X]} (ha : a ∈ primaryFactors x)
    {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U) {y : V} (hyU : y ∈ U)
    (hya : y ∈ primaryComponent x a) (hy0 : y ≠ 0) : a.natDegree ≤ finrank K U := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  let y' : primaryComponent x a := ⟨y, hya⟩
  have hy'0 : y' ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  let ψ : AdjoinRoot a →ₗ[K] V :=
    (Submodule.subtype _).comp
      ((LinearMap.toSpanSingleton (AdjoinRoot a) (primaryComponent x a) y').restrictScalars K)
  have hψ : ∀ e : AdjoinRoot a, ψ e ∈ U := by
    intro e
    induction e using AdjoinRoot.induction_on with
    | _ f =>
      change ((AdjoinRoot.mk a f • y' : primaryComponent x a) : V) ∈ U
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_stable hU f hyU
  let φ : AdjoinRoot a →ₗ[K] U := LinearMap.codRestrict U ψ hψ
  have hinj : Function.Injective φ := by
    intro e₁ e₂ h12
    have h1 : ψ e₁ = ψ e₂ := by simpa [φ] using congrArg Subtype.val h12
    have h2 : e₁ • y' = e₂ • y' := Subtype.ext h1
    exact (smul_left_injective (AdjoinRoot a) hy'0) h2
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [(AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] at this


omit [FiniteDimensional K V] in
theorem natCard_adjoinRoot [Finite K] (a : K[X]) [Fact (Irreducible a)] :
    Nat.card (AdjoinRoot a) = Nat.card K ^ a.natDegree := by
  have hmod : Module.Finite K (AdjoinRoot a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finite
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot a),
    (AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem det_restrict_eq_det (W : Submodule K V) (e : Module.End K V) (hW : W = LinearMap.range e)
    (he : e * e = e) (g : Module.End K V) (hc : ∀ v, g (e v) = e (g v))
    (hf : ∀ v, g (v - e v) = v - e v) (hmaps : W ≤ W.comap g) :
    LinearMap.det (g.restrict hmaps) = LinearMap.det g := by
  subst hW
  rw [LinearMap.det_eq_det_mul_det (LinearMap.range e) g hmaps]
  have ee : ∀ v, e (e v) = e v := fun v => by
    simpa using congrArg (fun f : Module.End K V => f v) he
  have h2 : (LinearMap.range e).mapQ (LinearMap.range e) g hmaps = LinearMap.id := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    have h3 : g v = g (e v) + (v - e v) := by
      calc g v = g (e v + (v - e v)) := by congr 1; abel
        _ = g (e v) + (v - e v) := by rw [map_add, hf]
    refine ⟨g v - v, ?_⟩
    rw [map_sub, ← hc v, h3]
    abel
  rw [h2, LinearMap.det_id, mul_one]

theorem det_eq_one_of_restrictScalars {x : Module.End K V} {a : K[X]} [Fact (Irreducible a)]
    (ha1 : a.natDegree = 1) (f : Module.End (AdjoinRoot a) (primaryComponent x a))
    (hf : LinearMap.det (f.restrictScalars K) = 1) : LinearMap.det f = 1 := by
  have hrank : finrank K (AdjoinRoot a) = 1 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, ha1]
  rw [LinearMap.det_restrictScalars] at hf
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot a) one_ne_zero).mp
    hrank (LinearMap.det f)
  have hd : LinearMap.det f = algebraMap K (AdjoinRoot a) c := by
    rw [← hc, Algebra.algebraMap_eq_smul_one]
  rw [hd, Algebra.norm_algebraMap, hrank, pow_one] at hf
  rw [hd, hf, map_one]


theorem exists_mixing_unipotent {x : Module.End K V} (hx : Squarefree (minpoly K x)) {h : K[X]}
    (hh : h ∈ primaryFactors x) {e e' : Module.End K V} (hex : Commute e x)
    (hex' : Commute e' x) (he : e * e = e) (he' : e' * e' = e') (hee' : e * e' = 0)
    (hne : e * primaryProjection x h ≠ 0) (hne' : e' * primaryProjection x h ≠ 0) :
    ∃ (β : Module.End K V) (hβ : β ∈ commutant x), e' * β = β ∧ β * e = β ∧ β ≠ 0 ∧
      β * β = 0 ∧
      (∀ k ∈ primaryFactors x, k ≠ h → ∀ v ∈ primaryComponent x k, β v = 0) ∧
      LinearMap.det (1 + commutantRestrict h ⟨β, hβ⟩) = 1 ∧
      2 ≤ finrank (AdjoinRoot h) (primaryComponent x h) := by
  classical
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  set P := primaryProjection x h with hP
  have hPx : Commute x P := (commute_aeval (Commute.refl x) _)
  have hPe : Commute e P := commute_aeval hex _
  have hPe' : Commute e' P := commute_aeval hex' _
  have hmem : ∀ v, P v ∈ primaryComponent x h := primaryProjection_mem hx hh
  have hfix : ∀ v ∈ primaryComponent x h, P v = v := fun v hv => primaryProjection_of_mem hx hh hv
  let ε : Module.End (AdjoinRoot h) (primaryComponent x h) :=
    commutantRestrict h ⟨e, (mem_commutant x).mpr hex⟩
  let ε' : Module.End (AdjoinRoot h) (primaryComponent x h) :=
    commutantRestrict h ⟨e', (mem_commutant x).mpr hex'⟩
  have hε : ∀ w : primaryComponent x h, ((ε w : primaryComponent x h) : V) = e (w : V) :=
    fun w => rfl
  have hε' : ∀ w : primaryComponent x h, ((ε' w : primaryComponent x h) : V) = e' (w : V) :=
    fun w => rfl
  have hεε : ∀ w, ε (ε w) = ε w := fun w => Subtype.ext (by
    rw [hε, hε]
    simpa using congrArg (fun f : Module.End K V => f (w : V)) he)
  have hεε' : ∀ w, ε (ε' w) = 0 := fun w => Subtype.ext (by
    rw [hε, hε']
    simpa using congrArg (fun f : Module.End K V => f (w : V)) hee')
  have hε'ε' : ∀ w, ε' (ε' w) = ε' w := fun w => Subtype.ext (by
    rw [hε', hε']
    simpa using congrArg (fun f : Module.End K V => f (w : V)) he')
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, e (P v₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (LinearMap.ext fun v => by simpa using hcon v)
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, e' (P v₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne' (LinearMap.ext fun v => by simpa using hcon v)
  let z₂ : primaryComponent x h := ε ⟨P v₀, hmem v₀⟩
  let y₁ : primaryComponent x h := ε' ⟨P v₁, hmem v₁⟩
  have hz₂ : z₂ ≠ 0 := fun h0 => hv₀ (congrArg Subtype.val h0)
  have hy₁ : y₁ ≠ 0 := fun h0 => hv₁ (congrArg Subtype.val h0)
  obtain ⟨θ, hθ⟩ := Projective.exists_dual_eq_one (AdjoinRoot h) hz₂
  let ξ : Module.Dual (AdjoinRoot h) (primaryComponent x h) := θ.comp ε
  have hξz : ξ z₂ = 1 := by
    change θ (ε (ε ⟨P v₀, hmem v₀⟩)) = 1
    rw [hεε]
    exact hθ
  have hξy : ξ y₁ = 0 := by
    change θ (ε (ε' ⟨P v₁, hmem v₁⟩)) = 0
    rw [hεε', map_zero]
  let π : V →ₗ[K] primaryComponent x h := P.codRestrict (primaryComponent x h) hmem
  have hπv : ∀ v, ((π v : primaryComponent x h) : V) = P v := fun v => rfl
  let β : Module.End K V := (primaryComponent x h).subtype ∘ₗ
    ((ξ.smulRight y₁).restrictScalars K) ∘ₗ π
  have hβv : ∀ v, β v = ((ξ (π v) • y₁ : primaryComponent x h) : V) := fun v => rfl
  have hπx : ∀ v, π (x v) = AdjoinRoot.root h • π v := fun v => Subtype.ext (by
    rw [hπv, coe_root_smul_primaryComponent, hπv]
    simpa using (congrArg (fun f : Module.End K V => f v) hPx.eq).symm)
  have hπe : ∀ v, π (e v) = ε (π v) := fun v => Subtype.ext (by
    rw [hπv, hε, hπv]
    simpa using (congrArg (fun f : Module.End K V => f v) hPe.eq).symm)
  have hξε : ∀ w, ξ (ε w) = ξ w := fun w => by
    change θ (ε (ε w)) = θ (ε w)
    rw [hεε]
  have hπfix : ∀ w : primaryComponent x h, π (w : V) = w := fun w => Subtype.ext (by
    rw [hπv]
    exact hfix _ w.2)
  have hβx : Commute β x := by
    refine LinearMap.ext fun v => ?_
    change β (x v) = x (β v)
    rw [hβv, hβv, hπx, map_smul, smul_eq_mul, mul_smul, ← coe_root_smul_primaryComponent]
  have hβ : β ∈ commutant x := (mem_commutant x).mpr hβx
  have hε'y : ε' y₁ = y₁ := hε'ε' _
  have hβ1 : e' * β = β := by
    refine LinearMap.ext fun v => ?_
    change e' (β v) = β v
    rw [hβv]
    have : e' ((ξ (π v) • y₁ : primaryComponent x h) : V) =
        ((ε' (ξ (π v) • y₁) : primaryComponent x h) : V) := (hε' _).symm
    rw [this, map_smul, hε'y]
  have hβ2 : β * e = β := by
    refine LinearMap.ext fun v => ?_
    change β (e v) = β v
    rw [hβv, hβv, hπe, hξε]
  have hβ0 : β ≠ 0 := by
    intro h0
    have h1 : β (z₂ : V) = 0 := by rw [h0]; rfl
    rw [hβv, hπfix, hξz, one_smul] at h1
    exact hy₁ (Subtype.ext h1)
  have hββ : β * β = 0 := by
    refine LinearMap.ext fun v => ?_
    change β (β v) = 0
    rw [hβv v, hβv, hπfix, map_smul, hξy, smul_zero, zero_smul]
    rfl
  have hkill : ∀ k ∈ primaryFactors x, k ≠ h → ∀ v ∈ primaryComponent x k, β v = 0 := by
    intro k hk hkh v hv
    have hPv : P v = 0 := primaryProjection_of_mem_ne hx hh hk hkh hv
    have hπ0 : π v = 0 := Subtype.ext (by rw [hπv, hPv]; rfl)
    rw [hβv, hπ0, map_zero, zero_smul]
    rfl
  have hR : ∀ w : primaryComponent x h, commutantRestrict h ⟨β, hβ⟩ w = ξ w • y₁ := fun w =>
    Subtype.ext (by
      change β (w : V) = _
      rw [hβv, hπfix])
  have hdet : LinearMap.det (1 + commutantRestrict h ⟨β, hβ⟩) = 1 := by
    have h1 : (1 + commutantRestrict h ⟨β, hβ⟩ : Module.End (AdjoinRoot h) (primaryComponent x h)) =
        LinearMap.transvection ξ y₁ := by
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.add_apply, Module.End.one_apply, hR, LinearMap.transvection.apply]
    have h2 := LinearEquiv.transvection.det_eq_one hξy
    have h4 := congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) h2
    rw [LinearEquiv.coe_det] at h4
    rw [h1]
    exact h4
  have hmult : 2 ≤ finrank (AdjoinRoot h) (primaryComponent x h) := by
    have hli : LinearIndependent (AdjoinRoot h) ![y₁, z₂] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : ε y₁ = 0 := hεε' _
      have h2 : ε z₂ = z₂ := hεε _
      have h3 := congrArg ε hst
      rw [map_add, map_smul, map_smul, h1, h2, smul_zero, zero_add, map_zero] at h3
      have ht : t = 0 := by
        by_contra ht
        exact hz₂ ((smul_eq_zero.mp h3).resolve_left ht)
      subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hy₁, rfl⟩
    have := hli.fintype_card_le_finrank
    simpa using this
  exact ⟨β, hβ, hβ1, hβ2, hβ0, hββ, hkill, hdet, hmult⟩


end Generic

section Blocks

variable {n : ℕ} {K : Type} [Field K]

theorem mem_blockImage_of_restrict {x : Module.End K (Fin n → K)}
    (hx : Squarefree (minpoly K x)) (a : primaryFactors x) {a0 g : GL (Fin n) K}
    (hax : Matrix.toLin' (a0 : Matrix (Fin n) (Fin n) K) = x) (hcomm : g * a0 = a0 * g)
    (hfix : ∀ k : primaryFactors x, k ≠ a → ∀ v ∈ primaryComponent x (k : K[X]),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v)
    (hdet : ∀ r : commutant x,
      (r : Module.End K (Fin n → K)) = Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) →
      LinearMap.det (commutantRestrict (a : K[X]) r) = 1) :
    g ∈ blockImage hx a := by
  classical
  set u : (commutant x)ˣ := commutantUnitOfCommute a0 g hax hcomm with hu
  set w : PiGL (Efac x) (mult x) := (thetaEquivUnits hx).symm u with hw
  have hθ : blockTheta hx w = g := by
    have : blockTheta hx w = commutantUnitsToGL x u := by simp [blockTheta, hw]
    rw [this, hu]
    exact commutantUnitsToGL_commutantUnitOfCommute a0 g hax hcomm
  have hucoe : ((u : commutant x) : Module.End K (Fin n → K)) =
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) := by
    rw [hu]
    exact toLinAlgEquiv'_eq_toLin' _
  have hmat : ∀ b : primaryFactors x,
      ((w b : GL (Fin (mult x b)) (Efac x b)) : Matrix (Fin (mult x b)) (Fin (mult x b))
        (Efac x b)) =
      LinearMap.toMatrix (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        (commutantRestrict (b : K[X]) (u : commutant x)) := by
    intro b
    have h1 := congrFun (commutantEquivMatrix_thetaEquivUnits hx w) b
    have h2 : ((thetaEquivUnits hx w : (commutant x)ˣ) : commutant x) = (u : commutant x) := by
      rw [hw]
      simp
    rw [h2] at h1
    rw [← h1]
    rfl
  have hw1 : ∀ b : primaryFactors x, b ≠ a → w b = 1 := by
    intro b hb
    apply Units.ext
    rw [hmat b, Units.val_one]
    have : commutantRestrict (b : K[X]) (u : commutant x) = LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change ((u : commutant x) : Module.End K (Fin n → K)) (v : Fin n → K) = v
      rw [hucoe]
      exact hfix b hb v v.2
    rw [this, LinearMap.toMatrix_id]
  have hdet1 : ((w a : GL (Fin (mult x a)) (Efac x a)) : Matrix (Fin (mult x a))
      (Fin (mult x a)) (Efac x a)).det = 1 := by
    rw [hmat a, LinearMap.det_toMatrix]
    exact hdet u hucoe
  obtain ⟨s, hs⟩ : w a ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (mult x a)) (Efac x a) →* _).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, hdet1]; rfl)
  have hwe : w = blockEmbed (Efac x) (mult x) a s := by
    funext b
    by_cases hb : b = a
    · subst hb
      rw [blockEmbed_apply_self, hs]
    · rw [blockEmbed_apply_of_ne hb, hw1 b hb]
  exact mem_blockImage.mpr ⟨s, by rw [← hwe]; exact hθ⟩


end Blocks

end CFSG.RankThree.PartOne.KCLinPlane
