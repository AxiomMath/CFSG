module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpCount
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUDim
public import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis

public section

namespace CFSG.StandardType

namespace OrdPNsGen

open Matrix Module Polynomial SUTB NoOffOm CFSG.RankThree.PartOne.OddIso
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section Fpf

variable {K : Type} [Field K] [Finite K]

theorem ordQ_dvd_finrank_of_fpf {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (T : Module.End K W),
      T ^ ℓ = 1 → (∀ w, T w = w → w = 0) → OrdPNS.ordQ K ℓ ∣ finrank K W := by
  intro W _ _ _ T
  induction hn : finrank K W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  intro hT hfix
  by_cases hT1 : T = 1
  · have hbot : (⊤ : Submodule K W) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun w _ => hfix w ?_
      rw [hT1, Module.End.one_apply]
    rw [← hn, ← finrank_top K W, hbot, finrank_bot]
    exact dvd_zero _
  obtain ⟨g, hg, hgd, hker⟩ := OrdPNS.exists_irreducible_ker_ne_bot hℓ hT hT1
  obtain ⟨h, hcompl, -⟩ := OrdPNS.isCompl_ker_aeval hℓ hℓK hT hg hgd
  set V₁ := LinearMap.ker (aeval T g) with hV₁
  set V₂ := LinearMap.ker (aeval T h) with hV₂
  set e₁ : Module.End K V₁ := T.restrict (OrdPNS.mapsTo_ker_aeval (Commute.refl T) g) with he₁
  have hge : aeval e₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
    rw [OrdPNS.coe_aeval_restrict_apply]
    exact w.2)
  obtain ⟨a, hdim₁, -, -⟩ := OrdPNS.exists_rank_of_aeval_eq_zero hℓ hℓK hg hgd hge
  set e₂ : Module.End K V₂ := T.restrict (OrdPNS.mapsTo_ker_aeval (Commute.refl T) h) with he₂
  have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
  have hpos : 0 < finrank K V₁ :=
    Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
  have h₂ := ih (finrank K V₂) (by omega) V₂ e₂ rfl (OrdPNS.restrict_pow_eq_one hT _)
    fun w hw => Subtype.ext (hfix w (congrArg Subtype.val hw))
  rw [← hn, ← hfr, hdim₁]
  exact dvd_add (dvd_mul_right _ _) h₂

end Fpf

section Alt

variable {K : Type} [Field K] {d : ℕ}

theorem even_finrank_of_nondegOn {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K}
    (hB : B.IsSymm) (hBalt : ∀ v, B v v = 0) {W : Submodule K (Fin d → K)}
    (hW : NondegOn B W) : Even (finrank K W) := by
  have halt : (B.domRestrict₁₂ W W).IsAlt := fun x => by
    rw [LinearMap.domRestrict₁₂_apply]
    exact hBalt x
  have hnd : (B.domRestrict₁₂ W W).Nondegenerate := by
    refine ⟨fun x hx => Subtype.ext (hW x x.2 fun w hw => ?_), fun x hx =>
      Subtype.ext (hW x x.2 fun w hw => hx ⟨w, hw⟩)⟩
    have h1 := hx ⟨w, hw⟩
    rw [LinearMap.domRestrict₁₂_apply] at h1
    rw [← hB.eq (x : Fin d → K) w, h1]
    rfl
  obtain ⟨m, -, hm, -⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis halt hnd
  exact ⟨m, by omega⟩

end Alt

section Recip

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem dualPoly_eq_self_of_dvd_id {p : ℕ} (hp : p.Prime) {g : K[X]} (hg : Irreducible g)
    (hgm : g.Monic) (hgd : g ∣ X ^ p - C 1) {j : ℕ} (hpj : p ∣ Nat.card K ^ j + 1) :
    dualPoly (RingHom.id K) g = g := by
  classical
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have h0 : g.coeff 0 ≠ 0 := CFSG.RankThree.PartOne.KCUnitaryPlane.coeff_zero_ne_zero_of_dvd hp.pos hgd
  have : CharP (AdjoinRoot g) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
  have : ExpChar (AdjoinRoot g) 2 := ExpChar.prime Nat.prime_two
  set ζ : AdjoinRoot g := AdjoinRoot.root g with hζ
  have hζp : ζ ^ p = 1 := by
    have h1 : AdjoinRoot.mk g (X ^ p - C 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hgd
    simpa [hζ, sub_eq_zero] using h1
  have hζ0 : ζ ≠ 0 := by
    intro h1
    rw [h1, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  set θ : AdjoinRoot g →+* AdjoinRoot g := iterateFrobenius (AdjoinRoot g) 2 ((f : ℕ) * j) with hθ
  have hθK : θ.comp (algebraMap K (AdjoinRoot g)) = algebraMap K (AdjoinRoot g) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, hθ, iterateFrobenius_def, ← map_pow, pow_mul, ← hf]
    rw [FiniteField.pow_card_pow]
  have hθζ : θ ζ = ζ⁻¹ := by
    rw [hθ, iterateFrobenius_def]
    obtain ⟨k, hk⟩ := hpj
    have h1 : ζ ^ (2 ^ ((f : ℕ) * j) + 1) = 1 := by
      rw [pow_mul, ← hq, hk, pow_mul, hζp, one_pow]
    rw [pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have heval : g.eval₂ (algebraMap K (AdjoinRoot g)) ζ⁻¹ = 0 := by
    rw [← hθζ, ← hθK, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root,
      map_zero]
  have hrev : (g.reverse).eval₂ (algebraMap K (AdjoinRoot g)) ζ = 0 := by
    let : Invertible ζ⁻¹ := invertibleOfNonzero (inv_ne_zero hζ0)
    have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap K (AdjoinRoot g)) ζ⁻¹ g
    rw [heval, invOf_eq_inv, inv_inv] at h1
    exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ (inv_ne_zero hζ0))
  have hroot : AdjoinRoot.mk g (dualPoly (RingHom.id K) g) = 0 := by
    rw [← AdjoinRoot.aeval_eq, dualPoly, Polynomial.map_id, map_mul, aeval_C, aeval_def, hrev,
      mul_zero]
  have hdvd : g ∣ dualPoly (RingHom.id K) g := AdjoinRoot.mk_eq_zero.mp hroot
  have hdirr : Irreducible (dualPoly (RingHom.id K) g) :=
    irreducible_dualPoly (fun _ => rfl) hg h0
  exact (eq_of_monic_of_associated hgm (monic_dualPoly h0) (hg.associated_of_dvd hdirr hdvd)).symm

theorem dualPoly_eq_self_of_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : K[X]}
    (hg : Irreducible g) (hgm : g.Monic) (hgd : g ∣ cyclotomic p K)
    (he : Even (OrdPNS.ordQ K p)) : dualPoly (RingHom.id K) g = g := by
  have : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  obtain ⟨k, hk⟩ := he
  have hepos := OrdPNS.ordQ_pos (K := K) hp hpK
  set t : ZMod p := ((Nat.card K : ℕ) : ZMod p) with ht
  have hte : t ^ OrdPNS.ordQ K p = 1 := pow_orderOf_eq_one t
  have hsq : (t ^ k) ^ 2 = 1 := by rw [← pow_mul, show k * 2 = k + k by ring, ← hk, hte]
  have hk1 : t ^ k ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one (by omega) h1
    rw [← OrdPNS.ordQ_def] at this
    omega
  have hneg : t ^ k = -1 := (sq_eq_one_iff.mp hsq).resolve_left hk1
  have hgX : g ∣ X ^ p - C 1 := by
    rw [C_1]
    exact hgd.trans (cyclotomic.dvd_X_pow_sub_one p K)
  refine dualPoly_eq_self_of_dvd_id hp hg hgm hgX (j := k) ?_
  have h1 : ((Nat.card K ^ k + 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, Nat.cast_pow, ← ht, hneg, Nat.cast_one]
    exact neg_add_cancel _
  exact (ZMod.natCast_eq_zero_iff _ _).mp h1

end Recip

section Pieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

omit [Finite K] [CharP K 2] in
theorem nondegOn_inf_selfDual' (H : UnitaryPrimaryData σ B x) {g : K[X]}
    (hg : g ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly σ g = g)
    {U : Submodule K V} (hU : NondegOn B U) (hUx : ∀ u ∈ U, (x : Module.End K V) u ∈ U) :
    NondegOn B (primaryComponent (x : Module.End K V) g ⊓ U) := by
  classical
  intro m hm hn
  refine hU m hm.2 fun u hu => ?_
  rw [eq_sum_primaryProjection H.squarefree u, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hbU : primaryProjection (x : Module.End K V) b u ∈ U := aeval_mem_of_inv hUx _ hu
  by_cases hbg : b = g
  · subst hbg
    exact hn _ ⟨primaryProjection_mem H.squarefree hb u, hbU⟩
  · refine orthogonal_of_ne_dualPoly H hb hg (fun hgb => hbg ?_)
      (primaryProjection_mem H.squarefree hb u) hm.1
    rw [← dualPoly_dualPoly_of_mem H hb, ← hgb, hself]

omit [Finite K] [CharP K 2] in
theorem exists_pair_vec' (H : UnitaryPrimaryData σ B x) {g : K[X]}
    (hg : g ∈ primaryFactors (x : Module.End K V)) {U : Submodule K V} (hnd : NondegOn B U)
    (hinv : ∀ u ∈ U, (x : Module.End K V) u ∈ U) {w : V} (hwU : w ∈ U) (hw0 : w ≠ 0)
    (hwg : aeval (x : Module.End K V) g w = 0) :
    ∃ w' : primaryComponent (x : Module.End K V) (dualPoly σ g), (w' : V) ∈ U ∧ B w w' ≠ 0 := by
  classical
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, B w u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (hnd w hwU fun u hu' => by rw [← H.symm.eq w u, hcon u hu', map_zero])
  have hg' := dualPoly_mem_primaryFactors H hg
  refine ⟨⟨primaryProjection (x : Module.End K V) (dualPoly σ g) u,
    primaryProjection_mem H.squarefree hg' u⟩, aeval_mem_of_inv hinv _ huU, fun h0 => hu ?_⟩
  rw [eq_sum_primaryProjection H.squarefree u, map_sum,
    Finset.sum_eq_single (dualPoly σ g)]
  · exact h0
  · intro b hb hbne
    exact orthogonal_of_ne_dualPoly H hg hb hbne (mem_primaryComponent.mpr hwg)
      (primaryProjection_mem H.squarefree hb u)
  · intro hnot
    exact absurd hg' hnot

end Pieces

section AltPieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
  {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K}

@[expose] noncomputable def toUnitGL (g : GL (Fin d) K) :
    LinearMap.GeneralLinearGroup K (Fin d → K) :=
  ⟨glin g, glin g⁻¹, by rw [← glin_mul, mul_inv_cancel, glin_one],
    by rw [← glin_mul, inv_mul_cancel, glin_one]⟩

omit [Finite K] [CharP K 2] in
theorem coe_toUnitGL (g : GL (Fin d) K) :
    ((toUnitGL g : LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) =
      glin g := rfl

omit [Finite K] in
theorem unitaryPrimaryData_glin (hB : B.IsSymm) (hBsep : ∀ v, (∀ w, B v w = 0) → v = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : GL (Fin d) K}
    (hyB : ∀ v w, B (glin y v) (glin y w) = B v w) (hyp : y ^ p = 1) :
    UnitaryPrimaryData (RingHom.id K) B (toUnitGL y) where
  invol := fun _ => rfl
  symm := hB
  sep := hBsep
  isom := hyB
  squarefree := by
    have hpK : (p : K) ≠ 0 := by
      rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
      exact one_ne_zero
    refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - 1) ?_ ?_
    · have := (separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree
      rwa [map_one] at this
    · rw [coe_toUnitGL, map_sub, map_pow, aeval_X, map_one, ← glin_pow, hyp, glin_one, sub_self]

theorem lcm_dvd_finrank_grng (hB : B.IsSymm) (hBalt : ∀ v, B v v = 0)
    (hBsep : ∀ v, (∀ w, B v w = 0) → v = 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : GL (Fin d) K} (hyB : ∀ v w, B (glin y v) (glin y w) = B v w) (hyp : y ^ p = 1) :
    Nat.lcm 2 (OrdPNS.ordQ K p) ∣ finrank K (grng y) := by
  have hpK : (p : K) ≠ 0 := by
    rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hlinp : glin y ^ p = 1 := by rw [← glin_pow, hyp, glin_one]
  have hnd : NondegOn B (grng y) := nondegOn_range hB hBsep hyB (hp.odd_of_ne_two hp2) hlinp
  have hinv : ∀ u ∈ grng y, glin y u ∈ grng y := by
    rintro _ ⟨v, rfl⟩
    refine ⟨glin y v, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul]
  refine Nat.lcm_dvd (even_iff_two_dvd.mp (even_finrank_of_nondegOn hB hBalt hnd)) ?_
  refine ordQ_dvd_finrank_of_fpf hp hpK (grng y) ((glin y).restrict hinv)
    (OrdPNS.restrict_pow_eq_one hlinp hinv) ?_
  intro w hw
  exact Subtype.ext (eq_zero_of_fixed_range (hp.odd_of_ne_two hp2) hlinp w.2
    (congrArg Subtype.val hw))

theorem finrank_le_lcm_of_minimal (hB : B.IsSymm) (hBsep : ∀ v, (∀ w, B v w = 0) → v = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : GL (Fin d) K}
    (hyB : ∀ v w, B (glin y v) (glin y w) = B v w) (hyp : y ^ p = 1)
    {U : Submodule K (Fin d → K)} (hUle : U ≤ grng y) (hU0 : U ≠ ⊥) (hUnd : NondegOn B U)
    (hUy : ∀ u ∈ U, glin y u ∈ U)
    (hmin : ∀ W : Submodule K (Fin d → K), W ≤ U → W ≠ ⊥ → NondegOn B W →
      (∀ w ∈ W, glin y w ∈ W) → W = U) :
    finrank K U ≤ Nat.lcm 2 (OrdPNS.ordQ K p) := by
  classical
  have hpK : (p : K) ≠ 0 := by
    rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hp1 : 1 ≤ p := hp.one_lt.le
  set x := toUnitGL y with hx
  have H : UnitaryPrimaryData (RingHom.id K) B x := unitaryPrimaryData_glin hB hBsep hp hp2 hyB hyp
  have hX : (x : Module.End K (Fin d → K)) = glin y := coe_toUnitGL y
  have hlinp : glin y ^ p = 1 := by rw [← glin_pow, hyp, glin_one]
  have hfix : ∀ u ∈ U, glin y u = u → u = 0 := fun u hu hyu =>
    eq_zero_of_fixed_range (hp.odd_of_ne_two hp2) hlinp (hUle hu) hyu
  set yU : Module.End K U := (glin y).restrict hUy with hyU
  have hyUp : yU ^ p = 1 := OrdPNS.restrict_pow_eq_one hlinp hUy
  have hyU1 : yU ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact hu0 (hfix u hu (congrArg Subtype.val (LinearMap.congr_fun h1 ⟨u, hu⟩)))
  obtain ⟨g₀, hg₀, hg₀d, hg₀k⟩ := OrdPNS.exists_irreducible_ker_ne_bot hp hyUp hyU1
  obtain ⟨g, hg, hgm, hgg₀, hker⟩ := exists_monic_of_irreducible (V := U) hg₀
  have : Fact (Irreducible g) := ⟨hg⟩
  have hgd : g ∣ cyclotomic p K := hgg₀.trans hg₀d
  have hgk : LinearMap.ker (aeval yU g) ≠ ⊥ := by rw [hker yU]; exact hg₀k
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hgk
  set w : Fin d → K := (w₀ : Fin d → K) with hw
  have hwU : w ∈ U := w₀.2
  have hw0 : w ≠ 0 := fun h0 => hw₀0 (Subtype.ext h0)
  have hwg : aeval (x : Module.End K (Fin d → K)) g w = 0 := by
    have h1 := OrdPNS.coe_aeval_restrict_apply hUy g w₀
    rw [LinearMap.mem_ker.mp hw₀, Submodule.coe_zero] at h1
    rw [hX, hw, ← h1]
  have hgx : g ∈ primaryFactors (x : Module.End K (Fin d → K)) :=
    mem_primaryFactors_of_ker hg hgm hw0 hwg
  have hd := OrdPNS.natDegree_eq_ordQ hp hpK hg hgd
  have hepos := OrdPNS.ordQ_pos (K := K) hp hpK
  have hlcm : 0 < Nat.lcm 2 (OrdPNS.ordQ K p) := Nat.lcm_pos two_pos hepos
  have hUx : ∀ u ∈ U, (x : Module.End K (Fin d → K)) u ∈ U := by rw [hX]; exact hUy
  have hxB : ∀ v w, B ((x : Module.End K (Fin d → K)) v) ((x : Module.End K (Fin d → K)) w) =
      B v w := by rw [hX]; exact hyB
  have hxp : (x : Module.End K (Fin d → K)) ^ p = 1 := by rw [hX]; exact hlinp
  have hxinv : ∀ (u : Fin d → K), ∀ v ∈ cyc (x : Module.End K (Fin d → K)) u,
      (x : Module.End K (Fin d → K)) v ∈ cyc (x : Module.End K (Fin d → K)) u :=
    fun u => cyc_invariant _ u
  by_cases hself : dualPoly (RingHom.id K) g = g
  ·
    set Wg := primaryComponent (x : Module.End K (Fin d → K)) g ⊓ U with hWg
    have hWnd : NondegOn B Wg := nondegOn_inf_selfDual' H hgx hself hUnd hUx
    have hWx : ∀ v ∈ Wg, (x : Module.End K (Fin d → K)) v ∈ Wg := fun v hv =>
      ⟨apply_mem_primaryComponent (Commute.refl _) hv.1, hUx v hv.2⟩
    have hwW : w ∈ Wg := ⟨mem_primaryComponent.mpr hwg, hwU⟩
    obtain ⟨u, huW, hu⟩ : ∃ u ∈ Wg, B u ((x : Module.End K (Fin d → K)) u) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hkey : ∀ v ∈ Wg, (x : Module.End K (Fin d → K)) v =
          ((x : Module.End K (Fin d → K)) ^ (p - 1)) v := by
        intro v hv
        have hmem : (x : Module.End K (Fin d → K)) v -
            ((x : Module.End K (Fin d → K)) ^ (p - 1)) v ∈ Wg :=
          Wg.sub_mem (hWx v hv) (invariant_pow hWx (p - 1) v hv)
        refine sub_eq_zero.mp (hWnd _ hmem fun u hu => ?_)
        have h1₀ := hcon (u + v) (Wg.add_mem hu hv)
        have e1 : B (u + v) ((x : Module.End K (Fin d → K)) (u + v)) =
            B u ((x : Module.End K (Fin d → K)) u) + B u ((x : Module.End K (Fin d → K)) v) +
              (B v ((x : Module.End K (Fin d → K)) u) +
                B v ((x : Module.End K (Fin d → K)) v)) := by
          simp only [map_add, LinearMap.add_apply]
          abel
        rw [e1, hcon u hu, hcon v hv, zero_add, add_zero] at h1₀
        have h1 : B u ((x : Module.End K (Fin d → K)) v) =
            B v ((x : Module.End K (Fin d → K)) u) := by
          rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1₀
          exact h1₀
        have h2 : B v ((x : Module.End K (Fin d → K)) u) =
            B u (((x : Module.End K (Fin d → K)) ^ (p - 1)) v) := by
          have h3 := hB.eq v ((x : Module.End K (Fin d → K)) u)
          rw [RingHom.id_apply] at h3
          rw [h3]
          exact apply_left_eq hxB hp1 hxp u v
        rw [map_sub, h1, h2, sub_self]
      have hsq : ∀ v ∈ Wg, ((x : Module.End K (Fin d → K)) ^ 2) v = v := by
        intro v hv
        have h1 := congrArg (x : Module.End K (Fin d → K)) (hkey v hv)
        have h2 : (x : Module.End K (Fin d → K)) (((x : Module.End K (Fin d → K)) ^ (p - 1)) v) =
            v := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp1, hxp,
            Module.End.one_apply]
        rw [h2] at h1
        rw [sq, Module.End.mul_apply]
        exact h1
      have hev : ∀ k : ℕ, ∀ v ∈ Wg, ((x : Module.End K (Fin d → K)) ^ (2 * k)) v = v := by
        intro k
        induction k with
        | zero => intro v _; rw [Nat.mul_zero, pow_zero, Module.End.one_apply]
        | succ k ih =>
          intro v hv
          rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hsq v hv, ih v hv]
      obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2)
      have hxw : (x : Module.End K (Fin d → K)) w = w := by
        have h1 := hev (k + 1) w hwW
        rw [show 2 * (k + 1) = p + 1 by omega, pow_succ, Module.End.mul_apply, hxp,
          Module.End.one_apply] at h1
        exact h1
      exact hw0 (hfix w hwU (by rw [← hX]; exact hxw))
    have hug : aeval (x : Module.End K (Fin d → K)) g u = 0 := mem_primaryComponent.mp huW.1
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hu (by rw [map_zero, LinearMap.zero_apply])
    set Z := cyc (x : Module.End K (Fin d → K)) u with hZ
    have huZ : u ∈ Z := by simpa using pow_mem_cyc (x : Module.End K (Fin d → K)) u 0
    obtain ⟨R, hR⟩ : ∃ R : Submodule K (Fin d → K), R = Z ⊓ Z.orthogonalBilin B := ⟨_, rfl⟩
    have hRZle : R ≤ Z := by rw [hR]; exact inf_le_left
    have hRo : ∀ z ∈ R, ∀ z' ∈ Z, B z' z = 0 := by
      intro z hz z' hz'
      rw [hR] at hz
      exact (Submodule.mem_orthogonalBilin.mp hz.2) z' hz'
    have hRmem : ∀ z ∈ Z, (∀ z' ∈ Z, B z' z = 0) → z ∈ R := by
      intro z hz hz'
      rw [hR]
      exact ⟨hz, Submodule.mem_orthogonalBilin.mpr hz'⟩
    have hRx : ∀ z ∈ R, (x : Module.End K (Fin d → K)) z ∈ R := by
      intro z hz
      refine hRmem _ (hxinv u z (hRZle hz)) fun z' hz' => ?_
      have h1 : (x : Module.End K (Fin d → K)) (((x : Module.End K (Fin d → K)) ^ (p - 1)) z') =
          z' := by
        rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp1, hxp,
          Module.End.one_apply]
      rw [← h1, hxB]
      exact hRo z hz _ (invariant_pow (hxinv u) (p - 1) z' hz')
    have hR0 : R = ⊥ := by
      by_contra hne
      have hRZ : R = Z := eq_cyc_of_le hg hug hRZle hRx hne
      have hxu : (x : Module.End K (Fin d → K)) u ∈ R := by rw [hRZ]; exact hxinv u u huZ
      exact hu (hRo _ hxu u huZ)
    have hZnd : NondegOn B Z := by
      intro m hm hn
      have hmR := hRmem m hm hn
      rw [hR0, Submodule.mem_bot] at hmR
      exact hmR
    have heq : Z = U := by
      refine hmin _ (cyc_le hUx huW.2) ?_ hZnd ?_
      · intro hbot
        apply hu0
        rw [hbot] at huZ
        exact (Submodule.mem_bot K).mp huZ
      · intro v hv
        rw [← hX]
        exact hxinv _ v hv
    rw [← heq]
    calc finrank K Z ≤ g.natDegree := OrdPNsU.finrank_cyc_le _ hgm hg.ne_one hug
      _ = OrdPNS.ordQ K p := hd
      _ ≤ Nat.lcm 2 (OrdPNS.ordQ K p) := Nat.le_of_dvd hlcm (Nat.dvd_lcm_right 2 _)
  ·
    have hodd : Odd (OrdPNS.ordQ K p) := by
      rcases Nat.even_or_odd (OrdPNS.ordQ K p) with he | he
      · exact absurd (dualPoly_eq_self_of_even hp hp2 hg hgm hgd he) hself
      · exact he
    obtain ⟨w', hw'U, hww'⟩ := exists_pair_vec' H hgx hUnd hUx hwU hw0 hwg
    have hg'x : dualPoly (RingHom.id K) g ∈ primaryFactors (x : Module.End K (Fin d → K)) :=
      dualPoly_mem_primaryFactors H hgx
    have hg'irr : Irreducible (dualPoly (RingHom.id K) g) := irreducible_of_mem_primaryFactors hg'x
    have hne : g ≠ dualPoly (RingHom.id K) g := fun h' => hself h'.symm
    have hgg : dualPoly (RingHom.id K) (dualPoly (RingHom.id K) g) = g :=
      dualPoly_dualPoly_of_mem H hgx
    have hne' : dualPoly (RingHom.id K) g ≠
        dualPoly (RingHom.id K) (dualPoly (RingHom.id K) g) := by rw [hgg]; exact hself
    have hVg : ∀ (a : K[X]) (v : Fin d → K),
        v ∈ primaryComponent (x : Module.End K (Fin d → K)) a →
          (x : Module.End K (Fin d → K)) v ∈ primaryComponent (x : Module.End K (Fin d → K)) a :=
      fun a v hv => apply_mem_primaryComponent (Commute.refl _) hv
    have hwV : w ∈ primaryComponent (x : Module.End K (Fin d → K)) g :=
      mem_primaryComponent.mpr hwg
    have hiso : ∀ a ∈ cyc (x : Module.End K (Fin d → K)) w,
        ∀ b ∈ cyc (x : Module.End K (Fin d → K)) w, B a b = 0 := fun a ha b hb =>
      isotropic_primaryComponent H hgx hne (cyc_le (hVg g) hwV ha) (cyc_le (hVg g) hwV hb)
    have hiso' : ∀ a ∈ cyc (x : Module.End K (Fin d → K)) (w' : Fin d → K),
        ∀ b ∈ cyc (x : Module.End K (Fin d → K)) (w' : Fin d → K), B a b = 0 := fun a ha b hb =>
      isotropic_primaryComponent H hg'x hne' (cyc_le (hVg _) w'.2 ha) (cyc_le (hVg _) w'.2 hb)
    have hnd := nondegOn_cyc_sup H.symm hxB hp1 hxp hg hg'irr hwg (mem_primaryComponent.mp w'.2)
      hww' hiso hiso'
    have heq : cyc (x : Module.End K (Fin d → K)) w ⊔
        cyc (x : Module.End K (Fin d → K)) (w' : Fin d → K) = U := by
      refine hmin _ (sup_le (cyc_le hUx hwU) (cyc_le hUx hw'U)) ?_ hnd ?_
      · intro hbot
        apply hw0
        have h1 : w ∈ cyc (x : Module.End K (Fin d → K)) w ⊔
            cyc (x : Module.End K (Fin d → K)) (w' : Fin d → K) :=
          Submodule.mem_sup_left (by simpa using pow_mem_cyc (x : Module.End K (Fin d → K)) w 0)
        rw [hbot, Submodule.mem_bot] at h1
        exact h1
      · intro v hv
        rw [← hX]
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.add_mem_sup (hxinv w a ha) (hxinv _ b hb)
    rw [← heq]
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (cyc (x : Module.End K (Fin d → K)) w)
      (cyc (x : Module.End K (Fin d → K)) (w' : Fin d → K))
    have h2 := OrdPNsU.finrank_cyc_le (x : Module.End K (Fin d → K)) hgm hg.ne_one hwg
    have h3 := OrdPNsU.finrank_cyc_le (x : Module.End K (Fin d → K))
      (monic_of_mem_primaryFactors hg'x) hg'irr.ne_one (mem_primaryComponent.mp w'.2)
    have h4 : (dualPoly (RingHom.id K) g).natDegree = g.natDegree :=
      natDegree_dualPoly (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree hgx)
    have h5 : Nat.lcm 2 (OrdPNS.ordQ K p) = 2 * OrdPNS.ordQ K p :=
      Nat.Coprime.lcm_eq_mul (Nat.coprime_two_left.mpr hodd)
    rw [h5]
    omega

end AltPieces

end OrdPNsGen

end CFSG.StandardType
