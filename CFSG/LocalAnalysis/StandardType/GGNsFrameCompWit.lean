module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompTwo

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.OddIso Multiplicative

@[expose] def supp {r p : ℕ} (t : Fin r → ZMod p) : Finset (Fin r) :=
  Finset.univ.filter fun i => t i ≠ 0

theorem mem_supp {r p : ℕ} {t : Fin r → ZMod p} {i : Fin r} : i ∈ supp t ↔ t i ≠ 0 := by
  simp [supp]

section Det

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_algebraMap_eq (z : AdjoinRoot (X - C (1 : K))) :
    ∃ c : K, algebraMap K (AdjoinRoot (X - C (1 : K))) c = z := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨P.eval 1, ?_⟩
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk]
  rw [show C (P.eval 1) - P = -(P - C (P.eval 1)) by ring]
  exact dvd_neg.mpr (X_sub_C_dvd_sub_C_eval (p := P) (a := (1 : K)))

theorem blockDetHom_X_sub_C_one_eq_one {y : LinearMap.GeneralLinearGroup K V}
    (hsq : Squarefree (minpoly K (y : Module.End K V)))
    (hmem : (X - C (1 : K) : K[X]) ∈ primaryFactors (y : Module.End K V)) {g : gl_centralizer y}
    (htriv : ∀ b ∈ primaryFactors (y : Module.End K V), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (y : Module.End K V) b,
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v)
    (hdet : LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1) :
    blockDetHom y (X - C 1) g = 1 := by
  have : Fact (Irreducible (X - C (1 : K))) := ⟨irreducible_X_sub_C 1⟩
  have hcomm : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (y : Module.End K V) := mem_gl_centralizer.mp g.2
  set γ := ((blockRestrict y (X - C 1) g : blockGL (y : Module.End K V) (X - C 1)) :
    Module.End (AdjoinRoot (X - C (1 : K))) (primaryComponent (y : Module.End K V) (X - C 1)))
    with hγ
  have h1 := det_restrictScalars_blockGL (x := (y : Module.End K V)) (X - C (1 : K)) γ
  have h2 : γ.restrictScalars K = ((g : LinearMap.GeneralLinearGroup K V) :
      Module.End K V).restrict (fun _ hv => apply_mem_primaryComponent hcomm hv :
        ∀ v ∈ primaryComponent (y : Module.End K V) (X - C 1),
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈
            primaryComponent (y : Module.End K V) (X - C 1)) := by
    ext v
    rfl
  have h3 := det_eq_det_restrict_of_trivial_off hsq hmem hcomm htriv
  rw [h2, ← h3, hdet] at h1
  obtain ⟨c, hc⟩ := exists_algebraMap_eq (LinearMap.det γ)
  have hfin : Module.finrank K (AdjoinRoot (X - C (1 : K))) = 1 := by
    rw [(AdjoinRoot.powerBasis (X_sub_C_ne_zero (1 : K))).finrank, AdjoinRoot.powerBasis_dim,
      natDegree_X_sub_C]
  rw [← hc, Algebra.norm_algebraMap, hfin, pow_one] at h1
  apply Units.ext
  change LinearMap.det γ = 1
  rw [← hc, ← h1]
  exact map_one _

end Det

section RootsOfUnity

theorem exists_pow_mul_pow_eq_one {E : Type*} [Field E] {p : ℕ} (hp : p.Prime) {α β : Eˣ}
    (hα : α ^ p = 1) (hβ : β ^ p = 1) :
    ∃ u v : ℕ, ((u : ZMod p) ≠ 0 ∨ (v : ZMod p) ≠ 0) ∧ α ^ u * β ^ v = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hα1 : α = 1
  · exact ⟨1, 0, Or.inl (by simp), by simp [hα1]⟩
  have hord : orderOf α = p := orderOf_eq_prime hα hα1
  have hle : Subgroup.zpowers α ≤ rootsOfUnity p E := by
    rw [Subgroup.zpowers_le]
    exact (mem_rootsOfUnity p α).mpr hα
  have hcard : Nat.card (rootsOfUnity p E) ≤ Nat.card (Subgroup.zpowers α) := by
    rw [Nat.card_zpowers, hord]
    have : NeZero p := ⟨hp.ne_zero⟩
    exact card_rootsOfUnity E p
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hβz : β ∈ Subgroup.zpowers α := by rw [heq]; exact (mem_rootsOfUnity p β).mpr hβ
  have hfin : IsOfFinOrder α := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hα⟩
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff β α).mp (hfin.mem_powers_iff_mem_zpowers.mpr hβz)
  refine ⟨m, p - 1, Or.inr ?_, ?_⟩
  · intro h0
    have h1 := (ZMod.natCast_eq_zero_iff (p - 1) p).mp h0
    have h2 := hp.two_le
    have h3 := Nat.le_of_dvd (by omega) h1
    omega
  · rw [hm, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hβ]

end RootsOfUnity

section Witness

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)} {x : ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem det_lin (g : ↥(unitarySU 2 f K n)) (h : UnitaryFieldData 2 f K) :
    LinearMap.det (lin g) = 1 := by
  have h1 : lin g = Matrix.toLin' (mx g) := LinearMap.ext fun v => by
    rw [lin_apply, Matrix.toLin'_apply]
  rw [h1, LinearMap.det_toLin']
  exact ((mem_unitarySU_iff h).mp g.2).1

theorem lin_pow_apply_of_fix {g : ↥(unitarySU 2 f K n)} {v : Fin n → K} (hv : lin g v = v)
    (k : ℕ) : lin (g ^ k) v = v := by
  induction k with
  | zero => rw [pow_zero, lin_one]; rfl
  | succ k ih => rw [pow_succ, lin_mul, Module.End.mul_apply, hv, ih]

theorem mem_sb_zero_of_fix (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hxA : x ∈ A)
    (i₀ : Fin F.r) (hfix : ∀ u ∈ rng (F.y i₀), lin x u = u) : F.b i₀ ∈ sb h x (X - C 1) := by
  have hp := hA.prime
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  have hsq := H.squarefree
  have hbC := mem_centralizer_of_mem hA hxA (F.b_mem i₀)
  have hU := toUnitHom_mem_unitaryCentralizer (h := h) hbC
  have hUfix : ∀ u ∈ rng (F.y i₀), u ∈ primaryComponent (Xe x) (X - C 1) := by
    intro u hu
    rw [primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    exact hfix u hu
  have hmem : (X - C 1 : K[X]) ∈ primaryFactors (Xe x) := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (F.ne_bot i₀)
    exact mem_primaryFactors_of_ker (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0
      (mem_primaryComponent.mp (hUfix u hu))
  have htriv : ∀ b ∈ primaryFactors (Xe x), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (Xe x) b, lin (F.b i₀) v = v := by
    intro b hb hb1 v hv
    refine F.b_off i₀ v (Submodule.mem_orthogonalBilin.mpr fun u hu => ?_)
    exact orthogonal_of_ne_dualPoly H hmem hb (by rw [dualPoly_X_sub_C_one]; exact hb1)
      (hUfix u hu) hv
  refine mem_specialBlock.mpr ⟨⟨hU, fun b hb hbS v hv => htriv b hb ?_ v hv⟩, hU.2, ?_⟩
  · intro e
    exact hbS (Or.inl e)
  · exact blockDetHom_X_sub_C_one_eq_one hsq hmem htriv (det_lin _ h)

theorem exists_mem_sb_class (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hxA : x ∈ A)
    (a : primaryFactors (Xe x)) (ha : IsGoodBlock h (toUnitHom x) a) (ha1 : (a : K[X]) ≠ X - C 1) :
    ∃ t : Fin F.r → ZMod p, t ≠ 0 ∧ (supp t).card ≤ 2 ∧ F.ι (ofAdd t) ∈ sb h x a := by
  classical
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  obtain ⟨j, j', hjj, hj, hj'⟩ := exists_two_pieces_orbW F hA hxA a ha ha1
  have hgl : ∀ c ∈ A, toUnitHom c ∈ gl_centralizer (toUnitHom x) := fun c hc =>
    (toUnitHom_mem_unitaryCentralizer (h := h) (mem_centralizer_of_mem hA hxA hc)).2
  set δ := blockDetHom (toUnitHom x) (a : K[X]) with hδ
  set α := δ ⟨toUnitHom (F.b j), hgl _ (F.b_mem j)⟩ with hαdef
  set β := δ ⟨toUnitHom (F.b j'), hgl _ (F.b_mem j')⟩ with hβdef
  have hpow : ∀ i : Fin F.r, (⟨toUnitHom (F.b i), hgl _ (F.b_mem i)⟩ :
      gl_centralizer (toUnitHom x)) ^ p = 1 := fun i =>
    Subtype.ext (by
      change toUnitHom (F.b i) ^ p = 1
      rw [← map_pow, hA.pow _ (F.b_mem i), map_one])
  have hα : α ^ p = 1 := by rw [hαdef, ← map_pow, hpow, map_one]
  have hβ : β ^ p = 1 := by rw [hβdef, ← map_pow, hpow, map_one]
  obtain ⟨u, v, huv, hαβ⟩ := exists_pow_mul_pow_eq_one hp hα hβ
  set t : Fin F.r → ZMod p := Pi.single j (u : ZMod p) + Pi.single j' (v : ZMod p) with ht
  have hιt : F.ι (ofAdd t) = F.b j ^ u * F.b j' ^ v := by
    rw [ht, ofAdd_add, map_mul, F.ι_single_pow, F.ι_single_pow]
  have htA : F.ι (ofAdd t) ∈ A := by
    rw [hιt]
    exact A.mul_mem (A.pow_mem (F.b_mem j) u) (A.pow_mem (F.b_mem j') v)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro h0
    rcases huv with hu | hv
    · apply hu
      have := congrFun h0 j
      simpa [ht, Pi.single_eq_of_ne hjj] using this
    · apply hv
      have := congrFun h0 j'
      simpa [ht, Pi.single_eq_of_ne (Ne.symm hjj)] using this
  · have hsub : supp t ⊆ {j, j'} := by
      intro i hi
      rw [mem_supp] at hi
      by_contra hne
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
      exact hi (by simp [ht, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2])
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hU := toUnitHom_mem_unitaryCentralizer (h := h) (mem_centralizer_of_mem hA hxA htA)
    refine mem_specialBlock.mpr ⟨⟨hU, fun b hb hbS w hw => ?_⟩, hU.2, ?_⟩
    ·
      have hwW : w ∈ (orbW h x (a : K[X])).orthogonalBilin (stdHermForm h n) := by
        refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
        obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hm
        have had := dualPoly_mem_primaryFactors H a.2
        have h1 : stdHermForm h n m₁ w = 0 :=
          orthogonal_of_ne_dualPoly H a.2 hb (fun e => hbS (Or.inr e)) hm₁ hw
        have h2 : stdHermForm h n m₂ w = 0 :=
          orthogonal_of_ne_dualPoly H had hb
            (fun e => hbS (Or.inl (e.trans (dualPoly_dualPoly_of_mem H a.2)))) hm₂ hw
        change stdHermForm h n (m₁ + m₂) w = 0
        rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
      change lin (F.ι (ofAdd t)) w = w
      rw [hιt, lin_mul, Module.End.mul_apply, lin_pow_apply_of_fix (hj' w hwW),
        lin_pow_apply_of_fix (hj w hwW)]
    · have hsplit : (⟨toUnitHom (F.ι (ofAdd t)), hU.2⟩ : gl_centralizer (toUnitHom x)) =
          (⟨toUnitHom (F.b j), hgl _ (F.b_mem j)⟩ : gl_centralizer (toUnitHom x)) ^ u *
            (⟨toUnitHom (F.b j'), hgl _ (F.b_mem j')⟩ : gl_centralizer (toUnitHom x)) ^ v :=
        Subtype.ext (by
          change toUnitHom (F.ι (ofAdd t)) = toUnitHom (F.b j) ^ u * toUnitHom (F.b j') ^ v
          rw [hιt, map_mul, map_pow, map_pow])
      change δ _ = 1
      rw [hsplit, map_mul, map_pow, map_pow]
      exact hαβ

theorem not_dvd_card_sb_zero (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hxA : x ∈ A)
    (hnz : ∀ i, ∃ u ∈ rng (F.y i), lin x u ≠ u) : ¬ p ∣ Nat.card (sb h x (X - C 1)) := by
  classical
  intro hdvd
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite K := h.finite
  have : Finite ↥(unitarySU 2 f K n) := Subtype.finite
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  have hsq := H.squarefree
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(sb h x (X - C 1))) p hdvd
  have hgord : orderOf (g : ↥(unitarySU 2 f K n)) = p := by rw [Subgroup.orderOf_coe, hg]
  have hgp : (g : ↥(unitarySU 2 f K n)) ^ p = 1 := hgord ▸ pow_orderOf_eq_one _
  have hxr : x ∈ F.ι.range := by rw [F.ι_range]; exact hxA
  obtain ⟨s, hs⟩ := hxr
  have hβ : ∀ i, toAdd s i ≠ 0 := by
    intro i hsi
    obtain ⟨u, hu, hux⟩ := hnz i
    apply hux
    rw [← hs, F.ι_on s i u hu, hsi, ZMod.val_zero, pow_zero, lin_one]
    rfl
  have hfixA : ∀ v, lin x v = v → ∀ c ∈ A, lin c v = v := by
    intro v hv c hc
    have hcr : c ∈ F.ι.range := by rw [F.ι_range]; exact hc
    obtain ⟨s', rfl⟩ := hcr
    have h1 := (F.ι_fix s v).mp (by rw [hs]; exact hv)
    exact (F.ι_fix s' v).mpr fun j _ => h1 j (hβ j)
  have hgC := sb_le_centralizer g.2
  have htrivg := (mem_specialBlock.mp (mem_sb.mp g.2)).1.2
  have hoff : ∀ b ∈ primaryFactors (Xe x), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (Xe x) b, lin (g : ↥(unitarySU 2 f K n)) v = v := by
    intro b hb hb1 v hv
    refine htrivg b hb (fun hbS => ?_) v hv
    rcases hbS with hbS | hbS
    · exact hb1 hbS
    · rw [dualPoly_X_sub_C_one] at hbS
      exact hb1 hbS
  have hfixV : ∀ v ∈ primaryComponent (Xe x) (X - C 1), lin x v = v := by
    intro v hv
    rw [primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hcommA : ∀ c ∈ A, (g : ↥(unitarySU 2 f K n)) * c = c * g := by
    intro c hc
    apply toUnitHom_injective
    rw [map_mul, map_mul]
    refine Units.ext (ext_primaryComponent hsq fun b hb v hv => ?_)
    change lin (g : ↥(unitarySU 2 f K n)) (lin c v) = lin c (lin (g : ↥(unitarySU 2 f K n)) v)
    by_cases hb1 : b = X - C 1
    · subst hb1
      have hgv := lin_mem_primaryComponent hgC hv
      rw [hfixA v (hfixV v hv) c hc, hfixA _ (hfixV _ hgv) c hc]
    · have hcv := lin_mem_primaryComponent (mem_centralizer_of_mem hA hxA hc) hv
      rw [hoff b hb hb1 _ hcv, hoff b hb hb1 v hv]
  have hgA : (g : ↥(unitarySU 2 f K n)) ∈ A := hA.max _ hgp fun c hc => hcommA c hc
  have hgr : (g : ↥(unitarySU 2 f K n)) ∈ F.ι.range := by rw [F.ι_range]; exact hgA
  obtain ⟨s', hs'⟩ := hgr
  have hgU : ∀ i, ∀ u ∈ rng (F.y i), lin (F.ι s') u = u := by
    intro i u hu
    have hkp : ¬ p ∣ (toAdd s i).val := by
      intro hdvd'
      apply hβ i
      rw [← ZMod.natCast_zmod_val (toAdd s i)]
      exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd'
    rw [hs']
    conv_lhs => rw [eq_sum_primaryProjection hsq u]
    conv_rhs => rw [eq_sum_primaryProjection hsq u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hb1 : b = X - C 1
    · subst hb1
      have hm : primaryProjection (Xe x) (X - C 1) u ∈ rng (F.y i) :=
        aeval_mem_of_inv (X := Xe x) (rng_inv hA (F.y_mem i) hxA) _ hu
      have hm' := hfixV _ (primaryProjection_mem hsq hb u)
      have h0 : primaryProjection (Xe x) (X - C 1) u = 0 := by
        refine eq_zero_of_pow_fix h hA (F.y_mem i) hkp hm ?_
        rw [← F.ι_on s i _ hm, hs]
        exact hm'
      rw [h0, map_zero]
    · exact hoff b hb hb1 _ (primaryProjection_mem hsq hb u)
  have hs'0 : s' = 1 := by
    apply toAdd.injective
    funext i
    exact F.coord_eq_zero hA (hgU i)
  rw [hs'0, map_one] at hs'
  rw [← hs', orderOf_one] at hgord
  exact hp.one_lt.ne hgord

end Witness

end NsFrameComp

end CFSG.StandardType
