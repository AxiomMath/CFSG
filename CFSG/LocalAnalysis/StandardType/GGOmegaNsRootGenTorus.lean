module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial QuadraticMap CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}
  {k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)}

private theorem noncommProd_apply_of_eq_of_ne {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → V ≃ₗ[F] V)
    (hcomm : (s : Set ι).Pairwise fun x y => Commute (g x) (g y)) {c : ι} (hc : c ∈ s)
    {x : V} (h : ∀ i ∈ s, i ≠ c → g i x = x) :
    (s.noncommProd g hcomm) x = g c x := by
  induction s using Finset.induction_on with
  | empty => exact absurd hc (Finset.notMem_empty c)
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem s a g hcomm ha]
    have hcomm' : (s : Set ι).Pairwise fun x y => Commute (g x) (g y) :=
      hcomm.mono fun _ hy => Finset.mem_insert_of_mem hy
    by_cases hac : a = c
    · subst hac
      have h1 : (s.noncommProd g hcomm') x = x := by
        refine Finset.noncommProd_induction s g hcomm' (fun y => y x = x) ?_
          rfl ?_
        · intro u v hu hv
          rw [LinearEquiv.mul_apply, hv, hu]
        · intro i hi
          exact h i (Finset.mem_insert_of_mem hi) fun hia => ha (hia ▸ hi)
      rw [LinearEquiv.mul_apply, h1]
    · have hcs : c ∈ s := by
        rcases Finset.mem_insert.mp hc with hca | hcs
        · exact absurd hca.symm hac
        · exact hcs
      have h1 : (s.noncommProd g hcomm') x = g c x :=
        ih hcomm' hcs fun i hi hic => h i (Finset.mem_insert_of_mem hi) hic
      rw [LinearEquiv.mul_apply, h1]
      have hcomm_ac : Commute (g a) (g c) :=
        hcomm (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hcs) hac
      rw [← LinearEquiv.mul_apply, hcomm_ac.eq, LinearEquiv.mul_apply,
        h a (Finset.mem_insert_self a s) hac]

private theorem pow_apply_eq_of_apply_eq {g : V ≃ₗ[F] V} {x : V} (h : g x = x) (n : ℕ) :
    (g ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]

private theorem tau_mem_closure_image_of_eq_one {G : Type*} [Group G] {p k : ℕ} [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c)
    (f : Fin k → Multiplicative (ZMod p)) (s : Finset (Fin k))
    (h : ∀ c, c ∉ s → f c = 1) :
    τ f ∈ Subgroup.closure (e' '' (s : Set (Fin k))) := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have hf : f = 1 := funext fun c => h c (Finset.notMem_empty c)
    rw [hf, map_one]
    exact Subgroup.one_mem _
  | insert c s hc ih =>
    set X : Fin k → Multiplicative (ZMod p) := Pi.mulSingle c (f c) with hX
    have hf' : ∀ j, j ∉ s → (f * X⁻¹) j = 1 := by
      intro j hj
      by_cases hjc : j = c
      · subst hjc
        simp [hX]
      · simp only [Pi.mul_apply, Pi.inv_apply, hX, Pi.mulSingle_eq_of_ne hjc, inv_one, mul_one]
        exact h j (by simp [hjc, hj])
    have h1 : τ (f * X⁻¹) ∈ Subgroup.closure (e' '' (s : Set (Fin k))) := ih (f * X⁻¹) hf'
    have h2 : τ X ∈
        Subgroup.closure (e' '' ((insert c s : Finset (Fin k)) : Set (Fin k))) := by
      rw [hX, ← ofAdd_toAdd (f c), SpCoord.mulSingle_ofAdd_eq_pow, map_pow, hτ c]
      refine Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _
      exact ⟨c, by simp, rfl⟩
    have h3 : τ f = τ (f * X⁻¹) * τ X := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.closure_mono (Set.image_mono (by simp)) h1) h2

private theorem eq_one_of_sq_eq_one_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : Multiplicative (ZMod p)} (h : x ^ 2 = 1) : x = 1 := by
  have hxp : x ^ p = 1 := by
    rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      ofAdd_zero]
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
  have hdvdp : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hgcd : Nat.gcd 2 p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hone : orderOf x = 1 := Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hdvd2 hdvdp)
  exact orderOf_eq_one_iff.mp hone

private theorem eq_zero_of_pow_apply_eq_on_plane (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    {c : Fin k} {n : ℕ} (hn : n < p)
    (h : ∀ x ∈ U c, ((e c : V ≃ₗ[F] V) ^ n) x = x) : n = 0 := by
  by_contra hn0
  have hpn : ¬ p ∣ n := fun hd => hn0 (Nat.eq_zero_of_dvd_of_lt hd hn)
  have hep : (e c : V ≃ₗ[F] V) ^ p = 1 := by
    have h1 := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq c ▸ pow_orderOf_eq_one (e c))
    simpa using h1
  have hcop : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).2 hpn).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hnm : (e c : V ≃ₗ[F] V) ^ (n * m) = (e c : V ≃ₗ[F] V) := by
    rw [pow_eq_pow_mod (n * m) hep, hm, pow_one]
  have hefix : ∀ x ∈ U c, (e c : V ≃ₗ[F] V) x = x := by
    intro x hx
    have h1 : (((e c : V ≃ₗ[F] V) ^ n) ^ m) x = x :=
      pow_apply_eq_of_apply_eq (h x hx) m
    rw [← hnm, pow_mul]
    exact h1
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U c) (hF.finrank_eq c)
  exact hx0 (hF.eq_zero_of_apply_eq c x hx (hefix x hx))

theorem exists_frameTorus (hF : IsPlaneFrame Q p U e E) (hp : p.Prime) :
    ∃ τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q),
      Function.Injective τ ∧ τ.range = E ∧
      (∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c) ∧
      ∀ f c, ∀ x ∈ U c, ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
        (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow : ∀ c, (e c) ^ p = 1 := fun c => by
    rw [← hF.orderOf_eq c]
    exact pow_orderOf_eq_one (e c)
  let coord : Fin k → Multiplicative (ZMod p) →* ↥(orthDerived Q) := fun c =>
    TableBSymp.zmodPowHom (hpow c)
  have hcommCoord : Pairwise fun c d : Fin k => ∀ a b, Commute (coord c a) (coord d b) := by
    intro c d hcd a b
    rw [show coord c a = (e c) ^ (Multiplicative.toAdd a).val from
        TableBSymp.zmodPowHom_apply (hpow c) a,
      show coord d b = (e d) ^ (Multiplicative.toAdd b).val from
        TableBSymp.zmodPowHom_apply (hpow d) b]
    have hcd : Commute (e c) (e d) := by
      have h := (isMulCommutative_iff.mp hF.isElemAbelian.1)
        (⟨e c, hF.mem c⟩ : ↥E) (⟨e d, hF.mem d⟩ : ↥E)
      exact Subtype.ext_iff.mp h
    exact hcd.pow_pow _ _
  let τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q) :=
    MonoidHom.noncommPiCoprod coord hcommCoord
  have hτc : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e c := by
    intro c
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    simpa using TableBSymp.zmodPowHom_natCast (hpow c) 1
  have hrange : τ.range = E := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      rw [MonoidHom.noncommPiCoprod_apply]
      refine Finset.noncommProd_induction _ _ _ (fun y => y ∈ E)
        (fun a b ha hb => E.mul_mem ha hb) E.one_mem ?_
      intro c _
      rw [show coord c (f c) = (e c) ^ (Multiplicative.toAdd (f c)).val from
        TableBSymp.zmodPowHom_apply (hpow c) (f c)]
      exact E.pow_mem (hF.mem c) _
    · rw [← hF.closure_eq]
      refine (Subgroup.closure_le τ.range).mpr ?_
      rintro _ ⟨c, rfl⟩
      exact ⟨Pi.mulSingle c (Multiplicative.ofAdd 1), hτc c⟩
  have hact : ∀ f c, ∀ x ∈ U c,
      ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
        (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x := by
    intro f c x hx
    have hcoe : ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
        ((Finset.univ.noncommProd (fun i => coord i (f i))
          (fun _ _ _ _ h => hcommCoord h _ _) : ↥(orthDerived Q)) : V ≃ₗ[F] V) := rfl
    have hgen : ∀ i, i ≠ c →
        ((coord i (f i) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
      intro i hic
      have hxperp : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp c i (fun h => hic h.symm) x hx y hy
      have hcoord : ((coord i (f i) : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
          ((e i : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f i)).val := by
        rw [TableBSymp.zmodPowHom_apply]
        rfl
      rw [hcoord]
      exact pow_apply_eq_of_apply_eq (hF.apply_of_perp i x hxperp) _
    rw [hcoe]
    change (Subgroup.subtype (orthDerived Q)
      (Finset.univ.noncommProd (fun i => coord i (f i))
        (fun _ _ _ _ h => hcommCoord h _ _))) x =
      (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x
    rw [Finset.map_noncommProd (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => coord i (f i)) (comm := fun _ _ _ _ h => hcommCoord h _ _)
      (g := Subgroup.subtype (orthDerived Q))]
    rw [noncommProd_apply_of_eq_of_ne (Finset.univ : Finset (Fin k))
      (g := fun i => (Subgroup.subtype (orthDerived Q)) (coord i (f i)))
      (hcomm := fun i _ j _ h =>
        ((hcommCoord h) (f i) (f j)).map (Subgroup.subtype (orthDerived Q)))
      (c := c) (hc := Finset.mem_univ c) (x := x) (h := fun i _ hic => hgen i hic)]
    rw [show (Subgroup.subtype (orthDerived Q)) (coord c (f c)) =
        ((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val from by
      rw [TableBSymp.zmodPowHom_apply]
      rfl]
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    funext c
    have hfix : ∀ x ∈ U c,
        ((e c : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x = x := by
      intro x hx
      have h1 := hact f c x hx
      rw [hf] at h1
      simpa using h1.symm
    have hk0 : (Multiplicative.toAdd (f c)).val = 0 :=
      eq_zero_of_pow_apply_eq_on_plane hF hp (ZMod.val_lt _) hfix
    rw [← ofAdd_toAdd (f c), (ZMod.val_eq_zero (Multiplicative.toAdd (f c))).mp hk0,
      ofAdd_zero, Pi.one_apply]
  exact ⟨τ, hinj, hrange, hτc, hact⟩

theorem mem_image_fix_sgnAut (hF : IsPlaneFrame Q p U e E) (hp : p.Prime)
    (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(orthDerived Q))
    (hτrange : τ.range = E)
    (hact : ∀ f c, ∀ x ∈ U c,
      ((τ f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
        (((e c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f c)).val) x)
    {a : Fin k} {x : ↥(orthDerived Q)} (hxE : x ∈ E)
    (hxa : ∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) :
    x ∈ τ '' {f | SpCoord.sgnAut a f = f} := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hxrange : x ∈ τ.range := hτrange ▸ hxE
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hxrange
  refine ⟨f, ?_, rfl⟩
  have hfa : f a = 1 := by
    have hfix : ∀ v ∈ U a,
        ((e a : V ≃ₗ[F] V) ^ (Multiplicative.toAdd (f a)).val) v = v := by
      intro v hv
      rw [← hact f a v hv]
      exact hxa v hv
    have hk0 : (Multiplicative.toAdd (f a)).val = 0 :=
      eq_zero_of_pow_apply_eq_on_plane hF hp (ZMod.val_lt _) hfix
    rw [← ofAdd_toAdd (f a), (ZMod.val_eq_zero (Multiplicative.toAdd (f a))).mp hk0,
      ofAdd_zero]
  funext j
  rw [SpCoord.sgnAut_apply]
  by_cases hja : j = a
  · subst hja
    rw [Function.update_self, hfa, inv_one]
  · rw [Function.update_of_ne hja]

section Generic

variable {G : Type*} [Group G] {p k : ℕ}

private abbrev mS (i : Fin k) (a : Multiplicative (ZMod p)) :
    Fin k → Multiplicative (ZMod p) :=
  Pi.mulSingle i a

theorem conj_eq_of_mulSingle [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (w : G)
    (s : MulAut (Fin k → Multiplicative (ZMod p)))
    (h : ∀ c, w * τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) * w⁻¹ =
      τ (s (Pi.mulSingle c (Multiplicative.ofAdd 1))))
    (f : Fin k → Multiplicative (ZMod p)) :
    w * τ f * w⁻¹ = τ (s f) := by
  have h1 : (MulAut.conj w).toMonoidHom.comp τ = τ.comp s.toMonoidHom :=
    SpCoord.hom_ext_mulSingle fun c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact h c
  exact DFunLike.congr_fun h1 f

theorem mem_image_fix_swap [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c) {a b : Fin k}
    (hab : a ≠ b) :
    e' a * e' b ∈ τ '' {f | SpCoord.permAut (Equiv.swap a b) f = f} := by
  let c : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  let W : Fin k → Multiplicative (ZMod p) := mS a c * mS b c
  refine ⟨W, ?_, ?_⟩
  · change SpCoord.permAut (Equiv.swap a b) W = W
    rw [show W = mS a c * mS b c from rfl, map_mul, SpCoord.permAut_mulSingle,
      SpCoord.permAut_mulSingle, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact (Pi.mulSingle_commute (f := fun _ : Fin k => Multiplicative (ZMod p)) hab c c).eq.symm
  · rw [show W = mS a c * mS b c from rfl, show c = Multiplicative.ofAdd 1 from rfl,
      map_mul, hτ a, hτ b]

theorem image_fix_swap_subset [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c) {a b : Fin k}
    (hab : a ≠ b) :
    τ '' {f | SpCoord.permAut (Equiv.swap a b) f = f} ⊆
      Subgroup.closure (insert (e' a * e' b) (e' '' {j | j ≠ a ∧ j ≠ b})) := by
  rintro _ ⟨f, hf, rfl⟩
  have hfab : f b = f a := by
    have h2 := congrFun hf a
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_left] at h2
    exact h2
  let X : Fin k → Multiplicative (ZMod p) := mS a (f a) * mS b (f b)
  let f' : Fin k → Multiplicative (ZMod p) := f * X⁻¹
  let W : Fin k → Multiplicative (ZMod p) :=
    mS a (Multiplicative.ofAdd 1) * mS b (Multiplicative.ofAdd 1)
  let n : ℕ := (Multiplicative.toAdd (f b)).val
  have hWn : W ^ n = mS a (f b) * mS b (f b) := by
    rw [show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd 1) from rfl, mul_pow,
      SpCoord.mulSingle_ofAdd_pow, SpCoord.mulSingle_ofAdd_pow, mul_one,
      show ((n : ℕ) : ZMod p) = Multiplicative.toAdd (f b) from ZMod.natCast_zmod_val _,
      ofAdd_toAdd]
  have hXW : X = W ^ n := by
    rw [hWn]
    show mS a (f a) * mS b (f b) = mS a (f b) * mS b (f b)
    rw [hfab]
  have hτX : τ X = (e' a * e' b) ^ n := by
    rw [hXW, map_pow]
    congr 1
    rw [show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd 1) from rfl, map_mul, hτ a, hτ b]
  have hf' : ∀ c, c ∉ (Finset.univ.erase a).erase b → f' c = 1 := by
    intro c hc
    by_cases hca : c = a
    · rw [hca]
      show f a * (X a)⁻¹ = 1
      rw [show X a = f a from by simp [X, mS, hab.symm]]
      exact mul_inv_cancel (f a)
    · by_cases hcb : c = b
      · rw [hcb]
        show f b * (X b)⁻¹ = 1
        rw [show X b = f b from by simp [X, mS, hab]]
        exact mul_inv_cancel (f b)
      · exfalso
        exact hc (by simp [Finset.mem_erase, hca, hcb])
  have h1 : τ f' ∈ Subgroup.closure (insert (e' a * e' b)
      (e' '' {j | j ≠ a ∧ j ≠ b})) := by
    refine Subgroup.closure_mono ?_
      (tau_mem_closure_image_of_eq_one τ e' hτ f' ((Finset.univ.erase a).erase b) hf')
    rintro _ ⟨j, hj, rfl⟩
    exact Set.mem_insert_of_mem _ ⟨j, by simpa [Finset.mem_erase] using hj, rfl⟩
  have h2 : τ X ∈ Subgroup.closure (insert (e' a * e' b)
      (e' '' {j | j ≠ a ∧ j ≠ b})) := by
    rw [hτX]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  rw [(inv_mul_cancel_right f X).symm, map_mul]
  exact Subgroup.mul_mem _ h1 h2

theorem mem_image_fix_omPlusRefl_true [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c) {a b : Fin k}
    (hab : a < b) :
    e' a * (e' b)⁻¹ ∈ τ '' {f | omPlusRefl p (⟨(a, b), hab⟩, true) f = f} := by
  let W : Fin k → Multiplicative (ZMod p) :=
    mS a (Multiplicative.ofAdd 1) * mS b (Multiplicative.ofAdd (-1))
  refine ⟨W, ?_, ?_⟩
  · change omPlusRefl p (⟨(a, b), hab⟩, true) W = W
    rw [omPlusRefl_true,
      show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd (-1)) from rfl,
      MulAut.mul_apply, MulAut.mul_apply, map_mul,
      SpCoord.permAut_mulSingle, SpCoord.permAut_mulSingle, Equiv.swap_apply_left,
      Equiv.swap_apply_right, map_mul, SpCoord.sgnAut_mulSingle_self,
      SpCoord.sgnAut_mulSingle_of_ne (i := b) (j := a) hab.ne, map_mul, map_inv,
      SpCoord.sgnAut_mulSingle_of_ne (i := a) (j := b) hab.ne',
      SpCoord.sgnAut_mulSingle_self, ← Pi.mulSingle_inv, ← Pi.mulSingle_inv,
      show (Multiplicative.ofAdd (1 : ZMod p))⁻¹ = Multiplicative.ofAdd (-1) from
        (ofAdd_neg (1 : ZMod p)).symm,
      show (Multiplicative.ofAdd (-1 : ZMod p))⁻¹ = Multiplicative.ofAdd 1 from by
        rw [← ofAdd_neg, neg_neg]]
    exact (Pi.mulSingle_commute (f := fun _ : Fin k => Multiplicative (ZMod p)) hab.ne
      (Multiplicative.ofAdd 1) (Multiplicative.ofAdd (-1))).eq.symm
  · have hb : (mS (p := p) (k := k) b (Multiplicative.ofAdd (-1)) :
          Fin k → Multiplicative (ZMod p)) =
        ((mS (p := p) (k := k) b (Multiplicative.ofAdd 1) :
          Fin k → Multiplicative (ZMod p)))⁻¹ := by
      rw [ofAdd_neg]
      change (Pi.mulSingle b ((Multiplicative.ofAdd 1)⁻¹) :
          Fin k → Multiplicative (ZMod p)) =
        ((Pi.mulSingle b (Multiplicative.ofAdd 1) : Fin k → Multiplicative (ZMod p)))⁻¹
      rw [Pi.mulSingle_inv]
    rw [show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd (-1)) from rfl, map_mul, hτ a, hb, map_inv, hτ b]

theorem image_fix_omPlusRefl_true_subset [NeZero p]
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c) {a b : Fin k}
    (hab : a < b) :
    τ '' {f | omPlusRefl p (⟨(a, b), hab⟩, true) f = f} ⊆
      Subgroup.closure (insert (e' a * (e' b)⁻¹) (e' '' {j | j ≠ a ∧ j ≠ b})) := by
  rintro _ ⟨f, hf, rfl⟩
  have hfab : f a = (f b)⁻¹ := by
    have h2 := congrFun hf a
    rw [omPlusRefl_true] at h2
    simp only [MulAut.mul_apply, SpCoord.permAut_apply, Function.comp_apply,
      Equiv.swap_inv, Equiv.swap_apply_left, SpCoord.sgnAut_apply, Function.update_self,
      Function.update_of_ne hab.ne, Ne.symm hab.ne] at h2
    exact h2.symm
  have hfab' : f b = (f a)⁻¹ := by
    rw [hfab, inv_inv]
  let X : Fin k → Multiplicative (ZMod p) := mS a (f a) * mS b (f b)
  let f' : Fin k → Multiplicative (ZMod p) := f * X⁻¹
  let W : Fin k → Multiplicative (ZMod p) :=
    mS a (Multiplicative.ofAdd 1) * mS b (Multiplicative.ofAdd (-1))
  let n : ℕ := (Multiplicative.toAdd (f a)).val
  have hWn : W ^ n = mS a (f a) * mS b ((f a)⁻¹) := by
    rw [show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd (-1)) from rfl, mul_pow,
      SpCoord.mulSingle_ofAdd_pow, SpCoord.mulSingle_ofAdd_pow, mul_one,
      show ((n : ℕ) : ZMod p) = Multiplicative.toAdd (f a) from ZMod.natCast_zmod_val _,
      mul_neg_one, ofAdd_neg, ofAdd_toAdd]
  have hXW : X = W ^ n := by
    rw [hWn]
    show mS a (f a) * mS b (f b) = mS a (f a) * mS b ((f a)⁻¹)
    rw [hfab']
  have hτX : τ X = (e' a * (e' b)⁻¹) ^ n := by
    rw [hXW, map_pow]
    congr 1
    have hb : (mS (p := p) (k := k) b (Multiplicative.ofAdd (-1)) :
          Fin k → Multiplicative (ZMod p)) =
        ((mS (p := p) (k := k) b (Multiplicative.ofAdd 1) :
          Fin k → Multiplicative (ZMod p)))⁻¹ := by
      rw [ofAdd_neg]
      change (Pi.mulSingle b ((Multiplicative.ofAdd 1)⁻¹) :
          Fin k → Multiplicative (ZMod p)) =
        ((Pi.mulSingle b (Multiplicative.ofAdd 1) : Fin k → Multiplicative (ZMod p)))⁻¹
      rw [Pi.mulSingle_inv]
    rw [show W = mS a (Multiplicative.ofAdd 1) *
        mS b (Multiplicative.ofAdd (-1)) from rfl, map_mul, hτ a, hb, map_inv, hτ b]
  have hf' : ∀ c, c ∉ (Finset.univ.erase a).erase b → f' c = 1 := by
    intro c hc
    by_cases hca : c = a
    · rw [hca]
      show f a * (X a)⁻¹ = 1
      rw [show X a = f a from by simp [X, mS, hab.ne.symm]]
      exact mul_inv_cancel (f a)
    · by_cases hcb : c = b
      · rw [hcb]
        show f b * (X b)⁻¹ = 1
        rw [show X b = f b from by simp [X, mS, hab.ne]]
        exact mul_inv_cancel (f b)
      · exfalso
        exact hc (by simp [Finset.mem_erase, hca, hcb])
  have h1 : τ f' ∈ Subgroup.closure (insert (e' a * (e' b)⁻¹)
      (e' '' {j | j ≠ a ∧ j ≠ b})) := by
    refine Subgroup.closure_mono ?_
      (tau_mem_closure_image_of_eq_one τ e' hτ f' ((Finset.univ.erase a).erase b) hf')
    rintro _ ⟨j, hj, rfl⟩
    exact Set.mem_insert_of_mem _ ⟨j, by simpa [Finset.mem_erase] using hj, rfl⟩
  have h2 : τ X ∈ Subgroup.closure (insert (e' a * (e' b)⁻¹)
      (e' '' {j | j ≠ a ∧ j ≠ b})) := by
    rw [hτX]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  rw [(inv_mul_cancel_right f X).symm, map_mul]
  exact Subgroup.mul_mem _ h1 h2

theorem image_fix_sgnAut_subset [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (τ : (Fin k → Multiplicative (ZMod p)) →* G) (e' : Fin k → G)
    (hτ : ∀ c, τ (Pi.mulSingle c (Multiplicative.ofAdd 1)) = e' c) {a : Fin k} :
    τ '' {f | SpCoord.sgnAut a f = f} ⊆ Subgroup.closure (e' '' {j | j ≠ a}) := by
  rintro _ ⟨f, hf, rfl⟩
  have hfa : f a = 1 := by
    have h1 : f a * f a = 1 := by
      have h2 := congrFun hf a
      rw [SpCoord.sgnAut_apply, Function.update_self] at h2
      exact mul_eq_one_iff_eq_inv.mpr h2.symm
    exact eq_one_of_sq_eq_one_of_odd hp hp2 (by rw [pow_two]; exact h1)
  refine Subgroup.closure_mono (Set.image_mono ?_)
    (tau_mem_closure_image_of_eq_one τ e' hτ f (Finset.univ.erase a) ?_)
  · intro j hj
    simpa using hj
  · intro c hc
    have hca : c = a := by
      by_contra hne
      exact hc (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ c⟩)
    rw [hca, hfa]

end Generic

end CFSG.StandardType.OmNsRootGen

end
