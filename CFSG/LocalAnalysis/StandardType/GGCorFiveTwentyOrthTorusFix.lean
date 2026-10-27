module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldFrame
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneD4Frame

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

section Subspaces

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s r : ℕ} {κ : Type} (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V) (a : Fin r → Fin s)

@[expose] def fixSub : Submodule K V where
  carrier := {v | ∀ j, (Φ.symm v).1 (a j) = 0}
  add_mem' := fun {v w} hv hw j => by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, Prod.fst_add, Pi.add_apply, hv j, hw j, add_zero]
  zero_mem' := fun j => by simp
  smul_mem' := fun c v hv j => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [map_smul, Prod.smul_fst, Pi.smul_apply, hv j, smul_zero]

theorem frame_mem_fixSub {d : Fin s → D} {w : κ → K} :
    Φ (d, w) ∈ fixSub Φ a ↔ ∀ j, d (a j) = 0 := by
  change (∀ j, (Φ.symm (Φ (d, w))).1 (a j) = 0) ↔ _
  rw [LinearEquiv.symm_apply_apply]

@[expose] def actSub : Submodule K V where
  carrier := {v | (Φ.symm v).2 = 0 ∧ ∀ i, (∀ j, a j ≠ i) → (Φ.symm v).1 i = 0}
  add_mem' := fun {v w} hv hw => by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    refine ⟨by rw [map_add, Prod.snd_add, hv.1, hw.1, add_zero], fun i hi => ?_⟩
    rw [map_add, Prod.fst_add, Pi.add_apply, hv.2 i hi, hw.2 i hi, add_zero]
  zero_mem' := ⟨by simp, fun i _ => by simp⟩
  smul_mem' := fun c v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    refine ⟨by rw [map_smul, Prod.smul_snd, hv.1, smul_zero], fun i hi => ?_⟩
    rw [map_smul, Prod.smul_fst, Pi.smul_apply, hv.2 i hi, smul_zero]

theorem frame_mem_actSub {d : Fin s → D} {w : κ → K} :
    Φ (d, w) ∈ actSub Φ a ↔ w = 0 ∧ ∀ i, (∀ j, a j ≠ i) → d i = 0 := by
  change ((Φ.symm (Φ (d, w))).2 = 0 ∧ ∀ i, (∀ j, a j ≠ i) → (Φ.symm (Φ (d, w))).1 i = 0) ↔ _
  rw [LinearEquiv.symm_apply_apply]

theorem actSub_inf_fixSub : actSub Φ a ⊓ fixSub Φ a = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  have h1 := (frame_mem_actSub Φ a).mp hv.1
  have h2 := (frame_mem_fixSub Φ a).mp hv.2
  have hd : d = 0 := funext fun i => by
    by_cases hi : ∃ j, a j = i
    · obtain ⟨j, rfl⟩ := hi
      exact h2 j
    · push Not at hi
      exact h1.2 i hi
  rw [hd, h1.1, Prod.mk_zero_zero, map_zero]

theorem actSub_sup_fixSub : actSub Φ a ⊔ fixSub Φ a = ⊤ := by
  classical
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  set d₁ : Fin s → D := fun i => if ∃ j, a j = i then d i else 0 with hd₁
  have e : Φ (d, w) = Φ (d₁, 0) + Φ (d - d₁, w) := by
    rw [← map_add, Prod.mk_add_mk, add_sub_cancel, zero_add]
  rw [e]
  refine Submodule.add_mem_sup ((frame_mem_actSub Φ a).mpr ⟨rfl, fun i hi => ?_⟩)
    ((frame_mem_fixSub Φ a).mpr fun j => ?_)
  · have : ¬ ∃ j, a j = i := fun ⟨j, hj⟩ => hi j hj
    simp [hd₁, this]
  · have : ∃ j', a j' = a j := ⟨j, rfl⟩
    simp [hd₁, this]

variable {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D}

theorem polar_actSub_fixSub
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    {u v : V} (hu : u ∈ actSub Φ a) (hv : v ∈ fixSub Φ a) : polar Q u v = 0 := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective u
  obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective v
  obtain ⟨hw, hd⟩ := (frame_mem_actSub Φ a).mp hu
  have hd' := (frame_mem_fixSub Φ a).mp hv
  have h1 : ∑ i, ω (d i) (d' i) = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : ∃ j, a j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hd' j, map_zero]
    · push Not at hi
      rw [hd i hi, map_zero, LinearMap.zero_apply]
  rw [← polarBilin_apply_apply, hdec, h1, zero_add, hw, Prod.mk_zero_zero, map_zero, map_zero,
    LinearMap.zero_apply]

theorem nondegOn_fixSub (hQ : (polarBilin Q).Nondegenerate)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w'))) :
    SUTB.NondegOn (polarBilin Q) (fixSub Φ a) := by
  intro m hm hmo
  refine hQ.2 m fun v => ?_
  have hv : v ∈ actSub Φ a ⊔ fixSub Φ a := by
    rw [actSub_sup_fixSub]
    trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, LinearMap.add_apply, hmo w hw, add_zero, polarBilin_apply_apply]
  exact polar_actSub_fixSub Φ a hdec hu hm

theorem charSum_top_eq [CharP K 2] [Finite K] [Finite V]
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w'))) :
    OrdPNsOm.charSum Q ⊤ = OrdPNsOm.charSum Q (actSub Φ a) * OrdPNsOm.charSum Q (fixSub Φ a) := by
  rw [← actSub_sup_fixSub Φ a]
  exact OrdPNsOm.charSum_sup (actSub_inf_fixSub Φ a) fun u hu v hv =>
    polar_actSub_fixSub Φ a hdec hu hv

@[expose] def pieceSub (j : Fin r) : Submodule K V :=
  LinearMap.range (OmMv.blkL Φ (a j))

theorem finrank_pieceSub [FiniteDimensional K D] (j : Fin r) :
    finrank K (pieceSub Φ a j) = finrank K D :=
  LinearMap.finrank_range_of_inj (OmMv.blkL_injective Φ (a j))

theorem nondegOn_pieceSub
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (j : Fin r) : SUTB.NondegOn (polarBilin Q) (pieceSub Φ a j) := by
  rintro _ ⟨y, rfl⟩ hmo
  have hy : y = 0 := hωnd.2 y fun y' => by
    have h1 := hmo _ ⟨y', rfl⟩
    rwa [OmMv.blkL_apply, OmMv.blkL_apply, polarBilin_apply_apply, OmMv.polar_frame_single hdec,
      Pi.single_eq_same] at h1
  rw [hy, map_zero]

end Subspaces

section Torus

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s r p : ℕ} [NeZero p] {κ : Type} (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V)
  {cE : D ≃ₗ[K] D} (hcp : cE ^ p = 1) {a : Fin r → Fin s}

theorem coordTorus_mem_actSub (f : Fin r → Multiplicative (ZMod p)) {v : V}
    (hv : v ∈ actSub Φ a) : coordTorus Φ hcp a f v ∈ actSub Φ a := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  obtain ⟨hw, hd⟩ := (frame_mem_actSub Φ a).mp hv
  rw [coordTorus_apply]
  refine (frame_mem_actSub Φ a).mpr ⟨hw, fun i hi => ?_⟩
  rw [hd i hi, map_zero]

theorem coordTorus_mem_pieceSub (ha : Function.Injective a) (f : Fin r → Multiplicative (ZMod p))
    (j : Fin r) {v : V} (hv : v ∈ pieceSub Φ a j) : coordTorus Φ hcp a f v ∈ pieceSub Φ a j := by
  obtain ⟨y, rfl⟩ := hv
  rw [OmMv.blkL_apply, coordTorus_single Φ hcp ha]
  exact ⟨_, rfl⟩

theorem coordTorus_mulSingle_sub (ha : Function.Injective a) (j : Fin r) (e : ZMod p)
    (d : Fin s → D) (w : κ → K) :
    coordTorus Φ hcp a (Pi.mulSingle j (ofAdd e)) (Φ (d, w)) - Φ (d, w) =
      Φ (Pi.single (a j) ((cE ^ e.val) (d (a j)) - d (a j)), 0) := by
  rw [coordTorus_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
  congr 2
  funext i
  by_cases hi : i = a j
  · subst hi
    simp only [Pi.sub_apply, Pi.single_eq_same]
    rw [OmMv.extC_apply_self ha, Pi.mulSingle_eq_same, toAdd_ofAdd]
  · simp only [Pi.sub_apply, Pi.single_eq_of_ne hi]
    have h0 : OmMv.extC a (fun k => toAdd ((Pi.mulSingle j (ofAdd e) :
        Fin r → Multiplicative (ZMod p)) k)) i = 0 := by
      by_cases hi' : ∃ k, a k = i
      · obtain ⟨k, rfl⟩ := hi'
        rw [OmMv.extC_apply_self ha]
        have hkj : k ≠ j := fun h => hi (h ▸ rfl)
        rw [Pi.mulSingle_eq_of_ne hkj, toAdd_one]
      · push Not at hi'
        exact OmMv.extC_apply_of_forall_ne _ hi'
    rw [h0, ZMod.val_zero, pow_zero]
    exact sub_self _

theorem coordTorus_sub_mem_pieceSub (ha : Function.Injective a) (j : Fin r) (e : ZMod p) (v : V) :
    coordTorus Φ hcp a (Pi.mulSingle j (ofAdd e)) v - v ∈ pieceSub Φ a j := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [coordTorus_mulSingle_sub Φ hcp ha]
  exact ⟨_, rfl⟩

variable [Fact p.Prime]

theorem coordTorus_fixSub (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (f : Fin r → Multiplicative (ZMod p)) {v : V} (hv : v ∈ fixSub Φ a) :
    coordTorus Φ hcp a f v = v := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  exact (coordTorus_apply_eq_self_iff Φ hcp hfix ha f d w).mpr fun j _ =>
    (frame_mem_fixSub Φ a).mp hv j

theorem eq_zero_of_coordTorus_actSub (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    {v : V} (hv : v ∈ actSub Φ a)
    (h : coordTorus Φ hcp a (fun _ => ofAdd (1 : ZMod p)) v = v) : v = 0 := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  obtain ⟨hw, hd⟩ := (frame_mem_actSub Φ a).mp hv
  have h1 := (coordTorus_apply_eq_self_iff Φ hcp hfix ha _ d w).mp h
  have hd0 : d = 0 := funext fun i => by
    by_cases hi : ∃ j, a j = i
    · obtain ⟨j, rfl⟩ := hi
      exact h1 j (by rw [Ne, ofAdd_eq_one]; exact one_ne_zero)
    · push Not at hi
      exact hd i hi
  rw [hd0, hw, Prod.mk_zero_zero, map_zero]

theorem eq_zero_of_coordTorus_pieceSub (hfix : ∀ x, cE x = x → x = 0)
    (ha : Function.Injective a) (j : Fin r) {v : V} (hv : v ∈ pieceSub Φ a j)
    (h : coordTorus Φ hcp a (Pi.mulSingle j (ofAdd (1 : ZMod p))) v = v) : v = 0 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  obtain ⟨y, rfl⟩ := hv
  rw [OmMv.blkL_apply, coordTorus_single Φ hcp ha, Pi.mulSingle_eq_same, toAdd_ofAdd,
    ZMod.val_one, pow_one] at h
  have h1 : cE y = y := OmMv.blkL_injective Φ (a j) (by rwa [OmMv.blkL_apply, OmMv.blkL_apply])
  rw [hfix y h1, map_zero]

theorem coordTorus_toLinearMap_pow (f : Fin r → Multiplicative (ZMod p)) :
    ((coordTorus Φ hcp a f : V ≃ₗ[K] V) : V →ₗ[K] V) ^ p = 1 := by
  rw [OmMv.toLinearMap_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one]
  rfl

variable [CharP K 2] [Finite V] {Q : QuadraticForm K V}

theorem charSum_actSub_modEq (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hiso : ∀ f v, Q (coordTorus Φ hcp a f v) = Q v) :
    OrdPNsOm.charSum Q (actSub Φ a) ≡ 1 [ZMOD p] :=
  OrdPNsOm.charSum_modEq (y := ((coordTorus Φ hcp a fun _ => ofAdd (1 : ZMod p) : V ≃ₗ[K] V) :
      V →ₗ[K] V)) (fun _ hu => coordTorus_mem_actSub Φ hcp _ hu) (fun v => hiso _ v)
    (coordTorus_toLinearMap_pow Φ hcp _) fun _ hu h =>
      eq_zero_of_coordTorus_actSub Φ hcp hfix ha hu h

theorem charSum_pieceSub_modEq (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hiso : ∀ f v, Q (coordTorus Φ hcp a f v) = Q v) (j : Fin r) :
    OrdPNsOm.charSum Q (pieceSub Φ a j) ≡ 1 [ZMOD p] :=
  OrdPNsOm.charSum_modEq (y := ((coordTorus Φ hcp a (Pi.mulSingle j (ofAdd (1 : ZMod p))) :
      V ≃ₗ[K] V) : V →ₗ[K] V)) (fun _ hu => coordTorus_mem_pieceSub Φ hcp ha _ j hu)
    (fun v => hiso _ v) (coordTorus_toLinearMap_pow Φ hcp _) fun _ hu h =>
      eq_zero_of_coordTorus_pieceSub Φ hcp hfix ha j hu h

end Torus

section Orth

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s r p : ℕ} [NeZero p] [Fact p.Prime] {κ : Type}
  (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V) {cE : D ≃ₗ[K] D} (hcp : cE ^ p = 1) {a : Fin r → Fin s}
  {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D}

theorem coordTorus_eq_of_polar (hfix : ∀ x, cE x = x → x = 0) (ha : Function.Injective a)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωnd : ω.Nondegenerate) (j : Fin r) {v : V}
    (hv : ∀ u ∈ pieceSub Φ a j, polar Q u v = 0) :
    coordTorus Φ hcp a (Pi.mulSingle j (ofAdd (1 : ZMod p))) v = v := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  have hd : d (a j) = 0 := hωnd.2 _ fun y' => by
    have h1 := hv _ ⟨y', rfl⟩
    rwa [OmMv.blkL_apply, OmMv.polar_frame_single hdec] at h1
  refine (coordTorus_apply_eq_self_iff Φ hcp hfix ha _ d w).mpr fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
    exact hd
  · exact absurd (Pi.mulSingle_eq_of_ne hjj _) hj'

omit [NeZero p] [Fact p.Prime] in
theorem finrank_eq_of_fixSub_eq_bot [Nontrivial D] [FiniteDimensional K D] [Fintype κ]
    (ha : Function.Injective a) (h : fixSub Φ a = ⊥) : finrank K V = r * finrank K D := by
  classical
  have hsurj : Function.Surjective a := by
    intro i
    by_contra hi
    push Not at hi
    obtain ⟨y, hy⟩ := exists_ne (0 : D)
    have h1 : Φ (Pi.single i y, 0) ∈ fixSub Φ a :=
      (frame_mem_fixSub Φ a).mpr fun j => by rw [Pi.single_eq_of_ne (hi j)]
    rw [h, Submodule.mem_bot] at h1
    have h2 := congrArg (fun x => (Φ.symm x).1 i) h1
    simp only [LinearEquiv.symm_apply_apply, Pi.single_eq_same, map_zero, Prod.fst_zero,
      Pi.zero_apply] at h2
    exact hy h2
  have hκ : IsEmpty κ := by
    by_contra hk
    rw [not_isEmpty_iff] at hk
    obtain ⟨k⟩ := hk
    have h1 : Φ (0, Pi.single k 1) ∈ fixSub Φ a := (frame_mem_fixSub Φ a).mpr fun j => rfl
    rw [h, Submodule.mem_bot] at h1
    have h2 := congrArg (fun x => (Φ.symm x).2 k) h1
    simp at h2
  have hrs : r = s := by
    have := Fintype.card_congr (Equiv.ofBijective a ⟨ha, hsurj⟩)
    simpa using this
  rw [← Φ.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_fintype_fun_eq_card, Fintype.card_eq_zero, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hrs]

end Orth

end OrthTorus

end CFSG.StandardType

end
