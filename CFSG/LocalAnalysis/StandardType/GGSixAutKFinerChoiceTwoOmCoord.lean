module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmPlane

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative SevOm QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Plane

variable {K : Type} [Field K] [CharP K 2]

theorem add_self_K (a : K) : a + a = 0 := CharTwo.add_self_eq_zero a

@[expose] def zL (K : Type) [Field K] [CharP K 2] : (K × K) ≃ₗ[K] (K × K) where
  toFun c := (c.2, c.1 + c.2)
  invFun c := (c.1 + c.2, c.1)
  map_add' c c' := Prod.ext (by simp) (by simp only [Prod.fst_add, Prod.snd_add]; ring)
  map_smul' t c := Prod.ext (by simp)
    (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring)
  left_inv c := by
    ext
    · show c.2 + (c.1 + c.2) = c.1
      linear_combination c.2 * add_self_K (1 : K)
    · rfl
  right_inv c := by
    ext
    · rfl
    · show c.1 + c.2 + c.1 = c.2
      linear_combination c.1 * add_self_K (1 : K)

theorem zL_apply (c : K × K) : zL K c = (c.2, c.1 + c.2) := rfl

@[expose] def σL (K : Type) [Field K] [CharP K 2] : (K × K) ≃ₗ[K] (K × K) where
  toFun c := (c.1 + c.2, c.2)
  invFun c := (c.1 + c.2, c.2)
  map_add' c c' := Prod.ext (by simp only [Prod.fst_add, Prod.snd_add]; ring) (by simp)
  map_smul' t c := Prod.ext
    (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring) (by simp)
  left_inv c := by
    ext
    · show c.1 + c.2 + c.2 = c.1
      linear_combination c.2 * add_self_K (1 : K)
    · rfl
  right_inv c := by
    ext
    · show c.1 + c.2 + c.2 = c.1
      linear_combination c.2 * add_self_K (1 : K)
    · rfl

theorem σL_apply (c : K × K) : σL K c = (c.1 + c.2, c.2) := rfl

theorem σL_σL (c : K × K) : σL K (σL K c) = c := (σL K).left_inv c

theorem zL_three (c : K × K) : zL K (zL K (zL K c)) = c := by
  ext
  · show c.2 + (c.1 + c.2) = c.1
    linear_combination c.2 * add_self_K (1 : K)
  · show c.1 + c.2 + (c.2 + (c.1 + c.2)) = c.2
    linear_combination (c.1 + c.2) * add_self_K (1 : K)

theorem σL_zL (c : K × K) : σL K (zL K c) = zL K (zL K (σL K c)) := by
  ext
  · show c.2 + (c.1 + c.2) = c.1 + c.2 + c.2
    ring
  · show c.1 + c.2 = c.2 + (c.1 + c.2 + c.2)
    linear_combination (-c.2) * add_self_K (1 : K)

@[expose] def nrm (c : K × K) : K := c.1 * c.1 + c.1 * c.2 + c.2 * c.2

theorem nrm_zL (c : K × K) : nrm (zL K c) = nrm c := by
  simp only [nrm, zL_apply]
  linear_combination (c.2 * c.2 + c.1 * c.2) * (add_self_K (1 : K))

theorem nrm_σL (c : K × K) : nrm (σL K c) = nrm c := by
  simp only [nrm, σL_apply]
  linear_combination (c.2 * c.2 + c.1 * c.2) * (add_self_K (1 : K))

theorem zL_pow_three : (zL K) ^ 3 = 1 :=
  LinearEquiv.ext fun c => by simpa [pow_succ, LinearEquiv.mul_apply] using zL_three c

@[expose] def zpow (a : ZMod 3) : (K × K) ≃ₗ[K] (K × K) := (zL K) ^ a.val

theorem zpow_val_cases (a : ZMod 3) :
    (a = 0 ∧ (zpow a : (K × K) ≃ₗ[K] (K × K)) = 1) ∨ zpow a = zL K ∨ zpow a = zL K * zL K := by
  have h := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 ∨ a.val = 2 by omega) with h0 | h1 | h2
  · left
    exact ⟨(ZMod.val_eq_zero a).mp h0, by rw [zpow, h0, pow_zero]⟩
  · right; left
    rw [zpow, h1, pow_one]
  · right; right
    rw [zpow, h2, _root_.sq]

theorem zpow_zero : (zpow (0 : ZMod 3) : (K × K) ≃ₗ[K] (K × K)) = 1 := by
  rw [zpow, ZMod.val_zero, pow_zero]

theorem zpow_add (a b : ZMod 3) : (zpow (a + b) : (K × K) ≃ₗ[K] (K × K)) = zpow a * zpow b := by
  rw [zpow, zpow, zpow, ← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ zL_pow_three]

theorem zpow_apply_add (a b : ZMod 3) (c : K × K) : zpow (a + b) c = zpow a (zpow b c) := by
  rw [zpow_add, LinearEquiv.mul_apply]

theorem nrm_zpow (a : ZMod 3) (c : K × K) : nrm (zpow a c) = nrm c := by
  rcases zpow_val_cases (K := K) a with ⟨-, h⟩ | h | h <;> rw [h]
  · rfl
  · exact nrm_zL c
  · rw [LinearEquiv.mul_apply, nrm_zL, nrm_zL]

theorem σL_zL_pow (k : ℕ) (c : K × K) :
    σL K (((zL K) ^ k) c) = ((zL K) ^ (2 * k)) (σL K c) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, σL_zL, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

theorem σL_zpow (a : ZMod 3) (c : K × K) : σL K (zpow a c) = zpow (-a) (σL K c) := by
  have key : (2 * a.val) % 3 = (-a).val % 3 := by
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : (3 : ZMod 3) = 0 := rfl
    linear_combination a * this
  rw [zpow, σL_zL_pow, zpow, pow_eq_pow_mod (2 * a.val) zL_pow_three,
    pow_eq_pow_mod (-a).val zL_pow_three, key]

theorem eq_zero_of_zpow_eq (a : ZMod 3) (ha : a ≠ 0) (c : K × K) (h : zpow a c = c) : c = 0 := by
  rcases zpow_val_cases (K := K) a with ⟨h0, -⟩ | h1 | h2
  · exact absurd h0 ha
  · rw [h1, zL_apply] at h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only at e1 e2
    have hc1 : c.1 = 0 := by linear_combination e2
    have hc2 : c.2 = 0 := by linear_combination e1 + e2
    ext
    · exact hc1
    · exact hc2
  · rw [h2, LinearEquiv.mul_apply, zL_apply, zL_apply] at h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only at e1 e2
    have hc2 : c.2 = 0 := by linear_combination e1
    have hc1 : c.1 = 0 := by linear_combination e2 - e1
    ext
    · exact hc1
    · exact hc2

end Plane

section Coord

variable {K : Type} [Field K] [CharP K 2] {s : ℕ}

@[expose] def torC (f : Fin s → ZMod 3) (d : Fin s → K × K) : Fin s → K × K :=
  fun i => zpow (f i) (d i)

theorem torC_apply (f : Fin s → ZMod 3) (d : Fin s → K × K) (i : Fin s) :
    torC f d i = zpow (f i) (d i) := rfl

theorem torC_add (f f' : Fin s → ZMod 3) (d : Fin s → K × K) :
    torC (f + f') d = torC f (torC f' d) :=
  funext fun i => zpow_apply_add (f i) (f' i) (d i)

theorem torC_zero (d : Fin s → K × K) : torC (0 : Fin s → ZMod 3) d = d :=
  funext fun i => by rw [torC_apply, Pi.zero_apply, zpow_zero]; rfl

variable {V : Type} [AddCommGroup V] [Module K V]

structure OmCoord (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (A : Subgroup (V ≃ₗ[K] V)) where
  s : ℕ
  W0 : Submodule K V
  Φ : ((Fin s → K × K) × W0) ≃ₗ[K] V
  form : ∀ d x, Q (Φ (d, x)) = (∑ i, nrm (d i)) + Q (x : V)
  tor : (Fin s → ZMod 3) → (V ≃ₗ[K] V)
  tor_acts : ∀ f d x, tor f (Φ (d, x)) = Φ (torC f d, x)
  tor_mem : ∀ f, tor f ∈ A
  mem_tor : ∀ c ∈ A, ∃ f, tor f = c

end Coord

section Exists

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem Q_sum_add {ι : Type} (S : Finset ι) (v : ι → V) (x : V)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → polar Q (v i) (v j) = 0)
    (hx : ∀ i ∈ S, polar Q (v i) x = 0) :
    Q (∑ i ∈ S, v i + x) = ∑ i ∈ S, Q (v i) + Q x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hsum : polar Q (v a) (∑ i ∈ S, v i) = ∑ i ∈ S, polar Q (v a) (v i) := by
      simp only [← QuadraticMap.polarBilin_apply_apply, map_sum]
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_assoc, QuadraticMap.map_add (⇑Q),
      ih (fun i hi j hj hij => horth i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij) (fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      polar_add_right, hsum, hx a (Finset.mem_insert_self a S),
      Finset.sum_eq_zero fun i hi => horth a (Finset.mem_insert_self a S) i
        (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)), add_zero, add_zero, add_assoc]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem Q_comb {u w : V} (hu : Q u = 1) (hw : Q w = 1) (huw : polar Q u w = 1) (c : K × K) :
    Q (c.1 • u + c.2 • w) = nrm c := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, hu, hw, huw, nrm]
  simp only [smul_eq_mul, mul_one]
  ring

omit [Finite K] [FiniteDimensional K V] in
theorem pow_comb {y : V ≃ₗ[K] V} {u w : V} (hyu : y u = w) (hyw : y w = u + w) (k : ℕ)
    (c : K × K) :
    (y ^ k) (c.1 • u + c.2 • w) = (((zL K) ^ k) c).1 • u + (((zL K) ^ k) c).2 • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, y_comb hyu hyw, pow_succ', LinearEquiv.mul_apply,
      zL_apply]

theorem exists_coord (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAΩ : A ≤ CFSG.RankThree.Classical2.orthDerived Q) (F : Frame Q 3 A r)
    (hmax : ∀ g ∈ CFSG.RankThree.Classical2.orthDerived Q, g ^ 3 = 1 →
      (∀ c ∈ A, g * c = c * g) → g ∈ A) :
    ∃ C : OmCoord K Q A, C.s = r := by
  classical
  have hAQ : ∀ a ∈ A, ∀ v, Q (a v) = Q v := fun a ha =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (hAΩ ha))
  choose u hu hQu huw hproj using exists_plane hK hQ hT hAΩ F hmax
  set w : Fin r → V := fun i => gen F i (u i) with hwdef
  have hwU : ∀ i, w i ∈ F.U i := fun i => gen_mem F i (hu i)
  have hQw : ∀ i, Q (w i) = 1 := fun i => by rw [hwdef]; exact (hAQ _ (gen_mem_A F i) _).trans (hQu i)
  have hyu : ∀ i, gen F i (u i) = w i := fun i => rfl
  have hyw : ∀ i, gen F i (w i) = u i + w i := fun i => by
    rw [hwdef, gen_gen F i (hu i), add_comm]
  set cv : (Fin r → K × K) → Fin r → V := fun d i => (d i).1 • u i + (d i).2 • w i with hcv
  have hcvU : ∀ d i, cv d i ∈ F.U i := fun d i =>
    add_mem (Submodule.smul_mem _ _ (hu i)) (Submodule.smul_mem _ _ (hwU i))
  set W0 : Submodule K V :=
    { carrier := {v | ∀ i, polar Q v (u i) = 0 ∧ polar Q v (w i) = 0}
      add_mem' := fun {a b} ha hb i => ⟨by rw [polar_add_left, (ha i).1, (hb i).1, add_zero],
        by rw [polar_add_left, (ha i).2, (hb i).2, add_zero]⟩
      zero_mem' := fun i => ⟨by simp, by simp⟩
      smul_mem' := fun c v hv i => ⟨by rw [polar_smul_left, (hv i).1, smul_zero],
        by rw [polar_smul_left, (hv i).2, smul_zero]⟩ } with hW0
  have hperpU : ∀ x ∈ W0, ∀ i, ∀ z ∈ F.U i, polar Q z x = 0 := by
    intro x hx i z hz
    rw [← hproj i z hz, proj_apply, polar_add_left, polar_smul_left, polar_smul_left,
      polar_comm Q (u i), polar_comm Q (w i), (hx i).1, (hx i).2, smul_zero, smul_zero, add_zero]
  have horth : ∀ i j, i ≠ j → ∀ z ∈ F.U i, ∀ z' ∈ F.U j, polar Q z z' = 0 := F.orth
  set toV : ((Fin r → K × K) × W0) →ₗ[K] V :=
    { toFun := fun p => ∑ i, cv p.1 i + (p.2 : V)
      map_add' := fun p q => by
        simp only [hcv, Prod.fst_add, Prod.snd_add, Pi.add_apply, Submodule.coe_add, add_smul,
          Finset.sum_add_distrib]
        abel
      map_smul' := fun c p => by
        simp only [hcv, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul,
          smul_eq_mul, mul_smul, RingHom.id_apply, smul_add, Finset.smul_sum] } with htoV
  have hpw : ∀ p : (Fin r → K × K) × W0, ∀ i,
      polar Q (toV p) (w i) = (p.1 i).1 ∧ polar Q (toV p) (u i) = (p.1 i).2 := by
    intro p i
    have hsplit : ∀ z : V, polar Q (∑ j, cv p.1 j + (p.2 : V)) z =
        ∑ j, polar Q (cv p.1 j) z + polar Q (p.2 : V) z := by
      intro z
      rw [polar_add_left]
      congr 1
      simp only [← QuadraticMap.polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
    have hother : ∀ z ∈ F.U i, ∑ j, polar Q (cv p.1 j) z = polar Q (cv p.1 i) z := by
      intro z hz
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), Finset.sum_eq_zero, zero_add]
      intro j hj
      exact horth j i (Finset.ne_of_mem_erase hj) _ (hcvU p.1 j) z hz
    have hx : ∀ z ∈ F.U i, polar Q (p.2 : V) z = 0 := fun z hz => by
      rw [polar_comm]
      exact hperpU _ p.2.2 i z hz
    refine ⟨?_, ?_⟩
    · show polar Q (∑ j, cv p.1 j + (p.2 : V)) (w i) = _
      rw [hsplit, hother _ (hwU i), hx _ (hwU i), add_zero, hcv]
      simp only
      rw [polar_add_left, polar_smul_left, polar_smul_left, huw i, polar_self_eq_zero]
      simp
    · show polar Q (∑ j, cv p.1 j + (p.2 : V)) (u i) = _
      rw [hsplit, hother _ (hu i), hx _ (hu i), add_zero, hcv]
      simp only
      rw [polar_add_left, polar_smul_left, polar_smul_left, polar_self_eq_zero,
        polar_comm Q (w i), huw i]
      simp
  set coordL : V →ₗ[K] (Fin r → K × K) :=
    LinearMap.pi fun i => LinearMap.prod ((polarBilin Q).flip (w i)) ((polarBilin Q).flip (u i))
    with hcoordL
  have hcoordL_apply : ∀ v i, coordL v i = (polar Q v (w i), polar Q v (u i)) := fun v i => rfl
  set restL : V →ₗ[K] V := LinearMap.id - ∑ i, proj Q (u i) (w i) with hrestL
  have hcvp : ∀ v i, cv (coordL v) i = proj Q (u i) (w i) v := fun v i => by
    rw [proj_apply]
    rfl
  have hrest_apply : ∀ v, restL v = v - ∑ i, cv (coordL v) i := fun v => by
    simp only [hrestL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, hcvp]
  have hrestW : ∀ v, restL v ∈ W0 := by
    intro v j
    have hsum : ∀ z ∈ F.U j, polar Q (∑ i, cv (coordL v) i) z = polar Q (cv (coordL v) j) z := by
      intro z hz
      simp only [← QuadraticMap.polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Finset.sum_eq_zero, zero_add]
      intro i hi
      exact horth i j (Finset.ne_of_mem_erase hi) _ (hcvU _ i) z hz
    rw [hrest_apply, polar_sub_left, polar_sub_left, hsum _ (hu j), hsum _ (hwU j), hcvp,
      ← polar_sub_left, ← polar_sub_left]
    exact ⟨polar_sub_proj_u (huw j) v, polar_sub_proj_w (huw j) v⟩
  set fromV : V →ₗ[K] ((Fin r → K × K) × W0) :=
    LinearMap.prod coordL (LinearMap.codRestrict W0 restL hrestW) with hfromV
  have h1 : ∀ v, toV (fromV v) = v := by
    intro v
    show ∑ i, cv (coordL v) i + restL v = v
    rw [hrest_apply]
    abel
  have h2 : ∀ p, fromV (toV p) = p := by
    rintro ⟨d, x⟩
    have hc : coordL (toV (d, x)) = d := funext fun i => by
      rw [hcoordL_apply, (hpw (d, x) i).1, (hpw (d, x) i).2]
    refine Prod.ext hc (Subtype.ext ?_)
    show restL (toV (d, x)) = (x : V)
    rw [hrest_apply, hc]
    show ∑ i, cv d i + (x : V) - ∑ i, cv d i = x
    abel
  set Φ : ((Fin r → K × K) × W0) ≃ₗ[K] V :=
    LinearEquiv.ofLinearMap toV fromV (LinearMap.ext h1) (LinearMap.ext h2) with hΦ
  have hΦ_apply : ∀ p, Φ p = ∑ i, cv p.1 i + (p.2 : V) := fun p => rfl
  have hfixW : ∀ (f : Fin r → ZMod 3) (x : V), x ∈ W0 → F.ι (ofAdd f) x = x := by
    intro f x hx
    exact (F.fix _ x).mpr fun j _ z hz => hperpU x hx j z hz
  have hact : ∀ (f : Fin r → ZMod 3) d i, F.ι (ofAdd f) (cv d i) = cv (torC f d) i := by
    intro f d i
    rw [act_piece F _ (hcvU d i), toAdd_ofAdd, hcv]
    simp only
    rw [pow_comb (hyu i) (hyw i), torC_apply, zpow]
  have hform : ∀ d (x : W0), Q (Φ (d, x)) = (∑ i, nrm (d i)) + Q (x : V) := by
    intro d x
    rw [hΦ_apply]
    simp only
    rw [Q_sum_add Finset.univ (cv d) (x : V) (fun i _ j _ hij => horth i j hij _ (hcvU d i) _
      (hcvU d j)) (fun i _ => hperpU _ x.2 i _ (hcvU d i))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Q_comb (hQu i) (hQw i) (huw i) (d i)
  have hacts : ∀ (f : Fin r → ZMod 3) d (x : W0),
      F.ι (ofAdd f) (Φ (d, x)) = Φ (torC f d, x) := by
    intro f d x
    rw [hΦ_apply, hΦ_apply, map_add, map_sum, hfixW f _ x.2]
    simp only [hact]
  have hmemtor : ∀ c ∈ A, ∃ f : Fin r → ZMod 3, F.ι (ofAdd f) = c := by
    intro c hc
    obtain ⟨s', rfl⟩ := F.exists_eq hc
    exact ⟨toAdd s', by rw [ofAdd_toAdd]⟩
  exact ⟨⟨r, W0, Φ, hform, fun f => F.ι (ofAdd f), hacts, fun f => F.mem _, hmemtor⟩, rfl⟩

end Exists

end ChoiceTwoOm

end CFSG.StandardType
