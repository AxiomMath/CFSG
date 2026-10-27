module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame

public section

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private noncomputable abbrev glinHom (K : Type) [Field K] (d : ℕ) :
    GL (Fin d) K →* Module.End K (Fin d → K) :=
  { toFun := NoOffOm.glin
    map_one' := NoOffOm.glin_one
    map_mul' := NoOffOm.glin_mul }

private lemma noncommProd_apply_eq_self {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Module.End K V) :
    (comm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b))) →
    (W : Submodule K V) → (∀ i ∈ s, ∀ w ∈ W, f i w = w) →
    ∀ w ∈ W, (s.noncommProd f comm) w = w := by
  induction s using Finset.induction_on with
  | empty => intro comm W hid w _; simp
  | insert a t ha ih =>
      intro comm W hid w hw
      rw [Finset.noncommProd_insert_of_notMem t a f comm ha, Module.End.mul_apply]
      rw [ih (comm.mono (fun _ => Finset.mem_insert_of_mem)) W
            (fun i hi => hid i (Finset.mem_insert_of_mem hi)) w hw]
      exact hid a (Finset.mem_insert_self a t) w hw

private lemma noncommProd_apply_eq_of_forall {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Module.End K V) :
    (comm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b))) →
    (i₀ : ι) → (W : Submodule K V) →
    i₀ ∈ s →
    (∀ i ∈ s, i ≠ i₀ → ∀ w ∈ W, f i w = w) →
    (∀ i ∈ s, ∀ w ∈ W, f i w ∈ W) →
    ∀ w ∈ W, (s.noncommProd f comm) w = f i₀ w := by
  induction s using Finset.induction_on with
  | empty => intro comm i₀ W hi₀ _ _; exact absurd hi₀ (Finset.notMem_empty i₀)
  | insert a t ha ih =>
      intro comm i₀ W hi₀ hid hmem w hw
      rw [Finset.noncommProd_insert_of_notMem t a f comm ha, Module.End.mul_apply]
      rcases Finset.mem_insert.mp hi₀ with h | h
      · subst h
        have hidt : ∀ i ∈ t, ∀ w ∈ W, f i w = w := by
          intro i hi
          refine hid i (Finset.mem_insert_of_mem hi) ?_
          intro hia; subst hia; exact ha hi
        rw [noncommProd_apply_eq_self t f (comm.mono (fun _ => Finset.mem_insert_of_mem)) W
          hidt w hw]
      · have hprod := ih (comm.mono (fun _ => Finset.mem_insert_of_mem)) i₀ W h
            (fun i hi hii => hid i (Finset.mem_insert_of_mem hi) hii)
            (fun i hi => hmem i (Finset.mem_insert_of_mem hi)) w hw
        rw [hprod]
        exact hid a (Finset.mem_insert_self a t) (by rintro rfl; exact ha h)
          (f i₀ w) (hmem i₀ (Finset.mem_insert_of_mem h) w hw)

private lemma pow_eq_of_apply_eq {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hT3 : T ^ 3 = 1)
    (hTmap : ∀ u ∈ W, T u ∈ W) (hfix : ∀ u ∈ W, T u = u → u = 0) (hWne : W ≠ ⊥)
    {n m : ℕ} (hn : n < 3) (hm : m < 3)
    (h : ∀ u ∈ W, (T ^ n) u = (T ^ m) u) : n = m := by
  obtain ⟨u₀, hu₀W, hu₀ne⟩ := (Submodule.ne_bot_iff W).mp hWne
  have hT_inj : ∀ u ∈ W, ∀ v ∈ W, T u = T v → u = v := by
    intro u hu v hv huv
    have h0 : T (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 : (T ^ 2) (T (u - v)) = 0 := by rw [h0, map_zero]
    have h2 : (T ^ 3) (u - v) = 0 := by
      rw [show T ^ 3 = T ^ 2 * T from pow_succ T 2, Module.End.mul_apply]
      exact h1
    rw [hT3, Module.End.one_apply] at h2
    exact sub_eq_zero.mp h2
  have hTpow_map : ∀ n, ∀ u ∈ W, (T ^ n) u ∈ W := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih => intro u hu; rw [pow_succ', Module.End.mul_apply]; exact hTmap _ (ih u hu)
  have hTpow_inj : ∀ n, ∀ u ∈ W, ∀ v ∈ W, (T ^ n) u = (T ^ n) v → u = v := by
    intro n
    induction n with
    | zero => intro u hu v hv hh; simpa using hh
    | succ n ih =>
        intro u hu v hv hh
        rw [pow_succ, Module.End.mul_apply] at hh
        exact hT_inj u hu v hv (ih (T u) (hTmap u hu) (T v) (hTmap v hv) hh)
  have hle : ∀ n m : ℕ, n ≤ m → m < 3 → (∀ u ∈ W, (T ^ n) u = (T ^ m) u) → n = m := by
    intro n m hnm hm h'
    rcases eq_or_lt_of_le hnm with rfl | hlt
    · rfl
    · exfalso
      have hd_id : ∀ u ∈ W, (T ^ (m - n)) u = u := by
        intro u hu
        have h1 : (T ^ n) u = (T ^ (n + (m - n))) u := by
          rw [Nat.add_sub_of_le hnm]; exact h' u hu
        rw [pow_add, Module.End.mul_apply] at h1
        exact (hTpow_inj n u hu ((T ^ (m - n)) u) (hTpow_map (m - n) u hu) h1).symm
      have hcases : m - n = 1 ∨ m - n = 2 := by
        have hlt3 : m - n < 3 := lt_of_le_of_lt (Nat.sub_le m n) hm
        have hpos : 0 < m - n := Nat.sub_pos_of_lt hlt
        omega
      rcases hcases with h1 | h2
      · exact hu₀ne (hfix u₀ hu₀W (by simpa [h1] using hd_id u₀ hu₀W))
      · have hT2 : (T ^ 2) u₀ = u₀ := by simpa [h2] using hd_id u₀ hu₀W
        have hcong := congrArg (fun w => T w) hT2
        have heq : T ((T ^ 2) u₀) = (T ^ 3) u₀ := by
          rw [← Module.End.mul_apply, ← pow_succ']
        rw [heq, hT3, Module.End.one_apply] at hcong
        exact hu₀ne (hfix u₀ hu₀W hcong.symm)
  rcases le_total n m with hnm | hnm
  · exact hle n m hnm hm h
  · exact (hle m n hnm hn (fun u hu => (h u hu).symm)).symm

theorem genMax_card_eq_pow_pieces {K : Type} [Field K] [Finite K] [CharP K 2]
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {S : Finset (GL (Fin (2 * 4)) K)} (hS : GenPieceSet (polB (coordinateQuadPlus 4 K)) A S)
    (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1) :
    Nat.card A = 3 ^ S.card := by
  classical
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have hzex : ∀ y : S, ∃ g : GL (Fin (2 * 4)) K, g ∈ A ∧
      (∀ w ∈ grng (y : GL (Fin (2 * 4)) K), glin g w = glin (y : GL (Fin (2 * 4)) K) w) ∧
      (∀ v ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
          (polB (coordinateQuadPlus 4 K)), glin g v = v) := by
    intro y
    exact GenMax.exists_mem_restrict (W := grng (y : GL (Fin (2 * 4)) K))
      (c := (y : GL (Fin (2 * 4)) K)) hA
      (nondegOn_grng hA (hS.mem y.1 y.2))
      (fun a ha w hw => grng_inv hA (hS.mem y.1 y.2) ha w hw)
      (hS.mem y.1 y.2)
  choose z hzA hzrest using hzex
  have hzag : ∀ y : S, ∀ w ∈ grng (y : GL (Fin (2 * 4)) K),
      glin (z y) w = glin (y : GL (Fin (2 * 4)) K) w := fun y => (hzrest y).1
  have hzor : ∀ y : S, ∀ v ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
      (polB (coordinateQuadPlus 4 K)), glin (z y) v = v := fun y => (hzrest y).2
  have hzcomm : ∀ y y' : S, y ≠ y' → Commute (z y) (z y') := by
    intro y y' hyne
    have hyA : (y : GL (Fin (2 * 4)) K) ∈ A := hS.mem y.1 y.2
    have hy'A : (y' : GL (Fin (2 * 4)) K) ∈ A := hS.mem y'.1 y'.2
    have hyne' : (y : GL (Fin (2 * 4)) K) ≠ (y' : GL (Fin (2 * 4)) K) :=
      fun h => hyne (Subtype.ext h)
    have hW : SUTB.NondegOn (polB (coordinateQuadPlus 4 K)) (grng (y : GL (Fin (2 * 4)) K)) :=
      nondegOn_grng hA hyA
    have hsub : grng (y : GL (Fin (2 * 4)) K) ≤
        (grng (y' : GL (Fin (2 * 4)) K)).orthogonalBilin (polB (coordinateQuadPlus 4 K)) := by
      intro u hu
      rw [Submodule.mem_orthogonalBilin]
      intro w hw
      exact hS.orth y' y'.2 y y.2 (fun h => hyne' h.symm) w hw u hu
    have hz'y_fix : ∀ w ∈ grng (y : GL (Fin (2 * 4)) K), glin (z y') w = w :=
      fun w hw => hzor y' w (hsub hw)
    have hzy_orth : ∀ v ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
        (polB (coordinateQuadPlus 4 K)), glin (z y) v = v :=
      fun v hv => hzor y v hv
    have hz'y_mem_orth : ∀ v ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
        (polB (coordinateQuadPlus 4 K)), glin (z y') v ∈
        (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin (polB (coordinateQuadPlus 4 K)) := by
      intro v hv
      rw [Submodule.mem_orthogonalBilin] at hv ⊢
      intro w hw
      have hinv : glin ((z y')⁻¹) w = w := by
        have h1 : glin ((z y')⁻¹) (glin (z y') w) = w := by
          rw [← Module.End.mul_apply, ← glin_mul, inv_mul_cancel, glin_one,
            Module.End.one_apply]
        rwa [hz'y_fix w hw] at h1
      have hiso := hA.iso (z y') (hzA y')
      have hweq : w = glin (z y') (glin ((z y')⁻¹) w) := by
        rw [hinv, hz'y_fix w hw]
      calc (polB (coordinateQuadPlus 4 K)) w (glin (z y') v)
          = (polB (coordinateQuadPlus 4 K)) (glin (z y') (glin ((z y')⁻¹) w))
              (glin (z y') v) := by nth_rewrite 1 [hweq]; rfl
        _ = (polB (coordinateQuadPlus 4 K)) (glin ((z y')⁻¹) w) v := hiso _ v
        _ = (polB (coordinateQuadPlus 4 K)) w v := by rw [hinv]
        _ = 0 := hv w hw
    have hzy_mem : ∀ w ∈ grng (y : GL (Fin (2 * 4)) K),
        glin (z y) w ∈ grng (y : GL (Fin (2 * 4)) K) :=
      fun w hw => grng_inv hA hyA (hzA y) w hw
    have hz'y_mem : ∀ w ∈ grng (y : GL (Fin (2 * 4)) K),
        glin (z y') w ∈ grng (y : GL (Fin (2 * 4)) K) :=
      fun w hw => by rw [hz'y_fix w hw]; exact hw
    have heq : glin (z y) * glin (z y') = glin (z y') * glin (z y) := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨m, hm, n, hn, rfl⟩ := SUTB.exists_add_orth hW v
      simp only [Module.End.mul_apply, map_add]
      rw [hz'y_fix m hm, hz'y_fix (glin (z y) m) (hzy_mem m hm),
        hzy_orth n hn, hzy_orth (glin (z y') n) (hz'y_mem_orth n hn)]
    exact glin_injective (by rw [glin_mul, glin_mul]; exact heq)
  have hcommG : ∀ k : S → ZMod 3,
      ((Finset.univ : Finset S) : Set S).Pairwise
        (fun a b => Commute ((z a) ^ ((k a).val)) ((z b) ^ ((k b).val))) := by
    intro k y _ y' _ hyne
    exact (hzcomm y y' hyne).pow_pow _ _
  let thetaG : (S → ZMod 3) → GL (Fin (2 * 4)) K :=
    fun k => (Finset.univ : Finset S).noncommProd (fun y => (z y) ^ ((k y).val)) (hcommG k)
  have htheta_mem : ∀ k : S → ZMod 3, thetaG k ∈ A := by
    intro k
    exact Submonoid.noncommProd_mem A.toSubmonoid (Finset.univ : Finset S)
      (fun y => (z y) ^ ((k y).val)) (hcommG k) (fun y _ => pow_mem (hzA y) ((k y).val))
  let theta : (S → ZMod 3) → A := fun k => ⟨thetaG k, htheta_mem k⟩
  have htheta_apply : ∀ (k : S → ZMod 3) (y₀ : S) {u : Fin (2 * 4) → K},
      u ∈ grng (y₀ : GL (Fin (2 * 4)) K) →
      glin (thetaG k) u = ((glin (y₀ : GL (Fin (2 * 4)) K)) ^ ((k y₀).val)) u := by
    intro k y₀ u hu
    change (glinHom K (2 * 4))
        ((Finset.univ : Finset S).noncommProd (fun y => (z y) ^ ((k y).val)) (hcommG k)) u =
      ((glin (y₀ : GL (Fin (2 * 4)) K)) ^ ((k y₀).val)) u
    let commMap : ((Finset.univ : Finset S) : Set S).Pairwise
        (fun a b => Commute (glin ((z a) ^ ((k a).val))) (glin ((z b) ^ ((k b).val)))) :=
      fun y _ y' _ hyne => ((hzcomm y y' hyne).pow_pow _ _).map (glinHom K (2 * 4))
    have hmap := Finset.map_noncommProd (Finset.univ : Finset S)
      (fun y : S => (z y) ^ ((k y).val)) (hcommG k) (glinHom K (2 * 4))
    rw [hmap]
    have hid : ∀ y ∈ (Finset.univ : Finset S), y ≠ y₀ →
        ∀ w ∈ grng (y₀ : GL (Fin (2 * 4)) K),
        glin ((z y) ^ ((k y).val)) w = w := by
      intro y _ hyne w hw
      rw [glin_pow]
      have hzid : glin (z y) w = w := by
        have hw_orth : w ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
            (polB (coordinateQuadPlus 4 K)) := by
          rw [Submodule.mem_orthogonalBilin]
          intro u' hu'
          exact hS.orth y y.2 y₀ y₀.2 (fun h => hyne (Subtype.ext h)) u' hu' w hw
        exact hzor y w hw_orth
      have hzpow : ∀ n : ℕ, ((glin (z y)) ^ n) w = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hzid]
      exact hzpow ((k y).val)
    have hmem : ∀ y ∈ (Finset.univ : Finset S),
        ∀ w ∈ grng (y₀ : GL (Fin (2 * 4)) K),
        glin ((z y) ^ ((k y).val)) w ∈ grng (y₀ : GL (Fin (2 * 4)) K) := by
      intro y _ w hw
      by_cases hy : y = y₀
      · rw [hy]
        have hzmap : ∀ v ∈ grng (y₀ : GL (Fin (2 * 4)) K),
            glin (z y₀) v ∈ grng (y₀ : GL (Fin (2 * 4)) K) := by
          intro v hv
          rw [hzag y₀ v hv]
          exact grng_inv hA (hS.mem y₀.1 y₀.2) (hS.mem y₀.1 y₀.2) v hv
        have hzpow : ∀ n : ℕ,
            ((glin (z y₀)) ^ n) w ∈ grng (y₀ : GL (Fin (2 * 4)) K) := by
          intro n
          induction n with
          | zero => simpa using hw
          | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hzmap _ ih
        rw [glin_pow]
        exact hzpow ((k y₀).val)
      · have hw_orth : w ∈ (grng (y : GL (Fin (2 * 4)) K)).orthogonalBilin
            (polB (coordinateQuadPlus 4 K)) := by
          rw [Submodule.mem_orthogonalBilin]
          intro u' hu'
          exact hS.orth y y.2 y₀ y₀.2 (fun h => hy (Subtype.ext h)) u' hu' w hw
        have hzid : glin (z y) w = w := hzor y w hw_orth
        have hzpow : ∀ n : ℕ, ((glin (z y)) ^ n) w = w := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hzid]
        rw [glin_pow, hzpow ((k y).val)]
        exact hw
    refine (noncommProd_apply_eq_of_forall (Finset.univ : Finset S)
      (fun y : S => (glinHom K (2 * 4)) ((z y) ^ ((k y).val))) (comm := ?_) y₀
      (grng (y₀ : GL (Fin (2 * 4)) K)) (Finset.mem_univ y₀) hid hmem u hu).trans ?_
    rw [map_pow]
    have hTy_map : ∀ n : ℕ, ∀ v ∈ grng (y₀ : GL (Fin (2 * 4)) K),
        ((glin (y₀ : GL (Fin (2 * 4)) K)) ^ n) v ∈ grng (y₀ : GL (Fin (2 * 4)) K) := by
      intro n
      induction n with
      | zero => intro v hv; simpa using hv
      | succ n ih =>
          intro v hv
          rw [pow_succ', Module.End.mul_apply]
          exact grng_inv hA (hS.mem y₀.1 y₀.2) (hS.mem y₀.1 y₀.2) _ (ih v hv)
    have hzpow_y₀ : ∀ n : ℕ,
        ((glin (z y₀)) ^ n) u = ((glin (y₀ : GL (Fin (2 * 4)) K)) ^ n) u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
          exact hzag y₀ (((glin (y₀ : GL (Fin (2 * 4)) K)) ^ n) u) (hTy_map n u hu)
    exact hzpow_y₀ ((k y₀).val)
  have hinj : Function.Injective theta := by
    intro k k' hkk
    have hG : thetaG k = thetaG k' := congrArg Subtype.val hkk
    funext y
    apply ZMod.val_injective 3
    have hyA : (y : GL (Fin (2 * 4)) K) ∈ A := hS.mem y.1 y.2
    have hT3 : (glin (y : GL (Fin (2 * 4)) K)) ^ 3 = 1 := by
      rw [← glin_pow, hA.pow (y : GL (Fin (2 * 4)) K) hyA, glin_one]
    have hTmap : ∀ u ∈ grng (y : GL (Fin (2 * 4)) K),
        glin (y : GL (Fin (2 * 4)) K) u ∈ grng (y : GL (Fin (2 * 4)) K) :=
      fun u hu => grng_inv hA hyA hyA u hu
    have hfix : ∀ u ∈ grng (y : GL (Fin (2 * 4)) K),
        glin (y : GL (Fin (2 * 4)) K) u = u → u = 0 :=
      fun u hu => eq_zero_of_mem_grng hA hyA hu
    have h_eq : ∀ u ∈ grng (y : GL (Fin (2 * 4)) K),
        ((glin (y : GL (Fin (2 * 4)) K)) ^ ((k y).val)) u =
        ((glin (y : GL (Fin (2 * 4)) K)) ^ ((k' y).val)) u := by
      intro u hu
      have h1 := htheta_apply k y hu
      have h2 := htheta_apply k' y hu
      rw [hG, h2] at h1
      exact h1.symm
    exact pow_eq_of_apply_eq (glin (y : GL (Fin (2 * 4)) K))
      (grng (y : GL (Fin (2 * 4)) K)) hT3 hTmap hfix
      (grng_ne_bot (hS.ne_one y.1 y.2))
      (ZMod.val_lt (k y)) (ZMod.val_lt (k' y)) h_eq
  have hsurj : Function.Surjective theta := by
    intro c
    choose kk hkk using fun y : S => hS.cyc y.1 y.2 c.1 c.2
    let k : S → ZMod 3 := fun y => (kk y : ZMod 3)
    refine ⟨k, ?_⟩
    let d : A := c * (theta k)⁻¹
    have htriv : ∀ v ∈ genPieceSpan S, glin (d : GL (Fin (2 * 4)) K) v = v := by
      have hle : genPieceSpan S ≤ LinearMap.ker (glin (d : GL (Fin (2 * 4)) K) - 1) := by
        unfold genPieceSpan
        refine iSup₂_le fun y hy => ?_
        let yS : S := ⟨y, hy⟩
        intro u hu
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        have hyA : (y : GL (Fin (2 * 4)) K) ∈ A := hS.mem y hy
        have hinvA : (thetaG k)⁻¹ ∈ A := A.inv_mem (htheta_mem k)
        have hw : glin ((thetaG k)⁻¹) u ∈ grng (y : GL (Fin (2 * 4)) K) :=
          grng_inv hA hyA hinvA u hu
        have hdapply : glin (d : GL (Fin (2 * 4)) K) u =
            glin c.1 (glin ((thetaG k)⁻¹) u) := by
          show glin (c.1 * (thetaG k)⁻¹) u = _
          rw [glin_mul, Module.End.mul_apply]
        rw [hdapply]
        have hc := hkk yS (glin ((thetaG k)⁻¹) u) hw
        have hth := htheta_apply k yS hw
        have hykk : (y : GL (Fin (2 * 4)) K) ^ (kk yS) =
            (y : GL (Fin (2 * 4)) K) ^ ((k yS).val) := by
          rw [pow_eq_pow_mod (kk yS) (hA.pow (y : GL (Fin (2 * 4)) K) hyA)]
          congr 1
        have hcw : glin c.1 (glin ((thetaG k)⁻¹) u) =
            glin (thetaG k) (glin ((thetaG k)⁻¹) u) := by
          rw [hc, hth, ← glin_pow, hykk]
        have hcancel : glin (thetaG k) (glin ((thetaG k)⁻¹) u) = u := by
          rw [← Module.End.mul_apply, ← glin_mul, mul_inv_cancel, glin_one,
            Module.End.one_apply]
        rw [hcw, hcancel]
      intro v hv
      have := hle hv
      simpa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using this
    have hd1G : (d : GL (Fin (2 * 4)) K) = 1 := hterm (d : GL (Fin (2 * 4)) K) d.2 htriv
    have hd1 : d = 1 := Subtype.ext hd1G
    have hc_eq : c = theta k := by
      have h : c.1 * (thetaG k)⁻¹ = 1 := by simpa [d] using hd1G
      have h2 : c.1 = thetaG k := by
        simpa [mul_assoc] using congrArg (fun x : GL (Fin (2 * 4)) K => x * thetaG k) h
      exact Subtype.ext h2
    exact hc_eq.symm
  have hcard : Nat.card A = Nat.card (S → ZMod 3) :=
    (Nat.card_congr (Equiv.ofBijective theta ⟨hinj, hsurj⟩)).symm
  rw [hcard, Nat.card_fun]
  rw [Nat.subtype_card S (fun x => Iff.rfl), Nat.card_eq_fintype_card, ZMod.card]

end CFSG.StandardType
