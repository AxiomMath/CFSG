module

public import CFSG.RankThree.PartOne.KF.D8Ctx
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

variable {p : ℕ} {K : Type} [Field K]

@[expose] def d8Ev (c : Fin 5) (v : D8Mod p K) : Kˣ :=
  match c with
  | 0 => ((v.1 : rootsOfUnity p K) : Kˣ)
  | 1 => ((v.2 : rootsOfUnity p K) : Kˣ)
  | 2 => ((v.2 : rootsOfUnity p K) : Kˣ)⁻¹
  | 3 => ((v.1 : rootsOfUnity p K) : Kˣ)⁻¹
  | 4 => 1

@[expose] def d8Rho (c : Fin 5) : Fin 5 :=
  match c with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4

@[expose] def d8RotCls (c : Fin 5) : Fin 5 :=
  match c with
  | 0 => 1
  | 1 => 3
  | 2 => 0
  | 3 => 2
  | 4 => 4

@[expose] def d8RefCls (c : Fin 5) : Fin 5 :=
  match c with
  | 0 => 3
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 4

theorem d8Ev_mul_rho (c : Fin 5) (v : D8Mod p K) : d8Ev c v * d8Ev (d8Rho c) v = 1 := by
  fin_cases c <;> simp [d8Ev, d8Rho]

theorem d8Ev_mul (c : Fin 5) (v w : D8Mod p K) : d8Ev c (v * w) = d8Ev c v * d8Ev c w := by
  fin_cases c <;> simp [d8Ev, mul_comm]

theorem d8Ev_one (c : Fin 5) : d8Ev c (1 : D8Mod p K) = 1 := by
  fin_cases c <;> simp [d8Ev]

theorem d8Ev_rot (c : Fin 5) (v : D8Mod p K) :
    d8Ev c (d8Rot v) = d8Ev (d8RotCls c) v := by
  fin_cases c <;> simp [d8Ev, d8RotCls, d8Rot_apply]

theorem d8Ev_ref (c : Fin 5) (v : D8Mod p K) :
    d8Ev c (d8Ref v) = d8Ev (d8RefCls c) v := by
  fin_cases c <;> simp [d8Ev, d8RefCls, d8Ref_apply]

theorem d8Ev_ne (z : rootsOfUnity p K) (hz1 : z ≠ 1) (hz2 : z ^ 2 ≠ 1) :
    ∀ a b : Fin 5, a ≠ b → ∃ v : D8Mod p K, d8Ev a v ≠ d8Ev b v := by
  have h1 : ((z : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h2 : ((z : rootsOfUnity p K) : Kˣ)⁻¹ ≠ ((z : rootsOfUnity p K) : Kˣ) := by
    intro h
    apply hz2
    apply Subtype.ext
    have : ((z : rootsOfUnity p K) : Kˣ) * ((z : rootsOfUnity p K) : Kˣ) = 1 := by
      nth_rewrite 1 [← h]
      exact inv_mul_cancel _
    simpa [pow_two] using this
  have h3 : ((z : rootsOfUnity p K) : Kˣ)⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have key : ∀ a b : Fin 5, a ≠ b →
      (d8Ev a (z, 1) ≠ d8Ev b (z, 1) ∨ d8Ev a (1, z) ≠ d8Ev b (1, z)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [d8Ev, h1, h2, h3, h1.symm, h2.symm, h3.symm] at hab ⊢
  intro a b hab
  rcases key a b hab with h | h
  · exact ⟨(z, 1), h⟩
  · exact ⟨(1, z), h⟩

theorem d8Ev_mul_ne_one (z : rootsOfUnity p K) (hz1 : z ≠ 1) (hz2 : z ^ 2 ≠ 1) :
    ∀ a b : Fin 5, b ≠ d8Rho a → ∃ v : D8Mod p K, d8Ev a v * d8Ev b v ≠ 1 := by
  have h1 : ((z : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h2 : ((z : rootsOfUnity p K) : Kˣ) * ((z : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h =>
    hz2 (Subtype.ext (by simpa [pow_two] using h))
  have h3 : ((z : rootsOfUnity p K) : Kˣ)⁻¹ ≠ 1 := inv_ne_one.mpr h1
  have h4 : ((z : rootsOfUnity p K) : Kˣ)⁻¹ * ((z : rootsOfUnity p K) : Kˣ)⁻¹ ≠ 1 := by
    rw [← mul_inv]; exact inv_ne_one.mpr h2
  have key : ∀ a b : Fin 5, b ≠ d8Rho a →
      (d8Ev a (z, 1) * d8Ev b (z, 1) ≠ 1 ∨ d8Ev a (1, z) * d8Ev b (1, z) ≠ 1) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [d8Rho, d8Ev, h1, h2, h3, h4] at hab ⊢
  intro a b hab
  rcases key a b hab with h | h
  · exact ⟨(z, 1), h⟩
  · exact ⟨(1, z), h⟩

@[expose] def d8Cls (n : ℕ) [NeZero n] (i : Fin n) : Fin 5 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = Fin.rev 1 then 2
  else if i = Fin.rev 0 then 3 else 4

@[expose] def d8Vec (n : ℕ) [NeZero n] (v : D8Mod p K) : Fin n → Kˣ := fun i =>
  d8Ev (d8Cls n i) v

@[expose] def d8VecHom (n : ℕ) [NeZero n] : D8Mod p K →* (Fin n → Kˣ) where
  toFun := d8Vec n
  map_one' := funext fun _ => d8Ev_one _
  map_mul' v w := funext fun _ => d8Ev_mul _ v w

@[expose] def d8RotPerm (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) :=
  Equiv.swap 0 (Fin.rev 1) * Equiv.swap (Fin.rev 1) (Fin.rev 0) * Equiv.swap (Fin.rev 0) 1

@[expose] def d8RefPerm (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) :=
  Equiv.swap 0 (Fin.rev 0)

structure D8Comb (n : ℕ) [NeZero n] : Prop where
  one_ne_zero : (1 : Fin n) ≠ 0
  rot_pow : d8RotPerm n ^ 4 = 1
  ref_sq : d8RefPerm n * d8RefPerm n = 1
  ref_rot : d8RefPerm n * d8RotPerm n * d8RefPerm n = (d8RotPerm n)⁻¹
  cls_inj : ∀ i j : Fin n, i ≠ j → d8Cls n i ≠ d8Cls n j
  cls_rev : ∀ i : Fin n, d8Cls n (Fin.rev i) = d8Rho (d8Cls n i)
  cls_rot : ∀ i : Fin n, d8Cls n ((d8RotPerm n).symm i) = d8RotCls (d8Cls n i)
  cls_ref : ∀ i : Fin n, d8Cls n ((d8RefPerm n).symm i) = d8RefCls (d8Cls n i)

theorem d8Comb_four : D8Comb 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem d8Comb_five : D8Comb 5 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

variable {n : ℕ} [NeZero n]

@[expose] def d8Perm (hc : D8Comb n) : DihedralGroup 4 →* Equiv.Perm (Fin n) :=
  dihedralLift (d8RotPerm n) (d8RefPerm n) hc.rot_pow hc.ref_sq hc.ref_rot

theorem d8Perm_r_one (hc : D8Comb n) : d8Perm hc (DihedralGroup.r 1) = d8RotPerm n := by
  show d8RotPerm n ^ (1 : ZMod 4).val = _
  have : (1 : ZMod 4).val = 1 := by decide
  rw [this, pow_one]

theorem d8Perm_sr_zero (hc : D8Comb n) : d8Perm hc (DihedralGroup.sr 0) = d8RefPerm n := by
  show d8RefPerm n * d8RotPerm n ^ (0 : ZMod 4).val = _
  simp

theorem d8Vec_rot (hc : D8Comb n) (v : D8Mod p K) :
    d8Vec n (d8Rot v) = d8Vec n v ∘ (d8RotPerm n).symm := by
  funext i
  simp only [d8Vec, Function.comp_apply, hc.cls_rot, d8Ev_rot]

theorem d8Vec_ref (hc : D8Comb n) (v : D8Mod p K) :
    d8Vec n (d8Ref v) = d8Vec n v ∘ (d8RefPerm n).symm := by
  funext i
  simp only [d8Vec, Function.comp_apply, hc.cls_ref, d8Ev_ref]

theorem d8Vec_act (hc : D8Comb n) (w : DihedralGroup 4) (v : D8Mod p K) :
    d8Vec n (d8Act w v) = d8Vec n v ∘ (d8Perm hc w).symm := by
  have hmul : ∀ w w' : DihedralGroup 4,
      (∀ v : D8Mod p K, d8Vec n (d8Act w v) = d8Vec n v ∘ (d8Perm hc w).symm) →
      (∀ v : D8Mod p K, d8Vec n (d8Act w' v) = d8Vec n v ∘ (d8Perm hc w').symm) →
      ∀ v : D8Mod p K, d8Vec n (d8Act (w * w') v) = d8Vec n v ∘ (d8Perm hc (w * w')).symm := by
    intro w w' h h' v
    rw [map_mul, map_mul, MulAut.mul_apply, h, h' v]
    funext i
    simp [Equiv.Perm.mul_def]
  have h1 : ∀ v : D8Mod p K, d8Vec n (d8Act 1 v) = d8Vec n v ∘ (d8Perm hc 1).symm := by
    intro v
    rw [map_one, map_one]
    rfl
  have hr1 : ∀ v : D8Mod p K,
      d8Vec n (d8Act (DihedralGroup.r 1) v) = d8Vec n v ∘ (d8Perm hc (DihedralGroup.r 1)).symm := by
    intro v
    rw [d8Perm_r_one, d8Act_r_one]
    exact d8Vec_rot hc v
  have hs0 : ∀ v : D8Mod p K,
      d8Vec n (d8Act (DihedralGroup.sr 0) v) =
        d8Vec n v ∘ (d8Perm hc (DihedralGroup.sr 0)).symm := by
    intro v
    rw [d8Perm_sr_zero, d8Act_sr_zero]
    exact d8Vec_ref hc v
  have e2 : (DihedralGroup.r 2 : DihedralGroup 4) = DihedralGroup.r 1 * DihedralGroup.r 1 := by
    decide
  have e3 : (DihedralGroup.r 3 : DihedralGroup 4) =
      DihedralGroup.r 1 * DihedralGroup.r 1 * DihedralGroup.r 1 := by decide
  have f1 : (DihedralGroup.sr 1 : DihedralGroup 4) = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
    decide
  have f2 : (DihedralGroup.sr 2 : DihedralGroup 4) =
      DihedralGroup.sr 0 * (DihedralGroup.r 1 * DihedralGroup.r 1) := by decide
  have f3 : (DihedralGroup.sr 3 : DihedralGroup 4) =
      DihedralGroup.sr 0 * (DihedralGroup.r 1 * DihedralGroup.r 1 * DihedralGroup.r 1) := by
    decide
  rcases dihedral_four_cases w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [DihedralGroup.r_zero]
    exact h1 v
  · exact hr1 v
  · rw [e2]
    exact hmul _ _ hr1 hr1 v
  · rw [e3]
    exact hmul _ _ (hmul _ _ hr1 hr1) hr1 v
  · exact hs0 v
  · rw [f1]
    exact hmul _ _ hs0 hr1 v
  · rw [f2]
    exact hmul _ _ hs0 (hmul _ _ hr1 hr1) v
  · rw [f3]
    exact hmul _ _ hs0 (hmul _ _ (hmul _ _ hr1 hr1) hr1) v

structure D8Comb2 (hc : D8Comb n) : Prop where
  comm_rev : ∀ (w : DihedralGroup 4) (i : Fin n), d8Perm hc w (Fin.rev i) = Fin.rev (d8Perm hc w i)
  closure : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
    ∃ w : DihedralGroup 4, d8Perm hc w = τ

theorem d8Comb2_four : D8Comb2 d8Comb_four := ⟨by decide +kernel, by decide +kernel⟩

theorem d8Comb2_five : D8Comb2 d8Comb_five := ⟨by decide +kernel, by decide +kernel⟩

theorem d8Vec_mul_rev (hc : D8Comb n) (v : D8Mod p K) (j : Fin n) :
    d8Vec n v j * d8Vec n v (Fin.rev j) = 1 := by
  simp only [d8Vec, hc.cls_rev]
  exact d8Ev_mul_rho _ v

@[expose] def d8Tor (p : ℕ) (K : Type) [Field K] (n : ℕ) [NeZero n] : Subgroup (GL (Fin n) K) :=
  (diagUHom.comp (d8VecHom (p := p) (K := K) n)).range

theorem mem_d8Tor_iff {x : GL (Fin n) K} :
    x ∈ d8Tor p K n ↔ ∃ v : D8Mod p K, diagU (d8Vec n v) = x := Iff.rfl

omit [NeZero n] in
theorem mem_normalizer_subgroupOf_iff {M T : Subgroup (GL (Fin n) K)} (hTM : T ≤ M) (m : ↥M) :
    m ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔
      (∀ x ∈ T, (m : GL (Fin n) K) * x * (m : GL (Fin n) K)⁻¹ ∈ T) ∧
      (∀ x ∈ T, (m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K) ∈ T) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact (h ⟨x, hTM hx⟩).mp hx
    · have h1 : (⟨(m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ : ↥M) ∈ T.subgroupOf M ↔ _ := h _
      have h2 : m * ⟨(m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ * m⁻¹ = ⟨x, hTM hx⟩ := by
        apply Subtype.ext
        show (m : GL (Fin n) K) * ((m : GL (Fin n) K)⁻¹ * x * (m : GL (Fin n) K)) *
          (m : GL (Fin n) K)⁻¹ = x
        group
      rw [h2] at h1
      exact h1.mpr hx
  · rintro ⟨h1, h2⟩ y
    constructor
    · intro hy
      exact h1 _ hy
    · intro hy
      have h4 := h2 ((m * y * m⁻¹ : ↥M) : GL (Fin n) K) hy
      have h3 : (m : GL (Fin n) K)⁻¹ * ((m * y * m⁻¹ : ↥M) : GL (Fin n) K) *
          (m : GL (Fin n) K) = (y : GL (Fin n) K) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3] at h4
      exact h4

theorem exists_d8ctx (hc : D8Comb n) (hc2 : D8Comb2 hc) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (M : Subgroup (GL (Fin n) K))
    (hT : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ M)
    (hP : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin n) K) ∈ M) :
    Nonempty (D8Ctx p K (⊤ : Subgroup ↥M) ((d8Tor p K n).subgroupOf M)) := by
  classical
  set T : Subgroup (GL (Fin n) K) := d8Tor p K n with hTdef
  have hTM : T ≤ M := by
    rintro _ ⟨v, rfl⟩
    exact hT v
  obtain ⟨ζ, hζ'⟩ := hζ
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ'.pow_eq_one⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have h0 : ζ = 1 := congrArg Subtype.val h
    rw [h0] at hζ'
    have := hζ'.eq_orderOf
    rw [orderOf_one] at this
    exact hp.ne_one this
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    exact hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h)
  have hdist : ∀ i j : Fin n, i ≠ j → ∃ x ∈ T, ent x i i ≠ ent x j j := by
    intro i j hij
    obtain ⟨v, hv⟩ := d8Ev_ne z hz1 hz2 _ _ (hc.cls_inj i j hij)
    refine ⟨diagU (d8Vec n v), ⟨v, rfl⟩, ?_⟩
    simp only [ent, diagU_apply_same]
    intro h
    exact hv (Units.ext h)
  have hpair : ∀ i j : Fin n, j ≠ Fin.rev i →
      ∃ v : D8Mod p K, d8Vec n v i * d8Vec n v j ≠ 1 := by
    intro i j hij
    have : d8Cls n j ≠ d8Rho (d8Cls n i) := by
      rw [← hc.cls_rev]
      exact hc.cls_inj _ _ hij
    exact d8Ev_mul_ne_one z hz1 hz2 _ _ this
  have hdmem : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ T := fun v => ⟨v, rfl⟩
  let torh : D8Mod p K →* ↥(T.subgroupOf M) :=
    { toFun := fun v => ⟨⟨diagU (d8Vec n v), hT v⟩, hdmem v⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show diagU (d8Vec n 1) = 1
        have : d8Vec (p := p) (K := K) n 1 = 1 := (d8VecHom n).map_one
        rw [this]
        exact diagU_one
      map_mul' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        show diagU (d8Vec n (v * w)) = diagU (d8Vec n v) * diagU (d8Vec n w)
        have : d8Vec (p := p) (K := K) n (v * w) = d8Vec n v * d8Vec n w :=
          (d8VecHom n).map_mul v w
        rw [this, ← diagU_mul] }
  have hinj : Function.Injective torh := by
    intro v w h
    have h1 : d8Vec n v = d8Vec n w :=
      diagU_injective (congrArg (fun x : ↥(T.subgroupOf M) => ((x : ↥M) : GL (Fin n) K)) h)
    have h0 : ∀ u : D8Mod p K, d8Vec n u 0 = ((u.1 : rootsOfUnity p K) : Kˣ) := fun u => by
      simp [d8Vec, d8Cls, d8Ev]
    have h1' : ∀ u : D8Mod p K, d8Vec n u 1 = ((u.2 : rootsOfUnity p K) : Kˣ) := fun u => by
      simp [d8Vec, d8Cls, d8Ev, hc.one_ne_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [← h0 v, ← h0 w, h1]
    · rw [← h1' v, ← h1' w, h1]
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨v, hv⟩ := hxT
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  let tor : D8Mod p K ≃* ↥(T.subgroupOf M) := MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  have hcoe : ∀ v, (((tor v : ↥(T.subgroupOf M)) : ↥M) : GL (Fin n) K) = diagU (d8Vec n v) :=
    fun v => rfl
  have hconj : ∀ (γ : DihedralGroup 4) (v : D8Mod p K),
      (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
        (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = diagU (d8Vec n (d8Act γ v)) := by
    intro γ v
    rw [permGL_conj_diagU, d8Vec_act hc]
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · intro γ
    set g : ↥M := ⟨permGL (d8Perm hc γ), hP _ (hc2.comm_rev γ)⟩ with hgdef
    have hg : g ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      rw [mem_normalizer_subgroupOf_iff hTM]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨v, rfl⟩ := hx
        show (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
          (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ ∈ T
        rw [hconj]
        exact hdmem _
      · obtain ⟨v, rfl⟩ := hx
        show (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ * diagU (d8Vec n v) *
          (permGL (d8Perm hc γ) : GL (Fin n) K) ∈ T
        have h1 : (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = permGL (d8Perm hc γ⁻¹) := by
          rw [map_inv, map_inv]
        have h2 : (permGL (d8Perm hc γ) : GL (Fin n) K) =
            (permGL (d8Perm hc γ⁻¹) : GL (Fin n) K)⁻¹ := by
          rw [map_inv, map_inv, inv_inv]
        rw [h1, h2, hconj]
        exact hdmem _
    refine ⟨g, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    show (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
      (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = diagU (d8Vec n (d8Act γ v))
    exact hconj γ v
  · intro m hm _
    obtain ⟨h1, h2⟩ := (mem_normalizer_subgroupOf_iff hTM m).mp hm
    obtain ⟨τ, -, -, hτ⟩ := exists_perm_of_normalizes T
      (fun x hx => by obtain ⟨v, rfl⟩ := hx; exact isDiag_diagU _) hdist h1 h2
    have hτv : ∀ v : D8Mod p K, ∃ v' : D8Mod p K, diagU (d8Vec n v') =
        (m : GL (Fin n) K) * diagU (d8Vec n v) * (m : GL (Fin n) K)⁻¹ ∧
        d8Vec n v' = d8Vec n v ∘ τ.symm := by
      intro v
      obtain ⟨v', hv'⟩ := h1 (diagU (d8Vec n v)) ⟨v, rfl⟩
      have hv'' : diagU (d8Vec n v') = (m : GL (Fin n) K) * diagU (d8Vec n v) *
          (m : GL (Fin n) K)⁻¹ := hv'
      refine ⟨v', hv'', funext fun i => ?_⟩
      have h3 := hτ (diagU (d8Vec n v)) ⟨v, rfl⟩ (τ.symm i)
      rw [Equiv.apply_symm_apply, ← hv''] at h3
      simp only [ent, diagU_apply_same] at h3
      exact Units.ext h3
    have hτrev : ∀ j, τ.symm (Fin.rev j) = Fin.rev (τ.symm j) := by
      intro j
      by_contra hne
      obtain ⟨v, hv⟩ := hpair (τ.symm j) (τ.symm (Fin.rev j)) hne
      obtain ⟨v', -, hv'⟩ := hτv v
      apply hv
      have h4 := d8Vec_mul_rev hc v' j
      rw [hv'] at h4
      exact h4
    have hτc : ∀ i, τ (Fin.rev i) = Fin.rev (τ i) := by
      intro i
      have h5 := hτrev (τ i)
      rw [Equiv.symm_apply_apply] at h5
      have h6 := congrArg τ h5
      rw [Equiv.apply_symm_apply] at h6
      exact h6.symm
    obtain ⟨w, hw⟩ := hc2.closure τ hτc
    refine ⟨w, MulEquiv.ext fun t => ?_⟩
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    obtain ⟨v', hv'1, hv'2⟩ := hτv v
    apply Subtype.ext
    apply Subtype.ext
    show (m : GL (Fin n) K) * diagU (d8Vec n v) * (m : GL (Fin n) K)⁻¹ =
      diagU (d8Vec n (d8Act w v))
    rw [← hv'1, d8Vec_act hc, hw, hv'2]

theorem d8Vec_pow_eq_one (v : D8Mod p K) : d8Vec n v ^ p = 1 := by
  funext i
  have h1 : (((v.1 : rootsOfUnity p K) : Kˣ)) ^ p = 1 := (mem_rootsOfUnity p _).mp v.1.2
  have h2 : (((v.2 : rootsOfUnity p K) : Kˣ)) ^ p = 1 := (mem_rootsOfUnity p _).mp v.2.2
  simp only [d8Vec, Pi.pow_apply, Pi.one_apply]
  generalize d8Cls n i = c
  fin_cases c <;> simp [d8Ev, inv_pow, h1, h2]

end CFSG.RankThree.PartOne.KFU
