module

public import CFSG.RankThree.PartOne.S11c.EvenOrthPairs
public import CFSG.RankThree.PartOne.S11c.EvenClassical
public import CFSG.RankThree.PartOne.S11c.PSU3InPSL2

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

section Bridge

theorem four_le_localRank_of_cube_witness {H : Type} [Group H] [Finite H] {X : Subgroup H}
    {T : Type} [Group T] (η : X →* T) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center X) {A : Type} [Group A] (hA : IsElementaryAbelian 3 A)
    (hAcard : Nat.card A = 3 ^ 6) (θ : A →* T) (hθ : Function.Injective θ) {s : T} (hs1 : s ≠ 1)
    (hs2 : s ^ 2 = 1) (hsθ : ∀ a, s * θ a = θ a * s) : 4 ≤ localRank 3 H := by
  have hel : IsElementaryAbelian 3 θ.range :=
    isElementaryAbelian_of_mulEquiv_lift (MonoidHom.ofInjective hθ) hA
  have hcard : Nat.card θ.range = 3 ^ 6 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv).symm
  obtain ⟨z, hz2, hz1, V, hV, hVel, r, hr, hVcard⟩ :=
    exists_rank_four_of_central_witness η hη hker Nat.prime_three (by norm_num) hel hcard
      (le_refl 6) hs1 hs2 (fun u hu => by
        obtain ⟨a, rfl⟩ := hu
        exact hsθ a)
  exact le_localRank_of_rank_four_witness (G := H) (Y := X) Nat.prime_three.one_lt
    ⟨z, hz2, hz1, V, hV, hVel, r, hr, hVcard⟩

theorem isElementaryAbelian_pi_cube :
    IsElementaryAbelian 3 (Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) ∧
      Nat.card (Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) = 3 ^ 6 := by
  refine ⟨?_, ?_⟩
  · refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    funext j
    have h3 : ∀ u : ZMod 3, 3 * u = 0 := fun u => by
      have : (3 : ZMod 3) = 0 := by decide
      rw [this, zero_mul]
    apply Multiplicative.toAdd.injective
    rw [Pi.pow_apply, Pi.one_apply, toAdd_pow, toAdd_one]
    ext
    · simpa using h3 (Multiplicative.toAdd (a j)).1
    · simpa using h3 (Multiplicative.toAdd (a j)).2
  · rw [Nat.card_pi]
    simp [Nat.card_eq_fintype_card, ZMod.card]

end Bridge

section Witness

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : (ι → K) → K} {m : ℕ} (P : PairSys K ι Q m) (hm : 9 ≤ m)

@[expose] def pa (b : Fin 4) : Fin m := ⟨2 * b.val, by have := b.2; omega⟩

@[expose] def pb (b : Fin 4) : Fin m := ⟨2 * b.val + 1, by have := b.2; omega⟩

include hm in
theorem pa_ne_pb (b : Fin 4) : (pa hm b : Fin m) ≠ pb hm b := by
  intro h
  have := congrArg Fin.val h
  simp [pa, pb] at this

@[expose] def blk (b : Fin 4) : Fin 4 ↪ ι := P.blockEmb (pa_ne_pb hm b)

theorem pa_ne_pa {b b' : Fin 4} (h : b ≠ b') : pa (m := m) hm b ≠ pa hm b' := by
  intro e
  apply h
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [pa] at this
  omega

theorem pa_ne_pb' {b b' : Fin 4} (h : b ≠ b') : pa (m := m) hm b ≠ pb hm b' := by
  intro e
  apply h
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [pa, pb] at this
  omega

theorem pb_ne_pa {b b' : Fin 4} (h : b ≠ b') : pb (m := m) hm b ≠ pa hm b' := by
  intro e
  apply h
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [pa, pb] at this
  omega

theorem pb_ne_pb {b b' : Fin 4} (h : b ≠ b') : pb (m := m) hm b ≠ pb hm b' := by
  intro e
  apply h
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [pb] at this
  omega

theorem blk_disjoint {b b' : Fin 4} (h : b ≠ b') : ∀ s t, blk P hm b s ≠ blk P hm b' t := by
  obtain ⟨a1, a2, a3, a4⟩ := P.four_ne (pa_ne_pa hm h)
  obtain ⟨b1, b2, b3, b4⟩ := P.four_ne (pa_ne_pb' hm h)
  obtain ⟨c1, c2, c3, c4⟩ := P.four_ne (pb_ne_pa hm h)
  obtain ⟨d1, d2, d3, d4⟩ := P.four_ne (pb_ne_pb hm h)
  intro s t
  fin_cases s <;> fin_cases t <;> simp [blk, PairSys.blockEmb_apply, a1, a2, a3, a4, b1, b2, b3,
    b4, c1, c2, c3, c4, d1, d2, d3, d4]

@[expose] def isoGroup (Q : (ι → K) → K) : Subgroup (Matrix.GeneralLinearGroup ι K) :=
  Subgroup.closure {A : Matrix.GeneralLinearGroup ι K |
    ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}

theorem statedOmega_eq (Q : (ι → K) → K) : StatedOmega Q = ⁅isoGroup Q, isoGroup Q⁆ := rfl

theorem blk_mem_isoGroup (b : Fin 4) (g : Matrix.GeneralLinearGroup (Fin 4) K)
    (hg : ∀ a : Fin 4 → K, quad4 ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ a) = quad4 a) :
    blockGL (blk P hm b) g ∈ isoGroup Q :=
  Subgroup.subset_closure fun v => P.blockGL_isometry (pa_ne_pb hm b) g hg v

theorem inv_mul_inv_of_pow_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) :
    g⁻¹ * g⁻¹ = g := by
  calc g⁻¹ * g⁻¹ = g⁻¹ * g⁻¹ * g ^ 3 := by rw [h, mul_one]
    _ = g := by group

variable [CharP K 2]

@[expose] def rhoB (b : Fin 4) :
    Multiplicative (ZMod 3 × ZMod 3) →* Matrix.GeneralLinearGroup ι K :=
  (blockGL (blk P hm b)).comp (rho4 K)

theorem rhoB_mem_isoGroup (b : Fin 4) (x : Multiplicative (ZMod 3 × ZMod 3)) :
    rhoB P hm b x ∈ isoGroup Q := by
  rw [rhoB, MonoidHom.comp_apply, rho4_apply, map_mul, map_pow, map_pow]
  exact mul_mem (pow_mem (blk_mem_isoGroup P hm b _ (quad4_Lg K)) _)
    (pow_mem (blk_mem_isoGroup P hm b _ (quad4_Rg K)) _)

theorem rhoB_mem_omega (b : Fin 4) (x : Multiplicative (ZMod 3 × ZMod 3)) :
    rhoB P hm b x ∈ StatedOmega Q := by
  have hc : blockGL (blk P hm b) (Cg K) ∈ isoGroup Q := blk_mem_isoGroup P hm b _ (quad4_Cg K)
  have hcomm : rhoB P hm b x = ⁅blockGL (blk P hm b) (Cg K), rhoB P hm b x⁆ := by
    rw [rhoB, MonoidHom.comp_apply, ← map_commutatorElement, commutatorElement_def,
      rho4_conj, inv_mul_inv_of_pow_three (rho4_pow_three K x)]
  rw [statedOmega_eq, hcomm]
  exact Subgroup.commutator_mem_commutator hc (rhoB_mem_isoGroup P hm b x)

theorem rhoB_commute {b b' : Fin 4} (h : b ≠ b') (x y : Multiplicative (ZMod 3 × ZMod 3)) :
    Commute (rhoB P hm b x) (rhoB P hm b' y) :=
  blockGL_commute _ _ (blk_disjoint P hm h) _ _

theorem three_mul_comm {G : Type*} [Group G] {A A' B B' C C' : G} (hBA : Commute B A')
    (hCA : Commute C A') (hCB : Commute C B') :
    A * B * C * (A' * B' * C') = (A * A') * (B * B') * (C * C') := by
  have h1 : Commute C (A' * B') := hCA.mul_right hCB
  calc A * B * C * (A' * B' * C') = A * B * (A' * B') * (C * C') := h1.mul_mul_mul_comm _ _
    _ = (A * A') * (B * B') * (C * C') := by rw [hBA.mul_mul_mul_comm A B']

@[expose] def thetaB :
    (Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) →* Matrix.GeneralLinearGroup ι K :=
  MonoidHom.mk' (fun a => rhoB P hm 0 (a 0) * rhoB P hm 1 (a 1) * rhoB P hm 2 (a 2)) (by
    intro a b
    simp only [Pi.mul_apply, map_mul]
    exact (three_mul_comm (rhoB_commute P hm (by decide) _ _) (rhoB_commute P hm (by decide) _ _)
      (rhoB_commute P hm (by decide) _ _)).symm)

theorem thetaB_apply (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) :
    thetaB P hm a = rhoB P hm 0 (a 0) * rhoB P hm 1 (a 1) * rhoB P hm 2 (a 2) := rfl

theorem thetaB_mem_omega (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) :
    thetaB P hm a ∈ StatedOmega Q := by
  rw [thetaB_apply]
  exact mul_mem (mul_mem (rhoB_mem_omega P hm 0 _) (rhoB_mem_omega P hm 1 _))
    (rhoB_mem_omega P hm 2 _)

@[expose] def sB : Matrix.GeneralLinearGroup ι K := blockGL (blk P hm 3) (Cg K)

theorem sB_mem_omega : sB P hm ∈ StatedOmega Q := by
  have h1 := blk_mem_isoGroup P hm 3 _ (quad4_c3g K)
  have h2 := blk_mem_isoGroup P hm 3 _ (quad4_g3g K)
  have : sB P hm = ⁅blockGL (blk P hm 3) (c3g K), blockGL (blk P hm 3) (g3g K)⁆ := by
    rw [← map_commutatorElement, commutatorElement_def, comm_c3g_g3g, sB]
  rw [statedOmega_eq, this]
  exact Subgroup.commutator_mem_commutator h1 h2

theorem sB_sq : sB P hm * sB P hm = 1 := by
  rw [sB, ← map_mul, Cg_sq, map_one]

theorem sB_ne_one : sB P hm ≠ 1 := fun h =>
  Cg_ne_one K (blockGL_injective (blk P hm 3) (h.trans (map_one _).symm))

theorem sB_commute (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) :
    sB P hm * thetaB P hm a = thetaB P hm a * sB P hm := by
  have h0 : Commute (sB P hm) (rhoB P hm 0 (a 0)) :=
    blockGL_commute _ _ (blk_disjoint P hm (by decide)) _ _
  have h1 : Commute (sB P hm) (rhoB P hm 1 (a 1)) :=
    blockGL_commute _ _ (blk_disjoint P hm (by decide)) _ _
  have h2 : Commute (sB P hm) (rhoB P hm 2 (a 2)) :=
    blockGL_commute _ _ (blk_disjoint P hm (by decide)) _ _
  rw [thetaB_apply]
  exact ((h0.mul_right h1).mul_right h2).eq

@[expose] def spareEmb : Unit ↪ ι :=
  ⟨fun _ => P.xs ⟨8, by omega⟩, fun _ _ _ => rfl⟩

omit [CharP K 2] in
theorem blk_spare_disjoint (b : Fin 4) : ∀ s t, blk P hm b s ≠ spareEmb P hm t := by
  have h8a : pa hm b ≠ (⟨8, by omega⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp only [pa] at this
    have := b.2
    omega
  have h8b : pb hm b ≠ (⟨8, by omega⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp only [pb] at this
    have := b.2
    omega
  obtain ⟨a1, a2, a3, a4⟩ := P.four_ne h8a
  obtain ⟨b1, b2, b3, b4⟩ := P.four_ne h8b
  intro s t
  fin_cases s
  exacts [a1, a3, b1, b3]

theorem rhoB_mulVec_spare (b : Fin 4) (x : Multiplicative (ZMod 3 × ZMod 3)) (c : Unit → K) :
    ((rhoB P hm b x : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (spareEmb P hm) *ᵥ c) = incl K (spareEmb P hm) *ᵥ c := by
  rw [rhoB, MonoidHom.comp_apply, blockGL_coe]
  exact blockExt_mulVec_incl_of_disjoint _ _ (blk_spare_disjoint P hm b) _ _

theorem rhoB_mulVec_self (b : Fin 4) (x : Multiplicative (ZMod 3 × ZMod 3)) (u : Fin 4 → K) :
    ((rhoB P hm b x : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (blk P hm b) *ᵥ u) =
      incl K (blk P hm b) *ᵥ (((rho4 K x : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *ᵥ u) := by
  rw [rhoB, MonoidHom.comp_apply, blockGL_coe]
  exact blockExt_mulVec_incl _ _ _

theorem rhoB_mulVec_other {b b' : Fin 4} (h : b ≠ b') (x : Multiplicative (ZMod 3 × ZMod 3))
    (u : Fin 4 → K) :
    ((rhoB P hm b x : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (blk P hm b') *ᵥ u) = incl K (blk P hm b') *ᵥ u := by
  rw [rhoB, MonoidHom.comp_apply, blockGL_coe]
  exact blockExt_mulVec_incl_of_disjoint _ _ (blk_disjoint P hm h) _ _

theorem thetaB_mulVec_spare (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) (c : Unit → K) :
    ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (spareEmb P hm) *ᵥ c) = incl K (spareEmb P hm) *ᵥ c := by
  rw [thetaB_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rhoB_mulVec_spare, rhoB_mulVec_spare, rhoB_mulVec_spare]

theorem thetaB_mulVec_blk0 (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) (u : Fin 4 → K) :
    ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (blk P hm 0) *ᵥ u) = incl K (blk P hm 0) *ᵥ
        (((rho4 K (a 0) : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          u) := by
  rw [thetaB_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rhoB_mulVec_other P hm (by decide), rhoB_mulVec_other P hm (by decide), rhoB_mulVec_self]

theorem thetaB_mulVec_blk1 (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) (u : Fin 4 → K) :
    ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (blk P hm 1) *ᵥ u) = incl K (blk P hm 1) *ᵥ
        (((rho4 K (a 1) : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          u) := by
  rw [thetaB_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rhoB_mulVec_other P hm (by decide), rhoB_mulVec_self, rhoB_mulVec_other P hm (by decide)]

theorem thetaB_mulVec_blk2 (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) (u : Fin 4 → K) :
    ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (blk P hm 2) *ᵥ u) = incl K (blk P hm 2) *ᵥ
        (((rho4 K (a 2) : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          u) := by
  rw [thetaB_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rhoB_mulVec_self, rhoB_mulVec_other P hm (by decide), rhoB_mulVec_other P hm (by decide)]

theorem sB_mulVec_spare (c : Unit → K) :
    ((sB P hm : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      (incl K (spareEmb P hm) *ᵥ c) = incl K (spareEmb P hm) *ᵥ c := by
  rw [sB, blockGL_coe]
  exact blockExt_mulVec_incl_of_disjoint _ _ (blk_spare_disjoint P hm 3) _ _

omit [CharP K 2] in
theorem eq_one_of_scalar_fix {A : Matrix.GeneralLinearGroup ι K} (hA : A ∈ StatedScalars ι K)
    (hfix : (A : Matrix ι ι K) *ᵥ (incl K (spareEmb P hm) *ᵥ fun _ => (1 : K)) =
      incl K (spareEmb P hm) *ᵥ fun _ => (1 : K)) : A = 1 := by
  obtain ⟨c, rfl⟩ := hA
  have h1 := congrFun hfix (spareEmb P hm ())
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
    incl_mulVec_emb] at h1
  have : (c : K) = 1 := by simpa using h1
  have hc : c = 1 := Units.ext this
  rw [hc, map_one]

omit [CharP K 2] in
theorem eq_one_of_mulVec_incl {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ↪ ι)
    (M : Matrix κ κ K) (h : ∀ u, incl K e *ᵥ (M *ᵥ u) = incl K e *ᵥ u) : M = 1 := by
  have hu : ∀ u, M *ᵥ u = u := fun u => by
    have := congrArg (fun w => (incl K e)ᵀ *ᵥ w) (h u)
    simpa only [inclT_mulVec_incl] using this
  ext i j
  have := congrFun (hu (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem thetaB_scalar (a : Fin 3 → Multiplicative (ZMod 3 × ZMod 3))
    (hA : thetaB P hm a ∈ StatedScalars ι K) : a = 1 := by
  have h1 : thetaB P hm a = 1 :=
    eq_one_of_scalar_fix P hm hA (thetaB_mulVec_spare P hm a _)
  have h1' : ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = 1 := by
    rw [h1]; rfl
  have key : ∀ (b : Fin 4) (x : Multiplicative (ZMod 3 × ZMod 3)),
      (∀ u, ((thetaB P hm a : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
        (incl K (blk P hm b) *ᵥ u) = incl K (blk P hm b) *ᵥ
          (((rho4 K x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
            u)) → x = 1 := by
    intro b x hx
    have hM : ((rho4 K x : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
      eq_one_of_mulVec_incl (blk P hm b) _ fun u => by
        rw [← hx u, h1', Matrix.one_mulVec]
    have h4 : rho4 K x = 1 := Units.ext hM
    exact rho4_injective K (h4.trans (map_one _).symm)
  funext j
  fin_cases j
  · exact key 0 _ (thetaB_mulVec_blk0 P hm a)
  · exact key 1 _ (thetaB_mulVec_blk1 P hm a)
  · exact key 2 _ (thetaB_mulVec_blk2 P hm a)

include P hm in
theorem exists_orthogonal_rank_six_witness :
    ∃ (θ : (Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) →* StatedProj (StatedOmega Q))
      (s : StatedProj (StatedOmega Q)), Function.Injective θ ∧ s ≠ 1 ∧ s ^ 2 = 1 ∧
        ∀ a, s * θ a = θ a * s := by
  let q : StatedOmega Q →* StatedProj (StatedOmega Q) := QuotientGroup.mk' _
  have hscal : ∀ g : StatedOmega Q, q g = 1 →
      (g : Matrix.GeneralLinearGroup ι K) ∈ StatedScalars ι K := fun g hg => by
    have : g ∈ (StatedScalars ι K).subgroupOf (StatedOmega Q) := (QuotientGroup.eq_one_iff _).1 hg
    exact this
  let θ' : (Fin 3 → Multiplicative (ZMod 3 × ZMod 3)) →* StatedOmega Q :=
    (thetaB P hm).codRestrict (StatedOmega Q) (thetaB_mem_omega P hm)
  refine ⟨q.comp θ', q ⟨sB P hm, sB_mem_omega P hm⟩, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    exact thetaB_scalar P hm a (hscal _ ha)
  · intro h
    exact sB_ne_one P hm (eq_one_of_scalar_fix P hm (hscal _ h) (sB_mulVec_spare P hm _))
  · rw [← map_pow]
    have : (⟨sB P hm, sB_mem_omega P hm⟩ : StatedOmega Q) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, sq, sB_sq]
      rfl
    rw [this, map_one]
  · intro a
    show q ⟨sB P hm, sB_mem_omega P hm⟩ * q (θ' a) = q (θ' a) * q ⟨sB P hm, sB_mem_omega P hm⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact sB_commute P hm a


end Witness

section Forms

variable {K : Type} [Field K]

@[expose] def plusPairSys (n : ℕ) : PairSys K (Fin n ⊕ Fin n) (StatedQuadPlus n K) n where
  xs := Sum.inl
  ys := Sum.inr
  xs_inj := Sum.inl_injective
  ys_inj := Sum.inr_injective
  xs_ne_ys := fun _ _ => Sum.inl_ne_inr
  R := fun _ => 0
  hR := fun _ _ _ => rfl
  hQ := fun v => by simp [StatedQuadPlus]

@[expose] def minusPairSys (n : ℕ) (b c : K) :
    PairSys K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (StatedQuadMinus n K b c) (n - 1) where
  xs := fun i => Sum.inl i
  ys := fun i => Sum.inr (Sum.inl i)
  xs_inj := Sum.inl_injective
  ys_inj := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
  xs_ne_ys := fun _ _ => Sum.inl_ne_inr
  R := fun v => v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) *
    v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2
  hR := fun v w hw => by
    have h0 : w (Sum.inr (Sum.inr 0)) = 0 := hw _ (fun i => ⟨by simp, by simp⟩)
    have h1 : w (Sum.inr (Sum.inr 1)) = 0 := hw _ (fun i => ⟨by simp, by simp⟩)
    simp [h0, h1]
  hQ := fun v => by simp [StatedQuadMinus, add_assoc]

end Forms

theorem evenOrthogonalHighDimRankFour_holds : EvenOrthogonalHighDimRankFour := by
  intro H _ _ X τ n f hτ hmod hn
  have hf : 1 ≤ f := hmod.1.2.1
  rcases hτ with rfl | rfl
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hf hk
    obtain ⟨η, hη, hker⟩ := exists_cover_of_model e
    obtain ⟨θ, s, hθ, hs1, hs2, hsθ⟩ :=
      exists_orthogonal_rank_six_witness (plusPairSys (K := k) n) (by omega)
    exact four_le_localRank_of_cube_witness η hη hker isElementaryAbelian_pi_cube.1
      isElementaryAbelian_pi_cube.2 θ hθ hs1 hs2 hsθ
  · obtain ⟨-, k, _, _, hk, b, c, -, ⟨e⟩⟩ := hmod
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hf hk
    obtain ⟨η, hη, hker⟩ := exists_cover_of_model e
    obtain ⟨θ, s, hθ, hs1, hs2, hsθ⟩ :=
      exists_orthogonal_rank_six_witness (minusPairSys (K := k) n b c) (by omega)
    exact four_le_localRank_of_cube_witness η hη hker isElementaryAbelian_pi_cube.1
      isElementaryAbelian_pi_cube.2 θ hθ hs1 hs2 hsθ

theorem evenClassicalHighDimRankFour_holds : EvenClassicalHighDimRankFour :=
  evenClassicalHighDimRankFour_of_orthogonal evenOrthogonalHighDimRankFour_holds

theorem fiveFixedExcludesClassical_of_sp4
    (hSp4 : OddSymplecticFourInnerDefiningFixedComponentFree) : FiveFixedExcludesClassical :=
  fiveFixedExcludesClassical_of_sp4_even hSp4 evenClassicalHighDimRankFour_holds

end CFSG.RankThree.PartOne.HNRed
