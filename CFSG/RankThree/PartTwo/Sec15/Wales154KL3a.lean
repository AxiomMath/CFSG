module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

namespace KL3aProof

open Matrix

section LinearAlgebra

variable {K : Type*} [Field K]

theorem sq_eq_zero_of_isNilpotent {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (hE : Module.finrank K E ≤ 2) {f : Module.End K E}
    (hf : IsNilpotent f) : f ^ 2 = 0 := by
  obtain ⟨m, hm⟩ := hf
  have h := Module.End.ker_pow_le_ker_pow_finrank f m
  rw [hm, LinearMap.ker_zero, top_le_iff, LinearMap.ker_eq_top] at h
  rw [← Nat.sub_add_cancel hE, pow_add, h, mul_zero]

theorem sq_mulVec_of_isNilpotent {N : Matrix (Fin 3) (Fin 3) K} (hN : IsNilpotent N)
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hNW : ∀ v ∈ W, N *ᵥ v ∈ W) :
    (∀ v ∈ W, N *ᵥ (N *ᵥ v) = 0) ∧ ∀ v, N *ᵥ (N *ᵥ v) ∈ W := by
  set f : Module.End K (Fin 3 → K) := Matrix.toLin' N with hf
  have hfv : ∀ v, f v = N *ᵥ v := fun v => Matrix.toLin'_apply N v
  have hfW : ∀ v ∈ W, f v ∈ W := fun v hv => by rw [hfv]; exact hNW v hv
  have hfn : IsNilpotent f := (Matrix.isNilpotent_toLin'_iff N).mpr hN
  have hdim := Submodule.finrank_quotient_add_finrank W
  rw [Module.finrank_fin_fun] at hdim
  have hW1 : Module.finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hW3 : Module.finrank K W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  constructor
  · intro v hv
    have hres : (f.restrict hfW) ^ 2 = 0 :=
      sq_eq_zero_of_isNilpotent (by omega) (Module.End.isNilpotent.restrict hfW hfn)
    have h1 := congrArg (fun φ : Module.End K W => ((φ ⟨v, hv⟩ : W) : Fin 3 → K)) hres
    simp only [sq, Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.zero_apply,
      ZeroMemClass.coe_zero] at h1
    rwa [hfv, hfv] at h1
  · intro v
    have hq : (W.mapQ W f hfW) ^ 2 = 0 :=
      sq_eq_zero_of_isNilpotent (by omega) (Module.End.IsNilpotent.mapQ hfW hfn)
    have h1 := congrArg (fun φ : Module.End K ((Fin 3 → K) ⧸ W) => φ (W.mkQ v)) hq
    simp only [sq, Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at h1
    rwa [hfv, hfv] at h1

end LinearAlgebra

section GeneralLinear

variable {K : Type*} [Field K] [CharP K 2]

theorem sq_fix_of_pow_two_pow {g : GL (Fin 3) K} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hgW : ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) :
    (∀ v ∈ W, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) ∧
      ∀ v, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hgN : (g : Matrix (Fin 3) (Fin 3) K) = N + 1 := by rw [hNdef, sub_add_cancel]
  have hnil : IsNilpotent N := by
    refine ⟨2 ^ k, ?_⟩
    rw [hNdef, sub_pow_char_pow_of_commute 2 k (Commute.one_right _),
      ← Units.val_pow_eq_pow_val, hg, Units.val_one, one_pow, sub_self]
  have hNW : ∀ v ∈ W, N *ᵥ v ∈ W := by
    intro v hv
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact W.sub_mem (hgW v hv) hv
  have hsq : (N + 1) ^ 2 = N * N + 1 := by
    rw [(Commute.one_right N).add_sq, CharTwo.two_eq_zero (R := Matrix (Fin 3) (Fin 3) K),
      zero_mul, zero_mul, add_zero, one_pow, sq]
  have hg2 : ∀ v, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      N *ᵥ (N *ᵥ v) + v := by
    intro v
    rw [Units.val_pow_eq_pow_val, hgN, hsq, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  obtain ⟨h1, h2⟩ := sq_mulVec_of_isNilpotent hnil hW0 hWt hNW
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [hg2, h1 v hv, zero_add]
  · rw [hg2, add_sub_cancel_right]
    exact h2 v

theorem sq_eq_one_of_fix {W : Submodule K (Fin 3 → K)} {g : GL (Fin 3) K}
    (h1 : ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v)
    (h2 : ∀ v, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W) : g ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, sq, ← Matrix.mulVec_mulVec]
  set gm : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K)
  have hw := h1 _ (h2 v)
  rw [Matrix.mulVec_sub] at hw
  have hself : ∀ x : Fin 3 → K, x + x = 0 := fun x => funext fun i => CharTwo.add_self_eq_zero (x i)
  have hneg : -v = v := funext fun i => CharTwo.neg_eq (v i)
  calc gm *ᵥ (gm *ᵥ v) = (gm *ᵥ v - v) + gm *ᵥ v := eq_add_of_sub_eq hw
    _ = (gm *ᵥ v + gm *ᵥ v) + -v := by abel
    _ = v := by rw [hself, zero_add, hneg]

@[expose] def fixGroup (W : Submodule K (Fin 3 → K)) : Subgroup (GL (Fin 3) K) where
  carrier := {g | (∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) ∧
    ∀ v, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W}
  one_mem' := ⟨fun v _ => by simp, fun v => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb1 v hv, ha1 v hv]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      have : (a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ v) - v =
          ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ v) -
            (b : Matrix (Fin 3) (Fin 3) K) *ᵥ v) + ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v) := by
        abel
      rw [this]
      exact W.add_mem (ha2 _) (hb2 v)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hinv : ∀ v, ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hinv' : ∀ v, (a : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← ha1 v hv]
      exact hinv v
    · have h := ha2 (((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
      rw [hinv'] at h
      have h' := W.neg_mem h
      rwa [neg_sub] at h'

theorem conj_mem_fixGroup {W : Submodule K (Fin 3 → K)} {d u : GL (Fin 3) K}
    (hd : ∀ v ∈ W, (d : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W)
    (hdi : ∀ v ∈ W, ((d⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W)
    (hu : u ∈ fixGroup W) : d * u * d⁻¹ ∈ fixGroup W := by
  obtain ⟨hu1, hu2⟩ := hu
  have hdd : ∀ v, (d : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((d⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hu1 _ (hdi v hv), hdd]
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    set w := ((d⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
    have h : (d : Matrix (Fin 3) (Fin 3) K) *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ w) - v =
        (d : Matrix (Fin 3) (Fin 3) K) *ᵥ ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ w - w) := by
      rw [Matrix.mulVec_sub, hdd]
    rw [h]
    exact hd _ (hu2 _)

end GeneralLinear

section Projective

variable {K : Type*} [Field K] [CharP K 2]

theorem eq_one_of_mem_center_of_pow {z : GL (Fin 3) K}
    (hz : z ∈ Subgroup.center (GL (Fin 3) K)) {m : ℕ} (hm : z ^ 2 ^ m = 1) : z = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, rfl⟩ := hz
  have hu : (u : K) ^ 2 ^ m = 1 := by
    have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 0) hm
    simpa [← map_pow, Matrix.GeneralLinearGroup.coe_scalar] using h
  have hu1 : (u : K) = 1 := by
    have h := sub_pow_char_pow (u : K) 1 (p := 2) (n := m)
    rw [hu, one_pow, sub_self] at h
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h)
  rw [show u = 1 from Units.ext hu1, map_one]

theorem mem_of_pow_two_pow {S : Subgroup (GL (Fin 3) K)} (hS : IsPGroup 2 S)
    {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hSP : P ≤ S.map ProjGenLinGroup.mk)
    {g : GL (Fin 3) K} (hg : ProjGenLinGroup.mk g ∈ P) {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g ∈ S := by
  obtain ⟨s, hs, hsg⟩ := hSP hg
  set z : GL (Fin 3) K := s⁻¹ * g with hzdef
  have hz : z ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, hzdef, map_mul, map_inv, hsg, inv_mul_cancel]
  have hgz : g = s * z := by rw [hzdef, mul_inv_cancel_left]
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcomm : Commute s z := Subgroup.mem_center_iff.mp hz s
  have hzn : z ^ 2 ^ (j + k) = 1 := by
    have h1 : g ^ 2 ^ (j + k) = 1 := by rw [pow_add, pow_mul', hgk, one_pow]
    have h2 : s ^ 2 ^ (j + k) = 1 := by rw [pow_add, pow_mul, hsj, one_pow]
    rw [hgz, hcomm.mul_pow, h2, one_mul] at h1
    exact h1
  have hz1 : z = 1 := eq_one_of_mem_center_of_pow hz hzn
  rw [hgz, hz1, mul_one]
  exact hs

variable [Finite K]

theorem exists_twoGroup_map_eq {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP : IsPGroup 2 P) :
    ∃ S : Subgroup (GL (Fin 3) K), IsPGroup 2 S ∧ S.map ProjGenLinGroup.mk = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective (ProjGenLinGroup.mk.subgroupComap P) :=
    MonoidHom.subgroupComap_surjective _ P ProjGenLinGroup.mk_surjective
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (P.comap ProjGenLinGroup.mk)))
  have hQ : ((T.mapSurjective hf : Sylow 2 P) : Subgroup P) = ⊤ :=
    ((T.mapSurjective hf).is_maximal' (hP.to_subgroup ⊤) le_top).symm
  refine ⟨(T : Subgroup _).map (P.comap ProjGenLinGroup.mk).subtype, T.isPGroup'.map _, ?_⟩
  have h1 : ((T : Subgroup _).map (P.comap ProjGenLinGroup.mk).subtype).map ProjGenLinGroup.mk =
      ((T : Subgroup _).map (ProjGenLinGroup.mk.subgroupComap P)).map P.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1, ← Sylow.coe_mapSurjective hf, hQ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_fixed_vector {S : Subgroup (GL (Fin 3) K)} (hS : IsPGroup 2 S) :
    ∃ w : Fin 3 → K, w ≠ 0 ∧ ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥S (Fin 3 → K) :=
    { smul := fun s w => ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w
      one_smul := fun w => by
        show ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w
        simp
      mul_smul := fun r s w => by
        show (((r : GL (Fin 3) K) * (s : GL (Fin 3) K) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ w =
          ((r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w)
        rw [Units.val_mul, Matrix.mulVec_mulVec] }
  have h2 : 2 ∣ Nat.card (Fin 3 → K) := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hm]
    exact dvd_pow (dvd_pow_self 2 (PNat.ne_zero m)) (by omega)
  have h0 : (0 : Fin 3 → K) ∈ MulAction.fixedPoints ↥S (Fin 3 → K) := by
    intro s
    show ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ 0 = 0
    simp
  obtain ⟨b, hb, hb0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 3 → K) h2 h0
  exact ⟨b, fun h => hb0 h.symm, fun s hs => hb ⟨s, hs⟩⟩

theorem exists_stable_subspace {P : Subgroup (ProjGenLinGroup (Fin 3) K)} (hP2 : IsPGroup 2 P)
    (hP : P ≠ ⊥) :
    ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin 3) K,
      ProjGenLinGroup.mk g ∈ Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)) →
        ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
  obtain ⟨S, hS2, hSP⟩ := exists_twoGroup_map_eq hP2
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {w | ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w}
      add_mem' := fun {a b} ha hb s hs => by
        rw [Matrix.mulVec_add, ha s hs, hb s hs]
      zero_mem' := fun s _ => by simp
      smul_mem' := fun c w hw s hs => by
        rw [Matrix.mulVec_smul, hw s hs] }
  have hmemW : ∀ w, w ∈ W ↔ ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := fun w => Iff.rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · obtain ⟨w, hw0, hw⟩ := exists_fixed_vector hS2
    intro hbot
    have hwW : w ∈ W := (hmemW w).mpr hw
    rw [hbot, Submodule.mem_bot] at hwW
    exact hw0 hwW
  · intro htop
    rcases P.bot_or_exists_ne_one with h | ⟨y, hyP, hy1⟩
    · exact hP h
    rw [← hSP] at hyP
    obtain ⟨s, hs, rfl⟩ := hyP
    apply hy1
    have hfix : ∀ v, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun v =>
      (hmemW v).mp (htop ▸ Submodule.mem_top) s hs
    have hs1 : s = 1 := by
      apply Units.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix v, Units.val_one, Matrix.one_mulVec]
    rw [hs1, map_one]
  · intro g hg v hv
    rw [hmemW]
    intro s hs
    have hsP : ProjGenLinGroup.mk s ∈ P := hSP ▸ Subgroup.mem_map_of_mem _ hs
    obtain ⟨j, hj⟩ := hS2 ⟨s, hs⟩
    have hsj : s ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hconjP : ProjGenLinGroup.mk (g⁻¹ * s * g) ∈ P := by
      have hgi : (ProjGenLinGroup.mk g)⁻¹ ∈
          Subgroup.normalizer (P : Set (ProjGenLinGroup (Fin 3) K)) := inv_mem hg
      have := (Subgroup.mem_normalizer_iff.mp hgi (ProjGenLinGroup.mk s)).mp hsP
      rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at this
    have hconj2 : (g⁻¹ * s * g) ^ 2 ^ j = 1 := by
      have h := conj_pow (a := g⁻¹) (b := s) (i := 2 ^ j)
      rw [inv_inv] at h
      rw [h, hsj, mul_one, inv_mul_cancel]
    have hmem : g⁻¹ * s * g ∈ S := mem_of_pow_two_pow hS2 hSP.ge hconjP hconj2
    have hfix := (hmemW v).mp hv _ hmem
    calc (s : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
            ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by rw [hfix]

theorem sq_eq_one_of_pow_four {G : Type*} [Group G]
    (ι : G →* ProjGenLinGroup (Fin 3) K) (hι : Function.Injective ι) {Xb P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hP : P ≠ ⊥) (hXP : Xb ≤ Subgroup.normalizer (P : Set G))
    (t : ↥Xb ⧸ CFSG.pCore 2 ↥Xb) (ht : t ^ 4 = 1) : t ^ 2 = 1 := by
  have hP'2 : IsPGroup 2 (P.map ι) := hP2.map ι
  have hP' : P.map ι ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι]
  obtain ⟨W, hW0, hWt, hW⟩ := exists_stable_subspace hP'2 hP'
  set D : Subgroup (GL (Fin 3) K) := (Xb.map ι).comap ProjGenLinGroup.mk with hD
  have hDW : ∀ d ∈ D, ∀ v ∈ W, (d : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro d hd
    apply hW d
    exact Subgroup.le_normalizer_map ι (Subgroup.map_mono hXP hd)
  let e : ↥Xb ≃* ↥(Xb.map ι) := Xb.equivMapOfInjective ι hι
  let ρ₀ : ↥D →* ↥(Xb.map ι) :=
    (ProjGenLinGroup.mk.comp D.subtype).codRestrict (Xb.map ι) (fun d => d.2)
  let ρ : ↥D →* ↥Xb := e.symm.toMonoidHom.comp ρ₀
  have hρ : Function.Surjective ρ := by
    intro x
    obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (e x : ProjGenLinGroup (Fin 3) K)
    have hgD : g ∈ D := by
      rw [hD, Subgroup.mem_comap, hg]
      exact (e x).2
    refine ⟨⟨g, hgD⟩, ?_⟩
    apply e.injective
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact Subtype.ext hg
  let U : Subgroup ↥D := (fixGroup W).subgroupOf D
  have hUn : U.Normal := by
    refine ⟨fun u hu d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_fixGroup (hDW d d.2) (hDW _ (D.inv_mem d.2)) hu
  have hUρ : U.map ρ ≤ CFSG.pCore 2 ↥Xb := by
    refine le_sSup ⟨hUn.map ρ hρ, ?_⟩
    intro x
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.mem_subgroupOf] at hu
    have h1 : (u : GL (Fin 3) K) ^ 2 = 1 := sq_eq_one_of_fix hu.1 hu.2
    have h2 : u ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])
    rw [pow_one, Subgroup.coe_pow, ← hux, ← map_pow, h2, map_one, Subgroup.coe_one]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Xb) t
  obtain ⟨d, rfl⟩ := hρ x
  obtain ⟨b, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hg : ((d ^ m : ↥D) : GL (Fin 3) K) ^ 2 ^ b = 1 := by
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hdm, pow_orderOf_eq_one, Subgroup.coe_one]
  have hU : (d ^ m) ^ 2 ∈ U := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    obtain ⟨h1, h2⟩ := sq_fix_of_pow_two_pow hg hW0 hWt (hDW _ (d ^ m).2)
    exact ⟨h1, h2⟩
  have h1 : ρ ((d ^ m) ^ 2) ∈ CFSG.pCore 2 ↥Xb := hUρ (Subgroup.mem_map_of_mem ρ hU)
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Xb) (ρ d)) ^ (2 * m) = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← map_pow]
    have : d ^ (2 * m) = (d ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [this]
    exact h1
  obtain ⟨r, rfl⟩ := hm
  have h4 : 2 * (2 * r + 1) = 4 * r + 2 := by ring
  rw [h4, pow_add, pow_mul, ht, one_pow, one_mul] at h2
  exact h2

end Projective

section OrderFour

theorem mk_ne_one_of_apply_ne {K : Type*} [Field K] {A : GL (Fin 3) K} {i j : Fin 3}
    (hij : i ≠ j) (hA : (A : Matrix (Fin 3) (Fin 3) K) i j ≠ 0) : ProjGenLinGroup.mk A ≠ 1 := by
  rw [Ne, ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨u, hu⟩
  apply hA
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij]

theorem exists_projSL_pow_four (K : Type*) [Field K] [CharP K 2] :
    ∃ t : ↥(CFSG.PGLModel.projSL 3 K), t ^ 4 = 1 ∧ t ^ 2 ≠ 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let M : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 1; 0, 0, 1]
  have hMdet : M.det = 1 := by simp [M, Matrix.det_fin_three]
  let A : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
  have hAM : (A : Matrix (Fin 3) (Fin 3) K) = M := rfl
  have hA : A ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    rw [MonoidHom.mem_ker]
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hAM, hMdet]
  have hM2 : M * M = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> linear_combination h2
  have hM4 : (M * M) * (M * M) = 1 := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linear_combination h2
  have hA4 : A ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hAM, Units.val_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      sq, sq, hM4]
  refine ⟨⟨ProjGenLinGroup.mk A, Subgroup.mem_map_of_mem _ hA⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change ProjGenLinGroup.mk A ^ 4 = 1
    rw [← map_pow, hA4, map_one]
  · intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    change ProjGenLinGroup.mk A ^ 2 = 1 at h'
    rw [← map_pow] at h'
    refine mk_ne_one_of_apply_ne (i := 0) (j := 2) (by decide) ?_ h'
    rw [Units.val_pow_eq_pow_val, hAM, sq, hM2]
    simp

theorem exists_pow_ne_self (n : ℕ) (hn : 1 ≤ n) :
    ∃ β : GaloisField 2 (2 * n), β ^ 2 ^ n ≠ β := by
  by_contra! hall
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 (2 * n))ˣ)
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : ζ ^ (2 ^ n - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h' : (ζ : GaloisField 2 (2 * n)) ^ (2 ^ n - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hall, one_mul]
    exact mul_right_cancel₀ ζ.ne_zero h'
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hζ, Nat.card_units, GaloisField.card 2 (2 * n) (by omega)] at hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  have h22 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  rw [h22] at hle
  have hmul : 2 * 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hq
  generalize 2 ^ n * 2 ^ n = Q at hle hmul
  omega

theorem exists_pow_eq_add_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : GaloisField 2 (2 * n), b ^ 2 ^ n = b + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := Fintype.ofFinite (GaloisField 2 (2 * n))
  obtain ⟨β, hβ⟩ := exists_pow_ne_self n hn
  set c : GaloisField 2 (2 * n) := β ^ 2 ^ n + β with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hβ
    have h' := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at h'
  have hββ : (β ^ 2 ^ n) ^ 2 ^ n = β := by
    rw [← pow_mul, ← pow_add, ← two_mul]
    have hcard : Fintype.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n) (by omega)]
    rw [← hcard, FiniteField.pow_card]
  have hcq : c ^ 2 ^ n = c := by
    rw [hc, add_pow_char_pow, hββ, add_comm]
  refine ⟨β / c, ?_⟩
  rw [div_pow, hcq, div_add_one hc0]
  congr 1
  rw [hc, add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem exists_projSU_pow_four (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : ↥(CFSG.PGLModel.projSU 3 2 n), t ^ 4 = 1 ∧ t ^ 2 ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := exists_pow_eq_add_one n hn
  let M : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)) :=
    !![1 + b, b, 1; b, 1 + b, 1; 1, 1, 1]
  have hMdet : M.det = 1 := by
    simp [M, Matrix.det_fin_three]
    grind
  let A : GL (Fin 3) (GaloisField 2 (2 * n)) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
  have hAM : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) = M := rfl
  have hpow1 : (1 + b) ^ 2 ^ n = b := by
    rw [add_pow_char_pow, one_pow, hb]
    grind
  have hmap : M.map (· ^ 2 ^ n) = !![b, b + 1, 1; b + 1, b, 1; 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, hb, hpow1]
  have hU : (M.map (· ^ 2 ^ n))ᵀ * M = 1 := by
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hM2 : M * M = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hM4 : (M * M) * (M * M) = 1 := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hA4 : A ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hAM, Units.val_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      sq, sq, hM4]
  have hAdet : Matrix.GeneralLinearGroup.det A = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hAM, hMdet]
  have hAmem : A ∈ Subgroup.closure {A : GL (Fin 3) (GaloisField 2 (2 * n)) |
      Matrix.GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))).map (· ^ (2 ^ n)))ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) = 1} :=
    Subgroup.subset_closure ⟨hAdet, by rw [hAM]; exact hU⟩
  refine ⟨⟨ProjGenLinGroup.mk A, Subgroup.mem_map_of_mem _ hAmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change ProjGenLinGroup.mk A ^ 4 = 1
    rw [← map_pow, hA4, map_one]
  · intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    change ProjGenLinGroup.mk A ^ 2 = 1 at h'
    rw [← map_pow] at h'
    refine mk_ne_one_of_apply_ne (i := 0) (j := 1) (by decide) ?_ h'
    rw [Units.val_pow_eq_pow_val, hAM, sq, hM2]
    simp

end OrderFour

end KL3aProof

open KL3aProof in
theorem kl3a_holds : KL3a := by
  intro Q _ _ f _ hQ Xb _ n hn hX
  have key : ∀ P : Subgroup Q, IsPGroup 2 P → Xb ≤ Subgroup.normalizer (P : Set Q) → P = ⊥ := by
    intro P hP2 hXP
    by_contra hP
    have hsq : ∀ t : ↥Xb ⧸ CFSG.pCore 2 ↥Xb, t ^ 4 = 1 → t ^ 2 = 1 := by
      rcases hQ with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact sq_eq_one_of_pow_four
          ((CFSG.PGLModel.projSL 3 (GaloisField 2 f)).subtype.comp φ.toMonoidHom)
          (fun a b h => φ.injective (Subtype.ext h)) hP2 hP hXP
      · exact sq_eq_one_of_pow_four
          ((CFSG.PGLModel.projSU 3 2 f).subtype.comp φ.toMonoidHom)
          (fun a b h => φ.injective (Subtype.ext h)) hP2 hP hXP
    obtain ⟨s, hs4, hs2⟩ : ∃ t : ↥Xb ⧸ CFSG.pCore 2 ↥Xb, t ^ 4 = 1 ∧ t ^ 2 ≠ 1 := by
      rcases hX with ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
      · obtain ⟨s, hs4, hs2⟩ := exists_projSL_pow_four (GaloisField 2 n)
        refine ⟨ψ.symm s, by rw [← map_pow, hs4, map_one], fun h => hs2 ?_⟩
        apply ψ.symm.injective
        rw [map_pow, h, map_one]
      · obtain ⟨s, hs4, hs2⟩ := exists_projSU_pow_four n hn
        refine ⟨ψ.symm s, by rw [← map_pow, hs4, map_one], fun h => hs2 ?_⟩
        apply ψ.symm.injective
        rw [map_pow, h, map_one]
    exact hs2 (hsq s hs4)
  refine ⟨?_, key⟩
  have h := key ((CFSG.pCore 2 ↥Xb).map Xb.subtype) (CFSG.pCore_isPGroup.map _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Xb)
  exact (Subgroup.map_eq_bot_iff_of_injective _ Xb.subtype_injective).mp h

end CFSG.RankThree.PartTwo.Sec15.Wales154
