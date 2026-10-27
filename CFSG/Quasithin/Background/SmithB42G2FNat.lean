module

public import CFSG.Quasithin.Background.SmithB42G2FDesc
public import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.Quasithin.B42G2F

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (frK frK_apply kron kron_apply)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing repD matRepE matRepE_apply finite_endRing
  equiv_apply)

section KronSingle

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
@[expose] noncomputable def evalEquiv (i₀ : ι) (hsub : ∀ i ≠ i₀, Subsingleton (κ i))
    [∀ i, Nonempty (κ i)] : (∀ i, κ i) ≃ κ i₀ where
  toFun x := x i₀
  invFun c := Function.update (fun i => Classical.arbitrary (κ i)) i₀ c
  left_inv x := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp
    · change Function.update (fun i => Classical.arbitrary (κ i)) i₀ (x i₀) i = x i
      rw [Function.update_of_ne h]
      exact (hsub i h).elim _ _
  right_inv c := by simp

omit [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem kron_single_apply (A : ∀ i, Matrix (κ i) (κ i) k) (i₀ : ι)
    (hsub : ∀ i ≠ i₀, Subsingleton (κ i)) (hone : ∀ i ≠ i₀, ∀ a, A i a a = 1)
    (x' x : ∀ i, κ i) : kron A x' x = A i₀ (x' i₀) (x i₀) := by
  classical
  rw [kron_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), Finset.prod_eq_one,
    one_mul]
  intro i hi
  have hne := Finset.ne_of_mem_erase hi
  rw [(hsub i hne).elim (x' i) (x i)]
  exact hone i hne (x i)

end KronSingle

section Single

variable {K : Type} [Field K] [CharP K 2] (k : Type) [Field k] [Algebra K k] [CharP k 2]
  {f : ℕ}

omit [CharP K 2] in
theorem subsingleton_idx_of_eq_one (l : G2L) (hl : l = .one) : Subsingleton l.idx := by
  subst hl
  exact inferInstanceAs (Subsingleton Unit)

theorem rep_one_apply_self (l : G2L) (hl : l = .one) (g : ↥(cayleyGroup K)) (a : l.idx) :
    l.rep g a a = 1 := by
  subst hl
  rfl

theorem tRep_single_iso (lab : Fin f → G2L) (i₀ : Fin f) (hlab : ∀ j ≠ i₀, lab j = .one) :
    ∃ (P : Matrix (lab i₀).idx (TIdx lab) k) (Q : Matrix (TIdx lab) (lab i₀).idx k),
      MatIso (tRep K k lab) (matMap (frK k (i₀ : ℕ)) (lab i₀).rep) P Q := by
  have hsub : ∀ j ≠ i₀, Subsingleton (lab j).idx := fun j hj =>
    subsingleton_idx_of_eq_one (lab j) (hlab j hj)
  refine ⟨_, _, matIso_of_reindex (evalEquiv i₀ hsub) fun g x' x => ?_⟩
  change frK k (i₀ : ℕ) ((lab i₀).rep g (x' i₀) (x i₀)) =
    (kron fun j => ((lab j).rep g).map (frK k (j : ℕ))) x' x
  rw [kron_single_apply _ i₀ hsub _ x' x]
  · rfl
  · intro j hj a
    rw [Matrix.map_apply, rep_one_apply_self (lab j) (hlab j hj), map_one]

omit [Algebra K k] [CharP k 2] in
theorem matRep_matMap_equiv_of_eq_nat (φ : K →+* k) (l : G2L) (hl : l = .nat) :
    Nonempty ((matRep (matMap φ l.rep)).Equiv (matRep (matMap φ (repQ (F := K))))) := by
  subst hl
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl k _) fun g => rfl⟩

omit [CharP K 2] [Field k] [Algebra K k] [CharP k 2] in
theorem card_idx (l : G2L) : Fintype.card l.idx =
    match l with
    | .one => 1
    | .nat => 6
    | .lie => 14
    | .st => 64 := by
  cases l
  · rfl
  · rfl
  · rfl
  · exact card_SIdx

omit [CharP K 2] [Field k] [Algebra K k] [CharP k 2] in
theorem single_nat_of_prod_six (lab : Fin f → G2L)
    (h : ∏ j, Fintype.card (lab j).idx = 6) : ∃ i, lab i = .nat ∧ ∀ j ≠ i, lab j = .one := by
  classical
  have hdvd : ∀ j, Fintype.card (lab j).idx ∣ 6 := fun j => by
    rw [← h]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨i, hi⟩ : ∃ i, lab i ≠ .one := by
    by_contra hall
    push Not at hall
    have : ∏ j, Fintype.card (lab j).idx = 1 :=
      Finset.prod_eq_one fun j _ => by rw [hall j]; rfl
    omega
  have hnat : ∀ l : G2L, l ≠ .one → Fintype.card l.idx ∣ 6 → l = .nat := by
    intro l hl hl6
    rw [card_idx] at hl6
    cases l
    · exact absurd rfl hl
    · rfl
    · exact absurd hl6 (by decide)
    · exact absurd hl6 (by decide)
  have hi' := hnat (lab i) hi (hdvd i)
  refine ⟨i, hi', fun j hj => ?_⟩
  have h6 : Fintype.card (lab j).idx * Fintype.card (lab i).idx ∣ 6 := by
    rw [← h, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    exact Nat.mul_dvd_mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr
      ⟨hj, Finset.mem_univ j⟩)) _
  have hci : Fintype.card (lab i).idx = 6 := by rw [card_idx, hi']
  rw [hci] at h6
  have hcj : Fintype.card (lab j).idx = 1 := by
    have h1 := Nat.le_of_dvd (by norm_num) h6
    have h2 : 0 < Fintype.card (lab j).idx := Fintype.card_pos
    omega
  rw [card_idx] at hcj
  revert hcj
  cases lab j <;> simp

end Single

section Natural

theorem exists_ringHom_of_dvd {F D : Type} [Field F] [Field D] [Finite F] [Finite D] [CharP F 2]
    [CharP D 2] {f d : ℕ} (hF : Nat.card F = 2 ^ f) (hD : Nat.card D = 2 ^ d) (hfd : f ∣ d) :
    Nonempty (F →+* D) := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : Algebra (ZMod 2) D := ZMod.algebra D 2
  have : Fintype F := Fintype.ofFinite F
  have : Fintype D := Fintype.ofFinite D
  have hfF : Module.finrank (ZMod 2) F = f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, Fintype.card_eq_nat_card, hF] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfD : Module.finrank (ZMod 2) D = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [ZMod.card, Fintype.card_eq_nat_card, hD] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := F) (L := D)
    (by rw [hfF, hfD]; exact hfd)
  exact ⟨ι.toRingHom⟩

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) ↥(cayleyGroup K) M} [Fact ρ.IsIrreducible]

theorem exists_equiv_twistQ [CharP (EndRing ρ) 2] {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    (ι : K →+* EndRing ρ) (b : Module.Basis (Fin 6) (EndRing ρ) M) :
    ∃ i : ℕ, Nonempty ((letI := ι.toAlgebra
      matRep (matMap (frK (F := K) (EndRing ρ) i) (repQ (F := K)))).Equiv
        (matRepE b (RingHom.id (EndRing ρ)))) := by
  classical
  let _ : Algebra K (EndRing ρ) := ι.toAlgebra
  obtain ⟨lab, ⟨Φ⟩, hdim'⟩ := exists_label hK b ι (RingHom.id (EndRing ρ))
  obtain ⟨i, hi, hother⟩ := single_nat_of_prod_six lab hdim'.symm
  obtain ⟨P, Q, hPQ⟩ := tRep_single_iso (K := K) (EndRing ρ) lab i hother
  obtain ⟨e1⟩ := hPQ.equiv
  obtain ⟨e2⟩ := matRep_matMap_equiv_of_eq_nat (EndRing ρ) (frK (F := K) (EndRing ρ) (i : ℕ))
    (lab i) hi
  exact ⟨i, ⟨(e2.symm.trans e1.symm).trans Φ⟩⟩

omit [CharP K 2] [Fintype K] [Fact ρ.IsIrreducible] in
theorem equivFun_rep {m : ℕ} [Fact ρ.IsIrreducible] (b : Module.Basis (Fin m) (EndRing ρ) M)
    (g : ↥(cayleyGroup K)) (w : M) :
    b.equivFun (ρ g w) = matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) := by
  rw [matRepE_apply]
  have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  simp only [Module.Basis.equivFun_apply]
  rw [show (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map (RingHom.id (EndRing ρ)) =
    CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g from Matrix.ext fun _ _ => rfl]
  exact this.symm

theorem exists_coords_of_six {f : ℕ} (hK : Fintype.card K = 2 ^ f) (ι : K →+* EndRing ρ)
    (hdim : Module.finrank (EndRing ρ) M = 6) :
    ∃ (i : ℕ) (θ : M ≃+ (Ix3 → EndRing ρ)), ∀ g w a,
      θ (ρ g w) a = ∑ c, ι (repQ g a c) ^ 2 ^ i * θ w c := by
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  let _ : Algebra K (EndRing ρ) := ι.toAlgebra
  have b : Module.Basis (Fin 6) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨i, ⟨Ψ⟩⟩ := exists_equiv_twistQ hK ι b
  obtain ⟨θ, hθ⟩ : ∃ θ : M ≃+ (Ix3 → EndRing ρ), ∀ w, θ w = Ψ.symm (b.equivFun w) :=
    ⟨b.equivFun.toAddEquiv.trans Ψ.symm.toLinearEquiv.toAddEquiv, fun w => rfl⟩
  refine ⟨i, θ, fun g w a => ?_⟩
  have h1 : b.equivFun (ρ g w) = matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) :=
    equivFun_rep b g w
  have h2 := equiv_apply Ψ.symm g (b.equivFun w)
  have h4 : Ψ.symm (b.equivFun (ρ g w)) =
      Ψ.symm (matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w)) := congrArg _ h1
  have h5 : θ (ρ g w) = matRep (matMap (frK (F := K) (EndRing ρ) i) (repQ (F := K))) g
      (θ w) :=
    (hθ (ρ g w)).trans (h4.trans (h2.trans (congrArg _ (hθ w).symm)))
  refine (congrFun h5 a).trans ?_
  simp only [matRep_apply, matMap_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, frK_apply,
    RingHom.algebraMap_toAlgebra]

theorem exists_natural_of_six {f d : ℕ} (hK : Fintype.card K = 2 ^ f)
    (hDcard : Nat.card (EndRing ρ) = 2 ^ d) (hfd : f ∣ d)
    (hdim : Module.finrank (EndRing ρ) M = 6) :
    ∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (ρ g w) = g2Act g (φ w) := by
  classical
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hFcard : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨ι⟩ := exists_ringHom_of_dvd hFcard hDcard hfd
  obtain ⟨i, θ, hθ⟩ := exists_coords_of_six hK ι hdim
  have hsurj : Function.Surjective ι := by
    obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
    let U₀ : AddSubgroup M :=
      { carrier := {w | ∀ a, θ w a ∈ ι.range}
        add_mem' := fun {x y} hx hy a => by
          rw [map_add, Pi.add_apply]
          exact ι.range.add_mem (hx a) (hy a)
        zero_mem' := fun a => by
          rw [map_zero, Pi.zero_apply]
          exact ι.range.zero_mem
        neg_mem' := fun {x} hx a => by
          rw [map_neg, Pi.neg_apply]
          exact ι.range.neg_mem (hx a) }
    let U : Submodule (ZMod 2) M := AddSubgroup.toZModSubmodule 2 U₀
    have hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
      intro g u hu a
      rw [hθ]
      refine ι.range.sum_mem fun c _ => ι.range.mul_mem ?_ (hu c)
      rw [← map_pow]
      exact ⟨_, rfl⟩
    have hne : θ.symm (Pi.single (.inl 0) 1) ∈ U := by
      intro a
      rw [AddEquiv.apply_symm_apply]
      by_cases ha : a = .inl 0
      · subst ha
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [ha]⟩
    rcases hirr U hU with h | h
    · exfalso
      have h1 : θ.symm (Pi.single (.inl 0) 1) = 0 := by
        have := hne
        rw [h] at this
        exact (Submodule.mem_bot _).mp this
      have h2 := congrArg (fun w => θ w (.inl 0)) h1
      simp at h2
    · intro x
      have hx : θ.symm (Pi.single (.inl 0) x) ∈ U := by rw [h]; exact Submodule.mem_top
      have := hx (.inl 0)
      change θ (θ.symm (Pi.single (.inl 0) x)) (.inl 0) ∈ ι.range at this
      rw [AddEquiv.apply_symm_apply] at this
      simpa using this
  let κ : EndRing ρ ≃+* K := (RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩).symm
  have hκ : ∀ x, κ (ι x) = x := fun x =>
    (RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩).symm_apply_apply x
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 i
  have hσ : ∀ x, σ.symm (x ^ 2 ^ i) = x := fun x => by
    rw [RingEquiv.symm_apply_eq, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  let τ : EndRing ρ →+* K := (κ.trans σ.symm).toRingHom
  have hτ : ∀ x, τ (ι x ^ 2 ^ i) = x := fun x => by
    change σ.symm (κ (ι x ^ 2 ^ i)) = x
    rw [map_pow, hκ, hσ]
  let φ : M ≃+ (Ix3 → K) :=
    θ.trans (AddEquiv.piCongrRight fun _ => (κ.trans σ.symm).toAddEquiv)
  have hφ : ∀ w a, φ w a = τ (θ w a) := fun w a => rfl
  refine ⟨φ, fun g w => ?_⟩
  funext a
  rw [← repQ_mulVec, hφ, hθ, map_sum]
  simp only [Matrix.mulVec, dotProduct, map_mul, hτ, hφ]

end Natural

section Dichotomy

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) ↥(cayleyGroup K) M} [Fact ρ.IsIrreducible]

omit [CharP K 2] [Fintype K] in
theorem prod_card_single {f : ℕ} (lab : Fin f → G2L) (j₀ : Fin f)
    (hlab : ∀ j ≠ j₀, lab j = .one) :
    ∏ j, Fintype.card (lab j).idx = Fintype.card (lab j₀).idx := by
  classical
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀), Finset.prod_eq_one, one_mul]
  intro j hj
  rw [card_idx, hlab j (Finset.ne_of_mem_erase hj)]

omit [Fintype K] in
theorem five_le_rank_of_ne [Finite K] (l : G2L) (h1 : l ≠ .one) (h2 : l ≠ .nat)
    {z : ↥(cayleyGroup K)} (hz : z * z = 1) (hz1 : z ≠ 1) : 5 ≤ (l.rep z - 1).rank := by
  cases l
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact five_le_rank_repLie hz hz1
  · exact le_trans (by norm_num) (eight_le_rank_repSt hz hz1)

theorem natural_or_large_displacement {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 1 ≤ f)
    (hnt : ∃ g, ρ g ≠ 1) :
    (∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (ρ g w) = g2Act g (φ w)) ∨
      ∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 →
        3 * f + 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := g2_descent hK hf hnt
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, lab, ⟨Φ⟩, hshift, hne, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  let _ : Algebra K E := ιF.toAlgebra
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  have hfS : f ≤ S.card * d := le_card_support_mul lab hd1 hshift hne
  have hdisp : ∀ z : ↥(cayleyGroup K), Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) =
      d * (tRep K E lab z - 1).rank := fun z =>
    finrank_range_eq hDcard _ ιF ιD lab Φ hdim z
  by_cases hS2 : 2 ≤ S.card
  · right
    intro z hz hz1
    rw [hdisp]
    have h := rank_tRep_ge E lab hz hz1 hS2
    nlinarith
  ·
    have hS1 : S.card = 1 := by
      obtain ⟨j, hj⟩ := hne
      have : 0 < S.card := Finset.card_pos.mpr ⟨j, by simpa [hS] using hj⟩
      omega
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hS1
    have hother : ∀ j ≠ j₀, lab j = .one := fun j hj => by
      by_contra h
      have : j ∈ S := by simpa [hS] using h
      rw [hj₀] at this
      exact hj (Finset.mem_singleton.mp this)
    have hj₀S : lab j₀ ≠ .one := by
      have : j₀ ∈ S := by rw [hj₀]; exact Finset.mem_singleton_self j₀
      simpa [hS] using this
    have hfd : f ∣ d := dvd_of_single lab j₀ hshift hj₀S hother
    by_cases hnat : lab j₀ = .nat
    · left
      have h6 : Module.finrank (EndRing ρ) M = 6 := by
        rw [hdim, prod_card_single lab j₀ hother, card_idx, hnat]
      exact exists_natural_of_six hK hDcard hfd h6
    · right
      intro z hz hz1
      rw [hdisp, rank_tRep_single E lab j₀ hother hz]
      have h5 := five_le_rank_of_ne (lab j₀) hj₀S hnat hz hz1
      have hdf : f ≤ d := Nat.le_of_dvd (by omega) hfd
      nlinarith

end Dichotomy

end CFSG.Quasithin.B42G2F
