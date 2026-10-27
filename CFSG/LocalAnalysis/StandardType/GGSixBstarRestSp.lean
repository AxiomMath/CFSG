module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestDefs
public import CFSG.LieType.Steinberg.Classical.Symplectic
public import CFSG.LieType.Universal.SymplecticExtras

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic

open TauCeti.GLSymplecticFin (RootSubgroupIndex)

open scoped commutatorElement

namespace RestSp

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem isDiag_of_commute_diagonal {κ : Type*} {M : Matrix ι ι F} {δ : κ → ι → F}
    (hsep : ∀ i j, i ≠ j → ∃ k, δ k i ≠ δ k j)
    (hM : ∀ k, M * diagonal (δ k) = diagonal (δ k) * M) : M.IsDiag := by
  intro i j hij
  obtain ⟨k, hk⟩ := hsep i j hij
  have h := congrFun (congrFun (hM k) i) j
  rw [mul_diagonal, diagonal_mul] at h
  have h2 : M i j * (δ k j - δ k i) = 0 := by rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hk

theorem isDiag_commute {M N : Matrix ι ι F} (hM : M.IsDiag) (hN : N.IsDiag) : M * N = N * M := by
  obtain ⟨a, rfl⟩ : ∃ a, M = diagonal a := ⟨_, hM.diagonal_diag.symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, N = diagonal b := ⟨_, hN.diagonal_diag.symm⟩
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

end Diag

section Chars

variable {n : ℕ} {F : Type} [Field F]

@[expose] def coordChar (t : Fin n → Fˣ) : Fin n ⊕ Fin n → F :=
  Sum.elim (fun i => (t i : F)) (fun i => (((t i)⁻¹ : Fˣ) : F))

theorem exists_root_of_coincide {κ : Type*} {T : κ → Fin n → Fˣ} {a b : Fin n ⊕ Fin n}
    (hab : a ≠ b) (h : ∀ k, coordChar (T k) a = coordChar (T k) b) :
    ∃ r : RootSubgroupIndex n, ∀ k, r.character (T k) = 1 := by
  rcases a with i | i <;> rcases b with j | j
  · have hij : i ≠ j := fun h' => hab (by rw [h'])
    refine ⟨.difference i j hij, fun k => ?_⟩
    have e : T k i = T k j := Units.ext (h k)
    rw [RootSubgroupIndex.character_difference, e, mul_inv_cancel]
  · have e : ∀ k, T k i = (T k j)⁻¹ := fun k => Units.ext (h k)
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · refine ⟨.positiveSum i j hlt, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveSum, e k, inv_mul_cancel]
    · refine ⟨.positiveLong i, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveLong]
      calc T k i * T k i = T k i * (T k i)⁻¹ := congrArg (T k i * ·) (e k)
        _ = 1 := mul_inv_cancel _
    · refine ⟨.positiveSum j i hgt, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveSum, e k, mul_inv_cancel]
  · have e : ∀ k, (T k i)⁻¹ = T k j := fun k => Units.ext (h k)
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · refine ⟨.positiveSum i j hlt, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveSum, ← e k, mul_inv_cancel]
    · refine ⟨.positiveLong i, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveLong]
      calc T k i * T k i = T k i * (T k i)⁻¹ := congrArg (T k i * ·) (e k).symm
        _ = 1 := mul_inv_cancel _
    · refine ⟨.positiveSum j i hgt, fun k => ?_⟩
      rw [RootSubgroupIndex.character_positiveSum, ← e k, inv_mul_cancel]
  · have hij : i ≠ j := fun h' => hab (by rw [h'])
    refine ⟨.difference i j hij, fun k => ?_⟩
    have e : T k i = T k j := inv_injective (Units.ext (h k))
    rw [RootSubgroupIndex.character_difference, e, mul_inv_cancel]

theorem diag_comm_elt {t : Fin n → Fˣ} {r : RootSubgroupIndex n} (hr : r.character t = 1)
    (c : F) :
    equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) * SpExtras.elt r c =
      SpExtras.elt r c * equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) := by
  have h := TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv r t (Multiplicative.ofAdd c)
  rw [hr, Units.val_one, one_mul, toAdd_ofAdd] at h
  have h2 : TauCeti.GLSymplecticFin.diagonal t * r.hom (Multiplicative.ofAdd c) =
      r.hom (Multiplicative.ofAdd c) * TauCeti.GLSymplecticFin.diagonal t := by
    calc TauCeti.GLSymplecticFin.diagonal t * r.hom (Multiplicative.ofAdd c) =
        (TauCeti.GLSymplecticFin.diagonal t * r.hom (Multiplicative.ofAdd c) *
          (TauCeti.GLSymplecticFin.diagonal t)⁻¹) * TauCeti.GLSymplecticFin.diagonal t := by
          group
      _ = r.hom (Multiplicative.ofAdd c) * TauCeti.GLSymplecticFin.diagonal t := by rw [h]
  simp only [SpExtras.elt]
  rw [← map_mul, ← map_mul, h2]

end Chars

section Frame

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def frameDiag (A₀ : StatedSp n F) (t : Fin n → Fˣ) : StatedSp n F :=
  A₀ * equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) * A₀⁻¹

theorem exists_root_of_frame {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {D J : Subgroup G} (hJψ : J ≤ ψ.range)
    (hJD : D ≤ Subgroup.centralizer (J : Set G)) (hJ : CFSG.Assembly.IsQuasisimple J)
    (A₀ : StatedSp n F) (T : G → Fin n → Fˣ) (hT : ∀ d ∈ D, d = ψ (frameDiag A₀ (T d))) :
    ∃ r : RootSubgroupIndex n, ∀ d ∈ D, r.character (T d) = 1 := by
  by_cases hsep : ∀ a b : Fin n ⊕ Fin n, a ≠ b →
      ∃ d : ↥D, coordChar (T d) a ≠ coordChar (T d) b
  · exfalso
    set S : Set G := {g | ∃ w : StatedSp n F,
      (SpExtras.mat n F (A₀⁻¹ * w * A₀)).IsDiag ∧ ψ w = g} with hS
    have hcommS : S.Pairwise Commute := by
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ -
      have h1 := isDiag_commute hw hw'
      rw [← map_mul, ← map_mul] at h1
      have e : ∀ a b : StatedSp n F, (A₀⁻¹ * a * A₀) * (A₀⁻¹ * b * A₀) = A₀⁻¹ * (a * b) * A₀ :=
        fun a b => by group
      rw [e, e] at h1
      have h3 : w * w' = w' * w := by
        have h4 := SpExtras.mat_injective h1
        exact mul_left_cancel (mul_right_cancel h4)
      change ψ w * ψ w' = ψ w' * ψ w
      rw [← map_mul, ← map_mul, h3]
    have hcent : ∀ d ∈ D, ∀ y : StatedSp n F, ψ y ∈ J →
        frameDiag A₀ (T d) * y * (frameDiag A₀ (T d))⁻¹ * y⁻¹ ∈ Subgroup.center _ := by
      intro d hd y hy
      apply hker
      have hc := Subgroup.mem_centralizer_iff.mp (hJD hd) (ψ y) hy
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hT d hd, ← hc]
      group
    have hcomm : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ S := by
      intro a ha b hb
      obtain ⟨y₁, rfl⟩ := hJψ ha
      obtain ⟨y₂, rfl⟩ := hJψ hb
      refine ⟨⁅y₁, y₂⁆, ?_, map_commutatorElement ψ y₁ y₂⟩
      apply isDiag_of_commute_diagonal hsep
      rintro ⟨d, hd⟩
      set Y := frameDiag A₀ (T d) with hY
      have hfix : Y * ⁅y₁, y₂⁆ * Y⁻¹ = ⁅y₁, y₂⁆ := by
        have h := RootPlaneA.commutatorElement_mul_central (hcent d hd y₁ ha) (hcent d hd y₂ hb)
          y₁ y₂
        simp only [inv_mul_cancel_right] at h
        have hconj : ⁅Y * y₁ * Y⁻¹, Y * y₂ * Y⁻¹⁆ = Y * ⁅y₁, y₂⁆ * Y⁻¹ := by
          have := map_commutatorElement (MulAut.conj Y) y₁ y₂
          simpa only [MulAut.conj_apply] using this.symm
        rw [← hconj, h]
      set W := A₀⁻¹ * ⁅y₁, y₂⁆ * A₀ with hW
      set Δ := equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (T d)) with hΔ
      have hWΔ : W * Δ = Δ * W := by
        have e1 : Y = A₀ * Δ * A₀⁻¹ := rfl
        have h2 : (A₀ * Δ * A₀⁻¹) * ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆ * (A₀ * Δ * A₀⁻¹) := by
          rw [← e1]
          calc Y * ⁅y₁, y₂⁆ = Y * ⁅y₁, y₂⁆ * Y⁻¹ * Y := by group
            _ = ⁅y₁, y₂⁆ * Y := by rw [hfix]
        calc W * Δ = A₀⁻¹ * (⁅y₁, y₂⁆ * (A₀ * Δ * A₀⁻¹)) * A₀ := by rw [hW]; group
          _ = A₀⁻¹ * ((A₀ * Δ * A₀⁻¹) * ⁅y₁, y₂⁆) * A₀ := by rw [h2]
          _ = Δ * W := by rw [hW]; group
      have hm : SpExtras.mat n F W * SpExtras.mat n F Δ =
          SpExtras.mat n F Δ * SpExtras.mat n F W := by
        rw [← map_mul, ← map_mul, hWΔ]
      rw [hΔ, SpExtras.mat_equiv_diagonal] at hm
      exact hm
    have hle : J ≤ Subgroup.closure S := by
      calc J = ⁅J, J⁆ := (RootPlaneA.commutator_eq_of_isQuasisimple hJ).symm
        _ ≤ Subgroup.closure S := Subgroup.commutator_le.mpr fun a ha b hb =>
            Subgroup.subset_closure (hcomm a ha b hb)
    have hab := Subgroup.isMulCommutative_closure hcommS
    exact RootPlaneA.false_of_isQuasisimple_of_comm hJ fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, hle ha⟩ ⟨b, hle hb⟩)
  · push Not at hsep
    obtain ⟨a, b, hab, hδ⟩ := hsep
    obtain ⟨r, hr⟩ := exists_root_of_coincide (T := fun d : ↥D => T d) hab hδ
    exact ⟨r, fun d hd => hr ⟨d, hd⟩⟩

theorem frameDiag_comm {A₀ : StatedSp n F} {t : Fin n → Fˣ} {r : RootSubgroupIndex n}
    (hr : r.character t = 1) (c : F) :
    frameDiag A₀ t * (A₀ * SpExtras.elt r c * A₀⁻¹) =
      (A₀ * SpExtras.elt r c * A₀⁻¹) * frameDiag A₀ t := by
  have h := diag_comm_elt hr c
  calc frameDiag A₀ t * (A₀ * SpExtras.elt r c * A₀⁻¹) =
      A₀ * (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) * SpExtras.elt r c) * A₀⁻¹ := by
        rw [frameDiag]; group
    _ = A₀ * (SpExtras.elt r c * equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t)) *
          A₀⁻¹ := by rw [h]
    _ = (A₀ * SpExtras.elt r c * A₀⁻¹) * frameDiag A₀ t := by rw [frameDiag]; group

theorem elt_one_not_mem_center (r : RootSubgroupIndex n) :
    SpExtras.elt (F := F) r 1 ∉ Subgroup.center (StatedSp n F) := by
  intro hc
  rw [Symplectic.center_eq] at hc
  obtain ⟨u, hu⟩ := hc
  have hu' : ((SpExtras.elt (F := F) r 1 : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      Matrix.GeneralLinearGroup.scalar _ u := hu.symm
  have h1 := SpExtras.mat_elt_apply_pos1 (F := F) r 1
  rw [SpExtras.mat_apply, hu', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_apply_ne _ (SpExtras.pos1_ne r)] at h1
  exact zero_ne_one h1

theorem comm_psi_frameDiag (ψ : StatedSp n F →* G) {A₀ : StatedSp n F} {t : Fin n → Fˣ}
    {r : RootSubgroupIndex n} (hr : r.character t = 1) (c : F) :
    ψ (A₀ * SpExtras.elt r c * A₀⁻¹) * ψ (frameDiag A₀ t) =
      ψ (frameDiag A₀ t) * ψ (A₀ * SpExtras.elt r c * A₀⁻¹) := by
  rw [← map_mul, ← map_mul, frameDiag_comm hr c]

theorem orderOf_psi_conj_elt [CharP F 2] (ψ : StatedSp n F →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) (A₀ : StatedSp n F)
    (r : RootSubgroupIndex n) : orderOf (ψ (A₀ * SpExtras.elt r 1 * A₀⁻¹)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← map_pow, conj_pow, pow_two, ← SpExtras.elt_add, CharTwo.add_self_eq_zero,
      SpExtras.elt_zero, mul_one, mul_inv_cancel, map_one]
  · intro h1
    have hc : A₀ * SpExtras.elt r 1 * A₀⁻¹ ∈ Subgroup.center _ := hker h1
    apply elt_one_not_mem_center (F := F) r
    have hcg := Subgroup.mem_center_iff.mp hc A₀⁻¹
    have e : SpExtras.elt r (1 : F) = A₀ * SpExtras.elt r 1 * A₀⁻¹ := by
      calc SpExtras.elt r (1 : F) = A₀⁻¹ * (A₀ * SpExtras.elt r 1 * A₀⁻¹) * A₀ := by group
        _ = (A₀ * SpExtras.elt r 1 * A₀⁻¹) * A₀⁻¹ * A₀ := by rw [hcg]
        _ = A₀ * SpExtras.elt r 1 * A₀⁻¹ := by group
    rw [e]
    exact hc

end Frame

end RestSp

section Inputs

@[expose] def GGPSpSplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSp ∧ p ∣ 2 ^ f - 1

@[expose] def GGPSpNonsplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSp ∧ ¬ p ∣ 2 ^ f - 1

@[expose] def GGSpBstarFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ → GGSixStepOne p B Bs x L D J →
      p ∣ 2 ^ f - 1 →
        ∃ A₀ : StatedSp n (GaloisField 2 f), ∀ b ∈ Bs, ∃ t : Fin n → (GaloisField 2 f)ˣ,
          b = ψ (RestSp.frameDiag A₀ t)

theorem ggRootPlaneInputOn_PSpSplit_of_frame (hF : GGSpBstarFrameInput) :
    GGRootPlaneInputOn GGPSpSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  obtain ⟨rfl, hp⟩ := hP
  obtain ⟨A₀, hA₀⟩ := hF G p B Bs x L D J n f ψ hctx s1 hp
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hJψ : J ≤ ψ.range := hctx.range_eq ▸ hctx.le_ggG0
  choose! T hT using fun d (hd : d ∈ D) => hA₀ d (hctx.d_le_bstar hd)
  obtain ⟨r, hr⟩ := RestSp.exists_root_of_frame hker hJψ hctx.le_centralizer_J
    hctx.stdSub.1.2.2.2.2.2.1.2.2 A₀ T hT
  obtain ⟨γ, hγ, hγr⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec r
  have hroot : ∀ z, z ∈ Symplectic.rootGroup n (GaloisField 2 f) γ ↔
      ∃ c : GaloisField 2 f, z = SpExtras.elt r c := fun z => SpExtras.mem_rootGroup_iff hγr.symm
  refine ⟨D, γ, A₀, ψ (A₀ * SpExtras.elt r 1 * A₀⁻¹), hctx.d_le_bstar, hctx.d_elem,
    hctx.stdSub.1.2.2.1, ⟨hγ, fun h => ?_⟩, ?_, ?_, ?_, fun e he _ => Or.inl he⟩
  · rcases h with h | h | h <;> cases h
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (hroot z).mp hz
    change ψ (A₀ * SpExtras.elt r c * A₀⁻¹) * d = d * ψ (A₀ * SpExtras.elt r c * A₀⁻¹)
    rw [hT d hd]
    exact RestSp.comm_psi_frameDiag ψ (hr d hd) c
  · exact ⟨_, ⟨SpExtras.elt r 1, (hroot _).mpr ⟨1, rfl⟩, rfl⟩, rfl⟩
  · exact RestSp.orderOf_psi_conj_elt ψ hker A₀ r

theorem ggRootPlaneAt_PSp_of_frame (hF : GGSpBstarFrameInput)
    (h₂ : GGRootPlaneInputOn GGPSpNonsplit) : GGRootPlaneAt .PSp := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1
  by_cases hp : p ∣ 2 ^ f - 1
  · exact ggRootPlaneInputOn_PSpSplit_of_frame hF G p B Bs x L D J t n f ψ ⟨ht, hp⟩ hctx s1
  · exact h₂ G p B Bs x L D J t n f ψ ⟨ht, hp⟩ hctx s1

end Inputs

end CFSG.StandardType
