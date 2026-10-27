module

public import CFSG.Quasithin.Background.SmithB45U33Coind
public import CFSG.Quasithin.Background.SmithB45U33Lie
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Vol2.Ch3Sec3G2XS3

public section

namespace CFSG.Quasithin.B45U33

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.H13 CFSG.CharacterTheory.SteinbergBY
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (frK frK_apply)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE finite_endRing equiv_apply
  natCard_eq_pow_finrank)

section Lie

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) ↥(cayleyGroup K) M} [Fact ρ.IsIrreducible]

omit [Fintype K] in
theorem matRep_matMap_equiv_of_eq_lie {k : Type} [Field k] (φ : K →+* k) (l : G2L)
    (hl : l = .lie) :
    Nonempty ((matRep (matMap φ (l.rep (F := K)))).Equiv
      (matRep (matMap φ (repLie (F := K))))) := by
  subst hl
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl k _) fun g => rfl⟩

theorem lab_eq_lie (lab : Fin 1 → G2L) (h : ∏ j, Fintype.card (lab j).idx = 14) :
    lab 0 = .lie := by
  rw [Fin.prod_univ_one, B42G2F.card_idx] at h
  revert h
  cases lab 0 <;> simp

theorem exists_equiv_lie [CharP (EndRing ρ) 2] (hK : Fintype.card K = 2 ^ 1)
    (ι : K →+* EndRing ρ) (b : Module.Basis (Fin 14) (EndRing ρ) M) :
    Nonempty ((letI := ι.toAlgebra
      matRep (matMap (frK (F := K) (EndRing ρ) 0) (repLie (F := K)))).Equiv
        (matRepE b (RingHom.id (EndRing ρ)))) := by
  classical
  let _ : Algebra K (EndRing ρ) := ι.toAlgebra
  obtain ⟨lab, ⟨Φ⟩, hdim'⟩ := B42G2F.exists_label hK b ι (RingHom.id (EndRing ρ))
  have hl : lab 0 = .lie := lab_eq_lie lab hdim'.symm
  obtain ⟨P, Q, hPQ⟩ := B42G2F.tRep_single_iso (K := K) (EndRing ρ) lab 0
    (fun j hj => absurd (Subsingleton.elim j 0) hj)
  have e1' := hPQ.equiv
  obtain ⟨e1⟩ := e1'
  have e2' := matRep_matMap_equiv_of_eq_lie (frK (F := K) (EndRing ρ) ((0 : Fin 1) : ℕ))
    (lab 0) hl
  obtain ⟨e2⟩ := e2'
  exact ⟨(e2.symm.trans e1.symm).trans Φ⟩

theorem exists_coords_of_lie (hK : Fintype.card K = 2 ^ 1) (ι : K →+* EndRing ρ)
    (hdim : Module.finrank (EndRing ρ) M = 14) :
    ∃ θ : M ≃+ (LIdx → EndRing ρ), ∀ g w a,
      θ (ρ g w) a = ∑ c, ι (repLie g a c) * θ w c := by
  classical
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  let _ : Algebra K (EndRing ρ) := ι.toAlgebra
  have b : Module.Basis (Fin 14) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨Ψ⟩ := exists_equiv_lie hK ι b
  obtain ⟨θ, hθ⟩ : ∃ θ : M ≃+ (LIdx → EndRing ρ), ∀ w, θ w = Ψ.symm (b.equivFun w) :=
    ⟨b.equivFun.toAddEquiv.trans Ψ.symm.toLinearEquiv.toAddEquiv, fun w => rfl⟩
  refine ⟨θ, fun g w a => ?_⟩
  have h1 : b.equivFun (ρ g w) = matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) :=
    B42G2F.equivFun_rep b g w
  have h2 := equiv_apply Ψ.symm g (b.equivFun w)
  have h4 : Ψ.symm (b.equivFun (ρ g w)) =
      Ψ.symm (matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w)) := congrArg _ h1
  have h5 : θ (ρ g w) = matRep (matMap (frK (F := K) (EndRing ρ) 0) (repLie (F := K))) g
      (θ w) :=
    (hθ (ρ g w)).trans (h4.trans (h2.trans (congrArg _ (hθ w).symm)))
  refine (congrFun h5 a).trans ?_
  simp only [matRep_apply, matMap_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, frK_apply,
    RingHom.algebraMap_toAlgebra, pow_zero, pow_one]

theorem exists_lie_of_fourteen (hK : Fintype.card K = 2 ^ 1)
    (hdim : Module.finrank (EndRing ρ) M = 14) (hD : Nat.card (EndRing ρ) = 2 ^ 1) :
    ∃ θ : M ≃+ (LIdx → K), ∀ g w, θ (ρ g w) = (repLie g).mulVec (θ w) := by
  classical
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hFcard : Nat.card K = 2 ^ 1 := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨ι⟩ := B42G2F.exists_ringHom_of_dvd hFcard hD (dvd_refl 1)
  obtain ⟨θ₀, hθ₀⟩ := exists_coords_of_lie hK ι hdim
  have hbij : Function.Bijective ι := ι.injective.bijective_of_nat_card_le (by
    rw [hD, hFcard])
  let κ : EndRing ρ ≃+* K := (RingEquiv.ofBijective ι hbij).symm
  have hκ : ∀ x, κ (ι x) = x := fun x => (RingEquiv.ofBijective ι hbij).symm_apply_apply x
  let τ : EndRing ρ →+* K := κ.toRingHom
  have hτ : ∀ x, τ (ι x) = x := hκ
  let θ : M ≃+ (LIdx → K) := θ₀.trans (AddEquiv.piCongrRight fun _ => κ.toAddEquiv)
  have hθ : ∀ w a, θ w a = τ (θ₀ w a) := fun w a => rfl
  refine ⟨θ, fun g w => funext fun a => ?_⟩
  change τ (θ₀ (ρ g w) a) = ∑ c, repLie g a c * θ w c
  rw [hθ₀]
  refine (map_sum τ (fun c => ι (repLie g a c) * θ₀ w c) Finset.univ).trans
    (Finset.sum_congr rfl fun c _ => ?_)
  refine (map_mul τ _ _).trans ?_
  rw [hτ, hθ]

end Lie

section LieTwo

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) ↥(cayleyGroup (ZMod 2)) M} [Fact ρ.IsIrreducible]

omit [Fact ρ.IsIrreducible] [Finite M] in
theorem eq_zero_or_eq_one_of_card {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (x : F) :
    x = 0 ∨ x = 1 := by
  classical
  let f : Bool → F := fun t => if t then 1 else 0
  have hf : Function.Injective f := by
    intro s t hst
    cases s <;> cases t <;> simp_all [f]
  have hbij := hf.bijective_of_nat_card_le (by rw [hF, Nat.card_eq_fintype_card,
    Fintype.card_bool])
  obtain ⟨t, rfl⟩ := hbij.2 x
  cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fact ρ.IsIrreducible] [Finite M] in
theorem eq_bot_or_eq_top_of_lie (θ : M ≃+ (LIdx → ZMod 2))
    (hθ : ∀ g w, θ (ρ g w) = (repLie g).mulVec (θ w)) (Y : Submodule (ZMod 2) M)
    (hY : ∀ w : FreeGroup (Fin 2), ∀ y ∈ Y, ρ (FreeGroup.lift ![g2a, g2b] w) y ∈ Y) :
    Y = ⊥ ∨ Y = ⊤ := by
  have h01 := eq_zero_or_eq_one_of_card (F := ZMod 2) (Nat.card_zmod 2)
  let T : Submodule (ZMod 2) (Fin 14 → ZMod 2) :=
    { carrier := θ '' Y
      add_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y + y', Y.add_mem hy hy', map_add θ y y'⟩
      zero_mem' := ⟨0, Y.zero_mem, map_zero θ⟩
      smul_mem' := by
        rintro δ _ ⟨y, hy, rfl⟩
        rcases h01 δ with rfl | rfl
        · rw [zero_smul]
          exact ⟨0, Y.zero_mem, map_zero θ⟩
        · rw [one_smul]
          exact ⟨y, hy, rfl⟩ }
  have hmemT : ∀ u, u ∈ T ↔ ∃ y ∈ Y, θ y = u := fun u => Iff.rfl
  obtain ⟨-, hirr⟩ := (isIrreducible_iff _).mp (isIrreducible_mFree (RingHom.id (ZMod 2)))
  have hTinv : ∀ w, ∀ u ∈ T, matrixBaseChange (RingHom.id (ZMod 2)) mFree w u ∈ T := by
    intro w u hu
    have hu' := (hmemT u).1 hu
    obtain ⟨y, hy, rfl⟩ := hu'
    refine (hmemT _).2 ⟨ρ (FreeGroup.lift ![g2a, g2b] w) y, hY w y hy, ?_⟩
    rw [hθ, matrixBaseChange_apply, repLie_lift]
    rfl
  rcases hirr T hTinv with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have h1 : θ y ∈ T := (hmemT _).2 ⟨y, hy, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact (map_eq_zero_iff θ θ.injective).mp h1
  · right
    rw [eq_top_iff]
    intro x _
    have h1 : θ x ∈ T := h ▸ Submodule.mem_top
    have h1' := (hmemT _).1 h1
    obtain ⟨y, hy, hyx⟩ := h1'
    rw [← θ.injective hyx]
    exact hy

end LieTwo

theorem index_g2Derived :
    (g2Derived (ZMod 2)).index = 2 := by
  have h1 := (g2Derived (ZMod 2)).card_mul_index
  rw [G2XS3.card_g2Derived, Orbit.card_g2Two] at h1
  omega

@[expose] noncomputable def cayEquiv : ↥(cayleyGroup (ZMod 2)) ≃* ↥(quasithinG2 (ZMod 2)) :=
  MulEquiv.subgroupCongr (G11.P3G2.quasithinG2_eq_cayleyGroup (K := ZMod 2)).symm

theorem coe_cayEquiv (g : ↥(cayleyGroup (ZMod 2))) :
    ((cayEquiv g : ↥(quasithinG2 (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) = g := rfl

theorem cayEquiv_lift_mem
    (w : FreeGroup (Fin 2)) :
    cayEquiv (FreeGroup.lift ![g2a, g2b] w) ∈ g2Derived (ZMod 2) := by
  have hle : (FreeGroup.lift ![g2a, g2b]).range ≤
      (g2Derived (ZMod 2)).comap cayEquiv.toMonoidHom := by
    refine FreeGroup.range_lift_le ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, g2Derived, Subgroup.mem_subgroupOf,
      MulEquiv.coe_toMonoidHom, coe_cayEquiv, G11.P3G2.quasithinG2_eq_cayleyGroup]
    match i with
    | 0 => exact g2a_mem
    | 1 => exact g2b_mem
  exact hle ⟨w, rfl⟩

section Main

theorem card_le_of_g2Derived {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (σ : ↥(g2Derived (ZMod 2)) →* (M →ₗ[ZMod 2] M)) (hnt : ∃ h, σ h ≠ 1)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ h, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcard : Nat.card M ≤ 2 ^ 12) : Nat.card M ≤ 2 ^ 6 := by
  classical
  have : Nontrivial M := by
    obtain ⟨h, hh⟩ := hnt
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact hh (LinearMap.ext fun x => Subsingleton.elim _ _)
  have : Finite ↥(quasithinG2 (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [Orbit.card_g2Two]; norm_num)
  obtain ⟨V, _, _, _, ρX, π, hirrX, hπ, hπH, hVcard⟩ := exists_quotient_rep σ index_g2Derived hirr
  have hV24 : Nat.card V ≤ 2 ^ 24 :=
    calc Nat.card V ≤ Nat.card M ^ 2 := hVcard
      _ ≤ (2 ^ 12) ^ 2 := Nat.pow_le_pow_left hcard 2
      _ = 2 ^ 24 := by norm_num
  have hMV : Nat.card M ≤ Nat.card V := Nat.card_le_card_of_surjective π hπ
  have : Nontrivial V := hπ.nontrivial
  let ρ : Representation (ZMod 2) ↥(cayleyGroup (ZMod 2)) V :=
    ρX.comp cayEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = ρX (cayEquiv g) v := fun _ _ => rfl
  have hirrρ : Representation.IsIrreducible (k := ZMod 2) (G := ↥(cayleyGroup (ZMod 2)))
      (V := V) ρ := by
    refine (isIrreducible_iff (k := ZMod 2) (G := ↥(cayleyGroup (ZMod 2)))
      (V := V) ρ).mpr
      ⟨inferInstance, fun U hU => hirrX U fun γ u hu => ?_⟩
    have h1 := hU (cayEquiv.symm γ) u hu
    rwa [hρ, MulEquiv.apply_symm_apply] at h1
  have : Fact (Representation.IsIrreducible (k := ZMod 2) (G := ↥(cayleyGroup (ZMod 2)))
      (V := V) ρ) := ⟨hirrρ⟩
  have hntρ : ∃ g, ρ g ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨h, hh⟩ := hnt
    apply hh
    refine LinearMap.ext fun m => ?_
    obtain ⟨v, rfl⟩ := hπ m
    have h1 : ρ (cayEquiv.symm h) v = v := by
      rw [hall]
      rfl
    rw [hρ, MulEquiv.apply_symm_apply] at h1
    rw [← hπH h v, h1]
    rfl
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨d, hDcard⟩ : ∃ d, Nat.card (EndRing ρ) = 2 ^ d :=
    ⟨Module.finrank (ZMod 2) (EndRing ρ), by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ), Nat.card_zmod]⟩
  have hK2 : Fintype.card (ZMod 2) = 2 ^ 1 := by rw [ZMod.card, pow_one]
  let b : Module.Basis (Fin (Module.finrank (EndRing ρ) V)) (EndRing ρ) V :=
    Module.finBasisOfFinrankEq (EndRing ρ) V rfl
  obtain ⟨lab, ⟨Φ⟩, hdim⟩ :=
    B42G2F.exists_label hK2 b (algebraMap (ZMod 2) (EndRing ρ)) (RingHom.id (EndRing ρ))
  have hne := B42G2F.exists_ne_one_of_equiv b (algebraMap (ZMod 2) (EndRing ρ))
    (RingHom.id (EndRing ρ)) lab Φ hntρ
  rw [Fin.prod_univ_one] at hdim
  have hVcard' : Nat.card V = 2 ^ (d * Module.finrank (EndRing ρ) V) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, ← pow_mul]
  cases hl : lab 0 with
  | one =>
    exfalso
    obtain ⟨j, hj⟩ := hne
    rw [Subsingleton.elim j 0, hl] at hj
    exact hj rfl
  | nat =>
    have h6 : Module.finrank (EndRing ρ) V = 6 := by
      rw [hdim, hl]
      rfl
    obtain ⟨φ, -⟩ := B42G2F.exists_natural_of_six hK2 hDcard (one_dvd d) h6
    have h64 : Nat.card V = 2 ^ 6 := by
      rw [Nat.card_congr φ.toEquiv, Vol2.Ch11.G2Q8.card_Q, Nat.card_zmod]
    omega
  | lie =>
    exfalso
    have h14 : Module.finrank (EndRing ρ) V = 14 := by
      rw [hdim, hl]
      rfl
    have hd : d = 1 := by
      rw [hVcard', h14] at hV24
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hV24
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with rfl | h
        · have h1 : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
          have h2 := Finite.one_lt_card_iff_nontrivial.mpr
            (inferInstance : Nontrivial (EndRing ρ))
          omega
        · exact h
      omega
    rw [hd] at hDcard
    obtain ⟨θ, hθ⟩ := exists_lie_of_fourteen hK2 h14 hDcard
    have hY : ∀ w : FreeGroup (Fin 2), ∀ y ∈ LinearMap.ker π,
        ρ (FreeGroup.lift ![g2a, g2b] w) y ∈ LinearMap.ker π := by
      intro w y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hρ, show cayEquiv (FreeGroup.lift ![g2a, g2b] w) =
        ((⟨_, cayEquiv_lift_mem w⟩ : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2))) from rfl,
        hπH, hy, map_zero]
    rcases eq_bot_or_eq_top_of_lie θ hθ (LinearMap.ker π) hY with h | h
    ·
      have hinj : Function.Injective π := LinearMap.ker_eq_bot.mp h
      have h1 := Nat.card_le_card_of_injective π hinj
      rw [hVcard', h14, hd] at h1
      omega
    ·
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      obtain ⟨v, rfl⟩ := hπ m
      exact hm (LinearMap.mem_ker.mp (h ▸ Submodule.mem_top))
  | st =>
    exfalso
    have h64 : Module.finrank (EndRing ρ) V = 64 := by
      rw [hdim, hl]
      exact card_SIdx
    rw [hVcard', h64] at hV24
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hV24
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · have h1 : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
        have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
        omega
      · exact h
    nlinarith

end Main

end CFSG.Quasithin.B45U33
