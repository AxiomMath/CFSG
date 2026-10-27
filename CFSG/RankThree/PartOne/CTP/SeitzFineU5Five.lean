module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalPlane
public import CFSG.RankThree.PartOne.CTP.SeitzFineDefs
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalize

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCEvenUnitaryFive
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Blocks

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def conjDU (n : ℕ) (P : primeFormUnitary h (idGram K n))
    (x : primeFormUnitary h (idGram K n)) : GL (Fin n) K :=
  (P : GL (Fin n) K)⁻¹ * (x : GL (Fin n) K) * (P : GL (Fin n) K)

theorem closure_centralizers_unitarySU_of_blocksU (hq : ℓ ^ f ≠ 2) (n : ℕ)
    (P : primeFormUnitary h (idGram K (n + 1))) (Sx : Set (primeFormUnitary h (idGram K (n + 1))))
    (hblk : ∀ i : Fin n, ∃ x ∈ Sx, ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((conjDU h (n + 1) P x : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((conjDU h (n + 1) P x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) * blockMat (n + 1) i A) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ Sx,
      (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K)} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : primeFormUnitary h (idGram K (n + 1)) → GL (Fin (n + 1)) K := conjDU h (n + 1) P
  let φ := conjSU h P
  set S := Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ Sx,
      (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K)} with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1))
      (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → φ y ∈ S := by
    intro i y A hA
    obtain ⟨x, hxS, hxc⟩ := hblk i
    refine Subgroup.subset_closure ⟨x, hxS, ?_⟩
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    have hxeq : (x : GL (Fin (n + 1)) K) = Pg * Dg x * Pg⁻¹ := by
      simp only [Dg, conjDU, Pg]
      group
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        (x : GL (Fin (n + 1)) K) =
      (x : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hxeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by group
      _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * Dg x * Pg⁻¹ *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'



end Blocks

section PLevel

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem closure_fixUnion_eq_top_of_abelian_lift (h5 : 5 ∣ 2 ^ f + 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAD : A ≤ primeFormD h (idGram K 5))
    (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hab : ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  classical
  have hn : 3 ≤ 5 := by norm_num
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hq3 : 3 < 2 ^ f := by omega
  have hfinK := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  set G : Subgroup (primeFormUnitary h (idGram K 5)) := A.comap ρ with hG
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy => hab x y hx hy
  have hGpow : ∀ x ∈ G, x ^ 5 ∈ idScalarKernel h 5 := fun x hx => by
    refine (primeFormConjHom_eq_one_iff hn hq3 _).mp ?_
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian _ hx
  have hGnc : ¬ IsCyclic G := by
    intro hcyc
    let π : G →* A := (ρ.comp G.subtype).codRestrict A (fun x => x.2)
    have hπ : Function.Surjective π := by
      intro a
      obtain ⟨x, hx⟩ := hAD a.2
      exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact a.2⟩, Subtype.ext hx⟩
    have hAcyc : IsCyclic A := isCyclic_of_surjective π hπ
    have h1 := IsCyclic.exponent_eq_card (α := A)
    have h2 : Monoid.exponent A ∣ 5 := IsElementaryAbelian.exponent_dvd_p 5 A
    rw [hAcard] at h1
    rw [h1] at h2
    norm_num at h2
  obtain ⟨P, hP⟩ := exists_unitary_diagonalizing h h5 G hGcomm hGnc hGpow
  set γ0 : MulAut (primeFormP h (idGram K 5)) := (ρ P)⁻¹ with hγ0
  let φ : MulAut (MulAut (primeFormP h (idGram K 5))) := MulAut.conj γ0
  have hφρ : ∀ x : primeFormUnitary h (idGram K 5), φ (ρ x) = ρ (P⁻¹ * x * P) := by
    intro x
    change γ0 * ρ x * γ0⁻¹ = _
    rw [hγ0, map_mul, map_mul, map_inv, inv_inv]
  have hAD' : A.map φ.toMonoidHom ≤ primeFormD h (idGram K 5) := by
    rintro _ ⟨a, haA, rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAD haA
    refine ⟨P⁻¹ * x₀ * P, ?_⟩
    rw [← hφρ, hx₀]
    rfl
  have hdiag' : ∀ y : primeFormUnitary h (idGram K 5), ρ y ∈ A.map φ.toMonoidHom →
      ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag := by
    intro y hy
    obtain ⟨a, haA, hay⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x₀, hx₀⟩ := hAD haA
    have hx₀G : x₀ ∈ G := by rw [hG, Subgroup.mem_comap, hx₀]; exact haA
    have hD0 := hP x₀ hx₀G
    have hay' : φ (ρ x₀) = ρ y := by rw [hx₀]; exact hay
    rw [hφρ] at hay'
    have h1 : ρ ((P⁻¹ * x₀ * P)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hay', inv_mul_cancel]
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq3 _).mp h1
    have hy' : ((y : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
        ((P⁻¹ * x₀ * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
          GeneralLinearGroup.scalar (Fin 5) c := by
      rw [← hc, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [hy', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    intro i j hij
    rw [Matrix.mul_diagonal, hD0 hij, zero_mul]
  have hAel' : IsElementaryAbelian 5 (A.map φ.toMonoidHom) :=
    IsElementaryAbelian.map φ.toMonoidHom
  have hAcard' : Nat.card (A.map φ.toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hAcard]
  let Sx : Set (primeFormUnitary h (idGram K 5)) :=
    {x | ρ x ∈ A.map φ.toMonoidHom ∧ ρ x ≠ 1 ∧
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag}
  have hblk : ∀ i : Fin 4, ∃ x ∈ Sx, ∀ A₂ : Matrix (Fin 2) (Fin 2) K,
      blockMat (4 + 1) i A₂ * ((conjDU h (4 + 1) 1 x : GL (Fin (4 + 1)) K) :
        Matrix (Fin (4 + 1)) (Fin (4 + 1)) K) =
        ((conjDU h (4 + 1) 1 x : GL (Fin (4 + 1)) K) :
          Matrix (Fin (4 + 1)) (Fin (4 + 1)) K) * blockMat (4 + 1) i A₂ := by
    intro i
    obtain ⟨x, hxA, hx1, hxij⟩ := exists_lift_equal_entries h (A.map φ.toMonoidHom) hAD' hAel'
      hAcard' hq3 hdiag' i.castSucc i.succ
    refine ⟨x, ⟨hxA, hx1, hdiag' x hxA⟩, fun A₂ => ?_⟩
    have hxdiag := hdiag' x hxA
    have hD : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        Matrix.diagonal (fun c => ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) c c) :=
      hxdiag.diagonal_diag.symm
    have hnz : ∀ c : Fin 5, ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) c c ≠ 0 := by
      intro c
      have h1 : (((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          (((x : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) c c = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [mul_apply_diag_of_isDiag hxdiag] at h1
      exact left_ne_zero_of_mul_eq_one h1
    have hc1 : (conjDU h (4 + 1) 1 x : GL (Fin (4 + 1)) K) = (x : GL (Fin 5) K) := by
      simp [conjDU]
    rw [hc1, hD]
    exact blockMat_mul_diagonal_comm (by omega) _ hnz i.castSucc i.succ (by simp) (by simp)
      hxij A₂
  have hmain := closure_centralizers_unitarySU_of_blocksU h (by omega) 4 1 Sx hblk
  let eg : unitarySU 2 f K 5 ≃* gramSU h (idGram K 5) :=
    MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 5)
  let π' : unitarySU 2 f K 5 →* primeFormP h (idGram K 5) :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 5)) 5)).comp eg.toMonoidHom
  have hπ' : Function.Surjective π' := (QuotientGroup.mk'_surjective _).comp eg.surjective
  have hfix : ∀ (g : unitarySU 2 f K 5) (x : primeFormUnitary h (idGram K 5)), x ∈ Sx →
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K) →
      π' g ∈ {k : primeFormP h (idGram K 5) | ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))),
        F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧ ∀ ψ ∈ F, ψ k = k} := by
    intro g x hx hgx
    refine ⟨Subgroup.zpowers (ρ x), Subgroup.zpowers_le.2 hx.1, ?_, ?_⟩
    · intro hbot
      exact hx.2.1 (Subgroup.zpowers_eq_bot.1 hbot)
    · have hfix1 : ρ x (π' g) = π' g := by
        show primeFormConjHom h (idGram K 5) x
          (((eg g : gramSU h (idGram K 5)) : primeFormP h (idGram K 5))) = _
        rw [primeFormConjHom_mk]
        congr 1
        apply Subtype.ext
        show (x : GL (Fin 5) K) * (g : GL (Fin 5) K) * (x : GL (Fin 5) K)⁻¹ = (g : GL (Fin 5) K)
        rw [mul_inv_eq_iff_eq_mul]
        exact hgx.symm
      intro ψ hψ
      have hmem : ρ x ∈ MulAction.stabilizer (MulAut (primeFormP h (idGram K 5))) (π' g) := by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix1
      have := Subgroup.zpowers_le.2 hmem hψ
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
  have hle : (Subgroup.closure {g : unitarySU 2 f K (4 + 1) | ∃ x ∈ Sx,
      (g : GL (Fin (4 + 1)) K) * (x : GL (Fin (4 + 1)) K) =
        (x : GL (Fin (4 + 1)) K) * (g : GL (Fin (4 + 1)) K)}).map π' ≤
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
          ∀ ψ ∈ F, ψ k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    exact Subgroup.subset_closure (hfix g x hx hgx)
  rw [hmain, Subgroup.map_top_of_surjective π' hπ'] at hle
  have hback : ∀ k' ∈ {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k}, γ0⁻¹ k' ∈ {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k} := by
    rintro k' ⟨F', hF'A, hF'ne, hF'fix⟩
    refine ⟨F'.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨ψ', hψ', rfl⟩
      obtain ⟨a, haA, rfl⟩ := hF'A hψ'
      simpa using haA
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective]
    · rintro _ ⟨ψ', hψ', rfl⟩
      have h1 := hF'fix ψ' hψ'
      show (φ.symm ψ') (γ0⁻¹ k') = γ0⁻¹ k'
      have h2 : φ.symm ψ' = γ0⁻¹ * ψ' * γ0 := by
        change (MulAut.conj γ0).symm ψ' = _
        rw [MulAut.conj_symm_apply]
      rw [h2]
      simp [MulAut.mul_apply, h1]
  rw [eq_top_iff]
  have hle2 : (Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A.map φ.toMonoidHom ∧ F ≠ ⊥ ∧
        ∀ ψ ∈ F, ψ k = k}).map (γ0⁻¹).toMonoidHom ≤
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ ψ ∈ F, ψ k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    exact Subgroup.subset_closure (hback k' hk')
  rw [eq_top_iff.mpr hle,
    Subgroup.map_top_of_surjective (γ0⁻¹).toMonoidHom (γ0⁻¹).surjective] at hle2
  exact hle2

end PLevel

section Ledger

@[expose] def PSU5DiagNonabelianPlane : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 5 ∣ 2 ^ f + 1 →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K 5))), IsElementaryAbelian 5 A →
      Nat.card A = 5 ^ 2 → A ≤ primeFormD h (idGram K 5) →
      ¬ (∀ x y : primeFormUnitary h (idGram K 5),
        primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
          x * y = y * x) →
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤

@[expose] def PSU5DiagPlane48 : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 5 ∣ 2 ^ f + 1 →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K 5))), IsElementaryAbelian 5 A →
      Nat.card A = 5 ^ 2 → A ≤ primeFormD h (idGram K 5) →
      ¬ (∀ x y : primeFormUnitary h (idGram K 5),
        primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
          x * y = y * x) →
      (∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A →
        ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 = z ^ 5) →
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤

@[expose] def PSU5DiagPlane49 : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 5 ∣ 2 ^ f + 1 →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K 5))), IsElementaryAbelian 5 A →
      Nat.card A = 5 ^ 2 → A ≤ primeFormD h (idGram K 5) →
      ¬ (∀ x y : primeFormUnitary h (idGram K 5),
        primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
          x * y = y * x) →
      (∃ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A ∧
        ∀ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 ≠ z ^ 5) →
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤

theorem psu5DiagNonabelianPlane_of_parts (h48 : PSU5DiagPlane48) (h49 : PSU5DiagPlane49) :
    PSU5DiagNonabelianPlane := by
  intro f K _ h h5 A hAel hAcard hAD hnab
  by_cases hshape : ∀ x : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A →
        ∃ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 = z ^ 5
  · exact h48 f K h h5 A hAel hAcard hAD hnab hshape
  · push Not at hshape
    exact h49 f K h h5 A hAel hAcard hAD hnab hshape

@[expose] def PSU5FieldPlane : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 5 ∣ 2 ^ f + 1 →
    ∀ A : Subgroup (MulAut (primeFormP h (idGram K 5))), IsElementaryAbelian 5 A →
      Nat.card A = 5 ^ 2 → ¬ A ≤ primeFormD h (idGram K 5) →
      Subgroup.closure {k : primeFormP h (idGram K 5) |
        ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤

theorem closure_fixSet_of_diag (hD : PSU5DiagNonabelianPlane) {ℓ f : ℕ} (hℓ : ℓ = 2) {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 2) (hAD : A ≤ primeFormD h (idGram K 5)) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  subst hℓ
  by_cases hab : ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x
  · exact closure_fixUnion_eq_top_of_abelian_lift h h5 A hAD hAel hAcard hab
  · exact hD f K h h5 A hAel hAcard hAD hab

theorem closure_fixSet_transport {K P : Type} [Group K] [Group P] (θ : K ≃* P)
    (E : Subgroup (MulAut K))
    (h : Subgroup.closure {k' : P | ∃ F : Subgroup (MulAut P),
      F ≤ E.map (MulAut.congr θ).toMonoidHom ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k' = k'} = ⊤) :
    Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
      ∀ φ ∈ F, φ k = k} = ⊤ := by
  have hback : ∀ k' ∈ {k' : P | ∃ F : Subgroup (MulAut P),
      F ≤ E.map (MulAut.congr θ).toMonoidHom ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k' = k'},
      θ.symm k' ∈ {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k = k} := by
    rintro k' ⟨F', hF'E, hF'ne, hF'fix⟩
    refine ⟨F'.map (MulAut.congr θ).symm.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨ψ', hψ', rfl⟩
      obtain ⟨a, haE, rfl⟩ := hF'E hψ'
      show (MulAut.congr θ).symm ((MulAut.congr θ) a) ∈ E
      rw [MulEquiv.symm_apply_apply]
      exact haE
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr θ).symm.injective]
    · rintro _ ⟨ψ', hψ', rfl⟩
      have h1 := hF'fix ψ' hψ'
      show ((MulAut.congr θ).symm ψ') (θ.symm k') = θ.symm k'
      have h2 : (MulAut.congr θ).symm ψ' = MulAut.congr θ.symm ψ' := rfl
      rw [h2, MulAut.congr_apply]
      simp [h1]
  rw [eq_top_iff]
  have hle : (Subgroup.closure {k' : P | ∃ F : Subgroup (MulAut P),
      F ≤ E.map (MulAut.congr θ).toMonoidHom ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k' = k'}).map
      θ.symm.toMonoidHom ≤ Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    exact Subgroup.subset_closure (hback k' hk')
  rw [h, Subgroup.map_top_of_surjective θ.symm.toMonoidHom θ.symm.surjective] at hle
  exact hle

theorem closure_fixSet_of_field (hF : PSU5FieldPlane) {ℓ f : ℕ} (hℓ : ℓ = 2) {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 2) (hAD : ¬ A ≤ primeFormD h (idGram K 5)) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  subst hℓ
  exact hF f K h h5 A hAel hAcard hAD

theorem extSeitzAtInnerFor_twistedA_four_five (hD : PSU5DiagNonabelianPlane)
    {q : TauCeti.PrimePower} (hq : q.p = 2) (h5 : 5 ∣ q.p ^ q.exponent + 1) :
    ExtSeitzAtInnerFor (.twistedA 4 q) fun p => p = 5 := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd hpe E hE hcard hinner
  subst hpe
  left
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, -, -, -, F, _, hU, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e0)
  refine closure_fixSet_transport θ E ?_
  refine closure_fixSet_of_diag hD hq hU h5 _ (IsElementaryAbelian.map _) ?_ ?_
  · rw [Subgroup.card_map_of_injective (MulAut.congr θ).injective, hcard]
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, rfl⟩ := hinner φ hφ
    refine innU_le_primeFormD hU (n := 5) ⟨θ g, ?_⟩
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem extSeitzAtOuterFor_twistedA_four_five (hD : PSU5DiagNonabelianPlane)
    (hF : PSU5FieldPlane) {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h5 : 5 ∣ q.p ^ q.exponent + 1) :
    ExtSeitzAtOuterFor (.twistedA 4 q) fun p => p = 5 := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd hpe E hE hcard _hout
  subst hpe
  left
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, -, -, -, F, _, hU, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e0)
  refine closure_fixSet_transport θ E ?_
  have hAel : IsElementaryAbelian 5 (E.map (MulAut.congr θ).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hAcard : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr θ).injective, hcard]
  by_cases hAD : E.map (MulAut.congr θ).toMonoidHom ≤ primeFormD hU (idGram F 5)
  · exact closure_fixSet_of_diag hD hq hU h5 _ hAel hAcard hAD
  · exact closure_fixSet_of_field hF hq hU h5 _ hAel hAcard hAD

end Ledger

end CFSG.RankThree.PartOne.CTP
