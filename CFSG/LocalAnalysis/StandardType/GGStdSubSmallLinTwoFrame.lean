module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp

public section

namespace CFSG.StandardType.SmallL2

open Polynomial Matrix Multiplicative CoordSL CFSG CFSG.Assembly TableB
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.StandardType.LinTwoTv

variable {K : Type} [Field K] [Finite K] {d : ℕ}

structure IsFrame {L' : Type} [Group L'] {g : K[X]} [Fact (Irreducible g)] {s r : ℕ}
    (φ₀ : SpecialLinearGroup (Fin d) K →* L')
    (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin d) K)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1) (A : Subgroup (MulAut L')) : Prop where
  bij : Function.Bijective φ₀
  gd : g ∣ cyclotomic 3 K
  s3 : 3 ≤ s
  conj_inj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y
  mem_A : ∀ a : MulAut L', a ∈ A ↔
    ∃ t : Fin s → ZMod 3, a = MulAut.conj (frameHom φ₀ A₀ ε hC hCp (ofAdd t))

theorem exists_frame_for [CharP K 2] (hK : Nat.card K = 2) (hd : 6 ≤ d) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : 3 ^ (d / 2) ≤ Nat.card A) :
    ∃ (φ₀ : SpecialLinearGroup (Fin d) K →* L') (g : K[X]) (_ : Fact (Irreducible g))
      (s r : ℕ) (ε : Fin d ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : SpecialLinearGroup (Fin d) K) (hC : (rootMat g).det = 1) (hCp : rootMat g ^ 3 = 1),
      IsFrame φ₀ ε A₀ hC hCp A := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hperfSL : commutator (SpecialLinearGroup (Fin (m + 2)) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := m + 2) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  have hsec : TypeA.SLHasSections (m + 2) K := TypeA.slHasSections_of_five_le (by omega)
  obtain ⟨φ₀, hφ₀s, hφ₀⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  have hφ₀inj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply TwoThree.eq_one_of_mem_scalars hK
    rw [← proj_eq_one_iff, ← hφ₀, hg, map_one]
  let Ξ₀ : SpecialLinearGroup (Fin (m + 2)) K ≃* L' := MulEquiv.ofBijective φ₀ ⟨hφ₀inj, hφ₀s⟩
  have hconj : ∀ g s : SpecialLinearGroup (Fin (m + 2)) K,
      φ₀ (g * s * g⁻¹) = MulAut.conj (φ₀ g) (φ₀ s) := by
    intro g s
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hinner : ∀ a ∈ A, ∃ b : L', a = MulAut.conj b := by
    intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have h1 := TypeA.act_of_lift hperfSL hker hφ₀ (a := a) (g := TwoThree.toSLHom hK B)
      (by rw [TwoThree.toGL_toSLHom]; exact hφa)
    refine ⟨φ₀ (TwoThree.toSLHom hK B), ?_⟩
    ext l
    obtain ⟨s, rfl⟩ := hφ₀s l
    rw [h1 s, hconj]
  have hZ : ∀ g h : L', MulAut.conj g = MulAut.conj h → g = h := by
    intro g h hgh
    obtain ⟨z, hz⟩ : ∃ z : L', z = h⁻¹ * g := ⟨_, rfl⟩
    have hc : ∀ x : L', z * x = x * z := by
      intro x
      have h1 := congrArg (fun f : MulAut L' => f x) hgh
      simp only [MulAut.conj_apply] at h1
      rw [hz]
      calc h⁻¹ * g * x = h⁻¹ * (g * x * g⁻¹) * g := by group
        _ = h⁻¹ * (h * x * h⁻¹) * g := by rw [h1]
        _ = x * (h⁻¹ * g) := by group
    have hs : Ξ₀.symm z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Ξ₀.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hc (Ξ₀ s)).symm
    rw [StandardType.LineL2.center_eq_bot_two hK, Subgroup.mem_bot] at hs
    have h2 : h⁻¹ * g = 1 := by
      have := congrArg Ξ₀ hs
      rw [← hz]
      simpa using this
    exact (inv_mul_eq_one.mp h2).symm
  have hinj : Function.Injective (MulAut.conj : L' →* MulAut L') := fun g h hgh => hZ g h hgh
  set E : Subgroup L' := A.comap (MulAut.conj : L' →* MulAut L') with hE
  have hmemE : ∀ b, b ∈ E ↔ MulAut.conj b ∈ A := fun b => Iff.rfl
  have hAE : ∀ a, a ∈ A ↔ ∃ b ∈ E, a = MulAut.conj b := by
    intro a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hinner a ha
      exact ⟨b, (hmemE b).mpr (hb ▸ ha), hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact (hmemE b).mp hb
  have hEel : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA a.2 b.2
    · rw [map_pow, map_one]
      exact hA.2 _ hx
  have hcardE : Nat.card E = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective (fun b : E => (⟨MulAut.conj b, b.2⟩ : A))
      ⟨?_, ?_⟩)
    · intro b b' h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb, rfl⟩ := (hAE a).mp ha
      exact ⟨⟨b, hb⟩, rfl⟩
  have hchar : CharP K 2 := inferInstance
  have hp3 : ((3 : ℕ) : K) ≠ 0 :=
    TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
  obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three K
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hnsplit : ¬ 3 ∣ Nat.card K - 1 := by rw [hK]; decide
  have hC : (rootMat g).det = 1 := det_rootMat Nat.prime_three hnsplit hp3 hgd
  have hCp : rootMat g ^ 3 = 1 := rootMat_pow_eq_one Nat.prime_three hp3 hgd
  have hunit : ∀ j : ℕ, ¬ 3 ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) := fun j hj c =>
    isUnit_rootMat_pow_sub Nat.prime_three hnsplit hp3 hgd j hj c
  have he2 : 2 ≤ (rootPB g).dim := two_le_rootPB_dim (fun c => hunit 1 (by decide) c)
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g Nat.prime_three hp3 hgd
    (Set.range fun x : E =>
      ((Ξ₀.symm (x : L') : SpecialLinearGroup (Fin (m + 2)) K) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h := congrArg (fun z : SpecialLinearGroup (Fin (m + 2)) K =>
        (z : Matrix (Fin (m + 2)) (Fin (m + 2)) K))
        (congrArg Ξ₀.symm (TableB.IsElemAbelian.comm hEel x.2 y.2))
      simpa [Commute, SemiconjBy, map_mul] using h)
    (by
      rintro _ ⟨x, rfl⟩
      have h1 : (Ξ₀.symm (x : L')) ^ 3 = 1 := by
        rw [← map_pow, hEel.2 (x : L') x.2, map_one]
      rw [← Matrix.SpecialLinearGroup.coe_pow, h1, Matrix.SpecialLinearGroup.coe_one])
  have hker₀ : φ₀.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [hφ₀inj (hx.trans (map_one φ₀).symm)]
    exact Subgroup.one_mem _
  set ι := frameHom φ₀ A₀ ε hC hCp with hι
  have hιinj : Function.Injective ι :=
    frameHom_injective φ₀ A₀ ε hC hCp hker₀ (rootPB_dim_pos g) hunit
  have hEle : E ≤ ι.range := by
    intro b hb
    obtain ⟨k, hk⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨ofAdd fun i => (k i : ZMod 3), ?_⟩
    rw [hι, frameHom_natCast, SLRep.ggFrame_apply]
    have hx : Ξ₀.symm b = A₀ * SLNS.nsSL ε hC k * A₀⁻¹ := by
      have h1 : Ξ₀.symm b * A₀ = A₀ * SLNS.nsSL ε hC k := Subtype.ext hk
      rw [← h1, mul_inv_cancel_right]
    have : b = Ξ₀ (Ξ₀.symm b) := (MulEquiv.apply_symm_apply Ξ₀ b).symm
    rw [this, hx]
    rfl
  have hcardι : Nat.card ι.range = 3 ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hsd : s ≤ (m + 2) / 2 := by
    have hcd : Fintype.card (Fin (m + 2)) = Fintype.card ((Fin (rootPB g).dim × Fin s) ⊕ Fin r) :=
      Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at hcd
    have : 2 * s ≤ m + 2 := by nlinarith
    omega
  have hEeq : E = ι.range := by
    apply Subgroup.eq_of_le_of_card_ge hEle
    rw [hcardι, hcardE]
    exact (Nat.pow_le_pow_right (by norm_num) hsd).trans hr
  have hs3 : 3 ≤ s := by
    have h1 : 3 ^ ((m + 2) / 2) ≤ 3 ^ s := by
      rw [← hcardι, ← hEeq, hcardE]
      exact hr
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  refine ⟨φ₀, g, inferInstance, s, r, ε, A₀, hC, hCp, ⟨⟨hφ₀inj, hφ₀s⟩, hgd, hs3, hZ, fun a => ?_⟩⟩
  rw [hAE a]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ ι.range := hEeq ▸ hb
    obtain ⟨x, rfl⟩ := hb'
    exact ⟨toAdd x, by rw [ofAdd_toAdd]⟩
  · rintro ⟨t, rfl⟩
    have hv : ι (ofAdd t) ∈ E := hEeq ▸ ⟨ofAdd t, rfl⟩
    exact ⟨_, hv, rfl⟩

end CFSG.StandardType.SmallL2

end
