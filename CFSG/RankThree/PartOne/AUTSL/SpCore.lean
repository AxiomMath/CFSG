module

public import CFSG.RankThree.PartOne.AUTSL.SpParabolic
public import CFSG.RankThree.PartOne.AUTSL.SemilinearGen
public import CFSG.RankThree.PartOne.AUTSL.StableGen
public import CFSG.RankThree.PartOne.AUTSL.DiagGen
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.AUTSL.GramRel
public import CFSG.RankThree.PartOne.AUTSL.SpDiag

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank Matrix


section Main

theorem sp_core {K : Type} [Field K] [Finite K] [CharP K 2]
    {S : Subgroup (StatedSp 3 K)} (hS : IsPGroup 2 S)
    (𝒲 : Set (Submodule K (Fin 3 ⊕ Fin 3 → K)))
    (hJ : ∀ y : StatedSp 3 K, y ∈ Subgroup.normalizer (S : Set (StatedSp 3 K)) ↔
      ∀ W ∈ 𝒲, ∀ w ∈ W,
        ((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ w ∈ W)
    {E B : Subgroup (StatedSp 3 K)} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hBE : B ≤ E)
    (hBJ : B ≤ Subgroup.normalizer (S : Set (StatedSp 3 K))) (hB : Nat.card B = 25)
    (α : MulAut (StatedSp 3 K)) (hαB : B.map α.toMonoidHom = B)
    (hα3 : ∀ b ∈ B, (α ^ 3) b = b) (hα1 : ∃ b ∈ B, α b ≠ b)
    (x : MulAut (StatedSp 3 K)) (hxB : ∀ b ∈ B, b⁻¹ * x b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set (StatedSp 3 K)) ∧ ∀ e ∈ E, e⁻¹ * x e ∈ S := by
  classical
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  let _ : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b => Subtype.ext (hEc a (hBE a.2) b (hBE b.2)) }
  have hE5' : ∀ e : E, e ^ 5 = 1 := fun e => Subtype.ext (by simpa using hE5 e e.2)
  have hB5' : ∀ b : B, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hE5 b (hBE b.2))
  obtain ⟨K', hF', hAlg, hFin, hChar, ζ, hζ⟩ := exists_finite_extension_five K
  let ρG : StatedSp 3 K →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    (Units.coeHom _).comp (StatedSp 3 K).subtype
  let ρ' : E →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K' :=
    (RingHom.mapMatrix (algebraMap K K')).toMonoidHom.comp (ρG.comp E.subtype)
  obtain ⟨P, f, hD'⟩ := exists_characters_gen hζ hE5' ρ'
  have hD : ∀ g : E, (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
      (ρG (g : StatedSp 3 K)).map (algebraMap K K') *
      ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') =
      Matrix.diagonal fun i => ((f i g : K'ˣ) : K') := fun g => hD' g
  have hPPi : (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
      ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') = 1 :=
    Units.mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
      (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') = 1 := Units.inv_mul P
  have hconjinj : ∀ X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K',
      (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') * X *
        ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') =
      (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') * Y *
        ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') →
      X = Y := fun X Y h => by
    calc X = (((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
          (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) * X *
          (((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
            (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) := by rw [hPiP, one_mul, mul_one]
      _ = ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
          ((P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') * X *
            ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) *
          (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') := by noncomm_ring
      _ = ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
          ((P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') * Y *
            ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) *
          (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') := by rw [h]
      _ = Y := by
        calc _ = (((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
              (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) * Y *
              (((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
                (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) := by noncomm_ring
          _ = Y := by rw [hPiP, one_mul, mul_one]
  have hmapinj : ∀ X Y : StatedSp 3 K,
      (ρG X).map (algebraMap K K') = (ρG Y).map (algebraMap K K') → X = Y := fun X Y h =>
    Subtype.ext (Units.ext (Matrix.map_injective (algebraMap K K').injective h))
  have hfaithE : ∀ g : E, (∀ i, f i g = 1) → g = 1 := fun g hg => by
    have h1 := hD g
    have h2 : (Matrix.diagonal fun i => ((f i g : K'ˣ) : K')) = 1 := by
      have : (fun i => ((f i g : K'ˣ) : K')) = fun _ => 1 := funext fun i => by rw [hg i]; rfl
      rw [this]
      exact Matrix.diagonal_one
    rw [h2] at h1
    have h3 := hconjinj _ 1 (by rw [h1, mul_one, hPPi])
    have h5 : (ρG (g : StatedSp 3 K)).map (algebraMap K K') = (ρG 1).map (algebraMap K K') := by
      rw [h3, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (hmapinj _ _ h5)
  let ιB : B →* E := Subgroup.inclusion hBE
  have hfaithB : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1 := fun b hb =>
    Subgroup.inclusion_injective hBE (by rw [hfaithE (ιB b) hb, map_one])
  have hαB' : ∀ b : B, α b ∈ B := fun b => by
    have : α b ∈ B.map α.toMonoidHom := ⟨b, b.2, rfl⟩
    rwa [hαB] at this
  have hαBinv : ∀ b : B, α⁻¹ b ∈ B := fun b => by
    have hb : (b : StatedSp 3 K) ∈ B.map α.toMonoidHom := by
      rw [hαB]
      exact b.2
    obtain ⟨c, hc, hcb⟩ := hb
    have : α⁻¹ b = c := by
      rw [← hcb]
      simp
    rw [this]
    exact hc
  let θ : MulAut B :=
    { toFun := fun b => ⟨α b, hαB' b⟩
      invFun := fun b => ⟨α⁻¹ b, hαBinv b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hθval : ∀ b : B, ((θ b : B) : StatedSp 3 K) = α b := fun b => rfl
  have hθ3 : θ ^ 3 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have h1 := hα3 b b.2
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1 ⊢
    simpa [hθval] using h1
  have hθ1 : θ ≠ 1 := by
    intro h
    obtain ⟨b, hb, hne⟩ := hα1
    apply hne
    have := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : StatedSp 3 K)) h
    simpa [hθval] using this
  have hnorm : ∀ b, b * θ b * θ (θ b) = 1 := norm_eq_one_of_order_three hB θ hθ3 hθ1
  let J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := Matrix.fromBlocks 0 1 (-1) 0
  let J' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K' := J.map (algebraMap K K')
  let Pi : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K' :=
    ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')
  let Q : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K' := Piᵀ * J' * Pi
  have hJJ : J * J = -1 := by
    simp only [J, Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hJu : IsUnit J := by
    have h1 : J * (-J) = 1 := by rw [Matrix.mul_neg, hJJ, neg_neg]
    exact ⟨⟨J, -J, h1, mul_eq_one_comm.1 h1⟩, rfl⟩
  have hJ'u : IsUnit J' := by
    have := hJu.map (RingHom.mapMatrix (algebraMap K K')).toMonoidHom
    exact this
  have hPiu : IsUnit Pi := (P⁻¹).isUnit
  have hPiTu : IsUnit Piᵀ := by
    have h1 : Piᵀ * (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPPi, Matrix.transpose_one]
    have h2 : (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')ᵀ * Piᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
    exact ⟨⟨Piᵀ, (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')ᵀ, h1, h2⟩, rfl⟩
  have hQ : IsUnit Q := (hPiTu.mul hJ'u).mul hPiu
  have hQE : ∀ g : E, Q * diagOf f g =
      Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) * Q := fun g => by
    have hg := SymplecticTorusWeyl.mem_statedSp_iff.mp (g : StatedSp 3 K).2
    have hg' : ((ρG (g : StatedSp 3 K))ᵀ * J * ρG (g : StatedSp 3 K)).map (algebraMap K K') =
        J.map (algebraMap K K') := by
      have : (ρG (g : StatedSp 3 K))ᵀ * J * ρG (g : StatedSp 3 K) = J := hg
      rw [this]
    have hG' : ((ρG (g : StatedSp 3 K)).map (algebraMap K K'))ᵀ * J' *
        (ρG (g : StatedSp 3 K)).map (algebraMap K K') = J' := by
      rw [← Matrix.transpose_map]
      simpa only [Matrix.map_mul] using hg'
    have h1 := gram_rel J' ((ρG (g : StatedSp 3 K)).map (algebraMap K K'))
      (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') Pi hPPi hPiP hG'
      (fun i => ((f i g : K'ˣ) : K')) (hD g)
    exact gram_rel_inv Q (fun i => f i g) h1
  have hQrel : ∀ b : B, Q * diagOf f (ιB b) =
      Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K'))⁻¹) * Q := fun b => hQE (ιB b)
  obtain ⟨A, σ, hform⟩ := exists_matrix_form_sp (r := 3) (K := K) (le_refl 3) α
  obtain ⟨j₀, e₀, A₀, hA₀, he₀, hrel₀⟩ :=
    exists_E_relation_gen ρG E.subtype α A σ hform P f hD
  have hrelB : ∀ b : B, A₀ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e₀) ^ 2 ^ j₀) =
      diagOf f (ιB (θ b)) * A₀ := fun b => by
    refine (hrel₀ (ιB b)).symm.trans ?_
    show _ = (Matrix.diagonal fun i => ((f i (ιB (θ b)) : K'ˣ) : K')) * A₀
    rw [← hD (ιB (θ b))]
    rfl
  have hcard6 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  obtain ⟨hinj, χ₀, hχ₀, h0, hall⟩ := weights_of_relation_sp f ιB hcard6 hB hB5' hfaithB θ hθ3
    hθ1 j₀ e₀ he₀ A₀ hA₀ hrelB Q hQ hQrel
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBp : IsPGroup 5 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨s, hsS, hs⟩ := exists_conj_eq_of_sylow_trick (p := 5) (q := 2) Nat.prime_two
    (by norm_num) hS hBp hBJ x hxB
  let x' : MulAut (StatedSp 3 K) := MulAut.conj s⁻¹ * x
  have hx'B : ∀ b ∈ B, x' b = b := fun b hb => by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply, hs b hb]
    group
  obtain ⟨A', σ', hform'⟩ := exists_matrix_form_sp (r := 3) (K := K) (le_refl 3) x'
  obtain ⟨l, e', A₁, hA₁, he', hrel₁⟩ :=
    exists_E_relation_gen ρG E.subtype x' A' σ' hform' P f hD
  have hrelB' : ∀ b : B, A₁ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A₁ := fun b => by
    refine (hrel₁ (ιB b)).symm.trans ?_
    show _ = (Matrix.diagonal fun i => ((f i (ιB b) : K'ˣ) : K')) * A₁
    rw [← hD (ιB b)]
    have h2 : x' (E.subtype (ιB b)) = E.subtype (ιB b) := hx'B _ b.2
    rw [h2]
    rfl
  have hm : ¬ 5 ∣ e₀ * 2 ^ j₀ := not_dvd_five_mul j₀ e₀ he₀
  have hall' := fun e₁ : E => fixes_of_relation_sp f ιB hB5' hE5' θ hnorm (e₀ * 2 ^ j₀) hm hinj hχ₀
    h0 hall Q hQ hQE l e' he' A₁ hA₁ hrelB' e₁
  have hfix : ∀ g : E, x' (g : StatedSp 3 K) = g := fun g => by
    have h3 := hrel₁ g
    have h4 := hall' g
    have h5 := hD g
    have h6 : (P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
        (ρG (x' (g : StatedSp 3 K))).map (algebraMap K K') *
        ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') * A₁ =
        ((P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *
          (ρG (g : StatedSp 3 K)).map (algebraMap K K') *
          ((P⁻¹ : GL (Fin 3 ⊕ Fin 3) K') : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K')) * A₁ := by
      refine h3.trans (h4.trans ?_)
      rw [h5]
      rfl
    exact hmapinj _ _ (hconjinj _ _ ((hA₁.mul_left_inj).1 h6))
  have hEJ : ∀ g : E, (g : StatedSp 3 K) ∈
      Subgroup.normalizer (S : Set (StatedSp 3 K)) := fun g => by
    rw [hJ]
    intro W hW
    have hdesc := rho_mem_span (ρG.comp E.subtype) ιB P f hD hinj g
    let St : Submodule K (Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :=
      { carrier := {M | ∀ w ∈ W, M *ᵥ w ∈ W}
        add_mem' := fun {M N} hM hN w hw => by
          rw [Matrix.add_mulVec]
          exact W.add_mem (hM w hw) (hN w hw)
        zero_mem' := fun w hw => by simp
        smul_mem' := fun c M hM w hw => by
          rw [Matrix.smul_mulVec]
          exact W.smul_mem c (hM w hw) }
    have hle : Submodule.span K (Set.range fun b : B => (ρG.comp E.subtype) (ιB b)) ≤ St := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact (hJ _).1 (hBJ b.2) W hW
    exact hle hdesc
  refine ⟨fun g hg => hEJ ⟨g, hg⟩, fun e he => ?_⟩
  have hx'e : x' e = e := hfix ⟨e, he⟩
  have hxe : x e = s * e * s⁻¹ := by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply] at hx'e
    calc x e = s * (s⁻¹ * x e * s⁻¹⁻¹) * s⁻¹ := by group
      _ = s * e * s⁻¹ := by rw [hx'e]
  rw [hxe]
  have hsconj : e⁻¹ * s * e ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (S : Set (StatedSp 3 K))).inv_mem (hEJ ⟨e, he⟩)) s).1 hsS
    simpa using this
  have hrw : e⁻¹ * (s * e * s⁻¹) = (e⁻¹ * s * e) * s⁻¹ := by group
  rw [hrw]
  exact S.mul_mem hsconj (S.inv_mem hsS)

end Main

end CFSG.RankThree.PartOne.AUTSL
