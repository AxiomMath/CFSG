module

public import CFSG.RankThree.PartOne.SEITZU49.Pair
public import CFSG.RankThree.PartOne.SEITZU49.Stmt

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Shape

open Matrix CFSG CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCEvenUnitaryFive
  CFSG.RankThree.PartOne.CTP
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr SUid SUid_eq_statedSU)
open CFSG.RankThree.PartOne.CTP.U5Heis
open CFSG.RankThree.PartOne.SEITZU49
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem closure_fixUnion_of_shape49 [Finite K] [CharP K 2] (hq3 : 3 < 2 ^ f)
    (h5 : 5 ∣ 2 ^ f + 1)
    (hgen : ∀ (z : K) (hz : unitaryInvolution K 2 f z * z = 1),
      (¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = z) →
      ∀ M : Subgroup (SUid (unitaryInvolution K 2 f) 5),
        GenHyp (unitaryInvolution K 2 f) z hz M → M = ⊤)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAel : IsElementaryAbelian 5 A)
    (hnab : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x)
    (hshape : ∃ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A ∧
      ∀ z ∈ (primeFormConjHom h (idGram K 5)).ker, x ^ 5 ≠ z ^ 5) :
    Subgroup.closure {k : primeFormP h (idGram K 5) |
      ∃ F : Subgroup (MulAut (primeFormP h (idGram K 5))), F ≤ A ∧ F ≠ ⊥ ∧
        ∀ φ ∈ F, φ k = k} = ⊤ := by
  classical
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hσi := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := 2) (f := f) hK
  have h2 : (2 : K) = 0 := U5Gen.two_eq_zero
  obtain ⟨e, g, ζ, zz, heA, hgA, hE5, hG5, hzzn, hzznf, hζ5, hζ1, hEF⟩ :=
    Pair.exists_heis_pair49 hq3 h5 hK hAel hnab hshape
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  have hEc := conjTr_mul_of_mem h e.2
  have hFc := conjTr_mul_of_mem h g.2
  obtain ⟨P, lam, hPP, hlam5, hEP, hFP⟩ := Frame.exists_frame_z (unitaryInvolution K 2 f) hσi h2
    (fun x hx => norm_one_of_pow_five h5 hx) hζ5 hζ1 hEc hFc hE5 hG5 hEF
  set Pu := unitaryOfMatrix h P hPP with hPu
  set D₀ : primeFormUnitary h (idGram K 5) := Pu⁻¹ * e * Pu with hD₀
  set S₀ : primeFormUnitary h (idGram K 5) := Pu⁻¹ * g * Pu with hS₀
  have hD₀mat : ((D₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal (fun j : Fin 5 => lam * ζ ^ (j : ℕ)) := by
    simp only [hD₀, Subgroup.coe_mul, Units.val_mul, hPu, coe_unitaryOfMatrix_inv,
      coe_unitaryOfMatrix]
    rw [Matrix.mul_assoc, hEP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hS₀mat : ((S₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = shiftZ zz := by
    simp only [hS₀, Subgroup.coe_mul, Units.val_mul, hPu, coe_unitaryOfMatrix_inv,
      coe_unitaryOfMatrix]
    rw [Matrix.mul_assoc, hFP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hG : conjTr (unitaryInvolution K 2 f) (shiftZ zz) * shiftZ zz = 1 :=
    Circ.conjTr_shiftZ_mul _ zz hzzn
  have hS₀eq : S₀ = unitaryOfMatrix h (shiftZ zz) hG := by
    apply Subtype.ext
    apply Units.ext
    rw [hS₀mat]
    rfl
  have hS₀inv : ((((S₀⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K)) :
      Matrix (Fin 5) (Fin 5) K) = conjTr (unitaryInvolution K 2 f) (shiftZ zz) := by
    rw [hS₀eq]
    rfl
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have hc : IsMulCommutative A := hAel.toIsMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  set γ0 : MulAut (primeFormP h (idGram K 5)) := (ρ Pu)⁻¹ with hγ0
  have hconj : ∀ x : primeFormUnitary h (idGram K 5),
      ρ (Pu⁻¹ * x * Pu) = (MulAut.conj γ0) (ρ x) := by
    intro x
    rw [map_mul, map_mul, map_inv, MulAut.conj_apply, hγ0, inv_inv]
  set A' := A.map (MulAut.conj γ0).toMonoidHom with hA'
  have hcommA' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj γ0) a * (MulAut.conj γ0) b = (MulAut.conj γ0) b * (MulAut.conj γ0) a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hnec : ¬ Commute e g := by
    intro hc
    have hmat : ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
      congrArg (fun m : primeFormUnitary h (idGram K 5) =>
        ((m : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hc.eq
    have h3 : ζ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) =
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((e : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
      rw [← hEF]; exact hmat
    exact hζ1 (eq_one_of_smul_eq ((g : GL (Fin 5) K) * (e : GL (Fin 5) K)) (by
      simpa only [Units.val_mul] using h3))
  have hρe1 : ρ e ≠ 1 := fun h1 =>
    hnec (commute_of_mem_ker h hq3 (MonoidHom.mem_ker.mpr h1) g)
  have hρg1 : ρ g ≠ 1 := fun h1 =>
    hnec (commute_of_mem_ker h hq3 (MonoidHom.mem_ker.mpr h1) e).symm
  let Sx : Set (primeFormUnitary h (idGram K 5)) := {x | ρ x ∈ A' ∧ ρ x ≠ 1}
  have hD₀Sx : D₀ ∈ Sx := by
    refine ⟨⟨ρ e, heA, (hconj e).symm⟩, ?_⟩
    rw [hD₀, hconj]
    exact fun h1 => hρe1 ((map_eq_one_iff _ (MulAut.conj γ0).injective).mp h1)
  have hS₀Sx : S₀ ∈ Sx := by
    refine ⟨⟨ρ g, hgA, (hconj g).symm⟩, ?_⟩
    rw [hS₀, hconj]
    exact fun h1 => hρg1 ((map_eq_one_iff _ (MulAut.conj γ0).injective).mp h1)
  have hstab : ∀ x ∈ Sx, S₀ * x * S₀⁻¹ ∈ Sx := by
    intro x hx
    have h1 : ρ (S₀ * x * S₀⁻¹) = ρ x := by
      rw [map_mul, map_mul, map_inv, hcommA' _ hS₀Sx.1 _ hx.1]
      group
    exact ⟨by rw [h1]; exact hx.1, by rw [h1]; exact hx.2⟩
  let 𝒢 : Set (SUid (unitaryInvolution K 2 f) 5) := {g | ∃ x ∈ Sx,
    ((g : GL (Fin 5) K)) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)}
  set M₀ : Subgroup (SUid (unitaryInvolution K 2 f) 5) := Subgroup.closure 𝒢 with hM₀
  have hD : ∀ (t : Fin 5 → K) (ht : ∀ i, unitaryInvolution K 2 f (t i) * t i = 1)
      (hdet : ∏ i, t i = 1), U5Gen.dgSU (unitaryInvolution K 2 f) t ht hdet ∈ M₀ := by
    intro t ht hdet
    refine Subgroup.subset_closure ⟨D₀, hD₀Sx, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD₀mat]
    show Matrix.diagonal t * _ = _ * Matrix.diagonal t
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hC : ∀ g : SUid (unitaryInvolution K 2 f) 5,
      U5Gen.mat (unitaryInvolution K 2 f) g * shiftZ zz =
        shiftZ zz * U5Gen.mat (unitaryInvolution K 2 f) g → g ∈ M₀ := by
    intro g hg
    refine Subgroup.subset_closure ⟨S₀, hS₀Sx, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hS₀mat]
    exact hg
  have hconjGL : ∀ y : SUid (unitaryInvolution K 2 f) 5,
      ((Eich.conjU (unitaryInvolution K 2 f) (shiftZ zz) hG y : SUid (unitaryInvolution K 2 f) 5) :
        GL (Fin 5) K) = (S₀ : GL (Fin 5) K) * (y : GL (Fin 5) K) * (S₀ : GL (Fin 5) K)⁻¹ := by
    intro y
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hinv : (((S₀ : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        conjTr (unitaryInvolution K 2 f) (shiftZ zz) := hS₀inv
    rw [hinv, hS₀mat]
    rfl
  have hS : ∀ x ∈ M₀, Eich.conjU (unitaryInvolution K 2 f) (shiftZ zz) hG x ∈ M₀ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z, hz, hyz⟩ := hy
      refine Subgroup.subset_closure ⟨S₀ * z * S₀⁻¹, hstab z hz, ?_⟩
      rw [hconjGL]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (S₀ : GL (Fin 5) K) * (y : GL (Fin 5) K) * (S₀ : GL (Fin 5) K)⁻¹ *
            ((S₀ : GL (Fin 5) K) * (z : GL (Fin 5) K) * (S₀ : GL (Fin 5) K)⁻¹)
          = (S₀ : GL (Fin 5) K) * ((y : GL (Fin 5) K) * (z : GL (Fin 5) K)) *
            (S₀ : GL (Fin 5) K)⁻¹ := by group
        _ = (S₀ : GL (Fin 5) K) * ((z : GL (Fin 5) K) * (y : GL (Fin 5) K)) *
            (S₀ : GL (Fin 5) K)⁻¹ := by rw [hyz]
        _ = _ := by group
    | one => rw [Eich.conjU_one]; exact M₀.one_mem
    | mul a b _ _ ha hb =>
      rw [Eich.conjU_mul]
      exact M₀.mul_mem ha hb
    | inv a _ ha =>
      have : Eich.conjU (unitaryInvolution K 2 f) (shiftZ zz) hG a⁻¹ =
          (Eich.conjU (unitaryInvolution K 2 f) (shiftZ zz) hG a)⁻¹ :=
        map_inv (Eich.conjUHom (unitaryInvolution K 2 f) (shiftZ zz) hG) a
      rw [this]
      exact M₀.inv_mem ha
  have hM : M₀ = ⊤ := hgen zz hzzn (fun ⟨u, hu, hu5⟩ => hzznf u hu hu5) M₀ ⟨hD, hC, hS⟩
  have hmain : Subgroup.closure {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
      (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)} = ⊤ := by
    let ε : Su K 2 f 5 ≃* unitarySU 2 f K 5 := MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)
    have himg : (ε.toMonoidHom '' 𝒢) = {g : unitarySU 2 f K 5 | ∃ x ∈ Sx,
        (g : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (g : GL (Fin 5) K)} := by
      ext g'
      constructor
      · rintro ⟨g, ⟨x, hx, hgx⟩, rfl⟩
        exact ⟨x, hx, hgx⟩
      · rintro ⟨x, hx, hgx⟩
        have hεs : ((ε.symm g' : SUid (unitaryInvolution K 2 f) 5) : GL (Fin 5) K) =
            (g' : GL (Fin 5) K) := rfl
        exact ⟨ε.symm g', ⟨x, hx, by rw [hεs]; exact hgx⟩, by simp⟩
    rw [← himg, ← MonoidHom.map_closure, ← hM₀, hM, Subgroup.map_top_of_surjective _ ε.surjective]
  exact closure_fixUnion_of_centralizers h γ0 A Sx (fun x hx => hx) hmain

end Main

end CFSG.RankThree.PartOne.SEITZU49.Shape
