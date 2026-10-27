module

public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJLinearCubeAutomizer
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityEigenspace
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.Mathlib.RingTheory.RootsOfUnity.ZModUnits
public import Mathlib.Algebra.Group.TypeTags.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TypeA.PGLTor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}
  {G : Subgroup (GL ι K)} [Nonempty ι]

theorem commChar_mul_left (hG : IsProjElem p G) {a₁ a₂ : GL ι K} (h₁ : a₁ ∈ G)
    (h₂ : a₂ ∈ G) (x : G) :
    commChar hG (mul_mem h₁ h₂) x = commChar hG h₁ x * commChar hG h₂ x := by
  set u₁ := commChar hG h₁ x
  set u₂ := commChar hG h₂ x
  have h1 := commChar_spec hG h₁ x
  have h2 := commChar_spec hG h₂ x
  have hmain : a₁ * a₂ * (x : GL ι K) =
      GeneralLinearGroup.scalar ι (u₁ * u₂) * ((x : GL ι K) * (a₁ * a₂)) := by
    calc a₁ * a₂ * (x : GL ι K) = a₁ * (a₂ * (x : GL ι K)) := by group
      _ = a₁ * (GeneralLinearGroup.scalar ι u₂ * ((x : GL ι K) * a₂)) := by rw [h2]
      _ = (a₁ * GeneralLinearGroup.scalar ι u₂) * ((x : GL ι K) * a₂) := by group
      _ = (GeneralLinearGroup.scalar ι u₂ * a₁) * ((x : GL ι K) * a₂) := by
          rw [(scalar_mul_comm u₂ a₁).symm]
      _ = GeneralLinearGroup.scalar ι u₂ * (a₁ * ((x : GL ι K) * a₂)) := by group
      _ = GeneralLinearGroup.scalar ι u₂ * ((a₁ * (x : GL ι K)) * a₂) := by group
      _ = GeneralLinearGroup.scalar ι u₂ *
            ((GeneralLinearGroup.scalar ι u₁ * ((x : GL ι K) * a₁)) * a₂) := by rw [h1]
      _ = GeneralLinearGroup.scalar ι u₂ *
            (GeneralLinearGroup.scalar ι u₁ * ((x : GL ι K) * a₁ * a₂)) := by group
      _ = (GeneralLinearGroup.scalar ι u₂ * GeneralLinearGroup.scalar ι u₁) *
            ((x : GL ι K) * a₁ * a₂) := by group
      _ = GeneralLinearGroup.scalar ι (u₂ * u₁) * ((x : GL ι K) * a₁ * a₂) := by
          rw [← map_mul]
      _ = GeneralLinearGroup.scalar ι (u₁ * u₂) * ((x : GL ι K) * (a₁ * a₂)) := by
          rw [mul_comm u₂ u₁]; group
  exact commChar_eq hG (mul_mem h₁ h₂) hmain

theorem commChar_self (hG : IsProjElem p G) (a : G) : commChar hG a.2 a = 1 := by
  have hmain : (a : GL ι K) * (a : GL ι K) =
      GeneralLinearGroup.scalar ι 1 * ((a : GL ι K) * (a : GL ι K)) := by
    rw [map_one, one_mul]
  exact commChar_eq hG a.2 hmain

theorem commChar_eq_of_eq_scalar_mul (hG : IsProjElem p G) {a a' : GL ι K} (ha : a ∈ G)
    (ha' : a' ∈ G) {z : Kˣ} (h : a' = GeneralLinearGroup.scalar ι z * a) (x : G) :
    commChar hG ha' x = commChar hG ha x := by
  set u := commChar hG ha x
  have hspec := commChar_spec hG ha x
  have hmain : a' * (x : GL ι K) =
      GeneralLinearGroup.scalar ι u * ((x : GL ι K) * a') := by
    calc a' * (x : GL ι K) = (GeneralLinearGroup.scalar ι z * a) * (x : GL ι K) := by rw [h]
      _ = GeneralLinearGroup.scalar ι z * (a * (x : GL ι K)) := by group
      _ = GeneralLinearGroup.scalar ι z *
            (GeneralLinearGroup.scalar ι u * ((x : GL ι K) * a)) := by rw [hspec]
      _ = (GeneralLinearGroup.scalar ι z * GeneralLinearGroup.scalar ι u) *
            ((x : GL ι K) * a) := by group
      _ = GeneralLinearGroup.scalar ι (z * u) * ((x : GL ι K) * a) := by rw [← map_mul]
      _ = GeneralLinearGroup.scalar ι (u * z) * ((x : GL ι K) * a) := by rw [mul_comm z u]
      _ = (GeneralLinearGroup.scalar ι u * GeneralLinearGroup.scalar ι z) *
            ((x : GL ι K) * a) := by rw [← map_mul]
      _ = GeneralLinearGroup.scalar ι u *
            (GeneralLinearGroup.scalar ι z * ((x : GL ι K) * a)) := by group
      _ = GeneralLinearGroup.scalar ι u *
            ((GeneralLinearGroup.scalar ι z * (x : GL ι K)) * a) := by group
      _ = GeneralLinearGroup.scalar ι u *
            (((x : GL ι K) * GeneralLinearGroup.scalar ι z) * a) := by
          rw [scalar_mul_comm z (x : GL ι K)]
      _ = GeneralLinearGroup.scalar ι u *
            ((x : GL ι K) * (GeneralLinearGroup.scalar ι z * a)) := by group
      _ = GeneralLinearGroup.scalar ι u * ((x : GL ι K) * a') := by rw [h]
  exact commChar_eq hG ha' hmain

theorem commChar_eq_of_eq_scalar_mul_arg (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G)
    {x x' : G} {z : Kˣ} (h : (x' : GL ι K) = GeneralLinearGroup.scalar ι z * (x : GL ι K)) :
    commChar hG ha x' = commChar hG ha x := by
  set u := commChar hG ha x
  have hspec := commChar_spec hG ha x
  have hmain : a * (x' : GL ι K) =
      GeneralLinearGroup.scalar ι u * ((x' : GL ι K) * a) := by
    calc a * (x' : GL ι K) = a * (GeneralLinearGroup.scalar ι z * (x : GL ι K)) := by rw [h]
      _ = (a * GeneralLinearGroup.scalar ι z) * (x : GL ι K) := by group
      _ = (GeneralLinearGroup.scalar ι z * a) * (x : GL ι K) := by
          rw [(scalar_mul_comm z a).symm]
      _ = GeneralLinearGroup.scalar ι z * (a * (x : GL ι K)) := by group
      _ = GeneralLinearGroup.scalar ι z *
            (GeneralLinearGroup.scalar ι u * ((x : GL ι K) * a)) := by rw [hspec]
      _ = (GeneralLinearGroup.scalar ι z * GeneralLinearGroup.scalar ι u) *
            ((x : GL ι K) * a) := by group
      _ = GeneralLinearGroup.scalar ι (z * u) * ((x : GL ι K) * a) := by rw [← map_mul]
      _ = GeneralLinearGroup.scalar ι (u * z) * ((x : GL ι K) * a) := by rw [mul_comm z u]
      _ = (GeneralLinearGroup.scalar ι u * GeneralLinearGroup.scalar ι z) *
            ((x : GL ι K) * a) := by rw [← map_mul]
      _ = GeneralLinearGroup.scalar ι u *
            (GeneralLinearGroup.scalar ι z * ((x : GL ι K) * a)) := by group
      _ = GeneralLinearGroup.scalar ι u *
            ((GeneralLinearGroup.scalar ι z * (x : GL ι K)) * a) := by group
      _ = GeneralLinearGroup.scalar ι u * ((x' : GL ι K) * a) := by rw [h]
  exact commChar_eq hG ha hmain

theorem commChar_eq_one_of_scalar (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G)
    {z : Kˣ} (hz : a = GeneralLinearGroup.scalar ι z) (x : G) :
    commChar hG ha x = 1 := by
  subst hz
  rw [commChar_eq_one_iff]
  exact scalar_mul_comm z (x : GL ι K)

theorem commChar_eq_one_of_scalar_arg (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G)
    {x : G} {z : Kˣ} (hz : (x : GL ι K) = GeneralLinearGroup.scalar ι z) :
    commChar hG ha x = 1 := by
  rw [commChar_eq_one_iff]
  show a * (x : GL ι K) = (x : GL ι K) * a
  rw [hz]
  exact (scalar_mul_comm z a).symm

theorem commChar_conj (hG : IsProjElem p G) {A a x : GL ι K} (ha : a ∈ G) (hx : x ∈ G)
    (hAa : A * a * A⁻¹ ∈ G) (hAx : A * x * A⁻¹ ∈ G) :
    commChar hG hAa ⟨A * x * A⁻¹, hAx⟩ = commChar hG ha ⟨x, hx⟩ := by
  set u := commChar hG ha ⟨x, hx⟩
  have hspec := commChar_spec hG ha ⟨x, hx⟩
  have hmain : (A * a * A⁻¹) * (A * x * A⁻¹) =
      GeneralLinearGroup.scalar ι u * ((A * x * A⁻¹) * (A * a * A⁻¹)) := by
    calc (A * a * A⁻¹) * (A * x * A⁻¹) = A * (a * x) * A⁻¹ := by group
      _ = A * (GeneralLinearGroup.scalar ι u * (x * a)) * A⁻¹ := by rw [hspec]
      _ = (A * GeneralLinearGroup.scalar ι u) * (x * a) * A⁻¹ := by group
      _ = (GeneralLinearGroup.scalar ι u * A) * (x * a) * A⁻¹ := by
          rw [(scalar_mul_comm u A).symm]
      _ = GeneralLinearGroup.scalar ι u * ((A * x * A⁻¹) * (A * a * A⁻¹)) := by group
  exact commChar_eq hG hAa hmain

end TypeA.PGLTor


open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Pairing

variable {G : Type} [Group G] {Bs J L : Subgroup G}
  {F : Type} [Field F] [Finite F] {d : ℕ}

@[expose] noncomputable def a3XHom (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : ↥Bs →* MulAut (projectiveSL d F) :=
  (ggLAut L θ).comp (Subgroup.inclusion hN)

theorem a3XHom_apply (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs) :
    a3XHom (L := L) θ hN b = ggLAut L θ ⟨(b : G), hN b.2⟩ := rfl

@[expose] noncomputable def a3X (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : Subgroup (MulAut (projectiveSL d F)) :=
  (a3XHom (L := L) θ hN).range

theorem a3X_isElemAbelian (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hE : IsElemAbelian 3 Bs) :
    IsElemAbelian 3 (a3X (L := L) θ hN) := by
  haveI : IsMulCommutative ↥Bs := hE.1
  have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative Bs a.1.2 b.1.2
    · apply Subtype.ext
      exact hE.2 (x : G) x.2
  have h := ggIsElemAbelian_map (p := 3) (E := (⊤ : Subgroup ↥Bs)) htop
    (a3XHom (L := L) θ hN)
  simpa [a3X, Subgroup.map_top] using h

@[expose] noncomputable def a3Gp (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : Subgroup (GL (Fin d) F) :=
  (a3X (L := L) θ hN).comap (conjAut d F)

theorem a3Gp_isProjElem (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d) (hE : IsElemAbelian 3 Bs) :
    TypeA.PGLTor.IsProjElem 3 (a3Gp (L := L) θ hN) :=
  TypeA.isProjElem_comap (d := d) (p := 3) (K := F) hd (a3X_isElemAbelian θ hN hE)

@[expose] noncomputable def a3Mat (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (b : ↥Bs) :
    GL (Fin d) F :=
  Classical.choose (mem_linearAutGroup_iff.mp (hlin b))

theorem a3Mat_spec (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (b : ↥Bs) :
    conjAut d F (a3Mat (L := L) θ hN hlin b) = a3XHom (L := L) θ hN b :=
  Classical.choose_spec (mem_linearAutGroup_iff.mp (hlin b))

theorem a3Mat_mem (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (b : ↥Bs) :
    a3Mat (L := L) θ hN hlin b ∈ a3Gp (L := L) θ hN := by
  rw [a3Gp, Subgroup.mem_comap, a3Mat_spec]
  exact MonoidHom.mem_range.mpr ⟨b, rfl⟩

@[expose] noncomputable def a3Lift (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (b : ↥Bs) :
    a3Gp (L := L) θ hN :=
  ⟨a3Mat (L := L) θ hN hlin b, a3Mat_mem θ hN hlin b⟩

@[simp]
theorem a3Lift_coe (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (b : ↥Bs) :
    ((a3Lift (L := L) θ hN hlin b : a3Gp (L := L) θ hN) : GL (Fin d) F) =
      a3Mat (L := L) θ hN hlin b := rfl

theorem a3Mat_mul_scalar (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (b₁ b₂ : ↥Bs) :
    ∃ z : Fˣ, a3Mat (L := L) θ hN hlin (b₁ * b₂) =
      GeneralLinearGroup.scalar (Fin d) z *
        (a3Mat (L := L) θ hN hlin b₁ * a3Mat (L := L) θ hN hlin b₂) := by
  have hconj : conjAut d F
      (a3Mat (L := L) θ hN hlin (b₁ * b₂) *
        (a3Mat (L := L) θ hN hlin b₁ * a3Mat (L := L) θ hN hlin b₂)⁻¹) = 1 := by
    simp only [map_mul, map_inv, a3Mat_spec]
    group
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj
  obtain ⟨z, hz⟩ := TypeA.exists_unit_of_scalar (d := d) (K := F) hd hc
  refine ⟨z, ?_⟩
  calc a3Mat (L := L) θ hN hlin (b₁ * b₂)
      = (a3Mat (L := L) θ hN hlin (b₁ * b₂) *
          (a3Mat (L := L) θ hN hlin b₁ * a3Mat (L := L) θ hN hlin b₂)⁻¹) *
          (a3Mat (L := L) θ hN hlin b₁ * a3Mat (L := L) θ hN hlin b₂) := by group
    _ = GeneralLinearGroup.scalar (Fin d) z *
          (a3Mat (L := L) θ hN hlin b₁ * a3Mat (L := L) θ hN hlin b₂) := by rw [hz]

theorem a3Mat_one_scalar (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d) :
    ∃ z : Fˣ, a3Mat (L := L) θ hN hlin (1 : ↥Bs) = GeneralLinearGroup.scalar (Fin d) z := by
  have h1 : conjAut d F (a3Mat (L := L) θ hN hlin (1 : ↥Bs)) = 1 := by
    rw [a3Mat_spec, map_one]
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one h1
  exact TypeA.exists_unit_of_scalar (d := d) (K := F) hd hc

section CubeClass

variable {G : Type} [Group G] {Bs J L : Subgroup G}
  {F : Type} [Field F] [Finite F] {d : ℕ} [Nonempty (Fin d)]
  {θ : L ⧸ Subgroup.center L ≃* projectiveSL d F}
  {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
  {hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F}
  {hd : 0 < d} {hE : IsElemAbelian 3 Bs}

@[expose] noncomputable def a3Lam (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (x : a3Gp (L := L) θ hN) : Fˣ :=
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
    (a3Gp_isProjElem (L := L) θ hN hd hE) x

theorem a3Lam_spec (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (x : a3Gp (L := L) θ hN) :
    ((x : GL (Fin d) F) ^ 3) =
      GeneralLinearGroup.scalar (Fin d) (a3Lam (L := L) θ hN hd hE x) := by
  unfold a3Lam
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
    (a3Gp_isProjElem (L := L) θ hN hd hE) x

theorem a3Lam_mul (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (x y : a3Gp (L := L) θ hN) :
    a3Lam (L := L) θ hN hd hE (x * y) =
      a3Lam (L := L) θ hN hd hE x * a3Lam (L := L) θ hN hd hE y := by
  unfold a3Lam
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact map_mul (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
    (a3Gp_isProjElem (L := L) θ hN hd hE)) x y

theorem a3Scalar_mem (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (z : Fˣ) :
    GeneralLinearGroup.scalar (Fin d) z ∈ a3Gp (L := L) θ hN := by
  rw [a3Gp, Subgroup.mem_comap, a3X, MonoidHom.mem_range]
  refine ⟨1, ?_⟩
  rw [a3XHom_apply]
  change (ggLAut L θ) (1 : Subgroup.normalizer (L : Set G)) = conjAut d F (GeneralLinearGroup.scalar (Fin d) z)
  rw [map_one, conjAut_scalar]

theorem a3Lam_scalar (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (z : Fˣ) :
    a3Lam (L := L) θ hN hd hE
      ⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩ = z ^ 3 := by
  unfold a3Lam
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply TypeA.PGLTor.scalar_injective (ι := Fin d)
  rw [← TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
    (a3Gp_isProjElem (L := L) θ hN hd hE)
    ⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩]
  rw [← map_pow]

theorem a3Lam_conj (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (A : GL (Fin d) F) (x : a3Gp (L := L) θ hN)
    (hx : A * (x : GL (Fin d) F) * A⁻¹ ∈ a3Gp (L := L) θ hN) :
    a3Lam (L := L) θ hN hd hE ⟨A * (x : GL (Fin d) F) * A⁻¹, hx⟩ =
      a3Lam (L := L) θ hN hd hE x := by
  unfold a3Lam
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply TypeA.PGLTor.scalar_injective (ι := Fin d)
  calc GeneralLinearGroup.scalar (Fin d)
        (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
          (a3Gp_isProjElem (L := L) θ hN hd hE)
          ⟨A * (x : GL (Fin d) F) * A⁻¹, hx⟩)
      = (A * (x : GL (Fin d) F) * A⁻¹) ^ 3 :=
        (TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
          (a3Gp_isProjElem (L := L) θ hN hd hE)
          ⟨A * (x : GL (Fin d) F) * A⁻¹, hx⟩).symm
    _ = A * (x : GL (Fin d) F) ^ 3 * A⁻¹ := by
        simp only [pow_three]
        group
    _ = A * GeneralLinearGroup.scalar (Fin d)
          (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
            (a3Gp_isProjElem (L := L) θ hN hd hE) x) * A⁻¹ := by
        rw [TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
          (a3Gp_isProjElem (L := L) θ hN hd hE) x]
    _ = GeneralLinearGroup.scalar (Fin d)
          (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
            (a3Gp_isProjElem (L := L) θ hN hd hE) x) := by
        rw [show A * GeneralLinearGroup.scalar (Fin d)
              (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
                (a3Gp_isProjElem (L := L) θ hN hd hE) x) =
            GeneralLinearGroup.scalar (Fin d)
              (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
                (a3Gp_isProjElem (L := L) θ hN hd hE) x) * A from
          (TypeA.PGLTor.scalar_mul_comm _ A).symm]
        group

theorem a3Lam_scalar_mul (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) (a b : a3Gp (L := L) θ hN) (z : Fˣ)
    (h : (a : GL (Fin d) F) =
      GeneralLinearGroup.scalar (Fin d) z * (b : GL (Fin d) F)) :
    a3Lam (L := L) θ hN hd hE a =
      z ^ 3 * a3Lam (L := L) θ hN hd hE b := by
  unfold a3Lam
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply TypeA.PGLTor.scalar_injective (ι := Fin d)
  rw [← TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
      (a3Gp_isProjElem (L := L) θ hN hd hE) a]
  have hcube : (a : GL (Fin d) F) ^ 3 =
      GeneralLinearGroup.scalar (Fin d)
        (z ^ 3 * TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
          (a3Gp_isProjElem (L := L) θ hN hd hE) b) := by
    rw [h]
    calc (GeneralLinearGroup.scalar (Fin d) z * (b : GL (Fin d) F)) ^ 3
        = GeneralLinearGroup.scalar (Fin d) z ^ 3 * (b : GL (Fin d) F) ^ 3 := by
            exact (Commute.mul_pow (TypeA.PGLTor.scalar_mul_comm z (b : GL (Fin d) F))) 3
      _ = GeneralLinearGroup.scalar (Fin d) (z ^ 3) * (b : GL (Fin d) F) ^ 3 := by
            rw [← map_pow]
      _ = GeneralLinearGroup.scalar (Fin d) (z ^ 3) *
            GeneralLinearGroup.scalar (Fin d)
              (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
                (a3Gp_isProjElem (L := L) θ hN hd hE) b) := by
            rw [TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
              (a3Gp_isProjElem (L := L) θ hN hd hE) b]
      _ = GeneralLinearGroup.scalar (Fin d)
            (z ^ 3 * TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
              (a3Gp_isProjElem (L := L) θ hN hd hE) b) := by
            rw [← map_mul]
  exact hcube

@[expose] noncomputable def a3Chi (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) :
    ↥Bs →* TypeA.PGLTor.PowQuot F 3 where
  toFun b := QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
    (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b))
  map_one' := by
    classical
    obtain ⟨z, hz⟩ := a3Mat_one_scalar (L := L) θ hN hlin hd
    have hlift : (a3Lift (L := L) θ hN hlin (1 : ↥Bs) : a3Gp (L := L) θ hN) =
        ⟨GeneralLinearGroup.scalar (Fin d) z,
          a3Scalar_mem (L := L) θ hN z⟩ := Subtype.ext hz
    rw [hlift, a3Lam_scalar]
    have hz3 : (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
        TypeA.PGLTor.PowQuot F 3) = 1 := by
      change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
        TypeA.PGLTor.PowQuot F 3) = 1
      rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
      exact ⟨z, rfl⟩
    exact hz3
  map_mul' := by
    classical
    intro b₁ b₂
    obtain ⟨z, hz⟩ := a3Mat_mul_scalar (L := L) θ hN hlin hd b₁ b₂
    have hlift : (a3Lift (L := L) θ hN hlin (b₁ * b₂) : a3Gp (L := L) θ hN) =
        ⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩ *
          (a3Lift (L := L) θ hN hlin b₁ * a3Lift (L := L) θ hN hlin b₂) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, a3Lift_coe]
      exact hz
    have hlam : a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (b₁ * b₂)) =
        z ^ 3 * (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₁) *
          a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₂)) := by
      calc a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (b₁ * b₂))
          = a3Lam (L := L) θ hN hd hE
              (⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩ *
                (a3Lift (L := L) θ hN hlin b₁ * a3Lift (L := L) θ hN hlin b₂)) := by
              rw [hlift]
        _ = a3Lam (L := L) θ hN hd hE
              ⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩ *
            a3Lam (L := L) θ hN hd hE
              (a3Lift (L := L) θ hN hlin b₁ * a3Lift (L := L) θ hN hlin b₂) := by
              rw [a3Lam_mul]
        _ = z ^ 3 * (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₁) *
              a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₂)) := by
              rw [a3Lam_scalar, a3Lam_mul]
    change (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
        (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (b₁ * b₂)))) =
      (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
        (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₁))) *
      (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
        (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b₂)))
    rw [hlam]
    simp only [map_mul]
    have hz3 : (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
        TypeA.PGLTor.PowQuot F 3) = 1 := by
      change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
        TypeA.PGLTor.PowQuot F 3) = 1
      rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
      exact ⟨z, rfl⟩
    rw [hz3, one_mul]

theorem a3Chi_pow_three (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b : ↥Bs) :
    a3Chi (L := L) θ hN hlin hd hE b ^ 3 = 1 := by
  calc a3Chi (L := L) θ hN hlin hd hE b ^ 3 =
      a3Chi (L := L) θ hN hlin hd hE (b ^ 3) :=
        (map_pow (a3Chi (L := L) θ hN hlin hd hE) b 3).symm
    _ = 1 := by
        have hb : (b : ↥Bs) ^ 3 = 1 := Subtype.ext (hE.2 (b : G) b.2)
        rw [hb, map_one]

@[expose] noncomputable def a3ChiPres (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) : Subgroup (MulAut ↥Bs) where
  carrier := {φ | ∀ b : ↥Bs, a3Chi (L := L) θ hN hlin hd hE (φ b) =
    a3Chi (L := L) θ hN hlin hd hE b}
  one_mem' := by intro b; simp
  mul_mem' := by
    intro φ ψ hφ hψ b
    rw [MulAut.mul_apply, hφ, hψ]
  inv_mem' := by
    intro φ hφ b
    have h := hφ (φ⁻¹ b)
    simpa using h.symm

theorem a3Chi_invariant_of_ggInduced
    (hJleL : J ≤ L)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced J Bs) :
    φ ∈ a3ChiPres (L := L) θ hN hlin hd hE := by
  classical
  simp only [ggInduced, Set.mem_setOf_eq] at hφ
  rcases hφ with ⟨g, hgJ, hgN, hgact⟩
  have hgL : g ∈ L := hJleL hgJ
  let gN : Subgroup.normalizer (L : Set G) := ⟨g, Subgroup.le_normalizer hgL⟩
  obtain ⟨gsl, hgsl⟩ := proj_surjective d F (ggQuotHom θ ⟨g, hgL⟩)
  let Ag : GL (Fin d) F := SpecialLinearGroup.toGL gsl
  have hAg : conjAut d F Ag = ggLAut L θ gN := by
    rw [show Ag = SpecialLinearGroup.toGL gsl from rfl, conjAut_toGL, hgsl]
    simpa [gN] using (ggLAut_of_mem (L := L) θ (⟨g, hgL⟩ : ↥L)
      (Subgroup.le_normalizer hgL)).symm
  intro b
  let bN : Subgroup.normalizer (L : Set G) := ⟨(b : G), hN b.2⟩
  have hφeq : (⟨(φ b : G), hN (φ b).2⟩ : Subgroup.normalizer (L : Set G)) =
      gN * bN * gN⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gN, bN, Subgroup.coe_mk]
    exact hgact b
  have hproj : a3XHom (L := L) θ hN (φ b) =
      conjAut d F (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) := by
    calc a3XHom (L := L) θ hN (φ b) = ggLAut L θ (gN * bN * gN⁻¹) := by
          rw [a3XHom_apply, hφeq]
      _ = ggLAut L θ gN * ggLAut L θ bN * (ggLAut L θ gN)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = conjAut d F Ag * a3XHom (L := L) θ hN b * (conjAut d F Ag)⁻¹ := by
          rw [← hAg, ← a3XHom_apply]
      _ = conjAut d F (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) := by
          rw [map_mul, map_mul, map_inv, a3Mat_spec]
  have hmem : Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹ ∈ a3Gp (L := L) θ hN := by
    rw [a3Gp, Subgroup.mem_comap, ← hproj]
    exact MonoidHom.mem_range.mpr ⟨φ b, rfl⟩
  have hconj : conjAut d F
      (a3Mat (L := L) θ hN hlin (φ b) *
        (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹)⁻¹) = 1 := by
    simp only [map_mul, map_inv, a3Mat_spec, hproj]
    group
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj
  obtain ⟨z, hz⟩ := TypeA.exists_unit_of_scalar (d := d) (K := F) hd hc
  have hz' : a3Mat (L := L) θ hN hlin (φ b) =
      GeneralLinearGroup.scalar (Fin d) z *
        (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) := by
    calc a3Mat (L := L) θ hN hlin (φ b)
        = (a3Mat (L := L) θ hN hlin (φ b) *
            (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹)⁻¹) *
            (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) := by group
      _ = GeneralLinearGroup.scalar (Fin d) z *
            (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) := by rw [hz]
  let x' : a3Gp (L := L) θ hN := ⟨Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹, hmem⟩
  have hlift_eq : (a3Lift (L := L) θ hN hlin (φ b) : a3Gp (L := L) θ hN) =
      ⟨GeneralLinearGroup.scalar (Fin d) z, a3Scalar_mem (L := L) θ hN z⟩ * x' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, a3Lift_coe, x']
    exact hz'
  have hlam_eq : a3Lam (L := L) θ hN hd hE
      (a3Lift (L := L) θ hN hlin (φ b)) = z ^ 3 * a3Lam (L := L) θ hN hd hE x' :=
    a3Lam_scalar_mul (L := L) θ hN hd hE _ _ z
      (by simpa using congrArg (fun x : a3Gp (L := L) θ hN => (x : GL (Fin d) F)) hlift_eq)
  have hlam_conj : a3Lam (L := L) θ hN hd hE x' =
      a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b) :=
    a3Lam_conj (L := L) θ hN hd hE Ag (a3Lift (L := L) θ hN hlin b) hmem
  change a3Chi (L := L) θ hN hlin hd hE (φ b) =
    a3Chi (L := L) θ hN hlin hd hE b
  change (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (φ b)))) =
    (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b)))
  calc (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
        (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (φ b))))
      = (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
          (z ^ 3 * a3Lam (L := L) θ hN hd hE x')) := by rw [hlam_eq]
    _ = (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3)) *
          (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
            (a3Lam (L := L) θ hN hd hE x')) := by rw [map_mul]
    _ = (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
          (a3Lam (L := L) θ hN hd hE x')) := by
        have hz3 : (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
            TypeA.PGLTor.PowQuot F 3) = 1 := by
          change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
            TypeA.PGLTor.PowQuot F 3) = 1
          rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
          exact ⟨z, rfl⟩
        rw [hz3, one_mul]
    _ = (QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
          (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin b))) := by rw [hlam_conj]

theorem a3Chi_invariant
    (hJleL : J ≤ L) :
    ggAutomizer J Bs ≤ a3ChiPres (L := L) θ hN hlin hd hE := by
  rw [ggAutomizer, Subgroup.closure_le]
  intro φ hφ
  exact a3Chi_invariant_of_ggInduced (L := L) (θ := θ) (hN := hN)
    (hlin := hlin) (hd := hd) (hE := hE) hJleL hφ

theorem powQuot_pow_three (c : TypeA.PGLTor.PowQuot F 3) : c ^ 3 = 1 := by
  refine QuotientGroup.induction_on c ?_
  intro u
  rw [← QuotientGroup.mk_pow]
  exact (TypeA.PGLTor.powQuot_mk_eq_one_iff (p := 3)).mpr ⟨u, rfl⟩

theorem a3Chi_kills_corootSpan
    (hJleL : J ≤ L)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r)) :
    ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      a3Chi (L := L) θ hN hlin hd hE (Additive.toMul (ι.symm v)) = 1 := by
  classical
  refine ggCharacter_apply_corootSpan ι r h α hform hα2 hgen
    (fun c => powQuot_pow_three (F := F) c)
    (a3Chi (L := L) θ hN hlin hd hE) ?_
  intro φ hφ b
  exact a3Chi_invariant (L := L) (θ := θ) (hN := hN) (hlin := hlin)
    (hd := hd) (hE := hE) hJleL hφ b

theorem a3Chi_coroot_eq_one
    (hJleL : J ≤ L)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin 3) :
    a3Chi (L := L) θ hN hlin hd hE (Additive.toMul (ι.symm (h j))) = 1 :=
  a3Chi_kills_corootSpan (L := L) (θ := θ) (hN := hN)
    (hlin := hlin) (hd := hd) (hE := hE) hJleL ι r h α hform hα2 hgen
    (h j) (Submodule.subset_span (Set.mem_range_self j))

end CubeClass

@[expose] noncomputable def a3PairU (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b c : ↥Bs) : Fˣ :=
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin b).2 (a3Lift (L := L) θ hN hlin c)

@[expose] noncomputable def a3PairR (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b c : ↥Bs) : rootsOfUnity 3 F := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ⟨a3PairU (L := L) θ hN hlin hd hE b c,
    (mem_rootsOfUnity 3 _).mpr
      (TypeA.PGLTor.commChar_pow_eq_one (a3Gp_isProjElem (L := L) θ hN hd hE)
        (a3Lift (L := L) θ hN hlin b).2 (a3Lift (L := L) θ hN hlin c))⟩

theorem a3PairR_one_right (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE b 1 = 1 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨z, hz⟩ := a3Mat_one_scalar (L := L) θ hN hlin hd
  apply Subtype.ext
  simp only [a3PairR, a3PairU]
  exact TypeA.PGLTor.commChar_eq_one_of_scalar_arg (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin b).2 hz

theorem a3PairR_one_left (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (c : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE 1 c = 1 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨z, hz⟩ := a3Mat_one_scalar (L := L) θ hN hlin hd
  apply Subtype.ext
  simp only [a3PairR, a3PairU]
  exact TypeA.PGLTor.commChar_eq_one_of_scalar (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin 1).2 hz (a3Lift (L := L) θ hN hlin c)

theorem a3PairR_self (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE b b = 1 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply Subtype.ext
  simp only [a3PairR, a3PairU]
  exact TypeA.PGLTor.commChar_self (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin b)

theorem a3PairR_mul_right (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b c₁ c₂ : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE b (c₁ * c₂) =
      a3PairR (L := L) θ hN hlin hd hE b c₁ *
        a3PairR (L := L) θ hN hlin hd hE b c₂ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨z, hz⟩ := a3Mat_mul_scalar (L := L) θ hN hlin hd c₁ c₂
  apply Subtype.ext
  change a3PairU (L := L) θ hN hlin hd hE b (c₁ * c₂) =
    a3PairU (L := L) θ hN hlin hd hE b c₁ *
      a3PairU (L := L) θ hN hlin hd hE b c₂
  have hstep := TypeA.PGLTor.commChar_eq_of_eq_scalar_mul_arg
    (a3Gp_isProjElem (L := L) θ hN hd hE) (a3Lift (L := L) θ hN hlin b).2
    (x := a3Lift (L := L) θ hN hlin c₁ * a3Lift (L := L) θ hN hlin c₂)
    (x' := a3Lift (L := L) θ hN hlin (c₁ * c₂)) (z := z) (by
      exact hz)
  exact hstep.trans (map_mul (TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin b).2) (a3Lift (L := L) θ hN hlin c₁)
    (a3Lift (L := L) θ hN hlin c₂))

theorem a3PairR_mul_left (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b₁ b₂ c : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE (b₁ * b₂) c =
      a3PairR (L := L) θ hN hlin hd hE b₁ c *
        a3PairR (L := L) θ hN hlin hd hE b₂ c := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨z, hz⟩ := a3Mat_mul_scalar (L := L) θ hN hlin hd b₁ b₂
  apply Subtype.ext
  change a3PairU (L := L) θ hN hlin hd hE (b₁ * b₂) c =
    a3PairU (L := L) θ hN hlin hd hE b₁ c *
      a3PairU (L := L) θ hN hlin hd hE b₂ c
  have hstep := TypeA.PGLTor.commChar_eq_of_eq_scalar_mul
    (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a := ((a3Lift (L := L) θ hN hlin b₁ * a3Lift (L := L) θ hN hlin b₂ :
      a3Gp (L := L) θ hN) : GL (Fin d) F))
    (a' := a3Mat (L := L) θ hN hlin (b₁ * b₂))
    (ha := mul_mem (a3Lift (L := L) θ hN hlin b₁).2 (a3Lift (L := L) θ hN hlin b₂).2)
    (ha' := (a3Lift (L := L) θ hN hlin (b₁ * b₂)).2) (z := z) (by
      exact hz)
    (a3Lift (L := L) θ hN hlin c)
  refine hstep.trans ?_
  exact TypeA.PGLTor.commChar_mul_left (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin b₁).2 (a3Lift (L := L) θ hN hlin b₂).2
    (a3Lift (L := L) θ hN hlin c)

theorem commChar_eq_of_conjAut_eq [Nonempty (Fin d)]
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d)
    (hG : TypeA.PGLTor.IsProjElem 3 (a3Gp (L := L) θ hN))
    {a a' : GL (Fin d) F} (ha : a ∈ a3Gp (L := L) θ hN) (ha' : a' ∈ a3Gp (L := L) θ hN)
    (h : conjAut d F a = conjAut d F a') (x : a3Gp (L := L) θ hN) :
    TypeA.PGLTor.commChar hG ha x = TypeA.PGLTor.commChar hG ha' x := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hconj : conjAut d F (a' * a⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj
  obtain ⟨z, hz⟩ := TypeA.exists_unit_of_scalar (d := d) (K := F) hd hc
  have hEq : a' = GeneralLinearGroup.scalar (Fin d) z * a := by
    calc a' = (a' * a⁻¹) * a := by group
      _ = GeneralLinearGroup.scalar (Fin d) z * a := by rw [hz]
  exact (TypeA.PGLTor.commChar_eq_of_eq_scalar_mul hG ha ha' hEq x).symm

theorem commChar_eq_of_conjAut_eq_arg [Nonempty (Fin d)]
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d)
    (hG : TypeA.PGLTor.IsProjElem 3 (a3Gp (L := L) θ hN))
    {a : GL (Fin d) F} (ha : a ∈ a3Gp (L := L) θ hN)
    {x x' : a3Gp (L := L) θ hN}
    (h : conjAut d F (x : GL (Fin d) F) = conjAut d F (x' : GL (Fin d) F)) :
    TypeA.PGLTor.commChar hG ha x = TypeA.PGLTor.commChar hG ha x' := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hconj : conjAut d F ((x' : GL (Fin d) F) * (x : GL (Fin d) F)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj
  obtain ⟨z, hz⟩ := TypeA.exists_unit_of_scalar (d := d) (K := F) hd hc
  have hEq : (x' : GL (Fin d) F) =
      GeneralLinearGroup.scalar (Fin d) z * (x : GL (Fin d) F) := by
    calc (x' : GL (Fin d) F) =
        ((x' : GL (Fin d) F) * (x : GL (Fin d) F)⁻¹) * (x : GL (Fin d) F) := by group
      _ = GeneralLinearGroup.scalar (Fin d) z * (x : GL (Fin d) F) := by rw [hz]
  exact (TypeA.PGLTor.commChar_eq_of_eq_scalar_mul_arg hG ha hEq).symm

theorem a3PairR_invariant_of_ggInduced
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced J Bs) (b c : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE (φ b) (φ c) =
      a3PairR (L := L) θ hN hlin hd hE b c := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨g, hgJ, hgBN, hgφ⟩ := hφ
  have hgL : g ∈ L := hJleL hgJ
  have hgNL : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hgL
  let xg : MulAut (projectiveSL d F) := ggLAut L θ ⟨g, hgNL⟩
  have hxg : xg = MulAut.conj (ggQuotHom θ ⟨g, hgL⟩) := by
    simpa [xg] using ggLAut_of_mem (L := L) θ (⟨g, hgL⟩ : ↥L) (Subgroup.le_normalizer hgL)
  obtain ⟨gsl, hgsl⟩ := proj_surjective d F (ggQuotHom θ ⟨g, hgL⟩)
  let Ag : GL (Fin d) F := SpecialLinearGroup.toGL gsl
  have hAg : conjAut d F Ag = xg := by
    rw [show Ag = SpecialLinearGroup.toGL gsl from rfl, conjAut_toGL, hgsl, ← hxg]
  have hxφb : a3XHom (L := L) θ hN (φ b) = xg * a3XHom (L := L) θ hN b * xg⁻¹ := by
    rw [a3XHom_apply, a3XHom_apply]
    have h1 : (⟨((φ b : ↥Bs) : G), hN (φ b).2⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hgNL⟩ * ⟨(b : G), hN b.2⟩ * ⟨g, hgNL⟩⁻¹ := by
      apply Subtype.ext
      show ((φ b : ↥Bs) : G) = g * (b : G) * g⁻¹
      exact hgφ b
    rw [h1, map_mul, map_mul, map_inv]
  have hxφc : a3XHom (L := L) θ hN (φ c) = xg * a3XHom (L := L) θ hN c * xg⁻¹ := by
    rw [a3XHom_apply, a3XHom_apply]
    have h1 : (⟨((φ c : ↥Bs) : G), hN (φ c).2⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hgNL⟩ * ⟨(c : G), hN c.2⟩ * ⟨g, hgNL⟩⁻¹ := by
      apply Subtype.ext
      show ((φ c : ↥Bs) : G) = g * (c : G) * g⁻¹
      exact hgφ c
    rw [h1, map_mul, map_mul, map_inv]
  have hconjb : conjAut d F (Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹) =
      a3XHom (L := L) θ hN (φ b) := by
    simp only [map_mul, map_inv, a3Mat_spec, hAg]
    exact hxφb.symm
  have hconjc : conjAut d F (Ag * a3Mat (L := L) θ hN hlin c * Ag⁻¹) =
      a3XHom (L := L) θ hN (φ c) := by
    simp only [map_mul, map_inv, a3Mat_spec, hAg]
    exact hxφc.symm
  have hAb : Ag * a3Mat (L := L) θ hN hlin b * Ag⁻¹ ∈ a3Gp (L := L) θ hN := by
    rw [a3Gp, Subgroup.mem_comap, hconjb]
    exact MonoidHom.mem_range.mpr ⟨φ b, rfl⟩
  have hAc : Ag * a3Mat (L := L) θ hN hlin c * Ag⁻¹ ∈ a3Gp (L := L) θ hN := by
    rw [a3Gp, Subgroup.mem_comap, hconjc]
    exact MonoidHom.mem_range.mpr ⟨φ c, rfl⟩
  apply Subtype.ext
  show TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
      (a3Lift (L := L) θ hN hlin (φ b)).2 (a3Lift (L := L) θ hN hlin (φ c)) =
    TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
      (a3Lift (L := L) θ hN hlin b).2 (a3Lift (L := L) θ hN hlin c)
  calc TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
        (a3Lift (L := L) θ hN hlin (φ b)).2 (a3Lift (L := L) θ hN hlin (φ c))
      = TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
          hAb (a3Lift (L := L) θ hN hlin (φ c)) := by
        exact commChar_eq_of_conjAut_eq θ hN hlin hd (a3Gp_isProjElem (L := L) θ hN hd hE)
          (a3Lift (L := L) θ hN hlin (φ b)).2 hAb (by
            simp only [a3Lift_coe, a3Mat_spec]
            exact hconjb.symm)
          (a3Lift (L := L) θ hN hlin (φ c))
    _ = TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
          hAb ⟨Ag * a3Mat (L := L) θ hN hlin c * Ag⁻¹, hAc⟩ := by
        exact commChar_eq_of_conjAut_eq_arg θ hN hlin hd (a3Gp_isProjElem (L := L) θ hN hd hE)
          hAb (by
            simp only [a3Lift_coe, a3Mat_spec]
            exact hconjc.symm)
    _ = TypeA.PGLTor.commChar (a3Gp_isProjElem (L := L) θ hN hd hE)
          (a3Lift (L := L) θ hN hlin b).2 (a3Lift (L := L) θ hN hlin c) := by
        exact TypeA.PGLTor.commChar_conj (a3Gp_isProjElem (L := L) θ hN hd hE)
          (a3Lift (L := L) θ hN hlin b).2 (a3Lift (L := L) θ hN hlin c).2 hAb hAc

@[expose] def a3PairPres (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d)
    (hE : IsElemAbelian 3 Bs) : Subgroup (MulAut ↥Bs) where
  carrier := {φ | ∀ b c : ↥Bs,
    a3PairR (L := L) θ hN hlin hd hE (φ b) (φ c) =
      a3PairR (L := L) θ hN hlin hd hE b c}
  one_mem' := by
    intro b c
    rfl
  mul_mem' := by
    intro φ ψ hφ hψ b c
    change a3PairR (L := L) θ hN hlin hd hE (φ (ψ b)) (φ (ψ c)) =
      a3PairR (L := L) θ hN hlin hd hE b c
    rw [hφ, hψ]
  inv_mem' := by
    intro φ hφ b c
    have h := hφ (φ⁻¹ b) (φ⁻¹ c)
    simpa using h.symm

theorem a3PairPres_ggAutomizer_le
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F) (hd : 0 < d) :
    ggAutomizer J Bs ≤ a3PairPres (L := L) θ hN hlin hd hE := by
  rw [ggAutomizer, Subgroup.closure_le]
  intro φ hφ
  exact a3PairR_invariant_of_ggInduced hJleL hE θ hN hlin hd hφ

@[expose] noncomputable def a3PairRightHom (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (b : ↥Bs) : ↥Bs →* rootsOfUnity 3 F where
  toFun c := a3PairR (L := L) θ hN hlin hd hE b c
  map_one' := a3PairR_one_right (L := L) θ hN hlin hd hE b
  map_mul' := a3PairR_mul_right (L := L) θ hN hlin hd hE b

@[expose] noncomputable def a3PairFirstHom (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) : ↥Bs →* (↥Bs →* rootsOfUnity 3 F) where
  toFun b := a3PairRightHom (L := L) θ hN hlin hd hE b
  map_one' := MonoidHom.ext (fun c => a3PairR_one_left (L := L) θ hN hlin hd hE c)
  map_mul' b₁ b₂ := MonoidHom.ext
    (fun c => a3PairR_mul_left (L := L) θ hN hlin hd hE b₁ b₂ c)

theorem corootSpan_eq_closure {G : Type} [Group G] {Bs : Subgroup G} {k : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (h : Fin k → V) :
    ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h)) =
      Subgroup.closure (Set.range (fun j : Fin k =>
        ((Additive.toMul (ι.symm (h j)) : ↥Bs) : G))) := by
  classical
  refine le_antisymm ?_ ?_
  · refine ggSpanSub_le (p := 3)
      (X := Subgroup.closure (Set.range (fun j : Fin k =>
        ((Additive.toMul (ι.symm (h j)) : ↥Bs) : G)))) (hv := h) ι ?_
    intro j
    exact Subgroup.subset_closure (Set.mem_range_self j)
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨h j, Submodule.subset_span (Set.mem_range_self j), rfl⟩

@[expose] noncomputable def a3ConjHom (d : ℕ) (F : Type) [Field F] :
    ProjGenLinGroup (Fin d) F →* MulAut (projectiveSL d F) :=
  QuotientGroup.lift (Subgroup.center (GL (Fin d) F)) (conjAut d F) (by
    intro x hx
    change conjAut d F x = 1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
    exact conjAut_scalar u)

theorem a3ConjHom_mk (d : ℕ) (F : Type) [Field F] (A : GL (Fin d) F) :
    a3ConjHom d F (ProjGenLinGroup.mk A) = conjAut d F A :=
  QuotientGroup.lift_mk' _ _ A

section AdditiveSetup

variable [IsMulCommutative ↥Bs]

local instance a3AddCommGroup : AddCommGroup (Additive ↥Bs) :=
  { (Additive.addGroup : AddGroup (Additive ↥Bs)) with
    add_comm := fun a b =>
      congrArg Additive.ofMul
        (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

@[expose] noncomputable def a3PairAdd
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) :
    Additive ↥Bs →+ Additive ↥Bs →+ Additive (rootsOfUnity 3 F) where
  toFun x := (a3PairRightHom (L := L) θ hN hlin hd hE (Additive.toMul x)).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change a3PairR (L := L) θ hN hlin hd hE (Additive.toMul (0 : Additive ↥Bs))
      (Additive.toMul y) = 1
    rw [show Additive.toMul (0 : Additive ↥Bs) = (1 : ↥Bs) from rfl,
      a3PairR_one_left (L := L) θ hN hlin hd hE (Additive.toMul y)]
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    change a3PairR (L := L) θ hN hlin hd hE (Additive.toMul (x + y)) (Additive.toMul z) =
      a3PairR (L := L) θ hN hlin hd hE (Additive.toMul x) (Additive.toMul z) *
        a3PairR (L := L) θ hN hlin hd hE (Additive.toMul y) (Additive.toMul z)
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
      a3PairR_mul_left (L := L) θ hN hlin hd hE (Additive.toMul x) (Additive.toMul y)
        (Additive.toMul z)]

theorem a3PairAdd_ofMul
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (x y : ↥Bs) :
    a3PairAdd (L := L) θ hN hlin hd hE (Additive.ofMul x) (Additive.ofMul y) =
      Additive.ofMul (a3PairR (L := L) θ hN hlin hd hE x y) := rfl

theorem a3PairAdd_self
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (x : Additive ↥Bs) :
    a3PairAdd (L := L) θ hN hlin hd hE x x = 0 := by
  change a3PairR (L := L) θ hN hlin hd hE (Additive.toMul x) (Additive.toMul x) = 1
  rw [a3PairR_self]

section Transport

variable [Finite G] {hJleL : J ≤ L} {hE : IsElemAbelian 3 Bs}
  {θ : L ⧸ Subgroup.center L ≃* projectiveSL d F}
  {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
  {hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F}
  {hd : 0 < d}

theorem a3AddEquiv_smul {A : Type} [AddCommGroup A] [Module (ZMod 3) A]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : A ≃+ V) (c : ZMod 3) (x : A) : ι (c • x) = c • ι x := by
  have hc : c = ((c.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val c).symm
  rw [hc, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

@[expose] noncomputable def a3PairV
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) := by
  classical
  let pairInnerFun (x : Additive ↥Bs) :
      Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) :=
    { toFun := a3PairAdd (L := L) θ hN hlin hd hE x
      map_add' := fun y z => map_add (a3PairAdd (L := L) θ hN hlin hd hE x) y z
      map_smul' := fun c y =>
        ZMod.map_smul (a3PairAdd (L := L) θ hN hlin hd hE x) c y }
  let pairInner : Additive ↥Bs →+
      (Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) :=
    AddMonoidHom.mk' pairInnerFun (by
      intro x y
      apply LinearMap.ext
      intro z
      change a3PairAdd (L := L) θ hN hlin hd hE (x + y) z =
        a3PairAdd (L := L) θ hN hlin hd hE x z +
          a3PairAdd (L := L) θ hN hlin hd hE y z
      rw [map_add]
      rfl)
  let pairA : Additive ↥Bs →ₗ[ZMod 3]
      (Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) :=
    pairInner.toZModLinearMap 3
  let pairRight : V → (V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) := fun u =>
    { toFun := fun v => pairA (ι.symm u) (ι.symm v)
      map_add' := by
        intro v₁ v₂
        rw [map_add, map_add]
      map_smul' := by
        intro c v
        rw [a3AddEquiv_smul ι.symm c v]
        exact map_smul (pairA (ι.symm u)) c (ι.symm v) }
  have hzero : pairRight 0 = 0 := by
    ext v
    simp [pairRight]
  have hadd : ∀ u u', pairRight (u + u') = pairRight u + pairRight u' := by
    intro u u'
    ext v
    simp [pairRight, map_add]
  exact ({ toFun := pairRight, map_zero' := hzero, map_add' := hadd } :
    V →+ (V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F))).toZModLinearMap 3

theorem a3PairV_apply
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (u v : V) :
    a3PairV (L := L) θ hN hlin hd hE ι u v =
      a3PairAdd (L := L) θ hN hlin hd hE (ι.symm u) (ι.symm v) := by
  unfold a3PairV
  rfl

theorem a3PairAdd_apply
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs) (x y : Additive ↥Bs) :
    a3PairAdd (L := L) θ hN hlin hd hE x y =
      Additive.ofMul (a3PairR (L := L) θ hN hlin hd hE
        (Additive.toMul x) (Additive.toMul y)) := rfl

theorem a3PairV_isAlt
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d) (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    (a3PairV (L := L) θ hN hlin hd hE ι).IsAlt := by
  intro u
  rw [a3PairV_apply]
  exact a3PairAdd_self θ hN hlin hd hE (ι.symm u)

theorem a3PairV_invariant
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    ∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
      a3PairV (L := L) θ hN hlin hd hE ι (ggLin (p := 3) ι φ u)
        (ggLin (p := 3) ι φ v) =
      a3PairV (L := L) θ hN hlin hd hE ι u v := by
  intro φ hφ u v
  have hpres : φ ∈ a3PairPres (L := L) θ hN hlin hd hE :=
    a3PairPres_ggAutomizer_le hJleL hE θ hN hlin hd hφ
  rw [a3PairV_apply, a3PairV_apply, ggLin_apply, ggLin_apply,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rw [a3PairAdd_apply, a3PairAdd_apply]
  simp only [toMul_ofMul]
  rw [hpres]

theorem a3PairR_coroot_eq_one
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin 3) (c : ↥Bs) :
    a3PairR (L := L) θ hN hlin hd hE
      (Additive.toMul (ι.symm (h j))) c = 1 := by
  classical
  let β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) :=
    a3PairV (L := L) θ hN hlin hd hE ι
  have hβalt : β.IsAlt := a3PairV_isAlt θ hN hlin hd hE ι
  have hβinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
      β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v :=
    a3PairV_invariant hJleL hE θ hN hlin hd ι
  obtain ⟨hvan, -, -⟩ :=
    GGResLineJDatum.coroot_span_le_ker_of_A3 ι r h α hform hpair hind hgen β hβalt hβinv
  have h0 := congrArg
    (fun f : V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) => f (ι (Additive.ofMul c)))
    (hvan j)
  rw [a3PairV_apply, a3PairAdd_apply] at h0
  apply Additive.ofMul.injective
  simpa only [toMul_ofMul, AddEquiv.symm_apply_apply, ofMul_one, LinearMap.zero_apply] using h0

theorem a3CorootLift_comm
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin 3) (c : ↥Bs) :
    Commute (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))))
      (a3Lift (L := L) θ hN hlin c) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hzero := a3PairR_coroot_eq_one (L := L) hJleL hE θ hN hlin hd ι r h α hform hpair
    hind hgen j c
  have hu : a3PairU (L := L) θ hN hlin hd hE
      (Additive.toMul (ι.symm (h j))) c = 1 := congrArg Subtype.val hzero
  apply Subtype.ext
  exact (TypeA.PGLTor.commChar_eq_one_iff (a3Gp_isProjElem (L := L) θ hN hd hE)
    (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j)))).2
    (a3Lift (L := L) θ hN hlin c)).mp hu

theorem a3CorootLift_comm_gp
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    (hJleL : J ≤ L) (hE : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hd : 0 < d)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin 3) (g : a3Gp (L := L) θ hN) :
    Commute (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j)))) g := by
  classical
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp g.2
  have hconj : conjAut d F (g * (a3Lift (L := L) θ hN hlin c)⁻¹) = 1 := by
    rw [map_mul, Subgroup.coe_inv, map_inv, a3Lift_coe, a3Mat_spec, hc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj
  obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar (d := d) (K := F) hd hz
  have hg : (g : GL (Fin d) F) =
      GeneralLinearGroup.scalar (Fin d) u *
        (a3Lift (L := L) θ hN hlin c : GL (Fin d) F) := by
    have hu' : (g : GL (Fin d) F) * (a3Lift (L := L) θ hN hlin c : GL (Fin d) F)⁻¹ =
        GeneralLinearGroup.scalar (Fin d) u := by
      simpa only [Subgroup.coe_inv] using hu
    calc (g : GL (Fin d) F)
        = ((g : GL (Fin d) F) * (a3Lift (L := L) θ hN hlin c : GL (Fin d) F)⁻¹) *
            (a3Lift (L := L) θ hN hlin c : GL (Fin d) F) := by group
      _ = GeneralLinearGroup.scalar (Fin d) u *
            (a3Lift (L := L) θ hN hlin c : GL (Fin d) F) := by rw [hu']
  apply Subtype.ext
  change (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))) : GL (Fin d) F) *
      (g : GL (Fin d) F) = (g : GL (Fin d) F) *
      (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))) : GL (Fin d) F)
  rw [hg]
  have hcomm_gl : Commute
      (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))) : GL (Fin d) F)
      (a3Lift (L := L) θ hN hlin c : GL (Fin d) F) := by
    exact congrArg (fun x : a3Gp (L := L) θ hN => (x : GL (Fin d) F))
      (a3CorootLift_comm (L := L) hJleL hE θ hN hlin hd ι r h α hform hpair hind hgen j c)
  exact Commute.mul_right
    (a := (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))) : GL (Fin d) F))
    (b := GeneralLinearGroup.scalar (Fin d) u)
    (c := (a3Lift (L := L) θ hN hlin c : GL (Fin d) F))
    ((TypeA.PGLTor.commute_scalar u
      (a3Lift (L := L) θ hN hlin (Additive.toMul (ι.symm (h j))) : GL (Fin d) F)).symm) hcomm_gl

theorem exists_scalarPairing_of_A3_data
    {B : Subgroup G} {x : G} {D : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 0 < d)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈ linearAutGroup d F)
    [Module (ZMod 3) (Additive ↥Bs)]
    [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r)) :
    ∃ β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F),
      β.IsAlt ∧
      (∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
        β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v) ∧
      (∀ j, β (h j) = 0) ∧
      Submodule.span (ZMod 3) (Set.range h) ≤ β.ker ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 3 := by
  classical
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hJleL : J ≤ L := le_of_stdSub_left hH.1.2.2
  have hlin' : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F :=
    fun b => hlin b.1 b.2
  let β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) :=
    a3PairV (L := L) θ hN hlin' hd hE ι
  have hβalt : β.IsAlt := a3PairV_isAlt θ hN hlin' hd hE ι
  have hβinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
      β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v :=
    a3PairV_invariant hJleL hE θ hN hlin' hd ι
  obtain ⟨hvan, hspan, hfin⟩ :=
    GGResLineJDatum.coroot_span_le_ker_of_A3 ι r h α hform hpair hind hgen β hβalt hβinv
  exact ⟨β, hβalt, hβinv, hvan, hspan, hfin⟩

theorem exists_scalarPairing_A3
    {B : Subgroup G} {x : G} {D : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 0 < d)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈ linearAutGroup d F)
    (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
      (α : Fin 3 → Module.Dual (ZMod 3) V)
      (β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)),
      (∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j) ∧
      (∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3)) ∧
      LinearIndependent (ZMod 3) h ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range r) ∧
      β.IsAlt ∧
      (∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
        β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v) ∧
      (∀ j, β (h j) = 0) ∧
      Submodule.span (ZMod 3) (Set.range h) ≤ β.ker ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 3 := by
  classical
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  letI : Module (ZMod 3) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact hE.2 (x.toMul : G) x.toMul.2)
  letI : Module (ZMod 3) (Additive (rootsOfUnity 3 F)) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact x.toMul.2)
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hpairA : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  obtain ⟨β, hβalt, hβinv, hvan, hspan, hfin⟩ :=
    exists_scalarPairing_of_A3_data hH hd θ hN hlin ι r h α hform hpairA hind hgen
  exact ⟨V, instA, instM, ι, r, h, α, β, hform, hpairA, hind, hgen, hβalt, hβinv,
    hvan, hspan, hfin⟩

end Transport

end AdditiveSetup

theorem exists_scalarPairing_A3'
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 0 < d)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hN hb⟩ ∈ linearAutGroup d F)
    (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
      (α : Fin 3 → Module.Dual (ZMod 3) V)
      (β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)),
      (∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j) ∧
      (∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3)) ∧
      LinearIndependent (ZMod 3) h ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range r) ∧
      β.IsAlt ∧
      (∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
        β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v) ∧
      (∀ j, β (h j) = 0) ∧
      Submodule.span (ZMod 3) (Set.range h) ≤ β.ker ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 3 := by
  classical
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  haveI : IsMulCommutative ↥Bs := hE.1
  letI : AddCommGroup (Additive ↥Bs) :=
    { (Additive.addGroup : AddGroup (Additive ↥Bs)) with
      add_comm := fun a b =>
        congrArg Additive.ofMul
          (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }
  letI : Module (ZMod 3) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact hE.2 (x.toMul : G) x.toMul.2)
  letI : Module (ZMod 3) (Additive (rootsOfUnity 3 F)) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact x.toMul.2)
  exact exists_scalarPairing_A3 hH hd θ hN hlin hD

end Pairing

theorem exists_E27_lifts
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 0 < d)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ Etilde : Subgroup (GL (Fin d) F),
      Etilde ≤ a3Gp (L := L) θ hN ∧
      IsElemAbelian 3 Etilde ∧
      (∀ e ∈ Etilde, ∀ g ∈ a3Gp (L := L) θ hN, e * g = g * e) ∧
      27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hJleL : J ≤ L := le_of_stdSub_left hH.1.2.2
  have hperfL : commutator ↥L = ⊤ := (GGConfig.data_L hH.1).2.2.2
  haveI : IsMulCommutative ↥Bs := hE.1
  letI : AddCommGroup (Additive ↥Bs) :=
    { (Additive.addGroup : AddGroup (Additive ↥Bs)) with
      add_comm := fun a b =>
        congrArg Additive.ofMul
          (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }
  letI : Module (ZMod 3) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact hE.2 (x.toMul : G) x.toMul.2)
  letI : Module (ZMod 3) (Additive (rootsOfUnity 3 F)) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact x.toMul.2)
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
    intro j
    rw [hpairA j j]
    fin_cases j <;> decide
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  let E : Subgroup G := ggSpanSub ι W
  have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_A3
    (hN := GGResHyp.Bs_le_normalizer_J hH) ι r h α hform hpairA
    hind hgen W rfl
  have hE_le_inf : E ≤ Bs ⊓ J := hEprops.1
  have hE_card : Nat.card E = 27 := hEprops.2.2.1
  have hE_bot : E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := hEprops.2.2.2
  have hE_le_bs : E ≤ Bs := hE_le_inf.trans inf_le_left
  let e : Fin 3 → ↥Bs := fun j => Additive.toMul (ι.symm (h j))
  have hE_closure : E = Subgroup.closure (Set.range (fun j : Fin 3 => ((e j : ↥Bs) : G))) := by
    dsimp [E, W, e]
    exact corootSpan_eq_closure (Bs := Bs) ι h
  have hE_mem : ∀ j : Fin 3, ((e j : ↥Bs) : G) ∈ E := by
    intro j
    rw [hE_closure]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  have hchi : ∀ j : Fin 3,
      a3Chi (L := L) θ hN hlin hd hE (e j) = 1 := by
    intro j
    exact a3Chi_coroot_eq_one (L := L) (θ := θ) (hN := hN) (hlin := hlin)
      (hd := hd) (hE := hE) hJleL ι r h α hform hα2 hgen j
  have hu : ∀ j : Fin 3, ∃ c : Fˣ,
      c ^ 3 = a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j)) := by
    intro j
    have h := hchi j
    change (QuotientGroup.mk (s := ((powMonoidHom 3 : Fˣ →* Fˣ).range))
      (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j))) :
        TypeA.PGLTor.PowQuot F 3) = 1 at h
    rw [TypeA.PGLTor.powQuot_mk_eq_one_iff] at h
    exact h
  let u : Fin 3 → Fˣ := fun j => Classical.choose (hu j)
  have hu_spec : ∀ j : Fin 3, (u j) ^ 3 =
      a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j)) :=
    fun j => Classical.choose_spec (hu j)
  let Z : Fin 3 → a3Gp (L := L) θ hN := fun j =>
    ⟨GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
        a3Mat (L := L) θ hN hlin (e j), by
      exact mul_mem (a3Scalar_mem (L := L) θ hN ((u j)⁻¹))
        (a3Mat_mem (L := L) θ hN hlin (e j))⟩
  have hZ_coe : ∀ j : Fin 3, (Z j : GL (Fin d) F) =
      GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
        a3Mat (L := L) θ hN hlin (e j) := fun j => rfl
  have hZ3 : ∀ j : Fin 3, (Z j) ^ 3 = 1 := by
    intro j
    apply Subtype.ext
    change (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
      a3Mat (L := L) θ hN hlin (e j)) ^ 3 = 1
    have hY3 : (a3Mat (L := L) θ hN hlin (e j)) ^ 3 =
        GeneralLinearGroup.scalar (Fin d)
          (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j))) := by
      simpa [a3Lift_coe] using
        (a3Lam_spec (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j)))
    have hscalar : (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹)) ^ 3 =
        GeneralLinearGroup.scalar (Fin d) (((u j) ^ 3)⁻¹) := by
      rw [← map_pow, inv_pow]
    calc (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
          a3Mat (L := L) θ hN hlin (e j)) ^ 3
        = (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹)) ^ 3 *
            (a3Mat (L := L) θ hN hlin (e j)) ^ 3 := by
          rw [Commute.mul_pow
            (TypeA.PGLTor.commute_scalar ((u j)⁻¹)
              (a3Mat (L := L) θ hN hlin (e j))) 3]
      _ = GeneralLinearGroup.scalar (Fin d) (((u j) ^ 3)⁻¹) *
            GeneralLinearGroup.scalar (Fin d)
              (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j))) := by
          rw [hscalar, hY3]
      _ = GeneralLinearGroup.scalar (Fin d)
            ((a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j)))⁻¹) *
            GeneralLinearGroup.scalar (Fin d)
              (a3Lam (L := L) θ hN hd hE (a3Lift (L := L) θ hN hlin (e j))) := by
          rw [hu_spec j]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hZ_cent : ∀ j : Fin 3, ∀ g ∈ a3Gp (L := L) θ hN,
      Z j * g = g * Z j := by
    intro j g hg
    change (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
        a3Mat (L := L) θ hN hlin (e j)) * (g : GL (Fin d) F) =
      (g : GL (Fin d) F) * (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
        a3Mat (L := L) θ hN hlin (e j))
    have hcomm : (a3Mat (L := L) θ hN hlin (e j)) * (g : GL (Fin d) F) =
        (g : GL (Fin d) F) * (a3Mat (L := L) θ hN hlin (e j)) := by
      have h := congrArg (fun x : a3Gp (L := L) θ hN => (x : GL (Fin d) F))
        (a3CorootLift_comm_gp (L := L) hJleL hE θ hN hlin hd ι r h α hform hpairA
          hind hgen j ⟨g, hg⟩)
      simpa [a3Lift_coe] using h
    calc (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
          a3Mat (L := L) θ hN hlin (e j)) * (g : GL (Fin d) F)
        = GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
            ((a3Mat (L := L) θ hN hlin (e j)) * (g : GL (Fin d) F)) := by group
      _ = GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
            ((g : GL (Fin d) F) * (a3Mat (L := L) θ hN hlin (e j))) := by rw [hcomm]
      _ = (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) * (g : GL (Fin d) F)) *
            (a3Mat (L := L) θ hN hlin (e j)) := by group
      _ = ((g : GL (Fin d) F) * GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹)) *
            (a3Mat (L := L) θ hN hlin (e j)) := by
          rw [show GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) * (g : GL (Fin d) F) =
            (g : GL (Fin d) F) * GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) from
            (TypeA.PGLTor.commute_scalar ((u j)⁻¹) (g : GL (Fin d) F))]
      _ = (g : GL (Fin d) F) * (GeneralLinearGroup.scalar (Fin d) ((u j)⁻¹) *
            (a3Mat (L := L) θ hN hlin (e j))) := by group
  let Etilde : Subgroup (GL (Fin d) F) :=
    Subgroup.closure (Set.range (fun j : Fin 3 => (Z j : GL (Fin d) F)))
  have hEtilde_le : Etilde ≤ a3Gp (L := L) θ hN := by
    dsimp only [Etilde]
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact (Z j).2
  have hEtilde_elem : IsElemAbelian 3 Etilde := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute
      (s := Set.range (fun j : Fin 3 => (Z j : GL (Fin d) F))) ?_ ?_
    · rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
      exact hZ_cent j (Z k) (Z k).2
    · rintro _ ⟨j, rfl⟩
      exact congrArg (fun x : a3Gp (L := L) θ hN => (x : GL (Fin d) F)) (hZ3 j)
  have hEtilde_cent_le : Etilde ≤
      Subgroup.centralizer (a3Gp (L := L) θ hN : Set (GL (Fin d) F)) := by
    dsimp only [Etilde]
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun g hg => (hZ_cent j g hg).symm)
  have hcent : ∀ e ∈ Etilde, ∀ g ∈ a3Gp (L := L) θ hN, e * g = g * e := by
    intro e he g hg
    exact (Subgroup.mem_centralizer_iff.mp (hEtilde_cent_le he) g hg).symm
  have hE0_sub : E.subgroupOf Bs = Subgroup.closure (Set.range e) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxmap : (x : G) ∈ (E.subgroupOf Bs).map Bs.subtype :=
        Subgroup.mem_map_of_mem Bs.subtype hx
      have hle : (E.subgroupOf Bs).map Bs.subtype ≤
          (Subgroup.closure (Set.range e)).map Bs.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hE_le_bs, MonoidHom.map_closure, hE_closure]
        exact Subgroup.closure_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨e j, ⟨j, rfl⟩, rfl⟩)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hxmap)
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact hE_mem j
  let X : Subgroup (MulAut (projectiveSL d F)) :=
    Subgroup.closure (Set.range (fun j : Fin 3 => a3XHom (L := L) θ hN (e j)))
  have hX_map : X = (E.subgroupOf Bs).map (a3XHom (L := L) θ hN) := by
    dsimp only [X]
    rw [hE0_sub, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hinj_on_E : Function.Injective
      (fun x : E.subgroupOf Bs => a3XHom (L := L) θ hN x) := by
    intro x y hxy
    apply Subtype.ext
    let b : ↥Bs := (x * y⁻¹ : E.subgroupOf Bs)
    have hdiff : a3XHom (L := L) θ hN (x * y⁻¹) = 1 := by
      change a3XHom (L := L) θ hN ((x : ↥Bs) * (y : ↥Bs)⁻¹) = 1
      have hxy' : a3XHom (L := L) θ hN (x : ↥Bs) =
          a3XHom (L := L) θ hN (y : ↥Bs) := hxy
      rw [map_mul, map_inv, hxy']
      exact mul_inv_cancel (a3XHom (L := L) θ hN (y : ↥Bs))
    let gN : Subgroup.normalizer (L : Set G) := ⟨(b : G), hN b.2⟩
    have hgg : ggLAut L θ gN = 1 := by
      simpa [gN, b, a3XHom_apply] using hdiff
    have hcentL : (b : G) ∈ Subgroup.centralizer (L : Set G) :=
      mem_centralizer_of_ggLAut_eq_one (L := L) θ hperfL hgg
    have hcentJ : (b : G) ∈ Subgroup.centralizer (J : Set G) :=
      Subgroup.centralizer_le hJleL hcentL
    have hbot : (b : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨(x * y⁻¹).2, hcentJ⟩
    rw [hE_bot] at hbot
    have hx1 : x * y⁻¹ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [b] using hbot
    have hx1B : (x : ↥Bs) * (y : ↥Bs)⁻¹ = 1 := by
      simpa using congrArg (fun z : E.subgroupOf Bs => (z : ↥Bs)) hx1
    exact mul_inv_eq_one.mp hx1B
  have hE_sub_card : Nat.card (E.subgroupOf Bs) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_bs).toEquiv, hE_card]
  let fE : E.subgroupOf Bs → X := fun x =>
    ⟨a3XHom (L := L) θ hN x, by
      rw [hX_map]
      exact Subgroup.mem_map_of_mem (a3XHom (L := L) θ hN) x.2⟩
  have hfE_inj : Function.Injective fE := by
    intro x y hxy
    exact hinj_on_E (congrArg Subtype.val hxy)
  have hfE_surj : Function.Surjective fE := by
    intro y
    have hy : (y : MulAut (projectiveSL d F)) ∈
        (E.subgroupOf Bs).map (a3XHom (L := L) θ hN) := by
      rw [← hX_map]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [fE] using hxy)⟩
  have hX_card : Nat.card X = 27 := by
    have hbij : Function.Bijective fE := ⟨hfE_inj, hfE_surj⟩
    calc Nat.card X = Nat.card (E.subgroupOf Bs) :=
          (Nat.card_congr (Equiv.ofBijective fE hbij)).symm
      _ = 27 := hE_sub_card

  have hZ_mk_conj : ∀ j : Fin 3,
      a3ConjHom d F (ProjGenLinGroup.mk (Z j : GL (Fin d) F)) =
        a3XHom (L := L) θ hN (e j) := by
    intro j
    rw [a3ConjHom_mk, hZ_coe, map_mul, conjAut_scalar, one_mul, a3Mat_spec]
  have hprojImage_eq : CFSG.PGLModel.projImage Etilde =
      Subgroup.closure (Set.range (fun j : Fin 3 =>
        ProjGenLinGroup.mk (Z j : GL (Fin d) F))) := by
    dsimp only [CFSG.PGLModel.projImage, Etilde]
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap_eq : (CFSG.PGLModel.projImage Etilde).map (a3ConjHom d F) =
      Subgroup.closure (Set.range (fun j : Fin 3 =>
        a3ConjHom d F (ProjGenLinGroup.mk (Z j : GL (Fin d) F)))) := by
    rw [hprojImage_eq, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hEtilde_image_eq_X : (CFSG.PGLModel.projImage Etilde).map (a3ConjHom d F) = X := by
    rw [hmap_eq]
    simp only [hZ_mk_conj]
    dsimp only [X]
  have hcard_proj : 27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde) := by
    rw [← hX_card]
    let f : CFSG.PGLModel.projImage Etilde → X := fun q =>
      ⟨a3ConjHom d F q, by
        rw [← hEtilde_image_eq_X]
        exact Subgroup.mem_map_of_mem (a3ConjHom d F) q.2⟩
    have hf : Function.Surjective f := by
      intro y
      have hy : (y : MulAut (projectiveSL d F)) ∈
          (CFSG.PGLModel.projImage Etilde).map (a3ConjHom d F) := by
        rw [hEtilde_image_eq_X]
        exact y.2
      obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨q, hq⟩, Subtype.ext (by simpa [f] using hqy)⟩
    exact Nat.card_le_card_of_surjective f hf
  exact ⟨Etilde, hEtilde_le, hEtilde_elem, hcent, hcard_proj⟩

theorem a3Gp_comm_of_E27
    {G : Type} [Group G] {Bs J L : Subgroup G}
    {F : Type} [Field F] [Finite F] {d : ℕ}
    {θ : L ⧸ Subgroup.center L ≃* projectiveSL d F}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F}
    {hd : 0 < d} {hE : IsElemAbelian 3 Bs}
    {ζ : F} (hζ : IsPrimitiveRoot ζ 3)
    (Etilde : Subgroup (GL (Fin d) F)) [Finite Etilde]
    (hEtilde_le : Etilde ≤ a3Gp (L := L) θ hN)
    (hEtilde_elem : IsElemAbelian 3 Etilde)
    (hcent : ∀ e ∈ Etilde, ∀ g ∈ a3Gp (L := L) θ hN, e * g = g * e)
    (hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde))
    (hn : d < 12) :
    ∀ g ∈ a3Gp (L := L) θ hN, ∀ h ∈ a3Gp (L := L) θ hN, g * h = h * g :=
  TypeA.PGLTor.pairwise_commute_of_isProjElem_of_projective_card_ge
    (K := F) (n := d) hζ (a3Gp_isProjElem (L := L) θ hN hd hE)
    hEtilde_le hEtilde_elem hcent hcard hn

theorem a3Gp_comm_of_A3_actual
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {F : Type} [Field F] [Finite F] {d : ℕ} (hd : 0 < d)
    (θ : L ⧸ Subgroup.center L ≃* projectiveSL d F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlin : ∀ b : ↥Bs, a3XHom (L := L) θ hN b ∈ linearAutGroup d F)
    {ζ : F} (hζ : IsPrimitiveRoot ζ 3)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hn : d < 12) :
    ∀ g ∈ a3Gp (L := L) θ hN, ∀ h ∈ a3Gp (L := L) θ hN, g * h = h * g := by
  obtain ⟨Etilde, hEtilde_le, hEtilde_elem, hcent, hcard⟩ :=
    exists_E27_lifts hH hd θ hN hlin hD
  exact a3Gp_comm_of_E27 (J := J) (θ := θ) (hN := hN) (hlin := hlin) (hd := hd)
    (hE := hH.1.2.1.2.1) hζ Etilde hEtilde_le hEtilde_elem hcent hcard hn

namespace ResJSU6Scalar

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Actor

noncomputable section

variable {F : Type} [Field F] [Finite F] {n : ℕ} [Nonempty (Fin n)]
variable {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}

@[expose] def actorProj (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F) :
    Subgroup (ProjGenLinGroup (Fin n) F) := ρ.range

@[expose] def actorFull (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F) :
    Subgroup (GL (Fin n) F) :=
  (actorProj ρ).comap (ProjGenLinGroup.mk : GL (Fin n) F →* ProjGenLinGroup (Fin n) F)

theorem actorProj_isElemAbelian (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) : IsElemAbelian 3 (actorProj ρ) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hb, ← hc, ← map_mul, ← map_mul,
      hE.1.is_comm.comm b c]
  · intro x hx
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
    rw [← hb]
    have hb3 : b ^ 3 = 1 := Subtype.ext (hE.2 b b.2)
    rw [← map_pow, hb3, map_one]

theorem actorFull_isProjElem (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) : TypeA.PGLTor.IsProjElem 3 (actorFull ρ) := by
  classical
  let N : Subgroup (GL (Fin n) F) := ⊤
  let ρN : N →* ProjGenLinGroup (Fin n) F :=
    (ProjGenLinGroup.mk : GL (Fin n) F →* ProjGenLinGroup (Fin n) F).domRestrict N
  have hNscal : ∀ u : Fˣ, GeneralLinearGroup.scalar (Fin n) u ∈ N := fun _ =>
    Subgroup.mem_top _
  have hρscal : ∀ u : Fˣ, ρN ⟨GeneralLinearGroup.scalar (Fin n) u, hNscal u⟩ = 1 := by
    intro u
    simp [ρN, N, ProjGenLinGroup.mk_scalar]
  have hker : ∀ x : N, ρN x = 1 → ∃ u : Fˣ,
      (x : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) u := by
    intro x hx
    have hx' : (ProjGenLinGroup.mk (x : GL (Fin n) F) : ProjGenLinGroup (Fin n) F) = 1 := by
      simpa [ρN, N, MonoidHom.domRestrict_apply] using hx
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hx'
    obtain ⟨u, hu⟩ := hx'
    exact ⟨u, hu.symm⟩
  have hK : IsElemAbelian 3 (actorProj ρ) := actorProj_isElemAbelian ρ hE
  have hG := TypeA.PGLTor.isProjElem_comap_map_subtype (N := N) (ρ := ρN)
    hNscal hρscal hker hK
  have hmap : ((actorProj ρ).comap ρN).map N.subtype = actorFull ρ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [actorFull, ρN, N, MonoidHom.domRestrict_apply] using hx
    · intro hg
      exact ⟨⟨g, Subgroup.mem_top g⟩, by
        simpa [actorFull, ρN, N, MonoidHom.domRestrict_apply] using hg, rfl⟩
  rwa [hmap] at hG

@[expose] def actorLift (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (Y : ↥Bs → GL (Fin n) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    actorFull ρ :=
  ⟨Y b, by
    rw [actorFull, Subgroup.mem_comap, actorProj, MonoidHom.mem_range]
    exact ⟨b, (hY b).symm⟩⟩

@[simp] theorem actorLift_coe (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (Y : ↥Bs → GL (Fin n) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    ((actorLift ρ Y hY b : actorFull ρ) : GL (Fin n) F) = Y b := rfl

@[expose] def actorLam (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) : Fˣ :=
  TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
    (actorFull_isProjElem ρ hE) (actorLift ρ Y hY b)

theorem actorLam_spec (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    (Y b) ^ 3 = GeneralLinearGroup.scalar (Fin n) (actorLam ρ hE Y hY b) := by
  simpa [actorLam, actorLift_coe] using
    TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
      (actorFull_isProjElem ρ hE) (actorLift ρ Y hY b)

@[expose] def actorLamOf (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (x : actorFull ρ) : Fˣ :=
  TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
    (actorFull_isProjElem ρ hE) x

theorem actorLamOf_spec (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (x : actorFull ρ) :
    ((x : actorFull ρ) : GL (Fin n) F) ^ 3 =
      GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE x) := by
  simpa [actorLamOf] using
    TypeA.PGLTor.lam_spec (p := 3) (by norm_num) (by norm_num)
      (actorFull_isProjElem ρ hE) x

theorem actorLamOf_mul (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (x y : actorFull ρ) :
    actorLamOf ρ hE (x * y) = actorLamOf ρ hE x * actorLamOf ρ hE y := by
  simpa [actorLamOf] using
    map_mul (TypeA.PGLTor.lam (p := 3) (by norm_num) (by norm_num)
      (actorFull_isProjElem ρ hE)) x y

theorem actorLam_eq (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    actorLam ρ hE Y hY b = actorLamOf ρ hE (actorLift ρ Y hY b) := rfl

theorem actorScalar_mem (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F) (z : Fˣ) :
    GeneralLinearGroup.scalar (Fin n) z ∈ actorFull ρ := by
  rw [actorFull, Subgroup.mem_comap, actorProj]
  rw [ProjGenLinGroup.mk_scalar]
  exact Subgroup.one_mem _

theorem actorLamOf_scalar (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (z : Fˣ) :
    actorLamOf ρ hE ⟨GeneralLinearGroup.scalar (Fin n) z, actorScalar_mem ρ z⟩ = z ^ 3 := by
  apply TypeA.PGLTor.scalar_injective (ι := Fin n)
  rw [← actorLamOf_spec]
  change (GeneralLinearGroup.scalar (Fin n) z) ^ 3 =
    GeneralLinearGroup.scalar (Fin n) (z ^ 3)
  rw [← map_pow]

theorem actorLamOf_scalar_mul (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (a b : actorFull ρ) (z : Fˣ)
    (h : (a : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) z * (b : GL (Fin n) F)) :
    actorLamOf ρ hE a = z ^ 3 * actorLamOf ρ hE b := by
  apply TypeA.PGLTor.scalar_injective (ι := Fin n)
  rw [← actorLamOf_spec]
  have hcube : ((a : GL (Fin n) F)) ^ 3 =
      GeneralLinearGroup.scalar (Fin n) (z ^ 3 * actorLamOf ρ hE b) := by
    rw [h]
    calc (GeneralLinearGroup.scalar (Fin n) z * (b : GL (Fin n) F)) ^ 3
        = (GeneralLinearGroup.scalar (Fin n) z) ^ 3 * (b : GL (Fin n) F) ^ 3 := by
            exact (Commute.mul_pow
              (TypeA.PGLTor.scalar_mul_comm z (b : GL (Fin n) F))) 3
      _ = GeneralLinearGroup.scalar (Fin n) (z ^ 3) *
            GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE b) := by
            rw [← map_pow, actorLamOf_spec]
      _ = GeneralLinearGroup.scalar (Fin n) (z ^ 3 * actorLamOf ρ hE b) := by
            rw [← map_mul]
  rw [hcube]

theorem actorLamOf_conj (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (A : GL (Fin n) F) (x : actorFull ρ)
    (hx : A * (x : GL (Fin n) F) * A⁻¹ ∈ actorFull ρ) :
    actorLamOf ρ hE ⟨A * (x : GL (Fin n) F) * A⁻¹, hx⟩ =
      actorLamOf ρ hE x := by
  apply TypeA.PGLTor.scalar_injective (ι := Fin n)
  rw [← actorLamOf_spec]
  calc (A * (x : GL (Fin n) F) * A⁻¹) ^ 3
      = A * (x : GL (Fin n) F) ^ 3 * A⁻¹ := by
        simp only [pow_three]
        group
    _ = A * GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE x) * A⁻¹ := by
        rw [actorLamOf_spec]
    _ = GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE x) := by
        rw [show A * GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE x) =
            GeneralLinearGroup.scalar (Fin n) (actorLamOf ρ hE x) * A from
          (TypeA.PGLTor.scalar_mul_comm _ A).symm]
        group

theorem actorLift_mul_scalar (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (Y : ↥Bs → GL (Fin n) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b c : ↥Bs) :
    ∃ z : Fˣ, Y (b * c) =
      GeneralLinearGroup.scalar (Fin n) z * (Y b * Y c) := by
  have h : ProjGenLinGroup.mk (Y (b * c) * (Y b * Y c)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hY]
    group
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  calc Y (b * c) = (Y (b * c) * (Y b * Y c)⁻¹) * (Y b * Y c) := by group
    _ = GeneralLinearGroup.scalar (Fin n) z * (Y b * Y c) := by rw [← hz]

@[expose] def actorPair (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b c : ↥Bs) : Fˣ :=
  TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
    (actorLift ρ Y hY b).2 (actorLift ρ Y hY c)

@[expose] def actorPairR (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b c : ↥Bs) : rootsOfUnity 3 F :=
  ⟨actorPair ρ hE Y hY b c,
    (mem_rootsOfUnity 3 _).mpr
      (TypeA.PGLTor.commChar_pow_eq_one (actorFull_isProjElem ρ hE)
        (actorLift ρ Y hY b).2 (actorLift ρ Y hY c))⟩

theorem actorLift_one_scalar (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (Y : ↥Bs → GL (Fin n) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    ∃ z : Fˣ, Y 1 = GeneralLinearGroup.scalar (Fin n) z := by
  have h : ProjGenLinGroup.mk (Y 1) = 1 := by rw [hY, map_one]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp h
  exact ⟨z, hz.symm⟩

theorem actorPair_one_right (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    actorPair ρ hE Y hY b 1 = 1 := by
  obtain ⟨z, hz⟩ := actorLift_one_scalar ρ Y hY
  simpa [actorPair, actorLift] using
    TypeA.PGLTor.commChar_eq_one_of_scalar_arg (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b).2 hz

theorem actorPair_one_left (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (c : ↥Bs) :
    actorPair ρ hE Y hY 1 c = 1 := by
  obtain ⟨z, hz⟩ := actorLift_one_scalar ρ Y hY
  simpa [actorPair, actorLift] using
    TypeA.PGLTor.commChar_eq_one_of_scalar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY 1).2 hz (actorLift ρ Y hY c)

theorem actorPair_self (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    actorPair ρ hE Y hY b b = 1 := by
  simpa [actorPair] using
    (TypeA.PGLTor.commChar_eq_one_iff (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b).2 (actorLift ρ Y hY b)).mpr rfl

theorem actorPair_mul_right (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b c d : ↥Bs) :
    actorPair ρ hE Y hY b (c * d) =
      actorPair ρ hE Y hY b c * actorPair ρ hE Y hY b d := by
  obtain ⟨z, hz⟩ := actorLift_mul_scalar ρ Y hY c d
  have hz' : (actorLift ρ Y hY (c * d) : GL (Fin n) F) =
      GeneralLinearGroup.scalar (Fin n) z *
        ((actorLift ρ Y hY c * actorLift ρ Y hY d : actorFull ρ) : GL (Fin n) F) := by
    simpa [Subgroup.coe_mul] using hz
  have hstep := TypeA.PGLTor.commChar_eq_of_eq_scalar_mul_arg
    (actorFull_isProjElem ρ hE) (ha := (actorLift ρ Y hY b).2)
    (x := actorLift ρ Y hY c * actorLift ρ Y hY d)
    (x' := actorLift ρ Y hY (c * d)) hz'
  change TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b).2 (actorLift ρ Y hY (c * d)) =
    TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b).2 (actorLift ρ Y hY c) *
    TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b).2 (actorLift ρ Y hY d)
  rw [hstep]
  exact map_mul (TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
    (actorLift ρ Y hY b).2) (actorLift ρ Y hY c) (actorLift ρ Y hY d)

theorem actorPair_mul_left (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b₁ b₂ c : ↥Bs) :
    actorPair ρ hE Y hY (b₁ * b₂) c =
      actorPair ρ hE Y hY b₁ c * actorPair ρ hE Y hY b₂ c := by
  obtain ⟨z, hz⟩ := actorLift_mul_scalar ρ Y hY b₁ b₂
  have hz' : (actorLift ρ Y hY (b₁ * b₂) : GL (Fin n) F) =
      GeneralLinearGroup.scalar (Fin n) z *
        ((actorLift ρ Y hY b₁ * actorLift ρ Y hY b₂ : actorFull ρ) : GL (Fin n) F) := by
    simpa [Subgroup.coe_mul] using hz
  have hstep := TypeA.PGLTor.commChar_eq_of_eq_scalar_mul
    (actorFull_isProjElem ρ hE)
    (a := ((actorLift ρ Y hY b₁ * actorLift ρ Y hY b₂ : actorFull ρ) : GL (Fin n) F))
    (a' := (actorLift ρ Y hY (b₁ * b₂) : GL (Fin n) F))
    (ha := mul_mem (actorLift ρ Y hY b₁).2 (actorLift ρ Y hY b₂).2)
    (ha' := (actorLift ρ Y hY (b₁ * b₂)).2) (z := z) hz'
    (actorLift ρ Y hY c)
  change TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY (b₁ * b₂)).2 (actorLift ρ Y hY c) =
    TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b₁).2 (actorLift ρ Y hY c) *
    TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ Y hY b₂).2 (actorLift ρ Y hY c)
  rw [hstep]
  exact TypeA.PGLTor.commChar_mul_left (actorFull_isProjElem ρ hE)
    (actorLift ρ Y hY b₁).2 (actorLift ρ Y hY b₂).2 (actorLift ρ Y hY c)

@[expose] def actorChiFun (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b : ↥Bs) :
    TypeA.PGLTor.PowQuot F 3 :=
  QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (actorLam ρ hE Y hY b)


theorem actorChiFun_one (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    actorChiFun ρ hE Y hY 1 = 1 := by
  obtain ⟨z, hz⟩ := actorLift_one_scalar ρ Y hY
  have hlift : actorLift ρ Y hY 1 = ⟨GeneralLinearGroup.scalar (Fin n) z,
      actorScalar_mem ρ z⟩ := Subtype.ext hz
  change QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
    (actorLamOf ρ hE (actorLift ρ Y hY 1)) = 1
  rw [hlift, actorLamOf_scalar]
  change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
    TypeA.PGLTor.PowQuot F 3) = 1
  rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
  exact ⟨z, rfl⟩

theorem actorChiFun_mul (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) (b c : ↥Bs) :
    actorChiFun ρ hE Y hY (b * c) =
      actorChiFun ρ hE Y hY b * actorChiFun ρ hE Y hY c := by
  obtain ⟨z, hz⟩ := actorLift_mul_scalar ρ Y hY b c
  let x : actorFull ρ :=
    ⟨GeneralLinearGroup.scalar (Fin n) z *
        ((actorLift ρ Y hY b * actorLift ρ Y hY c : actorFull ρ) : GL (Fin n) F),
      mul_mem (actorScalar_mem ρ z)
        (mul_mem (actorLift ρ Y hY b).2 (actorLift ρ Y hY c).2)⟩
  have hx : (actorLift ρ Y hY (b * c) : actorFull ρ) = x := by
    apply Subtype.ext
    simpa [x, Subgroup.coe_mul] using hz
  change QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
    (actorLamOf ρ hE (actorLift ρ Y hY (b * c))) =
    QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLamOf ρ hE (actorLift ρ Y hY b)) *
    QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLamOf ρ hE (actorLift ρ Y hY c))
  rw [hx]
  change QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
    (actorLamOf ρ hE x) = _
  have hxlam : actorLamOf ρ hE x =
      z ^ 3 * (actorLamOf ρ hE (actorLift ρ Y hY b) *
        actorLamOf ρ hE (actorLift ρ Y hY c)) := by
    rw [actorLamOf_scalar_mul ρ hE x
      (actorLift ρ Y hY b * actorLift ρ Y hY c) z (by rfl)]
    rw [actorLamOf_mul]
  rw [hxlam]
  rw [map_mul, map_mul]
  have hz3 : QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) = 1 := by
    change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
      TypeA.PGLTor.PowQuot F 3) = 1
    rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨z, rfl⟩
  rw [hz3, one_mul]

@[expose] def actorChi (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    ↥Bs →* TypeA.PGLTor.PowQuot F 3 where
  toFun := actorChiFun ρ hE Y hY
  map_one' := actorChiFun_one ρ hE Y hY
  map_mul' := actorChiFun_mul ρ hE Y hY


theorem actorFull_comm_of_E27 (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) {ζ : F} (hζ : IsPrimitiveRoot ζ 3)
    (Etilde : Subgroup (GL (Fin n) F)) [Finite Etilde]
    (hEtilde_le : Etilde ≤ actorFull ρ)
    (hEtilde_elem : IsElemAbelian 3 Etilde)
    (hcent : ∀ e ∈ Etilde, ∀ g ∈ actorFull ρ, e * g = g * e)
    (hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde))
    (hn : n < 12) :
    ∀ g ∈ actorFull ρ, ∀ h ∈ actorFull ρ, g * h = h * g :=
  TypeA.PGLTor.pairwise_commute_of_isProjElem_of_projective_card_ge
    (K := F) (n := n) hζ (actorFull_isProjElem ρ hE)
    hEtilde_le hEtilde_elem hcent hcard hn

theorem actorLift_comm_of_E27 (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ 3)
    (Etilde : Subgroup (GL (Fin n) F)) [Finite Etilde]
    (hEtilde_le : Etilde ≤ actorFull ρ)
    (hEtilde_elem : IsElemAbelian 3 Etilde)
    (hcent : ∀ e ∈ Etilde, ∀ g ∈ actorFull ρ, e * g = g * e)
    (hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde))
    (hn : n < 12) (b c : ↥Bs) :
    Y b * Y c = Y c * Y b := by
  have h := actorFull_comm_of_E27 ρ hE hζ Etilde hEtilde_le hEtilde_elem
    hcent hcard hn (actorLift ρ Y hY b : GL (Fin n) F) (actorLift ρ Y hY b).2
      (actorLift ρ Y hY c : GL (Fin n) F) (actorLift ρ Y hY c).2
  simpa [actorLift, Subgroup.coe_mul] using h


theorem actorChi_coroot_eq_one (ρ : ↥Bs →* ProjGenLinGroup (Fin n) F)
    (hE : IsElemAbelian 3 Bs) (Y : ↥Bs → GL (Fin n) F)
    (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {k : ℕ}
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (hχinv : ∀ φ ∈ ggAutomizer J Bs, ∀ b : ↥Bs,
      actorChi ρ hE Y hY (φ b) = actorChi ρ hE Y hY b)
    (j : Fin k) :
    actorChi ρ hE Y hY (Additive.toMul (ι.symm (h j))) = 1 := by
  have hkill := ggCharacter_apply_corootSpan (J := J) ι r h α hform hα2 hgen
    (C := TypeA.PGLTor.PowQuot F 3) (fun c => powQuot_pow_three (F := F) c)
    (actorChi ρ hE Y hY) hχinv
  exact hkill (h j) (Submodule.subset_span (Set.mem_range_self j))


end

end Actor

open Actor

noncomputable section

abbrev u6 (F : Type) [Field F] (n : ℕ) : Subgroup (GL (Fin 6) F) :=
  LargeEvenSUGroup (Fin 6) F (2 ^ n)

abbrev p6 (F : Type) [Field F] (n : ℕ) : Type :=
  LargeEvenProj (u6 F n)

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
variable {F : Type} [Field F] [Finite F] {n : ℕ}
variable {θ : ↥J ⧸ Subgroup.center ↥J ≃* p6 F n}
variable {hN : Bs ≤ Subgroup.normalizer (J : Set G)}
variable {ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F}
variable {A : ↥Bs → GL (Fin 6) F}
variable {hAnorm : ∀ b, A b ∈ Subgroup.normalizer (u6 F n : Set (GL (Fin 6) F))}
variable {hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
  ggBeta J θ hN b}
variable {hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b}

theorem exists_SU6_rep (θ : ↥J ⧸ Subgroup.center ↥J ≃* p6 F n)
    {g : G} (hgJ : g ∈ J) :
    ∃ gSU : u6 F n, LargeEvenProjMk (u6 F n) gSU =
      ggQuotHom θ (⟨g, hgJ⟩ : ↥J) :=
  QuotientGroup.mk'_surjective _ _

theorem actor_eq_scalar_conj
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    {g : G} (hgJ : g ∈ J) (hgBN : g ∈ Subgroup.normalizer (Bs : Set G))
    (φ : MulAut ↥Bs) (hgact : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    (gSU : u6 F n) (hgSU : LargeEvenProjMk (u6 F n) gSU =
      ggQuotHom θ (⟨g, hgJ⟩ : ↥J))
    (b : ↥Bs) :
    ∃ z : Fˣ, A (φ b) = GeneralLinearGroup.scalar (Fin 6) z *
      ((gSU : GL (Fin 6) F) * A b * ((gSU : GL (Fin 6) F))⁻¹) := by
  classical
  let gJ : ↥J := ⟨g, hgJ⟩
  let gN : Subgroup.normalizer (J : Set G) := ⟨g, Subgroup.le_normalizer hgJ⟩
  let bN : Subgroup.normalizer (J : Set G) := ⟨b, hN b.2⟩
  let fbN : Subgroup.normalizer (J : Set G) := ⟨φ b, hN (φ b).2⟩
  have hfbN : fbN = gN * bN * gN⁻¹ := by
    apply Subtype.ext
    show ((φ b : ↥Bs) : G) = g * (b : G) * g⁻¹
    exact hgact b
  have hgg : ggLAut J θ gN = MulAut.conj (ggQuotHom θ gJ) := by
    simpa [gJ, gN] using
      ggLAut_of_mem (L := J) θ gJ (Subgroup.le_normalizer hgJ)
  have hbeta : ggBeta J θ hN (φ b) =
      MulAut.conj (ggQuotHom θ gJ) * ggBeta J θ hN b *
        (MulAut.conj (ggQuotHom θ gJ))⁻¹ := by
    change ggLAut J θ fbN = MulAut.conj (ggQuotHom θ gJ) * ggLAut J θ bN *
      (MulAut.conj (ggQuotHom θ gJ))⁻¹
    rw [hfbN, ← ggLAut_conj, hgg]
  let X : GL (Fin 6) F := (gSU : GL (Fin 6) F) * A b * ((gSU : GL (Fin 6) F))⁻¹
  have hXmem : X ∈ Subgroup.normalizer (u6 F n : Set (GL (Fin 6) F)) := by
    exact mul_mem (mul_mem (Subgroup.le_normalizer gSU.2) (hAnorm b))
      (inv_mem (Subgroup.le_normalizer gSU.2))
  have hXproj : TableB.projConj (u6 F n) ⟨X, hXmem⟩ = ggBeta J θ hN (φ b) := by
    calc TableB.projConj (u6 F n) ⟨X, hXmem⟩
        = TableB.projConj (u6 F n) ⟨(gSU : GL (Fin 6) F), Subgroup.le_normalizer gSU.2⟩ *
            TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ *
            (TableB.projConj (u6 F n) ⟨(gSU : GL (Fin 6) F), Subgroup.le_normalizer gSU.2⟩)⁻¹ := by
          rw [show (⟨X, hXmem⟩ : Subgroup.normalizer (u6 F n : Set (GL (Fin 6) F))) =
              ⟨(gSU : GL (Fin 6) F), Subgroup.le_normalizer gSU.2⟩ *
                ⟨A b, hAnorm b⟩ *
                (⟨(gSU : GL (Fin 6) F), Subgroup.le_normalizer gSU.2⟩)⁻¹ from Subtype.ext rfl,
            map_mul, map_mul, map_inv]
      _ = MulAut.conj (ggQuotHom θ gJ) * ggBeta J θ hN b *
            (MulAut.conj (ggQuotHom θ gJ))⁻¹ := by
          rw [TableB.projConj_of_mem (u6 F n) (gSU : GL (Fin 6) F) gSU.2]
          change MulAut.conj (LargeEvenProjMk (u6 F n) gSU) *
              TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ *
              (MulAut.conj (LargeEvenProjMk (u6 F n) gSU))⁻¹ = _
          rw [hgSU, hAproj b]
      _ = ggBeta J θ hN (φ b) := hbeta.symm
  have hM : TableB.projConj (u6 F n)
      ⟨A (φ b) * X⁻¹,
        mul_mem (hAnorm (φ b)) (inv_mem hXmem)⟩ = 1 := by
    change TableB.projConj (u6 F n)
      (⟨A (φ b), hAnorm (φ b)⟩ *
        (⟨X, hXmem⟩ : Subgroup.normalizer (u6 F n : Set (GL (Fin 6) F)))⁻¹) = 1
    rw [map_mul, map_inv, hAproj (φ b), hXproj, mul_inv_cancel]
  let hU : UnitaryFieldData 2 n F := TableBU.unitaryFieldData_of_card hFcard hn
  have hdq : (6, 2 ^ n) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  have hscal : (A (φ b) * X⁻¹ : GL (Fin 6) F) ∈ LargeEvenScalars (Fin 6) F :=
    TableBUE.mem_scalars_of_projConj_eq_one (h := hU) hFcard (by norm_num) hdq
      Nat.prime_three hpq hM
  rw [largeEvenScalars_def] at hscal
  obtain ⟨z, hz⟩ := hscal
  refine ⟨z, ?_⟩
  calc A (φ b) = (A (φ b) * X⁻¹) * X := by group
    _ = GeneralLinearGroup.scalar (Fin 6) z * X := by rw [← hz]

theorem actorProj_equivariance
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b)
    {g : G} (hgJ : g ∈ J) (hgBN : g ∈ Subgroup.normalizer (Bs : Set G))
    (φ : MulAut ↥Bs) (hgact : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    (gSU : u6 F n) (hgSU : LargeEvenProjMk (u6 F n) gSU =
      ggQuotHom θ (⟨g, hgJ⟩ : ↥J))
    (b : ↥Bs) :
    ρ (φ b) = ProjGenLinGroup.mk (gSU : GL (Fin 6) F) * ρ b *
      (ProjGenLinGroup.mk (gSU : GL (Fin 6) F))⁻¹ := by
  obtain ⟨z, hz⟩ := actor_eq_scalar_conj (F := F) (n := n) hFcard hn hpq hAproj
    hgJ hgBN φ hgact gSU hgSU b
  rw [← hmk (φ b), hz]
  simp only [map_mul, map_inv, ProjGenLinGroup.mk_scalar, hmk b, one_mul]

theorem actorChi_invariant_of_induced
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced J Bs) :
    ∀ b : ↥Bs, actorChi ρ (hH.1.2.1.2.1) A hmk (φ b) =
      actorChi ρ (hH.1.2.1.2.1) A hmk b := by
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  rcases hφ with ⟨g, hgJ, hgBN, hgact⟩
  obtain ⟨gSU, hgSU⟩ := exists_SU6_rep (F := F) (n := n) θ hgJ
  intro b
  obtain ⟨z, hz⟩ := actor_eq_scalar_conj (F := F) (n := n) hFcard hn hpq hAproj
    hgJ hgBN φ hgact gSU hgSU b
  let X : GL (Fin 6) F := (gSU : GL (Fin 6) F) * A b * ((gSU : GL (Fin 6) F))⁻¹
  have hXmem : X ∈ actorFull ρ := by
    have hscalar : GeneralLinearGroup.scalar (Fin 6) z⁻¹ ∈ actorFull ρ :=
      actorScalar_mem ρ z⁻¹
    have hphi : A (φ b) ∈ actorFull ρ := (actorLift ρ A hmk (φ b)).2
    have hEq : X = GeneralLinearGroup.scalar (Fin 6) z⁻¹ * A (φ b) := by
      rw [hz, map_inv]
      simp only [X]
      group
    rw [hEq]
    exact mul_mem hscalar hphi
  have hlam_scalar : actorLamOf ρ hE (actorLift ρ A hmk (φ b)) =
      z ^ 3 * actorLamOf ρ hE ⟨X, hXmem⟩ := by
    rw [actorLamOf_scalar_mul ρ hE (actorLift ρ A hmk (φ b)) ⟨X, hXmem⟩ z]
    exact hz
  have hlam_conj : actorLamOf ρ hE ⟨X, hXmem⟩ =
      actorLamOf ρ hE (actorLift ρ A hmk b) := by
    simpa [X] using actorLamOf_conj ρ hE (gSU : GL (Fin 6) F)
      (actorLift ρ A hmk b) hXmem
  have hlam : actorLamOf ρ hE (actorLift ρ A hmk (φ b)) =
      z ^ 3 * actorLamOf ρ hE (actorLift ρ A hmk b) := by
    rw [hlam_scalar, hlam_conj]
  change QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLam ρ hE A hmk (φ b)) =
    QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLam ρ hE A hmk b)
  change QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLamOf ρ hE (actorLift ρ A hmk (φ b))) =
    QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range)
      (actorLamOf ρ hE (actorLift ρ A hmk b))
  rw [hlam]
  rw [map_mul]
  have hz3 : QuotientGroup.mk' ((powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) = 1 := by
    change (QuotientGroup.mk (s := (powMonoidHom 3 : Fˣ →* Fˣ).range) (z ^ 3) :
      TypeA.PGLTor.PowQuot F 3) = 1
    rw [TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨z, rfl⟩
  rw [hz3, one_mul]

@[expose] def actorChiPres
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    Subgroup (MulAut ↥Bs) where
  carrier := {φ | ∀ b : ↥Bs,
    actorChi ρ hE Y hY (φ b) = actorChi ρ hE Y hY b}
  one_mem' := by intro b; rfl
  mul_mem' := by
    intro φ ψ hφ hψ b
    rw [MulAut.mul_apply, hφ, hψ]
  inv_mem' := by
    intro φ hφ b
    have h := hφ (φ⁻¹ b)
    simpa using h.symm

theorem actorChi_invariant (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b) :
    ggAutomizer J Bs ≤ actorChiPres (F := F) ρ hH.1.2.1.2.1 A hmk := by
  rw [ggAutomizer, Subgroup.closure_le]
  intro φ hφ
  exact actorChi_invariant_of_induced (F := F) (n := n) (θ := θ) (hN := hN)
    (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
    hH hFcard hn hpq hAproj hφ


theorem actorFull_of_eq_scalar_mul {X : GL (Fin 6) F} {b : ↥Bs} {z : Fˣ}
    (hb : A b ∈ actorFull ρ) (h : A b = GeneralLinearGroup.scalar (Fin 6) z * X) :
    X ∈ actorFull ρ := by
  rw [h] at hb
  have hmem := mul_mem (actorScalar_mem ρ z⁻¹) hb
  convert hmem using 1
  rw [map_inv]
  group

theorem actorPair_invariant_of_induced
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced J Bs) (b c : ↥Bs) :
    actorPair ρ (hH.1.2.1.2.1) A hmk (φ b) (φ c) =
      actorPair ρ (hH.1.2.1.2.1) A hmk b c := by
  classical
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  rcases hφ with ⟨g, hgJ, hgBN, hgact⟩
  obtain ⟨gSU, hgSU⟩ := exists_SU6_rep (F := F) (n := n) θ hgJ
  obtain ⟨zb, hzb⟩ := actor_eq_scalar_conj (F := F) (n := n) hFcard hn hpq hAproj
    hgJ hgBN φ hgact gSU hgSU b
  obtain ⟨zc, hzc⟩ := actor_eq_scalar_conj (F := F) (n := n) hFcard hn hpq hAproj
    hgJ hgBN φ hgact gSU hgSU c
  let Xb : GL (Fin 6) F := (gSU : GL (Fin 6) F) * A b * ((gSU : GL (Fin 6) F))⁻¹
  let Xc : GL (Fin 6) F := (gSU : GL (Fin 6) F) * A c * ((gSU : GL (Fin 6) F))⁻¹
  have hXbmem : Xb ∈ actorFull ρ :=
    actorFull_of_eq_scalar_mul (ρ := ρ) (A := A) (b := φ b) (z := zb)
      (actorLift ρ A hmk (φ b)).2 (by simpa [Xb] using hzb)
  have hXcmem : Xc ∈ actorFull ρ :=
    actorFull_of_eq_scalar_mul (ρ := ρ) (A := A) (b := φ c) (z := zc)
      (actorLift ρ A hmk (φ c)).2 (by simpa [Xc] using hzc)
  have h1 : actorPair ρ hE A hmk (φ b) (φ c) =
      TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE) hXbmem
        (actorLift ρ A hmk (φ c)) := by
    change TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
      (actorLift ρ A hmk (φ b)).2 (actorLift ρ A hmk (φ c)) = _
    exact TypeA.PGLTor.commChar_eq_of_eq_scalar_mul (actorFull_isProjElem ρ hE)
      hXbmem (actorLift ρ A hmk (φ b)).2 (z := zb)
      (by simpa [Xb] using hzb) (actorLift ρ A hmk (φ c))
  have h2 : TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE) hXbmem
        (actorLift ρ A hmk (φ c)) =
      TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE) hXbmem ⟨Xc, hXcmem⟩ := by
    exact TypeA.PGLTor.commChar_eq_of_eq_scalar_mul_arg (actorFull_isProjElem ρ hE)
      hXbmem (x := ⟨Xc, hXcmem⟩) (x' := actorLift ρ A hmk (φ c)) (z := zc)
      (by simpa [Xc] using hzc)
  have h3 : TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE) hXbmem ⟨Xc, hXcmem⟩ =
      TypeA.PGLTor.commChar (actorFull_isProjElem ρ hE)
        (actorLift ρ A hmk b).2 (actorLift ρ A hmk c) :=
    TypeA.PGLTor.commChar_conj (actorFull_isProjElem ρ hE)
      (actorLift ρ A hmk b).2 (actorLift ρ A hmk c).2 hXbmem hXcmem
  change actorPair ρ hE A hmk (φ b) (φ c) = actorPair ρ hE A hmk b c
  rw [h1, h2, h3]
  rfl

@[expose] def actorPairPres
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    Subgroup (MulAut ↥Bs) where
  carrier := {φ | ∀ b c : ↥Bs,
    actorPair ρ hE Y hY (φ b) (φ c) = actorPair ρ hE Y hY b c}
  one_mem' := by intro b c; rfl
  mul_mem' := by
    intro φ ψ hφ hψ b c
    change actorPair ρ hE Y hY (φ (ψ b)) (φ (ψ c)) =
      actorPair ρ hE Y hY b c
    rw [hφ, hψ]
  inv_mem' := by
    intro φ hφ b c
    have h := hφ (φ⁻¹ b) (φ⁻¹ c)
    simpa using h.symm

theorem actorPair_invariant (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b) :
    ggAutomizer J Bs ≤ actorPairPres (F := F) ρ hH.1.2.1.2.1 A hmk := by
  rw [ggAutomizer, Subgroup.closure_le]
  intro φ hφ
  exact actorPair_invariant_of_induced (F := F) (n := n) (θ := θ) (hN := hN)
    (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
    hH hFcard hn hpq hAproj hφ

theorem actorPairR_invariant
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer J Bs) (b c : ↥Bs) :
    actorPairR ρ hH.1.2.1.2.1 A hmk (φ b) (φ c) =
      actorPairR ρ hH.1.2.1.2.1 A hmk b c := by
  have hpres := actorPair_invariant (F := F) (n := n) (θ := θ) (hN := hN)
    (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk) hH hFcard hn hpq hAproj
  exact Subtype.ext (hpres hφ b c)


@[expose] noncomputable def actorPairRightHom
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    (b : ↥Bs) : ↥Bs →* rootsOfUnity 3 F where
  toFun c := actorPairR ρ hE Y hY b c
  map_one' := Subtype.ext (actorPair_one_right ρ hE Y hY b)
  map_mul' c d := Subtype.ext (actorPair_mul_right ρ hE Y hY b c d)

@[expose] noncomputable def actorPairFirstHom
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    ↥Bs →* (↥Bs →* rootsOfUnity 3 F) where
  toFun b := actorPairRightHom ρ hE Y hY b
  map_one' := MonoidHom.ext (fun c => Subtype.ext (actorPair_one_left ρ hE Y hY c))
  map_mul' b₁ b₂ := MonoidHom.ext
    (fun c => Subtype.ext (actorPair_mul_left ρ hE Y hY b₁ b₂ c))

section Additive

variable [IsMulCommutative ↥Bs]

local instance actorAddCommGroup : AddCommGroup (Additive ↥Bs) :=
  { (Additive.addGroup : AddGroup (Additive ↥Bs)) with
    add_comm := fun a b =>
      congrArg Additive.ofMul
        (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

@[expose] noncomputable def actorPairAdd
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b) :
    Additive ↥Bs →+ Additive ↥Bs →+ Additive (rootsOfUnity 3 F) where
  toFun x := (actorPairRightHom ρ hE Y hY (Additive.toMul x)).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    change actorPair ρ hE Y hY (Additive.toMul (0 : Additive ↥Bs))
      (Additive.toMul y) = 1
    rw [show Additive.toMul (0 : Additive ↥Bs) = (1 : ↥Bs) from rfl,
      actorPair_one_left ρ hE Y hY (Additive.toMul y)]
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    change actorPair ρ hE Y hY (Additive.toMul (x + y)) (Additive.toMul z) =
      actorPair ρ hE Y hY (Additive.toMul x) (Additive.toMul z) *
        actorPair ρ hE Y hY (Additive.toMul y) (Additive.toMul z)
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
      actorPair_mul_left ρ hE Y hY (Additive.toMul x) (Additive.toMul y)
        (Additive.toMul z)]

theorem actorPairAdd_ofMul
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    (x y : ↥Bs) :
    actorPairAdd ρ hE Y hY (Additive.ofMul x) (Additive.ofMul y) =
      Additive.ofMul (actorPairR ρ hE Y hY x y) := rfl

theorem actorPairAdd_self
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    (x : Additive ↥Bs) :
    actorPairAdd ρ hE Y hY x x = 0 := by
  apply Subtype.ext
  change actorPair ρ hE Y hY (Additive.toMul x) (Additive.toMul x) = 1
  rw [actorPair_self]

theorem actorPairAdd_apply
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    (x y : Additive ↥Bs) :
    actorPairAdd ρ hE Y hY x y =
      Additive.ofMul (actorPairR ρ hE Y hY
        (Additive.toMul x) (Additive.toMul y)) := rfl

section PairingV

variable [Module (ZMod 3) (Additive ↥Bs)]
  [Module (ZMod 3) (Additive (rootsOfUnity 3 F))]

theorem actorAddEquiv_smul {A : Type} [AddCommGroup A] [Module (ZMod 3) A]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : A ≃+ V) (c : ZMod 3) (x : A) : ι (c • x) = c • ι x := by
  have hc : c = ((c.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val c).symm
  rw [hc, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

@[expose] noncomputable def actorPairV
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) := by
  classical
  let pairInnerFun (x : Additive ↥Bs) :
      Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) :=
    { toFun := actorPairAdd ρ hE Y hY x
      map_add' := fun y z => map_add (actorPairAdd ρ hE Y hY x) y z
      map_smul' := fun c y =>
        ZMod.map_smul (actorPairAdd ρ hE Y hY x) c y }
  let pairInner : Additive ↥Bs →+
      (Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) :=
    AddMonoidHom.mk' pairInnerFun (by
      intro x y
      apply LinearMap.ext
      intro z
      change actorPairAdd ρ hE Y hY (x + y) z =
        actorPairAdd ρ hE Y hY x z + actorPairAdd ρ hE Y hY y z
      rw [map_add]
      rfl)
  let pairA : Additive ↥Bs →ₗ[ZMod 3]
      (Additive ↥Bs →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) :=
    pairInner.toZModLinearMap 3
  let pairRight : V → (V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F)) := fun u =>
    { toFun := fun v => pairA (ι.symm u) (ι.symm v)
      map_add' := by
        intro v₁ v₂
        rw [map_add, map_add]
      map_smul' := by
        intro c v
        rw [actorAddEquiv_smul ι.symm c v]
        exact map_smul (pairA (ι.symm u)) c (ι.symm v) }
  have hzero : pairRight 0 = 0 := by
    ext v
    simp [pairRight]
  have hadd : ∀ u u', pairRight (u + u') = pairRight u + pairRight u' := by
    intro u u'
    ext v
    simp [pairRight, map_add]
  exact ({ toFun := pairRight, map_zero' := hzero, map_add' := hadd } :
    V →+ (V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F))).toZModLinearMap 3

theorem actorPairV_apply
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (u v : V) :
    actorPairV ρ hE Y hY ι u v =
      actorPairAdd ρ hE Y hY (ι.symm u) (ι.symm v) := by
  unfold actorPairV
  rfl

theorem actorPairV_isAlt
    (ρ : ↥Bs →* ProjGenLinGroup (Fin 6) F) (hE : IsElemAbelian 3 Bs)
    (Y : ↥Bs → GL (Fin 6) F) (hY : ∀ b, ProjGenLinGroup.mk (Y b) = ρ b)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    (actorPairV ρ hE Y hY ι).IsAlt := by
  intro u
  rw [actorPairV_apply]
  exact actorPairAdd_self ρ hE Y hY (ι.symm u)

theorem actorPairV_invariant
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    ∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
      actorPairV ρ hE A hmk ι (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) =
        actorPairV ρ hE A hmk ι u v := by
  intro φ hφ u v
  have hpres : φ ∈ actorPairPres (F := F) ρ hE A hmk :=
    actorPair_invariant (F := F) (n := n) (θ := θ) (hN := hN) (ρ := ρ)
      (A := A) (hAnorm := hAnorm) (hmk := hmk) hH hFcard hn hpq hAproj hφ
  have hbc := hpres (Additive.toMul (ι.symm u)) (Additive.toMul (ι.symm v))
  rw [actorPairV_apply, actorPairV_apply, ggLin_apply, ggLin_apply,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact congrArg Additive.ofMul (Subtype.ext hbc)

theorem actorPair_coroot_eq_one_of_diag
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {k : ℕ}
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin k) (c : ↥Bs) :
    actorPair ρ hE A hmk (Additive.toMul (ι.symm (h j))) c = 1 := by
  classical
  let β : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) :=
    actorPairV ρ hE A hmk ι
  have hβalt : β.IsAlt := actorPairV_isAlt ρ hE A hmk ι
  have hβinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v : V,
      β (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = β u v :=
    actorPairV_invariant hH hFcard hn hpq hAproj hE ι
  obtain ⟨hvan, -, -⟩ :=
    GGResLineJDatum.coroot_span_le_ker_of_diag_two ι r h α hform hα2 hind hgen β hβalt hβinv
  have h0 := congrArg
    (fun f : V →ₗ[ZMod 3] Additive (rootsOfUnity 3 F) => f (ι (Additive.ofMul c)))
    (hvan j)
  rw [actorPairV_apply, actorPairAdd_apply] at h0
  apply Additive.ofMul.injective
  have h1 : actorPairR ρ hE A hmk
      (Additive.toMul (ι.symm (h j))) c = 1 := by
    simpa only [toMul_ofMul, toMul_zero, AddEquiv.symm_apply_apply,
      LinearMap.zero_apply] using congrArg Additive.toMul h0
  simpa [actorPairR] using congrArg Subtype.val h1

theorem actorPair_coroot_eq_one
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hE : IsElemAbelian 3 Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (j : Fin 3) (c : ↥Bs) :
    actorPair ρ hE A hmk (Additive.toMul (ι.symm (h j))) c = 1 := by
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
    intro j
    rw [hpair j j]
    have hdiag : CartanMatrix.A 3 j j = 2 := by
      fin_cases j <;> decide
    rw [hdiag]
    norm_num
  exact actorPair_coroot_eq_one_of_diag hH hFcard hn hpq hAproj hE ι r h α hform hα2
    hind hgen j c


end PairingV

end Additive

theorem exists_eq_scalar_mul_actorLift
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b) (g : actorFull ρ) :
    ∃ (c : ↥Bs) (z : Fˣ),
      (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) z * A c := by
  classical
  have hgproj : ProjGenLinGroup.mk (g : GL (Fin 6) F) ∈ actorProj ρ := g.2
  rw [actorProj, MonoidHom.mem_range] at hgproj
  obtain ⟨c, hc⟩ := hgproj
  have hker : ProjGenLinGroup.mk
      ((g : GL (Fin 6) F) * (A c)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hc, ← hmk c, mul_inv_cancel]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨c, z, ?_⟩
  calc (g : GL (Fin 6) F) = ((g : GL (Fin 6) F) * (A c)⁻¹) * A c := by group
    _ = GeneralLinearGroup.scalar (Fin 6) z * A c := by rw [← hz]

theorem rho_injective_on_coroot
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {k : ℕ}
    (ι : Additive ↥Bs ≃+ V) (h : Fin k → V)
    (E : Subgroup G) (hE_le_inf : E ≤ Bs ⊓ J) (hEbot : E ⊓ Subgroup.centralizer (J : Set G) = ⊥)
    (e : Fin k → ↥Bs) (hE_closure : E = Subgroup.closure (Set.range (fun j => ((e j : ↥Bs) : G)))) :
    Function.Injective (fun x : E.subgroupOf Bs => ρ x) := by
  classical
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  intro x y hxy
  apply Subtype.ext
  let b : ↥Bs := (x : ↥Bs) * (y : ↥Bs)⁻¹
  have hbE : (b : G) ∈ E := by
    exact E.mul_mem (Subgroup.mem_subgroupOf.mp x.2) (E.inv_mem (Subgroup.mem_subgroupOf.mp y.2))
  have hρb : ρ b = 1 := by
    change ρ ((x : ↥Bs) * (y : ↥Bs)⁻¹) = 1
    rw [map_mul, map_inv]
    have hxy' : ρ (x : ↥Bs) = ρ (y : ↥Bs) := hxy
    rw [hxy', mul_inv_cancel]
  have hcenter : A b ∈ Subgroup.center (GL (Fin 6) F) := by
    rw [← ProjGenLinGroup.mk_eq_one]
    rw [hmk b, hρb]
  have hscal : A b ∈ LargeEvenScalars (Fin 6) F := by
    rw [largeEvenScalars_def, ← GeneralLinearGroup.center_eq_range_scalar]
    exact hcenter
  have hscal' := hscal
  obtain ⟨w, hw⟩ := hscal'
  have hproj1 : TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ = 1 := by
    have hscalw : GeneralLinearGroup.scalar (Fin 6) w ∈ LargeEvenScalars (Fin 6) F := by
      rw [hw]
      exact hscal
    have harg : (⟨A b, hAnorm b⟩ : Subgroup.normalizer (u6 F n : Set (GL (Fin 6) F))) =
        ⟨GeneralLinearGroup.scalar (Fin 6) w,
          TableB.scalar_mem_normalizer (u6 F n) hscalw⟩ := Subtype.ext hw.symm
    rw [harg]
    exact TableB.projConj_of_scalar (u6 F n) hscalw
  have hbeta1 : ggBeta J θ hN b = 1 := by
    rw [← hAproj b, hproj1]
  have hγ1 : ggLAut J θ ⟨(b : G), hN b.2⟩ = 1 := by
    rw [ggBeta_eq] at hbeta1
    exact hbeta1
  have hbcent : (b : G) ∈ Subgroup.centralizer (J : Set G) :=
    mem_centralizer_of_ggLAut_eq_one J θ hJperf hγ1
  have hbot : (b : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨hbE, hbcent⟩
  rw [hEbot] at hbot
  have hb1 : b = 1 := by
    apply Subtype.ext
    simpa using hbot
  have hx1 : (x : ↥Bs) * (y : ↥Bs)⁻¹ = 1 := by
    simpa [b] using hb1
  exact mul_inv_eq_one.mp hx1

theorem exists_E27_lifts_actual_of_rank3
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b) :
    ∃ Etilde : Subgroup (GL (Fin 6) F),
      Etilde ≤ actorFull ρ ∧ IsElemAbelian 3 Etilde ∧
      (∀ e ∈ Etilde, ∀ g ∈ actorFull ρ, e * g = g * e) ∧
      27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  haveI : IsMulCommutative ↥Bs := hE.1
  letI : AddCommGroup (Additive ↥Bs) :=
    { (Additive.addGroup : AddGroup (Additive ↥Bs)) with
      add_comm := fun a b =>
        congrArg Additive.ofMul
          (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }
  letI : Module (ZMod 3) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact hE.2 (x.toMul : G) x.toMul.2)
  letI : Module (ZMod 3) (Additive (rootsOfUnity 3 F)) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul]
      apply Subtype.ext
      exact x.toMul.2)
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hα2 : ∀ j : Fin T.rank, α j (h j) = 2 := by
    intro j
    rcases hT with rfl | rfl | rfl
    · dsimp [GGResLineJType.rank] at j ⊢
      rw [hpair j j]
      fin_cases j <;> norm_num [GGResLineJType.cartan, CartanMatrix.A]
    · dsimp [GGResLineJType.rank] at j ⊢
      rw [hpair j j]
      fin_cases j <;> norm_num [GGResLineJType.cartan, CartanMatrix.B]
    · dsimp [GGResLineJType.rank] at j ⊢
      rw [hpair j j]
      fin_cases j <;> norm_num [GGResLineJType.cartan, CartanMatrix.C]
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  let E : Subgroup G := ggSpanSub ι W
  have hEprops : ggSpanSub ι W ≤ Bs ⊓ J ∧ IsElemAbelian 3 (ggSpanSub ι W) ∧
      Nat.card (ggSpanSub ι W) = 27 ∧
      ggSpanSub ι W ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    rcases hT with rfl | rfl | rfl
    · have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
        intro i j
        simpa only [GGResLineJType.rank, GGResLineJType.cartan] using hpair i j
      exact GGResLineJDatum.coroot_span_subgroup_properties_of_A3
        (hN := hN) ι r h α hform hpairA hind hgen W rfl
    · have hpairB : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.B 3 i j : ZMod 3) := by
        intro i j
        simpa only [GGResLineJType.rank, GGResLineJType.cartan] using hpair i j
      have hC := ker_zero_of_det_two (C := CartanMatrix.B 3) (CartanMatrix.B_det (by norm_num))
      exact GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3)
        (hN := hN) ι r h α (CartanMatrix.B 3) hform hα2 hpairB hind hC hgen W rfl
    · have hpairC : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.C 3 i j : ZMod 3) := by
        intro i j
        simpa only [GGResLineJType.rank, GGResLineJType.cartan] using hpair i j
      have hC := ker_zero_of_det_two (C := CartanMatrix.C 3) (CartanMatrix.C_det (by norm_num))
      exact GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3)
        (hN := hN) ι r h α (CartanMatrix.C 3) hform hα2 hpairC hind hC hgen W rfl
  have hE_le_inf : E ≤ Bs ⊓ J := hEprops.1
  have hE_card : Nat.card E = 27 := hEprops.2.2.1
  have hE_bot : E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := hEprops.2.2.2
  have hE_le_bs : E ≤ Bs := hE_le_inf.trans inf_le_left
  let e : Fin T.rank → ↥Bs := fun j => Additive.toMul (ι.symm (h j))
  have hE_closure : E = Subgroup.closure (Set.range (fun j : Fin T.rank => ((e j : ↥Bs) : G))) := by
    dsimp [E, W, e]
    exact corootSpan_eq_closure (Bs := Bs) ι h
  have hχpres := actorChi_invariant (F := F) (n := n) (θ := θ) (hN := hN)
    (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk) hH hFcard hn hpq hAproj
  have hchi : ∀ j : Fin T.rank, actorChi ρ hE A hmk (e j) = 1 := by
    intro j
    exact Actor.actorChi_coroot_eq_one (J := J) ρ hE A hmk ι r h α hform hα2 hgen
      (fun φ hφ b => hχpres hφ b) j
  have hu : ∀ j : Fin T.rank, ∃ c : Fˣ,
      c ^ 3 = actorLam ρ hE A hmk (e j) := by
    intro j
    have h := hchi j
    change (QuotientGroup.mk (s := ((powMonoidHom 3 : Fˣ →* Fˣ).range))
      (actorLam ρ hE A hmk (e j)) : TypeA.PGLTor.PowQuot F 3) = 1 at h
    rw [TypeA.PGLTor.powQuot_mk_eq_one_iff] at h
    exact h
  let u : Fin T.rank → Fˣ := fun j => Classical.choose (hu j)
  have hu_spec : ∀ j : Fin T.rank, (u j) ^ 3 = actorLam ρ hE A hmk (e j) :=
    fun j => Classical.choose_spec (hu j)
  let Z : Fin T.rank → actorFull ρ := fun j =>
    ⟨GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j), by
      exact mul_mem (actorScalar_mem ρ ((u j)⁻¹)) (actorLift ρ A hmk (e j)).2⟩
  have hZ_coe : ∀ j : Fin T.rank, (Z j : GL (Fin 6) F) =
      GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j) := fun j => rfl
  have hZ3 : ∀ j : Fin T.rank, (Z j) ^ 3 = 1 := by
    intro j
    apply Subtype.ext
    change (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j)) ^ 3 = 1
    have hY3 : (A (e j)) ^ 3 =
        GeneralLinearGroup.scalar (Fin 6) (actorLam ρ hE A hmk (e j)) := by
      simpa [actorLift_coe] using
        actorLam_spec ρ hE A hmk (e j)
    have hscalar : (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹)) ^ 3 =
        GeneralLinearGroup.scalar (Fin 6) (((u j) ^ 3)⁻¹) := by
      rw [← map_pow, inv_pow]
    calc (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j)) ^ 3
        = (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹)) ^ 3 *
            (A (e j)) ^ 3 := by
          rw [Commute.mul_pow
            (TypeA.PGLTor.commute_scalar ((u j)⁻¹) (A (e j))) 3]
      _ = GeneralLinearGroup.scalar (Fin 6) (((u j) ^ 3)⁻¹) *
            GeneralLinearGroup.scalar (Fin 6) (actorLam ρ hE A hmk (e j)) := by
          rw [hscalar, hY3]
      _ = GeneralLinearGroup.scalar (Fin 6)
            ((actorLam ρ hE A hmk (e j))⁻¹) *
            GeneralLinearGroup.scalar (Fin 6) (actorLam ρ hE A hmk (e j)) := by
          rw [hu_spec j]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcommA : ∀ j : Fin T.rank, ∀ c : ↥Bs,
      A (e j) * A c = A c * A (e j) := by
    intro j c
    have hpair0 := actorPair_coroot_eq_one_of_diag (F := F) (n := n) (θ := θ) (hN := hN)
      (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
      hH hFcard hn hpq hAproj hE ι r h α hform hα2 hind hgen j c
    have hcc : actorPair ρ hE A hmk (e j) c = 1 := by
      simpa [e] using hpair0
    exact (TypeA.PGLTor.commChar_eq_one_iff (actorFull_isProjElem ρ hE)
      (actorLift ρ A hmk (e j)).2 (actorLift ρ A hmk c)).mp hcc
  have hZ_cent : ∀ j : Fin T.rank, ∀ g ∈ actorFull ρ,
      Z j * g = g * Z j := by
    intro j g hg
    obtain ⟨c, w, hgw⟩ := exists_eq_scalar_mul_actorLift (ρ := ρ) (A := A) (hmk := hmk) ⟨g, hg⟩
    have hc := hcommA j c
    change (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j)) * g =
      g * (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹) * A (e j))
    rw [show g = GeneralLinearGroup.scalar (Fin 6) w * A c from hgw]
    have hsu_sw : Commute (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹))
        (GeneralLinearGroup.scalar (Fin 6) w) :=
      GeneralLinearGroup.scalar_commute (n := Fin 6) ((u j)⁻¹)
        (GeneralLinearGroup.scalar (Fin 6) w)
    have hsu_Ac : Commute (GeneralLinearGroup.scalar (Fin 6) ((u j)⁻¹)) (A c) :=
      GeneralLinearGroup.scalar_commute (n := Fin 6) ((u j)⁻¹) (A c)
    have hAe_sw : Commute (A (e j)) (GeneralLinearGroup.scalar (Fin 6) w) :=
      (GeneralLinearGroup.scalar_commute (n := Fin 6) w (A (e j))).symm
    have hAe_Ac : Commute (A (e j)) (A c) := hc
    exact ((hsu_sw.mul_right hsu_Ac).mul_left (hAe_sw.mul_right hAe_Ac)).eq
  let Etilde : Subgroup (GL (Fin 6) F) :=
    Subgroup.closure (Set.range (fun j : Fin T.rank => (Z j : GL (Fin 6) F)))
  have hEtilde_le : Etilde ≤ actorFull ρ := by
    dsimp only [Etilde]
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact (Z j).2
  have hEtilde_elem : IsElemAbelian 3 Etilde := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute
      (s := Set.range (fun j : Fin T.rank => (Z j : GL (Fin 6) F))) ?_ ?_
    · rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
      exact hZ_cent j (Z k) (Z k).2
    · rintro _ ⟨j, rfl⟩
      exact congrArg (fun x : actorFull ρ => (x : GL (Fin 6) F)) (hZ3 j)
  have hEtilde_cent_le : Etilde ≤
      Subgroup.centralizer (actorFull ρ : Set (GL (Fin 6) F)) := by
    dsimp only [Etilde]
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun g hg => (hZ_cent j g hg).symm)
  have hcent : ∀ e ∈ Etilde, ∀ g ∈ actorFull ρ, e * g = g * e := by
    intro e he g hg
    exact (Subgroup.mem_centralizer_iff.mp (hEtilde_cent_le he) g hg).symm
  have hρinj : Function.Injective (fun x : E.subgroupOf Bs => ρ x) :=
    rho_injective_on_coroot (F := F) (n := n) (θ := θ) (hN := hN)
      (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
      hH hFcard hn hpq hAproj ι h E hE_le_inf hE_bot e hE_closure
  have hsub : E.subgroupOf Bs = Subgroup.closure (Set.range e) := by
    apply (Subgroup.map_subtype_inj (H := Bs)).mp
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE_le_bs,
      MonoidHom.map_closure, hE_closure]
    apply le_antisymm
    · apply Subgroup.closure_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨e j, ⟨j, rfl⟩, rfl⟩
    · apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  have hmkZ : ∀ j : Fin T.rank,
      ProjGenLinGroup.mk (Z j : GL (Fin 6) F) = ρ (e j) := by
    intro j
    rw [hZ_coe j, map_mul, hmk (e j), ProjGenLinGroup.mk_scalar, one_mul]
  have hproj_eq : CFSG.PGLModel.projImage Etilde = (E.subgroupOf Bs).map ρ := by
    rw [CFSG.PGLModel.projImage]
    dsimp only [Etilde]
    rw [hsub, MonoidHom.map_closure, MonoidHom.map_closure,
      ← Set.range_comp, ← Set.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hmkZ j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hmkZ j⟩
  have hE_sub_card : Nat.card (E.subgroupOf Bs) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_bs).toEquiv, hE_card]
  have hcard : 27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde) := by
    rw [hproj_eq]
    let f : E.subgroupOf Bs → (E.subgroupOf Bs).map ρ := fun x =>
      ⟨ρ x, ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        exact hρinj (congrArg Subtype.val hxy)
      · rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hE_sub_card]
    exact le_of_eq (Nat.card_congr (Equiv.ofBijective f hf))
  exact ⟨Etilde, hEtilde_le, hEtilde_elem, hcent, hcard⟩

theorem exists_E27_lifts_actual
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b) :
    ∃ Etilde : Subgroup (GL (Fin 6) F),
      Etilde ≤ actorFull ρ ∧ IsElemAbelian 3 Etilde ∧
      (∀ e ∈ Etilde, ∀ g ∈ actorFull ρ, e * g = g * e) ∧
      27 ≤ Nat.card (CFSG.PGLModel.projImage Etilde) :=
  exists_E27_lifts_actual_of_rank3 (T := .A3) hH hD (Or.inl rfl)
    hFcard hn hpq hAproj hmk

theorem exists_primitive_root_three_actual
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ 3 := by
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    conv_lhs => rw [show (1 : ℕ) = 1 ^ 2 by norm_num]
    rw [Nat.sq_sub_sq]
  have h3dvd : 3 ∣ Nat.card F - 1 := by
    rw [hFcard, hsq]
    exact dvd_mul_of_dvd_left hpq _
  exact TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd Nat.prime_three h3dvd

theorem actorFull_comm_of_actual
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b) :
    ∀ g ∈ actorFull ρ, ∀ h ∈ actorFull ρ, g * h = h * g := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_root_three_actual (F := F) (n := n) hFcard hpq
  obtain ⟨Etilde, hEtilde_le, hEtilde_elem, hcent, hcard⟩ :=
    exists_E27_lifts_actual (F := F) (n := n) (θ := θ) (hN := hN)
      (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
      hH hD hFcard hn hpq hAproj
  haveI : Finite Etilde := Subtype.finite
  exact Actor.actorFull_comm_of_E27 ρ hH.1.2.1.2.1 hζ Etilde hEtilde_le
    hEtilde_elem hcent hcard (by norm_num)

theorem actorLift_comm_of_actual
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hAproj : ∀ b, TableB.projConj (u6 F n) ⟨A b, hAnorm b⟩ =
      ggBeta J θ hN b)
    (hmk : ∀ b, ProjGenLinGroup.mk (A b) = ρ b) (b c : ↥Bs) :
    A b * A c = A c * A b := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_root_three_actual (F := F) (n := n) hFcard hpq
  obtain ⟨Etilde, hEtilde_le, hEtilde_elem, hcent, hcard⟩ :=
    exists_E27_lifts_actual (F := F) (n := n) (θ := θ) (hN := hN)
      (ρ := ρ) (A := A) (hAnorm := hAnorm) (hmk := hmk)
      hH hD hFcard hn hpq hAproj
  haveI : Finite Etilde := Subtype.finite
  exact Actor.actorLift_comm_of_E27 ρ hH.1.2.1.2.1 A hmk hζ Etilde hEtilde_le
    hEtilde_elem hcent hcard (by norm_num) b c

end

end ResJSU6Scalar

end CFSG.StandardType

end