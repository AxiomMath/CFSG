module

public import CFSG.Quasithin.Vol2.Ch11SecO1bA
public import CFSG.Quasithin.Vol2.Ch11SecAKB3
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecAKA8
public import CFSG.Quasithin.Vol2.Ch11SecO1B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem r1_le (hS : SecD.NatSetting11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) :
    ROf T L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (LOf L V₁ : Set G) := by
  have h : LOf L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := perfectCore_le _
  have hTV₁ := SecA.IsVi.le_normalizer hV₁
  have hT : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
      Set G) :=
    (le_inf hS.normal (hTV₁.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le
    (le_inf (le_inf (le_inf ?_ ?_) ?_) Subgroup.le_normalizer)
    (le_inf (le_inf (le_inf (SecA.T_le_normalizer_fsuV T I) hS.normal) hTV₁)
      (hT.trans (normalizer_le_normalizer_perfectCore _))))
  · exact h.trans (inf_le_left.trans hS.le_normalizer)
  · exact h.trans (inf_le_left.trans Subgroup.le_normalizer)
  · exact h.trans inf_le_right

theorem comm_mem_pCoreOf_r1 (hS : SecD.NatSetting11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    {r l : G} (hr : r ∈ ROf T L V₁) (hl : l ∈ LOf L V₁) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ROf T L V₁ with hR
  have hNR : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hle : R ⊓ LOf L V₁ ≤ pCoreOf 2 (LOf L V₁) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact (le_inf (le_sup_left.trans hNR) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine hle ⟨?_, ?_⟩
  · have h1 : l * r⁻¹ * l⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hNR (le_sup_left (α := Subgroup G) hl)) _).mp
        (R.inv_mem hr)
    have := R.mul_mem hr h1
    rwa [← mul_assoc, ← mul_assoc] at this
  · have h1 : r * l * r⁻¹ ∈ LOf L V₁ :=
      (Subgroup.mem_normalizer_iff.mp (r1_le hS hV₁ hr).2 _).mp hl
    exact (LOf L V₁).mul_mem h1 ((LOf L V₁).inv_mem hl)

theorem r1_le_normalizer (hS : SecD.NatSetting11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) {r : G}
    (hr : r ∈ ROf T L V₁) : r ∈ Subgroup.normalizer (fsuV T I : Set G) :=
  (r1_le hS hV₁ hr).1.1.1

theorem conjV_r1_centralizes (hS : SecD.NatSetting11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    {r : G} (hr : r ∈ ROf T L V₁) :
    (∃ k : ℕ, SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) ^ 2 ^ k = 1) ∧
    (∀ h ∈ autOn L (fsuV T I), SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) * h *
      (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr))⁻¹ ∈ autOn L (fsuV T I)) ∧
    (∀ x ∈ autOn (LOf L V₁) (fsuV T I), SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) *
      x * (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr))⁻¹ ∈ autOn (LOf L V₁) (fsuV T I))
    ∧ ∀ x : ↥(autOn (LOf L V₁) (fsuV T I)), ∃ y : ↥(autOn (LOf L V₁) (fsuV T I)),
      y ∈ CFSG.pCore 2 ↥(autOn (LOf L V₁) (fsuV T I)) ∧
      SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) * (x : MulAut ↥(fsuV T I)) *
        (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr))⁻¹ =
          (y : MulAut ↥(fsuV T I)) * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨⟨hrV, hrL⟩, hrV₁⟩, hrL₁⟩ := r1_le hS hV₁ hr
  set τ := SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) with hτ
  have hτinv : τ⁻¹ = SecA.conjV (fsuV T I) r⁻¹ (Subgroup.inv_mem _ hrV) :=
    (SecA.conjV_inv (fsuV T I) hrV).symm
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₁V : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := hL₁L.trans hS.le_normalizer
  have hP : ∀ x ∈ autOn (LOf L V₁) (fsuV T I), τ * x * τ⁻¹ ∈ autOn (LOf L V₁) (fsuV T I) := by
    intro x hx
    obtain ⟨y, hyL₁, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
    rw [hτ, SecA.conjV_conj]
    exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hrL₁ y).mp hyL₁) _
  have hcomm : ∀ x ∈ autOn (LOf L V₁) (fsuV T I), τ * x * τ⁻¹ * x⁻¹ ∈
      pCoreOf 2 (autOn (LOf L V₁) (fsuV T I)) := by
    rw [← SecA.autOn_pCoreOf hL₁V ((SecO1.isPGroup_inf_centralizer hS).to_le
      (inf_le_inf_right _ hL₁L))]
    intro x hx
    obtain ⟨y, hyL₁, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
    rw [hτinv, ← SecA.conjV_inv _ hyV, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn (comm_mem_pCoreOf_r1 hS hV₁ hr hyL₁) _
  refine ⟨?_, fun h hh => G2Q8.conjV_mul_conjV_inv_mem hrL hrV hh, hP, fun x => ?_⟩
  · obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₁ ⊔ T) ⟨r, hr⟩
    have hrm : r ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact ⟨m, SecA.conjV_pow_eq_one _ hrV hrm⟩
  · obtain ⟨y, hy, hyx⟩ := hcomm x x.2
    refine ⟨y, by exact hy, ?_⟩
    have hyx' : (y : MulAut ↥(fsuV T I)) =
        τ * (x : MulAut ↥(fsuV T I)) * τ⁻¹ * (x : MulAut ↥(fsuV T I))⁻¹ := hyx
    rw [hyx', inv_mul_cancel_right]

theorem r1_shape_sl3 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 3 → K)}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) :
    ∃ a b : K, ∀ w : ↥(fsuV T I), ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) =
        uMat a b 0 *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          f w) := by
  have hSL := commutator_SL2_eq_top (four_le_card hS.one_lt hK)
  obtain ⟨h2, hH, hP, hc⟩ := conjV_r1_centralizes hS hV₁ hr
  have hP1 : autOn (LOf L V₁) (fsuV T I) = perfectCore (autOn L (fsuV T I) ⊓
      SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) := by
    rw [SecS.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁), mem_V1_sl3 hS hK hf hg hV₁]
  rw [hP1] at hP hc
  exact PointStab.exists_uMat_of_centralizes hSL hf g h2 (SecO1.mem_stabW_bot _) hH hP hc

theorem r1_shape_sp4 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g : StatedSp 2 K}
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ w : ↥(fsuV T I),
      f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) = mat 2 K (g * N * g⁻¹) *ᵥ f w
    := by
  have hn : 2 ≤ n := hS.one_lt
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨h2, hH, -, hc⟩ := conjV_r1_centralizes hS hV₁ hr
  have hU := SecO1.isFlagW_of_isVi hS hV₁
  have hfix := factRadicalFixedSp4_holds K n hn hK _ (SecO1.sq_eq_one hS) _ ⊥ π hπ _
    (SecO1.isSylowTwoOf_P hS) _ hU
  have hpt := factPointSp4_holds K n hn hK _ (SecO1.sq_eq_one hS) _ ⊥ π hπ _
    (SecO1.isSylowTwoOf_P hS) _ hU
  rw [SecS.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁)] at hc
  obtain ⟨N, hN, hact⟩ := KA.exists_core hK4 hf g (mem_V1_sp4 hS hK hf hg hV₁) hfix hpt h2
    (SecO1.mem_stabW_bot _) hH hc
  exact ⟨N, hN, fun w => by rw [hact, psiSp_apply, hf.act4]⟩

end CFSG.Quasithin.Vol2.Ch11.SecO1b
