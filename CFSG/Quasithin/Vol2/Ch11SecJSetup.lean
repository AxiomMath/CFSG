module

public import CFSG.Quasithin.Vol2.Ch11SecJMat
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11StatementsA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open scoped MatrixGroups

structure Core (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ)
    (V₁ : Subgroup G) where
  St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G))
  h : Hyp11 G T L I n
  hV₁ : IsVi T L I n 1 V₁
  hSL3 : KindSL3 L (fsuV T I) n
  hK : KOf L V₁ V₁ = LOf L V₁
  hUL : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ L
  hO2L : pCoreOf 2 L = fsuV T I
  hcard : Nat.card ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) = 2 ^ (5 * n)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

omit [Finite G] in
theorem lOf_le_L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left

omit [Finite G] in
theorem lOf_le_G₁ : LOf L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  (perfectCore_le _).trans inf_le_right

namespace Core

variable (C : Core G T L I n V₁)

theorem theta_eq_one_iff (l : ↥L) : C.St.D.θ l = 1 ↔ (l : G) ∈ fsuV T I := by
  have hk : C.St.D.θ l = 1 ↔ (l : G) ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← MonoidHom.mem_ker, C.St.D.ker_eq, Subgroup.mem_subgroupOf]
  rw [hk]
  constructor
  · intro hl
    rw [← C.hO2L]
    have hle : pCoreOf 2 (L ⊔ T) ⊓ L ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
            ((le_sup_left : L ≤ L ⊔ T) hx), Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact hle ⟨hl, l.2⟩
  · intro hv
    exact C.St.V_le_O hv

theorem theta_of_mem_U {u : G}
    (hu : u ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) :
    ∃ b c : GaloisField 2 n, C.St.D.θ ⟨u, C.hUL hu⟩ = tq b c := by
  obtain ⟨b, c, hbc⟩ := C.St.Phi_of_U hu
  refine ⟨b, c, ?_⟩
  rw [← C.St.Phi_of_L ⟨u, C.hUL hu⟩]
  exact hbc

theorem theta_mem_Qv_of_mem_U {u : G}
    (hu : u ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) :
    C.St.D.θ ⟨u, C.hUL hu⟩ ∈ Qv (vE (GaloisField 2 n) 0) := by
  obtain ⟨b, c, hbc⟩ := C.theta_of_mem_U hu
  rw [hbc]
  exact tq_mem_Qv b c

theorem exists_theta_eq {A : SL(3, GaloisField 2 n)} (hA : A ∈ Qv (vE (GaloisField 2 n) 0)) :
    ∃ (u : G) (hu : u ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))),
      C.St.D.θ ⟨u, C.hUL hu⟩ = A := by
  have hA' : A ∈ C.St.Ubar := by rw [C.St.Ubar_eq_Qv]; exact hA
  obtain ⟨u, hu⟩ := hA'
  refine ⟨u, u.2, ?_⟩
  rw [← hu, C.St.betaU_apply, ← C.St.Phi_of_L ⟨u, C.hUL u.2⟩]

theorem mem_U_of_theta_mem_Qv (l : ↥L) (hl : C.St.D.θ l ∈ Qv (vE (GaloisField 2 n) 0)) :
    (l : G) ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) := by
  obtain ⟨u, hu, hθ⟩ := C.exists_theta_eq hl
  have h1 : C.St.D.θ (⟨u, C.hUL hu⟩⁻¹ * l) = 1 := by rw [map_mul, map_inv, hθ, inv_mul_cancel]
  have h2 := (C.theta_eq_one_iff _).1 h1
  have h3 : u⁻¹ * (l : G) ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) :=
    le_conjClosure _ _ h2
  have h4 := Subgroup.mul_mem _ hu h3
  rwa [mul_inv_cancel_left] at h4

theorem theta_mem_Pt (k : ↥(LOf L V₁)) :
    C.St.D.θ ⟨k, lOf_le_L k.2⟩ ∈ Pt (vE (GaloisField 2 n) 0) :=
  C.St.theta_mem_Pt_of_normalizer _ (lOf_le_G₁ k.2)

theorem theta_entry00 (k : ↥(LOf L V₁)) : (C.St.D.θ ⟨k, lOf_le_L k.2⟩).1 0 0 = 1 := by
  set H : Subgroup G := L ⊓ Subgroup.normalizer (V₁ : Set G) with hH
  have hne : ∀ h : ↥H, (C.St.D.θ ⟨h, h.2.1⟩).1 0 0 ≠ 0 := fun h =>
    left_ne_zero_of_mul_eq_one (entry00_mul_det_blk22 (C.St.theta_mem_Pt_of_normalizer _ h.2.2))
  let f : ↥H →* (GaloisField 2 n)ˣ :=
    { toFun := fun h => Units.mk0 _ (hne h)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one]
        have : (⟨((1 : ↥H) : G), (1 : ↥H).2.1⟩ : ↥L) = 1 := rfl
        rw [this, map_one]
        simp
      map_mul' := fun a b => by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have : (⟨((a * b : ↥H) : G), (a * b).2.1⟩ : ↥L) = ⟨a, a.2.1⟩ * ⟨b, b.2.1⟩ := rfl
        rw [this, map_mul]
        exact entry00_mul _ (C.St.theta_mem_Pt_of_normalizer _ b.2.2) }
  have hk : (k : G) ∈ (commutator ↥H).map H.subtype := by
    have := perfectCore_le_derivedSeriesOf H 1 k.2
    rwa [derivedSeriesOf_eq_map_derivedSeries, derivedSeries_one] at this
  obtain ⟨h, hh, hhk⟩ := hk
  have h1 : f h = 1 := Abelianization.commutator_subset_ker f hh
  have h2 := congrArg Units.val h1
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one] at h2
  have h3 : (⟨(h : G), h.2.1⟩ : ↥L) = ⟨k, lOf_le_L k.2⟩ := Subtype.ext hhk
  rwa [h3] at h2

theorem theta_mem_Pt1 (k : ↥(LOf L V₁)) : C.St.D.θ ⟨k, lOf_le_L k.2⟩ ∈ Pt1 (GaloisField 2 n) :=
  ⟨C.theta_mem_Pt k, C.theta_entry00 k⟩

@[expose] noncomputable def alpha : ↥(LOf L V₁) →* SL(2, GaloisField 2 n) :=
  blkHom.comp ((C.St.D.θ.comp (Subgroup.inclusion lOf_le_L)).codRestrict
    (Pt1 (GaloisField 2 n)) C.theta_mem_Pt1)

theorem coe_alpha (k : ↥(LOf L V₁)) :
    ((C.alpha k : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) =
      blk22 (C.St.D.θ ⟨k, lOf_le_L k.2⟩).1 := rfl

theorem alpha_surjective : Function.Surjective C.alpha := by
  intro M
  set H : Subgroup G := L ⊓ Subgroup.normalizer (V₁ : Set G) with hH
  have hcore : (perfectCore (H.subgroupOf L)).map L.subtype = LOf L V₁ := by
    rw [map_perfectCore, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 inf_le_left]
  have himg : (perfectCore (H.subgroupOf L)).map C.St.D.θ =
      perfectCore (Pt (vE (GaloisField 2 n) 0)) := by
    rw [map_perfectCore, C.St.map_theta_N]
  have hn0 : n ≠ 0 := by have := C.h.one_lt; omega
  obtain ⟨a, ha0, ha1⟩ : ∃ a : GaloisField 2 n, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | h
    · exfalso
      rw [GaloisField.card 2 n hn0] at h2
      have h3 : 2 ^ n = 2 ^ 1 := by rw [h2, pow_one]
      have := Nat.pow_right_injective (le_refl 2) h3
      have := C.h.one_lt
      omega
    · exact h
  set B : Subgroup SL(3, GaloisField 2 n) :=
    (blk : SL(2, GaloisField 2 n) →* SL(3, GaloisField 2 n)).range with hB
  have hperf : ⁅B, B⁆ = B := by
    rw [hB, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Matrix.SL2.commutator_eq_top ha0 ha1]
  have hle : B ≤ perfectCore (Pt (vE (GaloisField 2 n) 0)) :=
    le_perfectCore_of_perfect (by rintro _ ⟨N, rfl⟩; exact blk_mem_Pt N) hperf
  have hM : blk M ∈ (perfectCore (H.subgroupOf L)).map C.St.D.θ := by
    rw [himg]
    exact hle ⟨M, rfl⟩
  obtain ⟨k', hk', hk'θ⟩ := hM
  have hkK : (k' : G) ∈ LOf L V₁ := by
    rw [← hcore]
    exact ⟨k', hk', rfl⟩
  refine ⟨⟨k', hkK⟩, Subtype.ext ?_⟩
  rw [C.coe_alpha]
  have : (⟨((⟨(k' : G), hkK⟩ : ↥(LOf L V₁)) : G), lOf_le_L hkK⟩ : ↥L) = k' := rfl
  rw [this, hk'θ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk22, blk_coe]

include C in
theorem pCoreOf_lOf_le_U :
    pCoreOf 2 (LOf L V₁) ≤ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) := by
  intro y hy
  have hyK : y ∈ LOf L V₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
  set P : Subgroup SL(3, GaloisField 2 n) :=
    ((pCoreOf 2 (LOf L V₁)).subgroupOf L).map C.St.D.θ with hP
  have hPPt : P ≤ Pt (vE (GaloisField 2 n) 0) := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.St.theta_mem_Pt_of_normalizer z
      (lOf_le_G₁ (CFSG.LieType.BorelTits.pCoreOf_le 2 _ (Subgroup.mem_subgroupOf.1 hz)))
  have hPn : ∀ p ∈ Pt (vE (GaloisField 2 n) 0), ∀ x ∈ P, p * x * p⁻¹ ∈ P := by
    intro p hp x hx
    rw [← C.St.map_theta_N] at hp
    obtain ⟨l, hl, rfl⟩ := hp
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨l * z * l⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl hz ⊢
    have hlN : (l : G) ∈ Subgroup.normalizer (LOf L V₁ : Set G) :=
      normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hl)
    have hlP := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hlN
    simpa using (Subgroup.mem_normalizer_iff.mp hlP z).mp hz
  have hP2 : IsPGroup 2 P :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_of_injective L.subtype
      Subtype.val_injective).map _
  have hPQ := normal_two_le_Qv P hPPt hPn hP2
  exact C.mem_U_of_theta_mem_Qv ⟨y, lOf_le_L hyK⟩
    (hPQ ⟨⟨y, lOf_le_L hyK⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩)

end Core

end CFSG.Quasithin.Vol2.Ch11.SecJ
