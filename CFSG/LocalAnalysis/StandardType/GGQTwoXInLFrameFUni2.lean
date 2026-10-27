module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus5
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

namespace FrameSign

lemma pow_val_injective {M : Type} [Field M] {u : Mˣ} (h3 : u ^ 3 = 1) (h1 : u ≠ 1) :
    ∀ a b : ZMod 3, (u : M) ^ a.val = (u : M) ^ b.val → a = b := by
  have horder : orderOf u = 3 :=
    orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) h3 h1
  intro a b hab
  have hmod : a.val ≡ b.val [MOD 3] := by
    have hu : u ^ a.val = u ^ b.val :=
      Units.ext (by rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val])
    have h := (pow_eq_pow_iff_modEq (x := u) (n := a.val) (m := b.val)).mp hu
    rwa [horder] at h
  exact ZMod.val_injective 3 (by
    have h' := hmod
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h'
    exact h')

lemma tau_pow {M : Type} [Field M] {τ : M ≃+* M} (hτ2 : ∀ y, τ y = y ^ 2)
    {u : Mˣ} (h3 : u ^ 3 = 1) (h1 : u ≠ 1) (k : ZMod 3) :
    τ ((u : M) ^ k.val) = (u : M) ^ (-k).val := by
  have horder : orderOf u = 3 :=
    orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) h3 h1
  have hz : k + k = -k := by
    have h3' : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    have h : k + k + k = 0 := by
      calc k + k + k = 3 * k := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 from h3', zero_mul]
    rw [add_assoc] at h
    exact eq_neg_of_add_eq_zero_right h
  have hmod : (k.val + k.val) ≡ (-k).val [MOD 3] := by
    show (k.val + k.val) % 3 = (-k).val % 3
    rw [Nat.mod_eq_of_lt (ZMod.val_lt (-k)), ← ZMod.val_add, hz]
  have hu : u ^ (k.val + k.val) = u ^ (-k).val := by
    have hmod' : (k.val + k.val) ≡ (-k).val [MOD orderOf u] := by rwa [horder]
    exact (pow_eq_pow_iff_modEq (x := u) (n := k.val + k.val) (m := (-k).val)).mpr hmod'
  calc τ ((u : M) ^ k.val) = ((u : M) ^ k.val) ^ 2 := hτ2 _
    _ = (u : M) ^ k.val * (u : M) ^ k.val := pow_two _
    _ = (↑(u ^ k.val) : M) * (↑(u ^ k.val) : M) := by rw [Units.val_pow_eq_pow_val]
    _ = ↑(u ^ k.val * u ^ k.val) := (Units.val_mul _ _).symm
    _ = ↑(u ^ (k.val + k.val)) := by rw [pow_add]
    _ = ↑(u ^ (-k).val) := by rw [hu]
    _ = (u : M) ^ (-k).val := by rw [Units.val_pow_eq_pow_val]

lemma exists_cU {M : Type} [Field M] {c : M} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ cU : Mˣ, (cU : M) = c ∧ cU ^ 3 = 1 ∧ cU ≠ 1 := by
  have hc0 : c ≠ 0 := by
    intro h
    have h0 : (0 : M) ^ 3 = 0 := zero_pow (by norm_num)
    rw [h, h0] at hc3
    exact zero_ne_one hc3
  refine ⟨Units.mk0 c hc0, Units.val_mk0 hc0, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hc3
  · intro h
    apply hc1
    rw [← Units.val_mk0 hc0, h]
    rfl

noncomputable def dg {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) (cU : Mˣ)
    (v : Fin n → ZMod 3) : ↥(heldGU n M τ hτ) :=
  ((QTwoFrameTorus.frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
      (fun j => cU ^ (v j).val) :
      ↥(QTwoFrameTorus.frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
    ↥(heldGU n M τ hτ))

private lemma dg_val {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) (cU : Mˣ)
    (v : Fin n → ZMod 3) :
    (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) =
      ((diagHom n (fun j => cU ^ (v j).val) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) := by
  rw [dg, QTwoFrameTorus.frameDiagEquiv_apply_val,
    QTwoFrameTorus.frameDiagGL_val, coe_diagHom]

lemma dg_apply_eq {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) (cU : Mˣ)
    (v : Fin n → ZMod 3) (i : Fin n) :
    (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) i i = (cU : M) ^ (v i).val := by
  rw [dg_val, coe_diagHom, Matrix.diagonal_apply_eq, Units.val_pow_eq_pow_val]

lemma dg_off {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) (cU : Mˣ)
    (v : Fin n → ZMod 3) {i j : Fin n} (hij : i ≠ j) :
    (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) i j = 0 := by
  rw [dg_val, coe_diagHom, Matrix.diagonal_apply_ne _ hij]

lemma dg_injective {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    (hinj : ∀ a b : ZMod 3, (cU : M) ^ a.val = (cU : M) ^ b.val → a = b) :
    Function.Injective (fun v : Fin n → ZMod 3 => dg (τ := τ) (hτ := hτ) hM hτ2 cU v) := by
  intro v v' h
  funext i
  apply hinj
  have hv : dg hM hτ2 cU v = dg hM hτ2 cU v' := h
  have h1 : (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i i =
      (((dg hM hτ2 cU v' : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) i i := by rw [hv]
  rwa [dg_apply_eq, dg_apply_eq] at h1

lemma dg_mem_E {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {R : Type} [Group R] {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R}
    {L : Subgroup R} (hU : GGQTwoUFrame ρ E x L) (v : Fin n → ZMod 3) :
    ρ (dg hM hτ2 cU v) ∈ E := by
  rw [QTwoFrameTorus.frame_E_eq_diagSub (n := n) (τ := τ) (hτ := hτ) (ρ := ρ) (E := E)
    (x := x) (L := L) hM hτ2 hU]
  exact Subgroup.mem_map.mpr
    ⟨QTwoFrameTorus.frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
        (fun j => cU ^ (v j).val),
      (QTwoFrameTorus.frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
        (fun j => cU ^ (v j).val)).2, rfl⟩

lemma dg_coord {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {c : M} {cU : Mˣ}
    (hcU : (cU : M) = c)
    (hinj : ∀ a b : ZMod 3, (cU : M) ^ a.val = (cU : M) ^ b.val → a = b)
    {R : Type} [Group R] {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R}
    {L : Subgroup R} (hU : GGQTwoUFrame ρ E x L)
    (ι : Additive ↥E ≃+ (Fin n → ZMod 3))
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    (v : Fin n → ZMod 3) :
    ι (Additive.ofMul ⟨ρ (dg hM hτ2 cU v), dg_mem_E hM hτ2 hU v⟩) = v := by
  funext i
  apply hinj
  have h := hι (dg hM hτ2 cU v) (dg_mem_E hM hτ2 hU v)
    (fun i j hij => dg_off hM hτ2 cU v hij) i
  rw [dg_apply_eq, ← hcU] at h
  exact h.symm

lemma dg_eq_of_mem {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {c : M} {cU : Mˣ}
    (hcU : (cU : M) = c) {R : Type} [Group R] {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R}
    {x : R} {L : Subgroup R} (hU : GGQTwoUFrame ρ E x L)
    (ι : Additive ↥E ≃+ (Fin n → ZMod 3))
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {e : R} (he : e ∈ E) :
    e = ρ (dg hM hτ2 cU (ι (Additive.ofMul ⟨e, he⟩))) := by
  obtain ⟨A, hdiag, hAe⟩ := (hU.2.1 e).mp he
  have hsub : (⟨ρ A, hAe.symm ▸ he⟩ : ↥E) = ⟨e, he⟩ := Subtype.ext hAe
  have hcoord : ι (Additive.ofMul ⟨ρ A, hAe.symm ▸ he⟩) = ι (Additive.ofMul ⟨e, he⟩) := by
    rw [hsub]
  have hA : A = dg hM hτ2 cU (ι (Additive.ofMul ⟨e, he⟩)) := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hι A (hAe.symm ▸ he) hdiag i, hcoord, dg_apply_eq, hcU]
    · rw [hdiag i j hij, dg_off hM hτ2 cU _ hij]
  calc e = ρ A := hAe.symm
    _ = ρ (dg hM hτ2 cU (ι (Additive.ofMul ⟨e, he⟩))) := by rw [hA]

noncomputable def delta {R : Type} [Group R] {n : ℕ} {M : Type} [Field M]
    (cU : Mˣ) (E : Subgroup R) (ι : Additive ↥E ≃+ (Fin n → ZMod 3)) :
    R → Fin n → Mˣ := by
  classical
  exact fun e => if he : e ∈ E then fun j => cU ^ (ι (Additive.ofMul ⟨e, he⟩) j).val else 1

private lemma delta_apply {R : Type} [Group R] {n : ℕ} {M : Type} [Field M] (cU : Mˣ)
    (E : Subgroup R) (ι : Additive ↥E ≃+ (Fin n → ZMod 3)) {e : R} (he : e ∈ E)
    (j : Fin n) : delta cU E ι e j = cU ^ (ι (Additive.ofMul ⟨e, he⟩) j).val := by
  classical
  simp only [delta, dif_pos he]

private lemma diagHom_mem_normalizer {M : Type} [Field M] [Finite M] {n : ℕ}
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hSU : unitarySU 2 1 M n = heldSU n M τ hτ) {t : Fin n → Mˣ}
    (hB : diagHom n t ∈ heldGU n M τ hτ) :
    diagHom n t ∈ Subgroup.normalizer ((unitarySU 2 1 M n : Set (GL (Fin n) M))) := by
  have hdet : ∀ x : GL (Fin n) M,
      (((diagHom n t * x * (diagHom n t)⁻¹ : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M).det =
        (((x : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M).det) := by
    intro x
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  rw [hSU, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (heldGU n M τ hτ).mul_mem
        ((heldGU n M τ hτ).mul_mem hB (Subgroup.mem_inf.mp hx).1)
        ((heldGU n M τ hτ).inv_mem hB)
    · have hx2 := (Subgroup.mem_inf.mp hx).2
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hx2 ⊢
      exact (hdet x).trans hx2
  · intro hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hx1 := (Subgroup.mem_inf.mp hx).1
      have := (heldGU n M τ hτ).mul_mem
        ((heldGU n M τ hτ).mul_mem ((heldGU n M τ hτ).inv_mem hB) hx1) hB
      rw [show x = (diagHom n t)⁻¹ * ((diagHom n t) * x * (diagHom n t)⁻¹) *
        (diagHom n t) from by group]
      exact this
    · have hx2 := (Subgroup.mem_inf.mp hx).2
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hx2 ⊢
      exact (hdet x).symm.trans hx2

lemma mem_suPairs {M : Type} [Field M] [Finite M] {n : ℕ} {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2)
    {R : Type} [Group R] {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R}
    {L : Subgroup R} (hU : GGQTwoUFrame ρ E x L)
    (hSU : unitarySU 2 1 M n = heldSU n M τ hτ)
    {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {ι : Additive ↥E ≃+ (Fin n → ZMod 3)} {c : M} {cU : Mˣ} (hcU : (cU : M) = c)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {D : Subgroup R} (hDE : D ≤ E) {e : R} (heD : e ∈ D) :
    (e, diagHom n (delta cU E ι e)) ∈ SUTorus.suPairs
      (ρ.comp (Subgroup.inclusion hle)) := by
  have heE : e ∈ E := hDE heD
  set v : Fin n → ZMod 3 := ι (Additive.ofMul ⟨e, heE⟩) with hv
  have hBmat : ((diagHom n (delta cU E ι e) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) := by
    rw [dg_val]
    ext a b
    rw [coe_diagHom, coe_diagHom]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, delta_apply cU E ι heE a]
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
  have hBGU : ((diagHom n (delta cU E ι e) : GL (Fin n) M)) ∈ heldGU n M τ hτ := by
    rw [mem_heldGU, hBmat]
    exact mem_heldGU.mp (dg hM hτ2 cU v).2
  have hBeq : ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) =
      diagHom n (delta cU E ι e) := by
    apply Units.ext
    exact hBmat.symm
  refine (SUTorus.mem_suPairs).mpr ⟨diagHom_mem_normalizer hSU hBGU, ?_⟩
  intro u v' huv
  have hGL : ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) *
      ((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) *
      ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M)⁻¹ =
      ((v' : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) := by
    rw [hBeq]
    exact huv.symm
  have hheld : (dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) *
      (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) *
      (dg hM hτ2 cU v : ↥(heldGU n M τ hτ))⁻¹ =
      (⟨v', hle v'.2⟩ : ↥(heldGU n M τ hτ)) := by
    apply Subtype.ext
    exact hGL
  have heq : e = ρ (dg hM hτ2 cU v) := dg_eq_of_mem hM hτ2 hcU hU ι hι heE
  rw [heq]
  calc ρ (dg hM hτ2 cU v) * (ρ.comp (Subgroup.inclusion hle)) u *
        (ρ (dg hM hτ2 cU v))⁻¹
      = ρ (dg hM hτ2 cU v) * ρ (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) *
          (ρ (dg hM hτ2 cU v))⁻¹ := rfl
    _ = ρ ((dg hM hτ2 cU v) * (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) *
          (dg hM hτ2 cU v)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = ρ (⟨v', hle v'.2⟩ : ↥(heldGU n M τ hτ)) := by rw [hheld]
    _ = (ρ.comp (Subgroup.inclusion hle)) v' := rfl

lemma coord_const {m : ℕ} {M : Type} [Field M] {cU : Mˣ}
    (hinj : ∀ a b : ZMod 3, (cU : M) ^ a.val = (cU : M) ^ b.val → a = b)
    {E : Subgroup R} {ι : Additive ↥E ≃+ (Fin (m + 1) → ZMod 3)} {D : Subgroup R}
    {i : Fin (m + 1)} {e : R} (he : e ∈ E) (heD : e ∈ D) {j k : Fin (m + 1)}
    (hj : j ∈ LinTorus.diagClass (D : Set R) (delta cU E ι) i)
    (hk : k ∈ LinTorus.diagClass (D : Set R) (delta cU E ι) i) :
    ι (Additive.ofMul ⟨e, he⟩) j = ι (Additive.ofMul ⟨e, he⟩) k := by
  have hδeq : delta cU E ι e j = delta cU E ι e k :=
    LinTorus.eq_of_mem_diagClass hj hk heD
  rw [delta_apply cU E ι he j, delta_apply cU E ι he k] at hδeq
  exact hinj _ _ (congrArg (fun u : Mˣ => (u : M)) hδeq)

lemma block_comm {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {ρ : ↥(heldGU n M τ hτ) →* R} {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {I : Finset (Fin n)} {v : Fin n → ZMod 3}
    (hvconst : ∀ j ∈ I, ∀ k ∈ I, v j = v k)
    {u : ↥(unitarySU 2 1 M n)} (hu : u ∈ TableBUE.blockSU I) :
    ρ (dg hM hτ2 cU v) * (ρ.comp (Subgroup.inclusion hle)) u =
      (ρ.comp (Subgroup.inclusion hle)) u * ρ (dg hM hτ2 cU v) := by
  have hconst : ∀ j ∈ I, ∀ k ∈ I,
      (fun j => cU ^ (v j).val) j = (fun j => cU ^ (v j).val) k := by
    intro j hj k hk
    show cU ^ (v j).val = cU ^ (v k).val
    rw [hvconst j hj k hk]
  have hX : TableBUE.IsBlockOn I (((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) := TableBUE.mem_blockSU.mp hu
  have hc := TableBUE.diagHom_mul_comm_of_isBlockOn (K := M) (d := n)
    (S := I) (σ := fun j => cU ^ (v j).val) hconst hX
  have hGL : ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) *
      ((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) =
      ((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) *
      ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) := by
    have hBeq : ((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) =
        diagHom n (fun j => cU ^ (v j).val) := Units.ext (dg_val hM hτ2 cU v)
    rw [hBeq]
    exact hc
  have hheld : (dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) *
      (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) =
      (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) * (dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) := by
    apply Subtype.ext
    exact hGL
  calc ρ (dg hM hτ2 cU v) * (ρ.comp (Subgroup.inclusion hle)) u
      = ρ (dg hM hτ2 cU v) * ρ (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) := rfl
    _ = ρ ((dg hM hτ2 cU v) * (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ))) := by rw [map_mul]
    _ = ρ ((⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) * (dg hM hτ2 cU v)) := by rw [hheld]
    _ = ρ (⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) * ρ (dg hM hτ2 cU v) := by rw [map_mul]
    _ = (ρ.comp (Subgroup.inclusion hle)) u * ρ (dg hM hτ2 cU v) := rfl

lemma dg_mem_D {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    {D : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {I : Finset (Fin n)} {J : Subgroup R}
    (hJI : J ≤ Subgroup.map (ρ.comp (Subgroup.inclusion hle)) (TableBUE.blockSU I))
    (hEJ : E ⊓ Subgroup.centralizer (J : Set R) = D)
    {v : Fin n → ZMod 3} (hvconst : ∀ j ∈ I, ∀ k ∈ I, v j = v k) :
    ρ (dg hM hτ2 cU v) ∈ D := by
  have hE : ρ (dg hM hτ2 cU v) ∈ E := dg_mem_E hM hτ2 hU v
  have hCJ : ρ (dg hM hτ2 cU v) ∈ Subgroup.centralizer (J : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨u, hu, hju⟩ := Subgroup.mem_map.mp (hJI hj)
    rw [← hju]
    exact (block_comm hM hτ2 hvconst hu).symm
  have hinf := Subgroup.mem_inf.mpr ⟨hE, hCJ⟩
  rwa [hEJ] at hinf

lemma exists_psi_setup {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2) (m : ℕ)
    {ρ : ↥(heldGU (m + 1) M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) :
    ∃ (_hSU : unitarySU 2 1 M (m + 1) = heldSU (m + 1) M τ hτ)
      (hle : unitarySU 2 1 M (m + 1) ≤ heldGU (m + 1) M τ hτ),
      Function.Injective (ρ.comp (Subgroup.inclusion hle)) ∧
      (ρ.comp (Subgroup.inclusion hle)).ker ≤
        Subgroup.center ↥(unitarySU 2 1 M (m + 1)) ∧
      (ρ.comp (Subgroup.inclusion hle)).range = L := by
  have hSU : unitarySU 2 1 M (m + 1) = heldSU (m + 1) M τ hτ := by
    have h := hct_heldSU_eq_statedSU (a := m + 1) (Q := 2) (M := M) (hτ := hτ) hτ2
    show CFSG.Open.StatedSU (m + 1) (2 ^ 1) M = heldSU (m + 1) M τ hτ
    rw [pow_one]
    exact h.symm
  have hle : unitarySU 2 1 M (m + 1) ≤ heldGU (m + 1) M τ hτ := by
    rw [hSU]
    exact inf_le_left
  refine ⟨hSU, hle, ?_, ?_, ?_⟩
  · intro a b h
    have h1 : Subgroup.inclusion hle a = Subgroup.inclusion hle b := hU.1 h
    apply Subtype.ext
    simpa [Subgroup.coe_inclusion] using congrArg
      (fun y : ↥(heldGU (m + 1) M τ hτ) => (y : GL (Fin (m + 1)) M)) h1
  · have hψker : (ρ.comp (Subgroup.inclusion hle)).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (by
        intro a b h
        have h1 : Subgroup.inclusion hle a = Subgroup.inclusion hle b := hU.1 h
        apply Subtype.ext
        simpa [Subgroup.coe_inclusion] using congrArg
          (fun y : ↥(heldGU (m + 1) M τ hτ) => (y : GL (Fin (m + 1)) M)) h1)
    rw [hψker]
    exact bot_le
  · have h1 : (ρ.comp (Subgroup.inclusion hle)).range =
        ((unitarySU 2 1 M (m + 1)).subgroupOf (heldGU (m + 1) M τ hτ)).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have h2 : ((unitarySU 2 1 M (m + 1)).subgroupOf
        (heldGU (m + 1) M τ hτ)).map ρ =
        ((heldSU (m + 1) M τ hτ).subgroupOf (heldGU (m + 1) M τ hτ)).map ρ := by
      rw [hSU]
    exact h1.trans (h2.trans hU.2.2.2.1.symm)

end FrameSign

end CFSG.StandardType

end
