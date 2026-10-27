module

public import CFSG.Timmesfeld.ARS.FrameSL3
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType.Universal Matrix

namespace Linear

section Elem

variable (K : Type*) [Field K]

theorem upperElt_eq_tv (t : K) : upperElt K t = tv 0 1 t := by
  rw [tv_of_ne (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperElt, SpecialLinearGroup.transvection_coe]

theorem lowerElt_eq_tv (t : K) : lowerElt K t = tv 1 0 t := by
  rw [tv_of_ne (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerElt, SpecialLinearGroup.transvection_coe]

theorem tv_mem_upperUnipotent (t : K) : tv 0 1 t ∈ upperUnipotent K := by
  rw [← upperElt_eq_tv]
  exact (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩

theorem tv_mem_lowerUnipotent (t : K) : tv 1 0 t ∈ lowerUnipotent K := by
  rw [← lowerElt_eq_tv]
  exact (mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩

end Elem

section Hom

variable {G : Type*} [Group G] {F : Type*} [Field F]

theorem range_tv_upper (ρ : SpecialLinearGroup (Fin 2) F →* G) :
    Set.range (fun t => ρ (tv 0 1 t)) = ((upperUnipotent F).map ρ : Set G) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact Subgroup.mem_map_of_mem ρ (tv_mem_upperUnipotent F t)
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).1 ha
    exact ⟨t, by rw [upperElt_eq_tv]⟩

theorem range_tv_lower (ρ : SpecialLinearGroup (Fin 2) F →* G) :
    Set.range (fun t => ρ (tv 1 0 t)) = ((lowerUnipotent F).map ρ : Set G) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact Subgroup.mem_map_of_mem ρ (tv_mem_lowerUnipotent F t)
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff F).1 ha
    exact ⟨t, by rw [lowerElt_eq_tv]⟩

theorem exists_mulEquiv_of_injective {ρ : SpecialLinearGroup (Fin 2) F →* G}
    (hρ : Function.Injective ρ) {A B : Subgroup G} (hA : (upperUnipotent F).map ρ = A)
    (hB : (lowerUnipotent F).map ρ = B) :
    ∃ φ : ↥(A ⊔ B) ≃* SpecialLinearGroup (Fin 2) F,
      (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent F ∧
      (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = lowerUnipotent F ∧
      ∀ g, (φ.symm g : G) = ρ g := by
  have hrange : ρ.range = A ⊔ B := by
    rw [MonoidHom.range_eq_map, ← NaturalModule.upperUnipotent_sup_lowerUnipotent,
      Subgroup.map_sup, hA, hB]
  let e : SpecialLinearGroup (Fin 2) F ≃* ↥(A ⊔ B) :=
    (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ g, (e g : G) = ρ g := fun g => rfl
  have key : ∀ (H : Subgroup G) (S : Subgroup (SpecialLinearGroup (Fin 2) F)), S.map ρ = H →
      (H.subgroupOf (A ⊔ B)).map e.symm.toMonoidHom = S := by
    intro H S hS
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf, ← hS] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hy' : y = e.symm x :=
        e.injective (Subtype.ext (by rw [he, hxy, MulEquiv.apply_symm_apply]))
      rw [MulEquiv.coe_toMonoidHom, ← hy']
      exact hy
    · intro hg
      refine ⟨e g, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf, he, ← hS]
      exact Subgroup.mem_map_of_mem ρ hg
  exact ⟨e.symm, key A _ hA, key B _ hB, fun g => by rw [MulEquiv.symm_symm, he]⟩

theorem injective_of_mulEquiv {A B : Subgroup G} (φ : ↥(A ⊔ B) ≃* SpecialLinearGroup (Fin 2) F)
    (hA : (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent F)
    (hB : (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = lowerUnipotent F) :
    Function.Injective ((A ⊔ B).subtype.comp φ.symm.toMonoidHom) ∧
      (upperUnipotent F).map ((A ⊔ B).subtype.comp φ.symm.toMonoidHom) = A ∧
      (lowerUnipotent F).map ((A ⊔ B).subtype.comp φ.symm.toMonoidHom) = B := by
  have key : ∀ H : Subgroup G, H ≤ A ⊔ B → ∀ S : Subgroup (SpecialLinearGroup (Fin 2) F),
      (H.subgroupOf (A ⊔ B)).map φ.toMonoidHom = S →
      S.map ((A ⊔ B).subtype.comp φ.symm.toMonoidHom) = H := by
    intro H hH S hS
    ext g
    rw [Subgroup.mem_map, ← hS]
    constructor
    · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hx
    · intro hg
      refine ⟨φ ⟨g, hH hg⟩, ⟨⟨g, hH hg⟩, ?_, rfl⟩, by simp⟩
      simpa [Subgroup.mem_subgroupOf] using hg
  exact ⟨(A ⊔ B).subtype_injective.comp φ.symm.injective, key A le_sup_left _ hA,
    key B le_sup_right _ hB⟩

end Hom

section Center

variable (F : Type*) [Field F] [CharP F 2]

theorem eq_one_of_mem_center {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr
  have h2 : (r + 1) ^ 2 = 0 := by rw [CharTwo.add_sq, hr, one_pow, CharTwo.add_self_eq_zero]
  have hr1 : r = 1 := by
    rw [← CharTwo.neg_eq (1 : F), ← add_eq_zero_iff_eq_neg]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
  refine Subtype.ext ?_
  rw [← hrg, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_map_mem_center {H : Type*} [Group H]
    {ι : SpecialLinearGroup (Fin 2) F →* H} (hι : Function.Injective ι)
    {g : SpecialLinearGroup (Fin 2) F} (hg : ι g ∈ Subgroup.center H) : g = 1 := by
  refine eq_one_of_mem_center F (Subgroup.mem_center_iff.2 fun h => hι ?_)
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 hg (ι h)

end Center

section Swap

variable (F : Type*) [Field F] (N : ℕ)

@[expose] def revMat (M : Matrix (Fin N) (Fin N) F) : Matrix (Fin N) (Fin N) F :=
  (M.submatrix Fin.revPerm Fin.revPerm)ᵀ

theorem revMat_mul (M M' : Matrix (Fin N) (Fin N) F) :
    revMat F N (M * M') = revMat F N M' * revMat F N M := by
  rw [revMat, revMat, revMat, ← Matrix.submatrix_mul_equiv _ _ Fin.revPerm Fin.revPerm Fin.revPerm,
    Matrix.transpose_mul]

theorem revMat_one : revMat F N 1 = 1 := by
  rw [revMat, Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem det_revMat (M : Matrix (Fin N) (Fin N) F) : (revMat F N M).det = M.det := by
  rw [revMat, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]

@[expose] noncomputable def revHom :
    SpecialLinearGroup (Fin N) F →* SpecialLinearGroup (Fin N) F where
  toFun g := ⟨revMat F N ((g⁻¹ : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F), by
    rw [det_revMat]
    exact (g⁻¹).2⟩
  map_one' := by
    apply Subtype.ext
    show revMat F N (((1 : SpecialLinearGroup (Fin N) F)⁻¹ : SpecialLinearGroup (Fin N) F) :
      Matrix (Fin N) (Fin N) F) = ((1 : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F)
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, revMat_one]
  map_mul' g h := by
    apply Subtype.ext
    show revMat F N (((g * h)⁻¹ : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) =
      revMat F N ((g⁻¹ : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) *
        revMat F N ((h⁻¹ : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, revMat_mul]

theorem revHom_apply (g : SpecialLinearGroup (Fin N) F) (a b : Fin N) :
    (revHom F N g : Matrix (Fin N) (Fin N) F) a b =
      ((g⁻¹ : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F) b.rev a.rev :=
  rfl

theorem revHom_tv_of_ne {i j : Fin N} (hij : i ≠ j) (c : F) :
    revHom F N (tv i j c) = tv j.rev i.rev (-c) := by
  have hji : j.rev ≠ i.rev := fun h => hij (Fin.rev_injective h).symm
  rw [tv_of_ne hij, tv_of_ne hji]
  ext a b
  rw [revHom_apply, Matrix.SpecialLinearGroup.transvection_inv]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  congr 1
  · exact if_congr (Fin.rev_inj.trans eq_comm) rfl rfl
  · refine if_congr ?_ rfl rfl
    rw [Fin.rev_eq_iff, Fin.rev_eq_iff]
    exact and_comm

theorem revHom_tv [CharP F 2] (i j : Fin N) (c : F) :
    revHom F N (tv i j c) = tv j.rev i.rev c := by
  by_cases hij : i = j
  · subst hij
    simp [tv]
  · rw [revHom_tv_of_ne F N hij, CharTwo.neg_eq]

end Swap

section Step

variable {G : Type*} [Group G] [Finite G] {R : Set (Subgroup G)} (hR : IsRootClass R)
  (hiso : NoIsolated R) {A B A' B' : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hA' : A' ∈ R)
  (hB' : B' ∈ R) (hAB : Special R A B) (hAA' : Opposite A A') (hBB' : Opposite B B')
  (h1 : Commuting A' B) (h2 : ⁅A', ⁅A, B⁆⁆ = B) (h3 : Commuting A B')
  (h4 : ⁅⁅A, B⁆, B'⁆ = A) (h5 : Special R A' B') {n : ℕ} (hq : Nat.card A = 2 ^ n)
include hR hiso hA hB hA' hB' hAB hAA' hBB' h1 h2 h3 h4 h5 hq

theorem exists_sl3_right {ρ : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G}
    (hρ : Function.Injective ρ) (hρA : (upperUnipotent _).map ρ = A)
    (hρA' : (lowerUnipotent _).map ρ = A') :
    ∃ (ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* G)
      (ρ' : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G),
      (Function.Injective ρ' ∧ (upperUnipotent _).map ρ' = B ∧ (lowerUnipotent _).map ρ' = B') ∧
      ∀ c, ψ (tv 0 1 c) = ρ (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ (tv 1 0 c) ∧
        ψ (tv 1 2 c) = ρ' (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' (tv 1 0 c) := by
  set F := GaloisField 2 n
  obtain ⟨φ₁, hφ₁, hφ₁', hφρ⟩ := exists_mulEquiv_of_injective hρ hρA hρA'
  obtain ⟨n₂, -, hq₂, φ₂, hφ₂, hφ₂'⟩ := hBB'.exists_mulEquiv_SL2' hR hB
  obtain rfl : n₂ = n :=
    Nat.pow_right_injective le_rfl (hq₂.symm.trans ((hR.card_eq hB hA).trans hq))
  obtain ⟨xA, xB, xC, xA', xB', xC', rfl, rfl, rA, rB, rC, rA', rB', rC', aA, aB, aC, aA', aB',
    aC', r₁, r₂, r₃, r₄, r₅, r₆⟩ :=
    FrameSL3.exists_coords hR hiso hA hB hA' hB' hAB hAA' hBB' h1 h2 h3 h4 h5 φ₁ hφ₁ hφ₁' φ₂
      hφ₂ hφ₂'
  have mem : ∀ {f : F → G} {H : Subgroup G}, Set.range f = (H : Set G) → ∀ s, f s ∈ H :=
    fun hf s => by
      rw [← SetLike.mem_coe, ← hf]
      exact ⟨s, rfl⟩
  obtain ⟨ψ, hψ⟩ := FrameSL3.exists_hom_of_steinberg
    (FrameSL3.fam_add aA aB aC aA' aB' aC')
    (FrameSL3.fam_comm aA aB aC aA' aB' aC'
      (fun s t => (hAB.2.1 _ (mem rC t) _ (mem rA s)).symm)
      (fun s t => h3 _ (mem rA s) _ (mem rB' t))
      (fun s t => (hAB.2.2 _ (mem rC t) _ (mem rB s)).symm)
      (fun s t => (h1 _ (mem rA' t) _ (mem rB s)).symm)
      (fun s t => (h5.2.1 _ (mem rC' t) _ (mem rA' s)).symm)
      (fun s t => (h5.2.2 _ (mem rC' t) _ (mem rB' s)).symm) r₁ r₂ r₃ r₄ r₅ r₆)
  have v01 : ∀ c, ψ (tv 0 1 c) = ρ (tv 0 1 c) := fun c => by
    rw [← upperElt_eq_tv, ← hφρ, tv_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
    exact hψ 0 1 _ c
  have v10 : ∀ c, ψ (tv 1 0 c) = ρ (tv 1 0 c) := fun c => by
    rw [← lowerElt_eq_tv, ← hφρ, tv_of_ne (show (1 : Fin 3) ≠ 0 by decide)]
    exact hψ 1 0 _ c
  have v12 : ∀ c, ψ (tv 1 2 c) = xB c := fun c => by
    rw [tv_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
    exact hψ 1 2 _ c
  have v21 : ∀ c, ψ (tv 2 1 c) = xB' c := fun c => by
    rw [tv_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
    exact hψ 2 1 _ c
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (SpecialLinear.isQuasisimple 2 F le_rfl) ⟨tv 0 1 1, fun h => ?_⟩
    rw [v01, ← map_one ρ] at h
    have h' := hρ h
    rw [← upperElt_eq_tv, ← upperElt_zero F] at h'
    exact one_ne_zero (upperElt_injective F h')
  let e : Fin 2 ↪ Fin 3 := ⟨![1, 2], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩
  let ρ' : SpecialLinearGroup (Fin 2) F →* G := ψ.comp (blockHom F e)
  have w01 : ∀ c, ρ' (tv 0 1 c) = ψ (tv 1 2 c) := fun c => by
    simp only [ρ', MonoidHom.comp_apply]
    rw [blockHom_tv F e (by decide)]
    rfl
  have w10 : ∀ c, ρ' (tv 1 0 c) = ψ (tv 2 1 c) := fun c => by
    simp only [ρ', MonoidHom.comp_apply]
    rw [blockHom_tv F e (by decide)]
    rfl
  have hinj : Function.Injective ρ' := by
    refine (injective_iff_map_eq_one ρ').2 fun g hg => ?_
    exact eq_one_of_map_mem_center F (blockHom_injective F e) (hker hg)
  have hup : (upperUnipotent F).map ρ' = B := by
    apply SetLike.coe_injective
    rw [← range_tv_upper, ← rB]
    congr 1
    funext t
    rw [w01, v12]
  have hlow : (lowerUnipotent F).map ρ' = B' := by
    apply SetLike.coe_injective
    rw [← range_tv_lower, ← rB']
    congr 1
    funext t
    rw [w10, v21]
  exact ⟨ψ, ρ', ⟨hinj, hup, hlow⟩, fun c =>
    ⟨v01 c, v10 c, (w01 c).symm, (w10 c).symm⟩⟩

theorem exists_sl3_left {ρ' : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G}
    (hρ' : Function.Injective ρ') (hρ'B : (upperUnipotent _).map ρ' = B)
    (hρ'B' : (lowerUnipotent _).map ρ' = B') :
    ∃ (ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* G)
      (ρ : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G),
      (Function.Injective ρ ∧ (upperUnipotent _).map ρ = A ∧ (lowerUnipotent _).map ρ = A') ∧
      ∀ c, ψ (tv 0 1 c) = ρ (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ (tv 1 0 c) ∧
        ψ (tv 1 2 c) = ρ' (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' (tv 1 0 c) := by
  have hBA : ⁅B, A⁆ = ⁅A, B⁆ := Subgroup.commutator_comm B A
  obtain ⟨ψ₀, ρ, hρ, hψ₀⟩ := exists_sl3_right hR hiso hB hA hB' hA' hAB.symm hBB' hAA' h3.symm
    (by rw [Subgroup.commutator_comm B', hBA]; exact h4) h1.symm
    (by rw [hBA, Subgroup.commutator_comm ⁅A, B⁆ A']; exact h2) h5.symm
    ((hR.card_eq hB hA).trans hq) hρ' hρ'B hρ'B'
  refine ⟨ψ₀.comp (revHom _ 3), ρ, hρ, fun c => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hψ₀ c
  simp only [MonoidHom.comp_apply, revHom_tv]
  exact ⟨e3, e4, e1, e2⟩

end Step

theorem exists_path {T : Type*} {m : ℕ} (N : ℕ → T → Prop) (E : T → T → Prop)
    (hf : ∀ i t, i + 1 < m → N i t → ∃ t', N (i + 1) t' ∧ E t t')
    (hb : ∀ i t', i + 1 < m → N (i + 1) t' → ∃ t, N i t ∧ E t t')
    {k₀ : ℕ} (hk₀ : k₀ < m) {t₀ : T} (h₀ : N k₀ t₀) :
    ∃ ρ : ℕ → T, ρ k₀ = t₀ ∧ (∀ k < m, N k (ρ k)) ∧ ∀ i, i + 1 < m → E (ρ i) (ρ (i + 1)) := by
  classical
  have hf' : ∀ i t, ∃ t', i + 1 < m → N i t → N (i + 1) t' ∧ E t t' := by
    intro i t
    by_cases h : i + 1 < m ∧ N i t
    · obtain ⟨t', h1, h2⟩ := hf i t h.1 h.2
      exact ⟨t', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨t, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hb' : ∀ i t', ∃ t, i + 1 < m → N (i + 1) t' → N i t ∧ E t t' := by
    intro i t'
    by_cases h : i + 1 < m ∧ N (i + 1) t'
    · obtain ⟨t, h1, h2⟩ := hb i t' h.1 h.2
      exact ⟨t, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨t', fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose nxt hnxt using hf'
  choose prv hprv using hb'
  let f : ℕ → T := fun d => Nat.rec (motive := fun _ => T) t₀ (fun d t => nxt (k₀ + d) t) d
  let g : ℕ → T := fun d => Nat.rec (motive := fun _ => T) t₀ (fun d t => prv (k₀ - d - 1) t) d
  have hf0 : f 0 = t₀ := rfl
  have hfs : ∀ d, f (d + 1) = nxt (k₀ + d) (f d) := fun d => rfl
  have hg0 : g 0 = t₀ := rfl
  have hgs : ∀ d, g (d + 1) = prv (k₀ - d - 1) (g d) := fun d => rfl
  have hfN : ∀ d, k₀ + d < m → N (k₀ + d) (f d) := by
    intro d
    induction d with
    | zero => intro _; rw [hf0]; exact h₀
    | succ d ih =>
      intro hd
      rw [hfs, ← Nat.add_assoc]
      exact (hnxt _ _ (by omega) (ih (by omega))).1
  have hfE : ∀ d, k₀ + d + 1 < m → E (f d) (f (d + 1)) := fun d hd => by
    rw [hfs]
    exact (hnxt _ _ hd (hfN d (by omega))).2
  have hgN : ∀ d, d ≤ k₀ → N (k₀ - d) (g d) := by
    intro d
    induction d with
    | zero => intro _; rw [hg0]; exact h₀
    | succ d ih =>
      intro hd
      rw [hgs, show k₀ - (d + 1) = k₀ - d - 1 by omega]
      refine (hprv _ _ (by omega) ?_).1
      rw [show k₀ - d - 1 + 1 = k₀ - d by omega]
      exact ih (by omega)
  have hgE : ∀ d, d + 1 ≤ k₀ → E (g (d + 1)) (g d) := fun d hd => by
    rw [hgs]
    refine (hprv _ _ (by omega) ?_).2
    rw [show k₀ - d - 1 + 1 = k₀ - d by omega]
    exact hgN d (by omega)
  refine ⟨fun k => if k₀ ≤ k then f (k - k₀) else g (k₀ - k), ?_, fun k hk => ?_,
    fun i hi => ?_⟩
  · simp only [le_refl, ite_true, Nat.sub_self, hf0]
  · dsimp only
    by_cases h : k₀ ≤ k
    · rw [ite_eq_left h]
      have := hfN (k - k₀) (by omega)
      rwa [Nat.add_sub_cancel' h] at this
    · rw [ite_eq_right h]
      have := hgN (k₀ - k) (by omega)
      rwa [Nat.sub_sub_self (by omega)] at this
  · dsimp only
    by_cases h : k₀ ≤ i
    · rw [ite_eq_left h, ite_eq_left (by omega), show i + 1 - k₀ = i - k₀ + 1 by omega]
      exact hfE _ (by omega)
    · by_cases h' : k₀ ≤ i + 1
      · rw [ite_eq_right h, ite_eq_left h', show k₀ - i = 0 + 1 by omega,
          show i + 1 - k₀ = 0 by omega, hf0, ← hg0]
        exact hgE 0 (by omega)
      · rw [ite_eq_right h, ite_eq_right h', show k₀ - i = k₀ - (i + 1) + 1 by omega]
        exact hgE _ (by omega)

theorem exists_chain {G : Type*} [Group G] [Finite G] {R : Set (Subgroup G)}
    (hR : IsRootClass R) (hiso : NoIsolated R) {m : ℕ} {A B : Fin m → Subgroup G}
    (hA : ∀ k, A k ∈ R) (hB : ∀ k, B k ∈ R) (hAB : ∀ k, Opposite (A k) (B k))
    (hcfg : ∀ i j : Fin m, j.val = i.val + 1 → Special R (A i) (A j) ∧ Commuting (B i) (A j) ∧
      ⁅B i, ⁅A i, A j⁆⁆ = A j ∧ Commuting (A i) (B j) ∧ ⁅⁅A i, A j⁆, B j⁆ = A i ∧
      Special R (B i) (B j))
    {n : ℕ} (k₀ : Fin m) (hq : Nat.card (A k₀) = 2 ^ n)
    {ρ₀ : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G} (hρ₀ : Function.Injective ρ₀)
    (hρ₀A : (upperUnipotent _).map ρ₀ = A k₀) (hρ₀B : (lowerUnipotent _).map ρ₀ = B k₀) :
    ∃ ρ : Fin m → SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* G, ρ k₀ = ρ₀ ∧
      (∀ k, Function.Injective (ρ k) ∧ (upperUnipotent _).map (ρ k) = A k ∧
        (lowerUnipotent _).map (ρ k) = B k) ∧
      ∀ i j : Fin m, j.val = i.val + 1 →
        ∃ ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* G, ∀ c,
          ψ (tv 0 1 c) = ρ i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ i (tv 1 0 c) ∧
          ψ (tv 1 2 c) = ρ j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ j (tv 1 0 c) := by
  set F := GaloisField 2 n
  let Nd : ℕ → (SpecialLinearGroup (Fin 2) F →* G) → Prop := fun k ρ =>
    ∃ hk : k < m, Function.Injective ρ ∧ (upperUnipotent F).map ρ = A ⟨k, hk⟩ ∧
      (lowerUnipotent F).map ρ = B ⟨k, hk⟩
  let Ed : (SpecialLinearGroup (Fin 2) F →* G) → (SpecialLinearGroup (Fin 2) F →* G) → Prop :=
    fun ρ ρ' => ∃ ψ : SpecialLinearGroup (Fin 3) F →* G, ∀ c,
      ψ (tv 0 1 c) = ρ (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ' (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' (tv 1 0 c)
  have hq' : ∀ k, Nat.card (A k) = 2 ^ n := fun k => (hR.card_eq (hA k) (hA k₀)).trans hq
  have hfwd : ∀ i ρ, i + 1 < m → Nd i ρ → ∃ ρ', Nd (i + 1) ρ' ∧ Ed ρ ρ' := by
    rintro i ρ hi ⟨hi', hinj, hup, hlow⟩
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcfg ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
    obtain ⟨ψ, ρ', ⟨h1, h2, h3⟩, hψ⟩ := exists_sl3_right hR hiso (hA _) (hA _) (hB _) (hB _) c1
      (hAB _) (hAB _) c2 c3 c4 c5 c6 (hq' _) hinj hup hlow
    exact ⟨ρ', ⟨hi, h1, h2, h3⟩, ψ, hψ⟩
  have hbwd : ∀ i ρ', i + 1 < m → Nd (i + 1) ρ' → ∃ ρ, Nd i ρ ∧ Ed ρ ρ' := by
    rintro i ρ' hi ⟨_, hinj, hup, hlow⟩
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcfg ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
    obtain ⟨ψ, ρ, ⟨h1, h2, h3⟩, hψ⟩ := exists_sl3_left hR hiso (hA _) (hA _) (hB _) (hB _) c1
      (hAB _) (hAB _) c2 c3 c4 c5 c6 (hq' _) hinj hup hlow
    exact ⟨ρ, ⟨by omega, h1, h2, h3⟩, ψ, hψ⟩
  obtain ⟨ρ, hρ0, hρN, hρE⟩ := exists_path Nd Ed hfwd hbwd k₀.2 ⟨k₀.2, hρ₀, hρ₀A, hρ₀B⟩
  refine ⟨fun k => ρ k.val, hρ0, fun k => ?_, fun i j hij => ?_⟩
  · obtain ⟨_, h1, h2, h3⟩ := hρN k.val k.2
    exact ⟨h1, h2, h3⟩
  · simp only [hij]
    exact hρE i.val (by omega)

end Linear

end CFSG.Timmesfeld.ARS
