module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.Ch9.FFC

open CFSG.QuasithinUnique.Setup.X6 CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Product

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_mul_of_mem_sup_of_mul_comm {D T : Subgroup Y}
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) {x : Y} (hx : x ∈ D ⊔ T) :
    ∃ d ∈ D, ∃ t ∈ T, d * t = x := by
  let H : Subgroup Y :=
    { carrier := (D : Set Y) * (T : Set Y)
      mul_mem' := by
        rintro _ _ ⟨d₁, hd₁, t₁, ht₁, rfl⟩ ⟨d₂, hd₂, t₂, ht₂, rfl⟩
        have h : t₁ * d₂ ∈ (D : Set Y) * (T : Set Y) := by
          rw [hDT]
          exact Set.mul_mem_mul ht₁ hd₂
        obtain ⟨d₃, hd₃, t₃, ht₃, h3⟩ := h
        refine ⟨d₁ * d₃, D.mul_mem hd₁ hd₃, t₃ * t₂, T.mul_mem ht₃ ht₂, ?_⟩
        have h3' : d₃ * t₃ = t₁ * d₂ := h3
        simp only
        rw [mul_assoc, ← mul_assoc d₃, h3']
        group
      one_mem' := ⟨1, D.one_mem, 1, T.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨d, hd, t, ht, rfl⟩
        have h : t⁻¹ * d⁻¹ ∈ (D : Set Y) * (T : Set Y) := by
          rw [hDT]
          exact Set.mul_mem_mul (T.inv_mem ht) (D.inv_mem hd)
        simpa [mul_inv_rev] using h }
  have hle : D ⊔ T ≤ H := sup_le (fun d hd => ⟨d, hd, 1, T.one_mem, mul_one d⟩)
    (fun t ht => ⟨1, D.one_mem, t, ht, one_mul t⟩)
  obtain ⟨d, hd, t, ht, h⟩ := hle hx
  exact ⟨d, hd, t, ht, h⟩

theorem isSolvable_sup_of_mul_comm {D T : Subgroup Y} (hD : IsPGroup 3 D) (hT : IsPGroup 2 T)
    (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y)) :
    Group.IsSolvable ↥(D ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hD
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT
  have hle : Nat.card ↥(D ⊔ T) ≤ Nat.card D * Nat.card T := by
    let f : ↥D × ↥T → ↥(D ⊔ T) := fun p =>
      ⟨(p.1 : Y) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
        (Subgroup.mem_sup_right p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨d, hd, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_mul_comm hDT hx
      exact ⟨(⟨d, hd⟩, ⟨t, ht⟩), rfl⟩
    have h := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at h
  have hdvd : Nat.card D * Nat.card T ∣ Nat.card ↥(D ⊔ T) := by
    have h1 : Nat.card D ∣ Nat.card ↥(D ⊔ T) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card T ∣ Nat.card ↥(D ⊔ T) := Subgroup.card_dvd_of_le le_sup_right
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ h1 h2
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have hcard : Nat.card ↥(D ⊔ T) = 3 ^ a * 2 ^ b := by
    rw [← ha, ← hb]
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have : Fintype ↥(D ⊔ T) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three
    Nat.prime_two (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

end Product

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_dInf (Q : Subgroup X) : Q ≤ Subgroup.normalizer (dInf Q : Set X) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (dInf Q).map (MulAut.conj q).toMonoidHom ≤ dInf Q := by
    refine le_dInf_of_perfect (map_isPerfect (dInf_isPerfect Q) _) ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Q.mul_mem (Q.mul_mem hq (dInf_le Q hx)) (Q.inv_mem hq)
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj q).injective).ge

section Block

variable {U B : Subgroup X}

theorem le_of_perfect_of_le_sup (hU : IsPGroup 2 U) (hUB : U ≤ Subgroup.normalizer (B : Set X))
    {R : Subgroup X} (hR : Group.IsPerfect ↥R) (hRM : R ≤ B ⊔ U) : R ≤ B := by
  have hUs : Group.IsSolvable ↥U := by
    have := hU.isNilpotent
    infer_instance
  exact CFSG.Goldschmidt.G37.le_of_perfect_of_le_sup hR (by rw [sup_comm]; exact hRM) hUB hUs

theorem dInf_sup_eq (hU : IsPGroup 2 U) (hUB : U ≤ Subgroup.normalizer (B : Set X))
    (hB : Group.IsPerfect ↥B) : dInf (B ⊔ U) = B :=
  le_antisymm (le_of_perfect_of_le_sup hU hUB (dInf_isPerfect _) (dInf_le _))
    (le_dInf_of_perfect hB le_sup_left)

theorem sup_ne_top (hU : IsPGroup 2 U) (hUB : U ≤ Subgroup.normalizer (B : Set X))
    (hX : Group.IsPerfect X) (hBX : B ≠ ⊤) : B ⊔ U ≠ ⊤ := fun htop =>
  hBX (top_le_iff.mp (le_of_perfect_of_le_sup hU hUB (Group.IsPerfect.top_iff.mpr hX)
    (by rw [htop])))

omit [Finite X] in
theorem not_isSolvable_sup (hBs : ¬ Group.IsSolvable ↥B) : ¬ Group.IsSolvable ↥(B ⊔ U) :=
  fun _ => hBs (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (le_sup_left : B ≤ B ⊔ U)) (Subgroup.inclusion_injective _))

end Block

theorem le_normalizer_of_residual {U : Subgroup X} {P : Fin 2 → Subgroup X}
    (hres : ResidualOvergroupsAt X U P) (hnorm : ∀ j, Subgroup.normalizer (U : Set X) ≤ P j)
    (hsolv : ∀ A : Subgroup X, U ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer (U : Set X))
    (hU : IsPGroup 2 U) (hX : Group.IsPerfect X) {B D : Subgroup X} (hB : Group.IsPerfect ↥B)
    (hBs : ¬ Group.IsSolvable ↥B) (hBX : B ≠ ⊤) (hUB : U ≤ Subgroup.normalizer (B : Set X))
    (hD : Group.IsSolvable ↥(D ⊔ U)) : D ≤ Subgroup.normalizer (B : Set X) := by
  obtain ⟨j, -, hdj⟩ := hres.2.2.2.2.1 (B ⊔ U) le_sup_right (sup_ne_top hU hUB hX hBX)
    (not_isSolvable_sup hBs)
  have hDP : D ≤ P j :=
    (le_sup_left.trans (hsolv _ le_sup_right hD)).trans (hnorm j)
  have h := hDP.trans (le_normalizer_dInf (P j))
  rwa [← hdj, dInf_sup_eq hU hUB hB] at h

theorem map_eq_of_residual {U : Subgroup X} {P : Fin 2 → Subgroup X}
    (hres : ResidualOvergroupsAt X U P) (hU : IsPGroup 2 U) (hX : Group.IsPerfect X)
    {B : Subgroup X} (hB : Group.IsPerfect ↥B) (hBs : ¬ Group.IsSolvable ↥B) (hBX : B ≠ ⊤)
    (hUB : U ≤ Subgroup.normalizer (B : Set X)) (α : MulAut X) (hα : Odd (orderOf α))
    (hαU : U.map α.toMonoidHom = U) : B.map α.toMonoidHom = B := by
  have h := hres.2.2.2.2.2 α hα hαU (B ⊔ U) le_sup_right (sup_ne_top hU hUB hX hBX)
    (not_isSolvable_sup hBs)
  rwa [dInf_sup_eq hU hUB hB] at h

theorem le_normalizer_of_surjective {X' : Type} [Group X'] (π : X →* X')
    (hker : π.ker ≤ Subgroup.center X) {B D : Subgroup X} (hB : Group.IsPerfect ↥B)
    (hD : D.map π ≤ Subgroup.normalizer ((B.map π : Subgroup X') : Set X')) :
    D ≤ Subgroup.normalizer (B : Set X) := by
  intro d hd
  have hdB := hD ⟨d, hd, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hdB ⊢
  have hKN : π.ker ≤ Subgroup.normalizer (B : Set X) := fun z hz =>
    Subgroup.mem_normalizer_iff.mpr fun b => by
      have hzc := Subgroup.mem_center_iff.mp (hker hz)
      rw [← hzc b, mul_inv_cancel_right]
  have hKs : Group.IsSolvable ↥π.ker := by
    have : IsMulCommutative ↥π.ker := ⟨⟨fun a b => Subtype.ext
      ((Subgroup.mem_center_iff.mp (hker a.2) b).symm)⟩⟩
    infer_instance
  have hle : B.map (MulAut.conj d).toMonoidHom ≤ B := by
    have hperf : Group.IsPerfect ↥(B.map (MulAut.conj d).toMonoidHom) :=
      map_isPerfect hB _
    refine CFSG.Goldschmidt.G37.le_of_perfect_of_le_sup hperf ?_ hKN hKs
    rintro _ ⟨b, hb, rfl⟩
    have h1 : π (d * b * d⁻¹) ∈ B.map π := by
      rw [← hdB]
      exact ⟨π b, ⟨b, hb, rfl⟩, by simp [map_mul, map_inv]⟩
    obtain ⟨b', hb', hb'e⟩ := h1
    have hk : b'⁻¹ * (d * b * d⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb'e, inv_mul_cancel]
    have e : (MulAut.conj d).toMonoidHom b = b' * (b'⁻¹ * (d * b * d⁻¹)) := by
      simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hb') (Subgroup.mem_sup_left hk)
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj d).injective).ge

end Abstract

theorem exists_isPSL_of_isSL3 {X : Type} [Group X] [Finite X] (h : IsSL3 4 X) :
    ∃ (X' : Type) (_ : Group X') (_ : Finite X') (π : X →* X'), Function.Surjective π ∧
      π.ker ≤ Subgroup.center X ∧ (∀ x ∈ π.ker, x ^ 3 = 1) ∧ IsPSL 3 2 2 X' := by
  obtain ⟨K, hF, hK, hcard, ⟨e⟩⟩ := h
  set Z := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) with hZ
  set π : X →* StatedProj (StatedSL 3 K) := (QuotientGroup.mk' Z).comp e.toMonoidHom with hπ
  have hπs : Function.Surjective π := (QuotientGroup.mk'_surjective Z).comp e.surjective
  have hZ' : ∀ x ∈ π.ker, e x ∈ Z := fun x hx => by
    rw [hπ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  refine ⟨StatedProj (StatedSL 3 K), inferInstance, Finite.of_surjective π hπs, π, hπs, ?_, ?_,
    ?_⟩
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : e x ∈ Z := hZ' x hx
    have hc : ((e x : ↥(StatedSL 3 K)) : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hx'
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc (e y : GL (Fin 3) K))
  ·
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hZ' x hx)
    have hdet : (((e x : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have hle : StatedSL 3 K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker :=
        (Subgroup.closure_le _).mpr fun A hA => by
          rw [SetLike.mem_coe, MonoidHom.mem_ker]
          exact Units.ext (by simpa using hA)
      have h1 := hle (e x).2
      rw [MonoidHom.mem_ker] at h1
      simpa using congrArg Units.val h1
    have hc3 : (c : K) ^ 3 = 1 := by
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal] at hdet
      simpa [Finset.prod_const] using hdet
    apply e.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar,
      ← map_pow, hc3, map_one]
    rfl
  · exact ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, hF, hK,
      by rw [hcard]; norm_num, ⟨MulEquiv.refl _⟩⟩

end CFSG.Quasithin.H13.Ch9.FFC
