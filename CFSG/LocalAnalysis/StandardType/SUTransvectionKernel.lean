module

public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import CFSG.LocalAnalysis.StandardType.SURadicalVector
import CFSG.RankThree.OddKernel.OddLift
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.LocalAnalysis.StandardType.SUCenterOdd

public section

namespace CFSG.StandardType.SUTransvection

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCSTSU CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Stroth80
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom aform)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {k : ℕ}

theorem mem_centralizer_ggInvSU_of_map_commute {X : Type*} [Group X]
    (π : SU σ (k + 2) →* X)
    (hker : π.ker ≤ center (SU σ (k + 2))) {y : SU σ (k + 2)}
    (hy : π y * π (ggInvSU σ (k + 2) 1) = π (ggInvSU σ (k + 2) 1) * π y) :
    y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := by
  have hodd : Odd (Nat.card π.ker) := CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  have hτ2 : ggInvSU σ (k + 2) 1 ^ 2 = 1 := by rw [sq, ggInvSU_mul_self]
  have hc : y * ggInvSU σ (k + 2) 1 * y⁻¹ = ggInvSU σ (k + 2) 1 := by
    refine CFSG.Alternating.Multipliers.eq_of_sq_eq_one hker hodd ?_ ?_ hτ2
    · rw [map_mul, map_mul, map_inv, hy, mul_inv_cancel_right]
    · rw [conj_pow, hτ2, mul_one, mul_inv_cancel]
  rw [mem_centralizer_singleton_iff]
  calc y * ggInvSU σ (k + 2) 1 = y * ggInvSU σ (k + 2) 1 * y⁻¹ * y := by group
    _ = ggInvSU σ (k + 2) 1 * y := by rw [hc]

omit [Finite F] in
theorem corner_eq_one_of_pow_eq_one {y : SU σ (k + 2)}
    (hy : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) {e : ℕ}
    (he : y ^ 2 ^ e = 1) : mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  have h1 : (mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) - 1) ^ 2 ^ e = 0 := by
    rw [sub_pow_char_pow, one_pow, ← corner_pow hy, he, map_one, Matrix.one_apply_eq, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero e two_ne_zero) |>.mp h1)

omit [Finite F] in
private theorem exists_midBlockHom {T : Subgroup (SU σ (k + 2))}
    (hTC : T ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (hT1 : ∀ y ∈ T, mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    ∃ φ : T →* SU σ k, ∀ y, mat σ k (φ y) =
      (mat σ (k + 2) (y : SU σ (k + 2))).submatrix
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid := by
  classical
  have hex : ∀ y : T, ∃ B : SU σ k, mat σ k B =
      (mat σ (k + 2) (y : SU σ (k + 2))).submatrix
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid :=
    fun y => exists_mat_eq_submatrix_mid (hTC y.2) (hT1 y y.2)
  let φ : T →* SU σ k :=
    { toFun := fun y => Classical.choose (hex y)
      map_one' := by
        refine mat_injective ?_
        rw [Classical.choose_spec (hex 1)]
        simp [Matrix.submatrix_one _
          CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid_injective]
      map_mul' := by
        intro y y'
        refine mat_injective ?_
        rw [map_mul, Classical.choose_spec (hex (y * y')), Classical.choose_spec (hex y),
          Classical.choose_spec (hex y'), Subgroup.coe_mul,
          submatrix_mul_of_mem (hTC y.2) (hTC y'.2)] }
  exact ⟨φ, fun y => Classical.choose_spec (hex y)⟩

omit [Finite F] in
private theorem midBlockHom_range_eq_bot (L : Subgroup (SU σ k))
    (hLa : ∀ H : Subgroup (SU σ k), IsPGroup 2 H →
      (∀ l ∈ L, ∀ x ∈ H, l * x * l⁻¹ ∈ H) → H = ⊥)
    {T : Subgroup (SU σ (k + 2))}
    (hTC : T ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (hT2 : IsPGroup 2 T)
    (hTL : ∀ l ∈ L, ∀ y ∈ T, iotaHom l * y * (iotaHom l)⁻¹ ∈ T)
    (φ : T →* SU σ k)
    (hφ : ∀ y, mat σ k (φ y) =
      (mat σ (k + 2) (y : SU σ (k + 2))).submatrix
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid) :
    φ.range = ⊥ := by
  have hH2 : IsPGroup 2 φ.range := by
    have h := (hT2.to_subgroup (⊤ : Subgroup T)).map φ
    rwa [Subgroup.map_top] at h
  refine hLa φ.range hH2 ?_
  intro l hl x hx
  obtain ⟨y, rfl⟩ := hx
  have hιC : iotaHom l ∈ centralizer ({ggInvSU σ (k + 2) 1} :
      Set (SU σ (k + 2))) := range_iotaHom_le_centralizer ⟨l, rfl⟩
  let w : T := ⟨iotaHom l * (y : SU σ (k + 2)) * (iotaHom l)⁻¹, hTL l hl y y.2⟩
  have h1 : (mat σ (k + 2) (w : SU σ (k + 2))).submatrix
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid = mat σ k l * mat σ k (φ y) *
        mat σ k l⁻¹ := by
    have hinvι : (iotaHom l)⁻¹ = iotaHom (σ := σ) (m := k) l⁻¹ :=
      (map_inv iotaHom l).symm
    change (mat σ (k + 2) (iotaHom l * (y : SU σ (k + 2)) * (iotaHom l)⁻¹)).submatrix
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid =
      mat σ k l * mat σ k (φ y) * mat σ k l⁻¹
    rw [hinvι, submatrix_mul_of_mem (mul_mem hιC (hTC y.2))
      (by rw [← hinvι]; exact inv_mem hιC),
      submatrix_mul_of_mem hιC (hTC y.2), ← hφ y,
      mat_iotaHom, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.submatrix_iotaMat,
      mat_iotaHom, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.submatrix_iotaMat]
  refine ⟨w, ?_⟩
  refine mat_injective ?_
  rw [hφ w]
  change (mat σ (k + 2) (iotaHom l * (y : SU σ (k + 2)) * (iotaHom l)⁻¹)).submatrix
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid = mat σ k (l * φ y * l⁻¹)
  rw [h1, map_mul, map_mul]

omit [Finite F] in
theorem le_suRad_of_isPGroup (L : Subgroup (SU σ k))
    (hLa : ∀ H : Subgroup (SU σ k), IsPGroup 2 H → (∀ l ∈ L, ∀ x ∈ H, l * x * l⁻¹ ∈ H) → H = ⊥)
    {T : Subgroup (SU σ (k + 2))}
    (hTC : T ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (hT1 : ∀ y ∈ T, mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1)
    (hT2 : IsPGroup 2 T) (hTL : ∀ l ∈ L, ∀ y ∈ T, iotaHom l * y * (iotaHom l)⁻¹ ∈ T) :
    T ≤ suRad σ k := by
  obtain ⟨φ, hφ⟩ := exists_midBlockHom hTC hT1
  have hbot : φ.range = ⊥ := midBlockHom_range_eq_bot L hLa hTC hT2 hTL φ hφ
  intro y hy
  rw [mem_suRad]
  refine ⟨hTC hy, hT1 y hy, ?_⟩
  have hmem : φ ⟨y, hy⟩ ∈ φ.range := ⟨⟨y, hy⟩, rfl⟩
  have hEq : φ ⟨y, hy⟩ = 1 := by simpa [hbot] using hmem
  rw [← hφ ⟨y, hy⟩, hEq, map_one]

omit [Finite F] in
theorem radCol_eq_zero_of_forall_commute (hσ : ∀ c, σ (σ c) = c) (L : Subgroup (SU σ k))
    (hLb : ∀ V : AddSubgroup (Fin k → F), (∀ l ∈ L, ∀ v ∈ V, mat σ k l *ᵥ v ∈ V) →
      (∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v) → V = ⊥)
    {T : Subgroup (SU σ (k + 2))} (hTR : T ≤ suRad σ k)
    (hTc : ∀ y ∈ T, ∀ y' ∈ T, y * y' = y' * y)
    (hTL : ∀ l ∈ L, ∀ y ∈ T, iotaHom l * y * (iotaHom l)⁻¹ ∈ T) {y : SU σ (k + 2)}
    (hy : y ∈ T) : radCol y = 0 := by
  let V : AddSubgroup (Fin k → F) :=
    { carrier := {v | ∃ y ∈ T, radCol y = v}
      zero_mem' := ⟨1, T.one_mem, radCol_one⟩
      add_mem' := by
        rintro v w ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', T.mul_mem hy hy', radCol_mul (hTR hy) (hTR hy')⟩
      neg_mem' := by
        rintro v ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, T.inv_mem hy, radCol_inv (hTR hy)⟩ }
  have hLV : ∀ l ∈ L, ∀ v ∈ V, mat σ k l *ᵥ v ∈ V := by
    rintro l hl v ⟨y, hy, rfl⟩
    exact ⟨iotaHom l * y * (iotaHom l)⁻¹, hTL l hl y hy, radCol_conj_iotaHom y l⟩
  have hVsym : ∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v := by
    rintro v ⟨y, hy, rfl⟩ w ⟨y', hy', rfl⟩
    exact aform_radCol_comm hσ (hTR hy) (hTR hy') (hTc y hy y' hy')
  have hmem : radCol y ∈ V := ⟨y, hy, rfl⟩
  rw [hLb V hLV hVsym] at hmem
  simpa using hmem

omit [Finite F] in
private theorem corner_inv_of_eq_one {y : SU σ (k + 2)}
    (hy : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (h1 : mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    mat σ (k + 2) y⁻¹ (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  have h := corner_mul_of_mem (x := y) (y := y⁻¹) (inv_mem hy)
  rw [mul_inv_cancel, map_one, Matrix.one_apply_eq, h1, one_mul] at h
  exact h.symm

private theorem comap_le_centralizer_of_isKLConfig {X : Type*} [Group X] {a : ℕ}
    {N A : Subgroup X} {π : SU σ (k + 2) →* X}
    (h : IsKLConfig (π (ggInvSU σ (k + 2) 1)) a N A)
    (hker : π.ker ≤ center (SU σ (k + 2))) :
    A.comap π ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := by
  intro y hy
  exact mem_centralizer_ggInvSU_of_map_commute π hker
    (h.comm (π y) hy (π (ggInvSU σ (k + 2) 1)) h.mem)

omit [Finite F] in
private theorem isPGroup_of_corner_comap {X : Type*} [Group X] {A : Subgroup X}
    {π : SU σ (k + 2) →* X}
    (hZ : ∀ z ∈ π.ker, mat σ (k + 2) z (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 → z = 1)
    {T : Subgroup (SU σ (k + 2))} (hA : IsPGroup 2 A)
    (hT : ∀ y, y ∈ T ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A) :
    IsPGroup 2 T := by
  intro y
  have hy := (hT (y : SU σ (k + 2))).mp y.2
  obtain ⟨e, he⟩ := hA ⟨π (y : SU σ (k + 2)), hy.2.2⟩
  have he' : π (y : SU σ (k + 2)) ^ 2 ^ e = 1 := by
    simpa using congrArg Subtype.val he
  refine ⟨e, Subtype.ext ?_⟩
  have hker : (y : SU σ (k + 2)) ^ 2 ^ e ∈ π.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_pow, he'])
  have hc : mat σ (k + 2) ((y : SU σ (k + 2)) ^ 2 ^ e) (Fin.last (k + 1))
      (Fin.last (k + 1)) = 1 := by
    rw [corner_pow hy.1, hy.2.1, one_pow]
  simpa using hZ _ hker hc

private theorem le_map_of_isPGroup {X : Type*} [Group X] {a : ℕ} {N A : Subgroup X}
    {π : SU σ (k + 2) →* X} (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (SU σ (k + 2)))
    (h : IsKLConfig (π (ggInvSU σ (k + 2) 1)) a N A) (hA : IsPGroup 2 A)
    {T : Subgroup (SU σ (k + 2))}
    (hT : ∀ y, y ∈ T ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A) :
    A ≤ T.map π := by
  have hodd : Odd (Nat.card π.ker) := CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  obtain ⟨A₀, hA₀, hmap, -⟩ :=
    CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq π hπ hodd A hA
  rw [← hmap]
  rintro _ ⟨y, hy, rfl⟩
  have hyA : π y ∈ A := by rw [← hmap]; exact Subgroup.mem_map_of_mem π hy
  have hyC : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    comap_le_centralizer_of_isKLConfig h hker hyA
  obtain ⟨e, he⟩ := hA₀ ⟨y, hy⟩
  have he' : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨y, ?_, rfl⟩
  exact (hT y).mpr ⟨hyC, corner_eq_one_of_pow_eq_one hyC he', hyA⟩

omit [Finite F] in
private theorem conj_iotaHom_mem_of_isKLConfig {X : Type*} [Group X] {a : ℕ}
    {N A : Subgroup X} {π : SU σ (k + 2) →* X}
    (h : IsKLConfig (π (ggInvSU σ (k + 2) 1)) a N A)
    (L : Subgroup (SU σ k)) (hLN : ∀ g ∈ L, π (iotaHom g) ∈ N)
    {T : Subgroup (SU σ (k + 2))}
    (hT : ∀ y, y ∈ T ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A) :
    ∀ l ∈ L, ∀ y ∈ T, iotaHom l * y * (iotaHom l)⁻¹ ∈ T := by
  intro l hl y hy
  have hyC : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := ((hT y).mp hy).1
  have hy1 : mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := ((hT y).mp hy).2.1
  have hyA : π y ∈ A := ((hT y).mp hy).2.2
  have hιC : iotaHom l ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    range_iotaHom_le_centralizer ⟨l, rfl⟩
  refine (hT (iotaHom l * y * (iotaHom l)⁻¹)).mpr
    ⟨mul_mem (mul_mem hιC hyC) (inv_mem hιC), ?_, ?_⟩
  · rw [corner_mul_of_mem (inv_mem hιC), corner_mul_of_mem hyC, hy1, corner_iotaHom]
    simpa using corner_inv_of_eq_one hιC (corner_iotaHom l)
  · rw [map_mul, map_mul, map_inv]
    exact h.conj_mem (π (iotaHom l)) (hLN l hl) (π y) hyA

omit [Finite F] in
private theorem mul_comm_of_isKLConfig {X : Type*} [Group X] {a : ℕ} {N A : Subgroup X}
    {π : SU σ (k + 2) →* X} (h : IsKLConfig (π (ggInvSU σ (k + 2) 1)) a N A)
    (hZ : ∀ z ∈ π.ker, mat σ (k + 2) z (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 → z = 1)
    {T : Subgroup (SU σ (k + 2))}
    (hT : ∀ y, y ∈ T ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A) :
    ∀ y ∈ T, ∀ y' ∈ T, y * y' = y' * y := by
  intro y hy y' hy'
  have hyC : y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) := ((hT y).mp hy).1
  have hy'C : y' ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    ((hT y').mp hy').1
  have hy1 : mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := ((hT y).mp hy).2.1
  have hy'1 : mat σ (k + 2) y' (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 :=
    ((hT y').mp hy').2.1
  have hA : π y * π y' = π y' * π y :=
    h.comm (π y) ((hT y).mp hy).2.2 (π y') ((hT y').mp hy').2.2
  have hker : y * y' * y⁻¹ * y'⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hA]
    group
  have hC : y * y' * y⁻¹ * y'⁻¹ ∈ centralizer
      ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    mul_mem (mul_mem (mul_mem hyC hy'C) (inv_mem hyC)) (inv_mem hy'C)
  have h1 : mat σ (k + 2) (y * y' * y⁻¹ * y'⁻¹) (Fin.last (k + 1))
      (Fin.last (k + 1)) = 1 := by
    rw [corner_mul_of_mem (inv_mem hy'C), corner_mul_of_mem (inv_mem hyC),
      corner_mul_of_mem hy'C, hy1, hy'1, corner_inv_of_eq_one hyC hy1,
      corner_inv_of_eq_one hy'C hy'1]
    simp
  have hc : y * y' * y⁻¹ * y'⁻¹ = 1 := hZ _ hker h1
  have h1' : y * y' * y⁻¹ = y' := mul_inv_eq_one.mp hc
  calc y * y' = (y * y' * y⁻¹) * y := by group
    _ = y' * y := by rw [h1']

omit [CharP F 2] in
private theorem exists_odd_prime_orderOf (L : Subgroup (SU σ k)) (hL2 : ¬ IsPGroup 2 L) :
    ∃ g ∈ L, Nat.Prime (orderOf g) ∧ Odd (orderOf g) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card L) with ⟨n, hn⟩ |
      ⟨p, hp, hdvd, hodd⟩
  · exact absurd (IsPGroup.of_card_dvd_pow (p := 2) (n := n) (by rw [hn])) hL2
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) p hdvd
    exact ⟨g, g.2, by rw [Subgroup.orderOf_coe, hg]; exact hp,
      by rw [Subgroup.orderOf_coe, hg]; exact hodd⟩

omit [Finite F] in
private def cornerPreimage {X : Type*} [Group X] (π : SU σ (k + 2) →* X)
    (A : Subgroup X) : Subgroup (SU σ (k + 2)) where
  carrier := {y | y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
    mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A}
  one_mem' := ⟨by simp, by simp, by simp⟩
  mul_mem' := by
    rintro y y' ⟨hyC, hy1, hyA⟩ ⟨hy'C, hy'1, hy'A⟩
    exact ⟨mul_mem hyC hy'C, by
        rw [corner_mul_of_mem hy'C, hy1, hy'1, mul_one], by
        rw [map_mul]; exact A.mul_mem hyA hy'A⟩
  inv_mem' := by
    rintro y ⟨hyC, hy1, hyA⟩
    exact ⟨inv_mem hyC, corner_inv_of_eq_one hyC hy1, by
      rw [map_inv]; exact A.inv_mem hyA⟩

omit [Finite F] in
private theorem cornerPreimage_mem_iff {X : Type*} [Group X] (π : SU σ (k + 2) →* X)
    (A : Subgroup X) (y : SU σ (k + 2)) :
    y ∈ cornerPreimage π A ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} :
      Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A :=
  Iff.rfl

theorem false_of_isKLConfig_of_iotaHom (hσ : ∀ c, σ (σ c) = c) {X : Type*} [Group X]
    (π : SU σ (k + 2) →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (SU σ (k + 2)))
    (hZ : ∀ z ∈ π.ker, mat σ (k + 2) z (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 → z = 1)
    {a : ℕ} {N A : Subgroup X} (h : IsKLConfig (π (ggInvSU σ (k + 2) 1)) a N A)
    (L : Subgroup (SU σ k)) (hLN : ∀ g ∈ L, π (iotaHom g) ∈ N)
    (hLa : ∀ H : Subgroup (SU σ k), IsPGroup 2 H → (∀ l ∈ L, ∀ x ∈ H, l * x * l⁻¹ ∈ H) → H = ⊥)
    (hLb : ∀ V : AddSubgroup (Fin k → F), (∀ l ∈ L, ∀ v ∈ V, mat σ k l *ᵥ v ∈ V) →
      (∀ v ∈ V, ∀ w ∈ V, aform σ v w = aform σ w v) → V = ⊥)
    (hL1 : L ≠ ⊥) : False := by
  classical
  let T : Subgroup (SU σ (k + 2)) := cornerPreimage π A
  have hT : ∀ y, y ∈ T ↔ y ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) ∧
      mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 ∧ π y ∈ A :=
    fun y => cornerPreimage_mem_iff π A y
  have hTC : T ≤ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))) :=
    fun y hy => ((hT y).mp hy).1
  have hT1 : ∀ y ∈ T, mat σ (k + 2) y (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 :=
    fun y hy => ((hT y).mp hy).2.1
  have hT2 : IsPGroup 2 T := isPGroup_of_corner_comap hZ h.isPGroup hT
  have hTL : ∀ l ∈ L, ∀ y ∈ T, iotaHom l * y * (iotaHom l)⁻¹ ∈ T :=
    conj_iotaHom_mem_of_isKLConfig h L hLN hT
  have hTR : T ≤ suRad σ k := le_suRad_of_isPGroup L hLa hTC hT1 hT2 hTL
  have hTc : ∀ y ∈ T, ∀ y' ∈ T, y * y' = y' * y := mul_comm_of_isKLConfig h hZ hT
  have hR0 : ∀ y ∈ T, radCol y = 0 := fun y hy =>
    radCol_eq_zero_of_forall_commute hσ L hLb hTR hTc hTL hy
  have hAc : A ≤ T.map π := le_map_of_isPGroup hπ hker h h.isPGroup hT
  have hL2 : ¬ IsPGroup 2 L := fun hL =>
    hL1 (hLa L hL (fun l hl x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)))
  obtain ⟨g, hgL, hgprime, hgodd⟩ := exists_odd_prime_orderOf L hL2
  have hinj : Function.Injective (iotaHom (σ := σ) (m := k)) :=
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom_injective
  have hcomm : ∀ x ∈ A, π (iotaHom g) * x = x * π (iotaHom g) := by
    intro x hx
    obtain ⟨y, hyT, rfl⟩ := hAc hx
    rw [← map_mul, ← map_mul, commute_iotaHom_of_radCol_eq_zero hσ (hTR hyT) (hR0 y hyT) g]
  have hoddg : Odd (orderOf (π (iotaHom g))) :=
    Odd.of_dvd_nat hgodd (by
      rw [← orderOf_injective iotaHom hinj g]
      exact orderOf_map_dvd π (iotaHom g))
  have hpi : π (iotaHom g) = 1 := h.eq_one _ (hLN g hgL) hoddg hcomm
  have hι1 : iotaHom g = 1 := hZ _ (MonoidHom.mem_ker.mpr hpi) (corner_iotaHom g)
  have hg1 : g = 1 := hinj (hι1.trans (map_one iotaHom).symm)
  rw [hg1, orderOf_one] at hgprime
  exact hgprime.ne_one rfl


end CFSG.StandardType.SUTransvection
