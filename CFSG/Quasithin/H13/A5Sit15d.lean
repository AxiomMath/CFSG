module

public import CFSG.Quasithin.H13.A5Sit15c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth
open CFSG.Quasithin.H13.A5 (eq_one_of_conj_eq_mul normalizer_le_normalizer_centralizer' piQ
  piQ_eq_one_iff)

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem exists_y : ∃ y ∈ V ⊔ conjSub P.g⁻¹ V, y ^ 3 = 1 ∧ y ≠ 1 ∧ P.v * y * P.v⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h1, h3, -⟩ := P.S3_facts
  set a := P.v with hadef
  set b := P.g⁻¹ * P.v * P.g with hbdef
  have ha2 : a * a = 1 := S.sq_eq_one_of_mem_V P.v_mem
  have hb2 : b * b = 1 := by
    have e : b * b = P.g⁻¹ * (P.v * P.v) * P.g := by rw [hbdef]; group
    rw [e, ha2]
    group
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, h3⟩
  have hk' : ((a * b) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨(a * b) ^ 2 ^ k, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (le_sup_left (a := V) P.v_mem)
      (le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem)) _
  · rw [← pow_mul, mul_comm, pow_mul, hk']
  ·
    intro h
    apply h1
    have h2 : (a * b) ^ 2 ^ k ∈ pCoreOf 2 H := by rw [h]; exact Subgroup.one_mem _
    have hab : a * b ∈ H := H.mul_mem P.v_mem_H P.v'_mem_H
    have hπ : ∀ n : ℕ, piQ H ⟨a * b, hab⟩ ^ n = 1 ↔ (a * b) ^ n ∈ pCoreOf 2 H := by
      intro n
      rw [← map_pow, piQ_eq_one_iff]
      rfl
    have e1 := (hπ _).2 h2
    have e2 := (hπ 3).2 h3
    have hord : orderOf (piQ H ⟨a * b, hab⟩) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)
    rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at hord
    have := (hπ 1).1 (by rw [pow_one]; exact hord)
    simpa using this
  ·
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
    have e : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev, hai, hbi, ← mul_assoc, ha2, one_mul]
    rw [← conj_pow, e, inv_pow]

theorem y_not_mem_M {M : Subgroup G} (hVO : V ≤ pCoreOf 2 M) {y : G} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hinv : P.v * y * P.v⁻¹ = y⁻¹) : y ∉ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hyM
  have hv := hVO P.v_mem
  have hyv : y * P.v * y⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hyM) _).mp hv
  have hv2 : P.v * P.v = 1 := S.sq_eq_one_of_mem_V P.v_mem
  have hvy : P.v * y = y⁻¹ * P.v := by
    calc P.v * y = P.v * y * P.v⁻¹ * P.v := by group
      _ = y⁻¹ * P.v := by rw [hinv]
  have hyy : y⁻¹ * y⁻¹ = y := by
    calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * y ^ 3 := by rw [hy3, mul_one]
      _ = y := by group
  have e : y = P.v * (y * P.v * y⁻¹) := by
    calc y = y⁻¹ * y⁻¹ := hyy.symm
      _ = y⁻¹ * (P.v * P.v) * y⁻¹ := by rw [hv2, mul_one]
      _ = (y⁻¹ * P.v) * P.v * y⁻¹ := by group
      _ = (P.v * y) * P.v * y⁻¹ := by rw [hvy]
      _ = P.v * (y * P.v * y⁻¹) := by group
  have hyO : y ∈ pCoreOf 2 M := by
    rw [e]
    exact Subgroup.mul_mem _ hv hyv
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨y, hyO⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf y ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2), Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact hy1 h1

theorem centralizer_T_L (hM : IsUniqueM (S.L ⊔ T) (Subgroup.normalizer (S.L : Set G)))
    (hVO : V ≤ pCoreOf 2 (Subgroup.normalizer (S.L : Set G))) :
    T ⊓ Subgroup.centralizer (S.L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyI, hy3, hy1, hinv⟩ := P.exists_y
  set D := T ⊓ Subgroup.centralizer (S.L : Set G) with hDdef
  have hyH : y ∈ H := P.I_le_H hyI
  have hL1L : L₁ ≤ S.L := fun x hx =>
    (oTwoRes_le _ (show x ∈ L₁Of S.L V₁ from S.L1_eq ▸ hx)).1
  have hUL : conjClosure V₃ H ≤ S.L := (S.UH_le_L1 P.hn).trans hL1L
  obtain ⟨z, hz1, hzV⟩ := S.exists_V1_eq
  have hzC : z = P.C.z := by
    rcases (P.Cz z).1 ((hzV z).2 (Or.inr rfl)) with h | h
    · exact absurd h hz1
    · exact h
  have hDQ : ∀ d ∈ D, d ∈ pCoreOf 2 H := by
    intro d hd
    refine (S.mem_Q_iff (S.T_le_H hd.1)).2 fun u hu => ?_
    have := Subgroup.mem_centralizer_iff.mp hd.2 u (hUL hu)
    rw [← this, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hyD : ∀ d ∈ D, y * d * y⁻¹ = d := by
    intro d hd
    have hdQ := hDQ d hd
    have hdN := P.Q_le_NI hdQ
    set k := y * d * y⁻¹ * d⁻¹ with hk
    have hkI : k ∈ V ⊔ conjSub P.g⁻¹ V := by
      have h1 : d * y⁻¹ * d⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        (Subgroup.mem_normalizer_iff.mp hdN _).mp ((V ⊔ conjSub P.g⁻¹ V).inv_mem hyI)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem hyI h1
      simpa [hk, mul_assoc] using this
    have hkC : ∀ u ∈ conjClosure V₃ H, k * u = u * k := by
      intro u hu
      have hdu : ∀ x ∈ conjClosure V₃ H, d * x = x * d := fun x hx =>
        (Subgroup.mem_centralizer_iff.mp hd.2 x (hUL hx)).symm
      have hy' : y⁻¹ * u * y ∈ conjClosure V₃ H := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure V₃ H (H.inv_mem hyH)) u).mp hu
        simpa using this
      have h1 := hdu _ hy'
      have h2 := hdu u hu
      have hdinv : d⁻¹ * u = u * d⁻¹ := by
        calc d⁻¹ * u = d⁻¹ * (u * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * u) * d⁻¹ := by rw [h2]
          _ = u * d⁻¹ := by group
      calc k * u = y * d * y⁻¹ * (d⁻¹ * u) := by rw [hk]; group
        _ = y * d * y⁻¹ * (u * d⁻¹) := by rw [hdinv]
        _ = y * (d * (y⁻¹ * u * y)) * y⁻¹ * d⁻¹ := by group
        _ = y * ((y⁻¹ * u * y) * d) * y⁻¹ * d⁻¹ := by rw [h1]
        _ = u * k := by rw [hk]; group
    have hkQ : k ∈ pCoreOf 2 H := by
      refine (S.mem_Q_iff (P.I_le_H hkI)).2 fun u hu => ?_
      rw [hkC u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hkU : k ∈ conjClosure V₃ H := by
      rw [← P.I_inf_Q]
      exact ⟨hkI, hkQ⟩
    have hkV1 := P.mem_V1_of_central hkU hkC
    rcases (hzV k).1 hkV1 with h | h
    · rw [hk] at h
      calc y * d * y⁻¹ = y * d * y⁻¹ * d⁻¹ * d := by group
        _ = d := by rw [h, one_mul]
    · exfalso
      apply hz1
      have hz2 : z * z = 1 := by
        rw [hzC, ← pow_two]
        exact P.C.z_sq
      refine eq_one_of_conj_eq_mul (d := d) hy3 hz2 ?_ ?_
      · rw [hzC]
        exact P.comm_z hyH
      · rw [← h, hk]
        group
  by_contra hD
  have hDp : IsPGroup 2 D := S.isPGroup_T.to_le inf_le_left
  have hloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hD, hDp, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hLTD : S.L ⊔ T ≤ Subgroup.normalizer (D : Set G) := by
    refine sup_le ?_ ?_
    · intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := Subgroup.mem_centralizer_iff.mp hx.2 l hl
        rw [this, mul_inv_cancel_right]
        exact hx
      · intro hx
        have := Subgroup.mem_centralizer_iff.mp hx.2 l hl
        have e : x = l * x * l⁻¹ := by
          calc x = l⁻¹ * (l * x * l⁻¹ * l) := by group
            _ = l⁻¹ * (l * (l * x * l⁻¹)) := by rw [this]
            _ = l * x * l⁻¹ := by group
        rw [e]
        exact hx
    · exact F7.le_normalizer_inf Subgroup.le_normalizer
        (S.hF.normalizes_L.trans (normalizer_le_normalizer_centralizer' S.L))
  have hM'eq := hM.2 M' ⟨hM', hLTD.trans hle⟩
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      rw [hyD d hd]
      exact hd
    · intro hd
      have := hyD _ hd
      have e : d = y * d * y⁻¹ := by
        calc d = y⁻¹ * (y * d * y⁻¹) * y := by group
          _ = y⁻¹ * (y * (y * d * y⁻¹) * y⁻¹) * y := by rw [this]
          _ = y * d * y⁻¹ := by group
      rw [e]
      exact hd
  exact P.y_not_mem_M hVO hy3 hy1 hinv (hM'eq ▸ hle hyND)

end A5SitPf15

end CFSG.Quasithin.H13
