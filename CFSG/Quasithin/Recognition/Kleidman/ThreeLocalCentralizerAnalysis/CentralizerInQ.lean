module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.FixedLines
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem card_modEq_card_inf_centralizer {G : Type} [Group G] [Finite G] (Q : Subgroup G) (y : G)
    (hy3 : y ^ 3 = 1) (hQ : ∀ g ∈ Q, y * g * y⁻¹ ∈ Q) :
    Nat.card Q ≡ Nat.card (Q ⊓ Subgroup.centralizer {y} : Subgroup G) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥Q := Fintype.ofFinite _
  let f : Function.End ↥Q := fun q => ⟨y * q * y⁻¹, hQ q q.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext q
    apply Subtype.ext
    show y * (y * (y * (q : G) * y⁻¹) * y⁻¹) * y⁻¹ = q
    exact conj_cube hy3 q
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at hmod
  have hfix : ∀ p : Function.fixedPoints f, y * (p.1 : G) * y⁻¹ = p.1 := fun p =>
    congrArg Subtype.val p.2
  have e : Function.fixedPoints f ≃ ↥(Q ⊓ Subgroup.centralizer {y} : Subgroup G) :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (p.1 : G) * y = y * (p.1 : G) * y⁻¹ * y := by rw [hfix p]
          _ = y * (p.1 : G) := by group)⟩
      invFun := fun c => ⟨⟨c.1, c.2.1⟩, by
        apply Subtype.ext
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
        show y * (c : G) * y⁻¹ = c
        calc y * (c : G) * y⁻¹ = (c : G) * y * y⁻¹ := by rw [← h1]
          _ = c := by group⟩
      left_inv := fun p => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e] at hmod
  exact hmod

theorem not_mem_of_isPGroup_two {G : Type} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy3 : orderOf y = 3) : y ∉ P := by
  intro hyP
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hyP⟩
  rw [Subgroup.orderOf_mk, hy3] at hk
  rcases k with _ | k
  · simp at hk
  · have : (2 : ℕ) ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [← hk] at this
    omega

theorem eq_of_dvd_thirtytwo {c : ℕ} (hd : c ∣ 32) (hm : c % 3 = 2) : c = 2 ∨ c = 8 ∨ c = 32 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show c ∣ 2 ^ 5 by simpa using hd)
  interval_cases k <;> simp_all

variable {G : Type} [Group G] [Finite G] {z : G}

theorem _root_.CFSG.Quasithin.IsTypeH2.card_and_dihedral_pCoreOf_inf_centralizer
    (h : IsTypeH2 G z) {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hy3 : orderOf y = 3) :
    Nat.card ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓ Subgroup.centralizer ({y} : Set G))
        = 8 ∧
      Nonempty (↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
        Subgroup.centralizer ({y} : Set G)) ≃* DihedralGroup 4) := by
  classical
  set H := Subgroup.centralizer ({z} : Set G) with hH
  set Q := pCoreOf 2 H with hQ
  set C : Subgroup G := Q ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨x, hxQ, hx, -⟩ := h.exists_fiveLines
  obtain ⟨i, j, hij, hxi, hxj⟩ := h.exists_two_fixed_lines hxQ hx hy hy3'
  set a := x i with ha
  set b := x j with hb
  have haa : a * a = 1 := hx.x_sq i
  have hbb : b * b = 1 := hx.x_sq j
  have habz : (a * b) ^ 2 = z := hx.sq_eq i j hij
  have hz1 : z ≠ 1 := h.ne_one
  have haC : a ∈ C := ⟨hxQ i, Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc a * y = y * a * y⁻¹ * y := by rw [hxi]
      _ = y * a := by group)⟩
  have hbC : b ∈ C := ⟨hxQ j, Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc b * y = y * b * y⁻¹ * y := by rw [hxj]
      _ = y * b := by group)⟩
  have hab4 : orderOf (a * b) = 4 := by
    have h2 : ¬ (a * b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, habz]; exact hz1
    have h4 : (a * b) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, habz]
      calc z ^ 2 = z * z := pow_two z
        _ = 1 := hx.d_sq
    have := orderOf_eq_prime_pow h2 h4
    norm_num at this
    exact this
  have hTcard : Nat.card (Subgroup.zpowers (a * b)) = 4 := by
    rw [Nat.card_zpowers, hab4]
  have haT : a ∉ Subgroup.zpowers (a * b) := by
    intro haT
    have hcomm : (a * b) * a = a * (a * b) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haT
      have : Commute (a * b) a := by
        have h1 := (Commute.refl (a * b)).zpow_right k
        rwa [hk] at h1
      exact this.eq
    apply hz1
    rw [← habz, pow_two]
    calc a * b * (a * b) = (a * b * a) * b := by group
      _ = (a * (a * b)) * b := by rw [hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left haa).symm
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hbb).symm
  have hrefl : ∀ t ∈ Subgroup.zpowers (a * b), a * t * a⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      calc a * (a * b) * a⁻¹ = (a * a) * b * a := by rw [hainv]; group
        _ = b * a := by rw [haa, one_mul]
        _ = (a * b)⁻¹ := by rw [mul_inv_rev, hbinv, hainv]
    calc a * (a * b) ^ k * a⁻¹ = (a * (a * b) * a⁻¹) ^ k := conj_zpow.symm
      _ = ((a * b)⁻¹) ^ k := by rw [hconj]
      _ = ((a * b) ^ k)⁻¹ := (inv_zpow _ _)
  set D : Subgroup G := Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a with hD
  have hDiso : Nonempty (D ≃* DihedralGroup 4) := by
    rw [← hTcard]
    exact CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := Subgroup.zpowers (a * b)) (s := a)
      haT haa hrefl
  obtain ⟨eD⟩ := hDiso
  have hDcard : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hDC : D ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr (C.mul_mem haC hbC)) (Subgroup.zpowers_le.mpr haC)
  have hCQ : C ≤ Q := inf_le_left
  have hCdvd : Nat.card C ∣ 32 := by
    have := Subgroup.card_dvd_of_le hCQ
    rwa [h.card_pCoreOf] at this
  have hmod := card_modEq_card_inf_centralizer Q y hy3' (fun g hg => conj_mem_pCoreOf hy hg)
  rw [h.card_pCoreOf] at hmod
  have hCmod : Nat.card C % 3 = 2 := by
    have : 32 % 3 = Nat.card C % 3 := hmod
    omega
  have hD8C : 8 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le hDC
    omega
  have hC8 : Nat.card C = 8 := by
    rcases eq_of_dvd_thirtytwo hCdvd hCmod with h2 | h8 | h32
    · omega
    · exact h8
    · exfalso
      have hCeq : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by rw [h.card_pCoreOf, h32])
      have hyc : y ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hqC : q ∈ C := hCeq ▸ hq
        exact Subgroup.mem_centralizer_singleton_iff.mp hqC.2
      have hyQ : y ∈ Q := h.charTwo ⟨hy, hyc⟩
      exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 H) hy3 hyQ
  have hDCeq : D = C := Subgroup.eq_of_le_of_card_ge hDC (by rw [hDcard, hC8])
  refine ⟨hC8, ⟨(MulEquiv.subgroupCongr hDCeq).symm.trans eD⟩⟩

end CFSG.Quasithin.Kleidman.ThreeLocal
