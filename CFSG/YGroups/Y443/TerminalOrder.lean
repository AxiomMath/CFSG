module

public import CFSG.YGroups.Y443.EdgeIntersection
public import CFSG.Sporadic.Bridge.BPresentation
public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.Sporadic.B

public section

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived)

@[expose] noncomputable def toNativeB :
    B433 →* Blueprint.NativeSporadic.B :=
  Sporadic.Bridge.B.φ.comp Sporadic.Bridge.B.b433Hom

theorem toNativeB_surjective :
    Function.Surjective toNativeB :=
  Sporadic.Bridge.B.φ_surjective.comp Sporadic.Bridge.B.b433Hom_surjective

theorem toNativeB_bijective
    : Function.Bijective toNativeB := by
  have := YGroups.B433_finite_card_le.1
  exact toNativeB_surjective.bijective_of_nat_card_le
    (YGroups.B433_finite_card_le.2.trans Sporadic.Bridge.B.card_le_card_B)

noncomputable def B433EquivB
    : B433 ≃* Blueprint.NativeSporadic.B :=
  MulEquiv.ofBijective toNativeB toNativeB_bijective

theorem B433_isSimpleGroup
    : IsSimpleGroup B433 := by
  have h := Sporadic.B.fam_b_simplicity
  exact @MulEquiv.isSimpleGroup B433 _ Blueprint.NativeSporadic.B _ h B433EquivB

theorem B433_card_ge
    : 4154781481226426191177580544000000 ≤ Nat.card B433 := by
  rw [Nat.card_congr B433EquivB.toEquiv]
  exact Sporadic.Bridge.B.card_le_card_B

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

theorem rho_qc :

    rho f qc = f y443C := by rw [rho, MonoidHom.comp_apply, y443Q343Hom_qc]

theorem rho_injective_of
    (hc : f y443C ≠ 1) (h3 : ∃ h ∈ y443H.map f, orderOf h = 3) :
    Function.Injective (rho f) := by
  have hsimple := B433_isSimpleGroup
  have hN : ((rho f).ker.map beta).Normal :=
    Subgroup.Normal.map inferInstance beta beta_surjective
  rcases hN.eq_bot_or_eq_top with hb | ht
  ·
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have hq' : q ∈ beta.ker := by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hb]
      exact ⟨q, hq, rfl⟩
    rw [ker_beta] at hq'
    rcases mem_zpowers_involution qc_mul_self hq' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (by rw [← rho_qc]; exact hq) hc
  ·
    exfalso
    obtain ⟨h, hh, ho⟩ := h3
    rw [← range_rho] at hh
    obtain ⟨q, rfl⟩ := hh
    have htop : (rho f).ker ⊔ Subgroup.zpowers qc = ⊤ := by
      rw [← ker_beta, ← Subgroup.comap_map_eq, ht, Subgroup.comap_top]
    have hq : q ∈ (rho f).ker ⊔ Subgroup.zpowers qc := by rw [htop]; trivial
    rcases mem_sup_zpowers_qc hq with h1 | h1
    · rw [MonoidHom.mem_ker] at h1
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    · rw [MonoidHom.mem_ker, map_mul, rho_qc] at h1
      have e : rho f q = (f y443C)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hc2 : f y443C * f y443C = 1 := by rw [← map_mul, y443C_mul_self, map_one]
      have : rho f q ^ 2 = 1 := by
        rw [e, inv_pow, pow_two, hc2, inv_one]
      have hdvd := orderOf_dvd_of_pow_eq_one this
      rw [ho] at hdvd
      exact absurd hdvd (by norm_num)

theorem terminal_order
    (hc : f y443C ≠ 1) (h3 : ∃ h ∈ y443H.map f, orderOf h = 3) :
    Q343N ≤ Nat.card (y443H.map f) := by
  have := YGroups.Q343_finite_card_le.1
  have hinj := rho_injective_of f hc h3
  have hcard : Nat.card (y443H.map f) = Nat.card Q343 := by
    rw [← range_rho, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hqc : qc ≠ 1 := fun h => hc (by rw [← rho_qc, h, map_one])
  have hc312 : R433.c312 ≠ 1 := by
    rw [← Q343EquivR433_qc]
    exact fun h => hqc (Q343EquivR433.injective (h.trans (map_one _).symm))
  have h2 : Nat.card (Subgroup.zpowers R433.c312) = 2 := by
    rw [Nat.card_zpowers, R433.orderOf_c312 hc312]
  have hQ : Nat.card Q343 = 2 * Nat.card B433 := by
    rw [Nat.card_congr Q343EquivR433.toEquiv, R433.card_eq_mul, h2]
  rw [hcard, hQ]
  have hQN : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
  rw [hQN]
  exact Nat.mul_le_mul_left 2 B433_card_ge

end CFSG.YGroups.Y443Edge
