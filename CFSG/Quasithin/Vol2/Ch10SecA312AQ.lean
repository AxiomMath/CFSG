module

public import CFSG.Quasithin.Vol2.Ch10SecA312AB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Centralizer
public import CFSG.Quasithin.Vol2.Ch10SecA312AA

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

theorem exists_involution_pow {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsPGroup 2 ↥T) {z : X} (hzT : z ∈ T) (hz1 : z ≠ 1) :
    ∃ n : ℕ, z ^ n ≠ 1 ∧ z ^ n * z ^ n = 1 := by
  obtain ⟨n, h1, h2⟩ := exists_pow_involution hT (γ := ⟨z, hzT⟩)
    (fun h => hz1 (congrArg Subtype.val h))
  refine ⟨n, fun h => h1 (Subtype.ext ?_), ?_⟩
  · simpa using h
  · simpa using congrArg Subtype.val h2

theorem five_dvd_card_of_isExt {G : Type} [Group G] [Finite G]
    {P : ∀ (Y : Type) [Group Y], Prop} (h : IsExt G (fun V _ => IsE2 4 V) P)
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], P Y → 5 ∣ Nat.card Y) : 5 ∣ Nat.card G := by
  obtain ⟨V, hV, -, hY⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V]
  exact dvd_mul_of_dvd_left (hP _ hY) _

theorem five_dvd_card_of_isAlt {Y : Type} [Group Y] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (h : IsAlt n Y) : 5 ∣ Nat.card Y := by
  obtain ⟨e⟩ := h
  rcases hn with rfl | rfl <;>
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide

theorem five_dvd_card_of_isHat_alt6 {Y : Type} [Group Y] [Finite Y]
    (h : IsHat Y (alternatingGroup (Fin 6))) : 5 ∣ Nat.card Y := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  have h1 : 5 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  exact h1.trans (Subgroup.card_quotient_dvd_card _)

theorem false_of_hom_M22
    {X : Type} [Group X]
    (ψ : X →* CFSG.Blueprint.NativeSporadic.Carrier .M22) (hker : ∀ x, ψ x = 1 → x ^ 3 = 1)
    {b z : X} (hb : orderOf b = 5) (hz : z ≠ 1) (hz2 : z * z = 1) (hbz : z * b = b * z) :
    False := by
  have hψz : ψ z ≠ 1 := fun h => by
    have h3 := hker z h
    apply hz
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [h3, hz2, inv_one, mul_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (ψ z) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hz2, map_one]) hψz
  have hcard := CFSG.EvenSporadicStandard.M22Std.card_centralizer_involution hord
  have hψb : ψ b ≠ 1 := fun h => by
    have h3 := hker b h
    have h5 : b ^ 5 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    have hb1 : b = 1 := by
      calc b = b ^ 3 * b ^ 3 * (b ^ 5)⁻¹ := by group
        _ = 1 := by rw [h3, h5]; group
    rw [hb1, orderOf_one] at hb
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hordb : orderOf (ψ b) = 5 := by
    have hdvd : orderOf (ψ b) ∣ 5 := hb ▸ orderOf_map_dvd ψ b
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hψb
    · exact h
  have hmem : ψ b ∈ Subgroup.centralizer ({ψ z} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hbz]
  have h5 := orderOf_dvd_natCard (⟨ψ b, hmem⟩ : ↥(Subgroup.centralizer ({ψ z} : Set _)))
  rw [Subgroup.orderOf_mk, hordb, hcard] at h5
  norm_num at h5

theorem a312ZCentM22_holds :
    A312ZCentM22 := by
  intro X _ _ T B hcase hc
  obtain ⟨-, -, -, hT, -, -, -, -, ⟨z, hzT, hz1, -, hzB⟩, -⟩ := hc
  obtain ⟨k, hk1, hk2⟩ := exists_involution_pow hT.isPGroup hzT hz1
  have h5 : 5 ∣ Nat.card ↥B := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> rcases h with h | h
    · exact five_dvd_card_of_isExt h fun Y _ _ hY => five_dvd_card_of_isAlt (Or.inl rfl) hY
    · exact five_dvd_card_of_isExt h fun Y _ _ hY => five_dvd_card_of_isAlt (Or.inr rfl) hY
    · exact five_dvd_card_of_isExt h fun Y _ _ hY => five_dvd_card_of_isAlt (Or.inl rfl) hY
    · exact five_dvd_card_of_isExt h fun Y _ _ hY => five_dvd_card_of_isHat_alt6 hY
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 5 h5
  have hbz : z ^ k * (b : X) = b * z ^ k := ((Commute.pow_left (hzB b b.2) k))
  obtain ⟨ψ, hker⟩ : ∃ ψ : X →* CFSG.Blueprint.NativeSporadic.Carrier .M22,
      ∀ x, ψ x = 1 → x ^ 3 = 1 := by
    rcases hcase with ⟨-, ⟨e⟩⟩ | ⟨-, -, h3, ⟨e⟩⟩
    · refine ⟨e.toMonoidHom.comp (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).toMonoidHom,
        fun x hx => ?_⟩
      have h1 : (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)) x = 1 :=
        (map_eq_one_iff _ e.injective).1 hx
      rw [(map_eq_one_iff _ (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).injective).1 h1,
        one_pow]
    · refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' _).comp
        (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).toMonoidHom), fun x hx => ?_⟩
      have h1 : QuotientGroup.mk' (Subgroup.center ↥(⊤ : Subgroup X))
          ((Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)) x) = 1 :=
        (map_eq_one_iff _ e.injective).1 hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := pow_card_eq_one' (G := ↥(Subgroup.center ↥(⊤ : Subgroup X))) (x := ⟨_, h1⟩)
      rw [h3] at h2
      simpa using congrArg
        (fun y : ↥(Subgroup.center ↥(⊤ : Subgroup X)) => ((y : ↥(⊤ : Subgroup X)) : X)) h2
  exact false_of_hom_M22 ψ hker (by rwa [Subgroup.orderOf_coe]) hk1 hk2 hbz

end CFSG.Quasithin.Vol2.Ch10.A312A
