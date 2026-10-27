module

public import CFSG.Quasithin.EmptyFaithful.SzN15Sort
public import CFSG.Quasithin.EmptyFaithful.S153DGen4
public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.Quasithin.SzN15

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open (pCoreOf)

private theorem card_eq_mul_ker {Λ X : Type} [Group Λ] [Group X] (φ : Λ →* X)
    (hφ : Function.Surjective φ) : Nat.card Λ = Nat.card X * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem isQuasisimple_of_equiv_sl3 {Λ F : Type} [Group Λ] [Field F] [Finite F]
    (e : Λ ≃* ↥(StatedSL 3 F)) : CFSG.IsQuasisimple Λ := by
  have h1 : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  have h2 : CFSG.IsQuasisimple ↥(StatedSL 3 F) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialLinearGroupEquivStatedSL 3 F) h1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h2

theorem isQuasisimple_of_equiv_sp4 {Λ F : Type} [Group Λ] [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : Λ ≃* ↥(StatedSp 2 F)) : CFSG.IsQuasisimple Λ := by
  have h1 : CFSG.IsQuasisimple ↥(StatedSp 2 F) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr (by omega)))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h1

private theorem card_center_equiv_sl3_dvd {Λ F : Type} [Group Λ] [Field F] [Finite F]
    (e : Λ ≃* ↥(StatedSL 3 F)) : Nat.card (Subgroup.center Λ) ∣ 3 := by
  have h1 : Nat.card (Subgroup.center Λ) = Nat.card (Subgroup.center ↥(StatedSL 3 F)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have h2 : Nat.card (Subgroup.center ↥(StatedSL 3 F)) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    (Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 F)).toEquiv).symm
  rw [h1, h2, CFSG.RankThree.SubgroupLists.card_center_sl3]
  exact Nat.gcd_dvd_right _ _

private theorem card_center_equiv_sp4 {Λ F : Type} [Group Λ] [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : Λ ≃* ↥(StatedSp 2 F)) : Nat.card (Subgroup.center Λ) = 1 := by
  have h1 : Nat.card (Subgroup.center Λ) = Nat.card (Subgroup.center ↥(StatedSp 2 F)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [h1, CFSG.LieType.Universal.Symplectic.center_eq]
  have h2 : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) =
      Nat.card ↥(StatedSp 2 F ⊓ StatedScalars (Fin 2 ⊕ Fin 2) F) := by
    rw [← Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h2, (CFSG.LieType.Classical.symplectic_scalar_kernel F 2 (by norm_num)).2, hF]
  norm_num

private theorem nonempty_equiv_of_simple {Γ H : Type} [Group Γ] [Group H] (hΓ : IsSimpleGroup Γ)
    (hH : ∃ h : H, h ≠ 1) (π : Γ →* H) (hπ : Function.Surjective π) : Nonempty (H ≃* Γ) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact ⟨(MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp h, hπ⟩).symm⟩
  · exfalso
    obtain ⟨y, hy⟩ := hH
    obtain ⟨x, rfl⟩ := hπ y
    exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))

section Orders

variable {G : Type} [Group G] {L W : Subgroup G}

theorem xOrd_autOn (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hlie : IsSL3Quot L ∨ IsSp4Quot L) :
    XOrd (Nat.card ↥(autOn L W)) := by
  set ρ := S153D.autOnQuot hLW hker with hρ
  have hs : Function.Surjective ρ := S153D.autOnQuot_surjective hLW hker
  have hcent : ρ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
      (S153D.exists_autOnQuot_ne_one hLW hker hnt)
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(autOn L W) * Nat.card ρ.ker :=
    card_eq_mul_ker ρ hs
  have hdvd : Nat.card ρ.ker ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Subgroup.card_dvd_of_le hcent
  rcases hlie with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have : Finite F := inferInstance
    have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    have hΛ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hFc]
    have hZ : Nat.card ρ.ker ∣ 3 := hdvd.trans (card_center_equiv_sl3_dvd e)
    have hc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3 := (Nat.dvd_prime Nat.prime_three).1 hZ
    have hc3 : Nat.card ρ.ker ≤ 3 := by rcases hc with h | h <;> omega
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hbig : 60480 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      have := Nat.mul_le_mul (Nat.pow_le_pow_left hq4 3)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 3) 1))
      norm_num at this
      exact this
    refine ⟨?_, Or.inl ⟨n, Nat.card ρ.ker, hn, hc, ?_⟩⟩
    · rw [hΛ] at hcard
      have h3 : Nat.card ↥(autOn L W) * Nat.card ρ.ker ≤ Nat.card ↥(autOn L W) * 3 :=
        Nat.mul_le_mul_left _ hc3
      omega
    · rw [hΛ] at hcard
      have e3 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := pow_mul' 2 3 n
      have e2 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := pow_mul' 2 2 n
      rw [e3, e2, mul_comm, hcard]
  · have : Finite F := inferInstance
    have hF4 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card]; exact hF
    have hΛ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := by
      rw [Nat.card_congr e.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
        hF4, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    have hZ : Nat.card ρ.ker ∣ 1 := (card_center_equiv_sp4 hF4 e) ▸ hdvd
    have h1 : Nat.card ρ.ker = 1 := Nat.dvd_one.1 hZ
    rw [hΛ, h1] at hcard
    refine ⟨by omega, Or.inr (by omega)⟩

theorem not_surjective_autOn [Finite G] (hcover : AsA36NoOddCover)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hlie : IsSL3Quot L ∨ IsSp4Quot L) :
    ∀ m : ℕ, (m = 4 ∨ m = 5) → ∀ π : ↥(StatedSL m (ZMod 2)) →* ↥(autOn L W),
      ¬ Function.Surjective π := by
  intro m hm π hπ
  obtain ⟨k, hk⟩ := S153D.exists_autOnQuot_ne_one hLW hker hnt
  have hm3 : 3 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have hsimple : IsSimpleGroup ↥(StatedSL m (ZMod 2)) :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) hm3
  obtain ⟨e⟩ : Nonempty (↥(autOn L W) ≃* ↥(StatedSL m (ZMod 2))) :=
    nonempty_equiv_of_simple hsimple ⟨_, hk⟩ π hπ
  have hH : IsL345Type ↥(autOn L W) := by
    rcases hm with rfl | rfl
    · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨e⟩⟩)
    · exact Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨e⟩⟩)
  obtain ⟨e2⟩ := S153D.nonempty_quot_mulEquiv_autOn hcover hLW hq hsq hker hnt hH
  have hcardX : Nat.card ↥(autOn L W) = 20160 ∨ Nat.card ↥(autOn L W) = 9999360 := by
    rw [Nat.card_congr e.toEquiv]
    rcases hm with rfl | rfl
    · exact Or.inl card_statedSL_four_zmod1527d
    · exact Or.inr card_statedSL_five_zmod1527d
  have hcardΛ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(autOn L W) :=
    Nat.card_congr e2.toEquiv
  rcases hlie with ⟨n, F, _, _, hn, hF, ⟨e3⟩⟩ | ⟨F, _, _, hF, ⟨e3⟩⟩
  · have : Finite F := inferInstance
    have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    exact ne_card_sl3_1527d hFc hcardX ((Nat.card_congr e3.toEquiv).symm.trans hcardΛ)
  · have : Finite F := inferInstance
    have hF4 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card]; exact hF
    exact ne_card_sp4_1527d (n := 2) (by rw [hF4]; norm_num) hcardX
      ((Nat.card_congr e3.toEquiv).symm.trans hcardΛ)

end Orders

end CFSG.Quasithin.SzN15
