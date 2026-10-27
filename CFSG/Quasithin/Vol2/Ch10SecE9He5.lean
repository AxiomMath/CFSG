module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LK
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313He
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem isSylowTwoOf_sup_zpowers (hyp : Hyp10 G T L I) {K₁ : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K₁ : Set G)) (hTK1 : T ⊓ K₁ ≤ T1 T L) {n : G}
    (hnK : n ∈ Subgroup.normalizer (K₁ : Set G))
    (hnT : n ∈ Subgroup.normalizer (T1 T L : Set G)) (hno : Odd (orderOf n)) :
    IsSylowTwoOf (T1 T L) (K₁ ⊔ (T1 T L ⊔ Subgroup.zpowers n)) := by
  have hTsyl : IsSylowTwoOf T (K₁ ⊔ T) :=
    ⟨le_sup_right, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow le_sup_right⟩
  have h1 : IsSylowTwoOf (T1 T L) (K₁ ⊔ T1 T L) :=
    isSylowTwoOf_sup_of_inf_le inf_le_left hTK (by rw [inf_comm]; exact hTK1) hTsyl
  set B := K₁ ⊔ T1 T L with hB
  have hnB : Subgroup.zpowers n ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnK hnT ⊢
    rw [Subgroup.map_sup, hnK, hnT]
  have hY : K₁ ⊔ (T1 T L ⊔ Subgroup.zpowers n) = Subgroup.zpowers n ⊔ B := by
    rw [hB, sup_comm (Subgroup.zpowers n), sup_assoc]
  refine ⟨le_sup_left.trans le_sup_right, h1.2.1, ?_⟩
  have hidx : (T1 T L).relIndex (Subgroup.zpowers n ⊔ B) =
      (T1 T L).relIndex B * B.relIndex (Subgroup.zpowers n ⊔ B) :=
    (Subgroup.relIndex_mul_relIndex (T1 T L) B (Subgroup.zpowers n ⊔ B) le_sup_right
      le_sup_right).symm
  have h2 : B.relIndex (Subgroup.zpowers n ⊔ B) = B.relIndex (Subgroup.zpowers n) :=
    relIndex_sup_of_le_normalizer_aux hnB
  have h3 : B.relIndex (Subgroup.zpowers n) ∣ orderOf n := by
    rw [← Nat.card_zpowers]
    exact Subgroup.index_dvd_card (B.subgroupOf (Subgroup.zpowers n))
  have h4 : ¬ 2 ∣ B.relIndex (Subgroup.zpowers n) := fun h2' =>
    (Nat.not_even_iff_odd.mpr hno) ((even_iff_two_dvd).mpr (h2'.trans h3))
  show ¬ 2 ∣ (T1 T L).relIndex (K₁ ⊔ (T1 T L ⊔ Subgroup.zpowers n))
  rw [hY, hidx, h2]
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h5 with h6 | h6
  · exact h1.2.2 h6
  · exact h4 h6

theorem normalizer_T1_le_XOf_of_he (hRed : HeReduce)
    (hF : H13.FactAutHeSylow) (h : MaxCtx T L I t Ψ c) (h3 : Case10_1_1Three T L I)
    (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb)
    (hH : InH (XOf T L Ψ A ⊔ T)
      (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hHK : Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) ≤
      Subgroup.normalizer (K₁ : Set G))
    (hXK : XOf T L Ψ A ≤ K₁)
    (he : Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hTK1, -⟩ := hRed G T L I h.hyp h3 _
    (isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA) le_sup_right _ hH K₁ hK₁ hHK hXK he
  have hTH : T ≤ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    le_sup_right.trans hH.1
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := hTH.trans hHK
  have hXi := isXi_XOf h hD
  have hOT : pCoreOf 2 K₁ ≤ T := by
    have h1 : pCoreOf 2 K₁ ≤ pCoreOf 2 (K₁ ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
        ((sup_le Subgroup.le_normalizer hTK).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
    exact h1.trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      ⟨le_sup_right, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow le_sup_right⟩)
  have hON : pCoreOf 2 K₁ ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := hOT.trans hXi.2.1
  have hconj : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
      ∀ y ∈ XOf T L Ψ A, n * y * n⁻¹ ∈ XOf T L Ψ A := by
    intro n hn hno
    have hnK : n ∈ Subgroup.normalizer (K₁ : Set G) := hHK (Subgroup.mem_sup_left hn)
    have hEN : K₁ ⊔ (T1 T L ⊔ Subgroup.zpowers n) ≤ Subgroup.normalizer (K₁ : Set G) :=
      sup_le Subgroup.le_normalizer
        (sup_le (inf_le_left.trans hTK) (Subgroup.zpowers_le.mpr hnK))
    have hY := isSylowTwoOf_sup_zpowers h.hyp hTK hTK1 hnK hn hno
    have hcomm : ∀ y ∈ K₁, n * y * n⁻¹ * y⁻¹ ∈ pCoreOf 2 K₁ := fun y hy =>
      H13.Lem3313.comm_mem_pCoreOf_of_he hF he hEN hY
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))) hn hno hy
    set φ : ↥K₁ →* ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hφ
    have hker : ∀ k : ↥K₁, φ k = 1 → (k : G) ∈ pCoreOf 2 K₁ := fun k hk => by
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact ⟨_, hk, rfl⟩
    have hgen : ∀ x ∈ XOf T L Ψ A, Odd (orderOf x) → n * x * n⁻¹ ∈ XOf T L Ψ A := by
      intro x hx hxo
      have hxK := hXK hx
      have hnxK : n * x * n⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hnK x).mp hxK
      have hcK : n * x * n⁻¹ * x⁻¹ ∈ K₁ := K₁.mul_mem hnxK (K₁.inv_mem hxK)
      have hk1 : φ ⟨n * x * n⁻¹ * x⁻¹, hcK⟩ = 1 := by
        obtain ⟨k, hk, hkeq⟩ := hcomm x hxK
        have e : k = ⟨n * x * n⁻¹ * x⁻¹, hcK⟩ := Subtype.ext hkeq
        rw [← e, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hk
      have e2 : (⟨n * x * n⁻¹ * x⁻¹, hcK⟩ : ↥K₁) = ⟨n * x * n⁻¹, hnxK⟩ * (⟨x, hxK⟩ : ↥K₁)⁻¹ :=
        Subtype.ext (by simp)
      rw [e2, map_mul, map_inv, mul_inv_eq_one] at hk1
      refine C10P34.mem_of_odd_of_mem_map hker hON hXi.1.symm hnxK ?_
        ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hx, hk1.symm⟩
      rw [show n * x * n⁻¹ = MulAut.conj n x from rfl, MulEquiv.orderOf_eq]
      exact hxo
    intro y hy
    have hy' : y ∈ Subgroup.closure
        {x | x ∈ preIn Ψ (A.prod A) ⊔ T ∧ Odd (orderOf x)} := hy
    clear hy
    induction hy' using Subgroup.closure_induction with
    | mem z hz => exact hgen z (mem_oTwoUpper_of_odd hz.1 hz.2) hz.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hodd : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
      n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
    intro n hn hno
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj n hn hno y hy, fun hy => ?_⟩
    have hno' : Odd (orderOf n⁻¹) := by rw [orderOf_inv]; exact hno
    have := hconj n⁻¹ (Subgroup.inv_mem _ hn) hno' _ hy
    simpa [mul_assoc] using this
  have hTN := T1_normal h.h37 h.h38 h.hyp
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
    ⟨hTN, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow hTN⟩
  refine (C10P34.le_oTwoUpper_sup hTsyl).trans (sup_le ?_ hXi.2.1)
  exact (Subgroup.closure_le _).mpr fun n hn => hodd n hn.1 hn.2

end CFSG.Quasithin.Vol2.Ch10.SecB
