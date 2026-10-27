module

public import CFSG.Quasithin.H13.U3L14D2
public import CFSG.Quasithin.H13.U3L14L3

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_mul_pow {x : G} (hx : x ∈ Lp) (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) {l : G}
    (hl : l ∈ Lp) : ∃ q ∈ pCoreOf 2 Lp, ∃ k : ℕ, l = q * x ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx hxo
  have hxQ : x ∉ pCoreOf 2 Lp := by
    intro h
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Lp ⟨x, h⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hx1 (eq_one_of_pow_two_pow_of_odd hxo h1 (pow_orderOf_eq_one x))
  obtain ⟨q, hq, k, rfl⟩ := F6.exists_mul_zpow_of_relIndex_eq_three
    (LieType.BorelTits.le_normalizer_pCoreOf 2 Lp) S.Lp3 hx hxQ hl
  have hxo3 : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨q, hq, (k % 3).toNat, ?_⟩
  congr 1
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)),
    ← zpow_mod_orderOf x k, hxo3]
  norm_num

theorem exists_pStar_G1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfail : ¬ ((pCoreOf 2 Lp).subgroupOf (A6.g1 T V)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V))) ≤
        centralizer (CFSG.pCore p (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :
          Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)))) :
    ∃ x ∈ Lp, Odd (orderOf x) ∧ x ≠ 1 ∧ ∃ hxH : x ∈ A6.g1 T V,
      ∃ X : Subgroup (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)),
        PStarData p (((pCoreOf 2 Lp).subgroupOf (A6.g1 T V)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V))))
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) ⟨x, hxH⟩) X := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := A6.g1 T V with hH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  obtain ⟨x, hx, hxo, hx1⟩ := S.exists_odd
  have hx3 := S.odd_pow_three hx hxo
  have hxH : x ∈ H := S.Lp_G1 hx
  refine ⟨x, hx, hxo, hx1, hxH, ?_⟩
  set Nsub := (Lp.subgroupOf H).map π with hNsub
  set B := ((pCoreOf 2 Lp).subgroupOf H).map π with hB
  have hOLp : pCoreOf 2 Lp ≤ Lp := LieType.BorelTits.pCoreOf_le 2 Lp
  have hQne : pCoreOf 2 H ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.ash.V₁_le_pCoreOf))
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
    have hN : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥H) := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    rw [CFSG.SectionRank.pRank_quotient_eq _ hN, pRank_top_subtype]
    exact pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke hQne hp hp2
  have hBN : B ≤ Nsub := map_mono fun y hy => mem_subgroupOf.2 (hOLp (mem_subgroupOf.1 hy))
  have hB2 : IsPGroup 2 B := by
    have h1 : IsPGroup 2 ((pCoreOf 2 Lp).subgroupOf H) :=
      (LieType.BorelTits.pCoreOf_isPGroup 2 Lp).of_equiv
        (subgroupOfEquivOfLe ((LieType.BorelTits.pCoreOf_le 2 Lp).trans S.Lp_G1)).symm
    exact h1.map π
  have hBn : ∀ b ∈ B, ∀ n ∈ Nsub, n * b * n⁻¹ ∈ B := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨l * q * l⁻¹, ?_, by simp⟩
    simp only [SetLike.mem_coe, mem_subgroupOf] at hq hl ⊢
    simpa using (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 Lp hl) _).1 hq
  have hxN : π ⟨x, hxH⟩ ∈ Nsub := ⟨⟨x, hxH⟩, mem_subgroupOf.2 hx, rfl⟩
  have hx3' : (π ⟨x, hxH⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hNB : ∀ n ∈ Nsub, ∃ b ∈ B, ∃ k : ℕ, n = b * (π ⟨x, hxH⟩) ^ k := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨q, hq, k, hlq⟩ := S.exists_mul_pow hx hxo hx1 (mem_subgroupOf.1 hl)
    have hqH : q ∈ H := S.Lp_G1 (hOLp hq)
    refine ⟨π ⟨q, hqH⟩, ⟨⟨q, hqH⟩, mem_subgroupOf.2 hq, rfl⟩, k, ?_⟩
    rw [← map_pow, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hlq)
  have hgen : Nsub ≤ closure {y | y ∈ Nsub ∧ Odd (orderOf y)} := by
    set C := closure {y | y ∈ Nsub ∧ Odd (orderOf y)} with hC
    have hLp : Lp ≤ (C.comap π).map H.subtype := by
      rw [S.Lp_eq]
      refine (closure_le _).2 fun y hy => ?_
      have hyH : y ∈ H := S.Lp_G1 hy.1
      refine ⟨⟨y, hyH⟩, subset_closure ⟨⟨⟨y, hyH⟩, mem_subgroupOf.2 hy.1, rfl⟩, ?_⟩, rfl⟩
      have h1 : orderOf (π ⟨y, hyH⟩) ∣ orderOf y := by
        rw [← Subgroup.orderOf_mk y hyH]
        exact orderOf_map_dvd π _
      exact Odd.of_dvd_nat hy.2 h1
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨h', hh', hh'l⟩ := hLp (mem_subgroupOf.1 hl)
    have : h' = l := Subtype.ext hh'l
    rw [← this]
    exact hh'
  exact exists_pStar hp2 hrank hBN hB2 hBn hxN hx3' hNB hgen hfail

end Set14

structure DData (T V Lp : Subgroup G) (p : ℕ) (P : Subgroup G) (x : G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  le_G1 : P ≤ A6.g1 T V
  G1_le : A6.g1 T V ≤ normalizer (P : Set G)
  xi : IsXi T P
  exp : ∀ y ∈ P, y ^ p ∈ pCoreOf 2 P
  index : (pCoreOf 2 P).relIndex P = p ^ 2 ∨
    ((pCoreOf 2 P).relIndex P = p ^ 3 ∧ ¬ ⁅P, P⁆ ≤ pCoreOf 2 P)
  rank : 2 ≤ CFSG.Open.pRank p P
  x_mem : x ∈ Lp
  x_odd : Odd (orderOf x)
  x_ne : x ≠ 1
  x_act : ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ ⁅P, P⁆ ⊔ pCoreOf 2 P
  q8 : p = 3 → ∃ b₁ ∈ pCoreOf 2 Lp, ∃ b₂ ∈ pCoreOf 2 Lp,
    (∀ y ∈ P, b₁ ^ 2 * y * (b₁ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
    (∀ y ∈ P, b₂ ^ 2 * y * (b₂ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
    (∀ y ∈ P, (b₁ * b₂) ^ 2 * y * ((b₁ * b₂) ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
    ∃ y ∈ P, ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∉ ⁅P, P⁆ ⊔ pCoreOf 2 P
  e9 : p = 3 → (pCoreOf 2 P).relIndex P = p ^ 2

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_dData {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfail : ¬ ((pCoreOf 2 Lp).subgroupOf (A6.g1 T V)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V))) ≤
        centralizer (CFSG.pCore p (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :
          Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)))) :
    ∃ (P : Subgroup G) (x : G), DData T V Lp p P x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := A6.g1 T V with hH
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set Q₁ := pCoreOf 2 H with hQ₁
  obtain ⟨x, hx, hxo, hx1, hxH, Xs, hX⟩ := S.exists_pStar_G1 hp hp2 hfail
  have hπ1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ Q₁ := fun h => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQ₁, coe_mem_pCoreOf_iff]
  have hXsn : Xs.Normal := hX.normal
  have hXsp : IsPGroup p Xs := CFSG.pCore_isPGroup.to_le hX.le
  set Pp : Subgroup G := (Xs.comap π).map H.subtype with hPp
  have hmemPp : ∀ y : G, y ∈ Pp ↔ ∃ hy : y ∈ H, π ⟨y, hy⟩ ∈ Xs := by
    intro y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h.2, hh⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hPpH : Pp ≤ H := map_subtype_le _
  have hHPp : H ≤ normalizer (Pp : Set G) := by
    have key : ∀ g ∈ H, ∀ y ∈ Pp, g * y * g⁻¹ ∈ Pp := by
      intro g hg y hy
      obtain ⟨hyH, hyX⟩ := (hmemPp y).1 hy
      refine (hmemPp _).2 ⟨mul_mem (mul_mem hg hyH) (inv_mem hg), ?_⟩
      have e : (⟨g * y * g⁻¹, mul_mem (mul_mem hg hyH) (inv_mem hg)⟩ : ↥H) =
          ⟨g, hg⟩ * ⟨y, hyH⟩ * (⟨g, hg⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hXsn.conj_mem _ hyX _
    intro g hg
    rw [mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun h => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this
  set P : Subgroup G := oTwoUpper Pp with hPdef
  have hPPp : P ≤ Pp := oTwoUpper_le Pp
  have hPH : P ≤ H := hPPp.trans hPpH
  have hHP : H ≤ normalizer (P : Set G) := hHPp.trans (normalizer_le_normalizer_oTwoUpper Pp)
  have hO2 : pCoreOf 2 P = P ⊓ Q₁ := by
    apply le_antisymm
    · refine le_inf (LieType.BorelTits.pCoreOf_le 2 P) ?_
      exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 P).trans hPH)
        (hHP.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P))
        (LieType.BorelTits.pCoreOf_isPGroup 2 P)
    · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun y hy => mem_normalizer_inf (le_normalizer hy)
          (LieType.BorelTits.le_normalizer_pCoreOf 2 H (hPH hy)))
        ((LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  set πP : ↥P →* (↥H ⧸ CFSG.pCore 2 ↥H) := π.comp (inclusion hPH) with hπPdef
  have hπP : ∀ y : ↥P, πP y = π ⟨y, hPH y.2⟩ := fun y => rfl
  have hrange : πP.range = Xs := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      rw [hπP]
      exact ((hmemPp y).1 (hPPp y.2)).2
    · intro γ hγ
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) γ
      have hhPp : (h : G) ∈ Pp := (hmemPp h).2 ⟨h.2, hγ⟩
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper Pp hhPp
      have hodd : Nat.Coprime (2 ^ k) (orderOf (π h)) := by
        obtain ⟨n, hn⟩ := hXsp ⟨π h, hγ⟩
        have h1 : orderOf (π h) ∣ p ^ n :=
          orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
        exact Nat.Coprime.coprime_dvd_right h1
          (Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
      have h1 : π h ^ 2 ^ k ∈ πP.range := by
        refine ⟨⟨(h : G) ^ 2 ^ k, hk⟩, ?_⟩
        rw [hπP, ← map_pow]
        congr 1
      exact (zpowers_le.2 h1) (A4.mem_zpowers_pow_of_coprime hodd)
  have hker : ∀ y : ↥P, πP y = 1 ↔ (y : G) ∈ pCoreOf 2 P := by
    intro y
    rw [hπP, hπ1, hO2]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hkerP : πP.ker = (pCoreOf 2 P).subgroupOf P := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hker y
  have hcommXs : ⁅Xs, Xs⁆ = (commutator ↥P).map πP := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
  have hcommP : ⁅P, P⁆.subgroupOf P = commutator ↥P := by
    have h1 : (commutator ↥P).map P.subtype = ⁅P, P⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hPP : ⁅P, P⁆ ≤ P := commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hDP : ⁅P, P⁆ ⊔ pCoreOf 2 P ≤ P := sup_le hPP (LieType.BorelTits.pCoreOf_le 2 P)
  have htrans : ∀ (y : G) (hy : y ∈ P),
      y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P ↔ πP ⟨y, hy⟩ ∈ ⁅Xs, Xs⁆ := by
    intro y hy
    have h1 : (⁅P, P⁆ ⊔ pCoreOf 2 P).subgroupOf P = (⁅Xs, Xs⁆).comap πP := by
      rw [subgroupOf_sup hPP (LieType.BorelTits.pCoreOf_le 2 P), hcommP,
        ← hkerP, hcommXs, Subgroup.comap_map_eq]
    have h2 : (⟨y, hy⟩ : ↥P) ∈ (⁅P, P⁆ ⊔ pCoreOf 2 P).subgroupOf P ↔
        y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P := mem_subgroupOf
    rw [← h2, h1, mem_comap]
  have hconjπ : ∀ (g : G) (hg : g ∈ H) (y : G) (hy : y ∈ P),
      πP ⟨g * y * g⁻¹, (mem_normalizer_iff.1 (hHP hg) y).1 hy⟩ =
        π ⟨g, hg⟩ * πP ⟨y, hy⟩ * (π ⟨g, hg⟩)⁻¹ := by
    intro g hg y hy
    rw [hπP, hπP, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hidx : (pCoreOf 2 P).relIndex P = Nat.card Xs := by
    rw [relIndex, index_eq_card, ← hkerP,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange πP).toEquiv, hrange]
  have hexp : ∀ y ∈ P, y ^ p ∈ pCoreOf 2 P := by
    intro y hy
    have h1 : πP ⟨y, hy⟩ ∈ Xs := hrange ▸ ⟨⟨y, hy⟩, rfl⟩
    have h2 : πP (⟨y, hy⟩ ^ p) = 1 := by rw [map_pow]; exact hX.pow _ h1
    have := (hker _).1 h2
    simpa using this
  have hindex : (pCoreOf 2 P).relIndex P = p ^ 2 ∨
      ((pCoreOf 2 P).relIndex P = p ^ 3 ∧ ¬ ⁅P, P⁆ ≤ pCoreOf 2 P) := by
    rw [hidx]
    rcases hX.card with h | ⟨h, hnab⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, fun hle => hnab fun a ha b hb => ?_⟩
      rw [← hrange] at ha hb
      obtain ⟨y, rfl⟩ := ha
      obtain ⟨z, rfl⟩ := hb
      have h1 : ((⁅y, z⁆ : ↥P) : G) ∈ pCoreOf 2 P := by
        apply hle
        have : ((⁅y, z⁆ : ↥P) : G) = ⁅(y : G), (z : G)⁆ := by simp [commutatorElement_def]
        rw [this]
        exact commutator_mem_commutator y.2 z.2
      have h2 := (hker _).2 h1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
  have hO2LpT : pCoreOf 2 Lp ≤ T := S.pCoreOf_Lp_le_R1.trans S.R1_le_T
  have hirred : ∀ Y : Subgroup G, ⁅P, P⁆ ⊔ pCoreOf 2 P ≤ Y → Y ≤ P →
      T ≤ normalizer (Y : Set G) → Y = ⁅P, P⁆ ⊔ pCoreOf 2 P ∨ Y = P := by
    intro Y hDY hYP hTY
    set Yb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (Y.subgroupOf P).map πP with hYb
    have hCY : ⁅Xs, Xs⁆ ≤ Yb := by
      rw [hcommXs]
      refine map_mono fun c hc => mem_subgroupOf.2 (hDY (mem_sup_left ?_))
      rw [← hcommP] at hc
      exact mem_subgroupOf.1 hc
    have hYX : Yb ≤ Xs := hrange ▸ map_le_range _ _
    have hBY : ∀ b ∈ ((pCoreOf 2 Lp).subgroupOf H).map π, b ∈ normalizer (Yb : Set _) := by
      rintro _ ⟨q, hq, rfl⟩
      have hqT : (q : G) ∈ T := hO2LpT (mem_subgroupOf.1 hq)
      have key : ∀ g ∈ T, ∀ (hg : g ∈ H), ∀ γ ∈ Yb, π ⟨g, hg⟩ * γ * (π ⟨g, hg⟩)⁻¹ ∈ Yb := by
        rintro g hgT hg _ ⟨y, hy, rfl⟩
        simp only [SetLike.mem_coe, mem_subgroupOf] at hy
        refine ⟨⟨g * y * g⁻¹, (mem_normalizer_iff.1 (hHP hg) y).1 y.2⟩, ?_, ?_⟩
        · simp only [SetLike.mem_coe, mem_subgroupOf]
          exact (mem_normalizer_iff.1 (hTY hgT) y).1 hy
        · exact hconjπ g hg y y.2
      rw [mem_normalizer_iff]
      intro γ
      refine ⟨fun h => key q hqT q.2 γ h, fun h => ?_⟩
      have h1 := key (q : G)⁻¹ (inv_mem hqT) (inv_mem q.2) _ h
      have e : π ⟨(q : G)⁻¹, inv_mem q.2⟩ = (π q)⁻¹ := by rw [← map_inv]; rfl
      rw [e] at h1
      simpa [mul_assoc] using h1
    rcases hX.irred Yb hCY hYX hBY with h | h
    · left
      refine le_antisymm (fun y hy => ?_) hDY
      rw [htrans y (hYP hy), ← h]
      exact ⟨⟨y, hYP hy⟩, mem_subgroupOf.2 hy, rfl⟩
    · right
      refine le_antisymm hYP (fun y hy => ?_)
      have h1 : πP ⟨y, hy⟩ ∈ Yb := h ▸ (hrange ▸ ⟨⟨y, hy⟩, rfl⟩)
      obtain ⟨y', hy', hyy'⟩ := h1
      simp only [SetLike.mem_coe, mem_subgroupOf] at hy'
      have h2 : πP (y'⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hyy', inv_mul_cancel]
      have h3 := (hker _).1 h2
      have h4 : y = (y' : G) * ((y'⁻¹ * ⟨y, hy⟩ : ↥P) : G) := by simp
      rw [h4]
      exact mul_mem hy' (hDY (mem_sup_right h3))
  have hrank : 2 ≤ CFSG.Open.pRank p P := by
    obtain ⟨E, hEX, hE, hEc⟩ := hX.rank
    have h1 : 2 ≤ CFSG.Open.pRank p Xs := CFSG.SectionRank.le_pRank hp.one_lt hEX hE hEc
    have hN : ¬ p ∣ Nat.card ↥πP.ker := by
      rw [hkerP]
      have h2 : IsPGroup 2 ↥((pCoreOf 2 P).subgroupOf P) :=
        (LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
          (subgroupOfEquivOfLe (LieType.BorelTits.pCoreOf_le 2 P)).symm
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    rw [← pRank_top_subtype, ← CFSG.SectionRank.pRank_quotient_eq πP.ker hN,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (QuotientGroup.quotientKerEquivRange πP),
      pRank_top_subtype, hrange]
    exact h1
  have hxact : ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ ⁅P, P⁆ ⊔ pCoreOf 2 P := by
    obtain ⟨γ, hγ, hγn⟩ := hX.act
    rw [← hrange] at hγ
    obtain ⟨⟨y, hy⟩, rfl⟩ := hγ
    have hxy : x * y * x⁻¹ ∈ P := (mem_normalizer_iff.1 (hHP hxH) y).1 hy
    refine ⟨y, hy, fun h => hγn ?_⟩
    have h1 := (htrans _ (mul_mem hxy (inv_mem hy))).1 h
    have e : πP ⟨x * y * x⁻¹ * y⁻¹, mul_mem hxy (inv_mem hy)⟩ =
        π ⟨x, hxH⟩ * πP ⟨y, hy⟩ * (π ⟨x, hxH⟩)⁻¹ * (πP ⟨y, hy⟩)⁻¹ := by
      rw [← hconjπ x hxH y hy, ← map_inv, ← map_mul]
      rfl
    rw [e] at h1
    exact h1
  have hq8 : p = 3 → ∃ b₁ ∈ pCoreOf 2 Lp, ∃ b₂ ∈ pCoreOf 2 Lp,
      (∀ y ∈ P, b₁ ^ 2 * y * (b₁ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
      (∀ y ∈ P, b₂ ^ 2 * y * (b₂ ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
      (∀ y ∈ P, (b₁ * b₂) ^ 2 * y * ((b₁ * b₂) ^ 2)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P) ∧
      ∃ y ∈ P, ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∉ ⁅P, P⁆ ⊔ pCoreOf 2 P := by
    intro hp3
    obtain ⟨_, ⟨q₁, hq₁, rfl⟩, _, ⟨q₂, hq₂, rfl⟩, h1, h2, h3, γ, hγ, hγn⟩ := hX.q8 hp3
    simp only [SetLike.mem_coe, mem_subgroupOf] at hq₁ hq₂
    have hinv : ∀ c : ↥H, (∀ γ ∈ Xs, π c * γ * (π c)⁻¹ * γ ∈ ⁅Xs, Xs⁆) →
        ∀ y ∈ P, (c : G) * y * (c : G)⁻¹ * y ∈ ⁅P, P⁆ ⊔ pCoreOf 2 P := by
      intro c hc y hy
      have hcy : (c : G) * y * (c : G)⁻¹ ∈ P := (mem_normalizer_iff.1 (hHP c.2) y).1 hy
      rw [htrans _ (mul_mem hcy hy)]
      have e : πP ⟨(c : G) * y * (c : G)⁻¹ * y, mul_mem hcy hy⟩ =
          π c * πP ⟨y, hy⟩ * (π c)⁻¹ * πP ⟨y, hy⟩ := by
        rw [← hconjπ c c.2 y hy, ← map_mul]
        rfl
      rw [e]
      exact hc _ (hrange ▸ ⟨⟨y, hy⟩, rfl⟩)
    refine ⟨q₁, hq₁, q₂, hq₂, ?_, ?_, ?_, ?_⟩
    · exact hinv (q₁ ^ 2) (fun γ hγ => by simpa [hπ] using h1 γ hγ)
    · exact hinv (q₂ ^ 2) (fun γ hγ => by simpa [hπ] using h2 γ hγ)
    · exact hinv ((q₁ * q₂) ^ 2) (fun γ hγ => by simpa [hπ] using h3 γ hγ)
    · rw [← hrange] at hγ
      obtain ⟨⟨y, hy⟩, rfl⟩ := hγ
      refine ⟨y, hy, fun h => hγn ?_⟩
      have hcy : ((⁅q₁, q₂⁆ : ↥H) : G) * y * ((⁅q₁, q₂⁆ : ↥H) : G)⁻¹ ∈ P :=
        (mem_normalizer_iff.1 (hHP (⁅q₁, q₂⁆ : ↥H).2) y).1 hy
      have hc : ((⁅q₁, q₂⁆ : ↥H) : G) = ⁅(q₁ : G), (q₂ : G)⁆ := by simp [commutatorElement_def]
      rw [← hc] at h
      have h4 := (htrans _ (mul_mem hcy (inv_mem hy))).1 h
      have e : πP ⟨((⁅q₁, q₂⁆ : ↥H) : G) * y * ((⁅q₁, q₂⁆ : ↥H) : G)⁻¹ * y⁻¹,
          mul_mem hcy (inv_mem hy)⟩ =
          π ⁅q₁, q₂⁆ * πP ⟨y, hy⟩ * (π ⁅q₁, q₂⁆)⁻¹ * (πP ⟨y, hy⟩)⁻¹ := by
        rw [← hconjπ _ (⁅q₁, q₂⁆ : ↥H).2 y hy, ← map_inv, ← map_mul]
        rfl
      rw [e, map_commutatorElement] at h4
      exact h4
  refine ⟨P, x, hp, hp2, hPH, hHP, ?_, hexp, hindex, hrank, hx, hxo, hx1, hxact, hq8, ?_⟩
  · refine ⟨(A4.oTwoUpper_oTwoUpper Pp).symm, S.T_G1.trans hHP, ?_, p, hp, hp2, hexp, hindex,
      hirred⟩
    intro hbot
    have hQne : Q₁ ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.ash.V₁_le_pCoreOf))
    apply hQne
    have hle : Q₁ ≤ pCoreOf 2 (P ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (S.Q1_T.trans le_sup_right)
        (sup_le (hPH.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H))
          (S.T_G1.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H)))
        (LieType.BorelTits.pCoreOf_isPGroup 2 H)
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  · intro hp3
    rw [hidx]
    exact hX.e9 hp3

end Set14

end CFSG.Quasithin.H13.U3
