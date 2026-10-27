module

public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Vol2.Ch11SecA12Cop
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I V₁ K Y : Subgroup G} {n i : ℕ}

theorem pCoreOf_normalizer_ne_bot (h : Hyp11 G T L I n) {U : Subgroup G}
    (hU : IsVi T L I n i U) (hi : 1 ≤ i) : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
  intro h0
  apply IsVi.ne_bot h hU hi
  rw [eq_bot_iff, ← h0]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    ((isPGroup_fsuV h).to_le (IsVi.le_fsuV hU))

theorem sqtkGroup_of_le_normalizer_Vi (h : Hyp11 G T L I n) {U : Subgroup G}
    (hU : IsVi T L I n i U) (hi : 1 ≤ i) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.normalizer (U : Set G)) : SQTKGroup ↥Z := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  exact InternalSec.sqtkGroup_mono
    (InternalSec.sqtkGroup_of_localSQTK hloc (pCoreOf_normalizer_ne_bot h hU hi)) hZ

theorem a318_sup (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hYV : Y ≤ Subgroup.normalizer (V₁ : Set G))
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    A318Conclusion p (K.subgroupOf (K ⊔ Y)) := by
  have hKN := le_of_mem_cComp hK
  have hHN : K ⊔ Y ≤ Subgroup.normalizer (V₁ : Set G) := sup_le hKN hYV
  have hS := sqtkGroup_of_le_normalizer_Vi h hV₁ le_rfl hHN
  have hSQ := SQTKHyp.of_sqtkGroup ↥(K ⊔ Y) hS
  have hKc : K ∈ cComp (K ⊔ Y) := cComp_mem_of_le hK le_sup_left hHN
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := K) (le_sup_left : K ≤ K ⊔ Y)
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hr : 1 < CFSG.Open.pRank p (K.subgroupOf (K ⊔ Y)) := by
    rw [pRank_subgroupOf_eq le_sup_left hp hp2]
    omega
  exact a318 h318 hS (h36 _ hSQ) (h38 _ hSQ) (subgroupOf_mem_cComp hKc) hQ' hp hp2 hr

theorem false_of_isPGroup_commutator (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hY : IsPGroup 3 Y)
    (hYc : Y ≤ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)))
    (h2 : IsPGroup 2 ↥⁅LOf L V₁ ⊓ Subgroup.centralizer (Y : Set G),
      LOf L V₁ ⊓ Subgroup.centralizer (Y : Set G)⁆) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := LOf L V₁ with hL₁
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
  have hQ := isQuasisimple_of_mulEquiv_SL2 h.one_lt hF e
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) with hφ
  set D := (L₁ ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf L₁ with hD
  have hcop : Nat.Coprime 3 (Nat.card ↥(pCoreOf 2 L₁)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hsurj : D.map φ = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨c, hc, hcl⟩ := exists_mem_centralizer_of_coprime Nat.prime_three hY
      (fun y hy => (hYc hy).1) (CFSG.LieType.BorelTits.pCoreOf_le 2 L₁)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁) hcop
      (fun y hy b hb => (hYc hy).2.2 b hb) l.2
    refine ⟨⟨c, hc.1⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨k, hk, hkc⟩ := hcl
    have hk' : k ∈ CFSG.pCore 2 ↥L₁ := by assumption
    convert hk' using 1
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hkc.symm)
  have himg : (⁅D, D⁆).map φ = ⊤ := by
    rw [Subgroup.map_commutator, hsurj, ← commutator_def]
    exact hQ.1.commutator_eq_top
  have hDD : (⁅D, D⁆).map L₁.subtype =
      ⁅L₁ ⊓ Subgroup.centralizer (Y : Set G), L₁ ⊓ Subgroup.centralizer (Y : Set G)⁆ := by
    rw [Subgroup.map_commutator, hD, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have h2' : IsPGroup 2 ↥⁅D, D⁆ := by
    have e' : ↥⁅D, D⁆ ≃* ↥((⁅D, D⁆).map L₁.subtype) :=
      Subgroup.equivMapOfInjective _ _ L₁.subtype_injective
    rw [hDD] at e'
    exact h2.of_equiv e'.symm
  have hQ2 : IsPGroup 2 (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
    have h3 := h2'.map φ
    rw [himg] at h3
    exact h3.of_equiv Subgroup.topEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ2.of_equiv e)
  rw [card_SL_two hF] at hk
  have hdvd : 2 ^ (2 * n) - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk]; ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hn : 2 ≤ n := h.one_lt
  have h16 : 16 ≤ 2 ^ (2 * n) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hodd : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one (by omega)
  rcases j with _ | j
  · rw [pow_zero] at hj
    omega
  · rw [hj, pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

end CFSG.Quasithin.Vol2.Ch11.SecA
