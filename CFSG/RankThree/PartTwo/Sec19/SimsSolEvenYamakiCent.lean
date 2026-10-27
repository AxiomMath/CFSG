module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiOmega

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open CFSG.ClassicalInvolution.Solomon73

@[expose] def P2 : Finset SC := scOrb 1 ∪ scOrb 2 ∪ scOrb 5

theorem P2_spec : ∀ c ∈ scOrb 0 ∪ scOrb 6, ∀ c' ∈ scOrb 0 ∪ scOrb 6, c ≠ c' → c + c' ∈ P2 := by
  decide

theorem card_P2 : P2.card = 21 := by decide

theorem pi3_split : sc [2] = sc [0, 1, 2, 5] + sc [0, 1, 5] ∧ sc [0, 1, 2, 5] ∈ scOrb 0 ∪ scOrb 6 ∧
    sc [0, 1, 5] ∈ scOrb 0 ∪ scOrb 6 ∧ sc [0, 1, 2, 5] ≠ sc [0, 1, 5] := by decide

@[expose] def lineSum (c : Perm (Fin 7)) (ℓ : Finset (Fin 7)) : SC := ∑ j ∈ ℓ, bW (c⁻¹ j)

@[expose] def LS (c : Perm (Fin 7)) : Finset SC := (fanoLines.map (lineSum c)).toFinset

theorem mem_LS {c : Perm (Fin 7)} {x : SC} : x ∈ LS c ↔ ∃ ℓ ∈ fanoLines, lineSum c ℓ = x := by
  rw [LS, List.mem_toFinset, List.mem_map]

theorem sc01_mem_LS : sc [0, 1] ∈ LS s7c1 ∧ sc [0, 1] ∈ LS s7c2 := by decide

theorem card_LS : (LS s7c1).card = 7 ∧ (LS s7c2).card = 7 := by decide

theorem card_filter_sc01 : ((scOrb 0 ∪ scOrb 6).filter fun e => sc [0, 1] + e ∈ P2).card = 3 := by
  decide

set_option synthInstance.maxSize 1024 in
theorem classes_c1 : ∀ x : SC, x ≠ 0 → x ∈ scOrb 0 ∪ scOrb 6 ∨ x ∈ P2 ∨ x ∈ LS s7c1 ∨
    ((scOrb 0 ∪ scOrb 6).filter fun e => x + e ∈ LS s7c1).card = 1 := by
  decide

set_option synthInstance.maxSize 1024 in
theorem classes_c2 : ∀ x : SC, x ≠ 0 → x ∈ scOrb 0 ∪ scOrb 6 ∨ x ∈ P2 ∨ x ∈ LS s7c2 ∨
    ((scOrb 0 ∪ scOrb 6).filter fun e => x + e ∈ LS s7c2).card = 1 := by
  decide

theorem pCoreOf_le_of_maximal {G : Type} [Group G] [Finite G] {L R : Subgroup G} (hRL : R ≤ L)
    (hR : IsPGroup 2 R) (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → R ≤ Q → Q ≤ L → Q = R) :
    pCoreOf 2 L ≤ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' L
  have hRN : R ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hRL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hsup : IsPGroup 2 (R ⊔ pCoreOf 2 L : Subgroup G) := hR.to_sup_of_normal_right' hQ2 hRN
  have hle : R ⊔ pCoreOf 2 L ≤ L := sup_le hRL (Subgroup.map_subtype_le _)
  have := hmax _ hsup le_sup_left hle
  exact le_sup_right.trans this.le

theorem exists_mem_normalizer_not_mem {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 2 P) (hQP : Q ≤ P) (hne : Q ≠ P) :
    ∃ g ∈ P, g ∉ Q ∧ g ∈ Subgroup.normalizer (Q : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hQP fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥P) ∈ Q.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨g, hgN, hgQ⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨g, g.2, fun h => hgQ h, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    by_cases hxP : x ∈ P
    · have := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hxP⟩).mp hx
      exact this
    · exact absurd (hQP hx) hxP
  · intro hx
    have hxP : x ∈ P := by
      have h1 : (g : G) * x * (g : G)⁻¹ ∈ P := hQP hx
      have := P.mul_mem (P.mul_mem (P.inv_mem g.2) h1) g.2
      rwa [show (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g = x by group] at this
    exact (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hxP⟩).mpr hx

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

abbrev KK : Subgroup G := Y.NA ⊔ Subgroup.centralizer ({z} : Set G)

theorem exists_conj_mem_A {t : G} (ht : t ∈ Y.T) (h2 : t * t = 1) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * t * c⁻¹ ∈ Y.A := by
  obtain ⟨htC, htD⟩ := Y.mem_lift.mp ht
  have hsq : (Y.ϑ ⟨t, htC⟩ : Wr 6) * Y.ϑ ⟨t, htC⟩ = 1 := by
    rw [← Y.ϑ_mul_coe htC htC]
    have e : (⟨t * t, Subgroup.mul_mem _ htC htC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext h2
    rw [e, map_one]
    rfl
  obtain ⟨w, hw, hwS⟩ := exists_conj_mem_SW htD hsq
  refine ⟨Y.ι ⟨w, hw⟩, Y.ι_mem_C _, Y.mem_lift.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Y.ι_mem_C _) htC) (Subgroup.inv_mem _ (Y.ι_mem_C _)), ?_⟩⟩
  have e : (⟨Y.ι ⟨w, hw⟩ * t * (Y.ι ⟨w, hw⟩)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Y.ι_mem_C _) htC) (Subgroup.inv_mem _ (Y.ι_mem_C _))⟩ :
      ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨Y.ι ⟨w, hw⟩, Y.ι_mem_C _⟩ * ⟨t, htC⟩ * (⟨Y.ι ⟨w, hw⟩, Y.ι_mem_C _⟩)⁻¹ := rfl
  rw [e]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [show (Y.ϑ ⟨Y.ι ⟨w, hw⟩, Y.ι_mem_C _⟩ : Wr 6) = w from congrArg Subtype.val (Y.ϑ_ι _)]
  exact hwS

theorem exists_conj_le_T (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T) {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∀ x ∈ Q, c * x * c⁻¹ ∈ Y.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hTC : (P : Subgroup G) ≤ C := hP ▸ Y.T_le_C
  have hQ2' : IsPGroup 2 (Q.subgroupOf C) := hQ2.comap_subtype
  obtain ⟨S, hS⟩ := hQ2'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) S (P.subtype hTC)
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxS : (⟨x, hQC hx⟩ : ↥C) ∈ (S : Subgroup ↥C) := hS hx
  have h3 : c * ⟨x, hQC hx⟩ * c⁻¹ ∈ ((P.subtype hTC : Sylow 2 ↥C) : Subgroup ↥C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hxS
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h3
  rw [← hP]
  exact h3

theorem exists_conj_mem_A_of_mem_C (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) (h2 : x * x = 1) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * x * c⁻¹ ∈ Y.A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : x = 1
  · exact ⟨1, Subgroup.one_mem _, by rw [h1, mul_one, one_mul, inv_one]; exact Y.A.one_mem⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.zpowers_le).mpr hx
  obtain ⟨c₁, hc₁, hT⟩ := Y.exists_conj_le_T P hP hx2 hxC
  have ht := hT x (Subgroup.mem_zpowers x)
  have ht2 : (c₁ * x * c₁⁻¹) * (c₁ * x * c₁⁻¹) = 1 := by
    rw [show (c₁ * x * c₁⁻¹) * (c₁ * x * c₁⁻¹) = c₁ * (x * x) * c₁⁻¹ by group, h2]
    group
  obtain ⟨c₂, hc₂, hA⟩ := Y.exists_conj_mem_A ht ht2
  refine ⟨c₂ * c₁, Subgroup.mul_mem _ hc₂ hc₁, ?_⟩
  rw [show c₂ * c₁ * x * (c₂ * c₁)⁻¹ = c₂ * (c₁ * x * c₁⁻¹) * c₂⁻¹ by group]
  exact hA

omit [Finite G] in
theorem zz_one (hz : orderOf z = 2) : z * z = 1 := by
  rw [← sq, ← hz, pow_orderOf_eq_one]

theorem mem_K_of_conj_mem_C (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A) (hz : orderOf z = 2) {g : G}
    (hg : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G)) : g ∈ Y.KK := by
  have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    rw [show (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, zz_one hz]
    group
  obtain ⟨c, hc, hca⟩ := Y.exists_conj_mem_A_of_mem_C P hP hg h2
  have hca' : (c * g) * z * (c * g)⁻¹ ∈ Y.A := by
    rw [show (c * g) * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ by group]
    exact hca
  obtain ⟨m, hm, hmz⟩ := Y.exists_normalizer_conj P hP hE Y.z_mem_A hca' rfl
  have hk : m⁻¹ * (c * g) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * (c * g) * z = m⁻¹ * ((c * g) * z * (c * g)⁻¹) * (c * g) := by group
      _ = m⁻¹ * (m * z * m⁻¹) * (c * g) := by rw [hmz]
      _ = z * (m⁻¹ * (c * g)) := by group
  have e : g = c⁻¹ * m * (m⁻¹ * (c * g)) := by group
  rw [e]
  have hCK : Subgroup.centralizer ({z} : Set G) ≤ Y.KK := le_sup_right
  have hNK : Y.NA ≤ Y.KK := le_sup_left
  exact Y.KK.mul_mem (Y.KK.mul_mem (hCK (Subgroup.inv_mem _ hc)) (hNK hm)) (hCK hk)

theorem mul_self_of_mem_A {y : G} (hy : y ∈ Y.A) : y * y = 1 := Y.isE64_A.2.1 y hy

theorem centralizer_le_K_of_maximal (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hz : orderOf z = 2) {y : G} (hyA : y ∈ Y.A) (hy1 : y ≠ 1) {R : Subgroup G}
    (hRy : R ≤ Subgroup.centralizer ({y} : Set G)) (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hR2 : IsPGroup 2 R)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → R ≤ Q → Q ≤ Subgroup.centralizer ({y} : Set G) →
      Q = R) :
    Subgroup.centralizer ({y} : Set G) ≤ Y.KK := by
  set L := Subgroup.centralizer ({y} : Set G) with hLdef
  have hloc := isTwoLocal_centralizer_of_involution hy1 (Y.mul_self_of_mem_A hyA)
  have hcl := hchar L hloc
  have hOR : pCoreOf 2 L ≤ R := pCoreOf_le_of_maximal hRy hR2 hmax
  have hzL : z ∈ L := Subgroup.mem_centralizer_singleton_iff.mpr (Y.A_comm Y.z_mem_A hyA)
  have hzc : z ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRz (hOR hr))
  have hzO : z ∈ pCoreOf 2 L := hcl ⟨hzL, hzc⟩
  intro g hg
  exact Y.mem_K_of_conj_mem_C P hP hE hz
    (hRz (hOR (CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized L hg hzO)))

theorem centralizer_conj_le {b m : G} (hm : m ∈ Y.KK)
    (hb : Subgroup.centralizer ({b} : Set G) ≤ Y.KK) :
    Subgroup.centralizer ({m * b * m⁻¹} : Set G) ≤ Y.KK := by
  intro g hg
  have h1 : m⁻¹ * g * m ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    calc m⁻¹ * g * m * b = m⁻¹ * (g * (m * b * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * b * m⁻¹) * g) * m := by rw [hg]
      _ = b * (m⁻¹ * g * m) := by group
  have e : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e]
  exact Y.KK.mul_mem (Y.KK.mul_mem hm (hb h1)) (Y.KK.inv_mem hm)

section Classes

variable (hstd : Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6)
include hstd

theorem cc_mem_Omega {n : G} (hn : n ∈ Y.NA) {e : SC} (he : e ∈ scOrb 0 ∪ scOrb 6) :
    Y.cc n e ∈ scOrb 0 ∪ scOrb 6 := by
  rw [← Y.mem_conj_z_iff hstd, Y.σA_cc hn]
  exact conj_mem_conjSet ((Y.mem_conj_z_iff hstd e).mpr he) hn

omit hstd in
theorem cc_injective {n : G} (hn : n ∈ Y.NA) : Function.Injective (Y.cc n) := by
  intro x x' h
  have h1 := congrArg Y.σA h
  rw [Y.σA_cc hn, Y.σA_cc hn] at h1
  exact Y.σA_injective (mul_left_cancel (mul_right_cancel h1))

omit hstd in
theorem cc_sum {n : G} (hn : n ∈ Y.NA) {ι : Type*} (s : Finset ι) (f : ι → SC) :
    Y.cc n (∑ i ∈ s, f i) = ∑ i ∈ s, Y.cc n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Y.cc_zero hn
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Y.cc_add hn, ih]

omit hstd in
theorem cc_conj_of_mem {n : G} (hn : n ∈ Y.NA) {a : G} (ha : a ∈ Y.A) :
    Y.cc n (Y.coordOf a) = Y.coordOf (n * a * n⁻¹) := by
  apply Y.σA_injective
  rw [Y.σA_cc hn, Y.σA_coordOf ha, Y.σA_coordOf (Y.conj_mem_A hn ha)]

theorem coord_conj_pi3 (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12) :
    Y.coord (conjSet Y.NA Y.π3) = P2 := by
  obtain ⟨d, he1, he2, hne⟩ := pi3_split
  have hπ : Y.π3 = Y.σA (sc [0, 1, 2, 5]) * Y.σA (sc [0, 1, 5]) := by
    rw [← Y.σA_add, ← d, Y.σA_pi3]
  have hsub : Y.coord (conjSet Y.NA Y.π3) ⊆ P2 := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := Y.mem_coord.mp hx
    have h1 : Y.σA x = Y.σA (Y.cc n (sc [0, 1, 2, 5]) + Y.cc n (sc [0, 1, 5])) := by
      rw [Y.σA_add, Y.σA_cc hn, Y.σA_cc hn, ← hnx, hπ]
      group
    rw [Y.σA_injective h1]
    exact P2_spec _ (Y.cc_mem_Omega hstd hn he1) _ (Y.cc_mem_Omega hstd hn he2)
      fun h => hne (Y.cc_injective hn h)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [card_P2, Y.card_coord (conjSet_normalizer_subset Y.π3_mem_A),
    Y.ncard_conj_pi3_of_le (Y.centralizer_pi3_le hchar P hP hz h3 h12),
    ← Y.card_coord (conjSet_normalizer_subset Y.z_mem_A), hstd, card_Omega]

variable {c : Perm (Fin 7)} (hc : c = s7c1 ∨ c = s7c2) (hL : ∀ n : ↥Y.NA, Y.permHom hstd n ∈ Lc c)
include hc hL

omit hstd hL in
theorem LS_facts' : sc [0, 1] ∈ LS c ∧ (LS c).card = 7 ∧
    ∀ x : SC, x ≠ 0 → x ∈ scOrb 0 ∪ scOrb 6 ∨ x ∈ P2 ∨ x ∈ LS c ∨
      ((scOrb 0 ∪ scOrb 6).filter fun e => x + e ∈ LS c).card = 1 := by
  rcases hc with rfl | rfl
  · exact ⟨sc01_mem_LS.1, card_LS.1, classes_c1⟩
  · exact ⟨sc01_mem_LS.2, card_LS.2, classes_c2⟩

omit hc in
theorem cc_mem_LS (n : ↥Y.NA) {x : SC} (hx : x ∈ LS c) : Y.cc n x ∈ LS c := by
  obtain ⟨ℓ, hℓ, rfl⟩ := mem_LS.mp hx
  have hlam : InL32 (c * Y.permHom hstd n * c⁻¹) := hL n
  refine mem_LS.mpr ⟨ℓ.map (c * Y.permHom hstd n * c⁻¹).toEmbedding, (hlam ℓ hℓ).1, ?_⟩
  rw [lineSum, lineSum, Y.cc_sum n.2, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Y.bW_permHom hstd n]
  congr 1
  simp [Perm.mul_apply]

omit hstd hc hL in
theorem π12_mul_z (hz : orderOf z = 2) : Y.π12 * z = Y.π3 := by
  have h1 : Y.π3 * z = z * Y.π3 := Subgroup.mem_centralizer_singleton_iff.mp Y.π3_mem_C
  rw [← Y.z_mul_π3, mul_assoc, h1, ← mul_assoc, zz_one hz, one_mul]

theorem coord_conj_pi12 (hchar : IsCharTwoType G) (P : Sylow 2 G) (hP : (P : Subgroup G) = Y.T)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12) :
    Y.coord (conjSet Y.NA Y.π12) = LS c := by
  obtain ⟨h01, hcard, -⟩ := LS_facts' hc
  have hP2 := Y.coord_conj_pi3 hstd hchar P hP hz h3 h12
  have hsub : Y.coord (conjSet Y.NA Y.π12) ⊆ LS c := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := Y.mem_coord.mp hx
    have h1 : x = Y.cc n (sc [0, 1]) := by
      apply Y.σA_injective
      rw [Y.σA_cc hn, Y.σA_pi12, hnx]
    rw [h1]
    exact Y.cc_mem_LS hstd hL ⟨n, hn⟩ h01
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [hcard, Y.card_coord (conjSet_normalizer_subset Y.π12_mem_A)]
  show 7 ≤ (conjSet Y.NA Y.π12).ncard
  set N12 := Y.NA ⊓ Subgroup.centralizer ({Y.π12} : Set G) with hN12
  have e_a := ncard_conjSet_mul Y.NA Y.π12
  have e_b := ncard_conjSet_mul N12 z
  have hX12 : N12 ⊓ Subgroup.centralizer {z} = Y.XN ⊓ Subgroup.centralizer {Y.π12} :=
    inf_right_comm _ _ _
  rw [hX12] at e_b
  have e_c := ncard_conjSet_mul Y.XN Y.π12
  have h3' := Y.three_le_ncard_conjSet_pi12 (H := Y.XN) le_rfl
  have hz3 : (conjSet N12 z).ncard ≤ 3 := by
    set J := (scOrb 0 ∪ scOrb 6).filter fun e => sc [0, 1] + e ∈ P2 with hJ
    have hsubJ : conjSet N12 z ⊆ Y.σA '' ↑J := by
      rintro y ⟨n, hn, rfl⟩
      have hyN : n * z * n⁻¹ ∈ conjSet Y.NA z := ⟨n, hn.1, rfl⟩
      have hyA := conjSet_normalizer_subset Y.z_mem_A hyN
      refine ⟨Y.coordOf (n * z * n⁻¹), ?_, Y.σA_coordOf hyA⟩
      have hF : Y.coordOf (n * z * n⁻¹) ∈ scOrb 0 ∪ scOrb 6 := by
        rw [← Y.mem_conj_z_iff hstd, Y.σA_coordOf hyA]
        exact hyN
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hF, ?_⟩)
      rw [← hP2, Y.mem_coord, Y.σA_add, Y.σA_coordOf hyA, Y.σA_pi12]
      have hnπ : n * Y.π12 * n⁻¹ = Y.π12 := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hn.2, mul_inv_cancel_right]
      refine ⟨n, hn.1, ?_⟩
      rw [← Y.π12_mul_z hz]
      calc n * (Y.π12 * z) * n⁻¹ = (n * Y.π12 * n⁻¹) * (n * z * n⁻¹) := by group
        _ = Y.π12 * (n * z * n⁻¹) := by rw [hnπ]
    calc (conjSet N12 z).ncard ≤ (Y.σA '' ↑J).ncard :=
          Set.ncard_le_ncard hsubJ (Set.toFinite _)
      _ = J.card := by rw [Set.ncard_image_of_injective _ Y.σA_injective, Set.ncard_coe_finset]
      _ = 3 := card_filter_sc01
  have hN : Nat.card N12 ≤ 1536 := by
    rw [← e_b, ← Y.card_XN, ← e_c]
    exact Nat.mul_le_mul hz3 le_rfl |>.trans (Nat.mul_le_mul h3' le_rfl)
  have e_a' : (conjSet Y.NA Y.π12).ncard * Nat.card N12 = 10752 := by
    rw [← Y.card_NA hstd]
    exact e_a
  by_contra hlt
  push Not at hlt
  have : (conjSet Y.NA Y.π12).ncard * Nat.card N12 ≤ 6 * 1536 :=
    Nat.mul_le_mul (by omega) hN
  omega

omit hc in
theorem centralizer_N_le_C {y : G} (hyA : y ∈ Y.A)
    (hU : ∀ e ∈ scOrb 0 ∪ scOrb 6, Y.coordOf y + e ∈ LS c → e = sc [0, 1, 2])
    (hU0 : Y.coordOf y + sc [0, 1, 2] ∈ LS c) {n : G} (hn : n ∈ Y.NA) (hny : n * y = y * n) :
    n ∈ Subgroup.centralizer ({z} : Set G) := by
  have h012 : sc [0, 1, 2] ∈ scOrb 0 ∪ scOrb 6 := by decide
  have he := Y.cc_mem_Omega hstd hn h012
  have h1 : Y.coordOf y + Y.cc n (sc [0, 1, 2]) ∈ LS c := by
    have := Y.cc_mem_LS hstd hL ⟨n, hn⟩ hU0
    rwa [Y.cc_add hn, Y.cc_conj_of_mem hn hyA, show n * y * n⁻¹ = y by rw [hny]; group] at this
  have h2 := hU _ he h1
  have hz0 : Y.σA (sc [0, 1, 2]) = z := by rw [sc012_eq, Y.σA_one_zero]
  have h3 := Y.σA_cc hn (sc [0, 1, 2])
  rw [h2, hz0] at h3
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [← h3]

end Classes

omit [Finite G] in
theorem mem_normalizer_of_map_eq {B : Subgroup G} {r : G}
    (h : B.map (MulAut.conj r).toMonoidHom = B) : r ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨a, ha, hax⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hax
    have : a = x := mul_left_cancel (mul_right_cancel hax)
    rw [← this]
    exact ha

section Classes2

variable (hstd : Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6)
  {c : Perm (Fin 7)} (hc : c = s7c1 ∨ c = s7c2) (hL : ∀ n : ↥Y.NA, Y.permHom hstd n ∈ Lc c)
include hstd hL

theorem centralizer_le_K_of_point (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hz : orderOf z = 2) {y : G} (hyA : y ∈ Y.A) (hy1 : y ≠ 1)
    (hU : ∀ e ∈ scOrb 0 ∪ scOrb 6, Y.coordOf y + e ∈ LS c → e = sc [0, 1, 2])
    (hU0 : Y.coordOf y + sc [0, 1, 2] ∈ LS c) :
    Subgroup.centralizer ({y} : Set G) ≤ Y.KK := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cy := Subgroup.centralizer ({y} : Set G) with hCy
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hA : Y.A ≤ C ⊓ Cy := fun a ha =>
    ⟨Y.A_le_C ha, Subgroup.mem_centralizer_singleton_iff.mpr (Y.A_comm ha hyA)⟩
  have hA2 : IsPGroup 2 Y.A := IsPGroup.of_card (n := 6) (by rw [Y.card_A]; norm_num)
  obtain ⟨S, hS⟩ := (hA2.comap_subtype (K := C ⊓ Cy)).exists_le_sylow
  set Q : Subgroup G := (S : Subgroup ↥(C ⊓ Cy)).map (C ⊓ Cy).subtype with hQdef
  have hQle : Q ≤ C ⊓ Cy := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.map _
  have hAQ : Y.A ≤ Q := fun a ha => ⟨⟨a, hA ha⟩, hS ha, rfl⟩
  have hQmax : ∀ Q' : Subgroup G, IsPGroup 2 Q' → Q ≤ Q' → Q' ≤ C ⊓ Cy → Q' = Q := by
    intro Q' hQ'2 hQQ' hQ'le
    have h1 : IsPGroup 2 (Q'.comap (C ⊓ Cy).subtype) := hQ'2.comap_subtype
    have h2 : (S : Subgroup ↥(C ⊓ Cy)) ≤ Q'.comap (C ⊓ Cy).subtype := fun x hx =>
      hQQ' ⟨x, hx, rfl⟩
    have h3 := S.is_maximal' h1 h2
    refine le_antisymm (fun x hx => ?_) hQQ'
    have hx' : (⟨x, hQ'le hx⟩ : ↥(C ⊓ Cy)) ∈ (S : Subgroup ↥(C ⊓ Cy)) := by
      rw [← h3]
      exact hx
    exact ⟨_, hx', rfl⟩
  have hAuniq : ∀ B : Subgroup G, B ≤ Q → IsE64 B → B = Y.A := by
    intro B hBQ hB
    obtain ⟨d, -, hdT⟩ := Y.exists_conj_le_T P hP hQ2 (hQle.trans inf_le_left)
    have h1 : B.map (MulAut.conj d).toMonoidHom = Y.A :=
      hE _ (by rintro _ ⟨b, hb, rfl⟩; exact hdT b (hBQ hb)) (isE64_map_conj hB d)
    have h2 : Y.A.map (MulAut.conj d).toMonoidHom = Y.A :=
      hE _ (by rintro _ ⟨a, ha, rfl⟩; exact hdT a (hAQ ha)) (isE64_map_conj Y.isE64_A d)
    rw [← h2] at h1
    exact Subgroup.map_injective (MulAut.conj d).injective h1
  have hmax : ∀ R : Subgroup G, IsPGroup 2 R → Q ≤ R → R ≤ Cy → R = Q := by
    intro R hR2 hQR hRCy
    by_contra hne
    obtain ⟨g, hgR, hgQ, hgN⟩ := exists_mem_normalizer_not_mem hR2 hQR (Ne.symm hne)
    set R' := Subgroup.normalizer (Q : Set G) ⊓ R with hR'
    have hR'2 : IsPGroup 2 R' := hR2.to_le inf_le_right
    have hR'le : R' ≤ C ⊓ Cy := by
      rintro r ⟨hrN, hrR⟩
      have hrA : r ∈ Y.NA := by
        refine mem_normalizer_of_map_eq (hAuniq _ ?_ (isE64_map_conj Y.isE64_A r))
        rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hrN a).mp (hAQ ha)
      have hrCy : r ∈ Cy := hRCy hrR
      have hry : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.mp hrCy
      exact ⟨Y.centralizer_N_le_C hstd hL hyA hU hU0 hrA hry, hrCy⟩
    have hQR' : Q ≤ R' := fun q hq => ⟨Subgroup.le_normalizer hq, hQR hq⟩
    have := hQmax R' hR'2 hQR' hR'le
    exact hgQ (this ▸ ⟨hgN, hgR⟩)
  exact Y.centralizer_le_K_of_maximal hchar P hP hE hz hyA hy1 (hQle.trans inf_le_right)
    (hQle.trans inf_le_left) hQ2 hmax

omit hstd hL in
theorem centralizer_pi12_le_K (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hz : orderOf z = 2) : Subgroup.centralizer ({Y.π12} : Set G) ≤ Y.KK := by
  refine Y.centralizer_le_K_of_maximal hchar P hP hE hz Y.π12_mem_A Y.π12_ne_one (R := Y.T)
    (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (Y.commute_of_mem_T ht).2.1)
    Y.T_le_C (hP ▸ P.isPGroup') fun Q hQ2 hTQ _ => ?_
  rw [← hP] at hTQ ⊢
  exact P.is_maximal' hQ2 hTQ

include hc in
theorem centralizer_le_K (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3) (h12 : ¬ IsConj z Y.π12) {x : G}
    (hxA : x ∈ Y.A) (hx1 : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≤ Y.KK := by
  have hNK : Y.NA ≤ Y.KK := le_sup_left
  have hCK : Subgroup.centralizer ({z} : Set G) ≤ Y.KK := le_sup_right
  obtain ⟨x0, rfl⟩ := Y.exists_σA hxA
  have hx0 : x0 ≠ 0 := fun h => hx1 (by rw [h, Y.σA_zero])
  obtain ⟨-, -, hclasses⟩ := LS_facts' hc
  rcases hclasses x0 hx0 with h | h | h | h
  · obtain ⟨m, hm, hmz⟩ := (Y.mem_conj_z_iff hstd x0).mpr h
    rw [← hmz]
    exact Y.centralizer_conj_le (hNK hm) hCK
  · have hx : Y.σA x0 ∈ conjSet Y.NA Y.π3 := by
      rw [← Y.mem_coord, Y.coord_conj_pi3 hstd hchar P hP hz h3 h12]
      exact h
    obtain ⟨m, hm, hmx⟩ := hx
    rw [← hmx]
    exact Y.centralizer_conj_le (hNK hm) ((Y.centralizer_pi3_le hchar P hP hz h3 h12).trans hCK)
  · have hx : Y.σA x0 ∈ conjSet Y.NA Y.π12 := by
      rw [← Y.mem_coord, Y.coord_conj_pi12 hstd hc hL hchar P hP hz h3 h12]
      exact h
    obtain ⟨m, hm, hmx⟩ := hx
    rw [← hmx]
    exact Y.centralizer_conj_le (hNK hm) (Y.centralizer_pi12_le_K hchar P hP hE hz)
  ·
    obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp h
    have he0F := Finset.mem_filter.mp (he0 ▸ Finset.mem_singleton_self e0 :
      e0 ∈ (scOrb 0 ∪ scOrb 6).filter fun e => x0 + e ∈ LS c)
    obtain ⟨m, hm, hme⟩ := (Y.mem_conj_z_iff hstd e0).mpr he0F.1
    have hmi : m⁻¹ ∈ Y.NA := Y.NA.inv_mem hm
    set y := m⁻¹ * Y.σA x0 * m⁻¹⁻¹ with hy
    have hyA : y ∈ Y.A := Y.conj_mem_A hmi (Y.σA_mem_A x0)
    have hy1 : y ≠ 1 := by
      intro h1
      apply hx1
      have := congrArg (fun t => m * t * m⁻¹) h1
      simp only [hy] at this
      rw [show m * (m⁻¹ * Y.σA x0 * m⁻¹⁻¹) * m⁻¹ = Y.σA x0 by group] at this
      rw [this]
      group
    have hcy : Y.coordOf y = Y.cc m⁻¹ x0 := by
      apply Y.σA_injective
      rw [Y.σA_coordOf hyA, Y.σA_cc hmi]
    have hcm : ∀ w, Y.cc m (Y.cc m⁻¹ w) = w := fun w => by
      rw [← Y.cc_mul hm hmi, mul_inv_cancel, Y.cc_one]
    have hz0 : Y.cc m (sc [0, 1, 2]) = e0 := by
      apply Y.σA_injective
      rw [Y.σA_cc hm, sc012_eq, Y.σA_one_zero, hme]
    have hLS : ∀ w, w ∈ LS c ↔ Y.cc m w ∈ LS c := fun w =>
      ⟨fun hw => Y.cc_mem_LS hstd hL ⟨m, hm⟩ hw, fun hw => by
        have := Y.cc_mem_LS hstd hL ⟨m⁻¹, hmi⟩ hw
        rwa [show Y.cc (m⁻¹) (Y.cc m w) = w by rw [← Y.cc_mul hmi hm, inv_mul_cancel, Y.cc_one]]
          at this⟩
    have hU0 : Y.coordOf y + sc [0, 1, 2] ∈ LS c := by
      rw [hLS, Y.cc_add hm, hcy, hcm, hz0]
      exact he0F.2
    have hU : ∀ e ∈ scOrb 0 ∪ scOrb 6, Y.coordOf y + e ∈ LS c → e = sc [0, 1, 2] := by
      intro e he hye
      rw [hLS, Y.cc_add hm, hcy, hcm] at hye
      have h1 : Y.cc m e ∈ (scOrb 0 ∪ scOrb 6).filter fun e => x0 + e ∈ LS c :=
        Finset.mem_filter.mpr ⟨Y.cc_mem_Omega hstd hm he, hye⟩
      rw [he0, Finset.mem_singleton, ← hz0] at h1
      exact Y.cc_injective hm h1
    have hCy := Y.centralizer_le_K_of_point hstd hL hchar P hP hE hz hyA hy1 hU hU0
    have e : Y.σA x0 = m⁻¹⁻¹ * y * m⁻¹⁻¹⁻¹ := by rw [hy]; group
    rw [e]
    exact Y.centralizer_conj_le (Y.KK.inv_mem (hNK hmi)) hCy

end Classes2

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
