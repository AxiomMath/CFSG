module

public import CFSG.Quasithin.Vol2.Ch11SecD551A
public import CFSG.Quasithin.Vol2.Ch11SecDO22

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_mem_centralizer {V : Subgroup G} {t k : G}
    (ht : t ∈ Subgroup.centralizer (V : Set G)) (hk : k ∈ Subgroup.normalizer (V : Set G)) :
    t * k * t⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : k * t⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (SecA.mem_normalizer_centralizer hk) _).mp
      (Subgroup.inv_mem _ ht)
  simpa [mul_assoc] using Subgroup.mul_mem _ ht h1

omit [Finite G] in
theorem mk_mem_center {K V : Subgroup G} (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (V : Set G)) {c : ↥K}
    (hc : (c : G) ∈ Subgroup.centralizer (V : Set G)) :
    (QuotientGroup.mk c : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  set N := (Subgroup.centralizer (V : Set G)).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (SecA.mem_normalizer_centralizer (hKV g.2)) _).mp hx
  have hMn : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hMn with htop | hle
  · refine (hne fun k hk => ?_).elim
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := htop ▸ Subgroup.mem_top _
    obtain ⟨c', hc', he⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    have h1 : ((c'⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [← SecD.pCoreOf_subgroupOf] at he
      exact he
    have h2 : k = (c' : G) * ((c'⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hc') (hO h1)
  · exact hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc))

omit [Finite G] in
theorem comm_mem_pCoreOf {K V : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (V : Set G)) {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htV : t ∈ Subgroup.centralizer (V : Set G))
    {k : G} (hk : k ∈ K) : t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hcK : ∀ x : ↥K, t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ K := fun x =>
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp htK _).mp x.2) (K.inv_mem x.2)
  let c : ↥K → ↥K := fun x => ⟨t * x * t⁻¹ * (x : G)⁻¹, hcK x⟩
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hcZ : ∀ x, π (c x) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := fun x =>
    mk_mem_center hq hKV hO hne (comm_mem_centralizer htV (hKV x.2))
  have hc1 : c 1 = 1 := Subtype.ext (by show t * (1 : G) * t⁻¹ * (1 : G)⁻¹ = 1; group)
  have hcm : ∀ x y : ↥K, c (x * y) = c x * (x * c y * x⁻¹) := fun x y => Subtype.ext (by
    show t * ((x : G) * y) * t⁻¹ * ((x : G) * y)⁻¹ =
      t * x * t⁻¹ * (x : G)⁻¹ * ((x : G) * (t * y * t⁻¹ * (y : G)⁻¹) * (x : G)⁻¹)
    group)
  let f : ↥K →* ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    { toFun := fun x => ⟨π (c x), hcZ x⟩
      map_one' := Subtype.ext (by show π (c 1) = 1; rw [hc1, map_one])
      map_mul' := fun x y => Subtype.ext (by
        show π (c (x * y)) = π (c x) * π (c y)
        rw [hcm, map_mul, map_mul, map_mul, map_inv,
          Subgroup.mem_center_iff.mp (hcZ y) (π x), mul_inv_cancel_right]) }
  have hk' : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by
    have : k ∈ (commutator ↥K).map K.subtype := by
      rw [Subgroup.map_subtype_commutator, hK]
      exact hk
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp this
    have : x = ⟨k, hk⟩ := Subtype.ext hxk
    rwa [← this]
  have h1 : f ⟨k, hk⟩ = 1 := Abelianization.commutator_subset_ker f hk'
  have h2 : π (c ⟨k, hk⟩) = 1 := congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← SecD.pCoreOf_subgroupOf] at h2
  exact h2

theorem inf_sectionCentralizer_le_pCoreOf {K T : Subgroup G}
    (hT : QuasithinUnique.IsSylowTwoOf T (K ⊔ T)) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ⊓ sectionCentralizer K (pCoreOf 2 K) ≤ pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 K with hO
  set C := T ⊓ sectionCentralizer K O with hC
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hOT : O ≤ T := by
    have hO' : O ≤ pCoreOf 2 (K ⊔ T) :=
      SecD.le_ROf' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hTO)
    exact hO'.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hTO
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun t ht =>
    SecD.mem_normalizer_inf (Subgroup.le_normalizer ht)
      (SecD.mem_normalizer_sectionCentralizer (hTK ht) (hTO ht))
  have hKN : K ≤ Subgroup.normalizer ((O ⊔ C : Subgroup G) : Set G) := by
    intro l hl
    refine SecD.mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
    all_goals
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O C hCO] at hx
      obtain ⟨o, ho, c, hc, rfl⟩ := hx
    · have hlo := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hl) o).mp ho
      have hlc : l * c * l⁻¹ * c⁻¹ ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hl) _).mp
          (hc.2.2.2 l⁻¹ (K.inv_mem hl))
        convert this using 1
        group
      have : l * (o * c) * l⁻¹ = (l * o * l⁻¹) * (l * c * l⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (O ⊔ C).mul_mem ((O ⊔ C).mul_mem (Subgroup.mem_sup_left hlo)
        (Subgroup.mem_sup_left hlc)) (Subgroup.mem_sup_right hc)
    · have hl' := K.inv_mem hl
      have hlo := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hl') o).mp ho
      have hlc : l⁻¹ * c * l⁻¹⁻¹ * c⁻¹ ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hl') _).mp
          (hc.2.2.2 l⁻¹⁻¹ (K.inv_mem hl'))
        convert this using 1
        group
      have : l⁻¹ * (o * c) * l = (l⁻¹ * o * l⁻¹⁻¹) * (l⁻¹ * c * l⁻¹⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (O ⊔ C).mul_mem ((O ⊔ C).mul_mem (Subgroup.mem_sup_left hlo)
        (Subgroup.mem_sup_left hlc)) (Subgroup.mem_sup_right hc)
  have hOCT : O ⊔ C ≤ T := sup_le hOT inf_le_left
  have hOC := SecD.le_ROf' (hT.2.1.to_le hOCT) (hOCT.trans le_sup_right)
    (sup_le hKN (A1a.le_normalizer_sup hTO hTC))
  exact le_sup_right.trans hOC

theorem inf_centralizer_le_pCoreOf_of_quasisimple {K T V : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hT : QuasithinUnique.IsSylowTwoOf T (K ⊔ T)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  refine inf_sectionCentralizer_le_pCoreOf hT hTK ⟨ht.1, hTK ht.1,
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hTK ht.1), fun k hk => ?_⟩
  exact comm_mem_pCoreOf hK hq hKV hO hne (hTK ht.1) ht.2 hk

end CFSG.Quasithin.Vol2.Ch11.O10
