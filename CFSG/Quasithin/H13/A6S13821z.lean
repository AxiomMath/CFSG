module

public import CFSG.Quasithin.H13.A6S13821y
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Rk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType
public import CFSG.Quasithin.EmptyFaithful.S14620A
public import CFSG.Quasithin.H13.A6S13816b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6S20

theorem bor_of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : QA21.SolvableOvergroupsNormalize X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  intro A hUA hA
  by_cases hAt : A = ⊤
  · subst hAt
    have hX : Group.IsSolvable X :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype) fun x => ⟨⟨x, trivial⟩, rfl⟩
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hX
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [hcomm g u, mul_inv_cancel_right]
  · have hidx : ¬ 2 ∣ U.index := by
      have h2 : ¬ 2 ∣ U.relIndex ⊤ := hU.2.2
      rwa [Subgroup.relIndex_top_right] at h2
    exact Bridge.Over.le_normalizer_of_bender hB (hU.2.1.toSylow hidx) (M := A) hUA hAt

theorem bor_of_lieF2n
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n X ∨ IsPSL 3 2 n X ∨ IsPSU 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : QA21.SolvableOvergroupsNormalize X U := by
  rcases h with h | h | h | h | h
  · exact bor_of_bender (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL h) hU
  · exact QA21.solvableOvergroupsNormalize_of_isPSL3 hn h hU
  · exact bor_of_bender (GoldMLA.fusionIsBenderGroup_of_isPSU3 hn h) hU
  · exact QA21.solvableOvergroupsNormalize_of_isPSp4 hn h hU
  · obtain ⟨P, hP⟩ := QA21.borelPkg_g2 h hU
    exact hP.solv

theorem isSylowTwoOf_map_top {A B : Type} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) {U : Subgroup A} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map f) ⊤ := by
  refine ⟨le_top, hU.2.1.map f, ?_⟩
  have h1 : ¬ 2 ∣ U.index := by
    have h2 : ¬ 2 ∣ U.relIndex ⊤ := hU.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  show ¬ 2 ∣ (U.map f).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact fun h => h1 (h.trans (Subgroup.index_map_dvd U hf))

theorem bor_of_quot
    {X : Type} [Group X] [Finite X] (hO2 : CFSG.pCore 2 X = ⊥) {n : ℕ}
    (hn : 2 ≤ n) (h : LieF2n X n) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    QA21.SolvableOvergroupsNormalize X U :=
  QA23.solvableOvergroupsNormalize_of_quotient_center hO2 hU.2.1
    (bor_of_lieF2n hn h (isSylowTwoOf_map_top (QuotientGroup.mk'_surjective _) hU))

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem isSylowTwoOf_TK {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) : IsSylowTwoOf (T ⊓ K) K := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  exact A4.isSylowTwoOf_inf_normal hTsylH hKH hKn

theorem pCoreOf_le_TK {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ T ⊓ K :=
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf (S.isSylowTwoOf_TK hH hKH hKn)

theorem le_normalizer_TK
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n) {Y : Subgroup G} (hYK : Y ≤ K) (hTY : T ⊓ K ≤ Y)
    (hY : Group.IsSolvable ↥Y) : Y ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  have hU : IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := by
    refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm, ?_⟩
    show ¬ 2 ∣ ((T ⊓ K).subgroupOf K).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hsyl.2.2
  have hBOR := A6S20.bor_of_quot (pCore_two_quotient_pCore_two ↥K) hn hLie
    (A6S20.isSylowTwoOf_map_top (f := π) (QuotientGroup.mk'_surjective _) hU)
  have hYs : Group.IsSolvable ↥((Y.subgroupOf K).map π) := by
    have : Group.IsSolvable ↥(Y.subgroupOf K) := by
      have e := (Subgroup.subgroupOfEquivOfLe hYK).symm
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (Y.subgroupOf K))
      (MonoidHom.subgroupMap_surjective _ _)
  have hle := hBOR _ (Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hTY (Subgroup.mem_subgroupOf.mp hx))) hYs
  have hO2 : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K → (k : G) ∈ T ⊓ K := fun k hk => by
    have hk' : k ∈ (pCoreOf 2 K).subgroupOf K := by rw [pCoreOf_subgroupOf_eq]; exact hk
    exact S.pCoreOf_le_TK hH hKH hKn (Subgroup.mem_subgroupOf.mp hk')
  have hpre : ∀ k : ↥K, π k ∈ ((T ⊓ K).subgroupOf K).map π → (k : G) ∈ T ⊓ K := by
    rintro k ⟨s, hs, hsk⟩
    have h1 : s⁻¹ * k ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hsk, inv_mul_cancel]
    have h2 := hO2 _ h1
    have e : (k : G) = (s : G) * ((s⁻¹ * k : ↥K) : G) := by simp
    rw [e]
    exact (T ⊓ K).mul_mem (Subgroup.mem_subgroupOf.mp hs) h2
  have key : ∀ y ∈ Y, ∀ x ∈ T ⊓ K, y * x * y⁻¹ ∈ T ⊓ K := by
    intro y hy x hx
    have hyK : y ∈ K := hYK hy
    have hxK : x ∈ K := hx.2
    have hmem := (Subgroup.mem_normalizer_iff.mp (hle ⟨⟨y, hyK⟩,
      Subgroup.mem_subgroupOf.mpr hy, rfl⟩) (π ⟨x, hxK⟩)).mp
      ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have e : π ⟨y, hyK⟩ * π ⟨x, hxK⟩ * (π ⟨y, hyK⟩)⁻¹ =
        π ⟨y * x * y⁻¹, K.mul_mem (K.mul_mem hyK hxK) (K.inv_mem hyK)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at hmem
    exact hpre _ hmem
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key y hy x hx, fun hx => ?_⟩
  have := key y⁻¹ (Y.inv_mem hy) _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

theorem L1T_le_normalizer_TK
    (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    {n : ℕ} (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n) :
    S.L1 ⊔ T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  set Z := conjClosure (T ⊓ K) (S.L1 ⊔ T) with hZ
  have hZK : Z ≤ K := conjClosure_le fun l hl z hz =>
    (Subgroup.mem_normalizer_iff.mp (hKn (hLTH hl)) z).mp hz.2
  have hZLT : Z ≤ S.L1 ⊔ T := conjClosure_le fun l hl z hz =>
    (S.L1 ⊔ T).mul_mem ((S.L1 ⊔ T).mul_mem hl (Subgroup.mem_sup_right hz.1))
      ((S.L1 ⊔ T).inv_mem hl)
  have hsolv : Group.IsSolvable ↥Z := by
    have := S.isSolvable_L1T h1334 hS
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hZLT)
      (Subgroup.inclusion_injective hZLT)
  have hTZ : T ⊓ K ≤ Z := le_conjClosure _ _
  have hZN := S.le_normalizer_TK hH hKH hKn hn hLie hZK hTZ hsolv
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  have h2 : ∀ z ∈ Z, ∀ k : ℕ, z ^ 2 ^ k = 1 → z ∈ T ⊓ K := by
    intro z hz k hk
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) := by
      rintro ⟨g, hg⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hP : IsPGroup 2 ↥((T ⊓ K) ⊔ Subgroup.zpowers z) :=
      IsPGroup.to_sup_of_normal_left' hsyl.2.1 hzp (by
        rw [Subgroup.zpowers_le]
        exact hZN hz)
    have hle : (T ⊓ K) ⊔ Subgroup.zpowers z ≤ K :=
      sup_le inf_le_right (by rw [Subgroup.zpowers_le]; exact hZK hz)
    have heq := hsyl.eq_of_le le_sup_left hle hP
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hconj : ∀ g ∈ S.L1 ⊔ T, ∀ y ∈ T ⊓ K, g * y * g⁻¹ ∈ T ⊓ K := by
    intro g hg y hy
    obtain ⟨k, hk⟩ := hsyl.2.1 ⟨y, hy⟩
    refine h2 _ (mem_conjClosure hg hy) k ?_
    have hy2 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow, hy2, mul_one, mul_inv_cancel]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj l hl x hx, fun hx => ?_⟩
  have := hconj l⁻¹ ((S.L1 ⊔ T).inv_mem hl) _ hx
  rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this

theorem borel_le_M
    (h13 : Lem13813) (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    {n : ℕ} (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hN := S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLie
  have hB : Group.IsSolvable ↥(K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :=
    isSolvable_inf_normalizer_of_isSylowTwoOf (S.isSylowTwoOf_TK hH hKH hKn)
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  have hNB : S.L1 ⊔ T ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    intro l hl
    have hlK : l ∈ Subgroup.normalizer (K : Set G) := hKn (hLTH hl)
    have hlN : l ∈ Subgroup.normalizer
        ((Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (hN hl)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => ⟨(Subgroup.mem_normalizer_iff.mp hlK y).mp hy.1,
        (Subgroup.mem_normalizer_iff.mp hlN y).mp hy.2⟩,
      fun hy => ⟨(Subgroup.mem_normalizer_iff.mp hlK y).mpr hy.1,
        (Subgroup.mem_normalizer_iff.mp hlN y).mpr hy.2⟩⟩
  have hX := isSolvable_sup_of_le_normalizer_of_isSolvable hNB hB (S.isSolvable_L1T h1334 hS)
  have hXG : (K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) ⊔ (S.L1 ⊔ T) ≤ S.G1 :=
    sup_le ((inf_le_left.trans hKH).trans hH.2.1) (hLTH.trans hH.2.1)
  exact le_sup_left.trans (h13 G T L V S hS _ le_sup_right hXG hX)

end Setting4

end CFSG.Quasithin.H13.A6
