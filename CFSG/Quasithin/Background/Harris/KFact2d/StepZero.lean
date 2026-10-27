module

public import CFSG.Quasithin.Background.Harris.KFact2d.StarFacts
public import CFSG.Quasithin.Background.Harris.KFact2d.TwoElt
public import CFSG.Quasithin.Background.Harris.KFact2d.CaseI
public import CFSG.Quasithin.Background.Harris.KFact2d.CaseIIBasic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P B6 CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem mem_normalizer_of_mem_centralizer {X : Type} [Group X] {S : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.centralizer (S : Set X)) : x ∈ Subgroup.normalizer (S : Set X) := by
  have hc : ∀ z ∈ S, x * z * x⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hx z hz
    rw [← this]
    group
  have hc' : ∀ z ∈ S, x⁻¹ * z * x = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hx) z hz
    rw [← this]
    simp [mul_assoc]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun h => by rw [hc y h]; exact h, fun h => ?_⟩
  have := hc' _ h
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rw [e] at this
  exact this.symm ▸ h

variable {G : Type} [Group G] [Finite G]

theorem stepZero (hF1 : F1Stmt) {T N K K0 V : Subgroup G} (hmp : MinParabolic K T N)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (hc : CFSG.Quasithin.Gap6R2.E22Case2d K T N K0)
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVKs : E2.star N K V ≤ E2.star N K K0) : V ≤ pCoreOf 2 N := by
  obtain ⟨hTn, hker⟩ := case2d_facts hc
  obtain ⟨p, hX⟩ := exists_case2dStar hmp hK0 hKK0 hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : T ≤ K := hmp.isSylow.1
  have hNK : N ≤ K := hmp.maximal.1.le
  have hK0K : K0 ≤ K := le_of_mem_cComp hK0
  have hJN : kerIn N K ≤ N := kerIn_le
  have hJK : kerIn N K ≤ K := hJN.trans hNK
  have hQK : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hQleK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hDK : K0 ⊔ pCoreOf 2 K ≤ K := D_le_K hK0
  have hQJ : pCoreOf 2 K ≤ kerIn N K := Q_le_J hK0 hker
  have hodd := odd_of_J hker hJK
  have hJD : kerIn N K ≤ K0 ⊔ pCoreOf 2 K := fun x hx => ((hker x).mp hx).1
  have hTs : E2.star N K T ≤ E2.star N K N := star_mono hmp.le
  set S : Subgroup (E2.StarQuot N K) := E2.star N K T ⊓ E2.star N K K0 with hSdef
  have hSyl : IsSylowTwoOf S (E2.star N K K0) := isSylowTwoOf_star_inf hmp hK0
  have hL : IsL3U3 p ↥(E2.star N K K0) := hX.2.2.2.1.imp id fun h => ⟨h.1, h.2.1⟩
  have hVS : E2.star N K V ≤ S := le_inf (star_mono hVT) hVKs
  have hSn : S ≤ Subgroup.normalizer (E2.star N K V : Set (E2.StarQuot N K)) :=
    inf_le_left.trans (Ch3E213M.OS.star_le_normalizer hTV)
  have hZ : E2.star N K V ≤ zOf S :=
    hF1 (E2.StarQuot N K) (E2.star N K K0) S p hX.2.1 hX.2.2.1 hL hSyl (E2.star N K V)
      (isElemAbelian_star hV) hVS hSn
  have hzS : zOf S ≤ S := inf_le_left
  have hSKs : S ≤ E2.star N K K0 := inf_le_right
  set Y0 : Subgroup G := pre N K (zOf S) with hY0
  have hstarN : pre N K (E2.star N K N) = N := pre_star hNK hJN
  have hstarD : E2.star N K (K0 ⊔ pCoreOf 2 K) = E2.star N K K0 := star_sup_pCore hQJ hK0K hQK
  have hY0N : Y0 ≤ N := by
    have := pre_mono (hzS.trans (inf_le_left.trans hTs))
    rwa [hstarN] at this
  have hnormN : ∀ n ∈ N, ∀ hnK : n ∈ K,
      starMap N K ⟨n, hnK⟩ ∈ Subgroup.normalizer (zOf S : Set (E2.StarQuot N K)) := by
    intro n hn hnK
    have hKT : (↑(K0 ⊔ T) : Set G) = K0 * T := Subgroup.coe_mul_of_right_le_normalizer_left K0 T hTn
    have hn' : n ∈ (↑(K0 ⊔ T) : Set G) := hKK0 ▸ hnK
    rw [hKT] at hn'
    obtain ⟨k0, hk0, t, ht, hkt⟩ := hn'
    have hk0K : k0 ∈ K := hK0K hk0
    have htK : t ∈ K := hTK ht
    have hk0N : k0 ∈ N := by
      have : k0 = n * t⁻¹ := by rw [← hkt]; group
      rw [this]
      exact N.mul_mem hn (N.inv_mem (hmp.le ht))
    have hnew : (⟨n, hnK⟩ : ↥K) = ⟨k0, hk0K⟩ * ⟨t, htK⟩ := Subtype.ext hkt.symm
    rw [hnew, map_mul]
    refine Subgroup.mul_mem _ ?_ ?_
    · have hmem : starMap N K ⟨k0, hk0K⟩ ∈ E2.star N K (N ⊓ K0) :=
        ⟨⟨k0, hk0K⟩, Subgroup.mem_subgroupOf.mpr ⟨hk0N, hk0⟩, rfl⟩
      rw [star_inf_M K0] at hmem
      have hmem' : starMap N K ⟨k0, hk0K⟩ ∈ E2.star N K N ⊓ E2.star N K K0 := hmem
      rw [hX.2.2.2.2] at hmem'
      exact mem_normalizer_of_mem_centralizer hmem'.2
    · have htT : starMap N K ⟨t, htK⟩ ∈ E2.star N K T :=
        ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      apply normalizer_le_normalizer_zOf
      have hKn : (E2.star N K K0).Normal := hX.1.normal
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have key : ∀ x ∈ E2.star N K T, ∀ y ∈ S, x * y * x⁻¹ ∈ S := fun x hx y hy =>
        ⟨(E2.star N K T).mul_mem ((E2.star N K T).mul_mem hx hy.1) ((E2.star N K T).inv_mem hx),
          hKn.conj_mem y hy.2 x⟩
      refine ⟨fun h => key _ htT y h, fun h => ?_⟩
      have := key _ ((E2.star N K T).inv_mem htT) _ h
      simpa [mul_assoc] using this
  have hY0n : N ≤ Subgroup.normalizer (Y0 : Set G) := by
    have key : ∀ n ∈ N, ∀ y ∈ Y0, n * y * n⁻¹ ∈ Y0 := by
      intro n hn y hy
      obtain ⟨hyK, hyZ⟩ := mem_pre.mp hy
      have hnK : n ∈ K := hNK hn
      refine mem_pre.mpr ⟨K.mul_mem (K.mul_mem hnK hyK) (K.inv_mem hnK), ?_⟩
      have h1 := Subgroup.mem_normalizer_iff.mp (hnormN n hn hnK) (starMap N K ⟨y, hyK⟩)
      have : starMap N K ⟨n * y * n⁻¹, K.mul_mem (K.mul_mem hnK hyK) (K.inv_mem hnK)⟩ =
          starMap N K ⟨n, hnK⟩ * starMap N K ⟨y, hyK⟩ * (starMap N K ⟨n, hnK⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact h1.mp hyZ
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
    have := key n⁻¹ (N.inv_mem hn) _ hx
    simpa [mul_assoc] using this
  have hab : ∀ a ∈ Y0, ∀ b ∈ Y0, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K := by
    intro a ha b hb
    obtain ⟨haK, haZ⟩ := mem_pre.mp ha
    obtain ⟨hbK, hbZ⟩ := mem_pre.mp hb
    have hmemD : ∀ x (hxK : x ∈ K), starMap N K ⟨x, hxK⟩ ∈ zOf S → x ∈ K0 ⊔ pCoreOf 2 K := by
      intro x hxK hx
      have : x ∈ pre N K (E2.star N K (K0 ⊔ pCoreOf 2 K)) := by
        refine mem_pre.mpr ⟨hxK, ?_⟩
        rw [hstarD]
        exact hSKs (hzS hx)
      rwa [pre_star hDK hJD] at this
    have haD := hmemD a haK haZ
    have hbD := hmemD b hbK hbZ
    have habK : a * b * a⁻¹ * b⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem haK hbK) (K.inv_mem haK)) (K.inv_mem hbK)
    have hcJ : a * b * a⁻¹ * b⁻¹ ∈ kerIn N K := by
      have h1 : starMap N K ⟨a * b * a⁻¹ * b⁻¹, habK⟩ = 1 := by
        have e : (⟨a * b * a⁻¹ * b⁻¹, habK⟩ : ↥K) = ⁅(⟨a, haK⟩ : ↥K), ⟨b, hbK⟩⁆ := rfl
        rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp haZ.2 _ hbZ.1).symm
      have : (⟨a * b * a⁻¹ * b⁻¹, habK⟩ : ↥K) ∈ (starMap N K).ker := h1
      rw [ker_starMap] at this
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨m, hm⟩ := hSyl.2.1 ⟨_, haZ.1⟩
    have hm' : (starMap N K ⟨a, haK⟩) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hmJ : a ^ 2 ^ m ∈ kerIn N K := by
      have h1 : starMap N K ⟨a ^ 2 ^ m, K.pow_mem haK _⟩ = 1 := by
        have : (⟨a ^ 2 ^ m, K.pow_mem haK _⟩ : ↥K) = ⟨a, haK⟩ ^ 2 ^ m := rfl
        rw [this, map_pow]
        exact hm'
      have : (⟨a ^ 2 ^ m, K.pow_mem haK _⟩ : ↥K) ∈ (starMap N K).ker := h1
      rw [ker_starMap] at this
      exact Subgroup.mem_subgroupOf.mp this
    exact comm_mem_of_two_part (hDK.trans hQK) hJD (fun x hx y hy => ((hker x).mp hx).2 y hy)
      hodd haD hbD hcJ m hmJ
  have hVY : V ≤ Y0 := fun v hv => by
    have hvK : v ∈ K := hTK (hVT hv)
    exact mem_pre.mpr ⟨hvK, hZ ⟨⟨v, hvK⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩⟩
  exact le_pCoreOf_of_abelian_mod (pCoreOf_isPGroup 2 K) (hNK.trans hQK) hY0N hY0n hab hVY
    (hmp.isSylow.2.1.to_le hVT)

end CFSG.Quasithin.Background.Harris.KFact2d
