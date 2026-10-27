module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShape
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.UC1K31

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

abbrev Xhat : Type := ↥t.Xz ⧸ CFSG.pPrimeCore 3 ↥t.Xz

@[expose] noncomputable def Zhat : Subgroup t.Xhat :=
  (t.Z.subgroupOf t.Xz).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))

private theorem card_Z_subgroupOf : Nat.card (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe t.Z_le_Xz).toEquiv, t.card_Z]

private theorem inf_pPrimeCore_eq_bot :
    (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) ⊓ CFSG.pPrimeCore 3 ↥t.Xz = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card ↥((t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) ⊓
      CFSG.pPrimeCore 3 ↥t.Xz)) 3 :=
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card).symm
  have hdvd : Nat.card ↥((t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) ⊓
      CFSG.pPrimeCore 3 ↥t.Xz) ∣ 3 := by
    rw [← t.card_Z_subgroupOf]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem card_Zhat : Nat.card t.Zhat = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card t.Zhat ∣ 3 := by
    have h := Subgroup.card_map_dvd (t.Z.subgroupOf t.Xz)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))
    rwa [t.card_Z_subgroupOf] at h
  rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card t.Zhat) hdvd with h | h
  · exfalso
    have hbot : t.Zhat = ⊥ := Subgroup.card_eq_one.mp h
    have hle : t.Z.subgroupOf t.Xz ≤ CFSG.pPrimeCore 3 ↥t.Xz := by
      have hmap : Subgroup.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))
          (t.Z.subgroupOf t.Xz) = ⊥ := hbot
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
      exact hmap
    have h1 : Nat.card (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) = 1 := by
      have hle' : t.Z.subgroupOf t.Xz ≤ ⊥ := by
        have h2 : t.Z.subgroupOf t.Xz ≤
            (t.Z.subgroupOf t.Xz ⊓ CFSG.pPrimeCore 3 ↥t.Xz) := le_inf le_rfl hle
        rwa [t.inf_pPrimeCore_eq_bot] at h2
      exact Subgroup.card_eq_one.mpr (le_bot_iff.mp hle')
    rw [t.card_Z_subgroupOf] at h1
    norm_num at h1
  · exact h

private theorem Dz_le_Xz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) : t.Dz ≤ t.Xz :=
  t.Dz_le_Ky.trans (t.Ky_le_Xz hK32 hGA hSp)

theorem isCyclic_Dz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : IsCyclic ↥t.Dz := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) (t.d.hS.isPGroup.to_le inf_le_left) ?_
  calc CFSG.Open.pRank 3 t.Dz ≤ CFSG.Open.pRank 3 t.Xz :=
        CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (t.Dz_le_Xz hK32 hGA hSp)
    _ = 1 := t.pRank_Xz hK332 hOut hp hN hZ

private theorem isSylowOf_Dz_subgroupOf_top
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (t.Dz.subgroupOf t.Xz) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : CFSG.ABGLocalTools.IsSylowOf 3 t.Dz t.Xz :=
    t.isSylowOf_Dz_Xz hK32 hGA hSp hK332 hOut hp hN hZ
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff t.Xz,
    Subgroup.map_subgroupOf_eq_of_le hD.le, Subgroup.map_top, Subgroup.range_subtype]
  exact hD

theorem exists_mem_Xz_map_conj_eq_Z (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {W : Subgroup G} (hWX : W ≤ t.Xz)
    (hW : Nat.card W = 3) : ∃ x ∈ t.Xz, W.map (MulAut.conj x).toMonoidHom = t.Z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf 3 (t.Dz.subgroupOf t.Xz) ⊤ :=
    t.isSylowOf_Dz_subgroupOf_top hK32 hGA hSp hK332 hOut hp hN hZ
  have hDcyc : IsCyclic ↥(t.Dz.subgroupOf t.Xz) :=
    (Subgroup.subgroupOfEquivOfLe (t.Dz_le_Xz hK32 hGA hSp)).isCyclic.mpr
      (t.isCyclic_Dz hK32 hGA hSp hK332 hOut hp hN hZ)
  have hZ'le : t.Z.subgroupOf t.Xz ≤ t.Dz.subgroupOf t.Xz := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (t.Z_le_Dz (Subgroup.mem_subgroupOf.mp hz))
  have hZ'card : Nat.card (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) = 3 := t.card_Z_subgroupOf
  have hW'card : Nat.card (W.subgroupOf t.Xz : Subgroup ↥t.Xz) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv, hW]
  have hW'p : IsPGroup 3 ↥(W.subgroupOf t.Xz) :=
    IsPGroup.of_card (n := 1) (by rw [hW'card]; norm_num)
  obtain ⟨Q, hWQ⟩ := hW'p.exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup ↥t.Xz) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hDsyl.exists_mem_conj hQsyl
  have hle : (W.subgroupOf t.Xz).map (MulAut.conj k⁻¹).toMonoidHom ≤
      t.Dz.subgroupOf t.Xz := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem := (hk w).mp (hWQ hw)
    simpa [MulAut.conj_apply] using hmem
  have hcard : Nat.card ((W.subgroupOf t.Xz).map (MulAut.conj k⁻¹).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hW'card]
  have hsub : ((W.subgroupOf t.Xz).map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
        (t.Dz.subgroupOf t.Xz) = (t.Z.subgroupOf t.Xz).subgroupOf (t.Dz.subgroupOf t.Xz) := by
    haveI : IsCyclic ↥(t.Dz.subgroupOf t.Xz) := hDcyc
    refine (IsCyclic.subgroup_eq_iff_card_eq (G := ↥(t.Dz.subgroupOf t.Xz))).mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'le).toEquiv, hZ'card]
  have hWeq : (W.subgroupOf t.Xz).map (MulAut.conj k⁻¹).toMonoidHom =
      t.Z.subgroupOf t.Xz := by
    have h1 := congrArg (Subgroup.map (t.Dz.subgroupOf t.Xz).subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le hZ'le] at h1
  have hmapW : (W.subgroupOf t.Xz).map t.Xz.subtype = W :=
    Subgroup.map_subgroupOf_eq_of_le hWX
  have hmapZ : (t.Z.subgroupOf t.Xz).map t.Xz.subtype = t.Z :=
    Subgroup.map_subgroupOf_eq_of_le t.Z_le_Xz
  have hcomp : (MulAut.conj ((k : G)⁻¹)).toMonoidHom.comp t.Xz.subtype =
      t.Xz.subtype.comp (MulAut.conj (k⁻¹)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  refine ⟨(k : G)⁻¹, t.Xz.inv_mem k.2, ?_⟩
  rw [← hmapW, Subgroup.map_map, hcomp, ← Subgroup.map_map, hWeq, hmapZ]

theorem normalClosure_Z_subgroupOf_Xz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.normalClosure ((t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) : Set ↥t.Xz) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
  let N : Subgroup ↥t.Xz := Subgroup.normalClosure (t.Z.subgroupOf t.Xz : Set ↥t.Xz)
  let N₀ : Subgroup G := N.map t.Xz.subtype
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hZle : t.Z ≤ N₀ := by
    have h1 : (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz).map t.Xz.subtype ≤ N₀ :=
      Subgroup.map_mono Subgroup.le_normalClosure
    rwa [Subgroup.map_subgroupOf_eq_of_le t.Z_le_Xz] at h1
  have hN₀conj : ∀ x ∈ t.Xz, ∀ n ∈ N₀, x * n * x⁻¹ ∈ N₀ := by
    intro x hx n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    exact Subgroup.mem_map_of_mem t.Xz.subtype (hNnorm.conj_mem m hm ⟨x, hx⟩)
  have hXeq : t.Xz = (Subgroup.normalClosure (t.Z.subgroupOf K : Set ↥K)).map K.subtype := rfl
  have hXle : t.Xz ≤ N₀ := by
    intro g hg
    have hg' : g ∈ (Subgroup.normalClosure (t.Z.subgroupOf K : Set ↥K)).map K.subtype := by
      rwa [hXeq] at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg'
    change k ∈ Subgroup.closure (Group.conjugatesOfSet (t.Z.subgroupOf K : Set ↥K)) at hk
    refine Subgroup.closure_induction (G := ↥K) (p := fun w _ => (w : G) ∈ N₀) ?_ ?_ ?_ ?_ hk
    · intro w hw
      obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hw
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hzZ : (z : G) ∈ t.Z := Subgroup.mem_subgroupOf.mp hz
      have hWX : t.Z.map (MulAut.conj (u : G)).toMonoidHom ≤ t.Xz := by
        have hkX : (u : G) ∈ Subgroup.normalizer (t.Xz : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer t.Xz_le_centralizer).mp
            t.normal_Xz u.2
        intro y hy
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
        exact (Subgroup.mem_normalizer_iff.mp hkX c).mp (t.Z_le_Xz hc)
      have hWcard : Nat.card (t.Z.map (MulAut.conj (u : G)).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective, t.card_Z]
      obtain ⟨x, hxX, hxW⟩ :=
        t.exists_mem_Xz_map_conj_eq_Z hK32 hGA hSp hK332 hOut hp hN hZ hWX hWcard
      have hwW : (w : G) ∈ t.Z.map (MulAut.conj (u : G)).toMonoidHom := by
        rw [← hu]
        exact Subgroup.mem_map_of_mem _ hzZ
      have hxz : x * (w : G) * x⁻¹ ∈ t.Z := by
        have hmem : x * (w : G) * x⁻¹ ∈
            (t.Z.map (MulAut.conj (u : G)).toMonoidHom).map
              (MulAut.conj x).toMonoidHom := Subgroup.mem_map_of_mem _ hwW
        rwa [hxW] at hmem
      have h1 : x⁻¹ * (x * (w : G) * x⁻¹) * x ∈ N₀ := by
        simpa using hN₀conj x⁻¹ (t.Xz.inv_mem hxX) _ (hZle hxz)
      have h2 : x⁻¹ * (x * (w : G) * x⁻¹) * x = (w : G) := by group
      rwa [h2] at h1
    · exact N₀.one_mem
    · intro a b _ _ ha hb
      exact N₀.mul_mem ha hb
    · intro a _ ha
      exact N₀.inv_mem ha
  have hN₀le : N₀ ≤ t.Xz := Subgroup.map_subtype_le N
  have hNeq : N = ⊤ := by
    apply Subgroup.map_injective t.Xz.subtype_injective
    show N.map t.Xz.subtype = (⊤ : Subgroup ↥t.Xz).map t.Xz.subtype
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact le_antisymm hN₀le hXle
  exact hNeq

private noncomputable def Dhat : Subgroup t.Xhat :=
  (t.Dz.subgroupOf t.Xz).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))

private theorem isSylowOf_Dhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.Dhat ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf 3 (t.Dz.subgroupOf t.Xz) ⊤ :=
    t.isSylowOf_Dz_subgroupOf_top hK32 hGA hSp hK332 hOut hp hN hZ
  have hD'p : IsPGroup 3 ↥(t.Dz.subgroupOf t.Xz) := hDsyl.isPGroup
  have hD'nd : ¬ 3 ∣ (t.Dz.subgroupOf t.Xz).index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hDsyl).2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨QD, hQD⟩ : ∃ QD : Sylow 3 ↥t.Xz, (QD : Subgroup ↥t.Xz) = t.Dz.subgroupOf t.Xz :=
    ⟨hD'p.toSylow hD'nd, IsPGroup.toSylow_coe hD'p hD'nd⟩
  obtain ⟨QDhat, hQDhat⟩ : ∃ QDhat : Sylow 3 t.Xhat,
      (QDhat : Subgroup t.Xhat) = t.Dhat := by
    refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective _) QD, ?_⟩
    rw [Sylow.coe_mapSurjective, hQD]
    rfl
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right, ← hQDhat]
  exact ⟨le_top, QDhat.isPGroup', QDhat.not_dvd_index⟩

private theorem isCyclic_Dhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : IsCyclic ↥t.Dhat := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥(t.Dz.subgroupOf t.Xz) :=
    (Subgroup.subgroupOfEquivOfLe (t.Dz_le_Xz hK32 hGA hSp)).isCyclic.mpr
      (t.isCyclic_Dz hK32 hGA hSp hK332 hOut hp hN hZ)
  let f : ↥(t.Dz.subgroupOf t.Xz) →* ↥t.Dhat :=
    { toFun := fun x =>
        ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz) (x : ↥t.Xz),
          Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by simp
      map_mul' := by intro a b; simp }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact isCyclic_of_surjective f hf

private theorem Zhat_le_Dhat : t.Zhat ≤ t.Dhat :=
  Subgroup.map_mono fun _ hz =>
    Subgroup.mem_subgroupOf.mpr (t.Z_le_Dz (Subgroup.mem_subgroupOf.mp hz))

private theorem exists_conj_map_eq_Zhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {W : Subgroup t.Xhat}
    (hW : Nat.card W = 3) : ∃ k : t.Xhat, W.map (MulAut.conj k).toMonoidHom = t.Zhat := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hDcyc : IsCyclic ↥t.Dhat := t.isCyclic_Dhat hK32 hGA hSp hK332 hOut hp hN hZ
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf 3 t.Dhat ⊤ :=
    t.isSylowOf_Dhat hK32 hGA hSp hK332 hOut hp hN hZ
  have hWp : IsPGroup 3 ↥W := IsPGroup.of_card (n := 1) (by rw [hW]; norm_num)
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup t.Xhat) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hDsyl.exists_mem_conj hQsyl
  have hle : W.map (MulAut.conj k⁻¹).toMonoidHom ≤ t.Dhat := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem := (hk w).mp (hWQ hw)
    simpa [MulAut.conj_apply] using hmem
  have hcard : Nat.card (W.map (MulAut.conj k⁻¹).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hW]
  have hsub : (W.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf t.Dhat =
      t.Zhat.subgroupOf t.Dhat := by
    refine (IsCyclic.subgroup_eq_iff_card_eq (G := ↥t.Dhat)).mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe t.Zhat_le_Dhat).toEquiv, t.card_Zhat]
  have hWeq : W.map (MulAut.conj k⁻¹).toMonoidHom = t.Zhat := by
    have h1 := congrArg (Subgroup.map t.Dhat.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le t.Zhat_le_Dhat]
      at h1
  exact ⟨k⁻¹, hWeq⟩

theorem isCyclic_of_isPGroup_Xhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {P : Subgroup t.Xhat}
    (hP : IsPGroup 3 P) : IsCyclic ↥P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hDcyc : IsCyclic ↥t.Dhat := t.isCyclic_Dhat hK32 hGA hSp hK332 hOut hp hN hZ
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf 3 t.Dhat ⊤ :=
    t.isSylowOf_Dhat hK32 hGA hSp hK332 hOut hp hN hZ
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup t.Xhat) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hDsyl.exists_mem_conj hQsyl
  have hle : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ t.Dhat := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem := (hk w).mp (hPQ hw)
    simpa [MulAut.conj_apply] using hmem
  have hcyc : IsCyclic ↥(P.map (MulAut.conj k⁻¹).toMonoidHom) :=
    Subgroup.isCyclic_of_le hle
  exact (Subgroup.equivMapOfInjective P (MulAut.conj k⁻¹).toMonoidHom
    (MulAut.conj k⁻¹).injective).isCyclic.mpr hcyc

theorem pRank_Xhat (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hOut : PerfectAutInner) {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup t.Xhat) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥t.Xz) := by
    intro h
    have h1 : 3 = 1 := Nat.Coprime.eq_one_of_dvd CFSG.pPrimeCore_coprime_card h
    norm_num at h1
  have hq : CFSG.pRank 3 t.Xhat = CFSG.pRank 3 ↥t.Xz :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _ hO
  calc CFSG.Open.pRank 3 (⊤ : Subgroup t.Xhat)
      = CFSG.pRank 3 t.Xhat := (CFSG.SectionRank.pRank_eq_open_pRank_top 3 t.Xhat).symm
    _ = CFSG.pRank 3 ↥t.Xz := hq
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥t.Xz) :=
        CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥t.Xz
    _ = CFSG.Open.pRank 3 t.Xz := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup t.Xz).symm
    _ = 1 := t.pRank_Xz hK332 hOut hp hN hZ

private theorem normalClosure_Zhat_eq_top
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.normalClosure (t.Zhat : Set t.Xhat) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) :=
    QuotientGroup.mk'_surjective _
  have hset : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) ''
      (t.Z.subgroupOf t.Xz : Set ↥t.Xz) = (t.Zhat : Set t.Xhat) := by
    rw [Zhat, Subgroup.coe_map]
  calc Subgroup.normalClosure (t.Zhat : Set t.Xhat)
      = Subgroup.normalClosure ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) ''
          (t.Z.subgroupOf t.Xz : Set ↥t.Xz)) := by rw [hset]
    _ = (Subgroup.normalClosure ((t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) : Set ↥t.Xz)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) :=
        (Subgroup.map_normalClosure _ _ hsurj).symm
    _ = ⊤ := by
        rw [t.normalClosure_Z_subgroupOf_Xz hK32 hGA hSp hK332 hOut hp hN hZ, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr hsurj]

theorem isSimpleGroup_Xhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : IsSimpleGroup t.Xhat := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : Subgroup.normalClosure (t.Zhat : Set t.Xhat) = ⊤ :=
    t.normalClosure_Zhat_eq_top hK32 hGA hSp hK332 hOut hp hN hZ
  have hnt : Nontrivial t.Xhat := by
    have hne : t.Zhat ≠ ⊥ := by
      intro hb
      have h1 : Nat.card t.Zhat = 1 := by rw [hb, Subgroup.card_bot]
      rw [t.card_Zhat] at h1
      norm_num at h1
    haveI : Nontrivial ↥t.Zhat := (Subgroup.nontrivial_iff_ne_bot t.Zhat).mpr hne
    obtain ⟨a, b, hab⟩ := ‹Nontrivial ↥t.Zhat›
    exact ⟨(a : t.Xhat), (b : t.Xhat), fun h => hab (Subtype.ext h)⟩
  refine (isSimpleGroup_iff t.Xhat).mpr ⟨hnt, fun N hNnorm => ?_⟩
  by_cases h3 : 3 ∣ Nat.card N
  · right
    obtain ⟨w, hwN, hword⟩ : ∃ w : t.Xhat, w ∈ N ∧ orderOf w = 3 := by
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3
      exact ⟨(w : t.Xhat), w.2, by rwa [← Subgroup.orderOf_mk (w : t.Xhat) w.2]⟩
    have hWcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hword]
    have hWN : Subgroup.zpowers w ≤ N := Subgroup.zpowers_le.mpr hwN
    obtain ⟨k, hk⟩ :=
      t.exists_conj_map_eq_Zhat hK32 hGA hSp hK332 hOut hp hN hZ hWcard
    have hZle : t.Zhat ≤ N := by
      rw [← hk]
      calc (Subgroup.zpowers w).map (MulAut.conj k).toMonoidHom
          ≤ N.map (MulAut.conj k).toMonoidHom := Subgroup.map_mono hWN
        _ = N := Subgroup.normal_iff_map_conj_eq.mp hNnorm k
    have hle : Subgroup.normalClosure (t.Zhat : Set t.Xhat) ≤ N :=
      (Subgroup.normalClosure_subset_iff (N := N)).mp hZle
    rw [htop] at hle
    exact top_le_iff.mp hle
  · left
    have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have hle : N ≤ CFSG.pPrimeCore 3 t.Xhat := CFSG.le_pPrimeCore_of_normal_coprime hNnorm hcop
    have hbot : CFSG.pPrimeCore 3 t.Xhat = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    rw [hbot] at hle
    exact le_bot_iff.mp hle

theorem exists_mul_ne_mul_Xhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    ∃ a b : t.Xhat, a * b ≠ b * a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h
  push Not at h
  haveI hcomm : IsMulCommutative t.Xhat := isMulCommutative_iff.mpr fun a b => h a b
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  have hquot : ⁅(⊤ : Subgroup ↥t.Xz), ⊤⁆ ≤ CFSG.pPrimeCore 3 ↥t.Xz := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hmem : ⁅g₁, g₂⁆ ∈ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact isMulCommutative_iff.mp hcomm _ _
    rwa [QuotientGroup.ker_mk'] at hmem
  have hcommle : ⁅t.Xz, t.Xz⁆ ≤ t.Oz := by
    show ⁅t.Xz, t.Xz⁆ ≤ Subgroup.map t.Xz.subtype (CFSG.pPrimeCore 3 ↥t.Xz)
    have h2 := Subgroup.map_mono (f := t.Xz.subtype) hquot
    rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  have hKyle : t.Ky ≤ ⁅t.Xz, t.Xz⁆ := by
    rw [← t.commutator_Ky]
    exact Subgroup.commutator_mono hKyX hKyX
  have hZleOz : t.Z ≤ t.Oz :=
    t.Z_le_Dz.trans (t.Dz_le_Ky.trans (hKyle.trans hcommle))
  have hZ'leO : t.Z.subgroupOf t.Xz ≤ CFSG.pPrimeCore 3 ↥t.Xz := by
    intro z hz
    obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hZleOz (Subgroup.mem_subgroupOf.mp hz))
    have hzo : z = o := Subtype.ext hoeq.symm
    rwa [hzo]
  have hbot : t.Z.subgroupOf t.Xz = ⊥ := by
    refine le_bot_iff.mp ?_
    have h2 : t.Z.subgroupOf t.Xz ≤
        (t.Z.subgroupOf t.Xz ⊓ CFSG.pPrimeCore 3 ↥t.Xz) := le_inf le_rfl hZ'leO
    rwa [t.inf_pPrimeCore_eq_bot] at h2
  have h1 : Nat.card (t.Z.subgroupOf t.Xz : Subgroup ↥t.Xz) = 1 := by
    rw [hbot, Subgroup.card_bot]
  rw [t.card_Z_subgroupOf] at h1
  norm_num at h1

theorem isKGroup_Xhat : CFSG.Open.IsKGroup t.Xhat := by
  haveI hOnormal : (CFSG.pPrimeCore 3 ↥t.Xz).Normal := CFSG.pPrimeCore_normal
  have hXne : t.Xz ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := c.standing.simple
    have hcent : t.y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (t.Xz_le_centralizer (by rw [htop]; exact Subgroup.mem_top g))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · have hy1 : t.y = 1 := Subgroup.mem_bot.mp (by rw [← h]; exact hcent)
      have hord := t.orderOf_y
      rw [hy1, orderOf_one] at hord
      omega
    · obtain ⟨a, b, hab⟩ := c.standing.nonab
      exact hab (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a)
  exact (c.standing.kProper.isKGroup t.Xz hXne).quotient (CFSG.pPrimeCore 3 ↥t.Xz)

theorem Xhat_cases (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    (∃ ℓ f : ℕ, CFSG.Blueprint.LieModel t.Xhat .PSL 2 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel t.Xhat .PSL 3 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel t.Xhat .PSU 3 ℓ f) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor t.Xhat .J1 :=
  hK32 t.Xhat t.isKGroup_Xhat
    (t.isSimpleGroup_Xhat hK32 hGA hSp hK332 hOut hp hN hZ)
    (t.exists_mul_ne_mul_Xhat hK32 hGA hSp)
    (t.pRank_Xhat hK332 hOut hp hN hZ)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
