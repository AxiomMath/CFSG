module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNPerm
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNFullDiagonal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {n : ℕ}
variable {Bs L : Subgroup G} {x : G}

theorem e6QTwoN_sylow_conj_of_card_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X P₁ P₂ : Subgroup G} (hP₁ : P₁ ≤ X) (hP₂ : P₂ ≤ X)
    (hP₁g : IsPGroup p P₁) (hP₂g : IsPGroup p P₂) (hcard : Nat.card P₁ = Nat.card P₂)
    (hindex : ¬ p ∣ (P₁.subgroupOf X).index) :
    ∃ z ∈ X, P₂.map (MulAut.conj z).toMonoidHom = P₁ := by
  have h₁ : IsPGroup p (P₁.subgroupOf X) := hP₁g.comap_subtype
  have h₂ : IsPGroup p (P₂.subgroupOf X) := hP₂g.comap_subtype
  have hc₁ : Nat.card (P₁.subgroupOf X) = Nat.card P₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁).toEquiv
  have hc₂ : Nat.card (P₂.subgroupOf X) = Nat.card P₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₂).toEquiv
  have hindex₂ : ¬ p ∣ (P₂.subgroupOf X).index := by
    have e₁ := (P₁.subgroupOf X).card_mul_index
    have e₂ := (P₂.subgroupOf X).card_mul_index
    rw [hc₁, hcard] at e₁
    rw [hc₂] at e₂
    have hpos : 0 < Nat.card P₂ := Nat.card_pos
    have : (P₂.subgroupOf X).index = (P₁.subgroupOf X).index :=
      Nat.eq_of_mul_eq_mul_left hpos (e₂.trans e₁.symm)
    rwa [this]
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq X (h₂.toSylow hindex₂) (h₁.toSylow hindex)
  refine ⟨z, z.2, ?_⟩
  have hz' : MulAut.conj z • P₂.subgroupOf X = P₁.subgroupOf X := by
    have := congrArg (fun S : Sylow p X => (S : Subgroup X)) hz
    simpa [Sylow.coe_subgroup_smul] using this
  have hle : P₂.map (MulAut.conj (z : G)).toMonoidHom ≤ P₁ := by
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MulAut.conj z • (⟨g, hP₂ hg⟩ : X) ∈ MulAut.conj z • P₂.subgroupOf X :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (by simpa [Subgroup.mem_subgroupOf] using hg)
    rw [hz', Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.conj_apply] using hmem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective P₂ _ (MulAut.conj (z : G)).injective).toEquiv).le

@[expose] noncomputable def e6QTwoNNormAction
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :
    ↥(Subgroup.normalizer (L : Set G)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :=
  (MulAut.congr θ).toMonoidHom.comp
    ((e6QTwoQuotCenterAutHom L).comp (Subgroup.normalizerMonoidHom L))

omit [Finite G] [Finite K] in
theorem e6QTwoNNormAction_apply
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (g : ↥(Subgroup.normalizer (L : Set G))) :
    e6QTwoNNormAction θ g =
      (MulAut.congr θ) (e6QTwoQuotCenterAutHom L
        (Subgroup.normalizerMonoidHom L g)) := rfl

omit [Finite G] [Finite K] in
private theorem e6QTwoNNormAction_mk
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (g : ↥(Subgroup.normalizer (L : Set G))) (l : L) :
    e6QTwoNNormAction θ g (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L)
        (Subgroup.normalizerMonoidHom L g l)) := by
  rw [e6QTwoNNormAction_apply, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk]

omit [Finite G] [Finite K] in
theorem e6QTwoNNormAction_of_mem_L
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (g : ↥L) :
    e6QTwoNNormAction θ ⟨g, Subgroup.le_normalizer g.2⟩ =
      e6QTwoNConjOnQuot θ g := by
  ext q
  obtain ⟨q', rfl⟩ := θ.surjective q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q'
  rw [e6QTwoNNormAction_mk, e6QTwoNConjOnQuot_mk]
  have h : (Subgroup.normalizerMonoidHom L ⟨g, Subgroup.le_normalizer g.2⟩) l =
      g * l * g⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [h]

omit [Finite G] in
omit [Finite G] [Finite K] in
theorem e6QTwoNNormAction_of_mem_Bs
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) :
    e6QTwoNNormAction θ ⟨b, hNL b.2⟩ = e6QTwoNFrameAction hNL θ b := by
  ext q
  obtain ⟨q', rfl⟩ := θ.surjective q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q'
  rw [e6QTwoNNormAction_mk, e6QTwoNFrameAction_apply]
  have h : (Subgroup.normalizerMonoidHom L ⟨b, hNL b.2⟩) l =
      ⟨(b : G) * (l : G) * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL b.2) (l : G)).mp l.2⟩ := by
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [h]


omit [Finite G] in
theorem e6QTwoNNormalizesCenter
    {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Bs ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) := by
  have hC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hNL.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
  exact (le_inf hNL hC).trans
    (Subgroup.inf_normalizer_le_normalizer_inf (H := L)
      (K := Subgroup.centralizer (L : Set G)))

private theorem e6QTwoN_index_eq
    (hBZ : Bs ≤ Subgroup.normalizer
    ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G)) :
    (Bs.subgroupOf (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)))).index =
      ((Bs ⊓ (L ⊓ Subgroup.centralizer (L : Set G))).subgroupOf
        (L ⊓ Subgroup.centralizer (L : Set G))).index := by
  set Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  have hsup : Nat.card ↥(Bs ⊔ Z) * Nat.card ↥(Bs ⊓ Z) = Nat.card ↥Bs * Nat.card ↥Z :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hBZ
  have h1 : (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs = Nat.card ↥(Bs ⊔ Z) := by
    have h := Subgroup.relIndex_mul_card (H := Bs) (K := Bs ⊔ Z)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have h2 : ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥(Bs ⊓ Z) = Nat.card ↥Z := by
    have h := Subgroup.relIndex_mul_card (H := Bs ⊓ Z) (K := Z)
    rw [show (Bs ⊓ Z) ⊓ Z = Bs ⊓ Z from by rw [inf_assoc, inf_idem]] at h
    exact h
  have hpos : 0 < Nat.card ↥(Bs ⊓ Z) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥Bs := Nat.card_pos
  have step : (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs =
      ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥Bs := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs * Nat.card ↥(Bs ⊓ Z)
        = Nat.card ↥(Bs ⊔ Z) * Nat.card ↥(Bs ⊓ Z) := by rw [h1]
      _ = Nat.card ↥Bs * Nat.card ↥Z := hsup
      _ = Nat.card ↥Bs * (((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥(Bs ⊓ Z)) := by rw [h2]
      _ = ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥Bs * Nat.card ↥(Bs ⊓ Z) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos2 step

omit [Finite G] in
private theorem e6QTwoN_pow_three_mem
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    {z : G} (hzL : z ∈ L)
    (hzc : z ∈ Subgroup.centralizer (L : Set G)) {k : ℕ} (hz : z ^ 3 ^ k = 1) :
    z ∈ Bs := by
  have hzc' : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzc l l.2
  have hdvd3 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hz
  have hdvdZ : orderOf z ∣ Nat.card (Subgroup.center ↥L) := by
    rw [Subgroup.orderOf_coe (⟨z, hzL⟩ : ↥L)]
    rw [Subgroup.orderOf_coe (⟨⟨z, hzL⟩, hzc'⟩ : Subgroup.center ↥L)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Subgroup.center ↥L)) := hZcop.pow_left k
  have h1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvdZ
  have hz1 : z = 1 := orderOf_eq_one_iff.mp h1
  rw [hz1]
  exact Subgroup.one_mem _

omit [Finite K] in
theorem e6QTwoNSylowIndex
    (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (_hK : Nat.card K = 4) {x : G}
    (_θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (_hperf : commutator ↥L = ⊤) (_hBs : IsElemAbelian 3 Bs) (_hx : x ∈ Bs)
    (_hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (_hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ¬ 3 ∣ (Bs.subgroupOf (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)))).index := by
  classical
  set Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  rw [e6QTwoN_index_eq (e6QTwoNNormalizesCenter hNL)]
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := ↥Z)
  have hPle : (P : Subgroup ↥Z) ≤ (Bs ⊓ Z).subgroupOf Z := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨k, hk⟩ := (P.isPGroup'.exists_orderOf_dvd_pow (⟨z, hz⟩ : ↥P))
    have hzk : (z : G) ^ 3 ^ k = 1 := by
      have h1 : orderOf (z : ↥Z) ∣ 3 ^ k := by
        rw [← Subgroup.orderOf_mk (H := (P : Subgroup ↥Z)) z hz]
        exact hk
      have h2 : (z : ↥Z) ^ 3 ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg (fun w : ↥Z => (w : G)) h2
    refine ⟨e6QTwoN_pow_three_mem hZcop z.2.1 z.2.2 hzk, z.2⟩
  have hdvd : ((Bs ⊓ Z).subgroupOf Z).index ∣ (P : Subgroup ↥Z).index :=
    Subgroup.index_dvd_of_le hPle
  have h3 : ¬ 3 ∣ (P : Subgroup ↥Z).index := Sylow.not_dvd_index P
  exact fun h => h3 (h.trans hdvd)
