module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvMain
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace UnitTv

section Config

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_noTransvectionSCr_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (htv : GGNoTransvectionSCr p r R I)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφt : GGIsTransvection p φ) (b : ↥Bs) : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  classical
  by_contra hb0
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hC.2.1.2.2.2
  obtain ⟨g, hgx, -, hφg⟩ := hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  set α : MulAut L := L.normalizerMonoidHom ⟨g, hgL⟩ with hα
  have hgc : ∀ c : Bs, g * (c : G) * g⁻¹ ∈ Bs := fun c => by rw [← hφg c]; exact (φ c).2
  have hconj : ∀ c : Bs, α * γ c * α⁻¹ = γ (φ c) := by
    intro c
    have h1 := normalizerMonoidHom_mul_ggGamma L hN ⟨g, hgL⟩ c (hgc c)
    rw [hα, h1]
    congr 1
    exact Subtype.ext (hφg c).symm
  have hNa : α ∈ Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨φ c, (hconj c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      have h1 := hconj (φ.symm c)
      rw [MulEquiv.apply_symm_apply, hc] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  refine htv L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI
    hr h3 (ggTorusSelfCent_ggGamma hN hSC) ⟨α, hNa⟩
    ⟨ggLAut L θ ⟨g, hgL⟩, fun l => by rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]⟩ ?_
  have hkerγ : γ.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    rw [MonoidHom.ker_rangeRestrict]
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hγ, ggGamma_eq_one_iff,
      ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  refine isTransvection_of_center_ne hp (fun c c' => Subtype.ext (IsElemAbelian.comm hBs c.2
    c'.2)) γ.rangeRestrict γ.rangeRestrict_surjective ?_ hφt ?_ ?_ (b := b) ?_
  · rw [hkerγ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1]
  · intro c hc
    rw [hkerγ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  · intro c
    exact Subtype.ext (hconj c)
  · intro h1
    apply hb0
    have h2 : b⁻¹ * φ b ∈ γ.rangeRestrict.ker := h1
    rw [hkerγ, Subgroup.mem_subgroupOf] at h2
    exact h2

end Config

section PerGroup


theorem ggNoTransvectionSCr_unitary63 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hcov : LineU.UnitaryCoverAt n 6 K)
    (hpq : 3 ∣ 2 ^ n + 1) :
    GGNoTransvectionSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _h3 hsc α _
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel' hK hn (by norm_num) Nat.prime_three hpq hcov
    hψ hker hperf hA hAI hcard
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  exact not_transvection_of_model hM hK Nat.prime_three (by norm_num) hpq (by norm_num) hA hsc
    hdiag α

end PerGroup

end UnitTv

section Labels


theorem largeEvenLabelAll_unitDvd63_tv {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab) (hn1 : lab.n ≠ 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p 3 R ∧ GGNoTransvectionSCr p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3 hn1
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (5 + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hdnd : (6, n) ≠ (6, 1) := fun h => hn1 (by simpa using congrArg Prod.snd h)
  have hlift := ggTorusLift_unitary hK hn (by norm_num : 3 ≤ 5 + 1) hdq hp hpn
  have hrk : ggUnitaryTorusRank 3 (5 + 1) = 3 := by simp [ggUnitaryTorusRank]
  rw [hrk] at hlift
  exact ⟨K, i1, i2, hK, ⟨hQ', hlift, UnitTv.ggNoTransvectionSCr_unitary63 hK hn
    (LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num) hdnd) hpn⟩⟩

theorem ggLTransvectionCenterInputOn_unitDvd63_of (h5 : Line63.GGUnitDvd63BstarRankInput) :
    GGLTransvectionCenterInputOn fun p lab => GGUnitDvd63Label p lab ∧ lab.n ≠ 1 := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hcard := h5 G p B Bs x L D J hC (hM.mono fun _ _ h => h.1)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGUnitDvd63Label p lab ∧ lab.n ≠ 1)
    (fun lab hlab hs => largeEvenLabelAll_unitDvd63_tv hp hlab hs.1 hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  have hnc := UnitTv.exists_noncyclic_of_torusLift hp (by norm_num : 2 ≤ 3) hL θ hlift
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hBsN
  have h4' : p ^ 4 ≤ Nat.card (ggGamma L hBsN).range := by
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  exact UnitTv.mem_zpowers_of_noTransvectionSCr_card hC hnc hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4'
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4') htvt hφ htv b

end Labels

end CFSG.StandardType

end
