module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

theorem uc22p22m_T_le_centralizer_Z (D : Data G) : D.T ≤ centralizer (D.Z : Set G) := by
  intro t ht
  rw [mem_centralizer_iff]
  intro z hz
  exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz).2.1 t ht).symm

theorem uc22p22m_Z_le_U (D : Data G) : D.Z ≤ D.U := by
  intro z hz
  refine Subgroup.mem_iSup_of_mem (1 : D.M) ?_
  exact ⟨z, hz, by simp⟩

theorem uc22p22m_centralizer_U_le (D : Data G) :
    centralizer (D.U : Set G) ≤ centralizer (D.Z : Set G) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (uc22p22m_Z_le_U D))

theorem uc22p22m_le_L (D : Data G) {L B P : Subgroup G}
    (hL : L ∈ calLOf D.T D.M (centralizer (D.Z : Set G))) (hBL : B ≤ L)
    (hPZ : P ≤ centralizer (D.Z : Set G)) (hPB : ⁅P, B⁆ = P) : P ≤ L := by
  classical
  have hTH : D.T ≤ centralizer (D.Z : Set G) := uc22p22m_T_le_centralizer_Z D
  obtain ⟨⟨-, -, -, K, hK, hLK⟩, hsub⟩ := hL
  have hKL : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp (centralizer (D.Z : Set G)) :=
    CFSG.Quasithin.cComp_mem_of_subnormal hsub hKL
  have hKt : ∀ t : D.T, uc22p20bCj (t : G) K ∈ CFSG.Quasithin.cComp (centralizer (D.Z : Set G)) :=
    fun t => uc22p20b_cj_mem_cComp hKH (hTH t.2)
  set H₁ : Subgroup G := centralizer (D.Z : Set G) with hH₁
  set X : Subgroup G := CFSG.Quasithin.cCompSpan H₁ with hX
  have hLX : L ≤ X := by
    rw [hLK]
    exact iSup_le fun t => CFSG.Quasithin.le_cCompSpan (hKt t)
  have hXL : X ≤ normalizer (L : Set G) := by
    rw [hLK]
    exact uc22p20b_le_normalizer_iSup _ _ fun t => uc22p20e_cCompSpan_le_normalizer (hKt t)
  have hXn : ∀ h ∈ H₁, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    have hxH : x ∈ H₁ := uc22p20e_cCompSpan_le H₁ hx
    have hxs : (⟨x, hxH⟩ : ↥H₁) ∈ X.subgroupOf H₁ := hx
    have := (uc22p20b_normal_cCompSpan H₁).conj_mem _ hxs ⟨h, hh⟩
    exact this
  have hcomm : ∀ x b : G, ⁅x, b⁆ = (x * b * x⁻¹) * b⁻¹ := by
    intro x b
    simp only [commutatorElement_def, mul_assoc]
  have hPX : P ≤ X := by
    rw [← hPB]
    refine Subgroup.commutator_le.2 fun x hx b hb => ?_
    have hbX : b ∈ X := hLX (hBL hb)
    rw [hcomm]
    exact X.mul_mem (hXn x (hPZ hx) b hbX) (X.inv_mem hbX)
  rw [← hPB]
  refine Subgroup.commutator_le.2 fun x hx b hb => ?_
  have hxN : x ∈ normalizer (L : Set G) := hXL (hPX hx)
  rw [hcomm]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN b).1 (hBL hb)) (L.inv_mem (hBL hb))

theorem uc22p22m_le_L_ctx {D : Data G} {Ch : Choice2011 G} (c : Ctx22b D Ch) {P : Subgroup G}
    (hPU : P ≤ centralizer (D.U : Set G)) (hPB : ⁅P, c.B⁆ = P) : P ≤ c.L :=
  uc22p22m_le_L D c.hL (c.hB.1.trans c.hLge) (hPU.trans (uc22p22m_centralizer_U_le D)) hPB

end Core

section Parabolic

theorem uc22p22m_isSylowOf_map {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] (π : X →* Y)
    (hπ : Function.Surjective π) {A : Subgroup X} (hA : CFSG.ABGLocalTools.IsSylowOf 2 A ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (A.map π) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hA ⊢
  obtain ⟨-, hp, hdvd⟩ := hA
  refine ⟨le_top, hp.map π, ?_⟩
  rw [Subgroup.relIndex_top_right] at hdvd ⊢
  exact fun h => hdvd (h.trans (Subgroup.index_map_dvd A hπ))

theorem uc22p22m_normalizer_le_of_parabolic {Y : Type} [Group Y] [Finite Y] {Qb Sb S' : Subgroup Y}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤) (hSQ : Sb ≤ normalizer (Qb : Set Y))
    (hS' : CFSG.ABGLocalTools.IsSylowOf 2 S' ⊤) (hN : normalizer (S' : Set Y) ≤ Qb) :
    normalizer (Sb : Set Y) ≤ Qb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : Qb ⊔ Sb ≤ normalizer (Qb : Set Y) := sup_le Subgroup.le_normalizer hSQ
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 Sb (Qb ⊔ Sb) := hS.of_le le_sup_right le_top
  have hS'K : CFSG.ABGLocalTools.IsSylowOf 2 S' (Qb ⊔ Sb) :=
    hS'.of_le (Subgroup.le_normalizer.trans (hN.trans le_sup_left)) le_top
  obtain ⟨k, hkK, hk⟩ := uc22p22f_exists_conj_sylow hS'K hSK
  have hkS : ∀ y : Y, y ∈ Sb ↔ k⁻¹ * y * k ∈ S' := by
    intro y
    rw [hk, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro h
      exact ⟨k⁻¹ * y * k, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  intro g hg
  have hgS := Subgroup.mem_normalizer_iff.1 hg
  have hgS' : k⁻¹ * g * k ∈ normalizer (S' : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have e1 : s ∈ S' ↔ k * s * k⁻¹ ∈ Sb := by
      rw [hkS]; simp [mul_assoc]
    have e2 : (k⁻¹ * g * k) * s * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * (k * s * k⁻¹) * g⁻¹) * k := by
      group
    rw [e2, ← hkS, ← hgS, ← e1]
  have hq : k⁻¹ * g * k ∈ Qb := hN hgS'
  have h3 := (Subgroup.mem_normalizer_iff.1 (hKN hkK) (k⁻¹ * g * k)).1 hq
  have e3 : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
  rwa [e3] at h3

theorem uc22p22m_le_of_parabolic {G : Type} [Group G] [Finite G] {T L Q P : Subgroup G}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTL : T ≤ normalizer (L : Set G))
    (hQ : ParabolicOf L Q) (hTQ : T ≤ normalizer (Q : Set G)) (hPL : P ≤ L)
    (hPS : P ≤ normalizer ((T ⊓ L : Subgroup G) : Set G)) : P ≤ Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hOQ, hQL, S₁, hS₁⟩ := hQ
  have hTLT : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T) := hTsyl.of_le le_sup_right le_top
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L :=
    hTLT.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hTL)
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hSx : CFSG.ABGLocalTools.IsSylowOf 2 ((T ⊓ L).subgroupOf L) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl ⊢
    obtain ⟨-, hp, hdvd⟩ := hSyl
    exact ⟨le_top, hp.comap_subtype, by rw [Subgroup.relIndex_top_right]; exact hdvd⟩
  set Sb : Subgroup (Bar2 L) := ((T ⊓ L).subgroupOf L).map π with hSb
  set Qb : Subgroup (Bar2 L) := (Q.subgroupOf L).map π with hQb
  have hSbS : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤ := uc22p22m_isSylowOf_map π hπs hSx
  have hSQ : Sb ≤ normalizer (Qb : Set (Bar2 L)) := by
    refine uc22p20e_le_normalizer_of_conj fun y hy x hx => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨q, hq, rfl⟩ := hx
    refine ⟨s * q * s⁻¹, ?_, by simp⟩
    have hsT : (s : G) ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq
    exact (Subgroup.mem_normalizer_iff.1 (hTQ hsT) (q : G)).1 hqQ
  have hSyl₁ : CFSG.ABGLocalTools.IsSylowOf 2 (S₁ : Subgroup (Bar2 L)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S₁.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S₁.not_dvd_index⟩
  have hNQ : normalizer (Sb : Set (Bar2 L)) ≤ Qb :=
    uc22p22m_normalizer_le_of_parabolic hSbS hSQ hSyl₁ hS₁
  have hPb : (P.subgroupOf L).map π ≤ normalizer (Sb : Set (Bar2 L)) := by
    refine uc22p20e_le_normalizer_of_conj fun y hy x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨a * s * a⁻¹, ?_, by simp⟩
    have haP : (a : G) ∈ P := Subgroup.mem_subgroupOf.1 ha
    have hsTL : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
    exact (Subgroup.mem_normalizer_iff.1 (hPS haP) (s : G)).1 hsTL
  intro x hx
  have hxL : x ∈ L := hPL hx
  have hxb : π ⟨x, hxL⟩ ∈ Qb := hNQ (hPb ⟨⟨x, hxL⟩, hx, rfl⟩)
  obtain ⟨q, hq, hqx⟩ := hxb
  have hmem : q⁻¹ * ⟨x, hxL⟩ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq (s := CFSG.pCore 2 ↥L)).1 hqx
  have hqx' : ((q⁻¹ * ⟨x, hxL⟩ : ↥L) : G) ∈ Q :=
    hOQ (Subgroup.mem_map.2 ⟨_, hmem, rfl⟩)
  have e : x = (q : G) * ((q⁻¹ * ⟨x, hxL⟩ : ↥L) : G) := by simp
  rw [e]
  exact Q.mul_mem (Subgroup.mem_subgroupOf.1 hq) hqx'

theorem uc22p22m_le_normalizer_Hinf {G : Type} [Group G] (Q : Subgroup G) :
    Q ≤ normalizer (Hinf Q : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  have hn : (CFSG.perfectResidual ↥Q).Normal := inferInstance
  have key : ∀ (g : G) (hg : g ∈ Q) (y : G), y ∈ Hinf Q → g * y * g⁻¹ ∈ Hinf Q := by
    rintro g hg y ⟨w, hw, rfl⟩
    exact ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, hn.conj_mem w hw _, by simp⟩
  intro y
  exact ⟨key q hq y, fun h => by
    have := key q⁻¹ (Q.inv_mem hq) _ h
    simpa [mul_assoc] using this⟩

end Parabolic

section Residual

variable {G : Type} [Group G] [Finite G]

@[expose] def L0Parabolic (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M, ∀ K ∈ calLLow D.T D.M, K ≤ L →
    ∃ Q : Subgroup G, ParabolicOf L Q ∧ D.T ≤ normalizer (Q : Set G) ∧ K = Hinf Q

end Residual

end CFSG.LocalAnalysis.UniquenessCase.UC22
