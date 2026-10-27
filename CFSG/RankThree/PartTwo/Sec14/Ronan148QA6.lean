module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_delta_eqQ {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {B Q X : Subgroup G} (hB : IsHyperplane A B) (hQ : Q ∈ scriptQZero A (lB A))
    (hQB : Q ≤ Subgroup.centralizer (B : Set G)) {b d : G} (hb : b ∈ B)
    (hΔ : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hN : Inv143Q A b d X) :
    Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X := by
  have hbA : b ∈ A := hB.1 hb
  have hAab : IsMulCommutative A := h.isE27'.1.1
  have hQb : Q ≤ Subgroup.centralizer ({b} : Set G) :=
    hQB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hQΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hQ.1 hQb
  rw [hΔ, sup_right_comm] at hQΔ
  rw [hQ.2]
  exact (Subgroup.commutator_mono hQΔ le_rfl).trans (commutator_sup_le148
    (hN.le_normalizer hAab hbA) ((pPrimeCoreOf_le 3 _).trans (hN.centralizer_le hbA))
    (pPrimeCoreOf_le 3 _))

theorem pPrimeCoreOf_inf_sup_le {b : G} {X Y : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b) :
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G) ⊓
        (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X)) ≤
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  set YC := Y ⊓ Cb with hYC
  set E := sSup (thetaComponentsAt 3 b) with hE
  set M := YC ⊓ (N ⊔ X) with hM
  set M' := YC ⊓ (N ⊔ E) with hM'
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hCbE : Cb ≤ Subgroup.normalizer ((N ⊔ E : Subgroup G) : Set G) := by
    intro g hg
    refine Desc143X.mem_normalizer_sup (hCbN hg) ?_
    refine Ronan148D.mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : E.map (MulAut.conj g).toMonoidHom ≤ E := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun K hK y hy => ?_
      exact le_sSup (Sec6.map_conj_mem_thetaComponentsAt hg hK) ⟨y, hy, rfl⟩
    exact hle ⟨x, hx, rfl⟩
  have hEX : E ≤ Subgroup.normalizer ((N ⊔ X : Subgroup G) : Set G) := by
    refine sSup_le fun K hK y hy => ?_
    by_cases hKX : K = X
    · rw [hKX] at hy
      exact Subgroup.le_normalizer (Subgroup.mem_sup_right hy)
    have hyC : y ∈ Cb := le_centralizer_of_mem_thetaComponentsAt hK hy
    have h1 : N ⊔ X ≤ (N ⊔ X).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun n hn => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hCbN hyC) n).mp hn)
      · rw [Subgroup.mem_comap]
        have hcomm : ⁅y, x⁆ ∈ N := (inSubgroup_theta_le_pPrimeCoreOf Cb)
          (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hX hKX
            (Subgroup.commutator_mem_commutator hy hx))
        have e : (MulAut.conj y).toMonoidHom x = ⁅y, x⁆ * x := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hx)
    exact Ronan148D.mem_normalizer_of_conj_mem fun z hz => h1 hz
  have hNE : N ⊔ E ≤ Subgroup.normalizer ((N ⊔ X : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) hEX
  have hMM' : M ≤ M' := inf_le_inf_left _ (sup_le_sup_left (le_sSup hX) _)
  have hM'M : M' ≤ Subgroup.normalizer (M : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg.1, hNE hg.2⟩
  have hYCM' : YC ≤ Subgroup.normalizer (M' : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hCbE hg.2⟩
  have h1 : pPrimeCoreOf 3 M ≤ pPrimeCoreOf 3 M' :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 M).trans hMM')
      (hM'M.trans (normalizer_le_normalizer_pPrimeCoreOf 3 M)) (coprime_card_pPrimeCoreOf 3 M)
  have h2 : pPrimeCoreOf 3 M' ≤ pPrimeCoreOf 3 YC :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 M').trans inf_le_left)
      (hYCM'.trans (normalizer_le_normalizer_pPrimeCoreOf 3 M')) (coprime_card_pPrimeCoreOf 3 M')
  exact h1.trans h2

theorem le_pPrimeCoreOf_of_coprimeQ {Y Cb N J R Q : Subgroup G} {u : G} (hu3 : u ^ 3 = 1)
    (hNCb : N ≤ Cb) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hCbN : Cb ≤ Subgroup.normalizer (N : Set G))
    (huNJ : u ∈ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G))
    (hOM : pPrimeCoreOf 3 (Y ⊓ Cb ⊓ (N ⊔ J)) ≤ pPrimeCoreOf 3 (Y ⊓ Cb))
    (huY : u ∈ Subgroup.normalizer (Y : Set G)) (huCb : u ∈ Cb) (hJCb : J ≤ Cb)
    (hJu : J ≤ Subgroup.centralizer ({u} : Set G))
    (hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hR3 : Nat.Coprime 3 (Nat.card R)) (hQR : Q ≤ R) (hQ : Q ≤ Y ⊓ Cb) (hQNJ : Q ≤ N ⊔ J) :
    Q ≤ pPrimeCoreOf 3 (Y ⊓ Cb) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set YC := Y ⊓ Cb with hYC
  set M := YC ⊓ (N ⊔ J) with hM
  set K₀ := M ⊓ N with hK₀
  have huYC : u ∈ Subgroup.normalizer (YC : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huY, Subgroup.le_normalizer huCb⟩
  have huM : u ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huYC, huNJ⟩
  have huK : u ∈ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huM, hCbN huCb⟩
  have hMCb : M ≤ Cb := inf_le_left.trans inf_le_right
  have hMK : M ≤ Subgroup.normalizer (K₀ : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hMCb.trans hCbN)
  have hK3 : ¬ 3 ∣ Nat.card K₀ := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
      (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hZN : Subgroup.zpowers u ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (hCbN huCb)
  have hJZ : J ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [centralizer_zpowers148]
    exact hJu
  have hc := commutator_sup_le148 hZN (hJCb.trans hCbN) hJZ
  have hMu : ∀ m ∈ M, ⁅m, u⁆ ∈ K₀ := by
    intro m hm
    refine Subgroup.mem_inf.mpr ⟨?_, hc (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mp hm).2 (Subgroup.mem_zpowers u))⟩
    have h1 : u * m⁻¹ * u⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp huM _).mp (inv_mem hm)
    have h2 : ⁅m, u⁆ = m * (u * m⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hm h1
  set N₀ := N.subgroupOf Cb with hN₀
  have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNCb).mpr hCbN
  have hRM : R ⊓ M ≤ Cb := inf_le_right.trans hMCb
  set U := ((R ⊓ M).subgroupOf Cb).map (QuotientGroup.mk' N₀) with hU
  have hUN : (U.comap (QuotientGroup.mk' N₀)).map Cb.subtype = (R ⊓ M) ⊔ N := by
    rw [hU, Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hRM, hN₀, Subgroup.map_subgroupOf_eq_of_le hNCb]
  have hMnorm : M ≤ Subgroup.normalizer (((R ⊓ M) ⊔ N : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨c, hcM, hcu, hcm⟩ :=
      Item148HJ.exists_commute_of_commutator_mem hu3 inf_le_left hMK huK hK3 hm (hMu m hm)
    have hcC : c ∈ Cb := hMCb hcM
    have hmC : m ∈ Cb := hMCb hm
    have hcR : c ∈ Subgroup.normalizer (R : Set G) :=
      hR (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcM).1,
        Subgroup.mem_centralizer_singleton_iff.mpr hcu⟩)
    have hcRM : (⟨c, hcC⟩ : ↥Cb) ∈
        Subgroup.normalizer (((R ⊓ M).subgroupOf Cb : Subgroup ↥Cb) : Set ↥Cb) :=
      Item148HJ.mem_normalizer_subgroupOf ⟨c, hcC⟩
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨hcR, Subgroup.le_normalizer hcM⟩)
    have hπcm : QuotientGroup.mk' N₀ (⟨m, hmC⟩ : ↥Cb) = QuotientGroup.mk' N₀ ⟨c, hcC⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN₀,
        Subgroup.mem_subgroupOf]
      simpa using inv_mem (Subgroup.mem_inf.mp hcm).2
    have h1 : QuotientGroup.mk' N₀ (⟨m, hmC⟩ : ↥Cb) ∈
        Subgroup.normalizer (U : Set (↥Cb ⧸ N₀)) := by
      rw [hπcm]
      exact Subgroup.le_normalizer_map (QuotientGroup.mk' N₀) ⟨_, hcRM, rfl⟩
    have h2 : (⟨m, hmC⟩ : ↥Cb) ∈ Subgroup.normalizer
        ((U.comap (QuotientGroup.mk' N₀) : Subgroup ↥Cb) : Set ↥Cb) :=
      Subgroup.le_normalizer_comap (QuotientGroup.mk' N₀) h1
    rw [← hUN]
    exact Subgroup.le_normalizer_map Cb.subtype ⟨_, h2, rfl⟩
  have hU3 : ¬ 3 ∣ Nat.card U := fun h => by
    have h' := h.trans (Subgroup.card_map_dvd _ (QuotientGroup.mk' N₀))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv] at h'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR3
      (h'.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hW3 : Nat.Coprime 3 (Nat.card (M ⊓ ((R ⊓ M) ⊔ N) : Subgroup G)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    have h3' := h3.trans (Subgroup.card_dvd_of_le inf_le_right)
    rw [← hUN, Subgroup.card_map_of_injective Cb.subtype_injective] at h3'
    refine Item148HJ.not_dvd_card_comap (QuotientGroup.mk' N₀) hU3 ?_ h3'
    rw [QuotientGroup.ker_mk', hN₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNCb).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
  have hQM : Q ≤ M := le_inf hQ hQNJ
  exact ((le_inf hQM ((le_inf hQR hQM).trans le_sup_left)).trans
    (le_pPrimeCoreOf inf_le_left (Late.le_normalizer_inf Subgroup.le_normalizer hMnorm)
      hW3)).trans hOM

open Item148PtRes in
theorem false_of_tripleCover_A6Q {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)))
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) : False := by
  have hD := h.toSec13Data
  have hbA : b ∈ A := hB.1 hb
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx b hbA)
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hX
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  have hθXN : θX ≤ N := by
    rw [hθX, Sec6.theta_eq_inf_of_mem_thetaComponentsAt hX]
    exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hX
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  have hNX : N ⊓ X ≤ θX := inf_le_theta_of_quasisimple hXN hN3 hq hZ
  have h3X : 3 ∣ Nat.card X := by
    have h1 : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ∣
        Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := Subgroup.card_subgroup_dvd_card _
    rw [hZ] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨u, huB, hub⟩ := exists_mem_not_mem_zpowers hD.card_eq hD.isElemAbelian.2 hB hbA
  have huA : u ∈ A := hB.1 huB
  have hu3 : u ^ 3 = 1 := hD.isElemAbelian.2 u huA
  have hu1 : u ≠ 1 := fun h1 => hub (h1 ▸ one_mem _)
  have hne : Subgroup.zpowers b ≠ Subgroup.zpowers u := fun he =>
    hub (he ▸ Subgroup.mem_zpowers u)
  have huCb : u ∈ Cb := hAC huA
  have hCB : Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Item148HJ.centralizer_inf_le_of_mem_hyperplane hD.isElemAbelian hD.card_eq hB hb huB hb1 hu1
      hne
  have hQYC : Q ≤ Y ⊓ Cb := le_inf (hQY.trans inf_le_left)
    (hQY.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))))
  have hcontra : Q ≤ N → False := fun hQN =>
    hQb ((le_inf hQN hQYC).trans (inf_le_pPrimeCoreOf148 (inf_le_right.trans hCbN) hN3))
  by_cases htriv : ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ θX
  ·
    have hM : ∀ m ∈ N ⊔ X, ⁅m, u⁆ ∈ N := fun m hm =>
      commutator_mem_of_mem_sup hXN (hCbN huCb) (fun x hx => by
        have h1 : ⁅x, u⁆ = (u * x * u⁻¹ * x⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact hθXN (inv_mem (htriv x hx))) hm
    set J := (N ⊔ X) ⊓ Subgroup.centralizer ({u} : Set G) with hJ
    have hNJ : N ⊔ J = N ⊔ X := by
      apply le_antisymm (sup_le le_sup_left inf_le_left)
      intro m hm
      have hMK : N ⊔ X ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hXN
      obtain ⟨c', hc'M, hc'u, hc'm⟩ := Item148HJ.exists_commute_of_commutator_mem hu3 le_sup_left
        hMK (hCbN huCb) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3) hm (hM m hm)
      have hc'J : c' ∈ J :=
        Subgroup.mem_inf.mpr ⟨hc'M, Subgroup.mem_centralizer_singleton_iff.mpr hc'u⟩
      have hm' : m = c' * (c'⁻¹ * m) := by group
      rw [hm', sup_comm]
      exact mul_mem (Subgroup.mem_sup_left hc'J) (Subgroup.mem_sup_right hc'm)
    have hJCb : J ≤ Cb := inf_le_left.trans (sup_le (pPrimeCoreOf_le 3 Cb) hXCb)
    have hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
      intro g hg
      obtain ⟨hgYC, hgu⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨hgY, hgb⟩ := Subgroup.mem_inf.mp hgYC
      exact le_normalizer_pPrimeCoreOf 3 _
        (Subgroup.mem_inf.mpr ⟨hgY, hCB (Subgroup.mem_inf.mpr ⟨hgb, hgu⟩)⟩)
    have hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
      (le_sSup ⟨hQ, hQY⟩ : Q ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G))).trans
        (hYB B hB)
    have huNJ : u ∈ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) := by
      rw [hNJ]
      exact hAX huA
    have hOM : pPrimeCoreOf 3 (Y ⊓ Cb ⊓ (N ⊔ J)) ≤ pPrimeCoreOf 3 (Y ⊓ Cb) := by
      rw [hNJ]
      exact pPrimeCoreOf_inf_sup_le hX
    have hQNJ : Q ≤ N ⊔ J := by
      rw [hNJ]
      exact hQX
    exact hQb (le_pPrimeCoreOf_of_coprimeQ hu3 (pPrimeCoreOf_le 3 Cb) hN3 hCbN huNJ hOM
      (hY.2 huA) huCb hJCb inf_le_right hR (coprime_card_pPrimeCoreOf 3 _) hQR hQYC hQNJ)
  ·
    push Not at htriv
    obtain ⟨x₀, hx₀, hx₀u⟩ := htriv
    apply hcontra
    have huX : u ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_of_le_sup hX h3X huCb (hAX huA)
    set σ : MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨u, huX⟩) with hσ
    have hσmk : ∀ (x : G) (hx : x ∈ X),
        σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
            ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huX x).mp hx⟩ := fun x hx => by
      rw [hσ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
      rfl
    have hmk : ∀ (x y : G) (hx : x ∈ X) (hy : y ∈ X),
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨x, hx⟩ : ↥X) =
            QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ↔ x * y⁻¹ ∈ θX := by
      intro x y hx hy
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
      constructor
      · intro h1
        exact ⟨_, h1, by simp [div_eq_mul_inv]⟩
      · rintro ⟨z, hz, hzeq⟩
        have : z = (⟨x, hx⟩ : ↥X) / ⟨y, hy⟩ := Subtype.ext (by
          simp only [Subgroup.coe_subtype] at hzeq
          rw [hzeq, Subgroup.coe_div, div_eq_mul_inv])
        rwa [← this]
    have hσ3 : σ ^ 3 = 1 := by
      have h1 : (⟨u, huX⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hu3)
      rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hx₀u
      have h2 := hσmk x₀ hx₀
      rw [h1, MulAut.one_apply] at h2
      exact (hmk _ _ _ hx₀).mp h2.symm
    have : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) := hq.1
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    intro q hq'
    obtain ⟨n, hn, y, hy, rfl⟩ := exists_mul_of_mem_sup hXN (hQX hq')
    have hqu : u * (n * y) * u⁻¹ = n * y := by
      have h1 := Subgroup.mem_centralizer_iff.mp ((hQY hq').2) u huB
      calc u * (n * y) * u⁻¹ = n * y * u * u⁻¹ := by rw [h1]
        _ = n * y := by group
    have hyN : u * y * u⁻¹ * y⁻¹ ∈ N := by
      have h1 : u * y * u⁻¹ * y⁻¹ = (u * n * u⁻¹)⁻¹ * n := by
        have h2 : u * y * u⁻¹ = (u * n * u⁻¹)⁻¹ * (n * y) := by
          rw [← hqu]
          group
        rw [h2]
        group
      rw [h1]
      exact mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp (hCbN huCb) n).mp hn)) hn
    have hyX : u * y * u⁻¹ * y⁻¹ ∈ X :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp huX y).mp hy) (inv_mem hy)
    have hfix : σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ := by
      rw [hσmk y hy]
      exact (hmk _ _ _ hy).mpr (hNX (Subgroup.mem_inf.mpr ⟨hyN, hyX⟩))
    set k := orderOf (n * y) with hk
    have hk3 : Nat.Coprime k 3 := by
      have h1 : k ∣ Nat.card Q := by
        rw [hk, ← Subgroup.orderOf_mk (n * y) hq']
        exact orderOf_dvd_natCard _
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        fun h3 => hQ3 (h3.trans h1))
    obtain ⟨n', hn', hpow⟩ := exists_pow_eq_mul hXN hn hy k
    have hyk : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hy⟩ : ↥X) ^ k = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have h1 : y ^ k = n'⁻¹ := by
        have h2 : n' * y ^ k = 1 := by rw [← hpow, hk, pow_orderOf_eq_one]
        exact eq_inv_of_mul_eq_one_right h2
      have h2 : y ^ k ∈ θX := hNX (Subgroup.mem_inf.mpr ⟨h1 ▸ inv_mem hn', pow_mem hy k⟩)
      obtain ⟨z, hz, hzeq⟩ := h2
      have : z = (⟨y, hy⟩ : ↥X) ^ k := Subtype.ext (by
        simp only [Subgroup.coe_subtype] at hzeq
        rw [hzeq, Subgroup.coe_pow])
      rwa [← this]
    have hy1 := eq_one_of_fixed_tripleCover hZ e hσ3 hσ1 hfix hyk hk3
    have hyθ : y ∈ θX := by
      have h1 := (QuotientGroup.eq_one_iff _).mp hy1
      exact ⟨_, h1, rfl⟩
    exact mul_mem hn (hθXN hyθ)

theorem step148PointHJQ_of (hPHJ : Step148PointHJ) : Step148PointHJQ := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb hHJ
  obtain ⟨b', d, Lb, hb'Ω, hLb, hJ2, hdA, hd1, hdc, hbbd, X, hΔ, hN, hcase⟩ := hHJ
  rcases hN with hCX | ⟨hbd, hXθ, hT, hW⟩
  · exact hPHJ G A c L h Y hY hs hYB B hB Q hQ hQY b hb hb1 hbΩ hQb
      ⟨b', d, Lb, hb'Ω, hLb, hJ2, hdA, hd1, hdc, hbbd, X, hΔ, hCX, hcase⟩
  · have hInv : Inv143Q A b d X := Or.inr ⟨hbd, hXθ, hT, hW⟩
    exact (false_of_tripleCover_A6Q h hY hYB hB hQ hQY hb hb1 hQb
      (hInv.le_normalizer h.isE27'.1.1 (hB.1 hb)) hXθ hT
      (le_sup_of_delta_eqQ h hB hQ (hQY.trans inf_le_right) hb hΔ hInv)).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
