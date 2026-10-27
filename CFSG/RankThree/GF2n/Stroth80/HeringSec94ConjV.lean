module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreW
public import CFSG.RankThree.GF2n.Stroth80.Sec7CardBeta
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem card_Vt_inf_Q1_plus4_91 {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u) (ht : t ∈ LB M Q B)
    {β : G} (hβ : β ∈ LB M Q B) (hβN : β ∉ hc.CN t) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc β) = Nat.card Z ^ 3 := by
  classical
  have hβM : β ∈ M := hc.LB_le_M hβ
  have hβR : β ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hβ
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥(Rt M (LB M Q B) t), (β' : G) = β := ⟨⟨β, hβR⟩, rfl⟩
  have hβ'L : β' ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t) :=
    Subgroup.mem_subgroupOf.mpr (by rw [hβ']; exact hβ)
  have hA_mem : φ β' ∈ E.LomGL u := by
    rw [← P.root]
    exact Subgroup.mem_map_of_mem φ hβ'L
  have hA1 : φ β' ≠ 1 := by
    intro h1
    have hmem : β' ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [P.ker, Subgroup.mem_subgroupOf, hβ'] at hmem
    exact hβN hmem
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨-, w, hw, hAw⟩ := (Om10.mem_LomGL_iff_eichler E).mp hA_mem
  have hne : eichler (quadPlus 2 K) u w ≠ 1 := by
    intro h
    apply hA1
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, hAw v, h]
    simp
  have hli := eichler_pair_linearIndependent P.ne_zero P.sing hne
  have hfix : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (φ β' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x = x ↔
        eichler (quadPlus 2 K) u w x = x := fun x => by rw [hAw x]
  have hι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
  have hFixA : Nat.card {x : Fin 2 ⊕ Fin 2 → K //
      (φ β' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x = x} = Nat.card K ^ 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hfix),
      card_eichler_fixed hQnd P.sing hw hli, hι]
  have hA : ∀ v w : ↥(Vt M (LB M Q B) B Z t), (w : G) = β * (v : G) * β⁻¹ →
      secVec ψ w = (φ β' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ v := by
    intro v w hvw
    exact P.act β' v w (by rw [hβ']; exact hvw)
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZW : Z ≤ Vt M (LB M Q B) B Z t ⊓ Q1 hc β := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨sec39_Z_le_Vt hz, (hc.mem_Q1_iff hβM).mpr ⟨hc.Z_le_Q hz, ?_⟩⟩
    rw [commutatorElement_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz)
      (Z.inv_mem hz)
  have hW : ∀ w : ↥(Vt M (LB M Q B) B Z t),
      (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ Q1 hc β ↔ ⁅β, (w : G)⁆ ∈ Z := by
    intro w
    constructor
    · intro hw
      exact ((hc.mem_Q1_iff hβM).mp (Subgroup.mem_inf.mp hw).2).2
    · intro hw
      exact Subgroup.mem_inf.mpr ⟨w.2, (hc.mem_Q1_iff hβM).mpr ⟨hVQ w.2, hw⟩⟩
  have hcard := card_eq_card_Z_mul_fixed (hc.Rt_normalizes_Vt ht hβR) ψ _ hA hZW inf_le_left hW
  rw [hcard, hFixA, P.card]
  ring

theorem exists_subgroup_comm_mem_Vt91 (hc : Ctx M Q Z B) {V W : Subgroup G} (hZV : Z ≤ V)
    (hVQ : V ≤ Q) (hWQ : W ≤ Q) (β : G) :
    ∃ C : Subgroup G, ∀ x : G, x ∈ C ↔ x ∈ W ∧ ⁅β, x⁆ ∈ V := by
  have hnorm : ∀ a ∈ Q, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    have e : a * v * a⁻¹ = ⁅a, v⁆ * v := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (hZV (comm_Q91 hc ha (hVQ hv))) hv
  refine ⟨{ carrier := {x | x ∈ W ∧ ⁅β, x⁆ ∈ V}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨ha, hab⟩ ⟨hb, hbb⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    have e : ⁅β, a * b⁆ = ⁅β, a⁆ * (a * ⁅β, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hab (hnorm a (hWQ ha) _ hbb)
  · refine ⟨W.one_mem, ?_⟩
    have e : ⁅β, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [e]
    exact V.one_mem
  · rintro a ⟨ha, hab⟩
    refine ⟨W.inv_mem ha, ?_⟩
    have e : ⁅β, a⁻¹⁆ = a⁻¹ * (⁅β, a⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hnorm a⁻¹ (Q.inv_mem (hWQ ha)) _ (V.inv_mem hab)

theorem exists_chiTransport91 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hχ : IsChiIso Q (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t) Z t) {β : G} (hβR : β ∈ Rt M (LB M Q B) t) :
    ∃ C : Subgroup G, Wt Q (Vt M (LB M Q B) B Z t) ≤ C ∧ C ≤ Q ∧
      (∀ x ∈ Q, x ∈ C ↔ ⁅β, x⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
      Nat.card ↥C * Nat.card ↥Z =
        Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
          Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc β) := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hβM : β ∈ M := hc.Rt_le_M t hβR
  have hβt : ⁅β⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hβR)
  obtain ⟨c1, c2, c3, c4, c5⟩ := hχ
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨C, hC⟩ := exists_subgroup_comm_mem_Wt hc hVQ β
  have hCQ : C ≤ Q := fun x hx => ((hC x).mp hx).1
  have hWC : Wt Q (Vt M (LB M Q B) B Z t) ≤ C := by
    intro w hw
    refine (hC w).mpr ⟨hw.1, ?_⟩
    have hβW := conj_mem_Wt (hc.hyp.Q_normal.2 hβM) (hc.Rt_normalizes_Vt ht hβR) hw
    rw [commutatorElement_def]
    exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem hβW
      ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hw)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZU : Z ≤ Vt M (LB M Q B) B Z t ⊓ Q1 hc β := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hZV hz, (hc.mem_Q1_iff hβM).mpr ⟨hc.Z_le_Q hz, ?_⟩⟩
    rw [commutatorElement_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz)
      (Z.inv_mem hz)
  have hVQ' : Vt M (LB M Q B) B Z t ⊓ Q1 hc β ≤ Q :=
    fun x hx => hVQ (Subgroup.mem_inf.mp hx).1
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t ⊓ Q1 hc β)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ' hv)))
  have hchiC : IsChiIso C (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t ⊓ Q1 hc β) Z t := by
    refine ⟨fun x hx => ?_, fun u hu => ?_, fun x hx y hy => c3 x (hCQ hx) y (hCQ hy),
      fun x hx => c4 x (hCQ hx), fun r hr x hx => c5 r hr x (hCQ hx)⟩
    · have hxQ : x ∈ Q := hCQ hx
      have hyt : ⁅⁅β, x⁆, t⁆ ∈ Z :=
        (c4 _ (comm_left_mem_Q_of_mem_M hc hβM hxQ)).mpr ((hC x).mp hx).2
      have hb : ⁅β, ⁅x, t⁆⁆ ∈ Z :=
        (mem_iff_of_mul_inv_mem (comm_comm_congr_mod_Z hc htM hβM hβt hxQ)).mp hyt
      exact Subgroup.mem_inf.mpr ⟨c1 x hxQ, (hc.mem_Q1_iff hβM).mpr ⟨hc.comm_mem_Q htM hxQ, hb⟩⟩
    · obtain ⟨huV, huQ1⟩ := Subgroup.mem_inf.mp hu
      obtain ⟨-, hub⟩ := (hc.mem_Q1_iff hβM).mp huQ1
      obtain ⟨x, hxQ, hxu⟩ := c2 u huV
      obtain ⟨z, hz, hzeq⟩ : ∃ z ∈ Z, ⁅x, t⁆ = z * u := ⟨⁅x, t⁆ * u⁻¹, hxu, by simp⟩
      have hb : ⁅β, ⁅x, t⁆⁆ ∈ Z := by
        rw [hzeq]
        have e : ⁅β, z * u⁆ = β * z * β⁻¹ * ⁅β, u⁆ * z⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem (Z.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz) hub)
          (Z.inv_mem hz)
      have hyt : ⁅⁅β, x⁆, t⁆ ∈ Z :=
        (mem_iff_of_mul_inv_mem (comm_comm_congr_mod_Z hc htM hβM hβt hxQ)).mpr hb
      exact ⟨x, (hC x).mpr ⟨hxQ, (c4 _ (comm_left_mem_Q_of_mem_M hc hβM hxQ)).mp hyt⟩, hxu⟩
  exact ⟨C, hWC, hCQ, fun x hx => ⟨fun h => ((hC x).mp h).2, fun h => (hC x).mpr ⟨hx, h⟩⟩,
    card_mul_card_of_isChiIso hchiC hWC hZU⟩

end HS9

theorem step94ConjV_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) : Step94ConjVStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs V W hV hW Z0 hZ0 s hsZ x hxL hxN hconj
  subst hV hW
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  obtain ⟨-, g, hgM, hgq⟩ := hconj
  have hxe : x = (x * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) := by group
  have hsQ : s ∉ Q := by
    intro hsQ
    apply hxN
    have h1 : g * s * g⁻¹ ∈ Q := HS9.conj_mem_Q91 hc hgM hsQ
    have hxQ : x ∈ Q := by
      rw [hxe]
      exact Q.mul_mem hgq h1
    exact sec9_Q_le_CN hc ht hxQ
  have hUs : Ut Q Z s = Vt M (LB M Q B) B Z t := HS9.centre_clause91 h34 h91b hs hr hZ0 hsZ hsQ
  have hy0 : g * s * g⁻¹ ∈ H0 M Z := hc.conj_mem_H0 hgM (hc.Rt_le_H0 t hsR)
  have hUx : Nat.card ↥(Ut Q Z x) = Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [hxe, Ut_mul_Q hc hy0 hgq, card_Ut_conj hc hgM s, hUs]
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun v hv =>
    ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
      hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hβV : ∀ y ∈ Vt M (LB M Q B) B Z t, x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hxR) y).mp hy
  have hβW : ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun y hy => conj_mem_Wt (hc.hyp.Q_normal.2 hxM) (hc.Rt_normalizes_Vt ht hxR) hy
  obtain ⟨C₂, hC₂⟩ := HS9.exists_subgroup_comm_mem_Vt91 hc hZV hVQ hWQ x
  have hC₂W : C₂ ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun y hy => ((hC₂ y).mp hy).1
  have hVC₂ : Vt M (LB M Q B) B Z t ≤ C₂ := fun v hv => (hC₂ v).mpr ⟨hVW hv, by
    have e : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hβV v hv) ((Vt M (LB M Q B) B Z t).inv_mem hv)⟩
  have hχ := stroth91c_of_34 h34 G M Q Z B hc n t hs (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  obtain ⟨C₃, hWC₃, hC₃Q, hC₃iff, hC₃card⟩ := HS9.exists_chiTransport91 hc ht hχ hxR
  have hfilt := card_Q1_mul_le_filtration hc hxM hZV hVW hWQ hβV hβW hVC₂ hC₂W
    (fun y hy => ⟨fun h => ((hC₂ y).mp h).2, fun h => (hC₂ y).mpr ⟨hy, h⟩⟩) hWC₃ hC₃Q hC₃iff
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have h3 := HS9.card_Vt_inf_Q1_plus4_91 P ht hxL hxN
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hWpos : 0 < Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := Nat.card_pos
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs5.width
  have hVc : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 5 := hs.card_V
  have hWc : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * n - 3) :=
    hs.card_W h34
  have hn3 : 2 < n := hs5.n_gt
  have hQ1Q : Q1 hc x ≤ Q := fun y hy => hy.1
  haveI : (Z.subgroupOf (Ut Q Z x)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q hxM hv)))
  have hQ1U : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc x) * Nat.card ↥(Ut Q Z x) :=
    card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut hxL) hQ1Q (le_sup_right : Z ≤ Ut Q Z x)
  have h5 : 0 < Nat.card Z ^ 5 := by positivity
  have hQ1 : Nat.card ↥(Q1 hc x) = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := by
    have h := hQ1U
    rw [hUx, hVc, hQc] at h
    have e1 : Nat.card Z ^ (2 * n - 3) * Nat.card Z ^ 5 =
        Nat.card Z ^ (2 * n + 1) * Nat.card Z := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [hWc]
    refine Nat.eq_of_mul_eq_mul_right h5 ?_
    rw [e1]
    exact h.symm
  have hC3 : Nat.card ↥C₃ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 2 := by
    have h := hC₃card
    rw [h3] at h
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [h]
    ring
  have hle : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) ≤ Nat.card ↥C₂ := by
    have hpos : 0 < Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 *
          Nat.card (Wt Q (Vt M (LB M Q B) B Z t))
        = Nat.card ↥(Q1 hc x) * Nat.card (Vt M (LB M Q B) B Z t) *
            Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := by rw [hQ1, hVc]
      _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc x) * Nat.card ↥C₂ * Nat.card ↥C₃ := hfilt
      _ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 * Nat.card ↥C₂ := by
        rw [h3, hC3]
        ring
  have hCW : C₂ = Wt Q (Vt M (LB M Q B) B Z t) := Subgroup.eq_of_le_of_card_ge hC₂W hle
  intro w hwW
  have hwC : w ∈ C₂ := by rw [hCW]; exact hwW
  exact ((hC₂ w).mp hwC).2

end CFSG.RankThree.GF2n.Stroth80
