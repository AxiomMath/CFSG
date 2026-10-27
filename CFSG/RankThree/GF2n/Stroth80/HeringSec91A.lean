module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Pts
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVNe6Om4
public import CFSG.RankThree.GF2n.Stroth80.Sec91b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem hypPlane_iff_polar91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {K : Type} [Field K] [Finite K]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u) (r : ↥(Rt M (LB M Q B) t)) :
    HypPlane Q Z B (conjSubgroup (r : G) B) t ↔
      polar (quadPlus 2 K) u ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hK : Nat.card K = Nat.card Z := P.card
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hchi := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs5.notQ hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hX := addCommutantScalar_statedOmegaPlus_two (K := K) ⟨c0, hc0, hc1⟩
  have hφ := P.range
  have hψ := P.act
  have hsing := hc.omega_singular_flag h34 hs5 hK E hQ h3 hX φ hφ ψ hψ
  have hQu := P.sing
  have hu0 := P.ne_zero
  have hBiff := P.point
  let D := hc.natCommData ht hchi.1 hchi.2
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hb₀u⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
  have hb0 : secVec ψ b₀ ≠ 0 := by rw [hb₀u]; exact hu0
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), (b : G) ∈ B → secVec ψ b ≠ 0 →
      ∀ x : Fin 2 ⊕ Fin 2 → K, pairVec D ψ b x = 1 ↔
        polar (quadPlus 2 K) (secVec ψ b) x = 0 := by
    intro b hb hb0 x
    refine hc.pairVec_eq_one_iff_of_forward ht D ψ h θ hθ hb0
      (polarBilin (quadPlus 2 K) (secVec ψ b)) ?_ x
    intro y hy
    have hg0 := E.additive_eq_zero_of_range_polar hQ h3 φ hφ (pairHom D ψ b) (hsing b hb) hb0
      (fun r hr z => by
        show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
        rw [pairVec_conj D ψ hψ hVR _ r hr z]) (x := y) hy
    exact ofMul_eq_zero.mp hg0
  constructor
  · intro hyp
    obtain ⟨ĉ, hĉ, hĉC, b, hb, hne⟩ := hyp
    refine polar_ne_zero_of_commData E hQ h3 D φ hφ ψ hψ hVR hQu hu0 hBV
      (fun b' hb' => (hBiff (secVec ψ b')).mp ⟨b', hb', rfl⟩) (fun c hcC => ?_) hĉ hĉC hb hne
    obtain ⟨c₁, hc₁, z, hz, hcz⟩ := exists_mul_of_mem_sup (fun x hx z hz => by
      have := hc.conj_Z_of_mem_Q ((hc.conj_of_mem (hc.Rt_le_M t r.2)).le hx) hz
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [this]) hcC
    have hb1 : (r : G)⁻¹ * c₁ * r ∈ B := mem_conjSubgroup.mp hc₁
    have hb1V : (r : G)⁻¹ * c₁ * r ∈ Vt M (LB M Q B) B Z t := hBV hb1
    have hc₁V : c₁ ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (hVR r.2) _).mp hb1V
      rwa [show (r : G) * ((r : G)⁻¹ * c₁ * r) * (r : G)⁻¹ = c₁ by group] at this
    obtain ⟨a, haa⟩ := (hBiff (secVec ψ ⟨_, hb1V⟩)).mp ⟨⟨_, hb1V⟩, hb1, rfl⟩
    refine ⟨a, ?_⟩
    have e1 : secVec ψ ⟨c₁, hc₁V⟩ =
        (φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ ⟨_, hb1V⟩ :=
      hψ r ⟨_, hb1V⟩ ⟨c₁, hc₁V⟩ (by group)
    have hzV : z ∈ Vt M (LB M Q B) B Z t := hZV hz
    have e2 : c = ⟨c₁, hc₁V⟩ * ⟨z, hzV⟩ := Subtype.ext hcz
    rw [e2, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero, e1, haa,
      Matrix.mulVec_smul]
  · intro hne
    have hr0 : (r : G) * (b₀ : G) * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR r.2) b₀).mp b₀.2
    set c₀ : ↥(Vt M (LB M Q B) B Z t) := ⟨(r : G) * b₀ * (r : G)⁻¹, hr0⟩ with hc₀
    have hc₀vec : secVec ψ c₀ = (φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u := by
      rw [← hb₀u]
      exact hψ r b₀ c₀ rfl
    obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ c₀)
    refine ⟨(y : G), y.2, ?_, (b₀ : G), hb₀B, ?_⟩
    · have h1 : ⁅(y : G), t⁆ * (c₀ : G)⁻¹ ∈ Z :=
        (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ c₀).mp hy
      have hc₀C : (c₀ : G) ∈ conjSubgroup (r : G) B := by
        rw [mem_conjSubgroup]
        show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) ∈ B
        rw [show (r : G)⁻¹ * ((r : G) * (b₀ : G) * (r : G)⁻¹) * (r : G) = (b₀ : G) by group]
        exact hb₀B
      have e : ⁅(y : G), t⁆ = (⁅(y : G), t⁆ * (c₀ : G)⁻¹) * (c₀ : G) := by group
      rw [e]
      exact (conjSubgroup (r : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right h1)
        (Subgroup.mem_sup_left hc₀C)
    · have h2 : pairVec D ψ b₀ (secVec ψ c₀) ≠ 1 := fun h1 => hne (by
        have := (C' b₀ hb₀B hb0 _).mp h1
        rwa [hc₀vec, hb₀u] at this)
      rwa [pairVec_eq D ψ b₀ y hy] at h2

theorem exists_plane91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {K : Type} [Field K] [Finite K]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u) :
    ∃ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t ∧
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) := by
  classical
  have hK : Nat.card K = Nat.card Z := P.card
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  obtain ⟨P', hPe⟩ := exists_hypPair hQ P.sing P.ne_zero
  have hPf0 : P'.f ≠ 0 := fun h0 => by
    have := P'.polar_ef
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  obtain ⟨w, hw, hQw⟩ := exists_perp_vector_map_ne_zero hQ h3 hPf0
  have hw' : polar (quadPlus 2 K) P'.f w = 0 := hw
  set g : Gom (quadPlus 2 K) := eichlerG (quadPlus 2 K) P'.f w with hg
  set A : StatedOmega (StatedQuadPlus 2 K) := E.equiv.symm g with hA
  obtain ⟨r, hr⟩ : ∃ r : ↥(Rt M (LB M Q B) t), φ r = (A : GL (Fin 2 ⊕ Fin 2) K) := by
    have : (A : GL (Fin 2 ⊕ Fin 2) K) ∈ φ.range := by rw [P.range]; exact A.2
    exact MonoidHom.mem_range.mp this
  have hrv : (φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u =
      eichler (quadPlus 2 K) P'.f w u := by
    have h1 := E.app A u
    rw [hA, MulEquiv.apply_symm_apply] at h1
    rw [hr]
    exact h1.symm
  have hne : polar (quadPlus 2 K) u
      ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 := by
    rw [hrv, ← hPe, polar_eichler_apply_left P'.Q_e P'.Q_f hw', P'.polar_ef]
    simpa using hQw
  have hplane := (hypPlane_iff_polar91 h34 hs P r).mpr hne
  refine ⟨r, r.2, hplane, ?_⟩
  have hL2 := sec7_conj_LomGL E φ P.range r P.root
  rw [← hc.LB_conj (hc.Rt_le_M t r.2)] at hL2
  have hrX : (φ r : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hQu' : quadPlus 2 K ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = 0 := by
    rw [E.quad_mulVec hrX]
    exact P.sing
  exact le_sup_secOmega E hQ φ P.range P.ker P.sing hQu' hne P.root hL2

end HS9


theorem sec9AExists_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hNC : Sec9NCommStatement) : Sec9AExistsStatement := by
  intro G _ _ M Q Z B hc n t hs
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  obtain ⟨r, hr, hplane, hgen⟩ := HS9.exists_plane91 h34 hs P
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs5.mem hr
  have hgen' : Rt M (LB M Q B) t = hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup r B) :=
    le_antisymm (by rw [sup_assoc]; exact hgen)
      (sup_le (sup_le (sec9_CN_le_Rt hc t) hLR) hL'R)
  have hcore := hc.sec51_core h35 hs5.mem hr
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
    (hNC G M Q Z B hc n t hs) hgen'
  have hNle : hc.CN t ≤ LB M Q B ⊔ LB M Q (conjSubgroup r B) := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hcore.1 x hx
    exact Subgroup.mul_mem_sup ha.1 hb.1
  refine ⟨r, ⟨hr, hplane, ?_⟩⟩
  rw [sup_eq_right.mpr hNle] at hgen
  exact le_antisymm hgen (sup_le hLR hL'R)

end CFSG.RankThree.GF2n.Stroth80
