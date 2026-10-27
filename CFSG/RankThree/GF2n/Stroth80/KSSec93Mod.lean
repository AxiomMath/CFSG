module

public import CFSG.RankThree.GF2n.Stroth80.KSSec93Grp
public import CFSG.RankThree.GF2n.Stroth80.KSSec93Vec
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CTypeA
import CFSG.RankThree.GF2n.Stroth80.KSSec93LA
import CFSG.RankThree.GF2n.Stroth80.KSSec93Six
import CFSG.RankThree.GF2n.Stroth80.KSSec93Hom
import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
import CFSG.RankThree.GF2n.Stroth80.Sec7CardBeta
import CFSG.RankThree.GF2n.Stroth80.HeringSec95DLin
import CFSG.CGT.Timmesfeld75.Sec3Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Module QuadraticMap
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace KS93

section Coord

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] [CharP K 2]
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal] {K' : Type} [Field K'] [Finite K']
  {γ : G → K'} {M₀ : Tim79.QuadModel Q Z K' γ} {θ : K' ≃+* K}

theorem vecOf_mulVec (C : HS9.Coord95 hc t K) (hVD : VecData M₀ (Vt M (LB M Q B) B Z t) C.ψ θ)
    (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (ht : t ∈ LB M Q B) (g : ↥(Rt M (LB M Q B) t)) {v : M₀.E}
    (hv : v ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ v ∈ M₀.img (Vt M (LB M Q B) B Z t) ∧
      vecOf M₀ C.ψ (φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ v) =
        (C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ vecOf M₀ C.ψ v := by
  obtain ⟨w, hwV, hwQ, rfl⟩ := M₀.mem_img.mp hv
  have hgw : (g : G) * w * (g : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht g.2) w).mp hwV
  have hπ : φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ (M₀.π w) = M₀.π ((g : G) * w * (g : G)⁻¹) :=
    (hφπ ⟨g, hc.Rt_le_H0 t g.2⟩ w hwQ).symm
  rw [hπ]
  refine ⟨M₀.pi_mem_img hgw (hVD.le hgw), ?_⟩
  have h1 : vecOf M₀ C.ψ (M₀.π ((g : G) * w * (g : G)⁻¹)) = secVec C.ψ ⟨_, hgw⟩ :=
    hVD.vecOf_pi ⟨_, hgw⟩
  have h2 : vecOf M₀ C.ψ (M₀.π w) = secVec C.ψ ⟨w, hwV⟩ := hVD.vecOf_pi ⟨w, hwV⟩
  rw [h1, h2]
  exact C.hψ g ⟨w, hwV⟩ ⟨_, hgw⟩ rfl

theorem exists_point (C : HS9.Coord95 hc t K) (hVD : VecData M₀ (Vt M (LB M Q B) B Z t) C.ψ θ)
    (ht : t ∈ LB M Q B) {p : Fin 2 ⊕ Fin 2 → K} (hp0 : p ≠ 0) (hpQ : quadPlus 2 K p = 0) :
    ∃ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ conjSubgroup ρ B, ∃ c : K',
      M₀.π x = c • vecInv M₀ C.ψ p := by
  obtain ⟨A, hA, hAu⟩ := C.E.exists_mulVec_eq (nondegenerate_polarBilin_quadPlus 2 K)
    (P := plusPair K 0) (P' := plusPair K 1) (plusPair_orth (by decide)) C.hu0 hp0
    (by rw [C.hQu, hpQ])
  obtain ⟨ρ, hρ⟩ : A ∈ C.φ.range := by
    rw [C.hφ]
    exact hA
  refine ⟨ρ, ρ.2, fun x hx => ?_⟩
  rw [mem_conjSubgroup] at hx
  have hbV : (ρ : G)⁻¹ * x * ρ ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hx
  have hxV : x ∈ Vt M (LB M Q B) B Z t := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht ρ.2) _).mp hbV
    rwa [show (ρ : G) * ((ρ : G)⁻¹ * x * ρ) * (ρ : G)⁻¹ = x by group] at h1
  obtain ⟨c, hc'⟩ := (C.hBiff (secVec C.ψ ⟨_, hbV⟩)).mp ⟨⟨_, hbV⟩, hx, rfl⟩
  have hsec : secVec C.ψ ⟨x, hxV⟩ = c • p := by
    have h1 : secVec C.ψ ⟨x, hxV⟩ =
        (C.φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨_, hbV⟩ :=
      C.hψ ρ ⟨_, hbV⟩ ⟨x, hxV⟩ (by
        show x = (ρ : G) * ((ρ : G)⁻¹ * x * ρ) * (ρ : G)⁻¹
        group)
    rw [h1, hc', Matrix.mulVec_smul, hρ, hAu]
  refine ⟨θ.symm c, ?_⟩
  have h2 : M₀.π x = vecInv M₀ C.ψ (secVec C.ψ ⟨x, hxV⟩) :=
    (vecInv_secVec C.ψ hVD.le ⟨x, hxV⟩).symm
  rw [h2, hsec, ← hVD.vecInv_smul, RingEquiv.apply_symm_apply]

theorem exists_pairing (hKq : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (C : HS9.Coord95 hc t K)
    (hVD : VecData M₀ (Vt M (LB M Q B) B Z t) C.ψ θ) (ht : t ∈ LB M Q B)
    (φ₀ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K'] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ₀ m (M₀.π x))
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ₀ m e) = M₀.Qf e) (Φ : M₀.E →ₗ[K'] M₀.E)
    (hrange : ∀ e, e ∈ LinearMap.range Φ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hsa : ∀ e e', M₀.B (Φ e) e' = M₀.B e (Φ e'))
    (hcomm : ∀ (g : ↥(Rt M (LB M Q B) t)) e,
      Φ (φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ e) = φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ (Φ e)) :
    ∃ c : K, c ≠ 0 ∧ ∀ e b,
      θ (M₀.B e (vecInv M₀ C.ψ b)) = c * polar (quadPlus 2 K) (vecOf M₀ C.ψ (Φ e)) b := by
  classical
  have hQ : HS9.IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hVQ := hVD.le
  have hΦV : ∀ e, Φ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun e =>
    (hrange _).mp (LinearMap.mem_range_self Φ e)
  let κ : M₀.E →+ (Fin 2 ⊕ Fin 2 → K) :=
    AddMonoidHom.mk' (fun e => vecOf M₀ C.ψ (Φ e)) fun e e' => by
      show vecOf M₀ C.ψ (Φ (e + e')) = vecOf M₀ C.ψ (Φ e) + vecOf M₀ C.ψ (Φ e')
      rw [map_add]
      exact hVD.vecOf_add (hΦV e) (hΦV e')
  have hκ : ∀ e, κ e = vecOf M₀ C.ψ (Φ e) := fun e => rfl
  have hκs : Function.Surjective κ := fun b => by
    obtain ⟨e, he⟩ := LinearMap.mem_range.mp ((hrange _).mpr (vecInv_mem_img C.ψ hVQ b))
    exact ⟨e, by rw [hκ, he, hVD.vecOf_vecInv]⟩
  let act : ↥(Rt M (LB M Q B) t) → M₀.E →+ M₀.E := fun g =>
    (φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ : M₀.E →ₗ[K'] M₀.E).toAddMonoidHom
  have hact : ∀ g e, act g e = φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ e := fun g e => rfl
  have hκact : ∀ g e,
      κ (act g e) = (C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ κ e := fun g e => by
    rw [hact, hκ, hκ, hcomm]
    exact (vecOf_mulVec C hVD φ₀ hφπ ht g (hΦV e)).2
  have hvecInv : ∀ g b, vecInv M₀ C.ψ ((C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b) =
      φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ (vecInv M₀ C.ψ b) := fun g b => by
    obtain ⟨hmem, heq⟩ := vecOf_mulVec C hVD φ₀ hφπ ht g (vecInv_mem_img C.ψ hVQ b)
    rw [hVD.vecOf_vecInv] at heq
    rw [← heq, hVD.vecInv_vecOf hmem]
  let Pf : M₀.E → (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K := fun e =>
    { toFun := fun b => θ (M₀.B e (vecInv M₀ C.ψ b))
      map_add' := fun b b' => by
        simp only [vecInv_add C.ψ hVQ, map_add]
      map_smul' := fun c b => by
        obtain ⟨c', rfl⟩ := θ.surjective c
        simp only [hVD.vecInv_smul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply] }
  let P : M₀.E →+ ((Fin 2 ⊕ Fin 2 → K) →ₗ[K] K) := AddMonoidHom.mk' Pf fun e e' =>
    LinearMap.ext fun b => by
      show θ (M₀.B (e + e') (vecInv M₀ C.ψ b)) =
        θ (M₀.B e (vecInv M₀ C.ψ b)) + θ (M₀.B e' (vecInv M₀ C.ψ b))
      rw [map_add, LinearMap.add_apply, map_add]
  have hP : ∀ e b, P e b = θ (M₀.B e (vecInv M₀ C.ψ b)) := fun e b => rfl
  have hPact : ∀ g e b,
      P (act g e) ((C.φ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ b) = P e b := by
    intro g e b
    rw [hP, hP, hact, hvecInv, hQ.B_iso (φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩) (hφiso _)]
  have hPker : ∀ e, κ e = 0 → P e = 0 := fun e he => by
    rw [hκ, hVD.vecOf_eq_zero_iff (hΦV e)] at he
    refine LinearMap.ext fun b => ?_
    rw [hP, LinearMap.zero_apply]
    obtain ⟨f, hf⟩ := LinearMap.mem_range.mp ((hrange _).mpr (vecInv_mem_img C.ψ hVQ b))
    rw [← hf, ← hsa, he, map_zero, LinearMap.zero_apply, map_zero]
  obtain ⟨c, hcP⟩ := KS93.exists_eq_smul_polar hKq C.E C.φ C.hφ act κ hκs hκact P hPact hPker
  refine ⟨c, ?_, fun e b => hcP e b⟩
  rintro rfl
  apply C.hu0
  have h0 : ∀ e, M₀.B e (vecInv M₀ C.ψ C.u) = 0 := fun e => by
    have h1 := hcP e C.u
    rw [zero_mul, hP] at h1
    exact (map_eq_zero_iff θ θ.injective).mp h1
  have h1 : vecInv M₀ C.ψ C.u = 0 := M₀.nondeg _ fun f => by
    rw [M₀.B_comm, h0 f, neg_zero]
  exact vecInv_injective (M₀ := M₀) C.ψ hVQ (by rw [h1, vecInv_zero C.ψ hVQ])

end Coord

variable {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {s z : G}

namespace Hyp

variable (H : Hyp hc n t r Z0 s z)
include H

theorem le_QB_and_conj_le_Wt (h34 : Stroth34Statement) :
    Vt M (LB M Q B) B Z t ≤ QB (conjSubgroup z⁻¹ B) ∧
      conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  classical
  have hs5 := H.hs.toSec5
  have ht : t ∈ LB M Q B := H.t_mem
  have hzi : z⁻¹ ∈ M := M.inv_mem H.z_mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hcD : Ctx M Q Z (conjSubgroup z⁻¹ B) := H.hcD
  obtain ⟨K, fK, finK, hch, hnrm, ⟨C⟩⟩ := HS9.exists_coord95 h34 H.hs H.hr
  have hKq : ∃ c : K, c ≠ 0 ∧ c ≠ 1 :=
    exists_ne_zero_ne_one_of_nat_card_ge_four (by rw [C.hK]; exact hc.hyp.q4)
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht C.hK
    (addCommutantScalar_statedOmegaPlus_two hKq) C.φ C.hφ C.ψ C.hψ
  obtain ⟨φ₀, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have hVD : VecData M₀ (Vt M (LB M Q B) B Z t) C.ψ θ :=
    ⟨hVQ, fun c e he => hc.smul_mem_img_Vt h t c he, hθ⟩
  have hQ : HS9.IsQuadSpace M₀.B M₀.Qf := ⟨M₀.alt, M₀.nondeg, M₀.Qf_add⟩
  have hnoD : NoA2 Q Z (LB M Q (conjSubgroup z⁻¹ B)) := by
    rw [hc.LB_conj hzi]
    exact sec7ctr_NoA2_conj hc hzi hs5.noA2
  have hLD : Nat.card (LB M Q (conjSubgroup z⁻¹ B)) = Nat.card Q * Nat.card Z ^ (n - 1) := by
    rw [hc.LB_conj hzi, card_conjSubgroup]
    exact (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
  obtain ⟨U, hUmem, hUdim, hUperp, hUsing⟩ := hcD.lagr hs5.width hs5.n_gt hnoD h
  obtain ⟨d, hd0, hds, hdX, hdcent, -⟩ := hcD.dictB h
  have hUiso : ∀ u ∈ U, ∀ u' ∈ U, M₀.B u u' = 0 := fun u hu u' hu' => by
    have h1 := hQ.Qf_add u u'
    rw [hUsing _ (U.add_mem hu hu'), hUsing u hu, hUsing u' hu', zero_add, zero_add] at h1
    exact h1.symm
  have hsH : s ∈ H0 M Z := hc.LB_le_H0 H.s_mem_LB
  have hs2 : s ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB H.s_mem_LB
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : M₀.E →ₗ[GaloisField 2 nn] M₀.E,
      Φ = (φ₀ ⟨s, hsH⟩ : M₀.E →ₗ[GaloisField 2 nn] M₀.E) - 1 := ⟨_, rfl⟩
  have hΦe : ∀ e, Φ e = φ₀ ⟨s, hsH⟩ e - e := fun e => by
    rw [hΦ]
    rfl
  have hrange : ∀ e, e ∈ LinearMap.range Φ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun e => by
    rw [hΦ]
    exact mem_range_sub_one_iff hc φ₀ hφπ hφQ ⟨s, hsH⟩ hs2
      (H.hC.2.2 s H.s_mem H.s_not_mem_Q) e
  have hrangeEq : LinearMap.range Φ = imgSub M₀ (Vt M (LB M Q B) B Z t) hVD.smul :=
    SetLike.ext fun e => hrange e
  have hS2 : ∀ e, φ₀ ⟨s, hsH⟩ (φ₀ ⟨s, hsH⟩ e) = e := fun e => by
    have h1 : φ₀ ⟨s, hsH⟩ * φ₀ ⟨s, hsH⟩ = 1 := by
      rw [← map_mul, hφQ]
      show s * s ∈ Q
      rw [← pow_two]
      exact hs2
    have h2 := congrArg (fun f : M₀.E ≃ₗ[GaloisField 2 nn] M₀.E => f e) h1
    simpa using h2
  have hsa : ∀ e e', M₀.B (Φ e) e' = M₀.B e (Φ e') := fun e e' => by
    rw [hΦ]
    exact HS9.selfAdj_sub_one95 hQ _ (hφiso ⟨s, hsH⟩) hS2 e e'
  have hconjQ : ∀ x ∈ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t), x ∈ Q := fun x hx => by
    rw [mem_conjSubgroup, inv_inv] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hzi) _).mp (hVQ hx)
    rwa [show z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x by group] at h1
  have hkill : ∀ x ∈ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t), Φ (M₀.π x) = 0 :=
    fun x hx => by
      obtain ⟨hcQ, hcπ⟩ := pi_commutator hc φ₀ hφπ ⟨s, hsH⟩ (hconjQ x hx)
      rw [hΦe, ← hcπ]
      exact (M₀.π_ker _ hcQ).mpr (H.comm_conj hx)
  have hΦd : Φ d = 0 := by
    obtain ⟨x, hxD, -, rfl⟩ := M₀.mem_img.mp ((hdX d).mpr ⟨1, (one_smul _ d).symm⟩)
    exact hkill x (conjSubgroup_mono (hc.B_le_Vt ht) hxD)
  have hW : conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun x hx => by
      refine (M₀.mem_img_iff (Z_le_Wt_of_le_Q hc hVQ) (hconjQ x hx)).mp ?_
      refine (mem_img_Wt_iff M₀ h.reg hVQ).mpr fun v hv => ?_
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp ((hrange v).mpr hv)
      rw [← hsa, hkill x hx, map_zero, LinearMap.zero_apply]
  have hΦU : ∀ e ∈ U, Φ e ∈ U := fun e he => by
    obtain ⟨x, hx, hxQ, rfl⟩ := M₀.mem_img.mp ((hUmem e).mpr he)
    obtain ⟨hcQ, hcπ⟩ := pi_commutator hc φ₀ hφπ ⟨s, hsH⟩ hxQ
    rw [hΦe, ← hcπ]
    refine (hUmem _).mp (M₀.pi_mem_img ?_ hcQ)
    rw [commutatorElement_def]
    exact (Q ⊓ QB (conjSubgroup z⁻¹ B)).mul_mem (H.conj_QQBD hx)
      ((Q ⊓ QB (conjSubgroup z⁻¹ B)).inv_mem hx)
  have hmapV : U.map Φ ⊓ imgSub M₀ (Vt M (LB M Q B) B Z t) hVD.smul = U.map Φ :=
    inf_eq_left.mpr fun x hx => (hrange x).mp (LinearMap.map_le_range hx)
  have hdV : d ∉ M₀.img (Vt M (LB M Q B) B Z t) := fun hd => H.not_D_le fun y hy => by
    have hyQ : y ∈ Q := hcD.le hy
    obtain ⟨c, hc'⟩ := (hdX _).mp (M₀.pi_mem_img hy hyQ)
    have h1 : M₀.π y ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
      rw [hc']
      exact hc.smul_mem_img_Vt h t c hd
    exact (M₀.mem_img_iff hZV hyQ).mp h1
  have hΦcomm : ∀ g : H0 M Z, ⁅s, (g : G)⁆ ∈ Q → ∀ e, Φ (φ₀ g e) = φ₀ g (Φ e) :=
    fun g hg e => by
      have h1 := phi_mul_comm hφQ ⟨s, hsH⟩ g hg
      have h2 := congrArg (fun f : M₀.E ≃ₗ[GaloisField 2 nn] M₀.E => f e) h1
      simp only [LinearEquiv.mul_apply] at h2
      rw [hΦe, hΦe, h2, map_sub]
  have hRcomm : ∀ (g : ↥(Rt M (LB M Q B) t)) e,
      Φ (φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ e) = φ₀ ⟨g, hc.Rt_le_H0 t g.2⟩ (Φ e) := fun g e =>
    hΦcomm _ (((H.hZ0 s).mp H.s_mem).2 g g.2) e
  obtain ⟨c, hc0, hcP⟩ := exists_pairing hKq C hVD ht φ₀ hφπ hφiso Φ hrange hsa hRcomm
  have hYbot : hVD.trSub (U.map Φ) = ⊥ := by
    refine eq_bot_of_singular
      (hVD.trSub_mono (Submodule.map_le_iff_le_comap.mpr fun e he => hΦU e he)) ?_ ?_ ?_
    ·
      intro y hy u hu
      rw [hVD.mem_trSub] at hy hu
      obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.mp hy
      have h1 := hcP f u
      rw [hfy, hVD.vecOf_vecInv, hUiso f hf _ hu, map_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hc0
    ·
      have horth : M₀.B.orthogonal U = U := by
        refine le_antisymm (fun e he => hUperp e fun u hu => ?_) (fun e he => ?_)
        · have h0 : M₀.B u e = 0 := LinearMap.BilinForm.isOrtho_def.mp
            ((LinearMap.BilinForm.mem_orthogonal_iff.mp he) u hu)
          rw [M₀.B_comm, h0, neg_zero]
        · exact LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu =>
            LinearMap.BilinForm.isOrtho_def.mpr (hUiso u hu e he)
      have h4 : finrank (GaloisField 2 nn) (LinearMap.range Φ) = 4 := by
        have h1 := hVD.finrank_trSub ⊤
        have htop : hVD.trSub ⊤ = ⊤ :=
          eq_top_iff.mpr fun b _ => hVD.mem_trSub.mpr Submodule.mem_top
        rw [htop, finrank_top, top_inf_eq, ← hrangeEq] at h1
        rw [← h1]
        simp
      have hsum := HS9.finrank_range_eq_inf_orth_add95 hQ Φ hsa U
      rw [horth, h4] at hsum
      rw [hVD.finrank_trSub, hVD.finrank_trSub, hmapV, ← hrangeEq, inf_comm]
      omega
    ·
      intro p hp hp0 hpQ y hy
      rw [hVD.mem_trSub] at hp hy
      obtain ⟨e, heU, hey⟩ := Submodule.mem_map.mp hy
      obtain ⟨ρ, hρ, hρB⟩ := exists_point C hVD ht hp0 hpQ
      have hρM : ρ ∈ M := hc.Rt_le_M t hρ
      have hcρ : Ctx M Q Z (conjSubgroup ρ B) := hc.conj_of_mem hρM
      have hpv : vecInv M₀ C.ψ p ∈ M₀.img (Vt M (LB M Q B) B Z t) := vecInv_mem_img C.ψ hVQ p
      have hpd : ∀ c' : GaloisField 2 nn, vecInv M₀ C.ψ p ≠ c' • d := fun c' hc' => by
        by_cases hc0' : c' = 0
        · apply hp0
          apply vecInv_injective (M₀ := M₀) C.ψ hVQ
          rw [hc', hc0', zero_smul, vecInv_zero C.ψ hVQ]
        · apply hdV
          have h1 := hc.smul_mem_img_Vt h t c'⁻¹ hpv
          rwa [hc', smul_smul, inv_mul_cancel₀ hc0', one_smul] at h1
      have hfix : ∀ (l : G) (hl : l ∈ H0 M Z), l ∈ LB M Q (conjSubgroup z⁻¹ B) →
          φ₀ ⟨l, hl⟩ (vecInv M₀ C.ψ p) = vecInv M₀ C.ψ p → φ₀ ⟨l, hl⟩ (Φ e) = Φ e := by
        intro l hl hlD hlp
        have hlM : l ∈ M := (Subgroup.mem_inf.mp hl).1
        have hle : conjSubgroup l (conjSubgroup ρ B) ≤ conjSubgroup ρ B ⊔ Z := by
          intro y' hy'
          rw [mem_conjSubgroup] at hy'
          have hxQ : l⁻¹ * y' * l ∈ Q := hcρ.le hy'
          obtain ⟨c', hc'⟩ := hρB _ hy'
          have e2 : l * (l⁻¹ * y' * l) * l⁻¹ = y' := by group
          have hy'Q : y' ∈ Q := by
            have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) _).mp hxQ
            rwa [e2] at h1
          have h1 : M₀.π (l * (l⁻¹ * y' * l) * l⁻¹) = φ₀ ⟨l, hl⟩ (M₀.π (l⁻¹ * y' * l)) :=
            hφπ ⟨l, hl⟩ _ hxQ
          rw [e2, hc', map_smul, hlp, ← hc'] at h1
          have hxy : (l⁻¹ * y' * l)⁻¹ * y' ∈ Z := (M₀.pi_eq_iff hxQ hy'Q).mp h1.symm
          have e1 : y' = (l⁻¹ * y' * l) * ((l⁻¹ * y' * l)⁻¹ * y') := by group
          rw [e1]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy') (Subgroup.mem_sup_right hxy)
        have hLρ : conjSubgroup l (LB M Q (conjSubgroup ρ B)) = LB M Q (conjSubgroup ρ B) :=
          hcρ.conj_LB_eq_of_le_sup_Z hlM hle
        have hcomm1 : ⁅l, s⁆ ∈ LB M Q (conjSubgroup z⁻¹ B) := by
          have h1 : s * l⁻¹ * s⁻¹ ∈ LB M Q (conjSubgroup z⁻¹ B) := by
            rw [← H.conj_LD, mem_conjSubgroup, show s⁻¹ * (s * l⁻¹ * s⁻¹) * s = l⁻¹ by group]
            exact (LB M Q (conjSubgroup z⁻¹ B)).inv_mem hlD
          rw [show ⁅l, s⁆ = l * (s * l⁻¹ * s⁻¹) by rw [commutatorElement_def]; group]
          exact Subgroup.mul_mem _ hlD h1
        have hcomm2 : ⁅l, s⁆ ∈ LB M Q (conjSubgroup ρ B) := by
          have h1 : s ∈ LB M Q (conjSubgroup ρ B) := by
            rw [hc.LB_conj hρM]
            exact H.s_mem_LB_conj hρ
          have h2 : l * s * l⁻¹ ∈ LB M Q (conjSubgroup ρ B) := by
            rw [← hLρ, mem_conjSubgroup, show l⁻¹ * (l * s * l⁻¹) * l = s by group]
            exact h1
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1)
        have hlsQ : ⁅l, s⁆ ∈ Q := by
          rw [← H.inf_LB_conj_eq_Q hρ]
          exact ⟨hcomm1, hcomm2⟩
        have hcomm : ∀ e', Φ (φ₀ ⟨l, hl⟩ e') = φ₀ ⟨l, hl⟩ (Φ e') := by
          refine hΦcomm _ ?_
          rw [← commutatorElement_inv]
          exact Q.inv_mem hlsQ
        obtain ⟨-, hTe⟩ := hcD.LB_act_fix_line h hdX hlD
          (T := (φ₀ ⟨l, hl⟩ : M₀.E →ₗ[GaloisField 2 nn] M₀.E)) fun x hx => hφπ ⟨l, hl⟩ x hx
        obtain ⟨c', hc'⟩ := hTe e ((hUmem e).mpr heU)
        have h1 : φ₀ ⟨l, hl⟩ e = e + c' • d := by
          have h2 : φ₀ ⟨l, hl⟩ e - e = c' • d := hc'
          rw [← h2]
          abel
        rw [← hcomm, h1, map_add, map_smul, hΦd, smul_zero, add_zero]
      obtain ⟨a, b, hab⟩ := fix_stab_eq_add hcD hs5.n_gt hnoD hLD h φ₀ hφπ hφQ hφiso
        (fun e => (hUmem e).symm) hUdim hUsing
        (fun e he => hUperp e fun u hu => by rw [M₀.B_comm, he u hu, neg_zero])
        hd0 hds hdX hdcent hp hpd (hΦU e heU) hfix
      refine ⟨θ a, ?_⟩
      have hb : b = 0 := by
        by_contra hb0
        apply hdV
        have h1 : b • d ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
          have h2 : b • d = Φ e - a • vecInv M₀ C.ψ p := by
            rw [hab]
            abel
          rw [h2]
          exact (M₀.img _).sub_mem ((hrange _).mp (LinearMap.mem_range_self Φ e))
            (hc.smul_mem_img_Vt h t a hpv)
        have h3 := hc.smul_mem_img_Vt h t b⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h3
      rw [hb, zero_smul, add_zero, ← hVD.vecInv_smul] at hab
      exact vecInv_injective (M₀ := M₀) C.ψ hVQ (by rw [← hey, hab])
  have hΦU0 : ∀ e ∈ U, Φ e = 0 := by
    have h1 : finrank (GaloisField 2 nn) ↥(U.map Φ) = 0 := by
      have h2 := hVD.finrank_trSub (U.map Φ)
      rw [hYbot, finrank_bot, hmapV] at h2
      exact h2.symm
    have h3 : U.map Φ = ⊥ := Submodule.finrank_eq_zero.mp h1
    intro e he
    have h4 : Φ e ∈ U.map Φ := Submodule.mem_map_of_mem he
    rw [h3] at h4
    exact (Submodule.mem_bot _).mp h4
  have hVU : ∀ v ∈ M₀.img (Vt M (LB M Q B) B Z t), v ∈ U := fun v hv => by
    obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp ((hrange v).mpr hv)
    refine hUperp _ fun u hu => ?_
    rw [hsa, hΦU0 u hu, map_zero]
  refine ⟨fun x hx => ?_, hW⟩
  have hxQ : x ∈ Q := hVQ hx
  have h1 : M₀.π x ∈ M₀.img (Q ⊓ QB (conjSubgroup z⁻¹ B)) :=
    (hUmem _).mpr (hVU _ (M₀.pi_mem_img hx hxQ))
  exact ((M₀.mem_img_iff (le_inf hc.Z_le_Q hcD.Z_le_QB.1) hxQ).mp h1).2

end Hyp

end KS93

end CFSG.RankThree.GF2n.Stroth80
