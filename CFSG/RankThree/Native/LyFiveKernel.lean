module

public import CFSG.RankThree.Native.LyCertifiedOrder
public import CFSG.RankThree.CentralExtension.ScalarNormalizerKernel
public import CFSG.RankThree.Native.LyFiveSpec

public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup CFSG.RankThree.CentralExtension
open scoped Matrix

@[expose] def fiveBSq {G : Type*} [Group G] (a b : G) : closure ({a, b} : Set G) :=
  ⟨b ^ 2, FiveMRel.b_pow_mem 2⟩

namespace FiveMRel

variable {G : Type*} [Group G] {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 5} {a b : G}
  {Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)} {αc βc : Fin 4 → ZMod 5}
  (h : FiveMRel x v ω a b Ab Bb αc βc)
include h

variable {n : ℕ} {par : ℕ → ℕ} {gen : ℕ → Bool} {t : ℕ → G}
  {tb : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 5)} {next : ℕ → Bool → ℕ}
  {qc : ℕ → Bool → ZMod 5 × (Fin 4 → ZMod 5)}

theorem rhoMat_bSq : h.rhoMat (fiveBSq a b) = Bb * Bb := by
  have e : fiveBSq a b = (⟨b, b_mem⟩ : closure ({a, b} : Set G)) * ⟨b, b_mem⟩ :=
    Subtype.ext (pow_two b)
  rw [e, h.rhoMat_mul, h.rhoMat_b]

theorem cert_mk_comm_of_scalar (hc : CosetCert x v a b Ab Bb n par gen t tb next qc)
    {g : closure ({a, b} : Set G)} {r : ZMod 5}
    (hg : h.rhoMat g = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5))) (k : closure ({a, b} : Set G)) :
    ((k * g : closure ({a, b} : Set G)) :
        closure ({a, b} : Set G) ⧸ (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) =
      ((g * k : closure ({a, b} : Set G)) :
        closure ({a, b} : Set G) ⧸ (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) := by
  rw [QuotientGroup.eq, ← h.cert_rho_ker hc, MonoidHom.mem_ker]
  have hcomm : h.rho g * h.rho k = h.rho k * h.rho g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, rho_val, rho_val, hg, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  simp only [map_mul, map_inv]
  rw [hcomm, inv_mul_cancel]

theorem cert_kernel_trivial [Finite G] (hc : CosetCert x v a b Ab Bb n par gen t tb next qc)
    (hidx : (closure ({a, b} : Set G)).index.Coprime 5) (hn : ¬25 ∣ n) {r : ZMod 5}
    (hB : Bb * Bb = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5))) (hr2 : r ^ 2 ≠ 1) (hr3 : r ^ 3 ≠ 1)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (Cp : Sylow 5 π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := h.fiveQ_normal
  have hfin := h.cert_finite_M hc
  have hb2 : h.rhoMat (fiveBSq a b) = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5)) := by
    rw [h.rhoMat_bSq, hB]
  have hquot : Nat.card (closure ({a, b} : Set G) ⧸
      (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) = n := by
    have h1 := card_eq_card_quotient_mul_card_subgroup
      ((fiveQ x v).subgroupOf (closure ({a, b} : Set G)))
    rw [Nat.card_congr (subgroupOfEquivOfLe h.fiveQ_le_M).toEquiv, h.q.card_fiveQ,
      h.cert_card_M hc] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  have hcyc : ∀ P : Sylow 5 (closure ({a, b} : Set G) ⧸
      (fiveQ x v).subgroupOf (closure ({a, b} : Set G))), IsCyclic P := by
    intro P
    have : Finite (closure ({a, b} : Set G) ⧸
        (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) :=
      Nat.finite_of_card_ne_zero (by rw [hquot]; exact hc.pos.ne')
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd : 5 ^ k ∣ n := by
      have := card_subgroup_dvd_card P.toSubgroup
      rw [hk, hquot] at this
      exact this
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact hn (dvd_trans (pow_dvd_pow 5 (by omega : 2 ≤ k)) hdvd)
    apply isCyclic_of_card_dvd_prime (p := 5)
    rw [hk]
    exact (pow_dvd_pow 5 hk1).trans (pow_one 5).dvd
  refine central_cover_extraspecial_scalar_normalizer_kernel_trivial (p := 5) hidx h.fiveQ_le_M
    (fun q hq => h.q.pow_five_of_mem hq) h.q.commutator_eq_center.symm h.q.card_center hcyc
    ((fiveBSq a b : closure ({a, b} : Set G)) :
      closure ({a, b} : Set G) ⧸ (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) ?_ ?_ r hr2
    hr3 ?_ π hπ hC Cp
  · rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H k =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact h.cert_mk_comm_of_scalar hc hb2 k
  · have h4 : ((fiveBSq a b : closure ({a, b} : Set G)) :
        closure ({a, b} : Set G) ⧸ (fiveQ x v).subgroupOf (closure ({a, b} : Set G))) ^ 4 = 1 := by
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
      congr 1
      apply Subtype.ext
      show (b ^ 2) ^ 4 = 1
      rw [← pow_mul, show 2 * 4 = 8 from rfl, h.b8]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h4) (by norm_num)
  · intro g hg q hq
    have hgb : h.rho g = h.rho (fiveBSq a b) := by
      have hmem := QuotientGroup.eq.1 hg
      rw [← h.cert_rho_ker hc, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hmem
      exact hmem
    have hgm : h.rhoMat g = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5)) := by
      rw [← rho_val, hgb, rho_val, hb2]
    rw [h.q.center_map]
    exact h.conj_scalar hgm hq

end FiveMRel

theorem lyFiveBbar_sq :
    lyFiveBbar * lyFiveBbar = (2 : ZMod 5) • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5)) := by
  decide +kernel

theorem lyFiveMRelP : FiveMRel (lyPhiP lyFiveXJ) (lyPhiP ∘ lyFiveVJ) lyFiveOmega (lyPhiP lyFiveAJ)
    (lyPhiP lyFiveBJ) lyFiveAbar lyFiveBbar lyFiveAlpha lyFiveBeta :=
  lyFiveMRelJ.map lyPhiP_injective

theorem lyFiveCertP : CosetCert (lyPhiP lyFiveXJ) (lyPhiP ∘ lyFiveVJ) (lyPhiP lyFiveAJ)
    (lyPhiP lyFiveBJ) lyFiveAbar lyFiveBbar 2880 lyFivePar lyFiveGen
    (lyPhiP ∘ fiveLift lyFiveAJ lyFiveBJ) lyFiveTb lyFiveNext lyFiveQc :=
  lyFiveCertJ.map

theorem lyFiveM_index_P :
    (closure ({lyPhiP lyFiveAJ, lyPhiP lyFiveBJ} : Set lyP)).index = 5751686556 := by
  have h1 := (closure ({lyPhiP lyFiveAJ, lyPhiP lyFiveBJ} : Set lyP)).card_mul_index
  rw [lyFiveMRelP.cert_card_M lyFiveCertP, card_lyP] at h1
  omega

theorem lyP_five_kernel_trivial {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* lyP) (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (Cp : Sylow 5 π.ker) :
    (Cp : Subgroup π.ker) = ⊥ :=
  lyFiveMRelP.cert_kernel_trivial lyFiveCertP (by rw [lyFiveM_index_P]; norm_num) (by norm_num)
    lyFiveBbar_sq (by decide +kernel) (by decide +kernel) π hπ hC Cp

theorem sylow_eq_bot_of_ker_eq {E : Type*} [Group E] {K K' : Subgroup E} (hK : K' = K)
    (h : ∀ P : Sylow 5 K', (P : Subgroup K') = ⊥) (Cp : Sylow 5 K) : (Cp : Subgroup K) = ⊥ := by
  subst hK
  exact h Cp

theorem ly_five_kernel_trivial {S : Type*} [Group S]
    (eS : S ≃* CFSG.Blueprint.NativeSporadic.Ly) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* S) (hπ : Function.Surjective π) (hC : π.ker ≤ center E)
    (Cp : Sylow 5 π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  let φ : S ≃* lyP := eS.trans lyEquivP
  have hk : (φ.toMonoidHom.comp π).ker = π.ker := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulEquiv.map_eq_one_iff]
  have hπ' : Function.Surjective (φ.toMonoidHom.comp π) := φ.surjective.comp hπ
  have hC' : (φ.toMonoidHom.comp π).ker ≤ center E := hk ▸ hC
  exact sylow_eq_bot_of_ker_eq hk (fun P => lyP_five_kernel_trivial _ hπ' hC' P) Cp

theorem R3E_Ly_full_central_five_kernel_trivial {S : Type*} [Group S]
    (hS : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Ly))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) :
    (∀ C₅ : Sylow 5 π.ker, (C₅ : Subgroup π.ker) = ⊥) ∧ (IsPGroup 5 π.ker → π.ker = ⊥) := by
  have h1 : ∀ C₅ : Sylow 5 π.ker, (C₅ : Subgroup π.ker) = ⊥ := fun C₅ =>
    ly_five_kernel_trivial hS.some π hπ hC C₅
  refine ⟨h1, fun hp => ?_⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := (hp.to_subgroup (⊤ : Subgroup π.ker)).exists_le_sylow
  rw [h1 Q] at hQ
  rw [eq_bot_iff]
  intro g hg
  have := hQ (mem_top (⟨g, hg⟩ : π.ker))
  rw [mem_bot] at this
  rw [mem_bot]
  exact congrArg Subtype.val this

end CFSG.RankThree.Native
