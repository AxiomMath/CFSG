module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem rightTransitive_congr {x y : ℕ → V} {k : ℕ} (h : ∀ i ≤ k, x i = y i) :
    RightTransitive Γ G x 0 k ↔ RightTransitive Γ G y 0 k := by
  unfold RightTransitive
  have hstab : stabRange G x 0 k = stabRange G y 0 k := by
    ext g
    rw [mem_stabRange, mem_stabRange]
    constructor
    · intro hg i hi1 hi2
      rw [← h i hi2]
      exact hg i hi1 hi2
    · intro hg i hi1 hi2
      rw [h i hi2]
      exact hg i hi1 hi2
  have hxk : x k = y k := h k le_rfl
  have hxkm : x (k - 1) = y (k - 1) := h (k - 1) (by omega)
  rw [hstab, hxk, hxkm]

namespace Setup

variable (X : Setup Γ G)

theorem Z_fixes_of_dist (i : ℤ) {d : ℕ} (hs : IsSingularity Γ G s) (hd : d ≤ s)
    {v : V} (hv : Γ.dist (X.vert i) v = d)
    (hfix : X.Z i ≤ MulAction.stabilizer G v) :
    ∀ w : V, Γ.dist (X.vert i) w ≤ d → X.Z i ≤ MulAction.stabilizer G w := by
  classical
  intro w hw
  have hv' : Γ.dist (X.vert i) v = d := hv
  obtain ⟨P, hP0, hPm⟩ := IsTree.exists_arc_between X.hyp.isTree (X.vert i) w
  obtain ⟨Q, hQ0, hQd⟩ := IsTree.exists_arc_between X.hyp.isTree (X.vert i) v
  have hmle : Γ.dist (X.vert i) w ≤ Γ.dist (X.vert i) v := by
    rw [hv']
    exact hw
  have hmles : Γ.dist (X.vert i) w ≤ s := by
    rw [← hv'] at hd
    exact le_trans hmle hd
  let Qm : Arc Γ (Γ.dist (X.vert i) w) := Arc.take Q _ hmle
  have hQm0 : Qm.vert 0 = X.vert i := by
    simp [Qm, Arc.take, hQ0]
  obtain ⟨g, hg⟩ := arc_conj_of_le X.hyp.adj_smul
    (fun v a b ha hb => X.hyp.locTrans ha hb) hs hmles Qm P 1
    (by rw [hQm0, hP0]; simp)
  have hgGi : g ∈ X.Gi i := by
    rw [Setup.Gi, MulAction.mem_stabilizer_iff]
    have h := hg 0 (Nat.zero_le _)
    rwa [hQm0, hP0] at h
  have hgw : g • Qm.vert (Γ.dist (X.vert i) w) = w := by
    have h := hg (Γ.dist (X.vert i) w) le_rfl
    rwa [hPm] at h
  have hfixQ : ∀ z ∈ X.Z i,
      z • Q.vert (Γ.dist (X.vert i) w) = Q.vert (Γ.dist (X.vert i) w) := by
    intro z hz
    have hz0 : z • Q.vert 0 = Q.vert 0 := by
      rw [hQ0]
      exact MulAction.mem_stabilizer_iff.mp (X.Z_le_Gi i hz)
    have hzend : z • Q.vert (Γ.dist (X.vert i) v) = Q.vert (Γ.dist (X.vert i) v) := by
      rw [hQd]
      exact MulAction.mem_stabilizer_iff.mp (hfix hz)
    have h := Arc.fixes_of_ends X.hyp.isTree X.hyp.adj_smul Q hz0 hzend
      (Γ.dist (X.vert i) w) hmle
    simpa [Qm] using h
  have hZnorm : conjSub g (X.Z i) = X.Z i := X.Z_normal i g hgGi
  have hkey : ∀ z ∈ X.Z i, z • w = w := by
    intro z hz
    have hzZ : z ∈ conjSub g (X.Z i) := by
      rw [hZnorm]
      exact hz
    have hz' : g⁻¹ * z * g ∈ X.Z i := mem_conjSub.mp hzZ
    have hfixu : (g⁻¹ * z * g) • Qm.vert (Γ.dist (X.vert i) w) =
        Qm.vert (Γ.dist (X.vert i) w) := hfixQ _ hz'
    calc z • w = z • (g • Qm.vert (Γ.dist (X.vert i) w)) := by rw [hgw]
      _ = (z * g) • Qm.vert (Γ.dist (X.vert i) w) := (mul_smul z g _).symm
      _ = (g * (g⁻¹ * z * g)) • Qm.vert (Γ.dist (X.vert i) w) := by
          congr 1
          group
      _ = g • ((g⁻¹ * z * g) • Qm.vert (Γ.dist (X.vert i) w)) := mul_smul g _ _
      _ = g • Qm.vert (Γ.dist (X.vert i) w) := by rw [hfixu]
      _ = w := hgw
  intro z hz
  exact MulAction.mem_stabilizer_iff.mpr (hkey z hz)

theorem K_eq_sup_edge (i : ℤ) : X.K = X.Ki i ⊔ X.Ki (i + 1) := by
  classical
  have hKi_le : X.Ki i ⊔ X.Ki (i + 1) ≤ X.K := sup_le inf_le_left inf_le_left
  refine le_antisymm ?_ hKi_le
  set H := X.Gi i ⊓ X.Gi (i + 1) with hH
  set S := X.edgeSylow i with hS
  set A := H ⊓ oTwoRes (X.L i) with hA
  set B := H ⊓ oTwoRes (X.L (i + 1)) with hB
  have hH_eq : H = A ⊔ B := by
    rw [hH, hA, hB]
    simpa [Setup.Gi, Setup.L] using edgeLocal_eq_sup_oTwoRes X.hyp (X.adj i)
  have hcompL : X.Ki i ⊔ S = X.L i ⊓ X.Gi (i + 1) := by
    have h := (complement_inf_oTwoPrime (α := X.vert i) (β := X.vert (i + 1)) (K := X.K)
      X.hyp (X.adj i) (le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1)))
      (by simpa [Setup.edgeSylow] using X.K_inf_edgeSylow i)
      (by simpa [Setup.edgeSylow] using X.K_sup_edgeSylow i)).2
    simpa [Setup.Ki, Setup.L, Setup.Gi, Setup.edgeSylow] using h
  have hcompR : X.Ki (i + 1) ⊔ S = X.L (i + 1) ⊓ X.Gi i := by
    have h := (complement_inf_oTwoPrime (α := X.vert (i + 1)) (β := X.vert i) (K := X.K)
      X.hyp (X.adj i).symm (le_inf (X.K_le_Gi (i + 1)) (X.K_le_Gi i))
      (by simpa [Setup.edgeSylow, inf_comm] using X.K_inf_edgeSylow i)
      (by simpa [Setup.edgeSylow, inf_comm] using X.K_sup_edgeSylow i)).2
    simpa [Setup.Ki, Setup.L, Setup.Gi, Setup.edgeSylow, inf_comm] using h
  have hAle : A ≤ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S := by
    intro x hx
    have hxH : x ∈ H := hx.1
    have hxL : x ∈ X.L i := oTwoRes_le (X.L i) hx.2
    have hxG : x ∈ X.Gi (i + 1) := (Subgroup.mem_inf.mp hxH).2
    have hxS : x ∈ X.Ki i ⊔ S := by
      rw [hcompL]
      exact ⟨hxL, hxG⟩
    have hle : X.Ki i ⊔ S ≤ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    exact hle hxS
  have hBle : B ≤ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S := by
    intro x hx
    have hxH : x ∈ H := hx.1
    have hxL : x ∈ X.L (i + 1) := oTwoRes_le (X.L (i + 1)) hx.2
    have hxG : x ∈ X.Gi i := (Subgroup.mem_inf.mp hxH).1
    have hxS : x ∈ X.Ki (i + 1) ⊔ S := by
      rw [hcompR]
      exact ⟨hxL, hxG⟩
    have hle : X.Ki (i + 1) ⊔ S ≤ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S :=
      sup_le (le_sup_right.trans le_sup_left) le_sup_right
    exact hle hxS
  have hHle : H ≤ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S := by
    rw [hH_eq]
    exact sup_le hAle hBle
  have hHnorm : H ≤ Subgroup.normalizer (S : Set G) := by
    rw [hH, hS, Setup.edgeSylow]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1))
  have hTnorm : X.Ki i ⊔ X.Ki (i + 1) ≤ Subgroup.normalizer (S : Set G) :=
    hKi_le.trans ((le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1))).trans hHnorm)
  intro x hxK
  have hxH : x ∈ H := (le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1))) hxK
  have hx : x ∈ (X.Ki i ⊔ X.Ki (i + 1)) ⊔ S := hHle hxH
  rw [sup_comm] at hx
  have hcoe : ((S ⊔ (X.Ki i ⊔ X.Ki (i + 1)) : Subgroup G) : Set G) =
      (S : Set G) * ((X.Ki i ⊔ X.Ki (i + 1) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S (X.Ki i ⊔ X.Ki (i + 1)) hTnorm
  have hxmul : x ∈ (S : Set G) * ((X.Ki i ⊔ X.Ki (i + 1) : Subgroup G) : Set G) := by
    rw [← hcoe]
    exact hx
  obtain ⟨s, hsS, t, htT, hst⟩ := Set.mem_mul.mp hxmul
  have htK : t ∈ X.K := hKi_le htT
  have hsK : s ∈ X.K := by
    have hsEq : s = x * t⁻¹ := by rw [← hst]; group
    rw [hsEq]
    exact X.K.mul_mem hxK (X.K.inv_mem htK)
  have hbot : s ∈ X.K ⊓ S := ⟨hsK, hsS⟩
  rw [show X.K ⊓ S = ⊥ by rw [hS]; exact X.K_inf_edgeSylow i, Subgroup.mem_bot] at hbot
  rw [← hst, hbot, one_mul]
  exact htT

theorem K_eq_sup : X.K = X.Ki 0 ⊔ X.Ki 1 := by
  have h := X.K_eq_sup_edge 0
  simpa using h


theorem L_exists_Q_mul_normalizer (k : ℤ) {R : Subgroup G}
    (hodd : Odd (Nat.card ↥R)) (hRG : R ≤ X.Gi k)
    (hcomm : ⁅X.L k, R⁆ ≤ X.Q k) :
    ∀ l ∈ X.L k, ∃ q ∈ X.Q k, ∃ m ∈ Subgroup.normalizer (R : Set G), q * m = l := by
  classical
  haveI : Finite ↥(X.Gi k) := X.hyp.finite_stab (X.vert k)
  intro l hl
  have hQG : X.Q k ≤ X.Gi k := X.Q_le_Gi k
  have hQnorm : X.L k ≤ Subgroup.normalizer (X.Q k : Set G) :=
    (X.L_le_Gi k).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi k))
  have hstep : ∀ l' ∈ X.L k, conjSub l' (R ⊔ X.Q k) ≤ R ⊔ X.Q k := by
    intro l' hl'
    have hconjR : conjSub l' R ≤ R ⊔ X.Q k := by
      intro x hx
      rw [mem_conjSub] at hx
      set y := l'⁻¹ * x * l' with hy
      have hyR : y ∈ R := hx
      have hc : ⁅l', y⁆ ∈ X.Q k :=
        (Subgroup.commutator_le.mp hcomm) l' hl' y hyR
      have hynorm : y ∈ Subgroup.normalizer (X.Q k : Set G) :=
        (hRG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi k))) hyR
      have hq : y⁻¹ * ⁅l', y⁆ * y ∈ X.Q k :=
        (Subgroup.mem_normalizer_iff''.mp hynorm ⁅l', y⁆).mp hc
      have hxeq : x = y * (y⁻¹ * ⁅l', y⁆ * y) := by
        rw [commutatorElement_def]
        simp only [hy]
        group
      rw [hxeq]
      exact Subgroup.mul_mem_sup (S := R) (T := X.Q k) hyR hq
    have hconjQ : conjSub l' (X.Q k) = X.Q k := by
      rw [show conjSub l' (X.Q k) = (X.Q k).map (MulAut.conj l').toMonoidHom from rfl]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm hl')
    rw [conjSub_sup, hconjQ]
    exact sup_le hconjR le_sup_right
  have hconjQ : conjSub l (X.Q k) = X.Q k := by
    rw [show conjSub l (X.Q k) = (X.Q k).map (MulAut.conj l).toMonoidHom from rfl]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm hl)
  have hconjR : conjSub l R ≤ R ⊔ X.Q k := by
    have h := hstep l hl
    rw [conjSub_sup] at h
    exact le_trans le_sup_left h
  have hconjF : conjSub l (R ⊔ X.Q k) = R ⊔ X.Q k := by
    refine le_antisymm (hstep l hl) ?_
    have hback := conjSub_mono l (hstep l⁻¹ ((X.L k).inv_mem hl))
    rwa [conjSub_inv_conjSub] at hback
  have hFnorm : l ∈ Subgroup.normalizer ((R ⊔ X.Q k : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hconjF
  have hF_le_G : R ⊔ X.Q k ≤ X.Gi k := sup_le hRG hQG
  haveI : Finite ↥(R ⊔ X.Q k) :=
    finite_of_le_stabilizer X.hyp (H := R ⊔ X.Q k) hF_le_G
  have hdisj : R ⊓ X.Q k = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (A := R) (B := X.Q k) hodd (pCoreOf_isPGroup' (X.Gi k))
  have hRnorm : R ≤ Subgroup.normalizer (X.Q k : Set G) :=
    hRG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi k))
  have hcard : Nat.card ↥(R ⊔ X.Q k) = Nat.card ↥R * Nat.card ↥(X.Q k) := by
    rw [sup_comm]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (X.Q k) R hRnorm
      (by rw [disjoint_iff, inf_comm]; exact hdisj)]
    rw [mul_comm]
  haveI : Finite ↥(X.Q k) := finite_of_le_stabilizer X.hyp (H := X.Q k) hQG
  have hrel : (X.Q k).relIndex (R ⊔ X.Q k) = Nat.card ↥R := by
    have h := Subgroup.relIndex_mul_card (H := X.Q k) (K := R ⊔ X.Q k)
    rw [inf_eq_left.mpr (le_sup_right : X.Q k ≤ R ⊔ X.Q k)] at h
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hSylow : IsSylowTwoOf (X.Q k) (R ⊔ X.Q k) := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex le_sup_right
      (pCoreOf_isPGroup' (X.Gi k)) ?_
    rw [hrel]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hFQnorm : R ⊔ X.Q k ≤ Subgroup.normalizer (X.Q k : Set G) :=
    sup_le hRnorm Subgroup.le_normalizer
  have hNnorm : ((X.Q k).subgroupOf (R ⊔ X.Q k)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFQnorm
  have hconjF' : conjSub l R ⊔ X.Q k = R ⊔ X.Q k := by
    have h := hconjF
    rw [conjSub_sup, hconjQ] at h
    exact h
  have hodd_conj : Odd (Nat.card ↥(conjSub l R)) := by
    rw [show conjSub l R = R.map (MulAut.conj l).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hodd
  have hdisj_conj : X.Q k ⊓ conjSub l R = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup hodd_conj (pCoreOf_isPGroup' (X.Gi k))
  obtain ⟨n, hnQ, hnEq⟩ := exists_conj_eq_of_complement (F := R ⊔ X.Q k) (N := X.Q k)
    (H := R) (K := conjSub l R) le_sup_right hNnorm hSylow le_sup_left hconjR
    (by rw [sup_comm]) (by rw [sup_comm]; exact hconjF')
    (by rw [inf_comm]; exact hdisj) hdisj_conj
  have hnl : n * l ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub (n * l) R = R
    rw [conjSub_mul, hnEq, conjSub_inv_conjSub]
  exact ⟨n⁻¹, (X.Q k).inv_mem hnQ, n * l, hnl, by group⟩

theorem normalizer_transitive_of_commutator_le_Q (k : ℤ) {R : Subgroup G}
    (hodd : Odd (Nat.card ↥R)) (hRG : R ≤ X.Gi k)
    (hcomm : ⁅X.L k, R⁆ ≤ X.Q k) :
    ∀ a b : V, Γ.Adj (X.vert k) a → Γ.Adj (X.vert k) b →
      ∃ g ∈ Subgroup.normalizer (R : Set G) ⊓ X.Gi k, g • a = b := by
  intro a b ha hb
  obtain ⟨l, hlL, hlab⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert k)).trans a b ha hb
  obtain ⟨q, hqQ, m, hmNorm, hqm⟩ := X.L_exists_Q_mul_normalizer k hodd hRG hcomm l hlL
  have hmG : m ∈ X.Gi k := by
    have hm_eq : m = q⁻¹ * l := by rw [← hqm]; group
    rw [hm_eq]
    exact (X.Gi k).mul_mem ((X.Gi k).inv_mem (X.Q_le_Gi k hqQ)) (X.L_le_Gi k hlL)
  have hadj : Γ.Adj (X.vert k) (m • a) := by
    have hmk : m • X.vert k = X.vert k := MulAction.mem_stabilizer_iff.mp hmG
    rw [← hmk]
    exact (X.hyp.adj_smul m (X.vert k) a).2 ha
  refine ⟨m, ⟨hmNorm, hmG⟩, ?_⟩
  calc m • a = q • (m • a) := by rw [X.Q_fixes_neighbors_vert k (m • a) hadj q hqQ]
    _ = (q * m) • a := (mul_smul q m a).symm
    _ = l • a := by rw [hqm]
    _ = b := hlab

theorem eq_bot_of_commutator_le_Q {i j : ℤ} (hij : Γ.Adj (X.vert i) (X.vert j))
    {R : Subgroup G} (hodd : Odd (Nat.card ↥R)) (hR : R ≤ X.Gi i ⊓ X.Gi j)
    (hLi : ⁅X.L i, R⁆ ≤ X.Q i) (hLj : ⁅X.L j, R⁆ ≤ X.Q j) : R = ⊥ := by
  refine eq_bot_of_normalizer_trans X.hyp hij hR ?_ ?_
  · intro a b ha hb
    exact X.normalizer_transitive_of_commutator_le_Q i hodd (hR.trans inf_le_left) hLi a b ha hb
  · intro a b ha hb
    exact X.normalizer_transitive_of_commutator_le_Q j hodd (hR.trans inf_le_right) hLj a b ha hb

theorem Ki_zero_complement_neg_one :
    X.Ki 0 ⊔ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = X.L 0 ⊓ X.Gi (-1) ∧
    X.Ki 0 ⊓ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = ⊥ := by
  classical
  have hS_eq : pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = X.edgeSylow (-1) := by
    unfold Setup.edgeSylow
    rw [show (-1 : ℤ) + 1 = 0 by norm_num]
    exact congrArg (pCoreOf 2) (inf_comm (X.Gi 0) (X.Gi (-1)))
  have hKle : X.K ≤ X.Gi 0 ⊓ X.Gi (-1) := le_inf (X.K_le_Gi 0) (X.K_le_Gi (-1))
  have hKinf : X.K ⊓ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = ⊥ := by
    rw [hS_eq]; exact X.K_inf_edgeSylow (-1)
  have hKsup : X.K ⊔ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = X.Gi 0 ⊓ X.Gi (-1) := by
    rw [hS_eq]
    have h := X.K_sup_edgeSylow (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num,
      show X.Gi (-1) ⊓ X.Gi 0 = X.Gi 0 ⊓ X.Gi (-1) from inf_comm _ _] at h
    exact h
  have hadj : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have h := complement_inf_oTwoPrime (α := X.vert 0) (β := X.vert (-1)) (K := X.K)
    X.hyp hadj hKle hKinf hKsup
  exact ⟨by simpa [Setup.Ki] using h.2, by simpa [Setup.Ki] using h.1⟩

theorem Ki_zero_conj_complement (y₀ : G) (hy₀L : y₀ ∈ X.L 0)
    (hy₀ : y₀ • X.vert 1 = X.vert (-1)) :
    conjSub y₀ (X.Ki 0) ⊔ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = X.L 0 ⊓ X.Gi (-1) ∧
    conjSub y₀ (X.Ki 0) ⊓ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) = ⊥ := by
  classical
  have hy₀G0 : y₀ ∈ X.Gi 0 := X.L_le_Gi 0 hy₀L
  set S := pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) with hS
  have hcomp1 := complement_inf_oTwoPrime (α := X.vert 0) (β := X.vert 1) (K := X.K)
    X.hyp (X.adj 0) X.K_le_inf
    (by simpa [Setup.edgeSylow] using X.K_inf_edgeSylow 0)
    (by simpa [Setup.edgeSylow] using X.K_sup_edgeSylow 0)
  have hcomp1L : X.Ki 0 ⊔ X.edgeSylow 0 = X.L 0 ⊓ X.Gi 1 := by
    simpa [Setup.Ki, Setup.edgeSylow, Setup.L] using hcomp1.2
  have hconjG1 : conjSub y₀ (X.Gi 1) = X.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub y₀ (X.vert 1), hy₀]
  have hconjS : conjSub y₀ (X.edgeSylow 0) = S := by
    unfold Setup.edgeSylow
    rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
      conjSub_eq_of_mem hy₀G0, hconjG1, hS]
  have hconjF : conjSub y₀ (X.L 0 ⊓ X.Gi 1) = X.L 0 ⊓ X.Gi (-1) := by
    rw [conjSub_inf, conjSub_eq_of_mem hy₀L, hconjG1]
  have hconj_sup : conjSub y₀ (X.Ki 0) ⊔ S = X.L 0 ⊓ X.Gi (-1) := by
    have h := congrArg (fun H => conjSub y₀ H) hcomp1L
    rw [conjSub_sup, hconjS, hconjF] at h
    exact h
  have hcomp1inf : X.Ki 0 ⊓ X.edgeSylow 0 = ⊥ := by
    simpa [Setup.Ki, Setup.edgeSylow] using hcomp1.1
  have hconj_inf : conjSub y₀ (X.Ki 0) ⊓ S = ⊥ := by
    have h2 := congrArg (fun H => conjSub y₀ H) hcomp1inf
    rw [conjSub_inf, hconjS, conjSub_bot] at h2
    exact h2
  exact ⟨by simpa [hS] using hconj_sup, by simpa [hS] using hconj_inf⟩

theorem exists_mem_pCoreOf_conjSub_Ki_zero_eq (y₀ : G) (hy₀L : y₀ ∈ X.L 0)
    (hy₀ : y₀ • X.vert 1 = X.vert (-1)) :
    ∃ n ∈ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)),
      conjSub y₀ (X.Ki 0) = conjSub n⁻¹ (X.Ki 0) := by
  classical
  haveI : Finite ↥(X.Gi 0 ⊓ X.Gi (-1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi (-1)) inf_le_left
  obtain ⟨hHsup, hHinf⟩ := X.Ki_zero_complement_neg_one
  obtain ⟨hconj_sup, hconj_inf⟩ := X.Ki_zero_conj_complement y₀ hy₀L hy₀
  set F := X.L 0 ⊓ X.Gi (-1) with hF
  set S := pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) with hS
  have hF_le : F ≤ X.Gi 0 ⊓ X.Gi (-1) := by
    rw [hF]
    exact le_inf (inf_le_left.trans (X.L_le_Gi 0)) inf_le_right
  haveI : Finite ↥F := finite_of_le_stabilizer X.hyp (α := X.vert 0) (H := F)
    (hF_le.trans inf_le_left)
  have hSF : S ≤ F := by
    rw [hF]
    refine le_inf ?_ ?_
    · exact le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0 ⊓ X.Gi (-1)))
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 0 ⊓ X.Gi (-1))).trans inf_le_right
  have hadj : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hSylow : IsSylowTwoOf S F :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right
      (isSylowTwoOf_pCoreOf_edgeStab X.hyp hadj) hSF hF_le
  have hSnorm : (S.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hF_le.trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1))))
  have hHF : X.Ki 0 ≤ F := by rw [← hHsup]; exact le_sup_left
  have hK'F : conjSub y₀ (X.Ki 0) ≤ F := by rw [← hconj_sup]; exact le_sup_left
  obtain ⟨n, hnS, hnEq⟩ := exists_conj_eq_of_complement (F := F) (N := S)
    (H := X.Ki 0) (K := conjSub y₀ (X.Ki 0)) hSF hSnorm hSylow hHF hK'F
    (by rw [sup_comm]; exact hHsup) (by rw [sup_comm]; exact hconj_sup)
    (by rw [inf_comm]; exact hHinf) (by rw [inf_comm]; exact hconj_inf)
  exact ⟨n, hnS, hnEq⟩

theorem exists_normalizer_Ki_move :
    ∃ y ∈ X.L 0 ⊓ Subgroup.normalizer (X.Ki 0 : Set G), y • X.vert 1 = X.vert (-1) := by
  classical
  haveI : Finite ↥(X.Gi 0 ⊓ X.Gi (-1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi (-1)) inf_le_left
  obtain ⟨y₀, hy₀L, hy₀⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans
    (X.vert 1) (X.vert (-1)) (X.adj 0) (by
      have h := (X.adj (-1)).symm
      rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h)
  obtain ⟨n, hnS, hnEq⟩ := X.exists_mem_pCoreOf_conjSub_Ki_zero_eq y₀ hy₀L hy₀
  have hnL : n ∈ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0 ⊓ X.Gi (-1)))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left) hnS
  have hnG : n ∈ X.Gi (-1) :=
    (Subgroup.mem_inf.mp ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) hnS)).2
  refine ⟨n * y₀, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨(X.L 0).mul_mem hnL hy₀L, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub (n * y₀) (X.Ki 0) = X.Ki 0
    rw [conjSub_mul, hnEq, conjSub_inv_conjSub]
  · rw [mul_smul, hy₀]
    exact MulAction.mem_stabilizer_iff.mp hnG

theorem sup_Q_eq_edgeSylow_of_relIndex {e r j : ℤ} {A : Subgroup G}
    (hK : X.K ≤ Subgroup.normalizer (A : Set G))
    (hA : A ≤ X.edgeSylow e) (hnot : ¬ A ≤ X.Q r)
    (hQrS : X.Q r ≤ X.edgeSylow e)
    (hrel : (X.Q r).relIndex (X.edgeSylow e) = 2 ^ X.n r)
    (hn : X.n r = 1 ∨ X.n r = 2)
    (hj : j = r - 1 ∨ j = r + 1)
    (hSr : X.edgeSylow e ≤ X.Gi r) (hSj : X.edgeSylow e ≤ X.Gi j) :
    A ⊔ X.Q r = X.edgeSylow e := by
  classical
  set Q := X.Q r with hQ
  set S := X.edgeSylow e with hS
  set B := A ⊔ Q with hB
  have hQB : Q ≤ B := le_sup_right
  have hBS : B ≤ S := sup_le hA hQrS
  have hBneQ : B ≠ Q := by
    intro h
    apply hnot
    rw [← h]
    exact le_sup_left
  by_contra hBneS
  have hBlt : B < S := lt_of_le_of_ne hBS hBneS
  have hBrel_dvd : B.relIndex S ∣ 2 ^ X.n r := by
    rw [← hrel]
    exact Subgroup.relIndex_dvd_of_le_left (H := Q) (K := B) (L := S) hQB
  have hBrel_ne1 : B.relIndex S ≠ 1 := by
    intro h
    exact hBneS (le_antisymm hBS (Subgroup.relIndex_eq_one.mp h))
  have hBrel_ne0 : B.relIndex S ≠ 0 := by
    intro h0
    rw [h0] at hBrel_dvd
    exact absurd hBrel_dvd (by simp)
  rcases hn with hn1 | hn2
  ·
    have hrel2 : Q.relIndex S = 2 := by rw [hrel, hn1]; norm_num
    have hBrel : B.relIndex S = 2 := by
      have hdvd : B.relIndex S ∣ 2 := by
        have h := hBrel_dvd
        rwa [hn1, pow_one] at h
      have hle : B.relIndex S ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 1 ≤ B.relIndex S := Nat.one_le_iff_ne_zero.mpr hBrel_ne0
      omega
    have hprod := Subgroup.relIndex_mul_relIndex (H := Q) (K := B) (L := S) hQB hBS
    rw [hBrel, hrel2] at hprod
    have hQrelB : Q.relIndex B = 1 := by omega
    exact hnot (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hQrelB))
  ·
    have hrel4 : Q.relIndex S = 4 := by rw [hrel, hn2]; norm_num
    have hBrel_ne4 : B.relIndex S ≠ 4 := by
      intro h4
      have hprod := Subgroup.relIndex_mul_relIndex (H := Q) (K := B) (L := S) hQB hBS
      rw [h4, hrel4] at hprod
      have hQrelB : Q.relIndex B = 1 := by omega
      exact hnot (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hQrelB))
    have hBrel : B.relIndex S = 2 := by
      have hdvd : B.relIndex S ∣ 4 := by
        have h := hBrel_dvd
        rw [hn2] at h
        norm_num at h
        exact h
      have hdvd' : B.relIndex S ∣ 2 ^ 2 := by
        norm_num
        exact hdvd
      obtain ⟨m, hmle, hm⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 2)).mp hdvd'
      interval_cases m
      · exact absurd hm hBrel_ne1
      · simpa using hm
      · exact absurd (by simpa using hm) hBrel_ne4
    have hprod := Subgroup.relIndex_mul_relIndex (H := Q) (K := B) (L := S) hQB hBS
    rw [hBrel, hrel4] at hprod
    have hQrelB : Q.relIndex B = 2 := by omega
    have hcoset : ∀ x ∈ B, x ∉ Q → ∀ y ∈ B, y ∉ Q → x * y⁻¹ ∈ Q := by
      intro x hxB hxQ y hyB hyQ
      obtain ⟨a, -, ha⟩ := (Subgroup.relIndex_eq_two_iff (H := Q) (K := B)).mp hQrelB
      have hxaq : x * a ∈ Q := by
        rcases ha x hxB with ⟨h, -⟩ | ⟨hnx, -⟩
        · exact h
        · exact absurd hnx hxQ
      have hyaq : y * a ∈ Q := by
        rcases ha y hyB with ⟨h, -⟩ | ⟨hny, -⟩
        · exact h
        · exact absurd hny hyQ
      have hmul : (x * a) * (y * a)⁻¹ ∈ Q := Q.mul_mem hxaq (Q.inv_mem hyaq)
      rwa [show (x * a) * (y * a)⁻¹ = x * y⁻¹ by group] at hmul
    obtain ⟨u, huA, huQ⟩ := Set.not_subset.mp hnot
    have hKi : X.Ki r ≠ ⊥ := X.torus_ne_bot r (by omega)
    obtain ⟨⟨k, hkKi⟩, hkk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKi
    have hk1 : k ≠ 1 := fun h => hkk1 (Subtype.ext h)
    have hkK : k ∈ X.K := hkKi.1
    have hkQ : k ∈ Subgroup.normalizer (Q : Set G) := by
      rw [hQ]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi r) (X.K_le_Gi r hkK)
    have hKB : X.K ≤ Subgroup.normalizer (B : Set G) := by
      intro g hg
      have hgA : g ∈ Subgroup.normalizer (A : Set G) := hK hg
      have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := by
        rw [hQ]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi r) (X.K_le_Gi r hg)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hAeq : conjSub g A = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgA
      have hQeq : conjSub g Q = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgQ
      change conjSub g B = B
      rw [hB, conjSub_sup, hAeq, hQeq]
    have huB : u ∈ B := by rw [hB]; exact Subgroup.mem_sup_left huA
    have hvB : k * u * k⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hKB hkK) u).mp huB
    have hvQ : k * u * k⁻¹ ∉ Q := by
      intro hv
      have hiff := Subgroup.mem_normalizer_iff''.mp hkQ (k * u * k⁻¹)
      have hu : k⁻¹ * (k * u * k⁻¹) * k ∈ Q := hiff.mp hv
      rw [show k⁻¹ * (k * u * k⁻¹) * k = u by group] at hu
      exact huQ hu
    have hcommQ : ⁅k, u⁆ ∈ Q := by
      have h := hcoset (k * u * k⁻¹) hvB hvQ u huB huQ
      simpa [commutatorElement_def] using h
    have hu2 : ∃ m : ℕ, u ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := (X.isPGroup_edgeSylow e).exists_pow_pow_eq_one ⟨u, hA huA⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hui : u ∈ X.Gi r := hSr (hA huA)
    have huj : u ∈ X.Gi j := hSj (hA huA)
    have huq : u ∈ X.Q r :=
      X.mem_Q_of_commutator_mem r (by omega) hkKi hk1 hj hu2 hui huj (by simpa [hQ] using hcommQ)
    exact huQ huq

@[expose] def reverse (X : Setup Γ G) : Setup Γ G where
  line := X.line.rev
  τ := X.τ⁻¹
  trans i := by
    rw [Line.rev_vert, Line.rev_vert, show X.τ⁻¹ = X.τ ^ (-1 : ℤ) by simp]
    rw [X.zpow_smul_vert (-1) (-i)]
    congr 1
    ring
  K := X.K
  K_fix := by
    intro k hk i
    change k • X.line.vert (-i) = X.line.vert (-i)
    exact X.K_fix k hk (-i)
  τ_norm := inv_mem X.τ_norm
  hyp := X.hyp
  K_inf := by
    have h := X.K_inf_edgeSylow (-1)
    simpa [Line.rev_vert, Setup.edgeSylow, inf_comm] using h
  K_sup := by
    have h := X.K_sup_edgeSylow (-1)
    simpa [Line.rev_vert, Setup.edgeSylow, inf_comm] using h

@[simp] theorem reverse_line : X.reverse.line = X.line.rev := rfl

@[simp] theorem reverse_τ : X.reverse.τ = X.τ⁻¹ := rfl

@[simp] theorem reverse_K : X.reverse.K = X.K := rfl

@[simp] theorem reverse_hyp : X.reverse.hyp = X.hyp := rfl

@[simp] theorem reverse_vert (i : ℤ) : X.reverse.vert i = X.vert (-i) := rfl

@[simp] theorem reverse_Gi (i : ℤ) : X.reverse.Gi i = X.Gi (-i) := rfl

@[simp] theorem reverse_Q (i : ℤ) : X.reverse.Q i = X.Q (-i) := rfl

@[simp] theorem reverse_L (i : ℤ) : X.reverse.L i = X.L (-i) := rfl

@[simp] theorem reverse_Z (i : ℤ) : X.reverse.Z i = X.Z (-i) := rfl

@[simp] theorem reverse_Ki (i : ℤ) : X.reverse.Ki i = X.Ki (-i) := rfl

@[simp] theorem reverse_n (i : ℤ) : X.reverse.n i = X.n (-i) := rfl

@[simp] theorem reverse_S : X.reverse.S = pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) := by
  unfold Setup.S
  change pCoreOf 2 (X.Gi (-0) ⊓ X.Gi (-1)) = pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1))
  rw [show (-0 : ℤ) = 0 by norm_num]

@[simp] theorem reverse_arcStab (m r : ℤ) :
    X.reverse.arcStab m r = X.arcStab (-r) (-m) := by
  unfold Setup.arcStab
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨-i, ?_, ?_⟩
    · rw [Set.mem_Icc] at hi ⊢
      omega
    · rfl
  · rintro ⟨j, hj, rfl⟩
    refine ⟨-j, ?_, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · simp

@[simp] theorem reverse_GT : X.reverse.GT = X.GT := by
  unfold Setup.GT
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨-i, by simp⟩
  · rintro ⟨j, rfl⟩
    exact ⟨-j, by simp⟩

theorem reverse_hX (hs : IsSingularity Γ G s) (hodd : Odd s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ RightTransitive Γ G (X.reverse.line.arc 0 s).vert 0 s := by
  have hdist : Odd (Γ.dist (X.vert 0) (X.vert (-(s : ℤ)))) := by
    rw [dist_comm, Line.dist_eq X.hyp.isTree X.line (show -(s : ℤ) ≤ 0 by omega)]
    simpa using hodd
  have hleft : ¬ LeftTransitive Γ G (X.line.arc (-(s : ℤ)) s).vert 0 s :=
    leftSingular_of_start_odd X.hyp.isTree X.hyp.adj_smul
      (fun v a b ha hb => X.hyp.locTrans ha hb) X.hyp.edgeTrans X.hyp.preservesParts
      hs (γ := X.line.arc 0 s) hX (by simpa [Line.arc] using hdist)
  have hrev : ¬ RightTransitive Γ G (X.line.arc (-(s : ℤ)) s).rev.vert 0 s := by
    rw [rightTransitive_rev_iff (X.line.arc (-(s : ℤ)) s) hs.1]
    exact hleft
  have hvert : ∀ i ≤ s, (X.line.arc (-(s : ℤ)) s).rev.vert i =
      (X.reverse.line.arc 0 s).vert i := by
    intro i hi
    have hcast : ((s - i : ℕ) : ℤ) = (s : ℤ) - (i : ℤ) := Nat.cast_sub hi
    have h1 : (X.line.arc (-(s : ℤ)) s).rev.vert i = X.vert (-(i : ℤ)) := by
      rw [Arc.rev_vert]
      simp only [Line.arc]
      rw [hcast]
      congr 1
      ring
    have h2 : (X.reverse.line.arc 0 s).vert i = X.vert (-(i : ℤ)) := by
      simp only [Setup.reverse, Line.arc, Line.rev_vert]
      congr 1
      ring
    rw [h1, h2]
  intro hR
  exact hrev ((rightTransitive_congr hvert).mpr hR)

end Setup

end CFSG.Quasithin.St84
