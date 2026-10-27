module

public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldTwo
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item138Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix (GeneralLinearGroup ProjGenLinGroup)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits diagTau cycThree slPi glPi PiField ModThree)

section Diag

variable {K : Type} [Field K]

theorem diagUnits_comm (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [Sec4.diagUnits_mul, Sec4.diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem scalar_conj (l : Kˣ) (X : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) l * X * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ = X := by
  rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l X).eq, mul_inv_cancel_right]

theorem conj_diag_comm {g y : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) (a b c : Kˣ) :
    y * (g * diagUnits a b c * g⁻¹) * y⁻¹ = g * diagUnits a b c * g⁻¹ := by
  have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  rw [hy']
  calc g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ *
        (g * diagUnits a b c * g⁻¹) *
        (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹)⁻¹ =
      g * (GeneralLinearGroup.scalar (Fin 3) l * (diagUnits 1 s t * diagUnits a b c *
        (diagUnits 1 s t)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) * g⁻¹ := by group
    _ = g * diagUnits a b c * g⁻¹ := by
      rw [diagUnits_comm 1 s t a b c, mul_inv_cancel_right, scalar_conj]

theorem comm_cycThree_conj {g y : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) :
    (g * cycThree * g⁻¹) * y * (g * cycThree * g⁻¹)⁻¹ * y⁻¹ =
      g * diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹ := by
  have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  have hsc : cycThree * GeneralLinearGroup.scalar (Fin 3) l =
      GeneralLinearGroup.scalar (Fin 3) l * cycThree :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l cycThree).eq
  have h1 := Sec4.cycThree_conj_diagUnits (K := K) 1 s t
  have h2 : diagUnits t 1 s * (diagUnits 1 s t)⁻¹ = diagUnits t s⁻¹ (s * t⁻¹) := by
    rw [Sec4.diagUnits_inv, Sec4.diagUnits_mul, inv_one, mul_one, one_mul]
  rw [hy']
  calc g * cycThree * g⁻¹ * (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹) *
        (g * cycThree * g⁻¹)⁻¹ *
        (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹)⁻¹ =
      g * (cycThree * GeneralLinearGroup.scalar (Fin 3) l * (diagUnits 1 s t * cycThree⁻¹ *
        (diagUnits 1 s t)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) * g⁻¹ := by group
    _ = g * (GeneralLinearGroup.scalar (Fin 3) l * ((cycThree * diagUnits 1 s t * cycThree⁻¹) *
        (diagUnits 1 s t)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) * g⁻¹ := by
      rw [hsc]
      group
    _ = g * diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹ := by rw [h1, h2, scalar_conj]

theorem zpow_pow_three {M : Type*} [Group M] {a : M} (h : a ^ 3 = 1) (i : ℤ) : (a ^ i) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem diagUnits_pow_three {a b c : Kˣ} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) :
    diagUnits a b c ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one, Sec4.diagUnits_mul, Sec4.diagUnits_mul, ← pow_two, ← pow_two,
    ← pow_two, ← pow_succ, ← pow_succ, ← pow_succ, ha, hb, hc, Sec4.diagUnits_one]

theorem mk_diagTau_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ProjGenLinGroup.mk (diagTau hτ) ≠ 1 := by
  intro h2
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨t, ht⟩ := h2
  have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [Sec4.coe_scalar_eq_smul, Sec4.coe_diagTau] at e0 e2
  simp at e0 e2
  rw [e2] at e0
  simp at e0
  exact hτ1 e0.symm

theorem mk_cycThree_not_mem_zpowers {τ : K} (hτ : τ ^ 3 = 1) :
    ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ∉
      Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  intro hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : ProjGenLinGroup.mk (diagTau hτ ^ i) = ProjGenLinGroup.mk cycThree := by
    rw [map_zpow]
    exact hi
  have h2 : ProjGenLinGroup.mk (cycThree * (diagTau hτ ^ i)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨t, ht⟩ := h2
  have hdiag : diagTau hτ = Sec4.diagHom (Units.mk0 τ hτ0, Units.mk0 τ hτ0 ^ 2, 1) := by
    rw [Sec4.diagTau_eq_diagUnits hτ hτ0]
    rfl
  have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) ht
  rw [hdiag, ← map_zpow, ← map_inv, Units.val_mul, Sec4.coe_diagHom, Sec4.coe_scalar_eq_smul,
    Sec4.coe_cycThree] at e11
  simp [Matrix.mul_apply, Matrix.diagonal] at e11

end Diag

section Two

theorem two_lt_of_mulEquiv {X : Type} [Group X] (hX : IsQuasisimple X) {π : Bool} {p f : ℕ}
    {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : X ≃* projImage (slPi π 3 (p ^ f) K)) : 2 < p ^ f := by
  have h2 : 2 ≤ p ^ f :=
    le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
  by_contra hle
  have heq : p ^ f = 2 := by omega
  cases π
  · have : Group.IsSolvable (slPi false 3 (p ^ f) K) := Sec13.isSolvable_slPi_two hK heq
    have : Group.IsSolvable (projImage (slPi false 3 (p ^ f) K)) := Sec13.isSolvable_projImage
    have hsol : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have : Group.IsPerfect X := hX.1
    have : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
    have : Nontrivial X := (QuotientGroup.mk_surjective (s := Subgroup.center X)).nontrivial
    exact Group.IsPerfect.not_isSolvable X hsol
  · change p ^ f % 3 = 1 at hq
    omega

end Two

section Exists

variable {G : Type} [Group G] [Finite G]

theorem exists_isF138N {A : Subgroup G} {c : G} {L E : Subgroup G} (hH : Hyp138 A c L E) :
    ∃ F : Subgroup G, IsF138N L E F := by
  obtain ⟨h, -, hcE, hE3, -, hEN, -, hST, hC⟩ := hH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := by
    rcases hST with hS | hT
    · exact hS.1
    · exact hT.1
  have hEF : E ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hEE
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hEF.2.1
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3.2 g g.2)⟩
  obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hτD, -⟩ := hC
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hq2 := two_lt_of_mulEquiv
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt) hK hq e
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv e (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨g, hg, hdiag, -⟩ := Sec4.isTypeC_conj_std hK hq hD
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hd₁ : g * diagTau hτ * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (Sec4.diagTau_mem_slPi hπ hq' hτ)
  have hd₂ : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (Sec4.cycThree_mem_slPi hπ)
  set P₁ : projImage (slPi π 3 (p ^ f) K) := Sec4.projOf _ ⟨_, hd₁⟩ with hP₁
  set P₂ : projImage (slPi π 3 (p ^ f) K) := Sec4.projOf _ ⟨_, hd₂⟩ with hP₂
  have hP₁c : (P₁ : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹ := by
    rw [hP₁, Sec4.coe_projOf, map_mul, map_mul, map_inv]
  have hP₂c : (P₂ : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹ := by
    rw [hP₂, Sec4.coe_projOf, map_mul, map_mul, map_inv]
  set θ := aschbacherSolvableCore 3 L with hθ
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  set y₁ : L ⧸ θ := e.symm P₁ with hy₁
  set y₂ : L ⧸ θ := e.symm P₂ with hy₂
  have he₁ : ((e y₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹) := by
    rw [hy₁, MulEquiv.apply_symm_apply, hP₁, Sec4.coe_projOf]
  have he₂ : ((e y₂ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * cycThree * g⁻¹) := by
    rw [hy₂, MulEquiv.apply_symm_apply, hP₂, Sec4.coe_projOf]
  have hfixDiag : ∀ (z : L ⧸ θ) (a b c' : Kˣ),
      ((e z : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagUnits a b c' * g⁻¹) →
      ∀ (x : G) (hx : x ∈ E), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) z = z := by
    intro z a b c' hz x hx
    obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
    obtain ⟨l, s, t, -, -, hl⟩ := hdiag y hyD
    apply e.injective
    apply Subtype.ext
    rw [hyz z, hz, ← map_inv, ← map_mul, ← map_mul, conj_diag_comm hl]
  have hfix₁ := hfixDiag y₁ (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1
    (by rw [he₁, Sec4.diagTau_eq_diagUnits hτ hτ0])
  have hy₁3 : y₁ ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, he₁, ← map_pow, conj_pow,
      Sec4.diagTau_pow_three, mul_one, mul_inv_cancel, map_one]
  have hy₂3 : y₂ ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, he₂, ← map_pow, conj_pow,
      Sec4.cycThree_pow_three, mul_one, mul_inv_cancel, map_one]
  have hy12 : y₁ * y₂ = y₂ * y₁ := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂]
    simp only [map_mul, map_inv]
    have hc := Sec4.mk_diagTau_cycThree hτ
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree) *
          (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ)) *
          (ProjGenLinGroup.mk g)⁻¹ := by rw [hc]
      _ = _ := by group
  have hy₁1 : y₁ ≠ 1 := by
    intro h1
    have h2 : ((e y₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) = 1 := by
      rw [h1, map_one, Subgroup.coe_one]
    rw [he₁, map_mul, map_mul, map_inv] at h2
    apply mk_diagTau_ne_one hτ hτ1
    calc ProjGenLinGroup.mk (diagTau hτ) = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  have hord₁ : orderOf y₁ = 3 := orderOf_eq_prime hy₁3 hy₁1
  have hy₂₁ : y₂ ∉ Subgroup.zpowers y₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ((e y₂ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((e y₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ^ k := by
      rw [← hk, map_zpow, Subgroup.coe_zpow]
    rw [he₁, he₂, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, conj_zpow] at h1
    apply mk_cycThree_not_mem_zpowers hτ
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc ProjGenLinGroup.mk (diagTau hτ) ^ k = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) ^ k * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk cycThree * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by rw [h1]
      _ = ProjGenLinGroup.mk cycThree := by group
  set Ybar := Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ with hYbar
  have hY9 : Nat.card Ybar = 9 := Sec4.card_zpowers_sup_zpowers hy₂3 hord₁ hy₂₁ hy12.symm
  have hYab : CFSG.Assembly.IsElemAbelian 3 Ybar := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hY9]; norm_num), ?_⟩
    intro x hx
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hy12 hx
    rw [(Commute.zpow_zpow hy12 i j).mul_pow, zpow_pow_three hy₁3, zpow_pow_three hy₂3, mul_one]
  set M : Subgroup L := (Subgroup.normalizer (E : Set G)).comap L.subtype with hM
  have hmapN : ∀ w : L, (∀ x ∈ E, (w : G) * x * (w : G)⁻¹ ∈ E ⊔ θG) →
      (w : L ⧸ θ) ∈ M.map (QuotientGroup.mk' θ) := by
    intro w hw
    obtain ⟨m, hmL, hmN, hmw⟩ := exists_mem_normalizer_of_conj_mem hEN hEp w.2 hw
    refine ⟨⟨m, hmL⟩, hmN, ?_⟩
    change ((⟨m, hmL⟩ : L) : L ⧸ θ) = (w : L ⧸ θ)
    rw [mk_eq_mk_iff]
    refine inv_mul_mem_theta_of_mul_inv_mem hmL ?_
    have := inv_mem hmw
    rwa [mul_inv_rev, inv_inv] at this
  obtain ⟨w₁, hw₁⟩ := QuotientGroup.mk_surjective y₁
  obtain ⟨w₂, hw₂⟩ := QuotientGroup.mk_surjective y₂
  have hy₁M : y₁ ∈ M.map (QuotientGroup.mk' θ) := by
    rw [← hw₁]
    exact hmapN w₁ (conj_mem_sup_of_fixed hEN w₁ fun x hx => by rw [hw₁]; exact hfix₁ x hx)
  have hw₂E : ∀ x ∈ E, (w₂ : G) * x * (w₂ : G)⁻¹ ∈ E ⊔ θG := by
    intro x hx
    set σ := L.normalizerMonoidHom ⟨x, hEN hx⟩ with hσ
    set k : L := w₂ * (σ w₂)⁻¹ with hk
    have hkG : (k : G) = (w₂ : G) * (x * (w₂ : G) * x⁻¹)⁻¹ := rfl
    obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
    obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag y hyD
    have hs3 : s ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs
    have ht3 : t ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht
    have hmk : (k : L ⧸ θ) = y₂ * (Sec4.thetaQuotMulAut L σ y₂)⁻¹ := by
      rw [hk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← Sec4.thetaQuotMulAut_mk, hw₂]
    have hek : ((e (k : L ⧸ θ) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagUnits t s⁻¹ (s * t⁻¹) * g⁻¹) := by
      rw [hmk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyz y₂, he₂,
        ← comm_cycThree_conj hl]
      simp only [map_mul, map_inv]
      group
    have hk3 : (k : L ⧸ θ) ^ 3 = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hek, ← map_pow, conj_pow,
        diagUnits_pow_three ht3 (by rw [inv_pow, hs3, inv_one])
          (by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul]),
        mul_one, mul_inv_cancel, map_one]
    obtain ⟨n, hnE, hnk⟩ := exists_mem_of_fixed hEN hE3 hEmax hk3 (hfixDiag _ _ _ _ hek)
    have hnk' : (n : G)⁻¹ * (k : G) ∈ θG := (mk_eq_mk_iff n k).mp hnk
    have hθx : x⁻¹ * ((n : G)⁻¹ * (k : G)) * x⁻¹⁻¹ ∈ θG :=
      conj_mem_theta_of_normalizer (inv_mem (hEN hx)) hnk'
    have heq : (w₂ : G) * x * (w₂ : G)⁻¹ =
        ((n : G) * x) * (x⁻¹ * ((n : G)⁻¹ * (k : G)) * x⁻¹⁻¹) := by
      rw [hkG]
      group
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hnE hx)) (Subgroup.mem_sup_right hθx)
  have hy₂M : y₂ ∈ M.map (QuotientGroup.mk' θ) := by
    rw [← hw₂]
    exact hmapN w₂ hw₂E
  have hYM : Ybar ≤ M.map (QuotientGroup.mk' θ) :=
    sup_le (Subgroup.zpowers_le.mpr hy₁M) (Subgroup.zpowers_le.mpr hy₂M)
  obtain ⟨S, hSM, hSab, hS9, hSY⟩ := Sec13.exists_elemAbelian_map_eq hYab hYM
  have hS3 : IsPGroup 3 S := fun s => ⟨1, Subtype.ext (by simpa using hSab.2 s s.2)⟩
  have htr := Sec4.transitive_of_normal_form (L := (⊤ : Subgroup (L ⧸ θ))) hK hq
    (Subgroup.topEquiv.trans e) hτ hτ1 hg (x₁ := y₁) (x₂ := y₂) (Subgroup.mem_top _)
    (Subgroup.mem_top _) he₁ he₂
  have htr' : ∀ x ∈ S.map (QuotientGroup.mk' θ), x ≠ 1 →
      ∀ y ∈ S.map (QuotientGroup.mk' θ), y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((S.map (QuotientGroup.mk' θ) : Subgroup (L ⧸ θ)) :
          Set (L ⧸ θ)), n * x * n⁻¹ = y := by
    rw [hSY]
    intro x hx hx1 y hy hy1
    obtain ⟨n, hn, hnxy⟩ := htr x hx hx1 y hy hy1
    exact ⟨n, hn.2, hnxy⟩
  set Y : Subgroup G := S.map L.subtype with hYdef
  have hYL : Y ≤ L := Subgroup.map_subtype_le S
  have hYN : Y ≤ Subgroup.normalizer (E : Set G) := Subgroup.map_le_iff_le_comap.mpr hSM
  have hYab' : CFSG.Assembly.IsElemAbelian 3 Y := Sec13.isElemAbelian_map hSab L.subtype
  have hYcard : Nat.card Y = 9 := by
    rw [hYdef, Subgroup.card_map_of_injective L.subtype_injective, hS9, hY9]
  have hcY : c ∉ Y := fun hc => hcL (hYL hc)
  obtain ⟨hFab, hF27⟩ :=
    Sec5.isElemAbelian_sup_zpowers hYab' hcY hc3 (fun a ha => hLc a (hYL ha))
  have hFL : (Y ⊔ Subgroup.zpowers c) ⊓ L = Y := by
    rw [sup_comm]
    exact Sec13.zpowers_sup_inf_eq hc3 hcL hYL (fun y hy => (hLc y (hYL hy)).symm)
  refine ⟨Y ⊔ Subgroup.zpowers c, ⟨sup_le (hYL.trans le_sup_right)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcE)), hFab, by rw [hF27, hYcard], ?_,
    sup_le hYN (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hcE))⟩, by rw [hFL, hYcard]⟩
  intro y hy hy1 z hz hz1
  rw [hFL] at hy hz
  obtain ⟨y', hy'S, rfl⟩ := hy
  obtain ⟨z', hz'S, rfl⟩ := hz
  have hy'1 : y' ≠ 1 := fun h1 => hy1 (by rw [h1, map_one])
  have hz'1 : z' ≠ 1 := fun h1 => hz1 (by rw [h1, map_one])
  obtain ⟨n, -, hn⟩ := exists_conj_of_map_mk hS3 htr' hy'S hy'1 hz'S hz'1
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

end Exists

end CFSG.RankThree.PartTwo.Sec13.Item138Proof

namespace CFSG.RankThree.PartTwo.Sec13

theorem item138ExistsN : Item138ExistsN :=
  fun _ _ _ _ _ _ _ hH => Item138Proof.exists_isF138N hH

end CFSG.RankThree.PartTwo.Sec13
