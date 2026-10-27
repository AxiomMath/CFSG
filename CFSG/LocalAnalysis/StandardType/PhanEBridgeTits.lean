module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs
import CFSG.LocalAnalysis.StandardType.PhanEBridgeTitsPhi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

private theorem hmbTits_smul_mk (S : PhanFamilyE K 2 f M G) (g a : G) :
    g • (a : G ⧸ S.torus) = ((g * a : G) : G ⧸ S.torus) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]

private theorem hmbTits_isMorphism_smul (S : PhanFamilyE K 2 f M G) (g : G) :
    IsMorphism (phanSystemE S) (phanSystemE S) (g • ·) := by
  intro i x y h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [phanSystemE_adj_mk S] at h
  show (phanSystemE S).adj i (g • (a : G ⧸ S.torus)) (g • (b : G ⧸ S.torus))
  simp only [hmbTits_smul_mk]
  rw [phanSystemE_adj_mk S]
  simpa [mul_assoc] using h

private noncomputable def hmbTits_stabSub (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) :
    Subgroup G where
  carrier := {g | (g : G ⧸ S.torus) ∈ (phanSystemE S).residue J ((1 : G) : G ⧸ S.torus)}
  mul_mem' {a b} ha hb := by
    have h1 : a • (b : G ⧸ S.torus) ∈
        (phanSystemE S).residue J (a • ((1 : G) : G ⧸ S.torus)) :=
      (hmbTits_isMorphism_smul S a).mapsTo_residue J ((1 : G) : G ⧸ S.torus) hb
    simp only [hmbTits_smul_mk, mul_one] at h1
    rw [residue_eq_of_mem ha] at h1
    exact h1
  one_mem' := self_mem_residue _ _
  inv_mem' {a} ha := by
    have h1 : a⁻¹ • (a : G ⧸ S.torus) ∈
        (phanSystemE S).residue J (a⁻¹ • ((1 : G) : G ⧸ S.torus)) :=
      (hmbTits_isMorphism_smul S a⁻¹).mapsTo_residue J ((1 : G) : G ⧸ S.torus) ha
    simp only [hmbTits_smul_mk, mul_one, inv_mul_cancel] at h1
    exact mem_residue_symm h1

private theorem hmbTits_mem_stabSub (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) (g : G) :
    g ∈ hmbTits_stabSub S J ↔
      (g : G ⧸ S.torus) ∈ (phanSystemE S).residue J ((1 : G) : G ⧸ S.torus) :=
  Iff.rfl

private theorem hmbTits_mem_parab_iff (S : PhanFamilyE K 2 f M G) (J : Set (Fin n)) (g : G) :
    g ∈ S.parab J ↔
      (g : G ⧸ S.torus) ∈ (phanSystemE S).residue J ((1 : G) : G ⧸ S.torus) := by
  constructor
  · have hle : S.parab J ≤ hmbTits_stabSub S J := by
      refine sup_le (fun x hx => ?_) (iSup₂_le fun j hj => ?_)
      · rw [hmbTits_mem_stabSub, show (x : G ⧸ S.torus) = ((1 : G) : G ⧸ S.torus) from
          QuotientGroup.eq.2 (by simpa using inv_mem hx)]
        exact self_mem_residue _ _
      · rintro _ ⟨A, rfl⟩
        rw [hmbTits_mem_stabSub]
        refine residue_mono (Set.singleton_subset_iff.2 hj) _ ?_
        rw [mem_residue_singleton, phanSystemE_adj_mk S, inv_one, one_mul]
        exact S.ι_mem_parab (Set.mem_singleton j) A
    exact fun hg => hle hg
  · intro hg
    obtain ⟨s, hs, hsg⟩ := exists_mem_of_mem_residue (fun i => S.torus_le_parab {i})
      (S.parab J) (fun j hj => S.parab_mono (Set.singleton_subset_iff.2 hj)) 1 hg
    have h1 : s⁻¹ * g ∈ S.torus := by
      have := QuotientGroup.eq.1 hsg
      simpa using inv_mem this
    have : g = s * (s⁻¹ * g) := by group
    rw [this]
    exact mul_mem hs (S.torus_le_parab J h1)

theorem universal_of_geometryE (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : PhanFamilyE K 2 f M G) (hg : S.Good) (hconn : (phanSystemE S).Connected)
    (hsc : (phanSystemE S).SimplyTwoConnected) : S.IsUniversal := by
  intro Y _ F
  obtain ⟨φ, hφ, hcompat⟩ := hg.exists_phi_family hK hq F
  have hsmul : ∀ g : G, (g • ((1 : G) : G ⧸ S.torus) : G ⧸ S.torus) = (g : G ⧸ S.torus) :=
    fun g => by rw [hmbTits_smul_mk, mul_one]
  obtain ⟨ψ, hψ, -⟩ := tits_chamber_universal_completion_of_family (phanSystemE S)
    (fun J => J.encard ≤ 2) (by simp) (fun i => by simp) hconn
    ((simplyTwoConnected_iff _).1 hsc) (G := G)
    (fun g i x y h => hmbTits_isMorphism_smul S g i x y h) ((1 : G) : G ⧸ S.torus)
    (fun c => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      exact ⟨a, hsmul a⟩)
    S.parab (fun J _ g => by rw [hsmul g]; exact hmbTits_mem_parab_iff S J g)
    (fun J hJ => φ J hJ)
    (fun J J' hJ hJ' hJJ' g hgJ' hgJ => hcompat J J' hJ hJ' hJJ' g hgJ' hgJ)
  have hι : ∀ (i : Fin n) (A : Su K 2 f 2), ψ (S.ι i A) = F.ι i A := by
    intro i A
    have hJ : ({i} : Set (Fin n)).encard ≤ 2 := by simp
    have := hψ {i} hJ ⟨S.ι i A, S.ι_mem_parab (Set.mem_singleton i) A⟩
    exact this.trans ((hφ {i} hJ).2 i (Set.mem_singleton i) A)
  refine ⟨ψ, fun i => MonoidHom.ext fun A => hι i A, fun i j hij hMij => ?_⟩
  refine MonoidHom.ext fun B => ?_
  have hle : B12 K 2 f ⊔ B23 K 2 f ≤
      MonoidHom.eqLocus (ψ.comp (S.θ i j)) (F.θ i j) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      show ψ (S.θ i j (embSUid (unitaryInvolution K 2 f) 2 A)) =
        F.θ i j (embSUid (unitaryInvolution K 2 f) 2 A)
      rw [show S.θ i j (embSUid (unitaryInvolution K 2 f) 2 A) = S.ι i A from
            DFunLike.congr_fun (S.left i j hij hMij) A,
          show F.θ i j (embSUid (unitaryInvolution K 2 f) 2 A) = F.ι i A from
            DFunLike.congr_fun (F.left i j hij hMij) A]
      exact hι i A
    · rintro _ ⟨A, rfl⟩
      show ψ (S.θ i j (embSUid (unitaryInvolution K 2 f) 0 A)) =
        F.θ i j (embSUid (unitaryInvolution K 2 f) 0 A)
      rw [show S.θ i j (embSUid (unitaryInvolution K 2 f) 0 A) = S.ι j A from
            DFunLike.congr_fun (S.right i j hij hMij) A,
          show F.θ i j (embSUid (unitaryInvolution K 2 f) 0 A) = F.ι j A from
            DFunLike.congr_fun (F.right i j hij hMij) A]
      exact hι j A
  rw [B12_sup_B23_eq_top hK (by omega : 2 ^ f ≠ 2)] at hle
  exact hle (Subgroup.mem_top B)

end CFSG.ClassicalInvolution.Phan.PhanE
