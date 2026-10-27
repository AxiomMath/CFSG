module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQAux
public import Mathlib.Tactic.NormNum
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

noncomputable def permNorm (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (σ : Equiv.Perm (Fin 6)) : L :=
  Classical.choose (piOf_surjective θ (Psigma hK σ))

private theorem permNorm_pi (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (σ : Equiv.Perm (Fin 6)) : piOf θ (permNorm hK θ σ) = Psigma hK σ :=
  Classical.choose_spec (piOf_surjective θ (Psigma hK σ))

private theorem exists_mem_inf_pi_eq_torHom (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) :
    ∃ l : L, (l : G) ∈ Bs ⊓ L ∧ piOf θ l = torHom hK hω v := by
  have hm : (torHom hK hω v : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈
      ((Bs ⊓ L).subgroupOf L).map (piOf θ) := by
    rw [hmap]
    exact (torHom hK hω v).2
  obtain ⟨l, hlH, hlπ⟩ := Subgroup.mem_map.mp hm
  exact ⟨l, Subgroup.mem_subgroupOf.mp hlH, hlπ⟩

noncomputable def torPre (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) : L :=
  Classical.choose (exists_mem_inf_pi_eq_torHom hK θ hmap hω v)

private theorem torPre_mem (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) : (torPre hK θ hmap hω v : G) ∈ Bs ⊓ L :=
  (Classical.choose_spec (exists_mem_inf_pi_eq_torHom hK θ hmap hω v)).1

private theorem torPre_pi (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) :
    piOf θ (torPre hK θ hmap hω v) = torHom hK hω v :=
  (Classical.choose_spec (exists_mem_inf_pi_eq_torHom hK θ hmap hω v)).2

noncomputable def bsOf (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) : ↥Bs :=
  ⟨((torPre hK θ hmap hω v : L) : G),
    (Subgroup.mem_inf.mp (torPre_mem hK θ hmap hω v)).1⟩

theorem bsOf_coe_mem_L (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) : ((bsOf hK θ hmap hω v : ↥Bs) : G) ∈ L :=
  (Subgroup.mem_inf.mp (torPre_mem hK θ hmap hω v)).2

private theorem bsOf_mem_subgroupOf (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) :
    (⟨(bsOf hK θ hmap hω v : ↥Bs), bsOf_coe_mem_L hK θ hmap hω v⟩ : L) ∈
      (Bs ⊓ L).subgroupOf L := by
  rw [Subgroup.mem_subgroupOf]
  exact ⟨(bsOf hK θ hmap hω v).2, bsOf_coe_mem_L hK θ hmap hω v⟩

theorem bsOf_pi (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (v : ↥sumZeroSubgroup) :
    piOf θ ⟨(bsOf hK θ hmap hω v : ↥Bs), bsOf_coe_mem_L hK θ hmap hω v⟩ = torHom hK hω v := by
  have h : (⟨(bsOf hK θ hmap hω v : ↥Bs), bsOf_coe_mem_L hK θ hmap hω v⟩ : L) =
      torPre hK θ hmap hω v := by
    apply Subtype.ext
    rfl
  rw [h, torPre_pi]

private theorem bsOf_eq_iff (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) {v w : ↥sumZeroSubgroup} :
    bsOf hK θ hmap hω v = bsOf hK θ hmap hω w ↔
      torHom hK hω v = torHom hK hω w := by
  constructor
  · intro h
    have hval : (bsOf hK θ hmap hω v : G) = (bsOf hK θ hmap hω w : G) :=
      congrArg (fun y : ↥Bs => (y : G)) h
    have hL : (⟨(bsOf hK θ hmap hω v : ↥Bs),
        bsOf_coe_mem_L hK θ hmap hω v⟩ : L) =
        ⟨(bsOf hK θ hmap hω w : ↥Bs), bsOf_coe_mem_L hK θ hmap hω w⟩ :=
      Subtype.ext hval
    have h2 := congrArg (piOf θ) hL
    rw [bsOf_pi, bsOf_pi] at h2
    exact Subtype.ext h2
  · intro h
    apply Subtype.ext
    have hL : (⟨(bsOf hK θ hmap hω v : ↥Bs),
        bsOf_coe_mem_L hK θ hmap hω v⟩ : L) =
        ⟨(bsOf hK θ hmap hω w : ↥Bs), bsOf_coe_mem_L hK θ hmap hω w⟩ := by
      apply piOf_injective_of_pow_three θ hZ2
      · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω v)
      · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω w)
      · rw [bsOf_pi, bsOf_pi, h]
    exact congrArg (fun y : L => (y : G)) hL

theorem bsOf_surj (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (b : ↥Bs) (hbL : (b : G) ∈ L) :
    ∃ v : ↥sumZeroSubgroup, bsOf hK θ hmap hω v = b := by
  have hbL' : (⟨b, hbL⟩ : L) ∈ (Bs ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨b.2, hbL⟩
  have hmem : piOf θ ⟨b, hbL⟩ ∈ torU K := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (piOf θ) hbL'
  obtain ⟨v, hv⟩ := torHom_surjective hK hω ⟨piOf θ ⟨b, hbL⟩, hmem⟩
  refine ⟨v, ?_⟩
  refine Subtype.ext ?_
  have hL : (⟨(bsOf hK θ hmap hω v : ↥Bs),
      bsOf_coe_mem_L hK θ hmap hω v⟩ : L) = ⟨b, hbL⟩ := by
    apply piOf_injective_of_pow_three θ hZ2
    · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω v)
    · exact pow_three_of_mem_inf hBs hbL'
    · rw [bsOf_pi]
      exact congrArg Subtype.val hv
  exact congrArg (fun y : L => (y : G)) hL

@[expose] noncomputable def bsOfHom (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) : ↥sumZeroSubgroup →* ↥Bs where
  toFun := bsOf hK θ hmap hω
  map_one' := by
    apply Subtype.ext
    have hL : (⟨(bsOf hK θ hmap hω 1 : ↥Bs),
        bsOf_coe_mem_L hK θ hmap hω 1⟩ : L) = 1 := by
      apply piOf_injective_of_pow_three θ hZ2
      · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω 1)
      · exact one_pow 3
      · rw [bsOf_pi]
        simp
    simpa using congrArg (fun y : L => (y : G)) hL
  map_mul' v w := by
    apply Subtype.ext
    have hL : (⟨(bsOf hK θ hmap hω (v * w) : ↥Bs),
        bsOf_coe_mem_L hK θ hmap hω (v * w)⟩ : L) =
        (⟨(bsOf hK θ hmap hω v : ↥Bs), bsOf_coe_mem_L hK θ hmap hω v⟩ : L) *
          ⟨(bsOf hK θ hmap hω w : ↥Bs), bsOf_coe_mem_L hK θ hmap hω w⟩ := by
      apply piOf_injective_of_pow_three θ hZ2
      · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω (v * w))
      · apply pow_three_of_mem_inf hBs
        rw [Subgroup.mem_subgroupOf]
        exact ⟨Bs.mul_mem (bsOf hK θ hmap hω v).2 (bsOf hK θ hmap hω w).2,
          L.mul_mem (bsOf_coe_mem_L hK θ hmap hω v) (bsOf_coe_mem_L hK θ hmap hω w)⟩
      · rw [map_mul, bsOf_pi, bsOf_pi, bsOf_pi]
        exact congrArg Subtype.val (map_mul (torHom hK hω) v w)
    simpa using congrArg (fun y : L => (y : G)) hL

private theorem permNorm_conj_bsOf (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K)
    (hω : ω ^ 2 + ω + 1 = 0) (σ : Equiv.Perm (Fin 6)) (v : ↥sumZeroSubgroup) :
    (permNorm hK θ σ : G) * (bsOf hK θ hmap hω v : G) *
        ((permNorm hK θ σ : L) : G)⁻¹ =
      (bsOf hK θ hmap hω (permX σ v) : G) := by
  set l : L := permNorm hK θ σ with hl
  set b : L := ⟨(bsOf hK θ hmap hω v : ↥Bs), bsOf_coe_mem_L hK θ hmap hω v⟩ with hb
  have hmem1 : (l : G) * (b : G) * (l : G)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem l.2 b.2) (L.inv_mem l.2)
  have hmem2 : (bsOf hK θ hmap hω (permX σ v) : G) ∈ L :=
    bsOf_coe_mem_L hK θ hmap hω (permX σ v)
  have heq : (⟨_, hmem1⟩ : L) = l * b * l⁻¹ := by
    apply Subtype.ext
    rfl
  have hb3 : b ^ 3 = 1 := pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω v)
  have hL : (⟨_, hmem1⟩ : L) = ⟨_, hmem2⟩ := by
    apply piOf_injective_of_pow_three θ hZ2
    · rw [heq, conj_pow, hb3]
      group
    · exact pow_three_of_mem_inf hBs (bsOf_mem_subgroupOf hK θ hmap hω (permX σ v))
    · have hpi : piOf θ (⟨_, hmem1⟩ : L) =
          Psigma hK σ * torHom hK hω v * (Psigma hK σ)⁻¹ := by
        rw [heq, map_mul, map_mul, map_inv, hl, hb, permNorm_pi, bsOf_pi]
      calc piOf θ (⟨_, hmem1⟩ : L)
          = Psigma hK σ * torHom hK hω v * (Psigma hK σ)⁻¹ := hpi
        _ = torHom hK hω (permX σ v) := torHom_conj hK hω σ v
        _ = piOf θ ⟨(bsOf hK θ hmap hω (permX σ v) : ↥Bs),
            bsOf_coe_mem_L hK θ hmap hω (permX σ v)⟩ :=
            (bsOf_pi hK θ hmap hω (permX σ v)).symm
  simpa [hb] using congrArg Subtype.val hL

private theorem permNorm_mem_normalizer (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) :
    (permNorm hK θ σ : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  set l : L := permNorm hK θ σ with hl
  have hlx : (l : G) * x * (l : G)⁻¹ = x := by
    rw [show (l : G) * x = x * (l : G) from
      Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2)]
    group
  have hlP : (l : G) ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((l : G) * x * (l : G)⁻¹) = Subgroup.zpowers x
    rw [hlx]
  have hsup := Bs_eq_zpowers_sup hK θ hZ2 hBs hcard hmap hx hxL hLx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : Bs.map (MulAut.conj (l : G)).toMonoidHom ≤ Bs := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    change (l : G) * y * (l : G)⁻¹ ∈ Bs
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      exists_mul_zpowers hK θ hZ2 hmap hBs hcard hx hxL hLx hy
    rw [show (l : G) * (p * q) * (l : G)⁻¹ =
      ((l : G) * p * (l : G)⁻¹) * ((l : G) * q * (l : G)⁻¹) by group]
    rw [hsup]
    apply Subgroup.mul_mem_sup
    · exact (Subgroup.mem_normalizer_iff.mp hlP p).mp hp
    · obtain ⟨v, hv⟩ := bsOf_surj hK θ hZ2 hBs hmap hω ⟨q, hq.1⟩ hq.2
      have hqeq : (bsOf hK θ hmap hω v : G) = q := congrArg Subtype.val hv
      rw [← hqeq, permNorm_conj_bsOf hK θ hZ2 hBs hmap hω σ v]
      exact ⟨(bsOf hK θ hmap hω (permX σ v)).2,
        bsOf_coe_mem_L hK θ hmap hω (permX σ v)⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective).symm)

noncomputable def psi (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) : MulAut ↥Bs :=
  Subgroup.normalizerMonoidHom Bs
    ⟨(permNorm hK θ σ : L),
      permNorm_mem_normalizer hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ⟩

private theorem psi_apply_coe (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) (b : ↥Bs) :
    ((psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ b : ↥Bs) : G) =
      (permNorm hK θ σ : G) * (b : G) * ((permNorm hK θ σ : L) : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Bs
    ⟨(permNorm hK θ σ : L),
      permNorm_mem_normalizer hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ⟩ b

theorem psi_apply_bsOf (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) (v : ↥sumZeroSubgroup) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ (bsOf hK θ hmap hω v) =
      bsOf hK θ hmap hω (permX σ v) := by
  refine Subtype.ext ?_
  rw [psi_apply_coe]
  exact permNorm_conj_bsOf hK θ hZ2 hBs hmap hω σ v

theorem psi_mem_ggAutomizer (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ ∈ ggAutomizer L Bs := by
  apply Subgroup.subset_closure
  exact ⟨(permNorm hK θ σ : G), (permNorm hK θ σ).2,
    permNorm_mem_normalizer hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ,
    fun b => psi_apply_coe hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ b⟩

theorem psi_injective (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω) := by
  intro σ τ hστ
  have htor : ∀ v : ↥sumZeroSubgroup,
      torHom hK hω (permX σ v) = torHom hK hω (permX τ v) := by
    intro v
    have hb : bsOf hK θ hmap hω (permX σ v) =
        bsOf hK θ hmap hω (permX τ v) := by
      rw [← psi_apply_bsOf hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ v,
        ← psi_apply_bsOf hK θ hZ2 hBs hcard hmap hx hxL hLx hω τ v, hστ]
    exact (bsOf_eq_iff hK θ hZ2 hBs hmap hω).mp hb
  apply eq_of_permX_sub_const σ τ
  intro i j hij
  have hconst : permX σ (epsS hij) * (permX τ (epsS hij))⁻¹ ∈
      TorHomKernel.constSubgroup := by
    rw [← TorHomKernel.torHom_eq_one_iff hK hω]
    rw [map_mul, map_inv, htor (epsS hij), mul_inv_cancel]
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, fun k => ?_⟩
  have h := hc k
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
    Pi.neg_apply, sub_eq_add_neg] using h

private theorem psi_apply_x (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  refine Subtype.ext ?_
  rw [psi_apply_coe]
  rw [show (permNorm hK θ σ : G) * x = x * (permNorm hK θ σ : G) from
    Subgroup.mem_centralizer_singleton_iff.mp (hLx (permNorm hK θ σ).2)]
  group

theorem psi_fixes_zpowers (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    (σ : Equiv.Perm (Fin 6)) {p : ↥Bs} (hp : (p : G) ∈ Subgroup.zpowers x) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ p = p := by
  classical
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, orderOf_x_of_mem hBs hx hxL] at hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hp
  have hp_eq : p = ⟨x ^ i, Bs.pow_mem hx i⟩ := Subtype.ext hpi.symm
  rw [hp_eq]
  rw [show (⟨x ^ i, Bs.pow_mem hx i⟩ : ↥Bs) = (⟨x, hx⟩ : ↥Bs) ^ i from Subtype.ext rfl]
  rw [map_pow, psi_apply_x hK θ hZ2 hBs hcard hmap hx hxL hLx hω σ]

theorem psi_swap01_sq (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω (Equiv.swap 0 1) ^ 2 = 1 := by
  set ψ := psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω (Equiv.swap 0 1) with hψ
  apply MulEquiv.ext
  intro b
  obtain ⟨p, hp, q, hq, hb⟩ :=
    exists_mul_zpowers hK θ hZ2 hmap hBs hcard hx hxL hLx b.2
  set pbs : ↥Bs := ⟨p, Subgroup.zpowers_le.mpr hx hp⟩ with hpb
  set qbs : ↥Bs := ⟨q, hq.1⟩ with hqb
  have hb' : b = pbs * qbs := Subtype.ext hb.symm
  have hpp : ψ pbs = pbs :=
    psi_fixes_zpowers hK θ hZ2 hBs hcard hmap hx hxL hLx hω (Equiv.swap 0 1) hp
  have hqq : ψ (ψ qbs) = qbs := by
    obtain ⟨v, hv⟩ := bsOf_surj hK θ hZ2 hBs hmap hω qbs hq.2
    rw [← hv]
    rw [psi_apply_bsOf, psi_apply_bsOf]
    rw [TorConj.permX_invol_of (Equiv.swap 0 1)
      (fun i => Equiv.swap_apply_self 0 1 i) v]
  rw [hb', pow_two, MulAut.mul_apply]
  change ψ (ψ (pbs * qbs)) = pbs * qbs
  simp only [map_mul, hpp, hqq]

theorem psi_apply_swap01_threeAArg (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0) :
    psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω (Equiv.swap 0 1)
        (bsOf hK θ hmap hω threeAArg) = (bsOf hK θ hmap hω threeAArg)⁻¹ := by
  rw [psi_apply_bsOf, permX_swap01_threeAArg]
  change (bsOfHom hK θ hZ2 hBs hmap hω) threeAArg⁻¹ =
    ((bsOfHom hK θ hZ2 hBs hmap hω) threeAArg)⁻¹
  rw [map_inv]

theorem inv_mul_psi_swap01_mem_zpowers (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf θ) = USixTwo.torU K) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) (hω : ω ^ 2 + ω + 1 = 0)
    {q : ↥Bs} (hqL : (q : G) ∈ L) :
    q⁻¹ * psi hK θ hZ2 hBs hcard hmap hx hxL hLx hω (Equiv.swap 0 1) q ∈
      Subgroup.zpowers (bsOf hK θ hmap hω threeAArg) := by
  obtain ⟨v, hv⟩ := bsOf_surj hK θ hZ2 hBs hmap hω q hqL
  rw [← hv, psi_apply_bsOf]
  have hmem := inv_mul_permX_swap01_mem_zpowers v
  have hmapz : (bsOfHom hK θ hZ2 hBs hmap hω) (v⁻¹ * permX (Equiv.swap 0 1) v) ∈
      (Subgroup.zpowers threeAArg).map (bsOfHom hK θ hZ2 hBs hmap hω) :=
    Subgroup.mem_map_of_mem (bsOfHom hK θ hZ2 hBs hmap hω) hmem
  rw [MonoidHom.map_zpowers] at hmapz
  have hmul : (bsOfHom hK θ hZ2 hBs hmap hω) (v⁻¹ * permX (Equiv.swap 0 1) v) =
      (bsOf hK θ hmap hω v)⁻¹ * bsOf hK θ hmap hω (permX (Equiv.swap 0 1) v) := by
    rw [map_mul, map_inv]
    rfl
  rw [← hmul]
  exact hmapz

end CFSG.StandardType.E6QTwo

end
