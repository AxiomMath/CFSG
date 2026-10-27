module

public import CFSG.Sporadic.Co2Smith.GlU62Ker
public import CFSG.Sporadic.Co2Smith.GlRootW1
public import CFSG.Sporadic.Co2Smith.GlSteinG

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem exists_thetaG_of
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    ∃ θ : SU6 →* G, ∀ γ ∈ su6D.roots, ∀ x : su6D.rootGroup γ, θ x = psiGS φ ρ γ x :=
  exists_thetaG hm (w1Levi_holds hz hm) (d1Core_holds hz hm)

@[expose] noncomputable def thetaG
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    SU6 →* G :=
  Classical.choose (exists_thetaG_of hz hm)

theorem thetaG_root
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {γ : Fin su6D.rank → ℤ}
    (hγ : γ ∈ su6D.roots) (x : su6D.rootGroup γ) :
    thetaG hz hm x = psiE φ ρ (thetaK (x : SU6)) := by
  rw [thetaG, Classical.choose_spec (exists_thetaG_of hz hm) γ hγ x, thetaK_spec hγ x]
  rfl

theorem thetaG_su6Pre
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {r : ℕ} (hr : r < 18)
    {t : ℕ} (ht : t < 4) : thetaG hz hm (su6Pre r t) = psiE φ ρ (xRootK r t) := by
  have := thetaG_root hz hm ((mem_su6D_roots_iff' _).2 ⟨⟨r, hr⟩, rfl⟩)
    ⟨su6Pre r t, su6Pre_mem hr t⟩
  rw [thetaK_su6Pre hr ht] at this
  exact this

theorem psiE_z0
    (hz : z ≠ 1) : psiE φ ρ z0 = z := by
  rw [psiE_of_mem φ ρ z0_mem_Cz, phiInv_z0 (phi_zC_of_ne_one φ hz)]

theorem rhoK_z0
    (hz : z ≠ 1) (hm : SmithC0Marking φ α3c ρ) :
    rhoK ρ z0 = z := by
  rw [rhoK_eq_phiInv hm z0_mem_C0c z0_mem_Cz, phiInv_z0 (phi_zC_of_ne_one φ hz)]

theorem x61K_not_mem_Cz :
    x61K ∉ Cz := fun h => x16K_x61K_ne (by
  rw [x16K_eq]
  exact (comm_of_mem_Cz h).symm)

theorem w1K_conj_x61K :
    w1K * x61K * w1K = z0 := by
  have h := conj_xRootK (g := 0) (r := 15) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  rwa [show Native.glWAct 0 15 1 = (12, 1) from rfl, wGen_zero, xRootK_15, xRootK_12] at h

theorem w1K_conj_z0 :
    w1K * z0 * w1K = x61K := by
  have h := conj_xRootK (g := 0) (r := 12) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  rwa [show Native.glWAct 0 12 1 = (15, 1) from rfl, wGen_zero, xRootK_15, xRootK_12] at h

theorem psiE_x61K
    {α : Cz}
    (hm : SmithC0Marking φ α ρ) : psiE φ ρ x61K = rhoK ρ x61K := by
  rw [psiE_of_not_mem φ ρ x61K_not_mem_Cz, w1K_conj_x61K, ← rhoK_eq_phiInv hm z0_mem_C0c z0_mem_Cz,
    ← rhoK_inv ρ w1K_mem_C0c, ← rhoK_mul ρ w1K_mem_C0c z0_mem_C0c,
    ← rhoK_mul ρ (C0c.mul_mem w1K_mem_C0c z0_mem_C0c) (C0c.inv_mem w1K_mem_C0c),
    inv_eq_of_mul_eq_one_right w1K_mul_self, w1K_conj_z0]

theorem rhoK_injOn {α : Cz} (hm : SmithC0Marking φ α ρ) {g g' : K}
    (hg : g ∈ C0c) (hg' : g' ∈ C0c) (h : rhoK ρ g = rhoK ρ g') : g = g' := by
  rw [rhoK_of_mem ρ hg, rhoK_of_mem ρ hg'] at h
  exact congrArg Subtype.val (hm.1 h)

theorem eq_one_of_comm_psiE
    (hz : z ≠ 1) (hm : SmithC0Marking φ α3c ρ)
    {c : G} (h : ∀ r < 18, ∀ t < 4, c * psiE φ ρ (xRootK r t) = psiE φ ρ (xRootK r t) * c) :
    c = 1 := by
  have hφz := phi_zC_of_ne_one φ hz
  have hcz : c * z = z * c := by
    have := h 12 (by norm_num) 1 (by norm_num)
    rwa [xRootK_12, psiE_z0 hz] at this
  set c' : centralizer ({z} : Set G) := ⟨c, mem_centralizer_singleton_iff.2 hcz⟩ with hc'
  have hcomm : ∀ y ∈ Cz, c * phiInv φ y = phiInv φ y * c → (φ c' : K) * y = y * (φ c' : K) := by
    intro y hy hyc
    have e : c' * φ.symm ⟨y, hy⟩ = φ.symm ⟨y, hy⟩ * c' := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← phiInv_of_mem φ hy]
      exact hyc
    have := congrArg (fun x => (φ x : K)) e
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] using this
  have hk0 : (φ c' : K) * z0 = z0 * (φ c' : K) := by
    refine hcomm z0 z0_mem_Cz ?_
    rw [phiInv_z0 hφz]
    exact hcz
  have hkr : ∀ r < 4, ∀ t < 4, (φ c' : K) * xRootK r t = xRootK r t * (φ c' : K) := by
    intro r hr t ht
    have hy : xRootK r t ∈ Cz := Qsub_le_Cz (xRootK_mem_Qsub hr ht)
    refine hcomm _ hy ?_
    rw [← psiE_of_mem φ ρ hy]
    exact h r (by omega) t ht
  rcases centralizer_Q _ (φ c').2 (comm_Qsub_of_comm_roots hk0 hkr) with h1 | h1
  · have : c' = 1 := φ.injective (by rw [map_one]; exact Subtype.ext h1)
    exact congrArg Subtype.val this
  · exfalso
    have hcz' : c' = zC z := φ.injective (by rw [hφz]; exact Subtype.ext h1)
    have hc : c = z := congrArg Subtype.val hcz'
    have h61 := h 15 (by norm_num) 1 (by norm_num)
    rw [xRootK_15, psiE_x61K hm, hc, ← rhoK_z0 hz hm, ← rhoK_mul ρ z0_mem_C0c x61K_mem_C0c,
      ← rhoK_mul ρ x61K_mem_C0c z0_mem_C0c] at h61
    apply x16K_x61K_ne
    rw [x16K_eq]
    exact rhoK_injOn hm (C0c.mul_mem z0_mem_C0c x61K_mem_C0c)
      (C0c.mul_mem x61K_mem_C0c z0_mem_C0c) h61

theorem ker_thetaG
    (hz : z ≠ 1) (hm : SmithC0Marking φ α3c ρ) :
    (thetaG hz hm).ker = center SU6 := by
  refine le_antisymm (ker_le_center_of_ne _ ⟨su6Pre 12 1, ?_⟩) fun ζ hζ => ?_
  · rw [thetaG_su6Pre hz hm (by norm_num) (by norm_num), xRootK_12, psiE_z0 hz]
    exact hz
  · refine MonoidHom.mem_ker.2 (eq_one_of_comm_psiE hz hm fun r hr t ht => ?_)
    rw [← thetaG_su6Pre hz hm hr ht, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.1 hζ (su6Pre r t)).symm]

end CFSG.Sporadic.Co2Smith
