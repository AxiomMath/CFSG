module

public import CFSG.Quasithin.Vol2.KGFact4413Sz

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.QuasithinUnique

@[expose] def InvOut {Y : Type*} [Group Y] (S D : Subgroup Y) : Prop :=
  (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧
    ∃ w : Y, w ∉ Subgroup.normalizer (S : Set Y) ∧ ∀ d ∈ D, w * d * w⁻¹ = d⁻¹

@[expose] def CartanInv (Y : Type*) [Group Y] : Prop :=
  ∀ S D : Subgroup Y, IsSylowTwoOf S ⊤ → D ≤ Subgroup.normalizer (S : Set Y) →
    Subgroup.normalizer (S : Set Y) ≤ D ⊔ S → D ⊓ S = ⊥ → InvOut S D

variable {X X' : Type} [Group X] [Group X']

theorem InvOut.map {S D : Subgroup X} (h : InvOut S D) (e : X ≃* X') :
    InvOut (S.map e.toMonoidHom) (D.map e.toMonoidHom) := by
  obtain ⟨hab, w, hwS, hact⟩ := h
  have hN : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq S e).symm
  refine ⟨?_, e w, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hab a ha b hb]
  · intro hw
    rw [hN] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    rw [MulEquiv.coe_toMonoidHom] at hww'
    exact hwS (e.injective hww' ▸ hw')
  · rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hact d hd, map_inv]

variable [Finite X]

theorem InvOut.of_complement {S D₀ D : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    (hD₀N : D₀ ≤ Subgroup.normalizer (S : Set X))
    (hND₀ : Subgroup.normalizer (S : Set X) ≤ D₀ ⊔ S) (hD₀S : D₀ ⊓ S = ⊥)
    (hDN : D ≤ Subgroup.normalizer (S : Set X))
    (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥) (h : InvOut S D₀) :
    InvOut S D := by
  have hcard : Nat.card D = Nat.card D₀ := by
    have h1 := card_normalizer_of_complement hDN hND hDS
    have h2 := card_normalizer_of_complement hD₀N hND₀ hD₀S
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  obtain ⟨s, hs, hDeq⟩ := E2.BorelLift.exists_conj_of_card_eq hS.2.1
    (odd_card_of_complement hS hD₀N hD₀S) hD₀N (hDN.trans hND₀) hcard
  have hSs : S.map (MulAut.conj s⁻¹).toMonoidHom = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact S.mul_mem (S.mul_mem (S.inv_mem hs) hy) (by simpa using hs)
    · intro hx
      refine ⟨s * x * s⁻¹, S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h1 := h.map (MulAut.conj s⁻¹)
  rwa [hSs, ← hDeq] at h1

theorem cartanInv_of_exists {S₀ D₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hD₀N : D₀ ≤ Subgroup.normalizer (S₀ : Set X))
    (hND₀ : Subgroup.normalizer (S₀ : Set X) ≤ D₀ ⊔ S₀) (hD₀S : D₀ ⊓ S₀ = ⊥)
    (h : InvOut S₀ D₀) : CartanInv X := by
  intro S D hS hDN hND hDS
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hS₀ hS
  set c := MulAut.conj g with hc
  have hSg : S₀.map c.toMonoidHom = S := by
    ext x
    rw [hg x]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hc, MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hN : Subgroup.normalizer (S : Set X) =
      (Subgroup.normalizer (S₀ : Set X)).map c.toMonoidHom := by
    rw [← hSg, Subgroup.map_equiv_normalizer_eq]
  have h1 := h.map c
  rw [hSg] at h1
  refine InvOut.of_complement hS ?_ ?_ ?_ hDN hND hDS h1
  · rw [hN]
    exact Subgroup.map_mono hD₀N
  · rw [hN, ← hSg, ← Subgroup.map_sup]
    exact Subgroup.map_mono hND₀
  · rw [← hSg, ← Subgroup.map_inf_eq _ _ _ c.injective, hD₀S, Subgroup.map_bot]

omit [Finite X] in
theorem cartanInv_of_mulEquiv (h : CartanInv X) (e : X ≃* X') : CartanInv X' := by
  intro S D hS hDN hND hDS
  have hmm : ∀ T : Subgroup X', (T.map e.symm.toMonoidHom).map e.toMonoidHom = T := by
    intro T
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hN : ∀ T : Subgroup X', Subgroup.normalizer ((T.map e.symm.toMonoidHom : Subgroup X) :
      Set X) = (Subgroup.normalizer (T : Set X')).map e.symm.toMonoidHom :=
    fun T => (Subgroup.map_equiv_normalizer_eq T e.symm).symm
  have h1 := h (S.map e.symm.toMonoidHom) (D.map e.symm.toMonoidHom)
    (isSylowTwoOf_map e.symm.surjective hS) (by rw [hN]; exact Subgroup.map_mono hDN)
    (by rw [hN, ← Subgroup.map_sup]; exact Subgroup.map_mono hND)
    (by rw [← Subgroup.map_inf_eq _ _ _ e.symm.injective, hDS, Subgroup.map_bot])
  have h2 := h1.map e
  rwa [hmm, hmm] at h2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H13.KG22

theorem cartanInv_projectiveSL2 {K : Type} [Field K] [Finite K] [CharP K 2] :
    CartanInv (projectiveSL 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  have hS : IsSylowTwoOf (projUnitriangular 2 K) ⊤ := hP ▸ isSylowTwoOf_of_sylow P
  obtain ⟨h1, h2, h3⟩ := dL2_complement (K := K)
  refine cartanInv_of_exists hS h1 h2 h3 ⟨?_, proj 2 K w2, ?_, fun d hd => proj_w2_conj_dL2 hd⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]
  · rw [normalizer_projUnitriangular_two]
    exact proj_w2_not_mem

theorem cartanInv_of_isPSL2 {Y : Type} [Group Y] {n : ℕ} (hn : 1 ≤ n) (hY : IsPSL 2 2 n Y) :
    CartanInv Y := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hY
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have e' : Y ≃* projectiveSL 2 K' := e.trans (Id2519.projectiveSLEquivStatedProj 2 K').symm
  exact cartanInv_of_mulEquiv cartanInv_projectiveSL2 e'.symm

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups in
theorem cartanInv_of_isSz {Y : Type} [Group Y] {n : ℕ} (hY : IsSz n Y) : CartanInv Y := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hY
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e' : Y ≃* SuzukiMatrixGroup a :=
    ((e.trans (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K))).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard)).trans
      ((MulEquiv.subgroupCongr hmodel.symm).trans
        (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a)))
  have : Finite (SuzukiMatrixGroup a) := inferInstance
  obtain ⟨S₀, D₀, hS₀, h1, h2, h3, -, hcyc, w, hwN, hwinv⟩ :=
    weylOut_suzukiMatrixGroup a (by omega)
  refine cartanInv_of_mulEquiv (cartanInv_of_exists hS₀ h1 h2 h3 ⟨fun x hx y hy => ?_, w, hwN,
    hwinv⟩) e'.symm
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hx' : x = ((g : SuzukiMatrixGroup a) : _) ^ i := by
    rw [← Subgroup.coe_zpow, hi]
  have hy' : y = ((g : SuzukiMatrixGroup a) : _) ^ j := by
    rw [← Subgroup.coe_zpow, hj]
  rw [hx', hy', ← _root_.zpow_add, ← _root_.zpow_add, add_comm i j]

end CFSG.Quasithin.H13.KG4413
