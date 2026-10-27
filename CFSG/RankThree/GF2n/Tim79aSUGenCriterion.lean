module

public import CFSG.Timmesfeld.Transvection.ModelSUTransvLe
public import CFSG.RankThree.GF2n.Tim79aSURootS1
public import CFSG.Timmesfeld.Transvection.ModelSUGen
public import CFSG.Timmesfeld.Transvection.ModelSUTheta

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
  CFSG.LieType.BorelTits

section General

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}

theorem eq_top_of_uTransLe_pair_of (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) (hnorm : ∀ c, σ c = c → ∃ l, σ l * l = c)
    (hG : ∀ L : Subgroup (SU σ m), (∀ (v : Fin m → F) (X : Subgroup (SU σ m)),
      uForm σ v v = 0 → IsUTransGroup σ v X → X ≤ L) → L = ⊤) (hm : 4 ≤ m)
    {a d w₀ : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (hw₀ : w₀ ∈ perpPair σ a d) (hw₀0 : w₀ ≠ 0)
    (hw₀w₀ : uForm σ w₀ w₀ = 0) {L : Subgroup (SU σ m)} (ha : UTransLe L a) (hd : UTransLe L d)
    (hP : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → UTransLe L v)
    (hS : ∀ ν : F, ∃ z ∈ L, z ∈ uRad σ a ∧ radVec σ a d z = ν • w₀) : L = ⊤ := by
  have h1tr : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at had
    exact zero_ne_one had
  obtain ⟨T, hT⟩ := exists_isUTransGroup hσ haa
  have Θ := suThetaFacts_holds hσ htr haa hdd had hT
  have G := suGeomFacts_holds hσ htr hnorm hm haa hdd had
  set S : Set (Fin m → F) :=
    {w | ∃ z ∈ L, z ∈ uRad σ a ∧ radVec σ a d z = w} with hSdef
  have hS0 : (0 : Fin m → F) ∈ S := ⟨1, L.one_mem, (uRad σ a).one_mem, Θ.one⟩
  have hSadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S := by
    rintro x ⟨z, hzL, hzR, rfl⟩ y ⟨z', hz'L, hz'R, rfl⟩
    exact ⟨z * z', L.mul_mem hzL hz'L, (uRad σ a).mul_mem hzR hz'R, Θ.mul hzR hz'R⟩
  have hprop : ∀ x ∈ perpPair σ a d, (∀ ν : F, ν • x ∈ S) → ∀ v ∈ perpPair σ a d,
      uForm σ v v = 0 → uForm σ v x ≠ 0 → ∀ ν : F, ν • v ∈ S := by
    intro x hx hxS v hv hvv hvx ν
    obtain ⟨z, hzL, hzR, hzv⟩ := hxS (ν * (uForm σ v x)⁻¹)
    obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hvv h1tr
    have htL : t ∈ L := hP v hv hvv 1 t h1tr ht
    have hta' : suMat σ m t *ᵥ a = (1 : F) • a := by rw [Θ.transv_a hv ht, one_smul]
    have htline : t ∈ uLine σ a := ⟨1, one_ne_zero, hta'⟩
    have hxs : (ν * (uForm σ v x)⁻¹) • x ∈ perpPair σ a d := Submodule.smul_mem _ _ hx
    refine ⟨t * z * t⁻¹ * z⁻¹, L.mul_mem (L.mul_mem (L.mul_mem htL hzL) (L.inv_mem htL))
      (L.inv_mem hzL), (uRad σ a).mul_mem (conj_mem_uRad htline hzR) ((uRad σ a).inv_mem hzR),
      ?_⟩
    have hν : ν * (uForm σ v x)⁻¹ * uForm σ v x = ν := by
      rw [mul_assoc, inv_mul_cancel₀ hvx, mul_one]
    rw [Θ.mul (conj_mem_uRad htline hzR) ((uRad σ a).inv_mem hzR), Θ.inv hzR,
      Θ.conj hta' hzR, map_one, one_smul, hzv, Θ.levAct_transv hv hvv ht hxs,
      uForm_smul_right, one_mul, hν]
    abel
  have hS' : ∀ ν : F, ν • w₀ ∈ S := hS
  have hiso : ∀ v ∈ perpPair σ a d, uForm σ v v = 0 → v ≠ 0 → ∀ ν : F, ν • v ∈ S := by
    intro v hv hvv hv0
    obtain ⟨y, hy, hyy, hw₀y, hvy⟩ := G.both hw₀ hv hw₀0 hv0 hw₀w₀ hvv
    have hyw₀ : uForm σ y w₀ ≠ 0 := by
      rw [← uForm_conj σ hσ]
      exact (map_ne_zero σ).2 hw₀y
    have hyS := hprop w₀ hw₀ hS' y hy hyy hyw₀
    exact hprop y hy hyS v hv hvv hvy
  have hSP : ∀ w ∈ perpPair σ a d, w ∈ S := by
    intro w hw
    obtain ⟨e₁, he₁, e₂, he₂, he₁₁, he₂₂, rfl⟩ := G.sum hw
    have hmem : ∀ e ∈ perpPair σ a d, uForm σ e e = 0 → e ∈ S := by
      intro e he hee
      by_cases he0 : e = 0
      · rw [he0]
        exact hS0
      · have := hiso e he hee he0 1
        rwa [one_smul] at this
    exact hSadd _ (hmem e₁ he₁ he₁₁) _ (hmem e₂ he₂ he₂₂)
  have hTL : T ≤ L := (uTransLe_iff hT).1 ha
  have hQL : uRad σ a ≤ L := by
    intro z hz
    obtain ⟨z', hz'L, hz'R, hz'v⟩ := hSP _ (Θ.mem_perp z)
    have hmem : z'⁻¹ * z ∈ uRad σ a := (uRad σ a).mul_mem ((uRad σ a).inv_mem hz'R) hz
    have hzT : z'⁻¹ * z ∈ T := by
      refine (Θ.eq_zero_iff hmem).1 ?_
      rw [Θ.mul ((uRad σ a).inv_mem hz'R) hz, Θ.inv hz'R, hz'v, neg_add_cancel]
    have hz_eq : z = z' * (z'⁻¹ * z) := by group
    rw [hz_eq]
    exact L.mul_mem hz'L (hTL hzT)
  obtain ⟨s, hs⟩ := exists_suMat_eq_uTrans hσ haa h1tr
  obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hdd h1tr
  have e1 : uTrans σ a 1 *ᵥ a = a := by rw [uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
  have e2 : uTrans σ d 1 *ᵥ a = a + d := by rw [uTrans_mulVec, hda, mul_one, one_smul]
  have e3 : uTrans σ a 1 *ᵥ (a + d) = d := by
    rw [uTrans_mulVec, uForm_add_right, haa, had, zero_add, mul_one, one_smul]
    funext i
    simp only [Pi.add_apply]
    linear_combination (a i) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have hgd : suMat σ m (s * t * s) *ᵥ a = d := by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hs, ht, e1, e2, e3]
  have hTg := hT.conjSub (s * t * s)
  rw [hgd] at hTg
  obtain ⟨x, hx⟩ := hTg.2 1 h1tr
  have hxmem : x ∈ conjSub T (s * t * s) := (hTg.1 x).2 ⟨1, h1tr, hx⟩
  have hxL : x ∈ L := hd 1 x h1tr hx
  have hx1 : x ≠ 1 := by
    intro h1
    have hxa := congrArg (fun M => M *ᵥ a) hx
    simp only [h1, map_one, one_mulVec, uTrans_mulVec, hda, mul_one, one_smul] at hxa
    apply hd0
    have := congrArg (fun v => v - a) hxa
    simpa using this.symm
  have hg : ¬ Commuting T (conjSub T (s * t * s)) := by
    intro hc
    rcases IsUTransGroup.uForm_eq_zero hσ one_ne_zero h1tr hT hTg ha0 hc with h0 | ⟨l, hl⟩
    · rw [had] at h0
      exact one_ne_zero h0
    · rw [hl, uForm_smul_right, haa, mul_zero] at had
      exact zero_ne_one had
  have hB : SUBothStmt σ m := fun ha hu haa huu => exists_isotropic_both hσ htr ha hu haa huu
  have htop := CFSG.RankThree.GF2n.Tim79a.uRad_sup_zpowers_eq_top_of_involutive hσ hG hB ha0
    haa hT hg hxmem hx1
  rw [eq_top_iff, ← htop]
  exact sup_le hQL ((Subgroup.zpowers_le).2 hxL)

end General

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem eq_top_of_uTransLe_pair (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    {a d w₀ : Fin m → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1)
    (hw₀ : w₀ ∈ perpPair (unitaryInvolution F 2 f) a d) (hw₀0 : w₀ ≠ 0)
    (hw₀w₀ : uForm (unitaryInvolution F 2 f) w₀ w₀ = 0)
    {L : Subgroup (SU (unitaryInvolution F 2 f) m)} (ha : UTransLe L a) (hd : UTransLe L d)
    (hP : ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
      uForm (unitaryInvolution F 2 f) v v = 0 → UTransLe L v)
    (hS : ∀ ν : F, ∃ z ∈ L, z ∈ uRad (unitaryInvolution F 2 f) a ∧
      radVec (unitaryInvolution F 2 f) a d z = ν • w₀) : L = ⊤ :=
  eq_top_of_uTransLe_pair_of (unitaryInvolution_involutive hF)
    (fun c hc => exists_add_unitaryInvolution_eq hF hc)
    (fun c hc => exists_sigma_mul_self_eq hF hc)
    (fun _ h => eq_top_of_forall_isUTransGroup_le hF hm h) hm haa hdd had hw₀ hw₀0 hw₀w₀ ha hd
    hP hS

end Finite

end CFSG.Timmesfeld.Transvection.ModelRank
