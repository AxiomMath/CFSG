module

public import CFSG.Quasithin.Background.HStandard
import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorAlg
import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open scoped Matrix

open CFSG.Quasithin.H
open CFSG.RankThree.GF2n.Stroth80

section

variable {K : Type} [Field K] {m : ℕ}

section
variable [CharP K 2]

private lemma pMat_add {ω : K} (hωsum : ω + ω ^ 2 = 1)
    (D : Matrix (Fin m) (Fin m) K) :
    (D + ω • 1) + (D + ω ^ 2 • 1) = (1 : Matrix (Fin m) (Fin m) K) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp only [if_pos h, smul_eq_mul, mul_one]
    have h2 : D i j + D i j = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2 + hωsum
  · simp only [if_neg h, smul_zero, add_zero]
    exact CharTwo.add_self_eq_zero _

private lemma pMat_add_apply {ω : K} (hωsum : ω + ω ^ 2 = 1)
    (D : Matrix (Fin m) (Fin m) K) (v : Fin m → K) :
    ((D + ω • 1) + (D + ω ^ 2 • 1)) *ᵥ v = v := by
  rw [pMat_add hωsum D, Matrix.one_mulVec]

private lemma d_sq (D : Matrix (Fin m) (Fin m) K) (hD : D * D + D + 1 = 0) :
    D * D = D + 1 := by
  ext i j
  have h : (D * D + D + 1) i j = 0 := by rw [hD, Matrix.zero_apply]
  simp only [Matrix.add_apply, Matrix.one_apply] at h
  rw [add_assoc] at h
  exact (CharTwo.add_eq_zero (R := K)).mp h

private lemma scalar_facts {c : K} (hc : c ^ 2 + c + 1 = 0) :
    (1 : K) + c = c ^ 2 ∧ c ^ 3 = 1 ∧ c ^ 4 = c := by
  have hc2c : c ^ 2 + c = 1 := (CharTwo.add_eq_zero (R := K)).mp hc
  have hc1 : (1 : K) + c = c ^ 2 := by
    rw [← hc2c, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  refine ⟨hc1, hc3, ?_⟩
  rw [show c ^ 4 = c ^ 3 * c by ring, hc3, one_mul]

private lemma pMat_d_apply_mat (D : Matrix (Fin m) (Fin m) K) (hD : D * D + D + 1 = 0)
    {c : K} (hc : c ^ 2 + c + 1 = 0) :
    D * (D + c • 1) = c ^ 2 • (D + c • 1) := by
  obtain ⟨hc1, hc3, -⟩ := scalar_facts hc
  calc D * (D + c • 1)
      = D * D + D * (c • 1) := by rw [Matrix.mul_add]
  _ = (D + 1) + c • D := by rw [d_sq D hD, Matrix.mul_smul, Matrix.mul_one]
  _ = (D + c • D) + 1 := by abel
  _ = (1 + c) • D + 1 := by rw [add_smul, one_smul]
  _ = c ^ 2 • D + 1 := by rw [hc1]
  _ = c ^ 2 • D + c ^ 3 • 1 := by rw [hc3, one_smul]
  _ = c ^ 2 • (D + c • 1) := by
    rw [smul_add, smul_smul, show c ^ 2 * c = c ^ 3 by ring]

private lemma pMat_d_apply (D : Matrix (Fin m) (Fin m) K) (hD : D * D + D + 1 = 0)
    {c : K} (hc : c ^ 2 + c + 1 = 0) (v : Fin m → K) :
    D *ᵥ ((D + c • 1) *ᵥ v) = c ^ 2 • ((D + c • 1) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, pMat_d_apply_mat D hD hc, Matrix.smul_mulVec]

end

private lemma pMat_d_comm_mat (D : Matrix (Fin m) (Fin m) K) {c : K} :
    (D + c • 1) * D = D * (D + c • 1) := by
  have h : Commute D (D + c • 1) :=
    (Commute.refl D).add_right ((Commute.one_right D).smul_right c)
  exact h.eq.symm

private lemma pMat_d_comm (D : Matrix (Fin m) (Fin m) K) {c : K} (v : Fin m → K) :
    (D + c • 1) *ᵥ (D *ᵥ v) = D *ᵥ ((D + c • 1) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pMat_d_comm_mat D]

section
variable [CharP K 2]

private lemma pImage_smul_mem [Finite K] (D : Matrix (Fin m) (Fin m) K)
    (hD : D * D + D + 1 = 0) {c : K} (hc : c ^ 2 + c + 1 = 0)
    (S : AddSubgroup (Fin m → K)) (hDS : ∀ v ∈ S, D *ᵥ v ∈ S)
    (hK4 : Nat.card K = 4) {x : K} {v : Fin m → K}
    (hv : v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) :
    x • v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom := by
  classical
  obtain ⟨-, -, hc4⟩ := scalar_facts hc
  have key : ∀ w ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom,
      D *ᵥ w ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom ∧ D *ᵥ w = c ^ 2 • w := by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hw
    change D *ᵥ ((D + c • 1) *ᵥ s) ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom ∧
      D *ᵥ ((D + c • 1) *ᵥ s) = c ^ 2 • ((D + c • 1) *ᵥ s)
    refine ⟨?_, pMat_d_apply D hD hc s⟩
    rw [← pMat_d_comm D s]
    exact AddSubgroup.mem_map.mpr ⟨D *ᵥ s, hDS s hs, rfl⟩
  obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hv
  let w : Fin m → K := (D + c • 1) *ᵥ s
  have hw : w ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom :=
    AddSubgroup.mem_map.mpr ⟨s, hs, rfl⟩
  change x • w ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom
  let : Fintype K := Fintype.ofFinite K
  have hx : x ∈ ({0, 1, c, c ^ 2} : Finset K) := by
    rw [← TauCeti.univ_eq_zero_one_root_sq hK4 hc]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx0 | hx1 | hxc | hxc2
  · rw [hx0, zero_smul]; exact (S.map _).zero_mem
  · rw [hx1, one_smul]; exact hw
  · rw [hxc]
    have h1 := (key w hw).1
    have h2 := (key (D *ᵥ w) h1).1
    have hc2sq : c = (c ^ 2) ^ 2 := by
      rw [show (c ^ 2) ^ 2 = c ^ 4 by ring, hc4]
    have hEq : c • w = D *ᵥ (D *ᵥ w) := by
      rw [hc2sq, show (c ^ 2) ^ 2 = c ^ 2 * c ^ 2 by ring, ← smul_smul,
        ← (key w hw).2, ← (key (D *ᵥ w) h1).2]
    rw [hEq]; exact h2
  · rw [hxc2, ← (key w hw).2]; exact (key w hw).1

end

private lemma pMat_psi {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K)
    (hDψ : ∀ g, D * (ψ g : Matrix (Fin m) (Fin m) K) =
      (ψ g : Matrix (Fin m) (Fin m) K) * D)
    {c : K} (g : G) (v : Fin m → K) :
    (D + c • 1) *ᵥ ((ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v) =
      (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ ((D + c • 1) *ᵥ v) := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hDψ g]

private lemma pImage_psi_mem {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K)
    (hDψ : ∀ g, D * (ψ g : Matrix (Fin m) (Fin m) K) =
      (ψ g : Matrix (Fin m) (Fin m) K) * D)
    {c : K} (S : AddSubgroup (Fin m → K))
    (hSinv : ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (g : G) {v : Fin m → K}
    (hv : v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) :
    (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈
      S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom := by
  let P : Matrix (Fin m) (Fin m) K := D + c • 1
  let f : (Fin m → K) →+ (Fin m → K) := (Matrix.mulVecLin P).toAddMonoidHom
  have hf : ∀ w, f w = P *ᵥ w := fun w => rfl
  change v ∈ S.map f at hv
  obtain ⟨s, hs, hsv⟩ := AddSubgroup.mem_map.mp hv
  rw [← hsv]
  exact AddSubgroup.mem_map.mpr ⟨(ψ g : Matrix (Fin m) (Fin m) K) *ᵥ s, hSinv g s hs,
    by rw [hf, hf]; exact pMat_psi ψ D hDψ g s⟩

private lemma pImage_irreducible {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K) (hDψ : ∀ g,
      D * (ψ g : Matrix (Fin m) (Fin m) K) = (ψ g : Matrix (Fin m) (Fin m) K) * D)
    {c : K} (S : AddSubgroup (Fin m → K))
    (hSinv : ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (hirrS : ∀ T : AddSubgroup (Fin m → K), T ≤ S →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = S)
    {T : AddSubgroup (Fin m → K)}
    (hT : T ≤ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom)
    (hTinv : ∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) :
    T = ⊥ ∨ T = S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom := by
  let P : Matrix (Fin m) (Fin m) K := D + c • 1
  let f : (Fin m → K) →+ (Fin m → K) := (Matrix.mulVecLin P).toAddMonoidHom
  have hf : ∀ w, f w = P *ᵥ w := fun w => rfl
  have hpsi : ∀ (g : G) (w : Fin m → K), f ((ψ g : Matrix (Fin m) (Fin m) K) *ᵥ w) =
      (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ f w := by
    intro g w
    rw [hf, hf]
    exact pMat_psi ψ D hDψ g w
  change T ≤ S.map f at hT
  change T = ⊥ ∨ T = S.map f
  by_cases hTbot : T = ⊥
  · exact Or.inl hTbot
  · refine Or.inr (le_antisymm hT ?_)
    let T' : AddSubgroup (Fin m → K) := S ⊓ T.comap f
    have hT'le : T' ≤ S := inf_le_left
    have hT'inv : ∀ g, ∀ v ∈ T', (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T' := by
      intro g v hv
      obtain ⟨hvS, hvT⟩ := AddSubgroup.mem_inf.mp hv
      have hfvT : f v ∈ T := AddSubgroup.mem_comap.mp hvT
      refine AddSubgroup.mem_inf.mpr ⟨hSinv g v hvS, AddSubgroup.mem_comap.mpr ?_⟩
      rw [hpsi]
      exact hTinv g (f v) hfvT
    have hT'ne : T' ≠ ⊥ := by
      have hex : ∃ y ∈ T, y ≠ 0 := by
        by_contra h
        apply hTbot
        apply le_antisymm _ bot_le
        intro y hy
        rw [AddSubgroup.mem_bot]
        by_contra hy0
        exact h ⟨y, hy, hy0⟩
      obtain ⟨y, hyT, hy0⟩ := hex
      have hy : y ∈ S.map f := hT hyT
      obtain ⟨s, hs, hsv⟩ := AddSubgroup.mem_map.mp hy
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hsv
        exact hy0 hsv.symm
      intro hbot
      have hsT' : s ∈ T' := by
        refine AddSubgroup.mem_inf.mpr ⟨hs, AddSubgroup.mem_comap.mpr ?_⟩
        rwa [hsv]
      rw [hbot] at hsT'
      exact hs0 (by simpa using hsT')
    rcases hirrS T' hT'le hT'inv with hbot | htop
    · exact absurd hbot hT'ne
    · intro x hx
      obtain ⟨s, hs, hsv⟩ := AddSubgroup.mem_map.mp hx
      have hsT' : s ∈ T' := by rw [htop]; exact hs
      have hfs : f s ∈ T := AddSubgroup.mem_comap.mp (AddSubgroup.mem_inf.mp hsT').2
      rwa [hsv] at hfs

private lemma pImage_injOn {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K) (hDψ : ∀ g,
      D * (ψ g : Matrix (Fin m) (Fin m) K) = (ψ g : Matrix (Fin m) (Fin m) K) * D)
    {c : K} (S : AddSubgroup (Fin m → K))
    (hSinv : ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (hirrS : ∀ T : AddSubgroup (Fin m → K), T ≤ S →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = S)
    (hne : S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom ≠ ⊥) :
    Set.InjOn (fun v : Fin m → K => (D + c • 1) *ᵥ v) (S : Set (Fin m → K)) := by
  let P : Matrix (Fin m) (Fin m) K := D + c • 1
  let f : (Fin m → K) →+ (Fin m → K) := (Matrix.mulVecLin P).toAddMonoidHom
  have hf : ∀ w, f w = P *ᵥ w := fun w => rfl
  have hpsi : ∀ (g : G) (w : Fin m → K), f ((ψ g : Matrix (Fin m) (Fin m) K) *ᵥ w) =
      (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ f w := by
    intro g w
    rw [hf, hf]
    exact pMat_psi ψ D hDψ g w
  let K' : AddSubgroup (Fin m → K) := S ⊓ f.ker
  have hK'le : K' ≤ S := inf_le_left
  have hK'inv : ∀ g, ∀ v ∈ K', (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ K' := by
    intro g v hv
    obtain ⟨hvS, hvker⟩ := AddSubgroup.mem_inf.mp hv
    refine AddSubgroup.mem_inf.mpr ⟨hSinv g v hvS, ?_⟩
    rw [AddMonoidHom.mem_ker] at hvker ⊢
    rw [hpsi, hvker, Matrix.mulVec_zero]
  have hK'bot : K' = ⊥ := by
    rcases hirrS K' hK'le hK'inv with hbot | htop
    · exact hbot
    · exfalso
      apply hne
      rw [AddSubgroup.map_eq_bot_iff]
      rw [← htop]
      exact inf_le_right
  intro x hx y hy hxy
  have hsub : x - y ∈ K' := by
    refine AddSubgroup.mem_inf.mpr ⟨S.sub_mem hx hy, ?_⟩
    rw [AddMonoidHom.mem_ker, hf]
    have hxy' : P *ᵥ x = P *ᵥ y := hxy
    rw [Matrix.mulVec_sub, hxy', sub_self]
  rw [hK'bot, AddSubgroup.mem_bot] at hsub
  exact sub_eq_zero.mp hsub

private lemma pImage_card {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K) (hDψ : ∀ g,
      D * (ψ g : Matrix (Fin m) (Fin m) K) = (ψ g : Matrix (Fin m) (Fin m) K) * D)
    {c : K} (S : AddSubgroup (Fin m → K))
    (hSinv : ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (hirrS : ∀ T : AddSubgroup (Fin m → K), T ≤ S →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = S)
    (hne : S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom ≠ ⊥) :
    Nat.card ↥(S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) = Nat.card ↥S := by
  let P : Matrix (Fin m) (Fin m) K := D + c • 1
  let f : (Fin m → K) →+ (Fin m → K) := (Matrix.mulVecLin P).toAddMonoidHom
  have hinj : Set.InjOn (fun v : Fin m → K => P *ᵥ v) (S : Set (Fin m → K)) :=
    pImage_injOn ψ D hDψ S hSinv hirrS hne
  calc
    Nat.card ↥(S.map f) = Nat.card ((S.map f : Set (Fin m → K))) := Nat.card_coe_set_eq _
    _ = Nat.card ((fun v : Fin m → K => P *ᵥ v) '' (S : Set (Fin m → K))) := by
      rw [AddSubgroup.coe_map]
      rfl
    _ = Nat.card ↥S := by
      rw [Nat.card_image_of_injOn hinj]
      exact (Nat.card_coe_set_eq (S : Set (Fin m → K))).symm

private lemma exists_planes_of_iSupIndep {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {m : ℕ} (hK4 : Nat.card K = 4)
    (ψ : G →* GL (Fin m) K) {ι : Type} [Fintype ι]
    (W : ι → AddSubgroup (Fin m → K))
    (hWsub : ∀ i (c : K) (v : Fin m → K), v ∈ W i → c • v ∈ W i)
    (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hcard16 : ∀ i, Nat.card ↥(W i) = 16)
    (hinv : ∀ i g, ∀ v ∈ W i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ W i)
    (hfaith : ∀ i g, (∀ v ∈ W i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) :
    ∃ (n : ℕ) (R : Fin n → Submodule K (Fin m → K)), iSupIndep R ∧ iSup R = ⊤ ∧
      (∀ i, Module.finrank K ↥(R i) = 2) ∧
      (∀ i g, ∀ v ∈ R i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R i) ∧
      (∀ i g, (∀ v ∈ R i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) := by
  classical
  let n : ℕ := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let Wf : Fin n → AddSubgroup (Fin m → K) := fun i => W (e.symm i)
  have hWf_ind : iSupIndep Wf := by
    change iSupIndep (fun i : Fin n => W (e.symm i))
    exact hind.comp e.symm.injective
  have hWf_top : (⨆ i : Fin n, Wf i) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun j => ?_
    rw [show W j = Wf (e j) from by simp only [Wf, Equiv.symm_apply_apply]]
    exact le_iSup (fun i : Fin n => Wf i) (e j)
  have hWf_smul : ∀ i (c : K) (v : Fin m → K), v ∈ Wf i → c • v ∈ Wf i := by
    intro i c v hv
    change v ∈ W (e.symm i) at hv
    change c • v ∈ W (e.symm i)
    exact hWsub (e.symm i) c v hv
  let R : Fin n → Submodule K (Fin m → K) := fun i =>
    { carrier := Wf i
      add_mem' := fun {a b} ha hb => (Wf i).add_mem ha hb
      zero_mem' := (Wf i).zero_mem
      smul_mem' := fun c v hv => hWf_smul i c v hv }
  refine ⟨n, R, ?_, ?_, ?_, ?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hxi hxj
    let Jne := {j : Fin n // j ≠ i}
    let A : AddSubgroup (Fin m → K) := ⨆ j : Jne, Wf j.1
    have hA_smul : ∀ (c : K) (v : Fin m → K), v ∈ A → c • v ∈ A := by
      intro c v hv
      exact smul_mem_iSup_addSubgroup (fun j : Jne => Wf j.1)
        (fun j c v hv => hWf_smul j.1 c v hv) hv
    let S : Submodule K (Fin m → K) :=
      { carrier := A
        add_mem' := fun {a b} ha hb => A.add_mem ha hb
        zero_mem' := A.zero_mem
        smul_mem' := fun c v hv => hA_smul c v hv }
    have hRS : ∀ j : Jne, R j.1 ≤ S := by
      intro j y hy
      exact AddSubgroup.mem_iSup_of_mem j hy
    have hxjS : x ∈ S := by
      have hxj' : x ∈ ⨆ j : Jne, R j.1 := by
        rw [iSup_subtype]
        exact hxj
      exact (Submodule.mem_iSup (fun j : Jne => R j.1)).mp hxj' S hRS
    have hAeq : (⨆ (j) (_ : j ≠ i), Wf j) = A := by
      rw [show A = ⨆ j : Jne, Wf j.1 from rfl, iSup_subtype]
    have hdisj : Disjoint (Wf i) A := by
      simpa only [hAeq] using hWf_ind i
    have hx0 : x ∈ (⊥ : AddSubgroup (Fin m → K)) := by
      have hmem : x ∈ Wf i ⊓ A := ⟨hxi, hxjS⟩
      rw [disjoint_iff.mp hdisj] at hmem
      exact hmem
    simpa using hx0
  · apply Submodule.toAddSubgroup_injective
    rw [Submodule.top_toAddSubgroup]
    refine le_antisymm le_top ?_
    have hle : (⨆ i : Fin n, Wf i) ≤ (⨆ i : Fin n, R i).toAddSubgroup := by
      refine iSup_le fun i => ?_
      have h := Submodule.toAddSubgroup_mono (le_iSup (fun i : Fin n => R i) i)
      have hWi : (R i).toAddSubgroup = Wf i := rfl
      rwa [hWi] at h
    rw [hWf_top] at hle
    exact hle
  · intro i
    have hcardR : Nat.card ↥(R i) = 16 := by
      have h : Nat.card ↥(R i) = Nat.card ↥(Wf i) := rfl
      rw [h, hcard16 (e.symm i)]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥(R i))
    rw [hcardR, hK4] at h
    exact Nat.pow_right_injective (by norm_num : 1 < 4)
      (h.symm.trans (by norm_num : (16 : ℕ) = 4 ^ 2))
  · intro i g v hv
    change v ∈ Wf i at hv
    exact hinv (e.symm i) g v hv
  · intro i g hfix
    apply hfaith (e.symm i) g
    intro v hv
    exact hfix v hv

section
variable [CharP K 2]

private lemma pImage_facts [Finite K] {G : Type} [Group G] (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K) (hD : D * D + D + 1 = 0)
    (hDψ : ∀ g, D * (ψ g : Matrix (Fin m) (Fin m) K) =
      (ψ g : Matrix (Fin m) (Fin m) K) * D)
    (S : AddSubgroup (Fin m → K)) {c : K} (hc : c ^ 2 + c + 1 = 0)
    (hSinv : ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (hDS : ∀ v ∈ S, D *ᵥ v ∈ S)
    (hirrS : ∀ T : AddSubgroup (Fin m → K), T ≤ S →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = S)
    (hcardS : Nat.card ↥S = 16)
    (hfaithS : ∀ g, (∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1)
    (hK4 : Nat.card K = 4)
    (hne : S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom ≠ ⊥) :
    (∀ x : K, ∀ v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom,
        x • v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) ∧
      (∀ g, ∀ v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom,
        (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈
          S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) ∧
      Nat.card ↥(S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom) = 16 ∧
      (∀ g, (∀ v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom,
        (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x v hv
    exact pImage_smul_mem D hD hc S hDS hK4 hv
  · intro g v hv
    exact pImage_psi_mem ψ D hDψ S hSinv g hv
  · exact (pImage_card ψ D hDψ S hSinv hirrS hne).trans hcardS
  · intro g hfix
    have hinj := pImage_injOn ψ D hDψ S hSinv hirrS hne
    apply hfaithS g
    intro v hv
    refine hinj ?_ hv ?_
    · exact hSinv g v hv
    · change (D + c • 1) *ᵥ ((ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v) =
        (D + c • 1) *ᵥ v
      rw [pMat_psi ψ D hDψ g v]
      have hmem : (D + c • 1) *ᵥ v ∈ S.map (Matrix.mulVecLin (D + c • 1)).toAddMonoidHom :=
        AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩
      exact hfix ((D + c • 1) *ᵥ v) hmem

private lemma le_sup_pImage {ω : K} (hωsum : ω + ω ^ 2 = 1)
    (D : Matrix (Fin m) (Fin m) K) (S : AddSubgroup (Fin m → K)) :
    S ≤ S.map (Matrix.mulVecLin (D + ω • 1)).toAddMonoidHom ⊔
      S.map (Matrix.mulVecLin (D + ω ^ 2 • 1)).toAddMonoidHom := by
  intro s hs
  have h1 : (D + ω • 1) *ᵥ s ∈ S.map (Matrix.mulVecLin (D + ω • 1)).toAddMonoidHom :=
    AddSubgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have h2 : (D + ω ^ 2 • 1) *ᵥ s ∈ S.map (Matrix.mulVecLin (D + ω ^ 2 • 1)).toAddMonoidHom :=
    AddSubgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hsplit : ((D + ω • 1) + (D + ω ^ 2 • 1)) *ᵥ s = s := pMat_add_apply hωsum D s
  rw [← hsplit, Matrix.add_mulVec]
  exact AddSubgroup.add_mem_sup h1 h2

end

end

theorem exists_iSupIndep_finrank_two_of_iSup {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) {G : Type} [Group G] {m : ℕ} (ψ : G →* GL (Fin m) K)
    (D : Matrix (Fin m) (Fin m) K) (hD : D * D + D + 1 = 0)
    (hDψ : ∀ g, D * (ψ g : Matrix (Fin m) (Fin m) K) = (ψ g : Matrix (Fin m) (Fin m) K) * D)
    (𝒮 : Set (AddSubgroup (Fin m → K))) (hsup : ⨆ S ∈ 𝒮, S = ⊤)
    (hinv : ∀ S ∈ 𝒮, ∀ g, ∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ S)
    (hDS : ∀ S ∈ 𝒮, ∀ v ∈ S, D *ᵥ v ∈ S)
    (hirr : ∀ S ∈ 𝒮, ∀ T : AddSubgroup (Fin m → K), T ≤ S →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = S)
    (hcard : ∀ S ∈ 𝒮, Nat.card ↥S = 16)
    (hfaith : ∀ S ∈ 𝒮, ∀ g, (∀ v ∈ S, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) :
    ∃ (n : ℕ) (R : Fin n → Submodule K (Fin m → K)), iSupIndep R ∧ iSup R = ⊤ ∧
      (∀ i, Module.finrank K ↥(R i) = 2) ∧
      (∀ i g, ∀ v ∈ R i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R i) ∧
      (∀ i g, (∀ v ∈ R i, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hK4
  obtain ⟨-, hω3, hω4⟩ := scalar_facts hω
  have hωsum : ω + ω ^ 2 = 1 := by
    have h : (ω + ω ^ 2) + 1 = 0 := by rw [← hω]; ring
    exact (CharTwo.add_eq_zero (R := K)).mp h
  have hω2sq : (ω ^ 2) ^ 2 = ω := by
    rw [show (ω ^ 2) ^ 2 = ω ^ 4 by ring, hω4]
  have hω2poly : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
    rw [hω2sq, hωsum]
    exact CharTwo.add_self_eq_zero (1 : K)
  have hcBif : ∀ b : Bool, (bif b then ω else ω ^ 2) ^ 2 + (bif b then ω else ω ^ 2) + 1 = 0 := by
    intro b
    cases b
    · exact hω2poly
    · exact hω
  let φ : G →* Multiplicative (AddAut (Fin m → K)) :=
    (MulAutMultiplicative (Fin m → K)).toMonoidHom.comp (matHom.comp ψ)
  have hφ_apply : ∀ (g : G) (v : Fin m → K),
      (φ g).toAdd v = (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v := by
    intro g v
    show Multiplicative.toAdd ((MulAutMultiplicative (Fin m → K)) (matHom (ψ g))) v = _
    change toAddMap (matAut (ψ g)) v = (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v
    rw [toAddMap_matAut]
  let pImg : AddSubgroup (Fin m → K) → Bool → AddSubgroup (Fin m → K) := fun S b =>
    S.map (Matrix.mulVecLin (D + (bif b then ω else ω ^ 2) • 1)).toAddMonoidHom
  let W : (𝒮 × Bool) → AddSubgroup (Fin m → K) := fun p => pImg p.1 p.2
  let ι := {p : 𝒮 × Bool // W p ≠ ⊥}
  let W' : ι → AddSubgroup (Fin m → K) := fun p => W p.1
  have hsimple : ∀ p : ι, W' p ≠ ⊥ ∧ ∀ T : AddSubgroup (Fin m → K), T ≤ W' p →
      (∀ g, ∀ v ∈ T, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ T) → T = ⊥ ∨ T = W' p := by
    intro p
    obtain ⟨p0, hpne⟩ := p
    obtain ⟨S, b⟩ := p0
    refine ⟨by simpa only [W', W, pImg] using hpne, ?_⟩
    intro T hT hTinv
    exact pImage_irreducible ψ D hDψ (S : AddSubgroup (Fin m → K)) (hinv S S.2) (hirr S S.2)
      (by simpa only [W', W, pImg] using hT) hTinv
  have hinvW : ∀ p : ι, ∀ g, ∀ v ∈ W' p, (φ g).toAdd v ∈ W' p := by
    intro p g v hv
    obtain ⟨p0, hpne⟩ := p
    obtain ⟨S, b⟩ := p0
    rw [hφ_apply]
    exact pImage_psi_mem ψ D hDψ (S : AddSubgroup (Fin m → K)) (hinv S S.2) g
      (by simpa only [W', W, pImg] using hv)
  obtain ⟨J, hJfin, hJind, hJsup⟩ := exists_iSupIndep_of_simple φ W' hinvW hsimple
  have htopS : (⨆ S : 𝒮, (S : AddSubgroup (Fin m → K))) = ⊤ := by
    rw [← iSup_subtype' (p := fun S : AddSubgroup (Fin m → K) => S ∈ 𝒮)
      (f := fun S _ => S)]
    exact hsup
  have hW_le : ∀ p : 𝒮 × Bool, W p ≤ ⨆ q : ι, W' q := by
    intro p
    by_cases hp : W p = ⊥
    · rw [hp]; exact bot_le
    · exact le_iSup (fun q : ι => W' q) ⟨p, hp⟩
  have hS_le : ∀ S : 𝒮, (S : AddSubgroup (Fin m → K)) ≤ W (S, true) ⊔ W (S, false) :=
    fun S => le_sup_pImage hωsum D (S : AddSubgroup (Fin m → K))
  have htopW : (⨆ p : ι, W' p) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = ⨆ S : 𝒮, (S : AddSubgroup (Fin m → K)) := htopS.symm
      _ ≤ ⨆ S : 𝒮, (W (S, true) ⊔ W (S, false)) := by
          refine iSup_le fun S => ?_
          exact (hS_le S).trans (le_iSup (fun S : 𝒮 => W (S, true) ⊔ W (S, false)) S)
      _ ≤ ⨆ p : ι, W' p := by
          refine iSup_le fun S => ?_
          exact sup_le (hW_le (S, true)) (hW_le (S, false))
  have hJtop : (⨆ j : J, W' j) = ⊤ := by rw [hJsup, htopW]
  let : Fintype J := hJfin.fintype
  have hfacts : ∀ p : ι,
      (∀ x : K, ∀ v ∈ W' p, x • v ∈ W' p) ∧
      (∀ g, ∀ v ∈ W' p, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ W' p) ∧
      Nat.card ↥(W' p) = 16 ∧
      (∀ g, (∀ v ∈ W' p, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1) := by
    intro p
    obtain ⟨⟨S, b⟩, hpne⟩ := p
    have hpne' : (S : AddSubgroup (Fin m → K)).map
        (Matrix.mulVecLin (D + (bif b then ω else ω ^ 2) • 1)).toAddMonoidHom ≠ ⊥ := by
      simpa only [W', W, pImg] using hpne
    have h := pImage_facts ψ D hD hDψ (S : AddSubgroup (Fin m → K)) (hcBif b)
      (hinv (S : AddSubgroup (Fin m → K)) S.2) (hDS (S : AddSubgroup (Fin m → K)) S.2)
      (hirr (S : AddSubgroup (Fin m → K)) S.2)
      (hcard (S : AddSubgroup (Fin m → K)) S.2)
      (hfaith (S : AddSubgroup (Fin m → K)) S.2) hK4 hpne'
    simpa only [W', W, pImg] using h
  have hJsub : ∀ j : J, ∀ c : K, ∀ v : Fin m → K, v ∈ W' j → c • v ∈ W' j :=
    fun j => (hfacts j.1).1
  have hJcard : ∀ j : J, Nat.card ↥(W' j) = 16 :=
    fun j => (hfacts j.1).2.2.1
  have hJinv : ∀ j : J, ∀ g : G, ∀ v : Fin m → K, v ∈ W' j →
      (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ W' j :=
    fun j => (hfacts j.1).2.1
  have hJfaith : ∀ j : J, ∀ g : G,
      (∀ v ∈ W' j, (ψ g : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → g = 1 :=
    fun j => (hfacts j.1).2.2.2
  exact exists_planes_of_iSupIndep hK4 ψ (fun j : J => W' j)
    hJsub hJind hJtop hJcard hJinv hJfaith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
