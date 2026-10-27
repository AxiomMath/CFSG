module

public import CFSG.LocalAnalysis.StandardType.PhanEGateFlip
public import CFSG.LocalAnalysis.StandardType.PhanEGateMutual

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {w₀ : W} {t : C → C} {J : Set ι} {a x x' : C}

@[expose] noncomputable def flipPsi (cs : CoxeterSystem M W) (δ : C → C → W) (t : C → C)
    (J : Set ι) (a : C) (x : C) : C :=
  resProj cs δ J a (t x)

@[expose] noncomputable def flipPi (cs : CoxeterSystem M W) (δ : C → C → W) (w₀ : W) (t : C → C)
    (J : Set ι) (a : C) (x : C) : W :=
  δ (flipPsi cs δ t J a x) (t x) * w₀

@[expose] def flipPsiMax (cs : CoxeterSystem M W) (δ : C → C → W) (t : C → C) (J : Set ι)
    (a : C) : Set C :=
  {x | x ∈ flipCore cs δ t J a ∧ ∀ y ∈ flipCore cs δ t J a,
    cs.length (δ y (flipPsi cs δ t J a y)) ≤ cs.length (δ x (flipPsi cs δ t J a x))}

private theorem p9uGS_mem_residue_of_mem_flipCore (hB : IsWeylDistanceBuilding cs δ)
    (hx : x ∈ flipCore cs δ t J a) : x ∈ residue cs δ J a := by
  rw [flipCore, projSet] at hx
  obtain ⟨z, -, rfl⟩ := hx
  exact resProj_mem hB J a z

theorem flipPsi_mem (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a) :
    flipPsi cs δ t J a x ∈ flipCore cs δ t J a := by
  rw [flipCore, projSet] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  have hxR : resProj cs δ J a z ∈ residue cs δ J a := resProj_mem hB J a z
  exact ⟨t (resProj cs δ J a z), ⟨resProj cs δ J a z, hxR, rfl⟩, rfl⟩

theorem flipPsi_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a) :
    flipPsi cs δ t J a (flipPsi cs δ t J a x) = x := by
  have hxQ : x ∈ projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := by
    rw [← image_residue_flip hw ht J a, ← flipCore]
    exact hx
  obtain ⟨-, hg⟩ :=
    resProj_projSet hB (J := J) (K := flipType cs w₀ J) (a := a) (b := t a) hxQ
  have ht_res : t (flipPsi cs δ t J a x) = resProj cs δ (flipType cs w₀ J) (t a) x := by
    show t (resProj cs δ J a (t x)) = resProj cs δ (flipType cs w₀ J) (t a) x
    rw [t_resProj hB hw ht J a (t x), ht.invol x]
  show resProj cs δ J a (t (flipPsi cs δ t J a x)) = x
  rw [ht_res, hg]

theorem resProj_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a) :
    resProj cs δ (flipType cs w₀ J) (t a) (flipPsi cs δ t J a x) = t x := by
  have htx : t x ∈ projSet cs δ (flipType cs w₀ J) (t a) (residue cs δ J a) := by
    rw [← t_flipCore hB hw ht J a]
    exact ⟨x, hx, rfl⟩
  have h2 :=
    (resProj_projSet hB (J := flipType cs w₀ J) (K := J) (a := t a) (b := a) htx).2
  show resProj cs δ (flipType cs w₀ J) (t a) (resProj cs δ J a (t x)) = t x
  exact h2

theorem isClosestPair_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a) :
    IsClosestPair cs δ J (flipType cs w₀ J) a (t a) (flipPsi cs δ t J a x) (t x) := by
  have hxR : x ∈ residue cs δ J a := p9uGS_mem_residue_of_mem_flipCore hB hx
  have hmem : flipPsi cs δ t J a x ∈
      projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := by
    refine ⟨t x, ?_, rfl⟩
    rw [← image_residue_flip hw ht J a]
    exact ⟨x, hxR, rfl⟩
  obtain ⟨y, hy⟩ :=
    (mem_projSet_iff (J := J) (K := flipType cs w₀ J) (a := a) (b := t a)
      (x := flipPsi cs δ t J a x) hB).mp hmem
  have hyx : y = t x := by
    rw [← hy.eq_resProj_right hB, resProj_flipPsi hB hw ht hx]
  rw [← hyx]
  exact hy

theorem dist_flipPsi_const (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a)
    (hx' : x' ∈ flipCore cs δ t J a) :
    δ (flipPsi cs δ t J a x) (t x) = δ (flipPsi cs δ t J a x') (t x') :=
  IsClosestPair.dist_eq hB (isClosestPair_flipPsi hB hw ht hx)
    (isClosestPair_flipPsi hB hw ht hx')

theorem flipPi_eq (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a)
    (hx' : x' ∈ flipCore cs δ t J a) :
    flipPi cs δ w₀ t J a x = flipPi cs δ w₀ t J a x' := by
  unfold flipPi
  rw [dist_flipPsi_const hB hw ht hx hx']

theorem dist_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx : x ∈ flipCore cs δ t J a)
    (hx' : x' ∈ flipCore cs δ t J a) :
    δ (flipPsi cs δ t J a x) (flipPsi cs δ t J a x') =
        flipPi cs δ w₀ t J a x * δ x x' * (flipPi cs δ w₀ t J a x)⁻¹ ∧
      cs.length (δ (flipPsi cs δ t J a x) (flipPsi cs δ t J a x')) = cs.length (δ x x') := by
  have hc := isClosestPair_flipPsi hB hw ht hx
  have hc' := isClosestPair_flipPsi hB hw ht hx'
  have hw0 : w₀⁻¹ = w₀ :=
    inv_eq_of_mul_eq_one_left (CoxeterSystem.w0_mul_self cs w₀ hw)
  constructor
  · rw [IsClosestPair.dist_left_eq hB hc hc', ht.dist x x']
    unfold flipPi
    rw [mul_inv_rev, hw0]
    group
  · rw [IsClosestPair.length_left_eq hB hc hc', ht.dist x x',
      CoxeterSystem.length_w0_conj cs w₀ hw (δ x x')]

theorem exists_simple_flipPsi (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) {I : Set ι} {x₁ : C}
    (hI : flipCore cs δ t J a = residue cs δ I x₁) {i : ι} (hi : i ∈ I) :
    ∃ i' ∈ I, flipPi cs δ w₀ t J a x₁ * cs.simple i * (flipPi cs δ w₀ t J a x₁)⁻¹ =
      cs.simple i' := by
  have hx₁ : x₁ ∈ flipCore cs δ t J a := by
    rw [hI]
    exact self_mem_residue I x₁
  obtain ⟨z, hz, -⟩ := hB.exists_simple x₁ x₁ i
  have hzI : z ∈ residue cs δ I x₁ := Relation.ReflTransGen.single ⟨i, hi, hz⟩
  have hzcore : z ∈ flipCore cs δ t J a := by
    rw [hI]
    exact hzI
  obtain ⟨heq, hlen⟩ := dist_flipPsi hB hw ht hx₁ hzcore
  have hψx₁ : flipPsi cs δ t J a x₁ ∈ flipCore cs δ t J a := flipPsi_mem hB hw ht hx₁
  have hψz : flipPsi cs δ t J a z ∈ flipCore cs δ t J a := flipPsi_mem hB hw ht hzcore
  have hpar : δ (flipPsi cs δ t J a x₁) (flipPsi cs δ t J a z) ∈ cs.parabolic I := by
    rw [hI] at hψx₁ hψz
    exact mem_parabolic_of_mem_residue hB hψx₁ hψz
  have hlen1 : cs.length (δ (flipPsi cs δ t J a x₁) (flipPsi cs δ t J a z)) = 1 := by
    rw [hlen, hz, cs.length_simple]
  obtain ⟨ω, hred, hωI, hω⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hpar
  have hlenω : ω.length = 1 := by
    have h := hred.eq
    rw [hω, hlen1] at h
    omega
  obtain ⟨i', rfl⟩ := List.length_eq_one_iff.mp hlenω
  refine ⟨i', hωI i' (by simp), ?_⟩
  rw [← hz, ← heq, ← hω, cs.wordProd_singleton]

theorem flipPsiMax_nonempty (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) [Finite (cs.parabolic J)] :
    (flipPsiMax cs δ t J a).Nonempty := by
  classical
  let S : Set ℕ := {n | ∃ y ∈ flipCore cs δ t J a,
    cs.length (δ y (flipPsi cs δ t J a y)) = n}
  have hne : S.Nonempty := by
    refine ⟨cs.length (δ (resProj cs δ J a (t a))
        (flipPsi cs δ t J a (resProj cs δ J a (t a)))), ?_⟩
    refine ⟨resProj cs δ J a (t a), ?_, rfl⟩
    rw [flipCore, projSet]
    exact ⟨t a, ⟨a, self_mem_residue J a, rfl⟩, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨cs.length (longest cs J), fun n hn => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    have hyR : y ∈ residue cs δ J a := p9uGS_mem_residue_of_mem_flipCore hB hy
    have hψyR : flipPsi cs δ t J a y ∈ residue cs δ J a :=
      p9uGS_mem_residue_of_mem_flipCore hB (flipPsi_mem hB hw ht hy)
    exact (isLongest_longest J).2 _
      (mem_parabolic_of_mem_residue hB hyR hψyR)
  obtain ⟨y₀, hy₀core, hy₀len⟩ := Nat.sSup_mem hne hbdd
  refine ⟨y₀, hy₀core, fun y hy => ?_⟩
  have hle := le_csSup hbdd
    (show cs.length (δ y (flipPsi cs δ t J a y)) ∈ S from ⟨y, hy, rfl⟩)
  rwa [← hy₀len] at hle

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
