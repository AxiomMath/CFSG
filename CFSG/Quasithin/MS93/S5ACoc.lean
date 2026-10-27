module

public import CFSG.Quasithin.Background.JonesParshallSp4Derived
public import CFSG.Quasithin.MS93.MSPBasic

public noncomputable section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit MSP

variable {F : Type} [Field F]

theorem statedSp_eq_jpSp4 [CharP F 2] : StatedSp 2 F = Explicit.sp4 F := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
    ext i j
    rw [Matrix.neg_apply]
    exact CharTwo.neg_eq _
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Explicit.spJ F := by
    rw [hneg]
    rfl
  unfold StatedSp
  rw [hJ]
  exact Subgroup.closure_eq (Explicit.sp4 F)

section Sqf

variable [Fintype F] [CharP F 2]

@[expose] def sqf (M : Matrix Ix Ix F) : V4 F := fun i => sqrtF (quadQ (M i))

theorem sqrtF_ringEquiv {F' : Type} [Field F'] [Fintype F'] [CharP F' 2] (e : F ≃+* F') (x : F) :
    e (sqrtF x) = sqrtF (e x) := by
  apply sq_inj
  rw [sqrtF_sq, ← map_pow, sqrtF_sq]

end Sqf

section Q2

theorem exists_eq_cocAB {f : ↥subAB → (Ix → ZMod 2)} (hf : f ∈ Z1A muAB) :
    ∃ (c : ZMod 2) (m : Ix → ZMod 2), f = c • cocAB + coboundaryA muAB m := by
  have hrel : ∀ r ∈ relsAB, foxIx ![matA, matB] ![f (gensAB 0), f (gensAB 1)] r = 0 := by
    intro r hr
    have h := (foxEval_AB (fun i => f (gensAB i)) r).symm.trans
      (Z1A_wordEval hf gensAB r).symm
    have h1 : wordEval gensAB r = 1 :=
      Subtype.ext ((wordEval_gensAB r).trans (relsAB_spec r hr))
    rw [h1, Z1A_one hf] at h
    have hv : (![f (gensAB 0), f (gensAB 1)] : Fin 2 → Ix → ZMod 2) =
        fun i => f (gensAB i) := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact h
  rw [vec4_eta (f (gensAB 0)), vec4_eta (f (gensAB 1))] at hrel
  rcases sol_AB _ _ _ _ _ _ _ _ hrel with ⟨x, y, z, w, hv₀, hv₁⟩ | ⟨x, y, z, w, hv₀, hv₁⟩
  · refine ⟨0, vec4 x y z w, ?_⟩
    rw [zero_smul, zero_add]
    refine eq_of_agree_AB hf (B1A_le_Z1A _ ⟨_, rfl⟩) ?_ ?_
    · rw [vec4_eta (f (gensAB 0)), hv₀]
      rfl
    · rw [vec4_eta (f (gensAB 1)), hv₁]
      rfl
  · refine ⟨1, vec4 x y z w, ?_⟩
    rw [one_smul]
    refine eq_of_agree_AB hf (add_mem cocAB_mem (B1A_le_Z1A _ ⟨_, rfl⟩)) ?_ ?_
    · rw [vec4_eta (f (gensAB 0)), hv₀, Pi.add_apply, cocAB_gen0]
      exact (zero_add _).symm
    · rw [vec4_eta (f (gensAB 1)), hv₁, Pi.add_apply, cocAB_gen1]
      rfl

theorem eq_zero_of_fixed_AB (v : Ix → ZMod 2) (hA : matA *ᵥ v = v) (hB : matB *ᵥ v = v) :
    v = 0 := by
  revert v
  decide +kernel

theorem conj_mem_subAB {g : GL Ix (ZMod 2)} (hg : g ∈ Explicit.sp4 (ZMod 2)) {n : GL Ix (ZMod 2)}
    (hn : n ∈ subAB) : g * n * g⁻¹ ∈ subAB := by
  rw [← sp4Two_commutator_eq] at hn ⊢
  have h : (⁅Explicit.sp4 (ZMod 2), Explicit.sp4 (ZMod 2)⁆).map (MulAut.conj g).toMonoidHom =
      ⁅Explicit.sp4 (ZMod 2), Explicit.sp4 (ZMod 2)⁆ := by
    rw [Subgroup.map_commutator]
    have hs : (Explicit.sp4 (ZMod 2)).map (MulAut.conj g).toMonoidHom = Explicit.sp4 (ZMod 2) := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (Explicit.sp4 (ZMod 2)).mul_mem ((Explicit.sp4 (ZMod 2)).mul_mem hg hx)
          ((Explicit.sp4 (ZMod 2)).inv_mem hg)
      · intro x hx
        refine ⟨g⁻¹ * x * g, (Explicit.sp4 (ZMod 2)).mul_mem ((Explicit.sp4 (ZMod 2)).mul_mem
          ((Explicit.sp4 (ZMod 2)).inv_mem hg) hx) hg, ?_⟩
        simp [mul_assoc]
    rw [hs]
  rw [← h]
  exact ⟨n, hn, rfl⟩

theorem exists_eq_spF0_two {f : ↥(Explicit.sp4 (ZMod 2)) → (Ix → ZMod 2)}
    (hf : f ∈ Z1A (muSp (F := ZMod 2))) :
    ∃ (c : ZMod 2) (m : Ix → ZMod 2), ∀ g, f g = c • spF0 g + ((g : GL Ix (ZMod 2)) • m - m) := by
  let f₃ : ↥subAB → (Ix → ZMod 2) := fun n => f (Subgroup.inclusion subAB_le n)
  have hf₃ : f₃ ∈ Z1A muAB := Z1A_comp (Subgroup.inclusion subAB_le) hf
  obtain ⟨c, m, hcm⟩ := exists_eq_cocAB hf₃
  set ψ : ↥(Explicit.sp4 (ZMod 2)) → (Ix → ZMod 2) :=
    f - c • spF0 - coboundaryA muSp m with hψ
  have hψZ : ψ ∈ Z1A (muSp (F := ZMod 2)) :=
    sub_mem (sub_mem hf (smul_spF0_mem c)) (B1A_le_Z1A _ ⟨m, rfl⟩)
  have hψ0 : ∀ n : ↥subAB, ψ (Subgroup.inclusion subAB_le n) = 0 := fun n => by
    have h : f₃ n = c • cocAB n + coboundaryA muAB m n := by rw [hcm]; rfl
    have hcob : coboundaryA muAB m n = coboundaryA muSp m (Subgroup.inclusion subAB_le n) := rfl
    have hcoc : cocAB n = spF0 (Subgroup.inclusion subAB_le n) := rfl
    have hf3 : f₃ n = f (Subgroup.inclusion subAB_le n) := rfl
    rw [hcob, hcoc, hf3] at h
    rw [hψ, Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, h]
    abel
  have hfix : ∀ g, ψ g = 0 := by
    intro g
    have hn : ∀ n : ↥subAB, ((n : GL Ix (ZMod 2)) • ψ g) = ψ g := by
      intro n
      have hgn : (g : GL Ix (ZMod 2))⁻¹ * (n : GL Ix (ZMod 2)) * g ∈ subAB := by
        have := conj_mem_subAB ((Explicit.sp4 (ZMod 2)).inv_mem g.2) n.2
        simpa using this
      have e1 : Subgroup.inclusion subAB_le n * g =
          g * Subgroup.inclusion subAB_le (⟨_, hgn⟩ : ↥subAB) := by
        apply Subtype.ext
        change (n : GL Ix (ZMod 2)) * g = g * ((g : GL Ix (ZMod 2))⁻¹ * n * g)
        group
      have h1 := hψZ (Subgroup.inclusion subAB_le n) g
      have h2 := hψZ g (Subgroup.inclusion subAB_le (⟨_, hgn⟩ : ↥subAB))
      rw [e1, h2, hψ0, hψ0, map_zero] at h1
      exact (zero_add _).symm.trans (h1.symm.trans (add_zero _))
    have hA := hn (gensAB 0)
    have hB := hn (gensAB 1)
    exact eq_zero_of_fixed_AB _ hA hB
  refine ⟨c, m, fun g => ?_⟩
  have h : f g - c • spF0 g - coboundaryA muSp m g = 0 := hfix g
  have h' : f g - c • spF0 g = coboundaryA muSp m g := sub_eq_zero.mp h
  exact sub_eq_iff_eq_add'.mp h'

end Q2

section General

variable [Fintype F] [CharP F 2]

theorem exists_eq_sqf {k : ℕ} (hF : Fintype.card F = 2 ^ k) (hk : 1 ≤ k) {φ : Sp4 F → V4 F}
    (hφ : ∀ g h, φ (g * h) = φ g + mat g *ᵥ φ h) :
    ∃ (B : F) (m : V4 F), ∀ g, φ g = B • sqf (mat g) + (mat g *ᵥ m - m) := by
  have hsp := statedSp_eq_jpSp4 (F := F)
  rcases Nat.lt_or_ge 1 k with hk2 | hk1
  · let ι : ↥(Explicit.sp4 F) → Sp4 F := fun g => ⟨g, by rw [hsp]; exact g.2⟩
    let f : ↥(Explicit.sp4 F) → (Ix → F) := fun g => φ (ι g)
    have hf : f ∈ Z1A (muSp (F := F)) := fun g h => by
      have e : ι (g * h) = ι g * ι h := rfl
      change φ (ι (g * h)) = φ (ι g) + (g : GL Ix F) • φ (ι h)
      rw [e, hφ]
      rfl
    obtain ⟨B, hB⟩ := exists_sub_spF0_mem_B1A hF hk2 hf
    obtain ⟨m, hm⟩ := hB
    refine ⟨B, m, fun g => ?_⟩
    have hg' : (g : GL Ix F) ∈ Explicit.sp4 F := by rw [← hsp]; exact g.2
    have h' : mat g *ᵥ m - m = φ g - B • sqf (mat g) := congrFun hm ⟨(g : GL Ix F), hg'⟩
    rw [h']
    abel
  · have hk1' : k = 1 := le_antisymm hk1 hk
    subst hk1'
    have hF2 : Fintype.card F = 2 := by rw [hF, pow_one]
    let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF2).symm
    have hsp2 := statedSp_eq_jpSp4 (F := ZMod 2)
    let ι₂ : ↥(Explicit.sp4 (ZMod 2)) → Sp4 F := fun h =>
      ⟨glIxRingEquiv e.symm h, by rw [hsp]; exact glIxRingEquiv_mem e.symm h.2⟩
    let θ : Sp4 F → ↥(Explicit.sp4 (ZMod 2)) := fun g =>
      ⟨glIxRingEquiv e g, glIxRingEquiv_mem e (by rw [← hsp]; exact g.2)⟩
    have hιθ : ∀ g, ι₂ (θ g) = g := fun g => Subtype.ext (by
      change glIxRingEquiv e.symm (glIxRingEquiv e (g : GL Ix F)) = g
      ext i j
      change e.symm (e (((g : GL Ix F) : Matrix Ix Ix F) i j)) = _
      rw [RingEquiv.symm_apply_apply])
    have hglι : ∀ h, glIxRingEquiv e (ι₂ h : GL Ix F) = h := fun h => by
      ext i j
      change e (e.symm (((h : GL Ix (ZMod 2)) : Matrix Ix Ix (ZMod 2)) i j)) = _
      rw [RingEquiv.apply_symm_apply]
    let f₂ : ↥(Explicit.sp4 (ZMod 2)) → (Ix → ZMod 2) := fun h => vecIxRingEquiv e (φ (ι₂ h))
    have hf₂ : f₂ ∈ Z1A (muSp (F := ZMod 2)) := fun h h' => by
      have e1 : ι₂ (h * h') = ι₂ h * ι₂ h' := Subtype.ext (map_mul _ _ _)
      change vecIxRingEquiv e (φ (ι₂ (h * h'))) =
        vecIxRingEquiv e (φ (ι₂ h)) + (h : GL Ix (ZMod 2)) • vecIxRingEquiv e (φ (ι₂ h'))
      rw [e1, hφ, map_add]
      congr 1
      have := vecIxRingEquiv_smul e (ι₂ h : GL Ix F) (φ (ι₂ h'))
      rw [hglι] at this
      exact this
    obtain ⟨c, m₂, hcm⟩ := exists_eq_spF0_two hf₂
    refine ⟨e.symm c, vecIxRingEquiv e.symm m₂, fun g => ?_⟩
    have h := hcm (θ g)
    have h1 : φ g = vecIxRingEquiv e.symm (f₂ (θ g)) := by
      change φ g = vecIxRingEquiv e.symm (vecIxRingEquiv e (φ (ι₂ (θ g))))
      rw [hιθ]
      funext i
      change φ g i = e.symm (e (φ g i))
      rw [RingEquiv.symm_apply_apply]
    rw [h1, h, map_add, map_sub]
    have hsm : vecIxRingEquiv e.symm (c • spF0 (θ g)) = e.symm c • sqf (mat g) := by
      funext i
      change e.symm (c * sqrtF (quadQ (((θ g : GL Ix (ZMod 2)) : Matrix Ix Ix (ZMod 2)) i))) =
        e.symm c * sqrtF (quadQ (mat g i))
      rw [map_mul, sqrtF_ringEquiv]
      congr 2
      change e.symm (quadQ (fun j => e (mat g i j))) = quadQ (mat g i)
      simp [quadQ, map_add, map_mul]
    have hgm : vecIxRingEquiv e.symm ((θ g : GL Ix (ZMod 2)) • m₂) =
        mat g *ᵥ vecIxRingEquiv e.symm m₂ := by
      have := vecIxRingEquiv_smul e.symm (θ g : GL Ix (ZMod 2)) m₂
      rw [this]
      congr 1
      have e2 : glIxRingEquiv e.symm (θ g : GL Ix (ZMod 2)) = (g : GL Ix F) :=
        congrArg Subtype.val (hιθ g)
      rw [e2]
    rw [hsm, hgm]

end General

end CFSG.Quasithin.MS93.S5
