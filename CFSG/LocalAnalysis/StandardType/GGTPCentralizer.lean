module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_fixS_all : ∀ v : E6Dep.Vec6, (∀ i : Fin 5, (E6Dep.gS i).mulVec v = v) →
    v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by decide +kernel

private theorem ggTP_xx_eq_single : (E6Dep.xx : E6Dep.Vec6) = Pi.single 5 1 := by decide +kernel

private theorem ggTP_gS_fix_xs : ∀ i : Fin 5,
    (E6Dep.gS i).mulVec (E6Dep.xs : E6Dep.Vec6) = E6Dep.xs := by decide +kernel

private theorem ggTP_vec_eq_smul_xs_add_smul_xx : ∀ u : E6Dep.Vec6,
    u 0 = 0 → u 1 = 0 → u 2 = 0 → u 3 = 0 →
      u = u 4 • (E6Dep.xs : E6Dep.Vec6) + u 5 • (E6Dep.xx : E6Dep.Vec6) := by
  decide +kernel

private theorem ggTP_ofMul_mul {G : Type} [Group G] {Bs : Subgroup G} (a b : ↥Bs) :
    Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := rfl

private theorem ggTP_ofMul_pow {G : Type} [Group G] {Bs : Subgroup G} (z : ↥Bs) (n : ℕ) :
    Additive.ofMul (z ^ n) = n • Additive.ofMul z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ggTP_ofMul_mul, ih, succ_nsmul]

private theorem ggTP_smul_eq_nsmul (a : ZMod 3) (v : E6Dep.Vec6) :
    a • v = a.val • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3) a.val v, ZMod.natCast_zmod_val a]

theorem ggTPCentralizerJ_le_D {G : Type} [Group G] {Bs L D J : Subgroup G} {x y : G}
    (hxBs : x ∈ Bs) (hyBs : y ∈ Bs) {ι : Additive ↥Bs ≃+ E6Dep.Vec6}
    (hι : E6Dep.GGE6DepCoord Bs L x hxBs ι) (hyι : ι (Additive.ofMul ⟨y, hyBs⟩) = E6Dep.xs)
    (hD : D = Subgroup.closure {x, y})
    (hSJ : ∀ φ ∈ ggAutomizer L Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ → φ ∈ ggAutomizer J Bs) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  intro b hb
  obtain ⟨hbBs, hbJ⟩ := Subgroup.mem_inf.mp hb
  let β : ↥Bs := ⟨b, hbBs⟩
  let γ : ↥Bs := ⟨y, hyBs⟩
  let γx : ↥Bs := ⟨x, hxBs⟩
  have hγy : ι (Additive.ofMul γ) = E6Dep.xs := hyι
  have hγx : ι (Additive.ofMul γx) = E6Dep.xx := by
    rw [ggTP_xx_eq_single]
    exact hι.1
  have hfix : ∀ φ ∈ ggAutomizer J Bs, φ β = β := by
    intro φ hφ
    have hsub : ggInduced J Bs ⊆
        (MulAction.stabilizer (MulAut ↥Bs) β : Set (MulAut ↥Bs)) := by
      rintro ψ ⟨n, hnJ, _hnN, hnψ⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Subtype.ext
      rw [hnψ]
      have hcomm : n * (β : G) = (β : G) * n :=
        Subgroup.mem_centralizer_iff.mp hbJ n hnJ
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : φ ∈ MulAction.stabilizer (MulAut ↥Bs) β :=
      (Subgroup.closure_le (MulAction.stabilizer (MulAut ↥Bs) β)).mpr hsub
        (show φ ∈ Subgroup.closure (ggInduced J Bs) from hφ)
    simpa [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hmem
  have hfixu : ∀ i : Fin 5,
      (E6Dep.gS i).mulVec (ι (Additive.ofMul β)) = ι (Additive.ofMul β) := by
    intro i
    have hgS : E6Dep.gS i ∈ E6Dep.closureL :=
      Submonoid.subset_closure ⟨i.castSucc, rfl⟩
    obtain ⟨φ, hφA, hφActs⟩ := hι.2.2.2 (E6Dep.gS i) hgS
    have hφfixy : φ γ = γ := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [hφActs γ, hγy, ggTP_gS_fix_xs i]
    have hφJ : φ ∈ ggAutomizer J Bs :=
      hSJ φ hφA (show φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ from hφfixy)
    have hφfixβ : φ β = β := hfix φ hφJ
    have h := hφActs β
    rw [hφfixβ] at h
    exact h.symm
  obtain ⟨hu0, hu1, hu2, hu3⟩ := ggTP_fixS_all (ι (Additive.ofMul β)) hfixu
  let a : ZMod 3 := (ι (Additive.ofMul β)) 4
  let c : ZMod 3 := (ι (Additive.ofMul β)) 5
  have hu : ι (Additive.ofMul β) =
      a • (E6Dep.xs : E6Dep.Vec6) + c • (E6Dep.xx : E6Dep.Vec6) := by
    dsimp [a, c]
    exact ggTP_vec_eq_smul_xs_add_smul_xx _ hu0 hu1 hu2 hu3
  have hβ_eq : β = γ ^ a.val * γx ^ c.val := by
    apply Additive.ofMul.injective
    apply ι.injective
    symm
    calc
      ι (Additive.ofMul (γ ^ a.val * γx ^ c.val))
          = ι (Additive.ofMul (γ ^ a.val)) + ι (Additive.ofMul (γx ^ c.val)) := by
              rw [ggTP_ofMul_mul, map_add]
      _ = ι (a.val • Additive.ofMul γ) + ι (c.val • Additive.ofMul γx) := by
              rw [ggTP_ofMul_pow, ggTP_ofMul_pow]
      _ = a.val • ι (Additive.ofMul γ) + c.val • ι (Additive.ofMul γx) := by
              rw [map_nsmul, map_nsmul]
      _ = a.val • (E6Dep.xs : E6Dep.Vec6) + c.val • (E6Dep.xx : E6Dep.Vec6) := by
              rw [hγy, hγx]
      _ = a • (E6Dep.xs : E6Dep.Vec6) + c • (E6Dep.xx : E6Dep.Vec6) := by
              rw [← ggTP_smul_eq_nsmul a (E6Dep.xs : E6Dep.Vec6),
                ← ggTP_smul_eq_nsmul c (E6Dep.xx : E6Dep.Vec6)]
      _ = ι (Additive.ofMul β) := hu.symm
  have hb_eq : b = y ^ a.val * x ^ c.val := by
    have hcoe := congrArg (fun z : ↥Bs => (z : G)) hβ_eq
    have hR : ((γ ^ a.val * γx ^ c.val : ↥Bs) : G) = y ^ a.val * x ^ c.val := by
      simp [Subgroup.coe_mul, Subgroup.coe_pow, γ, γx]
    have hL : ((β : ↥Bs) : G) = b := rfl
    rw [hL, hR] at hcoe
    exact hcoe
  rw [hD]
  have hy : y ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hx : x ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [hb_eq]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hy _) (Subgroup.pow_mem _ hx _)

end CFSG.StandardType

end
