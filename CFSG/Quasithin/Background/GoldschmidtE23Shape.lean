module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.GoldschmidtE23Blocks
public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace GE23

section Shape

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem component_le_twoResidual {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    L ≤ twoResidual X :=
  le_twoResidual_of_perfect hL.1 (Group.isPerfect_def.mpr hL.2.2.1)

theorem NatBlk.isL2Natural {T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    (hKY : twoResidual X ≤ ffJ X) {H : Subgroup (MulAut V)} (h : NatBlk X H) :
    ∃ n : ℕ, E2.IsL2Natural H (fixV (twoResidual X)) n := by
  obtain ⟨L, e, hL, hblk, hHL, he, ⟨K, instK, instF, hK, π, β, hπs, hβs, hβz, hUinv, hβeq⟩, -⟩ := h
  subst hHL
  have hLK : H ≤ twoResidual X := component_le_twoResidual hL
  have hπi : Function.Injective π := NatData.injective_of hβs hUinv hβeq
  let e' : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MulEquiv.ofBijective π ⟨hπi, hπs⟩).symm
  have hZ : ∀ u : V, u ∈ commV H ⊓ fixV (ffJ X) ↔ u ∈ commV H ⊓ fixV (twoResidual X) := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, B1.fixV_le_fixV hKY h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, B69.mem_fixV_ffJ hB hL h1 fun y hy => ?_⟩
      rw [hblk] at hy
      exact h2 y (hLK hy)
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  refine ⟨e, ?_, K, instK, inferInstance, hcard, e', β, hβs, ?_, ?_⟩
  · omega
  · ext u
    rw [MonoidHom.mem_ker, hβz u, hZ, Subgroup.mem_subgroupOf]
  · intro g u hu
    have hg : g = π (e' g) := (MulEquiv.apply_symm_apply (MulEquiv.ofBijective π ⟨hπi, hπs⟩) g).symm
    have key := hβeq (e' g) u (by rw [← hg]; exact hu)
    have e1 : (⟨((π (e' g) : ↥H) : MulAut V) (u : V), by rw [← hg]; exact hu⟩ : ↥(commV H)) =
        ⟨(g : MulAut V) (u : V), hu⟩ := by
      apply Subtype.ext
      show ((π (e' g) : ↥H) : MulAut V) (u : V) = (g : MulAut V) (u : V)
      rw [← hg]
    rw [e1] at key
    simpa using congrArg Multiplicative.toAdd key

theorem mem_evenWeight_iff {n : ℕ} {x : Fin n → ZMod 2} :
    x ∈ evenWeight n ↔ ∑ i, x i = 0 := by
  simp [evenWeight]

@[expose] def coreEquivEven (n : ℕ) : ↥(coreMod n) ≃* Multiplicative ↥(evenWeight n) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd (x : PermMod n),
    mem_evenWeight_iff.2 (mem_coreMod.1 x.2)⟩
  invFun y := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd y : ↥(evenWeight n)) : Fin n → ZMod 2),
    mem_coreMod.2 (mem_evenWeight_iff.1 (Multiplicative.toAdd y).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem SymBlk.isA5Module {T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {H : Subgroup (MulAut V)} (h : SymBlk X H 2) : E2.IsA5Module H := by
  obtain ⟨L, A, hL, hA, hLA, hblk, rfl, hk, π, hπs, hreal, hLeq, -⟩ := h
  have hcomm : commV (L ⊔ A) = commV L := by
    rw [← hblk]
    exact commV_blk hB hL
  obtain ⟨θ, β₀, hθ, hβ, hrange, hker⟩ := Ch3z.isSymCore_of_realizes' hreal
  have hinj : Function.Injective β₀ := (injective_iff_map_eq_one β₀).2 fun u hu => by
    have : u ∈ β₀.ker := hu
    rw [hker] at this
    exact Subgroup.mem_bot.1 this
  let e1 : ↥(commV (L ⊔ A)) ≃* ↥(coreMod (2 * 2 + 1)) :=
    (MulEquiv.subgroupCongr (hcomm.trans hrange.symm)).trans (MonoidHom.ofInjective hinj).symm
  have he1 : ∀ u : ↥(commV (L ⊔ A)), β₀ (e1 u) = (u : V) := fun u => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hcomm.trans hrange.symm) u)
    exact congrArg Subtype.val this
  refine ⟨θ, e1.trans (coreEquivEven (2 * 2 + 1)), fun g u hu i => ?_⟩
  have hgu : e1 ⟨(g : MulAut V) (u : V), hu⟩ = coreAct (2 * 2 + 1) (θ g) (e1 u) := by
    apply hinj
    rw [he1, hβ g (e1 u), he1]
  show Multiplicative.toAdd (e1 ⟨(g : MulAut V) (u : V), hu⟩ : PermMod (2 * 2 + 1)) i = _
  rw [hgu]
  rfl

end Shape

end GE23

end CFSG.Quasithin
