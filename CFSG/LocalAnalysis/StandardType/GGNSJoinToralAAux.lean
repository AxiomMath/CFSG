module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem nsTor_commute_of_scalar {n : ℕ} {K : Type} [Field K] {u : GL (Fin n) K} {c : K}
    (hu : (u : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c) (t : GL (Fin n) K) :
    Commute u t := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hu]
  exact Matrix.scalar_commute c (fun _ => Commute.all _ _) (t : Matrix (Fin n) (Fin n) K)

theorem nsTor_card_ne {n : ℕ} (a : Fin n) : Nat.card {i : Fin n // i ≠ a} = n - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]

noncomputable def nsTor_ratioPi {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a : Fin n) :
    ↥Bs →* ({i : Fin n // i ≠ a} → Kˣ) where
  toFun s := fun i => ggNSPosPA7_ratioHom h hd i.1 a s
  map_one' := by funext i; exact map_one (ggNSPosPA7_ratioHom h hd i.1 a)
  map_mul' := by intro s t; funext i; exact map_mul (ggNSPosPA7_ratioHom h hd i.1 a) s t

theorem nsTor_ratioPi_ker_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a : Fin n) :
    ∀ s : ↥Bs, s ∈ (nsTor_ratioPi h hd a).ker →
      (s : G) ∈ Bs ⊓ Subgroup.centralizer (ψ.range : Set G) := by
  intro s hs
  refine Subgroup.mem_inf.mpr ⟨s.2, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  have hR1 : nsTor_ratioPi h hd a s = 1 := MonoidHom.mem_ker.mp hs
  have hd_eq : ∀ i : Fin n, ggNSPosPA_liftUnits hd s i = ggNSPosPA_liftUnits hd s a := by
    intro i
    by_cases hia : i = a
    · subst hia; rfl
    · have hcoord : nsTor_ratioPi h hd a s ⟨i, hia⟩ = 1 := by rw [hR1]; rfl
      change ggNSPosPA7_ratioHom h hd i a s = 1 at hcoord
      rw [ggNSPosPA7_ratioHom_apply] at hcoord
      exact mul_inv_eq_one.mp hcoord
  have hconst : (fun i : Fin n => ((ggNSPosPA_liftUnits hd s i : Kˣ) : K)) =
      (fun _ : Fin n => ((ggNSPosPA_liftUnits hd s a : Kˣ) : K)) := by
    funext i; rw [hd_eq i]
  obtain ⟨c, hc⟩ : ∃ c : K, ((ggNSPosPA_lift hd s : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c := by
    refine ⟨((ggNSPosPA_liftUnits hd s a : Kˣ) : K), ?_⟩
    rw [← ggNSPosPA_diagGL_liftUnits hd s, ggNSPosPA_coe_diagGL, hconst, Matrix.scalar_apply]
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨z, hz, hbz⟩ := (ggNSPosPA_lift_induces hd s).2 x
  have hcomm := nsTor_commute_of_scalar hc (x : GL (Fin n) K)
  have hz_eq : z = x := by
    apply Subtype.ext
    rw [hz]
    calc (ggNSPosPA_lift hd s : GL (Fin n) K) * (x : GL (Fin n) K) *
          (ggNSPosPA_lift hd s : GL (Fin n) K)⁻¹
        = (x : GL (Fin n) K) * (ggNSPosPA_lift hd s : GL (Fin n) K) *
            (ggNSPosPA_lift hd s : GL (Fin n) K)⁻¹ := by rw [hcomm]
      _ = x := by group
  rw [hz_eq] at hbz
  have h2 : (s : G) * ψ x = ψ x * (s : G) := by
    calc (s : G) * ψ x = (s : G) * ψ x * (s : G)⁻¹ * (s : G) := by group
      _ = ψ x * (s : G) := by rw [hbz]
  exact h2.symm

theorem nsTor_ratioPi_range_card_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a : Fin n) :
    Nat.card (nsTor_ratioPi h hd a).range ≤ p ^ (n - 1) := by
  haveI : NeZero p := ⟨h.prime.ne_zero⟩
  let Φ : ↥(nsTor_ratioPi h hd a).range → ({i : Fin n // i ≠ a} → rootsOfUnity p K) :=
    fun x => fun i => ⟨x.1 i, by
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp x.2
      rw [← hs, mem_rootsOfUnity]
      change (ggNSPosPA7_ratioHom h hd i.1 a s) ^ p = 1
      exact ggNSPosPA7_ratioHom_pow h hd i.1 a s⟩
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg (fun f : {i : Fin n // i ≠ a} → rootsOfUnity p K =>
      ((f i : rootsOfUnity p K) : Kˣ)) hxy
  calc Nat.card (nsTor_ratioPi h hd a).range
      ≤ Nat.card ({i : Fin n // i ≠ a} → rootsOfUnity p K) :=
        Nat.card_le_card_of_injective Φ hΦinj
    _ = (Nat.card (rootsOfUnity p K)) ^ (Nat.card {i : Fin n // i ≠ a}) := Nat.card_fun
    _ = (Nat.card (rootsOfUnity p K)) ^ (n - 1) := by rw [nsTor_card_ne]
    _ ≤ p ^ (n - 1) := pow_le_pow_left' (card_rootsOfUnity K p) (n - 1)

end CFSG.StandardType

end
