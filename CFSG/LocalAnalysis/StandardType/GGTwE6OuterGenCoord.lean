module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LieType.Chevalley.E6ToralGraphInvolution
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.TwE6OuterGen

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem corootTuple_single_one_apply {L : Type} [Field L] (ζ : Lˣ) (k : Fin 6) :
    TwE6RootAs.corootTuple (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) ζ k =
      ζ ^ ((![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) k) := by
  have h : ∀ k : Fin 6, ∑ l, TwistTag.E6.tag.cartan k l *
      (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ) : Fin TwistTag.E6.tag.rank → ℤ) l =
        (![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) k := by
    decide +kernel
  exact congrArg (fun e : ℤ => ζ ^ e) (h k)


theorem exists_mem_conj_eq_corootTuple {K : Type} [Field K] [Finite K]
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hel : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 4)
    {N : ModGL TwistTag.E6.tag K}
    (hN : ∀ x ∈ A, N * x * N⁻¹ ∈ torusGroup TwistTag.E6.tag K ∧
      diagramMap TwistTag.E6 K * (N * x * N⁻¹) = N * x * N⁻¹ * diagramMap TwistTag.E6 K)
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    ∃ x ∈ A, N * x * N⁻¹ = rootDiagUnit TwistTag.E6.tag
      (TwE6RootAs.corootTuple (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) ζ) := by
  classical
  have hb : ∀ x : A, ∃ b : Fin 6 → Kˣ,
      N * (x : ModGL TwistTag.E6.tag K) * N⁻¹ = rootDiagUnit TwistTag.E6.tag b :=
    fun x => exists_rootDiagUnit_eq_of_mem_torusGroup (hN x x.2).1
  choose b hbx using hb
  have hρ : ∀ x : A, b x 4 = b x 2 ∧ b x 5 = b x 0 := by
    intro x
    have h := (hN x x.2).2
    rw [hbx, E6_diagramMap_mul_rootDiagUnit] at h
    have h' := rootDiagUnit_injective (mul_right_cancel h)
    exact ⟨(congrFun h' (4 : Fin 6)).symm, (congrFun h' (5 : Fin 6)).symm⟩
  have h3 : ∀ x : A, ∀ i, b x i ^ 3 = 1 := by
    intro x i
    have hx3 : (N * (x : ModGL TwistTag.E6.tag K) * N⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hel.2 _ x.2, mul_one, mul_inv_cancel]
    have h : rootDiagUnit TwistTag.E6.tag (b x ^ 3 : Fin 6 → Kˣ) =
        rootDiagUnit TwistTag.E6.tag (1 : Fin 6 → Kˣ) := by
      rw [E6_rootDiagUnit_one, pow_three, E6_rootDiagUnit_mul, E6_rootDiagUnit_mul, ← hbx,
        ← pow_three, hx3]
    exact congrFun (rootDiagUnit_injective h) i
  let f : A → Fin 4 → rootsOfUnity 3 K := fun x j =>
    ⟨b x ((![0, 1, 2, 3] : Fin 4 → Fin 6) j), (mem_rootsOfUnity 3 _).2 (h3 x _)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hco : ∀ j : Fin 4, b x ((![0, 1, 2, 3] : Fin 4 → Fin 6) j) =
        b y ((![0, 1, 2, 3] : Fin 4 → Fin 6) j) :=
      fun j => congrArg Subtype.val (congrFun hxy j)
    have hall : b x = b y := by
      funext i
      fin_cases i
      · exact hco 0
      · exact hco 1
      · exact hco 2
      · exact hco 3
      · exact (hρ x).1.trans ((hco 2).trans (hρ y).1.symm)
      · exact (hρ x).2.trans ((hco 0).trans (hρ y).2.symm)
    have hxy' : N * (x : ModGL TwistTag.E6.tag K) * N⁻¹ = N * y * N⁻¹ := by
      rw [hbx, hbx, hall]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hxy'))
  have hcard : Nat.card (Fin 4 → rootsOfUnity 3 K) ≤ Nat.card A := by
    rw [Nat.card_fun, Nat.card_fin, hc]
    exact Nat.pow_le_pow_left (card_rootsOfUnity K 3) 4
  obtain ⟨-, hsurj⟩ := hinj.bijective_of_nat_card_le hcard
  obtain ⟨c, hcdef⟩ : ∃ c : Fin 6 → Kˣ,
      TwE6RootAs.corootTuple (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) ζ = c :=
    ⟨_, rfl⟩
  have hcv : ∀ k : Fin 6, c k = ζ ^ ((![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) k) := fun k => by
    rw [← hcdef]
    exact corootTuple_single_one_apply ζ k
  have hc3 : ∀ k : Fin 6, c k ^ 3 = 1 := fun k => by
    rw [hcv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  obtain ⟨x, hx⟩ := hsurj fun j =>
    ⟨c ((![0, 1, 2, 3] : Fin 4 → Fin 6) j), (mem_rootsOfUnity 3 _).2 (hc3 _)⟩
  have hco : ∀ j : Fin 4, b x ((![0, 1, 2, 3] : Fin 4 → Fin 6) j) =
      c ((![0, 1, 2, 3] : Fin 4 → Fin 6) j) :=
    fun j => congrArg Subtype.val (congrFun hx j)
  have hbc : b x = c := by
    funext i
    fin_cases i
    · exact hco 0
    · exact hco 1
    · exact hco 2
    · exact hco 3
    · exact (hρ x).1.trans ((hco 2).trans ((hcv 2).trans (hcv 4).symm))
    · exact (hρ x).2.trans ((hco 0).trans ((hcv 0).trans (hcv 5).symm))
  refine ⟨x, x.2, ?_⟩
  rw [hcdef, hbx, hbc]

end CFSG.StandardType.TwE6OuterGen

end
