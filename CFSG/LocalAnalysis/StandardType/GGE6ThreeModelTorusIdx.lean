module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise


@[expose] def coTorus (Ω : Type) [Field Ω] (N : ℕ) : Subgroup (ModGL Tag.E6 Ω) :=
  Subgroup.closure {x | ∃ (i : Fin Tag.E6.rank) (s : Ωˣ), s ^ N = 1 ∧ x = torusElt Tag.E6 Ω i s}


variable {Ω : Type} [Field Ω]

private theorem cw_spec :
    ∀ i k : Fin Tag.E6.rank,
      (∑ j : Fin Tag.E6.rank, (![![0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![-1, 0, 0, 0, 0, 0],
          ![2, 3, 4, 6, 4, 2], ![0, 1, 1, 2, 2, 1], ![-2, -1, -2, -2, -1, 0]] :
            Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) i j * Tag.E6.cartan j k) =
        (if k = i then 1 else 0) - (![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i *
          (if k = 0 then 1 else 0) := by
  decide +kernel

private theorem cw_cube_spec : ∀ k : Fin Tag.E6.rank,
    (∑ j : Fin Tag.E6.rank, (![4, 3, 5, 6, 4, 2] : Fin Tag.E6.rank → ℤ) j *
        Tag.E6.cartan j k) = 3 * (if k = 0 then 1 else 0) := by
  decide +kernel

private theorem zpow_pow_eq_one_of_pow_eq_one {G : Type} [CommGroup G] {s : G} {N : ℕ}
    (hs : s ^ N = 1) (a : ℤ) : (s ^ a) ^ N = 1 := by
  rw [← zpow_natCast, ← zpow_mul]
  rw [show a * (N : ℤ) = (N : ℤ) * a by ring]
  rw [zpow_mul, zpow_natCast, hs, one_zpow]

private theorem rootDiagUnit_zpow {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ)
    (n : ℤ) : rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) := by
  rcases n with m | m
  · rw [Int.ofNat_eq_coe, zpow_natCast, zpow_natCast, rootDiagUnit_pow]
  · rw [zpow_negSucc, zpow_negSucc, rootDiagUnit_pow, rootDiagUnit_inv]

private theorem rootDiagUnit_list_prod (L : List (Fin Tag.E6.rank → Ωˣ)) :
    rootDiagUnit Tag.E6 L.prod = (L.map (rootDiagUnit Tag.E6)).prod := by
  induction L with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, rootDiagUnit_one]
  | cons a L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, rootDiagUnit_mul, ih]

private theorem rootDiagUnit_mul_comm (b b' : Fin Tag.E6.rank → Ωˣ) :
    rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 b' =
      rootDiagUnit Tag.E6 b' * rootDiagUnit Tag.E6 b := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

private theorem thetaTorus_le_centralizer (q : ℕ) {z : ModGL Tag.E6 Ω}
    (hz : z ∈ TwistedDiag.thetaTorus Ω q) :
    TwistedDiag.thetaTorus Ω q ≤
      Subgroup.centralizer (Subgroup.zpowers z : Set (ModGL Tag.E6 Ω)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨b, -, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx
  obtain ⟨b', -, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact (show Commute (rootDiagUnit Tag.E6 b') (rootDiagUnit Tag.E6 b) from
    (rootDiagUnit_mul_comm b b').symm).zpow_left m

private theorem mulSingle_eq_pow {n : ℕ} {G : Type} [Group G] (i : Fin n) (u : G) :
    (Pi.mulSingle i u : Fin n → G) = fun k => u ^ (if k = i then (1 : ℤ) else 0) := by
  funext k
  by_cases h : k = i <;> simp [Pi.mulSingle_apply, h]

private theorem mulSingle_zpow {n : ℕ} [NeZero n] {G : Type} [Group G] (i : Fin n) (u : G)
    (c : ℤ) :
    (Pi.mulSingle i u : Fin n → G) ^ c = fun k => u ^ (c * (if k = i then (1 : ℤ) else 0)) := by
  funext k
  change (Pi.mulSingle (M := fun _ : Fin n => G) i u : Fin n → G) k ^ c =
    u ^ (c * (if k = i then (1 : ℤ) else 0))
  by_cases h : k = i <;> simp [Pi.mulSingle_apply, h]

private theorem mulSingle_mul_zpow {n : ℕ} [NeZero n] {G : Type} [CommGroup G] (i : Fin n)
    (u : G) (c : ℤ) :
    (Pi.mulSingle i u : Fin n → G) * (Pi.mulSingle (0 : Fin n) u) ^ (-c) =
      fun k => u ^ ((if k = i then (1 : ℤ) else 0) - c * (if k = 0 then (1 : ℤ) else 0)) := by
  rw [mulSingle_eq_pow i u, mulSingle_zpow 0 u (-c)]
  funext k
  rw [Pi.mul_apply, ← zpow_add]
  congr 1
  ring

private theorem rootDiagUnit_mul_zpow_eq (i : Fin Tag.E6.rank) (u : Ωˣ) :
    rootDiagUnit Tag.E6 (Pi.mulSingle i u) *
        (rootDiagUnit Tag.E6 (Pi.mulSingle (0 : Fin Tag.E6.rank) u)) ^
          (-(![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i) =
      rootDiagUnit Tag.E6 (fun k => u ^ (∑ j : Fin Tag.E6.rank,
        (![![0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![-1, 0, 0, 0, 0, 0],
           ![2, 3, 4, 6, 4, 2], ![0, 1, 1, 2, 2, 1], ![-2, -1, -2, -2, -1, 0]] :
             Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) i j * Tag.E6.cartan j k)) := by
  rw [rootDiagUnit_zpow, ← rootDiagUnit_mul]
  congr 1
  rw [mulSingle_mul_zpow i u ((![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i)]
  funext k
  rw [cw_spec i k]

private theorem rootDiagUnit_mem_coTorus_of_zpow (q : ℕ) {u : Ωˣ} (hu : u ^ (q + 1) = 1)
    (m : Fin Tag.E6.rank → ℤ) :
    rootDiagUnit Tag.E6 (fun k => u ^ (∑ j, m j * Tag.E6.cartan j k)) ∈
      coTorus Ω (q + 1) := by
  have hc : cartanChar (fun j => u ^ m j) =
      (fun k => u ^ (∑ j, m j * Tag.E6.cartan j k)) := by
    funext k
    rw [cartanChar, ← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_mul]
  rw [← hc, ← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, u ^ m j, zpow_pow_eq_one_of_pow_eq_one hu (m j), rfl⟩

private theorem exists_zpowers_cover (q : ℕ) :
    ∃ z ∈ TwistedDiag.thetaTorus Ω q, z ^ 3 ∈ coTorus Ω (q + 1) ∧
      TwistedDiag.thetaTorus Ω q ≤ coTorus Ω (q + 1) ⊔ Subgroup.zpowers z := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥(rootsOfUnity (q + 1) Ω))
  let u₀ : Ωˣ := (u : Ωˣ)
  have hu₀ : u₀ ^ (q + 1) = 1 := by
    simpa [u₀] using (mem_rootsOfUnity (q + 1) u₀).mp u.2
  let z : ModGL Tag.E6 Ω := rootDiagUnit Tag.E6 (Pi.mulSingle 0 u₀)
  have hzX : z ∈ TwistedDiag.thetaTorus Ω q := by
    rw [TwistedDiag.mem_thetaTorus]
    refine ⟨Pi.mulSingle (0 : Fin Tag.E6.rank) u₀, ?_, rfl⟩
    intro k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simpa using hu₀
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
  have hz3S : z ^ 3 ∈ coTorus Ω (q + 1) := by
    have hz : z ^ 3 = rootDiagUnit Tag.E6 (fun k => u₀ ^ (∑ j : Fin Tag.E6.rank,
        (![4, 3, 5, 6, 4, 2] : Fin Tag.E6.rank → ℤ) j * Tag.E6.cartan j k)) := by
      dsimp only [z]
      rw [rootDiagUnit_pow]
      congr 1
      have h3 : ((3 : ℕ) : ℤ) = (3 : ℤ) := by norm_num
      rw [← zpow_natCast, h3, mulSingle_zpow 0 u₀ 3]
      funext k
      rw [cw_cube_spec k]
    rw [hz]
    exact rootDiagUnit_mem_coTorus_of_zpow q hu₀ (![4, 3, 5, 6, 4, 2] : Fin Tag.E6.rank → ℤ)
  refine ⟨z, hzX, hz3S, ?_⟩
  intro x hx
  obtain ⟨b, hb, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx
  have he : ∀ i : Fin Tag.E6.rank, ∃ e : ℤ, u₀ ^ e = b i := by
    intro i
    have hmem : (⟨b i, (mem_rootsOfUnity (q + 1) (b i)).mpr (hb i)⟩ :
          ↥(rootsOfUnity (q + 1) Ω)) ∈
        Subgroup.zpowers u := hu _
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact ⟨e, by simpa [u₀] using congrArg Subtype.val he⟩
  choose e hee using he
  have hb_eq' : b = ((List.finRange Tag.E6.rank).map fun i => Pi.mulSingle i (b i)).prod := by
    rw [← List.ofFn_eq_map, List.prod_ofFn]
    exact (Finset.univ_prod_mulSingle b).symm
  have hmap : rootDiagUnit Tag.E6 b =
      ((List.finRange Tag.E6.rank).map fun i =>
        rootDiagUnit Tag.E6 (Pi.mulSingle i (b i))).prod := by
    conv_lhs => rw [hb_eq']
    rw [rootDiagUnit_list_prod, List.map_map]
    rfl
  rw [hmap]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  have hfactor : rootDiagUnit Tag.E6 (Pi.mulSingle i (b i)) =
      (rootDiagUnit Tag.E6 (Pi.mulSingle i u₀)) ^ (e i) := by
    rw [← hee i, rootDiagUnit_zpow]
    congr 1
    exact map_zpow (MonoidHom.mulSingle (fun _ : Fin Tag.E6.rank => Ωˣ) i) u₀ (e i)
  rw [hfactor]
  have homega : rootDiagUnit Tag.E6 (Pi.mulSingle i u₀) ∈
      coTorus Ω (q + 1) ⊔ Subgroup.zpowers z := by
    have hA : rootDiagUnit Tag.E6 (Pi.mulSingle i u₀) *
        z ^ (-(![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i) ∈ coTorus Ω (q + 1) := by
      dsimp only [z]
      rw [rootDiagUnit_mul_zpow_eq i u₀]
      exact rootDiagUnit_mem_coTorus_of_zpow q hu₀
        ((![![0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![-1, 0, 0, 0, 0, 0],
           ![2, 3, 4, 6, 4, 2], ![0, 1, 1, 2, 2, 1], ![-2, -1, -2, -2, -1, 0]] :
             Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) i)
    have hdecomp : rootDiagUnit Tag.E6 (Pi.mulSingle i u₀) =
        (rootDiagUnit Tag.E6 (Pi.mulSingle i u₀) *
          z ^ (-(![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i)) *
          z ^ ((![1, 0, 2, 0, 1, 2] : Fin Tag.E6.rank → ℤ) i) := by
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [hdecomp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hA)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z _))
  exact Subgroup.zpow_mem _ homega (e i)

theorem coTorus_le_thetaTorus (q : ℕ) : coTorus Ω (q + 1) ≤ TwistedDiag.thetaTorus Ω q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, s, hs, rfl⟩
  rw [torusElt_eq_rootDiagUnit]
  refine TwistedDiag.mem_thetaTorus.2 ⟨fun j => s ^ Tag.E6.cartan i j, ?_, rfl⟩
  intro j
  exact zpow_pow_eq_one_of_pow_eq_one hs (Tag.E6.cartan i j)

theorem thetaTorus_le_sup_of_not_mem (q : ℕ) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ TwistedDiag.thetaTorus Ω q) (hxS : x ∉ coTorus Ω (q + 1)) :
    TwistedDiag.thetaTorus Ω q ≤ coTorus Ω (q + 1) ⊔ Subgroup.zpowers x := by
  obtain ⟨z, hzX, hz3S, hle⟩ := exists_zpowers_cover (Ω := Ω) q
  have hSX : coTorus Ω (q + 1) ≤ TwistedDiag.thetaTorus Ω q := coTorus_le_thetaTorus q
  have hLE : coTorus Ω (q + 1) ≤ Subgroup.normalizer (Subgroup.zpowers z) :=
    (hSX.trans (thetaTorus_le_centralizer q hzX)).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set (ModGL Tag.E6 Ω)))
  have hx_sup : x ∈ coTorus Ω (q + 1) ⊔ Subgroup.zpowers z := hle hx
  have hset : (↑(coTorus Ω (q + 1) ⊔ Subgroup.zpowers z) : Set (ModGL Tag.E6 Ω)) =
      (coTorus Ω (q + 1) : Set (ModGL Tag.E6 Ω)) *
        (Subgroup.zpowers z : Set (ModGL Tag.E6 Ω)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE
  have hx' : x ∈ (coTorus Ω (q + 1) : Set (ModGL Tag.E6 Ω)) *
      (Subgroup.zpowers z : Set (ModGL Tag.E6 Ω)) := by rwa [← hset]
  obtain ⟨s, hsS, t, ht, hst⟩ := Set.mem_mul.1 hx'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hst' : s * z ^ k = x := by rw [hk]; exact hst
  have hkmod : k % 3 ≠ 0 := by
    intro h0
    apply hxS
    have hk_eq : k = 3 * (k / 3) := by
      have h := Int.mul_ediv_add_emod k 3
      rw [h0, add_zero] at h
      exact h.symm
    have hz_k_S : z ^ k ∈ coTorus Ω (q + 1) := by
      rw [hk_eq, zpow_mul]
      exact Subgroup.zpow_mem _ hz3S (k / 3)
    rw [← hst']
    exact Subgroup.mul_mem _ hsS hz_k_S
  have hz_in : z ∈ coTorus Ω (q + 1) ⊔ Subgroup.zpowers x := by
    have hz3S' : z ^ (3 : ℤ) ∈ coTorus Ω (q + 1) := by
      convert hz3S using 1
    set m : ℤ := k / 3 with hm
    set r : ℤ := k % 3 with hr
    have hkr : k = 3 * m + r := by
      rw [hm, hr]
      exact (Int.mul_ediv_add_emod k 3).symm
    have hr_ne : r ≠ 0 := by rw [hr]; exact hkmod
    have hr_pos : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg k (by norm_num)
    have hr_lt : r < 3 := by rw [hr]; exact Int.emod_lt_of_pos k (by norm_num)
    have h1or2 : r = 1 ∨ r = 2 := by omega
    have hA_mem : (z ^ (3 : ℤ)) ^ m ∈ coTorus Ω (q + 1) := Subgroup.zpow_mem _ hz3S' m
    have hzk : z ^ k = (z ^ (3 : ℤ)) ^ m * z ^ r := by
      rw [hkr, zpow_add, zpow_mul]
    have hzks : z ^ k = s⁻¹ * x := by rw [← hst']; group
    have hzr : z ^ r = ((z ^ (3 : ℤ)) ^ m)⁻¹ * (s⁻¹ * x) := by
      have h : (z ^ (3 : ℤ)) ^ m * z ^ r = s⁻¹ * x := by rw [← hzk, hzks]
      rw [← h]; group
    rcases h1or2 with hr1 | hr2
    · have hzr' : z = z ^ r := by rw [hr1, zpow_one]
      have hz_eq : z = ((z ^ (3 : ℤ)) ^ m)⁻¹ * (s⁻¹ * x) := hzr'.trans hzr
      rw [hz_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hA_mem))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hsS))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
    · have hz2' : z ^ (2 : ℤ) = z ^ r := by rw [hr2]
      have hz2 : z ^ (2 : ℤ) = ((z ^ (3 : ℤ)) ^ m)⁻¹ * (s⁻¹ * x) := hz2'.trans hzr
      have hz_eq : z = z ^ (3 : ℤ) * (z ^ (2 : ℤ))⁻¹ := by group
      rw [hz_eq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hz3S') ?_
      rw [hz2]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hA_mem))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hsS))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
  exact hle.trans (sup_le le_sup_left (Subgroup.zpowers_le.2 hz_in))

end CFSG.StandardType.E6ThreeModel
