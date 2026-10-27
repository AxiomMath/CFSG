module

public import CFSG.Quasithin.Vol2.Ch11SecBK4B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem flag_conclusions [IsMulCommutative ↥V] {T : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {W' : Subgroup G} (hW'V : W' ≤ V) {i : ℕ}
    (hfl : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (2 ^ n) i (W'.subgroupOf V)) :
    V ⊓ Subgroup.centralizer (L : Set G) ≤ W' ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) W' ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex W' = 2 ^ (n * i) ∧
      T ⊓ L ≤ Subgroup.normalizer (W' : Set G) := by
  obtain ⟨hZ, hst, hidx, hP⟩ := hfl
  refine ⟨fun v hv => ?_, ?_, ?_, fun t ht => ?_⟩
  · have h1 : (⟨v, hv.1⟩ : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := hv.2
    exact hZ h1
  · rw [SecA.isEndStable_iff hLV, SecA.inf_centralizer_subgroupOf]
    exact hst
  · rw [← Subgroup.relIndex_subgroupOf hW'V, SecA.inf_centralizer_subgroupOf, hidx, pow_mul]
  · have htV := hLV ht.2
    exact (SecA.conjV_mem_stabW_iff hW'V htV).mp (hP (SecA.conjV_mem_autOn ht htV))

theorem mem_conjSubgroup_iff_lin [IsMulCommutative ↥V] {D : FFModel} {M : Type}
    [AddCommGroup M] [Module K M] {LM : KGNat.LinModel D K M} {π : D.Gam →* ↥(autOn L V)}
    {f : ↥V → M}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {U : Subgroup G} {S : AddSubgroup M} (hU : ∀ v : ↥V, (v : G) ∈ U ↔ f v ∈ S) {l : G}
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) {γ : D.Gam}
    (hγ : ((π γ : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V l hlV) (v : ↥V) :
    (v : G) ∈ conjSubgroup U l ↔ LM.lin γ (f v) ∈ S := by
  rw [mem_conjSubgroup_iff, ← SecA.conjV_apply_coe V hlV v, hU, ← hγ, hf.act]

theorem two_pow_le_card_fix [Finite G] [IsMulCommutative ↥V] (hV : IsElemAbelian 2 V)
    {D : FFModel} {M : Type} [AddCommGroup M] [Module K M] {LM : KGNat.LinModel D K M}
    {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : D.Gam →* ↥H} {f : ↥V → M}
    (hf : KGNat.IsCoord LM H Z π f) {T : M →+ M} {C : Subgroup ↥V}
    (hC : ∀ w ∈ C, T (f w) = f w) {a m : ℕ} (hM : Nat.card M = 2 ^ a) (hm : rkIdx C = m) :
    2 ^ a ≤ 2 ^ m * Nat.card {x : M // T x = x} := by
  have h1 := card_le_index_mul hf hC
  rwa [hM, index_eq_two_pow hV C, hm] at h1

omit [Field K] in
theorem card_mul_le_of_mem {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Finite M]
    {S S' : Submodule K M} (hSS' : S ≤ S') {x₀ : M} (hx₀' : x₀ ∈ S') (hx₀ : x₀ ∉ S) :
    Nat.card S * Nat.card K ≤ Nat.card S' := by
  let ψ : S × K → S' := fun p => ⟨p.1.1 + p.2 • x₀, S'.add_mem (hSS' p.1.2) (S'.smul_mem _ hx₀')⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨⟨y, hy⟩, c⟩ ⟨⟨y', hy'⟩, c'⟩ h
    have h' : y + c • x₀ = y' + c' • x₀ := congrArg Subtype.val h
    have hcc : c = c' := by
      by_contra hne
      apply hx₀
      have e1 : (c - c') • x₀ = y' - y := by
        rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm, ← h', add_comm]
      have h2 : (c - c') • x₀ ∈ S := by rw [e1]; exact S.sub_mem hy' hy
      exact (Submodule.smul_mem_iff S (sub_ne_zero.mpr hne)).mp h2
    subst hcc
    have hyy : y = y' := add_right_cancel h'
    subst hyy
    rfl
  have h1 := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_prod] at h1

theorem exists_sl3_plane [Finite K] {P : Submodule K (Fin 3 → K)}
    (hP : Nat.card P = Nat.card K ^ 2) :
    ∃ B : SpecialLinearGroup (Fin 3) K,
      ∀ x, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ P ↔ x ∈ KGNat.stdPlane K := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have htop : Nat.card (⊤ : Submodule K (Fin 3 → K)) = Nat.card K ^ 3 := by
    have h1 : Nat.card (Fin 3 → K) = Nat.card K ^ 3 := by rw [Nat.card_fun, Nat.card_fin]
    rw [← h1]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => Submodule.mem_top)
  have hlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have h1 := hP
    rw [h, htop] at h1
    have := Nat.pow_right_injective hq h1
    omega
  obtain ⟨φ, hφ0, hφP⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hPφ : P ≤ LinearMap.ker φ := fun x hx => by
    have : φ x ∈ P.map φ := Submodule.mem_map_of_mem hx
    rwa [hφP, Submodule.mem_bot] at this
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, φ x₁ ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hφ0 (LinearMap.ext h)
  have hcardker : Nat.card (LinearMap.ker φ) ≤ Nat.card K ^ 2 := by
    have h1 := card_mul_le_of_mem le_top Submodule.mem_top (x₀ := x₁)
      (S := LinearMap.ker φ) (fun h => hx₁ (LinearMap.mem_ker.mp h))
    rw [htop, pow_succ] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hker : ∀ x, x ∈ P ↔ φ x = 0 := by
    intro x
    refine ⟨fun hx => LinearMap.mem_ker.mp (hPφ hx), fun hx => ?_⟩
    by_contra hxP
    have h1 := card_mul_le_of_mem hPφ (LinearMap.mem_ker.mpr hx) hxP
    rw [hP, ← pow_succ] at h1
    have h2 := Nat.pow_le_pow_iff_right hq |>.mp (h1.trans hcardker)
    omega
  set r : Fin 3 → K := fun i => φ (Pi.single i 1) with hr
  have hφr : ∀ x, φ x = r ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm, hr]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hr0 : r ≠ 0 := by
    intro h
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφr, h, zero_dotProduct, LinearMap.zero_apply]
  have he2 : (![0, 0, 1] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 2)
  obtain ⟨γ, hγ⟩ := KGNat.exists_sl3_lin_eq r ![0, 0, 1] hr0 he2
  set A : SpecialLinearGroup (Fin 3) K := (specialLinearGroupEquivStatedSL 3 K).symm γ with hA
  have hAr : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ r = ![0, 0, 1] := by
    rw [← hγ, KGNat.linModelNat_lin]
    have : specialLinearGroupEquivStatedSL 3 K A = γ := by rw [hA, MulEquiv.apply_symm_apply]
    rw [← this]
    rfl
  refine ⟨⟨(A : Matrix (Fin 3) (Fin 3) K)ᵀ, by rw [Matrix.det_transpose]; exact A.2⟩,
    fun x => ?_⟩
  rw [hker, hφr, KGNat.mem_stdPlane]
  change r ⬝ᵥ ((A : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ x) = 0 ↔ x 2 = 0
  rw [dotProduct_mulVec, vecMul_transpose, hAr]
  simp [dotProduct, Fin.sum_univ_three]

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
