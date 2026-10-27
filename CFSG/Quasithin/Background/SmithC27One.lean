module

public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.Background.SmithC27OTwoZ

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

namespace Hyp27

theorem le_normalizer_inf_centralizer (_h : Hyp27 H R M K) :
    K ⊔ R ≤ Subgroup.normalizer
      (((K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :
        Subgroup G) : Set G) := fun _ hx =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer_omegaOneCenterOf_pCoreOf _ hx⟩

theorem inf_centralizer_centralizes (h : Hyp27 H R M K) :
    ∀ c ∈ (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G),
      ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hKC : ¬ K ≤ (K ⊔ R) ⊓
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := fun hK =>
    h.not_le_centralizer (hK.trans inf_le_right)
  have hCK := inf_le_oTwoZIn_of_not_le h.perfect h.quasi le_sup_left
    h.le_normalizer_inf_centralizer hKC
  exact commutator_mem_pCoreOf_of_inf_le h.quasi le_sup_left h.sup_le_normalizer inf_le_left
    h.le_normalizer_inf_centralizer hCK

theorem mem_pCoreOf_of_mem_inf_centralizer (h : Hyp27 H R M K) {x : G}
    (hx : x ∈ (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    {j : ℕ} (hxj : x ^ 2 ^ j = 1) : x ∈ pCoreOf 2 (K ⊔ R) :=
  mem_pCoreOf_of_centralizes h.sup_le_normalizer (fun _ hy => h.exists_pow_mem hy) inf_le_left
    h.le_normalizer_inf_centralizer h.inf_centralizer_centralizes hx hxj

theorem le_pCoreOf_of_le_inf_centralizer (h : Hyp27 H R M K) {P : Subgroup G}
    (hP : P ≤ (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    (hP2 : IsPGroup 2 P) : P ≤ pCoreOf 2 (K ⊔ R) := fun x hx => by
  obtain ⟨j, hj⟩ := hP2 ⟨x, hx⟩
  exact h.mem_pCoreOf_of_mem_inf_centralizer (hP hx) (j := j) (congrArg Subtype.val hj)

theorem pCoreOf_le_inf_centralizer (_h : Hyp27 H R M K) :
    pCoreOf 2 (K ⊔ R) ≤
      (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
  le_inf (pCoreOf_le 2 _) (pCoreOf_le_centralizer_omegaOneCenterOf _)

theorem inf_centralizer_le (h : Hyp27 H R M K) :
    (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
      pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K :=
  le_pCoreOf_sup_oTwoZIn_of_centralizes h.sup_le_normalizer (fun _ hy => h.exists_pow_mem hy)
    inf_le_left h.le_normalizer_inf_centralizer h.inf_centralizer_centralizes

theorem isTwoReducedIn (h : Hyp27 H R M K) :
    IsTwoReducedIn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  refine ⟨omegaOneCenterOf_pCoreOf_le _, le_normalizer_omegaOneCenterOf_pCoreOf _,
    isElemAbelian_omegaOneCenterOf _, fun D hDX hXD hpowD => ?_⟩
  have hKD : ¬ K ≤ D := by
    intro hKD
    apply h.not_le_centralizer
    have hN : K ≤ Subgroup.normalizer
        ((Subgroup.centralizer (V : Set G) ⊓ K : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_centralizer_omegaOneCenterOf_pCoreOf _ (Subgroup.mem_sup_left hk),
          Subgroup.le_normalizer hk⟩
    have heq := C2Nine.eq_of_perfect_of_pow_mem h.perfect inf_le_right
      (Subgroup.normal_subgroupOf_of_le_normalizer hN) fun k hk => by
        obtain ⟨j, hj⟩ := hpowD k (hKD hk)
        exact ⟨j, hj, K.pow_mem hk _⟩
    exact heq.symm.le.trans inf_le_left
  have hDK := inf_le_oTwoZIn_of_not_le h.perfect h.quasi le_sup_left hXD hKD
  have hcentD := commutator_mem_pCoreOf_of_inf_le h.quasi le_sup_left h.sup_le_normalizer
    hDX hXD hDK
  intro d hd
  obtain ⟨a, b, rfl, haz, hbz, ⟨k, hak⟩, hbodd⟩ := exists_odd_mul_two_elt d
  have haD : a ∈ D := (Subgroup.zpowers_le.mpr hd) haz
  have haQ : a ∈ pCoreOf 2 (K ⊔ R) :=
    mem_pCoreOf_of_centralizes h.sup_le_normalizer (fun _ hy => h.exists_pow_mem hy) hDX hXD
      hcentD haD hak
  have haC : a ∈ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_omegaOneCenterOf _ haQ
  obtain ⟨j, hj⟩ := hpowD (b * a) hd
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hbz
  have hbj : b ^ 2 ^ j ∈ Subgroup.centralizer (V : Set G) := by
    have e : ((b * a) ^ i) ^ (2 ^ j : ℕ) = ((b * a) ^ (2 ^ j : ℕ)) ^ i := by
      rw [← zpow_natCast ((b * a) ^ i), ← zpow_natCast (b * a), ← zpow_mul, ← zpow_mul']
    rw [← hi, e]
    exact Subgroup.zpow_mem _ hj _
  have hcop : Nat.Coprime (orderOf b) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hbodd)
  exact Subgroup.mul_mem _ (B6.mem_of_pow_mem_of_coprime hbj hcop) haC

end Hyp27

theorem c27_one (h : Hyp27 H R M K) : C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  ⟨h.pCoreOf_le_inf_centralizer, h.inf_centralizer_le, h.isTwoReducedIn⟩

end CFSG.Quasithin.SmithC27
