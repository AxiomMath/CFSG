module

public import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S51Sp

public section

namespace CFSG.Quasithin.MS93.S51

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def conjA (g : MSP.Sp4 F) (a : ↥M →* ↥(StatedSp 2 F)) : ↥M →* ↥(StatedSp 2 F) :=
  (MulAut.conj g).toMonoidHom.comp a

theorem conjA_apply (g : MSP.Sp4 F) (m : ↥M) : conjA g a m = g * a m * g⁻¹ := rfl

theorem imSp_conjA (g : MSP.Sp4 F) (E : Subgroup G) :
    S5.imSp (conjA g a) E = (S5.imSp a E).map (MulAut.conj g).toMonoidHom := by
  rw [S5.imSp, S5.imSp, conjA, Subgroup.map_map]

theorem IsSp4Data.conjA [Fintype F] (hd : S5.IsSp4Data M T L k F a) (g : MSP.Sp4 F) :
    S5.IsSp4Data M T L k F (conjA g a) := by
  obtain ⟨hk, hF, hsurj, hMU, hZU, β, hβs, hβk, hβeq⟩ := hd
  let φ : (Fin 1 → MSP.V4 F) →+ (Fin 1 → MSP.V4 F) :=
    { toFun := fun x i => MSP.mat g *ᵥ x i
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp [Matrix.mulVec_add] }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext i
    exact MSP.mulVec_mat_injective g (congrFun hxy i)
  let β' := (AddMonoidHom.toMultiplicative φ).comp β
  refine ⟨hk, hF, fun y => ?_, hMU, hZU, β', ?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hsurj (g⁻¹ * y * g)
    refine ⟨m, ?_⟩
    rw [conjA_apply, hm]
    group
  · intro y
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun i => MSP.mat g⁻¹ *ᵥ Multiplicative.toAdd y i)
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (φ (Multiplicative.toAdd (β u))) = y
    rw [hu]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [φ]
    simp
    rw [← MSP.mat_mul, mul_inv_cancel, MSP.mat_one, Matrix.one_mulVec]
  · rw [← hβk]
    ext u
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : φ (Multiplicative.toAdd (β u)) = φ 0 := by
        rw [map_zero]
        exact congrArg Multiplicative.toAdd h
      have h2 := hφinj h1
      exact Multiplicative.toAdd.injective h2
    · intro h
      show Multiplicative.ofAdd (φ (Multiplicative.toAdd (β u))) = 1
      rw [h]
      simp
  · intro m u v huv i
    have h1 := hβeq m u v huv i
    show MSP.mat g *ᵥ Multiplicative.toAdd (β v) i = _
    rw [h1]
    simp only [CFSG.Quasithin.moduleAct, Bool.false_eq_true, ↓reduceIte, conjA_apply]
    show MSP.mat g *ᵥ (MSP.mat (a m) *ᵥ _) = MSP.mat (g * a m * g⁻¹) *ᵥ (MSP.mat g *ᵥ _)
    rw [MSP.mat_mul_mulVec, MSP.mat_mul_mulVec, MSP.mat_inv_mulVec]

theorem isSylowTwoOf_of_max [Finite G] {J P : Subgroup G} (hJP : J ≤ P) (hJ2 : IsPGroup 2 J)
    (hmax : ∀ S : Subgroup G, IsPGroup 2 S → J ≤ S → S ≤ P → S ≤ J) : IsSylowTwoOf J P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ2' : IsPGroup 2 (J.subgroupOf P) :=
    hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJP).symm
  obtain ⟨S, hS⟩ := hJ2'.exists_le_sylow
  have hS2 : IsPGroup 2 ((S : Subgroup ↥P).map P.subtype) := S.isPGroup'.map _
  have hJS : J ≤ (S : Subgroup ↥P).map P.subtype := fun j hj =>
    ⟨⟨j, hJP hj⟩, hS (Subgroup.mem_subgroupOf.2 hj), rfl⟩
  have hle := hmax _ hS2 hJS (Subgroup.map_subtype_le _)
  have heq : (S : Subgroup ↥P) = J.subgroupOf P :=
    le_antisymm (fun x hx => Subgroup.mem_subgroupOf.2 (hle ⟨x, hx, rfl⟩)) hS
  refine ⟨hJP, hJ2, ?_⟩
  rw [← heq]
  exact S.not_dvd_index

variable [Finite G]

theorem le_of_isPGroup_of_imSp_le [Fintype F] (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {J S : Subgroup G} (hQJ : pCoreOf 2 M ≤ J) (hJS : J ≤ S) (hSM : S ≤ M)
    (hS2 : IsPGroup 2 S) (hSa : S5.imSp a S ≤ S5.imSp a J) : S ≤ J := by
  intro s hs
  obtain ⟨j, hj, hjM, hja⟩ := S5.mem_imSp.1 (hSa (S5.mem_imSp.2 ⟨s, hs, hSM hs, rfl⟩))
  have hk : j⁻¹ * s ∈ S5.kerG a := by
    refine (S5.mem_kerG a).2 ⟨M.mul_mem (M.inv_mem hjM) (hSM hs), ?_⟩
    have e : (⟨j⁻¹ * s, M.mul_mem (M.inv_mem hjM) (hSM hs)⟩ : ↥M) =
        (⟨j, hjM⟩ : ↥M)⁻¹ * ⟨s, hSM hs⟩ := rfl
    rw [e, map_mul, map_inv, hja, inv_mul_cancel]
  have hk2 : ∃ e : ℕ, (j⁻¹ * s) ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hS2 ⟨j⁻¹ * s, S.mul_mem (S.inv_mem (hJS hj)) hs⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hQ := hd.mem_pCoreOf_of_mem_kerG h hk hk2
  have : s = j * (j⁻¹ * s) := by group
  rw [this]
  exact J.mul_mem hj (hQJ hQ)

theorem normalizer_le_imSp [Fintype F] (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {J : Subgroup G} (hJM : J ≤ M) (hJ2 : IsPGroup 2 J) (hQJ : pCoreOf 2 M ≤ J) :
    Subgroup.normalizer (S5.imSp a J : Set (MSP.Sp4 F)) ≤
      S5.imSp a (Subgroup.normalizer (J : Set G) ⊓ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := S5.kerG a with hN
  set K := J ⊔ N with hK
  have hNM : N ≤ M := S5.kerG_le a
  have hKM : K ≤ M := sup_le hJM hNM
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := hJM.trans (S5.le_normalizer_kerG a)
  have hKset : ((K : Subgroup G) : Set G) = (J : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right J N hJN
  have hdec : ∀ x ∈ K, ∃ j ∈ J, ∃ n ∈ N, j * n = x := by
    intro x hx
    have : x ∈ ((K : Subgroup G) : Set G) := hx
    rw [hKset] at this
    obtain ⟨j, hj, n, hn, rfl⟩ := this
    exact ⟨j, hj, n, hn, rfl⟩
  have himK : S5.imSp a K ≤ S5.imSp a J := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, n, hn, hjn⟩ := hdec x (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨hnM', hn1⟩ := (S5.mem_kerG a).1 hn
    refine S5.mem_imSp.2 ⟨j, hj, hJM hj, ?_⟩
    have e : x = ⟨j, hJM hj⟩ * ⟨n, hnM'⟩ := Subtype.ext hjn.symm
    rw [e, map_mul, hn1, mul_one]
  have hsyl : IsSylowTwoOf J K := isSylowTwoOf_of_max le_sup_left hJ2 fun S hS2 hJS hSK =>
    le_of_isPGroup_of_imSp_le hd h hQJ hJS (hSK.trans hKM) hS2
      ((S5.imSp_mono a hSK).trans himK)
  have hconj : ∀ y ∈ M, ∀ (hy : y ∈ M), a ⟨y, hy⟩ ∈
      Subgroup.normalizer (S5.imSp a J : Set (MSP.Sp4 F)) → ∀ x ∈ K, y * x * y⁻¹ ∈ K := by
    intro y hyM hy hya x hx
    obtain ⟨j, hj, n, hn, rfl⟩ := hdec x hx
    have hjM := hJM hj
    have hyj : a ⟨y * j * y⁻¹, M.mul_mem (M.mul_mem hy hjM) (M.inv_mem hy)⟩ ∈ S5.imSp a J := by
      have e : (⟨y * j * y⁻¹, M.mul_mem (M.mul_mem hy hjM) (M.inv_mem hy)⟩ : ↥M) =
          ⟨y, hy⟩ * ⟨j, hjM⟩ * (⟨y, hy⟩ : ↥M)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hya _).1 (S5.mem_imSp.2 ⟨j, hj, hjM, rfl⟩)
    obtain ⟨j', hj', hj'M, hja⟩ := S5.mem_imSp.1 hyj
    have hk : j'⁻¹ * (y * j * y⁻¹) ∈ N := by
      refine (S5.mem_kerG a).2 ⟨M.mul_mem (M.inv_mem hj'M)
        (M.mul_mem (M.mul_mem hy hjM) (M.inv_mem hy)), ?_⟩
      have e : (⟨j'⁻¹ * (y * j * y⁻¹), M.mul_mem (M.inv_mem hj'M)
          (M.mul_mem (M.mul_mem hy hjM) (M.inv_mem hy))⟩ : ↥M) = (⟨j', hj'M⟩ : ↥M)⁻¹ *
          ⟨y * j * y⁻¹, M.mul_mem (M.mul_mem hy hjM) (M.inv_mem hy)⟩ := rfl
      rw [e, map_mul, map_inv, hja, inv_mul_cancel]
    have hyn : y * n * y⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (S5.le_normalizer_kerG a hy) n).1 hn
    have e : y * (j * n) * y⁻¹ = j' * (j'⁻¹ * (y * j * y⁻¹)) * (y * n * y⁻¹) := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (Subgroup.mem_sup_left hj') (Subgroup.mem_sup_right hk))
      (Subgroup.mem_sup_right hyn)
  intro yb hyb
  obtain ⟨⟨y, hy⟩, rfl⟩ := hd.surj yb
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj y hy hy hyb x, fun hx => ?_⟩
    have hyi : a ⟨y⁻¹, M.inv_mem hy⟩ ∈ Subgroup.normalizer (S5.imSp a J : Set (MSP.Sp4 F)) := by
      have e : (⟨y⁻¹, M.inv_mem hy⟩ : ↥M) = (⟨y, hy⟩ : ↥M)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ hyb
    have := hconj y⁻¹ (M.inv_mem hy) (M.inv_mem hy) hyi _ hx
    simpa [mul_assoc] using this
  have hJK : (J.subgroupOf K).index = J.relIndex K := rfl
  let P₁ : Sylow 2 ↥K := (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow
    hsyl.2.2
  have hJ'K : (J.map (MulAut.conj y).toMonoidHom) ≤ K := by
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hyK j).1 (Subgroup.mem_sup_left hj)
  have hJ'2 : IsPGroup 2 (J.map (MulAut.conj y).toMonoidHom) := hJ2.map _
  have hidx : (J.map (MulAut.conj y).toMonoidHom).relIndex K = J.relIndex K := by
    have h1 := Subgroup.relIndex_mul_card (J.map (MulAut.conj y).toMonoidHom) K
    have h2 := Subgroup.relIndex_mul_card J K
    rw [inf_eq_left.2 hJ'K] at h1
    rw [inf_eq_left.2 le_sup_left] at h2
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  let P₂ : Sylow 2 ↥K := (hJ'2.of_equiv (Subgroup.subgroupOfEquivOfLe hJ'K).symm).toSylow
    (by rw [show ((J.map (MulAut.conj y).toMonoidHom).subgroupOf K).index =
      (J.map (MulAut.conj y).toMonoidHom).relIndex K from rfl, hidx]; exact hsyl.2.2)
  obtain ⟨κ, hκ⟩ := MulAction.exists_smul_eq (↥K) P₂ P₁
  have hκJ : ∀ x : G, x ∈ J ↔ (κ : G) * y * x * ((κ : G) * y)⁻¹ ∈ J := by
    intro x
    have hP₁ : ∀ z : ↥K, z ∈ P₁ ↔ (z : G) ∈ J := fun z => by
      rw [IsPGroup.mem_toSylow, Subgroup.mem_subgroupOf]
    have hP₂ : ∀ z : ↥K, z ∈ P₂ ↔ (z : G) ∈ J.map (MulAut.conj y).toMonoidHom := fun z => by
      rw [IsPGroup.mem_toSylow, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : (⟨y * x * y⁻¹, hJ'K ⟨x, hx, rfl⟩⟩ : ↥K) ∈ P₂ := (hP₂ _).2 ⟨x, hx, rfl⟩
      have h2 : κ * ⟨y * x * y⁻¹, hJ'K ⟨x, hx, rfl⟩⟩ * κ⁻¹ ∈ P₁ := by
        rw [← hκ]
        exact Subgroup.mem_map_of_mem _ h1
      rw [hP₁] at h2
      simpa [mul_assoc] using h2
    · intro hx
      have hxK : (κ : G) * y * x * ((κ : G) * y)⁻¹ ∈ K := hsyl.1 hx
      have h1 : (⟨_, hxK⟩ : ↥K) ∈ P₁ := (hP₁ _).2 hx
      rw [← hκ] at h1
      obtain ⟨z, hz, hzx⟩ := h1
      have hz' := (hP₂ z).1 hz
      obtain ⟨w, hw, hwz⟩ := hz'
      have e1 : ((κ * z * κ⁻¹ : ↥K) : G) = (κ : G) * y * x * ((κ : G) * y)⁻¹ :=
        congrArg Subtype.val hzx
      have e2 : (z : G) = y * w * y⁻¹ := hwz.symm
      have e3 : x = w := by
        have : (κ : G) * (y * w * y⁻¹) * (κ : G)⁻¹ = (κ : G) * y * x * ((κ : G) * y)⁻¹ := by
          rw [← e2]
          simpa using e1
        have : (κ : G) * y * w * ((κ : G) * y)⁻¹ = (κ : G) * y * x * ((κ : G) * y)⁻¹ := by
          rw [← this]
          group
        simpa using this.symm
      rw [e3]
      exact hw
  have hκyN : (κ : G) * y ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact hκJ x
  obtain ⟨j, hj, n, hn, hjn⟩ := hdec κ κ.2
  obtain ⟨hnM, hn1⟩ := (S5.mem_kerG a).1 hn
  have hxe : j⁻¹ * ((κ : G) * y) = n * y := by
    rw [← hjn]
    group
  have hxM : n * y ∈ M := M.mul_mem hnM hy
  refine S5.mem_imSp.2 ⟨n * y, ⟨?_, hxM⟩, hxM, ?_⟩
  · rw [← hxe]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hj)) hκyN
  · have e : (⟨n * y, hxM⟩ : ↥M) = ⟨n, hnM⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, hn1, one_mul]

theorem exists_odd_imSp_xBar [CharP F 2] {P : Subgroup G} (hx : xBar F ∈ S5.imSp a P) :
    ∃ x ∈ P, ∃ hxM : x ∈ M, Odd (orderOf x) ∧
      (a ⟨x, hxM⟩ = xBar F ∨ a ⟨x, hxM⟩ = (xBar F)⁻¹) := by
  obtain ⟨p, hp, hpM, hpa⟩ := S5.mem_imSp.1 hx
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p).ne'
  have hxM : p ^ 2 ^ e ∈ M := M.pow_mem hpM _
  refine ⟨p ^ 2 ^ e, P.pow_mem hp _, hxM, ?_, ?_⟩
  · have h1 : (p ^ 2 ^ e) ^ m = 1 := by rw [← pow_mul, ← he, pow_orderOf_eq_one]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · have e1 : (⟨p ^ 2 ^ e, hxM⟩ : ↥M) = (⟨p, hpM⟩ : ↥M) ^ 2 ^ e := rfl
    rw [e1, map_pow, hpa, pow_eq_pow_mod _ xBar_pow_three]
    have h3 : ¬ 3 ∣ 2 ^ e := fun h =>
      absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h)) (by norm_num)
    have hmod : 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 := by omega
    rcases hmod with h | h
    · left
      rw [h, pow_one]
    · right
      rw [h, inv_eq_of_mul_eq_one_right]
      rw [← pow_succ', xBar_pow_three]

end CFSG.Quasithin.MS93.S51
