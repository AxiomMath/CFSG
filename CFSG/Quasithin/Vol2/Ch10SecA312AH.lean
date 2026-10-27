module

public import CFSG.Quasithin.Vol2.Ch10SecA312AB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.Quasithin.Vol2.Ch10SecA312AA

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def ZCentAt {X : Type} [Group X] (T B : Subgroup X) (z : X) : Prop :=
  z ∈ T → z ≠ 1 → (∀ t ∈ T, z * t = t * z) → (∀ b ∈ B, z * b = b * z) →
    ∀ v ∈ pCoreOf 2 B, (∀ u ∈ pCoreOf 2 B, u * v = v * u) → v * v = 1 →
      ∀ b ∈ B, b * v = v * b

@[expose] def ZCentFor (X : Type) [Group X] : Prop :=
  ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ → ∀ z : X, ZCentAt T B z

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem zcentAt_of_map (e : X ≃* Y) {T B : Subgroup X} {z : X}
    (h : ZCentAt (T.map e.toMonoidHom) (B.map e.toMonoidHom) (e z)) : ZCentAt T B z := by
  intro hzT hz1 hzc hzB v hv hvc hv2 b hb
  have hO : pCoreOf 2 (B.map e.toMonoidHom) = (pCoreOf 2 B).map e.toMonoidHom :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e B
  apply e.injective
  rw [map_mul, map_mul]
  refine h ⟨z, hzT, rfl⟩ (fun h1 => hz1 (e.injective (by rw [h1, map_one]))) ?_ ?_ (e v)
    (by rw [hO]; exact ⟨v, hv, rfl⟩) ?_ (by rw [← map_mul, hv2, map_one]) (e b) ⟨b, hb, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    show e z * e t = e t * e z
    rw [← map_mul, ← map_mul, hzc t ht]
  · rintro _ ⟨c, hc, rfl⟩
    show e z * e c = e c * e z
    rw [← map_mul, ← map_mul, hzB c hc]
  · intro u' hu'
    rw [hO] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    show e u * e v = e v * e u
    rw [← map_mul, ← map_mul, hvc u hu]

theorem map_mem_lFamily_equiv (e : X ≃* Y) {T B : Subgroup X} (hB : B ∈ lFamily T) :
    B.map e.toMonoidHom ∈ lFamily (T.map e.toMonoidHom) := by
  have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
  rw [Subgroup.map_sup] at h1
  exact h1

theorem map_ne_top_equiv (e : X ≃* Y) {B : Subgroup X} (hB : B ≠ ⊤) :
    B.map e.toMonoidHom ≠ ⊤ := by
  intro htop
  apply hB
  have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) htop
  rwa [Vol2Native.A312L.map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1

variable [Finite X]

theorem ZCentFor.of_mulEquiv (e : X ≃* Y) (h : ZCentFor Y) : ZCentFor X :=
  fun _ hT _ hB hBtop _ => zcentAt_of_map e (h _
    (A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT) _ (map_mem_lFamily_equiv e hB)
    (map_ne_top_equiv e hBtop) _)

theorem ZCentFor.of_sylow (T₀ : Subgroup X) (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ B ∈ lFamily T₀, B ≠ ⊤ → ∀ z : X, ZCentAt T₀ B z) : ZCentFor X := by
  intro T hT B hB hBtop z
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hT₀ hT
  let e : X ≃* X := (MulAut.conj g).symm
  have hT' : T.map e.toMonoidHom = T₀ := by
    rw [← hg]
    exact Vol2Native.A312L.map_map_symm (MulAut.conj g) T₀
  refine zcentAt_of_map e ?_
  have hB' := map_mem_lFamily_equiv e hB
  rw [hT'] at hB' ⊢
  exact h _ hB' (map_ne_top_equiv e hBtop) _

theorem false_of_zcentFor (h : ZCentFor X) {T B : Subgroup X} (hc : ZCentConf X T B) : False := by
  obtain ⟨-, -, -, hT, hB, hBtop, -, -, ⟨z, hzT, hz1, hzc, hzB⟩, V, hVB, hV, hBV, hcomm, hV1,
    hcV, -⟩ := hc
  exact false_of_V hVB hV hBV hcomm hV1 hcV (h T hT B hB hBtop z hzT hz1 hzc hzB)

theorem ZCentFor.of_top (h : ZCentFor ↥(⊤ : Subgroup X)) : ZCentFor X :=
  ZCentFor.of_mulEquiv Subgroup.topEquiv.symm h

end Transport

theorem false_of_residual_bot {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hP : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt S U P)
    (hsolv : ∀ j, perfectCore (P j) = ⊥) {B : Subgroup S} (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) :
    False := by
  have hB' : B ∈ cComp (B ⊔ U) := hB
  have hne : B ⊔ U ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hns : ¬ Group.IsSolvable ↥(B ⊔ U) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ U))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 (B ⊔ U) le_sup_right hne hns
  apply hns
  rw [isSolvable_iff_perfectCore_eq_bot, ← Vol2Native.A312L.dInf_eq_perfectCore, hd,
    Vol2Native.A312L.dInf_eq_perfectCore]
  exact hsolv j

section Linear3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K]

theorem exists_smul_of_map_eq {S : Type} [Group S] (π : SpecialLinearGroup (Fin 3) K →* S)
    (hker : π.ker ≤ scalars 3 K) {u x : SpecialLinearGroup (Fin 3) K} (h : π (u * x) = π (x * u)) :
    ∃ c : K, (u : Matrix (Fin 3) (Fin 3) K) * x = c • ((x : Matrix (Fin 3) (Fin 3) K) * u) := by
  have hm : u * x * (x * u)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := hker hm
  refine ⟨c, ?_⟩
  have h2 : u * x = u * x * (x * u)⁻¹ * (x * u) := (inv_mul_cancel_right _ _).symm
  have h3 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
  rw [Matrix.SpecialLinearGroup.coe_mul u x,
    Matrix.SpecialLinearGroup.coe_mul (u * x * (x * u)⁻¹) (x * u), hc,
    Matrix.SpecialLinearGroup.coe_mul x u] at h3
  rw [h3, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem eq_one_of_comm_embMat {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (j : Fin 2) (h : ∀ A : SpecialLinearGroup (Fin 2) K, ∃ c : K,
      (u : Matrix (Fin 3) (Fin 3) K) * embMat j (A : Matrix (Fin 2) (Fin 2) K) =
        c • (embMat j (A : Matrix (Fin 2) (Fin 2) K) * u)) : u = 1 := by
  obtain ⟨hl, hd⟩ := hu
  obtain ⟨c₁, h₁⟩ := h ⟨!![1, 1; 0, 1], by simp⟩
  obtain ⟨c₂, h₂⟩ := h ⟨!![1, 0; 1, 1], by simp⟩
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h21 := hl 2 1 (by decide)
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have e₁ := fun i k => congrFun₂ h₁ i k
  have e₂ := fun i k => congrFun₂ h₂ i k
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] at e₁ e₂
  have hent : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    fin_cases j
    · have a1 := e₁ 0 0
      have a2 := e₁ 0 2
      have a3 := e₂ 0 0
      have a4 := e₂ 0 1
      have a5 := e₂ 1 1
      simp [embMat, h10, h20, h21, h00, h11, h22] at a1 a2 a3 a4 a5
      subst a1 a3
      exact ⟨by linear_combination a2, by linear_combination a4, by linear_combination a5⟩
    · have a1 := e₁ 2 2
      have a2 := e₁ 0 2
      have a3 := e₂ 2 2
      have a4 := e₂ 0 0
      have a5 := e₂ 1 2
      simp [embMat, h10, h20, h21, h00, h11, h22] at a1 a2 a3 a4 a5
      subst a1 a3
      exact ⟨by linear_combination a4, by linear_combination -a5, by linear_combination -a2⟩
  obtain ⟨h01, h02, h12⟩ := hent
  ext i k
  fin_cases i <;> fin_cases k <;> simp [h01, h02, h12, h10, h20, h21, h00, h11, h22]

variable [Finite K]

theorem eq_perfectCore_linear3 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {S : Type}
    [Group S] [Finite S] (hq : CFSG.IsQuasisimple S) (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K) {B : Subgroup S}
    (hB : B ∈ lFamily ((unitriangular 3 K).map π)) (hBtop : B ≠ ⊤) :
    (∃ s : Finset K, s.card = 4) ∧ ∃ j, B = perfectCore ((Q3 K j).map π) := by
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h4 : 4 ≤ Nat.card K
  · have hK4 := exists_finset_card_four h4
    refine ⟨hK4, rank2_eq_perfectCore hq hres (fun j => ?_) hB hBtop⟩
    let eN := perfectCoreMapEquiv π (Q3 K j) (hinj j)
    have := sl2_isSimple hK4
    refine ⟨SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance, sl2_nonabelian hK4,
      (blk3 j).comp eN.symm.toMonoidHom, (blk3_surjective hK4 j).comp eN.symm.surjective, ?_⟩
    have hP : IsPGroup 2 ((blk3 j).comp eN.symm.toMonoidHom).ker := by
      intro z
      obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      show z.1 ^ 2 ^ k = 1
      exact (map_eq_one_iff _ eN.symm.injective).mp (by rw [map_pow]; exact h1)
    have := hP.isNilpotent
    infer_instance
  · exfalso
    have hK2 : Nat.card K = 2 := by
      obtain ⟨k, hk⟩ := hK
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hk] at h1 h4 ⊢
      rcases k with _ | _ | k
      · simp at h1
      · rfl
      · exact absurd (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ k + 2))
          (by norm_num at h4 ⊢; omega)
    refine false_of_residual_bot hq hres (fun j => ?_) hB hBtop
    have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
      refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
      norm_num
    have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
      have := (blk3_ker_isPGroup hK j).isNilpotent
      infer_instance
    have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
      Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
        (by rw [Subgroup.range_subtype])
    have h1 := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
    rw [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at h1
    rw [← map_perfectCore, h1, Subgroup.map_bot]

theorem zcentFor_linear3 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {S : Type} [Group S]
    [Finite S] (hq : CFSG.IsQuasisimple S) (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) : ZCentFor S := by
  refine ZCentFor.of_sylow _ hSyl fun B hB hBtop z hzT hz1 _ hzB => ?_
  exfalso
  obtain ⟨hK4, j, rfl⟩ := eq_perfectCore_linear3 hK hq π hπ hker hB hBtop
  obtain ⟨u, hu, rfl⟩ := hzT
  refine hz1 ?_
  rw [eq_one_of_comm_embMat hu j fun A => ?_, map_one]
  have hx : π (embSL j A) ∈ perfectCore ((Q3 K j).map π) := by
    rw [← map_perfectCore]
    exact ⟨_, embSL_mem_perfectCore hK4 j A, rfl⟩
  have h1 := hzB _ hx
  rw [← map_mul, ← map_mul] at h1
  exact exists_smul_of_map_eq π hker h1

theorem zcentFor_of_isPSL3 {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ}
    (hf : 1 ≤ f) (h : IsPSL 3 2 f X) : ZCentFor X := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  exact ZCentFor.of_mulEquiv e' (zcentFor_linear3 ⟨f, hcard⟩
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq) (proj 3 K) (proj_surjective 3 K)
    (ker_proj 3 K).le hT₀)

theorem zcentFor_of_isSL3 {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ}
    (hf : 1 ≤ f) (h : IsSL3 (2 ^ f) X) : ZCentFor X := by
  obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hcard
  let e' : X ≃* SpecialLinearGroup (Fin 3) K :=
    φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine ZCentFor.of_mulEquiv e' (zcentFor_linear3 ⟨f, hcard⟩
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq) (MonoidHom.id _) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) ?_)
  rw [Subgroup.map_id]
  exact hT₀

end Linear3


end CFSG.Quasithin.Vol2.Ch10.A312A
