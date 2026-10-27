module

public import CFSG.Quasithin.Vol2.KGFact1297SL
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.KG1295

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.H13.KG1297

local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M₅" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem map_graphAut_flag {n : ℕ} (J : Set ℕ) :
    (flagStabilizer n (ZMod 2) J).map (BinaryParabolic.graphAut n).toMonoidHom =
      flagStabilizer n (ZMod 2) {i | 1 ≤ i ∧ i < n ∧ n - i ∈ J} := by
  set A := (flagStabilizer n (ZMod 2) J).map (BinaryParabolic.graphAut n).toMonoidHom with hA
  have hU : upperTriangular n (ZMod 2) ≤ A := by
    rw [BinaryParabolic.upperTriangular_eq_unitriangular,
      ← BinaryParabolic.map_graphAut_unitriangular]
    exact Subgroup.map_mono (unitriangular_le_flag J)
  have hmem : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      reflection n (ZMod 2) i hi hin ∈ A ↔ n - i ∉ J := by
    intro i hi hin
    rw [hA, Subgroup.mem_map_equiv]
    show BinaryParabolic.graphFun (reflection n (ZMod 2) i hi hin) ∈ _ ↔ _
    rw [BinaryParabolic.graphFun_reflection,
      (subflag_stabilizer_generation (K := ZMod 2) (n := n) J).2.2]
  obtain ⟨hA1, -⟩ := borel_overgroups A hU
  rw [hA1]
  congr 1
  ext i
  constructor
  · rintro ⟨hi, hin, hr⟩
    refine ⟨hi, hin, ?_⟩
    by_contra h
    exact hr ((hmem i hi hin).2 h)
  · rintro ⟨hi, hin, h⟩
    exact ⟨hi, hin, fun hr => (hmem i hi hin).1 hr h⟩

theorem map_graphAut_34 :
    (flagStabilizer 5 (ZMod 2) {3, 4}).map (BinaryParabolic.graphAut 5).toMonoidHom =
      flagStabilizer 5 (ZMod 2) {1, 2} := by
  rw [map_graphAut_flag]
  congr 1
  ext i
  constructor
  · rintro ⟨h1, h5, h⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    omega
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    refine ⟨by omega, by omega, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

theorem map_graphAut_12 :
    (flagStabilizer 5 (ZMod 2) {1, 2}).map (BinaryParabolic.graphAut 5).toMonoidHom =
      flagStabilizer 5 (ZMod 2) {3, 4} := by
  rw [← map_graphAut_34, KG1296.map_graphAut_map_graphAut]

abbrev Q3 : Subgroup SL₅ := flagStabilizer 5 (ZMod 2) {3}

@[expose] noncomputable def betaU : ↥Q3 →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  blkSLTwo (Nat.card_zmod 2) Q3 0 3 (by norm_num) (blockLeft_of_cut 3 (Or.inl rfl))
    (blockRight_of_cut (Or.inr rfl))

@[expose] noncomputable def betaL : ↥Q3 →* SpecialLinearGroup (Fin 2) (ZMod 2) :=
  blkSLTwo (Nat.card_zmod 2) Q3 3 2 (by norm_num) (blockLeft_of_cut 2 (Or.inr rfl))
    (blockRight_of_cut (Or.inl rfl))

@[expose] noncomputable def Kq : Subgroup SL₅ := betaU.ker.map Q3.subtype

@[expose] noncomputable def Wq : Subgroup SL₅ := betaL.ker.map Q3.subtype

theorem mem_Kq_iff {x : SL₅} : x ∈ Kq ↔ ∃ hx : x ∈ Q3, betaU ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨⟨y, hy3⟩, hy, rfl⟩
    exact ⟨hy3, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_Wq_iff {x : SL₅} : x ∈ Wq ↔ ∃ hx : x ∈ Q3, betaL ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨⟨y, hy3⟩, hy, rfl⟩
    exact ⟨hy3, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem le_normalizer_map_ker {M : Type*} [Group M] (f : ↥Q3 →* M) :
    Q3 ≤ Subgroup.normalizer ((f.ker.map Q3.subtype : Subgroup SL₅) : Set SL₅) := by
  refine KG1296.le_normalizer_of_forall fun g hg y hy => ?_
  obtain ⟨y', hy', rfl⟩ := hy
  refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * y' * (⟨g, hg⟩ : ↥Q3)⁻¹, ?_, by simp⟩
  rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.1 hy', mul_one, map_inv,
    mul_inv_cancel]

theorem le_normalizer_Kq : Q3 ≤ Subgroup.normalizer (Kq : Set SL₅) :=
  le_normalizer_map_ker betaU

theorem le_normalizer_Wq : Q3 ≤ Subgroup.normalizer (Wq : Set SL₅) :=
  le_normalizer_map_ker betaL

theorem exists_pow_mem_ker_of_upper {m : ℕ} (hm : 1 ≤ m) {H : Subgroup SL₅}
    (f : ↥H →* SpecialLinearGroup (Fin m) (ZMod 2)) {x : SL₅} (hx : x ∈ H)
    (h : ∀ i j : Fin m, j < i → (f ⟨x, hx⟩ : Matrix (Fin m) (Fin m) (ZMod 2)) i j = 0) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ f.ker.map H.subtype := by
  have hu : f ⟨x, hx⟩ ∈ unitriangular m (ZMod 2) := by
    rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
    exact h
  obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) hm ⟨_, hu⟩
  refine ⟨k, Subgroup.mem_map.2 ⟨⟨x, hx⟩ ^ 2 ^ k, ?_, by simp⟩⟩
  rw [MonoidHom.mem_ker, map_pow]
  exact congrArg Subtype.val hk

theorem exists_pow_mem_Wq {x : SL₅} (hx : x ∈ flagStabilizer 5 (ZMod 2) {3, 4}) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Wq := by
  have hx3 : x ∈ Q3 := flagStabilizer_anti (by simp) hx
  refine exists_pow_mem_ker_of_upper (by norm_num) betaL hx3 fun i j hij => ?_
  rw [betaL, blkSLTwo_coe, blkAt_apply]
  have hi := i.isLt
  have hij' := Fin.lt_def.1 hij
  exact stabilizer_entries (mem_flagStabilizer.1 hx 4 (by simp)) (by simp only; omega)
    (by simp only; omega)

theorem exists_pow_mem_Kq {x : SL₅} (hx : x ∈ flagStabilizer 5 (ZMod 2) {1, 2, 3}) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Kq := by
  have hx3 : x ∈ Q3 := flagStabilizer_anti (by simp) hx
  refine exists_pow_mem_ker_of_upper (by norm_num) betaU hx3 fun i j hij => ?_
  rw [betaU, blkSLTwo_coe, blkAt_apply]
  have hi := i.isLt
  have hij' := Fin.lt_def.1 hij
  have hc : 0 + (i : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  exact stabilizer_entries (mem_flagStabilizer.1 hx _ hc) (by simp only; omega)
    (by simp only; omega)

theorem Wq_le : Wq ≤ flagStabilizer 5 (ZMod 2) {3, 4} := by
  intro x hxW
  obtain ⟨hx3, hx⟩ := mem_Wq_iff.1 hxW
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod 2) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0) hx
  simp only [betaL, blkSLTwo_coe, blkAt_apply] at h1
  have hS3 := mem_flagStabilizer.1 hx3 3 rfl
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact stabilizer_entries hS3 hl hk
  · by_cases hl3 : (l : ℕ) < 3
    · exact stabilizer_entries hS3 hl3 (by omega)
    · have hk4 : k = 4 := Fin.ext (by have := k.isLt; simp; omega)
      have hl3' : l = 3 := Fin.ext (by simp; omega)
      rw [hk4, hl3']
      exact h1

theorem Wq_inf_Kq_le : Wq ⊓ Kq ≤ unitriangular 5 (ZMod 2) := by
  rintro x ⟨hxW, hxK⟩
  obtain ⟨hx3, hL⟩ := mem_Wq_iff.1 hxW
  obtain ⟨hx3', hU⟩ := mem_Kq_iff.1 hxK
  refine mem_unitriangular_of_blocks hx3 fun a m h ha hb hno => ?_
  have hno3 := hno 3 rfl
  simp only [Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl
  · obtain rfl : m = 3 := by omega
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) (ZMod 2) =>
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) hU
    rw [betaU, blkSLTwo_coe] at this
    exact this
  · rcases hb with hb | hb
    · obtain rfl : m = 2 := by omega
      have := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod 2) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) hL
      rw [betaL, blkSLTwo_coe] at this
      exact this
    · obtain rfl : m = 0 := by omega
      exact blkAt_zero 3 h _

@[expose] def ParOut {M : Type*} [Group M] (T B P : Subgroup M) : Prop :=
  T ≤ P ∧ (∀ Y : Subgroup M, T ≤ Y → Y ≤ P → Y = T ∨ Y = P) ∧ (∃ y ∈ P, orderOf y = 3) ∧
    P ≤ Subgroup.normalizer (B : Set M) ∧ ⁅B, oTwoUpper P⁆ ≤ pCoreOf 2 B

theorem map_symm_map {M M' : Type*} [Group M] [Group M'] (ι : M ≃* M') (Y : Subgroup M') :
    (Y.map ι.symm.toMonoidHom).map ι.toMonoidHom = Y := by
  ext x
  simp

theorem ParOut.map {M M' : Type*} [Group M] [Group M'] [Finite M] (ι : M ≃* M')
    {T B P : Subgroup M} (h : ParOut T B P) :
    ParOut (T.map ι.toMonoidHom) (B.map ι.toMonoidHom) (P.map ι.toMonoidHom) := by
  obtain ⟨hTP, hmax, ⟨y, hyP, hy⟩, hN, hc⟩ := h
  have hinj : Function.Injective (ι.toMonoidHom : M → M') := ι.injective
  refine ⟨Subgroup.map_mono hTP, fun Y hTY hYP => ?_, ⟨ι y, ⟨y, hyP, rfl⟩, ?_⟩,
    KG1296.map_le_normalizer_map ι hN, ?_⟩
  · have hY := map_symm_map ι Y
    have h1 : T ≤ Y.map ι.symm.toMonoidHom := by
      rw [← Subgroup.map_le_map_iff_of_injective hinj, hY]
      exact hTY
    have h2 : Y.map ι.symm.toMonoidHom ≤ P := by
      rw [← Subgroup.map_le_map_iff_of_injective hinj, hY]
      exact hYP
    rcases hmax _ h1 h2 with h | h
    · left
      rw [← hY, h]
    · right
      rw [← hY, h]
  · rw [MulEquiv.orderOf_eq]
    exact hy
  · rw [oTwoUpper_map, ← Subgroup.map_commutator, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hc

theorem oTwoUpper_idem {M : Type*} [Group M] (X : Subgroup M) :
    oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).2 fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

theorem flag_eq_unitriangular {J : Set ℕ} (hJ : ∀ i, 1 ≤ i → i < 5 → i ∈ J) :
    flagStabilizer 5 (ZMod 2) J = unitriangular 5 (ZMod 2) := by
  refine le_antisymm (fun x hx => ?_) (unitriangular_le_flag J)
  rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
  intro k l hlk
  have hlk' := Fin.lt_def.1 hlk
  have hl := k.isLt
  exact stabilizer_entries (mem_flagStabilizer.1 hx ((l : ℕ) + 1) (hJ _ (by omega) (by omega)))
    (by omega) (by omega)

theorem parOut_34 : ParOut (unitriangular 5 (ZMod 2))
    (oTwoUpper (flagStabilizer 5 (ZMod 2) {3, 4})) (flagStabilizer 5 (ZMod 2) {1, 2, 3}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := oTwoUpper (flagStabilizer 5 (ZMod 2) {3, 4}) with hBdef
  set P := flagStabilizer 5 (ZMod 2) {1, 2, 3} with hPdef
  have hBW : B ≤ Wq := oTwoUpper_le_of_pow_mem fun x hx => exists_pow_mem_Wq hx
  have hBeq : B = oTwoUpper Wq :=
    le_antisymm ((oTwoUpper_idem _).symm.le.trans (oTwoUpper_mono hBW)) (oTwoUpper_mono Wq_le)
  have hQ3B : Q3 ≤ Subgroup.normalizer (B : Set SL₅) := by
    rw [hBeq]
    exact le_normalizer_Wq.trans (normalizer_le_normalizer_oTwoUpper Wq)
  have hPQ3 : P ≤ Q3 := flagStabilizer_anti (by simp)
  have hBQ3 : B ≤ Q3 := hBW.trans (Subgroup.map_subtype_le _)
  have hPK : oTwoUpper P ≤ Kq := oTwoUpper_le_of_pow_mem fun x hx => exists_pow_mem_Kq hx
  refine ⟨unitriangular_le_flag _, fun Y hUY hYP => ?_, ⟨omg (4 : Fin 5) 3 (by decide),
    omg_mem (by decide) (by simp), ?_⟩, hPQ3.trans hQ3B, ?_⟩
  ·
    obtain ⟨J', hJ', rfl⟩ := exists_eq_flagStabilizer hUY
    have hsub := subset_of_flagStabilizer_le (I := {1, 2, 3}) (fun i hi => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega) hYP
    by_cases h4 : 4 ∈ J'
    · left
      refine flag_eq_unitriangular fun i hi1 hi5 => ?_
      interval_cases i
      · exact hsub (by simp)
      · exact hsub (by simp)
      · exact hsub (by simp)
      · exact h4
    · right
      congr 1
      ext i
      refine ⟨fun hi => ?_, fun hi => hsub hi⟩
      obtain ⟨hi1, hi5⟩ := hJ' i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have : i ≠ 4 := fun h => h4 (h ▸ hi)
      omega
  · exact orderOf_eq_prime (by decide) (by decide)
  ·
    refine Subgroup.commutator_le.2 fun b hb y hy => ?_
    have hyP := oTwoUpper_le P hy
    have hyQ := hPQ3 hyP
    have hbQ := hBQ3 hb
    set N := B ⊓ (Wq ⊓ Kq) with hN
    have hNB : N ≤ B := inf_le_left
    have hN2 : IsPGroup 2 N :=
      (isPGroup_unitriangular_charTwo (K := ZMod 2) (n := 5) (by norm_num)).to_le
        (inf_le_right.trans Wq_inf_Kq_le)
    have hNn : B ≤ Subgroup.normalizer (N : Set SL₅) := by
      refine KG1296.le_normalizer_of_forall fun a ha z hz => ?_
      have haQ := hBQ3 ha
      exact ⟨(Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ha) z).1 hz.1,
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_Wq haQ) z).1 hz.2.1,
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_Kq haQ) z).1 hz.2.2⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNB hNn hN2 ?_
    rw [commutatorElement_def]
    refine ⟨?_, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hQ3B hyQ) b⁻¹).1 (B.inv_mem hb)
      rw [mul_assoc, mul_assoc, ← mul_assoc y]
      exact B.mul_mem hb this
    · have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_Wq hyQ) b⁻¹).1
        (Wq.inv_mem (hBW hb))
      rw [mul_assoc, mul_assoc, ← mul_assoc y]
      exact Wq.mul_mem (hBW hb) this
    · have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_Kq hbQ) y).1 (hPK hy)
      exact Kq.mul_mem this (Kq.inv_mem (hPK hy))

theorem parOut_12 : ParOut (unitriangular 5 (ZMod 2))
    (oTwoUpper (flagStabilizer 5 (ZMod 2) {1, 2}))
    ((flagStabilizer 5 (ZMod 2) {1, 2, 3}).map (BinaryParabolic.graphAut 5).toMonoidHom) := by
  have h := parOut_34.map (BinaryParabolic.graphAut 5)
  rwa [BinaryParabolic.map_graphAut_unitriangular, ← oTwoUpper_map, map_graphAut_34] at h

end CFSG.Quasithin.H13.KG1295
