module

public import CFSG.Quasithin.Vol2.Ch12Sec5K1List
public import CFSG.Quasithin.Vol2.Ch12Sec5L4
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125W Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239.L52

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Pm

@[expose] noncomputable def q234 : Subgroup SL5 :=
  flagStabilizer 5 (ZMod 2) (Set.Icc 1 (5 - 1) \ {1})

theorem stabK_eq (k : ℕ) : S125Tr.stabK k = flagStabilizer 5 (ZMod 2) {k} := by
  ext g
  rw [mem_flagStabilizer]
  constructor
  · intro hg i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact hg
  · intro hg
    exact hg k (Set.mem_singleton k)

theorem mem_q234 {g : SL5} : g ∈ q234 ↔ StabGam 2 g ∧ StabGam 3 g ∧ StabGam 4 g := by
  rw [q234, mem_flagStabilizer]
  constructor
  · intro hg
    refine ⟨S125Tr.mem_stabK.1 (hg 2 (BinaryParabolic.mem_cuts.2 ⟨by norm_num, by norm_num,
      by norm_num⟩)), S125Tr.mem_stabK.1 (hg 3 (BinaryParabolic.mem_cuts.2 ⟨by norm_num,
      by norm_num, by norm_num⟩)), S125Tr.mem_stabK.1 (hg 4 (BinaryParabolic.mem_cuts.2
      ⟨by norm_num, by norm_num, by norm_num⟩))⟩
  · rintro ⟨h2, h3, h4⟩ i hi
    obtain ⟨hi1, hi4, hne⟩ := BinaryParabolic.mem_cuts.1 hi
    have : i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact S125Tr.mem_stabK.2 h2
    · exact S125Tr.mem_stabK.2 h3
    · exact S125Tr.mem_stabK.2 h4

theorem relIndex_q234 : (unitriangular 5 (ZMod 2)).relIndex q234 = 3 :=
  BinaryParabolic.relIndex_parabolic (n := 5) (j := 1) le_rfl (by norm_num)

theorem pR_sup_le_stabK1 : S125Gen.pR 2 3 rfl ⊔ unitriangular 5 (ZMod 2) ≤ S125Tr.stabK 1 := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [S125Tr.mem_stabK]
    obtain ⟨h1, h2⟩ := (S125Gen.mem_pR_iff rfl g).1 hg
    intro i j hj hi
    by_cases hi2 : 2 ≤ i.val
    · exact h1 i j (by omega) hi2
    · rw [h2 i j (by omega) (by omega), Matrix.one_apply_ne]
      intro h
      rw [h] at hi
      omega
  · rw [S125Tr.mem_stabK]
    exact S125Tr2.stabGam_of_upperTri (fun i j hij => (mem_unitriangular.1 hg).1 i j hij) 1

theorem not_q234_le : ¬ q234 ≤ S125Gen.pR 2 3 rfl ⊔ unitriangular 5 (ZMod 2) := by
  intro h
  have hr := BinaryParabolic.reflection_mem_parabolic (n := 5) (j := 1) le_rfl (by norm_num)
  have h1 := S125Tr.mem_stabK.1 (pR_sup_le_stabK1 (h hr)) 1 0 (by decide) (by decide)
  revert h1
  decide

theorem stabK4_le : S125Tr.stabK 4 ≤ S125Gen.pL 4 1 rfl := by
  intro g hg
  have hg' : g ∈ flagStabilizer 5 (ZMod 2) {4} := (stabK_eq 4) ▸ hg
  have hb := blkAt_one_eq_one (Nat.card_zmod 2) (flagStabilizer 5 (ZMod 2) {4}) 4
    (by norm_num) (blockLeft_of_cut 1 (Or.inr rfl)) (blockRight_of_cut (Or.inl rfl)) ⟨g, hg'⟩
  rw [S125Gen.mem_pL_iff rfl]
  refine ⟨fun a b hb' ha => S125Tr.mem_stabK.1 hg a b hb' ha, fun a b ha hb' => ?_⟩
  have ha4 : a = 4 := Fin.ext (by omega)
  have hb4 : b = 4 := Fin.ext (by omega)
  subst ha4
  subst hb4
  have := congrFun₂ hb 0 0
  simpa [blkAt_apply] using this

@[expose] noncomputable def beta3 :
    ↥(flagStabilizer 5 (ZMod 2) {2}) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  blkSLTwo (Nat.card_zmod 2) (flagStabilizer 5 (ZMod 2) {2}) 2 3 (by norm_num)
    (blockLeft_of_cut 3 (Or.inr rfl)) (blockRight_of_cut (Or.inl rfl))

@[expose] noncomputable def kq : Subgroup SL5 :=
  beta3.ker.map (flagStabilizer 5 (ZMod 2) {2}).subtype

theorem beta3_apply (g : ↥(flagStabilizer 5 (ZMod 2) {2})) (i j : Fin 3) :
    ((beta3 g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j =
      (g.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) ⟨2 + i, by omega⟩ ⟨2 + j, by omega⟩ := by
  rw [beta3, blkSLTwo_coe, blkAt_apply]

theorem stabK2_le_normalizer_kq : S125Tr.stabK 2 ≤ Subgroup.normalizer (kq : Set SL5) := by
  intro q hq
  have hq' : q ∈ flagStabilizer 5 (ZMod 2) {2} := (stabK_eq 2) ▸ hq
  rw [Subgroup.mem_normalizer_iff]
  intro k
  set q' : ↥(flagStabilizer 5 (ZMod 2) {2}) := ⟨q, hq'⟩
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk1 : beta3 k' = 1 := hk'
    refine ⟨q' * k' * q'⁻¹, ?_, ?_⟩
    · show beta3 (q' * k' * q'⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hk1, mul_one, mul_inv_cancel]
    · simp [q']
  · rintro ⟨k', hk', hkk⟩
    have hk1 : beta3 k' = 1 := hk'
    refine ⟨q'⁻¹ * k' * q', ?_, ?_⟩
    · show beta3 (q'⁻¹ * k' * q') = 1
      rw [map_mul, map_mul, map_inv, hk1, mul_one, inv_mul_cancel]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, q'] at hkk ⊢
      rw [hkk]
      group

theorem kq_le_q234 : kq ≤ q234 := by
  rintro _ ⟨k, hk, rfl⟩
  have hk1 : beta3 k = 1 := hk
  have h2 : StabGam 2 k.1 := S125Tr.mem_stabK.1 ((stabK_eq 2).symm ▸ k.2)
  have hblk : ∀ i j : Fin 3, (k.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) ⟨2 + i, by omega⟩
      ⟨2 + j, by omega⟩ = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
    intro i j
    rw [← beta3_apply, hk1]
    rfl
  have hst : ∀ m : ℕ, 2 ≤ m → StabGam m k.1 := by
    intro m hm i j hj hi
    by_cases hj2 : j.val < 2
    · exact h2 i j hj2 (by omega)
    · have h := hblk ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
      have hi' : (⟨2 + (i.val - 2), by omega⟩ : Fin 5) = i := Fin.ext (by simp; omega)
      have hj' : (⟨2 + (j.val - 2), by omega⟩ : Fin 5) = j := Fin.ext (by simp; omega)
      rw [hi', hj', Matrix.one_apply_ne] at h
      · exact h
      · intro hij
        have := congrArg Fin.val hij
        simp at this
        omega
  exact mem_q234.2 ⟨h2, hst 3 (by norm_num), hst 4 (by norm_num)⟩

theorem isPGroup_unitriangular3 : IsPGroup 2 ↥(unitriangular 3 (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 3) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem isPGroup_unitriangular5 : IsPGroup 2 ↥(unitriangular 5 (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem mem_kq_of_odd {g : SL5} (hg : g ∈ q234) (ho : Odd (orderOf g)) : g ∈ kq := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h2, h3, h4⟩ := mem_q234.1 hg
  have hg2 : g ∈ flagStabilizer 5 (ZMod 2) {2} := (stabK_eq 2) ▸ S125Tr.mem_stabK.2 h2
  refine ⟨⟨g, hg2⟩, ?_, rfl⟩
  have hU : beta3 ⟨g, hg2⟩ ∈ unitriangular 3 (ZMod 2) := by
    rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
    intro i j hij
    rw [beta3_apply]
    have hi : i.val = 1 ∨ i.val = 2 := by omega
    rcases hi with hi | hi
    · exact h3 _ _ (by simp; omega) (by simp; omega)
    · exact h4 _ _ (by simp; omega) (by simp; omega)
  obtain ⟨k, hk⟩ := isPGroup_unitriangular3 ⟨_, hU⟩
  have hk' : beta3 ⟨g, hg2⟩ ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf (beta3 ⟨g, hg2⟩) ∣ orderOf (⟨g, hg2⟩ : ↥(flagStabilizer 5 (ZMod 2) {2})) :=
    orderOf_map_dvd _ _
  have ho' : Odd (orderOf (⟨g, hg2⟩ : ↥(flagStabilizer 5 (ZMod 2) {2}))) := by
    rwa [Subgroup.orderOf_mk]
  have h1 : orderOf (beta3 ⟨g, hg2⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3' : Odd (orderOf (beta3 ⟨g, hg2⟩)) := ho'.of_dvd_nat hdvd
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases i with _ | i
  · simpa using hie
  · exfalso
    rw [hie] at h3'
    exact (Nat.not_even_iff_odd.2 h3') (Nat.even_pow.2 ⟨even_two, by omega⟩)

theorem oTwoUpper_q234 : oTwoUpper q234 = oTwoUpper kq := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro g ⟨hg, ho⟩
    exact mem_oTwoUpper_of_odd (mem_kq_of_odd hg ho) ho
  · exact oTwoUpper_mono kq_le_q234

theorem stabK2_le_normalizer : S125Tr.stabK 2 ≤ Subgroup.normalizer (oTwoUpper q234 : Set SL5) := by
  rw [oTwoUpper_q234]
  exact stabK2_le_normalizer_kq.trans (normalizer_le_normalizer_oTwoUpper kq)

theorem pR_le_stab2 : S125Gen.pR 2 3 rfl ≤ flagStabilizer 5 (ZMod 2) {2} := by
  intro g hg
  rw [← stabK_eq, S125Tr.mem_stabK]
  exact fun i j hj hi => ((S125Gen.mem_pR_iff rfl g).1 hg).1 i j hj hi

@[expose] noncomputable def lift3 (D : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : SL5 :=
  CFSG.LieType.SteinbergBR.BlockPar.reindexSL (ZMod 2) (rfl : 2 + 3 = 5)
    (CFSG.LieType.SteinbergBR.BlockPar.levR (ZMod 2) (Fin 2) D)

theorem lift3_mem (D : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    lift3 D ∈ S125Gen.pR 2 3 rfl :=
  ⟨_, CFSG.LieType.SteinbergBR.BlockPar.levR_mem_parJR D, rfl⟩

theorem beta3_lift3 (D : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    beta3 ⟨lift3 D, pR_le_stab2 (lift3_mem D)⟩ = D := by
  ext i j
  rw [beta3_apply]
  change (CFSG.LieType.SteinbergBR.BlockPar.reindexSL (ZMod 2) (rfl : 2 + 3 = 5)
    (CFSG.LieType.SteinbergBR.BlockPar.levR (ZMod 2) (Fin 2) D)).val _ _ = _
  rw [S125Gen.reindex_apply5, S125Tr3.sumEquiv_symm_of_le rfl (by simp),
    S125Tr3.sumEquiv_symm_of_le rfl (by simp), CFSG.LieType.SteinbergBR.BlockPar.levR_val,
    Matrix.fromBlocks_apply₂₂]
  simp

theorem beta3_surjective : Function.Surjective beta3 := fun D => ⟨_, beta3_lift3 D⟩

theorem exists_mul_of_stab2 {g : SL5} (hg : g ∈ S125Tr.stabK 2) :
    ∃ a ∈ q234, ∃ b ∈ S125Gen.pR 2 3 rfl, g = a * b := by
  have hg2 : g ∈ flagStabilizer 5 (ZMod 2) {2} := (stabK_eq 2) ▸ hg
  set b := lift3 (beta3 ⟨g, hg2⟩) with hb
  have hb2 : b ∈ flagStabilizer 5 (ZMod 2) {2} := pR_le_stab2 (lift3_mem _)
  have hbeta : beta3 ⟨b, hb2⟩ = beta3 ⟨g, hg2⟩ := beta3_lift3 _
  have hk : (⟨g, hg2⟩ : ↥(flagStabilizer 5 (ZMod 2) {2})) * ⟨b, hb2⟩⁻¹ ∈ beta3.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbeta, mul_inv_cancel]
  refine ⟨g * b⁻¹, kq_le_q234 ⟨_, hk, rfl⟩, b, lift3_mem _, by group⟩

theorem mem_q234_iff_beta3 (g : ↥(flagStabilizer 5 (ZMod 2) {2})) :
    (g : SL5) ∈ q234 ↔ beta3 g ∈ unitriangular 3 (ZMod 2) := by
  have h2 : StabGam 2 (g : SL5) := S125Tr.mem_stabK.1 ((stabK_eq 2).symm ▸ g.2)
  rw [mem_q234, ← BinaryParabolic.upperTriangular_eq_unitriangular]
  constructor
  · rintro ⟨-, h3, h4⟩ i j hij
    rw [beta3_apply]
    have hi : i.val = 1 ∨ i.val = 2 := by omega
    rcases hi with hi | hi
    · exact h3 _ _ (by simp; omega) (by simp; omega)
    · exact h4 _ _ (by simp; omega) (by simp; omega)
  · intro hU
    have key : ∀ i j : Fin 5, 2 ≤ j.val → j.val < i.val →
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0 := by
      intro i j hj hij
      have h := hU ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩ (by
        show (⟨j.val - 2, _⟩ : Fin 3) < ⟨i.val - 2, _⟩
        exact Fin.mk_lt_mk.2 (by omega))
      rw [beta3_apply] at h
      have hi' : (⟨2 + (i.val - 2), by omega⟩ : Fin 5) = i := Fin.ext (by simp; omega)
      have hj' : (⟨2 + (j.val - 2), by omega⟩ : Fin 5) = j := Fin.ext (by simp; omega)
      rw [hi', hj'] at h
      exact h
    refine ⟨h2, fun i j hj hi => ?_, fun i j hj hi => ?_⟩
    · by_cases hj2 : j.val < 2
      · exact h2 i j hj2 (by omega)
      · exact key i j (by omega) (by omega)
    · by_cases hj2 : j.val < 2
      · exact h2 i j hj2 (by omega)
      · exact key i j (by omega) (by omega)

theorem relIndex_stab2 : (unitriangular 5 (ZMod 2)).relIndex (S125Tr.stabK 2) = 63 := by
  have hq : q234 ≤ S125Tr.stabK 2 := fun g hg => S125Tr.mem_stabK.2 (mem_q234.1 hg).1
  have hU : unitriangular 5 (ZMod 2) ≤ q234 := by
    rw [q234]; exact BinaryParabolic.unitriangular_le_flagStabilizer _
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hU hq, relIndex_q234]
  have h21 : q234.relIndex (S125Tr.stabK 2) = 21 := by
    rw [stabK_eq, Subgroup.relIndex]
    have hc : q234.subgroupOf (flagStabilizer 5 (ZMod 2) {2}) =
        (unitriangular 3 (ZMod 2)).comap beta3 := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact mem_q234_iff_beta3 g
    rw [hc, Subgroup.index_comap_of_surjective (unitriangular 3 (ZMod 2)) beta3_surjective]
    have hm := Subgroup.card_mul_index (unitriangular 3 (ZMod 2))
    rw [card_unitriangular, Nat.card_zmod, card_sl_three_zmod_two] at hm
    norm_num at hm
    omega
  rw [h21]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem act_mem (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (x : ↥(L ⊔ T)) :
    A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x ∈ autOn L V := by
  rw [← S125St.autOn_sup_eq F hLV hTV]
  exact (A4.mem_autOn_iff (sup_le hLV hTV)).2 ⟨x, rfl⟩

omit [Finite G] in
@[expose] noncomputable def phi (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : ↥(L ⊔ T) →* SL5 :=
  F.γ.toMonoidHom.comp ((A4.actionOn V (L ⊔ T) (sup_le hLV hTV)).codRestrict (autOn L V)
    (act_mem F hLV hTV))

section Phi

variable (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (hTV : T ≤ Subgroup.normalizer (V : Set G))

omit [Finite G] in
theorem psi_phi (x : ↥(L ⊔ T)) :
    psi F (phi F hLV hTV x) = A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x := by
  simp [psi, phi]

omit [Finite G] in
theorem phi_surjective : Function.Surjective (phi F hLV hTV) := by
  intro g
  obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).1 (F.γ.symm g).2
  refine ⟨⟨l, (le_sup_left : L ≤ L ⊔ T) l.2⟩, ?_⟩
  apply psi_injective F
  rw [psi_phi]
  change _ = ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V)
  rw [← hl]
  rfl

omit [Finite G] in
theorem phi_eq_one_iff (x : ↥(L ⊔ T)) :
    phi F hLV hTV x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← A4.actionOn_eq_one_iff (sup_le hLV hTV), ← psi_phi F hLV hTV, map_eq_one_iff _
    (psi_injective F)]

omit [Finite G] in
theorem phi_eq_iff (x y : ↥(L ⊔ T)) :
    phi F hLV hTV x = phi F hLV hTV y ↔
      ((x⁻¹ * y : ↥(L ⊔ T)) : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← phi_eq_one_iff F hLV hTV, map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem mem_normalizer_sub_iff (S : Finset (Fin 10)) (x : ↥(L ⊔ T)) :
    (x : G) ∈ Subgroup.normalizer (F.sub S : Set G) ↔
      CoordFix S (JonesParshall.wedgeMat (phi F hLV hTV x : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
  have h := S125St.mapsTo_sub_iff F S
    ⟨A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x, act_mem F hLV hTV x⟩
  have he : F.γ ⟨A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x, act_mem F hLV hTV x⟩ =
      phi F hLV hTV x := rfl
  rw [he] at h
  rw [← h]
  constructor
  · intro hx v hv
    have h1 := (Subgroup.mem_normalizer_iff.mp hx v).mp hv
    exact h1
  · intro hmap
    apply S125St.mem_normalizer_of_conj_le
    intro w hw
    have hwV : w ∈ V := S125St.sub_le F S hw
    exact hmap ⟨w, hwV⟩ hw

end Phi

section Facts

omit [Finite G] in
theorem phi_mem_U (F : Frame125 T L V) {hLV : L ≤ Subgroup.normalizer (V : Set G)}
    {hTV : T ≤ Subgroup.normalizer (V : Set G)} (x : ↥(L ⊔ T)) (hx : (x : G) ∈ T) :
    phi F hLV hTV x ∈ unitriangular 5 (ZMod 2) := by
  obtain ⟨u, hu, hact⟩ := F.borel (x : G) hx
  have h : A4.actionOn V (L ⊔ T) (sup_le hLV hTV) x =
      ((F.γ.symm u : ↥(autOn L V)) : MulAut ↥V) := by
    refine MulEquiv.ext fun v => F.e.injective ?_
    rw [F.wedge, MulEquiv.apply_symm_apply]
    exact hact v _ rfl
  have he : phi F hLV hTV x = u := by
    apply psi_injective F
    rw [psi_phi, h]
    rfl
  rw [he, ← BinaryParabolic.upperTriangular_eq_unitriangular]
  exact hu

theorem centralizer_le_T (h1222 : Stmt12_2_2) (hH : Hyp125 G T L V) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hC := S125Tr2.isPGroup_centralizer hH hf
  have hS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
  have hN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      CFSG.Quasithin.normalizer_le_normalizer_centralizer V (sup_le hf.normalizes hf.T_le hx)⟩
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN hC).trans
    (pCoreOf_two_le_of_isSylowTwoOf hS)

theorem mem_P_iff (F : Frame125 T L V) {hLV : L ≤ Subgroup.normalizer (V : Set G)}
    {hTV : T ≤ Subgroup.normalizer (V : Set G)} (x : ↥(L ⊔ T)) :
    (x : G) ∈ F.P ↔ phi F hLV hTV x ∈ q234 := by
  rw [mem_q234, ← coordFix_V1_iff, ← coordFix_V3_iff, ← coordFix_V6_iff,
    ← mem_normalizer_sub_iff F hLV hTV, ← mem_normalizer_sub_iff F hLV hTV,
    ← mem_normalizer_sub_iff F hLV hTV]
  show (x : G) ∈ ((L ⊔ T) ⊓ Subgroup.normalizer (F.sub {0} : Set G)) ⊓
      Subgroup.normalizer (F.sub {0, 1, 4} : Set G) ⊓
      Subgroup.normalizer (F.sub {0, 1, 2, 4, 5, 7} : Set G) ↔ _
  simp only [Subgroup.mem_inf]
  exact ⟨fun ⟨⟨⟨_, h1⟩, h3⟩, h6⟩ => ⟨h1, h3, h6⟩, fun ⟨h1, h3, h6⟩ => ⟨⟨⟨x.2, h1⟩, h3⟩, h6⟩⟩

theorem mem_mi_iff (F : Frame125 T L V) {hLV : L ≤ Subgroup.normalizer (V : Set G)}
    {hTV : T ≤ Subgroup.normalizer (V : Set G)} (x : ↥(L ⊔ T)) :
    (x : G) ∈ mi T L F.V1 ↔ phi F hLV hTV x ∈ S125Tr.stabK 2 := by
  rw [S125Tr.mem_stabK, ← coordFix_V1_iff, ← mem_normalizer_sub_iff F hLV hTV]
  show (x : G) ∈ (L ⊔ T) ⊓ Subgroup.normalizer (F.sub {0} : Set G) ↔ _
  rw [Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem mem_T_iff (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {hLV : L ≤ Subgroup.normalizer (V : Set G)} {hTV : T ≤ Subgroup.normalizer (V : Set G)}
    (x : ↥(L ⊔ T)) : (x : G) ∈ T ↔ phi F hLV hTV x ∈ unitriangular 5 (ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨phi_mem_U F x, fun hx => ?_⟩
  have hS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
  set H : Subgroup G := ((unitriangular 5 (ZMod 2)).comap (phi F hLV hTV)).map (L ⊔ T).subtype
    with hHdef
  have hTH : T ≤ H := fun t ht => ⟨⟨t, (le_sup_right : T ≤ L ⊔ T) ht⟩, phi_mem_U F _ ht, rfl⟩
  have hHLT : H ≤ L ⊔ T := Subgroup.map_subtype_le _
  have hC := S125Tr2.isPGroup_centralizer hH (S125Ex.Facts125.of h1222 hH)
  have hH2 : IsPGroup 2 ↥H := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    obtain ⟨a, ha⟩ := isPGroup_unitriangular5 ⟨_, hy⟩
    have h1 : phi F hLV hTV (y ^ 2 ^ a) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val ha
    have h2 : ((y ^ 2 ^ a : ↥(L ⊔ T)) : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨(y ^ 2 ^ a).2, (phi_eq_one_iff F hLV hTV _).1 h1⟩
    obtain ⟨b, hb⟩ := hC ⟨_, h2⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hb
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
    rw [pow_add, pow_mul]
    exact h3
  have hidx : T.relIndex H = 1 := by
    have hdvd : T.relIndex H ∣ T.relIndex (L ⊔ T) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex T H (L ⊔ T) hTH hHLT)
    have hodd : ¬ 2 ∣ T.relIndex H := fun h => hS.2.2 (h.trans hdvd)
    obtain ⟨c, hc⟩ := hH2.exists_card_eq
    have hd : T.relIndex H ∣ 2 ^ c := hc ▸ Subgroup.relIndex_dvd_card T H
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rcases i with _ | i
    · simpa using hie
    · exact absurd (hie ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)) hodd
  have hle : H ≤ T := Subgroup.relIndex_eq_one.mp hidx
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem P_le (F : Frame125 T L V) : F.P ≤ L ⊔ T := inf_le_left.trans (inf_le_left.trans inf_le_left)

theorem relIndex_P (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    T.relIndex F.P = 3 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hT' : T.subgroupOf (L ⊔ T) =
      (unitriangular 5 (ZMod 2)).comap (phi F hf.normalizes hf.T_le) := by
    ext x
    exact mem_T_iff h1222 F hH x
  have hP' : F.P.subgroupOf (L ⊔ T) = q234.comap (phi F hf.normalizes hf.T_le) := by
    ext x
    exact mem_P_iff F x
  rw [← Subgroup.relIndex_subgroupOf (P_le F), hT', hP', Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (phi_surjective F _ _)]
  exact relIndex_q234

theorem phi_li_iff (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {W : Subgroup G} {R : Subgroup SL5} (hW : autOn (li L W) V = R.map (psi F)) :
    let hf := S125Ex.Facts125.of h1222 hH
    (∀ x : ↥(L ⊔ T), (x : G) ∈ li L W → phi F hf.normalizes hf.T_le x ∈ R) ∧
      ∀ g ∈ R, ∃ x : ↥(L ⊔ T), (x : G) ∈ li L W ∧ phi F hf.normalizes hf.T_le x = g := by
  intro hf
  have hWV : li L W ≤ Subgroup.normalizer (V : Set G) := (S125K6.li_le L W).trans hf.normalizes
  refine ⟨fun x hx => ?_, fun g hg => ?_⟩
  · have h1 : A4.actionOn V (L ⊔ T) (sup_le hf.normalizes hf.T_le) x ∈ autOn (li L W) V :=
      (A4.mem_autOn_iff hWV).2 ⟨⟨x, hx⟩, rfl⟩
    rw [hW] at h1
    obtain ⟨g, hg, hgx⟩ := h1
    rw [← psi_phi F hf.normalizes hf.T_le] at hgx
    rwa [← psi_injective F hgx]
  · have h1 : psi F g ∈ autOn (li L W) V := hW ▸ ⟨g, hg, rfl⟩
    obtain ⟨⟨y, hyW⟩, hy⟩ := (A4.mem_autOn_iff hWV).1 h1
    refine ⟨⟨y, (le_sup_left : L ≤ L ⊔ T) (S125K6.li_le L W hyW)⟩, hyW, ?_⟩
    apply psi_injective F
    rw [psi_phi, ← hy]
    rfl

theorem P_not_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ¬ F.P ≤ li L F.V1 ⊔ T := by
  intro hle
  have hf := S125Ex.Facts125.of h1222 hH
  set Φ := phi F hf.normalizes hf.T_le with hΦ
  set W : Subgroup G := ((S125Gen.pR 2 3 rfl ⊔ unitriangular 5 (ZMod 2)).comap Φ).map
    (L ⊔ T).subtype with hWdef
  have hL₁W : li L F.V1 ≤ W := by
    intro l hl
    have hlLT : l ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) (S125K6.li_le L _ hl)
    refine ⟨⟨l, hlLT⟩, Subgroup.mem_sup_left
      ((phi_li_iff h1222 F hH (S125L8.autOn_l1 h1222 F hH)).1 ⟨l, hlLT⟩ hl), rfl⟩
  have hTW : T ≤ W := fun t ht =>
    ⟨⟨t, (le_sup_right : T ≤ L ⊔ T) ht⟩, Subgroup.mem_sup_right (phi_mem_U F _ ht), rfl⟩
  apply not_q234_le
  intro g hg
  obtain ⟨x, rfl⟩ := phi_surjective F hf.normalizes hf.T_le g
  have hxP : (x : G) ∈ F.P := (mem_P_iff F x).2 hg
  obtain ⟨y, hy, hyx⟩ := sup_le hL₁W hTW (hle hxP)
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem centralizer_le_normalizer_l6 (h1222 : Stmt12_2_2) (F : Frame125 T L V)
    (hH : Hyp125 G T L V) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (li L F.V6 : Set G) :=
  (centralizer_le_T h1222 hH).trans (S125K6.T_le_normalizer_l6 h1222 F hH)

theorem oTwoUpper_P_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    oTwoUpper F.P ≤ li L F.V6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  set C₀ := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hC₀
  have hC₀2 : IsPGroup 2 ↥C₀ := S125Tr2.isPGroup_centralizer hH hf
  have hPle : F.P ≤ li L F.V6 ⊔ C₀ := by
    intro x hx
    set x' : ↥(L ⊔ T) := ⟨x, P_le F hx⟩
    have hq := (mem_P_iff (hLV := hf.normalizes) (hTV := hf.T_le) F x').1 hx
    have h4 : phi F hf.normalizes hf.T_le x' ∈ S125Gen.pL 4 1 rfl :=
      stabK4_le (S125Tr.mem_stabK.2 (mem_q234.1 hq).2.2)
    obtain ⟨y, hy, hyx⟩ := (phi_li_iff h1222 F hH (S125L4.autOn_l6 h1222 F hH)).2 _ h4
    have hc := (phi_eq_iff F hf.normalizes hf.T_le y x').1 hyx
    have hx' : x = (y : G) * ((y⁻¹ * x' : ↥(L ⊔ T)) : G) := by simp [x']
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right ⟨(y⁻¹ * x').2, hc⟩)
  have hN : ((li L F.V6).subgroupOf (li L F.V6 ⊔ C₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer (centralizer_le_normalizer_l6 h1222 F hH))
  exact (oTwoUpper_mono hPle).trans
    (L1295.oTwoUpper_le_of_normal_sup le_sup_left hN hC₀2 le_sup_right le_rfl)

theorem mi_le_normalizer (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    mi T L F.V1 ≤ Subgroup.normalizer (oTwoUpper F.P : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  set Φ := phi F hf.normalizes hf.T_le with hΦ
  set Y : Subgroup G := ((oTwoUpper q234).comap Φ).map (L ⊔ T).subtype with hYdef
  have hYP : Y ≤ F.P := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_P_iff F y).2 (oTwoUpper_le q234 hy)
  have hPY : oTwoUpper F.P = oTwoUpper Y := by
    apply le_antisymm
    · rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, ho⟩
      set x' : ↥(L ⊔ T) := ⟨x, P_le F hx⟩
      have hq := (mem_P_iff (hLV := hf.normalizes) (hTV := hf.T_le) F x').1 hx
      have ho' : Odd (orderOf (Φ x')) := by
        refine ho.of_dvd_nat ((orderOf_map_dvd Φ x').trans ?_)
        rw [Subgroup.orderOf_mk]
      exact mem_oTwoUpper_of_odd ⟨x', mem_oTwoUpper_of_odd hq ho', rfl⟩ ho
    · exact oTwoUpper_mono hYP
  have hMY : mi T L F.V1 ≤ Subgroup.normalizer (Y : Set G) := by
    intro m hm
    have hmLT : m ∈ L ⊔ T := (inf_le_left : mi T L F.V1 ≤ L ⊔ T) hm
    have hm2 := (mem_mi_iff (hLV := hf.normalizes) (hTV := hf.T_le) F ⟨m, hmLT⟩).1 hm
    have hmN := stabK2_le_normalizer hm2
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    have hy : Φ y ∈ oTwoUpper q234 := Subgroup.mem_comap.1 hy
    have hz : Φ (⟨m, hmLT⟩ * y * ⟨m, hmLT⟩⁻¹) ∈ oTwoUpper q234 := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hmN _).mp hy
    have hz' : ⟨m, hmLT⟩ * y * ⟨m, hmLT⟩⁻¹ ∈ (oTwoUpper q234).comap Φ := hz
    have h1 := Subgroup.mem_map_of_mem (L ⊔ T).subtype hz'
    have h2 : (L ⊔ T).subtype (⟨m, hmLT⟩ * y * ⟨m, hmLT⟩⁻¹) = m * (L ⊔ T).subtype y * m⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype]
    rw [h2] at h1
    exact h1
  rw [hPY]
  exact hMY.trans (normalizer_le_normalizer_oTwoUpper Y)

omit [Finite G] in
theorem mi_le (F : Frame125 T L V) : mi T L F.V1 ≤ L ⊔ T := inf_le_left

theorem relIndex_mi (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    T.relIndex (mi T L F.V1) = 63 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hT' : T.subgroupOf (L ⊔ T) =
      (unitriangular 5 (ZMod 2)).comap (phi F hf.normalizes hf.T_le) := by
    ext x
    exact mem_T_iff h1222 F hH x
  have hM' : (mi T L F.V1).subgroupOf (L ⊔ T) =
      (S125Tr.stabK 2).comap (phi F hf.normalizes hf.T_le) := by
    ext x
    exact mem_mi_iff F x
  rw [← Subgroup.relIndex_subgroupOf (mi_le F), hT', hM', Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (phi_surjective F _ _)]
  exact relIndex_stab2

theorem mi_le_sup (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    mi T L F.V1 ≤ F.P ⊔ (li L F.V1 ⊔ T) := by
  have hf := S125Ex.Facts125.of h1222 hH
  set Φ := phi F hf.normalizes hf.T_le with hΦ
  intro x hx
  set x' : ↥(L ⊔ T) := ⟨x, mi_le F hx⟩
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_stab2 ((mem_mi_iff F x').1 hx)
  obtain ⟨p, rfl⟩ := phi_surjective F hf.normalizes hf.T_le a
  obtain ⟨l, hl, hlb⟩ := (phi_li_iff h1222 F hH (S125L8.autOn_l1 h1222 F hH)).2 b hb
  have hpP : (p : G) ∈ F.P := (mem_P_iff F p).2 ha
  have he : Φ (p * l) = Φ x' := by rw [map_mul, hlb, hab]
  have hc := (phi_eq_iff F hf.normalizes hf.T_le (p * l) x').1 he
  have hcT : (((p * l)⁻¹ * x' : ↥(L ⊔ T)) : G) ∈ T :=
    centralizer_le_T h1222 hH ⟨((p * l)⁻¹ * x').2, hc⟩
  have hx' : x = (p : G) * ((l : G) * (((p * l)⁻¹ * x' : ↥(L ⊔ T)) : G)) := by
    simp [x', mul_assoc]
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hcT)))

end Facts

end S125Pm

end CFSG.Quasithin.H13
