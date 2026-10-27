module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdIso
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutSkelKb
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutSkelInv
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocPerf
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenterT
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFus
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqCard

public section

namespace CFSG.Quasithin.H13.F431.D4q.OutAsm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.ComponentClassification.RankTwoExceptional.D4
open scoped commutatorElement
open CFSG.Quasithin.H13.F431.D4q.Out (exists_field_involution fieldActor_mem_Kb sylow_T T_le_N
  S_le_T_Kb S_norm exists_cyc_Kb f_mem f_not f_sq sylow_Tf tf_lt W_le mem_W
  normalizer_eq_of_isCoatom card_subgroupOf)

set_option linter.unusedSectionVars false


section Fields

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
  (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) (Kb : Subgroup (MulAut (Cm σ)))
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

theorem conjK_mem_T {S2 : Subgroup (K ≃+* K)} {x : Cm σ} (hx : x ∈ Ust σ) :
    conjK σ Kb hinn x ∈ (Tsub σ S2).subgroupOf Kb :=
  Subgroup.mem_subgroupOf.2 ((mem_Tsub_iff σ S2 _).2
    ⟨x, hx, 1, S2.one_mem, by rw [fieldActor_one, mul_one]; rfl⟩)

theorem conjK_mem_S {x : Cm σ} (hx : x ∈ Ust σ) :
    conjK σ Kb hinn x ∈ (Tsub σ ⊥).subgroupOf Kb :=
  conjK_mem_T σ Kb hinn hx

theorem orderOf_zK : orderOf (zK σ Kb hinn) = 2 := by
  rw [zK, orderOf_injective (conjK σ Kb hinn) (conjK_injective σ Kb hinn), orderOf_zC σ]

theorem VrC_le_Ust : VrC σ ≤ Ust σ := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (graphFixedSimpleComplement_le _ (Subgroup.mem_subgroupOf.1 hx))

theorem invSet_le {i : ↥Kb} (hi : i ∈ invSet σ Kb hinn) :
    i ∈ (Tsub σ ⊥).subgroupOf Kb ∧ orderOf i = 2 := by
  obtain ⟨y, hy, hy2, hy1, rfl⟩ := (mem_invSet σ Kb hinn).1 hi
  refine ⟨conjK_mem_S σ Kb hinn (VrC_le_Ust σ hy), ?_⟩
  rw [orderOf_injective (conjK σ Kb hinn) (conjK_injective σ Kb hinn)]
  exact orderOf_eq_prime (by rw [← sq] at hy2; exact hy2) hy1

end Fields

section NF

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (hσ3 : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def ZgC : Subgroup (Cm σ) :=
  (d4Zz K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

include hσ3 in
theorem ZgC_le_VrC [CharP K 2] : ZgC σ ≤ VrC σ := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (NFq.Zg_le_Qg σ hσ3 (Subgroup.mem_subgroupOf.1 hx))

include hσ3 in
theorem commutator_VrC_le [CharP K 2] {x y : Cm σ} (hx : x ∈ VrC σ) (hy : y ∈ VrC σ) :
    ⁅x, y⁆ ∈ ZgC σ := by
  have h := NFq.commutator_mem_Zg σ hσ3 (Subgroup.mem_subgroupOf.1 hx)
    (Subgroup.mem_subgroupOf.1 hy)
  exact Subgroup.mem_subgroupOf.2 (by simpa [commutatorElement_def] using h)

include hσ3 in
theorem ZgC_central [CharP K 2] {z x : Cm σ} (hz : z ∈ ZgC σ) (hx : x ∈ VrC σ) :
    z * x = x * z :=
  Subtype.ext (NFq.Zg_central_Qg σ hσ3 (Subgroup.mem_subgroupOf.1 hx)
    (Subgroup.mem_subgroupOf.1 hz)).symm

theorem d4Vr_le_root : d4Vr K σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  (graphFixedSimpleComplement_le _).trans (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)

include hf hK hσq hσ3 in
theorem card_VrC [CharP K 2] : Nat.card (VrC σ) = (2 ^ f) ^ 9 := by
  rw [VrC, card_subgroupOf (d4Vr_le_root σ)]
  exact NFq.card_Qg σ hf hK hσq

include hf hK hσq hσ3 in
theorem card_ZgC [CharP K 2] : Nat.card (ZgC σ) = 2 ^ f := by
  rw [ZgC, card_subgroupOf ((NFq.Zg_le_Qg σ hσ3).trans (d4Vr_le_root σ))]
  exact NFq.card_Zg σ hf hK hσq

end NF

section Main

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

theorem normalizer_eq_of_conj_mem {P : Subgroup (Cm σ)}
    (hP : ∀ g : Cm σ, MulAut.conj g ∈ autStab P → g ∈ P) :
    Subgroup.normalizer (P : Set (Cm σ)) = P := by
  refine le_antisymm (fun g hg => hP g fun x => ?_) Subgroup.le_normalizer
  have := Subgroup.mem_normalizer_iff.1 hg x
  rw [MulAut.conj_apply]
  exact this

include hf hK hσq in
theorem f431TwoOut_d4q (Kb : Subgroup (MulAut (Cm σ)))
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
    (hev : ¬ Odd (Nat.card Kb / Nat.card (Cm σ))) :
    ∃ (T S : Subgroup ↥Kb) (g z : ↥Kb) (I : Finset ↥Kb),
      F431TwoOut T S g (MbSt σ Kb (Pst0 σ)) (MbSt σ Kb (Pst1 σ)) z I := by
  have : CharP K 2 := Struct.charP_two_of_card hK
  have hσ3 : ∀ c, σ (σ (σ c)) = c := Struct.sigma_cube σ hK hσq
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun δ : K ≃+* K => (δ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq
  obtain ⟨S2, hS2⟩ := exists_isSylowTwoOf (Kb.map (theta σ hf hK hσq))
  obtain ⟨e, hfe, δ, hδS2, hδ1, hδ2, hδc⟩ := exists_field_involution σ hf hK hσq hinn hev hS2
  have hg := fieldActor_mem_Kb σ hf hK hσq hinn hS2 hδS2
  have hP0 : Subgroup.normalizer ((Pst0 σ : Subgroup (Cm σ)) : Set (Cm σ)) = Pst0 σ :=
    normalizer_eq_of_conj_mem σ fun g hg => mem_Pst0_of_conj_mem_autStab σ hf hK hσq hg
  have hQU : VrC σ ≤ Ust σ := VrC_le_Ust σ
  have hZQ : ZgC σ ≤ VrC σ := ZgC_le_VrC σ hσ3
  have hcQ := card_VrC σ hf hK hσq hσ3
  have hcZ := card_ZgC σ hf hK hσq hσ3
  have hQZ : (2 ^ f) ^ 8 * Nat.card (ZgC σ) ≤ Nat.card (VrC σ) := by
    rw [hcQ, hcZ]
    exact le_of_eq (by ring)
  have hTf : ∀ i ∈ invSet σ Kb hinn,
      Nat.card (spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩) <
        Nat.card ↥((Tsub σ S2).subgroupOf Kb ⊓ Subgroup.centralizer ({i} : Set ↥Kb)) := by
    intro i hi
    obtain ⟨y, hy, -, -, rfl⟩ := (mem_invSet σ Kb hinn).1 hi
    exact Out.tf_lt σ hf hK hσq hinn hS2 hfe hδc hg (VrC σ) (ZgC σ) hQU hZQ
      (fun _ hx _ hy' => commutator_VrC_le σ hσ3 hx hy') (fun _ hz _ hx => ZgC_central σ hσ3 hz hx)
      hQZ hy _ rfl
  refine ⟨(Tsub σ S2).subgroupOf Kb, (Tsub σ ⊥).subgroupOf Kb, ⟨fieldActor σ δ, hg⟩,
    zK σ Kb hinn, invSet σ Kb hinn, ?_⟩
  refine
  { sylow := Out.sylow_T σ hf hK hσq hinn hS2 hS.sylow
    T_le := Out.T_le_N σ hf hK hσq hinn hS2 (Pst0 σ) (Ust_le_Pst0 σ)
      (fun δ' => fieldActor_mem_autStab_Pst0 σ hf hK hσq δ')
    T_le' := Out.T_le_N σ hf hK hσq hinn hS2 (Pst1 σ) (Ust_le_Pst1 σ)
      (fun δ' => fieldActor_mem_autStab_Pst1 σ hf hK hσq δ')
    S_le := Out.S_le_T_Kb σ
    S_norm := Out.S_norm σ
    cyc := Out.exists_cyc_Kb σ hf hK hσq hinn hS2 (n := 3 * f) (by omega)
      (by rw [hK, ← pow_mul, mul_comm])
    z_mem := conjK_mem_T σ Kb hinn (zC_mem_Ust σ hσ3)
    z_two := orderOf_zK σ Kb hinn
    z_ZN := zK_mem_centerOf_perfectCore σ hσ3 hf hK hσq Kb hinn
    center_T := fun w hw hc hne => center_T_K σ hσ3 hf hK hσq Kb hinn hw hc hne
    I_le := fun i hi => invSet_le σ Kb hinn hi
    fusion := fun x hx hx2 => fusion_Kb σ hσ3 Kb hinn hx hx2
    f_mem := Out.f_mem σ hδS2 hg
    f_not := Out.f_not σ hf hK hσq hδ1 hg
    f_sq := Out.f_sq σ hδ2 hg
    Tf_lt := hTf
    Sylow_Tf := Out.sylow_Tf σ hf hK hσq hinn hS2 hfe hδc hg (Pst0 σ) (Ust_le_Pst0 σ) hP0
      (fun δ' => fieldActor_mem_autStab_Pst0 σ hf hK hσq δ')
    Z_sq := fun x hx => sq_of_mem_centerOf_MbSt σ hσ3 hf hK hσq Kb hinn hx
    Z_S := centerOf_S_le σ hσ3 hf hK hσq Kb hinn
    W_le := Out.W_le σ hf hK hσq hinn hS2 hfe hδc hg
    W_ne := ⟨zK σ Kb hinn, ?_, zK_mem_centerOf_perfectCore σ hσ3 hf hK hσq Kb hinn, ?_⟩ }
  · exact Out.mem_W σ hf hK hσq hinn hS2 hfe hδc hg (zC σ) (coe_zC σ) (hinn ⟨zC σ, rfl⟩)
  · exact fun h => zC_ne_one σ (conjK_injective σ Kb hinn (h.trans (map_one _).symm))

end Main

section Concl

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσq in
theorem twoOutConcl_d4q [CharP K 2] {A : LieAmalgamExt (Cm σ)} (hA : IsNormalized σ A)
    (hev : ¬ Odd (Nat.card ↥A.K / Nat.card (Cm σ))) : TwoOutConcl A := by
  have hinn := IsNormalized.inn_le_K σ hf hK hσq hA
  obtain ⟨T, S, g, z, I, h⟩ := f431TwoOut_d4q σ hf hK hσq A.K hinn hev
  refine ⟨T, S, g, z, I, ?_⟩
  have hMb1 : ∀ P : Subgroup (Cm σ), A.P1 = P → A.Mb1 = MbSt σ A.K P := fun P hP => by
    rw [LieAmalgamExt.Mb1_eq_std, hP]
    rfl
  have hMb2 : ∀ P : Subgroup (Cm σ), A.P2 = P → A.Mb2 = MbSt σ A.K P := fun P hP => by
    rw [LieAmalgamExt.Mb2_eq_std, hP]
    rfl
  rcases hA.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by rw [hMb1 _ h1, hMb2 _ h2]; exact h)
  · exact Or.inr (by rw [hMb1 _ h1, hMb2 _ h2]; exact h)

end Concl

theorem twoOutNorm_d4q (f : ℕ) (hf : 1 ≤ f) : TwoOutNorm f := by
  intro K _ _ σ hK hσ A hA hev
  have : CharP K 2 := Struct.charP_two_of_card hK
  exact twoOutConcl_d4q σ hf hK hσ hA hev

end CFSG.Quasithin.H13.F431.D4q.OutAsm
