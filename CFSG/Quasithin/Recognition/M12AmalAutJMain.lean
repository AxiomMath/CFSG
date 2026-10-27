module

public import CFSG.Quasithin.Recognition.M12AmalAutJFacts
public import CFSG.Quasithin.Recognition.M12AmalAutFeit
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv CFSG.Quasithin.AmalTransport CFSG.Open CFSG.QuasithinUnique

theorem aut_pCoreOf_le_T {H : Subgroup AutG} (hH : autData.T ≤ H) :
    CFSG.Open.pCoreOf 2 H ≤ autData.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 AutG := aut_syl.1.toSylow aut_syl.2
  have hP : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnorm : autData.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set AutG) :=
    hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hsup : IsPGroup 2 (CFSG.Open.pCoreOf 2 H ⊔ autData.T : Subgroup AutG) :=
    hP.to_sup_of_normal_left' aut_syl.1 hnorm
  have h1 : CFSG.Open.pCoreOf 2 H ⊔ autData.T = (S : Subgroup AutG) :=
    S.is_maximal' hsup le_sup_right
  have h2 : (S : Subgroup AutG) = autData.T := rfl
  rw [h2] at h1
  exact le_sup_left.trans h1.le

theorem aut_conj_mem_pCoreOf {H : Subgroup AutG} {g : AutG} (hg : g ∈ H) {p : AutG}
    (hp : p ∈ CFSG.Open.pCoreOf 2 H) :
    g * p * g⁻¹ ∈ CFSG.Open.pCoreOf 2 H ∧ g⁻¹ * p * g ∈ CFSG.Open.pCoreOf 2 H := by
  refine ⟨(Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) p).1 hp, ?_⟩
  have h2 := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hg)) p).1 hp
  simpa using h2

theorem aut_core_tel {H : Subgroup AutG} (hH : autData.T ≤ H) {q : AutG}
    (hq : q ∈ CFSG.Open.pCoreOf 2 H) : ∃ i : Fin 128, telG i = q :=
  (autData.mem_T_iff q).1 (aut_pCoreOf_le_T hH hq)

theorem LBq_of_mem_core {i : Fin 128} (hq : telG i ∈ CFSG.Open.pCoreOf 2 autData.B) : LBq i := by
  obtain ⟨h1, h2⟩ := aut_conj_mem_pCoreOf autData.y_mem_B hq
  obtain ⟨j₁, hj₁⟩ := aut_core_tel autData.T_le_B h1
  obtain ⟨j₂, hj₂⟩ := aut_core_tel autData.T_le_B h2
  have hj₁' : telG j₁ = genG 4 * telG i * (genG 4)⁻¹ := hj₁
  have hj₂' : telG j₂ = (genG 4)⁻¹ * telG i * genG 4 := hj₂
  have r1 : ReprG (compL (compL (gl 4) (tl i)) (gil 4)) (genG 4 * telG i * (genG 4)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen 4 (by norm_num)) (reprG_tel i i.2))
      (reprG_inv_gen 4 (by norm_num))
  have r2 : ReprG (compL (compL (gil 4) (tl i)) (gl 4)) ((genG 4)⁻¹ * telG i * genG 4) :=
    reprG_mul (reprG_mul (reprG_inv_gen 4 (by norm_num)) (reprG_tel i i.2))
      (reprG_gen 4 (by norm_num))
  rw [← hj₁'] at r1
  rw [← hj₂'] at r2
  refine ⟨?_, ?_⟩
  · rw [repL_unique r1 (reprG_tel j₁ j₁.2)]
    exact tl_mem_chk j₁ j₁.2
  · rw [repL_unique r2 (reprG_tel j₂ j₂.2)]
    exact tl_mem_chk j₂ j₂.2

theorem aut_B_core_central {p : AutG} (hp : p ∈ CFSG.Open.pCoreOf 2 autData.B) :
    telG 111 * p = p * telG 111 ∧ telG 36 * p = p * telG 36 := by
  obtain ⟨i, rfl⟩ := aut_core_tel autData.T_le_B hp
  obtain ⟨h111, h36⟩ := B_central_chk i i.2 (LBq_of_mem_core hp)
  refine ⟨?_, ?_⟩
  · refine eq_of_reprG (reprG_mul (reprG_tel 111 (by norm_num)) (reprG_tel i i.2)) ?_
    show ReprG (compL (tl 111) (tl i)) (telG i * telG 111)
    rw [h111]
    exact reprG_mul (reprG_tel i i.2) (reprG_tel 111 (by norm_num))
  · refine eq_of_reprG (reprG_mul (reprG_tel 36 (by norm_num)) (reprG_tel i i.2)) ?_
    show ReprG (compL (tl 36) (tl i)) (telG i * telG 36)
    rw [h36]
    exact reprG_mul (reprG_tel i i.2) (reprG_tel 36 (by norm_num))

theorem aut_PB_le_T : autExtra.PB ≤ autData.T := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact autData.Tel_mem_T (111 : Fin 128)
  · exact autData.Tel_mem_T (36 : Fin 128)
  · exact autData.Tel_mem_T (106 : Fin 128)

theorem aut_PB_le_core : autExtra.PB ≤ CFSG.Open.pCoreOf 2 autData.B :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (aut_PB_le_T.trans autData.T_le_B)
    autExtra.PB_norm autExtra.PB_p

theorem telG_mem_PB (i : ℕ) (hi : i ∈ [111, 36, 106]) : telG i ∈ autExtra.PB := by
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp

theorem aut_card_center_B_ne_two :
    Nat.card ↥(centerOf (CFSG.Open.pCoreOf 2 autData.B)) ≠ 2 := by
  intro h2
  have hT0 : telG 111 ∈ CFSG.Open.pCoreOf 2 autData.B := aut_PB_le_core (telG_mem_PB 111 (by simp))
  have hT1 : telG 36 ∈ CFSG.Open.pCoreOf 2 autData.B := aut_PB_le_core (telG_mem_PB 36 (by simp))
  have hc0 : telG 111 ∈ centerOf (CFSG.Open.pCoreOf 2 autData.B) :=
    Subgroup.mem_inf.2 ⟨hT0, Subgroup.mem_centralizer_iff.2 fun p hp =>
      (aut_B_core_central hp).1.symm⟩
  have hc1 : telG 36 ∈ centerOf (CFSG.Open.pCoreOf 2 autData.B) :=
    Subgroup.mem_inf.2 ⟨hT1, Subgroup.mem_centralizer_iff.2 fun p hp =>
      (aut_B_core_central hp).2.symm⟩
  obtain ⟨hne, hn1, hn2⟩ := tl_ne_chk
  have h0 : telG 111 ≠ 1 := ne_of_reprG (reprG_tel 111 (by norm_num)) reprG_one hn1
  have h1 : telG 36 ≠ 1 := ne_of_reprG (reprG_tel 36 (by norm_num)) reprG_one hn2
  have h01 : telG 111 ≠ telG 36 :=
    ne_of_reprG (reprG_tel 111 (by norm_num)) (reprG_tel 36 (by norm_num)) hne
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(centerOf (CFSG.Open.pCoreOf 2 autData.B)))).1 h2
  have hu0 : (⟨telG 111, hc0⟩ : ↥(centerOf (CFSG.Open.pCoreOf 2 autData.B))) ≠ 1 := by
    intro h
    apply h0
    have := congrArg Subtype.val h
    exact this
  have hu1 : (⟨telG 36, hc1⟩ : ↥(centerOf (CFSG.Open.pCoreOf 2 autData.B))) ≠ 1 := by
    intro h
    apply h1
    have := congrArg Subtype.val h
    exact this
  have e0 := huniq _ hu0
  have e1 := huniq _ hu1
  have key := congrArg Subtype.val (e0.trans e1.symm)
  exact h01 key

noncomputable def autPCoreCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    ↥(CFSG.Open.pCore 2 X) ≃* ↥(CFSG.Open.pCore 2 Y) :=
  ((CFSG.Open.pCore 2 X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e))

noncomputable def autPCoreOfEquiv {D : Type*} [Group D] (H : Subgroup D) :
    ↥(CFSG.Open.pCore 2 ↥H) ≃* ↥(CFSG.Open.pCoreOf 2 H) :=
  (CFSG.Open.pCore 2 ↥H).equivMapOfInjective H.subtype H.subtype_injective

noncomputable def autPCoreOfCongr {D E : Type*} [Group D] [Group E] {H : Subgroup D}
    {K : Subgroup E} (e : ↥H ≃* ↥K) : ↥(CFSG.Open.pCoreOf 2 H) ≃* ↥(CFSG.Open.pCoreOf 2 K) :=
  ((autPCoreOfEquiv H).symm.trans (autPCoreCongr e)).trans (autPCoreOfEquiv K)

theorem autCardCenterOfEq {D E : Type*} [Group D] [Group E] {R : Subgroup D} {R' : Subgroup E}
    (e : ↥R ≃* ↥R') : Nat.card ↥(centerOf R) = Nat.card ↥(centerOf R') := by
  rw [card_centerOf_eq_card_center, card_centerOf_eq_card_center, ← Subgroup.map_center_eq e]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ e.injective).toEquiv

theorem aut_map_map_symm_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (M : Subgroup G) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

open scoped Pointwise in
theorem aut_pair_cases {T' M₁ M₂ : Subgroup AutG} (h : IsYAmalgamPair T' M₁ M₂) :
    ∃ φ : AutG ≃* AutG, (M₁.map φ.toMonoidHom = autData.A ∧ M₂.map φ.toMonoidHom = autData.B) ∨
      (M₁.map φ.toMonoidHom = autData.B ∧ M₂.map φ.toMonoidHom = autData.A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsyl, hne, hiff⟩ := h
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hN₂⟩ := (hiff M₂).2 (Or.inr rfl)
  obtain ⟨-, hp', hidx'⟩ := hsyl
  have e1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
  have hidx : ¬ 2 ∣ T'.index := by rwa [e1] at hidx'
  let S : Sylow 2 AutG := aut_syl.1.toSylow aut_syl.2
  let S' : Sylow 2 AutG := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq AutG S S'
  have hk' : MulAut.conj k • autData.T = T' := by
    have h1 := congrArg (fun P : Sylow 2 AutG => (P : Subgroup AutG)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hT'map : T' = autData.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : AutG ≃* AutG := (MulAut.conj k).symm
  have hT'φ : T'.map φ.toMonoidHom = autData.T := by
    rw [hT'map]
    exact aut_map_map_symm_eq (MulAut.conj k) autData.T
  have hTle : ∀ M : Subgroup AutG, IsMaximalTwoLocal M → Subgroup.normalizer (T' : Set AutG) ≤ M →
      autData.T ≤ M.map φ.toMonoidHom := by
    intro M _ hN
    rw [← hT'φ]
    exact Subgroup.map_mono (Subgroup.le_normalizer.trans hN)
  have hA₁ := autExtra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₁) (hTle M₁ hM₁ hN₁)
  have hA₂ := autExtra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hM₂) (hTle M₂ hM₂ hN₂)
  refine ⟨φ, ?_⟩
  rcases hA₁ with h₁ | h₁ <;> rcases hA₂ with h₂ | h₂
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (Subgroup.map_injective φ.injective (h₁.trans h₂.symm)) hne

end CFSG.Quasithin.M12AmalAut

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.Quasithin.AmalTransport

theorem autM12AmalgamFacts_unfolded
    :
    ∀ (G : Type) [Group G] [Finite G] (P₁ P₂ : Subgroup G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂)
        (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) →
      IsL2Quot 1 (oTwoQuot ↥P₁) → IsAutM12Vertex P₁ → IsL2Quot 1 (oTwoQuot ↥P₂) →
      Nat.card (pCoreOf 2 P₂) = 2 ^ 6 →
      ∃ R : Subgroup G, R ≤ P₁ ⊓ P₂ ∧ R.relIndex (P₁ ⊓ P₂) = 2 ∧
        IsElemAbelian 2 (thompsonJ (P₁ ⊓ P₂)) ∧
        P₂ ≤ Subgroup.normalizer (thompsonJ (P₁ ⊓ P₂) : Set G) ∧
        (∃ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R) ∧
        (∀ j ∈ thompsonJ (P₁ ⊓ P₂), j ∉ R → ∀ y ∈ P₂, y * j * y⁻¹ ∉ R) ∧
        ∀ r ∈ R, r ^ 2 = 1 → ∃ j ∈ thompsonJ (P₁ ⊓ P₂) ⊓ R, AmalFusion P₁ P₂ r j := by
  intro G _ _ P₁ P₂ hAm _ hV _ _
  obtain ⟨Y, _, ⟨eY⟩, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hAm
  obtain ⟨m⟩ := autM12PermModel
  let f : Y ≃* AutG := eY.trans m.symm
  have hpair' := IsYAmalgamPair.map f hpair
  obtain ⟨φ, hφ⟩ := aut_pair_cases hpair'
  have iso' := isoMap (isoMap iso f) φ
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · have h : AutConcl ((M₁.map f.toMonoidHom).map φ.toMonoidHom)
        ((M₂.map f.toMonoidHom).map φ.toMonoidHom) := by
      rw [hA, hB]
      exact autConcl_model
    exact AutConcl.of_iso iso' h
  · exfalso
    have e₁ : ↥P₁ ≃* ↥autData.B :=
      iso'.φ1.trans (MulEquiv.subgroupCongr hB)
    have hcard := autCardCenterOfEq (autPCoreOfCongr e₁)
    exact aut_card_center_B_ne_two (hcard.symm.trans hV.2.2)

end CFSG.Quasithin
