module

public import CFSG.Quasithin.EmptyFaithful.SzPS8PBasic
public import CFSG.Quasithin.EmptyFaithful.SzPS8Sylow
public import CFSG.Quasithin.EmptyFaithful.SzPS8E11
public import CFSG.Quasithin.EmptyFaithful.SzPS8Ovg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace SzPS8

section Generic

theorem exists_cComp_map_eq_of_le_range {Hg Γ : Type} [Group Hg] [Finite Hg] [Group Γ]
    (hspan : cCompSpan (⊤ : Subgroup Hg) = perfectCore (⊤ : Subgroup Hg))
    (ρ : Hg →* Γ) {K : Subgroup Γ} (hKr : K ≤ ρ.range) (hKn : (K.subgroupOf ρ.range).Normal)
    (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K) :
    ∃ L ∈ cComp (⊤ : Subgroup Hg), L.map ρ = K := by
  classical
  let e : ↥(K.subgroupOf ρ.range) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKr
  have hs : IsSimpleGroup ↥(K.subgroupOf ρ.range) := by
    have := hKs
    exact e.isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥(K.subgroupOf ρ.range) := fun hc =>
    hKnc ⟨⟨fun a b => e.symm.injective (hc.is_comm.comm (e.symm a) (e.symm b))⟩⟩
  obtain ⟨L, hL, hLρ⟩ := exists_cComp_map_eq hspan ρ.rangeRestrict ρ.rangeRestrict_surjective
    hKn hs hnc
  refine ⟨L, hL, ?_⟩
  have h1 := congrArg (Subgroup.map ρ.range.subtype) hLρ
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKr] at h1
  exact h1

end Generic

section Lift

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] noncomputable def imgΓ (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    (X : Subgroup G) : Subgroup ↥(D.img (mcOf T)) :=
  (X.subgroupOf (mcOf T)).map (rhoΓ h D)

theorem pCoreOf_ne_bot_of_le_cZU (h : Hyp1281Two G T M (yOfL22 T M)) {X : Subgroup G}
    (hX1 : centerOf (uOfL22 T M) ≤ X) (hX2 : X ≤ cZU T M) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 (centerOf (uOfL22 T M)) :=
    h.sylow.1.to_le ((inf_le_left : centerOf (uOfL22 T M) ≤ uOfL22 T M).trans h.uOfL22_le_T)
  have hle : centerOf (uOfL22 T M) ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 hX1
      (hX2.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) hZ2
  intro hbot
  exact h.omegaOneCenter_ne_bot (le_bot_iff.mp
    (hbot ▸ h.omegaOneCenter_le_centerOf_uOfL22.trans hle))

theorem exists_cZU_lift (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M))
    (h39 : A39ForSQTK) (D : HatModel T M) {X : Subgroup G}
    (hX1 : centerOf (uOfL22 T M) ≤ X) (hX2 : X ≤ cZU T M)
    {K : Subgroup ↥(D.img (mcOf T))} (hKr : K ≤ imgΓ h D X)
    (hKn : (K.subgroupOf (imgΓ h D X)).Normal) (hKs : IsSimpleGroup ↥K)
    (hKnc : ¬ IsMulCommutative ↥K) :
    ∃ L : Subgroup G, L ∈ cComp X ∧ (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K := by
  classical
  have hXH : X ≤ mcOf T := hX2.trans cZU_le
  have hH : pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_le_cZU h hX1 hX2
  have hspanX : cCompSpan X = perfectCore X :=
    lemma_1_2_1_one hyp.qtke hyp.simple hyp.nonabelian h39 hH
  have hspanTop : cCompSpan (⊤ : Subgroup ↥X) = perfectCore (⊤ : Subgroup ↥X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [← cCompSpan_eq_map_subtype, hspanX, map_perfectCore, Subgroup.map_top,
      Subgroup.range_subtype]
  let ρX : ↥X →* ↥(D.img (mcOf T)) := (rhoΓ h D).comp (Subgroup.inclusion hXH)
  have hrange : ρX.range = imgΓ h D X := by
    unfold imgΓ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨L', hL', hL'ρ⟩ := exists_cComp_map_eq_of_le_range hspanTop ρX
    (hrange ▸ hKr) (hrange ▸ hKn) hKs hKnc
  set L : Subgroup G := L'.map X.subtype with hLdef
  have hL : L ∈ cComp X := map_subtype_mem_cComp hL'
  refine ⟨L, hL, ?_⟩
  have e1 : L = (L'.map (Subgroup.inclusion hXH)).map (mcOf T).subtype := by
    rw [hLdef, Subgroup.map_map]
    rfl
  have e2 : L.subgroupOf (mcOf T) = L'.map (Subgroup.inclusion hXH) := by
    rw [e1]
    exact Subgroup.comap_map_eq_self_of_injective (mcOf T).subtype_injective _
  rw [e2, Subgroup.map_map]
  exact hL'ρ

theorem kbar_of_cZU_lift (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {X L : Subgroup G} (hX2 : X ≤ cZU T M) (hL : L ∈ cComp X)
    {K : Subgroup ↥(D.img (mcOf T))} (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K)
    (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K) :
    (∀ x : ↥(mcOf T), (x : G) ∈ L → rhoΓ h D x = 1 → (x : G) ∈ pCoreOf 2 L) ∧
      Nonempty (KBar L ≃* ↥K) := by
  classical
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLH : L ≤ mcOf T := hLX.trans (hX2.trans cZU_le)
  let χ : ↥L →* ↥K := rhoOn h D hLH hLρ
  have hχ : Function.Surjective χ := rhoOn_surjective h D hLH hLρ
  have hT2 : IsPGroup 2 ↥T := h.almostSpecialHyp_g1.sylow_H.2.1
  have hkerT : ∀ x : ↥L, χ x = 1 → (x : G) ∈ T := by
    intro x hx
    have hx1 : rhoΓ h D (Subgroup.inclusion hLH x) = 1 := congrArg Subtype.val hx
    exact cZU_ker_le_T h D (p := Subgroup.inclusion hLH x) (hX2 (hLX x.2))
      (congrArg Subtype.val hx1)
  have hker2 : IsPGroup 2 χ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hT2 ⟨((x : ↥L) : G), hkerT x.1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hkerle : χ.ker ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hker2⟩
  have hpc : CFSG.pCore 2 ↥L ≤ χ.ker := by
    set R : Subgroup ↥K := (CFSG.pCore 2 ↥L).map χ with hR
    have hRn : R.Normal := Subgroup.Normal.map CFSG.pCore_normal χ hχ
    have hR2 : IsPGroup 2 ↥R := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map χ
    rcases hKs.eq_bot_or_eq_top_of_normal R with h0 | h1
    · intro x hx
      have : χ x ∈ R := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hK2 : IsPGroup 2 ↥K := by
        rw [h1] at hR2
        exact hR2.of_equiv Subgroup.topEquiv
      have := hK2.isNilpotent
      have hs : Group.IsSolvable ↥K := inferInstance
      exact hKnc ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b⟩⟩
  have hkerEq : χ.ker = CFSG.pCore 2 ↥L := le_antisymm hkerle hpc
  have hsub : (pCoreOf 2 L).subgroupOf L = χ.ker := by
    rw [hkerEq]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  refine ⟨fun x hxL hx1 => ?_, ⟨?_⟩⟩
  · have hmem : (⟨(x : G), hxL⟩ : ↥L) ∈ χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hx1
    rw [← hsub] at hmem
    exact hmem
  · exact (QuotientGroup.quotientMulEquivOfEq hsub).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχ)

theorem normalizes_of_cZU_lift (hyp : Hyp1421 G T M) (h : Hyp1281Two G T M (yOfL22 T M))
    (h37 : A37ForSQTK) (D : HatModel T M) {X L : Subgroup G}
    (hX1 : centerOf (uOfL22 T M) ≤ X) (hX2 : X ≤ cZU T M)
    (hXn : ∀ x ∈ mcOf T, ∀ p ∈ X, x * p * x⁻¹ ∈ X) (hL : L ∈ cComp X)
    {K : Subgroup ↥(D.img (mcOf T))} (hKn : K.Normal)
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K)
    (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  classical
  intro t ht
  by_contra htn
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have htH : t ∈ mcOf T := hTH ht
  have hXH : X ≤ mcOf T := hX2.trans cZU_le
  have hHX : pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_le_cZU h hX1 hX2
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun p => ⟨fun hp => hXn t htH p hp, fun hp => by
      have := hXn t⁻¹ ((mcOf T).inv_mem htH) _ hp
      simpa [mul_assoc] using this⟩
  set L₂ : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hL₂def
  have hL₂ : L₂ ∈ cComp X := by
    have h1 := cComp_map_mulEquiv (MulAut.conj t) hL
    rwa [A38.map_conj_eq_iff.mpr htX] at h1
  have hne : L ≠ L₂ := fun hLL => htn (A38.map_conj_eq_iff.mp hLL.symm)
  have hc2 := lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hHX hL hL₂ hne
  have hcomm : ⁅L, L₂⁆ ≤ pCoreOf 2 X := hc2.1.trans hc2.2
  set ρ := rhoΓ h D with hρ
  set t' : ↥(mcOf T) := ⟨t, htH⟩ with ht'
  have hL₂ρ : ∀ k ∈ K, ∃ a : ↥(mcOf T), (a : G) ∈ L₂ ∧ ρ a = k := by
    intro k hk
    have hk' : (ρ t')⁻¹ * k * (ρ t') ∈ K := by
      have := hKn.conj_mem k hk (ρ t')⁻¹
      simpa [mul_assoc] using this
    rw [← hLρ] at hk'
    obtain ⟨l, hl, hlk⟩ := hk'
    refine ⟨t' * l * t'⁻¹, ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩, ?_⟩
    · simp [ht', MulAut.conj_apply]
    · rw [map_mul, map_mul, map_inv, hlk]
      group
  have hLρ' : ∀ k ∈ K, ∃ a : ↥(mcOf T), (a : G) ∈ L ∧ ρ a = k := by
    intro k hk
    rw [← hLρ] at hk
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, hak⟩
  set Q : Subgroup ↥(D.img (mcOf T)) := ((pCoreOf 2 X).subgroupOf (mcOf T)).map ρ with hQ
  have hQ2 : IsPGroup 2 ↥Q := by
    have h1 : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf (mcOf T)) :=
      (pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXH)).symm
    exact h1.map ρ
  have hKQ : K ≤ Q := by
    calc K = ⁅K, K⁆ := (commutator_self_of_simple hKs hKnc).symm
      _ ≤ Q := by
        refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
        obtain ⟨a₁, ha₁, rfl⟩ := hLρ' k₁ hk₁
        obtain ⟨a₂, ha₂, rfl⟩ := hL₂ρ k₂ hk₂
        have hmem : (⁅a₁, a₂⁆ : ↥(mcOf T)) ∈ (pCoreOf 2 X).subgroupOf (mcOf T) :=
          Subgroup.mem_subgroupOf.mpr (hcomm (Subgroup.commutator_mem_commutator ha₁ ha₂))
        exact ⟨_, hmem, map_commutatorElement ρ a₁ a₂⟩
  have hK2 : IsPGroup 2 ↥K := hQ2.to_le hKQ
  have := hK2.isNilpotent
  have hs : Group.IsSolvable ↥K := inferInstance
  exact hKnc ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b⟩⟩

end Lift

section Borel

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem borel_le_M_sl2_two (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (h35 : Lemma1435)
    (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) {L : Subgroup G}
    (hLH : L ≤ mcOf T) (hLc : L ∈ cComp (L ⊔ T)) (hTN : T ≤ Subgroup.normalizer (L : Set G))
    {K : Subgroup ↥(D.img (mcOf T))} (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = K)
    (e : ↥K ≃* SL(2, GaloisField 2 2))
    (hker : ∀ x : ↥(mcOf T), (x : G) ∈ L → rhoΓ h D x = 1 → (x : G) ∈ pCoreOf 2 L) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M := by
  classical
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hsylLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLc) hsylLT
  have hpc : pCoreOf 2 L ≤ T ⊓ L := pCoreOf_two_le_of_isSylowTwoOf hsylL
  set S : Subgroup G := T ⊓ L with hS
  set B : Subgroup G := L ⊓ Subgroup.normalizer (S : Set G) with hB
  have hSL : S ≤ L := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hBL : B ≤ L := inf_le_left
  let χ : ↥L →* ↥K := rhoOn h D hLH hLρ
  let ε : ↥L →* SL(2, GaloisField 2 2) := e.toMonoidHom.comp χ
  have hε : Function.Surjective ε := e.surjective.comp (rhoOn_surjective h D hLH hLρ)
  have hεker : ∀ x : ↥L, ε x = 1 → (x : G) ∈ S := by
    intro x hx
    have hχ : χ x = 1 := e.injective (by
      have : e (χ x) = 1 := hx
      rw [this, map_one])
    have hρ : rhoΓ h D (Subgroup.inclusion hLH x) = 1 := congrArg Subtype.val hχ
    exact hpc (hker (Subgroup.inclusion hLH x) x.2 hρ)
  have h3 : S.relIndex B = 2 ^ 2 - 1 :=
    relIndex_borel_of_surjective (n := 2) (by norm_num) hSL hsylL ε hε hεker
  have hTL : ∀ t ∈ T, ∀ x, x ∈ L ↔ t * x * t⁻¹ ∈ L := fun t ht =>
    Subgroup.mem_normalizer_iff.mp (hTN ht)
  have hTS : ∀ t ∈ T, ∀ x, x ∈ S ↔ t * x * t⁻¹ ∈ S := by
    intro t ht x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), (hTL t ht x).mp hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (hTL t ht x).mpr hxL⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
  have hTBfwd : ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B := by
    intro t ht x hx
    refine ⟨(hTL t ht x).mp hx.1, ?_⟩
    show t * x * t⁻¹ ∈ Subgroup.normalizer (S : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hxn := Subgroup.mem_normalizer_iff.mp hx.2
    have e1 : t * x * t⁻¹ * g * (t * x * t⁻¹)⁻¹ = t * (x * (t⁻¹ * g * t) * x⁻¹) * t⁻¹ := by group
    rw [e1, ← hTS t ht, ← hxn (t⁻¹ * g * t)]
    have := hTS t⁻¹ (T.inv_mem ht) g
    simpa using this
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hTBfwd t ht x hx, fun hx => by
      have := hTBfwd t⁻¹ (T.inv_mem ht) _ hx
      simpa [mul_assoc] using this⟩
  have hTB' : T ⊓ B = S := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans hBL)
    · exact le_inf hST (fun x hx => ⟨hSL hx, Subgroup.le_normalizer hx⟩)
  have hrel : T.relIndex (T ⊔ B) = 3 := by
    rw [relIndex_sup_of_le_normalizer hTB, ← Subgroup.inf_relIndex_right, hTB', h3]
    norm_num
  have hLTH : T ⊔ B ≤ mcOf T := sup_le hTH (hBL.trans hLH)
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hInH : InH T (T ⊔ B) := by
    refine ⟨le_sup_left, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (T ⊔ B) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsylH).trans le_sup_left)
        (hLTH.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    intro h0
    exact hH (le_bot_iff.mp (h0 ▸ h1))
  have hTBM : T ⊔ B ≤ M := h35 G T M hyp hnot _ hInH (Or.inl hrel)
  exact le_sup_right.trans hTBM

end Borel

section Single

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem false_of_normal_sl2_four (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G)
    (hnab : ¬ IsMulCommutative ↥(uOfL22 T M)) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h35 : Lemma1435) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN)
    (hF : FieldOne1432) (D : HatModel T M) {K : Subgroup ↥(D.img (mcOf T))} (hKn : K.Normal)
    (e : ↥K ≃* SL(2, GaloisField 2 2))
    (hKP : K ≤ imgΓ (hyp.hyp1281Two_of_inputs h11 h113) D (cZU T M)) : False := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hKs : IsSimpleGroup ↥K := by
    have : IsSimpleGroup SL(2, GaloisField 2 2) :=
      CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 le_rfl
    exact e.isSimpleGroup
  have hKnc : ¬ IsMulCommutative ↥K := not_isMulCommutative_of_sl2_gf (by norm_num) e
  have hZ : centerOf (uOfL22 T M) ≤ cZU T M := centerOf_uOfL22_le_cZU h1281
  obtain ⟨L, hL, hLρ⟩ := exists_cZU_lift hyp h1281 h39 D (X := cZU T M) hZ le_rfl hKP
    (hKn.subgroupOf _) hKs hKnc
  have hLX : L ≤ cZU T M := le_of_mem_cComp hL
  have hLH : L ≤ mcOf T := hLX.trans cZU_le
  have hTH : T ≤ mcOf T := h1281.almostSpecialHyp_g1.T_le_H
  have hLH' : L ∈ cComp (mcOf T) := cComp_mem_of_subnormal (cZU_isSubnormal h1281) hL
  have hLc : L ∈ cComp (L ⊔ T) := cComp_mem_of_le hLH' le_sup_left (sup_le hLH hTH)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) :=
    normalizes_of_cZU_lift hyp h1281 h37 D hZ le_rfl (cZU_normal h1281) hL hKn hLρ hKs hKnc
  obtain ⟨hker, ⟨eK⟩⟩ := kbar_of_cZU_lift h1281 D le_rfl hL hLρ hKs hKnc
  have hB := borel_le_M_sl2_two hyp hnot h35 h1281 D hLH hLc hTN hLρ e hker
  have hcard : Nat.card (KBar L) = ordL2 2 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr e.toEquiv, card_sl2_gf (by norm_num)]
    rfl
  have : IsSimpleGroup ↥K := hKs
  exact false_of_good_lift hyp hnot hnab h11 h113 hE22 hF D hKn hKnc (m := 2) le_rfl hLH hLc hTN
    hLρ eK.isSimpleGroup (fusionIsBenderGroup_of_sl2_gf le_rfl (eK.trans e)) hcard hB

end Single

end SzPS8

end CFSG.Quasithin
