module

public import CFSG.Quasithin.H13.A6S1522
public import CFSG.Quasithin.H13.A5S1521Six

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def FactCommRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → A5.Rows1321Final G L A →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ∀ S X : Subgroup (MulAut V), IsSylowTwoOf S L → S ≤ Subgroup.centralizer {v} →
          X ≤ L → X ≤ Subgroup.centralizer {v} →
          S ≤ Subgroup.normalizer (X : Set (MulAut V)) → X ≤ oTwoRes X → X ≠ ⊥ →
            A5.commSubOf ⊤ X = ⊤

theorem comm_L1_eq_of_commSubOf {G : Type} [Group G] [Finite G]
    {T V V₁ V₃ L₁ H : Subgroup G} (S : A5Sit G T V V₁ V₃ L₁ H)
    (h : A5.commSubOf ⊤ ((imQ H L₁).map S.rhoA) = ⊤) :
    ⁅conjClosure V₃ H, L₁⁆ ⊔ V₁ = conjClosure V₃ H := by
  have hL1H : L₁ ≤ H := S.L1_le_H
  have hUN : ∀ l ∈ L₁, ∀ u ∈ conjClosure V₃ H, l * u * l⁻¹ ∈ conjClosure V₃ H := fun l hl u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V₃ H (hL1H hl)) u).mp hu
  apply le_antisymm
  · refine sup_le ?_ (S.V1_le_V3.trans (le_conjClosure V₃ H))
    rw [Subgroup.commutator_le]
    intro u hu l hl
    rw [commutatorElement_def]
    have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu (hUN l hl _ (Subgroup.inv_mem _ hu))
  ·
    set C : Subgroup ↥(conjClosure V₃ H) := (⁅conjClosure V₃ H, L₁⁆).subgroupOf (conjClosure V₃ H)
      with hC
    have hle : A5.commSubOf ⊤ ((imQ H L₁).map S.rhoA) ≤ C.map S.utMk := by
      rw [A5.commSubOf, Subgroup.closure_le]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, w, -, rfl⟩
      obtain ⟨l, hl, rfl⟩ := (mem_imQ hL1H).mp hy
      obtain ⟨u, rfl⟩ := S.utMk_surjective w
      have hmem : l * (u : G) * l⁻¹ ∈ conjClosure V₃ H := hUN l hl _ u.2
      rw [S.rhoA_mk ⟨l, hL1H hl⟩ u ⟨_, hmem⟩ rfl, ← map_inv, ← map_mul]
      refine ⟨⟨l * u * l⁻¹, hmem⟩ * u⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      have e : ((⟨l * u * l⁻¹, hmem⟩ * u⁻¹ : ↥(conjClosure V₃ H)) : G) = ⁅(u : G), l⁆⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 hl)
    intro u hu
    have hmem : S.utMk ⟨u, hu⟩ ∈ C.map S.utMk := hle (by rw [h]; exact Subgroup.mem_top _)
    obtain ⟨c, hc, hcu⟩ := hmem
    have h1 : S.utMk (c⁻¹ * ⟨u, hu⟩) = 1 := by rw [map_mul, map_inv, hcu, inv_mul_cancel]
    rw [S.utMk_eq_one_iff] at h1
    have hcC : (c : G) ∈ ⁅conjClosure V₃ H, L₁⁆ := Subgroup.mem_subgroupOf.mp hc
    have e : u = (c : G) * ((c⁻¹ * ⟨u, hu⟩ : ↥(conjClosure V₃ H)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hcC h1

theorem commSubOf_L1_eq_top_of_rows
    {G : Type} [Group G] [Finite G]
    {T V V₁ V₃ L₁ H : Subgroup G} (S : A5Sit G T V V₁ V₃ L₁ H)
    (hF956 : A5.StmtF956i) (h38 : A38ForSQTK) {Y : Subgroup G} (SY : A5SitY S Y)
    (h1519 : V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (Y : Set G)))
    (h3 : ∀ l ∈ L₁, l ^ 3 ∈ pCoreOf 2 L₁) (hF : A5.Facts1321) (hR : A5.FactRankRows1321)
    (hA7 : A5.FactA7Grp1321) (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321)
    (hC : FactCommRows1321) : A5.commSubOf ⊤ ((imQ H L₁).map S.rhoA) = ⊤ := by
  obtain ⟨v, hv, hvQ⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 H := Set.not_subset.mp S.not_V_le
  obtain ⟨K, hK, hKb⟩ := S.exists_component hF956 SY h1519 hv hvQ
  set P := S.toHyp1321 hF956 hv hvQ K hK hKb with hP
  set QL := S.toHypL1 hF956 h38 hv hvQ K hK hKb h3 with hQL
  obtain ⟨hZ, hLK, U1, U2, h1, h2, hU21, hfix, hcomm, hirr, hB4, hcond, hinj, hDU1, -, hrk, A,
    hA⟩ := A5.lemma_13_5_21_main P (S.toHypY hF956 h38 hv hvQ K hK hKb SY h1519) QL hF hR hA7 hL3
      hO
  obtain ⟨hU1, hU2⟩ := P.chief_eq_canonical hZ h1 hU21 hfix hcomm hirr hDU1
  have hLne : QL.L ≠ ⊥ := by
    obtain ⟨l, hl, d, -, hld⟩ := QL.Dnt
    intro h
    rw [h, Subgroup.mem_bot] at hl
    rw [hl, map_one, MulAut.one_apply] at hld
    exact hld rfl
  have hT := S.isSylowTwoOf_Tstar
  have hTL : A5.Tstar T H ≤ Subgroup.normalizer (QL.L : Set (A5.Hstar H)) :=
    S.Tstar_le_normalizer_L1
  have hKn := P.normal_K (h38 _ S.sqtkHyp_Hstar) hZ hT hLK hLne hTL
  have htop := P.commSubOf_eq_top hKn S.iSup_Vt3 (by rw [← hU1]; exact hDU1)
  have hU1t : U1 = ⊤ := hU1.trans htop
  subst hU1t
  subst hU2
  have hS0K : IsSylowTwoOf (A5.Tstar T H ⊓ K) K :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hK.2.1 hT
  have hS0L : A5.Tstar T H ⊓ K ≤ Subgroup.normalizer (QL.L : Set (A5.Hstar H)) :=
    fun _ hs => hTL hs.1
  refine A5.Hyp1321.commSubOf_L_eq_top P QL hS0K hS0L htop ?_
  set ψ := A5.secAct P.ρ _ h1 h2 with hψ
  set f : ↥P.K →* MulAut (A5.ChiefSec ⊤ (⊤ ⊓ fixV (P.K.map P.ρ))) :=
    ψ.comp (Subgroup.inclusion le_sup_left : ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b)) with hf
  set vb : ↥(P.K ⊔ Subgroup.zpowers P.b) :=
    ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ with hvb
  have hcent : ∀ k : ↥P.K, (k : A5.Hstar H) * P.b = P.b * k →
      f k ∈ Subgroup.centralizer {ψ vb} := by
    intro k hk
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hkb : (Subgroup.inclusion le_sup_left k : ↥(P.K ⊔ Subgroup.zpowers P.b)) * vb =
        vb * Subgroup.inclusion le_sup_left k := Subtype.ext hk
    rw [hf, MonoidHom.comp_apply, ← map_mul, hkb, map_mul]
  have hinL : ∀ k : ↥P.K, f k ∈ (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ := fun k =>
    ⟨Subgroup.inclusion le_sup_left k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hLtop : (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ =
      (⊤ : Subgroup ↥P.K).map f := by
    rw [hf, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.inclusion_range]
  set Sh : Subgroup (MulAut (A5.ChiefSec ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)))) :=
    ((A5.Tstar T H ⊓ K).subgroupOf P.K).map f with hSh
  set Xh : Subgroup (MulAut (A5.ChiefSec ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)))) :=
    (QL.L.subgroupOf P.K).map f with hXh
  have hShSyl : IsSylowTwoOf Sh ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨k, -, rfl⟩
      exact hinL k
    · exact IsPGroup.map (hS0K.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS0K.1).symm) f
    · have h := hS0K.2.2
      rw [← Subgroup.relIndex] at h ⊢
      rw [hLtop, hSh, Subgroup.relIndex_map_map_of_injective _ _ hinj,
        Subgroup.relIndex_top_right]
      rwa [Subgroup.relIndex] at h
  have hShC : Sh ≤ Subgroup.centralizer {ψ vb} := by
    rintro _ ⟨k, hk, rfl⟩
    exact hcent k (S.comm_Tstar hv hvQ (Subgroup.mem_subgroupOf.mp hk).1)
  have hXhL : Xh ≤ (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ := by
    rintro _ ⟨k, -, rfl⟩
    exact hinL k
  have hXhC : Xh ≤ Subgroup.centralizer {ψ vb} := by
    rintro _ ⟨k, hk, rfl⟩
    exact hcent k (QL.comm _ (Subgroup.mem_subgroupOf.mp hk))
  have hShN : Sh ≤ Subgroup.normalizer (Xh : Set _) := by
    refine A5.le_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨s * k * s⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hsN := hS0L (Subgroup.mem_subgroupOf.mp hs)
    have := (Subgroup.mem_normalizer_iff.mp hsN _).mp (Subgroup.mem_subgroupOf.mp hk)
    simpa using this
  have hXhres : Xh ≤ oTwoRes Xh := by
    have key : ∀ y ∈ oTwoRes QL.L, ∃ hy : y ∈ P.K, f ⟨y, hy⟩ ∈ oTwoRes Xh := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨hyL, m, hm, hym⟩ := hy
        refine ⟨hLK hyL, Subgroup.subset_closure ⟨⟨⟨y, hLK hyL⟩, ?_, rfl⟩, m, hm, ?_⟩⟩
        · exact Subgroup.mem_subgroupOf.mpr hyL
        · rw [← map_pow]
          have : (⟨y, hLK hyL⟩ : ↥P.K) ^ m = 1 := Subtype.ext (by simpa using hym)
          rw [this, map_one]
      | one =>
        refine ⟨P.K.one_mem, ?_⟩
        rw [show (⟨1, P.K.one_mem⟩ : ↥P.K) = 1 from rfl, map_one]
        exact (oTwoRes Xh).one_mem
      | mul a b _ _ iha ihb =>
        obtain ⟨ha, ha'⟩ := iha
        obtain ⟨hb, hb'⟩ := ihb
        refine ⟨P.K.mul_mem ha hb, ?_⟩
        have : (⟨a * b, P.K.mul_mem ha hb⟩ : ↥P.K) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, map_mul]
        exact (oTwoRes Xh).mul_mem ha' hb'
      | inv a _ iha =>
        obtain ⟨ha, ha'⟩ := iha
        refine ⟨P.K.inv_mem ha, ?_⟩
        have : (⟨a⁻¹, P.K.inv_mem ha⟩ : ↥P.K) = (⟨a, ha⟩)⁻¹ := rfl
        rw [this, map_inv]
        exact (oTwoRes Xh).inv_mem ha'
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨_, hk'⟩ := key k (QL.res (Subgroup.mem_subgroupOf.mp hk))
    exact hk'
  have hXhne : Xh ≠ ⊥ := by
    intro h
    apply hLne
    rw [eq_bot_iff]
    intro y hy
    have hmem : f ⟨y, hLK hy⟩ ∈ Xh := ⟨⟨y, hLK hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one f] at hmem
    have := hinj hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hX := hC _ (P.chiefSec_sq ⊤ (⊤ ⊓ fixV (P.K.map P.ρ))) _ _ A hB4 hA _ hcond hrk Sh Xh
    hShSyl hShC hXhL hXhC hShN hXhres hXhne
  set M := A5.commSubOf ⊤ (QL.L.map P.ρ) with hM
  have hle : A5.commSubOf ⊤ Xh ≤ (M.subgroupOf ⊤).map (A5.chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ))) := by
    rw [A5.commSubOf, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, z, -, rfl⟩
    obtain ⟨u, rfl⟩ := A5.chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) z
    have hku : P.ρ (k : A5.Hstar H) u ∈ (⊤ : Subgroup S.Ut) := Subgroup.mem_top _
    refine ⟨⟨P.ρ (k : A5.Hstar H) u * (u : S.Ut)⁻¹, Subgroup.mem_top _⟩,
      Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩, u, u.2, rfl⟩
    · rw [hf, MonoidHom.comp_apply, A5.secAct_chiefQ, ← map_inv, ← map_mul]
      rfl
  rw [eq_top_iff]
  intro w _
  have hw : A5.chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) ⟨w, Subgroup.mem_top w⟩ ∈
      (M.subgroupOf ⊤).map (A5.chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ))) :=
    hle (by rw [hX]; exact Subgroup.mem_top _)
  obtain ⟨m, hm, hmw⟩ := hw
  have h1' : A5.chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) (m⁻¹ * ⟨w, Subgroup.mem_top w⟩) = 1 := by
    rw [map_mul, map_inv, hmw, inv_mul_cancel]
  rw [A5.chiefQ_eq_one_iff] at h1'
  have e : w = (m : S.Ut) * ((m⁻¹ * ⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup S.Ut)) : S.Ut) := by
    simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hm) h1'.2

theorem input13521Six_of_comm
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h38 : A38ForSQTK)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (hC : FactCommRows1321) :
    Input13521Six := by
  intro G _ _ T L V S hNS _ hcon H hH hna
  have hVH : V ≤ H := (S.toA5Sit hNS h13315 h1356two hH hna).V_le_H
  refine comm_L1_eq_of_commSubOf (S.toA5Sit hNS h13315 h1356two hH hna) ?_
  by_cases hhat : IsHatA6 L
  · exact commSubOf_L1_eq_top_of_rows (S.toA5Sit hNS h13315 h1356two hH hna) VolI.stmtF956i h38
      (S.toA5SitY_L0 hNS h13315 h1356two hH hna hhat) (S.lemma13_5_19_two_l0 hhat hVH)
      (fun _ hl => S.cube_mem_pCoreOf_L1_hat hhat hl) hF hR hA7 hL3 hO hC
  · exact commSubOf_L1_eq_top_of_rows (S.toA5Sit hNS h13315 h1356two hH hna) VolI.stmtF956i h38
      (S.toA5SitY hNS h13315 h1356two hH hna hhat)
      (S.lemma13_5_19_two_L1 hNS h13315 h1356two (hcon hhat) hH)
      (fun _ hl => S.cube_mem_pCoreOf_L1 hhat hl) hF hR hA7 hL3 hO hC

end CFSG.Quasithin.H13.A6
