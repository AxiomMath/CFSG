module

public import CFSG.Quasithin.MS93.S38EInst
public import CFSG.Quasithin.MS93.S38EndStmt

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem ofA_mem_centralizer_imM_iff (hTM : T ≤ M) {F : Subgroup G} (hFM : F ≤ M) (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ Subgroup.centralizer (imM hTM F : Set (puAmalgam hTM).Universal) ↔
      (m : G) ∈ Subgroup.centralizer (F : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hm f hf
    have := hm ((puAmalgam hTM).ofA ⟨f, hFM hf⟩) ⟨⟨f, hFM hf⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val ((puAmalgam hTM).ofA_injective this)
  · rintro hm _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hm f (Subgroup.mem_subgroupOf.mp hf))

theorem finite_imM' (hTM : T ≤ M) (K : Subgroup G) : Finite ↥(imM hTM K) :=
  Finite.of_surjective (fun x : ↥(K.subgroupOf M) =>
    (⟨_, Subgroup.mem_map_of_mem (puAmalgam hTM).ofA x.2⟩ : ↥(imM hTM K)))
    (by rintro ⟨_, ⟨m, hm, rfl⟩⟩; exact ⟨⟨m, hm⟩, rfl⟩)

theorem offCentAt_base (h : PUHyp M T L) (hC : XOffCentU M T L) :
    OffCentAt (puAmalgam h.le) (baseA _) (baseB _) := by
  intro F' hF' y hy hyF hyZ
  have hF'T : F' ≤ imM h.le T := by
    have := hF'.1
    rwa [puAmalgam.qv_baseB] at this
  obtain ⟨F, hFT, rfl⟩ := exists_imM_eq_of_le h.le hF'T
  have hF : IsXOff M T F := (h.isOffAt_base_iff hFT).mp hF'
  have hFM : F ≤ M := hFT.trans h.le
  rw [puAmalgam.qv_baseB] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have key : (t : G) ∈ F ⊔ pCoreOf 2 M := by
    refine hC F hF t htT ((ofA_mem_centralizer_imM_iff h.le hFM t).mp hyF) fun u hu => ?_
    have huM : u ∈ M := Uq_le h.L_le hu
    have hu' : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ ZM (puAmalgam h.le) (baseA _) := by
      rw [puAmalgam.zm_baseA h.le]
      exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr (Uq_le_Z0q h.L_le hu), rfl⟩
    have h1 := hyZ _ hu'
    rw [← map_commutatorElement] at h1
    have h2 := (ofA_mem_centralizer_imM_iff h.le hFM _).mp h1
    have e : ((⁅(⟨u, huM⟩ : ↥M), t⁆ : ↥M) : G) = ⁅u, (t : G)⁆ := by
      simp [commutatorElement_def]
    rwa [e] at h2
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    ← imM_sup h.le hFM (pCoreOf_le' M)]
  exact ⟨t, Subgroup.mem_subgroupOf.mpr key, rfl⟩

theorem puTrans_baseA_perfect (h : PUHyp M T L) :
    ⁅puTrans h.le L (baseA _), puTrans h.le L (baseA _)⁆ = puTrans h.le L (baseA _) := by
  rw [puTrans_baseA h.le h.L_subgroupOf_normal, ← imM_commutator h.le h.L_le h.L_le, h.perfect]

theorem stab_baseA_eq (h : PUHyp M T L) :
    stab (puAmalgam h.le) (baseA _) = puTrans h.le L (baseA _) ⊔ Qv _ (baseB _) := by
  rw [puAmalgam.stab_baseA h.le, puTrans_baseA h.le h.L_subgroupOf_normal, puAmalgam.qv_baseB,
    ← imM_sup h.le h.L_le h.le, ← h.eq_sup]

theorem endSetup_base (h : PUHyp M T L) (hD : XOffData M T) (hCU : XOffCentU M T L)
    (hb : critDist (puAmalgam h.le) = 4)
    (hstar : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) ∧
      puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal))
    (h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
      (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') ((Qv _ (baseA _)).relIndex (XM _ α')) := by
  have hOC : ∀ γ ρ : Vtx (puAmalgam h.le), IsMVtx _ γ → (puAmalgam h.le).treeGraph.Adj γ ρ →
      OffCentAt (puAmalgam h.le) γ ρ := fun γ ρ hγ hγρ =>
    offCentAt_of_edge _ (PU.isMVtx_baseA _) (adj_baseA_baseB _) (offCentAt_base h hCU) hγ hγρ
  have hXβ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 h.critDist_pos h.centHyp hc
  have key := endSetup_of h.hyp20 hb h.centHyp (fun ε ε' hc => (hstar ε ε' hc).1)
    (Lt := puTrans h.le L) (fun ε ε' hc => (hstar ε ε' hc).2)
    (fun γ ρ hγ hγρ => h.offDataAt hD hγ hγρ) hOC h8 hc
    (by rw [puAmalgam.stab_baseA h.le]; exact finite_imM' h.le M)
    (puTrans_le_stab h.le L (baseA _))
    (stab_le_normalizer_puTrans h.le h.L_subgroupOf_normal (baseA _))
    (puTrans_baseA_perfect h) (by rw [hgeo]; exact stab_baseA_eq h)
    (fun x hx hxQ => h.puTrans_L_le_closure (PU.isMVtx_baseA _) (adj_baseA_baseB _) (hXβ hx) hxQ)
  rwa [hgeo] at key

theorem relIndex_xm_eq (h : PUHyp M T L) (hD : XOffData M T)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    ∃ F : Subgroup G, IsXOff M T F ∧
      (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = (pCoreOf 2 M).relIndex F := by
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hoff := (isOffAt_xm h.hyp20 hb0 h.centHyp hc
    (h.offDataAt hD (PU.isMVtx_baseA _) (adj_geo_one_of_isCritical _ hb0 hc))
    (h.offDataAt hD hc'.1 (adj_geo_one_of_isCritical _ hb0 hc'))).1
  rw [hgeo] at hoff
  have hXT : XM (puAmalgam h.le) α' ≤ imM h.le T := by
    have := hoff.1
    rwa [puAmalgam.qv_baseB] at this
  obtain ⟨F, hFT, hF⟩ := exists_imM_eq_of_le h.le hXT
  refine ⟨F, (h.isOffAt_base_iff hFT).mp (hF ▸ hoff), ?_⟩
  rw [← hF, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    imM_relIndex' h.le _ (hFT.trans h.le)]

theorem e_eq_two_or_four (h : PUHyp M T L) (hD : XOffData M T)
    (hord : ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F ≤ 4)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = 2 ∨
      (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = 4 := by
  have hb0 := h.critDist_pos
  obtain ⟨F, hF, he⟩ := relIndex_xm_eq h hD hc hgeo
  have hle : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') ≤ 4 := he ▸ hord F hF
  have hne1 : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact xm_not_le_qv_of_isCritical h.hyp20 hb0 h.centHyp hc
  have hXβ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 hb0 h.centHyp hc
  have hfin : Finite ↥(XM (puAmalgam h.le) α') := by
    have : Finite ↥(imM h.le T) := finite_imM' h.le T
    rw [puAmalgam.qv_baseB] at hXβ
    exact Finite.of_injective _ (Subgroup.inclusion_injective hXβ)
  have h2 : IsPGroup 2 ↥(XM (puAmalgam h.le) α') :=
    (isPGroup_qv _ h.hyp20 (PU.not_isMVtx_baseB _)).to_le hXβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') ∣ 2 ^ k := by
    rw [← hk]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card _ _)
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hj'] at hle hne1 ⊢
  have hj2 : j ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  interval_cases j
  · simp at hne1
  · left; rfl
  · right; rfl

end CFSG.Quasithin.MS93.S38E
