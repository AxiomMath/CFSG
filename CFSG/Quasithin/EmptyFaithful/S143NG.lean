module

public import CFSG.Quasithin.EmptyFaithful.S143NF
public import CFSG.Quasithin.EmptyFaithful.S143NB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

namespace A6Model

set_option maxRecDepth 100000 in
theorem five_fixed_free : ∀ (p : Fin 6) (σ : Equiv.Perm (Fin 6)),
    (σ.sign = 1 ∧ σ p = p ∧ σ ^ 5 = 1 ∧ σ ≠ 1) → ∀ b : N6, n6Act σ b = b → b = 1 := by
  decide +kernel

end A6Model

section Stab

@[expose] noncomputable def stabAlt (p : Fin 6) : Subgroup ↥(alternatingGroup (Fin 6)) :=
  (alternatingGroup.ofSubtype (Finset.univ.erase p)).range

theorem mem_stabAlt {p : Fin 6} {σ : ↥(alternatingGroup (Fin 6))} :
    σ ∈ stabAlt p ↔ (σ : Equiv.Perm (Fin 6)) p = p := by
  unfold stabAlt
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    by_contra hne
    have : p ∈ (σ : Equiv.Perm (Fin 6)).support := Equiv.Perm.mem_support.mpr hne
    have := h this
    simp at this
  · intro h x hx
    have hx' : (σ : Equiv.Perm (Fin 6)) x ≠ x := Equiv.Perm.mem_support.mp hx
    have : x ≠ p := fun hxp => hx' (by rw [hxp]; exact h)
    simp [this]

noncomputable def stabAltEquiv (p : Fin 6) :
    ↥(alternatingGroup ↥(Finset.univ.erase p)) ≃* ↥(stabAlt p) :=
  MonoidHom.ofInjective alternatingGroup.ofSubtype_injective

theorem stabAlt_simple (p : Fin 6) : IsSimpleGroup ↥(stabAlt p) := by
  have h5 : 5 ≤ Nat.card ↥(Finset.univ.erase p) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp
  have : IsSimpleGroup ↥(alternatingGroup ↥(Finset.univ.erase p)) :=
    alternatingGroup.isSimpleGroup h5
  exact (stabAltEquiv p).symm.isSimpleGroup

theorem stabAlt_card (p : Fin 6) : Nat.card ↥(stabAlt p) = 60 := by
  have hcard : Fintype.card ↥(Finset.univ.erase p) = 5 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp
  have : Nontrivial ↥(Finset.univ.erase p) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  rw [← Nat.card_congr (stabAltEquiv p).toEquiv, Nat.card_eq_fintype_card,
    card_alternatingGroup, hcard]
  simp [Nat.factorial]

end Stab

section Kd

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2) {p : Fin 6}
  (hcoc : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ.1)

variable {hS}

@[expose] noncomputable def kdHom (hM : KModel hS cm y) (δ : G) :
    ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) →* ↥(alternatingGroup (Fin 6)) :=
  hM.q.comp (Subgroup.inclusion inf_le_left)

variable (hS)

include hS htT htRQ hM hδD hδ hδA hcoc

omit htT htRQ in
theorem A_le_kdOf : c.Ac hrW hrV hr2 ≤ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
  have hAK : c.Ac hrW hrV hr2 ≤ kOf T M (c.Ac hrW hrV hr2) :=
    (c.Ac_le_rOf hrW hrV hr2).trans (le_sup_left.trans (c.rOf_sup_uOfL22_le_kOf hrW hrV hr2))
  intro a' ha'
  refine ⟨hAK ha', Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (Subgroup.mem_centralizer_iff.mp hδ a' ha').symm

omit hS htT htRQ hM hδD hδ hδA hcoc in
theorem kdOf_le_normalizer : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤
    Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
  inf_le_left.trans (c.kOf_le_normalizer_Ac hrW hrV hr2)

theorem range_kdHom : (kdHom hM δ).range = stabAlt p := by
  have hkdK : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ kOf T M (c.Ac hrW hrV hr2) := inf_le_left
  ext σ
  rw [MonoidHom.mem_range, mem_stabAlt]
  constructor
  · rintro ⟨k, rfl⟩
    exact (mem_kdOf_iff hS htT htRQ hM hδD hδ hδA hcoc (hkdK k.2)).mp k.2
  · intro hσ
    obtain ⟨k, hk⟩ := hM.q_surjective σ
    have hkd : (k : G) ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
      rw [mem_kdOf_iff hS htT htRQ hM hδD hδ hδA hcoc k.2]
      have : hM.q ⟨(k : G), k.2⟩ = σ := hk
      rw [this]
      exact hσ
    exact ⟨⟨(k : G), hkd⟩, hk⟩

theorem blockData_kd
    {y₅ : G} (hy₅ : y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)
    (hy₅o : orderOf y₅ = 5) :
    BlockData (kdHom hM δ) ((c.Ac hrW hrV hr2).subgroupOf (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))
      ⟨y₅, hy₅⟩ := by
  have hB := hS.basis
  have hAkd := A_le_kdOf hS hM hδD hδ hδA hcoc
  have hkdN : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    kdOf_le_normalizer
  have hkdK : kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ≤ kOf T M (c.Ac hrW hrV hr2) := inf_le_left
  have hy₅K : y₅ ∈ kOf T M (c.Ac hrW hrV hr2) := hkdK hy₅
  have hrange := range_kdHom hS htT htRQ hM hδD hδ hδA hcoc
  have := stabAlt_simple p
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hAkd).mpr hkdN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu w hw
    exact Subtype.ext (hB.comm u hu w hw)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAkd).toEquiv]
    exact c.card_Ac hrW hrV hr2
  · ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hM.q_eq_one_iff htT htRQ ⟨k, hkdK k.2⟩
  · exact (MulEquiv.subgroupCongr hrange).isSimpleGroup
  · rw [Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv]
    exact stabAlt_card p
  · exact (Subgroup.orderOf_coe (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))).symm.trans hy₅o
  · intro u hu hcomm
    have huA : (u : G) ∈ c.Ac hrW hrV hr2 := Subgroup.mem_subgroupOf.mp hu
    have h1 : y₅ * (u : G) * y₅⁻¹ = (u : G) :=
      congrArg (fun q : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) => (q : G)) hcomm
    set τ := hM.q ⟨y₅, hy₅K⟩ with hτ
    have hτsign : (τ : Equiv.Perm (Fin 6)).sign = 1 := Equiv.Perm.mem_alternatingGroup.mp τ.2
    have hτp : (τ : Equiv.Perm (Fin 6)) p = p :=
      (mem_kdOf_iff hS htT htRQ hM hδD hδ hδA hcoc hy₅K).mp hy₅
    have hτ5 : (τ : Equiv.Perm (Fin 6)) ^ 5 = 1 := by
      have h5 : (⟨y₅, hy₅K⟩ : ↥(kOf T M (c.Ac hrW hrV hr2))) ^ 5 = 1 := by
        apply Subtype.ext
        show y₅ ^ 5 = 1
        rw [← hy₅o]
        exact pow_orderOf_eq_one y₅
      have := congrArg (fun q : ↥(alternatingGroup (Fin 6)) => (q : Equiv.Perm (Fin 6)))
        (show τ ^ 5 = 1 by rw [hτ, ← map_pow, h5, map_one])
      simpa using this
    have hτ1 : (τ : Equiv.Perm (Fin 6)) ≠ 1 := by
      intro h1'
      have hτ1' : τ = 1 := Subtype.ext h1'
      have hy₅A : y₅ ∈ c.Ac hrW hrV hr2 :=
        (hM.q_eq_one_iff htT htRQ ⟨y₅, hy₅K⟩).mp hτ1'
      have h2 : y₅ ^ 2 = 1 := by rw [pow_two]; exact c.sq_Ac hrW hrV hr2 hy₅A
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hy₅o] at this
      omega
    have hact : n6Act (τ : Equiv.Perm (Fin 6)) (psiA cm z a r r1 (u : G)) =
        psiA cm z a r r1 (u : G) := by
      have := psiA_conj hB (c.kOf_le_normalizer_Ac hrW hrV hr2 hy₅K) huA
        (σ := (τ : Equiv.Perm (Fin 6))) (fun w => hM.q_act ⟨y₅, hy₅K⟩ w)
      rw [h1] at this
      exact this.symm
    have h0 := five_fixed_free p _ ⟨hτsign, hτp, hτ5, hτ1⟩ _ hact
    apply Subtype.ext
    exact psiA_inj hB hM.inj huA (c.Ac hrW hrV hr2).one_mem (h0.trans (psiA_one hB).symm)

section KdFacts

variable {y₅ : G} (hy₅ : y₅ ∈ kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) (hy₅o : orderOf y₅ = 5)

include hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o

theorem kd_perfect
    : ⁅kdOf (kOf T M (c.Ac hrW hrV hr2)) δ, kdOf (kOf T M (c.Ac hrW hrV hr2)) δ⁆ =
    kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
  have h := (blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o).perfect
  have h1 := congrArg (Subgroup.map (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).subtype) h
  rw [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1

theorem kd_pCore_le
    : pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) ≤ c.Ac hrW hrV hr2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
  have hP : ((pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)).subgroupOf
      (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)
  have hP2 : IsPGroup 2 ((pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)).subgroupOf
      (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) :=
    A4.isPGroup_subgroupOf_of_le (pCoreOf_le 2 _) (pCoreOf_isPGroup 2 _)
  intro u hu
  have := hB.pCore_le hP hP2 (show (⟨u, pCoreOf_le 2 _ hu⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) ∈
    (pCoreOf 2 (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)).subgroupOf
      (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) from hu)
  exact Subgroup.mem_subgroupOf.mp this

theorem le_commutator_A_kd : c.Ac hrW hrV hr2 ≤
    ⁅c.Ac hrW hrV hr2, kdOf (kOf T M (c.Ac hrW hrV hr2)) δ⁆ := by
  have hB := blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
  have hAkd := A_le_kdOf hS hM hδD hδ hδA hcoc
  have hn := hB.normal
  set Â := (c.Ac hrW hrV hr2).subgroupOf (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) with hÂ
  have hle : ⁅Â, (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆ ≤ Â :=
    Subgroup.commutator_le_left _ _
  have hnorm : (⁅Â, (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆).Normal := inferInstance
  have heq : ⁅Â, (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆ = Â := by
    rcases hB.irred hle (fun x b hb => hnorm.conj_mem b hb x) with h0 | h1
    · exfalso
      have hcen : ∀ u ∈ Â, (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) * u *
          (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁻¹ = u := by
        intro u hu
        have hc : ⁅u, (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆ ∈
            ⁅Â, (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆ :=
          Subgroup.commutator_mem_commutator hu (Subgroup.mem_top _)
        rw [h0, Subgroup.mem_bot] at hc
        have := commutatorElement_eq_one_iff_mul_comm.mp hc
        calc (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) * u *
              (⟨y₅, hy₅⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁻¹
            = (⟨y₅, hy₅⟩ * u) * ⟨y₅, hy₅⟩⁻¹ := rfl
          _ = (u * ⟨y₅, hy₅⟩) * ⟨y₅, hy₅⟩⁻¹ := by rw [← this]
          _ = u := by group
      have hbot : Â = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        exact Subgroup.mem_bot.mpr (hB.fix u hu (hcen u hu))
      have := hB.card
      rw [hbot] at this
      simp at this
    · exact h1
  intro u hu
  have hu' : (⟨u, hAkd hu⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) ∈
      ⁅Â, (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ))⁆ := by
    rw [heq]
    exact hu
  have hmap := Subgroup.mem_map_of_mem (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).subtype hu'
  rw [Subgroup.map_commutator] at hmap
  have e1 : Â.map (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).subtype = c.Ac hrW hrV hr2 :=
    Subgroup.map_subgroupOf_eq_of_le hAkd
  have e2 : (⊤ : Subgroup ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)).map
      (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ).subtype = kdOf (kOf T M (c.Ac hrW hrV hr2)) δ := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [e1, e2] at hmap
  exact hmap

theorem kd_cComp {S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ : Set G)) :
    kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ∈
      cComp (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ ⊔ S) := by
  have hB := blockData_kd hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
  have hperf := kd_perfect hS htT htRQ hM hδD hδ hδA hcoc hy₅ hy₅o
  refine ⟨?_, hperf, ?_, ?_⟩
  · intro hbot
    have h1 : y₅ ∈ (⊥ : Subgroup G) := hbot ▸ hy₅
    have hy1 : y₅ = 1 := Subgroup.mem_bot.mp h1
    rw [hy1, orderOf_one] at hy₅o
    omega
  · refine A4.subnormal_of_normal le_sup_left ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hSN
  · intro K' hlt hne hperf' hsub'
    have hsub'' : IsSubnormal K' (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) :=
      A4.subnormal_of_le_of_le hsub' hlt.le le_sup_left
    have hsub3 := A4.subnormal_subgroupOf (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) hsub''
    rw [Subgroup.subgroupOf_self] at hsub3
    rcases hB.subnormal_cases hsub3 rfl with hle | htop
    · have hKA : K' ≤ c.Ac hrW hrV hr2 := fun u hu =>
        Subgroup.mem_subgroupOf.mp (hle (show (⟨u, hlt.le hu⟩ :
          ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) ∈
            K'.subgroupOf (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) from hu))
      have hcomm : ⁅K', K'⁆ ≤ ⊥ := by
        refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hS.basis.comm g₁ (hKA hg₁) g₂ (hKA hg₂))
      exact hne (by rw [← hperf']; exact le_bot_iff.mp hcomm)
    · exfalso
      apply hlt.not_ge
      intro u hu
      have : (⟨u, hu⟩ : ↥(kdOf (kOf T M (c.Ac hrW hrV hr2)) δ)) ∈
          K'.subgroupOf (kdOf (kOf T M (c.Ac hrW hrV hr2)) δ) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact this

end KdFacts

end Kd


end S143

end CFSG.Quasithin
