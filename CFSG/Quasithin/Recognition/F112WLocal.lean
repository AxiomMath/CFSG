module

public import CFSG.Quasithin.Background.D14Groups
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace F112W

section S3

variable {G : Type*} [Group G] {G₀ G₁ G₂ T V : Subgroup G}

structure IsNaturalS3 (G₁ V : Subgroup G) : Prop where
  card_eq : Nat.card V = 4
  index_eq : (G₁ ⊓ Subgroup.centralizer (V : Set G)).relIndex G₁ = 6

theorem relIndex_eq_two_pow [Finite G] {Q T : Subgroup G} (hT : IsPGroup 2 T) :
    ∃ k : ℕ, Q.relIndex T = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hT.index (Q.subgroupOf T)

theorem IsNaturalS3.ne_bot (hS : IsNaturalS3 G₁ V) : V ≠ ⊥ := by
  rintro rfl
  have := hS.card_eq
  rw [Subgroup.card_bot] at this
  omega

variable [Finite G]

theorem relIndex_pCoreOf_T (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V) :
    (pCoreOf 2 G₁).relIndex T = 2 := by
  have hN := hyp.normalizes
  have hTG₁ : T ≤ G₁ := hyp.sylow₁.1
  have hT2 : IsPGroup 2 T := hyp.sylow₁.2.1
  have hQ : pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G) := pCoreOf_eq_inf_centralizer hyp
  have hcardT := card_autOn_eq_relIndex (hTG₁.trans hN)
  have hcardG := card_autOn_eq_relIndex hN
  have hdvd : Nat.card (autOn T V) ∣ Nat.card (autOn G₁ V) :=
    Subgroup.card_dvd_of_le (autOn_le_autOn V hTG₁)
  rw [hcardT, hcardG, hS.index_eq] at hdvd
  obtain ⟨k, hk⟩ := relIndex_eq_two_pow (Q := T ⊓ Subgroup.centralizer (V : Set G)) hT2
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk2
    have := h4.trans hdvd
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hTC : T ≤ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.relIndex_eq_one.mp (show (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T = 1
        by rw [hk, pow_zero])
      exact fun t ht => (this ht).2
    have hTC' : T ≤ G₁ ⊓ Subgroup.centralizer (V : Set G) := le_inf hTG₁ hTC
    have hmul := Subgroup.relIndex_mul_relIndex T (G₁ ⊓ Subgroup.centralizer (V : Set G)) G₁ hTC'
      inf_le_left
    rw [hS.index_eq] at hmul
    exact isSylowTwoOf_odd_relIndex hyp.sylow₁ (hmul ▸ Dvd.dvd.mul_left (by norm_num : 2 ∣ 6) _)
  rw [hQ, hk]
  have : k = 1 := by omega
  rw [this, pow_one]

theorem card_inf_centralizer_T (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
  have hV := hS.ne_bot
  have hVQ : V ≤ T := (V_le_pCoreOf hyp).trans (isSylowTwoOf_pCoreOf_le hyp.sylow₁)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hyp.sylow₁.1.trans hyp.normalizes
  obtain ⟨x, hxV, hx1, hxT⟩ := D14.exists_fixed_of_lt hyp.sylow₁.2.1 hVQ (bot_lt_iff_ne_bot.mpr hV)
    hTN (fun t _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp [Subgroup.mem_bot])
  have hxC : x ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := hxT t ht
    rw [Subgroup.mem_bot] at this
    calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
      _ = x * t := by rw [this, one_mul]
  have hne : V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := by
    intro h
    exact hx1 (by
      have : x ∈ V ⊓ Subgroup.centralizer (T : Set G) := ⟨hxV, hxC⟩
      rwa [h] at this)
  have hnV : V ⊓ Subgroup.centralizer (T : Set G) ≠ V := by
    intro h
    have hVC : V ≤ Subgroup.centralizer (T : Set G) := h ▸ inf_le_right
    have hTC : T ≤ Subgroup.centralizer (V : Set G) := fun t ht => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((Subgroup.mem_centralizer_iff.mp (hVC hv)) t ht).symm
    have h2 := relIndex_pCoreOf_T hyp hS
    rw [pCoreOf_eq_inf_centralizer hyp, inf_eq_left.mpr hTC, Subgroup.relIndex_self] at h2
    omega
  have hlt : V ⊓ Subgroup.centralizer (T : Set G) < V := lt_of_le_of_ne inf_le_left hnV
  have h1 : 1 < Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have h4 : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) < 4 := hS.card_eq ▸ Subgroup.card_lt_of_lt hlt
  have hd : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G)) ∣ 4 :=
    hS.card_eq ▸ Subgroup.card_dvd_of_le inf_le_left
  interval_cases hc : Nat.card ↥(V ⊓ Subgroup.centralizer (T : Set G))
  · rfl
  · omega

theorem le_pCoreOf_G₂_of_critDist_eq_two (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : critDist G₀ G₁ G₂ V = 2) : V ≤ pCoreOf 2 G₂ := by
  by_contra h
  have := critDist_eq_one_of_not_le_pCoreOf hyp hV h
  omega

theorem exists_conj_of_critDist_eq_two (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : critDist G₀ G₁ G₂ V = 2) :
    ∃ x ∈ G₂, conjSub x V ≤ pCoreOf 2 G₂ ∧ conjSub x V ≤ G₁ ∧ ⁅V, conjSub x V⁆ ≠ ⊥ ∧
      ⁅V, conjSub x V⁆ ≤ V ⊓ conjSub x V ∧ ⁅⁅V, conjSub x V⁆, conjSub x V⁆ = ⊥ := by
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV
  have hVQ := le_pCoreOf_G₂_of_critDist_eq_two hyp hV hb
  have hd1 : dist (γ₁ G₀ G₁ G₂) γ = 1 := by
    have := hγ.geodesic
    omega
  have hγn : γ ∈ nbrs (γ₁ G₀ G₁ G₂) := dist_eq_one_iff_adj.mp hd1
  have hγ₁n : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
  have hγ₀n : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := mem_nbrs_symm hγ₁n
  obtain ⟨g, hg, hgγ⟩ := stab_transitive_on_nbrs hγ₀n hγn
  have hgG₂ : (g : G) ∈ G₂ := by rwa [stab_γ₁ hyp.le₂] at hg
  have hVγ : Vv V γ = conjSub (g : G) V := by
    rw [← hgγ]
    exact Vv_smul_γ₀ hyp.normalizes g
  have hev : Even (critDist G₀ G₁ G₂ V) := by rw [hb]; exact even_two
  obtain ⟨hnt, hle, hG1, hquad⟩ := commutator_V_Vv_of_even hyp hV hev hγ.dist_eq hγ.not_le
  rw [hVγ] at hnt hle hG1 hquad
  refine ⟨(g : G), hgG₂, ?_, hG1, hnt, hle, hquad⟩
  have e : conjSub (g : G) (pCoreOf 2 G₂) = pCoreOf 2 G₂ :=
    F1.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 G₂ hgG₂)
  rw [← e]
  exact conjSub_mono _ hVQ

theorem pCoreOf_sup_eq_T (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V) {W : Subgroup G}
    (hWQ : W ≤ pCoreOf 2 G₂) (hnt : ⁅V, W⁆ ≠ ⊥) : pCoreOf 2 G₁ ⊔ W = T := by
  have hQT : pCoreOf 2 G₁ ≤ T := isSylowTwoOf_pCoreOf_le hyp.sylow₁
  have hWT : W ≤ T := hWQ.trans (isSylowTwoOf_pCoreOf_le hyp.sylow₂)
  have hle : pCoreOf 2 G₁ ⊔ W ≤ T := sup_le hQT hWT
  have hWnQ : ¬ W ≤ pCoreOf 2 G₁ := by
    intro hW
    apply hnt
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hW.trans (pCoreOf_le_centralizer hyp))
  have h2 := relIndex_pCoreOf_T hyp hS
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁) (pCoreOf 2 G₁ ⊔ W) T le_sup_left hle
  rw [h2] at hmul
  have hdvd : (pCoreOf 2 G₁ ⊔ W).relIndex T ∣ 2 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  · exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
  · rw [h2'] at hmul
    have h3 : (pCoreOf 2 G₁).relIndex (pCoreOf 2 G₁ ⊔ W) = 1 := by omega
    exact absurd (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h3)) hWnQ

theorem pCoreOf_sup_pCoreOf_eq (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    {W : Subgroup G} (hWQ : W ≤ pCoreOf 2 G₂) (hnt : ⁅V, W⁆ ≠ ⊥) :
    pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ = T :=
  le_antisymm (sup_le (isSylowTwoOf_pCoreOf_le hyp.sylow₁) (isSylowTwoOf_pCoreOf_le hyp.sylow₂))
    ((pCoreOf_sup_eq_T hyp hS hWQ hnt).symm.le.trans (sup_le_sup_left hWQ _))

theorem inf_conj_eq_inf_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    {W : Subgroup G} (hWab : IsElemAbelian 2 W) (hWcard : Nat.card W = 4)
    (hWQ : W ≤ pCoreOf 2 G₂) (hnt : ⁅V, W⁆ ≠ ⊥) (hle : ⁅V, W⁆ ≤ V ⊓ W) :
    V ⊓ W = V ⊓ Subgroup.centralizer (T : Set G) ∧ ⁅V, W⁆ = V ⊓ W ∧ Nat.card ↥(V ⊓ W) = 2 := by
  have hT := pCoreOf_sup_eq_T hyp hS hWQ hnt
  have hc2 := card_inf_centralizer_T hyp hS
  have hCW : V ⊓ Subgroup.centralizer (T : Set G) = V ⊓ Subgroup.centralizer (W : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left V (Subgroup.centralizer_le (hWQ.trans (isSylowTwoOf_pCoreOf_le hyp.sylow₂)))
    · intro x hx
      refine ⟨hx.1, ?_⟩
      have hQx : pCoreOf 2 G₁ ≤ Subgroup.centralizer ({x} : Set G) := fun q hq => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer hyp hq) x hx.1).symm
      have hWx : W ≤ Subgroup.centralizer ({x} : Set G) := fun w hw => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hx.2 w hw)
      have hTx : T ≤ Subgroup.centralizer ({x} : Set G) := hT ▸ sup_le hQx hWx
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
  have hcom_ne : ⁅V, W⁆ ≠ ⊥ := hnt
  have h1' : 1 < Nat.card ↥⁅V, W⁆ := (Subgroup.one_lt_card_iff_ne_bot _).mpr hcom_ne
  have hVW_ne : V ⊓ W ≠ V := by
    intro h
    have hVW : V ≤ W := h ▸ inf_le_right
    have hVeqW : V = W := Subgroup.eq_of_le_of_card_ge hVW (by rw [hWcard, hS.card_eq])
    apply hnt
    rw [← hVeqW]
    exact commutator_self_eq_bot hyp.elemAbelian
  have hlt : V ⊓ W < V := lt_of_le_of_ne inf_le_left hVW_ne
  have h1 : 1 < Nat.card ↥(V ⊓ W) := h1'.trans_le (Subgroup.card_le_of_le hle)
  have h4 : Nat.card ↥(V ⊓ W) < 4 := hS.card_eq ▸ Subgroup.card_lt_of_lt hlt
  have hd : Nat.card ↥(V ⊓ W) ∣ 4 := hS.card_eq ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(V ⊓ W) = 2 := by
    interval_cases hc : Nat.card ↥(V ⊓ W)
    · rfl
    · omega
  have hle' : V ⊓ W ≤ V ⊓ Subgroup.centralizer (W : Set G) := by
    refine le_inf inf_le_left fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (isElemAbelian_comm hWab hy hw.2)
  have hEq : V ⊓ W = V ⊓ Subgroup.centralizer (W : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [← hCW, hc2, h2])
  refine ⟨hEq.trans hCW.symm, ?_, h2⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by
    have hd2 : Nat.card ↥⁅V, W⁆ ∣ 2 := h2 ▸ Subgroup.card_dvd_of_le hle
    have := Nat.le_of_dvd (by norm_num) hd2
    omega)

omit [Finite G] in
theorem conjClosure_le_pCoreOf_G₂ (hVQ : V ≤ pCoreOf 2 G₂) : conjClosure V G₂ ≤ pCoreOf 2 G₂ :=
  conjClosure_le fun _ hh _ hz =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hh) _).mp (hVQ hz)

theorem critDist_two_structure (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hS : IsNaturalS3 G₁ V)
    (hb : critDist G₀ G₁ G₂ V = 2) :
    V ≤ conjClosure V G₂ ∧ conjClosure V G₂ ≤ pCoreOf 2 G₂ ∧
      (pCoreOf 2 G₁).relIndex (conjClosure V G₂) = 2 ∧
      ∃ x ∈ G₂, conjSub x V ≤ conjClosure V G₂ ∧ conjSub x V ≤ G₁ ∧
        pCoreOf 2 G₁ ⊔ conjSub x V = T ∧ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ = T ∧
        ⁅V, conjSub x V⁆ = V ⊓ conjSub x V ∧
        V ⊓ conjSub x V = V ⊓ Subgroup.centralizer (T : Set G) ∧
        Nat.card ↥(V ⊓ conjSub x V) = 2 ∧ ⁅⁅V, conjSub x V⁆, conjSub x V⁆ = ⊥ := by
  have hV := hS.ne_bot
  have hVQ := le_pCoreOf_G₂_of_critDist_eq_two hyp hV hb
  obtain ⟨x, hxG₂, hWQ, hWG, hnt, hle, hquad⟩ := exists_conj_of_critDist_eq_two hyp hV hb
  have hWab : IsElemAbelian 2 (conjSub x V) := F7.isElemAbelian_conjSub hyp.elemAbelian
  have hWcard : Nat.card (conjSub x V) = 4 := (card_conjSub x V).trans hS.card_eq
  obtain ⟨hVW, hcomm, hc2⟩ := inf_conj_eq_inf_centralizer hyp hS hWab hWcard hWQ hnt hle
  have hWU : conjSub x V ≤ conjClosure V G₂ := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 := mem_conjClosure (Z := V) (H := G₂) hxG₂ hy
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e] at h1
  have hT := pCoreOf_sup_eq_T hyp hS hWQ hnt
  have hUQ := conjClosure_le_pCoreOf_G₂ hVQ
  have hUT : conjClosure V G₂ ≤ T := hUQ.trans (isSylowTwoOf_pCoreOf_le hyp.sylow₂)
  refine ⟨le_conjClosure V G₂, hUQ, ?_, x, hxG₂, hWU, hWG, hT,
    pCoreOf_sup_pCoreOf_eq hyp hS hWQ hnt, hcomm, hVW, hc2, hquad⟩
  have hsup : pCoreOf 2 G₁ ⊔ conjClosure V G₂ = T := by
    apply le_antisymm (sup_le (isSylowTwoOf_pCoreOf_le hyp.sylow₁) hUT)
    rw [← hT]
    exact sup_le_sup_left hWU _
  have hUN : conjClosure V G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ : Subgroup G) : Set G) :=
    (hUT.trans hyp.sylow₁.1).trans (le_normalizer_pCoreOf 2 G₁)
  have := F1.relIndex_sup_eq_of_le_normalizer hUN
  rw [sup_comm, hsup] at this
  rw [← this]
  exact relIndex_pCoreOf_T hyp hS

end S3

end F112W

end CFSG.Quasithin
