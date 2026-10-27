module

public import CFSG.Walter.ReeOrder.JT.Section7A
public import CFSG.Walter.ReeOrder.Ward.Defs

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma712a (h : JTHyp G) : Prop :=
  ∀ (s : Setup h) (μ : G), μ ∈ Subgroup.normalizer (s.Q : Set G) → orderOf μ = 3 →
    ∀ x ∈ s.Q, μ * x = x * μ → x = 1

@[expose] def Lemma716 (h : JTHyp G) : Prop :=
  ∀ C : Subgroup G, C ≤ h.F → IsCyclic C → 2 * Nat.card C + 1 = h.q →
    ∀ x ∈ C, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G)

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem eq_one_of_commute_of_dvd
    {x : G} (hxF : x ∈ h.F) (hx : 2 * orderOf x ∣ h.q - 1)
    {v : G} (hvF : v ∈ h.F) (hv : orderOf v = 2) (hxv : x * v = v * x) : x = 1 := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  obtain ⟨U, w, hU, hvU, hcard⟩ := (h.facts hp).even_torus v hvF hv
  have hUcard : 2 * Nat.card U = h.q + 1 := by
    rcases hcard with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · rw [JTHyp.q_eq] at hq8; omega
  have hxC : x ∈ h.F ⊓ Subgroup.centralizer ({v} : Set G) :=
    ⟨hxF, Subgroup.mem_centralizer_singleton_iff.mpr hxv⟩
  rw [hU.centralizer_eq hvU hv, hU.mem_sup_iff] at hxC
  have hodd : Odd (orderOf x) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h4 : 4 ∣ h.q - 1 := (Nat.mul_dvd_mul_left 2 (even_iff_two_dvd.mp hev)).trans hx
    omega
  rcases hxC with hxU | hxU
  · have h1 : orderOf x ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hxU
    have h2 : orderOf x ∣ (h.q - 1) / 2 := Nat.dvd_div_of_mul_dvd hx
    have h3 : (h.q - 1) / 2 + 1 = Nat.card U := by omega
    rw [← h3] at h1
    have := (Nat.dvd_add_right h2).mp h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  · have hxx := hU.mul_self_of_mul_mem hxU
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)

theorem normalizer_le_of_lemma716
    (h716 : Lemma716 h) {R : G} (hRF : R ∈ h.F)
    (hR : 2 * orderOf R + 1 = h.q) {R₀ : G} (hR₀ : R₀ ∈ Subgroup.zpowers R) (hR₀1 : R₀ ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers R₀ : Set G) ≤
      Subgroup.centralizer ({h.t} : Set G) := by
  have hC := h716 (Subgroup.zpowers R) ((Subgroup.zpowers_le).mpr hRF) inferInstance
    (by rw [Nat.card_zpowers, hR]) R₀ hR₀ hR₀1
  have hR₀F : R₀ ∈ h.F := (Subgroup.zpowers_le).mpr hRF hR₀
  have hR₀o : 2 * orderOf R₀ ∣ h.q - 1 := by
    rw [← hR, Nat.add_sub_cancel]
    exact Nat.mul_dvd_mul_left 2 (orderOf_dvd_of_mem_zpowers hR₀)
  have huniq : ∀ u : G, orderOf u = 2 → u * R₀ = R₀ * u → u = h.t := by
    intro u hu huR
    have huC : u ∈ Subgroup.centralizer ({h.t} : Set G) :=
      hC (Subgroup.mem_centralizer_singleton_iff.mpr huR)
    rcases h.mem_centralizer_t.mp huC with huF | huF
    · exact absurd (h.eq_one_of_commute_of_dvd hp3 hR₀F hR₀o huF hu huR.symm) hR₀1
    · by_contra hut
      have htu : h.t * u = u * h.t := (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
      have hv2 : orderOf (h.t * u) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two, show h.t * u * (h.t * u) = (h.t * h.t) * (u * u) by
            rw [mul_assoc, ← mul_assoc u, ← htu]; group, h.t_mul_t, one_mul,
            ← pow_two, ← hu, pow_orderOf_eq_one]
        · intro h0
          apply hut
          have := eq_inv_of_mul_eq_one_right h0
          rw [this, h.t_inv]
      refine hR₀1 (h.eq_one_of_commute_of_dvd hp3 hR₀F hR₀o huF hv2 ?_)
      have htR : h.t * R₀ = R₀ * h.t := (h.commute_of_mem_F hR₀F).symm
      calc R₀ * (h.t * u) = (R₀ * h.t) * u := by group
        _ = (h.t * R₀) * u := by rw [htR]
        _ = h.t * (R₀ * u) := by group
        _ = h.t * (u * R₀) := by rw [huR]
        _ = h.t * u * R₀ := by group
  intro g hg
  have hgR : g * R₀ * g⁻¹ ∈ Subgroup.zpowers R₀ :=
    (Subgroup.mem_normalizer_iff.mp hg R₀).mp (Subgroup.mem_zpowers R₀)
  have hzg : Subgroup.zpowers (g * R₀ * g⁻¹) = Subgroup.zpowers R₀ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgR) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq])
  have hR₀mem : R₀ ∈ Subgroup.zpowers (g * R₀ * g⁻¹) := hzg ▸ Subgroup.mem_zpowers R₀
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hR₀mem
  have hu2 : orderOf (g * h.t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
  have htR : h.t * R₀ = R₀ * h.t := (h.commute_of_mem_F hR₀F).symm
  have huz : Commute (g * h.t * g⁻¹) (g * R₀ * g⁻¹) := by
    change g * h.t * g⁻¹ * (g * R₀ * g⁻¹) = g * R₀ * g⁻¹ * (g * h.t * g⁻¹)
    calc g * h.t * g⁻¹ * (g * R₀ * g⁻¹) = g * (h.t * R₀) * g⁻¹ := by group
      _ = g * (R₀ * h.t) * g⁻¹ := by rw [htR]
      _ = g * R₀ * g⁻¹ * (g * h.t * g⁻¹) := by group
  have huR : g * h.t * g⁻¹ * R₀ = R₀ * (g * h.t * g⁻¹) := by
    have := (huz.zpow_right k).eq
    rwa [hk] at this
  have hut := huniq _ hu2 huR
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * h.t = (g * h.t * g⁻¹) * g := by group
    _ = h.t * g := by rw [hut]

theorem not_commute_of_lemma712a
    (h712 : Lemma712a h) {J' : G} (hJ'F : J' ∈ h.F)
    (hJ' : orderOf J' = 2) {S : G} (hSF : S ∈ h.F) (hS : 4 * orderOf S = h.q + 1)
    (hSJ : S * J' = J' * S) {A : G} (hA : orderOf A = 3)
    (hAN : A ∈ Subgroup.normalizer (Subgroup.closure ({h.t, J'} : Set G) : Set G)) :
    A * S ≠ S * A := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have htJ : Commute h.t J' := (h.commute_of_mem_F hJ'F).symm
  have hJJ : J' * J' = 1 := by rw [← pow_two, ← hJ', pow_orderOf_eq_one]
  have hJ1 : J' ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hJ'; omega
  have htJne : h.t ≠ J' := fun h0 => h.t_not_mem (h0 ▸ hJ'F)
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions h.t J' h.t_mul_t hJJ htJ with hTdef
  have hT : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.t_ne_one hJ1 htJne htJ
  have hmemT : ∀ x, x ∈ T ↔ x = h.t * J' ∨ x = h.t ∨ x = J' ∨ x = 1 := fun x => Iff.rfl
  have htT : h.t ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
  have hJT : J' ∈ T := (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hTcl : Subgroup.closure ({h.t, J'} : Set G) = T := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact htT
      · exact hJT
    · intro x hx
      have ht' : h.t ∈ Subgroup.closure ({h.t, J'} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hJ'' : J' ∈ Subgroup.closure ({h.t, J'} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      rcases (hmemT x).mp hx with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ ht' hJ''
      · exact ht'
      · exact hJ''
      · exact Subgroup.one_mem _
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
  obtain ⟨S₂, hTS⟩ := hT2.exists_le_sylow
  let s : Setup h := ⟨S₂, hTS htT, T, hTS, hT, htT⟩
  have hSC : S ∈ Subgroup.centralizer (s.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have htS : h.t * S = S * h.t := (h.commute_of_mem_F hSF).symm
    rcases (hmemT x).mp hx with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hSJ, ← mul_assoc, htS, mul_assoc]
    · exact htS
    · exact hSJ.symm
    · rw [one_mul, mul_one]
  have hSodd : Odd (orderOf S) := Nat.odd_iff.mpr (by omega)
  have hSQ : S ∈ s.Q := (s.mem_Q_iff hp).mpr ⟨hSC, hSodd⟩
  have hAT : A ∈ Subgroup.normalizer (s.T : Set G) := by
    change A ∈ Subgroup.normalizer (T : Set G)
    rw [← hTcl]
    exact hAN
  have hAQ : A ∈ Subgroup.normalizer (s.Q : Set G) := s.normalizer_T_le_normalizer_Q hp hAT
  intro hAS
  have hS1 := h712 s A hAQ hA S hSQ hAS
  rw [hS1, orderOf_one] at hS
  have := h.five_lt
  rw [← JTHyp.q_eq] at this
  omega

end JTHyp

theorem JTHyp.nonempty_reeTypeHyp
    (h : JTHyp G) (hp3 : h.p = 3) (h712 : Lemma712a h)
    (h716 : Lemma716 h) : Nonempty (Ward.ReeTypeHyp G) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hL := lemma_2_1 h hp
  have hward : Ward.wardSign (h.p ^ h.f) = -1 := by
    rw [Ward.wardSign, ← JTHyp.q_eq]
    simp [hq8]
  have hcast : ((h.p : ℤ) ^ h.f) = ((h.q : ℕ) : ℤ) := by rw [JTHyp.q_eq]; push_cast; ring
  refine ⟨{
    p := h.p
    f := h.f
    p_ne_two := hp
    f_pos := Nat.pos_of_ne_zero fun hf0 => by
      have := h.five_lt
      rw [hf0, pow_zero] at this
      omega
    card_sylow := fun P => (hL.2.1 P).2
    elementary_sylow := fun P => (hL.2.1 P).1
    index_ne_two := fun N _ => h.index_ne_two N
    J := h.t
    orderOf_J := h.orderOf_t
    L := h.F
    le_centralizer := h.le_centralizer
    J_not_mem := h.t_not_mem
    centralizer_eq := h.centralizer_eq
    iso := h.iso
    normalizer_le := ?_
    not_commute := ?_ }⟩
  · intro R hRF hR R₀ hR₀ hR₀1
    rw [hward, hcast] at hR
    have hR' : 2 * orderOf R + 1 = h.q := by omega
    exact h.normalizer_le_of_lemma716 hp3 h716 hRF hR' hR₀ hR₀1
  · intro J' hJ'F hJ' S hSF hS hSJ A hA hAN
    rw [hward, hcast] at hS
    have hS' : 4 * orderOf S = h.q + 1 := by omega
    exact h.not_commute_of_lemma712a hp3 h712 hJ'F hJ' hSF hS' hSJ hA hAN

end CFSG.Walter.JT
