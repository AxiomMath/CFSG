module

public import CFSG.Quasithin.EmptyFaithful.E111L2IH
public import CFSG.Quasithin.EmptyFaithful.E111L2IC
public import CFSG.Quasithin.EmptyFaithful.E111L2R

public section

namespace CFSG.Quasithin.E2.E22N.E111L

namespace KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

theorem conj_mem_of_cube {L V' P : Subgroup G} (hmem : ∀ x, x ∈ P ↔ x ∈ L ∧ x ^ 3 ∈ V')
    {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgV : g ∈ Subgroup.normalizer (V' : Set G)) {x : G} (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  rw [hmem] at hx ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgL x).mp hx.1, ?_⟩
  rw [conj_pow]
  exact (Subgroup.mem_normalizer_iff.mp hgV _).mp hx.2

theorem mem_normalizer_of_cube {L V' P : Subgroup G} (hmem : ∀ x, x ∈ P ↔ x ∈ L ∧ x ^ 3 ∈ V')
    {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgV : g ∈ Subgroup.normalizer (V' : Set G)) : g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_of_cube hmem hgL hgV, fun hx => ?_⟩
  have := conj_mem_of_cube hmem (Subgroup.inv_mem _ hgL) (Subgroup.inv_mem _ hgV) hx
  simpa [mul_assoc] using this

theorem conjSub_inf' (g : G) (H K : Subgroup G) :
    A1b.conjSub g (H ⊓ K) = A1b.conjSub g H ⊓ A1b.conjSub g K := by
  unfold A1b.conjSub
  exact Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem kleinMemberInner_main {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) : KleinMemberInner p := by
  intro G _ _ X T A S hR hPSL hAT hA hS h4 hinn z hzTS hz2 hzc
  have : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := by have := hp.two_le; omega
  have hSp := hPSL S hS
  obtain ⟨C, hCA, hCV0, hCV⟩ := exists_compl hA (inf_le_left : A ⊓ Subgroup.normalizer
    (S : Set G) ≤ A)
  have h : DiagSetting X T A S C := ⟨hR, hAT, hA, hS, hCA, hCV0⟩
  let _ : Fintype ↥C := Fintype.ofFinite _
  set D := diagSub S C h.diagComm with hDdef
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hRdef
  obtain ⟨hIK, hzI⟩ := innerImage_data hp7 hp8 hR hS hSp hAT hA h4 hinn hzTS hz2 hzc
  have hDp := isPSL_diag h hSp
  obtain ⟨m, hm, ⟨eTD⟩⟩ := sub_dihedral hp7 hp8 hDp h.isSylowIn_diag
  set V₀ := diagInner A S C h.diagComm with hV₀def
  have hV₀K := isKleinFour_diagInner h hIK
  obtain ⟨V', hV'TD, hV'K, hne, hV'N, hV₀N, hcard8, -, -⟩ :=
    CFSG.Quasithin.E22L2.dihedral_kleinFour_partner hm eTD
      (le_inf (diagInner_le_T h) (diagInner_le_diag h)) hV₀K
  have hV'D : V' ≤ D := hV'TD.trans inf_le_right
  set L₀ := Subgroup.normalizer (V' : Set G) ⊓ D with hL₀def
  have hL24 := sub_card_normalizer hp7 hp8 hDp hV'D hV'K
  obtain ⟨Φ, hΦs, hΦk⟩ := exists_phi hp7 hp8 hDp hV'D hV'K
  have hT8 : Nat.card ↥(T ⊓ L₀) = 8 := by
    rw [show T ⊓ L₀ = T ⊓ D ⊓ Subgroup.normalizer (V' : Set G) by
      rw [hL₀def, inf_comm (Subgroup.normalizer (V' : Set G)) D, inf_assoc]]
    exact hcard8
  have hV'L : V' ≤ L₀ := le_inf Subgroup.le_normalizer hV'D
  have hV₀L : V₀ ≤ L₀ := le_inf hV₀N (diagInner_le_diag h)
  obtain ⟨P, hPL, hmem, hVP, hPW, hLsup, y, hyP, hy⟩ :=
    exists_evenPart hV'L hV'K hV₀K hV₀L hne Φ hΦs hΦk hL24 hT8
  have hinv : ∀ k ∈ R, A1b.conjSub k D = D →
      A1b.conjSub k L₀ = L₀ ∧ A1b.conjSub k P = P ∧ A1b.conjSub k V' = V' := by
    intro k hk hkD
    have hkN : k ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_of_conjSub_eq hkD
    have hkV₀ : ∀ k' ∈ R, A1b.conjSub k' D = D → A1b.conjSub k' V₀ = V₀ := by
      intro k' hk' hk'D
      have hk'N : k' ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_of_conjSub_eq hk'D
      refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSub k' V₀).ge
      rintro _ ⟨w, hw, rfl⟩
      change k' * w * k'⁻¹ ∈ V₀
      rw [conj_eq_of_diagInner h hk'N hk'.2 hw]
      exact hw
    have hkT : A1b.conjSub k (T ⊓ D) = T ⊓ D := by
      rw [conjSub_inf', conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hk.1), hkD]
    have hV'k : A1b.conjSub k V' = V' := by
      refine partner_unique hm eTD (le_inf (diagInner_le_T h) (diagInner_le_diag h)) hV₀K
        (hkT ▸ A1b.conjSub_mono k hV'TD)
        (isKleinFour_of_equiv (V'.equivMapOfInjective _ (MulAut.conj k).injective).symm hV'K)
        hV'TD hV'K ?_ hne ?_ hV'N
      · intro heq
        apply hne
        have h1 := congrArg (A1b.conjSub k⁻¹) heq
        rwa [conjSub_inv_conjSub, hkV₀ k⁻¹ (R.inv_mem hk) (by
          rw [← hkD, conjSub_inv_conjSub, hkD])] at h1
      · calc A1b.conjSub k V' ≤ A1b.conjSub k (Subgroup.normalizer (V₀ : Set G)) :=
              A1b.conjSub_mono k hV'N
          _ = Subgroup.normalizer ((A1b.conjSub k V₀ : Subgroup G) : Set G) :=
              conjSub_normalizer k V₀
          _ = Subgroup.normalizer (V₀ : Set G) := by rw [hkV₀ k hk hkD]
    have hL₀k : A1b.conjSub k L₀ = L₀ := by
      rw [hL₀def, conjSub_inf', conjSub_normalizer, hV'k, hkD]
    refine ⟨hL₀k, ?_, hV'k⟩
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSub k P).ge
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_of_cube hmem (mem_normalizer_of_conjSub_eq hL₀k)
      (mem_normalizer_of_conjSub_eq hV'k) hx
  have hd : S4Data D T R L₀ P V' :=
    ⟨inf_le_right, hPL, hVP, hV'TD.trans inf_le_left, fun x hx => ((hmem x).mp hx).2,
      fun g hg => mem_normalizer_of_cube hmem (Subgroup.le_normalizer hg) hg.1, inf_le_left,
      hLsup, hinv⟩
  have hcent := sub_centralizer hp7 hDp hV'D hV'K
  have hV₀V : Nat.card ↥(V₀ ⊓ V') = 2 :=
    CFSG.Quasithin.E22L2.e22ps4_card_inf hcard8 (le_inf (le_inf (diagInner_le_T h)
      (diagInner_le_diag h)) hV₀N) (le_inf hV'TD Subgroup.le_normalizer) hV₀K.card_four
      hV'K.card_four hne
  have hamb := eOneAmb_K h hd hCV hinn hcent hV'K hV₀K hV₀L hV₀V hPW hyP hy
  set K := sSup (conjFam R L₀) ⊔ R with hKdef
  have hAK : A ≤ K := A_le_K h
  have hL₀K : L₀ ≤ K := by
    refine (le_sSup (conj_mem_conjFam (Subgroup.one_mem R))).trans' ?_ |>.trans le_sup_left
    rw [A1b.conjSub_one]
  refine ⟨K, ?_, ?_⟩
  · have hE1 := E1.eOne_of_eOneAmb hAK hamb
    obtain ⟨-, -, -, -, -, -, hc⟩ := id hE1
    exact ⟨le_top, le_inf (E1.tauOf_le ⊤ T A)
      ((E111R.tauOf_le (E111R.pCoreOf_two_eq_bot hR) T A).trans le_sup_right),
      isSylowIn_K h hd, Or.inl ⟨hE1, by rw [hc]; norm_num⟩⟩
  ·
    have hzS : z ∈ S := hzTS.2
    set zD := diagHom S C h.diagComm ⟨z, hzS⟩ with hzD
    have hinj := diagHom_injective h.diagComm h.center_trivial
    have hzD1 : zD ≠ 1 := by
      intro h1
      have : (⟨z, hzS⟩ : ↥S) = 1 := hinj (h1.trans (map_one _).symm)
      have hz1 : z = 1 := by simpa using congrArg Subtype.val this
      rw [hz1, orderOf_one] at hz2
      norm_num at hz2
    have hzDT : zD ∈ T ⊓ D := by
      rw [inf_diag_eq h]
      exact ⟨⟨z, hzS⟩, Subgroup.mem_subgroupOf.mpr hzTS, rfl⟩
    obtain ⟨z₀, hz₀, hz₀2, hz₀c, hKl, -⟩ := CFSG.Quasithin.E22L2.dihedral_sylow_data hm eTD
    have hz₀1 : z₀ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz₀2
      norm_num at hz₀2
    have hzV' : zD ∈ V' := by
      have := hKl V' hV'TD hV'K
      rwa [central_unique hm eTD hz₀ hzDT hz₀1 hzD1 hz₀c (diagHom_central h hzS hzc)] at this
    obtain ⟨g, hgL, hg⟩ := sub_moves hp7 hp8 hDp hV'D hV'K hzV' hzD1
    obtain ⟨s, rfl⟩ := hgL.2
    have hsc := inv_mul_diagHom_mem h.diagComm s
    refine ⟨_, hL₀K hgL, ?_, fun hcomm => hg ?_⟩
    · have : diagHom S C h.diagComm s = s * ((s : G)⁻¹ * diagHom S C h.diagComm s) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer s.2)
        (Subgroup.centralizer_le_normalizer _ hsc)
    · have hsz : s * ⟨z, hzS⟩ = ⟨z, hzS⟩ * s := by
        apply Subtype.ext
        have e1 := Subgroup.mem_centralizer_iff.mp hsc z hzS
        have e2 : diagHom S C h.diagComm s * z * (diagHom S C h.diagComm s)⁻¹ =
            (s : G) * z * (s : G)⁻¹ := by
          calc diagHom S C h.diagComm s * z * (diagHom S C h.diagComm s)⁻¹ =
              s * ((s : G)⁻¹ * diagHom S C h.diagComm s * z) *
                ((s : G)⁻¹ * diagHom S C h.diagComm s)⁻¹ * (s : G)⁻¹ := by group
            _ = s * (z * ((s : G)⁻¹ * diagHom S C h.diagComm s)) *
                ((s : G)⁻¹ * diagHom S C h.diagComm s)⁻¹ * (s : G)⁻¹ := by rw [← e1]
            _ = (s : G) * z * (s : G)⁻¹ := by group
        have e3 : diagHom S C h.diagComm s * z * (diagHom S C h.diagComm s)⁻¹ = z := by
          rw [hcomm]
          group
        simp only [Subgroup.coe_mul]
        calc (s : G) * z = ((s : G) * z * (s : G)⁻¹) * s := by group
          _ = z * s := by rw [← e2, e3]
      rw [← map_mul, ← map_mul, hsz]

end KMI

theorem kleinMemberInner_holds {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7) : KleinMemberInner p :=
  KMI.kleinMemberInner_main hp hp8

end CFSG.Quasithin.E2.E22N.E111L
