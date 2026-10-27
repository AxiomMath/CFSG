module

public import CFSG.Walter.W67.W2Local
import CFSG.Walter.W67.Prop24
import CFSG.Walter.W67.Prop23
import CFSG.Walter.W67.W1Prop24B

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem index_ne_two_of_perfect {X : Type} [Group X] (hperf : commutator X = ⊤) :
    ∀ N : Subgroup X, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (X ⧸ N) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hperf, top_le_iff] at h1
  rw [h1, Subgroup.index_top] at h2
  omega

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hnX := Subgroup.mem_normalizer_iff.mp hn
  constructor
  · intro hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro w hw
    have hw' : n⁻¹ * w * n ∈ X := by
      refine (hnX (n⁻¹ * w * n)).mpr ?_
      rw [show n * (n⁻¹ * w * n) * n⁻¹ = w by group]
      exact hw
    have := hz _ hw'
    calc w * (n * z * n⁻¹) = n * ((n⁻¹ * w * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * w * n)) * n⁻¹ := by rw [this]
      _ = n * z * n⁻¹ * w := by group
  · intro hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro w hw
    have hw' : n * w * n⁻¹ ∈ X := (hnX w).mp hw
    have := hz _ hw'
    have e1 : w * z = n⁻¹ * ((n * w * n⁻¹) * (n * z * n⁻¹)) * n := by group
    have e2 : z * w = n⁻¹ * ((n * z * n⁻¹) * (n * w * n⁻¹)) * n := by group
    rw [e1, e2, this]

omit [Finite G] in
theorem le_normalizer_of_normal_subgroupOf {L M : Subgroup G} (hLM : L ≤ M)
    (hn : (L.subgroupOf M).Normal) : M ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hn.conj_mem ⟨x, hLM hx⟩ hx ⟨y, hy⟩
  · intro hx
    have h1 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ ∈ L :=
      hn.conj_mem ⟨y * x * y⁻¹, hLM hx⟩ hx ⟨y⁻¹, M.inv_mem hy⟩
    simpa [mul_assoc] using h1

omit [Finite G] in
theorem normal_subgroupOf_of_le_normalizer {L M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (L : Set G)) : (L.subgroupOf M).Normal :=
  ⟨fun x hx m => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hM m.2) x).mp hx⟩

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_T_ne_one : ∃ t ∈ fr.T, t ≠ 1 := by
  have hT : fr.T ≠ ⊥ := fun h0 => by
    have := fr.isKleinFour_T.card_four
    rw [h0, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT
  exact ⟨t, ht, fun h1 => ht1 (Subtype.ext h1)⟩

theorem S_le_centralizer {X : Subgroup G} (hXE : X ≤ fr.E) :
    (fr.S : Subgroup G) ≤ Subgroup.centralizer (X : Set G) := fun s hs =>
  Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS (hXE hx)) s hs).symm

theorem cover_le_centralizer {X : Subgroup G} (hXE : X ≤ fr.E) :
    Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (fr.E : Set G) ≤
      Subgroup.centralizer (X : Set G) := fun _ hc =>
  Subgroup.mem_centralizer_iff.mpr fun x hx => Subgroup.mem_centralizer_iff.mp hc.2 x (hXE hx)

theorem T_le_commutator_KX
    {X : Subgroup G} (hXE : X ≤ fr.E)
    (e : h.KX X ≃* PSL(2, GaloisField h.p (h.f / h.eX X))) : fr.T ≤ ⁅h.KX X, h.KX X⁆ :=
  PSL2Sub.le_commutator e h.odd_p (fr.div_eX_pos hXE) (fr.mod_eight_KX hXE e) (fr.T_le_KX hXE)
    fr.isKleinFour_T le_rfl

theorem index_ne_two_X
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {X : Subgroup G}
    (hXE : X ≤ fr.E) (e : h.KX X ≃* PSL(2, GaloisField h.p (h.f / h.eX X))) {M : Subgroup G}
    (hKM : h.KX X ≤ M)
    (hM : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (fr.E : Set G)
      ≤ Subgroup.normalizer (M : Set G)) :
    ∀ N : Subgroup G, N ≤ M → (N.subgroupOf M).Normal → (N.subgroupOf M).index ≠ 2 := by
  obtain ⟨t, htT, ht1⟩ := fr.exists_T_ne_one
  have htM : t ∈ ⁅M, M⁆ :=
    Subgroup.commutator_mono hKM hKM (fr.T_le_commutator_KX hXE e htT)
  exact index_ne_two_of_sylow_le_commutator fr.S
    (fr.S_le_commutator' hidx hM (fr.T_le_S htT) ht1 htM)

theorem lspec_of_three
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {X : Subgroup G}
    (hXE : X ≤ fr.E) (hX : X ≠ ⊥) (h3 : h.p ^ (h.f / h.eX X) = 3) :
    ∃ L : Subgroup G, LSpec h fr X L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨eKX⟩, -⟩ := lemma_2_6_i G h fr hXE hX
  have hfe := fr.div_eX_pos hXE
  set NX := Subgroup.normalizer (X : Set G)
  set CX := Subgroup.centralizer (X : Set G)
  have hCN : CX ≤ NX := Subgroup.centralizer_le_normalizer _
  have hSC : (fr.S : Subgroup G) ≤ CX := fr.S_le_centralizer hXE
  have hSN := hSC.trans hCN
  have hKXN : h.KX X ≤ NX := inf_le_right.trans hCN
  have hKXC : h.KX X ≤ Subgroup.centralizer ({h.J} : Set G) := inf_le_left.trans h.K_le_H
  have hKn : ∀ x ∈ NX, x * h.J = h.J * x → ∀ k ∈ h.KX X, x * k * x⁻¹ ∈ h.KX X :=
    fun x hx hxJ k hk => ⟨h.conj_mem_K (h.mem_H_iff.mpr hxJ) hk.1,
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer X hx) k).mp hk.2⟩
  have hcovN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (fr.E : Set G) ≤ NX := (fr.cover_le_centralizer hXE).trans hCN
  let hN : Hyp NX := h.ofSubgroup ⟨fr.S, hSN⟩ (hSN fr.J_mem) h.orderOf_J hKXN hKXC hKn h.p
    (h.f / h.eX X) h.p_ne_two hfe eKX
  have hidxN := index_ne_two_subtype
    (fr.index_ne_two_X hidx hXE eKX hKXN (hcovN.trans Subgroup.le_normalizer))
  obtain ⟨L', hL'n, hsup, hinf, hOC, ⟨K', hK'L, hJK', hCL', ⟨eK'⟩⟩, -⟩ :=
    prop_2_4 NX hN h3 hidxN
  set ι := NX.subtype
  have hι : Function.Injective ι := NX.subtype_injective
  have hrange : ι.range = NX := Subgroup.range_subtype NX
  set O' := CFSG.pPrimeCore 2 NX
  set L := L'.map ι
  set O := O'.map ι
  set K'' := K'.map ι
  have hLN : L ≤ NX := Subgroup.map_subtype_le _
  have hLsub : L.subgroupOf NX = L' := Subgroup.comap_map_eq_self_of_injective hι L'
  have hLn : (L.subgroupOf NX).Normal := hLsub ▸ hL'n
  have hLO : L ⊔ O = NX := by
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, hrange]
  have hLO' : L ⊓ O = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ hι, hinf, Subgroup.map_bot]
  have hOCL : O ≤ Subgroup.centralizer (L : Set G) := by
    have := Subgroup.map_mono (f := ι) hOC
    rw [JT.map_centralizer_of_injective ι hι] at this
    exact this.trans inf_le_right
  have hXO : X ≤ O := by
    have hX' : X.subgroupOf NX ≤ O' := le_sSup ⟨Subgroup.normal_in_normalizer, by
      rw [Nat.coprime_two_left, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        Subgroup.le_normalizer).toEquiv]
      exact Odd.of_dvd_nat fr.odd_card_E (Subgroup.card_dvd_of_le hXE)⟩
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hX' hx, rfl⟩
  have hLC : L ≤ CX := Subgroup.le_centralizer_iff.mpr (hXO.trans hOCL)
  have hO'odd : Odd (Nat.card O') := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := NX)
    rwa [Nat.coprime_two_left] at this
  have hL'idx : L'.index = Nat.card O' := by
    have h1 := card_sup_mul_card_inf_of_normal L' O'
    rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top] at h1
    have h2 := L'.card_mul_index
    have hpos : 0 < Nat.card L' := Nat.card_pos
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hSL : (fr.S : Subgroup G) ≤ L := by
    have := hL'n
    have hS' : IsPGroup 2 ((fr.S : Subgroup G).subgroupOf NX) :=
      fr.S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
    have h1 := le_of_odd_index (hL'idx ▸ hO'odd) hS'
    intro s hs
    exact ⟨⟨s, hSN hs⟩, h1 hs, rfl⟩
  have hOE : O ≤ fr.E := by
    intro o ho
    have hoS : o ∈ fr.CS := Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_iff.mp (hOCL ho) s (hSL hs)
    obtain ⟨o', ho', rfl⟩ := ho
    have hodd : Odd (orderOf (ι o')) := by
      rw [orderOf_injective ι hι]
      exact Odd.of_dvd_nat hO'odd (Subgroup.orderOf_dvd_natCard _ ho')
    exact fr.mem_E_of_odd hoS hodd
  have hJN : h.J ∈ NX := hSN fr.J_mem
  have hιJ : ι hN.J = h.J := rfl
  have hCJ : (Subgroup.centralizer ({hN.J} : Set NX)).map ι =
      NX ⊓ Subgroup.centralizer ({h.J} : Set G) := by
    rw [JT.map_centralizer_singleton_of_injective ι hι, hrange]
    rfl
  have hK''L : K'' ≤ L ⊓ Subgroup.centralizer ({h.J} : Set G) := by
    have := Subgroup.map_mono (f := ι) hK'L
    rw [Subgroup.map_inf_eq _ _ _ hι, hCJ] at this
    exact this.trans (inf_le_inf_left _ inf_le_right)
  have hJK'' : h.J ∉ K'' := by
    rintro ⟨k, hk, hkJ⟩
    apply hJK'
    have : k = hN.J := hι hkJ
    rw [← this]
    exact hk
  have hCL : L ⊓ Subgroup.centralizer ({h.J} : Set G) = Subgroup.zpowers h.J ⊔ K'' := by
    have := congrArg (Subgroup.map ι) hCL'
    rw [Subgroup.map_inf_eq _ _ _ hι, hCJ, Subgroup.map_sup, MonoidHom.map_zpowers, hιJ] at this
    calc L ⊓ Subgroup.centralizer ({h.J} : Set G) =
          L ⊓ (NX ⊓ Subgroup.centralizer ({h.J} : Set G)) := by
          rw [← inf_assoc, inf_eq_left.mpr hLN]
      _ = _ := this
  have eK'' : K'' ≃* PSL(2, GaloisField 3 1) := (K'.equivMapOfInjective ι hι).symm.trans eK'
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have : Fintype (GaloisField h.p (h.f / h.eX X)) := Fintype.ofFinite _
  let e3 : GaloisField 3 1 ≃+* GaloisField h.p (h.f / h.eX X) :=
    FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, GaloisField.card 3 1 one_ne_zero,
        GaloisField.card _ _ hfe.ne', h3]
      norm_num)
  have eK3 : K'' ≃* PSL(2, GaloisField h.p (h.f / h.eX X)) := eK''.trans (psl2RingEquiv e3)
  have hLidx : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (N.subgroupOf L).index ≠ 2 := by
    obtain ⟨t, htT, ht1⟩ := fr.exists_T_ne_one
    have htL : t ∈ Subgroup.zpowers h.J ⊔ K'' := by
      rw [← hCL]
      exact ⟨hSL (fr.T_le_S htT), h.K_le_H htT.2⟩
    have hJN' : Subgroup.zpowers h.J ≤ Subgroup.normalizer (K'' : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K'' : Set G))
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hK''L hk).2
    rw [sup_comm] at htL
    obtain ⟨k, hk, j, hj, hkj⟩ := (mem_sup_iff_of_le_normalizer hJN').mp htL
    have hjS : j ∈ (fr.S : Subgroup G) := (Subgroup.zpowers_le.mpr fr.J_mem) hj
    have hkS : k ∈ (fr.S : Subgroup G) := by
      have : k = t * j⁻¹ := by rw [← hkj, mul_inv_cancel_right]
      rw [this]
      exact (fr.S : Subgroup G).mul_mem (fr.T_le_S htT) ((fr.S : Subgroup G).inv_mem hjS)
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [one_mul] at hkj
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with h1 | h1
      · exact ht1 (hkj ▸ h1)
      · rw [← hkj, h1] at htT
        exact fr.J_not_mem_T htT
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp fr.S.isPGroup') ⟨k, hkS⟩
    rw [Subgroup.orderOf_mk] at hn
    have hkc : k ∈ ⁅K'', K''⁆ := PSL2Sub.mem_commutator_of_orderOf eK'' (by decide) one_pos
      (by norm_num) hk hn
    have hkL : k ∈ ⁅L, L⁆ :=
      Subgroup.commutator_mono (hK''L.trans inf_le_left) (hK''L.trans inf_le_left) hkc
    have hcovL := hcovN.trans (le_normalizer_of_normal_subgroupOf hLN hLn)
    exact index_ne_two_of_sylow_le_commutator fr.S (fr.S_le_commutator' hidx hcovL hkS hk1 hkL)
  have hJR : IsJRSubgroup L h.J K'' h.p (h.f / h.eX X) :=
    ⟨hSL fr.J_mem, h.orderOf_J, hK''L, hJK'', hCL, ⟨eK3⟩, hLidx,
      ⟨fr.S, hSL, fr.isElementaryAbelian_S, fr.card_S⟩⟩
  refine ⟨L, ⟨hLC, ⟨hLN, hLn⟩, ⟨K'', hJR, fun h3' => absurd h3 (by omega)⟩, fun hFX => ?_,
    fun _ => ?_⟩⟩
  · refine le_antisymm ?_ (sup_le hLN (fr.E_le_normalizer_of_F_le hXE hFX))
    show NX ≤ L ⊔ fr.E
    rw [← hLO]
    exact sup_le_sup_left hOE L
  · refine le_antisymm (fun x hx => ?_) (sup_le hLC inf_le_left)
    have hON : O ≤ Subgroup.normalizer (L : Set G) :=
      hOCL.trans (Subgroup.centralizer_le_normalizer _)
    have hxN : x ∈ L ⊔ O := hLO ▸ hCN hx
    obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hON).mp hxN
    have hoC : o ∈ CX := by
      have : o = l⁻¹ * (l * o) := by group
      rw [this]
      exact CX.mul_mem (CX.inv_mem (hLC hl)) hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hoC, hOE ho⟩)

end Frame

end CFSG.Walter.W67
