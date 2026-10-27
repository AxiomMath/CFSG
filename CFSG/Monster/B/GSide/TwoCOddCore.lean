module

public import CFSG.Monster.B.GSide.TwoCCentralizer
public import CFSG.Monster.B.TwoA.Amalgam.RankFiveMatrix
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

theorem exists_adj_mem_sphereDistThree
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    ∃ w, cgraph.Adj u w ∧ w ∈ sphereDistThree cv0 := by
  have h := (rankFive_row_four ambientRootOrbitsHyp hu).2.2.2.2
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (s := cgraph.neighborSet u ∩ sphereDistThree cv0)
    (by rw [h]; decide)
  exact ⟨w, hw.1, hw.2⟩

theorem rankS_clabelS_mul_of_adj
    {p q : CVert} (h : cgraph.Adj p q) :
    rankS (clabelS p * clabelS q) = 2048 := by
  obtain ⟨-, -, -, -, s, hs⟩ := clabel_adj h
  have e : clabelS p * clabelS q = s⁻¹ * xhatS * s := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_clabelS]
    exact hs
  have hc : IsConj xhatS (s⁻¹ * xhatS * s) := isConj_iff.2 ⟨s⁻¹, by group⟩
  rw [e, ← rankS_conj hc, ← sEquiv_xs]
  exact rankS_sEquiv_xs

theorem orderOf_clabelS_mul_of_adj
    {p q : CVert} (h : cgraph.Adj p q) :
    orderOf (clabelS p * clabelS q) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (sq_clabelS_mul_of_commute (commute_clabelS_of_adj h)) fun h1 => ?_
  apply (clabel_adj h).1
  have e : clabelS p = clabelS q := by
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left (clabelS_mul_clabelS q)]
  exact congrArg Subtype.val e

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_map_subtype {H : Subgroup G} {N : Subgroup H} (hN : N.Normal) {g : G}
    (hg : g ∈ H) : g ∈ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hN.conj_mem n hn _, rfl⟩
  · rintro ⟨n, hn, hnx⟩
    refine ⟨⟨g, hg⟩⁻¹ * n * ⟨g, hg⟩⁻¹⁻¹, hN.conj_mem n hn _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hnx ⊢
    rw [hnx]
    group

theorem le_of_commute_centralizer_le [Finite G] {K M : Subgroup G} (hK : Odd (Nat.card K))
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : Commute a b) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (haM : Subgroup.centralizer {a} ≤ M)
    (hbM : Subgroup.centralizer {b} ≤ M) (habM : Subgroup.centralizer {a * b} ≤ M) : K ≤ M := by
  set T := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc
  have : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hab hc
  have hmem : ∀ x : G, x ∈ T ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => by
    change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have haT : a ∈ T := (hmem a).2 (Or.inr (Or.inl rfl))
  have hbT : b ∈ T := (hmem b).2 (Or.inr (Or.inr (Or.inl rfl)))
  have habT : a * b ∈ T := (hmem _).2 (Or.inl rfl)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ haK hbK
    · exact haK
    · exact hbK
    · exact Subgroup.one_mem _
  have hab1 : a * b ≠ 1 := fun h => hab (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left hb])
  have ha_ab : a ≠ a * b := fun h => hb1 (by
    have h' := congrArg (a⁻¹ * ·) h
    simpa using h'.symm)
  have hb_ab : b ≠ a * b := fun h => ha1 (by
    have h' := congrArg (· * b⁻¹) h
    simpa using h'.symm)
  have hdec := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers hK hTK haT hbT habT ha1 hb1
    hab1 hab ha_ab hb_ab
  intro k hk
  have hk' : k ∈ (K : Set G) := hk
  rw [hdec] at hk'
  obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩ := hk'
  exact M.mul_mem (M.mul_mem (haM (Subgroup.mem_inf.1 hx).2) (hbM (Subgroup.mem_inf.1 hy).2))
    (habM (Subgroup.mem_inf.1 hz).2)

theorem oddCore_centralizer_map_eq_bot_gen {S G : Type*} [Group S] [Group G] [Finite G]
    {Φ : S →* G} (hinj : Function.Injective Φ) {t a b : S} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) (hat : Commute a t)
    (hbt : Commute b t) (haM : Subgroup.centralizer {Φ a} ≤ Φ.range)
    (hbM : Subgroup.centralizer {Φ b} ≤ Φ.range)
    (habM : Subgroup.centralizer {Φ (a * b)} ≤ Φ.range)
    (hO : CFSG.oddCore (Subgroup.centralizer {t}) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer {Φ t}) = ⊥ := by
  rw [oddCore_eq_bot_iff] at hO ⊢
  intro N hN hNodd
  have hmapC : ∀ x : S, Commute x t → Φ x ∈ Subgroup.centralizer {Φ t} := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx.eq]
  set K : Subgroup G := N.map (Subgroup.centralizer {Φ t}).subtype with hKdef
  have hKodd : Odd (Nat.card K) := by
    rw [hKdef, Subgroup.card_map_of_injective (Subgroup.centralizer {Φ t}).subtype_injective]
    exact hNodd
  have hKC : K ≤ Subgroup.centralizer {Φ t} := Subgroup.map_subtype_le N
  have hKM : K ≤ Φ.range := le_of_commute_centralizer_le hKodd
    (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one])
    (fun h => ha1 (hinj (h.trans (map_one Φ).symm)))
    (fun h => hb1 (hinj (h.trans (map_one Φ).symm))) (fun h => hab (hinj h))
    (show Φ a * Φ b = Φ b * Φ a by rw [← map_mul, hc.eq, map_mul])
    (mem_normalizer_map_subtype hN (hmapC a hat)) (mem_normalizer_map_subtype hN (hmapC b hbt))
    haM hbM (by rw [← map_mul]; exact habM)
  have hmap : (K.comap Φ).map Φ = K := Subgroup.map_comap_eq_self hKM
  have hK'card : Nat.card (K.comap Φ) = Nat.card K := by
    have h : Nat.card ((K.comap Φ).map Φ) = Nat.card (K.comap Φ) :=
      Subgroup.card_map_of_injective hinj
    rw [hmap] at h
    exact h.symm
  have hK'C : K.comap Φ ≤ Subgroup.centralizer {t} := by
    intro x hx
    have h1 := hKC hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    exact hinj (by rw [map_mul, map_mul]; exact h1)
  have hK'n : ((K.comap Φ).subgroupOf (Subgroup.centralizer {t})).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show Φ ((g : S) * x * (g : S)⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    have hg := mem_normalizer_map_subtype hN
      (hmapC _ (Subgroup.mem_centralizer_singleton_iff.1 g.2))
    exact (Subgroup.mem_normalizer_iff.1 hg (Φ x)).1 hx
  have hcard : Nat.card ((K.comap Φ).subgroupOf (Subgroup.centralizer {t})) =
      Nat.card (K.comap Φ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'C).toEquiv
  have h1 := hO _ hK'n (by rw [hcard, hK'card]; exact hKodd)
  have h2 := Subgroup.subgroupOf_map_subtype (K.comap Φ) (Subgroup.centralizer {t})
  rw [h1, Subgroup.map_bot, inf_eq_left.2 hK'C] at h2
  have hK : K = ⊥ := by rw [← hmap, ← h2, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.centralizer {Φ t}).subtype_injective).1 hK

end Generic

theorem centralizer_map_clabelS_le
    {G : Type*} [Group G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {Φ : Shat →* G}
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) (p : CVert) :
    Subgroup.centralizer {Φ (clabelS p)} ≤ Φ.range := by
  have hE : IsConj (cV0 : Shat) (clabelS p) := by
    rw [coe_cV0]
    exact isConj_clabelS cv0 p
  obtain ⟨g, hg⟩ := isConj_iff.1 hE
  have e : Φ (clabelS p) = Φ g * d * (Φ g)⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv, map_cV0_of_psiInvHom hd ψ hΦ]
  rw [e]
  exact (completion_centralizer hd ψ Φ hΦ).2.2 _ ⟨g, rfl⟩

theorem oddCore_centralizer_twoC_eq_bot
    {G : Type} [Group G] [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hΓ2B : ∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range)
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    CFSG.oddCore (Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)}) = ⊥ := by
  have hinj : Function.Injective Φ :=
    injective_of_map_cV0_ne_one Φ ((map_cV0_of_psiInvHom hd ψ hΦ).symm ▸ hd)
  obtain ⟨w, huw, hw⟩ := exists_adj_mem_sphereDistThree hu
  have hcu : Commute (clabelS u) (cV0 : Shat) := (cV0_mul_clabelS_comm hu).symm
  have hcw : Commute (clabelS w) (cV0 : Shat) := (cV0_mul_clabelS_comm hw).symm
  have huw' : Commute (clabelS u) (clabelS w) := commute_clabelS_of_adj huw
  exact oddCore_centralizer_map_eq_bot_gen hinj (clabelS_mul_clabelS u) (clabelS_mul_clabelS w)
    (clabelS_ne_one u) (clabelS_ne_one w)
    (fun h => (clabel_adj huw).1 (congrArg Subtype.val h)) huw'
    (hcu.mul_right (Commute.refl _)) (hcw.mul_right huw'.symm)
    (centralizer_map_clabelS_le hd ψ hΦ u) (centralizer_map_clabelS_le hd ψ hΦ w)
    (hΓ2B _ (orderOf_clabelS_mul_of_adj huw) (rankS_clabelS_mul_of_adj huw))
    (native_B_all_involution_centralizers_odd_core_free.2.2 _ (orderOf_cV0_mul_clabelS hu))

theorem centralizer_le_range_of_rankS_eq_2158_of_twoB
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d)
    (hΓ2B : ∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range)
    {s : Shat} (hs : orderOf s = 2) (hrk : rankS s = 2158) :
    Subgroup.centralizer {Φ s} ≤ Φ.range := by
  obtain ⟨u, hu, hru⟩ := exists_rankS_clabelS_mul
  have hconj := isConj_of_rankS_eq (orderOf_cV0_mul_clabelS hu) hs (hru.trans hrk.symm)
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hg' : Φ g * Φ ((cV0 : Shat) * clabelS u) * (Φ g)⁻¹ = Φ s := by
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  exact centralizer_le_range_of_rankS_eq_2158 hd ψ Φ hΦ hDM hs hrk
    (oddCore_eq_bot_of_equiv (centralizerConjEquiv (Φ g) hg').symm
      (oddCore_centralizer_twoC_eq_bot hd ψ Φ hΦ hΓ2B hu))

end CFSG.Monster.B.GSide
