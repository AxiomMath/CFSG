module

public import CFSG.Quasithin.Background.C2Twelve

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H R M L V T : Subgroup G}

@[expose] def ASC213Step (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V : Subgroup G, HypC28 H R M L V → oTwoFstarIn H ≤ M → L ∈ cComp H

namespace C2Thirteen

omit [Finite G] in
theorem conjByElt_injective (g : G) : Function.Injective (conjByElt g) :=
  Subgroup.map_injective (MulAut.conj g).injective

omit [Finite G] in
theorem conjByElt_sup (g : G) (A B : Subgroup G) :
    conjByElt g (A ⊔ B) = conjByElt g A ⊔ conjByElt g B :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem conjByElt_sup_pair {g : G} {L L₂ : Subgroup G} (hne : L₂ ≠ L)
    (h₁ : conjByElt g L = L ∨ conjByElt g L = L₂)
    (h₂ : conjByElt g L₂ = L ∨ conjByElt g L₂ = L₂) :
    conjByElt g (L ⊔ L₂) = L ⊔ L₂ := by
  rw [conjByElt_sup]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (conjByElt_injective g (h₂.trans h₁.symm)) hne
  · rw [h₁, h₂]
  · rw [h₁, h₂, sup_comm]
  · exact absurd (conjByElt_injective g (h₁.trans h₂.symm)).symm hne

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

theorem component_le_of_sup_eq_top {H1 A T : Subgroup Q} [hH1 : H1.Normal]
    (hs1 : Group.IsSolvable H1) (hD : (H1 ⊔ A).Normal) (hsT : Group.IsSolvable T)
    (htop : H1 ⊔ A ⊔ T = ⊤) {K : Subgroup Q} (hK : CFSG.IsComponent K) : K ≤ A := by
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hKD : K ≤ H1 ⊔ A :=
    (le_perfectCore_of_perfect le_top hKperf).trans
      (perfectCore_le_of_sup_solvable le_top Subgroup.normal_subgroupOf htop.symm hsT)
  have hKH1 : K ≤ Subgroup.centralizer (H1 : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.component_solvable_centralizer hs1 hH1.isSubnormal).1 K hK)
  have hH1K : H1 ≤ Subgroup.centralizer (K : Set Q) := Subgroup.le_centralizer_iff.mpr hKH1
  have hEK : K ⊔ H1 ≤ Subgroup.normalizer (K : Set Q) :=
    sup_le Subgroup.le_normalizer (hH1K.trans (Subgroup.centralizer_le_normalizer _))
  have hperfE : perfectCore (K ⊔ H1) = K :=
    le_antisymm (perfectCore_le_of_sup_solvable le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer hEK) rfl hs1)
      (le_perfectCore_of_perfect le_sup_left hKperf)
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup Q, J = A ⊓ (K ⊔ H1) := ⟨_, rfl⟩
  have hJA : J ≤ A := hJ ▸ inf_le_left
  have hJE : J ≤ K ⊔ H1 := hJ ▸ inf_le_right
  have hEJ : K ⊔ H1 ≤ H1 ⊔ J := by
    intro x hx
    have hx' : x ∈ ((H1 ⊔ A : Subgroup Q) : Set Q) :=
      (sup_le hKD le_sup_left : K ⊔ H1 ≤ H1 ⊔ A) hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H1 A Subgroup.le_normalizer_of_normal] at hx'
    obtain ⟨s, hs, a, ha, rfl⟩ := hx'
    have haE : a ∈ K ⊔ H1 := by
      have := (K ⊔ H1).mul_mem ((K ⊔ H1).inv_mem (Subgroup.mem_sup_right hs)) hx
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs)
      (Subgroup.mem_sup_right (hJ ▸ (⟨ha, haE⟩ : a ∈ A ⊓ (K ⊔ H1))))
  have hE : K ⊔ H1 = H1 ⊔ J := le_antisymm hEJ (sup_le le_sup_right hJE)
  let φ : Q →* Q ⧸ H1 := QuotientGroup.mk' H1
  have hmapE : (K ⊔ H1).map φ = J.map φ := by
    rw [hE, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hmapK : K.map φ = (perfectCore J).map φ := by
    have h1 := map_perfectCore φ (K ⊔ H1)
    rw [hperfE, hmapE] at h1
    exact h1.trans (map_perfectCore φ J).symm
  have hKle : K ≤ perfectCore J ⊔ H1 := by
    have : K ≤ (K.map φ).comap φ := Subgroup.le_comap_map φ K
    rw [hmapK, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    exact this
  have hJ₀K : perfectCore J ≤ K := hperfE ▸ perfectCore_mono hJE
  have hH1J₀ : H1 ≤ Subgroup.centralizer (perfectCore J : Set Q) :=
    Subgroup.le_centralizer_iff.mpr (hJ₀K.trans hKH1)
  have hn : perfectCore J ⊔ H1 ≤ Subgroup.normalizer (perfectCore J : Set Q) :=
    sup_le Subgroup.le_normalizer (hH1J₀.trans (Subgroup.centralizer_le_normalizer _))
  have h3 : perfectCore (perfectCore J ⊔ H1) ≤ perfectCore J :=
    perfectCore_le_of_sup_solvable le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer hn)
      rfl hs1
  exact ((le_perfectCore_of_perfect hKle hKperf).trans h3).trans
    ((perfectCore_le J).trans hJA)

theorem isSolvable_map_of_solvable {Q' : Type*} [Group Q'] [Finite Q'] (f : Q →* Q')
    {S : Subgroup Q} (hS : Group.IsSolvable S) : Group.IsSolvable (S.map f) := by
  rw [isSolvable_iff_perfectCore_eq_bot] at hS ⊢
  rw [← map_perfectCore, hS, Subgroup.map_bot]

end Abstract

theorem oTwoFstarIn_le_of_solvable (hC129 : ASC129Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) (hRT : R ≤ T)
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ H) (hsolv : Group.IsSolvable ↥H₁)
    (hN : conjClosure L M ⊔ T ≤ Subgroup.normalizer (H₁ : Set G)) :
    oTwoFstarIn (H₁ ⊔ (conjClosure L M ⊔ T)) ≤ M ⊓ (H₁ ⊔ (conjClosure L M ⊔ T)) := by
  set M₀ := conjClosure L M with hM₀
  set H' := H₁ ⊔ (M₀ ⊔ T) with hH'
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hTM : T ≤ M := hT.1
  have hH'H : H' ≤ H := sup_le hH₁ (sup_le (hM₀M.trans h.le_H) (hTM.trans h.le_H))
  have hX : M₀ ⊔ T ≤ H' := le_sup_right
  have hH₁H' : H₁ ≤ H' := le_sup_left
  have hM₀H' : M₀ ≤ H' := le_sup_left.trans hX
  have hTH' : T ≤ H' := le_sup_right.trans hX
  have h' : HypC28 H' R (M ⊓ H') L V := c2_9_three hA3 h hT hRT hX hH'H
  have hF1 : oTwoFIn H' ≤ M ⊓ H' := c2_11 hC129 hC19 h'
  have hpC : pCoreOf 2 H' ≤ M ⊓ H' := (c2_1_pCore_le (c2_9_two h').2).trans h'.le_M
  let π : ↥H' →* ↥H' ⧸ CFSG.pCore 2 ↥H' := QuotientGroup.mk' (CFSG.pCore 2 ↥H')
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let N : Subgroup (↥H' ⧸ CFSG.pCore 2 ↥H') := ((M ⊓ H').subgroupOf H').map π
  have hFN : CFSG.fittingSubgroup (↥H' ⧸ CFSG.pCore 2 ↥H') ≤ N := by
    intro q hq
    obtain ⟨y, rfl⟩ := hπ q
    have hy : (y : G) ∈ oTwoFIn H' := ⟨y, hq, rfl⟩
    exact ⟨y, hF1 hy, rfl⟩
  have hEN : CFSG.layer (↥H' ⧸ CFSG.pCore 2 ↥H') ≤ N := by
    refine sSup_le fun K hK => ?_
    have hH'N : H' ≤ Subgroup.normalizer (H₁ : Set G) := sup_le Subgroup.le_normalizer hN
    have hS1n : (H₁.subgroupOf H').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hH'N
    have : ((H₁.subgroupOf H').map π).Normal := hS1n.map π hπ
    have : Group.IsSolvable ↥H₁ := hsolv
    have hS1s : Group.IsSolvable ↥(H₁.subgroupOf H') :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hH₁H').toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hH₁H').injective
    have hs1 : Group.IsSolvable ↥((H₁.subgroupOf H').map π) :=
      isSolvable_map_of_solvable π hS1s
    have hST2 : IsPGroup 2 ↥(T.subgroupOf H') :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH').symm
    have hSTs : Group.IsSolvable ↥(T.subgroupOf H') := by
      have : Group.IsNilpotent ↥(T.subgroupOf H') := hST2.isNilpotent
      infer_instance
    have hsT : Group.IsSolvable ↥((T.subgroupOf H').map π) := isSolvable_map_of_solvable π hSTs
    have hTn : T ≤ Subgroup.normalizer ((H₁ ⊔ M₀ : Subgroup G) : Set G) := by
      intro t ht
      have h1 : t ∈ Subgroup.normalizer (H₁ : Set G) := hN (Subgroup.mem_sup_right ht)
      have h2 : t ∈ Subgroup.normalizer (M₀ : Set G) := le_normalizer_conjClosure L M (hTM ht)
      rw [C2Eleven.mem_normalizer_iff_conjByElt] at h1 h2 ⊢
      rw [conjByElt_sup, h1, h2]
    have hH'n : H' ≤ Subgroup.normalizer ((H₁ ⊔ M₀ : Subgroup G) : Set G) := by
      rw [hH', ← sup_assoc]
      exact sup_le Subgroup.le_normalizer hTn
    have hDn : ((H₁ ⊔ M₀).subgroupOf H').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hH'n
    have hD : ((H₁.subgroupOf H').map π ⊔ (M₀.subgroupOf H').map π).Normal := by
      rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hH₁H' hM₀H']
      exact hDn.map π hπ
    have htop : (H₁.subgroupOf H').map π ⊔ (M₀.subgroupOf H').map π ⊔
        (T.subgroupOf H').map π = ⊤ := by
      rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hH₁H' hM₀H',
        ← Subgroup.subgroupOf_sup (sup_le hH₁H' hM₀H') hTH', sup_assoc, ← hH',
        Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective π hπ]
    have hKA := component_le_of_sup_eq_top hs1 hD hsT htop hK
    exact hKA.trans (Subgroup.map_mono (Subgroup.comap_mono (le_inf hM₀M hM₀H')))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, hzy⟩ := (sup_le hFN hEN) hy
  have hzy' : z⁻¹ * y ∈ CFSG.pCore 2 ↥H' := QuotientGroup.eq.mp hzy
  have hzp : (((z⁻¹ * y : ↥H')) : G) ∈ pCoreOf 2 H' :=
    ⟨z⁻¹ * y, hzy', rfl⟩
  have hzM : (z : G) ∈ M ⊓ H' := hz
  have : (y : G) = (z : G) * (((z⁻¹ * y : ↥H')) : G) := by simp
  show (y : G) ∈ M ⊓ H'
  rw [this]
  exact (M ⊓ H').mul_mem hzM (hpC hzp)

end C2Thirteen

theorem c2_13 (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) (hF : oTwoFstarIn H ≤ M) :
    H = M ∨ (conjClosure L M = L ∧ L ∈ cComp H ∧
      M = H ⊓ Subgroup.normalizer (conjClosure L M : Set G) ∧ M.relIndex H = 2) := by
  by_cases hMH : H = M
  · exact Or.inl hMH
  right
  have hL : L ∈ cComp H := hStep H R M L V h hF
  have h12 := c2_12 hC129 hC111 hC19 hA3 h hT hRT
  have hnn : ¬ H ≤ Subgroup.normalizer (conjClosure L M : Set G) := fun hHn =>
    hMH ((inf_eq_left.mpr hHn).symm.trans h12)
  obtain ⟨T', hT', hTT'⟩ := B6.exists_isSylowTwoOf_ge hT.2.1 (hT.1.trans h.le_H)
  obtain ⟨hconj, hcase⟩ := hA3 H T' L h.sqtk hT' hL
  rcases hcase with hall | ⟨t, htT', htn, hset, -, -, -⟩
  ·
    exfalso
    have hHL : ∀ g ∈ H, conjByElt g L = L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj] at hmem
      obtain ⟨t, ht, hteq⟩ := hmem
      rw [show conjByElt g L = conjByElt t L from hteq]
      exact C2Eleven.mem_normalizer_iff_conjByElt.mp (hall t ht)
    have hM0L : conjClosure L M = L := by
      refine le_antisymm (conjClosure_le fun m hm z hz => ?_) (le_conjClosure L M)
      have := C2Eleven.conj_mem_conjByElt (g := m) hz
      rwa [hHL m (h.le_H hm)] at this
    apply hnn
    rw [hM0L]
    exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hHL g hg)
  ·
    have hne : conjByElt t L ≠ L := fun heq =>
      htn (C2Eleven.mem_normalizer_iff_conjByElt.mpr heq)
    have htH : t ∈ H := hT'.1 htT'
    have hHset : ∀ g ∈ H, conjByElt g L = L ∨ conjByElt g L = conjByElt t L := by
      intro g hg
      have hmem : conjByElt g L ∈ conjSubgroupsBy H L := ⟨g, hg, rfl⟩
      rw [hconj, hset] at hmem
      exact hmem
    have hHset₂ : ∀ g ∈ H, conjByElt g (conjByElt t L) = L ∨
        conjByElt g (conjByElt t L) = conjByElt t L := by
      intro g hg
      rw [← C2Eleven.conjByElt_mul]
      exact hHset (g * t) (H.mul_mem hg htH)
    have hpair : ∀ g ∈ H, conjByElt g (L ⊔ conjByElt t L) = L ⊔ conjByElt t L := fun g hg =>
      C2Thirteen.conjByElt_sup_pair hne (hHset g hg) (hHset₂ g hg)
    obtain ⟨-, hM0, -⟩ := c2_9_one hA3 h hT
    have hM0L : conjClosure L M = L := by
      rcases hM0 with hM0 | ⟨L₂, hL₂T, hL₂ne, hM0eq, -⟩
      · exact hM0
      · exfalso
        obtain ⟨t', ht', hteq⟩ := hL₂T
        have h₂ : L₂ = conjByElt t L := by
          rcases hHset t' (h.le_H (hT.1 ht')) with h₃ | h₃
          · exact absurd (hteq.trans h₃) hL₂ne
          · exact hteq.trans h₃
        apply hnn
        rw [hM0eq, h₂]
        exact fun g hg => C2Eleven.mem_normalizer_iff_conjByElt.mpr (hpair g hg)
    refine ⟨hM0L, hL, h12.symm, ?_⟩
    have hMeq : M = H ⊓ Subgroup.normalizer (L : Set G) := by
      have := h12.symm
      rwa [hM0L] at this
    have hmemM : ∀ g ∈ H, g ∈ M ↔ conjByElt g L = L := by
      intro g hg
      rw [hMeq, Subgroup.mem_inf, C2Eleven.mem_normalizer_iff_conjByElt]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    show (M.subgroupOf H).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htH⟩, fun b => ?_⟩
    have hb := b.2
    have h1 : b * ⟨t, htH⟩ ∈ M.subgroupOf H ↔ conjByElt (b : G) (conjByElt t L) = L := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmemM _ (H.mul_mem hb htH),
        C2Eleven.conjByElt_mul]
    have h2 : b ∈ M.subgroupOf H ↔ conjByElt (b : G) L = L := by
      rw [Subgroup.mem_subgroupOf, hmemM _ hb]
    rw [h1, h2]
    rcases hHset b hb with h3 | h3
    · have h4 : ¬ conjByElt (b : G) (conjByElt t L) = L := fun h4 =>
        hne (C2Thirteen.conjByElt_injective (b : G) (h4.trans h3.symm))
      exact Or.inr ⟨h3, h4⟩
    · have h4 : conjByElt (b : G) (conjByElt t L) = L := by
        rcases hHset₂ b hb with h5 | h5
        · exact h5
        · exact absurd (C2Thirteen.conjByElt_injective (b : G) (h3.trans h5.symm)) hne.symm
      have h5 : ¬ conjByElt (b : G) L = L := fun h5 => hne (h3.symm.trans h5)
      exact Or.inl ⟨h4, h5⟩

theorem c2_14 (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (hStep : ASC213Step G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) {H₁ : Subgroup G} (hH₁ : H₁ ≤ H) (hsolv : Group.IsSolvable ↥H₁)
    (hN : conjClosure L M ⊔ T ≤ Subgroup.normalizer (H₁ : Set G)) : H₁ ≤ M := by
  set M₀ := conjClosure L M with hM₀
  set H' := H₁ ⊔ (M₀ ⊔ T) with hH'
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hTM : T ≤ M := hT.1
  have hH'H : H' ≤ H := sup_le hH₁ (sup_le (hM₀M.trans h.le_H) (hTM.trans h.le_H))
  have hX : M₀ ⊔ T ≤ H' := le_sup_right
  have hH₁H' : H₁ ≤ H' := le_sup_left
  have hTH' : T ≤ H' := le_sup_right.trans hX
  have h' : HypC28 H' R (M ⊓ H') L V := c2_9_three hA3 h hT hRT hX hH'H
  have hT' : IsSylowTwoOf T (M ⊓ H') := B6.isSylowTwoOf_mono hT (le_inf hTM hTH') inf_le_left
  have hF : oTwoFstarIn H' ≤ M ⊓ H' :=
    C2Thirteen.oTwoFstarIn_le_of_solvable hC129 hC19 hA3 h hT hRT hH₁ hsolv hN
  rcases c2_13 hC129 hC111 hC19 hA3 hStep h' hT' hRT hF with hEq | ⟨hM0L, hLc, hMeq, -⟩
  · exact hH₁H'.trans (hEq.symm ▸ inf_le_left : H' ≤ M)
  · have hLN : L ≤ Subgroup.normalizer (H₁ : Set G) :=
      (le_conjClosure L M).trans (le_sup_left.trans hN)
    have hcomm := cComp_commutator_perfectCore hLc hH₁H' hsolv hLN
    have hH₁L : H₁ ≤ Subgroup.normalizer (L : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm.1
    rw [hM0L] at hMeq
    have : H₁ ≤ M ⊓ H' := by
      rw [hMeq]
      exact le_inf hH₁H' hH₁L
    exact this.trans inf_le_left

end CFSG.Quasithin
