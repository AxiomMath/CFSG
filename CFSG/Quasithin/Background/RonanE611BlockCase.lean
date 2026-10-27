module

public import CFSG.Quasithin.Background.RonanE611Defs
public import CFSG.Quasithin.Background.RonanE611Clause
public import CFSG.Quasithin.Background.RonanE611X
public import CFSG.Quasithin.Background.RonanE611Block

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6

section Generic

variable {G : Type} [Group G]

theorem list_prod_mem_mul {A L : Subgroup G} (hAL : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) :
    ∀ l : List G, (∀ g ∈ l, g ∈ A ∨ g ∈ L) → ∃ a ∈ A, ∃ ℓ ∈ L, l.prod = a * ℓ := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, A.one_mem, 1, L.one_mem, by simp⟩
  | cons g l ih =>
    intro hl
    obtain ⟨a', ha', ℓ', hℓ', hprod⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.prod_cons, hprod]
    rcases hl g List.mem_cons_self with hg | hg
    · exact ⟨g * a', A.mul_mem hg ha', ℓ', hℓ', by group⟩
    · refine ⟨a', ha', (a'⁻¹ * g * a') * ℓ', L.mul_mem ?_ hℓ', by group⟩
      have := hAL a'⁻¹ (A.inv_mem ha') g hg
      simpa using this

theorem inf_eq_inf_normalizer_of_block {H L M Q : Subgroup G} [Finite G]
    (hQH : IsSylowTwoOf Q H) (hQM : Q ≤ M) (hK : CharTwo H) (hL : IsBlock2 H L)
    {k : ℕ} (hk : 1 < k) (hlin : IsLin2Type L k)
    (hBor : IsBorelOfBlock L (L ⊓ (H ⊓ M))) :
    ∃ S : Subgroup G, IsSylowTwoOf S L ∧ L ⊓ M = L ⊓ Subgroup.normalizer (S : Set G) := by
  unfold IsBorelOfBlock at hBor
  split_ifs at hBor with h3
  · exact absurd h3 (card_quot_ne_three_of_lin2 hk hlin)
  obtain ⟨S, hS, hBS⟩ := hBor
  refine ⟨S, hS, ?_⟩
  have hLK : L ≤ H := hL.2.1
  have hOL : pCoreOf 2 L ≤ L ⊓ (H ⊓ M) := by
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 H :=
      Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hLK hL.2.2
    have h2 : pCoreOf 2 H ≤ Q := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQH
    exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 L)) (le_inf (((CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans hLK)
      ((h1.trans h2).trans hQM))
  rw [sup_eq_left.2 hOL] at hBS
  rw [← hBS]
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1, hLK hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩

end Generic


section Block

variable {G : Type} [Group G] [Finite G] {T M V U : Subgroup G}

theorem block_case (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h : E6.HypE61 T M V) (hU : U ∈ E6.gammaE64 V M)
    (hmax : ∀ W : Subgroup G, W ≤ V → U < W → Subgroup.centralizer (W : Set G) ≤ M)
    (hn : 1 < E3.mQuot V U) (hH : CharTwo (Subgroup.centralizer (U : Set G))) :
    ∃ L X : Subgroup G, Concl h U L X := by
  classical
  have hV := h.isElemAbelian
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax' : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M :=
    fun W h1 h2 => hmax W h2 h1
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hUV : U ≤ V := hU.1
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hCVM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le
  have hNH : ∀ g ∈ Subgroup.normalizer (U : Set G), g ∈ Subgroup.normalizer (H : Set G) :=
    fun g hg => B2F.le_normalizer_centralizer le_rfl hg
  have hCV : ∀ L : Subgroup G, L ≤ H → ¬ L ≤ M → V ⊓ Subgroup.centralizer (L : Set G) = U := by
    intro L hLH hLM
    have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun l hl =>
        (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
    by_contra hne
    have hlt : U < V ⊓ Subgroup.centralizer (L : Set G) := lt_of_le_of_ne hUC (Ne.symm hne)
    apply hLM
    refine le_trans (fun l hl => ?_) (hmax' _ hlt inf_le_left)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm
  have hVXL : ∀ L : Subgroup G, (∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)) →
      ⁅V, L ⊓ M⁆ ≤ L := fun L hVN =>
    commutator_le_of_normalizes hVN inf_le_left
  have hXU : ∀ L : Subgroup G, L ≤ H → L ⊓ M ≤ Subgroup.centralizer (U : Set G) :=
    fun L hLH => inf_le_left.trans hLH
  have hXN : ∀ L : Subgroup G, L ≤ H → L ⊓ M ≤ Subgroup.normalizer (V : Set G) :=
    fun L hLH y hy => hHMN ⟨hLH hy.1, hy.2⟩
  have hcgs : cgsIn H Q ≤ H ⊓ M := (e6_5_two h hU).1
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hH
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQH.1.trans h1)
  have hsq : IsSQTKIn H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G H Q (H ⊓ M) hsq hH hQH hcgs inf_le_left
  obtain ⟨i, hiM⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hU.2.2.1
    intro y hy
    obtain ⟨m, hm, z, hz, rfl⟩ := hprod y hy
    refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun w hw => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hw
    exact hall j (hz j)
  obtain ⟨⟨hL, htype⟩, hBor, hJ⟩ := hLb i
  set L := Lb i with hLdef
  have hLH : L ≤ H := hL.2.1
  have hCL := hCV L hLH hiM
  have hVL : ¬ V ≤ Subgroup.centralizer (L : Set G) := by
    intro hVC
    have h1 := hCL
    rw [inf_eq_left.2 hVC] at h1
    rw [← h1, E3.mQuot_self] at hn
    exact absurd hn (by norm_num)
  rcases htype with ⟨k, hk, hlin⟩ | h3 | h5
  · obtain ⟨hVN, hidx, x, hx, hxj, hall, hker2, -⟩ := lin2_block_torus'' hV h.le hQH
      (inf_le_left.trans h.inM.2) hHMN hH hL hk hlin hBor hVL
    rw [hCL, E3.relIndex_eq_two_pow hV2] at hidx
    have hkn : E3.mQuot V U = k := Nat.pow_right_injective (le_refl 2) hidx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hHMN hx.2
    set ξ := convI hV ⟨x, hxN⟩ with hξdef
    have hξpow : ∀ j : ℕ, ξ ^ j = 1 ↔ (2 ^ k - 1) ∣ j := by
      intro j
      rw [← hxj j, hξdef, ← map_pow, convI_eq_one_iff]
      simp only [Subgroup.coe_pow]
    have hξord : orderOf ξ = 2 ^ k - 1 :=
      Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hξpow _).2 dvd_rfl))
        ((hξpow _).1 (pow_orderOf_eq_one ξ))
    have hXeq : autI hV (L ⊓ M) = Subgroup.zpowers ξ := by
      apply le_antisymm
      · intro φ hφ
        obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).1 hφ
        obtain ⟨j, hj⟩ := hall g ⟨hgX.1, hLH hgX.1, hgX.2⟩
        refine Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), ?_⟩
        rw [zpow_natCast, hξdef, ← map_pow]
        have h1 : convI hV (g * (⟨x, hxN⟩ ^ j)⁻¹) = 1 := (convI_eq_one_iff hV _).2
          (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
            Subgroup.coe_mk] using hj)
        rw [map_mul, map_inv, mul_inv_eq_one] at h1
        exact h1.symm
      · rw [Subgroup.zpowers_le]
        exact convI_mem_autI hV (show x ∈ L ⊓ M from ⟨hx.1, hx.2.2⟩) hxN
    have hcyc : IsCyclic (autI hV (L ⊓ M)) := by
      rw [hXeq]
      infer_instance
    have hcard : Nat.card (autI hV (L ⊓ M)) = 2 ^ E3.mQuot V U - 1 := by
      rw [hXeq, Nat.card_zpowers, hξord, hkn]
    obtain ⟨hinf, hsup, hreg⟩ :=
      singer_autI hV hUV hn (hXU L hLH) (hXN L hLH) hcyc hcard
    have hdich : ∀ g ∈ Subgroup.normalizer (H : Set G),
        CFSG.conjugate L g = L ∨ ⁅L, CFSG.conjugate L g⁆ = ⊥ := by
      intro g hg
      by_cases he : CFSG.conjugate L g = L
      · exact Or.inl he
      · exact Or.inr (distinctBlocksCommuteStatement H L (CFSG.conjugate L g) hH hL
          (isBlock2_conjugate_of_mem_normalizer hL hg) (Ne.symm he))
    have hNL : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G),
        g ∈ Subgroup.normalizer (U : Set G) → g ∈ Subgroup.normalizer (L : Set G) :=
      fun g hg hgU => mem_normalizer_of_eq_or_commute hCVM hLH hiM (hVXL L hVN) hsup hg.1 hgU
        (hdich g (hNH g hgU))
    have hLn : (L.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLH]
      intro y hy
      obtain ⟨m, hm, z, hz, rfl⟩ := hprod y hy
      refine Subgroup.mul_mem _ (hNL m ⟨hm.2, hHMN hm⟩
        (Subgroup.centralizer_le_normalizer _ hm.1))
        (Subgroup.list_prod_mem (K := Subgroup.normalizer (L : Set G)) fun w hw => ?_)
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hw
      by_cases hj : Lb j = L
      · exact Subgroup.le_normalizer (hj ▸ hz j)
      · have hc := distinctBlocksCommuteStatement H (Lb j) L hH (hLb j).1.1 hL hj
        exact Subgroup.centralizer_le_normalizer _
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc (hz j))
    have hkerp : ∀ p : ℕ, p.Prime → p ∣ 2 ^ E3.mQuot V U - 1 →
        ¬ p ∣ Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G)) := by
      intro p hp hpd hpK
      have h2grp : IsPGroup 2 ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G)) := by
        intro g
        obtain ⟨j, hj⟩ := hker2 g ⟨g.2.1.1, hLH g.2.1.1, g.2.1.2⟩ g.2.2
        exact ⟨j, Subtype.ext (by simpa using hj)⟩
      obtain ⟨a, ha⟩ := h2grp.exists_card_eq
      rw [ha] at hpK
      have hp2 : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpK)
      rw [hp2] at hpd
      have h4 : 4 ≤ 2 ^ E3.mQuot V U :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hn
      have he : Even (2 ^ E3.mQuot V U) := (Nat.even_pow' (by omega)).2 even_two
      have hodd : Odd (2 ^ E3.mQuot V U - 1) := Nat.Even.sub_odd (by omega) he odd_one
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpd)
    obtain ⟨X, hXLM, hXc, hXcard, hautX⟩ := exists_X_of_coprime hV (hXN L hLH) hcyc
      (fun p hp hpd => hkerp p hp (hcard ▸ hpd))
    rw [hcard] at hXcard
    obtain ⟨hinf2, hsup2, hXLM', hXc', hXcard', hne, hfree, htrans, hnorm, hle⟩ :=
      clause_two h hU hn hXLM hLH hXc hXcard hautX hcyc hcard hNL
    have hXL : X ≤ L := fun x hx => (hXLM' hx).1
    have hVXL' : ⁅V, X⁆ ≤ L := commutator_le_of_normalizes hVN hXL
    have hother : ∀ j, Lb j = L ∨ Lb j ≤ M := by
      intro j
      by_cases hj : Lb j = L
      · exact Or.inl hj
      · right
        by_contra hjM
        have hLjH : Lb j ≤ H := (hLb j).1.1.2.1
        have hc : ⁅Lb j, L⁆ = ⊥ := distinctBlocksCommuteStatement H (Lb j) L hH (hLb j).1.1 hL hj
        have hLjL : Lb j ≤ Subgroup.centralizer (L : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
        have hLjV : Lb j ≤ Subgroup.centralizer (V : Set G) := by
          rw [Subgroup.le_centralizer_iff, ← hsup2]
          refine sup_le ?_ ?_
          · exact Subgroup.le_centralizer_iff.1 hLjH
          · exact Subgroup.le_centralizer_iff.1 (hLjL.trans (Subgroup.centralizer_le hVXL'))
        exact hjM (hLjV.trans hCVM)
    have hAL : ∀ a ∈ H ⊓ M, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
      (Subgroup.mem_normalizer_iff.1 (hNL a ⟨ha.2, hHMN ha⟩
        (Subgroup.centralizer_le_normalizer _ ha.1)) l).1 hl
    have hprodset : ((H ⊓ M : Subgroup G) : Set G) * (L : Set G) = (H : Set G) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨a, ha, l, hl, rfl⟩
        exact H.mul_mem ha.1 (hLH hl)
      · intro y hy
        obtain ⟨m, hm, z, hz, rfl⟩ := hprod y hy
        obtain ⟨a, ha, ℓ, hℓ, hlist⟩ := list_prod_mem_mul hAL (List.ofFn z) (by
          intro g hg
          obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
          rcases hother j with hj | hj
          · exact Or.inr (hj ▸ hz j)
          · exact Or.inl ⟨(hLb j).1.1.2.1 (hz j), hj (hz j)⟩)
        refine ⟨m * a, (H ⊓ M).mul_mem hm ha, ℓ, hℓ, ?_⟩
        rw [hlist]
        group
    obtain ⟨S, hSsyl, hSeq⟩ := inf_eq_inf_normalizer_of_block hQH (inf_le_right.trans hCVM) hH hL
      hk hlin hBor
    have hidx' : M.relIndex L = 2 ^ E3.mQuot V U + 1 := by
      rw [← Subgroup.inf_relIndex_right, inf_comm M L, hSeq, relIndex_normalizer_of_lin2 hlin hSsyl,
        hkn]
    refine ⟨L, X, ⟨hLH, hLn, hprodset⟩,
      ⟨hinf2, hsup2, hXLM', hXc', hXcard', hne, hfree, htrans, hnorm, hle⟩,
      Or.inl ⟨hH, hL, hkn ▸ hlin, hidx'⟩, clause_four h hsup2 hVN hXL⟩
  · exfalso
    have h1 := relIndex_le_two_of_alt3 hH hL h3 hQH hJ.symm hVQ hQV
    rw [hCL] at h1
    have := mQuot_le_one_of_relIndex_le_two hV2 h1
    omega
  · exfalso
    have h1 := relIndex_le_two_of_alt5 hH hL h5 hQH hVQ hQV
    rw [hCL] at h1
    have := mQuot_le_one_of_relIndex_le_two hV2 h1
    omega

end Block

end CFSG.Quasithin.RonanE611
