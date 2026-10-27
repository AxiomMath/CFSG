module

public import CFSG.Quasithin.Background.E6TwentyFiveA
public import CFSG.Quasithin.Background.E6ElevenSinger
public import CFSG.Quasithin.Background.E6ElevenComp
public import CFSG.Quasithin.Background.E6EightBorel
public import CFSG.Quasithin.Background.E6EightStmt

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Singer

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

omit [Finite G] in
theorem map_valHom_commSub_eq (hV : CFSG.Open.IsElemAbelian 2 V) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) :
    (commSub ⊤ (autI hV X)).map (E3.valHom hV) = ⁅V, X⁆ := by
  refine le_antisymm (map_valHom_commSub_le hV X) ?_
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hξ : convI hV ⟨x, hXN hx⟩ ∈ autI hV X := convI_mem_autI hV hx (hXN hx)
  set w : IntMod V hV := IntMod.mk hV ⟨v⁻¹, V.inv_mem hv⟩ with hw
  refine ⟨convI hV ⟨x, hXN hx⟩ w * w⁻¹,
    Subgroup.subset_closure ⟨_, hξ, w, Subgroup.mem_top w, rfl⟩, ?_⟩
  have hxv : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXN hx) v⁻¹).1 (V.inv_mem hv)
  have hc : x * v⁻¹ * x⁻¹ * v = v * (x * v⁻¹ * x⁻¹) := B2F.isElemAbelian_comm hV hxv hv
  rw [map_mul, map_inv, E3.valHom_apply, E3.valHom_apply, convI_apply_val, commutatorElement_def]
  show x * v⁻¹ * x⁻¹ * (v⁻¹)⁻¹ = v * x * v⁻¹ * x⁻¹
  rw [inv_inv, hc]
  group

theorem singer_autI {U X : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (hUV : U ≤ V)
    (hn : 1 < E3.mQuot V U) (hXU : X ≤ Subgroup.centralizer (U : Set G))
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hXc : IsCyclic (autI hV X))
    (hXcard : Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1) :
    U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧
      ∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v = v * x →
        x ∈ Subgroup.centralizer (V : Set G) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  obtain ⟨ξ, hξ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (autI hV X)).1 hXc
  have hord : orderOf ξ = 2 ^ E3.mQuot V U - 1 := by
    rw [← Nat.card_zpowers, hξ, hXcard]
  set U' : Subgroup (IntMod V hV) := U.comap (E3.valHom hV) with hU'def
  have hU'map : U'.map (E3.valHom hV) = U :=
    Subgroup.map_comap_eq_self fun u hu => ⟨IntMod.mk hV ⟨u, hUV hu⟩, rfl⟩
  have hU'fix : U' ≤ fixV (Subgroup.zpowers ξ) := by
    intro w hw
    rw [hξ, mem_fixV_autI hV hXN w]
    exact Subgroup.le_centralizer_iff.1 hXU (Subgroup.mem_comap.1 hw)
  have hU'idx : U'.index = 2 ^ E3.mQuot V U := by
    rw [B1.index_eq_two_pow hW U', E3.rkIdx_eq_mQuot_map hV U', hU'map]
  obtain ⟨hfix, -, hreg⟩ := singer hW hn hord hU'fix hU'idx
  rw [hξ] at hfix hreg
  have hodd : Odd (Nat.card (autI hV X)) := by
    rw [hXcard]
    have h4 : 4 ≤ 2 ^ E3.mQuot V U :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hn
    have he : Even (2 ^ E3.mQuot V U) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  have hdec1 := Asc81c.fixV_inf_commSub_eq_bot' hW hodd
  have hdec2 := Asc81c.fixV_sup_commSub_eq_top' hW hodd
  have hcomm := map_valHom_commSub_eq hV hXN
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgU, hgc⟩
    rw [← hcomm] at hgc
    obtain ⟨c, hc, rfl⟩ := hgc
    have hcF : c ∈ fixV (autI hV X) ⊓ commSub ⊤ (autI hV X) :=
      ⟨by rw [hfix]; exact Subgroup.mem_comap.2 hgU, hc⟩
    rw [hdec1, Subgroup.mem_bot] at hcF
    rw [hcF, map_one]
    exact Subgroup.one_mem _
  · refine le_antisymm (sup_le hUV ?_) fun v hv => ?_
    · rw [← hcomm]
      exact E3.map_valHom_le hV _
    · have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (autI hV X) ⊔ commSub ⊤ (autI hV X) := by
        rw [hdec2]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hw
      have hv' : v = E3.valHom hV a * E3.valHom hV b := by
        rw [← map_mul, hab]
        rfl
      rw [hv']
      refine Subgroup.mul_mem_sup ?_ ?_
      · rw [hfix] at ha
        exact Subgroup.mem_comap.1 ha
      · rw [← hcomm]
        exact ⟨b, hb, rfl⟩
  · intro v hv hv1 x hx hxv
    rw [← hcomm] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    have hc1 : c ≠ 1 := fun h0 => hv1 (by rw [h0, map_one])
    have hfixc : convI hV ⟨x, hXN hx⟩ c = c := by
      apply IntMod.val_injective
      rw [convI_apply_val]
      rw [E3.valHom_apply] at hxv
      show x * c.val * x⁻¹ = c.val
      rw [hxv, mul_inv_cancel_right]
    exact (convI_eq_one_iff hV _).1
      (hreg c hc hc1 _ (convI_mem_autI hV hx (hXN hx)) hfixc)

end Singer

section Conj

variable {G : Type} [Group G]

theorem isBlock2_conjugate_of_mem_normalizer {H B : Subgroup G} (hB : IsBlock2 H B) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : IsBlock2 H (CFSG.conjugate B g) := by
  have h := Setup.Campbell.isBlock2_map_conj hB g⁻¹
  have hH : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg
  rw [hH] at h
  exact h

theorem isComponentIn_conjugate_of_mem_normalizer' {H L : Subgroup G} (hL : IsComponentIn L H)
    {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsComponentIn (CFSG.conjugate L g) H := by
  have h := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hL
  have hH : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg
  rw [hH] at h
  exact h

theorem mem_normalizer_of_eq_or_commute {M V U L W : Subgroup G} {g : G}
    (hCV : Subgroup.centralizer (V : Set G) ≤ M) (hLU : L ≤ Subgroup.centralizer (U : Set G))
    (hLM : ¬ L ≤ M) (hWL : W ≤ L) (hUW : U ⊔ W = V) (hgM : g ∈ M)
    (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hdich : CFSG.conjugate L g = L ∨ ⁅L, CFSG.conjugate L g⁆ = ⊥) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rcases hdich with he | hc
  · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 he
  · exfalso
    apply hLM
    have hLgU : CFSG.conjugate L g ≤ Subgroup.centralizer (U : Set G) := by
      have h1 := BenderBranch.conjugate_mono hLU g
      rwa [BenderBranch.conjugate_centralizer,
        BenderBranch.conjugate_eq_iff_mem_normalizer.2 hgU] at h1
    have hLgW : CFSG.conjugate L g ≤ Subgroup.centralizer (W : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [Subgroup.commutator_comm]; exact hc)).trans (Subgroup.centralizer_le hWL)
    have hLgV : CFSG.conjugate L g ≤ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← hUW]
      exact sup_le (Subgroup.le_centralizer_iff.1 hLgU) (Subgroup.le_centralizer_iff.1 hLgW)
    intro l hl
    have hl' : g⁻¹ * l * g ∈ CFSG.conjugate L g :=
      BenderBranch.mem_conjugate_iff.2 (by rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]; exact hl)
    have hm := hCV (hLgV hl')
    have he : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
    rw [he]
    exact M.mul_mem (M.mul_mem hgM hm) (M.inv_mem hgM)

end Conj

section Main

variable {G : Type} [Group G]

abbrev E611TypeBender (L : Subgroup G) (n : ℕ) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 n ∨
    CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n ∨
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n

abbrev E611TypeLie (L : Subgroup G) (n : ℕ) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n ∨
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n

theorem not_dvd_card_inf_centralizer_of_borel [Finite G] (hBK : E68BorelKernel)
    {V L M Q : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) {n : ℕ} (hn : 2 ≤ n)
    (htype : E611TypeBender L n) (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hS : IsSylowTwoOf (Q ⊓ L) L)
    (hBor : L ⊓ M = L ⊓ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G))
    (hN : L ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1) :
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
      ¬ p ∣ Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G)) := by
  intro p hp hpd hpK
  have : Fact p.Prime := ⟨hp⟩
  have hS' : IsSylowTwoOf ((Q ⊓ L).subgroupOf L) ⊤ := SBc5.isSylowTwoOf_subgroupOf_top hS
  have h2 := hBK ↥L n hn htype hZ _ hS' p hp hpd
  have h3 : Nat.card (Subgroup.normalizer (((Q ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L)) =
      Nat.card ↥(L ⊓ M) := by
    rw [hBor, ← map_subtype_normalizer (inf_le_right : Q ⊓ L ≤ L),
      Subgroup.card_map_of_injective L.subtype_injective]
  have h1 := card_autI_mul_card_inf hV hN
  rw [h3, ← h1, hcard] at h2
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos1 : 2 ^ n - 1 ≠ 0 := by omega
  have hpos2 : Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G)) ≠ 0 := Nat.card_pos.ne'
  rw [padicValNat.mul hpos1 hpos2] at h2
  have h5 := one_le_padicValNat_of_dvd hpos2 hpK
  omega

theorem e611Data_of {M V U L : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hLH : L ≤ Subgroup.centralizer (U : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal) (hLM : ¬ L ≤ M)
    (hCL : V ⊓ Subgroup.centralizer (L : Set G) = U) (hcyc : IsCyclic (autI hV (L ⊓ M)))
    (hcard : Nat.card (autI hV (L ⊓ M)) = 2 ^ E3.mQuot V U - 1)
    (hinf : U ⊓ ⁅V, L ⊓ M⁆ = ⊥) (hsup : U ⊔ ⁅V, L ⊓ M⁆ = V)
    (hreg : ∀ v ∈ ⁅V, L ⊓ M⁆, v ≠ 1 → ∀ x ∈ L ⊓ M, x * v = v * x →
      x ∈ Subgroup.centralizer (V : Set G))
    (hNL : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      g ∈ Subgroup.normalizer (L : Set G))
    (htype : (((IsBlock2 (Subgroup.centralizer (U : Set G)) L ∧ IsLin2Type L (E3.mQuot V U)) ∨
        (IsComponentIn L (Subgroup.centralizer (U : Set G)) ∧ E611TypeBender L (E3.mQuot V U))) ∧
        ∀ p : ℕ, p.Prime → p ∣ 2 ^ E3.mQuot V U - 1 →
          ¬ p ∣ Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G))) ∨
      (IsComponentIn L (Subgroup.centralizer (U : Set G)) ∧ E611TypeLie L (E3.mQuot V U))) :
    E611Data hV M U L (L ⊓ M) := by
  refine ⟨hLH, hLn, hLM, hCL, le_rfl, hcyc, hcard, hinf, hsup, hreg, ?_, hNL, le_rfl, htype⟩
  intro g hg hgU x hx
  have hgL := hNL g hg hgU
  refine ⟨g * x * g⁻¹, ⟨(Subgroup.mem_normalizer_iff.1 hgL x).1 hx.1,
    M.mul_mem (M.mul_mem hg.1 hx.2) (M.inv_mem hg.1)⟩, ?_⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem e611Strong_of (h68 : E68Stmt)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hBK : E68BorelKernel) :
    E611Strong := by
  intro G _ _ T M V U hV h hU hmax hn
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hUV : U ≤ V := hU.1
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hVH : V ≤ H := hVQ.trans hQH.1
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hCVM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le
  have hO : oddCoreIn H = ⊥ := oddCoreIn_eq_bot_of_maximal h hU hmax hn
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
    refine le_trans (fun l hl => ?_) (hmax _ hlt inf_le_left)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm
  have hVXL : ∀ L : Subgroup G, (∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G)) →
      ⁅V, L ⊓ M⁆ ≤ L := by
    intro L hVN
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVN v hv) x).1 hx.1) (L.inv_mem hx.1)
  have hXU : ∀ L : Subgroup G, L ≤ H → L ⊓ M ≤ Subgroup.centralizer (U : Set G) :=
    fun L hLH => inf_le_left.trans hLH
  have hXN : ∀ L : Subgroup G, L ≤ H → L ⊓ M ≤ Subgroup.normalizer (V : Set G) :=
    fun L hLH y hy => hHMN ⟨hLH hy.1, hy.2⟩
  by_cases hH : CharTwo H
  ·
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
      exact ⟨L, L ⊓ M, e611Data_of hV hLH hLn hiM hCL hcyc hcard hinf hsup hreg hNL
        (Or.inl ⟨Or.inl ⟨hL, by rw [hkn]; exact hlin⟩, hkerp⟩)⟩
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
  ·
    obtain ⟨L, hL⟩ : ∃ L : Subgroup G, IsComponentIn L H := by
      by_contra hno
      push Not at hno
      exact hH (DoubleA3.charTwo_of_no_component hno hO)
    obtain ⟨hLM, hcases⟩ := h68 G T M V U L hV h hU hL
    have hLH : L ≤ H := hL.1
    have hCL := hCV L hLH hLM
    have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQH hLH hL.2.2
    obtain ⟨hcyc, hcard, htype⟩ : IsCyclic (autI hV (L ⊓ M)) ∧
        Nat.card (autI hV (L ⊓ M)) = 2 ^ E3.mQuot V U - 1 ∧
        ((E611TypeBender L (E3.mQuot V U) ∧ ∀ p : ℕ, p.Prime → p ∣ 2 ^ E3.mQuot V U - 1 →
            ¬ p ∣ Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G))) ∨
          E611TypeLie L (E3.mQuot V U)) := by
      unfold E68Case1 E68Case2 E68Case3 E68Case4 E68Case5 at hcases
      rw [hCL] at hcases
      rcases hcases with ⟨k, htype, hZ, hBor, hcyc, hcard, hk, -, -⟩ |
          ⟨k, -, htype, -, -, ⟨-, ⟨-, A, hUA, hAV, -, hAM⟩ | ⟨-, h1⟩⟩ | ⟨-, -, -, hk, hcyc⟩⟩ |
          ⟨-, -, -, h1, -⟩ | ⟨-, ⟨A, hUA, hAV, hA1, hAM⟩, -, -⟩ | ⟨-, -, h1, -⟩
      · subst hk
        have hn2 : 2 ≤ E3.mQuot V U := hn
        refine ⟨hcyc, hcard, ?_⟩
        have hker := fun (ht : E611TypeBender L (E3.mQuot V U)) =>
          not_dvd_card_inf_centralizer_of_borel hBK hV hn2 ht hZ hSL hBor (hXN L hLH) hcard
        rcases htype with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl ⟨Or.inl h, hker (Or.inl h)⟩
        · exact Or.inl ⟨Or.inr (Or.inl h), hker (Or.inr (Or.inl h))⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl ⟨Or.inr (Or.inr h), hker (Or.inr (Or.inr h))⟩
      · exact absurd (hmax A hUA hAV.le) fun hle => hAM (inf_le_right.trans hle)
      · omega
      · subst hk
        obtain ⟨hcyc', hcard'⟩ := hcyc hn
        refine ⟨hcyc', hcard', Or.inr (Or.inr ?_)⟩
        rcases htype with ⟨-, h⟩ | ⟨h1, -⟩
        · exact h
        · omega
      · omega
      · have hne : U ≠ A := fun he => by rw [he, hA1] at hn; exact lt_irrefl 1 hn
        exact absurd (hmax A (lt_of_le_of_ne hUA hne) hAV) fun hle => hAM (inf_le_right.trans hle)
      · omega
    obtain ⟨hinf, hsup, hreg⟩ := singer_autI hV hUV hn (hXU L hLH) (hXN L hLH) hcyc hcard
    have hcoreH : CFSG.pPrimeCore 2 ↥H = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn' hO
    have hQ2' : IsPGroup 2 (Q.subgroupOf H) :=
      hQH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH.1).symm
    set P : Sylow 2 ↥H := hQ2'.toSylow hQH.2.2 with hPdef
    have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := by
      intro v hv
      have hvz : (⟨v, hVH hv⟩ : ↥H) ∈ Subgroup.centralizer ((P : Subgroup ↥H) : Set ↥H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subtype.ext
          (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) v hv).symm
      have hvzS : (⟨v, hVH hv⟩ : ↥H) ∈ (P : Subgroup ↥H) := show v ∈ Q from hVQ hv
      have hnorm := central_sylow_normalizes_components hcoreH P hvz hvzS hL.2
      have h2 : v ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H)).map
          H.subtype := ⟨_, hnorm, rfl⟩
      rw [map_subtype_normalizer hL.1] at h2
      exact h2.2
    have hdich : ∀ g ∈ Subgroup.normalizer (H : Set G),
        CFSG.conjugate L g = L ∨ ⁅L, CFSG.conjugate L g⁆ = ⊥ := fun g hg =>
      (BenderBranch.eq_or_commute_of_isComponentIn hL
        (isComponentIn_conjugate_of_mem_normalizer' hL hg)).imp Eq.symm id
    have hNL : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G),
        g ∈ Subgroup.normalizer (U : Set G) → g ∈ Subgroup.normalizer (L : Set G) :=
      fun g hg hgU => mem_normalizer_of_eq_or_commute hCVM hLH hLM (hVXL L hVN) hsup hg.1 hgU
        (hdich g (hNH g hgU))
    have hLn : (L.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLH]
      intro y hy
      have hyN : y ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hy
      rcases hdich y hyN with he | hc
      · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 he
      · exfalso
        have hLy := isComponentIn_conjugate_of_mem_normalizer' hL hyN
        have hLyU : CFSG.conjugate L y ≤ H := hLy.1
        have hLyW : CFSG.conjugate L y ≤
            Subgroup.centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (by rw [Subgroup.commutator_comm]; exact hc)).trans
            (Subgroup.centralizer_le (hVXL L hVN))
        have hLyV : CFSG.conjugate L y ≤ Subgroup.centralizer (V : Set G) := by
          rw [Subgroup.le_centralizer_iff, ← hsup]
          exact sup_le (Subgroup.le_centralizer_iff.1 hLyU) (Subgroup.le_centralizer_iff.1 hLyW)
        exact DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) _
          (BenderBranch.isComponentIn_of_le hLy (le_inf (hLyV.trans hCVM) hLyU) inf_le_right)
    exact ⟨L, L ⊓ M, e611Data_of hV hLH hLn hLM hCL hcyc hcard hinf hsup hreg hNL
      (htype.imp (fun ht => ⟨Or.inr ⟨hL, ht.1⟩, ht.2⟩) (fun ht => ⟨hL, ht⟩))⟩

end Main

end E6

end CFSG.Quasithin
