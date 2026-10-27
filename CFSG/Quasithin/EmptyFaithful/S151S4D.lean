module

public import CFSG.Quasithin.EmptyFaithful.S151S4C
public import CFSG.Quasithin.EmptyFaithful.S151ZD
public import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.Quasithin.S151S4

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sylow_sup_of_normalizes [Finite G] {L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hS2 : IsPGroup 2 ↥S) (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf S (L ⊔ S) := by
  have e1 := zb_relIndex_sup hSN
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ L) L (L ⊔ S) inf_le_right le_sup_left
  have e3 := Subgroup.relIndex_mul_relIndex (S ⊓ L) S (L ⊔ S) inf_le_left le_sup_right
  have e4 : (S ⊓ L).relIndex S = L.relIndex S := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right L S
  have hr : L.relIndex S ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card L S
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥S)).ne' h1.symm
  have e5 : S.relIndex (L ⊔ S) = (S ⊓ L).relIndex L := by
    rw [e1] at e2
    rw [e4] at e3
    have : (S ⊓ L).relIndex L * L.relIndex S = L.relIndex S * S.relIndex (L ⊔ S) := by
      rw [e2, e3]
    rw [mul_comm (L.relIndex S)] at this
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr) this).symm
  refine ⟨le_sup_right, hS2, ?_⟩
  have h3 : (S.subgroupOf (L ⊔ S)).index = (S ⊓ L).relIndex L := e5
  rw [h3]
  exact hsyl.2.2

theorem l2_isMinParabolic [Finite G] {L S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    IsMinParabolicOf (L ⊔ S) (L ⊔ S) := by
  obtain ⟨Bor, hBorL, hBBor, hBorne, hmax, hnn⟩ := l2_rank_one hn hL hsyl
  have hSH : IsSylowTwoOf S (L ⊔ S) := sylow_sup_of_normalizes hSN hS2 hsyl
  have hSB : ∀ s ∈ S, s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hconj : ∀ s ∈ S, ∀ x ∈ Bor, s * x * s⁻¹ ∈ Bor := by
    intro s hs
    have hKL : B6.conjSub s Bor ≤ L := by
      intro x hx
      have h1 : s⁻¹ * x * s ∈ Bor := B6.mem_conjSub.mp hx
      have h2 : s * (s⁻¹ * x * s) * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hSN hs) (s⁻¹ * x * s)).mp (hBorL h1)
      simpa [mul_assoc] using h2
    have hBK : S ⊓ L ≤ B6.conjSub s Bor := by
      intro b hb
      refine B6.mem_conjSub.mpr (hBBor ?_)
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hSB s hs)) b).mp hb
      simpa using this
    rcases hmax _ hBK hKL with h | h
    · intro x hx
      have : s * x * s⁻¹ ∈ B6.conjSub s Bor := B6.mem_conjSub.mpr (by simpa [mul_assoc] using hx)
      exact h this
    · exfalso
      apply hBorne
      refine le_antisymm hBorL (fun y hy => ?_)
      have hy' : s * y * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSN hs) y).mp hy
      have : s * y * s⁻¹ ∈ B6.conjSub s Bor := h ▸ hy'
      simpa [mul_assoc] using B6.mem_conjSub.mp this
  have hSBor : S ≤ Subgroup.normalizer (Bor : Set G) := fun s hs =>
    B6.mem_normalizer_of_forall_mem (hconj s hs) (fun x hx => by
      simpa using hconj s⁻¹ (S.inv_mem hs) x hx)
  have hX_le : Bor ⊔ S ≤ L ⊔ S := sup_le (hBorL.trans le_sup_left) le_sup_right
  have hXne : Bor ⊔ S ≠ L ⊔ S := by
    intro hXeq
    apply hBorne
    refine le_antisymm hBorL (fun l hl => ?_)
    have hl' : l ∈ Bor ⊔ S := hXeq ▸ Subgroup.mem_sup_left hl
    obtain ⟨b, hb, s, hs, hbs⟩ := zb_mem_sup hSBor hl'
    have hsL : s ∈ L := by
      have : s = b⁻¹ * l := by rw [hbs]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hBorL hb)) hl
    have hsBor : s ∈ Bor := hBBor ⟨hs, hsL⟩
    rw [hbs]
    exact Bor.mul_mem hb hsBor
  have hXH : Bor ⊔ S < L ⊔ S := lt_of_le_of_ne hX_le hXne
  have hmaxX : ∀ Y : Subgroup G, S ≤ Y → Y < L ⊔ S → Y ≤ Bor ⊔ S := by
    intro Y hSY hYH
    have hY1 : Y ⊓ L ≤ Bor := by
      rcases hmax (Y ⊓ L) (le_inf (inf_le_left.trans hSY) inf_le_right) inf_le_right with h | h
      · exact h
      · exfalso
        have hLY : L ≤ Y := by
          intro x hx
          have hx' : x ∈ Y ⊓ L := by
            rw [h]
            exact hx
          exact hx'.1
        exact absurd (sup_le hLY hSY) (not_le_of_gt hYH)
    intro y hy
    obtain ⟨l, hl, s, hs, rfl⟩ := zb_mem_sup hSN (hYH.le hy)
    have hlY : l ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem (hSY hs))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hY1 ⟨hlY, hl⟩)) (Subgroup.mem_sup_right hs)
  have hnn' : ¬ (L ⊔ S) ≤ Subgroup.normalizer (S : Set G) := by
    intro hH
    apply hnn
    intro l hl
    exact zb_mem_normalizer_inf (hH (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  have hmaxX' : IsMaxSubgroupIn (L ⊔ S) (Bor ⊔ S) := by
    refine ⟨hXH, fun K hXK hKH => ?_⟩
    by_contra hne
    exact absurd (hmaxX K (le_sup_right.trans hXK.le) (lt_of_le_of_ne hKH hne)) (not_le_of_gt hXK)
  have huniq : IsUniqueMaxOver (L ⊔ S) S (Bor ⊔ S) := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmaxX', le_sup_right⟩, fun N hN => ?_⟩
    have hNX : N ≤ Bor ⊔ S := hmaxX N hN.2 hN.1.1
    by_contra hne
    exact absurd (hN.1.2 _ (lt_of_le_of_ne hNX hne) hXH.le) (ne_of_lt hXH)
  exact (minParabolic_iff.mp ⟨hSH, hnn', huniq⟩).1

theorem isPerfect_of_commutator_eq' {L : Subgroup G} (h : ⁅L, L⁆ = L) : Group.IsPerfect ↥L := by
  rw [Group.isPerfect_def]
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (commutator ↥L).map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
    rw [h1, h, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective L.subtype_injective h2

theorem twoResidual_eq_self_of_perfect [Finite G] {L : Subgroup G} (h : ⁅L, L⁆ = L) :
    twoResidual L = L := by
  have hp : Group.IsPerfect ↥L := isPerfect_of_commutator_eq' h
  have hpt : Group.IsPerfect ↥(⊤ : Subgroup ↥L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥L) ≃* ↥L).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  have htop : twoResidual (⊤ : Subgroup ↥L) = ⊤ := top_le_iff.mp (B6.perfect_le_twoResidual (P := ⊤))
  rw [E1.twoResidual_eq_map_top L, htop, Subgroup.map_top, Subgroup.range_subtype]

theorem twoResidual_sup_eq_self [Finite G] {L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hS2 : IsPGroup 2 ↥S) (hperf : ⁅L, L⁆ = L) : twoResidual (L ⊔ S) = L := by
  apply le_antisymm
  · exact twoResidual_le_of_isTwoQuotient le_sup_left (sup_le Subgroup.le_normalizer hSN)
      (zb_two_pow hSN hS2)
  · calc L = twoResidual L := (twoResidual_eq_self_of_perfect hperf).symm
      _ ≤ twoResidual (L ⊔ S) := E1.twoResidual_mono le_sup_left

theorem isShort2_of_c126Third [Finite G] {L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hS2 : IsPGroup 2 ↥S) (hperf : ⁅L, L⁆ = L) (hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (h3 : C126Third (L ⊔ S) S) : IsShort2 L := by
  obtain ⟨r, K, hr, hblock, hcomm, hres, -, -⟩ := h3
  rw [twoResidual_sup_eq_self hSN hS2 hperf] at hres
  have hKL : ∀ i, K i ≤ L := fun i => by
    calc K i ≤ ⨆ j, K j := le_iSup K i
      _ = L := hres.symm
  have hKN : ∀ i, L ≤ Subgroup.normalizer (K i : Set G) := by
    intro i
    calc L = ⨆ j, K j := hres
      _ ≤ Subgroup.normalizer (K i : Set G) := by
        refine iSup_le fun j => ?_
        by_cases hij : j = i
        · subst hij
          exact Subgroup.le_normalizer
        · have hc : ⁅K j, K i⁆ = ⊥ := hcomm j i hij
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
            (Subgroup.centralizer_le_normalizer _)
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hex : ∃ i, ((K i).subgroupOf L).map π = ⊤ := by
    by_contra hne
    push Not at hne
    have hcen : ∀ i, ((K i).subgroupOf L).map π ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro i
      have hnorm : ((K i).subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hKL i)).mpr (hKN i)
      have hmn : (((K i).subgroupOf L).map π).Normal := hnorm.map π hπs
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hmn with h | h
      · exact absurd h (hne i)
      · exact h
    have hC : L ≤ ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap π).map L.subtype := by
      calc L = ⨆ j, K j := hres
        _ ≤ _ := by
          refine iSup_le fun j x hx => ?_
          have hxL : x ∈ L := hKL j hx
          refine ⟨⟨x, hxL⟩, ?_, rfl⟩
          exact hcen j ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hall : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, q ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro q
      obtain ⟨l, rfl⟩ := hπs q
      obtain ⟨c, hc, hcl⟩ := hC l.2
      have : c = l := Subtype.ext hcl
      rw [← this]
      exact hc
    have hsub : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b => exact QuotientGroup.eq.mpr (hall _)
    have hnt : Nontrivial ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      hqs.2.1.toNontrivial
    exact false_of_nontrivial_of_subsingleton
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  obtain ⟨i, hi⟩ := hex
  have hOp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hLKi : L ≤ K i := by
    have h2 : twoResidual L ≤ K i := by
      refine twoResidual_le_of_isTwoQuotient (hKL i) (hKN i) ?_
      intro y hy
      have hmem : π ⟨y, hy⟩ ∈ ((K i).subgroupOf L).map π := hi ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxy⟩ := hmem
      have hker : x⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥L := by
        have h3 : π (x⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h3
      have hker' : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ pCoreOf 2 L :=
        ⟨_, by assumption, rfl⟩
      obtain ⟨m, hm⟩ := hOp ⟨_, hker'⟩
      have hm' : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have hxK : (x : G) ∈ K i := Subgroup.mem_subgroupOf.mp hx
      have hoN : ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ Subgroup.normalizer (K i : Set G) :=
        hKN i (CFSG.LieType.BorelTits.pCoreOf_le 2 L hker')
      obtain ⟨q, hq, hqe⟩ := zb_mul_pow_mem hoN hxK (2 ^ m)
      refine ⟨m, ?_⟩
      have hy' : y = (x : G) * ((x⁻¹ * ⟨y, hy⟩ : ↥L) : G) := by
        simp
      rw [hy', hqe, hm', mul_one]
      exact hq
    rw [← twoResidual_eq_self_of_perfect hperf]
    exact h2
  have hKiL : K i = L := le_antisymm (hKL i) hLKi
  have hsh := (hblock i).1.1.1
  rwa [hKiL] at hsh

end CFSG.Quasithin.S151S4
