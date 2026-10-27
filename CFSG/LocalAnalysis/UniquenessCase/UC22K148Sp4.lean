module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Fac
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Matrix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

namespace Sp4Aux

theorem fix_iff_mem_centralizer {L B : Subgroup G} [IsSimpleGroup ↥L] {U : Submodule (ZMod 2) V}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U)
    (hnt : ∃ l ∈ L, ∃ u ∈ U, ρ l u ≠ u)
    (hmov : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) {b : G}
    (hb : b ∈ B) : (∀ u ∈ U, ρ b u = u) ↔ b ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h
    have hsec : b ∈ secKer ρ U ⊥ := by
      refine ⟨fun y hy => ?_, fun z hz => ?_, fun z hz => ?_⟩
      · rw [h y hy, sub_self]
        exact Submodule.zero_mem _
      · rw [Submodule.mem_bot] at hz ⊢
        rw [hz, map_zero]
      · rw [Submodule.mem_bot] at hz ⊢
        rw [hz, map_zero]
    have hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L ⊥ := fun a _ z hz => by
      rw [Submodule.mem_bot] at hz ⊢
      rw [hz, map_zero]
    have hnt' : ∃ l ∈ L, ∃ y ∈ U, ρ l y - y ∉ (⊥ : Submodule (ZMod 2) V) := by
      obtain ⟨l, hl, u, hu, hne⟩ := hnt
      exact ⟨l, hl, u, hu, fun h' => hne (sub_eq_zero.1 ((Submodule.mem_bot _).1 h'))⟩
    exact Subgroup.mem_centralizer_iff.2 (commute_of_mem_secKer hLU hZ hnt' (hBN hb) hsec)
  · intro hc
    by_contra hcon
    push Not at hcon
    have hb' : b ∉ cenOn ρ B U := fun h => by
      obtain ⟨u, hu, hne⟩ := hcon
      exact hne (h.2 u hu)
    obtain ⟨k, hk, u, hu, hne⟩ := hmov b hb hb'
    apply hne
    have hkb : k * b = b * k := Subgroup.mem_centralizer_iff.1 hc k hk
    have e1 : ρ b (ρ k u) = ρ (b * k) u := by rw [map_mul]; rfl
    have e2 : ρ k (ρ b u) = ρ (k * b) u := by rw [map_mul]; rfl
    rw [e1, e2, hkb]

theorem exists_card_eq_two_pow_mul [Finite G] {B C : Subgroup G} (hB : IsPGroup 2 ↥B)
    (hBC : ¬ B ≤ C) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ C) := by
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  have hdvd : Nat.card ↥(B ⊓ C) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hjlt : j < k := by
    refine lt_of_le_of_ne hjk fun h => hBC ?_
    have hcard : Nat.card ↥B ≤ Nat.card ↥(B ⊓ C) := le_of_eq (by rw [hk, hj, h])
    exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge inf_le_left hcard)
  exact ⟨k - j, by omega, by rw [hj, hk, ← pow_add, Nat.sub_add_cancel hjk]⟩

theorem secCost_bot_le [Finite G] [Finite V] {B : Subgroup G} {U : Submodule (ZMod 2) V} {m : ℕ}
    (hBO : Nat.card ↥U * Nat.card ↥(cenOn ρ B U) ≤ Nat.card ↥B * Nat.card ↥(fixOn ρ B U))
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(cenOn ρ B U)) : secCost ρ B U ⊥ ≤ m := by
  have hc : 0 < Nat.card ↥(cenOn ρ B U) := Nat.card_pos
  rw [hm, mul_right_comm] at hBO
  have h1 := Nat.le_of_mul_le_mul_right hBO hc
  have hF : fixOn ρ B U = U ⊓ fixSub ρ B := rfl
  rw [hF] at h1
  rw [← FiniteField.pow_finrank_eq_natCard 2 ↥U,
    ← FiniteField.pow_finrank_eq_natCard 2 ↥(U ⊓ fixSub ρ B), ← pow_add] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  rw [secCost_bot]
  omega

theorem secCost_le_secCost_bot [Finite V] {D : Subgroup G} {Y Z X : Submodule (ZMod 2) V}
    (hZY : Z ≤ Y) (hYX : Y ≤ X) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ D Z) :
    secCost ρ D Y Z ≤ secCost ρ D X ⊥ := by
  have h1 : secCost ρ D X Y + secCost ρ D Y ⊥ ≤ secCost ρ D X ⊥ := secCost_superadd bot_le hYX hY
  have h2 : secCost ρ D Y Z + secCost ρ D Z ⊥ ≤ secCost ρ D Y ⊥ := secCost_superadd bot_le hZY hZ
  omega

theorem inf_modFix_zpowers_eq {U X : Submodule (ZMod 2) V} {s : G} (hs : Odd (orderOf s))
    (hX : ∀ x ∈ X, ρ s x = x) :
    U ⊓ P22x.modFix ρ X (Subgroup.zpowers s) = U ⊓ fixSub ρ (Subgroup.zpowers s) :=
  le_antisymm (inf_le_inf_left U (modFix_zpowers_le_fixSub hs hX))
    (inf_le_inf_left U (fixSub_le_modFix _ _))

theorem finrank_inf_modFix_conj [Finite V] {U X : Submodule (ZMod 2) V} {g s s' : G}
    (hU : ∀ u ∈ U, ρ g u ∈ U) (hU' : ∀ u ∈ U, ρ g⁻¹ u ∈ U) (hs' : s' = g * s * g⁻¹)
    (hs : Odd (orderOf s)) (hXs : ∀ x ∈ X, ρ s x = x) (hXs' : ∀ x ∈ X, ρ s' x = x) :
    finrank (ZMod 2) ↥(U ⊓ P22x.modFix ρ X (Subgroup.zpowers s')) =
      finrank (ZMod 2) ↥(U ⊓ P22x.modFix ρ X (Subgroup.zpowers s)) := by
  have hs'o : Odd (orderOf s') := by
    have h : orderOf s = orderOf s' :=
      SemiconjBy.orderOf_eq g (show g * s = s' * g by rw [hs']; group)
    rwa [← h]
  rw [inf_modFix_zpowers_eq hs'o hXs', inf_modFix_zpowers_eq hs hXs, hs']
  exact finrank_inf_fixSub_conj hU hU' s

end Sp4Aux

theorem sp4Graph_commute_calP [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) {n : ℕ} (hSp : IsSp4 ↥L n)
    {g : G} (hg : ActsNontrivOnDiagramIn L g) {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) :
    ⁅L, A⁆ = ⊥ := by
  classical
  by_contra hne
  haveI : IsSimpleGroup ↥L := isSimpleGroup_of_isSp4 hSp
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := exists_antiSp_of_isSp4 hSp
  have hAN := le_normalizer_of_mem_calP hρ hL hA
  have hLA := commutator_eq_self_of_mem_calP hρ hL hA hne
  have hAe := isElementaryAbelian_of_mem_calP hA
  have hbest := isBestOffenderOn_of_mem_calP hρ hA
  have hLp : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hLnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro hle
    have hL1 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hρ
      ext w
      simp [(hle hl).2 w Submodule.mem_top]
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance hL1
  obtain ⟨B, hBA, hBinv, hLU, hBU, hBbest, -, hmov, -⟩ :=
    exists_strictMin_moving L A hAe hAN hLA hLnt hbest
  set U := commOn ρ L ⊤ with hU
  have hBe : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_le hAe hBA
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U := fun a ha u hu => hBinv a (Subgroup.mem_sup_left ha) u hu
  have hLnt' : ∃ l ∈ L, ∃ u ∈ U, ρ l u ≠ u := by
    by_contra h
    push Not at h
    exact hLU fun l hl => ⟨hl, fun u hu => h l hl u hu⟩
  have hcenEq : ∀ b ∈ B, (∀ u ∈ U, ρ b u = u) ↔ b ∈ Subgroup.centralizer (L : Set G) :=
    fun b hb => Sp4Aux.fix_iff_mem_centralizer hBN hLinv hLnt' hmov hb
  have hcen : cenOn ρ B U = B ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hcenEq x hx.1).1 hx.2⟩, fun hx => ⟨hx.1, (hcenEq x hx.1).2 hx.2⟩⟩
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧
      Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Sp4Aux.exists_card_eq_two_pow_mul (IsElementaryAbelian.isPGroup 2 ↥B) fun hle => hBU ?_
    intro b hb
    exact ⟨hb, (hcenEq b hb).2 (hle hb)⟩
  have hcost0 : secCost ρ B U ⊥ ≤ m := by
    refine Sp4Aux.secCost_bot_le hBbest.isOffenderOn.2 ?_
    rw [hcen]
    exact hm
  have hCBU : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ U, ρ b y = y :=
    fun b hb hc y hy => (hcenEq b hb).2 hc y hy
  have hUne : U ≠ ⊥ := by
    intro h
    obtain ⟨l, -, u, hu, hne'⟩ := hLnt'
    rw [h, Submodule.mem_bot] at hu
    exact hne' (by rw [hu, map_zero])
  obtain ⟨X, hXU, hXinv, hXmax⟩ := exists_maximal_invariant hBinv hUne
  have hXinvB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B X := fun a ha x hx => hXinv a (Subgroup.mem_sup_right ha) x hx
  have hUL : commOn ρ L U = U := commOn_commOn_eq hAe hAN hLA
  have hnt : ∃ l ∈ L, ∃ y ∈ U, ρ l y - y ∉ X := by
    by_contra h
    push Not at h
    have hle : commOn ρ L U ≤ X :=
      Submodule.span_le.2 fun w ⟨a, ha, u, hu, hw⟩ => hw ▸ h a ha u hu
    rw [hUL] at hle
    exact lt_irrefl X (lt_of_lt_of_le hXU hle)
  have hcost1 : secCost ρ B U X + secCost ρ B X ⊥ ≤ secCost ρ B U ⊥ :=
    secCost_superadd bot_le hXU.le hXinvB
  obtain ⟨h2m, i, hnat⟩ :=
    factor_lemma hn hK e hBe hBN hm1 hm hXU.le hBinv hXinv hCBU hXmax hnt (by omega)
  have hLX : ∀ l ∈ L, ∀ x ∈ X, ρ l x = x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨Y, Z, hZY, hYX, hY, hZ, hirr, hnt'⟩ :=
      exists_irr_section (le_sup_left : L ≤ L ⊔ B) hLp hXinv hcon
    have hYB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Y := fun a ha y hy => hY a (Subgroup.mem_sup_right ha) y hy
    have hZB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Z := fun a ha z hz => hZ a (Subgroup.mem_sup_right ha) z hz
    have hsY : secCost ρ B Y Z ≤ secCost ρ B X ⊥ :=
      Sp4Aux.secCost_le_secCost_bot hZY hYX hYB hZB
    have hCBY : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y :=
      fun b hb hc y hy => hCBU b hb hc y (hXU.le (hYX hy))
    obtain ⟨h2m', -⟩ := factor_lemma hn hK e hBe hBN hm1 hm hZY hY hZ hCBY hirr hnt' (by omega)
    omega
  obtain ⟨s, s', hs3, hss', hne'⟩ := exists_card_fix_ne_of_diagram hn hK e i hg
  rw [← hnat s, ← hnat s'] at hne'
  apply hne'
  have hU1 : ∀ u ∈ U, ρ g u ∈ U := fun u hu => commOn_top_mapsTo hg.1 hu
  have hU2 : ∀ u ∈ U, ρ g⁻¹ u ∈ U := fun u hu => commOn_top_mapsTo (inv_mem hg.1) hu
  have hodd : Odd (orderOf (s : G)) := by
    rw [Subgroup.orderOf_coe, hs3]
    exact ⟨1, rfl⟩
  rw [Sp4Aux.finrank_inf_modFix_conj hU1 hU2 hss' hodd (hLX s s.2) (hLX s' s'.2)]

theorem sp4Graph_commute_hP [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) {n : ℕ} (hSp : IsSp4 ↥L n)
    {g : G} (hg : ActsNontrivOnDiagramIn L g) : ⁅L, UC22.Ext.hP ρ⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun A hA => ?_
  have h := sp4Graph_commute_calP hρ hL hSp hg hA
  rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
