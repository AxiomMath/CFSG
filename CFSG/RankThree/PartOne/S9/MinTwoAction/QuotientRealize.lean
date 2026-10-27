module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientDefs
public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniModuleRealization
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial
open scoped IsMulCommutative commutatorElement

section Aux

variable {G : Type*} [Group G]

theorem normal_subgroupOf_sup {R A : Subgroup G} (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    (R.subgroupOf (R ⊔ A)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le (Subgroup.le_normalizer) hAR

theorem card_sup_dvd {R A : Subgroup G} (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card ↥(R ⊔ A) ∣ Nat.card R * Nat.card A := by
  let L := R ⊔ A
  let R' : Subgroup L := R.subgroupOf L
  let A' : Subgroup L := A.subgroupOf L
  have : R'.Normal := normal_subgroupOf_sup hAR
  have hsup : R' ⊔ A' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  let π : ↥L →* ↥L ⧸ R' := QuotientGroup.mk' R'
  have hmap : A'.map π = ⊤ := by
    have h1 : (R' ⊔ A').map π = ⊤ := by
      rw [hsup]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R')
    rw [Subgroup.map_sup] at h1
    have h2 : R'.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, bot_sup_eq] at h1
  have hsurj : Function.Surjective (π.comp A'.subtype) := by
    intro v
    have : v ∈ A'.map π := by rw [hmap]; exact Subgroup.mem_top v
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨⟨a, ha⟩, rfl⟩
  have h1 : Nat.card (↥L ⧸ R') ∣ Nat.card A' := Subgroup.card_dvd_of_surjective hsurj
  have hR'card : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : R ≤ R ⊔ A)).toEquiv
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ R ⊔ A)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup R', hR'card, mul_comm]
  rw [hA'card] at h1
  exact mul_dvd_mul_left _ h1

end Aux

section Commutator

variable {A Q : Type*} [Group A] [Group Q] [MulDistribMulAction A Q]

theorem commutatorAction_eq_actionCommutator :
    commutatorAction (A := A) (G := Q) = actionCommutator A (⊤ : Subgroup Q) := by
  unfold CFSG.commutatorAction CFSG.commutatorSubgroup actionCommutator
  congr 1
  ext x
  constructor
  · rintro ⟨a, h, hh, rfl⟩
    exact ⟨h, hh, a, rfl⟩
  · rintro ⟨h, hh, a, rfl⟩
    exact ⟨a, h, hh, rfl⟩

end Commutator

section Minimal

theorem exists_minimal_invariant {L V : Type*} [Group L] [Finite L] [Group V] [Finite V]
    [MulDistribMulAction L V] (N : Subgroup L) [hN : N.Normal] (hcomm : IsMulCommutative V)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card V)) (hnt : ∃ n ∈ N, ∃ v : V, n • v ≠ v) :
    ∃ W : Subgroup V, W ≠ ⊥ ∧ (∀ l : L, ∀ w ∈ W, l • w ∈ W) ∧
      (∀ W' : Subgroup V, W' ≤ W → (∀ l : L, ∀ w ∈ W', l • w ∈ W') → W' = ⊥ ∨ W' = W) ∧
      ∃ n ∈ N, ∃ w ∈ W, n • w ≠ w := by
  classical
  let E : Subgroup V := actionCommutator ↥N (⊤ : Subgroup V)
  have hEinv : ∀ l : L, ∀ x ∈ E, l • x ∈ E := fun l x hx =>
    SteinbergBM.smul_mem_actionCommutator_of_normal hN (fun l x _ => Subgroup.mem_top _) l hx
  have hEne : E ≠ ⊥ := by
    obtain ⟨n, hn, v, hv⟩ := hnt
    intro hE
    have h1 : v⁻¹ * ((⟨n, hn⟩ : ↥N) • v) ∈ E :=
      gen_mem_actionCommutator (A := ↥N) (Subgroup.mem_top v) ⟨n, hn⟩
    rw [hE, Subgroup.mem_bot] at h1
    exact hv (inv_mul_eq_one.mp h1).symm
  have hsolv : Group.IsSolvable V := by
    let _ : CommGroup V := IsMulCommutative.instCommGroup
    infer_instance
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := ↥N) hsolv hcop hcomm
  rw [commutatorAction_eq_actionCommutator] at hcompl
  have hdis : fixedPointSubgroup ↥N V ⊓ E = ⊥ := hcompl.inf_eq_bot
  let T : Set (Subgroup V) := {W | W ≤ E ∧ W ≠ ⊥ ∧ ∀ l : L, ∀ w ∈ W, l • w ∈ W}
  obtain ⟨W, ⟨hWE, hW1, hWinv⟩, hWmin⟩ :=
    (measure fun W : Subgroup V => Nat.card W).wf.has_min T
      (⟨E, le_rfl, hEne, hEinv⟩ : T.Nonempty)
  refine ⟨W, hW1, hWinv, ?_, ?_⟩
  · intro W' hle hinv
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    · right
      have : ¬ Nat.card W' < Nat.card W := hWmin W' ⟨hle.trans hWE, h0, hinv⟩
      exact Subgroup.eq_of_le_of_card_ge hle (not_lt.mp this)
  · by_contra h
    push Not at h
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    have h1 : w ∈ fixedPointSubgroup ↥N V := fun n => h n n.2 w hw
    have h2 : w ∈ fixedPointSubgroup ↥N V ⊓ E := ⟨h1, hWE hw⟩
    rw [hdis] at h2
    exact h2

end Minimal

section Transport

variable {G : Type*} [Group G]

theorem map_actionCommutator_sup {R A D : Subgroup G}
    (hLD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) (X₀ : Subgroup ↥D) :
    letI : MulDistribMulAction ↥(R ⊔ A) ↥D := MulDistribMulAction.compHom ↥D (conjHom hLD)
    (actionCommutator ↥(R.subgroupOf (R ⊔ A)) X₀).map D.subtype = ⁅X₀.map D.subtype, R⁆ := by
  let _ : MulDistribMulAction ↥(R ⊔ A) ↥D := MulDistribMulAction.compHom ↥D (conjHom hLD)
  have hsm : ∀ (n : ↥(R.subgroupOf (R ⊔ A))) (x : ↥D),
      ((n • x : ↥D) : G) = ((n : ↥(R ⊔ A)) : G) * x * ((n : ↥(R ⊔ A)) : G)⁻¹ := fun _ _ => rfl
  unfold actionCommutator
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨_, ⟨x, hx, n, rfl⟩, rfl⟩
    have e : D.subtype (x⁻¹ * (n • x)) =
        ⁅((x⁻¹ : ↥D) : G), (((n : ↥(R ⊔ A)) : G))⁆ := by
      rw [map_mul, Subgroup.coe_subtype, hsm, commutatorElement_def]
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ (X₀.inv_mem hx), _,
      Subgroup.mem_subgroupOf.mp n.2, rfl⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, c, hc, rfl⟩
    let n : ↥(R.subgroupOf (R ⊔ A)) := ⟨⟨c, (le_sup_left : R ≤ R ⊔ A) hc⟩, hc⟩
    have hnc : ((n : ↥(R ⊔ A)) : G) = c := rfl
    have e : ⁅D.subtype x, c⁆ = D.subtype ((x⁻¹)⁻¹ * (n • x⁻¹)) := by
      rw [map_mul, Subgroup.coe_subtype, hsm, hnc, commutatorElement_def]
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨_, ⟨x⁻¹, X₀.inv_mem hx, n, rfl⟩, rfl⟩

theorem map_frattini_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem inSubgroup_frattini_map' {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (K : Subgroup G) :
    inSubgroup frattini (K.map f) = (inSubgroup frattini K).map f := by
  unfold inSubgroup
  rw [← map_frattini_mulEquiv' (K.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

end Transport

section Realize

variable {G : Type} [Group G] [Finite G]

theorem exists_realization {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {A D R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hAord : ¬ q ∣ Nat.card A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hLD : R ⊔ A ≤ Subgroup.normalizer (D : Set G))
    (hDq : IsPGroup q D) (hact : ⁅R, D⁆ ≠ ⊥) :
    ∃ X : Subgroup G, X ≤ D ∧ R ⊔ A ≤ Subgroup.normalizer (X : Set G) ∧ ⁅X, R⁆ = X ∧
      IsFrattiniIrreducibleFor (R ⊔ A) X ∧
      X ⊓ inSubgroup frattini D = inSubgroup frattini X ∧
      ¬ R ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  let L : Subgroup G := R ⊔ A
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := le_trans le_sup_left hLD
  let fL : ↥L →* MulAut ↥D := conjHom hLD
  let _ : MulDistribMulAction ↥L ↥D := MulDistribMulAction.compHom ↥D fL
  have hsm : ∀ (l : ↥L) (x : ↥D), ((l • x : ↥D) : G) = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  have hLq : ¬ q ∣ Nat.card ↥L := by
    intro h
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
    have h1 := h.trans (card_sup_dvd hAR)
    rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · rw [ha] at h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
    · exact hAord h2
  let N : Subgroup ↥L := R.subgroupOf L
  have hNn : N.Normal := normal_subgroupOf_sup hAR
  let _ : MulDistribMulAction ↥L (↥D ⧸ frattini ↥D) := frattiniQuotientAction ↥L ↥D
  have hRord : ∀ r : R, ¬ q ∣ orderOf r := by
    intro r hdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
    have h1 : q ∣ 2 ^ a := ha ▸ hdvd.trans (orderOf_dvd_natCard r)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))
  obtain ⟨r, hrR, hrD⟩ : ∃ r ∈ R, r ∉ Subgroup.centralizer (D : Set G) := by
    by_contra h
    push Not at h
    exact hact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨d, hdD, hrd⟩ : ∃ d ∈ D, ¬ d * r = r * d := by
    rw [Subgroup.mem_centralizer_iff] at hrD
    push Not at hrD
    exact hrD
  let rL : ↥L := ⟨r, (le_sup_left : R ≤ R ⊔ A) hrR⟩
  have hrN : rL ∈ N := hrR
  have hnontriv : ∃ n ∈ N, ∃ v : ↥D ⧸ frattini ↥D, n • v ≠ v := by
    refine ⟨rL, hrN, ?_⟩
    by_contra h
    push Not at h
    have hord : ¬ q ∣ orderOf rL := by
      have h1 : orderOf rL = orderOf (⟨r, hrR⟩ : R) := by
        rw [← Subgroup.orderOf_coe rL, ← Subgroup.orderOf_coe (⟨r, hrR⟩ : R)]
      rw [h1]
      exact hRord _
    have h2 := smul_eq_of_smul_mk_eq hDq rL hord (fun x => h (x : ↥D ⧸ frattini ↥D)) ⟨d, hdD⟩
    have h3 := congrArg (fun y : ↥D => (y : G)) h2
    change r * d * r⁻¹ = d at h3
    apply hrd
    calc d * r = (r * d * r⁻¹) * r := by rw [h3]
      _ = r * d := by group
  have hVcomm : IsMulCommutative (↥D ⧸ frattini ↥D) :=
    (isElementaryAbelian_quotient_frattini (p := q) (R := ↥D)).toIsMulCommutative
  have hN2 : IsPGroup 2 ↥N := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  have hcop : Nat.Coprime (Nat.card ↥N) (Nat.card (↥D ⧸ frattini ↥D)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hN2
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hDq.to_quotient (frattini ↥D))
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  obtain ⟨W, hW1, hWinv, hWirr, hWnt⟩ := exists_minimal_invariant N hVcomm hcop hnontriv
  obtain ⟨X₀, hX₀inv, hX₀W, hX₀frat, -, hX₀C, -, hX₀comm⟩ :=
    SteinbergBM.invariant_frattini_module_realization hq hDq hLq W hW1 hWinv hWirr
  have hsm' : ∀ (l : ↥L) (x : ↥D), ((l • x : ↥D) : G) = (l : G) * x * (l : G)⁻¹ := hsm
  let X : Subgroup G := X₀.map D.subtype
  have hXD : X ≤ D := Subgroup.map_subtype_le _
  have hmemX : ∀ x : ↥D, (x : G) ∈ X ↔ x ∈ X₀ := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by rwa [← Subtype.ext hyx], fun hx => ⟨x, hx, rfl⟩⟩
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_conj_mem fun c hc g hg => ?_
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨(⟨c, hc⟩ : ↥L) • x, hX₀inv ⟨c, hc⟩ x hx, rfl⟩
  have hΦX : inSubgroup frattini X = (X₀ ⊓ frattini ↥D).map D.subtype := by
    rw [inSubgroup_frattini_map' D.subtype D.subtype_injective X₀, hX₀frat]
    rfl
  have hmemΦX : ∀ x : ↥D, (x : G) ∈ inSubgroup frattini X ↔ x ∈ X₀ ∧ x ∈ frattini ↥D := by
    intro x
    rw [hΦX]
    refine ⟨fun h => ?_, fun h => ⟨x, h, rfl⟩⟩
    obtain ⟨y, hy, hyx⟩ := h
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    exact hy
  have hcommX : ⁅X, R⁆ = X := by
    have h1 := hX₀comm N hNn hWnt
    have h2 := map_actionCommutator_sup (R := R) (A := A) hLD X₀
    rw [h1] at h2
    exact h2.symm
  have hXfrat : X ⊓ inSubgroup frattini D = inSubgroup frattini X := by
    rw [hΦX]
    show X₀.map D.subtype ⊓ (frattini ↥D).map D.subtype = _
    exact (Subgroup.map_inf X₀ (frattini ↥D) D.subtype D.subtype_injective).symm
  have hnoC : ¬ R ≤ Subgroup.centralizer (X : Set G) := by
    intro hRC
    obtain ⟨n, hn, w, hw, hnw⟩ := hWnt
    apply hnw
    refine (hX₀C n).mp (fun x hx => ?_) w hw
    apply Subtype.ext
    rw [hsm']
    have h1 : (n : G) ∈ Subgroup.centralizer (X : Set G) := hRC hn
    have h2 := Subgroup.mem_centralizer_iff.mp h1 (x : G) ((hmemX x).mpr hx)
    calc (n : G) * x * (n : G)⁻¹ = (x * n) * (n : G)⁻¹ := by rw [← h2]
      _ = x := by group
  have hirrX : IsFrattiniIrreducibleFor L X := by
    refine ⟨hLX, ?_, ?_⟩
    · refine lt_of_le_of_ne ?_ ?_
      · intro g hg
        rw [hΦX] at hg
        obtain ⟨y, hy, rfl⟩ := hg
        exact (hmemX y).mpr hy.1
      · intro h
        apply hW1
        rw [← hX₀W, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        intro x hx
        have h1 : (x : G) ∈ inSubgroup frattini X := by rw [h]; exact ⟨x, hx, rfl⟩
        exact ((hmemΦX x).mp h1).2
    · intro Y hΦY hYX hLY
      let Y₀ : Subgroup ↥D := Y.subgroupOf D
      have hY₀ : ∀ y : ↥D, y ∈ Y₀ ↔ (y : G) ∈ Y := fun y => Iff.rfl
      have hY₀X : ∀ y : ↥D, y ∈ Y₀ → y ∈ X₀ := fun y hy => (hmemX y).mp (hYX ((hY₀ y).mp hy))
      have hW'le : Y₀.map (QuotientGroup.mk' (frattini ↥D)) ≤ W := by
        rw [← hX₀W]
        exact Subgroup.map_mono fun y hy => hY₀X y hy
      have hW'inv : ∀ l : ↥L, ∀ w ∈ Y₀.map (QuotientGroup.mk' (frattini ↥D)),
          l • w ∈ Y₀.map (QuotientGroup.mk' (frattini ↥D)) := by
        rintro l _ ⟨y, hy, rfl⟩
        refine ⟨l • y, ?_, rfl⟩
        show ((l • y : ↥D) : G) ∈ Y
        rw [hsm']
        exact (Subgroup.mem_normalizer_iff.mp (hLY l.2) y).mp ((hY₀ y).mp hy)
      rcases hWirr _ hW'le hW'inv with h0 | h1
      · left
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
        refine le_antisymm (fun g hg => ?_) hΦY
        have hgD : g ∈ D := hXD (hYX hg)
        have := (hmemΦX ⟨g, hgD⟩).mpr ⟨hY₀X ⟨g, hgD⟩ hg, h0 hg⟩
        exact this
      · right
        refine le_antisymm hYX (fun g hg => ?_)
        obtain ⟨x, hx, rfl⟩ := hg
        have : (QuotientGroup.mk' (frattini ↥D)) x ∈ W := by rw [← hX₀W]; exact ⟨x, hx, rfl⟩
        rw [← h1] at this
        obtain ⟨y, hy, hyx⟩ := this
        have h2 : y⁻¹ * x ∈ frattini ↥D := by
          have := QuotientGroup.eq.mp hyx
          exact this
        have h3 : ((y⁻¹ * x : ↥D) : G) ∈ inSubgroup frattini X :=
          (hmemΦX _).mpr ⟨X₀.mul_mem (X₀.inv_mem (hY₀X y hy)) hx, h2⟩
        have h4 : (x : G) = (y : G) * ((y⁻¹ * x : ↥D) : G) := by simp
        rw [show (D.subtype x) = (x : G) from rfl, h4]
        exact Y.mul_mem ((hY₀ y).mp hy) (hΦY h3)
  exact ⟨X, hXD, hLX, hcommX, hirrX, hXfrat, hnoC⟩

end Realize

end CFSG.RankThree.PartOne.Quotient36
