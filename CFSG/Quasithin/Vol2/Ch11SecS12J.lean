module

public import CFSG.Quasithin.Vol2.Ch11SecS12I
public import CFSG.Quasithin.Vol2.Ch11SecS12B
public import CFSG.Quasithin.Vol2.Ch11SecS12G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section Seven

variable {F : Type} [Field F] {r : ℕ}

theorem comm_mem_of_seven {M S W S₃ : Subgroup G} {θ : ↥M →* SL(3, F)}
    {φ₇ : ↥S →* Multiplicative (Fin r → Fin 3 → F)}
    (h₇ : IsSumOfSL3ModulesVia r M S S₃ θ φ₇)
    (hc₇ : ∀ y : ↥S, (y : G) ∈ W ⊔ S₃ ↔
      ∀ l : Fin r, ∃ c : F, Multiplicative.toAdd (φ₇ y) l = c • vE F 0)
    (hWS : W ≤ S) {k : ↥M} (hkS : (k : G) ∈ Subgroup.normalizer (S : Set G))
    (hkW : (k : G) ∈ Subgroup.normalizer (W : Set G)) (hk0 : θ k • vE F 0 = vE F 0)
    {d : G} (hd : d ∈ W) : (k : G) * d * (k : G)⁻¹ * d⁻¹ ∈ W ⊓ S₃ := by
  have hdS := hWS hd
  have hd' : (k : G) * d * (k : G)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hkS d).mp hdS
  have hdW : (k : G) * d * (k : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hkW d).mp hd
  have e := h₇.2.2 k ⟨d, hdS⟩ ⟨_, hd'⟩ rfl
  have hco := (hc₇ ⟨d, hdS⟩).1 (Subgroup.mem_sup_left hd)
  have e2 : φ₇ ⟨_, hd'⟩ = φ₇ ⟨d, hdS⟩ := by
    rw [e]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    funext l
    obtain ⟨c, hc⟩ := hco l
    rw [hc, smul_comm, hk0]
  have hmem : (k : G) * d * (k : G)⁻¹ * d⁻¹ ∈ S := S.mul_mem hd' (S.inv_mem hdS)
  refine ⟨W.mul_mem hdW (W.inv_mem hd), (h₇.2.1 ⟨_, hmem⟩).1 ?_⟩
  have e3 : φ₇ ⟨_, hmem⟩ = φ₇ ⟨_, hd'⟩ * (φ₇ ⟨d, hdS⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e3, e2, mul_inv_cancel]

end Seven

theorem qFil_le_top {F : Type} [Field F] {s : ℕ} {S₃ : Subgroup G}
    (φ : ↥S₃ →* Multiplicative (Fin s → Fin 3 → F)) (i : ℕ) : qFil φ i ≤ qFil φ s := by
  intro y hy
  obtain ⟨hy, h⟩ := mem_qFil.1 hy
  exact mem_qFil.2 ⟨hy, fun l => ⟨(h l).1, fun hl => absurd hl (not_le.mpr l.2)⟩⟩

namespace L3Setting'

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H)

theorem isLabFactor_top (hn : 2 ≤ n) (hV₁V : V₁ ≤ V)
    (hNH : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ H) {Y : Subgroup G} (hL₁Y : LOf L V₁ ≤ Y)
    (hYN : Y ≤ L ⊓ Subgroup.normalizer (V₁ : Set G)) {x : G} (hxY : x ∈ Y)
    {c : GaloisField 2 n}
    (hxc : ∀ w : Fin 3 → GaloisField 2 n, St.D.θ ⟨x, (hYN hxY).1⟩ • w = c • w) :
    IsLabFactor Y (LOf L V₁) x (NatData3'.alpha0 St.D hV₁V)
      (conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H)) (conjClosure V H) (some 1) := by
  have hUab : ∀ u ∈ conjClosure V H, ∀ v ∈ conjClosure V H, u * v * u⁻¹ * v⁻¹ ∈ V₁ :=
    fun u hu v hv => St.hyp.base.G22_commutator_mem hu hv
  have hV₁U : V₁ ≤ conjClosure V H := hV₁V.trans (le_conjClosure V H)
  have hNU : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((conjClosure V H : Subgroup G) : Set G) :=
    hNH.trans (le_normalizer_conjClosure V H)
  have hNS : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((pCoreOf 2 (L ⊔ conjClosure V H) : Subgroup G) : Set G) :=
    inf_le_left.trans ((le_sup_left : L ≤ L ⊔ conjClosure V H).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hVS : V ≤ pCoreOf 2 (L ⊔ conjClosure V H) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure V H).trans le_sup_right) St.LU_le_normV St.isPGroup_V
  have hV₁W : V₁ ≤ conjClosure V H ⊓ pCoreOf 2 (L ⊔ conjClosure V H) :=
    le_inf hV₁U (hV₁V.trans hVS)
  exact isLabFactor_of_nat (NatData3'.alpha0_surjective St.D hn hV₁V) hL₁Y inf_le_left
    (le_normalizer_of_comm hV₁W inf_le_left le_rfl hUab)
    (fun y hy => mem_normalizer_inf_of (hNU (hYN hy)) (hNS (hYN hy))) (hYN.trans hNU)
    (natEig_top St hV₁V (hYN hxY).1 hxc)

theorem exists_labSeries (hn : 2 ≤ n) (hV₁V : V₁ ≤ V)
    (hNH : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ H) {Y : Subgroup G} (hL₁Y : LOf L V₁ ≤ Y)
    (hYN : Y ≤ L ⊓ Subgroup.normalizer (V₁ : Set G)) {x : G} (hxY : x ∈ Y)
    {c : GaloisField 2 n}
    (hxc : ∀ w : Fin 3 → GaloisField 2 n, St.D.θ ⟨x, (hYN hxY).1⟩ • w = c • w) :
    ∃ (s : ℕ) (l : List (Subgroup G × Option (GaloisField 2 n))),
      IsLabSeries Y (LOf L V₁) x (NatData3'.alpha0 St.D hV₁V) V₁ l (conjClosure V H) ∧
        labMultiset l = c ::ₘ (Multiset.replicate s c⁻¹ + {1}) := by
  set U := conjClosure V H with hU
  have hα := NatData3'.alpha0_surjective St.D hn hV₁V
  have hxL : x ∈ L := (hYN hxY).1
  obtain ⟨g, hg, h, hh, hθg, hθh, hV⟩ := exists_weyl' St.D hV₁V
  have hI : L ⊔ U = U ⊔ rconj U g ⊔ rconj U h := (St.G25_two_aux hg hh hV).symm
  set S := pCoreOf 2 (L ⊔ U) with hS
  set W := U ⊓ S with hW
  obtain ⟨hVS₂, hS₂S₃, hS₃S, -, -, hIS₂, hIS⟩ := St.hyp.G25_four hU hg hh hV hI hS hW
  have hIS₃ := St.hyp.G25_four_inv hU hg hh hV hI hS hW
  have h5 := St.hyp.G25_five hU hg hh hV hI
  obtain ⟨r, s, φ₇, φ₆, h₇, hc₇, -, -, h₆, hc₆g, hc₆h, -, -⟩ :=
    St.hyp.G25_six_seven_eight hU hg hh hV hI hS hW St.D
  set S₂ := U ⊓ rconj U g ⊓ rconj U h with hS₂
  have hUab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁ :=
    fun u hu v hv => St.hyp.base.G22_commutator_mem hu hv
  have hVU : V ≤ U := le_conjClosure V H
  have hV₁U : V₁ ≤ U := hV₁V.trans hVU
  have hS₂U : S₂ ≤ U := inf_le_left.trans inf_le_left
  have hS₂W : S₂ ≤ W := le_inf hS₂U (hS₂S₃.trans hS₃S)
  have hWU : W ≤ U := inf_le_left
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have hA : ∀ y : ↥(sThree W g h), (y : G) ∈ W ⊓ rconj W g ↔ ∀ l : Fin s,
      Multiplicative.toAdd (φ₆ y) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
        Multiplicative.toAdd (φ₆ y) l ⬝ᵥ vE (GaloisField 2 n) 1 = 0 := by
    intro y
    have e : St.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0 = vE (GaloisField 2 n) 1 := by
      rw [map_inv, hθg, wS_inv_smul_e0 h01]
    simp only [hc₆g y, e]
  have hB : ∀ y : ↥(sThree W g h), (y : G) ∈ W ⊓ rconj W h ↔ ∀ l : Fin s,
      Multiplicative.toAdd (φ₆ y) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
        Multiplicative.toAdd (φ₆ y) l ⬝ᵥ vE (GaloisField 2 n) 2 = 0 := by
    intro y
    have e : St.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0 = vE (GaloisField 2 n) 2 := by
      rw [map_inv, hθh, wS_inv_smul_e0 h02]
    simp only [hc₆h y, e]
  have hQ0 : qFil φ₆ 0 = S₂ := qFil_zero h₆.2.1 hS₂S₃
  have hA₆W : qFil φ₆ s ≤ W := qFil_top_le h₆.1 h₆.2.1 hS₂W hA hB
  have hS₂Q : ∀ i, S₂ ≤ qFil φ₆ i := fun i => by
    rw [← hQ0]
    exact qFil_mono φ₆ (Nat.zero_le i)
  have hQU : ∀ i, qFil φ₆ i ≤ U := fun i => (qFil_le_top φ₆ i).trans (hA₆W.trans hWU)
  have hV₁Q : ∀ i, V₁ ≤ qFil φ₆ i := fun i => hV₁V.trans (hVS₂.trans (hS₂Q i))
  have hW₃U : W ⊓ sThree W g h ≤ U := inf_le_left.trans hWU
  have hV₁W₃ : V₁ ≤ W ⊓ sThree W g h := le_inf (hV₁V.trans (hVS₂.trans hS₂W))
    (hV₁V.trans (hVS₂.trans hS₂S₃))
  have hV₁W : V₁ ≤ W := hV₁W₃.trans inf_le_left
  have hLI : L ≤ L ⊔ U := le_sup_left
  have hNV₁ : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (V₁ : Set G) :=
    inf_le_right
  have hNV : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans St.D.hnorm
  have hNS₂ : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (S₂ : Set G) :=
    inf_le_left.trans (hLI.trans hIS₂)
  have hNS : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (S : Set G) :=
    inf_le_left.trans (hLI.trans hIS)
  have hNS₃ : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((sThree W g h : Subgroup G) : Set G) :=
    inf_le_left.trans (hLI.trans hIS₃)
  have hNU : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    hNH.trans (le_normalizer_conjClosure V H)
  have hNW : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    fun a ha => mem_normalizer_inf_of (hNU ha) (hNS ha)
  have hNW₃ : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((W ⊓ sThree W g h : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_inf_of (hNW ha) (hNS₃ ha)
  have hNQ : ∀ i, L ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((qFil φ₆ i : Subgroup G) : Set G) := fun i =>
    le_normalizer_of_conj_mem fun a ha y hy => by
      obtain ⟨μ, hμ, hμe, -⟩ := exists_smul_e0 (NatData3'.theta_mem_Pt St.D hV₁V ⟨a, ha.1⟩ ha.2)
      exact conj_mem_qFil (a := ⟨a, ha.1⟩) h₆ (hNS₃ ha) hμ hμe hy
  have fV : IsLabFactor Y (LOf L V₁) x (NatData3'.alpha0 St.D hV₁V) V₁ V (some c) :=
    isLabFactor_of_nat hα hL₁Y hV₁V (le_normalizer_of_comm le_rfl hV₁U hVU hUab)
      (hYN.trans hNV₁) (hYN.trans hNV) (NatData3'.natEig_V St.D hV₁V hxL hxc)
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_isLabSeries_central (Y := Y) (K := LOf L V₁) (x := x)
    (α₀ := NatData3'.alpha0 St.D hV₁V) hVS₂ (le_normalizer_of_comm hV₁V hVU hS₂U hUab)
    (hYN.trans hNV) (hYN.trans hNS₂) fun k hk d hd => by
      have h1 := h5 (Subgroup.commutator_mem_commutator hd (hLI (NatData3'.lOf_le hk)))
      have e : k * d * k⁻¹ * d⁻¹ = ⁅d, k⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact V.inv_mem h1
  have hQ : ∀ i, i ≤ s → ∃ lq : List (Subgroup G × Option (GaloisField 2 n)),
      IsLabSeries Y (LOf L V₁) x (NatData3'.alpha0 St.D hV₁V) S₂ lq (qFil φ₆ i) ∧
        labMultiset lq = Multiset.replicate i c⁻¹ := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨[], hQ0.symm, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨lq, hlq, hmq⟩ := ih (Nat.le_of_succ_le hi)
      have hf := isLabFactor_of_nat hα hL₁Y (qFil_mono φ₆ (Nat.le_succ i))
        (le_normalizer_of_comm (hV₁Q i) (hQU i) (hQU (i + 1)) hUab) (hYN.trans (hNQ i))
        (hYN.trans (hNQ (i + 1))) (natEig_qFil St.D hV₁V h₆ (Nat.lt_of_succ_le hi) hxL hxc)
      refine ⟨lq ++ [(qFil φ₆ (i + 1), some c⁻¹)], hlq.append (isLabSeries_singleton hf), ?_⟩
      rw [labMultiset_append, hmq, labMultiset_cons, labMultiset_nil, add_zero,
        Multiset.replicate_succ, ← Multiset.singleton_add, add_comm]
      rfl
  obtain ⟨lq, hlq, hmq⟩ := hQ s le_rfl
  have hL₁S₃ : LOf L V₁ ≤ Subgroup.normalizer ((sThree W g h : Subgroup G) : Set G) :=
    NatData3'.lOf_le.trans (hLI.trans hIS₃)
  obtain ⟨l₃, hl₃, hm₃⟩ := exists_isLabSeries_central (Y := Y) (K := LOf L V₁) (x := x)
    (α₀ := NatData3'.alpha0 St.D hV₁V) (le_inf hA₆W (qFil_le φ₆ s))
    (le_normalizer_of_comm (hV₁Q s) (hQU s) hW₃U hUab) (hYN.trans (hNQ s)) (hYN.trans hNW₃)
    fun k hk d hd => comm_mem_qFil_top St.D hV₁V h₆ hL₁S₃ hk hd.2
  obtain ⟨l₄, hl₄, hm₄⟩ := exists_isLabSeries_central (Y := Y) (K := LOf L V₁) (x := x)
    (α₀ := NatData3'.alpha0 St.D hV₁V) inf_le_left
    (le_normalizer_of_comm hV₁W₃ hW₃U hWU hUab) (hYN.trans hNW₃) (hYN.trans hNW)
    fun k hk d hd => by
      have hkL : k ∈ L := NatData3'.lOf_le hk
      have hkW : k ∈ Subgroup.normalizer (W : Set G) :=
        mem_normalizer_inf_of (lOf_le_normalizer_U St hk) (hIS (hLI hkL))
      exact comm_mem_of_seven (k := ⟨k, hkL⟩) h₇ hc₇ inf_le_right (hIS (hLI hkL)) hkW
        (NatData3'.theta_mem_stab0 St.D hV₁V ⟨k, hk⟩) hd
  have fU := isLabFactor_top St hn hV₁V hNH hL₁Y hYN hxY hxc
  refine ⟨s, [(V, some c)] ++ (l₁ ++ (lq ++ (l₃ ++ (l₄ ++ [(U, some 1)])))),
    (isLabSeries_singleton fV).append (hl₁.append (hlq.append (hl₃.append
      (hl₄.append (isLabSeries_singleton fU))))), ?_⟩
  rw [labMultiset_append, labMultiset_append, labMultiset_append, labMultiset_append,
    labMultiset_append, hm₁, hmq, hm₃, hm₄, labMultiset_cons, labMultiset_nil, labMultiset_cons,
    labMultiset_nil]
  simp only [Option.elim, add_zero, zero_add]
  rfl

end L3Setting'

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
