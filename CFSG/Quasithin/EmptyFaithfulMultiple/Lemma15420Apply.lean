module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Xi
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

structure Comp15420 (s : Setting15419 G T) (I₀ L : Subgroup G) (y : G) : Prop where
  mem : L ∈ cComp I₀
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  le : s.X ≤ conjClosure L (T ⊓ I₀)
  y_mem : y ∈ s.X ⊓ L
  y_order : orderOf y = 3
  type : ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1) ∨
    (T ⊓ I₀ ≤ Subgroup.normalizer (L : Set G) ∧
      (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))) ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1 ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)))

omit [Finite G] in
theorem conjClosure_eq_of_le_normalizer {L S : Subgroup G}
    (h : S ≤ Subgroup.normalizer (L : Set G)) : conjClosure L S = L := by
  refine le_antisymm (conjClosure_le fun g hg l hl => ?_) fun l hl => ?_
  · exact (Subgroup.mem_normalizer_iff.mp (h hg) l).mp hl
  · have := mem_conjClosure (Subgroup.one_mem S) hl
    simpa using this

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem pCoreOf_X_le_TI (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : pCoreOf 2 s.X ≤ T ⊓ I₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXI : s.X ⊔ T ⊓ I₀ ≤ I₀ := sup_le (c.le_X hyp h12) inf_le_right
  have hsyl := L15420.isSylowTwoOf_of_le_of_le c.sylow (le_sup_right : T ⊓ I₀ ≤ _) hXI
  refine le_trans ?_ (L15420.pCoreOf_le_of_isSylowTwoOf hsyl)
  have hTX : T ⊓ I₀ ≤ Subgroup.normalizer (s.X : Set G) :=
    (inf_le_left.trans s.inM₁.2).trans (M₁_le_normalizer_X h12 s)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 s.X).trans le_sup_left) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.X)
  refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.X) ?_
  exact hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X)

theorem le_pCoreOf_sup_normalizer (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (c : Config15420 s I₀) {P : Subgroup G} (hP : IsSylowIn 3 P s.X) :
    T ⊓ I₀ ≤ pCoreOf 2 s.X ⊔ ((T ⊓ I₀) ⊓ Subgroup.normalizer (P : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := c.isXi hyp h12
  have hQT := c.pCoreOf_X_le_TI hyp h12
  have h3 : 3 ∣ Nat.card s.X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, (s.relIndex_X_and_pow hyp h12).1]
    exact Dvd.dvd.mul_left (by norm_num) _
  intro t ht
  obtain ⟨g, hgX, hg⟩ := Ch1Sec3.exists_conj_of_isSylowIn hP
    (Ch1Sec3.isSylowIn_map_conj hP (hX.2.1 ht))
  rw [← hX.pCoreOf_sup_eq (by norm_num) h3 hP] at hgX
  obtain ⟨q, hq, a, ha, rfl⟩ :=
    (Ch1Sec3.mem_sup_iff_of_le_normalizer hP.le_normalizer_pCoreOf_two).1 hgX
  have hn : q⁻¹ * t ∈ (T ⊓ I₀) ⊓ Subgroup.normalizer (P : Set G) := by
    refine ⟨(T ⊓ I₀).mul_mem ((T ⊓ I₀).inv_mem (hQT hq)) ht,
      Subgroup.mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · intro hz
      have h2 := (hg (t * z * t⁻¹)).1 ⟨z, hz, rfl⟩
      have e : q⁻¹ * t * z * (q⁻¹ * t)⁻¹ =
          a * ((q * a)⁻¹ * (t * z * t⁻¹) * (q * a)) * a⁻¹ := by group
      rw [e]
      exact P.mul_mem (P.mul_mem ha h2) (P.inv_mem ha)
    · intro hz
      have h1 : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) ∈ P := by
        have e : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) =
            a⁻¹ * (q⁻¹ * t * z * (q⁻¹ * t)⁻¹) * a := by group
        rw [e]
        exact P.mul_mem (P.mul_mem (P.inv_mem ha) hz) ha
      obtain ⟨w, hw, hwe⟩ := (hg (t * z * t⁻¹)).2 h1
      have hwz : w = z := by
        have hwe' : t * w * t⁻¹ = t * z * t⁻¹ := hwe
        simpa using hwe'
      rw [← hwz]
      exact hw
  have e : t = q * (q⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hq hn

theorem not_autCyclic (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) {P : Subgroup G} (hP : IsSylowIn 3 P s.X) :
    ¬ AutCyclic (T ⊓ I₀) P := by
  rintro ⟨cc, hcc, hcyc⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := c.isXi hyp h12
  have h3 : 3 ∣ Nat.card s.X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, (s.relIndex_X_and_pow hyp h12).1]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨-, hO₁, -, -, -, -, -, hc₁, -⟩ := s.dataX
  set V := VZ T s.M₁ with hVdef
  set V₁ := (⁅V, s.X₁⁆ : Subgroup G) with hV₁def
  set V₂ := (⁅V, s.X₂⁆ : Subgroup G) with hV₂def
  have hV := s.isElemAbelian_VZ hyp
  have hVN : s.M₁ ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hV₁V : V₁ ≤ V := commutator_le_of_le_normalizer ((s.X₁_le_X.trans s.le_X).trans hVN)
  have hV₂V : V₂ ≤ V := commutator_le_of_le_normalizer ((s.X₂_le_X.trans s.le_X).trans hVN)
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v (hV₁V hv)
  have hXV₁ : s.X ≤ Subgroup.normalizer (V₁ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₁ hx)
  have hNC : pCoreOf 2 s.X ≤ Subgroup.centralizer (V : Set G) :=
    s.pCoreOf_X_le_centralizer hyp h12
  obtain ⟨a, haJ, ha2, haC₂, haC₁⟩ := s.exists_diag hyp
  have haTI : a ∈ T ⊓ I₀ := c.lt.le (s.baum_le_T₀ (L15420.thompsonJ_le_baum T haJ))
  have haN₁ : a ∈ Subgroup.normalizer (V₁ : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS₁, -⟩ := s.dataX
    exact A4.mem_normalizer_commutator (hVN (s.inM₁.2 haTI.1))
      (hS₁ (L15420.thompsonJ_le_baum T haJ))
  obtain ⟨u, huTI, hu₁, hu₂⟩ := c.exists_swap' hyp h12
  have huV : u ∈ Subgroup.normalizer (V : Set G) := hVN (s.inM₁.2 huTI.1)
  have huV₁ : V₁.map (MulAut.conj u).toMonoidHom = V₂ := by
    rw [hV₁def, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer huV, hu₁]
  have hfr := c.le_pCoreOf_sup_normalizer hyp h12 hP
  have hTQ : (T ⊓ I₀) ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 s.X : Set G) :=
    (inf_le_left.trans ((inf_le_left.trans s.inM₁.2).trans (M₁_le_normalizer_X h12 s))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X)
  obtain ⟨o, ho, a', ha', hao⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hTQ).1 (hfr haTI)
  obtain ⟨o', ho', u', hu', huo⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hTQ).1 (hfr huTI)
  have hoV : ∀ v ∈ V, o * v = v * o := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (hNC ho) v hv).symm
  have ho'V : ∀ v ∈ V, o' * v = v * o' := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (hNC ho') v hv).symm
  have ha'V : a' ∈ Subgroup.normalizer (V : Set G) := hVN (s.inM₁.2 ha'.1.1)
  have hu'V : u' ∈ Subgroup.normalizer (V : Set G) := hVN (s.inM₁.2 hu'.1.1)
  have hA : ∀ v ∈ V, a' * v * a'⁻¹ = a * v * a⁻¹ := by
    intro v hv
    have h1 : a' * v * a'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp ha'V v).mp hv
    rw [hao]
    calc a' * v * a'⁻¹ = (a' * v * a'⁻¹) * o * o⁻¹ := by group
      _ = o * (a' * v * a'⁻¹) * o⁻¹ := by rw [hoV _ h1]
      _ = o * a' * v * (o * a')⁻¹ := by group
  have hA' : ∀ v ∈ V, a'⁻¹ * v * a' = a⁻¹ * v * a := by
    intro v hv
    rw [hao]
    calc a'⁻¹ * v * a' = a'⁻¹ * (o⁻¹ * (o * v)) * a' := by group
      _ = a'⁻¹ * (o⁻¹ * (v * o)) * a' := by rw [hoV v hv]
      _ = (o * a')⁻¹ * v * (o * a') := by group
  have hU : ∀ v ∈ V, u' * v * u'⁻¹ = u * v * u⁻¹ := by
    intro v hv
    have h1 : u' * v * u'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hu'V v).mp hv
    rw [huo]
    calc u' * v * u'⁻¹ = (u' * v * u'⁻¹) * o' * o'⁻¹ := by group
      _ = o' * (u' * v * u'⁻¹) * o'⁻¹ := by rw [ho'V _ h1]
      _ = o' * u' * v * (o' * u')⁻¹ := by group
  have hU' : ∀ v ∈ V, u'⁻¹ * v * u' = u⁻¹ * v * u := by
    intro v hv
    rw [huo]
    calc u'⁻¹ * v * u' = u'⁻¹ * (o'⁻¹ * (o' * v)) * u' := by group
      _ = u'⁻¹ * (o'⁻¹ * (v * o')) * u' := by rw [ho'V v hv]
      _ = (o' * u')⁻¹ * v * (o' * u') := by group
  set g := a'⁻¹ * u'⁻¹ * a' * u' with hgdef
  have hgTI : g ∈ T ⊓ I₀ := by
    have h1 := ha'.1
    have h2 := hu'.1
    exact (T ⊓ I₀).mul_mem ((T ⊓ I₀).mul_mem ((T ⊓ I₀).mul_mem ((T ⊓ I₀).inv_mem h1)
      ((T ⊓ I₀).inv_mem h2)) h1) h2
  have hg : ∀ v ∈ V₁, g * v * g⁻¹ = a⁻¹ * v * a := by
    intro v hv
    have hvV := hV₁V hv
    have hw : u * v * u⁻¹ ∈ V₂ := by
      rw [← huV₁]
      exact ⟨v, hv, by simp [MulAut.conj_apply]⟩
    have hwV : u * v * u⁻¹ ∈ V := hV₂V hw
    have haw : a * (u * v * u⁻¹) * a⁻¹ = u * v * u⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp haC₂ _ hw
      calc a * (u * v * u⁻¹) * a⁻¹ = (u * v * u⁻¹) * a * a⁻¹ := by rw [this]
        _ = u * v * u⁻¹ := by group
    calc g * v * g⁻¹ = a'⁻¹ * (u'⁻¹ * (a' * (u' * v * u'⁻¹) * a'⁻¹) * u') * a' := by
          rw [hgdef]; group
      _ = a'⁻¹ * (u'⁻¹ * (a' * (u * v * u⁻¹) * a'⁻¹) * u') * a' := by rw [hU v hvV]
      _ = a'⁻¹ * (u'⁻¹ * (a * (u * v * u⁻¹) * a⁻¹) * u') * a' := by rw [hA _ hwV]
      _ = a'⁻¹ * (u'⁻¹ * (u * v * u⁻¹) * u') * a' := by rw [haw]
      _ = a'⁻¹ * (u⁻¹ * (u * v * u⁻¹) * u) * a' := by rw [hU' _ hwV]
      _ = a'⁻¹ * v * a' := by group
      _ = a⁻¹ * v * a := hA' v hvV
  have hgN₁ : g ∈ Subgroup.normalizer (V₁ : Set G) := by
    have hpa := s.permutesX hyp h12 (s.inM₁.2 ((T ⊓ I₀).inv_mem ha'.1).1)
    have hpu := s.permutesX hyp h12 (s.inM₁.2 ((T ⊓ I₀).inv_mem hu'.1).1)
    have hfix := PermutesPair.commutator_fix s.dataX.ne hpa hpu
    have hgX₁ : g ∈ Subgroup.normalizer (s.X₁ : Set G) := by
      rw [mem_normalizer_iff_map_conj]
      convert hfix using 3
      rw [commutatorElement_def, hgdef, inv_inv, inv_inv]
    exact A4.mem_normalizer_commutator (hVN (s.inM₁.2 hgTI.1)) hgX₁
  have hgC : g ∉ Subgroup.centralizer (V₁ : Set G) := by
    intro hgc
    apply haC₁
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hg v hv
    have h2 : g * v * g⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.mp hgc v hv
      calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [this]
        _ = v := by group
    have h3 : a⁻¹ * v * a = v := h1.symm.trans h2
    calc v * a = a * (a⁻¹ * v * a) := by group
      _ = a * v := by rw [h3]
  obtain ⟨k₁, hk₁⟩ := hcyc a' ha'
  obtain ⟨k₂, hk₂⟩ := hcyc u' hu'
  have hccP : ∀ k : ℕ, cc ^ k ∈ Subgroup.normalizer (P : Set G) := fun k =>
    Subgroup.pow_mem _ hcc.2 k
  have hgP : ∀ x ∈ P, x * g = g * x := by
    intro x hx
    have hm₂ : cc ^ k₂ * x * (cc ^ k₂)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hccP k₂) x).mp hx
    have hm₁ : cc ^ k₁ * x * (cc ^ k₁)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hccP k₁) x).mp hx
    have hcomm : cc ^ k₁ * cc ^ k₂ = cc ^ k₂ * cc ^ k₁ := by rw [← pow_add, ← pow_add, add_comm]
    have e1 : a' * u' * x * (a' * u')⁻¹ =
        (cc ^ k₁ * cc ^ k₂) * x * (cc ^ k₁ * cc ^ k₂)⁻¹ := by
      calc a' * u' * x * (a' * u')⁻¹ = a' * (u' * x * u'⁻¹) * a'⁻¹ := by group
        _ = a' * (cc ^ k₂ * x * (cc ^ k₂)⁻¹) * a'⁻¹ := by rw [hk₂ x hx]
        _ = cc ^ k₁ * (cc ^ k₂ * x * (cc ^ k₂)⁻¹) * (cc ^ k₁)⁻¹ := hk₁ _ hm₂
        _ = (cc ^ k₁ * cc ^ k₂) * x * (cc ^ k₁ * cc ^ k₂)⁻¹ := by group
    have e2 : u' * a' * x * (u' * a')⁻¹ =
        (cc ^ k₂ * cc ^ k₁) * x * (cc ^ k₂ * cc ^ k₁)⁻¹ := by
      calc u' * a' * x * (u' * a')⁻¹ = u' * (a' * x * a'⁻¹) * u'⁻¹ := by group
        _ = u' * (cc ^ k₁ * x * (cc ^ k₁)⁻¹) * u'⁻¹ := by rw [hk₁ x hx]
        _ = cc ^ k₂ * (cc ^ k₁ * x * (cc ^ k₁)⁻¹) * (cc ^ k₂)⁻¹ := hk₂ _ hm₁
        _ = (cc ^ k₂ * cc ^ k₁) * x * (cc ^ k₂ * cc ^ k₁)⁻¹ := by group
    have e3 : a' * u' * x * (a' * u')⁻¹ = u' * a' * x * (u' * a')⁻¹ := by
      rw [e1, e2, hcomm]
    have e4 : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = (u' * a')⁻¹ * (a' * u' * x * (a' * u')⁻¹) * (u' * a') := by
            rw [hgdef]; group
        _ = (u' * a')⁻¹ * (u' * a' * x * (u' * a')⁻¹) * (u' * a') := by rw [e3]
        _ = x := by group
    calc x * g = g * x * g⁻¹ * g := by rw [e4]
      _ = g * x := by group
  have hg2 : IsPGroup 2 (Subgroup.zpowers g) :=
    hyp.sylow.1.to_le ((Subgroup.zpowers_le.mpr hgTI).trans inf_le_left)
  have hcard := L15420.card_inf_centralizer_eq_two hc₁ hg2 hgN₁ hgC
  obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one
    (V₁ ⊓ Subgroup.centralizer ({g} : Set G))).resolve_left (by
      intro h
      rw [h, Subgroup.card_bot] at hcard
      omega)
  have hgf : g * f * g⁻¹ = f := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hf.2
    calc g * f * g⁻¹ = f * g * g⁻¹ := by rw [this]
      _ = f := by group
  have hPC : P ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro x hx
    have hxX := hP.le hx
    have hxf : x * f * x⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hXV₁ hxX) f).mp hf.1
    have hxg := hgP x hx
    have hxfC : x * f * x⁻¹ ∈ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxg' : x⁻¹ * g = g * x⁻¹ := by
        calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * g) * x⁻¹ := by rw [hxg]
          _ = g * x⁻¹ := by group
      calc x * f * x⁻¹ * g = x * f * (x⁻¹ * g) := by group
        _ = x * f * (g * x⁻¹) := by rw [hxg']
        _ = x * (g * f * g⁻¹) * g * x⁻¹ := by rw [hgf]; group
        _ = (x * g) * f * x⁻¹ := by group
        _ = (g * x) * f * x⁻¹ := by rw [hxg]
        _ = g * (x * f * x⁻¹) := by group
    have hxf1 : x * f * x⁻¹ ≠ 1 := fun h => hf1 (by
      calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    have he := L15420.eq_of_card_eq_two hcard ⟨hxf, hxfC⟩ hf hxf1 hf1
    have hxodd : Odd (orderOf x) := by
      obtain ⟨n, hn⟩ := hP.isPGroup ⟨x, hx⟩
      have ho : orderOf x ∣ 3 ^ n := by
        rw [← Subgroup.orderOf_mk x hx]
        exact orderOf_dvd_of_pow_eq_one hn
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp ho
      rw [hm]
      exact Odd.pow (by norm_num)
    have hcomm : x * f = f * x := by
      calc x * f = x * f * x⁻¹ * x := by group
        _ = f * x := by rw [he]
    exact mem_centralizer_of_card_eq_four hc₁ hV₁2 (hXV₁ hxX) hxodd hf.1 hf1 hcomm
  have hXC : s.X ≤ Subgroup.centralizer (V₁ : Set G) := by
    rw [← hX.pCoreOf_sup_eq (by norm_num) h3 hP]
    exact sup_le (hNC.trans (Subgroup.centralizer_le hV₁V)) hPC
  have hX₁V : s.X₁ ≤ Subgroup.normalizer (V : Set G) := (s.X₁_le_X.trans s.le_X).trans hVN
  have hbot := commutator_inf_centralizer_eq_bot_of_card_eq_four hV hX₁V hO₁ hc₁
  have : V₁ ⊓ Subgroup.centralizer (s.X₁ : Set G) = V₁ := by
    refine inf_eq_left.mpr fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXC (s.X₁_le_X hx)) v hv).symm
  rw [← hV₁def, this] at hbot
  rw [hbot, Subgroup.card_bot] at hc₁
  omega

theorem exists_comp (hAS : Prop134E9He) (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (h19 : Stmt15419 G T) (c : Config15420 s I₀) :
    ∃ (L : Subgroup G) (y : G), Comp15420 s I₀ L y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := c.isXi hyp h12
  obtain ⟨hi, -⟩ := s.relIndex_X_and_pow hyp h12
  have h3 : 3 ∣ Nat.card s.X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ s.X) IsPGroup.of_bot
  have hPc : Nat.card P = 9 := by rw [hX.card_sylow (by norm_num) h3 hP, hi]
  have hP3 : ∀ y ∈ P, y ^ 3 = 1 := fun y hy => hX.pow_eq_one (by norm_num) h3 hP hy
  have hord : ∀ y ∈ P, y ≠ 1 → orderOf y = 3 := fun y hy hy1 =>
    orderOf_eq_prime (hP3 y hy) hy1
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    omega
  have hsq := isSQTKCat_of_hyp hyp c.inH.2
  rcases hAS G I₀ (T ⊓ I₀) s.X P hsq c.inH.2 c.sylow (c.le_X hyp h12) hX hi hP.le
      hP.isPGroup hPc with hN | ⟨L, hL, hq, hXL, hcases⟩
  ·
    exfalso
    have hM : s.M₁ = Subgroup.normalizer (s.X : Set G) :=
      ((h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X).2.1
    have hL₂ : s.L₂ ≤ I₀ := (le_sup_left.trans le_sup_right).trans c.inH.1
    exact (h19 s).2.2.2.1 (hL₂.trans (hN.trans hM.ge))
  rcases hcases with ⟨⟨t, -, -, hPeq, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨-, -, hcyc⟩ | ⟨hTL, htype⟩ |
    ⟨hHL, hHe⟩
  ·
    have hPL : P ⊓ L ≠ ⊥ := by
      intro h
      apply hPne
      rw [hPeq, h]
      simp [conjByElt]
    obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one (P ⊓ L)).resolve_left hPL
    exact ⟨L, y, ⟨hL, hq, hXL, ⟨hP.le hy.1, hy.2⟩, hord y hy.1 hy1, Or.inl htype⟩⟩
  ·
    have hXL' : s.X ≤ L := by rwa [conjClosure_eq_of_le_normalizer hTL] at hXL
    obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
    refine ⟨L, y, ⟨hL, hq, hXL, ⟨hP.le hy, hXL' (hP.le hy)⟩, hord y hy hy1, Or.inr ⟨hTL, ?_⟩⟩⟩
    rcases htype with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  ·
    exact absurd hcyc (c.not_autCyclic hyp h12 hP)
  ·
    have hXL' : s.X ≤ L := by rwa [conjClosure_eq_of_le_normalizer hTL] at hXL
    obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
    refine ⟨L, y, ⟨hL, hq, hXL, ⟨hP.le hy, hXL' (hP.le hy)⟩, hord y hy hy1, Or.inr ⟨hTL, ?_⟩⟩⟩
    rcases htype with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  ·
    have hTL : T ⊓ I₀ ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans hHL
    have hXL' : s.X ≤ L := by rwa [conjClosure_eq_of_le_normalizer hTL] at hXL
    obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hPne
    exact ⟨L, y, ⟨hL, hq, hXL, ⟨hP.le hy, hXL' (hP.le hy)⟩, hord y hy hy1,
      Or.inr ⟨hTL, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hHe))))⟩⟩⟩

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
