module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondCaseI
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem le_normalizer_of_le_of_abelian {V A C : Subgroup G}
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hA : A ≤ V) (hC : C ≤ V) :
    C ≤ Subgroup.normalizer (A : Set G) := by
  intro z hz
  have hzV : z ∈ V := hC hz
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : z * h * z⁻¹ = h := by
      rw [hab z hzV h (hA hh), mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hh
    have hV : z * h * z⁻¹ ∈ V := hA hh
    have hc : z⁻¹ * (z * h * z⁻¹) = (z * h * z⁻¹) * z⁻¹ := hab _ (V.inv_mem hzV) _ hV
    have e : h = z * h * z⁻¹ := by
      calc h = z⁻¹ * (z * h * z⁻¹) * z := by group
        _ = (z * h * z⁻¹) * z⁻¹ * z := by rw [hc]
        _ = z * h * z⁻¹ := by group
    rw [e]
    exact hh

theorem exists_eq_commutator_of_mem_comm_zpowers {V : Subgroup G} {x : G} (hx2 : x * x = 1)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hn : ∀ v ∈ V, x * v * x⁻¹ ∈ V) {e : G}
    (he : e ∈ ⁅V, Subgroup.zpowers x⁆) : ∃ v ∈ V, e = ⁅v, x⁆ := by
  have key : ∀ a ∈ V, ∀ b ∈ V, ⁅a, x⁆ * ⁅b, x⁆ = ⁅a * b, x⁆ := by
    intro a ha b hb
    have hwa : x * a⁻¹ * x⁻¹ ∈ V := hn _ (V.inv_mem ha)
    have hwb : x * b⁻¹ * x⁻¹ ∈ V := hn _ (V.inv_mem hb)
    have hc1 : (x * a⁻¹ * x⁻¹) * b = b * (x * a⁻¹ * x⁻¹) := hab _ hwa _ hb
    have hc2 : (x * a⁻¹ * x⁻¹) * (x * b⁻¹ * x⁻¹) = (x * b⁻¹ * x⁻¹) * (x * a⁻¹ * x⁻¹) :=
      hab _ hwa _ hwb
    calc ⁅a, x⁆ * ⁅b, x⁆ = a * ((x * a⁻¹ * x⁻¹) * b) * (x * b⁻¹ * x⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = a * (b * (x * a⁻¹ * x⁻¹)) * (x * b⁻¹ * x⁻¹) := by rw [hc1]
      _ = a * b * ((x * a⁻¹ * x⁻¹) * (x * b⁻¹ * x⁻¹)) := by group
      _ = a * b * ((x * b⁻¹ * x⁻¹) * (x * a⁻¹ * x⁻¹)) := by rw [hc2]
      _ = ⁅a * b, x⁆ := by simp only [commutatorElement_def]; group
  have hinv : ∀ a ∈ V, ⁅a, x⁆⁻¹ = ⁅a⁻¹, x⁆ := by
    intro a ha
    have hu : x * a * x⁻¹ ∈ V := hn a ha
    have hc : (x * a * x⁻¹) * a⁻¹ = a⁻¹ * (x * a * x⁻¹) := hab _ hu _ (V.inv_mem ha)
    calc ⁅a, x⁆⁻¹ = (x * a * x⁻¹) * a⁻¹ := by simp only [commutatorElement_def]; group
      _ = a⁻¹ * (x * a * x⁻¹) := hc
      _ = ⁅a⁻¹, x⁆ := by simp only [commutatorElement_def]; group
  let H : Subgroup G :=
    { carrier := {e | ∃ v ∈ V, e = ⁅v, x⁆}
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, rfl⟩
        exact ⟨v₁ * v₂, V.mul_mem hv₁ hv₂, key v₁ hv₁ v₂ hv₂⟩
      one_mem' := ⟨1, V.one_mem, by rw [commutatorElement_one_left]⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, V.inv_mem hv, hinv v hv⟩ }
  have hgen : Subgroup.closure {g | ∃ q ∈ V, ⁅q, x⁆ = g} ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact (⟨q, hq, rfl⟩ : ∃ v ∈ V, ⁅q, x⁆ = ⁅v, x⁆)
  rw [commutator_zpowers_eq_closure hx2] at he
  exact hgen he

theorem hasDimOn_contradiction {V Z C₀ : Subgroup G} {x : G} {k m : ℕ}
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hxn : x ∈ Subgroup.normalizer (V : Set G))
    (hZV : Z ≤ V) (hCV : C₀ ≤ V) (hEZ : ⁅V, Subgroup.zpowers x⁆ ⊓ Z = ⊥)
    (hcard : Nat.card C₀ = Nat.card Z) (hq : 2 ≤ Nat.card Z) (hkZ : HasDimOn V Z k x)
    (hmC : HasDimOn V C₀ m x) (hkm : k ≤ m) {c : G}
    (hcE : c ∈ ⁅V, Subgroup.zpowers x⁆) (hcC : c ∈ C₀) (hc1 : c ≠ 1) : False := by
  have hEV : ⁅V, Subgroup.zpowers x⁆ ≤ V := commutator_zpowers_le hxn
  unfold HasDimOn at hkZ hmC
  set E : Subgroup G := ⁅V, Subgroup.zpowers x⁆
  have hP1 := card_sup_mul_card_inf_of_normalizer
    (A := E) (C := Z) (le_normalizer_of_le_of_abelian hab hEV hZV)
  have hP2 := card_sup_mul_card_inf_of_normalizer
    (A := E) (C := C₀) (le_normalizer_of_le_of_abelian hab hEV hCV)
  rw [hEZ, Subgroup.card_bot, mul_one, hkZ] at hP1
  rw [hmC, hcard, ← hP1] at hP2
  have hRpos : 0 < Nat.card Z ^ (k + 1) := pow_pos (by omega) _
  have hpow : Nat.card Z ^ (k + 1) ≤ Nat.card Z ^ (m + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hPpos : 0 < Nat.card Z ^ (m + 1) := pow_pos (by omega) _
  have hK0 : Nat.card ↥(E ⊓ C₀) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hP2
    omega
  haveI : Finite ↥(E ⊓ C₀) := Nat.finite_of_card_ne_zero hK0
  have hKne : E ⊓ C₀ ≠ ⊥ := by
    intro h
    apply hc1
    have hm : c ∈ E ⊓ C₀ := Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    rw [h, Subgroup.mem_bot] at hm
    exact hm
  have ha : 2 ≤ Nat.card ↥(E ⊓ C₀) := by
    have h1 := (Subgroup.one_lt_card_iff_ne_bot (E ⊓ C₀)).mpr hKne
    omega
  have h2 : Nat.card Z ^ (m + 1) * 2 ≤ Nat.card Z ^ (m + 1) * Nat.card ↥(E ⊓ C₀) :=
    Nat.mul_le_mul_left _ ha
  omega

theorem OddSetup.inf_QB_eq {V V' : Subgroup G} (S : OddSetup M Q Z B V V') {Y : Subgroup G}
    (hY : IsZConjugate Z Y) (hYZ : Y ≠ Z) (hYV : Y ≤ V) (hα : V ≤ QB Y) :
    Q ⊓ QB Y = V := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := S.dec u hu.1
    have haY : a ∈ QB Y := hα ha
    have hbY : b ∈ QB Y := by
      have := (QB Y).mul_mem ((QB Y).inv_mem haY) hu.2
      simpa using this
    by_cases hbZ : b ∈ Z
    · exact V.mul_mem ha (S.ZV hbZ)
    · exact absurd hbY (S.not_mem_QB_of_dual hY hYZ hYV hb hbZ)
  · exact le_inf S.VQ hα

theorem caseII_iff_comm (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) :
    (∀ z' ∈ Z, ∀ q ∈ Q, q⁻¹ * x * q = x * z' → z' = 1) ↔
      (∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1) := by
  constructor
  · intro h q hq hqZ
    refine h _ hqZ q⁻¹ (Q.inv_mem hq) ?_
    have := (comm_eq_iff_conj hxZ hqZ).mp rfl
    simpa using this
  · intro h z' hz' q hq hqz
    have hp : ⁅q⁻¹, x⁆ = z' := by
      refine (comm_eq_iff_conj hxZ hz').mpr ?_
      simpa using hqz
    have := h q⁻¹ (Q.inv_mem hq) (hp ▸ hz')
    rw [hp] at this
    exact this

theorem caseII_comm (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hII : ∀ z' ∈ Z, ∀ q ∈ Q, q⁻¹ * x * q = x * z' → z' = 1) :
    ⁅V₁, Subgroup.zpowers x⁆ ⊓ Z = ⊥ ∧ ⁅V₁, Subgroup.zpowers x⁆ ≠ ⊥ ∧
      ∀ c ∈ ⁅V₁, Subgroup.zpowers x⁆, x * c = c * x := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxL := lin_x_mem_Lgen_of_sit hb hc hS hn hs
  obtain ⟨-, hV₁Q, -, -, -, -, hN₁, hN₂, -, -⟩ := hS.basic
  have hxn₁ := hN₁ hxL
  have hxn₂ := hN₂ hxL
  obtain ⟨R⟩ := exists_restModel hc hS hn
  have S₀ := OddSetup.of_linSetup hc hS (p31_of hb hc hS hn)
  have hII' := (caseII_iff_comm hxZ).mp hII
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro e he
    obtain ⟨v, hv, rfl⟩ := exists_eq_commutator_of_mem_comm_zpowers hx2 S₀.abV
      (fun v hv => (Subgroup.mem_normalizer_iff.mp hxn₁ v).mp hv) he.1
    rw [hII' v (hV₁Q hv) he.2]
    exact Subgroup.one_mem _
  · obtain ⟨q', hq'V, hq'T⟩ := R.exists_moved hs hx hxn₁ hxn₂
    intro hE
    have hmem : ⁅q', x⁆ ∈ ⁅V₁, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator hq'V (Subgroup.mem_zpowers x)
    rw [hE, Subgroup.mem_bot] at hmem
    apply hq'T
    have h1 := (R.xact x hx).pi_comm R.hyp hx.1 (hV₁Q hq'V)
    rw [hmem, Tim79.QuadModel.pi_one R.M₀] at h1
    exact (sub_eq_zero.mp h1.symm).symm
  · intro c hc'
    have hcQ : c ∈ Q := hV₁Q (commutator_zpowers_le hxn₁ hc')
    have hcN : R.M₀.π c ∈ R.Nsp hx := by
      have hmem : c ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) :=
        Subgroup.mem_sup_left (Subgroup.commutator_mono hV₁Q le_rfl hc')
      exact ((R.mem_comm_sup_iff hx hx2).mp hmem).2
    exact R.comm_eq_of_mem_Nsp hs hx hxn₁ hxn₂ hcQ hcN

theorem lin28Cond_caseII (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hII : ∀ z' ∈ Z, ∀ q ∈ Q, q⁻¹ * x * q = x * z' → z' = 1) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxL := lin_x_mem_Lgen_of_sit hb hc hS hn hs
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, -, hN₁, hN₂, hcard₁, hcard₂⟩ := hS.basic
  have hxn₁ := hN₁ hxL
  have hxn₂ := hN₂ hxL
  obtain ⟨R⟩ := exists_restModel hc hS hn
  have S₀ := OddSetup.of_linSetup hc hS (p31_of hb hc hS hn)
  obtain ⟨q', hq'V, hq'T⟩ := R.exists_moved hs hx hxn₁ hxn₂
  have hq'Q : q' ∈ Q := hV₁Q hq'V
  have hcQ : ⁅q', x⁆ ∈ Q := comm_mem_Q H hs.memM hq'Q
  have hcV₁ : ⁅q', x⁆ ∈ V₁ := by
    have e : ⁅q', x⁆ = q' * (x * q'⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact V₁.mul_mem hq'V ((Subgroup.mem_normalizer_iff.mp hxn₁ q'⁻¹).mp (V₁.inv_mem hq'V))
  have hπc : R.M₀.π ⁅q', x⁆ ≠ 0 := by
    rw [(R.xact x hx).pi_comm R.hyp hx.1 hq'Q]
    intro h
    exact hq'T (sub_eq_zero.mp h).symm
  have hcZ : ⁅q', x⁆ ∉ Z := fun h => hπc ((R.M₀.π_ker _ hcQ).mpr h)
  have hc1 : ⁅q', x⁆ ≠ 1 := fun h => hcZ (h ▸ Z.one_mem)
  have hclc : InZClass Z ⁅q', x⁆ := (S₀.p31 _ hcQ hc1).mpr (Or.inl hcV₁)
  obtain ⟨g, z₀, hz₀, -, hcg⟩ := hclc
  have hC₀c : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hcC₀ : ⁅q', x⁆ ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, hcg]
    simpa [mul_assoc] using hz₀
  obtain ⟨hC₀V₁, hC₀Q, hC₀Z⟩ := S₀.root_le_V hC₀c hcC₀ hcV₁ hcZ
  have hα := linModuleStatement_holds G M Q Z B n V₁ V₂ hb hc hS hn (conjSubgroup g Z) hC₀c hC₀Z
  have hV₁QB : V₁ ≤ QB (conjSubgroup g Z) := hα.1 hC₀V₁
  have hQV₁ : Q ⊓ QB (conjSubgroup g Z) = V₁ := S₀.inf_QB_eq hC₀c hC₀Z hC₀V₁ hV₁QB
  have hxc : x * ⁅q', x⁆ = ⁅q', x⁆ * x :=
    R.comm_eq_of_mem_Nsp hs hx hxn₁ hxn₂ hcQ (R.pi_comm_mem_Nsp hx hq'Q)
  have hxN : x ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) :=
    hC₀c.mem_normalizer_of_commute H hc1 hcC₀ hxc
  by_cases hxQ : x ∈ QB (conjSubgroup g Z)
  · have hXle : X ≤ QB (conjSubgroup g Z) :=
      IsZConjugate.le_QB_of_mem H hC₀c hs.conj hs.ne_one hs.mem hxQ
    have hC₀X : conjSubgroup g Z ≤ QB X := (IsZConjugate.le_QB_iff H hC₀c hs.conj).mp hXle
    exact ⟨conjSubgroup g Z, hC₀c, le_inf hC₀Q hC₀X⟩
  exfalso
  have hQ' : conjSubgroup g Q = QB (conjSubgroup g Z) := (QB_conj_eq H g).symm
  have hc' := hc.conjBy g
  have hS' := hS.conj g
  have hxM' : x ∈ conjSubgroup g M := by
    rw [← normalizer_conj_eq H g]
    exact hxN
  have hs' : Sit (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z) X x := by
    refine ⟨H.conj g, ?_, hs.mem, hs.ne_one, hxM', by rw [hQ']; exact hxQ⟩
    obtain ⟨h, hh⟩ := hs.conj
    exact ⟨h * g⁻¹, by rw [hh, ← conjSubgroup_mul, inv_mul_cancel_right]⟩
  have hxZ' : ∀ z ∈ conjSubgroup g Z, x * z * x⁻¹ = z := hs'.x_cent (smith_1_12 hs')
  have hq'Q' : q' ∈ conjSubgroup g Q := by
    rw [hQ']
    exact hV₁QB hq'V
  have hcomm : ∀ z ∈ conjSubgroup g Z, ∃ q ∈ conjSubgroup g Q, ⁅q, x⁆ = z := by
    rcases theta_dichotomy_comm hb hc' hS' hn hs' with h | h
    · exact h
    · exact absurd (h q' hq'Q' hcC₀) hc1
  have hcomm' : ∀ z' ∈ conjSubgroup g Z, ∃ q ∈ conjSubgroup g Q, q⁻¹ * x * q = x * z' := by
    intro z' hz'
    obtain ⟨p, hp, hpz⟩ := hcomm z' hz'
    refine ⟨p⁻¹, (conjSubgroup g Q).inv_mem hp, ?_⟩
    have := (comm_eq_iff_conj hxZ' hz').mp hpz
    simpa using this
  have hD0 : conjSubgroup g Q ⊓ QB X = ⊥ := by
    by_contra hne
    obtain ⟨A, hA, hAle⟩ := lin28Cond_caseI hb hc' hS' hn hs' hcomm' hne
    have c4 := c4_of_A hb hc' hS' hn hs' hA (hAle.trans inf_le_left) (hAle.trans inf_le_right)
    have hxcl : InZClass (conjSubgroup g Z) x :=
      inZClass_of_mem_root hs'.conj hs'.mem hs'.ne_one
    have hq'x : q' * x * q'⁻¹ = x * ⁅q', x⁆ := (comm_eq_iff_conj hxZ' hcC₀).mp rfl
    have hcl : InZClass (conjSubgroup g Z) (x * ⁅q', x⁆) := by
      rw [← hq'x]
      exact (inZClass_conj_iff q').mpr hxcl
    exact hc1 (c4 _ hcC₀ hcl)
  have hxL' := lin_x_mem_Lgen_of_sit hb hc' hS' hn hs'
  have hrank := lin115RankStatement_holds G (conjSubgroup g M) (conjSubgroup g Q)
    (conjSubgroup g Z) (conjSubgroup g B) X x n (conjSubgroup g V₁) (conjSubgroup g V₂) hc' hS'
    hn hs' hxL' hD0
  have hZQ' : Z ≤ conjSubgroup g Q := by
    rw [hQ']
    exact hZV₁.trans hV₁QB
  have hZconj : IsZConjugate (conjSubgroup g Z) Z :=
    ⟨g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]⟩
  have hp31' := p31_of hb hc' hS' hn
  have hZunion : (Z : Set G) ⊆ (conjSubgroup g V₁ : Set G) ∪ (conjSubgroup g V₂ : Set G) := by
    intro z hz
    by_cases hz1 : z = 1
    · left
      rw [hz1]
      exact (conjSubgroup g V₁).one_mem
    · exact (hp31' z (hZQ' hz) hz1).mp (inZClass_of_mem_root hZconj hz hz1)
  have hmod' := linModuleStatement_holds G (conjSubgroup g M) (conjSubgroup g Q)
    (conjSubgroup g Z) (conjSubgroup g B) n (conjSubgroup g V₁) (conjSubgroup g V₂) hb hc' hS' hn
    Z hZconj hC₀Z.symm
  have hQZ : QB Z = Q := H.QB_Z
  have hrankV : HasDimOn V₁ (conjSubgroup g Z) (n / 2) x := by
    rcases SubgroupClass.subset_union.mp hZunion with hZ1 | hZ2
    · have h1 : conjSubgroup g V₁ ≤ Q := hQZ ▸ hmod'.1 hZ1
      have h1' : conjSubgroup g V₁ ≤ conjSubgroup g Q := Subgroup.map_mono hV₁Q
      have h2 : conjSubgroup g V₁ ≤ V₁ :=
        (le_inf h1 (hQ' ▸ h1') : conjSubgroup g V₁ ≤ Q ⊓ QB (conjSubgroup g Z)).trans hQV₁.le
      have h3 : conjSubgroup g V₁ = V₁ :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [card_conjSubgroup])
      rw [h3] at hrank
      exact hrank.1
    · have h1 : conjSubgroup g V₂ ≤ Q := hQZ ▸ hmod'.2 hZ2
      have h1' : conjSubgroup g V₂ ≤ conjSubgroup g Q := Subgroup.map_mono hV₂Q
      have h2 : conjSubgroup g V₂ ≤ V₁ :=
        (le_inf h1 (hQ' ▸ h1') : conjSubgroup g V₂ ≤ Q ⊓ QB (conjSubgroup g Z)).trans hQV₁.le
      have h3 : conjSubgroup g V₂ = V₁ :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [card_conjSubgroup, hcard₁, hcard₂])
      rw [h3] at hrank
      exact hrank.2
  obtain ⟨k, -, hkn, hk₁, -⟩ := linRankBoundStatement_holds G M Q Z B n V₁ V₂ hc hS x hxL
    hs.notQ (by rw [hx2]; exact Q.one_mem)
  have hEZ := (caseII_comm hb hc hS hn hs hII).1
  exact hasDimOn_contradiction (k := k) (m := n / 2) S₀.abV hxn₁ hZV₁ hC₀V₁ hEZ hC₀c.card_eq
    (by have := H.q4; omega) hk₁ hrankV hkn
    (Subgroup.commutator_mem_commutator hq'V (Subgroup.mem_zpowers x)) hcC₀ hc1

end CFSG.RankThree.GF2n.Smith81
