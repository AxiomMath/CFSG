module

public import CFSG.Quasithin.Background.GoldschmidtE23Nat
public import CFSG.Quasithin.Background.GoldschmidtE23SL2
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SL2MinimalFaithful

namespace GE23

section NatSyl

variable {V : Type} [CommGroup V]

@[expose] def NatSyl (H : Subgroup (MulAut V)) (U Z : Subgroup V) (e : ℕ)
    (P : Subgroup (MulAut V)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
    ∃ (π : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H) (β : ↥U →* Multiplicative (Fin 2 → K)),
      Function.Surjective π ∧ Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      (∀ (h : ↥H) (u : V), u ∈ U → (h : MulAut V) u ∈ U) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd
            ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))) ∧
      ∀ p : MulAut V, p ∈ P ↔ ∃ t : K, ((π (unipotent t) : ↥H) : MulAut V) = p

@[expose] noncomputable def twistHom {K : Type} [Field K] {U : Subgroup V}
    (β : ↥U →* Multiplicative (Fin 2 → K)) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ↥U →* Multiplicative (Fin 2 → K) where
  toFun u := Multiplicative.ofAdd
    ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem twistHom_apply {K : Type} [Field K] {U : Subgroup V}
    (β : ↥U →* Multiplicative (Fin 2 → K)) (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U) :
    twistHom β g u = Multiplicative.ofAdd
      ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u))) := rfl

variable [Finite V]

theorem exists_natSyl {H : Subgroup (MulAut V)} {U Z : Subgroup V} {e : ℕ}
    (hN : NatData H U Z e) {P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) :
    NatSyl H U Z e P := by
  classical
  obtain ⟨K, iK, iF, hK, π, β, hπs, hβs, hβz, hUinv, hβeq⟩ := hN
  have hπi : Function.Injective π := NatData.injective_of hβs hUinv hβeq
  have hPH : P ≤ H := hP.1
  let eπ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  have hHcard : Nat.card H = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← card_specialLinearGroup_fin_two K]
    exact (Nat.card_congr eπ.toEquiv).symm
  have hPcard : Nat.card P = Nat.card K := by
    obtain ⟨m, hm⟩ := hP.2.1.exists_card_eq
    have hrel : Nat.card P * P.relIndex H = Nat.card H := by
      have h1 := Subgroup.card_mul_index (P.subgroupOf H)
      have h2 : Nat.card (P.subgroupOf H) = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
      rw [h2] at h1
      exact h1
    have hodd : ¬ 2 ∣ P.relIndex H := hP.2.2
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have h1K : 1 < Nat.card K := Finite.one_lt_card
    have hq : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by
      have h2 : 2 ∣ Nat.card K := by
        rw [hK]
        refine dvd_pow_self 2 ?_
        rintro rfl
        simp at hK
        omega
      intro hd
      have h3 : 2 ∣ Nat.card K ^ 2 := dvd_pow h2 two_ne_zero
      have h4 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hKpos
      omega
    have hrelpos : 0 < P.relIndex H := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hv1 : padicValNat 2 (Nat.card P * P.relIndex H) = m := by
      rw [padicValNat.mul Nat.card_pos.ne' hrelpos.ne', hm, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hodd, add_zero]
    have hq0 : Nat.card K ^ 2 - 1 ≠ 0 := by
      intro h0
      have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow two_ne_zero h1K
      omega
    have hv2 : padicValNat 2 (Nat.card K * (Nat.card K ^ 2 - 1)) = e := by
      rw [padicValNat.mul hKpos.ne' hq0, padicValNat.eq_zero_of_not_dvd hq, add_zero, hK,
        padicValNat.prime_pow]
    rw [hrel, hHcard, hv2] at hv1
    rw [hm, hK, ← hv1]
  let S₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (P.subgroupOf H).comap eπ.toMonoidHom
  have hS₀ : Nat.card S₀ = Nat.card K := by
    have h1 : Nat.card S₀ = Nat.card (P.subgroupOf H) :=
      Nat.card_congr ((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm eπ _)).trans
        (MulEquiv.subgroupMap eπ.symm _).symm).toEquiv
    rw [h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).trans hPcard
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hK hS₀
  have hSeq : ∀ γ ∈ S₀, ∃ t : K, γ = g * unipotent t * g⁻¹ := by
    let R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (unipotentHom (F := K)).range.map (MulAut.conj g).toMonoidHom
    have hRS : R ≤ S₀ := by
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      exact hg t.toAdd
    have hRcard : Nat.card R = Nat.card K := by
      have h1 := Nat.card_congr (((unipotentHom (F := K)).range).equivMapOfInjective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
      rw [← h1]
      exact (Nat.card_congr (MonoidHom.ofInjective unipotentHom_injective).toEquiv).symm.trans
        (Nat.card_congr Multiplicative.toAdd)
    have hReq : R = S₀ := Subgroup.eq_of_le_of_card_ge hRS (by rw [hRcard, hS₀])
    intro γ hγ
    rw [← hReq] at hγ
    obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hγ
    exact ⟨t.toAdd, rfl⟩
  refine ⟨K, iK, iF, hK, π.comp (MulAut.conj g).toMonoidHom, twistHom β g⁻¹,
    hπs.comp (MulAut.conj g).surjective, ?_, ?_, fun h u hu => hUinv h u hu, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd w)))
    refine ⟨u, ?_⟩
    rw [twistHom_apply, hu, toAdd_ofAdd, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  · intro u
    rw [← hβz u]
    constructor
    · intro h1
      have h2 := congrArg Multiplicative.toAdd h1
      rw [twistHom_apply, toAdd_ofAdd, toAdd_one] at h2
      have h3 := congrArg (fun x => (g : Matrix (Fin 2) (Fin 2) K).mulVec x) h2
      simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h3
      rw [← ofAdd_toAdd (β u), h3]
      rfl
    · intro h1
      rw [twistHom_apply, h1]
      simp
  · intro γ u hu
    have h1 := hβeq (g * γ * g⁻¹) u hu
    show twistHom β g⁻¹ ⟨((π (g * γ * g⁻¹) : ↥H) : MulAut V) (u : V), hu⟩ = _
    have hmat : g⁻¹ * (g * γ * g⁻¹) = γ * g⁻¹ := by
      rw [← mul_assoc g⁻¹ (g * γ) g⁻¹, ← mul_assoc g⁻¹ g γ, inv_mul_cancel, one_mul]
    rw [twistHom_apply, h1, toAdd_ofAdd, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      twistHom_apply, toAdd_ofAdd, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hmat]
  · intro p
    constructor
    · intro hp
      have hpH : p ∈ H := hPH hp
      obtain ⟨γ, hγ⟩ := hπs ⟨p, hpH⟩
      have hγS : γ ∈ S₀ := by
        show eπ γ ∈ P.subgroupOf H
        rw [Subgroup.mem_subgroupOf]
        show ((π γ : ↥H) : MulAut V) ∈ P
        rw [hγ]
        exact hp
      obtain ⟨t, ht⟩ := hSeq γ hγS
      refine ⟨t, ?_⟩
      show ((π (g * unipotent t * g⁻¹) : ↥H) : MulAut V) = p
      rw [← ht, hγ]
    · rintro ⟨t, rfl⟩
      have := hg t
      have h2 : eπ (g * unipotent t * g⁻¹) ∈ P.subgroupOf H := this
      exact Subgroup.mem_subgroupOf.1 h2

@[expose] def lineHom (K : Type) [Field K] : Multiplicative K →* Multiplicative (Fin 2 → K) where
  toFun c := Multiplicative.ofAdd ![Multiplicative.toAdd c, 0]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp

theorem lineHom_injective (K : Type) [Field K] : Function.Injective (lineHom K) := by
  intro a b h
  have := congrFun (congrArg Multiplicative.toAdd h) 0
  exact Multiplicative.toAdd.injective (by simpa [lineHom] using this)

theorem mem_range_lineHom {K : Type} [Field K] {w : Multiplicative (Fin 2 → K)} :
    w ∈ (lineHom K).range ↔ Multiplicative.toAdd w 1 = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [lineHom]
  · intro h
    refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd w 0), ?_⟩
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · simp [lineHom]
    · simp [lineHom, h]

omit [Finite V] in
theorem fixV_le_of_ker {K : Type} [Field K] {U : Subgroup V} (β : ↥U →* Multiplicative (Fin 2 → K))
    {F : Subgroup V} (hker : ∀ u : ↥U, β u = 1 → (u : V) ∈ F) {u u' : ↥U} (h : β u = β u')
    (hu' : (u' : V) ∈ F) : (u : V) ∈ F := by
  have h1 : β (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hker _ h1
  have : (u : V) = ((u * u'⁻¹ : ↥U) : V) * (u' : V) := by simp
  rw [this]
  exact F.mul_mem h2 hu'

theorem NatSyl.facts {H : Subgroup (MulAut V)} {U Z : Subgroup V} {e : ℕ}
    {P : Subgroup (MulAut V)} (hS : NatSyl H U Z e P) (hZP : Z ≤ fixV P)
    (hoff : Nat.card V ≤ Nat.card P * Nat.card (fixV P)) :
    (∀ a ∈ P, a ≠ 1 → ∀ u ∈ U, a u = u → u ∈ fixV P) ∧
    (∀ a ∈ P, ∀ u ∈ U, a u * u⁻¹ ∈ fixV P) ∧
    (∃ u ∈ U, u ∈ fixV P ∧ u ∉ Z) ∧
    (∃ w ∈ H, H ≤ P ⊔ P.map (MulAut.conj w).toMonoidHom) ∧
    Nat.card P = 2 ^ e ∧ 1 ≤ e ∧ Nat.card U = Nat.card ↥(Z ⊓ U) * 4 ^ e := by
  classical
  obtain ⟨K, iK, iF, hK, π, β, hπs, hβs, hβz, hUinv, hβeq, hPmem⟩ := hS
  have hπi : Function.Injective π := NatData.injective_of hβs hUinv hβeq
  have h1K : 1 < Nat.card K := Finite.one_lt_card
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hPcard : Nat.card P = Nat.card K := by
    have hbij : Function.Bijective (fun t : K => (⟨((π (unipotent t) : ↥H) : MulAut V),
        (hPmem _).2 ⟨t, rfl⟩⟩ : ↥P)) := by
      constructor
      · intro a b hab
        have h1 : ((π (unipotent a) : ↥H) : MulAut V) = ((π (unipotent b) : ↥H) : MulAut V) :=
          congrArg (fun x : ↥P => (x : MulAut V)) hab
        exact unipotent_injective (hπi (Subtype.ext h1))
      · rintro ⟨p, hp⟩
        obtain ⟨t, ht⟩ := (hPmem p).1 hp
        exact ⟨t, Subtype.ext ht⟩
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hPH : ∀ p ∈ P, p ∈ H := by
    intro p hp
    obtain ⟨t, rfl⟩ := (hPmem p).1 hp
    exact (π (unipotent t)).2
  have hact : ∀ (t : K) (u : ↥U) (hu : ((π (unipotent t) : ↥H) : MulAut V) (u : V) ∈ U),
      Multiplicative.toAdd (β ⟨((π (unipotent t) : ↥H) : MulAut V) (u : V), hu⟩) =
        ![Multiplicative.toAdd (β u) 0 + t * Multiplicative.toAdd (β u) 1,
          Multiplicative.toAdd (β u) 1] := by
    intro t u hu
    rw [hβeq (unipotent t) u hu, toAdd_ofAdd, unipotent_mulVec]
  have hrange : Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi, Fin.prod_univ_two]
    ring
  have hline : ∀ c : K, ∃ u : ↥U, (u : V) ∈ fixV P ∧ β u = Multiplicative.ofAdd ![c, 0] := by
    set F := fixV P with hF
    let W' : Subgroup ↥U := F.comap U.subtype
    have hkerW : β.ker ≤ W' := fun u hu => hZP ((hβz u).1 hu)
    have hWline : ∀ w ∈ W'.map β, Multiplicative.toAdd w 1 = 0 := by
      rintro _ ⟨u, hu, rfl⟩
      have hp : ((π (unipotent (1 : K)) : ↥H) : MulAut V) ∈ P := (hPmem _).2 ⟨1, rfl⟩
      have hfix : ((π (unipotent (1 : K)) : ↥H) : MulAut V) (u : V) = u := hu _ hp
      have hu' := hUinv (π (unipotent 1)) u u.2
      have h1 := hact 1 u hu'
      have h2 : (⟨((π (unipotent (1 : K)) : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u :=
        Subtype.ext hfix
      rw [h2] at h1
      have h0 := congrFun h1 0
      simpa using h0
    have hWcard : Nat.card W' = Nat.card ↥(F ⊓ U) := by
      have : W' = (F ⊓ U).subgroupOf U := (Subgroup.inf_subgroupOf_right F U).symm
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hUle : Nat.card ↥U ≤ Nat.card P * Nat.card W' := by
      have e1 := B2F.card_sup_mul_card_inf_of_commute (A := U) (B := F)
        (fun a _ b _ => mul_comm a b)
      have e2 : Nat.card ↥(U ⊔ F) ≤ Nat.card V := Subgroup.card_le_card_group _
      have e3 : Nat.card ↥(U ⊓ F) = Nat.card ↥(F ⊓ U) := by rw [inf_comm]
      rw [hWcard, ← e3]
      have hFpos : 0 < Nat.card ↥F := Nat.card_pos
      have : Nat.card ↥U * Nat.card ↥F ≤ Nat.card P * Nat.card ↥(U ⊓ F) * Nat.card ↥F := by
        calc Nat.card ↥U * Nat.card ↥F = Nat.card ↥(U ⊔ F) * Nat.card ↥(U ⊓ F) := e1.symm
          _ ≤ Nat.card V * Nat.card ↥(U ⊓ F) := Nat.mul_le_mul_right _ e2
          _ ≤ (Nat.card P * Nat.card ↥F) * Nat.card ↥(U ⊓ F) := Nat.mul_le_mul_right _ hoff
          _ = Nat.card P * Nat.card ↥(U ⊓ F) * Nat.card ↥F := by ring
      exact Nat.le_of_mul_le_mul_right this hFpos
    have hidx : W'.index ≤ Nat.card K := by
      have h1 := Subgroup.card_mul_index W'
      have hWpos : 0 < Nat.card W' := Nat.card_pos
      rw [← hPcard]
      have : Nat.card W' * W'.index ≤ Nat.card W' * Nat.card P := by
        rw [h1, mul_comm (Nat.card W')]
        exact hUle
      exact Nat.le_of_mul_le_mul_left this hWpos
    have hrel := Subgroup.relIndex_mul_relIndex β.ker W' ⊤ hkerW le_top
    rw [Subgroup.relIndex_ker, Subgroup.relIndex_ker, Subgroup.relIndex_top_right,
      Subgroup.map_top, MonoidHom.range_eq_top_of_surjective β hβs, Subgroup.card_top,
      hrange] at hrel
    have hcardβW : Nat.card K ≤ Nat.card ↥(W'.map β) := by
      have hpos : 0 < Nat.card K := Nat.card_pos
      have : Nat.card K * Nat.card K ≤ Nat.card K * Nat.card ↥(W'.map β) := by
        calc Nat.card K * Nat.card K = Nat.card K ^ 2 := (sq _).symm
          _ = Nat.card ↥(W'.map β) * W'.index := hrel.symm
          _ ≤ Nat.card ↥(W'.map β) * Nat.card K := Nat.mul_le_mul_left _ hidx
          _ = Nat.card K * Nat.card ↥(W'.map β) := mul_comm _ _
      exact Nat.le_of_mul_le_mul_left this hpos
    have hle : W'.map β ≤ (lineHom K).range := fun w hw => mem_range_lineHom.2 (hWline w hw)
    have hlcard : Nat.card ↥(lineHom K).range = Nat.card K :=
      (Nat.card_congr (MonoidHom.ofInjective (lineHom_injective K)).toEquiv).symm.trans
        (Nat.card_congr Multiplicative.toAdd)
    have heq : W'.map β = (lineHom K).range :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hlcard]; exact hcardβW)
    intro c
    have hmem : Multiplicative.ofAdd ![c, 0] ∈ W'.map β := by
      rw [heq]
      exact ⟨Multiplicative.ofAdd c, rfl⟩
    obtain ⟨u, hu, hβu⟩ := hmem
    exact ⟨u, hu, hβu⟩
  have hker : ∀ x : ↥U, β x = 1 → (x : V) ∈ fixV P := fun x hx => hZP ((hβz x).1 hx)
  refine ⟨?_, ?_, ?_, ?_, hPcard.trans hK, he1, ?_⟩
  ·
    intro a ha ha1 u hu hau
    obtain ⟨t, rfl⟩ := (hPmem a).1 ha
    have ht : t ≠ 0 := by
      rintro rfl
      apply ha1
      rw [unipotent_zero, map_one]
      rfl
    let u' : ↥U := ⟨u, hu⟩
    have hu1 := hUinv (π (unipotent t)) u hu
    have h1 := hact t u' hu1
    have h2 : (⟨((π (unipotent t) : ↥H) : MulAut V) u, hu1⟩ : ↥U) = u' := Subtype.ext hau
    rw [h2] at h1
    have h0 := congrFun h1 0
    have hw1 : Multiplicative.toAdd (β u') 1 = 0 := by
      simp only [Matrix.cons_val_zero] at h0
      have h3 : t * Multiplicative.toAdd (β u') 1 = 0 := by
        have := h0
        linear_combination -this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 ht
      · exact h4
    obtain ⟨u'', hfix, hβ⟩ := hline (Multiplicative.toAdd (β u') 0)
    refine fixV_le_of_ker β hker (u := u') (u' := u'') ?_ hfix
    rw [hβ]
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · simp
    · simp [hw1]
  ·
    intro a ha u hu
    obtain ⟨t, rfl⟩ := (hPmem a).1 ha
    let u' : ↥U := ⟨u, hu⟩
    have hu1 := hUinv (π (unipotent t)) u hu
    have h1 := hact t u' hu1
    obtain ⟨u'', hfix, hβ⟩ := hline (t * Multiplicative.toAdd (β u') 1)
    let x : ↥U := ⟨((π (unipotent t) : ↥H) : MulAut V) u, hu1⟩ * u'⁻¹
    have hx : (x : V) ∈ fixV P := by
      refine fixV_le_of_ker β hker (u := x) (u' := u'') ?_ hfix
      rw [hβ]
      show β (⟨((π (unipotent t) : ↥H) : MulAut V) u, hu1⟩ * u'⁻¹) = _
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, h1]
      ext i
      fin_cases i
      · simp
      · simp
    simpa [x, u'] using hx
  ·
    obtain ⟨u, hfix, hβ⟩ := hline 1
    refine ⟨(u : V), u.2, hfix, fun hZu => ?_⟩
    have h1 := (hβz u).2 hZu
    rw [hβ] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
    simp at h2
  ·
    refine ⟨((π weylSL : ↥H) : MulAut V), (π weylSL).2, ?_⟩
    let Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (P ⊔ P.map (MulAut.conj ((π weylSL : ↥H) : MulAut V)).toMonoidHom).comap
        (H.subtype.comp π)
    have hU₀ : (unipotentHom (F := K)).range ≤ Q := by
      rintro _ ⟨t, rfl⟩
      exact Subgroup.mem_sup_left ((hPmem _).2 ⟨t.toAdd, rfl⟩)
    have hU₁ : (unipotentHom (F := K)).range.map
        (MulAut.conj (weylSL : Matrix.SpecialLinearGroup (Fin 2) K)).toMonoidHom ≤ Q := by
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine Subgroup.mem_sup_right ⟨((π (unipotent t.toAdd) : ↥H) : MulAut V),
        (hPmem _).2 ⟨t.toAdd, rfl⟩, ?_⟩
      simp [MulAut.conj_apply, map_mul, map_inv]
      rfl
    have hQ : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ Q := by
      rw [sl2_eq_sup_conj]
      exact sup_le hU₀ hU₁
    intro h hh
    obtain ⟨γ, hγ⟩ := hπs ⟨h, hh⟩
    have h3 : ((π γ : ↥H) : MulAut V) ∈ P ⊔ P.map (MulAut.conj ((π weylSL : ↥H) :
        MulAut V)).toMonoidHom := hQ (Subgroup.mem_top γ)
    rw [hγ] at h3
    exact h3
  ·
    have h1 := Subgroup.card_ker_mul_card_range β
    have hker' : β.ker = Z.subgroupOf U := by
      ext u
      rw [MonoidHom.mem_ker, hβz u]
      rfl
    have h2 : Nat.card β.ker = Nat.card ↥(Z ⊓ U) := by
      rw [hker', ← Subgroup.inf_subgroupOf_right Z U]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [MonoidHom.range_eq_top_of_surjective β hβs, Subgroup.card_top, hrange, h2, hK] at h1
    have h4 : ((2 : ℕ) ^ e) ^ 2 = 4 ^ e := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [← h1, h4]

end NatSyl

end GE23

end CFSG.Quasithin
