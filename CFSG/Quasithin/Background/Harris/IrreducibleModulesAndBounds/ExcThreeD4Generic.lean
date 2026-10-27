module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.RankThree.PerfectCover

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem false_of_cover_rank_prime {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S)
    (hlt : 2 * (r + 1) < orderOf (2 : ZMod p)) : False := by
  obtain ⟨f, -⟩ := exists_mulEquiv_of_cover h.L_comp.2.2 h.H_irr e hCover
  have hm := m_le_of_autRank h f hr
  have hd := orderOf_two_le_finrank_of_dvd_card_quotient e hp2 hpS
  have hb := h.bound
  omega

theorem card_le_two_of_cyclic_sq {Q : Type*} [Group Q] [IsCyclic Q] (B : Subgroup Q)
    (hB : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 := by
  haveI : IsCyclic B := inferInstance
  have hexp : Monoid.exponent B ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => by
    apply Subtype.ext
    simpa [sq] using hB z z.2
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd (by norm_num) hexp

theorem card_le_two_pow_succ_of_mulAut {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {Q : Type*} [Group Q] [IsCyclic Q] (Θ : MulAut S →* Q)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ (r + 1) := by
  intro B hBc hB2
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hc : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun (MonoidHom.mem_ker.1 hs) g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s = (s * g * s⁻¹) * s := by rw [this]
        _ = s * g := by group
    rw [hZ] at hc
    exact hc
  let φ : B →* Q := Θ.comp B.subtype
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ 2 := by
    refine card_le_two_of_cyclic_sq φ.range ?_
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [this, map_one]
  let B' : Subgroup S := B.comap (MulAut.conj : S →* MulAut S)
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    hconj (by rw [map_mul, map_mul]; exact hBc _ hx _ hy)
  have hB'2 : ∀ x ∈ B', x * x = 1 := fun x hx =>
    hconj (by rw [map_mul, map_one]; exact hB2 _ hx)
  have hB' : Nat.card B' ≤ 2 ^ r := hr B' hB'c hB'2
  have hkerle : Nat.card φ.ker ≤ Nat.card B' := by
    refine Nat.card_le_card_of_surjective
      (fun s : B' => (⟨⟨(MulAut.conj : S →* MulAut S) s, s.2⟩, ?_⟩ : φ.ker)) ?_
    · rw [MonoidHom.mem_ker]
      show Θ ((MulAut.conj : S →* MulAut S) s) = 1
      have : (MulAut.conj : S →* MulAut S) s ∈ Θ.ker := by rw [hker]; exact ⟨s, rfl⟩
      exact this
    · rintro ⟨⟨b, hbB⟩, hb⟩
      have hb' : b ∈ Θ.ker := hb
      rw [hker] at hb'
      obtain ⟨s, rfl⟩ := hb'
      exact ⟨⟨s, hbB⟩, rfl⟩
  calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := hmul.symm
    _ ≤ 2 ^ r * 2 := Nat.mul_le_mul (hkerle.trans hB') hrange
    _ = 2 ^ (r + 1) := by ring

theorem ker_eq_bot_of_section {E S : Type*} [Group E] [Group S] [Group.IsPerfect E]
    (π : E →* S) (hcen : π.ker ≤ Subgroup.center E) (s : S →* E) (hs : ∀ g, π (s g) = g) :
    π.ker = ⊥ := by
  have hδ : ∀ x : E, (s (π x))⁻¹ * x ∈ Subgroup.center E := fun x => hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
  let δ : E →* Subgroup.center E :=
    { toFun := fun x => ⟨(s (π x))⁻¹ * x, hδ x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have h1 := Subgroup.mem_center_iff.1 (hδ x) (s (π y))⁻¹
        have : (s (π (x * y)))⁻¹ * (x * y) =
            (s (π y))⁻¹ * ((s (π x))⁻¹ * x) * y := by
          rw [map_mul, map_mul]; group
        show (s (π (x * y)))⁻¹ * (x * y) = ((s (π x))⁻¹ * x) * ((s (π y))⁻¹ * y)
        rw [this, h1, mul_assoc, mul_assoc]) }
  have hδ1 : ∀ x, δ x = 1 := by
    have hle : commutator E ≤ δ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Subtype.ext_iff.2 (Subgroup.mem_center_iff.1 (δ b).2 (δ a)))
        |> fun h => by simpa using h
    have htop : commutator E = ⊤ := Group.isPerfect_def.1 inferInstance
    intro x
    exact (MonoidHom.mem_ker.1 (hle (htop ▸ Subgroup.mem_top x)))
  rw [eq_bot_iff]
  intro k hk
  have h1 : (s (π k))⁻¹ * k = 1 := congrArg Subtype.val (hδ1 k)
  have hk1 : π k = 1 := hk
  rw [hk1, map_one, inv_one, one_mul] at h1
  exact h1

theorem exists_ppd_prime {k : ℕ} (hk : 2 ≤ k) (hk6 : k ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = k ∧ p ∣ 2 ^ k - 1 ∧
      ∀ j : ℕ, 0 < j → j < k → ¬ p ∣ 2 ^ j - 1 := by
  obtain ⟨p, hpP⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hk hk6
  have hp := hpP.prime
  have hp2 : p ≠ 2 := hpP.ne_two (by omega)
  refine ⟨p, hp, hp2, ?_, hpP.dvd, hpP.2.2⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (2 : ZMod p) ^ k = 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff k).1 hpP.dvd
  have hdv : orderOf (2 : ZMod p) ∣ k := orderOf_dvd_of_pow_eq_one hpow
  have hpos : 0 < orderOf (2 : ZMod p) :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0] at hdv; omega
  refine le_antisymm (Nat.le_of_dvd (by omega) hdv) ?_
  by_contra hlt
  push Not at hlt
  exact hpP.2.2 _ hpos hlt
    ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).2 (pow_orderOf_eq_one _))

theorem center_eq_bot_of_hopf_subsingleton' {L X : Type} [Group L] [Finite L] [Group X]
    (hL : CFSG.Open.IsQuasisimple L) (e : L ⧸ Subgroup.center L ≃* X)
    (hM : Subsingleton (CFSG.Open.griessHopfMultiplier X)) : Subgroup.center L = ⊥ := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center L := centralQuotientMap_ker e
  have : Finite X := finite_of_surjective_monoidHom q hq
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := centralQuotientMap e) (centralQuotientMap_surjective e)
  let ψ : hopfMultiplier X →* q.ker := hopfMultiplierToKer q hq hk.le
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q hq hk.le
  have hsub : Subsingleton (hopfMultiplier X) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (hopfMultiplierEquivGriess X).surjective a
    obtain ⟨b', rfl⟩ := (hopfMultiplierEquivGriess X).surjective b
    rw [Subsingleton.elim a' b']
  have : Subsingleton ↥q.ker := hψ.subsingleton
  rw [← hk]
  exact Subgroup.eq_bot_of_subsingleton _

theorem false_of_center_bot_rank_prime {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : G93Hyp Γ A L L m) (hZ : Subgroup.center ↥L = ⊥)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S)
    (hlt : 2 * (r + 1) < orderOf (2 : ZMod p)) : False := by
  let f : ↥L ≃* S :=
    ((QuotientGroup.quotientBot (G := ↥L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hm := m_le_of_autRank h f hr
  have hd := orderOf_two_le_finrank_of_dvd_card_quotient e hp2 hpS
  have hb := h.bound
  omega

theorem card_le_two_pow_of_inner {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (hinn : ∀ α : MulAut S, α ^ 2 = 1 →
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r := by
  intro B hBc hB2
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hc : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun (MonoidHom.mem_ker.1 hs) g
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s = (s * g * s⁻¹) * s := by rw [this]
        _ = s * g := by group
    rw [hZ] at hc
    exact hc
  let B' : Subgroup S := B.comap (MulAut.conj : S →* MulAut S)
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    hconj (by rw [map_mul, map_mul]; exact hBc _ hx _ hy)
  have hB'2 : ∀ x ∈ B', x * x = 1 := fun x hx =>
    hconj (by rw [map_mul, map_one]; exact hB2 _ hx)
  have hle : Nat.card B ≤ Nat.card B' := by
    refine Nat.card_le_card_of_surjective
      (fun s : B' => (⟨(MulAut.conj : S →* MulAut S) s, s.2⟩ : B)) ?_
    rintro ⟨b, hb⟩
    have hb2 : b ^ 2 = 1 := by rw [sq]; exact hB2 b hb
    obtain ⟨s, rfl⟩ := hinn b hb2
    exact ⟨⟨s, hb⟩, rfl⟩
  exact hle.trans (hr B' hB'c hB'2)

theorem rank_transport {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {r : ℕ}
    (hr : ∀ B : Subgroup S', (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  intro B hBc hB2
  have h := hr (B.map e.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBc x hx y hy]) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hB2 x hx, map_one])
  rwa [Subgroup.card_map_of_injective e.injective] at h

theorem center_eq_bot_of_mulEquiv_generic {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx y']
  rw [hY, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans e.map_one.symm)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
