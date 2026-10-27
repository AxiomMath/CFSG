module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallBase
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallPerm

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {n : ℕ}

private theorem zmod_two_ite_eq {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then (1 : ZMod 2) else 0) + if q then 1 else 0) = 1 ↔ (p ↔ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

theorem pairEW_eq_iff {a b c d : Fin n} (hab : a ≠ b) :
    pairEW a b = pairEW c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha := congrArg (fun v : evenWeight n => (v : Fin n → ZMod 2) a) h
    have hb := congrArg (fun v : evenWeight n => (v : Fin n → ZMod 2) b) h
    simp only [pairEW_apply, if_neg hab, if_neg (Ne.symm hab)] at ha hb
    simp only [if_true, add_zero, zero_add] at ha hb
    have ha' := zmod_two_ite_eq.1 ha.symm
    have hb' := zmod_two_ite_eq.1 hb.symm
    by_cases hac : a = c
    · refine Or.inl ⟨hac, ?_⟩
      by_contra hbd
      exact hab (hac.trans (hb'.2 hbd).symm)
    · have had : a = d := by
        by_contra had
        exact hac (ha'.2 had)
      exact Or.inr ⟨had, hb'.2 fun hbd => hab (had.trans hbd.symm)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact pairEW_comm a b

theorem mk_pairEW_eq_iff (hn : 5 ≤ n) {a b c d : Fin n} :
    (pairEW a b : altHeart n) = (pairEW c d : altHeart n) ↔ pairEW a b = pairEW c d := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [QuotientAddGroup.eq] at h
  have h1 : ((-pairEW a b + pairEW c d : evenWeight n) : Fin n → ZMod 2) ∈
      AddSubgroup.zmultiples (allOnes n) := h
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin n))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_four hn)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨hpa, hpb, hpc, hpd⟩ := hp
  rcases (mem_zmultiples_allOnes_iff _).1 h1 with h0 | h0
  · have : -pairEW a b + pairEW c d = 0 := Subtype.ext h0
    rw [neg_add_eq_zero] at this
    exact this
  · exfalso
    have := congrFun h0 p
    simp [pairEW_apply, hpa, hpb, hpc, hpd, allOnes] at this

theorem altAct_pairEW_eq_iff (hn : 5 ≤ n) (σ : Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    altAct σ (pairEW i j : altHeart n) = (pairEW i j : altHeart n) ↔ PresPair σ i j := by
  rw [altAct_mk, evenWeightPerm_pairEW, mk_pairEW_eq_iff hn,
    pairEW_eq_iff (σ.injective.ne hij)]
  unfold PresPair
  tauto

theorem evenWeightPerm_pairEW_eq_iff (σ : Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    evenWeightPerm σ (pairEW i j) = pairEW i j ↔ PresPair σ i j := by
  rw [evenWeightPerm_pairEW, pairEW_eq_iff (σ.injective.ne hij)]
  unfold PresPair
  tauto

theorem add_mem_range_heartToBar {v w : permBar n} (hv : v ∉ Set.range (heartToBar (n := n)))
    (hw : w ∉ Set.range (heartToBar (n := n))) : v + w ∈ Set.range (heartToBar (n := n)) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
  have hodd : ∀ z : Fin n → ZMod 2, ((z : permBar n) ∉ Set.range (heartToBar (n := n))) →
      ∑ i, z i = 1 := by
    intro z hz
    by_contra h1
    apply hz
    have h0 : ∑ i, z i = 0 := by
      generalize ∑ i, z i = s at h1 ⊢
      revert s
      decide
    have hz' : z ∈ evenWeight n := by
      simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      exact h0
    exact ⟨((⟨z, hz'⟩ : evenWeight n) : altHeart n), heartToBar_mk _⟩
  have hx := hodd x hv
  have hy := hodd y hw
  have hxy : x + y ∈ evenWeight n := by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Pi.add_apply,
      Finset.sum_add_distrib, hx, hy]
    decide
  exact ⟨((⟨x + y, hxy⟩ : evenWeight n) : altHeart n), by
    rw [heartToBar_mk, QuotientAddGroup.mk_add]⟩

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem exists_pair_witness (C : Cfg G M X n) (hn : 5 ≤ n)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β) {i j : Fin n} (hij : i ≠ j) :
    ∃ w ∈ blockU X, ∀ m : ↥M, ((m : G) * w = w * m ↔ PresPair (C.θ m) i j) := by
  rcases hW with hU | hinj
  · obtain ⟨ψ⟩ := hU
    refine ⟨(ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : G), (ψ.ψ _).2, fun m => ?_⟩
    rw [← evenWeightPerm_pairEW_eq_iff (C.θ m) hij]
    have he := ψ.equivar m (pairEW i j)
    constructor
    · intro h
      have h1 : (m : G) * (ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : G) * (m : G)⁻¹ =
          ψ.ψ (Multiplicative.ofAdd (pairEW i j)) := by
        rw [h]
        group
      rw [he] at h1
      exact Multiplicative.ofAdd.injective (ψ.ψ.injective (Subtype.ext h1))
    · intro h
      rw [h] at he
      calc (m : G) * (ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : G) =
          ((m : G) * (ψ.ψ (Multiplicative.ofAdd (pairEW i j)) : G) * (m : G)⁻¹) * m := by group
        _ = _ := by rw [he]
  · obtain ⟨u, hu⟩ := C.β_surj (Multiplicative.ofAdd (pairEW i j : altHeart n))
    refine ⟨(u : G), u.2, fun m => ?_⟩
    rw [← altAct_pairEW_eq_iff hn (C.θ m) hij]
    have hv := C.θ_spec m u ⟨(m : G) * u * (m : G)⁻¹, C.S.W_normalized m.2 u.2⟩ rfl
    rw [hu, toAdd_ofAdd] at hv
    constructor
    · intro h
      have hvu : (⟨(m : G) * u * (m : G)⁻¹, C.S.W_normalized m.2 u.2⟩ : ↥(blockU X)) = u :=
        Subtype.ext (by
          show (m : G) * u * (m : G)⁻¹ = u
          rw [h]
          group)
      rw [hvu, hu, toAdd_ofAdd] at hv
      exact hv.symm
    · intro h
      have hβ : C.β ⟨(m : G) * u * (m : G)⁻¹, C.S.W_normalized m.2 u.2⟩ = C.β u := by
        apply Multiplicative.toAdd.injective
        rw [hv, h, hu, toAdd_ofAdd]
      have hc : (m : G) * u * (m : G)⁻¹ = u := congrArg Subtype.val (hinj hβ)
      calc (m : G) * u = ((m : G) * u * (m : G)⁻¹) * m := by group
        _ = u * m := by rw [hc]

omit [Finite G] in
private theorem exists_two_ne_one {T : Subgroup G} (hT : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ τ₁ ∈ T, ∃ τ₂ ∈ T, τ₁ ≠ 1 ∧ τ₂ ≠ 1 ∧ τ₁ ≠ τ₂ := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hT
  by_cases ha : (a : G) = 1
  · refine ⟨b, b.2, c, c.2, fun h => hab (Subtype.ext (ha.trans h.symm)),
      fun h => hac (Subtype.ext (ha.trans h.symm)), fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : (b : G) = 1
    · exact ⟨a, a.2, c, c.2, ha, fun h => hbc (Subtype.ext (hb.trans h.symm)),
        fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩

theorem false_of_caseI (C : Cfg G M X n) (D : C.PiData) (hn : 8 ≤ n)
    (hW : Nonempty C.UIso ∨ Function.Injective C.β)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    {g : G} (hTM : conjSubgroup g (Rc X) ≤ M) (hne : conjSubgroup g (Rc X) ≠ Rc X)
    (hcard : 3 ≤ Nat.card ↥(Rc X))
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M = ⊥) : False := by
  classical
  set T := conjSubgroup g (Rc X) with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have : Fintype ↥T := Fintype.ofFinite _
  have hthree : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rw [← Fintype.two_lt_card_iff, ← Nat.card_eq_fintype_card, hT, card_conj]
    omega
  have hCQ : ∀ t ∈ T, t ≠ 1 → ∀ q ∈ Q, q * t = t * q → ∀ τ ∈ T, q * τ = τ * q := by
    intro t ht ht1 q hq hqt τ hτ
    have h1 : q * τ * q⁻¹ ∈ T := conj_normalized C.S (conj_mem_of_comm C.S ht ht1 hqt) hτ
    have h3 : q * τ * q⁻¹ * τ⁻¹ ∈ Q := by
      have h4 : τ * q⁻¹ * τ⁻¹ ∈ Q := pCoreOf_normalized M (hTM hτ) (Q.inv_mem hq)
      have e : q * τ * q⁻¹ * τ⁻¹ = q * (τ * q⁻¹ * τ⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq h4
    have h5 : q * τ * q⁻¹ * τ⁻¹ ∈ T ⊓ Q := ⟨T.mul_mem h1 (T.inv_mem hτ), h3⟩
    rw [hTQ, Subgroup.mem_bot] at h5
    calc q * τ = (q * τ * q⁻¹ * τ⁻¹) * (τ * q) := by group
      _ = τ * q := by rw [h5, one_mul]
  have hTC : ∀ τ ∈ T, τ ∈ Subgroup.centralizer (X : Set G) → τ = 1 := by
    intro τ hτ hτC
    obtain ⟨j, hj⟩ := two_pow_of_mem_conj hτ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
    have h2 : IsPGroup 2 (Subgroup.zpowers τ) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hR' := hRsyl _ h2 (Subgroup.zpowers_le.2 hτC)
    have h5 : τ ∈ Rc X ⊓ T := ⟨hR' (Subgroup.mem_zpowers τ), hτ⟩
    rw [inf_conj_eq_bot C.S hne, Subgroup.mem_bot] at h5
    exact h5
  by_cases hK : ∃ t ∈ T, t ∈ C.K ∧ t ≠ 1
  ·
    obtain ⟨t, htT, htK, ht1⟩ := hK
    have hTK : ∀ τ ∈ T, τ ∈ C.K := by
      intro τ hτ
      have hτM := hTM hτ
      rw [C.mem_K]
      refine ⟨hτM, (C.theta_eq_one_iff C.S.five_le_degree ⟨τ, hτM⟩).2 fun u v hv => ?_⟩
      have hut : (u : G) * t = t * u := (K_comm_W C htK u.2).symm
      have hτu := hCQ t htT ht1 u (C.S.W_le_Q u.2) hut τ hτ
      have hvu : v = u := Subtype.ext (by
        rw [hv]
        show τ * (u : G) * τ⁻¹ = u
        rw [← hτu]
        group)
      rw [hvu]
    have hnot : ∀ τ (hτ : τ ∈ T), τ ≠ 1 →
        Multiplicative.toAdd (D.π ⟨τ, hTK τ hτ⟩) ∉ Set.range (heartToBar (n := n)) := by
      rintro τ hτ hτ1 ⟨u, hu⟩
      obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
      have hwQ : (w : G) ∈ Q := C.S.W_le_Q w.2
      have hπw : D.π ⟨τ, hTK τ hτ⟩ = D.π ⟨w, Q_le_K C hwQ⟩ := by
        apply Multiplicative.toAdd.injective
        rw [D.π_W ⟨w, Q_le_K C hwQ⟩ w rfl, hw, toAdd_ofAdd, hu]
      have hτQ := mem_Q_of_pi_eq D hRsyl (k := ⟨τ, hTK τ hτ⟩) (two_pow_of_mem_conj hτ) hwQ hπw
      have h5 : τ ∈ T ⊓ Q := ⟨hτ, hτQ⟩
      rw [hTQ, Subgroup.mem_bot] at h5
      exact hτ1 h5
    have hsq : ∀ τ ∈ T, τ * τ = 1 := by
      intro τ hτ
      apply hTC _ (T.mul_mem hτ hτ)
      have h0 : D.π (⟨τ, hTK τ hτ⟩ * ⟨τ, hTK τ hτ⟩) = 1 := by
        rw [map_mul]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one, permBar_add_self]
      exact (D.ker _).1 h0
    obtain ⟨τ₁, h₁, τ₂, h₂, h₁1, h₂1, h₁₂⟩ := exists_two_ne_one hthree
    have h12 : τ₁ * τ₂ ≠ 1 := by
      intro h
      apply h₁₂
      calc τ₁ = τ₁ * (τ₂ * τ₂) := by rw [hsq τ₂ h₂, mul_one]
        _ = (τ₁ * τ₂) * τ₂ := by group
        _ = τ₂ := by rw [h, one_mul]
    apply hnot _ (T.mul_mem h₁ h₂) h12
    have e : D.π ⟨τ₁ * τ₂, hTK _ (T.mul_mem h₁ h₂)⟩ =
        D.π ⟨τ₁, hTK τ₁ h₁⟩ * D.π ⟨τ₂, hTK τ₂ h₂⟩ := by
      rw [← map_mul]
      rfl
    rw [e, toAdd_mul]
    exact add_mem_range_heartToBar (hnot τ₁ h₁ h₁1) (hnot τ₂ h₂ h₂1)
  ·
    push Not at hK
    have hinj : ∀ a b : G, ∀ (ha : a ∈ T) (hb : b ∈ T),
        C.θ ⟨a, hTM ha⟩ = C.θ ⟨b, hTM hb⟩ → a = b := by
      intro a b ha hb h
      have hab : a * b⁻¹ ∈ C.K := by
        rw [C.mem_K]
        refine ⟨M.mul_mem (hTM ha) (M.inv_mem (hTM hb)), ?_⟩
        have e : (⟨a * b⁻¹, M.mul_mem (hTM ha) (M.inv_mem (hTM hb))⟩ : ↥M) =
            ⟨a, hTM ha⟩ * (⟨b, hTM hb⟩ : ↥M)⁻¹ := rfl
        rw [e, map_mul, map_inv, h, mul_inv_cancel]
      have h1 := hK _ (T.mul_mem ha (T.inv_mem hb)) hab
      calc a = a * b⁻¹ * b := by group
        _ = b := by rw [h1, one_mul]
    set P : Subgroup (Perm (Fin n)) := (T.subgroupOf M).map C.θ with hP
    have hmemP : ∀ τ ∈ P, ∃ t ∈ T, ∃ ht : t ∈ M, C.θ ⟨t, ht⟩ = τ := by
      rintro τ ⟨t, ht, rfl⟩
      exact ⟨t, Subgroup.mem_subgroupOf.1 ht, t.2, rfl⟩
    have h2T : 2 ∣ Nat.card ↥T := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hT2 : IsPGroup 2 ↥T :=
        (isPGroup_pCoreOf' (Subgroup.centralizer (X : Set G))).map (MulAut.conj g).toMonoidHom
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
      have hcT : 3 ≤ Nat.card ↥T := by rw [hT, card_conj]; exact hcard
      rw [hk] at hcT ⊢
      have hk0 : k ≠ 0 := by
        rintro rfl
        norm_num at hcT
      exact dvd_pow_self 2 hk0
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 h2T
    have ht₀M : (t₀ : G) ∈ M := hTM t₀.2
    set σ := C.θ ⟨t₀, ht₀M⟩ with hσ
    have hσP : σ ∈ P := ⟨⟨t₀, ht₀M⟩, Subgroup.mem_subgroupOf.2 t₀.2, rfl⟩
    have ht₀1 : (t₀ : G) ≠ 1 := by
      intro h
      have : t₀ = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht₀
      exact absurd ht₀ (by norm_num)
    have hσ2 : σ * σ = 1 := by
      have h1 : (t₀ : G) * t₀ = 1 := by
        have := pow_orderOf_eq_one t₀
        rw [ht₀, pow_two] at this
        exact congrArg Subtype.val this
      rw [hσ, ← map_mul]
      have e : (⟨t₀, ht₀M⟩ : ↥M) * ⟨t₀, ht₀M⟩ = 1 := Subtype.ext h1
      rw [e, map_one]
    have hpairs : ∀ τ ∈ P, τ ≠ 1 → ∀ i j : Fin n, i ≠ j →
        (PresPair τ i j ↔ PresPair σ i j) := by
      intro τ hτ hτ1 i j hij
      obtain ⟨t, htT, htM, rfl⟩ := hmemP τ hτ
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact hτ1 (by rw [show (⟨(1 : G), htM⟩ : ↥M) = 1 from rfl, map_one])
      obtain ⟨w, hwW, hw⟩ := exists_pair_witness C (by omega) hW hij
      have hwQ : w ∈ Q := C.S.W_le_Q hwW
      rw [← hw ⟨t, htM⟩, ← hw ⟨t₀, ht₀M⟩]
      constructor
      · intro h
        exact (hCQ t htT ht1 w hwQ h.symm _ t₀.2).symm
      · intro h
        exact (hCQ _ t₀.2 ht₀1 w hwQ h.symm _ htT).symm
    have hall := eq_one_or_eq_of_presPair hn hσP hσ2 hpairs
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hthree
    have hval : ∀ x : ↥T, C.θ ⟨x, hTM x.2⟩ = 1 ∨ C.θ ⟨x, hTM x.2⟩ = σ := fun x =>
      hall _ ⟨⟨x, hTM x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    have hinj' : ∀ x y : ↥T, C.θ ⟨x, hTM x.2⟩ = C.θ ⟨y, hTM y.2⟩ → x = y := fun x y h =>
      Subtype.ext (hinj x y x.2 y.2 h)
    rcases hval a with ha | ha <;> rcases hval b with hb | hb <;> rcases hval c with hc | hc
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hac (hinj' a c (ha.trans hc.symm))
    · exact hbc (hinj' b c (hb.trans hc.symm))
    · exact hbc (hinj' b c (hb.trans hc.symm))
    · exact hac (hinj' a c (ha.trans hc.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))
    · exact hab (hinj' a b (ha.trans hb.symm))

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
