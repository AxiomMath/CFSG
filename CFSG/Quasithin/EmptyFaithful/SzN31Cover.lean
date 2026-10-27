module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

namespace Cover

@[expose] def ElemBound (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ E : Subgroup G, (∀ x ∈ E, x ^ p = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
    Nat.card E ≤ p ^ 2

theorem ElemBound.of_injective {p : ℕ} {A G : Type*} [Group A] [Group G] (h : ElemBound p G)
    (f : A →* G) (hf : Function.Injective f) : ElemBound p A := by
  intro E hpow hcomm
  have h1 := h (E.map f) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy])
  rwa [Subgroup.card_map_of_injective hf] at h1

theorem elemBound_iff_pRank {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G] :
    ElemBound p G ↔ CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => h E hE.2 fun x hx y hy => ?_
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  · intro h E hpow hcomm
    have hE : CFSG.Open.IsElemAbelian p E :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, hpow⟩
    have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hpow x.1 x.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank hp.one_lt le_top hE hk).trans h
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk2

theorem elemBound_of_stronglyQuasithin {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.SQTKTauCeti.StronglyQuasithin S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ElemBound p S :=
  (elemBound_iff_pRank hp).2 (hS p hp hp2)

theorem exists_frattini_cover {T Γ : Type*} [Group T] [Finite T] [Group Γ] (ψ : T →* Γ)
    (X : Subgroup Γ) (hX : X ≤ ψ.range) :
    ∃ H : Subgroup T, X ≤ H.map ψ ∧ (ψ.comp H.subtype).ker ≤ frattini H := by
  have hne : {H : Subgroup T | X ≤ H.map ψ}.Nonempty :=
    ⟨⊤, show X ≤ (⊤ : Subgroup T).map ψ by rwa [← MonoidHom.range_eq_map]⟩
  obtain ⟨H, hH, hmin⟩ := (wellFounded_lt (α := Subgroup T)).has_min _ hne
  refine ⟨H, hH, ?_⟩
  simp only [frattini, Order.radical, le_iInf_iff, Set.mem_ofPred_eq]
  intro M hM
  by_contra hnot
  set K := (ψ.comp H.subtype).ker
  have hlt : M < M ⊔ K := lt_of_le_of_ne le_sup_left fun h =>
    hnot (le_sup_right.trans h.symm.le)
  have hsup : M ⊔ K = ⊤ := hM.2 _ hlt
  have hKmap : K.map (ψ.comp H.subtype) = ⊥ := (Subgroup.map_eq_bot_iff _).2 le_rfl
  have hMmap : M.map (ψ.comp H.subtype) = H.map ψ := by
    have h1 := congrArg (Subgroup.map (ψ.comp H.subtype)) hsup
    rw [Subgroup.map_sup, hKmap, sup_bot_eq, ← MonoidHom.range_eq_map,
      MonoidHom.range_comp, Subgroup.range_subtype] at h1
    exact h1
  have hgood : X ≤ (M.map H.subtype).map ψ := by
    rw [Subgroup.map_map, hMmap]
    exact hH
  refine hmin _ hgood ⟨Subgroup.map_subtype_le M, fun hle => ?_⟩
  have hM1 : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : H.subtype x ∈ M.map H.subtype := hle x.2
    rwa [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective M]
  exact hM.1 hM1

theorem exists_pPrime_normal_quotient {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (K : Subgroup H) [K.Normal] (hK : Group.IsNilpotent K) :
    ∃ (N : Subgroup H) (_ : N.Normal), N ≤ K ∧ ¬ p ∣ Nat.card N ∧
      ∀ k ∈ K, ∃ j : ℕ, k ^ (p ^ j) ∈ N := by
  refine ⟨(CFSG.pPrimeCore p K).map K.subtype, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 CFSG.pPrimeCore_coprime_card
  · intro k hk
    have hk' : (⟨k, hk⟩ : K) ∈ CFSG.pCore p K ⊔ CFSG.pPrimeCore p K :=
      CFSG.nilpotent_top_le_pCore_sup_pPrimeCore hK (Subgroup.mem_top _)
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := p) (G := K) ⟨a, ha⟩
    refine ⟨j, ?_⟩
    have hb1 : QuotientGroup.mk' ((CFSG.pPrimeCore p K).map K.subtype) (b : H) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨b, hb, rfl⟩
    have hkab : k = (a : H) * (b : H) := by
      simpa using congrArg Subtype.val hab.symm
    have ha1 : (a : H) ^ (p ^ j) = 1 := by
      simpa using congrArg (fun z : CFSG.pCore p K => ((z : K) : H)) hj
    rw [← QuotientGroup.eq_one_iff (N := (CFSG.pPrimeCore p K).map K.subtype),
      ← QuotientGroup.mk'_apply, map_pow, hkab, map_mul, hb1, mul_one, ← map_pow, ha1, map_one]

theorem exists_quotient_cover {S Γ : Type} [Group S] [Finite S] [Group Γ] (φ : S →* Γ)
    (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) (hrank : ElemBound p S)
    (X : Subgroup Γ) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T) (ψ : T →* Γ),
      (∀ t : T, ψ t = 1 → ∃ k : ℕ, t ^ (p ^ k) = 1) ∧ ElemBound p T ∧ X ≤ ψ.range := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hXH, hker⟩ :=
    exists_frattini_cover φ X (le_top.trans (MonoidHom.range_eq_top.2 hφ).ge)
  set ψ : H →* Γ := φ.comp H.subtype
  have hnil : Group.IsNilpotent ψ.ker := by
    have : Group.IsNilpotent (frattini H) := frattini_nilpotent
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hker)
  obtain ⟨N, hNn, hNK, hNp, hNk⟩ := exists_pPrime_normal_quotient (p := p) ψ.ker hnil
  have := hNn
  refine ⟨H ⧸ N, inferInstance, inferInstance, QuotientGroup.lift N ψ hNK, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective t
    have hh : h ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      rwa [QuotientGroup.lift_mk] at ht
    obtain ⟨j, hj⟩ := hNk h hh
    exact ⟨j, by rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).2 hj]⟩
  · have h1 : ElemBound p H := hrank.of_injective H.subtype H.subtype_injective
    refine (elemBound_iff_pRank hp).2 ?_
    rw [CFSG.SectionRank.pRank_quotient_eq N hNp]
    exact (elemBound_iff_pRank hp).1 h1
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (hXH hx)
    exact ⟨((⟨s, hs⟩ : H) : H ⧸ N), by rw [QuotientGroup.lift_mk]; exact hsx⟩

theorem eq_one_of_pow_two_pow_of_pow_p_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : G} (h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) (hp' : ∃ k : ℕ, x ^ (p ^ k) = 1) :
    x = 1 := by
  obtain ⟨k, hk⟩ := h2
  obtain ⟨j, hj⟩ := hp'
  have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one hj))

theorem isPGroup_two_of_mul_self_eq_one {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ x ∈ H, x * x = 1) : IsPGroup 2 H :=
  fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h x.1 x.2)⟩

theorem exists_equivariant_of_ker_pGroup {T Γ : Type} [Group T] [Finite T] [Group Γ]
    (ψ : T →* Γ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hker : ∀ t : T, ψ t = 1 → ∃ k : ℕ, t ^ (p ^ k) = 1) (hrank : ElemBound p T)
    (P B : Subgroup Γ) (hP : IsPGroup p P)
    (hB : ∀ b ∈ B, b * b = 1 ∧ ∀ c ∈ B, b * c = c * b)
    (hBP : ∀ b ∈ B, ∀ x ∈ P, b * x * b⁻¹ ∈ P) (hPr : P ≤ ψ.range) (hBr : B ≤ ψ.range) :
    ∃ (Phat Bhat : Type) (_ : Group Phat) (_ : Finite Phat) (_ : Group Bhat) (_ : Finite Bhat)
      (act : Bhat →* MulAut Phat) (π : Phat →* Γ) (β : Bhat →* Γ),
      IsPGroup p Phat ∧
      (∀ E : Subgroup Phat, (∀ x ∈ E, x ^ p = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        Nat.card E ≤ p ^ 2) ∧
      (∀ b : Bhat, b * b = 1 ∧ ∀ c : Bhat, b * c = c * b) ∧ π.range = P ∧ β.range = B ∧
      ∀ (b : Bhat) (x : Phat), π (act b x) = β b * π x * (β b)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Pt : Subgroup T := P.comap ψ
  set M : Subgroup T := B.comap ψ
  let ρ : M →* B := (ψ.comp M.subtype).codRestrict B fun m => m.2
  have hρ : Function.Surjective ρ := by
    intro b
    obtain ⟨t, ht⟩ := hBr b.2
    exact ⟨⟨t, show ψ t ∈ B by rw [ht]; exact b.2⟩, Subtype.ext ht⟩
  have hB2 : IsPGroup 2 (⊤ : Subgroup B) :=
    isPGroup_two_of_mul_self_eq_one _ fun x _ => Subtype.ext (hB x.1 x.2).1
  obtain ⟨Q⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hQtop : (Q : Subgroup M).map ρ = ⊤ := by
    have h1 := (Q.mapSurjective hρ).is_maximal' hB2 le_top
    rw [Sylow.coe_mapSurjective] at h1
    exact h1.symm
  have hQB : ∀ b ∈ B, ∃ q : M, q ∈ Q ∧ ψ q = b := by
    intro b hb
    obtain ⟨q, hq, hqb⟩ := Subgroup.mem_map.1 (hQtop ▸ Subgroup.mem_top (⟨b, hb⟩ : B))
    exact ⟨q, hq, congrArg Subtype.val hqb⟩
  set Bt : Subgroup T := (Q : Subgroup M).map M.subtype
  have hBt1 : ∀ x ∈ Bt, ψ x ∈ B := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hBt2 : ∀ x ∈ Bt, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (Q.isPGroup'.map M.subtype) ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hBt3 : ∀ x ∈ Bt, ψ x = 1 → x = 1 := fun x hx hx1 =>
    eq_one_of_pow_two_pow_of_pow_p_pow hp hp2 (hBt2 x hx) (hker x hx1)
  have hPp : IsPGroup p Pt := by
    intro x
    obtain ⟨a, ha⟩ := hP ⟨ψ x.1, x.2⟩
    have ha' : ψ (x.1 ^ (p ^ a)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hker _ ha'
    exact ⟨a + b, Subtype.ext (by rw [pow_add, pow_mul]; exact hb)⟩
  have hmem : ∀ b ∈ Bt, ∀ x ∈ Pt, b * x * b⁻¹ ∈ Pt := by
    intro b hb x hx
    show ψ (b * x * b⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hBP _ (hBt1 b hb) _ hx
  let actFun : Bt → MulAut Pt := fun b =>
    { toFun := fun x => ⟨b.1 * x.1 * b.1⁻¹, hmem b.1 b.2 x.1 x.2⟩
      invFun := fun x => ⟨b.1⁻¹ * x.1 * b.1, by simpa using hmem b.1⁻¹ (inv_mem b.2) x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let act : Bt →* MulAut Pt :=
    { toFun := actFun
      map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [actFun])
      map_mul' := fun b c => MulEquiv.ext fun x => Subtype.ext (by simp [actFun, mul_assoc]) }
  refine ⟨Pt, Bt, inferInstance, inferInstance, inferInstance, inferInstance, act,
    ψ.comp Pt.subtype, ψ.comp Bt.subtype, hPp,
    hrank.of_injective Pt.subtype Pt.subtype_injective, ?_, ?_, ?_, ?_⟩
  · have hinj : Function.Injective (ψ.comp Bt.subtype) := by
      rw [injective_iff_map_eq_one]
      intro b hb
      exact Subtype.ext (hBt3 b.1 b.2 hb)
    intro b
    refine ⟨hinj ?_, fun c => hinj ?_⟩
    · rw [map_mul, map_one]
      exact (hB _ (hBt1 b.1 b.2)).1
    · rw [map_mul, map_mul]
      exact (hB _ (hBt1 b.1 b.2)).2 _ (hBt1 c.1 c.2)
  · refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · obtain ⟨t, ht⟩ := hPr hy
      exact ⟨⟨t, show ψ t ∈ P by rw [ht]; exact hy⟩, ht⟩
  · refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, rfl⟩
      exact hBt1 x.1 x.2
    · obtain ⟨q, hq, hqy⟩ := hQB y hy
      exact ⟨⟨q.1, q, hq, rfl⟩, hqy⟩
  · intro b x
    show ψ (b.1 * x.1 * b.1⁻¹) = ψ b.1 * ψ x.1 * (ψ b.1)⁻¹
    rw [map_mul, map_mul, map_inv]

end Cover

theorem sqtk_cover_equivariant {Γ : Type} [Group Γ] [Finite Γ]
    (hq : CFSG.Quasithin.IsQuotientOfSQTKTauCeti Γ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P B : Subgroup Γ) (hP : IsPGroup p P)
    (hB : ∀ b ∈ B, b * b = 1 ∧ ∀ c ∈ B, b * c = c * b)
    (hBP : ∀ b ∈ B, ∀ x ∈ P, b * x * b⁻¹ ∈ P) :
    ∃ (Phat Bhat : Type) (_ : Group Phat) (_ : Finite Phat) (_ : Group Bhat) (_ : Finite Bhat)
      (act : Bhat →* MulAut Phat) (π : Phat →* Γ) (β : Bhat →* Γ),
      IsPGroup p Phat ∧
      (∀ E : Subgroup Phat, (∀ x ∈ E, x ^ p = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        Nat.card E ≤ p ^ 2) ∧
      (∀ b : Bhat, b * b = 1 ∧ ∀ c : Bhat, b * c = c * b) ∧ π.range = P ∧ β.range = B ∧
      ∀ (b : Bhat) (x : Phat), π (act b x) = β b * π x * (β b)⁻¹ := by
  obtain ⟨S, _, _, hS, -, φ, hφ⟩ := hq
  obtain ⟨T, _, _, ψ, hker, hrankT, hX⟩ :=
    Cover.exists_quotient_cover φ hφ hp (Cover.elemBound_of_stronglyQuasithin hS hp hp2) (P ⊔ B)
  exact Cover.exists_equivariant_of_ker_pGroup ψ hp hp2 hker hrankT P B hP hB hBP
    (le_sup_left.trans hX) (le_sup_right.trans hX)

end CFSG.Quasithin.SzN31
