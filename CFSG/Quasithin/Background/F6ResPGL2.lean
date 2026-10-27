module

public import CFSG.Quasithin.Background.F6NQShapes

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

namespace F6

namespace PGL2Res

section Transport

variable {K : Type} [Field K] [Finite K] {D : Type} [Group D]

@[expose] noncomputable def statedEquiv (K : Type) [Field K] :
    GL (Fin 2) K ⧸ StatedScalars (Fin 2) K ≃* PGL2 K :=
  QuotientGroup.quotientMulEquivOfEq (M := StatedScalars (Fin 2) K)
    (N := Subgroup.center (GL (Fin 2) K))
    (by rw [StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar])

theorem finite_pgl2 : Finite (PGL2 K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem false_of_kleinFour_commute
    (e : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K))
    {V : Subgroup D} (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) {x : D} (hx1 : x ≠ 1)
    (hxo : Odd (orderOf x)) (hc : ∀ v ∈ V, v * x = x * v) : False := by
  have : Finite (PGL2 K) := finite_pgl2
  set V' := V.map e.toMonoidHom
  have hV'4 : Nat.card V' = 4 := by rw [Subgroup.card_map_of_injective e.injective, hV4]
  have hVK : IsKleinFour V' := isKleinFour_of_card_four_of_mul_self hV'4 (by
    rintro ⟨_, v, hv, rfl⟩
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, hVsq v hv, map_one])
  refine pgl2_no_kleinFour_centralizes_odd_cyclic K hK (Subgroup.zpowers (e x)) V'
    inferInstance ?_ ?_ hVK ?_
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact fun h => hx1 (e.injective (by rw [h, map_one]))
  · rw [Nat.card_zpowers, MulEquiv.orderOf_eq]
    exact hxo
  · rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_zpow, ← map_mul, ← map_mul]
    exact congrArg e (Commute.zpow_left (show Commute x v from (hc v hv).symm) k).eq

theorem centralizer_le_of_kleinFour
    (e : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K))
    {V : Subgroup D} (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) :
    Subgroup.centralizer (V : Set D) ≤ V := by
  have : Finite (PGL2 K) := finite_pgl2
  set V' := V.map e.toMonoidHom
  have hV'4 : Nat.card V' = 4 := by rw [Subgroup.card_map_of_injective e.injective, hV4]
  have hVK : IsKleinFour V' := isKleinFour_of_card_four_of_mul_self hV'4 (by
    rintro ⟨_, v, hv, rfl⟩
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, hVsq v hv, map_one])
  intro g hg
  have hmem : e g ∈ Subgroup.centralizer (V' : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg v hv]
  rw [pgl2_kleinFour_centralizer_eq_self K hK V' hVK] at hmem
  obtain ⟨v, hv, hve⟩ := hmem
  rwa [e.injective hve] at hv

@[expose] def pslPart (e : D ≃* PGL2 K) : Subgroup D :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.comap e.toMonoidHom

theorem pslPart_index (e : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K)) :
    (pslPart e).index = 2 := by
  rw [pslPart, Subgroup.index_comap_of_surjective _ e.surjective]
  exact pgl2_psl2Range_index_eq_two K hK

theorem sq_mem_pslPart (e : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K)) (a : D) :
    a ^ 2 ∈ pslPart e :=
  Subgroup.sq_mem_of_index_two (pslPart_index e hK) a

theorem card_eq (e : D ≃* PGL2 K) :
    Nat.card D = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv, pgl2_card_formula]

theorem two_mul_card_pslPart (e : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K)) :
    Nat.card (pslPart e) * 2 = Nat.card D := by
  rw [← pslPart_index e hK, Subgroup.card_mul_index]

theorem mod_twelve_of_dihedral_le
    (e : D ≃* PGL2 K) (hq : (Nat.card K).Prime)
    (hq2 : Nat.card K ≠ 2) {H : Subgroup D} (hHL : H ≤ pslPart e) (φ : H ≃* DihedralGroup 6) :
    Nat.card K % 12 = 1 ∨ Nat.card K % 12 = 11 := by
  set ι : PSL2 K →* D :=
    e.symm.toMonoidHom.comp (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))
  have hι : Function.Injective ι :=
    e.symm.injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hHι : H ≤ ι.range := by
    intro x hx
    obtain ⟨y, hy⟩ := hHL hx
    refine ⟨y, ?_⟩
    change e.symm (Matrix.ProjectiveSpecialLinearGroup.toPGL y) = x
    rw [hy]
    exact e.symm_apply_apply x
  set H' := H.comap ι
  have ψ : H' ≃* H := (H'.equivMapOfInjective ι hι).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hHι))
  set ε := projectiveSpecialLinearGroupEquivStatedProj 2 K
  set H'' := H'.map ε.toMonoidHom
  have ψ' : H' ≃* H'' := H'.equivMapOfInjective ε.toMonoidHom ε.injective
  obtain ⟨h12, -, -⟩ := l2DicksonFacts_holds (Nat.card K) 1 K hq hq2 le_rfl (pow_one _).symm H''
  have := h12 ⟨ψ'.symm.trans (ψ.trans φ)⟩
  rwa [pow_one] at this

end Transport

@[expose] def vSet : Finset (Equiv.Perm (Fin 4)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

theorem vSet_mul : ∀ a ∈ vSet, ∀ b ∈ vSet, a * b ∈ vSet := by decide

theorem vSet_inv : ∀ a ∈ vSet, a⁻¹ ∈ vSet := by decide

theorem vSet_conj : ∀ g : Equiv.Perm (Fin 4), ∀ a ∈ vSet, g * a * g⁻¹ ∈ vSet := by decide

theorem vSet_mul_self : ∀ a ∈ vSet, a * a = 1 := by decide

theorem vSet_square : ∀ a ∈ vSet, ∃ y : Equiv.Perm (Fin 4), y * y = a := by decide

theorem vSet_card : vSet.card = 4 := by decide

@[expose] def permFourV : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := vSet
  mul_mem' ha hb := vSet_mul _ ha _ hb
  one_mem' := Finset.mem_coe.mpr (by decide)
  inv_mem' ha := vSet_inv _ ha

theorem card_permFourV : Nat.card permFourV = 4 := by
  have h : Nat.card permFourV = vSet.card := by
    rw [← Nat.card_eq_finsetCard]
    rfl
  rw [h, vSet_card]

instance permFourV_normal : permFourV.Normal :=
  ⟨fun a ha g => vSet_conj g a ha⟩

variable {D : Type} [Group D]

@[expose] def kleinOf (G : Subgroup D) (e : G ≃* Equiv.Perm (Fin 4)) : Subgroup D :=
  (permFourV.map e.symm.toMonoidHom).map G.subtype

variable {G : Subgroup D} (e : G ≃* Equiv.Perm (Fin 4))

theorem mem_kleinOf {x : D} : x ∈ kleinOf G e ↔ ∃ y ∈ vSet, (e.symm y : D) = x := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem card_kleinOf : Nat.card (kleinOf G e) = 4 := by
  rw [kleinOf, Subgroup.card_map_of_injective G.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective, card_permFourV]

theorem mul_self_of_mem_kleinOf {v : D} (hv : v ∈ kleinOf G e) : v * v = 1 := by
  obtain ⟨y, hy, rfl⟩ := (mem_kleinOf e).mp hv
  rw [← Subgroup.coe_mul, ← map_mul, vSet_mul_self y hy, map_one, Subgroup.coe_one]

theorem exists_mul_self_of_mem_kleinOf {v : D} (hv : v ∈ kleinOf G e) :
    ∃ z : D, z * z = v := by
  obtain ⟨y, hy, rfl⟩ := (mem_kleinOf e).mp hv
  obtain ⟨z, hz⟩ := vSet_square y hy
  exact ⟨e.symm z, by rw [← Subgroup.coe_mul, ← map_mul, hz]⟩

theorem le_normalizer_kleinOf : G ≤ Subgroup.normalizer (kleinOf G e : Set D) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_kleinOf e).mp hx
    refine (mem_kleinOf e).mpr ⟨e ⟨g, hg⟩ * y * (e ⟨g, hg⟩)⁻¹, vSet_conj _ y hy, ?_⟩
    simp
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (mem_kleinOf e).mp hx
    refine (mem_kleinOf e).mpr ⟨(e ⟨g, hg⟩)⁻¹ * y * (e ⟨g, hg⟩)⁻¹⁻¹,
      vSet_conj _ y hy, ?_⟩
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [hxy]
    group

theorem kleinOf_le_of_sylow (S : Sylow 2 D) (hSG : (S : Subgroup D) ≤ G) :
    kleinOf G e ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := permFourV.map e.symm.toMonoidHom
  have hN : N.Normal := permFourV_normal.map _ e.symm.surjective
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 2) (by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_permFourV]
    norm_num)
  have hle := hNp.le_sylow_of_normal (S.subtype hSG)
  rw [Sylow.coe_subtype] at hle
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hle hy

section Claims

variable {K : Type} [Field K] [Finite K]

theorem isOddPrimePower_of_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : IsOddPrimePower q :=
  ⟨q, 1, hq, hq.odd_of_ne_two hq2, le_rfl, (pow_one _).symm⟩

theorem not_isGoldCaseIV
    (ε : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K))
    (G₁ G₂ : Subgroup D) :
    ¬ IsGoldCaseIV G₁ G₂ := by
  rintro ⟨-, -, φ, -, ⟨ψ⟩⟩
  set ι : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* D :=
    G₂.subtype.comp (φ.ker.subtype.comp ψ.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    G₂.subtype_injective.comp (φ.ker.subtype_injective.comp ψ.symm.injective)
  set w : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (Multiplicative.ofAdd 1, 1)
  set V := (MonoidHom.inr (Multiplicative (ZMod 3))
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))).range.map ι
  have hw : w ^ 3 = 1 ∧ w ≠ 1 ∧
      ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by
    decide
  refine false_of_kleinFour_commute ε hK (V := V) ?_ ?_ (x := ι w) ?_ ?_ ?_
  · rw [Subgroup.card_map_of_injective hι, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (fun a b h => by simpa using congrArg Prod.snd h),
      Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [← map_mul, ← map_one ι]
    congr 1
    exact Prod.ext (by simp) (by simp [hw.2.2 y])
  · exact fun h1 => hw.2.1 (hι (by rw [h1, map_one]))
  · rw [orderOf_injective ι hι, orderOf_eq_prime hw.1 hw.2.1]
    decide
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp [w]) (by simp [w])

theorem not_eight_dvd_card_pslPart (ε : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) : ¬ 8 ∣ Nat.card (pslPart ε) := by
  intro h8
  have h1 := two_mul_card_pslPart ε hK
  rw [card_eq ε] at h1
  have h16 : 16 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← h1]
    exact Nat.mul_dvd_mul_right h8 2
  have hodd : Odd (Nat.card K) := by
    rw [Nat.odd_iff]
    omega
  have hcop : Nat.Coprime 16 (Nat.card K) :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hodd)
  have h16' := hcop.dvd_of_dvd_mul_left h16
  have h9 := sq_mod_sixteen hq8
  have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem card_le_four_of_isPGroup (ε : D ≃* PGL2 K) (hK : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) {W : Subgroup D} [Finite W]
    (hW : IsPGroup 2 W) (hWL : W ≤ pslPart ε) : Nat.card W ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card (pslPart ε) := hk ▸ Subgroup.card_dvd_of_le hWL
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ Nat.card (pslPart ε) := (pow_dvd_pow 2 (by omega)).trans hdvd
    exact not_eight_dvd_card_pslPart ε hK hq8 (by simpa using h8)
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem dihedral_twelve_outside : ∀ x : DihedralGroup 12,
    (∀ k : Fin 12, x ≠ DihedralGroup.r 1 ^ (k : ℕ)) →
      x * x = 1 ∧ x * DihedralGroup.r 1 * x⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  decide

theorem mod_twentyfour_of_isGoldCaseIII
    [Finite D] (ε : D ≃* PGL2 K) (hq : (Nat.card K).Prime)
    (hq8 : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (hIII : IsGoldCaseIII G₁ G₂) :
    Nat.card K % 24 = 11 ∨ Nat.card K % 24 = 13 := by
  have hq2 : Nat.card K ≠ 2 := by omega
  have hK := isOddPrimePower_of_prime hq hq2
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := hIII
  obtain ⟨S, hS⟩ := h.sylow
  set V := kleinOf G₂ e₂
  have hVG₁ : V ≤ G₁ :=
    (kleinOf_le_of_sylow e₂ S (hS ▸ inf_le_right)).trans (hS ▸ inf_le_left)
  set r : D := (e₁.symm (DihedralGroup.r 1) : D) with hr
  have hro : orderOf r = 12 := by
    rw [hr, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨v, hvV, hvr⟩ : ∃ v ∈ V, v ∉ Subgroup.zpowers r := by
    by_contra hall
    push Not at hall
    have hcyc : IsCyclic V :=
      (Subgroup.subgroupOfEquivOfLe (fun v hv => hall v hv)).isCyclic.mp (Subgroup.isCyclic _)
    have hK4 : IsKleinFour V := isKleinFour_of_card_four_of_mul_self (card_kleinOf e₂)
      (fun x => Subtype.ext (mul_self_of_mem_kleinOf e₂ x.2))
    exact hK4.not_isCyclic hcyc
  have hvG : v ∈ G₁ := hVG₁ hvV
  have hv' : ∀ k : Fin 12, e₁ ⟨v, hvG⟩ ≠ DihedralGroup.r 1 ^ (k : ℕ) := by
    intro k hk
    apply hvr
    refine ⟨(k : ℤ), ?_⟩
    have hvk : (⟨v, hvG⟩ : G₁) = e₁.symm (DihedralGroup.r 1 ^ (k : ℕ)) := by
      rw [← hk, MulEquiv.symm_apply_apply]
    have hvk' := congrArg Subtype.val hvk
    simp only [map_pow, Subgroup.coe_pow] at hvk'
    change r ^ ((k : ℕ) : ℤ) = v
    rw [zpow_natCast, hvk']
  obtain ⟨hv2, hvinv⟩ := dihedral_twelve_outside _ hv'
  have hv2' : v * v = 1 := by
    have := congrArg (fun x => ((e₁.symm x : G₁) : D)) hv2
    simpa using this
  have hvinv' : v * r * v⁻¹ = r⁻¹ := by
    have := congrArg (fun x => ((e₁.symm x : G₁) : D)) hvinv
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    exact this
  set h6 := r ^ 2 with hh6
  have h6o : orderOf h6 = 6 := by
    rw [hh6, orderOf_pow, hro]
    rfl
  have h6inv : v * h6 * v⁻¹ = h6⁻¹ := by
    rw [hh6, ← conj_pow, hvinv', inv_pow]
  have hv6 : v ∉ Subgroup.zpowers h6 := fun hm =>
    hvr (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers r) 2) hm)
  obtain ⟨φ⟩ := nonempty_dihedral_of_inverting (by rw [pow_two]; exact hv2') h6inv hv6
  rw [h6o] at φ
  have hHL : Subgroup.zpowers h6 ⊔ Subgroup.zpowers v ≤ pslPart ε := by
    refine sup_le (Subgroup.zpowers_le.mpr (sq_mem_pslPart ε hK r)) (Subgroup.zpowers_le.mpr ?_)
    obtain ⟨z, hz⟩ := exists_mul_self_of_mem_kleinOf e₂ hvV
    rw [← hz, ← pow_two]
    exact sq_mem_pslPart ε hK z
  have h12 := mod_twelve_of_dihedral_le ε hq hq2 hHL φ
  omega

theorem not_perm_four_pair
    [Finite D] (ε : D ≃* PGL2 K) (hq : (Nat.card K).Prime)
    (hq8 : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (e₁ : G₁ ≃* Equiv.Perm (Fin 4))
    (e₂ : G₂ ≃* Equiv.Perm (Fin 4)) : False := by
  have hq2 : Nat.card K ≠ 2 := by omega
  have hK := isOddPrimePower_of_prime hq hq2
  obtain ⟨S, hS⟩ := h.sylow
  set W := (S : Subgroup D) ⊓ pslPart ε
  have hW : Nat.card W ≤ 4 :=
    card_le_four_of_isPGroup ε hK hq8 (S.isPGroup'.to_le inf_le_left) inf_le_right
  have hVW : ∀ {G : Subgroup D} (e : G ≃* Equiv.Perm (Fin 4)), (S : Subgroup D) ≤ G →
      kleinOf G e = W := by
    intro G e hSG
    refine Subgroup.eq_of_le_of_card_ge (le_inf (kleinOf_le_of_sylow e S hSG) ?_)
      (by rw [card_kleinOf]; exact hW)
    intro v hv
    obtain ⟨z, rfl⟩ := exists_mul_self_of_mem_kleinOf e hv
    rw [← pow_two]
    exact sq_mem_pslPart ε hK z
  have h1 := hVW e₁ (hS ▸ inf_le_left)
  have h2 := hVW e₂ (hS ▸ inf_le_right)
  have hWn : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.gen]
    exact sup_le (h1 ▸ le_normalizer_kleinOf e₁) (h2 ▸ le_normalizer_kleinOf e₂)
  have hW4 : Nat.card W = 4 := h1 ▸ card_kleinOf e₁
  have hWsq : ∀ v ∈ W, v * v = 1 := fun v hv => mul_self_of_mem_kleinOf e₁ (h1 ▸ hv)
  set φ : D →* MulAut W := MulAut.conjNormal
  have hker : φ.ker ≤ W := by
    intro g hg
    apply centralizer_le_of_kleinFour ε hK hW4 hWsq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := congrArg (fun α : MulAut W => (α ⟨w, hw⟩ : D)) (MonoidHom.mem_ker.mp hg)
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc w * g = g * w * g⁻¹ * g := by rw [this]
      _ = g * w := by group
  have hD : Nat.card D ≤ 96 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have hr : Nat.card φ.range ≤ 24 := by
      calc Nat.card φ.range ≤ Nat.card (MulAut W) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Equiv.Perm W) :=
          Nat.card_le_card_of_injective _ MulEquiv.toEquiv_injective
        _ = 24 := by rw [Nat.card_perm, hW4]; rfl
    have hk : Nat.card φ.ker ≤ 4 := hW4 ▸ Subgroup.card_le_of_le hker
    calc _ ≤ 24 * 4 := Nat.mul_le_mul hr hk
      _ = 96 := by norm_num
  rw [card_eq ε] at hD
  have hq3 : Nat.card K = 3 := by
    by_contra hne
    have h5 : 5 ≤ Nat.card K := by have := hq.two_le; omega
    have h25 : 25 ≤ Nat.card K ^ 2 := by nlinarith
    have h24 : 24 ≤ Nat.card K ^ 2 - 1 := by omega
    have := Nat.mul_le_mul h5 h24
    omega
  have hDc : Nat.card D = 24 := by
    rw [card_eq ε, hq3]
    norm_num
  have htop : ∀ {G : Subgroup D}, (G ≃* Equiv.Perm (Fin 4)) → G = ⊤ := fun e =>
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, hDc]
      rfl)
  have h3 := h.relIndex_inf_left
  rw [htop e₁, htop e₂, inf_idem, Subgroup.relIndex_self] at h3
  norm_num at h3

end Claims

end PGL2Res

theorem pgl2InspectionFact_holds
    : PGL2InspectionFact := by
  intro K _ _ hq hq8 G₁ G₂ h
  set ε := PGL2Res.statedEquiv K
  have : Finite (PGL2 K) := PGL2Res.finite_pgl2
  have : Finite (GL (Fin 2) K ⧸ StatedScalars (Fin 2) K) := Finite.of_equiv _ ε.symm.toEquiv
  exact ⟨fun hIII => PGL2Res.mod_twentyfour_of_isGoldCaseIII ε hq hq8 h hIII,
    PGL2Res.not_isGoldCaseIV ε (PGL2Res.isOddPrimePower_of_prime hq (by omega)) G₁ G₂,
    fun ⟨⟨e₁⟩, ⟨e₂⟩⟩ => PGL2Res.not_perm_four_pair ε hq hq8 h e₁ e₂⟩

end F6

end CFSG.Quasithin
