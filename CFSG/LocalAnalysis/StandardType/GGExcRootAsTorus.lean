module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8

public section

namespace CFSG.StandardType.ExcRootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.StandardType TableBExc TableBExc.Three TableBExcTwo TableBExcTwoFusion

section IndexNine

variable {V : Type*} [AddCommGroup V]

theorem exists_sub_or_add_mem_of_index_le_nine [Finite V] (h3 : ∀ v : V, 3 • v = 0)
    {X : AddSubgroup V} (hX : X.index ≤ 9) (v : Fin 6 → V) :
    ∃ i j : Fin 6, i < j ∧ (v i - v j ∈ X ∨ v i + v j ∈ X) := by
  classical
  have : Finite (V ⧸ X) := Finite.of_surjective _ (QuotientAddGroup.mk'_surjective X)
  have := Fintype.ofFinite (V ⧸ X)
  by_contra hcon
  simp only [not_exists, not_and, not_or] at hcon
  have hq : ∀ x : V, (x : V ⧸ X) = 0 ↔ x ∈ X := fun x => QuotientAddGroup.eq_zero_iff x
  have hne : ∀ i j : Fin 6, i ≠ j →
      (v i : V ⧸ X) ≠ v j ∧ (v i : V ⧸ X) ≠ -(v j : V ⧸ X) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · obtain ⟨h1, h2⟩ := hcon i j h
      refine ⟨fun e => h1 ((hq _).1 ?_), fun e => h2 ((hq _).1 ?_)⟩
      · rw [QuotientAddGroup.mk_sub, e, sub_self]
      · rw [QuotientAddGroup.mk_add, e, neg_add_cancel]
    · obtain ⟨h1, h2⟩ := hcon j i h
      refine ⟨fun e => h1 ((hq _).1 ?_), fun e => h2 ((hq _).1 ?_)⟩
      · rw [QuotientAddGroup.mk_sub, e, sub_self]
      · rw [QuotientAddGroup.mk_add, e, add_neg_cancel]
  set T₁ := Finset.univ.image fun i => (v i : V ⧸ X) with hT₁
  set T₂ := Finset.univ.image fun i => -(v i : V ⧸ X) with hT₂
  have hc₁ : T₁.card = 6 := by
    rw [hT₁, Finset.card_image_of_injective _ fun i j hij => by_contra fun h => (hne i j h).1 hij,
      Finset.card_univ, Fintype.card_fin]
  have hc₂ : T₂.card = 6 := by
    rw [hT₂, Finset.card_image_of_injective _ fun i j hij =>
        by_contra fun h => (hne i j h).1 (neg_injective hij),
      Finset.card_univ, Fintype.card_fin]
  have hc₃ : (T₁ ∩ T₂).card ≤ 1 := by
    have h0 : ∀ y ∈ T₁ ∩ T₂, y = 0 := by
      intro y hy
      rw [Finset.mem_inter, hT₁, hT₂, Finset.mem_image, Finset.mem_image] at hy
      obtain ⟨⟨i, -, rfl⟩, ⟨j, -, hj⟩⟩ := hy
      by_cases hij : i = j
      · subst hij
        have h2 : v i + v i ∈ X := (hq _).1 (by
          rw [QuotientAddGroup.mk_add]
          exact (congrArg (· + (v i : V ⧸ X)) hj).symm.trans (neg_add_cancel _))
        have e : v i = -(v i + v i) + 3 • v i := by
          rw [succ_nsmul, two_nsmul]
          abel
        rw [(hq _).2]
        rw [e, h3 (v i), add_zero]
        exact neg_mem h2
      · exact absurd hj.symm (hne i j hij).2
    exact Finset.card_le_one.2 fun a ha b hb => (h0 a ha).trans (h0 b hb).symm
  have hU := Finset.card_union_add_card_inter T₁ T₂
  have hle : (T₁ ∪ T₂).card ≤ X.index := by
    have h := Finset.card_le_univ (T₁ ∪ T₂)
    rw [Fintype.card_eq_nat_card] at h
    exact h
  omega

theorem index_le_nine_of_card {r : ℕ} {X : AddSubgroup (Fin r → ZMod 3)}
    (hX : 3 ^ (r - 2) ≤ Nat.card X) (hr : 2 ≤ r) : X.index ≤ 9 := by
  have h := X.index_mul_card
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
  have hr' : 3 ^ r = 9 * 3 ^ (r - 2) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [hr'] at h
  by_contra hcon
  have : 9 * 3 ^ (r - 2) < X.index * Nat.card X :=
    Nat.mul_lt_mul_of_lt_of_le (not_le.mp hcon) hX Nat.card_pos
  omega

theorem exists_root_mem_of_index_le_nine {τ : Tag} (ε : Fin 6 → Fin τ.rank → ZMod 3)
    (hε : ∀ i j : Fin 6, i < j → ε i - ε j ∈ rootModSet τ ∧ ε i + ε j ∈ rootModSet τ)
    {X : AddSubgroup (Fin τ.rank → ZMod 3)} (hX : X.index ≤ 9) : ∃ x ∈ rootModSet τ, x ∈ X := by
  obtain ⟨i, j, hij, h | h⟩ := exists_sub_or_add_mem_of_index_le_nine three_nsmul_eq_zero hX ε
  · exact ⟨_, (hε i j hij).1, h⟩
  · exact ⟨_, (hε i j hij).2, h⟩

end IndexNine

section Eps

@[expose] def epsE7 : Fin 6 → (Fin Tag.E7.rank → ZMod 3) :=
  ![![0, 2, 2, 1, 1, 1, 1], ![0, 2, 2, 1, 1, 1, 0], ![0, 2, 2, 1, 1, 0, 0], ![0, 2, 2, 1, 0, 0, 0],
    ![0, 2, 2, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0]]

@[expose] def epsE8 : Fin 6 → (Fin Tag.E8.rank → ZMod 3) :=
  ![![0, 2, 2, 1, 1, 1, 1, 0], ![0, 2, 2, 1, 1, 1, 0, 0], ![0, 2, 2, 1, 1, 0, 0, 0],
    ![0, 2, 2, 1, 0, 0, 0, 0], ![0, 2, 2, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0]]

theorem eps_roots_E7 : ∀ i j : Fin 6, i < j →
    (∃ β ∈ rootFinset .E7, redMod .E7 3 β = epsE7 i - epsE7 j) ∧
      ∃ β ∈ rootFinset .E7, redMod .E7 3 β = epsE7 i + epsE7 j := by
  decide +kernel

theorem eps_roots_E8 : ∀ i j : Fin 6, i < j →
    (∃ β ∈ rootFinset .E8, redMod .E8 3 β = epsE8 i - epsE8 j) ∧
      ∃ β ∈ rootFinset .E8, redMod .E8 3 β = epsE8 i + epsE8 j := by
  decide +kernel


theorem exists_root_mem_E7_of_card (X : AddSubgroup (Fin Tag.E7.rank → ZMod 3))
    (hX : 3 ^ 5 ≤ Nat.card X) : ∃ x ∈ rootModSet .E7, x ∈ X := by
  refine exists_root_mem_of_index_le_nine epsE7 (fun i j hij => ?_)
    (index_le_nine_of_card (r := Tag.E7.rank) hX (by decide))
  obtain ⟨⟨β, hβ, hβe⟩, ⟨γ, hγ, hγe⟩⟩ := eps_roots_E7 i j hij
  exact ⟨⟨β, mem_rootFinset.1 hβ, hβe⟩, ⟨γ, mem_rootFinset.1 hγ, hγe⟩⟩

theorem exists_root_mem_E8_of_card (X : AddSubgroup (Fin Tag.E8.rank → ZMod 3))
    (hX : 3 ^ 6 ≤ Nat.card X) : ∃ x ∈ rootModSet .E8, x ∈ X := by
  refine exists_root_mem_of_index_le_nine epsE8 (fun i j hij => ?_)
    (index_le_nine_of_card (r := Tag.E8.rank) hX (by decide))
  obtain ⟨⟨β, hβ, hβe⟩, ⟨γ, hγ, hγe⟩⟩ := eps_roots_E8 i j hij
  exact ⟨⟨β, mem_rootFinset.1 hβ, hβe⟩, ⟨γ, mem_rootFinset.1 hγ, hγe⟩⟩

end Eps

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem exists_mem_torusSet_of_le_of_noOffender [Finite K] {p : ℕ} [NeZero p] (hp : p.Prime)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {S : Subgroup (WeylGroup τ)} {T T₀ : ℕ}
    {Good : Set (Fin τ.rank → ZMod p)}
    (hS : ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian p A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} < T)
    (hGood : ∀ X : AddSubgroup (Fin τ.rank → ZMod p), T₀ ≤ Nat.card X → ∃ x ∈ Good, x ∈ X)
    {E E₀ : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E) (hEX : E ≤ weylX τ K S)
    (hT : T ≤ Nat.card E) (hE₀E : E₀ ≤ E) (hT₀ : T₀ ≤ Nat.card E₀) :
    ∃ x ∈ Good, chevTorus τ ζ hζ (.ofAdd x) ∈ E₀ := by
  have := Fact.mk hp
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨A, hAS, hA, hcard, hfix⟩ :=
    exists_card_eq_mul_card_torusSet hp hdet hV hsymm hζo hζ hE hEX
  have hbot : A = ⊥ := by
    by_contra hbot
    set C := {x : Fin τ.rank → ZMod p // ∀ a ∈ A, torusAct τ p a x = x} with hC
    let f : torusSet hζ E → C := fun x => ⟨x.1, hfix x.1 x.2⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (congrArg Subtype.val hxy :)
    have hle : Nat.card (torusSet hζ E) ≤ Nat.card C := Nat.card_le_card_of_injective f hf
    have hlt := hS A hAS hA hbot
    change Nat.card A * Nat.card C < T at hlt
    have : Nat.card A * Nat.card (torusSet hζ E) ≤ Nat.card A * Nat.card C :=
      Nat.mul_le_mul_left _ hle
    omega
  have h1 : Nat.card A = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [h1, one_mul] at hcard
  have hφinj := chevTorus_injective hζo hζ hdet
  let φ : torusSet hζ E → E := fun x => ⟨chevTorus τ ζ hζ (.ofAdd x.1), x.2⟩
  have hφ : Function.Injective φ := fun x y hxy =>
    Subtype.ext (Multiplicative.ofAdd.injective (hφinj (congrArg Subtype.val hxy)))
  have hφs : Function.Surjective φ := (hφ.bijective_of_nat_card_le hcard.le).2
  have hT₀' : Nat.card E₀ ≤ Nat.card (torusSet hζ E₀) := by
    let φ₀ : torusSet hζ E₀ → E₀ := fun x => ⟨chevTorus τ ζ hζ (.ofAdd x.1), x.2⟩
    refine Nat.card_le_card_of_surjective φ₀ fun e => ?_
    obtain ⟨x, hx⟩ := hφs ⟨e, hE₀E e.2⟩
    have hxe : chevTorus τ ζ hζ (.ofAdd x.1) = e := congrArg Subtype.val hx
    exact ⟨⟨x.1, by rw [mem_torusSet, hxe]; exact e.2⟩, Subtype.ext hxe⟩
  exact hGood _ (hT₀.trans hT₀')

end Count

section Fusion

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_mem_highRootSL2_of_weylX_le (hτ : τ = .E7 ∨ τ = .E8) (F : OrthFrame τ d)
    (hF0 : F.root 0 = CFSG.SeitzReduction.highRoot τ)
    (hw : ∀ v : Fin τ.rank → ℤ, (List.ofFn fun i => rootReflection (F.root i)).prod • v = -v)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3))
    (hV : Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank)
    {S : Subgroup (WeylGroup τ)} (hidx : ¬ 3 ∣ (weylX τ (FiniteField.Extension K 2 2) S).index)
    {T T₀ : ℕ}
    (hS : ∀ (ζ : (FiniteField.Extension K 2 2)ˣ), orderOf ζ = 3 → ∀ (hζ : ζ ^ 3 = 1)
      (E E₀ : Subgroup (adjointGroup τ (FiniteField.Extension K 2 2))), IsElemAbelian 3 E →
      E ≤ weylX τ _ S → T ≤ Nat.card E → E₀ ≤ E → T₀ ≤ Nat.card E₀ →
      ∃ β, IsRoot τ β ∧ chevTorus τ ζ hζ (.ofAdd (redMod τ 3 β)) ∈ E₀)
    (hK : Nat.card K = 2) {A B : Subgroup (adjointGroup τ K)} (hA : IsElemAbelian 3 A)
    (hT : T ≤ Nat.card A) (hBA : B ≤ A) (hT₀ : T₀ ≤ Nat.card B) :
    ∃ t ∈ B, t ≠ 1 ∧ ∃ g : adjointGroup τ K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K) := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3)
    (three_dvd_natCard_ext_sub_one hK)
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  set g := langElt F hωo with hg
  set j := adjointMap τ (algebraMap K L) with hj
  have hjinj : Function.Injective j := adjointMap_injective _
  have : Finite (adjointGroup τ L) := generated_group_finite τ L
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hdesc : ∀ m : adjointGroup τ L, (m : ModGL τ L) ∈ monomialSubgroup τ L →
      ∃ m₀ : adjointGroup τ K, j m₀ = g * m * g⁻¹ := fun m hm =>
    exists_adjointMap_eq_of_frob hτ (adjointMap_frob_conj_langElt hK F hw hsymm hdet hV hωo hm)
  set X := weylX τ L S with hX
  have hXj : X.map (MulAut.conj g).toMonoidHom ≤ j.range := by
    rintro _ ⟨m, hmX, rfl⟩
    obtain ⟨m₀, hm₀⟩ := hdesc m (mem_weylX.mp hmX).1
    exact ⟨m₀, hm₀⟩
  set Y := (X.map (MulAut.conj g).toMonoidHom).comap j with hY
  have hYidx : ¬ 3 ∣ Y.index := fun h => hidx (h.trans (index_comap_dvd hjinj g hXj))
  obtain ⟨x, hx⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hYidx
    (TableB.isPGroup_of_isElemAbelian hA)
  set E' := ((A.map (MulAut.conj x).toMonoidHom).map j).map (MulAut.conj g⁻¹).toMonoidHom with
    hE'def
  set E₀' := ((B.map (MulAut.conj x).toMonoidHom).map j).map (MulAut.conj g⁻¹).toMonoidHom with
    hE₀'def
  have hE'X : E' ≤ X := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨m, hmX, hm⟩ := hx hb
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hm, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
    rw [e]
    exact hmX
  have hE₀'E' : E₀' ≤ E' := Subgroup.map_mono (Subgroup.map_mono (Subgroup.map_mono hBA))
  have hE' : IsElemAbelian 3 E' :=
    TableB.isElemAbelian_map (TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _) _
  have hcard : Nat.card E' = Nat.card A := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective hjinj,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hcard₀ : Nat.card E₀' = Nat.card B := by
    rw [hE₀'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective hjinj,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  obtain ⟨β, hβ, hβE⟩ := hS ω hωo hω3 E' E₀' hE' hE'X (hcard ▸ hT) hE₀'E' (hcard₀ ▸ hT₀)
  obtain ⟨_, ⟨_, ⟨a, haB, rfl⟩, rfl⟩, hya⟩ := hβE
  set y := chevTorus τ ω hω3 (.ofAdd (redMod τ 3 β)) with hy
  have hjxa : j (x * a * x⁻¹) = g * y * g⁻¹ := by
    rw [← hya]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨a, haB, fun ha1 => ?_, ?_⟩
  ·
    have hy1 : y = 1 := by
      rw [← hya, ha1]
      simp
    have h0 := chevTorus_injective hωo hω3 hdet (hy1.trans (map_one _).symm)
    exact redMod_ne_zero_of_isRoot F.symm_one hβ (Multiplicative.ofAdd.injective h0)
  ·
    obtain ⟨w, hwβ⟩ := CFSG.SeitzReduction.EPilot.exists_smul_eq_highRoot hτ' hβ
    obtain ⟨ω', hω'⟩ := (coxeterSystem τ).wordProd_surjective w
    set n := nWord τ L ω' with hn
    have hny : n * y * n⁻¹ =
        chevTorus τ ω hω3 (.ofAdd (redMod τ 3 (CFSG.SeitzReduction.highRoot τ))) := by
      rw [hy, hn, nWord_conj_chevTorus hω3 ω', torusWord_eq_torusAct hsymm, hω', torusAct,
        redMod_smul_eq w (redMod_liftMod (redMod τ 3 β)), hwβ]
    obtain ⟨z, hz⟩ := hdesc n (coe_nWord_mem_monomialSubgroup ω')
    have hroot := langElt_conj_chevTorus_highRoot hτ' F hF0 hωo hω3
    refine ⟨z * x, ?_⟩
    have key : j (z * x * a * (z * x)⁻¹) = j (rho K F 0 (uSL 1 * vSL 1)) := by
      calc j (z * x * a * (z * x)⁻¹) = j z * j (x * a * x⁻¹) * (j z)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = (g * n * g⁻¹) * (g * y * g⁻¹) * (g * n * g⁻¹)⁻¹ := by rw [hz, hjxa]
        _ = g * (n * y * n⁻¹) * g⁻¹ := by group
        _ = j (rho K F 0 (uSL 1 * vSL 1)) := by rw [hny, ← hroot]
    rw [Subgroup.mem_subgroupOf, hjinj key, coe_rho, hF0,
      ← CFSG.SeitzReduction.E6Pilot.range_rootSL2_highRoot]
    exact ⟨_, rfl⟩

theorem exists_conj_mem_highRootSL2_E7_of_le (hK : Nat.card K = 2)
    {A B : Subgroup (adjointGroup .E7 K)} (hA : IsElemAbelian 3 A) (h7 : 3 ^ 7 ≤ Nat.card A)
    (hBA : B ≤ A) (h5 : 3 ^ 5 ≤ Nat.card B) :
    ∃ t ∈ B, t ≠ 1 ∧ ∃ g : adjointGroup .E7 K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf
        (adjointGroup .E7 K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  have hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num)
  have hV := card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  refine exists_conj_mem_highRootSL2_of_weylX_le (Or.inl rfl) frameE7 rfl frameE7_reflections
    cartan_symm_E7 hdet hV (not_three_dvd_index_E7 h3) (T := 3 ^ 7) (T₀ := 3 ^ 5) ?_ hK hA h7
    hBA h5
  intro ζ hζo hζ E E₀ hE hEX hT hE₀E hT₀
  obtain ⟨x, ⟨β, hβ, rfl⟩, hxE⟩ := exists_mem_torusSet_of_le_of_noOffender Nat.prime_three hdet
    hV cartan_symm_E7 hζo hζ (Good := rootModSet .E7) (fun A' hA'S hA' hA'1 => by
      rcases noOffenderRoot_E7 A' hA'S hA' hA'1 with h | ⟨h, -⟩
      · exact h.trans (by norm_num)
      · exact h.trans_lt (by norm_num)) exists_root_mem_E7_of_card hE hEX hT hE₀E hT₀
  exact ⟨β, hβ, hxE⟩

theorem exists_conj_mem_highRootSL2_E8_of_le (hK : Nat.card K = 2)
    {A B : Subgroup (adjointGroup .E8 K)} (hA : IsElemAbelian 3 A) (h8 : 3 ^ 8 ≤ Nat.card A)
    (hBA : B ≤ A) (h6 : 3 ^ 6 ≤ Nat.card B) :
    ∃ t ∈ B, t ≠ 1 ∧ ∃ g : adjointGroup .E8 K,
      g * t * g⁻¹ ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E8 K).subgroupOf
        (adjointGroup .E8 K) := by
  have h3 := three_dvd_natCard_ext_sub_one hK
  have hdet := isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num)
  have hV := card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  refine exists_conj_mem_highRootSL2_of_weylX_le (Or.inr rfl) frameE8 rfl frameE8_reflections
    cartan_symm_E8 hdet hV (not_three_dvd_index_E8 h3) (T := 3 ^ 8) (T₀ := 3 ^ 6) ?_ hK hA h8
    hBA h6
  intro ζ hζo hζ E E₀ hE hEX hT hE₀E hT₀
  obtain ⟨x, ⟨β, hβ, rfl⟩, hxE⟩ := exists_mem_torusSet_of_le_of_noOffender Nat.prime_three hdet
    hV cartan_symm_E8 hζo hζ (Good := rootModSet .E8) (fun A' hA'S hA' hA'1 => by
      rcases noOffenderRoot_E8 A' hA'S hA' hA'1 with h | ⟨h, -⟩
      · exact h.trans (by norm_num)
      · exact h.trans_lt (by norm_num)) exists_root_mem_E8_of_card hE hEX hT hE₀E hT₀
  exact ⟨β, hβ, hxE⟩

end Fusion

end CFSG.StandardType.ExcRootAs
