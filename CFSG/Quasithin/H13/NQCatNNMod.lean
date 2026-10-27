module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNM
public import CFSG.Quasithin.H13.NQCatNNModCore
public import CFSG.Quasithin.H13.NQCatNNModWedge
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall

namespace CFSG.Quasithin.H13.NQCat.NNMod

section Sorting

variable {V : Type} [CommGroup V] [Finite V]

theorem sort_cases {G₀ X : Subgroup (MulAut V)} (hN : Nat.card ↥X = 9999360)
    (hP1 : B51Part1 G₀ X) (hP2 : B51Part2 X) :
    IsIntDirect (commV X) (fixV X) ⊤ ∧
      (SLExteriorTwo X (commV X) ⊥ 5 ∨ SumNatDual X (commV X) 5 ∨
        ∃ k : ℕ, 1 ≤ k ∧
          DirectSumOfCopies X (commV X) ⊥ (FFModel.nat (StatedSL 5 (ZMod 2))) k) := by
  have hN' : Nat.card ↥X = 20160 ∨ Nat.card ↥X = 9999360 := Or.inr hN
  have h4 : ∀ π : ↥(StatedSL 4 (ZMod 2)) →* ↥X, Function.Surjective π → False := by
    intro π hπ
    have h1 := Nat.card_le_card_of_surjective π hπ
    rw [card_statedSL_four_zmod1527d, hN] at h1
    omega
  have hdir : IsIntDirect (commV X) (fixV X) ⊤ := by
    by_contra hnot
    obtain ⟨-, hl⟩ := hP2.2 hnot
    rcases hl with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | hn | hn | hn | hn
    · exact not_binaryNaturalSL_two1527d hN' hn
    · exact not_binaryNaturalSp4_1527d hN' hn
    · exact not_g2Natural1527d hN' hn
    · exact not_alternatingNatural1527d (n := 6) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) hn
    · exact not_alternatingNatural1527d (n := 8) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) hn
    · exact not_g2NaturalDerived_one1527d hN' hn
    · exact not_binaryNaturalSL_three1527d hN' hn
  have hZ : fixV X ⊓ commV X = ⊥ := by
    rw [inf_comm]
    exact hdir.2
  refine ⟨hdir, ?_⟩
  rcases hP1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hpair, -⟩ := hi
    rw [hZ] at hpair
    rcases hpair with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact (not_binaryNaturalSL_two1527d hN' h).elim
    · exact (not_binaryNaturalSL_three1527d hN' h).elim
    · exact (not_binaryNaturalSp4_1527d hN' h).elim
    · exact (not_g2Natural1527d hN' h).elim
    · exact (not_g2NaturalDerived_one1527d hN' h).elim
    · exact (not_alternatingNatural1527d (n := 5) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_alternatingNatural1527d (n := 6) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_alternatingNatural1527d (n := 7) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_a7Four1527d hN' h).elim
    · exact (not_tripleA6Six1527d hN' h).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (h4 π hπ.1).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact Or.inr (Or.inr ⟨1, le_rfl, directSumOfCopies_one1527d hπ⟩)
    · obtain ⟨π, hπ⟩ := h
      exact (h4 π hπ.1).elim
    · exact Or.inl h
  · exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hF (N := Nat.card ↥X) hN'
      (card_eq_of_nat_realizes1527d (hreal 0)).symm
  · obtain ⟨hn, π, U₁, U₂, -, h1, -⟩ := hiii.2
    rcases hn with rfl | rfl
    · exact (h4 π h1.1).elim
    · exact Or.inr (Or.inl hiii.2)
  · obtain ⟨-, n, hn, k, hk1, -, hds⟩ := hiv
    rcases hn with rfl | rfl
    · obtain ⟨I, π, -, -, -, hreal⟩ := hds
      exact (h4 π (hreal ⟨0, hk1⟩).1).elim
    · exact Or.inr (Or.inr ⟨k, hk1, hds⟩)

end Sorting

section Sums

variable {V : Type} [CommGroup V] {ι : Type*}

theorem fix_sup {U₁ U₂ : Subgroup V} (hinf : U₁ ⊓ U₂ = ⊥) (f : ι → MulAut V) (K : ι → Prop)
    (hinv₁ : ∀ i, ∀ u ∈ U₁, f i u ∈ U₁) (hinv₂ : ∀ i, ∀ u ∈ U₂, f i u ∈ U₂)
    (h₁ : ∀ u ∈ U₁, (∀ i, K i → f i u = u) → ∀ i, f i u = u)
    (h₂ : ∀ u ∈ U₂, (∀ i, K i → f i u = u) → ∀ i, f i u = u) :
    ∀ u ∈ U₁ ⊔ U₂, (∀ i, K i → f i u = u) → ∀ i, f i u = u := by
  intro u hu hK
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hu
  have hsplit : ∀ i, K i → f i u₁ = u₁ ∧ f i u₂ = u₂ := by
    intro i hi
    have e := hK i hi
    rw [map_mul] at e
    have hm : f i u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ := by
      refine ⟨U₁.mul_mem (hinv₁ i u₁ hu₁) (U₁.inv_mem hu₁), ?_⟩
      have : f i u₁ * u₁⁻¹ = u₂ * (f i u₂)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, e, mul_comm]
      rw [this]
      exact U₂.mul_mem hu₂ (U₂.inv_mem (hinv₂ i u₂ hu₂))
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hm
    refine ⟨hm, ?_⟩
    rw [hm] at e
    exact mul_left_cancel e
  intro i
  rw [map_mul, h₁ u₁ hu₁ (fun j hj => (hsplit j hj).1) i, h₂ u₂ hu₂ (fun j hj => (hsplit j hj).2) i]

theorem fix_iSup {k : ℕ} (I : Fin k → Subgroup V)
    (hind : ∀ j, I j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), I j' = ⊥) (f : ι → MulAut V) (K : ι → Prop)
    (hinv : ∀ i j, ∀ u ∈ I j, f i u ∈ I j)
    (h : ∀ j, ∀ u ∈ I j, (∀ i, K i → f i u = u) → ∀ i, f i u = u) :
    ∀ u ∈ ⨆ j, I j, (∀ i, K i → f i u = u) → ∀ i, f i u = u := by
  classical
  intro u hu hK
  obtain ⟨x, hx, rfl⟩ : ∃ x : Fin k → V, (∀ j, x j ∈ I j) ∧ u = ∏ j, x j := by
    refine Subgroup.iSup_induction I (C := fun u => ∃ x : Fin k → V, (∀ j, x j ∈ I j) ∧
      u = ∏ j, x j) hu (fun j y hy => ⟨Pi.mulSingle j y, fun j' => ?_, ?_⟩) ⟨1, fun j => ?_, ?_⟩
      (fun a b ⟨xa, hxa, ha⟩ ⟨xb, hxb, hb⟩ => ⟨xa * xb, fun j => (I j).mul_mem (hxa j) (hxb j),
        by rw [ha, hb, Pi.mul_def, Finset.prod_mul_distrib]⟩)
    · by_cases hj : j' = j
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact hy
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact (I j').one_mem
    · simp only [Finset.prod_pi_mulSingle', Finset.mem_univ, ↓reduceIte]
    · exact (I j).one_mem
    · simp
  have hcomp : ∀ i, K i → ∀ j, f i (x j) = x j := by
    intro i hi j
    set y : Fin k → V := fun j => f i (x j) * (x j)⁻¹ with hy
    have hyI : ∀ j, y j ∈ I j := fun j => (I j).mul_mem (hinv i j _ (hx j)) ((I j).inv_mem (hx j))
    have hprod : ∏ j, y j = 1 := by
      rw [hy, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← map_prod, hK i hi,
        mul_inv_cancel]
    have hyj : y j = (∏ j' ∈ Finset.univ.erase j, y j')⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ j), hprod]
    have hmem : y j ∈ I j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), I j' := by
      refine ⟨hyI j, ?_⟩
      rw [hyj]
      refine Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j' hj' => ?_)
      exact (le_iSup₂ (f := fun (j'' : Fin k) (_ : j'' ≠ j) => I j'') j'
        (Finset.ne_of_mem_erase hj')) (hyI j')
    rw [hind j, Subgroup.mem_bot, hy] at hmem
    exact mul_inv_eq_one.1 hmem
  intro i
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => h j (x j) (hx j) (fun i' hi' => hcomp i' hi' j) i

end Sums

section Coord

variable {ι : Type*}

theorem fix_conj (act : SpecialLinearGroup (Fin 5) (ZMod 2) → (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (hone : ∀ w, act 1 w = w)
    (F : ι → SpecialLinearGroup (Fin 5) (ZMod 2)) (K : ι → Prop)
    (g : SpecialLinearGroup (Fin 5) (ZMod 2))
    (h : ∀ w, (∀ i, K i → act (g * F i * g⁻¹) w = w) → ∀ i, act (g * F i * g⁻¹) w = w) :
    ∀ w, (∀ i, K i → act (F i) w = w) → ∀ i, act (F i) w = w := by
  intro w hw i
  have key : ∀ i, act (g * F i * g⁻¹) (act g w) = act g (act (F i) w) := fun i => by
    rw [hmul, hmul, ← hmul g⁻¹ g, inv_mul_cancel, hone]
  have h1 := h (act g w) (fun j hj => by rw [key, hw j hj]) i
  rw [key] at h1
  have h2 := congrArg (act g⁻¹) h1
  have hinv : ∀ v, act g⁻¹ (act g v) = v := fun v => by rw [← hmul, inv_mul_cancel, hone]
  rwa [hinv, hinv] at h2

theorem nact_mul (x y : SpecialLinearGroup (Fin 5) (ZMod 2)) (w : Fin 5 → ZMod 2) :
    ((x * y : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w =
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ((y : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec]

theorem dact_mul (x y : SpecialLinearGroup (Fin 5) (ZMod 2)) (w : Fin 5 → ZMod 2) :
    (((x * y)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w =
      ((x⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ
        (((y⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w) := by
  rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, transpose_mul, mulVec_mulVec]

theorem fix_coord {V : Type} [CommGroup V] [Finite (MulAut V)] {X P D : Subgroup (MulAut V)}
    {τ : MulAut V} (hτX : τ ∈ Subgroup.normalizer (X : Set (MulAut V))) (hP : IsParabolic2 X P)
    (hτP : τ ∈ Subgroup.normalizer (P : Set (MulAut V))) (hDP : D ≤ P)
    (hPD : P ≤ Subgroup.normalizer (D : Set (MulAut V)))
    (π : ↥D →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hπ : Function.Surjective π)
    (hτD : τ ∈ Subgroup.normalizer (D : Set (MulAut V)))
    (hni : ¬ ∃ z : SpecialLinearGroup (Fin 3) (ZMod 2), ∀ d : ↥D,
      π ⟨τ * d * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτD d).mp d.2⟩ = z * π d * z⁻¹)
    (ψ : ↥X ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) (hDX : D ≤ X) :
    (∀ w : Fin 5 → ZMod 2,
      (∀ k : ↥D, π k = 1 → ((ψ ⟨k, hDX k.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) →
      ∀ d : ↥D, ((ψ ⟨d, hDX d.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) ∧
    (∀ w : Fin 5 → ZMod 2,
      (∀ k : ↥D, π k = 1 → (((ψ ⟨k, hDX k.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) →
      ∀ d : ↥D, (((ψ ⟨d, hDX d.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) := by
  obtain ⟨hPX, S, hS, hSP⟩ := hP
  have hS' : IsSylowTwoOf ((S.subgroupOf X).map ψ.toMonoidHom) ⊤ := by
    have hU := Setup.X6.isSylowTwoOf_subgroupOf_top hS
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    have h1 := hU.2.2
    rw [show ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index from
      Subgroup.relIndex_top_right _] at h1
    rw [show (((S.subgroupOf X).map ψ.toMonoidHom).subgroupOf ⊤).index =
        ((S.subgroupOf X).map ψ.toMonoidHom).index from Subgroup.relIndex_top_right _,
      MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact h1
  have hU : IsSylowTwoOf (unitriangular 5 (ZMod 2)) ⊤ :=
    SzN2.isSylowTwoOf_unitriangular (by omega)
  obtain ⟨g, -, hg⟩ := hS'.exists_conj hU
  let θ : ↥X ≃* SpecialLinearGroup (Fin 5) (ZMod 2) := ψ.trans (MulAut.conj g)
  have hθS : (S.subgroupOf X).map θ.toMonoidHom = unitriangular 5 (ZMod 2) := by
    rw [hg, Subgroup.map_map]
    rfl
  let ct : ↥X ≃* ↥X :=
    { toFun := fun y => ⟨τ * y * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτX y).mp y.2⟩
      invFun := fun y => ⟨τ⁻¹ * y * τ, by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hτX) y).mp y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)) := θ.symm.trans (ct.trans θ)
  have hα : ∀ y : ↥X, α (θ y) = θ (ct y) := fun y => by simp [α]
  set P' := (P.subgroupOf X).map θ.toMonoidHom with hP'
  set D' := (D.subgroupOf X).map θ.toMonoidHom with hD'
  have hBP' : upperTriangular 5 (ZMod 2) ≤ P' := by
    rw [← normalizer_unitriangular, ← hθS, ← Subgroup.map_equiv_normalizer_eq,
      ← Subgroup.subgroupOf_normalizer_eq hS.1]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hSP ⟨y.2, hy⟩, rfl⟩
  have hDP' : D' ≤ P' := Subgroup.map_mono fun y hy => hDP hy
  have hPD' : P' ≤ Subgroup.normalizer (D' : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    rw [hD', ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.subgroupOf_normalizer_eq hDX]
    exact Subgroup.map_mono fun y hy => hPD hy
  have hct : ∀ {H : Subgroup (MulAut V)}, τ ∈ Subgroup.normalizer (H : Set (MulAut V)) →
      ∀ y : ↥X, (y : MulAut V) ∈ H ↔ ((ct y : ↥X) : MulAut V) ∈ H := fun hH y =>
    Subgroup.mem_normalizer_iff.mp hH y
  have hαP : P'.map α.toMonoidHom = P' := by
    ext b
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨ct y, ?_, (hα y).symm⟩
      exact (hct hτP y).1 hy
    · rintro ⟨y, hy, rfl⟩
      refine ⟨θ (ct.symm y), ⟨ct.symm y, ?_, rfl⟩, ?_⟩
      · show ((ct.symm y : ↥X) : MulAut V) ∈ P
        rw [hct hτP, MulEquiv.apply_symm_apply]
        exact hy
      · rw [MulEquiv.coe_toMonoidHom, hα, MulEquiv.apply_symm_apply]
        rfl
  have hαD : ∀ d ∈ D', α d ∈ D' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hα]
    exact ⟨ct y, (hct hτD y).1 hy, rfl⟩
  have hαD' : ∀ d, α d ∈ D' → d ∈ D' := by
    intro d hd
    obtain ⟨y, rfl⟩ := θ.surjective d
    rw [hα] at hd
    obtain ⟨y', hy', hyy'⟩ := hd
    have : y' = ct y := θ.injective hyy'
    subst this
    exact ⟨y, (hct hτD y).2 hy', rfl⟩
  let ψD : ↥D ≃* ↥D' := (Subgroup.subgroupOfEquivOfLe hDX).symm.trans
    ((D.subgroupOf X).equivMapOfInjective θ.toMonoidHom θ.injective)
  have hψD : ∀ d : ↥D, ((ψD d : ↥D') : SpecialLinearGroup (Fin 5) (ZMod 2)) =
      θ ⟨d, hDX d.2⟩ := fun d => rfl
  let π' : ↥D' →* SpecialLinearGroup (Fin 3) (ZMod 2) := π.comp ψD.symm.toMonoidHom
  have hπ' : Function.Surjective π' := hπ.comp ψD.symm.surjective
  have e1 : ∀ x : ↥D, π' (ψD x) = π x := fun x => by
    simp only [π', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hni' : ¬ ∃ z : SpecialLinearGroup (Fin 3) (ZMod 2),
      ∀ d : ↥D', π' ⟨α d, hαD d d.2⟩ = z * π' d * z⁻¹ := by
    rintro ⟨z, hz⟩
    refine hni ⟨z, fun d => ?_⟩
    have h1 := hz (ψD d)
    have h2 : (⟨α (ψD d), hαD _ (ψD d).2⟩ : ↥D') =
        ψD ⟨τ * d * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτD d).mp d.2⟩ := by
      apply Subtype.ext
      show α ((ψD d : ↥D') : SpecialLinearGroup (Fin 5) (ZMod 2)) =
        ((ψD ⟨τ * d * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτD d).mp d.2⟩ : ↥D') :
          SpecialLinearGroup (Fin 5) (ZMod 2))
      rw [hψD, hψD, hα]
      rfl
    rw [h2, e1, e1] at h1
    exact h1
  have hPq := eq_q14 hBP' hDP' hPD' π' hπ' α hαP hαD hαD' hni'
  have hDQ : D' ≤ Q14 := by
    show D' ≤ flagStabilizer 5 (ZMod 2) {1, 4}
    rw [← hPq]
    exact hDP'
  have hQD : Q14 ≤ Subgroup.normalizer (D' : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    show flagStabilizer 5 (ZMod 2) {1, 4} ≤ _
    rw [← hPq]
    exact hPD'
  obtain ⟨hfn, hfd⟩ := fix_q14 hDQ hQD π' hπ'
  have hθ : ∀ d : ↥D, ((ψD d : ↥D') : SpecialLinearGroup (Fin 5) (ZMod 2)) =
      g * ψ ⟨d, hDX d.2⟩ * g⁻¹ := fun d => rfl
  have hK : ∀ k' : ↥D', π' k' = 1 → ∃ k : ↥D, π k = 1 ∧ ψD k = k' := fun k' hk' => by
    obtain ⟨k, rfl⟩ := ψD.surjective k'
    exact ⟨k, by rwa [e1] at hk', rfl⟩
  constructor
  · refine fix_conj (fun x w => (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w) nact_mul
      (fun w => by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])
      (fun d : ↥D => ψ ⟨d, hDX d.2⟩) (fun d => π d = 1) g fun w hw d => ?_
    have h1 := hfn w (fun k' hk' => by
      obtain ⟨k, hk, rfl⟩ := hK k' hk'
      rw [hθ]
      exact hw k hk) (ψD d)
    rwa [hθ] at h1
  · refine fix_conj (fun x w => ((x⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w) dact_mul
      (fun w => by rw [inv_one, Matrix.SpecialLinearGroup.coe_one, transpose_one, one_mulVec])
      (fun d : ↥D => ψ ⟨d, hDX d.2⟩) (fun d => π d = 1) g fun w hw d => ?_
    have h1 := hfd w (fun k' hk' => by
      obtain ⟨k, hk, rfl⟩ := hK k' hk'
      rw [hθ]
      exact hw k hk) (ψD d)
    rwa [hθ] at h1

end Coord

section Sections

variable {V : Type} [CommGroup V] {ι : Type*}

theorem exists_coord {X : Subgroup (MulAut V)} (hN : Nat.card ↥X = 9999360)
    {π₁ : ↥(StatedSL 5 (ZMod 2)) →* ↥X} (hs : Function.Surjective π₁) :
    ∃ ψ : ↥X ≃* SpecialLinearGroup (Fin 5) (ZMod 2),
      ∀ x : ↥X, π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) = x := by
  have hb : Function.Bijective π₁ :=
    hs.bijective_of_nat_card_le (by rw [card_statedSL_five_zmod1527d, hN])
  let e : SpecialLinearGroup (Fin 5) (ZMod 2) ≃* ↥X :=
    (specialLinearGroupEquivStatedSL 5 (ZMod 2)).trans (MulEquiv.ofBijective π₁ hb)
  exact ⟨e.symm, fun x => e.apply_symm_apply x⟩

theorem nat_fix {X : Subgroup (MulAut V)} {U₁ : Subgroup V} {π₁ : ↥(StatedSL 5 (ZMod 2)) →* ↥X}
    (h : (FFModel.nat (StatedSL 5 (ZMod 2))).RealizesVia X U₁ ⊥ π₁)
    (ψ : ↥X ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hψ : ∀ x : ↥X, π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) = x)
    (F : ι → ↥X) (K : ι → Prop)
    (hfix : ∀ w : Fin 5 → ZMod 2,
      (∀ i, K i → ((ψ (F i) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) →
      ∀ i, ((ψ (F i) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) :
    ∀ u ∈ U₁, (∀ i, K i → ((F i : ↥X) : MulAut V) u = u) → ∀ i, ((F i : ↥X) : MulAut V) u = u := by
  obtain ⟨f, -, hfk, hfe⟩ := FFC.exists_natMap h
  have hinj : ∀ a b : ↥U₁, f a = f b → a = b := fun a b hab => by
    have h1 : f (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have h2 := (hfk _).1 h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.1 (Subtype.ext h2)
  have hact : ∀ (x : ↥X) (u : ↥U₁) (hu : (x : MulAut V) u ∈ U₁),
      Multiplicative.toAdd (f ⟨_, hu⟩) = ((ψ x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (f u) := by
    intro x u hu
    have hu' : ((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u ∈ U₁ :=
      by rw [hψ]; exact hu
    have e := hfe (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) u hu'
    have e1 : (⟨((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u, hu'⟩ :
        ↥U₁) = ⟨(x : MulAut V) u, hu⟩ := Subtype.ext (by
      show ((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u =
        (x : MulAut V) u
      rw [hψ])
    rw [e1] at e
    rw [e]
    rfl
  intro u hu hK i
  have hw : ∀ i, K i → ((ψ (F i) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (f ⟨u, hu⟩) =
        Multiplicative.toAdd (f ⟨u, hu⟩) := fun i hi => by
    have hu2 : ((F i : ↥X) : MulAut V) u ∈ U₁ := by rw [hK i hi]; exact hu
    rw [← hact (F i) ⟨u, hu⟩ hu2]
    congr 2
    exact Subtype.ext (hK i hi)
  have h2 := hfix _ hw i
  have h3 := hact (F i) ⟨u, hu⟩ (h.2.2.2.1 (F i) u hu)
  rw [h2] at h3
  exact congrArg Subtype.val (hinj _ _ (Multiplicative.toAdd.injective h3))

theorem dual_fix {X : Subgroup (MulAut V)} {U₂ : Subgroup V} {π₁ : ↥(StatedSL 5 (ZMod 2)) →* ↥X}
    (h : (FFModel.dualNat (StatedSL 5 (ZMod 2))).RealizesVia X U₂ ⊥ π₁)
    (ψ : ↥X ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hψ : ∀ x : ↥X, π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) = x)
    (F : ι → ↥X) (K : ι → Prop)
    (hfix : ∀ w : Fin 5 → ZMod 2,
      (∀ i, K i → (((ψ (F i))⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) →
      ∀ i, (((ψ (F i))⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) :
    ∀ u ∈ U₂, (∀ i, K i → ((F i : ↥X) : MulAut V) u = u) → ∀ i, ((F i : ↥X) : MulAut V) u = u := by
  obtain ⟨f, -, hfk, hfe⟩ := FFC.RealizesVia.secMap (D := FFModel.dualNat (StatedSL 5 (ZMod 2)))
    rfl h
  let f' : ↥U₂ → Fin 5 → ZMod 2 := fun u => Multiplicative.toAdd
    ((f u : ↥(FFModel.dualNat (StatedSL 5 (ZMod 2))).sec) :
      (FFModel.dualNat (StatedSL 5 (ZMod 2))).Amb)
  have hinj : ∀ a b : ↥U₂, f' a = f' b → a = b := fun a b hab => by
    have hab' : f a = f b := Subtype.ext (Multiplicative.toAdd.injective hab)
    have h1 : f (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab']
      exact mul_inv_cancel _
    have h2 := (hfk _).1 h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.1 (Subtype.ext h2)
  have hfe' : ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (u : ↥U₂) (hu : ((π₁ γ : ↥X) : MulAut V) u ∈ U₂),
      f' ⟨_, hu⟩ = ((((γ⁻¹ : ↥(StatedSL 5 (ZMod 2))) : GL (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))ᵀ *ᵥ f' u :=
    fun γ u hu => congrArg Multiplicative.toAdd (hfe γ u hu)
  have hact : ∀ (x : ↥X) (u : ↥U₂) (hu : (x : MulAut V) u ∈ U₂),
      f' ⟨_, hu⟩ = (((ψ x)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ f' u := by
    intro x u hu
    have hu' : ((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u ∈ U₂ :=
      by rw [hψ]; exact hu
    have e := hfe' (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) u hu'
    have e1 : (⟨((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u, hu'⟩ :
        ↥U₂) = ⟨(x : MulAut V) u, hu⟩ := Subtype.ext (by
      show ((π₁ (specialLinearGroupEquivStatedSL 5 (ZMod 2) (ψ x)) : ↥X) : MulAut V) u =
        (x : MulAut V) u
      rw [hψ])
    rw [e1, ← map_inv, specialLinearGroupEquivStatedSL_coe] at e
    exact e
  intro u hu hK i
  have hw : ∀ i, K i → (((ψ (F i))⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ f' ⟨u, hu⟩ = f' ⟨u, hu⟩ := fun i hi => by
    have hu2 : ((F i : ↥X) : MulAut V) u ∈ U₂ := by rw [hK i hi]; exact hu
    rw [← hact (F i) ⟨u, hu⟩ hu2]
    congr 1
    exact Subtype.ext (hK i hi)
  have h2 := hfix _ hw i
  have h3 := hact (F i) ⟨u, hu⟩ (h.2.2.2.1 (F i) u hu)
  rw [h2] at h3
  exact congrArg Subtype.val (hinj _ _ h3)

end Sections

section Wedge

variable {V : Type} [CommGroup V]

theorem apply_mem_fixV {X : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (X : Set (MulAut V))) {w : V} (hw : w ∈ fixV X) :
    a w ∈ fixV X :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer ha hw

theorem false_of_extSq [Finite V] {X : Subgroup (MulAut V)} {τ : MulAut V}
    (hN : Nat.card ↥X = 9999360) (hdir : IsIntDirect (commV X) (fixV X) ⊤)
    (hE : SLExteriorTwo X (commV X) ⊥ 5)
    (hτX : τ ∈ Subgroup.normalizer (X : Set (MulAut V)))
    (hτout : ¬ ∃ x ∈ X, ∀ y ∈ X, τ * y * τ⁻¹ = x * y * x⁻¹) : False := by
  obtain ⟨πE, hπE⟩ := hE
  obtain ⟨F, hFs, hFk, hFe⟩ := exists_wedgeMap hπE hdir.1 hdir.2
  obtain ⟨ψ, hψ⟩ := exists_coord hN hπE.1
  let ρ : SpecialLinearGroup (Fin 5) (ZMod 2) →* MulAut V := X.subtype.comp ψ.symm.toMonoidHom
  have hψs : ∀ g, πE (specialLinearGroupEquivStatedSL 5 (ZMod 2) g) = ψ.symm g := fun g => by
    have := hψ (ψ.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hρ : ∀ g w, Multiplicative.toAdd (F (ρ g w)) =
      wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (F w) := by
    intro g w
    have e := hFe (specialLinearGroupEquivStatedSL 5 (ZMod 2) g) w
    rw [specialLinearGroupEquivStatedSL_coe] at e
    show Multiplicative.toAdd (F (((ψ.symm g : ↥X) : MulAut V) w)) = _
    rw [← hψs g]
    exact e
  let ct : ↥X ≃* ↥X :=
    { toFun := fun y => ⟨τ * y * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτX y).mp y.2⟩
      invFun := fun y => ⟨τ⁻¹ * y * τ, by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hτX) y).mp y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)) := ψ.symm.trans (ct.trans ψ)
  have hα : ∀ g, ρ (α g) = τ * ρ g * τ⁻¹ := fun g => by
    show ((ψ.symm (ψ (ct (ψ.symm g))) : ↥X) : MulAut V) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hout : ¬ ∃ x : SpecialLinearGroup (Fin 5) (ZMod 2), ∀ y, α y = x * y * x⁻¹ := by
    rintro ⟨x, hx⟩
    refine hτout ⟨ρ x, (ψ.symm x).2, fun y hy => ?_⟩
    obtain ⟨y', hy'⟩ : ∃ y' : SpecialLinearGroup (Fin 5) (ZMod 2), ρ y' = y :=
      ⟨ψ ⟨y, hy⟩, by simp [ρ]⟩
    rw [← hy', ← hα, hx, map_mul, map_mul, map_inv]
  obtain ⟨A, σ, h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (by norm_num) α
  have hσ : ∀ c : ZMod 2, σ c = c := by
    intro c
    fin_cases c
    · exact map_zero σ
    · exact map_one σ
  have hmap : ∀ M : Matrix (Fin 5) (Fin 5) (ZMod 2), M.map σ = M := fun M => by
    ext r c
    simp [hσ]
  have hAA : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) * ((A⁻¹ : GL (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := SLk.det_eq_one_of_mul_eq_one hAA
  set A' : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨A, hdet⟩ with hA'
  have hA'inv : ((A'⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one,
      one_smul]
  rcases h with h | h
  · refine hout ⟨A', fun y => Subtype.ext ?_⟩
    rw [h, hmap, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hA'inv]
  · refine false_of_wedge F hFs ρ hρ τ (fun w hw => ?_) (fun w hw => ?_) α hα A' fun g => ?_
    · rw [hFk] at hw ⊢
      exact apply_mem_fixV hτX hw
    · rw [hFk] at hw ⊢
      exact apply_mem_fixV (inv_mem hτX) hw
    · rw [h, hmap, hA'inv]

end Wedge

section Main

theorem lem1211NNMod_holds : Lem1211NNMod := by
  intro V _ _ _ G₀ X P D τ hX hP1 hP2 hτX hτout hP hτP hDP hPD π hπ _ hτD hni v hv d
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) fun a b hab => MulEquiv.ext (congrFun hab)
  obtain ⟨e₀⟩ := hX
  have hN : Nat.card ↥X = 9999360 := by
    rw [Nat.card_congr e₀.toEquiv]
    exact card_statedSL_five_zmod1527d
  obtain ⟨hdir, hcase⟩ := sort_cases hN hP1 hP2
  have hDX : D ≤ X := hDP.trans hP.1
  have hXinv : ∀ (x : ↥D), ∀ {U : Subgroup V}, (∀ h : ↥X, ∀ u ∈ U, (h : MulAut V) u ∈ U) →
      ∀ u ∈ U, (x : MulAut V) u ∈ U := fun x _ hU u hu => hU ⟨x, hDX x.2⟩ u hu
  have hred : ∀ u ∈ commV X, (∀ k : ↥D, π k = 1 → (k : MulAut V) u = u) →
      ∀ d : ↥D, (d : MulAut V) u = u := by
    rcases hcase with hE | ⟨-, π₁, U₁, U₂, hdirU, h1, h2⟩ | ⟨k, hk1, I, πC, -, hind, hsupI, hreal⟩
    · exact (false_of_extSq hN hdir hE hτX hτout).elim
    ·
      obtain ⟨ψ, hψ⟩ := exists_coord hN h1.1
      obtain ⟨hfn, hfd⟩ := fix_coord hτX hP hτP hDP hPD π hπ hτD hni ψ hDX
      rw [← hdirU.1]
      exact fix_sup hdirU.2 (fun d : ↥D => (d : MulAut V)) (fun k => π k = 1)
        (fun x => hXinv x h1.2.2.2.1) (fun x => hXinv x h2.2.2.2.1)
        (nat_fix h1 ψ hψ (fun d : ↥D => ⟨d, hDX d.2⟩) _ hfn)
        (dual_fix h2 ψ hψ (fun d : ↥D => ⟨d, hDX d.2⟩) _ hfd)
    ·
      obtain ⟨ψ, hψ⟩ := exists_coord hN (hreal ⟨0, hk1⟩).1
      obtain ⟨hfn, -⟩ := fix_coord hτX hP hτP hDP hPD π hπ hτD hni ψ hDX
      rw [← hsupI, bot_sup_eq]
      refine fix_iSup I (fun j => ?_) (fun d : ↥D => (d : MulAut V)) (fun k => π k = 1)
        (fun x j => hXinv x (hreal j).2.2.2.1)
        (fun j => nat_fix (hreal j) ψ hψ (fun d : ↥D => ⟨d, hDX d.2⟩) _ hfn)
      have := hind j
      rwa [bot_sup_eq] at this
  have hv' : v ∈ commV X ⊔ fixV X := by
    rw [hdir.1]
    exact Subgroup.mem_top v
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv'
  have hcD : ∀ x : ↥D, (x : MulAut V) c = c := fun x => hc _ (hDX x.2)
  have hu' : ∀ k : ↥D, π k = 1 → (k : MulAut V) u = u := fun k hk => by
    have := hv k (MonoidHom.mem_ker.2 hk)
    rw [map_mul, hcD] at this
    exact mul_right_cancel this
  rw [map_mul, hred u hu hu' d, hcD]

end Main

end CFSG.Quasithin.H13.NQCat.NNMod
