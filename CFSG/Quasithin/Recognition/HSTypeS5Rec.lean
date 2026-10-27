module

public import CFSG.Quasithin.Background.I4Recognition
public import CFSG.Quasithin.Recognition.HSTypeAutA5
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.GorensteinWalter CFSG.Quasithin.I4

theorem dihedral_four_central : ∀ a : DihedralGroup 4, a * a = 1 → a ≠ 1 →
    (∀ b : DihedralGroup 4, a * b = b * a) → a = DihedralGroup.r 2 := by
  decide

theorem dihedral_four_conj_mul : ∀ a : DihedralGroup 4, a * a = 1 → a ≠ 1 →
    a ≠ DihedralGroup.r 2 → ∃ b : DihedralGroup 4, b * a * b⁻¹ = DihedralGroup.r 2 * a := by
  decide

theorem dihedral_four_sq : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 = DihedralGroup.r 2 := by
  decide

theorem eq_bot_of_inf_centralizer_eq_bot_three {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} [K.Normal] {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hKa : K ⊓ Subgroup.centralizer {a} = ⊥)
    (hKb : K ⊓ Subgroup.centralizer {b} = ⊥)
    (hKab : K ⊓ Subgroup.centralizer {a * b} = ⊥) : K = ⊥ := by
  have hinv : ∀ u : G, orderOf u = 2 → K ⊓ Subgroup.centralizer {u} = ⊥ →
      ∀ k ∈ K, u * k * u⁻¹ = k⁻¹ := by
    intro u hu hKu k hk
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    let φ : MulAut K := MulAut.conjNormal u
    have hφ : ∀ x : K, (φ x : G) = u * x * u⁻¹ := fun x => MulAut.conjNormal_apply u x
    have hfree : MonoidHom.FixedPointFree φ := by
      intro x hx
      have hx' : (x : G) ∈ K ⊓ Subgroup.centralizer {u} := by
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg Subtype.val hx
        rw [hφ] at h
        calc (x : G) * u = u * x * u⁻¹ * u := by rw [h]
          _ = u * x := by group
      rw [hKu, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have huu : u * u = 1 := by rw [← sq]; exact hu2
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hinvol : Function.Involutive φ := by
      intro x
      apply Subtype.ext
      rw [hφ, hφ, hui]
      calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [huu, one_mul, mul_one]
    have h := congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨k, hk⟩
    have h' := congrArg Subtype.val h
    rwa [hφ] at h'
  rw [eq_bot_iff, ← hKab]
  intro k hk
  refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hk' : (a * b) * k * (a * b)⁻¹ = k := by
    have e1 : (a * b) * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
    rw [e1, hinv b hb hKb k hk]
    have e2 : a * k⁻¹ * a⁻¹ = (a * k * a⁻¹)⁻¹ := by group
    rw [e2, hinv a ha hKa k hk, inv_inv]
  calc k * (a * b) = (a * b) * k * (a * b)⁻¹ * (a * b) := by rw [hk']
    _ = (a * b) * k := by group

theorem exists_embedding_of_alt {C : Type*} [Group C] {n : ℕ} {L : Subgroup C} [L.Normal]
    (eA : ↥L ≃* ↥(alternatingGroup (Fin n)))
    (haut : ∀ α : ↥(alternatingGroup (Fin n)) ≃* ↥(alternatingGroup (Fin n)),
      ∃ ρ : Equiv.Perm (Fin n), ∀ σ : ↥(alternatingGroup (Fin n)),
        ((α σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = ρ * σ * ρ⁻¹)
    (huniq : ∀ ρ : Equiv.Perm (Fin n),
      (∀ σ ∈ alternatingGroup (Fin n), ρ * σ = σ * ρ) → ρ = 1)
    (hCL : ∀ c : C, (∀ l ∈ L, c * l = l * c) → c = 1) :
    ∃ θ : C →* Equiv.Perm (Fin n), Function.Injective θ ∧
      ∀ l : ↥L, θ l = ((eA l : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
  classical
  let α : C → (↥(alternatingGroup (Fin n)) ≃* ↥(alternatingGroup (Fin n))) := fun c =>
    eA.symm.trans ((MulAut.conjNormal c).trans eA)
  have hα : ∀ (c : C) (l : ↥L), ((α c (eA l) : ↥(alternatingGroup (Fin n))) :
      Equiv.Perm (Fin n)) = ((eA ⟨c * l * c⁻¹, (inferInstance : L.Normal).conj_mem _ l.2 c⟩ :
        ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
    intro c l
    simp only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 2
  let ρ : C → Equiv.Perm (Fin n) := fun c => (haut (α c)).choose
  have hρ : ∀ (c : C) (σ : ↥(alternatingGroup (Fin n))),
      ((α c σ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) = ρ c * σ * (ρ c)⁻¹ :=
    fun c => (haut (α c)).choose_spec
  have huniq' : ∀ π π' : Equiv.Perm (Fin n), (∀ σ ∈ alternatingGroup (Fin n),
      π * σ * π⁻¹ = π' * σ * π'⁻¹) → π = π' := by
    intro π π' h
    have := huniq (π'⁻¹ * π) fun σ hσ => by
      have h1 := h σ hσ
      calc π'⁻¹ * π * σ = π'⁻¹ * (π * σ * π⁻¹) * π := by group
        _ = π'⁻¹ * (π' * σ * π'⁻¹) * π := by rw [h1]
        _ = σ * (π'⁻¹ * π) := by group
    calc π = π' * (π'⁻¹ * π) := by group
      _ = π' := by rw [this, mul_one]
  have hmul : ∀ c d : C, ρ (c * d) = ρ c * ρ d := by
    intro c d
    refine huniq' _ _ fun σ hσ => ?_
    obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
    have e1 := hρ (c * d) ⟨σ, hσ⟩
    have e2 := hρ d ⟨σ, hσ⟩
    have e3 := hρ c (α d ⟨σ, hσ⟩)
    rw [← hl, hα] at e1
    rw [← hl, hα] at e2
    have e4 : α d (eA l) = eA ⟨d * l * d⁻¹, (inferInstance : L.Normal).conj_mem _ l.2 d⟩ :=
      Subtype.ext (hα d l)
    rw [← hl, e4, hα] at e3
    have e5 : (⟨c * d * l * (c * d)⁻¹, (inferInstance : L.Normal).conj_mem _ l.2 (c * d)⟩ : ↥L) =
        ⟨c * (d * l * d⁻¹) * c⁻¹, (inferInstance : L.Normal).conj_mem _
          ((inferInstance : L.Normal).conj_mem _ l.2 d) c⟩ := Subtype.ext (by group)
    show ρ (c * d) * σ * (ρ (c * d))⁻¹ = ρ c * ρ d * σ * (ρ c * ρ d)⁻¹
    have hσ' : σ = ((eA l : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by rw [hl]
    rw [hσ', ← e1, e5, e3, e2]
    group
  let θ : C →* Equiv.Perm (Fin n) :=
    { toFun := ρ
      map_one' := huniq' _ _ fun σ hσ => by
        have := hρ 1 ⟨σ, hσ⟩
        obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
        rw [← hl, hα] at this
        have e : (⟨1 * l * 1⁻¹, (inferInstance : L.Normal).conj_mem _ l.2 1⟩ : ↥L) = l :=
          Subtype.ext (by simp)
        rw [e] at this
        rw [show σ = ((eA l : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) by rw [hl],
          ← this]
        group
      map_mul' := hmul }
  refine ⟨θ, fun c d hcd => ?_, fun l => ?_⟩
  ·
    have h1 : ρ (d⁻¹ * c) = 1 := by
      have : θ (d⁻¹ * c) = 1 := by rw [map_mul, map_inv, hcd, inv_mul_cancel]
      exact this
    have hcen : ∀ l ∈ L, d⁻¹ * c * l = l * (d⁻¹ * c) := by
      intro l hl
      have e1 := hρ (d⁻¹ * c) (eA ⟨l, hl⟩)
      rw [hα, h1, one_mul, inv_one, mul_one] at e1
      have e2 := eA.injective (Subtype.ext e1)
      have e3 := congrArg Subtype.val e2
      simp only at e3
      calc d⁻¹ * c * l = d⁻¹ * c * l * (d⁻¹ * c)⁻¹ * (d⁻¹ * c) := by group
        _ = l * (d⁻¹ * c) := by rw [e3]
    have := hCL _ hcen
    calc c = d * (d⁻¹ * c) := by group
      _ = d := by rw [this, mul_one]
  ·
    show ρ l = _
    refine huniq' _ _ fun σ hσ => ?_
    obtain ⟨m, hm⟩ := eA.surjective ⟨σ, hσ⟩
    have e1 := hρ (l : C) ⟨σ, hσ⟩
    rw [← hm, hα] at e1
    have e2 : (⟨(l : C) * m * (l : C)⁻¹, (inferInstance : L.Normal).conj_mem _ m.2 l⟩ : ↥L) =
        l * m * l⁻¹ := rfl
    rw [e2, map_mul, map_mul, map_inv] at e1
    rw [show σ = ((eA m : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) by rw [hm], ← e1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem card_centralizer_subtype {G : Type*} [Group G] (L : Subgroup G) {z : G} (hz : z ∈ L) :
    Nat.card (Subgroup.centralizer ({⟨z, hz⟩} : Set ↥L)) =
      Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2))⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem dihedral_four_center : ∀ a : DihedralGroup 4,
    (∀ b : DihedralGroup 4, a * b = b * a) → a = 1 ∨ a = DihedralGroup.r 2 := by
  decide

theorem s4_or_s5_of_dihedral
    {C : Type} [Group C] [Finite C] (D : Sylow 2 C) (eD : (D : Subgroup C) ≃* DihedralGroup 4)
    {z : C} (hz : orderOf z = 2) (hC : Subgroup.centralizer ({z} : Set C) = D)
    {e : C} (he : orderOf e = 2) (heD : e ∈ (D : Subgroup C)) (hez : e ≠ z)
    (hze : IsConj z e) {f : C} (hf : orderOf f = 2) (hfD : f ∈ (D : Subgroup C))
    (hzf : ¬ IsConj z f) {w : C} (hw : orderOf w = 3) :
    Nonempty (C ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (C ≃* Equiv.Perm (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : HasDihedralSylowTwo C := hasDihedralSylowTwo_of_sylow D (by norm_num) eD
  have hzC : z ∈ Subgroup.centralizer ({z} : Set C) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzD : z ∈ (D : Subgroup C) := by rw [← hC]; exact hzC
  have hCp : IsPGroup 2 (Subgroup.centralizer ({z} : Set C)) := hC ▸ D.isPGroup'
  have hcardD : Nat.card (D : Subgroup C) = 8 :=
    (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
  have hDz : ∀ y : (D : Subgroup C), (y : C) * z = z * y := fun y => by
    have hy : (y : C) ∈ Subgroup.centralizer ({z} : Set C) := by rw [hC]; exact y.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hinvD : ∀ y : (D : Subgroup C), orderOf (y : C) = 2 → eD y * eD y = 1 ∧ eD y ≠ 1 := by
    intro y hy
    refine ⟨?_, fun h1 => ?_⟩
    · rw [← map_mul]
      have hyy : (y : C) * y = 1 := by
        have := pow_orderOf_eq_one (y : C)
        rwa [hy, sq] at this
      have : y * y = 1 := Subtype.ext hyy
      rw [this, map_one]
    · have := congrArg Subtype.val (eD.injective (h1.trans (map_one eD).symm))
      rw [Subgroup.coe_one] at this
      rw [this, orderOf_one] at hy
      exact absurd hy (by norm_num)
  have hz' : eD ⟨z, hzD⟩ = DihedralGroup.r 2 := by
    obtain ⟨h1, h2⟩ := hinvD ⟨z, hzD⟩ hz
    refine dihedral_four_central _ h1 h2 fun b => ?_
    obtain ⟨y, rfl⟩ := eD.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hDz y).symm
  obtain ⟨d, hde⟩ : ∃ d : (D : Subgroup C), (d : C) * e * (d : C)⁻¹ = z * e := by
    obtain ⟨h1, h2⟩ := hinvD ⟨e, heD⟩ he
    have h3 : eD ⟨e, heD⟩ ≠ DihedralGroup.r 2 := fun h => hez (by
      have := eD.injective (h.trans hz'.symm)
      exact congrArg Subtype.val this)
    obtain ⟨b, hb⟩ := dihedral_four_conj_mul _ h1 h2 h3
    refine ⟨eD.symm b, ?_⟩
    have : eD.symm b * ⟨e, heD⟩ * (eD.symm b)⁻¹ = ⟨z, hzD⟩ * ⟨e, heD⟩ := by
      apply eD.injective
      rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply, hb, hz']
    exact congrArg Subtype.val this
  have hKz : pPrimeCore 2 C ⊓ Subgroup.centralizer {z} = ⊥ := by
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := 2) (G := C)).symm
  have hKe : pPrimeCore 2 C ⊓ Subgroup.centralizer {e} = ⊥ :=
    inf_centralizer_eq_bot_of_isConj hKz hze
  have hKze : pPrimeCore 2 C ⊓ Subgroup.centralizer {z * e} = ⊥ :=
    inf_centralizer_eq_bot_of_isConj hKe (isConj_iff.mpr ⟨d, hde⟩)
  have hO : pPrimeCore 2 C = ⊥ := eq_bot_of_inf_centralizer_eq_bot_three hz he hKz hKe hKze
  let eQ : C ⧸ pPrimeCore 2 C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases gorensteinWalter C hdih with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ |
      ⟨-, K, hK, L, hLn, hLodd, hLmodel⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (hTwo.of_equiv eQ) w
    have h3 := orderOf_dvd_of_pow_eq_one hk
    rw [hw] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  ·
    exfalso
    let f7 : C ≃* alternatingGroup (Fin 7) := eQ.symm.trans h7
    have hfz : orderOf (f7 z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (f7 z) a7t
      (isInvolution_of_orderOf_eq_two hfz) a7t_involution
    have h24 : (24 : ℕ) = 8 := by
      rw [← a7t_centralizer_card, ← hg]
      change Nat.card (Subgroup.centralizer {(MulAut.conj g) (f7 z)}) = 8
      rw [card_centralizer_map, card_centralizer_map, hC, hcardD]
    norm_num at h24
  ·
    obtain ⟨p, fexp, hp, hpodd, hf0, hKcard⟩ := hK
    have : Fact p.Prime := ⟨hp⟩
    have hqodd : Odd (Nat.card K) := hKcard ▸ hpodd.pow
    have : L.Normal := hLn
    set L' : Subgroup C := L.map eQ.toMonoidHom with hL'def
    have hL'n : L'.Normal := hLn.map eQ.toMonoidHom eQ.surjective
    have hL'odd : Odd L'.index := by
      rw [hL'def, Subgroup.index_map_of_injective _ eQ.injective,
        MonoidHom.range_eq_top.mpr eQ.surjective, Subgroup.index_top, mul_one]
      exact hLodd
    let eL : L' ≃* L := (L.equivMapOfInjective eQ.toMonoidHom eQ.injective).symm
    have hDL : (D : Subgroup C) ≤ L' := le_of_odd_index hL'odd D.isPGroup'
    have hnotPSL : ∀ M : Subgroup C, Nonempty (M ≃* PSL2 K) → ∀ (hzM : z ∈ M) (hfM : f ∈ M),
        False := by
      intro M ⟨eM⟩ hzM hfM
      have hz' : orderOf (eM ⟨z, hzM⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
      have hf' : orderOf (eM ⟨f, hfM⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hf]
      have hc := CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hKcard hpodd hf0 hz' hf'
      have hc' : IsConj (⟨z, hzM⟩ : M) ⟨f, hfM⟩ := by
        simpa using eM.symm.toMonoidHom.map_isConj hc
      exact hzf (M.subtype.map_isConj hc')
    rcases hLmodel with hPSL | hPGL
    · obtain ⟨ePSL⟩ := hPSL
      exact (hnotPSL L' ⟨eL.trans ePSL⟩ (hDL hzD) (hDL hfD)).elim
    · obtain ⟨ePGL⟩ := hPGL
      let eP : L' ≃* PGL2 K := eL.trans ePGL
      have hK' : IsOddPrimePower (Nat.card K) := ⟨p, fexp, hp, hpodd, hf0, hKcard⟩
      obtain ⟨L'', hL''n, hL''L, ⟨eL''⟩⟩ :
          ∃ L'' : Subgroup C, L''.Normal ∧ L'' ≤ L' ∧ Nonempty (L'' ≃* PSL2 K) := by
        by_cases h3 : 3 < Nat.card K
        · exact exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three L' hL'n K hK' h3 eP
        · have hK3 : Nat.card K = 3 := by
            have hp3 : 3 ≤ p := by
              have := hp.two_le
              rcases hpodd with ⟨k, hk⟩
              omega
            have : p ≤ p ^ fexp := Nat.le_self_pow (by omega) p
            omega
          let : Fintype K := Fintype.ofFinite K
          let eK : ZMod 3 ≃+* K :=
            ZMod.ringEquivOfPrime K Nat.prime_three (by rw [← Nat.card_eq_fintype_card, hK3])
          obtain ⟨L'', h1, h2, ⟨e3⟩⟩ := exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
            L' hL'n (eP.trans (pgl2RingEquiv eK).symm)
          exact ⟨L'', h1, h2, ⟨e3.trans (psl2RingEquiv eK)⟩⟩
      have : L''.Normal := hL''n
      have hcard1 : Nat.card L' = Nat.card K * (Nat.card K ^ 2 - 1) :=
        (Nat.card_congr eP.toEquiv).trans (pgl2_card_formula K)
      have hcard2 : Nat.card L'' = Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
        (Nat.card_congr eL''.toEquiv).trans (psl2_card_formula K hK')
      have heven : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
        (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd.mul_left _
      have hcard : Nat.card L' = 2 * Nat.card L'' := by
        rw [hcard1, hcard2, Nat.mul_div_cancel' heven]
      have hidx2 : (L''.subgroupOf L').index = 2 := by
        have h1 := (L''.subgroupOf L').card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL''L).toEquiv, hcard] at h1
        have hpos : 0 < Nat.card L'' := Nat.card_pos
        exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
      have hzL'' : z ∈ L'' := by
        set w0 : (D : Subgroup C) := eD.symm (DihedralGroup.r 1) with hw0
        have hw0z : w0 ^ 2 = ⟨z, hzD⟩ := by
          apply eD.injective
          rw [map_pow, hw0, MulEquiv.apply_symm_apply, dihedral_four_sq, hz']
        have h1 := Subgroup.sq_mem_of_index_two hidx2 ⟨(w0 : C), hDL w0.2⟩
        rw [Subgroup.mem_subgroupOf] at h1
        have h2 : (((⟨(w0 : C), hDL w0.2⟩ : ↥L') ^ 2 : ↥L') : C) = z := by
          rw [Subgroup.coe_pow]
          exact congrArg Subtype.val hw0z
        rwa [h2] at h1
      have ht : orderOf (eL'' ⟨z, hzL''⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
      obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K hKcard hpodd hf0 ht
      have hcC : Nat.card (Subgroup.centralizer ({eL'' ⟨z, hzL''⟩} : Set (PSL2 K))) =
          Nat.card ↥(L'' ⊓ Subgroup.centralizer ({z} : Set C)) := by
        rw [card_centralizer_map, card_centralizer_subtype]
      have hdvd8 : Nat.card ↥(L'' ⊓ Subgroup.centralizer ({z} : Set C)) ∣ 8 := by
        rw [← hcardD, ← hC]
        exact Subgroup.card_dvd_of_le inf_le_right
      have hnot8 : Nat.card ↥(L'' ⊓ Subgroup.centralizer ({z} : Set C)) ≠ 8 := by
        intro h8
        have heq : L'' ⊓ Subgroup.centralizer ({z} : Set C) = Subgroup.centralizer {z} :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hC, hcardD])
        have hfL'' : f ∈ L'' := by
          have : f ∈ Subgroup.centralizer ({z} : Set C) := hC ▸ hfD
          rw [← heq] at this
          exact this.1
        exact hnotPSL L'' ⟨eL''⟩ hzL'' hfL''
      have hq : Nat.card K = 3 ∨ Nat.card K = 5 := by
        have h4 : p ^ fexp % 4 = 1 ∨ p ^ fexp % 4 = 3 := by
          have := Nat.odd_iff.mp (hpodd.pow (n := fexp))
          omega
        have hq3 : 3 ≤ p ^ fexp := by
          have := hp.two_le
          have : p ≤ p ^ fexp := Nat.le_self_pow (by omega) p
          rcases hpodd with ⟨k, hk⟩
          omega
        rw [hKcard]
        rcases h4 with h4 | h4
        · have hc := (h1 h4).1
          rw [hcC] at hc
          rw [hc] at hdvd8 hnot8
          have : p ^ fexp - 1 ∣ 8 := hdvd8
          have hle : p ^ fexp - 1 ≤ 8 := Nat.le_of_dvd (by norm_num) this
          interval_cases hq : p ^ fexp - 1 <;> omega
        · have hc := (h3 h4).1
          rw [hcC] at hc
          rw [hc] at hdvd8 hnot8
          have : p ^ fexp + 1 ∣ 8 := hdvd8
          have hle : p ^ fexp + 1 ≤ 8 := Nat.le_of_dvd (by norm_num) this
          interval_cases hq : p ^ fexp + 1 <;> omega
      have hcardL'' : Nat.card L'' = 12 ∨ Nat.card L'' = 60 := by
        rw [hcard2]
        rcases hq with h | h <;> rw [h] <;> norm_num
      have hCL : ∀ c : C, (∀ l ∈ L'', c * l = l * c) → c = 1 := by
        set N := Subgroup.centralizer (L'' : Set C) with hN
        have hNn : N.Normal := ⟨fun n hn g => Subgroup.mem_centralizer_iff.mpr fun l hl => by
          have hl' : g⁻¹ * l * g ∈ L'' := by
            have := (inferInstance : L''.Normal).conj_mem l hl g⁻¹
            rwa [inv_inv] at this
          have := Subgroup.mem_centralizer_iff.mp hn _ hl'
          calc l * (g * n * g⁻¹) = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
            _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
            _ = g * n * g⁻¹ * l := by group⟩
        have hzN : z ∉ N := by
          intro hzN'
          have hle : L'' ≤ Subgroup.centralizer ({z} : Set C) := fun l hl =>
            Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp hzN' l hl)
          have := Subgroup.card_dvd_of_le hle
          rw [hC, hcardD] at this
          rcases hcardL'' with h | h <;> rw [h] at this <;> norm_num at this
        have hNodd : Nat.Coprime 2 (Nat.card N) := by
          by_contra hcop
          have h2 : 2 ∣ Nat.card N := (Nat.Prime.dvd_iff_not_coprime Nat.prime_two).mpr hcop
          obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
          have hup : IsPGroup 2 ↥(Subgroup.zpowers (u : C)) := IsPGroup.of_card (n := 1) (by
            rw [Nat.card_zpowers, Subgroup.orderOf_coe, hu, pow_one])
          obtain ⟨P, hP⟩ := hup.exists_le_sylow
          obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P D
          have hgu : g * (u : C) * g⁻¹ ∈ (D : Subgroup C) := by
            have h1 : (u : C) ∈ (P : Subgroup C) := hP (Subgroup.mem_zpowers _)
            rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
              ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv,
              show g⁻¹ * (g * (u : C) * g⁻¹) * g = u by group]
            exact h1
          have hguN : g * (u : C) * g⁻¹ ∈ N := hNn.conj_mem _ u.2 g
          set H : Subgroup (D : Subgroup C) := N.subgroupOf D with hH
          have hHn : H.Normal := ⟨fun n hn x => by
            rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
            exact hNn.conj_mem _ hn x⟩
          have hH1 : H ≠ ⊥ := by
            intro hbot
            have : (⟨g * (u : C) * g⁻¹, hgu⟩ : (D : Subgroup C)) ∈ H :=
              Subgroup.mem_subgroupOf.mpr hguN
            rw [hbot, Subgroup.mem_bot] at this
            have h1 : g * (u : C) * g⁻¹ = 1 := congrArg Subtype.val this
            have hu1 : (u : C) = 1 := by
              calc (u : C) = g⁻¹ * (g * (u : C) * g⁻¹) * g := by group
                _ = 1 := by rw [h1]; group
            have : u = 1 := Subtype.ext hu1
            rw [this, orderOf_one] at hu
            exact absurd hu (by norm_num)
          have : Group.IsNilpotent (D : Subgroup C) := D.isPGroup'.isNilpotent
          obtain ⟨⟨c, hcH, hcZ⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
            (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
          have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
          have hcz : c = ⟨z, hzD⟩ := by
            have hcc : ∀ b : DihedralGroup 4, eD c * b = b * eD c := fun b => by
              obtain ⟨y, rfl⟩ := eD.surjective b
              rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcZ y]
            rcases dihedral_four_center _ hcc with h | h
            · exact absurd (eD.injective (h.trans (map_one eD).symm)) hc1'
            · exact eD.injective (h.trans hz'.symm)
          apply hzN
          have := Subgroup.mem_subgroupOf.mp hcH
          rw [hcz] at this
          exact this
        have hNbot : N = ⊥ := by
          have hle : N ≤ pPrimeCore 2 C := le_sSup ⟨hNn, hNodd⟩
          rw [hO] at hle
          exact eq_bot_iff.mpr hle
        intro c hc
        have : c ∈ N := Subgroup.mem_centralizer_iff.mpr fun l hl => (hc l hl).symm
        rw [hNbot, Subgroup.mem_bot] at this
        exact this
      have h8C : 8 ∣ Nat.card C := by
        rw [← hcardD]
        exact Subgroup.card_subgroup_dvd_card _
      have hfull : ∀ {n : ℕ} (θ : C →* Equiv.Perm (Fin n)), Function.Injective θ →
          alternatingGroup (Fin n) ≤ θ.range → Nat.card (alternatingGroup (Fin n)) * 2 =
            Nat.card (Equiv.Perm (Fin n)) →
          Nat.Coprime (Nat.card (alternatingGroup (Fin n)) / 4) 2 →
          4 ∣ Nat.card (alternatingGroup (Fin n)) → θ.range = ⊤ := by
        intro n θ hθ hA hidx hodd h4
        have hcard : Nat.card θ.range = Nat.card C :=
          (Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv).symm
        obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hA
        have hdvd := Subgroup.card_subgroup_dvd_card θ.range
        rw [← hidx, hk] at hdvd
        have hpos : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
        have hk2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
        have hk1 : k ≠ 1 := by
          rintro rfl
          rw [mul_one] at hk
          rw [← hcard, hk] at h8C
          obtain ⟨m, hm⟩ := h4
          rw [hm] at h8C hodd
          rw [Nat.mul_div_cancel_left _ (by norm_num)] at hodd
          have : 2 ∣ m := by
            have h8 : 4 * 2 ∣ 4 * m := by rwa [show (8 : ℕ) = 4 * 2 by norm_num] at h8C
            exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h8
          exact absurd (Nat.Coprime.coprime_dvd_left this hodd) (by norm_num)
        have hk' : k = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h | h
          · exact absurd h hk1
          · exact h
        apply Subgroup.eq_top_of_card_eq
        rw [hk, hk', ← hidx]
      rcases hq with h3' | h5'
      ·
        left
        let : Fintype K := Fintype.ofFinite K
        obtain ⟨e3⟩ := nonempty_psl2_equiv_zmod (K := K) Nat.prime_three
          (by rw [← Nat.card_eq_fintype_card, h3'])
        let eA : L'' ≃* ↥(alternatingGroup (Fin 4)) :=
          (eL''.trans e3).trans psl2_three_equiv_alternatingGroup
        obtain ⟨θ, hθ, hθL⟩ := exists_embedding_of_alt eA alt_four_aut_conj
          (fun ρ hρ => eq_one_of_comm_alt_four ρ ⟨hρ _ aA4_mem, hρ _ bA4_mem⟩) hCL
        have hA : alternatingGroup (Fin 4) ≤ θ.range := fun σ hσ => by
          obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
          exact ⟨l, by rw [hθL, hl]⟩
        have hA12 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup]
          decide
        have hrange := hfull θ hθ hA (by rw [hA12, Nat.card_perm, Nat.card_fin]; decide)
          (by rw [hA12]; decide) (by rw [hA12]; decide)
        exact ⟨MulEquiv.ofBijective θ ⟨hθ, MonoidHom.range_eq_top.mp hrange⟩⟩
      ·
        right
        obtain ⟨⟨e5⟩, -⟩ := CFSG.LinearGroups.five_field_linear_two_alternating_five_model K h5'
        let eA : L'' ≃* ↥(alternatingGroup (Fin 5)) := eL''.trans e5
        obtain ⟨θ, hθ, hθL⟩ := exists_embedding_of_alt eA alt_five_aut_conj
          (fun ρ hρ => eq_one_of_comm_alt_five ρ ⟨hρ _ aA5_mem, hρ _ bA5_mem⟩) hCL
        have hA : alternatingGroup (Fin 5) ≤ θ.range := fun σ hσ => by
          obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
          exact ⟨l, by rw [hθL, hl]⟩
        have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup]
          decide
        have hrange := hfull θ hθ hA (by rw [hA60, Nat.card_perm, Nat.card_fin]; decide)
          (by rw [hA60]; decide) (by rw [hA60]; decide)
        exact ⟨MulEquiv.ofBijective θ ⟨hθ, MonoidHom.range_eq_top.mp hrange⟩⟩

end CFSG.Quasithin.HSType
