module

public import CFSG.Quasithin.Background.E6NineteenA
public import CFSG.Quasithin.Background.GoldschmidtTDE68A6Aut
public import CFSG.Quasithin.Background.GoldschmidtTDE68L2pPsl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique

theorem oddInvertFree_of_sylow {X : Type*} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (h : ∀ α β δ : MulAut X, α * α = 1 → α ≠ 1 → (∀ s ∈ S₀, α s = s) → β * β = 1 →
      (∀ s ∈ S₀, β s = s) → α * β = β * α → Odd (orderOf δ) → δ * α = α * δ →
      β⁻¹ * δ * β = δ⁻¹ → δ = 1) : OddInvertFree X := by
  intro S hS α β δ hα2 hα1 hαS hβ2 hβS hαβ hodd hδα hinv
  obtain ⟨g, -, hg⟩ := hS₀.exists_conj hS
  set c := MulAut.conj g with hc
  have hfix : ∀ φ : MulAut X, (∀ s ∈ S, φ s = s) → ∀ s ∈ S₀, (c⁻¹ * φ * c) s = s := by
    intro φ hφ s hs
    have hs' : c s ∈ S := by rw [hg]; exact ⟨s, hs, rfl⟩
    simp only [MulAut.mul_apply, hφ _ hs', MulAut.inv_apply_self]
  have key := h (c⁻¹ * α * c) (c⁻¹ * β * c) (c⁻¹ * δ * c)
    (by rw [show c⁻¹ * α * c * (c⁻¹ * α * c) = c⁻¹ * (α * α) * c by group, hα2]; group)
    (fun h1 => hα1 (by
      have := congrArg (fun φ => c * φ * c⁻¹) h1
      simpa [mul_assoc] using this))
    (hfix α hαS)
    (by rw [show c⁻¹ * β * c * (c⁻¹ * β * c) = c⁻¹ * (β * β) * c by group, hβ2]; group)
    (hfix β hβS)
    (by rw [show c⁻¹ * α * c * (c⁻¹ * β * c) = c⁻¹ * (α * β) * c by group, hαβ]; group)
    (by rwa [show c⁻¹ * δ * c = MulAut.conj c⁻¹ δ by simp,
      MulEquiv.orderOf_eq])
    (by rw [show c⁻¹ * δ * c * (c⁻¹ * α * c) = c⁻¹ * (δ * α) * c by group, hδα]; group)
    (by rw [show (c⁻¹ * β * c)⁻¹ * (c⁻¹ * δ * c) * (c⁻¹ * β * c) = c⁻¹ * (β⁻¹ * δ * β) * c by
      group, hinv]; group)
  have := congrArg (fun φ => c * φ * c⁻¹) key
  simpa [mul_assoc] using this

section A6

open CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.Unc25A6
  CFSG.Quasithin.E6.Alt.A6

theorem oddInv_check : (Core.autL.all fun ce => invCentD.all fun ca => invCentD.all fun cb =>
    !(Core.cmul ce ca == Core.cmul ca ce &&
      Core.cmul (Core.cmul (Core.cmul cb ce) cb) ce == Core.cid &&
      Core.cpow ce 45 == Core.cid) || ce == Core.cid) = true := by
  decide +kernel

@[expose] noncomputable def conjAutHom : ↥A6Models.autA6 →* MulAut X0 where
  toFun := DoubleA3.conjAut
  map_one' := Alt.A6.conjAut_one
  map_mul' := Alt.A6.conjAut_mul

theorem oddInvertFree_X0 : OddInvertFree X0 := by
  refine oddInvertFree_of_sylow Unc25A6.isSylowTwoOf_Dsub
    fun α β δ hα2 hα1 hαS hβ2 hβS _ hodd hδα hinv => ?_
  have hcomm : ∀ φ : MulAut X0, (∀ s ∈ Unc25A6.Dsub, φ s = s) → ∀ d ∈ Unc25A6.Dsub,
      φ * MulAut.conj d = MulAut.conj d * φ := by
    intro φ hφ d hd
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hφ d hd]
  have hαI : α ∈ Alt.InvSet Unc25A6.Dsub := ⟨hα1, hα2, hcomm α hαS⟩
  obtain ⟨a, rfl, ha⟩ := (Alt.A6.mem_invSet_iff α).1 hαI
  obtain ⟨e, rfl⟩ := DoubleA3.conjAut_surjective δ
  by_cases hβ1 : β = 1
  · exact eq_one_of_eq_one_or_eq (Or.inl hβ1) hodd hδα hinv
  have hβI : β ∈ Alt.InvSet Unc25A6.Dsub := ⟨hβ1, hβ2, hcomm β hβS⟩
  obtain ⟨b, rfl, hb⟩ := (Alt.A6.mem_invSet_iff β).1 hβI
  have hinj : Function.Injective conjAutHom := DoubleA3.conjAut_injective
  have hea : e * a = a * e := hinj (by
    rw [map_mul, map_mul]
    exact hδα)
  have hbb : b * b = 1 := hinj (by
    rw [map_mul, map_one]
    exact hβ2)
  have hbeb : b * e * b * e = 1 := by
    have h1 : conjAutHom (b⁻¹ * e * b) = conjAutHom e⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hinv
    have h2 := hinj h1
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    rw [hbinv] at h2
    rw [h2, inv_mul_cancel]
  have he45 : e ^ 45 = 1 := by
    have hodd' : Odd (orderOf e) := by
      rw [← orderOf_injective conjAutHom hinj e]
      exact hodd
    have hd : orderOf e ∣ 32 * 45 := by
      have := orderOf_dvd_natCard e
      rwa [A6Facts.card_autA6] at this
    have h2 : Nat.Coprime 2 (orderOf e) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Odd.not_two_dvd_nat hodd')
    have hcop : Nat.Coprime (orderOf e) 32 := (h2.pow_left 5).symm
    exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hd)
  have hce : code (e : P10) ∈ Core.autL := code_mem_autL e.2
  have hchk := oddInv_check
  rw [List.all_eq_true] at hchk
  have h3 := hchk _ hce
  rw [List.all_eq_true] at h3
  have h4 := h3 _ ha
  rw [List.all_eq_true] at h4
  have h5 := h4 _ hb
  have c1 : Core.cmul (code (e : P10)) (code (a : P10)) =
      Core.cmul (code (a : P10)) (code (e : P10)) := by
    rw [← code_mul, ← code_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hea]
  have c2 : Core.cmul (Core.cmul (Core.cmul (code (b : P10)) (code (e : P10))) (code (b : P10)))
      (code (e : P10)) = Core.cid := by
    rw [← code_mul, ← code_mul, ← code_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, hbeb, Subgroup.coe_one, code_one]
  have c3 : Core.cpow (code (e : P10)) 45 = Core.cid := by
    rw [← code_pow, ← Subgroup.coe_pow, he45, Subgroup.coe_one, code_one]
  simp only [c1, c2, c3, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    beq_iff_eq] at h5
  have he1 : e = 1 := Subtype.ext (code_injective (by rw [h5, Subgroup.coe_one, code_one]))
  rw [he1]
  exact Alt.A6.conjAut_one

theorem oddInvertFree_alt6 : OddInvertFree (alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  exact OddInvertFree.of_mulEquiv ψ.symm oddInvertFree_X0

end A6

section L33

open CFSG.QuasithinUnique.Unc25K1 CFSG.QuasithinUnique.Unc25L33 CFSG.Assembly.LowTwoRank

theorem center_eq_bot_of_simple_not_prime {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnp : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative X :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hnp (Group.is_simple_iff_prime_card.mp hs)

theorem oddInvertFree_psl33 :
    ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSL 3 3 1 → OddInvertFree X := by
  intro X _ _ hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := psl33_equiv hmodel
  let e : X ≃* S3 := e₀.trans psl33EquivS3
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 3 1 hmodel).2
  have hZ : Subgroup.center X = ⊥ := by
    refine center_eq_bot_of_simple_not_prime hs ?_
    rw [Nat.card_congr e.toEquiv, card_S3]
    norm_num
  have hfix := (l33_facts X hmodel).2
  refine oddInvertFree_of_cyclic hZ (Inn.InvolFixInner.of_forall fun Q hQ β hβ =>
    L2p.sylowCentralizingAutInner_of_fixPointwiseInner hfix Q hQ β hβ) fun S hS => ?_
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map e.toMonoidHom, ?_⟩
    have h1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have h2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective S]
    have := hS.2.2
    rwa [h2] at this
  obtain ⟨g, -, hg⟩ := isSylowTwoOf_P0.exists_conj hS'
  obtain ⟨ψ⟩ := shape_P0
  let f : ↥S ≃* CFSG.Open.SemidihedralGroup 4 :=
    ((S.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hg)).trans
      ((P0.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
        ψ)
  have hc : Nat.card ↥(Subgroup.center ↥S) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr f).toEquiv, CFSG.Semidihedral.center_card 4 le_rfl]
  exact isCyclic_of_prime_card hc

end L33

section Overgroups

open CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.EscapingLocal

theorem oddInvertFree_of_overgroups {X : Type} [Group X] [Finite X] (hO : Overgroups X)
    (hT : SylowAutTrivial X) : OddInvertFree X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS α β δ _ hα1 hαS hβ2 hβS _ hodd hδα hinv
  let C : Subgroup X :=
    { carrier := {x | α x = x}
      mul_mem' := fun {a b} ha hb => by
        change α (a * b) = a * b
        rw [map_mul, show α a = a from ha, show α b = b from hb]
      one_mem' := map_one α
      inv_mem' := fun {a} ha => by
        change α a⁻¹ = a⁻¹
        rw [map_inv, show α a = a from ha] }
  have hmemC : ∀ x, x ∈ C ↔ α x = x := fun x => Iff.rfl
  have hSC : S ≤ C := fun s hs => (hmemC s).2 (hαS s hs)
  have hCne : C ≠ ⊤ := by
    intro h
    apply hα1
    ext x
    exact (hmemC x).1 (h ▸ Subgroup.mem_top x)
  have hchar : CFSG.IsCharacteristicP 2 ↥C :=
    EscapingLocal.isCharacteristicP_of_charTwo (hO S C hS hSC hCne)
  set N : Subgroup X := (CFSG.pCore 2 ↥C).map C.subtype with hNdef
  have hNC : N ≤ C := Subgroup.map_subtype_le _
  have hN2 : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).map C.subtype
  have hCN : C ≤ Subgroup.normalizer (N : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨c, hc⟩ * m * ⟨c, hc⟩⁻¹, CFSG.pCore_normal.conj_mem m hm ⟨c, hc⟩, rfl⟩
    · rintro ⟨m, hm, hmn⟩
      have hnC : n ∈ C := by
        have h1 : c⁻¹ * (c * n * c⁻¹) * c = n := by group
        rw [← h1, ← hmn]
        exact C.mul_mem (C.mul_mem (C.inv_mem hc) m.2) hc
      refine ⟨⟨n, hnC⟩, ?_, rfl⟩
      have h2 := CFSG.pCore_normal.conj_mem m hm ⟨c, hc⟩⁻¹
      have h3 : (⟨c, hc⟩⁻¹ * m * (⟨c, hc⟩⁻¹)⁻¹ : ↥C) = ⟨n, hnC⟩ := Subtype.ext (by
        have hm' : (m : X) = c * n * c⁻¹ := hmn
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hm']
        group)
      rwa [h3] at h2
  have hSylC : IsSylowTwoOf S C := by
    refine ⟨hSC, hS.isPGroup, fun h2 => hS.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_index hSC
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3, ← h1]
    exact Dvd.dvd.mul_right h2 _
  have hNS : N ≤ S := hSylC.le_of_normalizes hNC hCN hN2
  have hδC : ∀ x ∈ C, δ x ∈ C := fun x hx => by
    rw [hmemC] at hx ⊢
    rw [← MulAut.mul_apply, ← hδα, MulAut.mul_apply, hx]
  have hδC' : ∀ x ∈ C, δ⁻¹ x ∈ C := fun x hx => by
    rw [hmemC] at hx ⊢
    have h1 : α * δ⁻¹ = δ⁻¹ * α := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hδα, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← MulAut.mul_apply, h1, MulAut.mul_apply, hx]
  let δC : MulAut ↥C :=
    { toFun := fun c => ⟨δ (c : X), hδC c c.2⟩
      invFun := fun c => ⟨δ⁻¹ (c : X), hδC' c c.2⟩
      left_inv := fun c => Subtype.ext (MulAut.inv_apply_self _ δ (c : X))
      right_inv := fun c => Subtype.ext (MulAut.apply_inv_self _ δ (c : X))
      map_mul' := fun a b => Subtype.ext (map_mul δ (a : X) (b : X)) }
  have hδN : ∀ n ∈ N, δ n ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : (CFSG.pCore 2 ↥C).comap δC.toMonoidHom = CFSG.pCore 2 ↥C :=
      (CFSG.pCore_characteristic (p := 2) (G := ↥C)).fixed δC
    have h2 : m ∈ (CFSG.pCore 2 ↥C).comap δC.toMonoidHom := by rw [h1]; exact hm
    exact ⟨δC m, h2, rfl⟩
  have hδN' : ∀ n ∈ N, δ⁻¹ n ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : (CFSG.pCore 2 ↥C).comap δC.symm.toMonoidHom = CFSG.pCore 2 ↥C :=
      (CFSG.pCore_characteristic (p := 2) (G := ↥C)).fixed δC.symm
    have h2 : m ∈ (CFSG.pCore 2 ↥C).comap δC.symm.toMonoidHom := by rw [h1]; exact hm
    exact ⟨δC.symm m, h2, rfl⟩
  have hδsq : ∀ n ∈ N, δ (δ n) = n := by
    intro n hn
    have hβn : ∀ x ∈ N, β x = x := fun x hx => hβS x (hNS hx)
    have h1 : δ * β = β * δ⁻¹ := by
      rw [← hinv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have h2 := congrArg (fun φ : MulAut X => φ n) h1
    simp only [MulAut.mul_apply, hβn n hn, hβn _ (hδN' n hn)] at h2
    calc δ (δ n) = δ (δ⁻¹ n) := by rw [h2]
      _ = n := MulAut.apply_inv_self _ δ n
  obtain ⟨k, hk⟩ := hodd
  have hδm : δ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one δ
  have hδfixN : ∀ n ∈ N, δ n = n := by
    intro n hn
    have hpow : ∀ j : ℕ, (δ ^ (2 * j)) n = n := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, MulAut.mul_apply, pow_two,
          MulAut.mul_apply, hδsq n hn, ih]
    have h1 : δ = δ ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hδm, one_mul]
    rw [h1]
    exact hpow (k + 1)
  have hδfixC : ∀ h ∈ C, δ h = h := by
    intro h hh
    set d := h⁻¹ * δ h with hd
    have hdC : d ∈ C := C.mul_mem (C.inv_mem hh) (hδC h hh)
    have hdcen : d ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hhx : h * x * h⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hCN hh) x).1 hx
      have h1 := hδfixN _ hhx
      rw [map_mul, map_mul, map_inv, hδfixN x hx] at h1
      calc x * d = h⁻¹ * (h * x * h⁻¹) * δ h := by rw [hd]; group
        _ = h⁻¹ * (δ h * x * (δ h)⁻¹) * δ h := by rw [h1]
        _ = d * x := by rw [hd]; group
    have hdN : d ∈ N := by
      have h1 : (⟨d, hdC⟩ : ↥C) ∈ CFSG.pCore 2 ↥C := by
        apply hchar
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hdcen _ ⟨n, hn, rfl⟩)
      exact ⟨⟨d, hdC⟩, h1, rfl⟩
    have hiter : ∀ j : ℕ, (δ ^ j) h = h * d ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hδfixN d hdN, pow_succ',
          ← mul_assoc, hd, mul_inv_cancel_left]
    have h1 := hiter (2 * k + 1)
    rw [hδm, MulAut.one_apply] at h1
    have hd1 : d ^ (2 * k + 1) = 1 := by
      have := congrArg (fun y => h⁻¹ * y) h1
      simpa using this.symm
    obtain ⟨j, hj⟩ := hN2 ⟨d, hdN⟩
    have hj' : d ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h2c : Nat.Coprime 2 (2 * k + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Odd.not_two_dvd_nat ⟨k, rfl⟩)
    have hcop : Nat.Coprime (2 * k + 1) (2 ^ j) := (h2c.pow_left j).symm
    have hdo : orderOf d = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hd1) (orderOf_dvd_of_pow_eq_one hj')
    have hd1' : d = 1 := orderOf_eq_one_iff.1 hdo
    calc δ h = h * d := by rw [hd]; group
      _ = h := by rw [hd1', mul_one]
  have hidx : ¬ 2 ∣ S.index := by
    have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    have := hS.2.2
    rwa [h1] at this
  exact hT (hS.isPGroup.toSylow hidx) δ ⟨k, hk⟩ fun t ht => hδfixC t (hSC ht)

theorem oddInvertFree_psu33 :
    ∀ (X : Type) [Group X] [Finite X],
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 → OddInvertFree X := by
  intro X _ _ h
  have hL : CFSG.Blueprint.LieModel X .PSU 3 3 1 := Or.inl ⟨by decide, h⟩
  have hs : IsSimpleGroup X := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 h).2
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  have hc : Nat.card X = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      (CFSG.GH74.KGroups.U33.QP_valid).2]
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_simple_not_prime hs (by rw [hc]; norm_num)
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    have : Nontrivial X := hs.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : X)
    have haZ : a ∉ Subgroup.center X := by rw [hZ, Subgroup.mem_bot]; exact ha
    rw [Subgroup.mem_center_iff] at haZ
    push Not at haZ
    obtain ⟨b, hb⟩ := haZ
    exact ⟨b, a, hb⟩
  exact oddInvertFree_of_overgroups (Over.CertU33.overgroups_of_lieModel hL)
    (Bridge.sylowAutTrivial_psu_three_three hs hnc h)

end Overgroups

end E6

end CFSG.Quasithin
