module

public import CFSG.Timmesfeld.Bridge.RootStructR2Defs2
public import CFSG.Timmesfeld.Bridge.RootStructR2Fix
public import CFSG.Timmesfeld.Bridge.RootStructWTIRadical

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootMany

theorem card_dvd_of_free {P β : Type*} [Group P] [MulAction P β] [Finite P] [Finite β]
    (hfree : ∀ (g : P) (b : β), g • b = b → g = 1) : Nat.card P ∣ Nat.card β := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    MulAction.card_eq_sum_card_group_div_card_stabilizer P β]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : Fintype.card (MulAction.stabilizer P ω.out) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun g => Subtype.ext (hfree g.1 _ g.2)⟩
  rw [hstab, Nat.div_one]

variable {G : Type} [Group G] {D : Set G}

@[expose] def IsTransv (D : Set G) (a d g : G) : Prop :=
  (∀ α ∈ rootGroup D a, Commute g α) ∧
    ∀ t ∈ rootGroup D a ⊔ rootGroup D d, g * t * g⁻¹ * t⁻¹ ∈ rootGroup D a

theorem IsTransv.one (a d : G) : IsTransv D a d 1 :=
  ⟨fun α _ => Commute.one_left α, fun t _ => by simp⟩

theorem IsTransv.mul {a d g g' : G} (hg : IsTransv D a d g) (hg' : IsTransv D a d g') :
    IsTransv D a d (g * g') := by
  refine ⟨fun α hα => (hg.1 α hα).mul_left (hg'.1 α hα), fun t ht => ?_⟩
  have h1 := hg'.2 t ht
  have h2 := hg.2 t ht
  have hc : Commute g (g' * t * g'⁻¹ * t⁻¹) := hg.1 _ h1
  have e : g * g' * t * (g * g')⁻¹ * t⁻¹ =
      (g * (g' * t * g'⁻¹ * t⁻¹) * g⁻¹) * (g * t * g⁻¹ * t⁻¹) := by group
  rw [e, hc.eq, mul_inv_cancel_right]
  exact Subgroup.mul_mem _ h1 h2

theorem IsTransv.pow {a d g : G} (hg : IsTransv D a d g) (k : ℕ) : IsTransv D a d (g ^ k) := by
  induction k with
  | zero => simpa using IsTransv.one (D := D) a d
  | succ k ih => rw [pow_succ]; exact ih.mul hg

theorem IsTransv.inv [Finite G] {a d g : G} (hg : IsTransv D a d g) : IsTransv D a d g⁻¹ := by
  have h := hg.pow (orderOf g - 1)
  have e : g ^ (orderOf g - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos g),
      pow_orderOf_eq_one]
  rwa [e] at h

@[expose] def transvSubgroup [Finite G] (D : Set G) (a d : G) : Subgroup G where
  carrier := {g | IsTransv D a d g}
  mul_mem' := IsTransv.mul
  one_mem' := IsTransv.one a d
  inv_mem' := IsTransv.inv

section TransvHom

variable [Finite G] {a d : G} (ha : a ∈ D) (hd : d ∈ D) {H : Subgroup G}
  (hH : H ≤ transvSubgroup D a d)
include ha hd hH

@[expose] def transvHom : H →* rootGroup D a where
  toFun h := ⟨(h : G) * d * (h : G)⁻¹ * d⁻¹, (hH h.2).2 d (right_mem_line hd)⟩
  map_one' := by ext; simp
  map_mul' h h' := by
    apply Subtype.ext
    have hβ' := (hH h'.2).2 d (right_mem_line hd)
    have hβ := (hH h.2).2 d (right_mem_line hd)
    have hc : Commute (h : G) ((h' : G) * d * (h' : G)⁻¹ * d⁻¹) := (hH h.2).1 _ hβ'
    have hab : Commute ((h : G) * d * (h : G)⁻¹ * d⁻¹) ((h' : G) * d * (h' : G)⁻¹ * d⁻¹) :=
      commute_of_mem_rootGroup ha hβ hβ'
    simp only [Subgroup.coe_mul]
    calc (h : G) * h' * d * ((h : G) * h')⁻¹ * d⁻¹
        = (h : G) * ((h' : G) * d * (h' : G)⁻¹ * d⁻¹) * (h : G)⁻¹ *
            ((h : G) * d * (h : G)⁻¹ * d⁻¹) := by group
      _ = ((h' : G) * d * (h' : G)⁻¹ * d⁻¹) * ((h : G) * d * (h : G)⁻¹ * d⁻¹) := by
          rw [hc.eq, mul_inv_cancel_right]
      _ = ((h : G) * d * (h : G)⁻¹ * d⁻¹) * ((h' : G) * d * (h' : G)⁻¹ * d⁻¹) :=
          hab.symm.eq

theorem transvHom_apply (h : H) :
    (transvHom ha hd hH h : G) = (h : G) * d * (h : G)⁻¹ * d⁻¹ := rfl

theorem ker_transvHom : (transvHom ha hd hH).ker = (Subgroup.centralizer {d}).subgroupOf H := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    rw [transvHom_apply, OneMemClass.coe_one] at h2
    calc (h : G) * d = (h : G) * d * (h : G)⁻¹ * d⁻¹ * (d * h) := by group
      _ = d * (h : G) := by rw [h2, one_mul]
  · intro h1
    apply Subtype.ext
    rw [transvHom_apply, OneMemClass.coe_one, h1]
    group

theorem card_eq_mul_card_range :
    Nat.card H = Nat.card ↥(H ⊓ Subgroup.centralizer {d}) *
      Nat.card (transvHom ha hd hH).range := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (transvHom ha hd hH).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv] at hcard
  have hker : Nat.card (transvHom ha hd hH).ker = Nat.card ↥(H ⊓ Subgroup.centralizer {d}) := by
    rw [ker_transvHom, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  rw [hcard, hker, mul_comm]

theorem card_le_mul_card_inf_of_le :
    Nat.card H ≤ Nat.card (rootGroup D a) * Nat.card ↥(H ⊓ Subgroup.centralizer {d}) := by
  rw [card_eq_mul_card_range ha hd hH, mul_comm]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)

theorem card_mul_card_inf_le {B : Subgroup G} (hBH : B ≤ H)
    (hB : ∀ b ∈ B, Commute b d → b = 1) :
    Nat.card B * Nat.card ↥(H ⊓ Subgroup.centralizer {d}) ≤ Nat.card H := by
  rw [card_eq_mul_card_range ha hd hH, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  refine Nat.card_le_card_of_injective
    (fun b : B => (⟨transvHom ha hd hH ⟨b, hBH b.2⟩, ⟨_, rfl⟩⟩ : (transvHom ha hd hH).range))
    fun b b' hbb' => ?_
  have h1 := congrArg (fun w : (transvHom ha hd hH).range => (w : G)) hbb'
  simp only [transvHom_apply] at h1
  have hc : Commute ((b' : G)⁻¹ * b) d := by
    show (b' : G)⁻¹ * b * d = d * ((b' : G)⁻¹ * b)
    calc (b' : G)⁻¹ * b * d = (b' : G)⁻¹ * ((b : G) * d * (b : G)⁻¹ * d⁻¹) * d * b := by group
      _ = (b' : G)⁻¹ * ((b' : G) * d * (b' : G)⁻¹ * d⁻¹) * d * b := by rw [h1]
      _ = d * ((b' : G)⁻¹ * b) := by group
  have := hB _ (B.mul_mem (B.inv_mem b'.2) b.2) hc
  apply Subtype.ext
  rw [inv_mul_eq_one] at this
  exact this.symm

end TransvHom

theorem lineSetting_of_counter (C : ThinGateCounter G D) : LineSetting G D := by
  obtain ⟨b, hb, c₁, hc₁, c₂, -, c₃, -, hc, -⟩ := C.three
  obtain ⟨hbc, hbcD, hcT⟩ := hc c₁ (by simp)
  exact ⟨C.hyp, C.closure, C.special, C.conn,
    ⟨b, hb, c₁, hc₁, hbc, hbcD, hcT, C.allTI b hb c₁ hc₁ hbc hbcD hcT⟩⟩

section Line

variable [Finite G] (C : ThinGateCounter G D) {a d : G} (ha : a ∈ D) (hd : d ∈ D)
  (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
include C ha hd had hadD hdT

omit [Finite G] had hadD in
theorem not_mem_rootGroup : d ∉ rootGroup D a := by
  intro h
  rcases (mem_rootGroup_iff_of_rootClosure C.hyp.root C.closure ha).1 h with h1 | h1
  · exact C.hyp.root.ne_one hd h1
  · exact hdT h1

omit hadD hdT in
theorem nCore_le_transv : nCore D a ≤ transvSubgroup D a d := by
  have hLS := lineSetting_of_counter C
  intro g hg
  refine ⟨fun α hα => commute_of_mem_nCore_of_mem_rootGroup hg hα, fun t ht => ?_⟩
  exact nCoreCommutatorInRoot_of_hyp C.hyp C.closure a ha g hg t
    (hLS.sup_rootGroup_le_nCore ha hd had ht)

theorem lineRadical_le_transv :
    lineRadical D a (rootGroup D a ⊔ rootGroup D d) ≤ transvSubgroup D a d := by
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  rw [hLS.lineRadical_eq ha hT hd (right_mem_line hd) (not_mem_rootGroup C ha hd hdT)]
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · have hgT := (Subgroup.mem_inf.1 hg).2
    refine ⟨fun α hα => ?_, fun t ht => ?_⟩
    · exact ((Subgroup.mem_centralizer_iff.1 hgT) α (Subgroup.mem_sup_left hα)).symm
    · rw [((Subgroup.mem_centralizer_iff.1 hgT) t ht).symm, mul_inv_cancel_right, mul_inv_cancel]
      exact (rootGroup D a).one_mem
  · exact nCore_le_transv C ha hd had hg

theorem isPGroup_lineRadical :
    IsPGroup 2 (lineRadical D a (rootGroup D a ⊔ rootGroup D d)) := by
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  rw [hLS.lineRadical_eq ha hT hd (right_mem_line hd) (not_mem_rootGroup C ha hd hdT)]
  refine IsPGroup.to_sup_of_normal_right' ((isPGroup_nCore D d).to_le inf_le_left)
    (isPGroup_nCore D a) fun g hg => ?_
  have hga : Commute g a :=
    ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2) a (left_mem_line ha)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conj_mem_nCore_conj C.hyp.isClass hx g
    rwa [hga.eq, mul_inv_cancel_right] at this
  · intro hx
    have := conj_mem_nCore_conj C.hyp.isClass hx g⁻¹
    have e : g⁻¹ * a * g⁻¹⁻¹ = a := by
      calc g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * (a * g) := by group
        _ = g⁻¹ * (g * a) := by rw [← hga.eq]
        _ = a := by group
    rw [e] at this
    simpa [mul_assoc] using this

theorem commute_of_mem_lineRadical_inf {g : G}
    (hg : g ∈ lineRadical D a (rootGroup D a ⊔ rootGroup D d) ⊓ Subgroup.centralizer {d})
    {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute g t := by
  have hD := C.hyp.root
  have hgT : IsTransv D a d g :=
    lineRadical_le_transv C ha hd had hadD hdT (Subgroup.mem_inf.1 hg).1
  have hgd : Commute g d := (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2)
  refine commute_of_mul_inv_mem C.hyp C.closure C.special ha hd had hadD hdT (p := a) (q := d)
    (left_mem_line ha) (hD.ne_one ha) (right_mem_line hd) (hD.ne_one hd) hdT hgT.1 hgT.2
    (fun s hs => ?_) ht
  have h1 : (rootGroup D d).map (MulAut.conj g).toMonoidHom = rootGroup D d := by
    rw [← rootGroup_conj C.hyp.isClass, hgd.eq, mul_inv_cancel_right]
  rw [← h1]
  exact ⟨s, hs, rfl⟩

theorem le_card_lineRadical {q n : ℕ} (hcard : (rootLines D a).ncard = q ^ n + 1) :
    q ^ n * Nat.card (nCore D a) ≤
      Nat.card (lineRadical D a (rootGroup D a ⊔ rootGroup D d)) := by
  classical
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  set S := lineRadical D a (rootGroup D a ⊔ rootGroup D d) with hS
  have hSN : S ≤ Subgroup.normalizer (rootGroup D a : Set G) :=
    (LineSetting.lineRadical_le_centralizer ha hT).trans
      (centralizer_le_normalizer_rootGroup C.hyp.isClass a)
  let _ : MulAction S (rootLines D a) :=
    MulAction.compHom _ ((hLS.lineAction ha).comp (Subgroup.inclusion hSN))
  have hsmul : ∀ (s : S) (L : rootLines D a),
      ((s • L : rootLines D a) : Subgroup G) = L.1.map (MulAut.conj (s : G)).toMonoidHom :=
    fun s L => hLS.lineAction_apply ha _ L
  obtain ⟨L₁, hL₁, hL₁T⟩ := hLS.exists_ne_mem_rootLines ha hT
  have horbit : ({⟨_, hT⟩}ᶜ : Set (rootLines D a)) ⊆
      MulAction.orbit S (⟨L₁, hL₁⟩ : rootLines D a) := by
    intro L hL
    have hLT : (L : Subgroup G) ≠ rootGroup D a ⊔ rootGroup D d := fun h =>
      hL (Subtype.ext h)
    obtain ⟨x, hx, hxL⟩ := hLS.exists_mem_lineRadical_map_conj_eq ha hT hL₁ L.2 hL₁T hLT
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [hsmul]; exact hxL)⟩
  have hstab : (nCore D a).subgroupOf S ≤ MulAction.stabilizer S (⟨L₁, hL₁⟩ : rootLines D a) := by
    intro m hm
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [hsmul]
    exact hLS.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hm) hL₁
  have hMS : nCore D a ≤ S := nCore_le_lineRadical a _
  have h1 : Nat.card (nCore D a) ≤
      Nat.card (MulAction.stabilizer S (⟨L₁, hL₁⟩ : rootLines D a)) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMS).toEquiv]
    exact Subgroup.card_le_of_le hstab
  have h2 : q ^ n ≤ (MulAction.orbit S (⟨L₁, hL₁⟩ : rootLines D a)).ncard := by
    have hc : ({⟨_, hT⟩}ᶜ : Set (rootLines D a)).ncard = q ^ n := by
      rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_coe_set_eq, hcard]
      omega
    rw [← hc]
    exact Set.ncard_le_ncard horbit
  calc q ^ n * Nat.card (nCore D a)
      ≤ (MulAction.orbit S (⟨L₁, hL₁⟩ : rootLines D a)).ncard *
          Nat.card (MulAction.stabilizer S (⟨L₁, hL₁⟩ : rootLines D a)) := Nat.mul_le_mul h2 h1
    _ = Nat.card S := by
      rw [mul_comm, ← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem card_le_mul_card_inf :
    Nat.card (lineRadical D a (rootGroup D a ⊔ rootGroup D d)) ≤
      Nat.card (rootGroup D a) *
        Nat.card ↥(lineRadical D a (rootGroup D a ⊔ rootGroup D d) ⊓
          Subgroup.centralizer {d}) :=
  card_le_mul_card_inf_of_le ha hd (lineRadical_le_transv C ha hd had hadD hdT)

end Line

section Points

variable (C : ThinGateCounter G D) {a : G}
include C

theorem map_conj_mem_oneOmega {g : G} (hga : Commute g a) {B : Subgroup G}
    (hB : B ∈ oneOmega D a) : B.map (MulAut.conj g).toMonoidHom ∈ oneOmega D a := by
  have hclass := C.hyp.isClass
  obtain ⟨x, hx, rfl, hax, hodd, e, he, hae, haeD, h4⟩ := hB
  have hga' : g * a * g⁻¹ = a := by rw [hga.eq, mul_inv_cancel_right]
  refine ⟨g * x * g⁻¹, conj_mem_of_isClass hclass g hx, (rootGroup_conj hclass g x).symm,
    fun h => hax ?_, ?_, g * e * g⁻¹, conj_mem_of_isClass hclass g he, ?_, ?_, ?_⟩
  · rw [← hga'] at h
    exact (Commute.conj_iff g).1 h
  · have e1 : a * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by
      calc a * (g * x * g⁻¹) = g * a * g⁻¹ * (g * x * g⁻¹) := by rw [hga']
        _ = g * (a * x) * g⁻¹ := by group
    rw [e1, orderOf_conj_eq]
    exact hodd
  · rw [← hga']
    exact (Commute.conj_iff g).2 hae
  · have e1 : a * (g * e * g⁻¹) = g * (a * e) * g⁻¹ := by
      calc a * (g * e * g⁻¹) = g * a * g⁻¹ * (g * e * g⁻¹) := by rw [hga']
        _ = g * (a * e) * g⁻¹ := by group
    rw [e1]
    exact conj_mem_of_isClass hclass g haeD
  · rw [show g * x * g⁻¹ * (g * e * g⁻¹) = g * (x * e) * g⁻¹ by group, orderOf_conj_eq]
    exact h4

theorem map_conj_mem_gatedPoints {g : G} (hga : Commute g a) {T : Subgroup G}
    (hgT : ∀ t ∈ T, Commute g t) {B : Subgroup G} (hB : B ∈ gatedPoints D a T) :
    B.map (MulAut.conj g).toMonoidHom ∈ gatedPoints D a T := by
  have hclass := C.hyp.isClass
  obtain ⟨hBΩ, x, hx, rfl, p, hp, hpT, h4⟩ := hB
  refine ⟨map_conj_mem_oneOmega C hga hBΩ, g * x * g⁻¹, conj_mem_of_isClass hclass g hx,
    (rootGroup_conj hclass g x).symm, p, hp, hpT, ?_⟩
  have hgp : g * p * g⁻¹ = p := by rw [(hgT p hpT).eq, mul_inv_cancel_right]
  rw [show g * x * g⁻¹ * p = g * (x * p) * g⁻¹ by
    conv_lhs => rw [← hgp]
    group, orderOf_conj_eq]
  exact h4

end Points

theorem false_of_card_nCore (C : ThinGateCounter G D) {q n : ℕ} (K : ThinGateCount G D q n 2)
    (hn : 1 ≤ n) {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (hM : q ^ (n + 4) ≤ Nat.card (nCore D a)) : False := by
  classical
  have := C.hyp.finite
  have hD := C.hyp.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  have hq : Nat.card (rootGroup D a) = q := K.card_rootGroup a ha
  have hA2 : IsPGroup 2 (rootGroup D a) :=
    OddLocal.isPGroup_two_of_mul_self fun _ hg => mul_self_eq_one_of_mem_rootGroup hD ha hg
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hA2
  rw [hq] at hr
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0, pow_zero, ← hq] at hr
      have hbot := Subgroup.eq_bot_of_card_eq _ hr
      have haA : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
      rw [hbot, Subgroup.mem_bot] at haA
      exact hD.ne_one ha haA
    · exact h0
  have hqpos : 0 < q := by rw [hr]; positivity
  set P := lineRadical D a (rootGroup D a ⊔ rootGroup D d) ⊓ Subgroup.centralizer {d} with hP
  have h1 := le_card_lineRadical C ha hd had hadD hdT (K.ncard_rootLines a ha)
  have h2 := card_le_mul_card_inf C ha hd had hadD hdT
  rw [hq] at h2
  have hPcard : q ^ (2 * n + 3) ≤ Nat.card P := by
    have h3 : q * q ^ (2 * n + 3) ≤ q * Nat.card P := by
      calc q * q ^ (2 * n + 3) = q ^ n * q ^ (n + 4) := by ring
        _ ≤ q ^ n * Nat.card (nCore D a) := Nat.mul_le_mul_left _ hM
        _ ≤ _ := h1.trans h2
    exact Nat.le_of_mul_le_mul_left h3 hqpos
  have hP2 : IsPGroup 2 P := (isPGroup_lineRadical C ha hd had hadD hdT).to_le inf_le_left
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP2
  have hPT : ∀ g ∈ P, ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute g t := fun g hg t ht =>
    commute_of_mem_lineRadical_inf C ha hd had hadD hdT hg ht
  have hPa : ∀ g ∈ P, Commute g a := fun g hg => hPT g hg a (left_mem_line ha)
  set Ω : Set (Subgroup G) := oneOmega D a \ gatedPoints D a (rootGroup D a ⊔ rootGroup D d)
    with hΩ
  have hmapΩ : ∀ g ∈ P, ∀ B ∈ Ω, B.map (MulAut.conj g).toMonoidHom ∈ Ω := by
    intro g hg B hB
    refine ⟨map_conj_mem_oneOmega C (hPa g hg) hB.1, fun hgB => hB.2 ?_⟩
    have h := map_conj_mem_gatedPoints C (hPa g⁻¹ (P.inv_mem hg)) (hPT g⁻¹ (P.inv_mem hg)) hgB
    rwa [map_conj_inv_map_conj_eq] at h
  let _ : MulAction P Ω :=
    { smul := fun g B => ⟨B.1.map (MulAut.conj (g : G)).toMonoidHom, hmapΩ g g.2 B B.2⟩
      one_smul := fun B => Subtype.ext (RankOne.map_conj_one B.1)
      mul_smul := fun g g' B => Subtype.ext (RankOne.map_conj_mul B.1 g g') }
  obtain ⟨g, B, hgB, hg1⟩ : ∃ g : P, ∃ B : Ω, g • B = B ∧ g ≠ 1 := by
    by_contra hfree
    push Not at hfree
    have hdvd := card_dvd_of_free (P := P) (β := Ω) fun g B h => hfree g B h
    rw [Nat.card_coe_set_eq, hj] at hdvd
    have hsub : gatedPoints D a (rootGroup D a ⊔ rootGroup D d) ⊆ oneOmega D a := fun B hB => hB.1
    have hΩcard : 2 * Ω.ncard = (q ^ n - 1) * q ^ (2 * n + 3) := by
      rw [hΩ, Set.ncard_sdiff hsub, K.ncard_gatedPoints a ha _ hT]
      have hK := K.ncard_oneOmega a ha
      have hq1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hqpos
      generalize q ^ (2 * n + 3) = X at hK ⊢
      generalize q ^ n = Y at hK hq1 ⊢
      generalize (oneOmega D a).ncard = O at hK ⊢
      obtain ⟨Y', rfl⟩ : ∃ Y', Y = Y' + 1 := ⟨Y - 1, by omega⟩
      have hK' : O * 2 = Y' * X + 2 * X := by rw [hK]; ring
      rw [show Y' + 1 - 1 = Y' by omega]
      generalize Y' * X = Z at hK' ⊢
      omega
    have hodd : Odd (q ^ n - 1) := by
      rw [hr, ← pow_mul]
      have : 2 ≤ 2 ^ (r * n) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have heven : Even (2 ^ (r * n)) := (Nat.even_pow.2 ⟨even_two, by nlinarith⟩)
      obtain ⟨k, hk⟩ := heven
      exact ⟨k - 1, by omega⟩
    have hdvd2 : 2 ^ (j + 1) ∣ (q ^ n - 1) * q ^ (2 * n + 3) := by
      rw [← hΩcard, pow_succ']
      exact Nat.mul_dvd_mul_left 2 hdvd
    have hcop : Nat.Coprime (2 ^ (j + 1)) (q ^ n - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    have hdvd3 := hcop.dvd_of_dvd_mul_left hdvd2
    have hle := Nat.le_of_dvd (by positivity) hdvd3
    rw [hj] at hPcard
    have : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨x, hx, hBx, hax, hoddax, hx1⟩, hBg⟩ := B.2
  have hnogate : ∀ p ∈ D, p ∈ rootGroup D a ⊔ rootGroup D d → orderOf (x * p) ≠ 4 :=
    fun p hp hpT h4 => hBg ⟨B.2.1, x, hx, hBx, p, hp, hpT, h4⟩
  have hgB' : (B : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = B :=
    congrArg Subtype.val hgB
  have hxA : x ∈ rootGroup D x := rootSet_subset_rootGroup D x (mem_rootSet_self hx)
  have hgxA : (g : G) * x * (g : G)⁻¹ ∈ rootGroup D x := by
    have : (g : G) * x * (g : G)⁻¹ ∈ (B : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [hBx]
      exact ⟨x, hxA, rfl⟩
    rwa [hgB', hBx] at this
  have hgxT : (g : G) * x * (g : G)⁻¹ ∈ rootSet D x :=
    mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure hx hgxA (fun h => hD.ne_one hx (by
      have := congrArg (fun w => (g : G)⁻¹ * w * g) h
      simpa [mul_assoc] using this))
  have hga' : ∀ a' ∈ rootSet D a, Commute (g : G) a' := fun a' h' =>
    hPT g g.2 a' (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hgx := fun {u : G} (hu : u ∈ rootGroup D x) =>
    commute_of_conj_mem_rootSet_of_centralizes' C.hyp C.closure C.special ha hx hax hoddax hx1
      hga' hgxT hu
  have htop := C.gen a ha d hd x hx had hadD hdT hax hoddax hx1 hnogate
  have hcen : (g : G) ∈ Subgroup.center G := by
    have hle : rootGroup D a ⊔ rootGroup D d ⊔ rootGroup D x ≤
        Subgroup.centralizer ({(g : G)} : Set G) := by
      refine sup_le (fun t ht => ?_) (fun u hu => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hPT g g.2 t ht).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hgx hu).eq.symm
    rw [htop] at hle
    rw [Subgroup.mem_center_iff]
    intro h'
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top h'))
  rw [C.hyp.center_eq_bot, Subgroup.mem_bot] at hcen
  exact hg1 (Subtype.ext hcen)

end RootMany

end CFSG.Timmesfeld.Bridge
