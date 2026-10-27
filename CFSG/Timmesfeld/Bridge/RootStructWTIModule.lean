module

public import CFSG.Timmesfeld.Bridge.RootStructWTIModBasic
public import CFSG.Timmesfeld.Bridge.RootStructWTINatSum

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {D : Set G}

namespace LineSetting

variable (hL : LineSetting G D)
include hL

section Line

variable {a d : G}

theorem sup_rootGroup_le_normalizer_lineN (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D x ⊔ rootGroup D y ≤ Subgroup.normalizer (lineN D a d : Set G) := by
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hyT
  refine sup_le (hL.rootGroup_le_normalizer_lineN ha hd had hadD hdT hx hax haxD hxT) ?_
  have := hL.rootGroup_le_normalizer_lineN hd ha had.symm hdaD haT hy hdy hdyD hyT'
  rwa [lineN_comm] at this

theorem sup_rootGroup_le_normalizer_lineN₀ (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D x ⊔ rootGroup D y ≤ Subgroup.normalizer (lineN₀ D a d : Set G) := by
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  have hxT' : x ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hxT
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hyT
  refine sup_le (hL.rootGroup_le_normalizer_lineN₀ ha hd had hadD hdT hx hax haxD hxT hy hdy
    hdyD hyT) ?_
  have := hL.rootGroup_le_normalizer_lineN₀ hd ha had.symm hdaD haT hy hdy hdyD hyT' hx hax haxD
    hxT'
  rwa [lineN₀_comm] at this

theorem quotModHyp (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d) :
    QuotMod.Hyp (rootGroup D x ⊔ rootGroup D y) (lineN D a d) (lineN₀ D a d) where
  le := lineN₀_le_lineN D a d
  comm := fun _ hn _ hn' => hL.commutator_mem_lineN₀ ha hd had hadD hdT hn hn'
  conj := fun _ hg n hn => (Subgroup.mem_normalizer_iff.1
    (hL.sup_rootGroup_le_normalizer_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT hg)
      n).1 hn
  conj₀ := fun _ hg n hn => (Subgroup.mem_normalizer_iff.1
    (hL.sup_rootGroup_le_normalizer_lineN₀ ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
      hg) n).1 hn

theorem exists_natural_lineN (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D)
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hyT : y ∉ rootGroup D a ⊔ rootGroup D d)
    {K : Type*} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2]
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφx : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      upperUnipotent K)
    (hφy : ((rootGroup D y).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      lowerUnipotent K) :
    ∃ k : ℕ, ∃ Nf : Fin k → Subgroup G, ∃ θ : Fin k → (Fin 2 → K) → G,
      (∀ i, lineN₀ D a d ≤ Nf i ∧ Higman.IsNaturalQuotient φ (Nf i) (lineN₀ D a d) (θ i)) ∧
      (∀ i (s : K), θ i ![s, 0] ∈ nCore D a ⊓ Subgroup.centralizer {d} ∧
        θ i ![0, s] ∈ nCore D d ⊓ Subgroup.centralizer {a}) ∧
      lineN₀ D a d ⊔ ⨆ i, Nf i = lineN D a d ∧
      Nat.card (lineN D a d) = Nat.card (lineN₀ D a d) * Nat.card K ^ (2 * k) ∧
      Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) =
        Nat.card (lineN₀ D a d) * Nat.card K ^ k ∧
      Nat.card ↥(nCore D d ⊓ Subgroup.centralizer {a}) =
        Nat.card (lineN₀ D a d) * Nat.card K ^ k := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h => hdT (mem_rootSet_comm hd h)
  have hxT' : x ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hxT
  have hyT' : y ∉ rootGroup D d ⊔ rootGroup D a := by rw [sup_comm]; exact hyT
  have hH := hL.quotModHyp ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT
  have := hH.normal
  have hcomm := nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure
  have hN₀B : lineN₀ D a d ≤ nCore D d ⊓ Subgroup.centralizer {a} := by
    rw [← lineN₀_comm]
    exact lineN₀_le_nCore_inf D d a
  have hxX : x ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
  have hyX : y ∈ rootGroup D x ⊔ rootGroup D y :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self hy))
  refine QuotMod.exists_isNaturalQuotient hH φ (lineN₀_le_nCore_inf D a d) hN₀B le_sup_left
    le_sup_right rfl (fun x' hx' k hk => ?_) (fun x' hx' w hw => ?_) ⟨⟨x, hxX⟩, ?_, ?_⟩
    (fun y' hy' w hw => ?_) ⟨⟨y, hyX⟩, ?_, ?_⟩
  · have hx'A : (x' : G) ∈ rootGroup D x := (NaturalModule.coe_mem_iff hφx x').2 hx'
    exact hL.line_le_lineN₀ ha hd had (Subgroup.mem_sup_left
      (hcomm a ha _ (hL.rootGroup_le_nCore ha hax hx'A) k hk.1))
  · have hx'A : (x' : G) ∈ rootGroup D x := (NaturalModule.coe_mem_iff hφx x').2 hx'
    exact hL.commutator_mem_of_collinear ha hd had hadD hdT hx hax haxD hxT hx'A hw
  · exact (NaturalModule.coe_mem_iff hφx _).1 (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
  · exact fun w hw h => hL.mem_lineN₀_of_mul_inv_mem ha hd had hadD hdT hx hax haxD hxT hy hdy
      hdyD hyT (mem_rootSet_self hx) hw h
  · have hy'A : (y' : G) ∈ rootGroup D y := (NaturalModule.coe_mem_iff hφy y').2 hy'
    have := hL.line_le_lineN₀ hd ha had.symm (Subgroup.mem_sup_left
      (hcomm d hd _ (hL.rootGroup_le_nCore hd hdy hy'A) w hw.1))
    rwa [lineN₀_comm] at this
  · exact (NaturalModule.coe_mem_iff hφy _).1 (rootSet_subset_rootGroup D y (mem_rootSet_self hy))
  · intro k hk h
    have := hL.mem_lineN₀_of_mul_inv_mem hd ha had.symm hdaD haT hy hdy hdyD hyT' hx hax haxD hxT'
      (mem_rootSet_self hy) hk (by rwa [lineN₀_comm])
    rwa [lineN₀_comm] at this

theorem card_rootGroup_eq_card_field (ha : a ∈ D) {x y : G} (hx : x ∈ D)
    {K : Type*} [Field K]
    (φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφx : ((rootGroup D x).subgroupOf (rootGroup D x ⊔ rootGroup D y)).map φ.toMonoidHom =
      upperUnipotent K) :
    Nat.card (rootGroup D a) = Nat.card K := by
  have := hL.hyp.finite
  rw [← card_rootGroup_eq hL.hyp.isClass hL.hyp.root hL.closure ha hx,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : rootGroup D x ≤ rootGroup D x ⊔ rootGroup D y)).toEquiv,
    ← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hφx,
    RankOne.card_upperUnipotent]

theorem card_nCore_inf_eq (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x : G} (hx : x ∈ D) (hax : Commute a x)
    (haxD : a * x ∈ D) (hxT : x ∉ rootGroup D a ⊔ rootGroup D d) :
    Nat.card ↥(nCore D d ⊓ Subgroup.centralizer {a}) =
      Nat.card (lineN₀ D a d) * ((rootLines D a).ncard - 1) := by
  classical
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  set B := nCore D d ⊓ Subgroup.centralizer {a} with hB
  set T := rootGroup D a ⊔ rootGroup D d with hT
  set L₀ := rootGroup D a ⊔ rootGroup D x with hL₀
  have hN₀B : lineN₀ D a d ≤ B := by
    rw [← lineN₀_comm]
    exact lineN₀_le_nCore_inf D d a
  have hxTa : x ∉ rootSet D a := fun h => hxT (Subgroup.mem_sup_left
    (rootSet_subset_rootGroup D a h))
  have hTmem : T ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  have hL₀mem : L₀ ∈ rootLines D a := ⟨x, hx, hax, haxD, hxTa, rfl⟩
  have hL₀T : L₀ ≠ T := fun h => hxT (h ▸ Subgroup.mem_sup_right
    (rootSet_subset_rootGroup D x (mem_rootSet_self hx)))
  have hBnorm : ∀ k ∈ B, k ∈ Subgroup.normalizer (rootGroup D a : Set G) := fun k hk =>
    centralizer_le_normalizer_rootGroup hclass a hk.2
  have hBT : ∀ k ∈ B, T.map (MulAut.conj k).toMonoidHom = T := fun k hk =>
    map_conj_eq_of_forall_commute fun t ht => hL.commute_of_mem_nCore_inf' ha hd had hadD hdT hk ht
  have hM : ∀ k ∈ nCore D a, L₀.map (MulAut.conj k).toMonoidHom = L₀ := fun k hk =>
    hL.map_conj_eq_of_mem_closure ha (nCore_le_closure_commute D a hk) hL₀mem
  let f : B → {L : Subgroup G // L ∈ rootLines D a ∧ L ≠ T} := fun k =>
    ⟨L₀.map (MulAut.conj (k : G)).toMonoidHom,
      hL.map_conj_mem_rootLines ha (hBnorm k k.2) hL₀mem, fun h => hL₀T (by
        have := congrArg (fun H : Subgroup G => H.map (MulAut.conj (k : G)⁻¹).toMonoidHom) h
        simp only [RankOne.map_conj_inv_map_conj] at this
        rw [this]
        exact hBT (k : G)⁻¹ (B.inv_mem k.2))⟩
  have hfeq : ∀ k k' : B, f k = f k' ↔ (k : G)⁻¹ * k' ∈ lineN₀ D a d := by
    intro k k'
    constructor
    · intro h
      have h1 : L₀.map (MulAut.conj ((k : G)⁻¹ * k')).toMonoidHom = L₀ := by
        rw [RankOne.map_conj_mul]
        have := congrArg Subtype.val h
        simp only [f] at this
        rw [← this, RankOne.map_conj_inv_map_conj]
      have hkk : (k : G)⁻¹ * k' ∈ B := B.mul_mem (B.inv_mem k.2) k'.2
      have ha' := hL.mem_nCore_of_map_conj_eq ha hd had hadD hdT hx hax haxD hxT hkk.1
        (Subgroup.mem_centralizer_singleton_iff.1 hkk.2) h1
      exact ⟨ha', hkk.1⟩
    · intro h
      apply Subtype.ext
      show L₀.map (MulAut.conj (k : G)).toMonoidHom = L₀.map (MulAut.conj (k' : G)).toMonoidHom
      rw [show (k' : G) = k * ((k : G)⁻¹ * k') by group, RankOne.map_conj_mul (g := (k : G)),
        hM _ h.1]
  have hfsurj : Function.Surjective f := by
    rintro ⟨L, hL', hLT⟩
    obtain ⟨c, hc, hac, hacD, hcT, rfl⟩ := hL'
    have hcL : c ∉ T := fun h => hLT (hL.sup_rootGroup_eq_of_mem_sup ha hc hd hac hcT had hadD
      hdT h)
    obtain ⟨k, hk, hkL⟩ := hL.exists_mem_nCore_conj_line_eq ha hd had hadD hdT hx hax haxD hxT
      hc hac hacD hcL
    exact ⟨⟨k, hk⟩, Subtype.ext hkL⟩
  let N₀' := (lineN₀ D a d).subgroupOf B
  let F : B ⧸ N₀' → {L : Subgroup G // L ∈ rootLines D a ∧ L ≠ T} :=
    Quotient.lift f fun k k' hkk => (hfeq k k').2 (by
      have := QuotientGroup.leftRel_apply.1 hkk
      rwa [Subgroup.mem_subgroupOf] at this)
  have hFbij : Function.Bijective F := by
    refine ⟨fun q q' hqq => ?_, fun L => ?_⟩
    · induction q using QuotientGroup.induction_on with | H k => ?_
      induction q' using QuotientGroup.induction_on with | H k' => ?_
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact (hfeq k k').1 hqq
    · obtain ⟨k, hk⟩ := hfsurj L
      exact ⟨QuotientGroup.mk k, hk⟩
  have hcardQ : Nat.card (B ⧸ N₀') = (rootLines D a).ncard - 1 := by
    rw [Nat.card_congr (Equiv.ofBijective F hFbij)]
    have : Nat.card {L : Subgroup G // L ∈ rootLines D a ∧ L ≠ T} =
        (rootLines D a \ {T}).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [this, Set.ncard_sdiff_singleton_of_mem hTmem]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀', hcardQ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀B).toEquiv, mul_comm]

end Line

end LineSetting

theorem rootLinesPowerStep : RootLinesPowerStep := by
  intro G _ D hL a ha
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hc := hL.closure
  obtain ⟨m, hm⟩ := hL.exists_ncard_rootLines ha
  obtain ⟨e, he⟩ := exists_card_rootGroup_eq_two_pow hD ha
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · interval_cases e
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at he
      have : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
      rw [he, Subgroup.mem_bot] at this
      exact hD.ne_one ha this
    · exact ⟨m, by rw [he, pow_one, hm]⟩
  obtain ⟨T, hT⟩ := hL.exists_mem_rootLines ha
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hT
  obtain ⟨L, hL', hLT⟩ := hL.exists_ne_mem_rootLines ha ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨x, hx, hax, haxD, hxTa, rfl⟩ := hL'
  have hxT : x ∉ rootGroup D a ⊔ rootGroup D d := fun h =>
    hLT (hL.sup_rootGroup_eq_of_mem_sup ha hx hd hax hxTa had hadD hdT h)
  have hTI := hL.lineTI ha hd had hadD hdT
  obtain ⟨y, hy, hdy, hdyD, hay⟩ := exists_special_of_not_mem_line hL.hyp hc hL.special
    hL.lineCentralizerEq ha hd had hadD hdT hTI hx hax haxD hxTa hxT
  have hyT : y ∉ rootGroup D a ⊔ rootGroup D d := fun h =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hy) hay
      (commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) h)
  obtain ⟨hyx, hodd⟩ := opposite_of_not_mem_line hclass hD hc hL.special hL.commLambda
    hL.lineCentralizerEq ha hd had hadD hdT hTI hy hdy hdyD hay hx hax haxD hxT
  have hxd : orderOf (x * d) = 4 :=
    orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hd had hadD hdT hTI hx hax hxT
  have h1 : OneOpposite D y x := ⟨d, hd, hdy.symm, by rw [← hdy.eq]; exact hdyD, hxd⟩
  have hq4 : 4 ≤ Nat.card (rootGroup D y) := by
    rw [card_rootGroup_eq hclass hD hc ha hy, he]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  obtain ⟨n, -, -, φ, hφx, hφy⟩ := exists_mulEquiv_SL2_of_oneOpposite hL.hyp hc hL.special
    hL.commLambda hy hx hyx hodd h1 hq4
  obtain ⟨k, -, -, -, -, -, -, -, hB⟩ :=
    hL.exists_natural_lineN ha hd had hadD hdT hx hax haxD hxT hy hdy hdyD hyT φ hφx hφy
  have hcount := hL.card_nCore_inf_eq ha hd had hadD hdT hx hax haxD hxT
  have hq := hL.card_rootGroup_eq_card_field ha hx φ hφx
  refine ⟨k, ?_⟩
  rw [hq]
  have hpos : 0 < Nat.card (lineN₀ D a d) := Nat.card_pos
  have h2 : (rootLines D a).ncard - 1 = Nat.card (GaloisField 2 n) ^ k :=
    Nat.eq_of_mul_eq_mul_left hpos (hcount.symm.trans hB)
  have hm1 : 1 ≤ (rootLines D a).ncard := by rw [hm]; exact Nat.le_add_left 1 _
  rw [← h2, Nat.sub_add_cancel hm1]

end CFSG.Timmesfeld.Bridge
