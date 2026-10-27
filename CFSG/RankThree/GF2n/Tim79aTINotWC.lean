module

public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.CGT.T75E.UtiInd
public import CFSG.CGT.T75E.J2
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.Timmesfeld.CorollaryBOutcome
public import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld

variable {G : Type} [Group G]

private theorem mem_rootSet_iff {D : Set G} {e d : G} :
    e ∈ rootSet D d ↔ e ∈ D ∧ ∀ f ∈ D, Commute e f ↔ Commute d f :=
  Iff.rfl

private theorem mem_rootClass {D : Set G} {E : Subgroup G} :
    E ∈ rootClass D ↔ ∃ d ∈ D, E = rootGroup D d :=
  Iff.rfl

private theorem commute_conj_iff (g x y : G) :
    Commute (g * x * g⁻¹) (g * y * g⁻¹) ↔ Commute x y := by
  constructor
  · intro h
    unfold Commute SemiconjBy at h ⊢
    calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · intro h
    unfold Commute SemiconjBy at h ⊢
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

private theorem conj_mem_of_isClass {D : Set G} (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (g x : G) (hx : x ∈ D) : g * x * g⁻¹ ∈ D := by
  obtain ⟨d₀, rfl⟩ := hcl
  have hx' : IsConj d₀ x := hx
  show IsConj d₀ (g * x * g⁻¹)
  exact hx'.trans (isConj_iff.2 ⟨g, rfl⟩)

private theorem rootGroup_ne_bot {D : Set G} (h : Hyp G D) {d : G} (hd : d ∈ D) :
    rootGroup D d ≠ ⊥ := by
  intro hbot
  have hmem : d ∈ rootGroup D d := Subgroup.subset_closure (mem_rootSet_self hd)
  rw [hbot, Subgroup.mem_bot] at hmem
  have h2 := h.root.1 d hd
  rw [hmem, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem isPGroup_two_of_isElemAbelian {X : Subgroup G}
    (hX : CFSG.Open.IsElemAbelian 2 X) : IsPGroup 2 X := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using hX.2 _ g.2)

private theorem comm_of_isElemAbelian {X : Subgroup G} (hX : CFSG.Open.IsElemAbelian 2 X)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x :=
  congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem isElemAbelian_conjSubgroup {X : Subgroup G}
    (hX : CFSG.Open.IsElemAbelian 2 X) (g : G) :
    CFSG.Open.IsElemAbelian 2 (conjSubgroup g X) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hx' : g⁻¹ * (x : G) * g ∈ X := mem_conjSubgroup.1 x.2
    have hy' : g⁻¹ * (y : G) * g ∈ X := mem_conjSubgroup.1 y.2
    have h1 : (g⁻¹ * (x : G) * g) * (g⁻¹ * (y : G) * g)
        = (g⁻¹ * (y : G) * g) * (g⁻¹ * (x : G) * g) :=
      congrArg Subtype.val (hX.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
    calc (x : G) * y = g * ((g⁻¹ * (x : G) * g) * (g⁻¹ * (y : G) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (y : G) * g) * (g⁻¹ * (x : G) * g)) * g⁻¹ := by rw [h1]
      _ = (y : G) * x := by group
  · have h2 : (g⁻¹ * x * g) ^ 2 = 1 := hX.2 _ (mem_conjSubgroup.1 hx)
    rw [pow_two] at h2
    calc x ^ 2 = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [h2]; group

private theorem not_mem_rootSet_conj {D : Set G} (h : Hyp G D) {a b : G}
    (hab : b ∉ rootSet D a) (g : G) : g * b * g⁻¹ ∉ rootSet D (g * a * g⁻¹) := by
  intro hmem
  apply hab
  obtain ⟨hD1, hD2⟩ := mem_rootSet_iff.1 hmem
  refine mem_rootSet_iff.2 ⟨?_, fun f hf => ?_⟩
  · have h1 := conj_mem_of_isClass h.isClass g⁻¹ _ hD1
    rwa [show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at h1
  · have h2 := hD2 _ (conj_mem_of_isClass h.isClass g f hf)
    exact ((commute_conj_iff g b f).symm.trans h2).trans (commute_conj_iff g a f)

private theorem rootClass_conjSub {D : Set G} (h : Hyp G D) {E : Subgroup G}
    (hE : E ∈ rootClass D) (g : G) : ARS.conjSub E g ∈ rootClass D := by
  obtain ⟨d, hd, rfl⟩ := mem_rootClass.1 hE
  exact mem_rootClass.2 ⟨g * d * g⁻¹, conj_mem_of_isClass h.isClass g d hd,
    (rootGroup_conj h.isClass g d).symm⟩

private theorem conjSub_conjSub_inv (E : Subgroup G) (g : G) :
    ARS.conjSub (ARS.conjSub E g) g⁻¹ = E := by
  rw [← ARS.conjSub_mul, inv_mul_cancel, ARS.conjSub_one]

private theorem mem_rootClass_of_conjSub {D : Set G} (h : Hyp G D) {E : Subgroup G} {g : G}
    (hE : ARS.conjSub E g ∈ rootClass D) : E ∈ rootClass D := by
  have := rootClass_conjSub h hE g⁻¹
  rwa [conjSub_conjSub_inv] at this

private theorem centralizer_le_normalizer_of_isTI [Finite G] {A : Subgroup G} (hTI : IsTI A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hconj : c⁻¹ * a * c = a := by
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have haC : a ∈ conjSubgroup c A := mem_conjSubgroup.2 (by rw [hconj]; exact ha)
  have hne : A ⊓ conjSubgroup c A ≠ ⊥ := by
    intro hbot
    apply ha1
    have hmem : a ∈ A ⊓ conjSubgroup c A := ⟨ha, haC⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact conjSubgroup_eq_self_iff.1 (conjSubgroup_eq_of_isTI hTI hne)

private theorem exists_commuting_conj_of_not_isWC [Finite G] {A : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 A) (hTI : IsTI A) (hA : A ≠ ⊥) (hWC : ¬ IsWC A) :
    ∃ g : G, A ⊓ conjSubgroup g A = ⊥ ∧ conjSubgroup g A ≠ ⊥ ∧
      ∀ x ∈ A, ∀ y ∈ conjSubgroup g A, Commute x y := by
  have hex : ∃ t ∈ A, t ≠ 1 ∧ ¬ WeaklyClosedIn A (Subgroup.centralizer ({t} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hWC ⟨hE, fun t ht ht1 => hcon t ht ht1⟩
  obtain ⟨t, ht, ht1, hnwc⟩ := hex
  have hAC : A ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_isElemAbelian hE hx ht
  have hg : ∃ g : G, conjSubgroup g A ≤ Subgroup.centralizer ({t} : Set G) ∧
      conjSubgroup g A ≠ A := by
    unfold WeaklyClosedIn at hnwc
    by_contra hcon
    push Not at hcon
    exact hnwc ⟨hAC, fun g hgC => hcon g hgC⟩
  obtain ⟨g, hgC, hgA⟩ := hg
  have hWN : conjSubgroup g A ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    centralizer_le_normalizer_of_isTI hTI ht ht1 (hgC hw)
  have hel := CFSG.RankThree.GF2n.Tim77.tim77_2_3 hE hTI hWN
  refine ⟨g, inf_conjSubgroup_eq_bot_of_isTI hTI hgA, ?_, ?_⟩
  · intro hbot
    apply hA
    apply Subgroup.eq_bot_of_card_eq
    rw [← card_conjSubgroup g A, hbot, Subgroup.card_bot]
  · intro x hx y hy
    exact comm_of_isElemAbelian hel (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

private theorem mem_rootSet_of_isCoatom [Finite G] {D : Set G} (h : Hyp G D) {A : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 A) (hTI : IsTI A) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hmax : ∀ x ∈ D, IsCoatom (Subgroup.centralizer ({x} : Set G))) :
    ∀ b ∈ A, b ≠ 1 → b ∈ rootSet D a := by
  have hNtop : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : A.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    have hbot : A = ⊥ := h.twoCore A hnorm (isPGroup_two_of_isElemAbelian hE)
    rw [hbot, Subgroup.mem_bot] at ha
    exact ha1 ha
  have hcen : ∀ x ∈ A, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Subgroup.normalizer (A : Set G) := by
    intro x hx hx1
    have hle := centralizer_le_normalizer_of_isTI hTI hx hx1
    have hmx := hmax x (hAD x hx hx1)
    by_contra hne
    exact hNtop (hmx.2 _ (lt_of_le_of_ne hle hne))
  intro b hb hb1
  have hbD := hAD b hb hb1
  have hC : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({a} : Set G) := by
    rw [hcen b hb hb1, hcen a ha ha1]
  have key : ∀ x : G, x ∈ Subgroup.centralizer ({b} : Set G) ↔
      x ∈ Subgroup.centralizer ({a} : Set G) := fun x => by rw [hC]
  simp only [Subgroup.mem_centralizer_singleton_iff] at key
  refine mem_rootSet_iff.2 ⟨hbD, fun f _ => ?_⟩
  constructor
  · intro hc
    have h1 : f * b = b * f := (show b * f = f * b from hc).symm
    exact show a * f = f * a from ((key f).1 h1).symm
  · intro hc
    have h1 : f * a = a * f := (show a * f = f * a from hc).symm
    exact show b * f = f * b from ((key f).2 h1).symm

private theorem isCoatom_of_map_equiv' {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y)
    {H : Subgroup X} (h : IsCoatom (H.map ψ.toMonoidHom)) : IsCoatom H := by
  refine ⟨?_, fun K hK => ?_⟩
  · intro htop
    apply h.1
    rw [htop, Subgroup.map_top_of_surjective _ ψ.surjective]
  · have hψ : Function.Injective ψ.toMonoidHom := ψ.injective
    have hlt : H.map ψ.toMonoidHom < K.map ψ.toMonoidHom := by
      refine lt_of_le_of_ne (Subgroup.map_mono hK.le) ?_
      intro heq
      exact hK.ne (Subgroup.map_injective hψ heq)
    have htop := h.2 _ hlt
    apply Subgroup.map_injective hψ
    rw [htop, Subgroup.map_top_of_surjective _ ψ.surjective]

private theorem map_centralizer_singleton_equiv' {X Y : Type} [Group X] [Group Y]
    (ψ : X ≃* Y) (k : X) :
    (Subgroup.centralizer ({k} : Set X)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ k} : Set Y) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg ψ hx
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h2
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨ψ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

private theorem false_of_alt6 [Finite G] {A : Subgroup G} (e : G ≃* alternatingGroup (Fin 6))
    (hE : CFSG.Open.IsElemAbelian 2 A) (hTI : IsTI A) (hWC : ¬ IsWC A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    False := by
  have hA : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at ha
    exact ha1 ha
  obtain ⟨g, hAW, hWne, hcomm⟩ := exists_commuting_conj_of_not_isWC hE hTI hA hWC
  have hG : Nat.card G = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hcard3 : 3 ≤ Nat.card A := by
    have h01 : (1 : A) ≠ ⟨a, ha⟩ := fun k => ha1 (congrArg Subtype.val k).symm
    have h02 : (1 : A) ≠ ⟨b, hb⟩ := fun k => hb1 (congrArg Subtype.val k).symm
    have h12 : (⟨a, ha⟩ : A) ≠ ⟨b, hb⟩ := fun k => hab (congrArg Subtype.val k)
    have hinj : Function.Injective (![(1 : A), ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → A) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd hij h01
        | exact absurd hij.symm h01
        | exact absurd hij h02
        | exact absurd hij.symm h02
        | exact absurd hij h12
        | exact absurd hij.symm h12
    simpa using Nat.card_le_card_of_injective _ hinj
  obtain ⟨m, hm⟩ : ∃ m, Nat.card A = 2 ^ m :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_isElemAbelian hE)
  have hWcard : Nat.card (conjSubgroup g A) = Nat.card A := card_conjSubgroup g A
  have hsup := CFSG.CGT.T75P.card_sup_of_commute (A := A) (B := conjSubgroup g A)
    (fun x hx y hy => hcomm x hx y hy) hAW
  have hdvd := Subgroup.card_subgroup_dvd_card (A ⊔ conjSubgroup g A : Subgroup G)
  rw [hG, hsup, hWcard, hm] at hdvd
  have hm1 : m ≤ 1 := by
    by_contra hm2
    have h4 : 2 ^ 4 ∣ 2 ^ m * 2 ^ m := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    have h360 : 2 ^ 4 ∣ 360 := dvd_trans h4 hdvd
    norm_num at h360
  have hA2 : Nat.card A ≤ 2 := by
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 2 := by norm_num
  omega

private def rootGroupsIn (D : Set G) (A : Subgroup G) : Set (Subgroup G) :=
  {E | E ∈ rootClass D ∧ E ≤ A}

private theorem mem_rootGroupsIn {D : Set G} {A E : Subgroup G} :
    E ∈ rootGroupsIn D A ↔ E ∈ rootClass D ∧ E ≤ A :=
  Iff.rfl

section Certified


private theorem rootGroup_le_of_not_mem_rootSet [Finite G] {D : Set G} (h : Hyp G D)
    {A : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 A) (hTI : IsTI A)
    (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) {u v : G} (hu : u ∈ A) (hu1 : u ≠ 1) (hv : v ∈ A)
    (hv1 : v ≠ 1) (huv : v ∉ rootSet D u) : rootGroup D v ≤ A := by
  have huD := hAD u hu hu1
  have hvD := hAD v hv hv1
  by_cases hS : ∀ d ∈ D, rootSet D d = {d}
  · have hvS : rootSet D v = {v} := hS v hvD
    unfold rootGroup
    rw [hvS]
    exact (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hv)
  · push Not at hS
    obtain ⟨d, hdD, hd⟩ := hS
    have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d := by
      by_contra hcon
      push Not at hcon
      apply hd
      exact Set.eq_singleton_iff_unique_mem.2 ⟨mem_rootSet_self hdD, fun e he => hcon d hdD e he⟩
    obtain ⟨hc, hs, -, -⟩ := CFSG.Timmesfeld.CorB.largeFacts h hl
    have hcomm : Commute u v := comm_of_isElemAbelian hE hu hv
    have hu_self : u ∈ rootSet D u := mem_rootSet_self huD
    have huv1 : u ≠ v := fun e => huv (by rw [← e]; exact hu_self)
    have huvA : u * v ∈ A := A.mul_mem hu hv
    have hu2 : u * u = 1 := by
      rw [← pow_two]
      exact hE.2 u hu
    have huv_ne : u * v ≠ 1 := by
      intro e
      apply huv1
      have hv' : v = u⁻¹ := eq_inv_of_mul_eq_one_right e
      have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      exact (hv'.trans hu').symm
    have huvD : u * v ∈ D := hAD _ huvA huv_ne
    obtain ⟨x, hxD, hx3, hxnc, hxv⟩ :=
      CFSG.Timmesfeld.Bridge.RootClosure.exists_orderOf_eq_three_of_collinear_class
        h.isClass h.root (CFSG.Timmesfeld.Bridge.oppositeDetermines_of_hyp h) huD hvD hcomm
        huvD huv
    have hodd : Odd (orderOf (u * x)) := by
      have h3 : orderOf (u * x) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      exact Odd.of_dvd_nat ⟨1, by norm_num⟩ h3
    obtain ⟨y, hyD, -, -, -, hyeq⟩ :=
      CFSG.Timmesfeld.Bridge.exists_conj_eq_mul_of_odd_special h.root
        (conj_mem_of_isClass h.isClass) huD hxD hvD hxnc hodd hxv hcomm huvD
    have hsq : (u * y) ^ 2 = v := by
      calc (u * y) ^ 2 = u * (y * u * y) := by rw [pow_two]; group
        _ = u * (u * v) := by rw [hyeq]
        _ = (u * u) * v := by group
        _ = v := by rw [hu2, one_mul]
    have h4 : orderOf (u * y) = 4 := by
      have hnot : ¬ (u * y) ^ 2 ^ 1 = 1 := by
        show ¬ (u * y) ^ 2 = 1
        rw [hsq]
        exact hv1
      have hfin : (u * y) ^ 2 ^ (1 + 1) = 1 := by
        show (u * y) ^ 4 = 1
        have hv2 : v ^ 2 = 1 := hE.2 v hv
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, hv2]
      exact (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)
    have hcent := CFSG.Timmesfeld.special_pair_central h huD hyD h4
    rw [hsq] at hcent
    have hvmem : v ∈ rootGroup D v := Subgroup.subset_closure (mem_rootSet_self hvD)
    have hyN : rootGroup D y ≤ Subgroup.normalizer (A : Set G) := by
      intro s hs
      have hsS : s ∈ (rootGroup D u ⊔ rootGroup D y ⊔ rootGroup D v : Subgroup G) :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right hs)
      have hsC : s ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 (hcent hvmem) s hsS
      exact centralizer_le_normalizer_of_isTI hTI hv hv1 hsC
    have him := CFSG.Timmesfeld.image_mul_sq_rootGroup_right h.isClass h.root hc hs huD hyD h4
      (mem_rootSet_self huD)
    rw [hsq] at him
    have hgsq : ∀ g ∈ rootGroup D y, g * g = 1 := by
      intro g hg
      have hg' : g ∈ insert 1 (rootSet D y) := by
        rw [← CFSG.Timmesfeld.coe_rootGroup_of_rootClosure h.root hc hyD]
        exact hg
      rcases Set.mem_insert_iff.1 hg' with rfl | hgS
      · exact mul_one 1
      · have h2 : orderOf g = 2 := h.root.1 g (mem_rootSet_iff.1 hgS).1
        have h3 := pow_orderOf_eq_one g
        rw [h2, pow_two] at h3
        exact h3
    intro z hz
    have hz' : z ∈ (fun g => (u * g) ^ 2) '' (rootGroup D y : Set G) := by
      rw [him]
      exact hz
    obtain ⟨g, hg, hgz⟩ := hz'
    rw [← hgz]
    show (u * g) ^ 2 ∈ A
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hgsq g hg)
    have hcon : g * u * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hyN hg) u).1 hu
    have hsq' : (u * g) ^ 2 = u * (g * u * g⁻¹) := by
      rw [pow_two, hginv]
      group
    rw [hsq']
    exact A.mul_mem hu hcon

private theorem rootGroup_le_of_forall [Finite G] {D : Set G} (h : Hyp G D) {B : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 B) (hTI : IsTI B) (hBD : ∀ a ∈ B, a ≠ 1 → a ∈ D)
    {a b : G} (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hab : b ∉ rootSet D a) : ∀ v ∈ B, v ≠ 1 → rootGroup D v ≤ B := by
  intro v hv hv1
  by_cases hva : v ∈ rootSet D a
  · refine rootGroup_le_of_not_mem_rootSet h hE hTI hBD hb hb1 hv hv1 ?_
    intro hvb
    apply hab
    refine mem_rootSet_iff.2 ⟨hBD b hb hb1, fun f hf => ?_⟩
    exact ((mem_rootSet_iff.1 hvb).2 f hf).symm.trans ((mem_rootSet_iff.1 hva).2 f hf)
  · exact rootGroup_le_of_not_mem_rootSet h hE hTI hBD ha ha1 hv hv1 hva

private theorem isTI_rootGroupsIn [Finite G] {D : Set G} (h : Hyp G D) {A : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 A) (hTI : IsTI A) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D)
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hab : b ∉ rootSet D a) : ARS.IsTI (rootClass D) (rootGroupsIn D A) := by
  have hroot : ∀ v ∈ A, v ≠ 1 → rootGroup D v ∈ rootGroupsIn D A := fun v hv hv1 =>
    mem_rootGroupsIn.2 ⟨mem_rootClass.2 ⟨v, hAD v hv hv1, rfl⟩,
      rootGroup_le_of_forall h hE hTI hAD ha ha1 hb hb1 hab v hv hv1⟩
  have hconjSet' : ∀ (g : G) (E : Subgroup G), E ∈ ARS.conjSet (rootGroupsIn D A) g ↔
      E ∈ rootClass D ∧ E ≤ conjSubgroup g A := by
    intro g E
    rw [ARS.mem_conjSet, mem_rootGroupsIn, CFSG.CGT.T75E.conjSub_inv_le_iff]
    constructor
    · rintro ⟨hR, hle⟩
      exact ⟨mem_rootClass_of_conjSub h hR, hle⟩
    · rintro ⟨hR, hle⟩
      exact ⟨rootClass_conjSub h hR g⁻¹, hle⟩
  refine ⟨fun E hE' => (mem_rootGroupsIn.1 hE').1,
    ⟨rootGroup D a, hroot a ha ha1, rootGroup D b, hroot b hb hb1, ?_⟩, ?_, fun g => ?_⟩
  · intro e
    have hbA : b ∈ rootGroup D a := by
      rw [e]
      exact Subgroup.subset_closure (mem_rootSet_self (hAD b hb hb1))
    exact hab (mem_rootSet_of_mem_rootGroup h.isClass (hAD a ha ha1) (hAD b hb hb1) hbA)
  · intro hΔ
    have hDA : D ⊆ A := by
      intro d hd
      have hmem : rootGroup D d ∈ rootGroupsIn D A := by
        rw [hΔ]
        exact mem_rootClass.2 ⟨d, hd, rfl⟩
      exact (mem_rootGroupsIn.1 hmem).2 (Subgroup.subset_closure (mem_rootSet_self hd))
    have hle : ⊤ ≤ A := by
      rw [← h.gen]
      exact (Subgroup.closure_le _).2 hDA
    have htop : A = ⊤ := top_le_iff.1 hle
    have hnorm : A.Normal := by
      rw [htop]
      infer_instance
    have hbot : A = ⊥ := h.twoCore A hnorm (isPGroup_two_of_isElemAbelian hE)
    rw [hbot, Subgroup.mem_bot] at ha
    exact ha1 ha
  · by_cases hg : conjSubgroup g A = A
    · right
      ext E
      constructor
      · intro hEi
        exact hEi.1
      · intro hEΔ
        exact ⟨hEΔ, (hconjSet' g E).2 ⟨(mem_rootGroupsIn.1 hEΔ).1, by
          rw [hg]
          exact (mem_rootGroupsIn.1 hEΔ).2⟩⟩
    · left
      refine Set.eq_empty_of_forall_notMem fun E hE' => ?_
      obtain ⟨hE1, hE2⟩ := hE'
      have hE1' := mem_rootGroupsIn.1 hE1
      have hle : E ≤ A ⊓ conjSubgroup g A :=
        le_inf hE1'.2 ((hconjSet' g E).1 hE2).2
      rw [inf_conjSubgroup_eq_bot_of_isTI hTI hg, le_bot_iff] at hle
      obtain ⟨d, hd, rfl⟩ := mem_rootClass.1 hE1'.1
      exact rootGroup_ne_bot h hd hle

private theorem false_of_arsHyp [Finite G] {D : Set G} (h : Hyp G D)
    (hars : ARS.Hyp G (rootClass D)) {A : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 A)
    (hTI : IsTI A) (hAD : ∀ a ∈ A, a ≠ 1 → a ∈ D) (hWC : ¬ IsWC A)
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hab : b ∉ rootSet D a) : False := by
  have hA : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at ha
    exact ha1 ha
  obtain ⟨g, hAW, hWne, hcomm⟩ := exists_commuting_conj_of_not_isWC hE hTI hA hWC
  have hWE := isElemAbelian_conjSubgroup hE g
  have hWTI := isTI_conjSubgroup hTI g
  have hWD : ∀ w ∈ conjSubgroup g A, w ≠ 1 → w ∈ D := by
    intro w hw hw1
    have h1 : g⁻¹ * w * g ∈ A := mem_conjSubgroup.1 hw
    have h2 : g⁻¹ * w * g ≠ 1 := fun e => hw1 (by
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group)
    have h4 := conj_mem_of_isClass h.isClass g _ (hAD _ h1 h2)
    rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h4
  have ha' : g * a * g⁻¹ ∈ conjSubgroup g A := mem_conjSubgroup.2 (by
    rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
    exact ha)
  have hb' : g * b * g⁻¹ ∈ conjSubgroup g A := mem_conjSubgroup.2 (by
    rw [show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb)
  have ha1' : g * a * g⁻¹ ≠ 1 := fun e => ha1 (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  have hb1' : g * b * g⁻¹ ≠ 1 := fun e => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  have hWroot := rootGroup_le_of_forall h hWE hWTI hWD ha' ha1' hb' hb1'
    (not_mem_rootSet_conj h hab g)
  have hΔ := isTI_rootGroupsIn h hE hTI hAD ha ha1 hb hb1 hab
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWne
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hwD := hWD w hwW hw1'
  have hCW : rootGroup D w ≤ conjSubgroup g A := hWroot w hwW hw1'
  have hgen : ARS.gen (rootGroupsIn D A) ≤ A := by
    unfold ARS.gen
    exact iSup₂_le fun B hB => (mem_rootGroupsIn.1 hB).2
  have hCV : ARS.Commuting (rootGroup D w) (ARS.gen (rootGroupsIn D A)) := by
    unfold ARS.Commuting
    intro c hc s hs
    exact (hcomm s (hgen hs) c (hCW hc)).symm
  have hmem := CFSG.Timmesfeld.ARS.Sec5.mem_of_commuting_gen hars.root hars.noIsolated
    hars.nondeg (fun _ hX _ hY e => CFSG.Timmesfeld.ARS.eq_of_omegaSet_eq hars hX hY e)
    hΔ.isWeakTI (mem_rootClass.2 ⟨w, hwD, rfl⟩) hCV
  have hwA : w ∈ A ⊓ conjSubgroup g A :=
    ⟨(mem_rootGroupsIn.1 hmem).2 (Subgroup.subset_closure (mem_rootSet_self hwD)), hwW⟩
  rw [hAW, Subgroup.mem_bot] at hwA
  exact hw1' hwA

end Certified

section J2

open CFSG.ComponentClassification.J2Cover (P permA permA_mem permTwoA nativeEquivP inner_classes)


private theorem false_of_sq_eq_permA {η : ↥P} (h4 : orderOf η = 4)
    (hsq : η ^ 2 = ⟨permA, permA_mem⟩) : False := by
  have hperm : (η : Equiv.Perm (Fin 315)) ^ 2 = permA := by
    have := congrArg Subtype.val hsq
    simpa using this
  have hmem : (η : Equiv.Perm (Fin 315)) ∈ CFSG.Sporadic.Schreier.centralizerIn P permA := by
    refine CFSG.Sporadic.Schreier.mem_centralizerIn.2 ⟨η.2, ?_⟩
    rw [← hperm]
    exact Commute.self_pow _ 2
  have hord : orderOf (η : Equiv.Perm (Fin 315)) = 4 := by
    rw [Subgroup.orderOf_coe]
    exact h4
  exact CFSG.CGT.T75E.orderOf_ne_four_of_mem_centralizerIn_permA hmem hord

private theorem not_conj_permA_of_root {D : Set G} (h : Hyp G D) (e : G ≃* ↥P) {x : G}
    (hx : x ∈ D) (c : ↥P) (hc : e x = c * ⟨permA, permA_mem⟩ * c⁻¹) : False := by
  obtain ⟨d, hd, f, hf, h4⟩ := h.nondeg
  have hz : (d * f) ^ 2 ∈ D := h.root.2.2 d hd f hf h4
  obtain ⟨d₀, hcl⟩ := h.isClass
  have hxc : IsConj d₀ x := by
    rw [hcl] at hx
    exact hx
  have hzc : IsConj d₀ ((d * f) ^ 2) := by
    rw [hcl] at hz
    exact hz
  obtain ⟨g, hg⟩ := isConj_iff.1 (hxc.symm.trans hzc)
  have hz2 : e ((d * f) ^ 2) = (e g * c) * ⟨permA, permA_mem⟩ * (e g * c)⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv, hc]
    group
  have hδ4 : orderOf (e d * e f) = 4 := by
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h4
  have hδ2 : (e d * e f) ^ 2 = (e g * c) * ⟨permA, permA_mem⟩ * (e g * c)⁻¹ := by
    rw [← hz2, map_pow, map_mul]
  refine false_of_sq_eq_permA (η := (e g * c)⁻¹ * (e d * e f) * (e g * c)) ?_ ?_
  · rw [orderOf_inv_mul_mul_eq]
    exact hδ4
  · calc ((e g * c)⁻¹ * (e d * e f) * (e g * c)) ^ 2
        = (e g * c)⁻¹ * (e d * e f) ^ 2 * (e g * c) := by rw [pow_two, pow_two]; group
      _ = ⟨permA, permA_mem⟩ := by rw [hδ2]; group

private theorem isCoatom_centralizer_of_j2 {D : Set G} (h : Hyp G D)
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic G .J2) :
    ∀ x ∈ D, IsCoatom (Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨e0⟩ := hJ
  have e : G ≃* ↥P := e0.trans nativeEquivP
  intro x hx
  have hord : orderOf ((e x : ↥P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.root.1 x hx
  obtain ⟨r, hr, c, hc, hceq⟩ :=
    inner_classes.1 ((e x : ↥P) : Equiv.Perm (Fin 315)) (e x).2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (not_conj_permA_of_root h e hx ⟨c, hc⟩ (Subtype.ext hceq)).elim
  · have hex : e x = (⟨c, hc⟩ : ↥P) * CFSG.CGT.T75E.tP * (⟨c, hc⟩ : ↥P)⁻¹ :=
      Subtype.ext hceq
    have hcoat : IsCoatom (Subgroup.centralizer ({e x} : Set ↥P)) := by
      rw [hex]
      exact CFSG.CGT.T75E.isCoatom_centralizer_conj_tP ⟨c, hc⟩
    exact isCoatom_of_map_equiv' e (by rw [map_centralizer_singleton_equiv' e x]; exact hcoat)

end J2

section Main


theorem tim75aTINotWCRoot_holds : Tim75aTINotWCRoot := by
  unfold Tim75aTINotWCRoot
  intro Y _ _ D h A hA1 hAD hE hTI hWC
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  have haD : a ∈ D := hAD a ha ha1'
  by_cases hall : ∀ b ∈ A, b ≠ 1 → b ∈ rootSet D a
  · refine ⟨a, haD, fun x hx => ?_⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · exact Subgroup.subset_closure (hall x hx hx1)
  · exfalso
    push Not at hall
    obtain ⟨b, hb, hb1, hab⟩ := hall
    have hne : a ≠ b := by
      rintro rfl
      exact hab (mem_rootSet_self haD)
    rcases CFSG.CGT.T75E.arsHyp_or_exc_of_hyp h with hars | hNe | hJ
    · exact false_of_arsHyp h hars hE hTI hAD hWC ha ha1' hb hb1 hab
    · obtain ⟨e⟩ := hNe
      exact false_of_alt6 e hE hTI hWC ha hb ha1' hb1 hne
    · exact hab (mem_rootSet_of_isCoatom h hE hTI hAD ha ha1'
        (isCoatom_centralizer_of_j2 h hJ) b hb hb1)

end Main

end CFSG.RankThree.GF2n.Tim79a
