module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10
public import CFSG.CGT.PushingUpLit.SolK.FourD

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

namespace H4b

section Supported

variable {n : ℕ}

theorem uvec_eq_barInd {x y : Fin n} (hxy : x ≠ y) : uvec x y = barInd {x, y} := by
  unfold uvec barInd
  congr 1
  funext i
  simp only [Pi.add_apply, indVec, Finset.mem_insert, Finset.mem_singleton, Pi.single_apply]
  by_cases hix : i = x
  · subst hix
    simp [hxy]
  · by_cases hiy : i = y
    · subst hiy
      simp [hix]
    · simp [hix, hiy]

@[expose] def barSub (J : Finset (Fin n)) : AddSubgroup (permBar n) where
  carrier := {v | ∃ x : Fin n → ZMod 2, (∀ i, i ∉ J → x i = 0) ∧ (x : permBar n) = v}
  zero_mem' := ⟨0, fun _ _ => rfl, rfl⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, fun i hi => by simp [hx i hi, hy i hi], rfl⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, fun i hi => by simp [hx i hi], rfl⟩

theorem barAct_eq_self_of_mem_barSub {J : Finset (Fin n)} {σ : Perm (Fin n)}
    (hσ : ∀ j ∈ J, σ j = j) {v : permBar n} (hv : v ∈ barSub J) : barAct σ v = v := by
  obtain ⟨x, hx, rfl⟩ := hv
  rw [barAct_mk]
  congr 1
  funext i
  rw [vecPerm_apply]
  by_cases hi : i ∈ J
  · have : σ⁻¹ i = i := by
      rw [Perm.inv_eq_iff_eq]
      exact (hσ i hi).symm
    rw [this]
  · have hi' : σ⁻¹ i ∉ J := by
      intro h
      apply hi
      have e : i = σ⁻¹ i := by
        have := hσ _ h
        rwa [perm_apply_inv_self] at this
      rw [e]
      exact h
    rw [hx _ hi', hx _ hi]

theorem barLen_zero' : barLen (0 : permBar n) = 0 := by
  have := barLen_barInd (n := n) ∅
  rwa [barInd_empty, Finset.card_empty, Nat.zero_min] at this

theorem uvec_mem_barSub {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∈ J) :
    uvec a b ∈ barSub J := by
  refine ⟨Pi.single a 1 + Pi.single b 1, fun i hi => ?_, rfl⟩
  have h1 : i ≠ a := fun h => hi (h ▸ ha)
  have h2 : i ≠ b := fun h => hi (h ▸ hb)
  simp [Pi.single_apply, h1, h2]

theorem eq_of_uvec_eq {x y a b : Fin 10} (hxy : x ≠ y) (hab : a ≠ b) (h : uvec x y = uvec a b) :
    x = a ∨ x = b := by
  rw [uvec_eq_barInd hxy, uvec_eq_barInd hab] at h
  have hI : ({x, y} : Finset (Fin 10)).card = 2 := Finset.card_pair hxy
  have hJ : ({a, b} : Finset (Fin 10)).card = 2 := Finset.card_pair hab
  have h2 : ({x, y} : Finset (Fin 10)) = {a, b} :=
    eq_of_barInd_eq (I := {x, y}) (J := {a, b}) (by rw [hI]; norm_num) (by rw [hI, hJ]) h
  have h3 : x ∈ ({a, b} : Finset (Fin 10)) := h2 ▸ Finset.mem_insert_self x {y}
  simpa using h3

theorem fix_of_fix_uvec {J : Finset (Fin 10)} (hJ : 3 ≤ J.card) {σ : Perm (Fin 10)}
    (hσ : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → barAct σ (uvec a b) = uvec a b) : ∀ a ∈ J, σ a = a := by
  classical
  intro a ha
  obtain ⟨b, hbJ, hbs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a} : Finset (Fin 10))) (t := J) (by simp; omega)
  simp only [Finset.mem_singleton] at hbs
  obtain ⟨c, hcJ, hcs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin 10))) (t := J) (by
      have := Finset.card_le_two (a := a) (b := b)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
  have hab : a ≠ b := Ne.symm hbs
  have hac : a ≠ c := Ne.symm hcs.1
  have h1 := hσ a ha b hbJ hab
  have h2 := hσ a ha c hcJ hac
  rw [barAct_uvec] at h1 h2
  have hσab : σ a ≠ σ b := fun h' => hab (σ.injective h')
  have hσac : σ a ≠ σ c := fun h' => hac (σ.injective h')
  rcases eq_of_uvec_eq hσab hab h1 with h3 | h3
  · exact h3
  · rcases eq_of_uvec_eq hσac hac h2 with h4 | h4
    · exact h4
    · exact absurd (h3.symm.trans h4) (Ne.symm hcs.2)

@[expose] noncomputable def barPerm (n : ℕ) : Perm (Fin n) →* Equiv.Perm (permBar n) where
  toFun σ :=
    { toFun := barAct σ
      invFun := barAct σ⁻¹
      left_inv := fun v => by rw [← barAct_mul, inv_mul_cancel, barAct_one]
      right_inv := fun v => by rw [← barAct_mul, mul_inv_cancel, barAct_one] }
  map_one' := Equiv.ext fun v => barAct_one v
  map_mul' σ τ := Equiv.ext fun v => barAct_mul σ τ v

end Supported

section Delta

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10}

section PiDataLemmas

variable (D : C.PiData)

theorem piQ_injective (hrbot : Rc X = ⊥) : Function.Injective D.piQ := by
  intro a b h
  have h1 : D.piQ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (D.piQ_eq_one_iff _).1 h1
  rw [hrbot, Subgroup.mem_bot] at h2
  have h3 : (a : G)⁻¹ * (b : G) = 1 := h2
  exact Subtype.ext (inv_mul_eq_one.1 h3)

theorem exists_piQ_eq_uvec (a b : Fin 10) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (D.piQ q) = uvec a b := by
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd (pairEW a b : altHeart 10))
  refine ⟨⟨(w : G), C.S.W_le_Q w.2⟩, ?_⟩
  rw [D.piQ_W w _ rfl, hw, toAdd_ofAdd, heartToBar_pairEW_eq_uvec]

@[expose] noncomputable def DeltaJ (J : Finset (Fin 10)) : Subgroup G :=
  (((barSub J).toSubgroup).comap D.piQ).map (CFSG.Open.pCoreOf 2 M).subtype

theorem mem_DeltaJ {J : Finset (Fin 10)} {g : G} :
    g ∈ DeltaJ D J ↔ ∃ hg : g ∈ CFSG.Open.pCoreOf 2 M,
      Multiplicative.toAdd (D.piQ ⟨g, hg⟩) ∈ barSub J := by
  unfold DeltaJ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem DeltaJ_le_Q (J : Finset (Fin 10)) : DeltaJ D J ≤ CFSG.Open.pCoreOf 2 M := by
  intro g hg
  obtain ⟨hgQ, -⟩ := (mem_DeltaJ D).1 hg
  exact hgQ

theorem mem_DeltaJ_of_piQ {J : Finset (Fin 10)} (q : ↥(CFSG.Open.pCoreOf 2 M))
    (h : Multiplicative.toAdd (D.piQ q) ∈ barSub J) : (q : G) ∈ DeltaJ D J :=
  (mem_DeltaJ D).2 ⟨q.2, h⟩

theorem centralizes_DeltaJ_of_fix (hrbot : Rc X = ⊥) {J : Finset (Fin 10)} {m : ↥M}
    (hm : ∀ j ∈ J, C.θ m j = j) : ∀ g ∈ DeltaJ D J, (m : G) * g * (m : G)⁻¹ = g := by
  intro g hg
  obtain ⟨hgQ, hgJ⟩ := (mem_DeltaJ D).1 hg
  have hmgQ : (m : G) * g * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M m.2 hgQ
  have h1 := D.piQ_conj m ⟨g, hgQ⟩ ⟨(m : G) * g * (m : G)⁻¹, hmgQ⟩ rfl
  rw [barAct_eq_self_of_mem_barSub hm hgJ] at h1
  have h2 : D.piQ ⟨(m : G) * g * (m : G)⁻¹, hmgQ⟩ = D.piQ ⟨g, hgQ⟩ :=
    Multiplicative.toAdd.injective h1
  exact congrArg Subtype.val (piQ_injective D hrbot h2)

theorem fix_of_centralizes_DeltaJ {J : Finset (Fin 10)} (hJ : 3 ≤ J.card) {m : ↥M}
    (hc : ∀ g ∈ DeltaJ D J, (m : G) * g * (m : G)⁻¹ = g) : ∀ j ∈ J, C.θ m j = j := by
  refine fix_of_fix_uvec hJ ?_
  intro a ha b hb hab
  obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a b
  have hqJ : (q : G) ∈ DeltaJ D J :=
    mem_DeltaJ_of_piQ D q (by rw [hq]; exact uvec_mem_barSub ha hb)
  have hmq : (m : G) * (q : G) * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M m.2 q.2
  have h1 := D.piQ_conj m q ⟨(m : G) * (q : G) * (m : G)⁻¹, hmq⟩ rfl
  have h2 : (⟨(m : G) * (q : G) * (m : G)⁻¹, hmq⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = q :=
    Subtype.ext (hc _ hqJ)
  rw [h2, hq] at h1
  exact h1.symm

theorem DeltaJ_ne_bot {J : Finset (Fin 10)} (hJ : 2 ≤ J.card) : DeltaJ D J ≠ ⊥ := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
  intro hbot
  obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a b
  have hqJ : (q : G) ∈ DeltaJ D J :=
    mem_DeltaJ_of_piQ D q (by rw [hq]; exact uvec_mem_barSub ha hb)
  rw [hbot, Subgroup.mem_bot] at hqJ
  have hq1 : q = 1 := Subtype.ext hqJ
  rw [hq1, map_one, toAdd_one] at hq
  have hlen : barLen (uvec a b) = 2 := by
    rw [uvec_eq_barInd hab, barLen_barInd, Finset.card_pair hab]
    norm_num
  rw [← hq] at hlen
  have h0 : barLen (0 : permBar 10) = 0 := barLen_zero'
  omega

theorem pCore_centralizer_DeltaJ_le (hR : Nat.card ↥(Rc X) ≤ 2) (hrbot : Rc X = ⊥)
    {J : Finset (Fin 10)} (hJ : 3 ≤ J.card)
    (hJc : Jᶜ.card ≤ 1 ∨ Jᶜ.card = 3 ∨ 5 ≤ Jᶜ.card) :
    CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ((DeltaJ D J : Subgroup G) : Set G)) ≤
      CFSG.Open.pCoreOf 2 M := by
  classical
  set Cc : Subgroup G := M ⊓ Subgroup.centralizer ((DeltaJ D J : Subgroup G) : Set G) with hCc
  set TB : Subgroup G := CFSG.Open.pCoreOf 2 Cc with hTB
  have hTBM : TB ≤ M := (pCoreOf_le_self Cc).trans inf_le_left
  set N : Subgroup (Perm (Fin 10)) := (TB.subgroupOf M).map C.θ with hN
  have hN2 : IsPGroup 2 N := by
    have h2 : IsPGroup 2 ↥(TB.subgroupOf M) :=
      (isPGroup_pCoreOf' Cc).of_equiv (Subgroup.subgroupOfEquivOfLe hTBM).symm
    exact h2.map C.θ
  have hcentral : ∀ c : G, c ∈ Cc → ∀ g ∈ DeltaJ D J, c * g * c⁻¹ = g := by
    intro c hc g hg
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 g hg
    calc c * g * c⁻¹ = (g * c) * c⁻¹ := by rw [← h1]
      _ = g := by group
  have hfixJ : ∀ σ ∈ N, ∀ j ∈ J, σ j = j := by
    intro σ hσ j hj
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hmC : (m : G) ∈ Cc := pCoreOf_le_self Cc (Subgroup.mem_subgroupOf.1 hm)
    exact fix_of_centralizes_DeltaJ D hJ (hcentral _ hmC) j hj
  have hNJ : N ≤ setStab Jᶜ := fun σ hσ => setStab_compl_of_fix (hfixJ σ hσ)
  have hnorm : ∀ τ ∈ altOn Jᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
    intro τ hτ σ hσ
    have hτalt : τ ∈ alternatingGroup (Fin 10) :=
      Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2
    have hτJ : ∀ j ∈ J, τ j = j := fun j hj => (mem_altOn.1 hτ).1 j (by simpa using hj)
    obtain ⟨c, hcθ⟩ := C.exists_lift hτalt
    have hcM : (c : G) ∈ M := C.S.le c.2
    have hcC : (c : G) ∈ Cc := by
      refine Subgroup.mem_inf.2 ⟨hcM, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have this : (c : G) * g * (c : G)⁻¹ = g :=
        centralizes_DeltaJ_of_fix D hrbot (m := ⟨(c : G), hcM⟩)
          (by rw [show C.θ ⟨(c : G), hcM⟩ = τ from hcθ]; exact hτJ) g hg
      calc g * (c : G) = ((c : G) * g * (c : G)⁻¹) * (c : G) := by rw [this]
        _ = (c : G) * g := by group
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hcm : (c : G) * (m : G) * (c : G)⁻¹ ∈ TB :=
      pCoreOf_normalized Cc hcC (Subgroup.mem_subgroupOf.1 hm)
    have hcmM : (c : G) * (m : G) * (c : G)⁻¹ ∈ M :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcM m.2) (M.inv_mem hcM)
    refine Subgroup.mem_map.2 ⟨⟨(c : G) * (m : G) * (c : G)⁻¹, hcmM⟩,
      Subgroup.mem_subgroupOf.2 hcm, ?_⟩
    have : (⟨(c : G) * (m : G) * (c : G)⁻¹, hcmM⟩ : ↥M) =
        ⟨(c : G), hcM⟩ * m * ⟨(c : G), hcM⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, show C.θ ⟨(c : G), hcM⟩ = τ from hcθ]
  have hfixc := block_fixes hN2 hNJ hnorm hJc
  intro t ht
  have htM : t ∈ M := hTBM ht
  have hmem : C.θ ⟨t, htM⟩ ∈ N :=
    Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have hθ1 : C.θ ⟨t, htM⟩ = 1 := by
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    by_cases hx : x ∈ J
    · exact hfixJ _ hmem x hx
    · exact hfixc _ hmem x (Finset.mem_compl.2 hx)
  have hK : t ∈ C.K := C.mem_K.2 ⟨htM, hθ1⟩
  rwa [C.K_eq_Q hR] at hK

theorem centralizer_DeltaJ_le_M (hR : Nat.card ↥(Rc X) ≤ 2) (hrbot : Rc X = ⊥)
    {J : Finset (Fin 10)} (hJ : 3 ≤ J.card) (hJc : Jᶜ.card ≤ 1 ∨ Jᶜ.card = 3 ∨ 5 ≤ Jᶜ.card) :
    Subgroup.centralizer ((DeltaJ D J : Subgroup G) : Set G) ≤ M := by
  have h := C.centralizer_le_M hR (DeltaJ_le_Q D J) (DeltaJ_ne_bot D (by omega))
    (pCore_centralizer_DeltaJ_le D hR hrbot hJ hJc)
  exact (Subgroup.centralizer_le_normalizer _).trans h.2

end PiDataLemmas

end Delta

section Four

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

abbrev centerP (x : G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (CGOf x) ⊓
    Subgroup.centralizer ((CFSG.Open.pCoreOf 2 (CGOf x) : Subgroup G) : Set G)

theorem mem_normalizer_centerP {x k : G} (hk : k ∈ CGOf x) :
    k ∈ Subgroup.normalizer ((centerP x : Subgroup G) : Set G) := by
  have hP : ∀ k ∈ CGOf x, ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x),
      k * p * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (CGOf x) := fun k hk p hp => pCoreOf_normalized _ hk hp
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => center_conj_mem hP hk he, fun he => ?_⟩
  have := center_conj_mem hP ((CGOf x).inv_mem hk) he
  simpa [mul_assoc] using this

section CfgLemmas

variable {n : ℕ} (C : Cfg G M X n) (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M)
include C hR hx

theorem Q_le_CGOf : CFSG.Open.pCoreOf 2 M ≤ CGOf x := fun q hq =>
  mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 (C.Q_comm hR q hq x hx))

theorem Q_le_normalizer_P : CFSG.Open.pCoreOf 2 M ≤
    Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (CGOf x) : Subgroup G) : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have hqK : q ∈ CGOf x := Q_le_CGOf C hR hx hq
  refine ⟨fun hp => pCoreOf_normalized _ hqK hp, fun hp => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hp
  simpa [mul_assoc] using this

theorem isPGroup_sup :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) :=
  (isPGroup_pCoreOf' (CGOf x)).to_sup_of_normal_left' (isPGroup_pCoreOf' M)
    (Q_le_normalizer_P C hR hx)

theorem sup_inf_le_TOf :
    (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M ≤ TOf M x := by
  have hT2 := isPGroup_sup C hR hx
  have hTK : CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M ≤ CGOf x :=
    sup_le (pCoreOf_le_self _) (Q_le_CGOf C hR hx)
  refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTK ht.1⟩) (fun k hk z hz => ?_)
    (isPGroup_of_le hT2 inf_le_left)
  exact Subgroup.mem_inf.2 ⟨sup_norm hk hz.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1
    hz.2) (M.inv_mem hk.1)⟩

theorem twoConstrained_P (hx1 : x ≠ 1) :
    CGOf x ⊓ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 (CGOf x) : Subgroup G) : Set G) ≤
      CFSG.Open.pCoreOf 2 (CGOf x) := by
  have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have hB2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) (Subgroup.zpowers_le.2 hx)
  exact centralizer_two_constrained C.S.charTwo hB hB2

theorem not_P_le_Q (hx1 : x ≠ 1) (hKM : ¬ CGOf x ≤ M) :
    ¬ CFSG.Open.pCoreOf 2 (CGOf x) ≤ CFSG.Open.pCoreOf 2 M := by
  intro hPQ
  apply hKM
  have hQK : CFSG.Open.pCoreOf 2 M ≤ CGOf x := Q_le_CGOf C hR hx
  have hcons := twoConstrained_P C hR hx hx1
  have hQP : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
    intro q hq
    apply hcons
    refine Subgroup.mem_inf.2 ⟨hQK hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact C.Q_comm hR p (hPQ hp) q hq
  have hPeq : CFSG.Open.pCoreOf 2 (CGOf x) = CFSG.Open.pCoreOf 2 M := le_antisymm hPQ hQP
  intro k hk
  rw [← C.S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
  intro q
  rw [← hPeq]
  refine ⟨fun hq => pCoreOf_normalized _ hk hq, fun hq => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) hq
  simpa [mul_assoc] using this

end CfgLemmas

section PiDataLemmas

variable {C : Cfg G M X 10} (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
  (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
  (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
include hR hx hI hπ

omit hR in
theorem x_ne_one : x ≠ 1 := by
  intro h
  subst h
  have h1 : D.piQ ⟨1, hx⟩ = 1 := by
    have : (⟨1, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := rfl
    rw [this, map_one]
  rw [h1, toAdd_one] at hπ
  have h2 := congrArg barLen hπ
  rw [barLen_barInd, hI, barLen_zero'] at h2
  norm_num at h2

omit hR in
theorem theta_normalized_of_normalized {U : Subgroup G} (hUM : U ≤ M)
    (hUn : ∀ k ∈ CMOf M x, ∀ u ∈ U, k * u * k⁻¹ ∈ U) {S : Finset (Fin 10)}
    (hS : S = I ∨ S = Iᶜ) :
    ∀ τ ∈ altOn S, ∀ σ ∈ (U.subgroupOf M).map C.θ, τ * σ * τ⁻¹ ∈ (U.subgroupOf M).map C.θ := by
  intro τ hτ σ hσ
  obtain ⟨c, hcC, hcθ⟩ := Subgroup.mem_map.1 (D.altOn_le_theta_CMOf hx (by omega) hπ hS hτ)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hσ
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcuU : (c : G) * (u : G) * (c : G)⁻¹ ∈ U := hUn _ hcC' _ (Subgroup.mem_subgroupOf.1 hu)
  refine Subgroup.mem_map.2 ⟨c * u * c⁻¹, Subgroup.mem_subgroupOf.2 hcuU, ?_⟩
  rw [map_mul, map_mul, map_inv, hcθ]

theorem sup_eq_TOf (hKM : ¬ CGOf x ≤ M) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x := by
  classical
  have hx1 : x ≠ 1 := x_ne_one D hx hI hπ
  have hH2 := isPGroup_sup C hR hx
  have hUT : (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M ≤ TOf M x :=
    sup_inf_le_TOf C hR hx
  have hPQ : ¬ CFSG.Open.pCoreOf 2 (CGOf x) ≤ CFSG.Open.pCoreOf 2 M :=
    not_P_le_Q C hR hx hx1 hKM
  have hQH : CFSG.Open.pCoreOf 2 M ≠ CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M :=
    fun h' => hPQ (by rw [h']; exact le_sup_left)
  obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
  have htM : t ∈ M := by rw [← C.S.normalizer_Q_eq]; exact htN
  have htU : t ∈ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M := ⟨htH, htM⟩
  have hUM : (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M ≤ M := inf_le_right
  have hUn : ∀ k ∈ CMOf M x, ∀ u ∈ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M,
      k * u * k⁻¹ ∈ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M := fun k hk u hu =>
    ⟨sup_norm hk hu.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.1 hk).1 hu.2)
      (M.inv_mem (Subgroup.mem_inf.1 hk).1)⟩
  have hθT := D.theta_TOf_len_four hR hx hI hπ
  have hF := klein4_fourGroup hI
  have hle : ((((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M).subgroupOf M).map
      C.θ) ≤ klein4 I := by
    rw [← hθT]
    exact Subgroup.map_mono fun m hm =>
      Subgroup.mem_subgroupOf.2 (hUT (Subgroup.mem_subgroupOf.1 hm))
  have hne : ((((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M).subgroupOf M).map
      C.θ) ≠ ⊥ := by
    intro hbot
    apply htQ
    have hmem : C.θ ⟨t, htM⟩ ∈
        ((((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M).subgroupOf M).map C.θ) :=
      Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 htU, rfl⟩
    rw [hbot] at hmem
    have hK : t ∈ C.K := C.mem_K.2 ⟨htM, Subgroup.mem_bot.1 hmem⟩
    rwa [C.K_eq_Q hR] at hK
  have hEq : ((((CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M).subgroupOf M).map
      C.θ) = klein4 I :=
    hF.eq_of_le hI hle hne (theta_normalized_of_normalized D hx hI hπ hUM hUn (Or.inl rfl))
  have hTU : TOf M x ≤ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M := by
    intro t' ht'
    have ht'M : t' ∈ M := TOf_le_M M _ ht'
    have hσ : C.θ ⟨t', ht'M⟩ ∈ klein4 I := by
      rw [← hθT]
      exact Subgroup.mem_map.2 ⟨⟨t', ht'M⟩, Subgroup.mem_subgroupOf.2 ht', rfl⟩
    rw [← hEq] at hσ
    obtain ⟨u, hu, hθ⟩ := Subgroup.mem_map.1 hσ
    have huU : (u : G) ∈ (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M :=
      Subgroup.mem_subgroupOf.1 hu
    have hM' : t' * (u : G)⁻¹ ∈ M := M.mul_mem ht'M (M.inv_mem u.2)
    have hdiv : t' * (u : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      have hθ1 : C.θ ⟨t' * (u : G)⁻¹, hM'⟩ = 1 := by
        have : (⟨t' * (u : G)⁻¹, hM'⟩ : ↥M) = ⟨t', ht'M⟩ * u⁻¹ := rfl
        rw [this, map_mul, map_inv, hθ, mul_inv_cancel]
      have hK : t' * (u : G)⁻¹ ∈ C.K := C.mem_K.2 ⟨hM', hθ1⟩
      rwa [C.K_eq_Q hR] at hK
    have hQU : CFSG.Open.pCoreOf 2 M ≤
        (CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M) ⊓ M :=
      le_inf le_sup_right (pCoreOf_le_self M)
    have e : t' = (t' * (u : G)⁻¹) * u := by group
    rw [e]
    exact Subgroup.mul_mem _ (hQU hdiv) huU
  have hTH : TOf M x ≤ CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M :=
    hTU.trans inf_le_left
  by_contra hne'
  obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hTH (Ne.symm hne')
  have hhM : h ∈ M := D.normalizer_TOf_le_M_len_four hR hx hI hπ hhN
  exact hhT (hUT ⟨hhH, hhM⟩)

theorem not_Q_le_P (hKM : ¬ CGOf x ≤ M) :
    ¬ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  intro hQP
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) = TOf M x := (sup_eq_left.2 hQP).symm.trans hsup
  apply hKM
  intro k hk
  apply D.normalizer_TOf_le_M_len_four hR hx hI hπ
  rw [Subgroup.mem_normalizer_iff]
  intro t
  rw [← hPT]
  refine ⟨fun ht => pCoreOf_normalized _ hk ht, fun ht => ?_⟩
  have := pCoreOf_normalized _ ((CGOf x).inv_mem hk) ht
  simpa [mul_assoc] using this

theorem theta_P_eq (hKM : ¬ CGOf x ≤ M) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ = klein4 I := by
  have hx1 : x ≠ 1 := x_ne_one D hx hI hπ
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M _)
  have hθT := D.theta_TOf_len_four hR hx hI hπ
  have hle : ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ ≤ klein4 I := by
    rw [← hθT]
    exact Subgroup.map_mono fun m hm =>
      Subgroup.mem_subgroupOf.2 (hPT (Subgroup.mem_subgroupOf.1 hm))
  have hne : ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ ≠ ⊥ := by
    intro hbot
    apply not_P_le_Q C hR hx hx1 hKM
    intro p hp
    have hpM : p ∈ M := hPM hp
    have hmem : C.θ ⟨p, hpM⟩ ∈ ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ :=
      Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
    rw [hbot] at hmem
    have hK : p ∈ C.K := C.mem_K.2 ⟨hpM, Subgroup.mem_bot.1 hmem⟩
    rwa [C.K_eq_Q hR] at hK
  exact (klein4_fourGroup hI).eq_of_le hI hle hne
    (theta_normalized_of_normalized D hx hI hπ hPM
      (fun k hk p hp => pCoreOf_normalized _ (Subgroup.mem_inf.1 hk).2 hp) (Or.inl rfl))

theorem center_P_le_Q (hKM : ¬ CGOf x ≤ M) {z : G}
    (hzP : z ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (hz : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * z = z * p) : z ∈ CFSG.Open.pCoreOf 2 M := by
  classical
  by_contra hzQ
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M _)
  have hzM : z ∈ M := hPM hzP
  have hθz : C.θ ⟨z, hzM⟩ ≠ 1 := fun h => hzQ (by
    have hK : z ∈ C.K := C.mem_K.2 ⟨hzM, h⟩
    rwa [C.K_eq_Q hR] at hK)
  have hθP := theta_P_eq D hR hx hI hπ hKM
  have hF := klein4_fourGroup hI
  have hzN : C.θ ⟨z, hzM⟩ ∈ klein4 I := by
    rw [← hθP]
    exact Subgroup.mem_map.2 ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hzP, rfl⟩
  have hNne : klein4 I ≠ ⊥ := fun h => hθz (Subgroup.mem_bot.1 (h ▸ hzN))
  obtain ⟨σ', hσ'N, hσ'1, hσ'z⟩ := hF.exists_ne hI hNne (C.θ ⟨z, hzM⟩)
  have hσ'P : σ' ∈ ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ := by
    rw [hθP]
    exact hσ'N
  obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 hσ'P
  have hpP : (pm : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := Subgroup.mem_subgroupOf.1 hpm
  obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨d', hd'I⟩ : Iᶜ.Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_compl, Fintype.card_fin, hI]; omega)
  have hd'fix : σ' d' = d' := hF.fix σ' hσ'N d' (Finset.mem_compl.1 hd'I)
  obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a d'
  have hqK : (q : G) ∈ CGOf x := Q_le_CGOf C hR hx q.2
  have hpq : (pm : G) * (q : G) * (pm : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M pm.2 q.2
  have hconj := D.piQ_conj pm q ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩ rfl
  let cq : ↥(CFSG.Open.pCoreOf 2 M) := q⁻¹ * ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩
  have hπc : Multiplicative.toAdd (D.piQ cq) = uvec a (σ' a) := by
    simp only [cq, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hconj, hpmσ, hq, barAct_uvec, hd'fix]
    exact neg_uvec_add_uvec a (σ' a) d'
  have hcP : (cq : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
    have e : (cq : G) = ((q : G)⁻¹ * (pm : G) * (q : G)) * (pm : G)⁻¹ := by
      show (q : G)⁻¹ * ((pm : G) * (q : G) * (pm : G)⁻¹) = _
      group
    have h3 : (q : G)⁻¹ * (pm : G) * (q : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
      have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hpP
      simpa using this
    rw [e]
    exact (CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem h3 ((CFSG.Open.pCoreOf 2 (CGOf x)).inv_mem hpP)
  have hzc : (cq : G) = z * (cq : G) * z⁻¹ := by
    have h1 := hz _ hcP
    calc (cq : G) = ((cq : G) * z) * z⁻¹ := by group
      _ = (z * (cq : G)) * z⁻¹ := by rw [h1]
  have h2 := D.piQ_conj ⟨z, hzM⟩ cq cq hzc
  rw [hπc] at h2
  exact hF.barAct_uvec_ne hI hzN hθz hσ'N hσ'1 (Ne.symm hσ'z) haI h2.symm

theorem rc_eq_bot (hKM : ¬ CGOf x ≤ M) : Rc X = ⊥ := by
  classical
  by_contra hRbot
  obtain ⟨⟨r0, hr0⟩, hr01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRbot
  have hr01' : r0 ≠ 1 := fun h => hr01 (Subtype.ext h)
  have hx1 : x ≠ 1 := x_ne_one D hx hI hπ
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M _)
  have hr0Q : r0 ∈ CFSG.Open.pCoreOf 2 M := by
    have h := hr0
    rw [C.S.R_eq_inf] at h
    exact (Subgroup.mem_inf.1 h).1
  have hr0K : r0 ∈ CGOf x := Q_le_CGOf C hR hx hr0Q
  have hcons := twoConstrained_P C hR hx hx1
  have hr0cent : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * r0 = r0 * p := by
    intro p hp
    have h1 := C.R_central hR p (hPM hp) r0 hr0
    calc p * r0 = (p * r0 * p⁻¹) * p := by group
      _ = r0 * p := by rw [h1]
  have hr0P : r0 ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
    hcons (Subgroup.mem_inf.2 ⟨hr0K, Subgroup.mem_centralizer_iff.2 hr0cent⟩)
  have hEQ : centerP x ≤ CFSG.Open.pCoreOf 2 M := fun z hz =>
    center_P_le_Q D hR hx hI hπ hKM hz.1 (fun p hp => Subgroup.mem_centralizer_iff.1 hz.2 p hp)
  have hr0E : r0 ∈ centerP x := Subgroup.mem_inf.2 ⟨hr0P, Subgroup.mem_centralizer_iff.2 hr0cent⟩
  have hKE : ∀ k ∈ CGOf x, ∀ e ∈ centerP x, k * e * k⁻¹ ∈ centerP x := fun k hk e he =>
    center_conj_mem (fun k hk p hp => pCoreOf_normalized _ hk hp) hk he
  have hKN : ∀ k ∈ CGOf x, k ∈ Subgroup.normalizer ((centerP x : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hKE k hk e he, fun he => ?_⟩
    have := hKE k⁻¹ ((CGOf x).inv_mem hk) _ he
    simpa [mul_assoc] using this
  have hCEM : Subgroup.centralizer ((centerP x : Subgroup G) : Set G) ≤ M := by
    intro c hc
    have h1 : r0 * c = c * r0 := Subgroup.mem_centralizer_iff.1 hc r0 hr0E
    have hl : barLen (Multiplicative.toAdd (D.piQ ⟨r0, hr0Q⟩)) ≠ 2 ∧
        barLen (Multiplicative.toAdd (D.piQ ⟨r0, hr0Q⟩)) ≠ 4 := by
      rw [(D.piQ_eq_one_iff ⟨r0, hr0Q⟩).2 hr0, toAdd_one, barLen_zero']
      exact ⟨by norm_num, by norm_num⟩
    exact (D.centralizer_le_of_len hR ⟨r0, hr0Q⟩ hr01' hl).1
      (Subgroup.mem_centralizer_singleton_iff.2 h1.symm)
  have hQC : CFSG.Open.pCoreOf 2 M ≤ Subgroup.centralizer ((centerP x : Subgroup G) : Set G) :=
    fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => C.Q_comm hR e (hEQ he) q hq
  have hQO : CFSG.Open.pCoreOf 2 M ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ((centerP x : Subgroup G) : Set G)) :=
    le_pCoreOf_of_normalized hQC (fun c hc q hq => pCoreOf_normalized M (hCEM hc) hq)
      (isPGroup_pCoreOf' M)
  have hnormC : ∀ n' ∈ CGOf x, ∀ c ∈ Subgroup.centralizer ((centerP x : Subgroup G) : Set G),
      n' * c * n'⁻¹ ∈ Subgroup.centralizer ((centerP x : Subgroup G) : Set G) :=
    fun n' hn' c hc => centralizer_normalized (hKN n' hn') hc
  have hB'P : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ((centerP x : Subgroup G) : Set G)) ⊓
      CGOf x ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
    refine le_pCoreOf_of_normalized inf_le_right (fun k hk b hb => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' _) inf_le_left)
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized_of_normal hnormC hk hb.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hb.2) ((CGOf x).inv_mem hk)⟩
  exact not_Q_le_P D hR hx hI hπ hKM fun q hq =>
    hB'P (Subgroup.mem_inf.2 ⟨hQO hq, Q_le_CGOf C hR hx hq⟩)

theorem DeltaJ_le_centerP (hKM : ¬ CGOf x ≤ M) (hrbot : Rc X = ⊥) {J : Finset (Fin 10)}
    (hJ : J ⊆ Iᶜ) : DeltaJ D J ≤ centerP x := by
  have hx1 : x ≠ 1 := x_ne_one D hx hI hπ
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hPT : CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x := le_sup_left.trans hsup.le
  have hPM : CFSG.Open.pCoreOf 2 (CGOf x) ≤ M := hPT.trans (TOf_le_M M _)
  have hθP := theta_P_eq D hR hx hI hπ hKM
  have hF := klein4_fourGroup hI
  have hcons := twoConstrained_P C hR hx hx1
  intro g hg
  obtain ⟨hgQ, -⟩ := (mem_DeltaJ D).1 hg
  have hgK : g ∈ CGOf x := Q_le_CGOf C hR hx hgQ
  have hcent : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * g = g * p := by
    intro p hp
    have hpM : p ∈ M := hPM hp
    have hσ : C.θ ⟨p, hpM⟩ ∈ klein4 I := by
      rw [← hθP]
      exact Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
    have h1 : p * g * p⁻¹ = g := centralizes_DeltaJ_of_fix D hrbot (J := J) (m := ⟨p, hpM⟩)
      (fun j hj => hF.fix _ hσ j (Finset.mem_compl.1 (hJ hj))) g hg
    calc p * g = (p * g * p⁻¹) * p := by group
      _ = g * p := by rw [h1]
  have hgP : g ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
    hcons (Subgroup.mem_inf.2 ⟨hgK, Subgroup.mem_centralizer_iff.2 hcent⟩)
  exact Subgroup.mem_inf.2 ⟨hgP, Subgroup.mem_centralizer_iff.2 hcent⟩

theorem centralizer_centerP_le_M (hKM : ¬ CGOf x ≤ M) (hrbot : Rc X = ⊥) :
    Subgroup.centralizer ((centerP x : Subgroup G) : Set G) ≤ M := by
  classical
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ Iᶜ.card by rw [Finset.card_compl, Fintype.card_fin, hI]; omega)
  have hJc : Jᶜ.card = 6 := by rw [Finset.card_compl, Fintype.card_fin, hJcard]
  have hDJ : DeltaJ D J ≤ centerP x := DeltaJ_le_centerP D hR hx hI hπ hKM hrbot hJsub
  exact (Subgroup.centralizer_le (show ((DeltaJ D J : Subgroup G) : Set G) ⊆
    ((centerP x : Subgroup G) : Set G) from hDJ)).trans
    (centralizer_DeltaJ_le_M D hR hrbot (by omega) (Or.inr (Or.inr (by omega))))

theorem pCore_centralizer_centerP_eq (hKM : ¬ CGOf x ≤ M) (hrbot : Rc X = ⊥) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ((centerP x : Subgroup G) : Set G)) = TOf M x := by
  have hx1 : x ≠ 1 := x_ne_one D hx hI hπ
  have hsup := sup_eq_TOf D hR hx hI hπ hKM
  have hCEM := centralizer_centerP_le_M D hR hx hI hπ hKM hrbot
  have hcons := twoConstrained_P C hR hx hx1
  have hEQ : centerP x ≤ CFSG.Open.pCoreOf 2 M := fun z hz =>
    center_P_le_Q D hR hx hI hπ hKM hz.1 (fun p hp => Subgroup.mem_centralizer_iff.1 hz.2 p hp)
  have hxE : x ∈ centerP x := by
    have hxK : x ∈ CGOf x := Q_le_CGOf C hR hx hx
    have hcentx : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * x = x * p := by
      intro p hp
      have h1 := mem_centralizer_zpowers_iff.1 (pCoreOf_le_self _ hp)
      calc p * x = (p * x * p⁻¹) * p := by group
        _ = x * p := by rw [h1]
    exact Subgroup.mem_inf.2
      ⟨hcons (Subgroup.mem_inf.2 ⟨hxK, Subgroup.mem_centralizer_iff.2 hcentx⟩),
        Subgroup.mem_centralizer_iff.2 hcentx⟩
  have hmemC : ∀ c : G, c ∈ Subgroup.centralizer ((centerP x : Subgroup G) : Set G) →
      c ∈ CMOf M x := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨hCEM hc, mem_centralizer_zpowers_iff.2 ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hc x hxE
    calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [h1]
      _ = x := by group
  apply le_antisymm
  · refine le_pCoreOf_of_normalized
      (fun t ht => hmemC t (pCoreOf_le_self _ ht)) (fun c hc t ht => ?_) (isPGroup_pCoreOf' _)
    exact pCoreOf_normalized_of_normal (fun n' hn' k hk => centralizer_normalized hn' hk)
      (mem_normalizer_centerP (Subgroup.mem_inf.1 hc).2) ht
  · refine le_pCoreOf_of_normalized ?_
      (fun c hc t ht => normalized_TOf M x (hmemC c hc) ht) (isPGroup_TOf M x)
    rw [← hsup]
    refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.2 fun e he => ?_)
      (fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => C.Q_comm hR e (hEQ he) q hq)
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 he).2 p hp).symm

theorem normalizer_centerP_le_M (hKM : ¬ CGOf x ≤ M) (hrbot : Rc X = ⊥) :
    Subgroup.normalizer ((centerP x : Subgroup G) : Set G) ≤ M := by
  intro g hg
  have hgT : g ∈ Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← pCore_centralizer_centerP_eq D hR hx hI hπ hKM hrbot]
    refine ⟨fun ht => pCoreOf_normalized_of_normal
      (fun n' hn' k hk => centralizer_normalized hn' hk) hg ht, fun ht => ?_⟩
    have := pCoreOf_normalized_of_normal (fun n' hn' k hk => centralizer_normalized hn' hk)
      ((Subgroup.normalizer _).inv_mem hg) ht
    simpa [mul_assoc] using this
  exact D.normalizer_TOf_le_M_len_four hR hx hI hπ hgT

theorem centralizer_le_M_aux : CGOf x ≤ M := by
  by_contra hKM
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  apply hKM
  intro k hk
  exact normalizer_centerP_le_M D hR hx hI hπ hKM hrbot (mem_normalizer_centerP hk)

end PiDataLemmas

end Four

section Fusion

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem CGOf_conj (g x : G) : CGOf (g * x * g⁻¹) = conjSubgroup g (CGOf x) := by
  ext z
  rw [mem_conjSubgroup]
  show z ∈ Subgroup.centralizer ((Subgroup.zpowers (g * x * g⁻¹) : Subgroup G) : Set G) ↔
    g⁻¹ * z * g ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
  rw [mem_centralizer_zpowers_iff, mem_centralizer_zpowers_iff]
  constructor
  · intro h
    calc g⁻¹ * z * g * x * (g⁻¹ * z * g)⁻¹ = g⁻¹ * (z * (g * x * g⁻¹) * z⁻¹) * g := by group
      _ = x := by rw [h]; group
  · intro h
    calc z * (g * x * g⁻¹) * z⁻¹ = g * ((g⁻¹ * z * g) * x * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [h]

theorem conj_pCoreOf_le (g : G) (H : Subgroup G) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 H) ≤ CFSG.Open.pCoreOf 2 (conjSubgroup g H) := by
  refine le_pCoreOf_of_normalized (Subgroup.map_mono (pCoreOf_le_self H)) (fun k hk u hu => ?_)
    ((isPGroup_pCoreOf' H).map _)
  have hk' : g⁻¹ * k * g ∈ H := mem_conjSubgroup.1 hk
  have hu' : g⁻¹ * u * g ∈ CFSG.Open.pCoreOf 2 H := mem_conjSubgroup.1 hu
  refine mem_conjSubgroup.2 ?_
  have e : g⁻¹ * (k * u * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * u * g) * (g⁻¹ * k * g)⁻¹ := by group
  rw [e]
  exact pCoreOf_normalized H hk' hu'

theorem CGOf_eq_of_mem_R {n : ℕ} {C : Cfg G M X n} (hR : Nat.card ↥(Rc X) ≤ 2) {x y : G}
    (hxC : CGOf x ≤ M) (hyC : CGOf y ≤ M) {r : G} (hr : r ∈ Rc X) (hxy : y = x * r) :
    CGOf y = CGOf x := by
  ext k
  constructor
  · intro hk
    have hkM : k ∈ M := hyC hk
    have hky : k * y * k⁻¹ = y := mem_centralizer_zpowers_iff.1 hk
    have hkr : k * r * k⁻¹ = r := C.R_central hR k hkM r hr
    refine mem_centralizer_zpowers_iff.2 ?_
    have hx' : x = y * r⁻¹ := by rw [hxy]; group
    calc k * x * k⁻¹ = (k * y * k⁻¹) * (k * r * k⁻¹)⁻¹ := by rw [hx']; group
      _ = y * r⁻¹ := by rw [hky, hkr]
      _ = x := hx'.symm
  · intro hk
    have hkM : k ∈ M := hxC hk
    have hkx : k * x * k⁻¹ = x := mem_centralizer_zpowers_iff.1 hk
    have hkr : k * r * k⁻¹ = r := C.R_central hR k hkM r hr
    refine mem_centralizer_zpowers_iff.2 ?_
    calc k * y * k⁻¹ = (k * x * k⁻¹) * (k * r * k⁻¹) := by rw [hxy]; group
      _ = x * r := by rw [hkx, hkr]
      _ = y := hxy.symm

section CfgLemmas

variable {n : ℕ} (C : Cfg G M X n)

@[expose] def barStab (v : permBar n) : Subgroup ↥M where
  carrier := {m | barAct (C.θ m) v = v}
  mul_mem' := by
    intro a b ha hb
    show barAct (C.θ (a * b)) v = v
    have ha' : barAct (C.θ a) v = v := ha
    have hb' : barAct (C.θ b) v = v := hb
    rw [map_mul, barAct_mul, hb', ha']
  one_mem' := by
    show barAct (C.θ 1) v = v
    rw [map_one, barAct_one]
  inv_mem' := by
    intro a ha
    show barAct (C.θ a⁻¹) v = v
    have ha' : barAct (C.θ a) v = v := ha
    calc barAct (C.θ a⁻¹) v = barAct (C.θ a)⁻¹ (barAct (C.θ a) v) := by rw [map_inv, ha']
      _ = v := by rw [← barAct_mul, inv_mul_cancel, barAct_one]

theorem card_M_eq_orbit_mul (v : permBar n) :
    Nat.card ↥M = Set.ncard {u : permBar n | ∃ m : ↥M, barAct (C.θ m) v = u} *
      Nat.card ↥(barStab C v) := by
  letI : MulAction ↥M (permBar n) := MulAction.compHom (permBar n) ((barPerm n).comp C.θ)
  have hstab : MulAction.stabilizer ↥M v = barStab C v := by
    ext m
    rw [MulAction.mem_stabilizer_iff]
    rfl
  have horb : MulAction.orbit ↥M v = {u : permBar n | ∃ m : ↥M, barAct (C.θ m) v = u} := by
    ext u
    rfl
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥M v)
  rw [MulAction.index_stabilizer, hstab, horb] at h1
  rw [← h1, mul_comm]

include C in
theorem Rc_le_M : Rc X ≤ M := by
  rw [C.S.R_eq_inf]
  exact inf_le_left.trans (pCoreOf_le_self M)

end CfgLemmas

section CfgLemmasTen

variable (C : Cfg G M X 10)

theorem orbit_eq_barLen {v : permBar 10} {l : ℕ} (hl : l = 2 ∨ l = 4) (hv : barLen v = l) :
    {u : permBar 10 | ∃ m : ↥M, barAct (C.θ m) v = u} = {u : permBar 10 | barLen u = l} := by
  ext u
  constructor
  · rintro ⟨m, rfl⟩
    show barLen (barAct (C.θ m) v) = l
    rw [barLen_barAct, hv]
  · intro hu
    have hu' : barLen u = l := hu
    obtain ⟨σ, hσA, hσ⟩ : ∃ σ ∈ alternatingGroup (Fin 10), barAct σ v = u := by
      rcases hl with rfl | rfl
      · exact exists_alt_barAct_eq_of_barLen_two hv hu'
      · exact exists_alt_barAct_eq_of_barLen_four hv hu'
    obtain ⟨c, hc⟩ := C.exists_lift hσA
    exact ⟨⟨(c : G), C.S.le c.2⟩, by rw [show C.θ ⟨(c : G), C.S.le c.2⟩ = σ from hc]; exact hσ⟩

theorem card_M_eq_four {v : permBar 10} (hv : barLen v = 4) :
    Nat.card ↥M = 210 * Nat.card ↥(barStab C v) := by
  have h : Set.ncard {u : permBar 10 | barLen u = 4} = 210 := by
    rw [← Nat.card_coe_set_eq]
    exact card_barLen_four
  rw [card_M_eq_orbit_mul C v, orbit_eq_barLen C (Or.inr rfl) hv, h]

theorem card_M_eq_two {v : permBar 10} (hv : barLen v = 2) :
    Nat.card ↥M = 45 * Nat.card ↥(barStab C v) := by
  have h : Set.ncard {u : permBar 10 | barLen u = 2} = 45 := by
    rw [← Nat.card_coe_set_eq]
    exact card_barLen_two
  rw [card_M_eq_orbit_mul C v, orbit_eq_barLen C (Or.inl rfl) hv, h]

end CfgLemmasTen

theorem comm_mul_of_central {m m' y ra rb : G} (hra : ra = m * y * m⁻¹ * y⁻¹)
    (hrb : rb = m' * y * m'⁻¹ * y⁻¹) (hc1 : m * rb * m⁻¹ = rb) (hcomm : rb * ra = ra * rb) :
    m * m' * y * (m * m')⁻¹ * y⁻¹ = ra * rb := by
  calc m * m' * y * (m * m')⁻¹ * y⁻¹ = (m * rb * m⁻¹) * ra := by rw [hra, hrb]; group
    _ = rb * ra := by rw [hc1]
    _ = ra * rb := hcomm

section PiDataLemmas

variable {n : ℕ} {C : Cfg G M X n} (D : C.PiData)

theorem card_CMOf_le_barStab (x : ↥(CFSG.Open.pCoreOf 2 M)) :
    Nat.card ↥(CMOf M (x : G)) ≤ Nat.card ↥(barStab C (Multiplicative.toAdd (D.piQ x))) := by
  have hle : (CMOf M (x : G)).subgroupOf M ≤ barStab C (Multiplicative.toAdd (D.piQ x)) := by
    intro m hm
    have hc : (m : G) * (x : G) * (m : G)⁻¹ = x :=
      mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hm)).2
    exact (D.piQ_conj m x x hc.symm).symm
  have h1 : Nat.card ↥((CMOf M (x : G)).subgroupOf M) = Nat.card ↥(CMOf M (x : G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1]
  exact Subgroup.card_le_of_le hle

theorem card_barStab_le (hR : Nat.card ↥(Rc X) ≤ 2) (y : ↥(CFSG.Open.pCoreOf 2 M)) :
    Nat.card ↥(barStab C (Multiplicative.toAdd (D.piQ y))) ≤ Nat.card ↥(CMOf M (y : G)) * 2 := by
  classical
  set v := Multiplicative.toAdd (D.piQ y) with hv
  have hmem : ∀ m : ↥(barStab C v),
      ((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹ * (y : G)⁻¹ ∈ Rc X := by
    intro m
    have hmyQ : ((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      pCoreOf_normalized M (m : ↥M).2 y.2
    have hQ' : ((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹ * (y : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem hmyQ ((CFSG.Open.pCoreOf 2 M).inv_mem y.2)
    have h1 : D.piQ ⟨((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹, hmyQ⟩ = D.piQ y := by
      apply Multiplicative.toAdd.injective
      rw [D.piQ_conj (m : ↥M) y _ rfl]
      exact m.2
    have h2 : D.piQ ⟨_, hQ'⟩ = 1 := by
      have e : (⟨_, hQ'⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
          ⟨((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹, hmyQ⟩ * y⁻¹ := rfl
      rw [e, map_mul, map_inv, h1, mul_inv_cancel]
    exact (D.piQ_eq_one_iff _).1 h2
  let f : ↥(barStab C v) →* ↥(Rc X) :=
    { toFun := fun m =>
        ⟨((m : ↥M) : G) * (y : G) * ((m : ↥M) : G)⁻¹ * (y : G)⁻¹, hmem m⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hra := hmem a
        have hrb := hmem b
        have hc1 := C.R_central hR _ (a : ↥M).2 _ hrb
        have hc2 := C.R_central hR _ (Rc_le_M C hrb) _ hra
        exact comm_mul_of_central rfl rfl hc1 (mul_inv_eq_iff_eq_mul.1 hc2) }
  have hker : Nat.card f.ker ≤ Nat.card ↥(CMOf M (y : G)) := by
    refine Nat.card_le_card_of_injective
      (fun m : f.ker => (⟨(((m : ↥(barStab C v)) : ↥M) : G), ?_⟩ : ↥(CMOf M (y : G)))) ?_
    · refine Subgroup.mem_inf.2 ⟨((m : ↥(barStab C v)) : ↥M).2,
        mem_centralizer_zpowers_iff.2 ?_⟩
      have h1 : f (m : ↥(barStab C v)) = 1 := m.2
      have h2 : (((m : ↥(barStab C v)) : ↥M) : G) * (y : G) *
          (((m : ↥(barStab C v)) : ↥M) : G)⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val h1
      exact mul_inv_eq_one.1 h2
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hrange : Nat.card f.range ≤ 2 :=
    (Nat.card_le_card_of_injective (fun r : f.range => (r : ↥(Rc X))) Subtype.val_injective).trans
      hR
  have hcard := Subgroup.card_ker_mul_card_range f
  calc Nat.card ↥(barStab C v) = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ Nat.card ↥(CMOf M (y : G)) * 2 := Nat.mul_le_mul hker hrange

end PiDataLemmas

section PiDataLemmasTen

variable {C : Cfg G M X 10} (D : C.PiData)

theorem card_TOf_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 10)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Nat.card ↥(TOf M x) = Nat.card ↥(CFSG.Open.pCoreOf 2 M) * 4 := by
  have h := C.card_eq_card_inf_mul hR (TOf_le_M M x)
  rw [inf_eq_right.2 (Q_le_TOf (C.Q_comm hR) hx), D.theta_TOf_len_four hR hx hI hπ,
    card_klein4 hI] at h
  exact h

theorem exists_supp_four {v : permBar 10} (hl : barLen v = 4) :
    ∃ I : Finset (Fin 10), I.card = 4 ∧ v = barInd I := by
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len v
  exact ⟨I, hl ▸ hIc, hI⟩

theorem CGOf_le_M_of_len_four (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) : CGOf (x : G) ≤ M := by
  obtain ⟨I, hIc, hI⟩ := exists_supp_four hl
  exact centralizer_le_M_aux D hR x.2 hIc hI

theorem len_ne_two_of_conj (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) {g : G}
    (y : ↥(CFSG.Open.pCoreOf 2 M)) (hy : (y : G) = g * (x : G) * g⁻¹) :
    barLen (Multiplicative.toAdd (D.piQ y)) ≠ 2 := by
  intro hl2
  have hxC : CGOf (x : G) ≤ M := CGOf_le_M_of_len_four D hR x hl
  have hCMx : CMOf M (x : G) = CGOf (x : G) := inf_eq_right.2 hxC
  have hc1 : Nat.card ↥(CGOf (y : G)) = Nat.card ↥(CGOf (x : G)) := by
    rw [hy, CGOf_conj]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc2 : Nat.card ↥(CMOf M (y : G)) ≤ Nat.card ↥(CGOf (y : G)) :=
    Subgroup.card_le_of_le inf_le_right
  have h4 := card_M_eq_four C hl
  have h2 := card_M_eq_two C hl2
  have h3 := card_CMOf_le_barStab D x
  have h5 := card_barStab_le D hR y
  rw [hCMx] at h3
  have hpos : 0 < Nat.card ↥M := Nat.card_pos
  omega

theorem len_eq_two_or_four_of_conj (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) {g : G}
    (y : ↥(CFSG.Open.pCoreOf 2 M)) (hy : (y : G) = g * (x : G) * g⁻¹) :
    barLen (Multiplicative.toAdd (D.piQ y)) = 2 ∨ barLen (Multiplicative.toAdd (D.piQ y)) = 4 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨I, hIc, hπ⟩ := exists_supp_four hl
  have hx1 : (x : G) ≠ 1 := x_ne_one D x.2 hIc hπ
  have hy1 : (y : G) ≠ 1 := by
    intro h
    apply hx1
    rw [hy] at h
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this
  have hxC : CGOf (x : G) ≤ M := CGOf_le_M_of_len_four D hR x hl
  have hCMx : CMOf M (x : G) = CGOf (x : G) := inf_eq_right.2 hxC
  have hY := (D.centralizer_le_of_len hR y hy1 hcon).2
  have hY' : CFSG.Open.pCoreOf 2 (CGOf (y : G)) = CFSG.Open.pCoreOf 2 M := by
    rwa [centralizer_singleton_eq_zpowers] at hY
  have hTx : TOf M (x : G) = CFSG.Open.pCoreOf 2 (CGOf (x : G)) := by
    show CFSG.Open.pCoreOf 2 (CMOf M (x : G)) = _
    rw [hCMx]
  have hle : conjSubgroup g (TOf M (x : G)) ≤ CFSG.Open.pCoreOf 2 M := by
    rw [hTx]
    refine (conj_pCoreOf_le g (CGOf (x : G))).trans ?_
    rw [← CGOf_conj, ← hy, hY']
  have hcard1 := Subgroup.card_le_of_le hle
  have hcard2 : Nat.card ↥(conjSubgroup g (TOf M (x : G))) = Nat.card ↥(TOf M (x : G)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard3 := card_TOf_len_four D hR x.2 hIc hπ
  have hpos : 0 < Nat.card ↥(CFSG.Open.pCoreOf 2 M) := Nat.card_pos
  omega

theorem mem_M_of_conj_of_len_four (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) {g : G}
    (y : ↥(CFSG.Open.pCoreOf 2 M)) (hy : (y : G) = g * (x : G) * g⁻¹)
    (hl4 : barLen (Multiplicative.toAdd (D.piQ y)) = 4) : g ∈ M := by
  obtain ⟨I, hIc, hπ⟩ := exists_supp_four hl
  have hxC : CGOf (x : G) ≤ M := CGOf_le_M_of_len_four D hR x hl
  have hCMx : CMOf M (x : G) = CGOf (x : G) := inf_eq_right.2 hxC
  obtain ⟨σ, hσA, hσ⟩ := exists_alt_barAct_eq_of_barLen_four
    (u := Multiplicative.toAdd (D.piQ y)) (v := Multiplicative.toAdd (D.piQ x)) hl4 hl
  obtain ⟨c, hcθ⟩ := C.exists_lift hσA
  have hcM : (c : G) ∈ M := C.S.le c.2
  have hy'Q : (c : G) * (y : G) * (c : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M hcM y.2
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(CFSG.Open.pCoreOf 2 M), (y' : G) = (c : G) * (y : G) * (c : G)⁻¹ :=
    ⟨⟨_, hy'Q⟩, rfl⟩
  have hπy' : Multiplicative.toAdd (D.piQ y') = Multiplicative.toAdd (D.piQ x) := by
    rw [D.piQ_conj ⟨(c : G), hcM⟩ y y' hy', show C.θ ⟨(c : G), hcM⟩ = σ from hcθ, hσ]
  have hy'C : CGOf (y' : G) ≤ M :=
    CGOf_le_M_of_len_four D hR y' (by rw [hπy']; exact hl)
  have hr : (x : G)⁻¹ * (y' : G) ∈ Rc X := by
    have h1 : D.piQ (x⁻¹ * y') = 1 := by
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_one, hπy']
      exact neg_add_cancel _
    exact (D.piQ_eq_one_iff _).1 h1
  have hCeq : CGOf (y' : G) = CGOf (x : G) :=
    CGOf_eq_of_mem_R (C := C) hR hxC hy'C hr (by group)
  have hg'x : ((c : G) * g) * (x : G) * ((c : G) * g)⁻¹ = (y' : G) := by
    rw [hy', hy]
    group
  have hconj : conjSubgroup ((c : G) * g) (CGOf (x : G)) = CGOf (x : G) := by
    rw [← CGOf_conj, hg'x, hCeq]
  have hg'N : (c : G) * g ∈ Subgroup.normalizer ((CGOf (x : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro z
    rw [← mem_conjSubgroup, hconj]
  have hnormK : ∀ n ∈ Subgroup.normalizer ((CGOf (x : G) : Subgroup G) : Set G),
      ∀ k ∈ CGOf (x : G), n * k * n⁻¹ ∈ CGOf (x : G) :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  have hTx : TOf M (x : G) = CFSG.Open.pCoreOf 2 (CGOf (x : G)) := by
    show CFSG.Open.pCoreOf 2 (CMOf M (x : G)) = _
    rw [hCMx]
  have hg'T : (c : G) * g ∈ Subgroup.normalizer ((TOf M (x : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hTx]
    refine ⟨fun ht => pCoreOf_normalized_of_normal hnormK hg'N ht, fun ht => ?_⟩
    have := pCoreOf_normalized_of_normal hnormK ((Subgroup.normalizer _).inv_mem hg'N) ht
    simpa [mul_assoc] using this
  have hg'M : (c : G) * g ∈ M := D.normalizer_TOf_le_M_len_four hR x.2 hIc hπ hg'T
  have e : g = (c : G)⁻¹ * ((c : G) * g) := by group
  rw [e]
  exact M.mul_mem (M.inv_mem hcM) hg'M

end PiDataLemmasTen

end Fusion

end H4b

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10} (D : C.PiData)

theorem centralizer_le_M_of_len_four (hR : Nat.card ↥(Rc X) ≤ 2)
    (x : ↥(CFSG.Open.pCoreOf 2 M)) (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) :
    Subgroup.centralizer ({(x : G)} : Set G) ≤ M := by
  rw [centralizer_singleton_eq_zpowers]
  exact H4b.CGOf_le_M_of_len_four D hR x hl

theorem mem_M_of_conj_len_four (hR : Nat.card ↥(Rc X) ≤ 2) (x : ↥(CFSG.Open.pCoreOf 2 M))
    (hl : barLen (Multiplicative.toAdd (D.piQ x)) = 4) {g : G}
    (hg : g * (x : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  obtain ⟨y, hy⟩ : ∃ y : ↥(CFSG.Open.pCoreOf 2 M), (y : G) = g * (x : G) * g⁻¹ :=
    ⟨⟨_, hg⟩, rfl⟩
  rcases H4b.len_eq_two_or_four_of_conj D hR x hl y hy with h2 | h4
  · exact absurd h2 (H4b.len_ne_two_of_conj D hR x hl y hy)
  · exact H4b.mem_M_of_conj_of_len_four D hR x hl y hy h4

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
