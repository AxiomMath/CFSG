module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31b
public import CFSG.Quasithin.Vol2.Ch12Sec6L33f

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G]

section ConjOn

variable {Q : Type*} [Group Q]

@[expose] def conjOn (X Y : Subgroup Q) (hY : Y ≤ Subgroup.normalizer (X : Set Q)) :
    ↥Y →* MulAut ↥X where
  toFun y :=
    { toFun := fun x => ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.1 (hY y.2) x).1 x.2⟩
      invFun := fun x => ⟨(y : Q)⁻¹ * x * y, by
        have := (Subgroup.mem_normalizer_iff.1 (hY (Y.inv_mem y.2)) x).1 x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' a b := MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (X Y : Subgroup Q) (hY : Y ≤ Subgroup.normalizer (X : Set Q)) (y : ↥Y)
    (x : ↥X) : ((conjOn X Y hY y x : ↥X) : Q) = y * x * y⁻¹ := rfl

end ConjOn

section Star

variable [Finite G] {H : Subgroup G}

theorem isSylowTwoOf_star {T : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H) :
    QuasithinUnique.IsSylowTwoOf (star H T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 ↥H :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2
  let T'' : Sylow 2 (HStar H) := T'.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H))
  have he : (T'' : Subgroup (HStar H)) = star H T := rfl
  refine ⟨le_top, he ▸ T''.isPGroup', ?_⟩
  show ¬ 2 ∣ (star H T).relIndex ⊤
  rw [Subgroup.relIndex_top_right, ← he]
  exact T''.not_dvd_index

omit [Finite G] in
theorem pCoreOf_le_of_isSylowTwoOf {T : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 ↥H :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2
  have h1 : CFSG.Open.pCore 2 ↥H ≤ T' := by
    have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal T'
  rintro _ ⟨x, hx, rfl⟩
  exact h1 hx

omit [Finite G] in
theorem not_le_star_M {L K : Subgroup G} (hKH : K ≤ H)
    (hQ : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G))
    (hK : ¬ K ≤ Subgroup.normalizer (L : Set G)) :
    ¬ star H K ≤ star H (Subgroup.normalizer (L : Set G) ⊓ H) := by
  intro hle
  apply hK
  intro k hk
  obtain ⟨m, hm, he⟩ := hle (mk_mem_star (h := ⟨k, hKH hk⟩) hk)
  have hq := F126.mem_pCoreOf_of_mk_eq he
  have hmL : (m : G) ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_subgroupOf.1 hm).1
  have : k = m * ((m : G)⁻¹ * k) := by group
  rw [this]
  exact Subgroup.mul_mem _ hmL (hQ hq)

omit [Finite G] in
theorem le_normalizer_pre {Y : Subgroup G} (hYH : Y ≤ H) {Z : Subgroup (HStar H)}
    (hYZ : star H Y ≤ Subgroup.normalizer (Z : Set (HStar H))) :
    Y ≤ Subgroup.normalizer (pre H Z : Set G) := by
  intro y hy
  have hyH := hYH hy
  have hyN := Subgroup.mem_normalizer_iff.1 (hYZ (mk_mem_star (h := ⟨y, hyH⟩) hy))
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hmk : ∀ (hgH : g ∈ H) (hm : y * g * y⁻¹ ∈ H),
      (QuotientGroup.mk ⟨y * g * y⁻¹, hm⟩ : HStar H) =
        QuotientGroup.mk ⟨y, hyH⟩ * QuotientGroup.mk ⟨g, hgH⟩ * (QuotientGroup.mk ⟨y, hyH⟩)⁻¹ :=
    fun hgH hm => by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  constructor
  · intro hg
    obtain ⟨hgH, hgZ⟩ := mem_pre.1 hg
    have hm : y * g * y⁻¹ ∈ H := H.mul_mem (H.mul_mem hyH hgH) (H.inv_mem hyH)
    refine mem_pre.2 ⟨hm, ?_⟩
    rw [hmk hgH hm]
    exact (hyN _).1 hgZ
  · intro hg
    obtain ⟨hgH', hgZ⟩ := mem_pre.1 hg
    have hgH : g ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hyH) hgH') hyH
      simpa [mul_assoc] using this
    refine mem_pre.2 ⟨hgH, (hyN _).2 ?_⟩
    rw [← hmk hgH hgH']
    exact hgZ

omit [Finite G] in
theorem relIndex_star {A B : Subgroup G} (hQA : pCoreOf 2 H ≤ A) (hAB : A ≤ B) (hBH : B ≤ H) :
    (star H A).relIndex (star H B) = A.relIndex B := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker ≤ A.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hQA ⟨q, by assumption, rfl⟩
  unfold S126.star
  rw [Subgroup.relIndex_map_map, sup_of_le_left hker,
    sup_of_le_left (hker.trans fun x hx => hAB hx),
    Subgroup.relIndex_subgroupOf hBH]

end Star

section CaseTwo

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V] {H K : Subgroup G}

omit [IsMulCommutative ↥V] in
theorem card_star_K₀ (hH : Hyp126 G T L V) {V₁ Vp : Subgroup G} (h918 : HypF918 T V L V₁ Vp H K)
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(star H (conjClosure K T)) = 3600 := by
  rw [Nat.card_congr (equivK₀ hH h918 e₁ ht₀ ht₀K).toEquiv, Nat.card_prod,
    S126.card_alternatingGroup_five]

theorem inf_star_M_eq_borel (h1229 : Lemma12_6_29) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hHK : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5))
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    star H (Subgroup.normalizer (L : Set G) ⊓ H) ⊓ star H (conjClosure K T) =
      borel (star H (conjClosure K T)) (star H T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  set K0s := star H (conjClosure K T) with hK0s
  set Ks := star H K with hKs
  set K2s := star H (conjSub t₀ K) with hK2s
  set Ts := star H T with hTs
  set Ms := star H (Subgroup.normalizer (L : Set G) ⊓ H) with hMs
  have hK0n : K0s.Normal := normal_star h918.K₀_normal
  have hTsN : Ts ≤ Subgroup.normalizer (K0s : Set (HStar H)) := Subgroup.le_normalizer_of_normal
  have hSs : QuasithinUnique.IsSylowTwoOf (Ts ⊓ K0s) K0s :=
    A4.isSylowTwoOf_inf_normal hsylTs le_top Subgroup.le_normalizer_of_normal
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le_of_isSylowTwoOf hsylT).trans hH.hyp.normalizes
  have hTsM : Ts ≤ Ms := star_mono (le_inf hH.hyp.normalizes hTH)
  have hBM : borel K0s Ts ≤ Ms := le_sup_right.trans (le_star_M h1229 F hH hZ hTH
    (pCoreOf_ne_bot h) le_sup_left (isSolvable_sup_borel hsylTs.2.1 hTsN hSs))
  refine le_antisymm ?_ (le_inf hBM inf_le_left)
  obtain ⟨hc, hi⟩ := commute_pair h918 e₁ ht₀ ht₀K
  have hsup : K0s = Ks ⊔ K2s := star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K
  have e₂ := equivConjSub e₁ (hTH ht₀)
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥Ks := e₁.isSimpleGroup
  have hsK₂ : IsSimpleGroup ↥K2s := e₂.isSimpleGroup
  have hKsK0 : Ks ≤ K0s := hsup ▸ le_sup_left
  have hK2sK0 : K2s ≤ K0s := hsup ▸ le_sup_right
  have hK2C : K2s ≤ Subgroup.centralizer (Ks : Set (HStar H)) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hc x hx y hy
  have hKC : Ks ≤ Subgroup.centralizer (K2s : Set (HStar H)) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm
  have hK0N1 : K0s ≤ Subgroup.normalizer (Ks : Set (HStar H)) := hsup ▸
    sup_le Subgroup.le_normalizer (hK2C.trans (Subgroup.centralizer_le_normalizer _))
  have hK0N2 : K0s ≤ Subgroup.normalizer (K2s : Set (HStar H)) := hsup ▸
    sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  set S := Ts ⊓ K0s with hS
  have hS₁ : QuasithinUnique.IsSylowTwoOf (S ⊓ Ks) Ks := A4.isSylowTwoOf_inf_normal hSs hKsK0 hK0N1
  have hS₂ : QuasithinUnique.IsSylowTwoOf (S ⊓ K2s) K2s :=
    A4.isSylowTwoOf_inf_normal hSs hK2sK0 hK0N2
  have hcS : ∀ x ∈ S ⊓ Ks, ∀ y ∈ S ⊓ K2s, x * y = y * x := fun x hx y hy => hc x hx.2 y hy.2
  have hiS : (S ⊓ Ks) ⊓ (S ⊓ K2s) = ⊥ := le_bot_iff.1 (hi ▸ inf_le_inf inf_le_right inf_le_right)
  have hcardS : Nat.card S = 16 := by
    have h1 := (hSs.2.1.comap_subtype.toSylow hSs.2.2).card_eq_multiplicity
    rw [card_star_K₀ hH h918 e₁ ht₀ ht₀K,
      L1233.factorization_two_eq (k := 4) (by norm_num) (by norm_num) (by norm_num)] at h1
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSs.1).toEquiv]
    exact h1
  have hSeq : S = (S ⊓ Ks) ⊔ (S ⊓ K2s) := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
    rw [L1233.card_sup_of_commute hcS hiS, card_sylow_of_alt5 e₁ hS₁,
      card_sylow_of_alt5 e₂ hS₂, hcardS]
  have hB₁ : Ks ⊓ Subgroup.normalizer ((S ⊓ Ks : Subgroup (HStar H)) : Set (HStar H)) ≤
      borel K0s Ts := by
    rintro x ⟨hxK, hxN⟩
    refine ⟨hKsK0 hxK, ?_⟩
    show x ∈ Subgroup.normalizer ((S : Subgroup (HStar H)) : Set (HStar H))
    rw [hSeq]
    refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hxN, ?_⟩
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy =>
      (hc x hxK y hy.2).symm)
  have hB₂ : K2s ⊓ Subgroup.normalizer ((S ⊓ K2s : Subgroup (HStar H)) : Set (HStar H)) ≤
      borel K0s Ts := by
    rintro x ⟨hxK, hxN⟩
    refine ⟨hK2sK0 hxK, ?_⟩
    show x ∈ Subgroup.normalizer ((S : Subgroup (HStar H)) : Set (HStar H))
    rw [hSeq]
    refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, hxN⟩
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy =>
      hc y hy.2 x hxK)
  have hKM : ¬ Ks ≤ Ms := not_le_star_M (le_of_mem_cComp h918.K_cComp) hQM hHK.2.1
  have hK2M : ¬ K2s ≤ Ms := by
    intro hle
    apply hKM
    intro k hk
    set tb : HStar H := QuotientGroup.mk ⟨t₀, hTH ht₀⟩ with htb
    have htbM : tb ∈ Ms := hTsM (mk_mem_star ht₀)
    have h1 : tb * k * tb⁻¹ ∈ K2s := by
      rw [hK2s, L1233.star_conjSub (hTH ht₀)]
      exact ⟨k, hk, rfl⟩
    have h2 := Ms.mul_mem (Ms.mul_mem (Ms.inv_mem htbM) (hle h1)) htbM
    simpa [mul_assoc] using h2
  have hne : ∀ {X : Subgroup (HStar H)} {S' : Subgroup (HStar H)}
      (_ : ↥X ≃* alternatingGroup (Fin 5)) (_ : QuasithinUnique.IsSylowTwoOf S' X),
      X ⊓ Subgroup.normalizer (S' : Set (HStar H)) ≠ ⊥ := by
    intro X S' eX hS' h0
    have := card_inf_normalizer eX hS'
    rw [h0, Subgroup.card_bot] at this
    exact absurd this (by norm_num)
  rintro p ⟨hpM, hpK0⟩
  rw [hsup, ← L1233.range_mulHom _ _ hc] at hpK0
  obtain ⟨⟨a, b⟩, rfl⟩ := hpK0
  rw [L1233.mulHom_apply] at hpM ⊢
  have ha : (a : HStar H) ∈ Ks ⊓ Subgroup.normalizer ((S ⊓ Ks : Subgroup (HStar H)) :
      Set (HStar H)) :=
    mem_of_mul_mem hsK hc inf_le_left (hB₁.trans hBM)
      (fun Z h1 h2 => eq_or_eq_of_le_normalizer e₁ hS₁ h1 h2) (hne e₁ hS₁) hKM a.2 b.2 hpM
  have hb : (b : HStar H) ∈ K2s ⊓ Subgroup.normalizer ((S ⊓ K2s : Subgroup (HStar H)) :
      Set (HStar H)) :=
    mem_of_mul_mem hsK₂ (fun x hx y hy => (hc y hy x hx).symm) inf_le_left (hB₂.trans hBM)
      (fun Z h1 h2 => eq_or_eq_of_le_normalizer e₂ hS₂ h1 h2) (hne e₂ hS₂) hK2M b.2 a.2
      (by rw [← hc a a.2 b b.2]; exact hpM)
  exact Subgroup.mul_mem _ (hB₁ ha) (hB₂ hb)

omit [IsMulCommutative ↥V] in
theorem conjSub_mem_pair_H (hH : Hyp126 G T L V) {V₁ Vp : Subgroup G}
    (h918 : HypF918 T V L V₁ Vp H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) {g : G} (hg : g ∈ H) :
    conjSub g K = K ∨ conjSub g K = conjSub t₀ K := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t₀ K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht₀)
  have hXc : conjSub g K ∈ cComp H := L1233.conjSub_mem_cComp hKc hg
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥(star H K) := e₁.isSimpleGroup
  have hsX := isSimple_star_conjSub e₁ hg
  have hsK₂ := isSimple_star_conjSub e₁ (hTH ht₀)
  have hc1 := L1233.commute_star hXc hKc hne1 hsX hsK
  have hc2 := L1233.commute_star hXc hK₂c hne2 hsX hsK₂
  obtain ⟨hc, -⟩ := commute_pair h918 e₁ ht₀ ht₀K
  have hsup := star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K
  have hXK₀ : star H (conjSub g K) ≤ star H (conjClosure K T) := by
    refine star_mono fun x hx => ?_
    have h1 := mem_conjSub.1 hx
    have h2 := (Subgroup.mem_normalizer_iff.1 (h918.K₀_normal hg) _).1
      (le_conjClosure K T h1)
    simpa [mul_assoc] using h2
  have hXC : star H (conjSub g K) ≤
      Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hsup, ← L1233.range_mulHom _ _ hc] at hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    rw [L1233.mulHom_apply]
    have h1 := hc1 x hx a a.2
    have h2 := hc2 x hx b b.2
    calc (a : HStar H) * b * x = a * (x * b) := by rw [mul_assoc, h2]
      _ = x * (a * b) := by rw [← mul_assoc, ← h1, mul_assoc]
  have h0 := inf_centralizer_eq_bot hH h918 e₁ ht₀ ht₀K
  obtain ⟨a, b, hab⟩ := hsX.exists_pair_ne
  apply hab
  have ha : (a : HStar H) = 1 := by
    have : (a : HStar H) ∈ star H (conjClosure K T) ⊓
        Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := ⟨hXK₀ a.2, hXC a.2⟩
    rw [h0] at this
    exact this
  have hb : (b : HStar H) = 1 := by
    have : (b : HStar H) ∈ star H (conjClosure K T) ⊓
        Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := ⟨hXK₀ b.2, hXC b.2⟩
    rw [h0] at this
    exact this
  exact Subtype.ext (ha.trans hb.symm)

omit [IsMulCommutative ↥V] in
theorem map_conj_mem_pair (hH : Hyp126 G T L V) {V₁ Vp : Subgroup G}
    (h918 : HypF918 T V L V₁ Vp H K) (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) (h : HStar H) :
    (star H K).map (MulAut.conj h).toMonoidHom = star H K ∨
      (star H K).map (MulAut.conj h).toMonoidHom = star H (conjSub t₀ K) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  rw [← L1233.star_conjSub g.2]
  rcases conjSub_mem_pair_H hH h918 e₁ ht₀ ht₀K g.2 with h1 | h1
  · left; rw [h1]
  · right; rw [h1]

theorem card_mulAut_of_alt5 {Q : Type*} [Group Q] {X : Subgroup Q}
    (e : ↥X ≃* alternatingGroup (Fin 5)) : Nat.card (MulAut ↥X) = 120 :=
  (Nat.card_congr (MulAut.congr e).toEquiv).trans card_mulAut_alt5

theorem card_dvd_28800 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hHK : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (e₁ : ↥(star H K) ≃* alternatingGroup (Fin 5)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) : Nat.card (HStar H) ∣ 28800 := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  set Ks := star H K with hKs
  set K2s := star H (conjSub t₀ K) with hK2s
  set N₁ := Subgroup.normalizer (Ks : Set (HStar H)) with hN₁
  obtain ⟨hc, hi⟩ := commute_pair h918 e₁ ht₀ ht₀K
  have hsup := star_conjClosure_eq_sup hH h918 e₁ ht₀ ht₀K
  have e₂ := equivConjSub e₁ (hTH ht₀)
  have := isSimpleGroup_alt5
  have hsK : IsSimpleGroup ↥Ks := e₁.isSimpleGroup
  have hKne : Ks ≠ K2s := by
    intro he
    obtain ⟨a, b, hab⟩ := hsK.exists_pair_ne
    apply hab
    have ha : (a : HStar H) ∈ Ks ⊓ K2s := ⟨a.2, he ▸ a.2⟩
    have hb : (b : HStar H) ∈ Ks ⊓ K2s := ⟨b.2, he ▸ b.2⟩
    rw [hi] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  set cs : HStar H → Subgroup (HStar H) → Subgroup (HStar H) :=
    fun x X => X.map (MulAut.conj x).toMonoidHom with hcs
  have hcsmul : ∀ (x y : HStar H) (X : Subgroup (HStar H)), cs (x * y) X = cs x (cs y X) := by
    intro x y X
    simp only [hcs]
    rw [Subgroup.map_map, map_mul]
    rfl
  have hcsinj : ∀ (x : HStar H) {X Y : Subgroup (HStar H)}, cs x X = cs x Y → X = Y :=
    fun x X Y h => Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective h
  have hpair : ∀ x, cs x Ks = Ks ∨ cs x Ks = K2s := map_conj_mem_pair hH h918 e₁ ht₀ ht₀K
  set tb : HStar H := QuotientGroup.mk ⟨t₀, hTH ht₀⟩ with htb
  have hK2 : K2s = cs tb Ks := L1233.star_conjSub (hTH ht₀)
  have hpair2 : ∀ x, cs x K2s = Ks ∨ cs x K2s = K2s := fun x => by
    have h1 : cs x K2s = cs (x * tb) Ks := by rw [hcsmul, ← hK2]
    rw [h1]
    exact hpair _
  have hmem : ∀ x : HStar H, x ∈ N₁ ↔ cs x Ks = Ks := fun x =>
    Subgroup.mem_normalizer_iff_map_conj_eq
  have hN₁2 : N₁ ≤ Subgroup.normalizer (K2s : Set (HStar H)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases hpair2 x with h1 | h1
    · exact absurd (hcsinj x (h1.trans ((hmem x).1 hx).symm)).symm hKne
    · exact h1
  have hout : ∀ x, x ∉ N₁ → cs x Ks = K2s ∧ cs x K2s = Ks := by
    intro x hx
    have h1 : cs x Ks = K2s := (hpair x).resolve_left fun h => hx ((hmem x).2 h)
    refine ⟨h1, (hpair2 x).resolve_right fun h => hKne (hcsinj x (h1.trans h.symm))⟩
  have hidx : N₁.index ∣ 2 := by
    by_cases htop : N₁ = ⊤
    · rw [htop, Subgroup.index_top]
      exact one_dvd 2
    · obtain ⟨a, ha⟩ : ∃ a, a ∉ N₁ := by
        by_contra hall
        push Not at hall
        exact htop (eq_top_iff.2 fun x _ => hall x)
      refine dvd_of_eq (Subgroup.index_eq_two_iff.2 ⟨a, fun b => ?_⟩)
      by_cases hb : b ∈ N₁
      · refine Or.inr ⟨hb, fun hba => ?_⟩
        have h1 := (hmem (b * a)).1 hba
        rw [hcsmul, (hout a ha).1] at h1
        have h2 : cs b K2s = K2s := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hN₁2 hb)
        exact hKne (h2.symm.trans h1).symm
      · refine Or.inl ⟨(hmem (b * a)).2 ?_, hb⟩
        rw [hcsmul, (hout a ha).1, (hout b hb).2]
  set ψ : ↥N₁ →* MulAut ↥Ks × MulAut ↥K2s :=
    (conjOn Ks N₁ le_rfl).prod (conjOn K2s N₁ hN₁2) with hψ
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hy
    have h1 : ∀ x ∈ Ks, (y : HStar H) * x = x * y := fun x hx => by
      have := congrArg (fun φ : MulAut ↥Ks => ((φ ⟨x, hx⟩ : ↥Ks) : HStar H)) hy.1
      simp only [conjOn_apply, MulAut.one_apply, Subgroup.coe_inv] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    have h2 : ∀ x ∈ K2s, (y : HStar H) * x = x * y := fun x hx => by
      have := congrArg (fun φ : MulAut ↥K2s => ((φ ⟨x, hx⟩ : ↥K2s) : HStar H)) hy.2
      simp only [conjOn_apply, MulAut.one_apply, Subgroup.coe_inv] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    have hyC : (y : HStar H) ∈ Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hsup, ← L1233.range_mulHom _ _ hc] at hz
      obtain ⟨⟨a, b⟩, rfl⟩ := hz
      rw [L1233.mulHom_apply]
      calc (a : HStar H) * b * y = a * (y * b) := by rw [mul_assoc, h2 b b.2]
        _ = y * (a * b) := by rw [← mul_assoc, ← h1 a a.2, mul_assoc]
    rw [centralizer_eq_bot h1222 F hH hHK h918 e₁ ht₀ ht₀K] at hyC
    exact Subgroup.mem_bot.2 (Subtype.ext hyC)
  have hcardN : Nat.card N₁ ∣ 14400 := by
    have h1 : Nat.card N₁ = Nat.card ψ.range :=
      Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv
    have h2 := Subgroup.card_subgroup_dvd_card ψ.range
    rw [Nat.card_prod, card_mulAut_of_alt5 e₁, card_mulAut_of_alt5 e₂] at h2
    rw [h1]
    exact h2
  have hc := N₁.card_mul_index
  rw [← hc]
  exact mul_dvd_mul hcardN hidx

omit [Finite G] in
theorem star_L1_le {L V₁ X : Subgroup G} (hL1H : Li L V₁ ≤ H) (hn : (star H X).Normal)
    (hidx : (star H X).index ∣ 8) : star H (Li L V₁) ≤ star H X := by
  have hle : Li L V₁ ≤ pre H (star H X) := by
    show Subgroup.closure _ ≤ _
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxLN, m, hm, hxm⟩
    have hxH : x ∈ H := hL1H (Subgroup.subset_closure ⟨hxLN, m, hm, hxm⟩)
    refine mem_pre.2 ⟨hxH, ?_⟩
    set π := QuotientGroup.mk' (star H X) with hπ
    set y : HStar H := QuotientGroup.mk ⟨x, hxH⟩ with hy
    have h1 : π y ^ m = 1 := by
      rw [← map_pow, hy, ← QuotientGroup.mk_pow]
      have : (⟨x, hxH⟩ : ↥H) ^ m = 1 := Subtype.ext (by simpa using hxm)
      rw [this, QuotientGroup.mk_one, map_one]
    have h2 : π y ^ 8 = 1 := by
      obtain ⟨c, hc⟩ := hidx
      have h3 := pow_card_eq_one' (G := HStar H ⧸ star H X) (x := π y)
      rw [← Subgroup.index_eq_card] at h3
      rw [hc, pow_mul, h3, one_pow]
    have hcop : Nat.Coprime m 8 :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hm)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hd
    exact hd
  calc star H (Li L V₁) ≤ star H (pre H (star H X)) := star_mono hle
    _ = star H X := star_pre _

theorem four_le_index (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (h : HypF91 T V L F.V1 F.V5 H) {X : Subgroup G} (hn : (star H X).Normal)
    (hL1 : star H (Li L F.V1) ≤
      Subgroup.normalizer ((star H T ⊓ star H X : Subgroup (HStar H)) : Set (HStar H))) :
    4 ≤ (star H X).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := h.T_le_H
  have hsylT := isSylowTwoOf_T h
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hsylT
  set Ts := star H T with hTs
  set Xs := star H X with hXs
  set Sh := pre H (Ts ⊓ Xs) with hSh
  have hShT : Sh ≤ T := by
    intro x hx
    obtain ⟨hxH, hxS⟩ := mem_pre.1 hx
    obtain ⟨t, ht, he⟩ := hxS.1
    have hq := F126.mem_pCoreOf_of_mk_eq he
    have : x = (t : G) * ((t : G)⁻¹ * x) := by group
    rw [this]
    exact T.mul_mem (Subgroup.mem_subgroupOf.1 ht) (hQT hq)
  have hShp : IsPGroup 2 Sh := hsylT.2.1.to_le hShT
  have hL1T : Li L F.V1 ⊔ T ≤ H := h.L₁T_le_H
  have hN : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (Sh : Set G) := by
    refine sup_le (le_normalizer_pre (le_sup_left.trans hL1T) hL1) (le_normalizer_pre hTH ?_)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hx) y
    have h2 := Subgroup.mem_normalizer_iff.1
      ((Subgroup.le_normalizer_of_normal : Ts ≤ Subgroup.normalizer (Xs : Set (HStar H))) hx) y
    exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩
  have hShR : Sh ≤ Ri T L F.V1 :=
    le_pCoreOf_of_le_normalizer 2 (hShT.trans le_sup_right) hN hShp
  have h4 := four_le_relIndex h1222 F hH
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hne : Sh.relIndex T ≠ 0 := by
    intro h0
    have h3 := Subgroup.relIndex_mul_card (H := Sh) (K := T)
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := ↥T)).ne h3
  have h5 : (Ri T L F.V1).relIndex T ≤ Sh.relIndex T :=
    Subgroup.relIndex_le_of_le_left hShR hne
  have h6 : Sh.relIndex T = (Ts ⊓ Xs).relIndex Ts := by
    rw [← relIndex_star (pCoreOf_le_pre _) hShT hTH, star_pre]
  have h7 : (Ts ⊓ Xs).relIndex Ts ≤ Xs.index := by
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_top_right]
    refine Subgroup.relIndex_le_of_le_right le_top ?_
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  omega

theorem case2_of (h1222 : Stmt12_2_2) (h1229 : Lemma12_6_29) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hHK : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hA : Nonempty (↥(star H K) ≃* alternatingGroup (Fin 5))) (hK₀ : conjClosure K T ≠ K) :
    Case2 T L H K := by
  obtain ⟨e₁⟩ := hA
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  obtain ⟨t₀, ht₀, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact hK₀ (le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.1 (hall t ht) k).1 hk) (le_conjClosure K T))
  set K0s := star H (conjClosure K T) with hK0s
  set Ms := star H (Subgroup.normalizer (L : Set G) ⊓ H) with hMs
  have hK0n : K0s.Normal := normal_star h918.K₀_normal
  have hK₀H : conjClosure K T ≤ H := by
    rw [hHK.2.2]
    exact le_sup_left
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h.L₁T_le_H
  have hL1TM : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (L : Set G) ⊓ H :=
    le_inf (sup_le (F126.L1_le_L.trans Subgroup.le_normalizer) hH.hyp.normalizes) hL1TH
  have hcard0 := card_star_K₀ hH h918 e₁ ht₀ ht₀K
  have hdvd := card_dvd_28800 h1222 F hH hHK h918 e₁ ht₀ ht₀K
  have h1 := K0s.card_mul_index
  rw [hcard0] at h1
  have hidx8 : K0s.index ∣ 8 := by
    rw [← h1] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3600)
      (by simpa using hdvd)
  have hL1K : star H (Li L F.V1) ≤ K0s := star_L1_le (le_sup_left.trans hL1TH) hK0n hidx8
  have hL1M : star H (Li L F.V1) ≤ Ms := star_mono (le_sup_left.trans hL1TM)
  have hB := inf_star_M_eq_borel h1229 F hH hZ hHK h918 e₁ ht₀ ht₀K
  have hL1B : star H (Li L F.V1) ≤ borel K0s (star H T) := hB ▸ le_inf hL1M hL1K
  have hidx4 : 4 ≤ K0s.index := four_le_index h1222 F hH h hK0n (hL1B.trans inf_le_right)
  refine ⟨hK₀, ⟨e₁⟩, ⟨equivK₀ hH h918 e₁ ht₀ ht₀K⟩,
    centralizer_eq_bot h1222 F hH hHK h918 e₁ ht₀ ht₀K, ?_, ?_⟩
  · have hle : K0s.index ≤ 8 := Nat.le_of_dvd (by norm_num) hidx8
    have h48 : K0s.index = 4 ∨ K0s.index = 8 := by
      interval_cases hi : K0s.index
      · left; rfl
      · exact absurd hidx8 (by norm_num)
      · exact absurd hidx8 (by norm_num)
      · exact absurd hidx8 (by norm_num)
      · right; rfl
    rcases h48 with h4 | h8
    · left
      rw [← h1, h4]
    · right
      rw [← h1, h8]
  · have hTsM : star H T ≤ Ms := star_mono (le_inf hH.hyp.normalizes hTH)
    have hBM : borel K0s (star H T) ≤ Ms := hB ▸ inf_le_left
    refine le_antisymm ?_ (sup_le hTsM hBM)
    intro x hx
    have htop : K0s ⊔ star H (Li L F.V1 ⊔ T) = ⊤ := by
      rw [hK0s, ← star_sup hK₀H hL1TH, ← hHK.2.2, star_self]
    have hx' : x ∈ K0s ⊔ star H (Li L F.V1 ⊔ T) := htop ▸ Subgroup.mem_top x
    obtain ⟨k, hk, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
    have hyM : y ∈ Ms := star_mono hL1TM hy
    have hkM : k ∈ Ms := by
      have := Ms.mul_mem hx (Ms.inv_mem hyM)
      simpa using this
    have hkB : k ∈ borel K0s (star H T) := hB ▸ ⟨hkM, hk⟩
    rw [star_sup (le_sup_left.trans hL1TH) hTH] at hy
    have hy' : y ∈ star H T ⊔ borel K0s (star H T) :=
      (sup_le (hL1B.trans le_sup_right) le_sup_left) hy
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkB) hy'

end CaseTwo

end CFSG.Quasithin.H13.S126P31
