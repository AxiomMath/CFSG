module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19NDec
public import CFSG.Quasithin.Background.SzG11G64Old

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative

namespace L619

variable {G : Type} [Group G]

section Transvections

variable {V : Type} [CommGroup V]

theorem eq_of_card_eq_two {C : Subgroup V} (hC : Nat.card C = 2) {u w : V} (hu : u ∈ C)
    (hw : w ∈ C) (hu1 : u ≠ 1) (hw1 : w ≠ 1) : u = w := by
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have h1 : (⟨u, hu⟩ : C) = x := hx _ fun h => hu1 (congrArg Subtype.val h)
  have h2 : (⟨w, hw⟩ : C) = x := hx _ fun h => hw1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem apply_eq_of_conj_eq {c d : MulAut V} (hcd : c * d * c⁻¹ = d)
    (hd : Nat.card (commV (Subgroup.zpowers d)) = 2) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers d)) : c u = u := by
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  have hcu : c u ∈ commV (Subgroup.zpowers d) := by
    have e := G6.commV_zpowers_conj c d
    rw [hcd] at e
    rw [e]
    exact ⟨u, hu, rfl⟩
  refine eq_of_card_eq_two hd hcu hu (fun h1 => hu1 ?_) hu1
  have := congrArg c.symm h1
  simpa using this

theorem eq_one_of_conj_eq {D : Set (MulAut V)}
    (hD : ∀ d ∈ D, Nat.card (commV (Subgroup.zpowers d)) = 2)
    (hV : commV (Subgroup.closure D) = ⊤) {c : MulAut V} (hc : ∀ d ∈ D, c * d * c⁻¹ = d) :
    c = 1 := by
  have hle : commV (Subgroup.closure D) ≤ (MonoidHom.id V).eqLocus c.toMonoidHom :=
    G6.commV_closure_le fun d hd v =>
      (apply_eq_of_conj_eq (hc d hd) (hD d hd)
        (G6.mem_commV_of_mem (Subgroup.mem_zpowers d) v)).symm
  rw [hV] at hle
  exact MulEquiv.ext fun v => (hle (Subgroup.mem_top v)).symm

theorem pCoreOf_eq_bot_of_conj_eq [Finite V] {N P : Subgroup (MulAut V)} (hPN : P ≤ N)
    (hnorm : ∀ g ∈ N, ∀ k ∈ P, g * k * g⁻¹ ∈ P) (hP : pCoreOf 2 P = ⊥)
    (hC : ∀ c : MulAut V, (∀ k ∈ P, c * k * c⁻¹ = k) → c = 1) : pCoreOf 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 N with hQ
  have hQN : Q ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hNQ : N ≤ Subgroup.normalizer (Q : Set (MulAut V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hint : Q ⊓ P ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hNQ (hPN hk), Subgroup.le_normalizer hk⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_left)
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  refine hC q fun k hk => ?_
  have h1 : q * k * q⁻¹ * k⁻¹ ∈ Q ⊓ P := by
    refine ⟨?_, P.mul_mem (hnorm q (hQN hq) k hk) (P.inv_mem hk)⟩
    have h2 : k * q⁻¹ * k⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hNQ (hPN hk)) _).mp (Q.inv_mem hq)
    have := Q.mul_mem hq h2
    simpa [mul_assoc] using this
  have h3 := hint h1
  rw [hP, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

theorem mem_or_eq_mul_of_mem_sup_zpowers {N K : Subgroup (MulAut V)} {t x : MulAut V}
    (htN : t ∈ N) (hKN : ∀ g ∈ N, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (ht : t * t = 1)
    (hx : x ∈ K ⊔ Subgroup.zpowers t) : x ∈ K ∨ ∃ k ∈ K, x = k * t := by
  have hzK : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => hKN t htN k hk, fun hk => ?_⟩
    have := hKN t⁻¹ (N.inv_mem htN) _ hk
    simpa [mul_assoc] using this
  have hx' : x ∈ ((K ⊔ Subgroup.zpowers t : Subgroup (MulAut V)) : Set (MulAut V)) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ hzK] at hx'
  obtain ⟨k, hk, t', ht', rfl⟩ := Set.mem_mul.mp hx'
  rcases G64.eq_one_or_eq_of_mem_zpowers (by rw [pow_two]; exact ht) ht' with rfl | rfl
  · left
    simpa using hk
  · exact Or.inr ⟨k, hk, rfl⟩

theorem card_commV_ne_two_of_swap [Finite V] {K : Subgroup (MulAut V)}
    {Ks : Fin 2 → Subgroup (MulAut V)} (hd : G6.IsTransvectionDecomposition K Ks)
    {x : MulAut V} (hx : conjSubgroup (Ks 0) x = Ks 1) :
    Nat.card (commV (Subgroup.zpowers x)) ≠ 2 := by
  intro h2
  have hdis : Disjoint (commV (Ks 0)) (commV (Ks 1)) :=
    hd.commV_indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)
  have hmap : ∀ v ∈ commV (Ks 1), x v ∈ commV (Ks 0) := by
    have hle : commV (Ks 1) ≤ (commV (Ks 0)).comap x.toMonoidHom := by
      rw [G6.commV_le_iff]
      intro k hk w
      rw [Subgroup.mem_comap]
      have hk' : x * k * x⁻¹ ∈ Ks 0 := by
        rw [← hx] at hk
        exact mem_conjSubgroup_iff.mp hk
      have := G6.mem_commV_of_mem hk' (x w)
      simpa using this
    exact fun v hv => hle hv
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hd.ne_bot 1)
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have htop : commV (Ks 0) ⊔ commV (Ks 1) = ⊤ := by
    have := G6.iSup_fin_two (fun i => commV (Ks i))
    rw [hd.iSup_commV] at this
    exact this.symm
  obtain ⟨u, hu, hku⟩ : ∃ u ∈ commV (Ks 1), k u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hk1'
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ commV (Ks 0) ⊔ commV (Ks 1) := by
      rw [htop]
      exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hd.apply_eq_of_ne (by decide : (1 : Fin 2) ≠ 0) hk hv₁, hcon v₂ hv₂]
    rfl
  have hu1 : u ≠ 1 := fun h => hku (by rw [h, map_one])
  have hku1 : k u ≠ 1 := fun h => hu1 (by simpa using congrArg k.symm h)
  have hkuV : k u ∈ commV (Ks 1) := hd.isHSubmodule 1 k hk u hu
  have hf : ∀ w ∈ commV (Ks 1), w ≠ 1 → x w * w⁻¹ ≠ 1 := by
    intro w hw hw1 h1
    have hxw : x w = w := mul_inv_eq_one.mp h1
    have h0 : w ∈ commV (Ks 0) := hxw ▸ hmap w hw
    exact hw1 (Subgroup.disjoint_def.mp hdis h0 hw)
  have hw : u * (k u)⁻¹ ∈ commV (Ks 1) :=
    (commV (Ks 1)).mul_mem hu ((commV (Ks 1)).inv_mem hkuV)
  have hw1 : u * (k u)⁻¹ ≠ 1 := fun h => hku (mul_inv_eq_one.mp h).symm
  have hC : ∀ w, x w * w⁻¹ ∈ commV (Subgroup.zpowers x) := fun w =>
    G6.mem_commV_of_mem (Subgroup.mem_zpowers x) w
  have he := eq_of_card_eq_two h2 (hC u) (hC (k u)) (hf u hu hu1) (hf _ hkuV hku1)
  apply hf _ hw hw1
  rw [mul_inv_eq_one, map_mul, map_inv, mul_inv_eq_mul_inv_iff_mul_eq_mul,
    mul_inv_eq_mul_inv_iff_mul_eq_mul.mp he, mul_comm]

end Transvections

section Centre

variable [Finite G] {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z X : Subgroup G)

omit [Finite G] in
theorem commV_zpowers_act0_le {C : Subgroup G} {g : ↥(normWZX W Z X)}
    (hg : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ C) :
    commV (Subgroup.zpowers (act0 hW Z X g)) ≤ (imgSub hW Z C).comap (V0 hW Z X).subtype := by
  rw [Subgroup.zpowers_eq_closure]
  refine G6.commV_closure_le fun s hs v => ?_
  rw [Set.mem_singleton_iff] at hs
  subst hs
  show ((act0 hW Z X g v * v⁻¹ : ↥(V0 hW Z X)) : IntMod W hW ⧸ modSub hW Z) ∈ imgSub hW Z C
  rw [Subgroup.coe_mul, Subgroup.coe_inv, act0_apply, actQX_apply]
  exact actQ_mul_inv_mem_imgSub hW Z ⟨g, g.2.1⟩ hg _

theorem card_comap_imgSub_le {C : Subgroup G} (hcard : Nat.card (imgSub hW Z C) = 2) :
    Nat.card ((imgSub hW Z C).comap (V0 hW Z X).subtype) ≤ 2 := by
  rw [← hcard]
  refine Nat.card_le_card_of_injective (fun a => (⟨(a : ↥(V0 hW Z X)), a.2⟩ : imgSub hW Z C))
    fun a b hab => ?_
  exact Subtype.ext (Subtype.ext
    (congrArg (fun x : ↥(imgSub hW Z C) => (x : IntMod W hW ⧸ modSub hW Z)) hab))

end Centre

end L619

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Cfg619

variable (h : Hyp6116 G T M L V n) {H : Subgroup G} (c : Cfg619 T L V H n y)
include h c

theorem exists_decomposition_b5 (h56 : AsB56) (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (hab : IsMulCommutative ↥(conjClosure V (ch619I T L V))) {z : G} (hz : Z619 T L V H y z)
    {Y : Subgroup G} (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z)) :
    ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
        (conjClosure (conjSub y V) Y)))),
      G6.IsTransvectionDecomposition
        (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y)) Ks ∧
      L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) Y) Ks := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  set K := L619.img0 hW (ch6ZS T L V) X with hK
  set φ := L619.act0 hW (ch6ZS T L V) X with hφ
  set Nst := φ.range with hNst
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  have hYN : Y ≤ N := Cfg619.Y_le_normWZX hY
  have hsq : ∀ v : ↥(L619.V0 hW (ch6ZS T L V) X), v ^ 2 = 1 := fun v => Subtype.ext (by
    simpa using L619.sq_eq_one_quot hW (ch6ZS T L V)
      (v : IntMod (ch619W T L V z) hW ⧸ L619.modSub hW (ch6ZS T L V)))
  have htv : ∀ d ∈ transv619 hW y Y, Nat.card (commV (Subgroup.zpowers d)) = 2 := by
    rintro d ⟨g, hg, e, he, hx, rfl, hd1⟩
    exact L619.card_commV_zpowers_act0 hW _ X (c.card_imgSub_conj_ZE h hz hY hW hg)
      (fun w hw => c.commutator_W_conj_mem h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm
        (hY.le_normalizer_W hg) he hw) hd1
  have hgen : Subgroup.closure (transv619 hW y Y) = K := c.closure_transv619 hY hW
  have htop : commV K = ⊤ := c.commV_img0_eq_top h h432 h6110 hab hz hY hW
  have hO : pCoreOf 2 K = ⊥ := c.pCoreOf_img0_eq_bot h h432 hz hY hW
  obtain ⟨e, he, heK⟩ : ∃ e ∈ conjSub y V, e ∉ ch619K2 T L V z := by
    by_contra hcon
    push Not at hcon
    exact c.not_le_K2 h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm hcon
  have he1X : (1 : G) * e * 1⁻¹ ∈ X := CFSG.Quasithin.mem_conjClosure Y.one_mem he
  set a := φ ⟨1 * e * 1⁻¹, hXN he1X⟩ with ha
  have ha1 : a ≠ 1 := fun h1 => heK (by
    simpa using (c.act0_eq_one_iff h h432 hz hY hW (x := ⟨1 * e * 1⁻¹, hXN he1X⟩) he1X).mp h1)
  have htr : Nat.card (commV (Subgroup.zpowers a)) = 2 :=
    htv a ⟨1, Y.one_mem, e, he, hXN he1X, rfl, ha1⟩
  have haK : a ∈ K := L619.act0_mem_img0 hW _ X he1X
  have he2 : e * e = 1 := by
    have h2 : (y⁻¹ * e * y) * (y⁻¹ * e * y) = 1 := by
      rw [← pow_two]
      exact h.toHyp611.isElemAbelian.2 _ (mem_conjSub.mp he)
    have e1 : e * e = y * ((y⁻¹ * e * y) * (y⁻¹ * e * y)) * y⁻¹ := by group
    rw [e1, h2]
    group
  have hKN : ∀ g ∈ Nst, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    rintro _ ⟨g, rfl⟩ k hk
    exact L619.act0_conj_mem_img0 hW _ X g hk
  have hKle : K ≤ Nst := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hC : ∀ c' : MulAut ↥(L619.V0 hW (ch6ZS T L V) X), (∀ k ∈ K, c' * k * c'⁻¹ = k) →
      c' = 1 := fun c' hc' =>
    L619.eq_one_of_conj_eq htv (by rw [hgen]; exact htop) fun d hd =>
      hc' d (by rw [← hgen]; exact Subgroup.subset_closure hd)
  have hNsq : IsQuotientOfSQTK ↥Nst := by
    have := h.toHyp5_0_1.simple
    have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
      B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
    have hZI : ch6ZS T L V ≤ ch619I T L V := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => B2F.isElemAbelian_comm hZel hb ha
    have hON : pCoreOf 2 N ≠ ⊥ := by
      intro h0
      apply h.toHyp611Nat.ZS_ne_bot
      rw [eq_bot_iff, ← h0]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hZI.trans (hY.I_le.trans hYN)) (fun g hg => hg.1.2) (B2F.isPGroup_of_isElemAbelian hZel)
    have hNs : CFSG.SectionRank.IsSQTKCat ↥N :=
      (qtkeCore_of_cat h.toHyp5_0_1.nonabelian h.toHyp5_0_1.qtke).1 _ hON
    exact ⟨↥N, inferInstance, inferInstance, hNs, φ.rangeRestrict, φ.rangeRestrict_surjective⟩
  have hspan : G6.submoduleClosure Nst (commV (Subgroup.zpowers a)) = ⊤ := by
    rw [eq_top_iff, ← htop, ← hgen]
    refine G6.commV_closure_le fun d hd v => ?_
    obtain ⟨g, hg, e', he', hx, rfl, -⟩ := hd
    have hcard := c.card_imgSub_conj_ZE h hz hY hW hg
    have hxg : g * e * g⁻¹ ∈ N := hXN (CFSG.Quasithin.mem_conjClosure hg he)
    have ha' : φ ⟨g * e * g⁻¹, hxg⟩ = φ ⟨g, hYN hg⟩ * a * (φ ⟨g, hYN hg⟩)⁻¹ := by
      rw [ha, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have ha'1 : φ ⟨g * e * g⁻¹, hxg⟩ ≠ 1 := by
      rw [ha']
      intro h1
      apply ha1
      have e1 : a = (φ ⟨g, hYN hg⟩)⁻¹ * (φ ⟨g, hYN hg⟩ * a * (φ ⟨g, hYN hg⟩)⁻¹) *
          φ ⟨g, hYN hg⟩ := by group
      rw [e1, h1]
      group
    have hle1 := L619.commV_zpowers_act0_le hW (ch6ZS T L V) X (g := ⟨g * e' * g⁻¹, hx⟩)
      fun w hw => c.commutator_W_conj_mem h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm
        (hY.le_normalizer_W hg) he' hw
    have hle2 := L619.commV_zpowers_act0_le hW (ch6ZS T L V) X (g := ⟨g * e * g⁻¹, hxg⟩)
      fun w hw => c.commutator_W_conj_mem h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm
        (hY.le_normalizer_W hg) he hw
    have hc2 : Nat.card (commV (Subgroup.zpowers (φ ⟨g * e * g⁻¹, hxg⟩))) = 2 :=
      L619.card_commV_zpowers_act0 hW _ X hcard
        (fun w hw => c.commutator_W_conj_mem h h6110 hab hz.ne_one hz.eq_inf hz.eq_comm
          (hY.le_normalizer_W hg) he hw) ha'1
    have heq := Subgroup.eq_of_le_of_card_ge hle2
      (by rw [hc2]; exact L619.card_comap_imgSub_le hW _ X hcard)
    have hmem : φ ⟨g * e' * g⁻¹, hx⟩ v * v⁻¹ ∈
        commV (Subgroup.zpowers (φ ⟨g, hYN hg⟩ * a * (φ ⟨g, hYN hg⟩)⁻¹)) := by
      rw [← ha', heq]
      exact hle1 (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
    rw [G6.commV_zpowers_conj] at hmem
    unfold G6.submoduleClosure
    exact (le_iSup₂ (f := fun (k : MulAut ↥(L619.V0 hW (ch6ZS T L V) X)) (_ : k ∈ Nst) =>
      (commV (Subgroup.zpowers a)).map k.toMonoidHom) (φ ⟨g, hYN hg⟩) ⟨_, rfl⟩) hmem
  have hyp : G6.Hypothesis61 Nst a :=
    ⟨hsq, L619.pCoreOf_eq_bot_of_conj_eq hKle hKN hO hC, hNsq, hKle haK, ha1,
      by
        rw [ha, ← map_mul]
        have e1 : (⟨1 * e * 1⁻¹, hXN he1X⟩ : ↥N) * ⟨1 * e * 1⁻¹, hXN he1X⟩ = 1 :=
          Subtype.ext (by simpa using he2)
        rw [e1, map_one],
      by rw [htr]; norm_num, hspan⟩
  have hcl : G6.classClosure Nst a ≤ K :=
    CFSG.Quasithin.conjClosure_le fun g hg x hx => hKN g hg x (Subgroup.zpowers_le.mpr haK hx)
  rcases SzG11.lemma_G64_of_b5 h56 hyp htr with
    ⟨Ks, hdec, hGK⟩ | ⟨Ks, hdec, -, -, t, htN, ht1, hGt, ht01⟩
  ·
    have hKeq : G6.classClosure Nst a = K := by
      refine le_antisymm hcl ?_
      rw [← hgen, Subgroup.closure_le]
      intro d hd
      have hdN : d ∈ Nst := hKle (by rw [← hgen]; exact Subgroup.subset_closure hd)
      rw [hGK] at hdN
      exact hdN
    refine ⟨1, Ks, by rw [← hKeq]; exact hdec.decomp, fun g =>
      ⟨hdec.permute _ ⟨g, rfl⟩, fun _ => ?_⟩⟩
    have hg : φ g ∈ Nst := ⟨g, rfl⟩
    rw [hGK, hKeq] at hg
    exact hg
  ·
    have hKN' : ∀ g ∈ Nst, ∀ k ∈ G6.classClosure Nst a, g * k * g⁻¹ ∈ G6.classClosure Nst a :=
      fun g hg k hk => G6.conj_mem_classClosure_of_mem hg hk
    have hsw : ∀ k ∈ G6.classClosure Nst a, conjSubgroup (Ks 0) (k * t) = Ks 1 := fun k hk => by
      rw [← conjSubgroup_conjSubgroup,
        conjSubgroup_eq_iff_mem_normalizer.2 (hdec.decomp.le_normalizer 0 hk), ht01]
    have hcos : ∀ x ∈ Nst, x ∈ G6.classClosure Nst a ∨ conjSubgroup (Ks 0) x = Ks 1 := by
      intro x hx
      rw [hGt] at hx
      rcases L619.mem_or_eq_mul_of_mem_sup_zpowers htN hKN' ht1 hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr (hsw k hk)
    have hKeq : G6.classClosure Nst a = K := by
      refine le_antisymm hcl ?_
      rw [← hgen, Subgroup.closure_le]
      intro d hd
      rcases hcos d (hKle (by rw [← hgen]; exact Subgroup.subset_closure hd)) with h1 | h1
      · exact h1
      · exact absurd (htv d hd) (L619.card_commV_ne_two_of_swap hdec.decomp h1)
    have hne : Ks 0 ≠ Ks 1 := by
      intro heq
      apply hdec.decomp.ne_bot 0
      have hdisj : Ks 0 ⊓ Ks 1 = ⊥ :=
        disjoint_iff.mp (hdec.decomp.indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
      rw [← inf_idem (Ks 0)]
      nth_rewrite 2 [heq]
      exact hdisj
    refine ⟨2, Ks, by rw [← hKeq]; exact hdec.decomp, fun g =>
      ⟨hdec.permute _ ⟨g, rfl⟩, fun hfix => ?_⟩⟩
    rcases hcos _ ⟨g, rfl⟩ with h1 | h1
    · rw [← hK, ← hKeq]
      exact h1
    · exact absurd ((hfix 0).symm.trans h1) hne

end Cfg619

end CFSG.Quasithin.H13
