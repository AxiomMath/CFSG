module

public import CFSG.Quasithin.Background.SmithB45HatA6OutData
public import CFSG.Quasithin.Background.SmithB42HatA6Dim

public section

namespace CFSG.Quasithin.B45HatA6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  CFSG.QuasithinUnique.A6Facts.Core

theorem mem_qList_of_all {c : List ℕ} (hc : c ∈ qList) : c ∈ pslLit := by
  have h := qList_facts.1
  rw [List.all_eq_true] at h
  exact List.contains_iff_mem.mp (h c hc)

theorem xC_mem : xC ∈ qList := List.contains_iff_mem.mp qList_facts.2.2.2.2.2.2.2.2.1

theorem yC_mem : yC ∈ qList := List.contains_iff_mem.mp qList_facts.2.2.2.2.2.2.2.2.2

@[expose] def Q9 : Subgroup ↥A6Models.psl29 where
  carrier := {w | code (w : P10) ∈ qList}
  mul_mem' := by
    intro a b ha hb
    show code ((a : P10) * (b : P10)) ∈ qList
    rw [code_mul]
    have h := qList_facts.2.2.2.2.1
    rw [List.all_eq_true] at h
    have h2 := h _ ha
    rw [List.all_eq_true] at h2
    exact List.contains_iff_mem.mp (h2 _ hb)
  one_mem' := by
    show code (1 : P10) ∈ qList
    rw [code_one]
    exact List.contains_iff_mem.mp qList_facts.2.2.2.1
  inv_mem' := by
    intro a ha
    show code ((a : P10)⁻¹) ∈ qList
    rw [code_inv]
    have h := qList_facts.2.2.2.2.2.1
    rw [List.all_eq_true] at h
    exact List.contains_iff_mem.mp (h _ ha)

theorem mem_Q9 {w : ↥A6Models.psl29} : w ∈ Q9 ↔ code (w : P10) ∈ qList := Iff.rfl

theorem exists_of_code {c : List ℕ} (hc : c ∈ pslLit) :
    ∃ w : ↥A6Models.psl29, code (w : P10) = c := by
  obtain ⟨x, hx, hxc⟩ := exists_psl29_of_code hc
  exact ⟨⟨x, hx⟩, hxc⟩

noncomputable def xP : ↥A6Models.psl29 := (exists_of_code (mem_qList_of_all xC_mem)).choose

noncomputable def yP : ↥A6Models.psl29 := (exists_of_code (mem_qList_of_all yC_mem)).choose

theorem code_xP : code (xP : P10) = xC := (exists_of_code (mem_qList_of_all xC_mem)).choose_spec

theorem code_yP : code (yP : P10) = yC := (exists_of_code (mem_qList_of_all yC_mem)).choose_spec

theorem eq_of_code_eq {u w : ↥A6Models.psl29} (h : code (u : P10) = code (w : P10)) : u = w :=
  Subtype.ext (code_injective h)

theorem code_qP (p q : ℕ) : code ((xP ^ p * yP ^ q : ↥A6Models.psl29) : P10) = qC p q := by
  rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, code_mul, code_pow, code_pow,
    code_xP, code_yP]
  rfl

theorem closure_xy_eq : Subgroup.closure ({xP, yP} : Set ↥A6Models.psl29) = Q9 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · rw [SetLike.mem_coe, mem_Q9, code_xP]; exact xC_mem
    · rw [SetLike.mem_coe, mem_Q9, code_yP]; exact yC_mem
  · intro w hw
    rw [mem_Q9, qList_eq, List.mem_map] at hw
    obtain ⟨i, -, hi⟩ := hw
    have hw' : w = xP ^ (i / 3) * yP ^ (i % 3) := eq_of_code_eq (by rw [code_qP, hi])
    rw [hw']
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)

theorem card_Q9 : Nat.card Q9 = 9 := by
  classical
  let f : ↥Q9 → ↥qList.toFinset := fun w =>
    ⟨code ((w : ↥A6Models.psl29) : P10), List.mem_toFinset.mpr w.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u w h => Subtype.ext (eq_of_code_eq (congrArg Subtype.val h)), fun c => ?_⟩
    obtain ⟨w, hw⟩ := exists_of_code (mem_qList_of_all (List.mem_toFinset.mp c.2))
    exact ⟨⟨w, by rw [mem_Q9, hw]; exact List.mem_toFinset.mp c.2⟩, Subtype.ext hw⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup qList_facts.2.1, qList_facts.2.2.1]

theorem isElemAbelian_Q9 : CFSG.Open.IsElemAbelian 3 Q9 := by
  refine ⟨⟨⟨fun a b => Subtype.ext (eq_of_code_eq ?_)⟩⟩, fun w hw => eq_of_code_eq ?_⟩
  · show code (((a : ↥A6Models.psl29) : P10) * ((b : ↥A6Models.psl29) : P10)) =
      code (((b : ↥A6Models.psl29) : P10) * ((a : ↥A6Models.psl29) : P10))
    rw [code_mul, code_mul]
    have h := qList_facts.2.2.2.2.2.2.1
    rw [List.all_eq_true] at h
    have h2 := h _ a.2
    rw [List.all_eq_true] at h2
    exact beq_iff_eq.mp (h2 _ b.2)
  · rw [Subgroup.coe_pow, code_pow, Subgroup.coe_one, code_one]
    have h := qList_facts.2.2.2.2.2.2.2.1
    rw [List.all_eq_true] at h
    exact beq_iff_eq.mp (h _ hw)

theorem factorization_three : (360 : ℕ).factorization 3 = 2 := by
  have h : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

noncomputable def sylowQ9 : Sylow 3 ↥A6Models.psl29 :=
  Sylow.ofCard Q9 (by rw [card_Q9, card_psl29, factorization_three]; norm_num)

theorem coe_sylowQ9 : (sylowQ9 : Subgroup ↥A6Models.psl29) = Q9 := Sylow.coe_ofCard _ _

theorem conjAut_mul (b c : AutA6) :
    DoubleA3.conjAut (b * c) = DoubleA3.conjAut b * DoubleA3.conjAut c := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  show (b : P10) * (c : P10) * (x : P10) * ((b : P10) * (c : P10))⁻¹ =
    (b : P10) * ((c : P10) * (x : P10) * (c : P10)⁻¹) * (b : P10)⁻¹
  group

theorem conjAut_one : DoubleA3.conjAut 1 = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  show (1 : P10) * (x : P10) * (1 : P10)⁻¹ = x
  group

theorem conjAut_of_mem {b : AutA6} (hb : (b : P10) ∈ A6Models.psl29) :
    DoubleA3.conjAut b = MulAut.conj (⟨b, hb⟩ : ↥A6Models.psl29) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem det_ne_one {p q r t : ℕ} (hp : p < 3) (hq : q < 3) (hr : r < 3) (ht : t < 3)
    (h : (p * t + 2 * (q * r)) % 3 ≠ 1) : (((p * t - r * q : ℤ)) : ZMod 3) ≠ 1 := by
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases t <;>
    simp_all <;> decide

theorem exists_det_witness (b : AutA6) (hb2 : b * b = 1) (hb : (b : P10) ∉ A6Models.psl29) :
    ∃ s : AutA6, (s : P10) ∈ A6Models.psl29 ∧ ∃ p q r t : ℕ,
      DoubleA3.conjAut (b * s) xP = xP ^ p * yP ^ q ∧
      DoubleA3.conjAut (b * s) yP = xP ^ r * yP ^ t ∧
      (((p * t - r * q : ℤ)) : ZMod 3) ≠ 1 := by
  have hc := cd_mem_autL b
  have hcc : cmul (cd b) (cd b) = cid := by rw [← cd_mul, hb2, cd_one]
  have hcp : pslLit.contains (cd b) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hb ((mem_psl29_iff _).mpr (List.contains_iff_mem.mp h))
  have h := f1Check_true
  unfold f1Check at h
  rw [List.all_eq_true] at h
  have h1 := h _ hc
  rw [hcc, hcp] at h1
  simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h1
  obtain ⟨⟨c, s, p, q, r, t⟩, -, rfl, hw⟩ := h1
  unfold wOK at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hp⟩, hq⟩, hr⟩, ht⟩, hx⟩, hy⟩, hdet⟩ := hw
  obtain ⟨s', hs', hs'c⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hs)
  have hsA : s' ∈ A6Models.autA6 := psl29_le_autA6 hs'
  refine ⟨⟨s', hsA⟩, hs', p, q, r, t, ?_, ?_, det_ne_one hp hq hr ht hdet⟩
  · apply eq_of_code_eq
    rw [code_qP, ← hx, DoubleA3.conjAut_apply]
    show code (((b : P10) * s') * (xP : P10) * ((b : P10) * s')⁻¹) = _
    rw [code_mul, code_mul, code_inv, code_mul, code_xP, hs'c]
    rfl
  · apply eq_of_code_eq
    rw [code_qP, ← hy, DoubleA3.conjAut_apply]
    show code (((b : P10) * s') * (yP : P10) * ((b : P10) * s')⁻¹) = _
    rw [code_mul, code_mul, code_inv, code_mul, code_yP, hs'c]
    rfl

section B4

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem mem_of_commute_center (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L) {zL : ↥L}
    (hcen : Subgroup.center ↥L = Subgroup.zpowers zL) {a : MulAut V} (haG : a ∈ G)
    (ha2 : a * a = 1) (hza : a * (zL : MulAut V) = (zL : MulAut V) * a) : a ∈ L := by
  classical
  obtain ⟨hq, hZ3, ⟨eL⟩⟩ := hP
  have hLG := HatA6.le_of_b4Hyp hHyp
  have hGN := HatA6.le_normalizer_of_b4Hyp hHyp
  have hCL := HatA6.inf_centralizer_le_of_b4Hyp hHyp
  set L' : Subgroup ↥G := L.subgroupOf G with hL'
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2 hGN
  let eLL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hq' : CFSG.IsQuasisimple ↥L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eLL.symm hq
  have : Group.IsPerfect ↥L' := hq'.1
  obtain ⟨psi⟩ : Nonempty (↥A6Models.psl29 ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
    exact ⟨ψ⟩
  let eQ : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥A6Models.psl29 :=
    ((QuotientGroup.congr _ _ eLL (Subgroup.map_center_eq eLL)).trans eL).trans psi.symm
  set φ := Setup.X3.outAct L' eQ ⟨a, haG⟩ with hφ
  obtain ⟨b, hb⟩ := DoubleA3.conjAut_surjective φ
  have hb2 : b * b = 1 := by
    apply DoubleA3.conjAut_injective
    rw [conjAut_mul, hb, conjAut_one, ← map_mul]
    have : (⟨a, haG⟩ : ↥G) * ⟨a, haG⟩ = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hlift : ∀ s : ↥A6Models.psl29, ∃ l : ↥L', eQ (QuotientGroup.mk l) = s := by
    intro s
    obtain ⟨y, hy⟩ := eQ.surjective s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨l, hy⟩
  have hlL : ∀ l : ↥L', ((l : ↥G) : MulAut V) ∈ L := fun l => Subgroup.mem_subgroupOf.1 l.2
  by_cases hbP : (b : P10) ∈ A6Models.psl29
  ·
    obtain ⟨l, hl⟩ := hlift ⟨b, hbP⟩
    have h1 : Setup.X3.outAct L' eQ ((⟨a, haG⟩ : ↥G) * (l : ↥G)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hφ, Setup.X3.outAct_of_mem, hl, ← conjAut_of_mem hbP, hb,
        mul_inv_cancel]
    have h2 := Setup.X3.mem_centralizer_of_outAct_eq_one L' eQ h1
    have h3 : a * ((l : ↥G) : MulAut V)⁻¹ ∈
        G ⊓ Subgroup.centralizer (L : Set (MulAut V)) := by
      refine ⟨G.mul_mem haG (G.inv_mem (l : ↥G).2), Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have h4 := Subgroup.mem_centralizer_iff.1 h2 ⟨x, hLG hx⟩ (Subgroup.mem_subgroupOf.2 hx)
      exact congrArg Subtype.val h4
    have h5 : a = a * ((l : ↥G) : MulAut V)⁻¹ * ((l : ↥G) : MulAut V) := by group
    rw [h5]
    exact L.mul_mem (hCL h3) (hlL l)
  ·
    exfalso
    obtain ⟨s, hs, p, q, r, t, hx, hy, hdet⟩ := exists_det_witness b hb2 hbP
    obtain ⟨l, hl⟩ := hlift ⟨s, hs⟩
    set g : ↥G := ⟨a, haG⟩ * (l : ↥G) with hg
    have hgφ : Setup.X3.outAct L' eQ g = DoubleA3.conjAut (b * s) := by
      rw [hg, map_mul, ← hφ, Setup.X3.outAct_of_mem, hl, ← conjAut_of_mem hs, ← hb, conjAut_mul]
    let π : ↥L' →* ↥A6Models.psl29 :=
      eQ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L'))
    have hπ : Function.Surjective π := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center ↥L' := by
      ext x
      rw [MonoidHom.mem_ker]
      show eQ (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    let α : MulAut ↥L' := MulAut.conjNormal g
    have hαβ : ∀ e, π (α e) = DoubleA3.conjAut (b * s) (π e) := by
      intro e
      rw [← hgφ]
      show eQ (QuotientGroup.mk (α e)) = Setup.X3.outAct L' eQ g (eQ (QuotientGroup.mk e))
      rw [Setup.X3.outAct_apply_mk]
      have he : α e = ⟨g * (e : ↥G) * g⁻¹, (Subgroup.mem_normalizer_iff.1
          (Setup.X3.mem_normalizer_of_normal L' g) e).1 e.2⟩ :=
        Subtype.ext (MulAut.conjNormal_apply g e)
      rw [he]
    have hαC : ∀ c ∈ π.ker, α c = c := by
      intro c hc
      rw [hker] at hc
      have hcL : eLL c ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff] at hc ⊢
        intro k
        obtain ⟨k', rfl⟩ := eLL.surjective k
        rw [← map_mul, ← map_mul, hc k']
      rw [hcen] at hcL
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcL
      have hcz : ((c : ↥G) : MulAut V) = (zL : MulAut V) ^ n := by
        have := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow] at this
        exact this.symm
      have hlc : (l : ↥G) * (c : ↥G) = (c : ↥G) * (l : ↥G) := by
        have := Subgroup.mem_center_iff.1 hc l
        exact congrArg Subtype.val this
      have hac : a * ((c : ↥G) : MulAut V) = ((c : ↥G) : MulAut V) * a := by
        rw [hcz]
        exact (Commute.zpow_right hza n).eq
      apply Subtype.ext
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show ((g : MulAut V) * ((c : ↥G) : MulAut V) * (g : MulAut V)⁻¹) = ((c : ↥G) : MulAut V)
      have hlc' : ((l : ↥G) : MulAut V) * ((c : ↥G) : MulAut V) =
          ((c : ↥G) : MulAut V) * ((l : ↥G) : MulAut V) := congrArg Subtype.val hlc
      rw [hg, Subgroup.coe_mul]
      show a * ((l : ↥G) : MulAut V) * ((c : ↥G) : MulAut V) *
        (a * ((l : ↥G) : MulAut V))⁻¹ = ((c : ↥G) : MulAut V)
      calc a * ((l : ↥G) : MulAut V) * ((c : ↥G) : MulAut V) * (a * ((l : ↥G) : MulAut V))⁻¹
          = a * (((l : ↥G) : MulAut V) * ((c : ↥G) : MulAut V)) * ((l : ↥G) : MulAut V)⁻¹ *
              a⁻¹ := by group
        _ = a * (((c : ↥G) : MulAut V) * ((l : ↥G) : MulAut V)) * ((l : ↥G) : MulAut V)⁻¹ *
              a⁻¹ := by rw [hlc']
        _ = a * ((c : ↥G) : MulAut V) * a⁻¹ := by group
        _ = ((c : ↥G) : MulAut V) := by rw [hac]; group
    obtain ⟨Cp⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
    have hbot := SectionRank.sylow_kernel_eq_bot_of_det π hπ hker.le sylowQ9
      (coe_sylowQ9 ▸ isElemAbelian_Q9) α (DoubleA3.conjAut (b * s)) hαβ hαC
      (closure_xy_eq.trans coe_sylowQ9.symm) hx hy hdet Cp
    have hk3 : Nat.card π.ker = 3 := by
      rw [hker, ← hZ3]
      exact Nat.card_congr (eLL.subgroupMap (Subgroup.center ↥L')).toEquiv |>.trans
        (by rw [Subgroup.map_center_eq eLL])
    have hCp := Sylow.card_eq_multiplicity Cp
    rw [hk3, hbot, Subgroup.card_bot, Nat.Prime.factorization_self Nat.prime_three] at hCp
    norm_num at hCp

end B4

end CFSG.Quasithin.B45HatA6
