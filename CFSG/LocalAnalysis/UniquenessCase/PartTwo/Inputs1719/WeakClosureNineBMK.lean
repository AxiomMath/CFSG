module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMX
public import CFSG.Quasithin.H13.A5S1327n

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

set_option maxRecDepth 100000

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (N ⊓ H : Subgroup G) = Nat.card H * Nat.card N := by
  set Y := H ⊔ N
  set N' := N.subgroupOf Y
  set H' := H.subgroupOf Y
  have hNn : N'.Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ normalizer (N : Set G) := sup_le hHN le_normalizer g.2
    exact (mem_normalizer_iff.1 hg n).1 hn
  have htop : H' ⊔ N' = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have h1 : N'.index = N'.relIndex H' := by
    rw [← relIndex_top_right, ← htop, relIndex_sup_right]
  have h2 := N'.index_mul_card
  have h3 := relIndex_mul_card N' H'
  have hH' : Nat.card H' = Nat.card H := Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv
  have hN' : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have hI : Nat.card (N' ⊓ H' : Subgroup Y) = Nat.card (N ⊓ H : Subgroup G) := by
    have e : N' ⊓ H' = (N ⊓ H).subgroupOf Y := by
      ext x
      simp [N', H', mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_right.trans le_sup_left)).toEquiv
  rw [h1, hN'] at h2
  rw [hH', hI] at h3
  rw [← h3, ← h2]
  ring

theorem pow_mul_inv_mem {N : Subgroup G} {a b : G} (ha : a ∈ N)
    (hb : b ∈ normalizer (N : Set G)) (n : ℕ) : (a * b) ^ n * (b ^ n)⁻¹ ∈ N := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : b ^ n ∈ normalizer (N : Set G) := pow_mem hb n
    have e : (a * b) ^ (n + 1) * (b ^ (n + 1))⁻¹ =
        ((a * b) ^ n * (b ^ n)⁻¹) * (b ^ n * a * (b ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih ((mem_normalizer_iff.1 hbn a).1 ha)

theorem pow_mem_of_mem_sup {N H : Subgroup G} (hH : H ≤ normalizer (N : Set G)) {x : G}
    (hx : x ∈ N ⊔ H) {n : ℕ} (hn : ∀ b ∈ H, b ^ n = 1) : x ^ n ∈ N := by
  have hmem : x ∈ (N : Set G) * (H : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left N H hH]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem
  have := pow_mul_inv_mem ha (hH hb) n
  rwa [hn b hb, inv_one, mul_one] at this

end General

structure KData where
  sGen : List (List ℕ)
  sLit : List (List ℕ)
  sn : ℕ
  qGen : List (List ℕ)
  qLit : List (List ℕ)
  qn : ℕ
  yGen : List (List ℕ)
  yLit : List (List ℕ)
  yn : ℕ
  yDec : List (List ℕ × List ℕ × List ℕ)

@[expose] def KChk (tLit : List (List ℕ)) (D : KData) : Bool :=
  D.sLit.all tLit.contains && D.qLit.all D.sLit.contains &&
  D.sLit.length == 2 ^ D.sn && D.qLit.length == 2 ^ D.qn && D.yLit.length == 3 ^ D.yn &&
  (D.yn == 1 || D.yn == 2) &&
  D.yLit.all (fun y => Core.cmul (Core.cmul y y) y == cid) &&
  D.yGen.all (fun a => D.yGen.all fun b => ccomm a b) &&
  (D.yGen ++ D.sGen).all (fun g => D.qLit.all fun q => D.qLit.contains (cconj g q)) &&
  D.sGen.all (fun s => D.yGen.all fun y => D.qLit.any fun q => D.yLit.any fun y' =>
    cconj s y == Core.cmul q y') &&
  D.yGen.length == D.yDec.length &&
  (D.yGen.zip D.yDec).all (fun p => l1Lit.contains p.2.1 && l2Lit.contains p.2.2.1 &&
    tLit.contains p.2.2.2 && Core.cmul (Core.cmul p.2.1 p.2.2.1) p.2.2.2 == p.1) &&
  D.yLit.any (fun y => y != cid && (l1Lit.contains y || l2Lit.contains y)) &&
  (D.yn == 1 || D.yLit.all fun w => w == cid || D.sLit.any fun s =>
    D.yGen.all (fun g => D.yLit.contains (cconj s g)) &&
      !([cid, w, Core.cmul w w].contains (cconj s w)))

structure KEnum (D : KData) : Prop where
  s : LDesc (closureC D.sGen) D.sLit
  q : LDesc (closureC D.qGen) D.qLit
  y : LDesc (closureC D.yGen) D.yLit
  snd : D.sLit.Nodup
  qnd : D.qLit.Nodup
  ynd : D.yLit.Nodup
  sg : ∀ c ∈ D.sGen, c ∈ D.sLit
  qg : ∀ c ∈ D.qGen, c ∈ D.qLit
  yg : ∀ c ∈ D.yGen, c ∈ D.yLit

variable (i : Fin 4)

abbrev Sx (D : KData) : Subgroup ↥(GB i) := (closureC D.sGen).subgroupOf (GB i)
abbrev Qx (D : KData) : Subgroup ↥(GB i) := (closureC D.qGen).subgroupOf (GB i)
abbrev Yx (D : KData) : Subgroup ↥(GB i) := (closureC D.yGen).subgroupOf (GB i)
abbrev Kx (D : KData) : Subgroup ↥(GB i) := Yx i D ⊔ Sx i D
abbrev Mx (D : KData) : Subgroup ↥(GB i) := Qx i D ⊔ Yx i D

section Spec

variable {i} {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
  (hC : KChk tLit D = true)
include hT hE hC

omit hE in
theorem kchk_parts :
    (∀ c ∈ D.sLit, c ∈ tLit) ∧ (∀ c ∈ D.qLit, c ∈ D.sLit) ∧ D.sLit.length = 2 ^ D.sn ∧
    D.qLit.length = 2 ^ D.qn ∧ D.yLit.length = 3 ^ D.yn ∧ (D.yn = 1 ∨ D.yn = 2) ∧
    (∀ y ∈ D.yLit, Core.cmul (Core.cmul y y) y = cid) ∧
    (∀ a ∈ D.yGen, ∀ b ∈ D.yGen, ccomm a b = true) ∧
    (∀ g ∈ D.yGen ++ D.sGen, ∀ q ∈ D.qLit, cconj g q ∈ D.qLit) ∧
    (∀ s ∈ D.sGen, ∀ y ∈ D.yGen, ∃ q ∈ D.qLit, ∃ y' ∈ D.yLit, cconj s y = Core.cmul q y') ∧
    (∀ c ∈ D.yGen, ∃ σ : P16, σ ∈ GB i ∧ code σ = c) ∧
    (∃ y ∈ D.yLit, y ≠ cid ∧ (y ∈ l1Lit ∨ y ∈ l2Lit)) ∧
    (D.yn = 1 ∨ ∀ w ∈ D.yLit, w = cid ∨ ∃ s ∈ D.sLit, (∀ g ∈ D.yGen, cconj s g ∈ D.yLit) ∧
      cconj s w ∉ [cid, w, Core.cmul w w]) := by
  simp only [KChk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    Bool.or_eq_true, List.any_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hq⟩, hsl⟩, hql⟩, hyl⟩, hyn⟩, hy3⟩, hyc⟩, hqn⟩, hsm⟩, hdl⟩, hdec⟩, hgood⟩,
    hirr⟩ := hC
  refine ⟨hs, hq, hsl, hql, hyl, hyn, hy3, hyc, hqn, hsm, ?_, hgood, ?_⟩
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < D.yDec.length := hdl ▸ hk
    have hz : (D.yGen[k], D.yDec[k]) ∈ D.yGen.zip D.yDec :=
      List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hdec _ hz
    obtain ⟨σ1, hσ1, e1⟩ := l1_desc.surj _ h1
    obtain ⟨σ2, hσ2, e2⟩ := l2_desc.surj _ h2
    obtain ⟨σ3, hσ3, e3⟩ := hT.surj _ h3
    refine ⟨σ1 * σ2 * σ3, mul_mem (mul_mem (L01_le_GB i hσ1) (L02_le_GB i hσ2))
      (TB_le_GB i hσ3), ?_⟩
    rw [code_mul, code_mul, e1, e2, e3]
    exact h4
  · rcases hirr with h | h
    · exact Or.inl h
    · refine Or.inr fun w hw => ?_
      rcases h w hw with h' | ⟨s, hs', h1, h2⟩
      · exact Or.inl h'
      · exact Or.inr ⟨s, hs', h1, fun hm => by
          rw [List.contains_iff_mem.2 hm] at h2
          exact Bool.noConfusion h2⟩

end Spec


theorem mem_normalizer_of_forall {H : Subgroup P16} {g : P16} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ normalizer (H : Set P16) :=
  mem_normalizer_of_map_le (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem mem_normalizer_sup {A B : Subgroup P16} {g : P16} (hA : g ∈ normalizer (A : Set P16))
    (hB : g ∈ normalizer (B : Set P16)) : g ∈ normalizer ((A ⊔ B : Subgroup P16) : Set P16) := by
  apply mem_normalizer_of_map_le
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hA x).1 hx
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hB x).1 hx

theorem mem_normalizer_subgroupOf {G : Subgroup P16} {H : Subgroup P16} {g : ↥G}
    (h : (g : P16) ∈ normalizer (H : Set P16)) :
    g ∈ normalizer ((H.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
  rw [mem_normalizer_iff]
  intro x
  change (x : P16) ∈ H ↔ ((g * x * g⁻¹ : ↥G) : P16) ∈ H
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.1 h x

section Main

variable {i} {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {D : KData} (hE : KEnum D)
  (hC : KChk tLit D = true)
include hT hE hC

theorem kS_le_TB : closureC D.sGen ≤ TB i := fun σ hσ =>
  (hT.mem σ).2 ((kchk_parts hT hC).1 _ ((hE.s.mem σ).1 hσ))

theorem kQ_le_S : closureC D.qGen ≤ closureC D.sGen := fun σ hσ =>
  (hE.s.mem σ).2 ((kchk_parts hT hC).2.1 _ ((hE.q.mem σ).1 hσ))

omit hE in
theorem kY_le_GB : closureC D.yGen ≤ GB i := by
  apply closureC_le
  intro σ hσ
  obtain ⟨τ, hτ, hτc⟩ := (kchk_parts hT hC).2.2.2.2.2.2.2.2.2.2.1 _ hσ
  rw [code_injective hτc] at hτ
  exact hτ

theorem kS_le_GB : closureC D.sGen ≤ GB i := (kS_le_TB hT hE hC).trans (TB_le_GB i)

theorem kQ_le_GB : closureC D.qGen ≤ GB i := (kQ_le_S hT hE hC).trans (kS_le_GB hT hE hC)

theorem kgen_normQ {g : P16} (hg : code g ∈ D.yGen ++ D.sGen) :
    g ∈ normalizer ((closureC D.qGen : Subgroup P16) : Set P16) := by
  apply mem_normalizer_of_forall
  intro x hx
  rw [hE.q.mem, code_conj]
  exact (kchk_parts hT hC).2.2.2.2.2.2.2.2.1 _ hg _ ((hE.q.mem x).1 hx)

theorem kY_le_normQ : closureC D.yGen ≤ normalizer ((closureC D.qGen : Subgroup P16) : Set P16) :=
  closureC_le fun _ hσ => kgen_normQ hT hE hC (List.mem_append_left _ hσ)

theorem kS_le_normQ : closureC D.sGen ≤ normalizer ((closureC D.qGen : Subgroup P16) : Set P16) :=
  closureC_le fun _ hσ => kgen_normQ hT hE hC (List.mem_append_right _ hσ)

theorem kS_le_normM : closureC D.sGen ≤
    normalizer ((closureC D.qGen ⊔ closureC D.yGen : Subgroup P16) : Set P16) := by
  apply closureC_le
  intro s hs
  apply mem_normalizer_of_map_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_sup_left ((mem_normalizer_iff.1 (kS_le_normQ hT hE hC (subset_closureC hs)) x).1 hx)
  · rw [closureC, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq, y', hy', he⟩ := (kchk_parts hT hC).2.2.2.2.2.2.2.2.2.1 _ hs _ hy
    obtain ⟨σq, hσq, rfl⟩ := hE.q.surj q hq
    obtain ⟨σy, hσy, rfl⟩ := hE.y.surj y' hy'
    rw [← code_conj, ← code_mul] at he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [code_injective he]
    exact mul_mem (mem_sup_left hσq) (mem_sup_right hσy)

theorem kY_le_normM : closureC D.yGen ≤
    normalizer ((closureC D.qGen ⊔ closureC D.yGen : Subgroup P16) : Set P16) := fun _ hy =>
  mem_normalizer_sup (kY_le_normQ hT hE hC hy) (le_normalizer hy)

theorem card_Sx : Nat.card (Sx i D) = 2 ^ D.sn := by
  rw [card_subgroupOf i (kS_le_GB hT hE hC), hE.s.card hE.snd, (kchk_parts hT hC).2.2.1]

theorem card_Qx : Nat.card (Qx i D) = 2 ^ D.qn := by
  rw [card_subgroupOf i (kQ_le_GB hT hE hC), hE.q.card hE.qnd, (kchk_parts hT hC).2.2.2.1]

theorem card_Yx : Nat.card (Yx i D) = 3 ^ D.yn := by
  rw [card_subgroupOf i (kY_le_GB hT hC), hE.y.card hE.ynd, (kchk_parts hT hC).2.2.2.2.1]

theorem Yx_le_normQx : Yx i D ≤ normalizer ((Qx i D : Subgroup ↥(GB i)) : Set ↥(GB i)) :=
  fun _ hy => mem_normalizer_subgroupOf (kY_le_normQ hT hE hC hy)

theorem Kx_le_normQx : Kx i D ≤ normalizer ((Qx i D : Subgroup ↥(GB i)) : Set ↥(GB i)) :=
  sup_le (Yx_le_normQx hT hE hC) fun _ hs => mem_normalizer_subgroupOf (kS_le_normQ hT hE hC hs)

theorem Mx_eq : Mx i D = (closureC D.qGen ⊔ closureC D.yGen).subgroupOf (GB i) :=
  (subgroupOf_sup (kQ_le_GB hT hE hC) (kY_le_GB hT hC)).symm

theorem Kx_le_normMx : Kx i D ≤ normalizer ((Mx i D : Subgroup ↥(GB i)) : Set ↥(GB i)) := by
  rw [Mx_eq hT hE hC]
  exact sup_le (fun y hy => mem_normalizer_subgroupOf (kY_le_normM hT hE hC hy))
    (fun s hs => mem_normalizer_subgroupOf (kS_le_normM hT hE hC hs))

theorem Qx_le_Sx : Qx i D ≤ Sx i D := fun _ hx => kQ_le_S hT hE hC hx

theorem Mx_le_Kx : Mx i D ≤ Kx i D :=
  sup_le ((Qx_le_Sx hT hE hC).trans le_sup_right) le_sup_left

theorem Kx_eq_sup : Kx i D = Mx i D ⊔ Sx i D :=
  le_antisymm (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    (sup_le (Mx_le_Kx hT hE hC) le_sup_right)

theorem Qx_inf_Yx : Qx i D ⊓ Yx i D = ⊥ := by
  apply inf_eq_bot_of_coprime
  rw [card_Qx hT hE hC, card_Yx hT hE hC]
  exact Nat.Coprime.pow _ _ (by norm_num)

theorem card_Mx : Nat.card (Mx i D) = 2 ^ D.qn * 3 ^ D.yn := by
  have h := card_sup_mul_card_inf (Yx_le_normQx hT hE hC)
  rw [Qx_inf_Yx hT hE hC, card_bot, mul_one, card_Yx hT hE hC, card_Qx hT hE hC, sup_comm] at h
  rw [Mx, h, mul_comm]

theorem card_Mx_inf_Sx : Nat.card (Mx i D ⊓ Sx i D : Subgroup ↥(GB i)) = 2 ^ D.qn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Sx i D) := IsPGroup.of_card (card_Sx hT hE hC)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hp.to_inf_right (H := Mx i D))
  have hdvd : 2 ^ k ∣ 2 ^ D.qn * 3 ^ D.yn := by
    rw [← hk, ← card_Mx hT hE hC]
    exact card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (2 ^ k) (3 ^ D.yn) := Nat.Coprime.pow _ _ (by norm_num)
  have h1 : 2 ^ k ∣ 2 ^ D.qn := hcop.dvd_of_dvd_mul_right hdvd
  have h2 : 2 ^ D.qn ≤ 2 ^ k := by
    rw [← hk, ← card_Qx hT hE hC]
    exact card_le_of_le (le_inf le_sup_left (Qx_le_Sx hT hE hC))
  rw [hk]
  exact le_antisymm (Nat.le_of_dvd (by positivity) h1) h2

theorem card_Kx : Nat.card (Kx i D) = 2 ^ D.sn * 3 ^ D.yn := by
  have h := card_sup_mul_card_inf ((le_sup_right.trans (Kx_eq_sup hT hE hC).ge).trans
    (Kx_le_normMx hT hE hC))
  rw [card_Mx_inf_Sx hT hE hC, card_Sx hT hE hC, card_Mx hT hE hC, sup_comm,
    ← Kx_eq_sup hT hE hC] at h
  have hpos : 0 < 2 ^ D.qn := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h]; ring)


theorem Sx_le_Tb : Sx i D ≤ Tb i := fun _ hx => kS_le_TB hT hE hC hx

theorem Kx_inf_Tb (hTp : IsPGroup 2 (Tb i)) : Kx i D ⊓ Tb i = Sx i D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  symm
  refine eq_of_le_of_card_ge (le_inf le_sup_right (Sx_le_Tb hT hE hC)) ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hTp.to_inf_right (H := Kx i D))
  have hdvd : 2 ^ k ∣ 2 ^ D.sn * 3 ^ D.yn := by
    rw [← hk, ← card_Kx hT hE hC]
    exact card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (2 ^ k) (3 ^ D.yn) := Nat.Coprime.pow _ _ (by norm_num)
  rw [hk, card_Sx hT hE hC]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem relIndex_Sx_Kx : (Sx i D).relIndex (Kx i D) = 3 ^ D.yn := by
  have h := relIndex_mul_card (Sx i D) (Kx i D)
  rw [inf_eq_left.2 le_sup_right, card_Sx hT hE hC, card_Kx hT hE hC] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ D.sn) (by rw [h]; ring)

theorem relIndex_Yx_Kx : (Yx i D).relIndex (Kx i D) = 2 ^ D.sn := by
  have h := relIndex_mul_card (Yx i D) (Kx i D)
  rw [inf_eq_left.2 le_sup_left, card_Yx hT hE hC, card_Kx hT hE hC] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 3 ^ D.yn) h

theorem pow_three_mem_Qx {x : ↥(GB i)} (hx : x ∈ Mx i D) : x ^ 3 ∈ Qx i D := by
  refine pow_mem_of_mem_sup (Yx_le_normQx hT hE hC) hx fun b hb => ?_
  apply Subtype.ext
  apply code_injective
  have h3 := (kchk_parts hT hC).2.2.2.2.2.2.1 _ ((hE.y.mem b.1).1 hb)
  rw [Subgroup.coe_pow, pow_succ, pow_two, code_mul, code_mul, h3, Subgroup.coe_one, code_one]

theorem pow_two_mem_Mx (x : ↥(GB i)) (hx : x ∈ Kx i D) : x ^ 2 ^ D.sn ∈ Mx i D := by
  rw [Kx_eq_sup hT hE hC] at hx
  refine pow_mem_of_mem_sup ((le_sup_right.trans (Kx_eq_sup hT hE hC).ge).trans
    (Kx_le_normMx hT hE hC)) hx fun b hb => ?_
  have := pow_card_eq_one' (G := Sx i D) (x := ⟨b, hb⟩)
  rw [card_Sx hT hE hC] at this
  exact congrArg Subtype.val this

theorem irred_nine (h2 : D.yn = 2) : IrredOnFrattiniQuot (Sx i D) (Yx i D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hparts := kchk_parts hT hC
  have hY9 : Nat.card (Yx i D) = 3 ^ 2 := by rw [card_Yx hT hE hC, h2]
  have hcube : ∀ y ∈ Yx i D, y ^ 3 = 1 := by
    intro y hy
    apply Subtype.ext
    apply code_injective
    have h3 := hparts.2.2.2.2.2.2.1 _ ((hE.y.mem y.1).1 hy)
    rw [Subgroup.coe_pow, pow_succ, pow_two, code_mul, code_mul, h3, Subgroup.coe_one, code_one]
  have hfr : nineFrattini (Yx i D) = ⊥ := by
    unfold nineFrattini
    have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hY9).is_comm.comm
    rw [CFSG.Quasithin.H13.A5.frattini_eq_bot_of_forall Nat.prime_three hcomm
      (fun a => Subtype.ext (hcube a.1 a.2)), Subgroup.map_bot]
  refine ⟨?_, fun W hW1 hW2 hWn => ?_⟩
  · rw [hfr, bot_lt_iff_ne_bot]
    intro hb
    have := card_bot (G := ↥(GB i))
    rw [← hb, hY9] at this
    norm_num at this
  · rw [hfr]
    have hdvd : Nat.card W ∣ 3 ^ 2 := hY9 ▸ card_dvd_of_le hW2
    rcases (Nat.dvd_prime_pow Nat.prime_three).1 hdvd with ⟨k, hk, hWk⟩
    interval_cases k
    · left
      exact eq_bot_of_card_eq W (by rw [hWk]; rfl)
    · exfalso
      have hne : W ≠ ⊥ := by
        intro hb
        rw [hb, card_bot] at hWk
        norm_num at hWk
      obtain ⟨⟨w, hwW⟩, hw1⟩ := ne_bot_iff_exists_ne_one.1 hne
      have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hwY : w ∈ Yx i D := hW2 hwW
      have hwc : code w.1 ∈ D.yLit := (hE.y.mem w.1).1 hwY
      have hwne : code w.1 ≠ cid := fun h => hw1' (Subtype.ext (code_injective (h.trans code_one.symm)))
      rcases hparts.2.2.2.2.2.2.2.2.2.2.2.2 with h1 | h
      · omega
      rcases h _ hwc with h' | ⟨sc, hsc, hsY, hsw⟩
      · exact hwne h'
      obtain ⟨σ, hσS, rfl⟩ := hE.s.surj sc hsc
      set sX : ↥(GB i) := ⟨σ, kS_le_GB hT hE hC hσS⟩
      have hsN : sX ∈ normalizer ((Yx i D : Subgroup ↥(GB i)) : Set ↥(GB i)) := by
        apply mem_normalizer_subgroupOf
        apply mem_normalizer_of_map_le
        rw [closureC, MonoidHom.map_closure, closure_le]
        rintro _ ⟨y, hy, rfl⟩
        have := hsY _ hy
        rw [← code_conj] at this
        exact (hE.y.mem _).2 this
      have hconj : sX * w * sX⁻¹ ∈ W := hWn sX ⟨hσS, hsN⟩ w hwW
      have hord : orderOf w = 3 := orderOf_eq_prime (hcube w hwY) hw1'
      have hzW : zpowers w = W := by
        refine eq_of_le_of_card_ge (zpowers_le.2 hwW) ?_
        rw [Nat.card_zpowers, hord, hWk, pow_one]
      rw [← hzW] at hconj
      classical
      rw [mem_zpowers_iff_mem_range_orderOf, hord] at hconj
      simp only [Finset.mem_image, Finset.mem_range] at hconj
      obtain ⟨m, hm, hme⟩ := hconj
      apply hsw
      have hcode : code (sX * w * sX⁻¹).1 = cconj (code σ) (code w.1) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj]
      rw [← hcode, ← hme]
      interval_cases m
      · simp [code_one]
      · simp
      · simp [pow_two, code_mul]
    · right
      exact eq_of_le_of_card_ge hW2 (by rw [hWk, hY9])

theorem twoPTwoIrred_Kx (hTp : IsPGroup 2 (Tb i)) :
    TwoPTwoIrred (Kx i D) (Kx i D ⊓ Tb i) (Yx i D) 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hparts := kchk_parts hT hC
  rw [Kx_inf_Tb hT hE hC hTp]
  have hQn : (Qx i D).subgroupOf (Kx i D) |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer ((Qx_le_Sx hT hE hC).trans le_sup_right)).2
      (Kx_le_normQx hT hE hC)
  have hMn : (Mx i D).subgroupOf (Kx i D) |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer (Mx_le_Kx hT hE hC)).2 (Kx_le_normMx hT hE hC)
  have hO : E1.oTwoPTwo ↥(Kx i D) 3 = ⊤ := by
    refine E1.oTwoPTwo_eq_top_of_series (N₂ := (Qx i D).subgroupOf (Kx i D))
      (N₂p := (Mx i D).subgroupOf (Kx i D)) ?_ (fun x hx => ⟨1, ?_⟩) (fun q => ⟨D.sn, ?_⟩)
    · have hc : Nat.card ((Qx i D).subgroupOf (Kx i D)) = 2 ^ D.qn := by
        rw [Nat.card_congr (subgroupOfEquivOfLe ((Qx_le_Sx hT hE hC).trans le_sup_right)).toEquiv,
          card_Qx hT hE hC]
      exact IsPGroup.of_card hc
    · rw [mem_subgroupOf, pow_one, Subgroup.coe_pow]
      exact pow_three_mem_Qx hT hE hC hx
    · rw [mem_subgroupOf, Subgroup.coe_pow]
      exact pow_two_mem_Mx hT hE hC _ q.2
  refine ⟨⟨Nat.prime_three, by decide, hO, ⟨le_sup_right, IsPGroup.of_card (card_Sx hT hE hC), ?_⟩,
    ⟨le_sup_left, IsPGroup.of_card (card_Yx hT hE hC), ?_⟩⟩, ?_⟩
  · rw [relIndex_Sx_Kx hT hE hC]
    exact fun h => absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)) (by decide)
  · rw [relIndex_Yx_Kx hT hE hC]
    exact fun h => absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)) (by decide)
  · rcases hparts.2.2.2.2.2.1 with h1 | h2
    · exact NFF7.irredOnFrattiniQuot_of_card_prime Nat.prime_three (by rw [card_Yx hT hE hC, h1]; rfl)
    · exact irred_nine hT hE hC h2

end Main

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
