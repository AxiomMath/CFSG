module

public import CFSG.Quasithin.H13.J4TypeCheck
public import CFSG.Quasithin.H13.J4AutM22
public import CFSG.Quasithin.H13.J4TwoCore
public import CFSG.Quasithin.H13.J4PlusType
public import CFSG.GroupTheory.Fitting.CharacteristicP

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def hypElt (k : ℕ) : GL (Fin 112) (ZMod 2) := rProd (hypList k)

theorem prRep_hyp
    (k : ℕ) : PrRep (hypElt k) (hypPair k) := prRep_rProd _

@[expose] def hypProd (l : List ℕ) : GL (Fin 112) (ZMod 2) := (l.map hypElt).prod

theorem prRep_hypProd
    (l : List ℕ) : PrRep (hypProd l) (hypProdPair l) := by
  unfold hypProd hypProdPair
  suffices ∀ (acc : Pr) (g : GL (Fin 112) (ZMod 2)), PrRep g acc →
      PrRep (g * (l.map hypElt).prod) (l.foldl (fun acc k => prMul acc (hypPair k)) acc) by
    simpa using this prOne 1 PrRep.one
  induction l with
  | nil => intro acc g hg; simpa using hg
  | cons k l ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hg.mul (prRep_hyp k))

theorem rConjN_mem_P (j : ℕ) : rConjN j ∈ P := by
  unfold rConjN
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨_, rfl⟩)
  · exact P.one_mem

theorem rProd_mem_P (l : List ℕ) : rProd l ∈ P :=
  P.list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact rConjN_mem_P i

theorem hypElt_mem_P (k : ℕ) : hypElt k ∈ P := rProd_mem_P _

theorem t_mem_P : t ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)

theorem prRep_tPair : PrRep t tPair := prRep_t

theorem plusChecks_spec :
    (∀ i < 6, hypElt (2 * i) * hypElt (2 * i) = 1 ∧ hypElt (2 * i + 1) * hypElt (2 * i + 1) = 1 ∧
      hypElt (2 * i) * hypElt (2 * i + 1) * (hypElt (2 * i) * hypElt (2 * i + 1)) = t) ∧
    ∀ i < 6, ∀ j < 6, i ≠ j →
      hypElt (2 * i) * hypElt (2 * j) = hypElt (2 * j) * hypElt (2 * i) ∧
      hypElt (2 * i) * hypElt (2 * j + 1) = hypElt (2 * j + 1) * hypElt (2 * i) ∧
      hypElt (2 * i + 1) * hypElt (2 * j + 1) = hypElt (2 * j + 1) * hypElt (2 * i + 1) := by
  have h := plusChecks_eq
  simp only [plusChecks, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · obtain ⟨⟨ha, hb⟩, hab⟩ := h1 i hi
    have pa := prRep_hyp (2 * i)
    have pb := prRep_hyp (2 * i + 1)
    refine ⟨eq_of_eqRows (pa.mul pa).1 PrRep.one.1 ha, eq_of_eqRows (pb.mul pb).1 PrRep.one.1 hb,
      eq_of_eqRows ((pa.mul pb).mul (pa.mul pb)).1 prRep_tPair.1 hab⟩
  · have h3 := h2 i hi j hj
    rcases h3 with h3 | h3
    · exact absurd h3 hij
    obtain ⟨⟨e1, e2⟩, e3⟩ := h3
    have pai := prRep_hyp (2 * i)
    have pbi := prRep_hyp (2 * i + 1)
    have paj := prRep_hyp (2 * j)
    have pbj := prRep_hyp (2 * j + 1)
    exact ⟨eq_of_eqRows (pai.mul paj).1 (paj.mul pai).1 e1,
      eq_of_eqRows (pai.mul pbj).1 (pbj.mul pai).1 e2,
      eq_of_eqRows (pbi.mul pbj).1 (pbj.mul pbi).1 e3⟩

theorem genChecks_spec
    (j : ℕ) (hj : j < 12) :
    rConjN j = t ^ (rExprH.getD j ([], 0)).2 * hypProd (rExprH.getD j ([], 0)).1 := by
  have h := genChecks_eq
  simp only [genChecks, List.all_eq_true, List.mem_range] at h
  exact eq_of_eqRows (prRep_rConjN j).1 ((prRep_tPair.pow _).mul (prRep_hypProd _)).1 (h j hj)

theorem w0Check_spec :
    (wordProd uvGen ntWord ^ 11) * rConjN 0 * (wordProd uvGen ntWord ^ 11)⁻¹ * (rConjN 0)⁻¹ ≠ 1 ∧
    (wordProd uvGen ntWord ^ 11) * rConjN 0 * (wordProd uvGen ntWord ^ 11)⁻¹ * (rConjN 0)⁻¹ ≠
      t := by
  have h := w0Check_eq
  simp only [w0Check, Bool.and_eq_true] at h
  have pw : PrRep (wordProd uvGen ntWord ^ 11) w0Pair := (famRep_uv.word ntWord).pow 11
  have pr := prRep_rConjN 0
  have pc := ((pw.mul pr).mul pw.inv).mul pr.inv
  refine ⟨fun e => rowsMatrix_ne_of_rowsNe h.1 ?_, fun e => rowsMatrix_ne_of_rowsNe h.2 ?_⟩
  · rw [pc.1, e, rowsMatrix_idRows, Units.val_one]
  · rw [pc.1, e, prRep_tPair.1]

@[expose] def gWeak : GL (Fin 112) (ZMod 2) := wordProd baseGL weakWord

@[expose] def hWeak : GL (Fin 112) (ZMod 2) := (t * (gWeak⁻¹ * hypElt 0 * gWeak)) ^ 6 * gWeak⁻¹

theorem weakChecks_spec
    : hWeak⁻¹ * t * hWeak = hypElt 0 ∧ hypElt 0 ≠ t := by
  have h := weakChecks_eq
  simp only [weakChecks, Bool.and_eq_true] at h
  have pg : PrRep gWeak (prWord basePairs weakWord) := famRep_base.word weakWord
  have ph : PrRep hWeak weakPair :=
    ((prRep_tPair.mul ((pg.inv.mul (prRep_hyp 0)).mul pg)).pow 6).mul pg.inv
  refine ⟨eq_of_eqRows ((ph.inv.mul prRep_tPair).mul ph).1 (prRep_hyp 0).1 h.1, fun e => ?_⟩
  exact rowsMatrix_ne_of_rowsNe h.2 (by rw [(prRep_hyp 0).1, e, prRep_tPair.1])

@[expose] def hypP (k : ℕ) : P := ⟨hypElt k, hypElt_mem_P k⟩

@[expose] def tInP : P := ⟨t, t_mem_P⟩

theorem rExprH_lt : ∀ j < 12, ∀ k ∈ (rExprH.getD j ([], 0)).1, k < 12 := by decide

theorem hypElt_mem_closure {k : ℕ} (hk : k < 12) :
    hypElt k ∈ Subgroup.closure (Set.range (fun i : Fin 6 => hypElt (2 * i)) ∪
      Set.range (fun i : Fin 6 => hypElt (2 * i + 1))) := by
  apply Subgroup.subset_closure
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact Or.inl ⟨⟨m, by omega⟩, by simp only; ring_nf⟩
  · exact Or.inr ⟨⟨m, by omega⟩, rfl⟩

theorem closure_hypElt
    : Subgroup.closure (Set.range (fun i : Fin 6 => hypElt (2 * i)) ∪
    Set.range (fun i : Fin 6 => hypElt (2 * i + 1))) = P := by
  set T := Set.range (fun i : Fin 6 => hypElt (2 * i)) ∪
    Set.range (fun i : Fin 6 => hypElt (2 * i + 1))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> exact hypElt_mem_P _
  · have ht : t ∈ Subgroup.closure T := by
      rw [← (plusChecks_spec.1 0 (by norm_num)).2.2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hypElt_mem_closure (by norm_num))
        (hypElt_mem_closure (by norm_num))) (Subgroup.mul_mem _ (hypElt_mem_closure
          (by norm_num)) (hypElt_mem_closure (by norm_num)))
    rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact ht
    · have e : rConj i = rConjN i := by rw [rConjN, dite_eq_left i.2]
      rw [SetLike.mem_coe, e, genChecks_spec i i.2]
      refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ht _) ?_
      unfold hypProd
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact hypElt_mem_closure (rExprH_lt i i.2 k hk)

theorem closure_hypP
    : Subgroup.closure (Set.range (fun i : Fin 6 => hypP (2 * i)) ∪
    Set.range (fun i : Fin 6 => hypP (2 * i + 1))) = ⊤ := by
  apply Subgroup.map_injective P.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_union,
    ← Set.range_comp, ← Set.range_comp]
  exact closure_hypElt

theorem nonempty_mulEquiv_P
    : Nonempty (P ≃* D8CentralProduct 6) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [card_P]; norm_num)
  refine nonempty_mulEquiv_D8CentralProduct (G := P) (n := 6) (by norm_num)
    (fun i => hypP (2 * i)) (fun i => hypP (2 * i + 1)) tInP (fun i => ?_) (fun i => ?_)
    (fun i => ?_) ?_ (fun i j hij => ?_) closure_hypP (by rw [card_P])
  · apply Subtype.ext
    rw [sq]
    exact (plusChecks_spec.1 i i.2).1
  · apply Subtype.ext
    rw [sq]
    exact (plusChecks_spec.1 i i.2).2.1
  · apply Subtype.ext
    rw [sq]
    exact (plusChecks_spec.1 i i.2).2.2
  · apply Subtype.ext
    rw [sq]
    exact t_mul_t
  · have h := plusChecks_spec.2 i i.2 j j.2 (fun e => hij (Fin.ext e))
    exact ⟨Subtype.ext h.1, Subtype.ext h.2.1, Subtype.ext h.2.2⟩

theorem center_M22
    : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M22 = ⊥ := by
  obtain ⟨-, hnt, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M22)
    with h | h
  · exact h
  · exfalso
    have hc : commutator ↥CFSG.Blueprint.NativeSporadic.M22 = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) y
      exact this
    rw [commutator_M22] at hc
    exact (top_ne_bot (α := Subgroup ↥CFSG.Blueprint.NativeSporadic.M22)) hc

theorem normal_mulAut_M22
    (X : Subgroup (MulAut ↥CFSG.Blueprint.NativeSporadic.M22))
    (hX : X.Normal) : X = ⊥ ∨ inner ↥CFSG.Blueprint.NativeSporadic.M22 ≤ X := by
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have hY : (X.comap (MulAut.conj : ↥CFSG.Blueprint.NativeSporadic.M22 →*
      MulAut ↥CFSG.Blueprint.NativeSporadic.M22)).Normal := hX.comap _
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hY with h | h
  · left
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun m => ?_
    have hmem : MulAut.conj (φ m * m⁻¹) ∈ X := by
      rw [map_mul, map_inv]
      have e : MulAut.conj (φ m) = φ * MulAut.conj m * φ⁻¹ := by
        refine MulEquiv.ext fun x => ?_
        simp [MulAut.conj_apply, MulAut.mul_apply]
      rw [e]
      have := X.mul_mem hφ (hX.conj_mem _ (X.inv_mem hφ) (MulAut.conj m))
      rw [show φ * MulAut.conj m * φ⁻¹ * (MulAut.conj m)⁻¹ =
        φ * (MulAut.conj m * φ⁻¹ * (MulAut.conj m)⁻¹) by group]
      exact this
    have h1 : φ m * m⁻¹ ∈ (⊥ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22) := by
      rw [← h]
      exact hmem
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    rw [MulAut.one_apply]
    exact h1
  · right
    rintro _ ⟨m, rfl⟩
    have : m ∈ X.comap (MulAut.conj : ↥CFSG.Blueprint.NativeSporadic.M22 →*
        MulAut ↥CFSG.Blueprint.NativeSporadic.M22) := by
      rw [h]
      exact Subgroup.mem_top m
    exact this

theorem mem_Zq_of_prime
    {L : Subgroup QW} (hL : L ≤ Zq) (hne : L ≠ ⊥) : Zq ≤ L := by
  have hcard : Nat.card (L.subgroupOf Zq) ∣ 3 := by
    rw [← card_Zq]
    exact Subgroup.card_subgroup_dvd_card _
  rcases (Nat.dvd_prime Nat.prime_three).1 hcard with h | h
  · exfalso
    apply hne
    have h1 : L.subgroupOf Zq = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hL hx⟩ : Zq) ∈ L.subgroupOf Zq := hx
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · have h1 : L.subgroupOf Zq = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, card_Zq])
    intro x hx
    have : (⟨x, hx⟩ : Zq) ∈ L.subgroupOf Zq := by rw [h1]; exact Subgroup.mem_top _
    exact this

theorem commutator_eq_of_commute {G : Type*} [Group G] {z₁ z₂ a b : G} (h1a : Commute z₁ a)
    (h1b : Commute z₁ b) (h2a : Commute z₂ a) (h2b : Commute z₂ b) (h12 : Commute z₁ z₂) :
    z₁ * a * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have k1 : Commute z₁ (z₂ * b * a⁻¹) := (h12.mul_right h1b).mul_right h1a.inv_right
  have k2 : Commute z₂ (a * b * a⁻¹ * b⁻¹) :=
    ((h2a.mul_right h2b).mul_right h2a.inv_right).mul_right h2b.inv_right
  calc z₁ * a * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹
      = (z₁ * a) * (z₂ * b * a⁻¹) * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = a * (z₁ * (z₂ * b * a⁻¹)) * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by rw [h1a.eq]; group
    _ = (a * z₂) * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [k1.eq]; group
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [← h2a.eq]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [k2.eq, mul_inv_cancel_right]

theorem Zq_le_of_normal
    (L : Subgroup QW) (hL : L.Normal) (hne : L ≠ ⊥) : Zq ≤ L := by
  rcases normal_mulAut_M22 (L.map qToAut) (hL.map _ qToAut_surjective) with h | h
  · apply mem_Zq_of_prime _ hne
    rw [← ker_qToAut]
    intro x hx
    have : qToAut x ∈ L.map qToAut := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  ·
    have hCLZ : ∀ c ∈ CQ, ∃ l ∈ L, ∃ z ∈ Zq, c = z * l := by
      intro c hc
      have h1 : qToAut c ∈ L.map qToAut := h (map_qToAut_CQ ▸ ⟨c, hc, rfl⟩)
      obtain ⟨l, hl, hlc⟩ := h1
      refine ⟨l, hl, c * l⁻¹, ?_, by group⟩
      rw [← ker_qToAut, MonoidHom.mem_ker, map_mul, map_inv, hlc, mul_inv_cancel]
    have hcomm : ∀ c₁ ∈ CQ, ∀ c₂ ∈ CQ, c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ L := by
      intro c₁ h₁ c₂ h₂
      obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := hCLZ c₁ h₁
      obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := hCLZ c₂ h₂
      have hzc : ∀ z ∈ Zq, ∀ g ∈ CQ, Commute z g := fun z hz g hg =>
        Subgroup.mem_centralizer_iff.1 hg z hz
      have hl₁C : l₁ ∈ CQ := by
        have := CQ.mul_mem (CQ.inv_mem (Zq_le_CQ hz₁)) h₁
        rwa [inv_mul_cancel_left] at this
      have hl₂C : l₂ ∈ CQ := by
        have := CQ.mul_mem (CQ.inv_mem (Zq_le_CQ hz₂)) h₂
        rwa [inv_mul_cancel_left] at this
      rw [commutator_eq_of_commute (hzc _ hz₁ _ hl₁C) (hzc _ hz₁ _ hl₂C) (hzc _ hz₂ _ hl₁C)
        (hzc _ hz₂ _ hl₂C) (hzc _ hz₁ _ (Zq_le_CQ hz₂))]
      exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
    have hCL : CQ ≤ L := by
      have h1 : (commutator CQ).map CQ.subtype ≤ L := by
        rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.commutator_le]
        rintro _ ⟨c₁, -, rfl⟩ _ ⟨c₂, -, rfl⟩
        exact hcomm _ c₁.2 _ c₂.2
      rw [commutator_CQ, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1
    exact Zq_le_CQ.trans hCL

@[expose] def uvW (i : ℕ) : W := if i = 0 then ⟨u, u_mem_W⟩ else if i = 1 then ⟨v, v_mem_W⟩ else 1

theorem coe_uvW (i : ℕ) : W.subtype (uvW i) = uvGen i := by
  unfold uvW uvGen
  split_ifs <;> rfl

theorem mk_uvW
    (i : ℕ) : QuotientGroup.mk' (P.subgroupOf W) (uvW i) = uvQ i := by
  unfold uvW uvQ
  split_ifs <;> rfl

@[expose] def w0W : W := wordProd uvW ntWord ^ 11

theorem coe_w0W : (w0W : GL (Fin 112) (ZMod 2)) = wordProd uvGen ntWord ^ 11 := by
  have h := map_wordProd' W.subtype uvW ntWord
  have e : (fun i => W.subtype (uvW i)) = uvGen := funext coe_uvW
  rw [e] at h
  rw [w0W, Subgroup.coe_pow]
  congr 1

theorem mk_w0W
    : (QuotientGroup.mk w0W : QW) = zq := by
  show QuotientGroup.mk' (P.subgroupOf W) (wordProd uvW ntWord ^ 11) = wq ^ 11
  rw [map_pow, map_wordProd']
  congr 2
  funext i
  exact mk_uvW i

theorem mem_zpowers_t_cases
    {c : GL (Fin 112) (ZMod 2)} (hc : c ∈ Subgroup.zpowers t) :
    c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact t_mul_t
  have hk : t ^ k = t ^ (k % 2) := zpow_eq_zpow_emod k (by exact_mod_cast ht2)
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h, zpow_zero]
  · right; rw [hk, h, zpow_one]

theorem centralizer_P_le
    :
    Subgroup.centralizer ((P.subgroupOf W : Subgroup W) : Set W) ≤ P.subgroupOf W := by
  set D := Subgroup.centralizer ((P.subgroupOf W : Subgroup W) : Set W)
  have hDn : D.Normal := Subgroup.normal_centralizer
  set L := D.map (QuotientGroup.mk' (P.subgroupOf W))
  have hLn : L.Normal := hDn.map _ (QuotientGroup.mk'_surjective _)
  by_cases hL : L = ⊥
  · intro d hd
    have : (QuotientGroup.mk' (P.subgroupOf W) d) ∈ L := ⟨d, hd, rfl⟩
    rw [hL, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    obtain ⟨d, hd, hdz⟩ := Zq_le_of_normal L hLn hL (Subgroup.mem_zpowers zq)
    have hp : d⁻¹ * w0W ∈ P.subgroupOf W := by
      rw [← QuotientGroup.eq]
      rw [QuotientGroup.mk'_apply] at hdz
      rw [hdz, mk_w0W]
    set p := d⁻¹ * w0W with hp_def
    have hw : w0W = d * p := by rw [hp_def]; group
    have hpP : (p : GL (Fin 112) (ZMod 2)) ∈ P := hp
    have hr : rConjN 0 ∈ P := rConjN_mem_P 0
    have hPP : ⁅P, P⁆ = Subgroup.zpowers t := by
      rw [← secondLocal_extraspecial.2.1, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hc : (rConjN 0)⁻¹ * ((p : GL (Fin 112) (ZMod 2)) * rConjN 0 *
        (p : GL (Fin 112) (ZMod 2))⁻¹) ∈ Subgroup.zpowers t := by
      rw [← hPP]
      have := Subgroup.commutator_mem_commutator (P.inv_mem hr) hpP
      rw [commutatorElement_def, inv_inv] at this
      convert this using 1
      group
    have hdc : ∀ x ∈ P, (d : GL (Fin 112) (ZMod 2)) * x = x * d := by
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.1 hd ⟨x, P_le_W hx⟩
        (Subgroup.mem_subgroupOf.2 hx)
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
      exact h2.symm
    have hct : ∀ c ∈ Subgroup.zpowers t, ∀ g ∈ W, g * c = c * g := by
      intro c hc g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have ht : t ∈ Subgroup.centralizer ({g} : Set (GL (Fin 112) (ZMod 2))) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (Subgroup.mem_centralizer_iff.1 (W_le_centralizer hg) t (Set.mem_singleton t)).symm
      exact Subgroup.mem_centralizer_iff.1 ((Subgroup.centralizer _).zpow_mem ht k) g
        (Set.mem_singleton g)
    set c := (rConjN 0)⁻¹ * ((p : GL (Fin 112) (ZMod 2)) * rConjN 0 *
      (p : GL (Fin 112) (ZMod 2))⁻¹)
    have hprp : (p : GL (Fin 112) (ZMod 2)) * rConjN 0 * (p : GL (Fin 112) (ZMod 2))⁻¹ =
        rConjN 0 * c := by rw [mul_inv_cancel_left]
    have hrcP : rConjN 0 * c ∈ P := by
      rw [← hprp]
      exact P.mul_mem (P.mul_mem hpP hr) (P.inv_mem hpP)
    have key : (w0W : GL (Fin 112) (ZMod 2)) * rConjN 0 * (w0W : GL (Fin 112) (ZMod 2))⁻¹ *
        (rConjN 0)⁻¹ = c := by
      rw [hw, Subgroup.coe_mul]
      calc (d : GL (Fin 112) (ZMod 2)) * p * rConjN 0 * (d * p : GL (Fin 112) (ZMod 2))⁻¹ *
            (rConjN 0)⁻¹
          = d * (p * rConjN 0 * (p : GL (Fin 112) (ZMod 2))⁻¹) * (d : GL (Fin 112) (ZMod 2))⁻¹ *
            (rConjN 0)⁻¹ := by group
        _ = d * (rConjN 0 * c) * (d : GL (Fin 112) (ZMod 2))⁻¹ * (rConjN 0)⁻¹ := by rw [hprp]
        _ = rConjN 0 * c * d * (d : GL (Fin 112) (ZMod 2))⁻¹ * (rConjN 0)⁻¹ := by
            rw [hdc _ hrcP]
        _ = rConjN 0 * c * (rConjN 0)⁻¹ := by group
        _ = c * rConjN 0 * (rConjN 0)⁻¹ := by rw [hct c hc _ (rConjN_mem_W 0)]
        _ = c := by group
    rw [coe_w0W] at key
    have := w0Check_spec
    rcases mem_zpowers_t_cases hc with h | h
    · exact this.1 (key.trans h)
    · exact this.2 (key.trans h)

theorem isCharacteristicP_W
    : CFSG.IsCharacteristicP 2 W := by
  unfold CFSG.IsCharacteristicP
  rw [pCore_W]
  exact centralizer_P_le

theorem generalizedFitting_W
    : CFSG.generalizedFitting W = CFSG.pCore 2 W := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [card_W]; norm_num)
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore W 2).1 isCharacteristicP_W

end CFSG.Quasithin.H13.J4
