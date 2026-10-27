module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.RankThree.GF2n.Parrott.FusionE16Defs
public import CFSG.RankThree.GF2n.Parrott.FusionE16Check

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

private theorem getD_tab {v : ℕ} (hv : v < 16) (r0 r1 r2 r3 : ℕ) :
    (tab r0 r1 r2 r3).getD v 0 = vmul v r0 r1 r2 r3 := by
  simp [tab, List.getD_eq_getElem?_getD, hv]

private theorem getD_comp {v : ℕ} (hv : v < 16) (t u : List ℕ) :
    (comp t u).getD v 0 = t.getD (u.getD v 0) 0 := by
  simp [comp, List.getD_eq_getElem?_getD, hv]

private theorem getD_idTab {v : ℕ} (hv : v < 16) : idTab.getD v 0 = v := by
  simp [idTab, List.getD_eq_getElem?_getD, hv]

private theorem length_comp (t u : List ℕ) : (comp t u).length = 16 := by
  simp [comp]

private theorem eq_idTab_of_getD {L : List ℕ} (hL : L.length = 16) (h : ∀ v < 16, L.getD v 0 = v) :
    L = idTab := by
  refine List.ext_getElem (by simp [hL, idTab]) fun n h1 h2 => ?_
  have := h n (hL ▸ h1)
  rw [List.getD_eq_getElem _ _ h1] at this
  simpa [idTab] using this

private theorem getD_lt {T : List ℕ} (h : ∀ x ∈ T, x < 16) (w : ℕ) : T.getD w 0 < 16 := by
  rcases lt_or_ge w T.length with hw | hw
  · rw [List.getD_eq_getElem _ _ hw]
    exact h _ (List.getElem_mem hw)
  · rw [List.getD_eq_default _ _ hw]
    norm_num

private theorem forall_lt_comp {t : List ℕ} (ht : ∀ x ∈ t, x < 16) (u : List ℕ) :
    ∀ x ∈ comp t u, x < 16 := by
  intro x hx
  simp only [comp, List.mem_map, List.mem_range] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact getD_lt ht _

private theorem vmul_lt {v r0 r1 r2 r3 : ℕ} (h0 : r0 < 16) (h1 : r1 < 16) (h2 : r2 < 16)
    (h3 : r3 < 16) : vmul v r0 r1 r2 r3 < 16 := by
  have hx : ∀ m n : ℕ, m < 16 → n < 16 → m ^^^ n < 16 := fun m n hm hn =>
    Nat.xor_lt_two_pow (n := 4) hm hn
  unfold vmul
  refine hx _ _ (hx _ _ (hx _ _ ?_ ?_) ?_) ?_ <;> split_ifs <;> first | assumption | norm_num

private theorem forall_lt_tab {r0 r1 r2 r3 : ℕ} (h0 : r0 < 16) (h1 : r1 < 16) (h2 : r2 < 16)
    (h3 : r3 < 16) : ∀ x ∈ tab r0 r1 r2 r3, x < 16 := by
  intro x hx
  simp only [tab, List.mem_map, List.mem_range] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact vmul_lt h0 h1 h2 h3

private theorem forall_lt_A4tabs : ∀ T ∈ A4tabs, ∀ x ∈ T, x < 16 := by decide +kernel

variable {X : Type} [Group X] [Finite X]

private theorem exists_conj_le_sylow {P Q : Subgroup X} (hP : ∃ R : Sylow 2 X, (R : Subgroup X) = P)
    (hQ : IsPGroup 2 Q) : ∃ c : X, ∀ q ∈ Q, c⁻¹ * q * c ∈ P := by
  classical
  obtain ⟨R, rfl⟩ := hP
  obtain ⟨R', hR'⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R R'
  refine ⟨c, fun q hq => ?_⟩
  have h1 : q ∈ ((c • R : Sylow 2 X) : Subgroup X) := by rw [hc]; exact hR' hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨r, hr, rfl⟩ := h1
  simp only [MulAut.smul_def, MulAut.conj_apply]
  have h3 : c⁻¹ * (c * r * c⁻¹) * c = r := by group
  rw [h3]
  exact hr

private theorem conj_mem_of_unique {P S : Subgroup X}
    (hunique : ∀ E : Subgroup X, E ≤ P → CFSG.Open.IsElemAbelian 2 E → Nat.card E = Nat.card S →
      E = S)
    (hS : CFSG.Open.IsElemAbelian 2 S) {γ : X} (hSγ : ∀ s ∈ S, γ⁻¹ * s * γ ∈ P) :
    ∀ s ∈ S, γ * s * γ⁻¹ ∈ S ∧ γ⁻¹ * s * γ ∈ S := by
  have hER : S.map (MulAut.conj γ⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using hSγ s hs
  have hEel : CFSG.Open.IsElemAbelian 2 (S.map (MulAut.conj γ⁻¹).toMonoidHom) :=
    hS.map (MulAut.conj γ⁻¹).toMonoidHom
  have hEcard : Nat.card (S.map (MulAut.conj γ⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj γ⁻¹).injective
  have hEeq := hunique _ hER hEel hEcard
  intro s hs
  refine ⟨?_, ?_⟩
  · have h' : s ∈ S.map (MulAut.conj γ⁻¹).toMonoidHom := by rw [hEeq]; exact hs
    obtain ⟨s', hs', hss'⟩ := h'
    have : γ * s * γ⁻¹ = s' := by
      rw [← hss']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hs'
  · have h' : γ⁻¹ * s * γ ∈ S.map (MulAut.conj γ⁻¹).toMonoidHom :=
      ⟨s, hs, by simp [MulAut.conj_apply]⟩
    rw [hEeq] at h'
    exact h'

theorem exists_conj_normalizer_of_central_sylow {x y : X} {P S Q : Subgroup X}
    (hP : ∃ R : Sylow 2 X, (R : Subgroup X) = P) (hxP : x ∈ P) (hxc : ∀ p ∈ P, p * x = x * p)
    (hSP : S ≤ P) (hunique : ∀ E : Subgroup X, E ≤ P → CFSG.Open.IsElemAbelian 2 E →
      Nat.card E = Nat.card S → E = S)
    (hS : CFSG.Open.IsElemAbelian 2 S) (hyS : y ∈ S) (hQ : IsPGroup 2 Q) (hSQ : S ≤ Q)
    (hQy : ∀ q ∈ Q, q * y = y * q) (hxy : IsConj x y) :
    ∃ γ : X, γ * x * γ⁻¹ = y ∧ (∀ s ∈ S, γ * s * γ⁻¹ ∈ S ∧ γ⁻¹ * s * γ ∈ S) ∧
      ∀ q ∈ Q, γ⁻¹ * q * γ ∈ P := by
  classical
  obtain ⟨R, rfl⟩ := hP
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  set D : Subgroup X := Subgroup.centralizer ({y} : Set X) with hD
  have hcR : ((c • R : Sylow 2 X) : Subgroup X) ≤ D := by
    intro g hg
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hg
    obtain ⟨r, hr, rfl⟩ := hg
    rw [hD, Subgroup.mem_centralizer_singleton_iff, ← hc]
    have := hxc r hr
    simp only [MulAut.smul_def, MulAut.conj_apply]
    calc c * r * c⁻¹ * (c * x * c⁻¹) = c * (r * x) * c⁻¹ := by group
      _ = c * (x * r) * c⁻¹ := by rw [this]
      _ = c * x * c⁻¹ * (c * r * c⁻¹) := by group
  have hQD : Q ≤ D := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQy q hq)
  obtain ⟨T, hT⟩ := (hQ.comap_subtype (K := D)).exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D ((c • R).subtype hcR) T
  have hQγ : ∀ q ∈ Q, ((d : X) * c)⁻¹ * q * ((d : X) * c) ∈ (R : Subgroup X) := by
    intro q hq
    have h1 : (⟨q, hQD hq⟩ : D) ∈ (T : Subgroup D) := hT (Subgroup.mem_subgroupOf.mpr hq)
    rw [← hd, Sylow.smul_subtype] at h1
    have h2 : q ∈ ((d • c • R : Sylow 2 X) : Subgroup X) :=
      Subgroup.mem_subgroupOf.mp h1
    simp only [Subgroup.smul_def, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists,
      MulAut.smul_def, MulAut.conj_apply] at h2
    obtain ⟨s, ⟨r, hr, rfl⟩, rfl⟩ := h2
    have h3 : ((d : X) * c)⁻¹ * ((d : X) * (c * r * c⁻¹) * (d : X)⁻¹) * ((d : X) * c) = r := by
      group
    rw [h3]
    exact hr
  refine ⟨(d : X) * c, ?_, ?_, hQγ⟩
  · calc (d : X) * c * x * ((d : X) * c)⁻¹ = (d : X) * (c * x * c⁻¹) * (d : X)⁻¹ := by group
      _ = y := by
        rw [hc]
        have := Subgroup.mem_centralizer_singleton_iff.mp d.2
        calc (d : X) * y * (d : X)⁻¹ = y * (d : X) * (d : X)⁻¹ := by rw [this]
          _ = y := by group
  · exact conj_mem_of_unique hunique hS fun s hs => hQγ s (hSQ hs)

namespace E16Config

variable (cfg : E16Config X)

private def vecOf (n : ℕ) : Fin 4 → ZMod 2 := fun i => if n.testBit i then 1 else 0

private theorem vecOf_xor (m n : ℕ) : vecOf (m ^^^ n) = vecOf m + vecOf n := by
  funext i
  simp only [vecOf, Nat.testBit_xor, Pi.add_apply]
  cases m.testBit i <;> cases n.testBit i <;> decide

private theorem vecOf_inj : ∀ m < 16, ∀ n < 16, vecOf m = vecOf n → m = n := by
  decide +kernel

private theorem vecOf_surj : ∀ v : Fin 4 → ZMod 2, ∃ n < 16, vecOf n = v := by
  decide +kernel

private theorem exists_coords :
    ∃ ev : ℕ → X, (∀ m n, ev (m ^^^ n) = ev m * ev n) ∧ ev 1 = cfg.u 0 ∧ ev 2 = cfg.u 1 ∧
      ev 4 = cfg.u 2 ∧ ev 8 = cfg.u 3 ∧ (∀ m < 16, ∀ n < 16, ev m = ev n → m = n) ∧
      (∀ s ∈ Subgroup.closure (Set.range cfg.u), ∃ n < 16, ev n = s) ∧
      (∀ n, ev n ∈ Subgroup.closure (Set.range cfg.u)) := by
  obtain ⟨η, hη, hinj, hrange, -, -⟩ := CFSG.Sporadic.GLQ.exists_elemAbelian_two cfg.u cfg.hsq
    cfg.hcomm cfg.hker
  have hv1 : ZMod.val (1 : ZMod 2) = 1 := rfl
  refine ⟨fun n => η (Multiplicative.ofAdd (vecOf n)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n
    dsimp only
    rw [vecOf_xor, ofAdd_add, map_mul]
  · have h1 : vecOf 1 = ![1, 0, 0, 0] := by decide +kernel
    dsimp only; rw [hη, h1]; simp [List.ofFn_succ, hv1]
  · have h1 : vecOf 2 = ![0, 1, 0, 0] := by decide +kernel
    dsimp only; rw [hη, h1]; simp [List.ofFn_succ, hv1]
  · have h1 : vecOf 4 = ![0, 0, 1, 0] := by decide +kernel
    dsimp only; rw [hη, h1]; simp [List.ofFn_succ, hv1]
  · have h1 : vecOf 8 = ![0, 0, 0, 1] := by decide +kernel
    dsimp only; rw [hη, h1]; simp [List.ofFn_succ, hv1]
  · intro m hm n hn h
    exact vecOf_inj m hm n hn (Multiplicative.ofAdd.injective (hinj h))
  · intro s hs
    rw [← hrange] at hs
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨n, hn, hvn⟩ := vecOf_surj (Multiplicative.toAdd a)
    exact ⟨n, hn, by simp [hvn]⟩
  · intro n
    rw [← hrange]
    exact ⟨_, rfl⟩

noncomputable def ev : ℕ → X := Classical.choose cfg.exists_coords

theorem ev_xor (m n : ℕ) : cfg.ev (m ^^^ n) = cfg.ev m * cfg.ev n :=
  (Classical.choose_spec cfg.exists_coords).1 m n

theorem ev_one : cfg.ev 1 = cfg.u 0 := (Classical.choose_spec cfg.exists_coords).2.1

theorem ev_two : cfg.ev 2 = cfg.u 1 := (Classical.choose_spec cfg.exists_coords).2.2.1

theorem ev_four : cfg.ev 4 = cfg.u 2 := (Classical.choose_spec cfg.exists_coords).2.2.2.1

theorem ev_eight : cfg.ev 8 = cfg.u 3 := (Classical.choose_spec cfg.exists_coords).2.2.2.2.1

theorem ev_inj : ∀ m < 16, ∀ n < 16, cfg.ev m = cfg.ev n → m = n :=
  (Classical.choose_spec cfg.exists_coords).2.2.2.2.2.1

theorem exists_ev_eq : ∀ s ∈ Subgroup.closure (Set.range cfg.u), ∃ n < 16, cfg.ev n = s :=
  (Classical.choose_spec cfg.exists_coords).2.2.2.2.2.2.1

theorem ev_mem (n : ℕ) : cfg.ev n ∈ Subgroup.closure (Set.range cfg.u) :=
  (Classical.choose_spec cfg.exists_coords).2.2.2.2.2.2.2 n

theorem ev_zero : cfg.ev 0 = 1 := by
  have h := cfg.ev_xor 0 0
  simpa using h

theorem isElemAbelian_S : CFSG.Open.IsElemAbelian 2 (Subgroup.closure (Set.range cfg.u)) ∧
    Nat.card (Subgroup.closure (Set.range cfg.u)) = 16 := by
  obtain ⟨η, -, -, -, -, hcard⟩ := CFSG.Sporadic.GLQ.exists_elemAbelian_two cfg.u cfg.hsq
    cfg.hcomm cfg.hker
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun s hs => ?_⟩, by simpa using hcard⟩
  · obtain ⟨m, -, hm⟩ := cfg.exists_ev_eq _ a.2
    obtain ⟨n, -, hn⟩ := cfg.exists_ev_eq _ b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← hm, ← hn, ← cfg.ev_xor, ← cfg.ev_xor, Nat.xor_comm]
  · obtain ⟨n, -, rfl⟩ := cfg.exists_ev_eq _ hs
    rw [sq, ← cfg.ev_xor, Nat.xor_self, cfg.ev_zero]

private theorem comm_u0_of_mem_P {p : X} (hp : p ∈ cfg.P) : p * cfg.u 0 = cfg.u 0 * p := by
  obtain ⟨s, hs, i, j, rfl⟩ := cfg.hPcos p hp
  have hSel := (cfg.isElemAbelian_S).1
  have hsc : s * cfg.u 0 = cfg.u 0 * s :=
    hSel.comm hs (Subgroup.subset_closure ⟨0, rfl⟩)
  have hac : cfg.a * cfg.u 0 = cfg.u 0 * cfg.a := by
    have := cfg.act_a.1
    calc cfg.a * cfg.u 0 = (cfg.a * cfg.u 0 * cfg.a⁻¹) * cfg.a := by group
      _ = cfg.u 0 * cfg.a := by rw [this]
  have hbc : cfg.b₁ * cfg.u 0 = cfg.u 0 * cfg.b₁ := by
    have := cfg.act_b.1
    calc cfg.b₁ * cfg.u 0 = (cfg.b₁ * cfg.u 0 * cfg.b₁⁻¹) * cfg.b₁ := by group
      _ = cfg.u 0 * cfg.b₁ := by rw [this]
  have h1 : Commute (s * cfg.a ^ (i : ℕ) * cfg.b₁ ^ (j : ℕ)) (cfg.u 0) :=
    ((Commute.mul_left (hsc) ((Commute.pow_left hac _))).mul_left (Commute.pow_left hbc _))
  exact h1.eq

private theorem exists_gamma (h : IsConj (cfg.u 0) (cfg.u 1)) :
    ∃ γ : X, γ * cfg.u 0 * γ⁻¹ = cfg.u 1 ∧
      ∀ s ∈ Subgroup.closure (Set.range cfg.u),
        γ * s * γ⁻¹ ∈ Subgroup.closure (Set.range cfg.u) ∧
        γ⁻¹ * s * γ ∈ Subgroup.closure (Set.range cfg.u) := by
  obtain ⟨hSel, hScard⟩ := cfg.isElemAbelian_S
  have hSP : Subgroup.closure (Set.range cfg.u) ≤ cfg.P :=
    (Subgroup.closure_le cfg.P).mpr (by rintro _ ⟨i, rfl⟩; exact cfg.hSP i)
  obtain ⟨R, hR⟩ := cfg.hPsyl
  have hP2 : IsPGroup 2 cfg.P := hR ▸ R.isPGroup'
  obtain ⟨γ, hγx, hγS, -⟩ := exists_conj_normalizer_of_central_sylow ⟨R, hR⟩ (cfg.hSP 0)
    (fun p hp => cfg.comm_u0_of_mem_P hp) hSP
    (fun E hE hEel hEc => cfg.hunique E hE hEel (hEc.trans hScard)) hSel
    (Subgroup.subset_closure ⟨1, rfl⟩) (hP2.to_le hSP) le_rfl
    (fun q hq => hSel.comm hq (Subgroup.subset_closure ⟨1, rfl⟩)) h
  exact ⟨γ, hγx, hγS⟩


private theorem ev_comm (m n : ℕ) : cfg.ev m * cfg.ev n = cfg.ev n * cfg.ev m := by
  rw [← cfg.ev_xor, ← cfg.ev_xor, Nat.xor_comm]

private theorem conj_ev_of_mem {g : X} (hg : g ∈ Subgroup.closure (Set.range cfg.u)) (v : ℕ) :
    g * cfg.ev v * g⁻¹ = cfg.ev v := by
  have := (cfg.isElemAbelian_S).1.comm hg (cfg.ev_mem v)
  rw [this]
  group

private theorem acts_of_basis {g : X} {r0 r1 r2 r3 : ℕ}
    (h0 : g * cfg.ev 1 * g⁻¹ = cfg.ev r0) (h1 : g * cfg.ev 2 * g⁻¹ = cfg.ev r1)
    (h2 : g * cfg.ev 4 * g⁻¹ = cfg.ev r2) (h3 : g * cfg.ev 8 * g⁻¹ = cfg.ev r3) :
    ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (vmul v r0 r1 r2 r3) := by
  have hdec : ∀ v < 16, v = (if v.testBit 0 then 1 else 0) ^^^ (if v.testBit 1 then 2 else 0) ^^^
      (if v.testBit 2 then 4 else 0) ^^^ (if v.testBit 3 then 8 else 0) := by decide +kernel
  have key : ∀ (b : Prop) [Decidable b] (k r : ℕ), g * cfg.ev k * g⁻¹ = cfg.ev r →
      g * cfg.ev (if b then k else 0) * g⁻¹ = cfg.ev (if b then r else 0) := by
    intro b _ k r h
    by_cases hb : b
    · simpa [hb] using h
    · simp [hb, cfg.ev_zero]
  intro v hv
  have e0 := key (v.testBit 0 = true) 1 r0 h0
  have e1 := key (v.testBit 1 = true) 2 r1 h1
  have e2 := key (v.testBit 2 = true) 4 r2 h2
  have e3 := key (v.testBit 3 = true) 8 r3 h3
  conv_lhs => rw [hdec v hv]
  unfold vmul
  simp only [cfg.ev_xor]
  rw [← e0, ← e1, ← e2, ← e3]
  group

private theorem exists_rows {g : X} (hg : ∀ s ∈ Subgroup.closure (Set.range cfg.u),
      g * s * g⁻¹ ∈ Subgroup.closure (Set.range cfg.u)) :
    ∃ r0 < 16, ∃ r1 < 16, ∃ r2 < 16, ∃ r3 < 16,
      ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (vmul v r0 r1 r2 r3) := by
  have hn : ∀ k, ∃ r < 16, g * cfg.ev k * g⁻¹ = cfg.ev r := fun k => by
    obtain ⟨n, hn, h⟩ := cfg.exists_ev_eq _ (hg _ (cfg.ev_mem k))
    exact ⟨n, hn, h.symm⟩
  obtain ⟨r0, hr0, h0⟩ := hn 1
  obtain ⟨r1, hr1, h1⟩ := hn 2
  obtain ⟨r2, hr2, h2⟩ := hn 4
  obtain ⟨r3, hr3, h3⟩ := hn 8
  exact ⟨r0, hr0, r1, hr1, r2, hr2, r3, hr3, cfg.acts_of_basis h0 h1 h2 h3⟩

private theorem acts_comp {g h : X} {T U : List ℕ}
    (hg : ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (T.getD v 0))
    (hh : ∀ v < 16, h * cfg.ev v * h⁻¹ = cfg.ev (U.getD v 0)) (hU : ∀ x ∈ U, x < 16) :
    ∀ v < 16, (g * h) * cfg.ev v * (g * h)⁻¹ = cfg.ev ((comp T U).getD v 0) := by
  intro v hv
  rw [getD_comp hv]
  calc g * h * cfg.ev v * (g * h)⁻¹ = g * (h * cfg.ev v * h⁻¹) * g⁻¹ := by group
    _ = g * cfg.ev (U.getD v 0) * g⁻¹ := by rw [hh v hv]
    _ = cfg.ev (T.getD (U.getD v 0) 0) := hg _ (getD_lt hU v)

private theorem acts_of_eq {g : X} {T T' : List ℕ} (h : T = T')
    (hg : ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (T.getD v 0)) :
    ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (T'.getD v 0) := h ▸ hg

private theorem acts_a :
    ∀ v < 16, cfg.a * cfg.ev v * cfg.a⁻¹ = cfg.ev ((tab 1 2 5 11).getD v 0) := by
  intro v hv
  rw [getD_tab hv]
  obtain ⟨h0, h1, h2, h3⟩ := cfg.act_a
  refine cfg.acts_of_basis ?_ ?_ ?_ ?_ v hv
  · rw [cfg.ev_one]; exact h0
  · rw [cfg.ev_two]; exact h1
  · rw [cfg.ev_four, show (5 : ℕ) = 1 ^^^ 4 by decide, cfg.ev_xor, cfg.ev_one, cfg.ev_four]
    exact h2
  · rw [cfg.ev_eight, show (11 : ℕ) = 1 ^^^ 2 ^^^ 8 by decide, cfg.ev_xor, cfg.ev_xor,
      cfg.ev_one, cfg.ev_two, cfg.ev_eight]
    exact h3

private theorem acts_b :
    ∀ v < 16, cfg.b₁ * cfg.ev v * cfg.b₁⁻¹ = cfg.ev ((tab 1 3 4 13).getD v 0) := by
  intro v hv
  rw [getD_tab hv]
  obtain ⟨h0, h1, h2, h3⟩ := cfg.act_b
  refine cfg.acts_of_basis ?_ ?_ ?_ ?_ v hv
  · rw [cfg.ev_one]; exact h0
  · rw [show (3 : ℕ) = 1 ^^^ 2 by decide, cfg.ev_xor, cfg.ev_one, cfg.ev_two]
    exact h1
  · rw [cfg.ev_four]; exact h2
  · rw [cfg.ev_eight, show (13 : ℕ) = 1 ^^^ 4 ^^^ 8 by decide, cfg.ev_xor, cfg.ev_xor,
      cfg.ev_one, cfg.ev_four, cfg.ev_eight]
    exact h3

private theorem acts_ρ :
    ∀ v < 16, cfg.ρ * cfg.ev v * cfg.ρ⁻¹ = cfg.ev ((tab 1 4 6 8).getD v 0) := by
  intro v hv
  rw [getD_tab hv]
  obtain ⟨h0, h1, h2, h3⟩ := cfg.act_ρ
  refine cfg.acts_of_basis ?_ ?_ ?_ ?_ v hv
  · rw [cfg.ev_one]; exact h0
  · rw [cfg.ev_two, cfg.ev_four]; exact h1
  · rw [cfg.ev_four, show (6 : ℕ) = 2 ^^^ 4 by decide, cfg.ev_xor, cfg.ev_two, cfg.ev_four]
    exact h2
  · rw [cfg.ev_eight]; exact h3

private theorem exists_A4_elems : ∀ T ∈ A4tabs, ∃ g : X,
    ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (T.getD v 0) := by
  have hZ := cfg.acts_ρ
  have hA := cfg.acts_a
  have hB := cfg.acts_b
  have bZ : ∀ x ∈ tab 1 4 6 8, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bA : ∀ x ∈ tab 1 2 5 11, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bB : ∀ x ∈ tab 1 3 4 13, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro T hT
  simp only [A4tabs, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cfg.ρ, hZ⟩
  · exact ⟨cfg.b₁ * cfg.ρ, cfg.acts_of_eq (by decide +kernel) (cfg.acts_comp hB hZ bZ)⟩
  · refine ⟨1, fun v hv => ?_⟩
    rw [getD_tab hv, show vmul v 1 2 4 8 = v from
      (by decide +kernel : ∀ v < 16, vmul v 1 2 4 8 = v) v hv]
    simp
  · exact ⟨cfg.a, hA⟩
  · exact ⟨cfg.ρ * cfg.ρ, cfg.acts_of_eq (by decide +kernel) (cfg.acts_comp hZ hZ bZ)⟩
  · exact ⟨cfg.a * (cfg.b₁ * (cfg.ρ * cfg.ρ)), cfg.acts_of_eq (by decide +kernel)
      (cfg.acts_comp hA (cfg.acts_comp hB (cfg.acts_comp hZ hZ bZ) (forall_lt_comp bZ _))
        (forall_lt_comp bB _))⟩
  · exact ⟨cfg.a * (cfg.b₁ * cfg.ρ), cfg.acts_of_eq (by decide +kernel)
      (cfg.acts_comp hA (cfg.acts_comp hB hZ bZ) (forall_lt_comp bB _))⟩
  · exact ⟨cfg.a * cfg.ρ, cfg.acts_of_eq (by decide +kernel) (cfg.acts_comp hA hZ bZ)⟩
  · exact ⟨cfg.b₁, hB⟩
  · exact ⟨cfg.a * cfg.b₁, cfg.acts_of_eq (by decide +kernel) (cfg.acts_comp hA hB bB)⟩
  · exact ⟨cfg.a * (cfg.ρ * cfg.ρ), cfg.acts_of_eq (by decide +kernel)
      (cfg.acts_comp hA (cfg.acts_comp hZ hZ bZ) (forall_lt_comp bZ _))⟩
  · exact ⟨cfg.b₁ * (cfg.ρ * cfg.ρ), cfg.acts_of_eq (by decide +kernel)
      (cfg.acts_comp hB (cfg.acts_comp hZ hZ bZ) (forall_lt_comp bZ _))⟩

theorem mem_zpowers_of_central {z : X} (hzP : z ∈ cfg.P) (hz : ∀ p ∈ cfg.P, z * p = p * z) :
    z ∈ Subgroup.zpowers (cfg.u 0) := by
  have hSP : Subgroup.closure (Set.range cfg.u) ≤ cfg.P :=
    (Subgroup.closure_le cfg.P).mpr (by rintro _ ⟨i, rfl⟩; exact cfg.hSP i)
  have hzS : z ∈ Subgroup.closure (Set.range cfg.u) :=
    cfg.hCS z fun s hs => hz s (hSP hs)
  obtain ⟨n, hn, rfl⟩ := cfg.exists_ev_eq z hzS
  have bA : ∀ x ∈ tab 1 2 5 11, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bB : ∀ x ∈ tab 1 3 4 13, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ca : cfg.a * cfg.ev n * cfg.a⁻¹ = cfg.ev n := by
    rw [← hz cfg.a cfg.haP]
    group
  have cb : cfg.b₁ * cfg.ev n * cfg.b₁⁻¹ = cfg.ev n := by
    rw [← hz cfg.b₁ cfg.hbP]
    group
  rw [cfg.acts_a n hn] at ca
  rw [cfg.acts_b n hn] at cb
  have ha' := cfg.ev_inj _ (getD_lt bA n) n hn ca
  have hb' := cfg.ev_inj _ (getD_lt bB n) n hn cb
  have hfix : ∀ n < 16, (tab 1 2 5 11).getD n 0 = n → (tab 1 3 4 13).getD n 0 = n →
      n = 0 ∨ n = 1 := by decide +kernel
  rcases hfix n hn ha' hb' with rfl | rfl
  · rw [cfg.ev_zero]; exact Subgroup.one_mem _
  · rw [cfg.ev_one]; exact Subgroup.mem_zpowers _

private theorem mul_self_mem_of_acts {g : X} {T : List ℕ} (hTb : ∀ x ∈ T, x < 16)
    (hg : ∀ v < 16, g * cfg.ev v * g⁻¹ = cfg.ev (T.getD v 0)) (hTT : comp T T = idTab) :
    g * g ∈ Subgroup.closure (Set.range cfg.u) := by
  have h2 := cfg.acts_comp hg hg hTb
  refine cfg.hCS _ fun s hs => ?_
  obtain ⟨n, hn, rfl⟩ := cfg.exists_ev_eq s hs
  have := h2 n hn
  rw [hTT, getD_idTab hn] at this
  calc g * g * cfg.ev n = (g * g * cfg.ev n * (g * g)⁻¹) * (g * g) := by group
    _ = cfg.ev n * (g * g) := by rw [this]

private theorem sq_mem_of_mem_P {p : X} (hp : p ∈ cfg.P) :
    p * p ∈ Subgroup.closure (Set.range cfg.u) := by
  obtain ⟨s, hs, i, j, rfl⟩ := cfg.hPcos p hp
  have hA := cfg.acts_a
  have hB := cfg.acts_b
  have bI : ∀ x ∈ idTab, x < 16 := by decide +kernel
  have bA : ∀ x ∈ tab 1 2 5 11, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bB : ∀ x ∈ tab 1 3 4 13, x < 16 :=
    forall_lt_tab (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs0 : ∀ v < 16, s * cfg.ev v * s⁻¹ = cfg.ev (idTab.getD v 0) := by
    intro v hv
    rw [getD_idTab hv]
    exact cfg.conj_ev_of_mem hs v
  fin_cases i <;> fin_cases j
  · simpa using Subgroup.mul_mem _ hs hs
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
    exact cfg.mul_self_mem_of_acts (forall_lt_comp bI _) (cfg.acts_comp hs0 hB bB)
      (by decide +kernel)
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
    exact cfg.mul_self_mem_of_acts (forall_lt_comp bI _) (cfg.acts_comp hs0 hA bA)
      (by decide +kernel)
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
    exact cfg.mul_self_mem_of_acts (forall_lt_comp (forall_lt_comp bI _) _)
      (cfg.acts_comp (cfg.acts_comp hs0 hA bA) hB bB) (by decide +kernel)

private theorem false_of_order_four {W : X} {T : List ℕ} (hTb : ∀ x ∈ T, x < 16)
    (hT : ∀ v < 16, W * cfg.ev v * W⁻¹ = cfg.ev (T.getD v 0))
    (hT2 : comp T T ≠ idTab) (hT4 : comp (comp T T) (comp T T) = idTab) : False := by
  obtain ⟨hSel, hScard⟩ := cfg.isElemAbelian_S
  have hWS : ∀ s ∈ Subgroup.closure (Set.range cfg.u),
      W * s * W⁻¹ ∈ Subgroup.closure (Set.range cfg.u) := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := cfg.exists_ev_eq s hs
    rw [hT n hn]
    exact cfg.ev_mem _
  have hWSeq : (Subgroup.closure (Set.range cfg.u)).map (MulAut.conj W).toMonoidHom =
      Subgroup.closure (Set.range cfg.u) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply] using hWS s hs
    · rw [Subgroup.card_map_of_injective (MulAut.conj W).injective]
  have hWinv : ∀ s ∈ Subgroup.closure (Set.range cfg.u),
      W⁻¹ * s * W ∈ Subgroup.closure (Set.range cfg.u) := by
    intro s hs
    rw [← hWSeq] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have e : W⁻¹ * (W * s' * W⁻¹) * W = s' := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e]
    exact hs'
  have hnorm : W ∈ Subgroup.normalizer (Subgroup.closure (Set.range cfg.u) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hWS h hh, fun hh => ?_⟩
    have h1 := hWinv _ hh
    have e : W⁻¹ * (W * h * W⁻¹) * W = h := by group
    rwa [e] at h1
  have hTTb : ∀ x ∈ comp T T, x < 16 := forall_lt_comp hTb T
  have hW2 := cfg.acts_comp hT hT hTb
  have hW4S : W * W * (W * W) ∈ Subgroup.closure (Set.range cfg.u) :=
    cfg.mul_self_mem_of_acts hTTb hW2 hT4
  have hW8 : W ^ 8 = 1 := by
    have := hSel.mul_self_eq_one hW4S
    calc W ^ 8 = W * W * (W * W) * (W * W * (W * W)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hord : orderOf W ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact orderOf_dvd_of_pow_eq_one hW8
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hZ2 : IsPGroup 2 (Subgroup.zpowers W) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hQ : IsPGroup 2 ↥(Subgroup.closure (Set.range cfg.u) ⊔ Subgroup.zpowers W) :=
    IsPGroup.to_sup_of_normal_left' hSel.isPGroup hZ2 (Subgroup.zpowers_le.mpr hnorm)
  obtain ⟨c, hc⟩ := exists_conj_le_sylow cfg.hPsyl hQ
  have hcnorm := conj_mem_of_unique
    (fun E hE hEel hEc => cfg.hunique E hE hEel (hEc.trans hScard)) hSel
    (fun s hs => hc s (Subgroup.mem_sup_left hs))
  have hcW : c⁻¹ * W * c ∈ cfg.P :=
    hc W (Subgroup.mem_sup_right (Subgroup.mem_zpowers W))
  have hsq := cfg.sq_mem_of_mem_P hcW
  have hWW : W * W ∈ Subgroup.closure (Set.range cfg.u) := by
    have h1 := (hcnorm _ hsq).1
    have e : c * ((c⁻¹ * W * c) * (c⁻¹ * W * c)) * c⁻¹ = W * W := by group
    rwa [e] at h1
  apply hT2
  refine eq_idTab_of_getD (length_comp T T) fun v hv => ?_
  have h1 := hW2 v hv
  rw [cfg.conj_ev_of_mem hWW v] at h1
  exact (cfg.ev_inj v hv _ (getD_lt hTTb v) h1).symm

private theorem pairs16_sub : ∀ bc ∈ pairs16, bc.1 ∈ A4tabs ∧ bc.2 ∈ A4tabs := by
  decide +kernel

theorem false_of_isConj (h : IsConj (cfg.u 0) (cfg.u 1)) : False := by
  obtain ⟨γ, hγx, hγS⟩ := cfg.exists_gamma h
  obtain ⟨r0, hr0, r1, hr1, r2, hr2, r3, hr3, hγ⟩ := cfg.exists_rows fun s hs => (hγS s hs).1
  have hr0' : r0 = 2 := by
    have h1 := hγ 1 (by norm_num)
    rw [cfg.ev_one, hγx, ← cfg.ev_two] at h1
    have t0 : Nat.testBit 1 0 = true := by decide
    have t1 : Nat.testBit 1 1 = false := by decide
    have t2 : Nat.testBit 1 2 = false := by decide
    have t3 : Nat.testBit 1 3 = false := by decide
    have : vmul 1 r0 r1 r2 r3 = r0 := by simp [vmul, t0, t1, t2, t3]
    rw [this] at h1
    exact (cfg.ev_inj 2 (by norm_num) r0 hr0 h1).symm
  subst hr0'
  have hker : ((List.range 15).all fun k => vmul (k + 1) 2 r1 r2 r3 != 0) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    simp only [bne_iff_ne, ne_eq]
    intro h0
    have h1 := hγ (k + 1) (by omega)
    rw [h0, cfg.ev_zero] at h1
    have h2 : cfg.ev (k + 1) = cfg.ev 0 := by
      rw [cfg.ev_zero]
      have h3 : γ * cfg.ev (k + 1) = γ := mul_inv_eq_one.mp h1
      simpa using h3
    have := cfg.ev_inj (k + 1) (by omega) 0 (by norm_num) h2
    omega
  have hconcl := hasOrderFourProduct_tab r1 hr1 r2 hr2 r3 hr3 hker
  simp only [hasOrderFourProduct, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hconcl
  obtain ⟨⟨b, c⟩, hbc, hW2, hW4⟩ := hconcl
  obtain ⟨hb, hc⟩ := pairs16_sub ⟨b, c⟩ hbc
  obtain ⟨eb, heb⟩ := cfg.exists_A4_elems b hb
  obtain ⟨ec, hec⟩ := cfg.exists_A4_elems c hc
  have hM : ∀ v < 16, γ * cfg.ev v * γ⁻¹ = cfg.ev ((tab 2 r1 r2 r3).getD v 0) := fun v hv => by
    rw [getD_tab hv]
    exact hγ v hv
  have bM : ∀ x ∈ tab 2 r1 r2 r3, x < 16 := forall_lt_tab (by norm_num) hr1 hr2 hr3
  have bb : ∀ x ∈ b, x < 16 := forall_lt_A4tabs b hb
  have bc' : ∀ x ∈ c, x < 16 := forall_lt_A4tabs c hc
  have h1 := cfg.acts_comp hM hec bc'
  have h2 := cfg.acts_comp heb h1 (forall_lt_comp bM c)
  have h3 := cfg.acts_comp hM h2 (forall_lt_comp bb _)
  exact cfg.false_of_order_four (forall_lt_comp bM _) h3 hW2 hW4

end E16Config

end CFSG.RankThree.GF2n.Parrott.FusionE16
