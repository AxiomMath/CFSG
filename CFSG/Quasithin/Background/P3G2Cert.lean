module

public import CFSG.Quasithin.Background.P3G2Codes
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.G11.P3G2

open CFSG.Quasithin.G2U

structure Cert where
  key : ℕ → ℕ
  par : ℕ → ℕ
  gen : ℕ → ℕ
  dep : ℕ → ℕ
  rA : ℕ → ℕ
  rB : ℕ → ℕ
  N : ℕ
  root : ℕ

@[expose] def parentChk (c : Cert) (i : ℕ) : Bool :=
  match c.dep i with
  | 0 => c.key i == oneK
  | d + 1 =>
    decide (c.par i < c.N) && c.dep (c.par i) == d &&
      (if c.gen i == 0 then c.rA (c.par i) else c.rB (c.par i)) == i

@[expose] def nodeOK (ρA ρB : ℕ → ℕ) (c : Cert) (i : ℕ) : Bool :=
  decide (c.key i / B9 < 2 ^ 64) &&
  decide (c.rA i < c.N) && c.key (c.rA i) == ρA (c.key i) &&
  decide (c.rB i < c.N) && c.key (c.rB i) == ρB (c.key i) &&
  parentChk c i &&
  ((c.key i / B9 == id8p) == (c.key i % B9 == id3p)) &&
  (i + 1 == c.N || decide (c.key i < c.key (i + 1)))

@[expose] def rootChk (c : Cert) : Bool :=
  decide (c.root < c.N) && c.key c.root == oneK

theorem parentChk_spec {c : Cert} {i : ℕ} (h : parentChk c i = true) :
    (c.dep i = 0 → c.key i = oneK) ∧
      ∀ d, c.dep i = d + 1 → c.par i < c.N ∧ c.dep (c.par i) = d ∧
        (c.gen i = 0 → c.rA (c.par i) = i) ∧ (c.gen i ≠ 0 → c.rB (c.par i) = i) := by
  unfold parentChk at h
  constructor
  · intro h0
    rw [h0] at h
    exact beq_iff_eq.mp h
  · intro d hd
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, h2, fun hg => ?_, fun hg => ?_⟩
    · rw [ite_eq_left (by simpa using hg)] at h3
      exact h3
    · rw [ite_eq_right (by simpa using hg)] at h3
      exact h3

theorem nodeOK_spec {ρA ρB : ℕ → ℕ} {c : Cert} {i : ℕ} (h : nodeOK ρA ρB c i = true) :
    c.key i / B9 < 2 ^ 64 ∧ c.rA i < c.N ∧ c.key (c.rA i) = ρA (c.key i) ∧
      c.rB i < c.N ∧ c.key (c.rB i) = ρB (c.key i) ∧ parentChk c i = true ∧
      (c.key i / B9 = id8p ↔ c.key i % B9 = id3p) ∧
      (i + 1 < c.N → c.key i < c.key (i + 1)) := by
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · have e1 : (c.key i / B9 == id8p) = true ↔ c.key i / B9 = id8p := beq_iff_eq
    have e2 : (c.key i % B9 == id3p) = true ↔ c.key i % B9 = id3p := beq_iff_eq
    rw [← e1, ← e2, h7]
  · intro hi
    rcases h8 with h8 | h8
    · omega
    · exact h8

theorem rootChk_spec {c : Cert} (h : rootChk c = true) : c.root < c.N ∧ c.key c.root = oneK := by
  simpa [rootChk] using h

variable {G : Type*} [Group G] [Finite G]

theorem cert_image {ρA ρB : ℕ → ℕ}
    {GA GB : Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9}
    (hA : ∀ k, decK (ρA k) = decK k * GA) (hB : ∀ k, decK (ρB k) = decK k * GB)
    {c : Cert} (hnode : ∀ i < c.N, nodeOK ρA ρB c i = true) (hroot : rootChk c = true)
    (f : G →* Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9) (S : Set G)
    (hS : f '' S = {GA, GB}) :
    f '' (Subgroup.closure S : Set G) = {y | ∃ i < c.N, decK (c.key i) = y} := by
  have hcl : f '' (Subgroup.closure S : Set G) = (Submonoid.closure {GA, GB} : Set _) := by
    rw [← hS, ← MonoidHom.map_mclosure, Submonoid.coe_map,
      ← Subgroup.closure_toSubmonoid_of_finite]
    rfl
  obtain ⟨hr1, hr2⟩ := rootChk_spec hroot
  rw [hcl]
  apply Set.Subset.antisymm
  · intro y hy
    induction hy using Submonoid.closure_induction_right with
    | one => exact ⟨c.root, hr1, by rw [hr2, decK_oneK]⟩
    | mul_right x _ z hz ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨-, h1, h2, h3, h4, -⟩ := nodeOK_spec (hnode i hi)
      rcases hz with rfl | rfl
      · exact ⟨c.rA i, h1, by rw [h2, hA]⟩
      · exact ⟨c.rB i, h3, by rw [h4, hB]⟩
  · have key : ∀ d, ∀ i < c.N, c.dep i = d →
        decK (c.key i) ∈ (Submonoid.closure {GA, GB} : Set _) := by
      intro d
      induction d with
      | zero =>
        intro i hi hd
        obtain ⟨-, -, -, -, -, hp, -⟩ := nodeOK_spec (hnode i hi)
        rw [(parentChk_spec hp).1 hd, decK_oneK]
        exact one_mem _
      | succ d ih =>
        intro i hi hd
        obtain ⟨-, -, -, -, -, hp, -⟩ := nodeOK_spec (hnode i hi)
        obtain ⟨hpar, hpd, hg0, hg1⟩ := (parentChk_spec hp).2 d hd
        obtain ⟨-, -, h2, -, h4, -⟩ := nodeOK_spec (hnode (c.par i) hpar)
        have hmem := ih (c.par i) hpar hpd
        by_cases hg : c.gen i = 0
        · have := hg0 hg
          rw [← this, h2, hA]
          exact mul_mem hmem (Submonoid.subset_closure (Set.mem_insert _ _))
        · have := hg1 hg
          rw [← this, h4, hB]
          exact mul_mem hmem (Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))
    rintro _ ⟨i, hi, rfl⟩
    exact key (c.dep i) i hi rfl

theorem cert_keys_strictMono {ρA ρB : ℕ → ℕ} {c : Cert}
    (hnode : ∀ i < c.N, nodeOK ρA ρB c i = true) :
    ∀ i j, i < j → j < c.N → c.key i < c.key j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base =>
    intro hj
    exact (nodeOK_spec (hnode i (by omega))).2.2.2.2.2.2.2 hj
  | succ j hij ih =>
    intro hj
    exact (ih (by omega)).trans ((nodeOK_spec (hnode j (by omega))).2.2.2.2.2.2.2 hj)

theorem cert_card {ρA ρB : ℕ → ℕ}
    {GA GB : Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9}
    (hA : ∀ k, decK (ρA k) = decK k * GA) (hB : ∀ k, decK (ρB k) = decK k * GB)
    {c : Cert} (hnode : ∀ i < c.N, nodeOK ρA ρB c i = true) (hroot : rootChk c = true)
    (f : G →* Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9)
    (hf : Function.Injective f) (S : Set G) (hS : f '' S = {GA, GB}) :
    Nat.card (Subgroup.closure S) = c.N := by
  have himg := cert_image hA hB hnode hroot f S hS
  have hinj : Function.Injective fun i : Fin c.N => decK (c.key i) := by
    intro i j hij
    have h1 := (nodeOK_spec (hnode i i.2)).1
    have h2 := (nodeOK_spec (hnode j j.2)).1
    have hk := decK_injective h1 h2 hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact absurd hk (cert_keys_strictMono hnode i j hlt j.2).ne
    · exact absurd hk.symm (cert_keys_strictMono hnode j i hlt i.2).ne
  have hrange : f '' (Subgroup.closure S : Set G) =
      Set.range fun i : Fin c.N => decK (c.key i) := by
    rw [himg]
    ext y
    exact ⟨fun ⟨i, hi, e⟩ => ⟨⟨i, hi⟩, e⟩, fun ⟨i, e⟩ => ⟨i, i.2, e⟩⟩
  calc Nat.card (Subgroup.closure S)
      = Nat.card (f '' (Subgroup.closure S : Set G)) :=
        (Nat.card_image_of_injective hf _).symm
    _ = Nat.card (Fin c.N) := by
        rw [hrange]
        exact Nat.card_range_of_injective hinj
    _ = c.N := Nat.card_fin _

theorem cert_graph {ρA ρB : ℕ → ℕ}
    {GA GB : Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9}
    (hA : ∀ k, decK (ρA k) = decK k * GA) (hB : ∀ k, decK (ρB k) = decK k * GB)
    {c : Cert} (hnode : ∀ i < c.N, nodeOK ρA ρB c i = true) (hroot : rootChk c = true)
    (f : G →* Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9) (S : Set G)
    (hS : f '' S = {GA, GB}) {g : G} (hg : g ∈ Subgroup.closure S) :
    ((f g).1 = 1 ↔ (f g).2 = 1) := by
  have himg := cert_image hA hB hnode hroot f S hS
  have hmem : f g ∈ f '' (Subgroup.closure S : Set G) := Set.mem_image_of_mem f hg
  rw [himg] at hmem
  obtain ⟨i, hi, hig⟩ := hmem
  obtain ⟨h1, -, -, -, -, -, h7, -⟩ := nodeOK_spec (hnode i hi)
  rw [← hig]
  simp only [decK]
  rw [matDec8_eq_one_iff h1, matDec3_eq_one_iff (Nat.mod_lt _ (by norm_num [B9]))]
  exact h7

end CFSG.Quasithin.G11.P3G2
