module

public import CFSG.Quasithin.Vol2.KGFactC31RuGens

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

@[expose] noncomputable def vOf (ws : List (List ℤ)) (k : ℕ) (i : Fin k) :
    Equiv.Perm (Fin 4060) :=
  wG (ws.getD i [])

theorem vOf_mem (ws : List (List ℤ)) (k : ℕ) (i : Fin k) : vOf ws k i ∈ ruP := wG_mem _

noncomputable abbrev vE : Fin 3 → Equiv.Perm (Fin 4060) := vOf basisEW 3
noncomputable abbrev v64 : Fin 6 → Equiv.Perm (Fin 4060) := vOf basis64W 6
noncomputable abbrev v3 : Fin 3 → Equiv.Perm (Fin 4060) := vOf basis3W 3
noncomputable abbrev v16 : Fin 4 → Equiv.Perm (Fin 4060) := vOf basis16W 4
noncomputable abbrev v32 : Fin 5 → Equiv.Perm (Fin 4060) := vOf basis32W 5
noncomputable abbrev vV32E : Fin 5 → Equiv.Perm (Fin 4060) := vOf basisV32EW 5
noncomputable abbrev vV32p : Fin 5 → Equiv.Perm (Fin 4060) := vOf basisV32pW 5

@[expose] noncomputable def refSub {k : ℕ} (v : Fin k → Equiv.Perm (Fin 4060)) :
    Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure (Set.range v)

noncomputable abbrev uE : Subgroup (Equiv.Perm (Fin 4060)) := refSub vE
noncomputable abbrev u64 : Subgroup (Equiv.Perm (Fin 4060)) := refSub v64
noncomputable abbrev u3 : Subgroup (Equiv.Perm (Fin 4060)) := refSub v3
noncomputable abbrev u16 : Subgroup (Equiv.Perm (Fin 4060)) := refSub v16
noncomputable abbrev u32 : Subgroup (Equiv.Perm (Fin 4060)) := refSub v32
noncomputable abbrev uV32E : Subgroup (Equiv.Perm (Fin 4060)) := refSub vV32E
noncomputable abbrev uV32p : Subgroup (Equiv.Perm (Fin 4060)) := refSub vV32p

theorem refSub_eq {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} (h : EBasis v) :
    refSub v = eSub h :=
  (eSub_eq_closure h).symm

theorem refSub_le_ruP {k : ℕ} (ws : List (List ℤ)) : refSub (vOf ws k) ≤ ruP := by
  rw [refSub, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact vOf_mem ws k i

theorem card_refSub {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} (hv : EBasis v) :
    Nat.card (refSub v) = 2 ^ k := by
  rw [refSub_eq hv, card_eSub]

theorem refSub_le_of_forall {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)}
    {H : Subgroup (Equiv.Perm (Fin 4060))} (h : ∀ i, v i ∈ H) : refSub v ≤ H := by
  rw [refSub, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact h i

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {x : G}
    (h : ∀ u ∈ H, x * u * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem mem_normalizer_of_forall {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)}
    {x : Equiv.Perm (Fin 4060)}
    (h : ∀ i, x * v i * x⁻¹ ∈ refSub v) : x ∈ Subgroup.normalizer (refSub v : Set _) := by
  refine mem_normalizer_of_conj_le fun u hu => ?_
  have hle : refSub v ≤ (refSub v).comap (MulAut.conj x).toMonoidHom := by
    rw [refSub, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hle hu

noncomputable abbrev x16 : Equiv.Perm (Fin 4060) := wG x16W
noncomputable abbrev g16 : Equiv.Perm (Fin 4060) := wG g16W
noncomputable abbrev k16 : Equiv.Perm (Fin 4060) := wG k16W
noncomputable abbrev xE : Equiv.Perm (Fin 4060) := wG xEW
noncomputable abbrev nE : Equiv.Perm (Fin 4060) := wG nEW
noncomputable abbrev x32 : Equiv.Perm (Fin 4060) := wG x32W
noncomputable abbrev cQ : Equiv.Perm (Fin 4060) := wG cQW

@[expose] noncomputable def h30 : Equiv.Perm (Fin 4060) :=
  evalSigned [ruA0, ruA1] (hWordsZ.getD 0 [])

@[expose] noncomputable def r30 : Equiv.Perm (Fin 4060) := h30 * ruZ * h30⁻¹

@[expose] def OrbComm (x g : Equiv.Perm (Fin 4060)) (m : ℕ) : Prop :=
  ∀ j < m, g * (x ^ (j + 1) * g * (x ^ (j + 1))⁻¹) = x ^ (j + 1) * g * (x ^ (j + 1))⁻¹ * g

@[expose] def CentB {k : ℕ} (v : Fin k → Equiv.Perm (Fin 4060)) (g : Equiv.Perm (Fin 4060)) :
    Prop :=
  ∀ i, g * v i = v i * g

@[expose] def BigZ (g : Equiv.Perm (Fin 4060)) : Prop :=
  (CentB vE g → g * g = 1 → OrbComm xE g 3 → g ∈ uV32E) ∧
  (CentB v64 g → g ∈ u64) ∧
  (CentB v3 g → g ∈ u64) ∧
  (CentB v16 g → g ^ 2 ^ 7 = 1 ∧ CentB v16 (g16 * g * g16⁻¹) ∧
    (g * g = 1 → OrbComm x16 g 2 → g ∈ uV32p)) ∧
  ((∀ i, ∃ d, eElt v16 d = g * v16 i * g⁻¹) → g ^ 2 ^ 10 = 1) ∧
  (CentB v32 g → g ^ 2 ^ 7 = 1 ∧ (g * g = 1 → OrbComm x32 g 2 → g ∈ u32))

structure RefFacts : Prop where
  ebasis : EBasis vE ∧ EBasis v64 ∧ EBasis v3 ∧ EBasis v16 ∧ EBasis v32 ∧ EBasis vV32E ∧
    EBasis vV32p
  ruZ_mem : ruZ ∈ uE ∧ ruZ ∈ u64 ∧ ruZ ∈ u3 ∧ ruZ ∈ u16 ∧ ruZ ∈ u32
  uE_le_uV32E : uE ≤ uV32E
  ncard_fix_uE : ∀ g ∈ uE, g ≠ 1 → (fixSet g).ncard = 92
  ncard_fix_uV32E : ∀ g ∈ uV32E, g ∉ uE → (fixSet g).ncard = 0
  x16_mem_normalizer : x16 ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))
  ruC_le_normalizer32 : ruC ≤ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060)))
  orderOf_eq : orderOf xE = 7 ∧ orderOf x16 = 5 ∧ orderOf x32 = 5
  conj_x16_not_mem_normalizer :
    g16 * x16 * g16⁻¹ ∉ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))
  conj_k16_u32 : ∀ i, k16 * v32 i * k16⁻¹ ∈ uV32p
  conj64_distinct : ∀ i < 20, ∀ j < 20, i ≠ j →
    u64.map (MulAut.conj (wG (conj64W.getD i []))).toMonoidHom ≠
      u64.map (MulAut.conj (wG (conj64W.getD j []))).toMonoidHom
  ruK_sq_commut : ∀ a < 8, ∀ b < 8,
    ruKGens.getD a 1 * ruKGens.getD a 1 ∈ uE ∧
      ruKGens.getD a 1 * ruKGens.getD b 1 * (ruKGens.getD a 1)⁻¹ * (ruKGens.getD b 1)⁻¹ ∈ uE
  vE_commut :
    vE 0 = ruKGens.getD 3 1 * ruKGens.getD 4 1 * (ruKGens.getD 3 1)⁻¹ * (ruKGens.getD 4 1)⁻¹ ∧
    vE 1 = ruKGens.getD 3 1 * ruKGens.getD 1 1 * (ruKGens.getD 3 1)⁻¹ * (ruKGens.getD 1 1)⁻¹ ∧
    vE 2 = ruKGens.getD 4 1 * ruKGens.getD 0 1 * (ruKGens.getD 4 1)⁻¹ * (ruKGens.getD 0 1)⁻¹
  ruNs_words : ruNs0 = evalSigned [xE, nE * xE * nE⁻¹] (nsInXW.getD 0 []) ∧
    ruNs1 = evalSigned [xE, nE * xE * nE⁻¹] (nsInXW.getD 1 [])
  commut_not_mem :
    x32 * cQ * x32⁻¹ * cQ⁻¹ ∉ Subgroup.centralizer (u32 : Set (Equiv.Perm (Fin 4060)))
  cQ_memJ : cQ ∈ ruJ
  vE_conj : ∀ i : Fin 3, ∃ m ∈ ruN, m * ruZ * m⁻¹ = vE i
  exists_conj_r30 : ∀ v ∈ u32, v ≠ 1 → v ≠ ruZ → ∃ c ∈ ruC, c * r30 * c⁻¹ = v

end CFSG.Quasithin.KGC31.Ru

end
