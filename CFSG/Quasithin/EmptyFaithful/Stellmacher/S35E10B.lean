module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem card_two_cases {Z : Subgroup G} (hZ : Nat.card Z = 2) {a : G} (ha : a ∈ Z)
    (h1 : a ≠ 1) : ∀ y ∈ Z, y = 1 ∨ y = a := by
  intro y hy
  by_contra hcon
  push Not at hcon
  obtain ⟨u, v, -, hs⟩ := Nat.card_eq_two_iff.mp hZ
  have hmem : ∀ t : Z, t = u ∨ t = v := fun t => by
    have : t ∈ ({u, v} : Set Z) := by rw [hs]; trivial
    simpa using this
  have n1 : (1 : Z) ≠ ⟨a, ha⟩ := fun h => h1 (by simpa using (congrArg Subtype.val h).symm)
  have n2 : (1 : Z) ≠ ⟨y, hy⟩ := fun h => hcon.1 (by simpa using (congrArg Subtype.val h).symm)
  have n3 : (⟨a, ha⟩ : Z) ≠ ⟨y, hy⟩ := fun h =>
    hcon.2 (by simpa using (congrArg Subtype.val h).symm)
  rcases hmem 1 with h | h <;> rcases hmem ⟨a, ha⟩ with h' | h' <;>
    rcases hmem ⟨y, hy⟩ with h'' | h''
  all_goals first
    | exact n1 (h.trans h'.symm)
    | exact n2 (h.trans h''.symm)
    | exact n3 (h'.trans h''.symm)

omit [Finite G] in
theorem le_of_ne_bot {Z A : Subgroup G} (hZ : Nat.card Z = 2) (hAZ : A ≤ Z) (hA : A ≠ ⊥) :
    Z ≤ A := by
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  intro y hy
  rcases card_two_cases hZ (hAZ haA) ha1' y hy with h | h
  · rw [h]; exact A.one_mem
  · rw [h]; exact haA

omit [Finite G] in
theorem relIndex_le_two_of {K N : Subgroup G} (hKN : K ≤ N)
    (h : ∀ a ∈ N, a ∉ K → ∀ b ∈ N, b ∉ K → a⁻¹ * b ∈ K) : K.relIndex N ≤ 2 := by
  by_cases hK : K = N
  · rw [hK, Subgroup.relIndex_self]; omega
  obtain ⟨c, hcN, hcK⟩ : ∃ c ∈ N, c ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hK (le_antisymm hKN hcon)
  have hind : (K.subgroupOf N).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hcN⟩, fun b => ?_⟩
    have hmem : ∀ t : N, t ∈ K.subgroupOf N ↔ (t : G) ∈ K := fun t => Iff.rfl
    simp only [hmem]
    by_cases hb : (b : G) ∈ K
    · refine Or.inr ⟨hb, ?_⟩
      intro hbc
      exact hcK (by simpa using K.mul_mem (K.inv_mem hb) hbc)
    · refine Or.inl ⟨?_, hb⟩
      have := h (b : G)⁻¹ (N.inv_mem b.2) (fun h' => hb (by simpa using K.inv_mem h')) c hcN hcK
      simpa using this
  show (K.subgroupOf N).index ≤ 2
  omega

theorem mem_stab_of_centralizes (hS : Sit H M S) {m α' : Geo H M} (hm : vtype m = true)
    (hα' : α' ∈ nbrs m) {w : G} (hw : w ∈ stab m) (hc : ∀ z ∈ Zv α', w * z * w⁻¹ = z) :
    w ∈ stab α' := by
  let g : ↥(H ⊔ M) := ⟨w, stab_le m hw⟩
  have h1 : g • α' ∈ nbrs m := smul_mem_nbrs_of_stab hw hα'
  by_contra hne
  have hne' : g • α' ≠ α' := fun h => hne (mem_stab_of_smul_eq h)
  refine (Zv_ne hS hm h1 hα' hne').1 ?_
  rw [Zv_smul]
  have hcomm : ∀ z ∈ Zv α', (w : G)⁻¹ * z * w = z := by
    intro z hz
    have h := hc z hz
    have hwz : (w : G) * z = z * w := by
      calc (w : G) * z = (w * z * w⁻¹) * w := by group
        _ = z * w := by rw [h]
    calc (w : G)⁻¹ * z * w = (w : G)⁻¹ * (z * w) := by group
      _ = z := by rw [← hwz]; group
  ext z
  rw [mem_conjSub]
  change (w : G)⁻¹ * z * w ∈ Zv α' ↔ z ∈ Zv α'
  constructor
  · intro hz
    have h := hc _ hz
    rw [show (w : G) * ((w : G)⁻¹ * z * w) * (w : G)⁻¹ = z by group] at h
    rw [h]
    exact hz
  · intro hz
    rw [hcomm z hz]
    exact hz

theorem relIndex_le_two_of_le_Qv (hS : Sit H M S) {m α' γ' : Geo H M} (hm : vtype m = true)
    (hα' : α' ∈ nbrs m) (hγ' : γ' ∈ nbrs m) (hne : α' ≠ γ') {W : Subgroup G}
    (hW : W ≤ Qv γ') : (W ⊓ stab α').relIndex W ≤ 2 := by
  refine relIndex_le_two_of inf_le_left ?_
  obtain ⟨δ'', h3, h1, h2, hall⟩ := nbrs_S3_third hS hm hα' hγ' hne
  have key : ∀ w ∈ W, w ∉ stab α' → ∃ hw : w ∈ stab m,
      (⟨w, stab_le m hw⟩ : ↥(H ⊔ M)) • α' = δ'' := by
    intro w hw hwα
    have hwγ : w ∈ stab γ' := pCoreOf_le 2 (stab γ') (hW hw)
    have hwm : w ∈ stab m := Qv_le_stab hS (mem_nbrs_symm.mp hγ') (hW hw)
    refine ⟨hwm, ?_⟩
    let g : ↥(H ⊔ M) := ⟨w, stab_le m hwm⟩
    have hg1 : g • α' ∈ nbrs m := smul_mem_nbrs_of_stab hwm hα'
    have hgγ : g • γ' = γ' := smul_eq_of_mem_stab hwγ
    rcases hall _ hg1 with h | h | h
    · exact absurd (mem_stab_of_smul_eq h) hwα
    · exact absurd (MulAction.injective g (h.trans hgγ.symm)) hne
    · exact h
  intro a ha haK b hb hbK
  have haα : a ∉ stab α' := fun h => haK ⟨ha, h⟩
  have hbα : b ∉ stab α' := fun h => hbK ⟨hb, h⟩
  obtain ⟨hma, ha3⟩ := key a ha haα
  obtain ⟨hmb, hb3⟩ := key b hb hbα
  refine ⟨W.mul_mem (W.inv_mem ha) hb, ?_⟩
  let ga : ↥(H ⊔ M) := ⟨a, stab_le m hma⟩
  let gb : ↥(H ⊔ M) := ⟨b, stab_le m hmb⟩
  have : (ga⁻¹ * gb) • α' = α' := by
    rw [mul_smul, hb3, ← ha3, inv_smul_smul]
  exact mem_stab_of_smul_eq this

theorem back_facts (hS : Sit H M S) {β α' m γ' : Geo H M} (hp : S34.PD β α')
    (hb : Back H M β α' m γ') :
    vtype m = true ∧ vtype γ' = false ∧ dist β γ' + 3 = bMin H M ∧ dist β m + 2 = bMin H M ∧
      α' ≠ γ' ∧ dist γ' α' + 3 ≤ bMin H M := by
  have e := hp.dist_eq
  obtain ⟨h1, h2, h3, h4⟩ := hb
  have hvm : vtype m = true := vtype_nbr_S5 hp.vδ' h1
  have hv : vtype γ' = false := vtype_nbr_S3 hvm h2
  have hd1 : dist γ' m = 1 := dist_eq_one_iff_adj.mpr (mem_nbrs_symm.mp h2)
  have hd2 := dist_le_dist_nbr (mem_nbrs_symm.mp h1) γ'
  have hb5 := hS.b5
  refine ⟨hvm, hv, by omega, by omega, ?_, by omega⟩
  intro h
  subst h
  omega

omit [Finite G] in
theorem exists_nbr_Zv_not_le {β α' : Geo H M} (hp : S34.PD β α') :
    ∃ α ∈ nbrs β, ¬ Zv α ≤ Qv α' := by
  by_contra hcon
  push Not at hcon
  exact hp.not_le (iSup₂_le fun μ hμ => hcon μ hμ)

theorem exists_not_mem_Qv (hS : Sit H M S) {α : Geo H M} {B : Subgroup G}
    (hB : ⁅B, Zv α⁆ ≠ ⊥) : ∃ x ∈ B, x ∉ Qv α := by
  by_contra hcon
  push Not at hcon
  refine hB ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr fun b hb => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz'
  exact (Subgroup.mem_centralizer_iff.mp
    ((Zv_le_centerOf_Qv hS.glob.amalg α hz').2) b (hcon b hb)).symm

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
