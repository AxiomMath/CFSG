module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Orbit
public import CFSG.RankThree.GF2n.Stroth80.Sec101Tt
public import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem index_ker_commHom_le (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Q) {V : Subgroup G}
    (hV : V ≤ Q) : (hc.commHom hy hV).ker.index ≤ Nat.card Z := by
  rw [Subgroup.index_ker]
  exact Nat.card_le_card_of_injective (fun z => (z.1 : ↥Z)) (fun a b h => Subtype.ext h)

private theorem card_le_of_forall_mem_Wt (hc : Ctx M Q Z B) {t α : G} (hα : α ∈ Q)
    (hcon : ∀ c ∈ Q, c * α = α * c → c ∈ Subgroup.centralizer (B : Set G) →
      c ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    Nat.card Q ≤ Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * (Nat.card Z * Nat.card Z) := by
  obtain ⟨b, hb, hb1⟩ := hc.exists_ne_one
  set Kr := (hc.commHom hα le_rfl).ker ⊓ (hc.commHom (hc.le hb) le_rfl).ker
  have hidx : Kr.index ≤ Nat.card Z * Nat.card Z :=
    Subgroup.index_inf_le.trans
      (Nat.mul_le_mul (index_ker_commHom_le hc hα le_rfl) (index_ker_commHom_le hc _ le_rfl))
  have hKW : ∀ x : ↥Q, x ∈ Kr → (x : G) ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx => by
    have h1 : ⁅(x : G), α⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx.1)
    have h2 : ⁅(x : G), b⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx.2)
    have hxB := hc.centralizes_of_comm x.2 hb hb1 (commutatorElement_eq_one_iff_mul_comm.mp h2)
    exact hcon x x.2 (commutatorElement_eq_one_iff_mul_comm.mp h1)
      (Subgroup.mem_centralizer_iff.mpr fun d hd => (hxB d hd).symm)
  have hcard : Nat.card Kr ≤ Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥Kr => (⟨((x : ↥Q) : G), hKW x x.2⟩ : ↥(Wt Q (Vt M (LB M Q B) B Z t)))) ?_
    intro a b h
    have h1 := congrArg (fun x : ↥(Wt Q (Vt M (LB M Q B) B Z t)) => (x : G)) h
    exact Subtype.ext (Subtype.ext h1)
  rw [← Subgroup.card_mul_index Kr]
  exact Nat.mul_le_mul hcard hidx

theorem SLMNat.exists_mem_centralizer_not_mem_Wt {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (hm : SLMNat hc t m) (hm3 : 3 ≤ m) {α : G} (hα : α ∈ Q) :
    ∃ c ∈ Q, c * α = α * c ∧ c ∈ Subgroup.centralizer (B : Set G) ∧
      c ∉ Wt Q (Vt M (LB M Q B) B Z t) := by
  by_contra hcon
  push Not at hcon
  have hQ := card_le_of_forall_mem_Wt hc hα hcon
  have hWV := hc.card_Wt_mul_card_Vt t
  rw [hm.card_Vt] at hWV
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have h3 : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ (m + 1) ≤
      Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 3 := by
    rw [hWV]
    calc Nat.card Q * Nat.card Z
        ≤ Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * (Nat.card Z * Nat.card Z) * Nat.card Z :=
          Nat.mul_le_mul_right _ hQ
      _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 3 := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 Nat.card_pos
  have h5 := Nat.pow_lt_pow_right hq (show 3 < m + 1 by omega)
  omega

private theorem Good101.exists_comm_not_mem (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {m : ℕ}
    (hm : SLMNat hc t m) (hm3 : 3 ≤ m) {c : G} (hcQ : c ∈ Q) :
    ∃ a ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t, a * c = c * a ∧ a ∉ B := by
  have hA₀Q : Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ≤ Q := inf_le_left.trans inf_le_left
  set f := hc.commHom hcQ hA₀Q
  by_contra hcon
  push Not at hcon
  have hkB : ∀ x : ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t), x ∈ f.ker → (x : G) ∈ B :=
    fun x hx => hcon x x.2 (commutatorElement_eq_one_iff_mul_comm.mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  have hcardk : Nat.card f.ker ≤ Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [← card_conjSubgroup g Z, ← hg]
    refine Nat.card_le_card_of_injective (fun x : ↥f.ker =>
      (⟨((x : ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)) : G), hkB x x.2⟩ : ↥B)) ?_
    intro a b h
    have h1 := congrArg (fun x : ↥B => (x : G)) h
    exact Subtype.ext (Subtype.ext h1)
  have hmul := Subgroup.card_mul_index f.ker
  rw [ht.card_inf_QB_inf_Vt h34 hspread H hs hm] at hmul
  have hle : Nat.card Z ^ m ≤ Nat.card Z ^ 2 := by
    rw [← hmul, pow_two]
    exact Nat.mul_le_mul hcardk (index_ker_commHom_le hc hcQ hA₀Q)
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have h5 := Nat.pow_lt_pow_right hq (show 2 < m by omega)
  omega

theorem Good101.exists_root_group_centralizer (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {m : ℕ}
    (hm : SLMNat hc t m) (hm3 : 3 ≤ m) {c : G} (hcQ : c ∈ Q) :
    ∃ D : Subgroup G, Ctx M Q Z D ∧ D ≤ QB Y ∧ Y ≤ QB D ∧
      D ≤ Subgroup.centralizer ({c} : Set G) ∧ ¬ D ≤ B := by
  obtain ⟨a, haA, hac, haB⟩ := ht.exists_comm_not_mem h34 hspread H hs hm hm3 hcQ
  have ha1 : a ≠ 1 := fun h => haB (h ▸ B.one_mem)
  have haZ : a ∉ Z := fun h => ha1 (by
    have h' : a ∈ Z ⊓ QB Y := ⟨h, haA.1.2⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at h')
  obtain ⟨D, hD, haD, hDY, hYD⟩ :=
    Sit.exists_root_group hs haA.1 ha1 (Good101.isRoot_of_mem_Vt H ht haA.2 haZ)
  refine ⟨D, hD, hDY, hYD, fun d hd => ?_, fun hDB => haB (hDB haD)⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (hD.centralizes_of_comm hcQ haD ha1 hac.symm d hd).symm

end CFSG.RankThree.GF2n.Stroth80
