module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WInt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem card_mul_relIndex_of_le {H L : Subgroup D} (h : H ≤ L) :
    Nat.card H * H.relIndex L = Nat.card L := by
  have h1 : (H.subgroupOf L).index * Nat.card (H.subgroupOf L) = Nat.card L :=
    Subgroup.index_mul_card _
  have h2 : Nat.card (H.subgroupOf L) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [Subgroup.relIndex, ← h2, mul_comm]
  exact h1

omit [Finite D] in
theorem four_le_card_inf_of_card_sixteen {X Y L : Subgroup D} (hX : X ≤ L) (hY : Y ≤ L)
    (hL : Nat.card L = 16) (hXc : 8 ≤ Nat.card X) (hYc : 8 ≤ Nat.card Y) :
    4 ≤ Nat.card ↥(X ⊓ Y) := by
  have hXI := card_mul_relIndex_of_le hX
  have hYI := card_mul_relIndex_of_le hY
  have hZI := card_mul_relIndex_of_le (inf_le_left.trans hX : X ⊓ Y ≤ L)
  have hle : (X ⊓ Y).relIndex L ≤ X.relIndex L * Y.relIndex L := Subgroup.relIndex_inf_le
  have h1 : X.relIndex L ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : Y.relIndex L ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h3 : (X ⊓ Y).relIndex L ≤ 4 := hle.trans (by nlinarith)
  by_contra hcon
  push Not at hcon
  nlinarith

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem card_inf_Vv_le_four {β a a' t t' : CosetGeom (A ⊔ B) A B}
    (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hF : ¬ ballStab 1 a ⊓ ballStab 1 β ≤ ballStab 1 a') (hβ : vtype β = true)
    (hβa : (graph (A ⊔ B) A B).Adj β a) (hβa' : (graph (A ⊔ B) A B).Adj β a')
    (haa' : a ≠ a') (hat : (graph (A ⊔ B) A B).Adj a t)
    (ha't' : (graph (A ⊔ B) A B).Adj a' t') (htβ : t ≠ β) (ht'β : t' ≠ β) :
    Nat.card ↥(Vv V t ⊓ Vv V t') ≤ 4 := by
  by_contra hbig
  push Not at hbig
  have ha : vtype a = false := vtype_eq_false_of_adj hβa hβ
  have ha' : vtype a' = false := vtype_eq_false_of_adj hβa' hβ
  have ht : vtype t = true := vtype_eq_true_of_adj hat ha
  obtain ⟨ρ, hρ, hρn⟩ := IsConcreteLE.not_le_iff_exists.1 hF
  have hρβ : ρ ∈ ballStab 1 β := hρ.2
  have hρβs : ρ ∈ stab β := ballStab_le_stab 1 β hρβ
  have hρG : ρ ∈ A ⊔ B := stab_le β hρβs
  have hρts : ρ ∈ stab t :=
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hat).le hρ.1
  have hρa's : ρ ∈ stab a' :=
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hβa').le hρβ
  have hρt'ne : ρ ∉ stab t' := fun hρt' =>
    hρn (h.mem_ballStab_one_of_fix_two' hβa'.symm ha't' (Ne.symm ht'β) hρa's hρβs hρt')
  lift ρ to ↥(A ⊔ B) using hρG with g
  have hgt : g • t = t := smul_eq_of_mem_stab hρts
  have hgβ : g • β = β := smul_eq_of_mem_stab hρβs
  have hga' : g • a' = a' := smul_eq_of_mem_stab hρa's
  have hgt'ne : g • t' ≠ t' := fun e => hρt'ne (mem_stab_of_smul_eq e)
  have hadj : (graph (A ⊔ B) A B).Adj a' (g • t') := by
    have := (smul_adj g).mpr ha't'
    rwa [hga'] at this
  have hX' : Vv V t ⊓ Vv V (g • t') = conjSub (g : D) (Vv V t ⊓ Vv V t') := by
    rw [conjSub_inf, ← Vv_smul h.natural.reduced.2.1, ← Vv_smul h.natural.reduced.2.1, hgt]
  have hXX' : (Vv V t ⊓ Vv V t') ⊓ (Vv V t ⊓ Vv V (g • t')) ≤ Zv z β := by
    intro x hx
    have hx_a' : x ∈ Vv V a' :=
      hI1 a' t' (g • t') ha' ha't' hadj (Ne.symm hgt'ne) ⟨hx.1.2, hx.2.2⟩
    have hx_β : x ∈ Vv V β := Vv_le_Vv_of_adj hβa'.symm ha' hx_a'
    have hx_a : x ∈ Vv V a := hI1 a t β ha hat hβa.symm htβ ⟨hx.1.1, hx_β⟩
    exact h.mem_Zv_of_mem_Vv_of_mem_Vv hβ hβa hβa' haa' hx_a hx_a'
  have hZ2 : Nat.card ↥(Zv z β) = 2 := h.card_Zv hβ
  have hU16 : Nat.card ↥(Vv V t) = 16 := h.card_Vv_B_of_card hU ht
  have hXle : Vv V t ⊓ Vv V t' ≤ Vv V t := inf_le_left
  have hX'le : Vv V t ⊓ Vv V (g • t') ≤ Vv V t := inf_le_left
  have hdvd : Nat.card ↥(Vv V t ⊓ Vv V t') ∣ 16 := hU16 ▸ Subgroup.card_dvd_of_le hXle
  have h8 : 8 ≤ Nat.card ↥(Vv V t ⊓ Vv V t') := by
    have hle16 : Nat.card ↥(Vv V t ⊓ Vv V t') ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(Vv V t ⊓ Vv V t') = n at hdvd hbig hle16 ⊢
    interval_cases n <;> omega
  have h8' : 8 ≤ Nat.card ↥(Vv V t ⊓ Vv V (g • t')) := by
    rw [hX', card_conjSub]
    exact h8
  have h4 := four_le_card_inf_of_card_sixteen hXle hX'le hU16 h8 h8'
  have h2 : Nat.card ↥((Vv V t ⊓ Vv V t') ⊓ (Vv V t ⊓ Vv V (g • t'))) ≤ 2 := by
    have := Subgroup.card_le_of_le hXX'
    omega
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
