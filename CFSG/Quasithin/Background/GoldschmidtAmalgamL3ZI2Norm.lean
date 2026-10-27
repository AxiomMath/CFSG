module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Rel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WInt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_smul_swap {β a γ₁ γ₂ : CosetGeom (A ⊔ B) A B} (ha : (graph (A ⊔ B) A B).Adj β a)
    (h₂ : (graph (A ⊔ B) A B).Adj a γ₁) (h₃ : (graph (A ⊔ B) A B).Adj a γ₂) (n12 : β ≠ γ₁)
    (n13 : β ≠ γ₂) (n23 : γ₁ ≠ γ₂) {ρ : D} (hρβ : ρ ∈ ballStab 1 β) (hρa : ρ ∉ ballStab 1 a) :
    ∃ g : ↥(A ⊔ B), (g : D) = ρ ∧ g • a = a ∧ g • β = β ∧ g • γ₁ = γ₂ := by
  have hd : CosetGeom.dist β a ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr ha).le
  have hρs : ρ ∈ stab a := ballStab_le_stab_of_dist_le hd hρβ
  have hρb : ρ ∈ stab β := ballStab_le_stab 1 β hρβ
  have hρG : ρ ∈ A ⊔ B := stab_le β hρb
  refine ⟨⟨ρ, hρG⟩, rfl, smul_eq_of_mem_stab hρs, smul_eq_of_mem_stab hρb, ?_⟩
  refine h.smul_eq_third ha.symm h₂ h₃ n12 n13 n23 (smul_eq_of_mem_stab hρs)
    (smul_eq_of_mem_stab hρb) fun hfix => hρa ?_
  exact h.mem_ballStab_one_of_fix_two' ha.symm h₂ n12 hρs hρb (mem_stab_of_smul_eq hfix)

theorem Theta_le_sup_of_normal {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hC2 : InvLeZvProp A B z V) {β a a' t t₂ : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a') (haa' : a ≠ a')
    (hat : (graph (A ⊔ B) A B).Adj a t) (hat₂ : (graph (A ⊔ B) A B).Adj a t₂) (n1 : β ≠ t)
    (n2 : β ≠ t₂) (n3 : t ≠ t₂)
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β)
    {ρ : D} (hρβ : ρ ∈ ballStab 1 β) (hρa' : ρ ∈ ballStab 1 a') (hρa : ρ ∉ ballStab 1 a) :
    Theta z V a t ≤ Zv z β ⊔ Theta z V a t₂ := by
  obtain ⟨g, hgρ, hga, hgβ, hgt⟩ := h.exists_smul_swap ha hat hat₂ n1 n2 n3 hρβ hρa
  intro w hw
  have hwM : w ∈ EtilT V z a ⊔ Vv V β := Subgroup.mem_sup_left (Theta_le_EtilT hat hw)
  have e : Theta z V a t₂ = conjSub ρ (Theta z V a t) := by
    have := h.Theta_smul g a t
    rw [hga, hgt, hgρ] at this
    exact this
  have hmem : ρ * w * ρ⁻¹ ∈ Theta z V a t₂ := by
    rw [e]
    exact mul_mem_conjSub hw
  have hc := h.comm_mem_Zv_of_normal hb hb5 hC2 hβ ha ha' haa' hM hρβ hρa' hρa hwM
  have e2 : w = (ρ * w * ρ⁻¹ * w⁻¹)⁻¹ * (ρ * w * ρ⁻¹) := by group
  rw [e2]
  exact (Zv z β ⊔ Theta z V a t₂).mul_mem (Subgroup.mem_sup_left ((Zv z β).inv_mem hc))
    (Subgroup.mem_sup_right hmem)

theorem false_of_normal {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hSw : SwapProp A B)
    (hC2 : InvLeZvProp A B z V) {β a : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a)
    (hM : ∀ g ∈ stab β, conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β) : False := by
  have hat : vtype a = false := vtype_eq_false_of_adj ha hβ
  obtain ⟨t, t₂, hat1, hat2, nβt, nβt₂, ntt₂⟩ := h.exists_two_others ha.symm
  have htB : vtype t = true := vtype_eq_true_of_adj hat1 hat
  have ht₂B : vtype t₂ = true := vtype_eq_true_of_adj hat2 hat
  obtain ⟨g, hga, hgβ⟩ := exists_stab_smul_eq ha.symm hat1
  have hMt := h.normal_transport hM g hga
  rw [hgβ] at hMt
  obtain ⟨x, x', hx, hx', nax, nax', nxx'⟩ := h.exists_two_others hat1.symm
  have hxA : vtype x = false := vtype_eq_false_of_adj hx htB
  obtain ⟨ρ, hρt, hρx, hρa⟩ :=
    hSw hx.symm hxA hat1.symm nax
  have hrel := h.Theta_le_sup_of_normal hb hb5 hC2 htB hat1.symm hx nax hat2 ha.symm ntt₂
    nβt.symm nβt₂.symm hMt hρt hρx hρa
  have hle : Theta z V a t₂ ≤ Vv V β :=
    hrel.trans (sup_le ((h.Zv_le_Vv hat1 hat).trans (Vv_le_Vv_of_adj ha.symm hat))
      (h.Theta_le_Vv hat ha.symm))
  have hI : Vv V β ⊓ Vv V t₂ ≤ Vv V a := hI1 a β t₂ hat ha.symm hat2 nβt₂
  have hle2 : Theta z V a t₂ ≤ Vv V a := fun y hy => hI ⟨hle hy, h.Theta_le_Vv hat hat2 hy⟩
  have hU16 : Nat.card (Vv V t₂) = 16 := h.card_Vv_B_of_card hU ht₂B
  have hZ : Theta z V a t₂ ≤ Zv z t₂ := by
    have := h.Theta_inf_Vv hat hat2 hU16
    rw [← this]
    exact le_inf le_rfl hle2
  have hc := Subgroup.card_le_of_le hZ
  rw [h.card_Theta hat hat2 hU16, h.card_Zv ht₂B] at hc
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
