module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10E
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.A10S

open S35.II S35.Std S35.E10

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_Vn_le_Qv (hS : Sit H M S) {β α' m γ' : Geo H M} (h3a : Claim3a H M)
    (hl : Lam β α') (hb : Back H M β α' m γ') : ¬ Vn α' ≤ Qv β := by
  intro hle
  obtain ⟨hp, hZβ⟩ := hl
  obtain ⟨hne, -⟩ := h3a β α' m γ' hp hb
  have h1 : ⁅Vn β, Vn α'⁆ ≤ Zv β :=
    (Subgroup.commutator_mono le_rfl hle).trans (comm_Vn_Qv hS hp.vδ).le
  have h2 : Zv β ≤ ⁅Vn β, Vn α'⁆ := le_of_ne_bot (hS.cardZ5 β hp.vδ) h1 hne
  exact hZβ (h2.trans ((PD_comm_le hS hp).trans inf_le_right))

theorem not_B_le_Qv (hS : Sit H M S) {β α' α : Geo H M} {B : Subgroup G} (hp : S34.PD β α')
    (hZβ : ¬ Zv β ≤ Vn α') (hα : α ∈ nbrs β) (hB : B ≤ Vn α') (hne : ⁅B, Zv α⁆ ≠ ⊥) :
    ¬ B ≤ Qv β := by
  intro hBQ
  have hvβ := hp.vδ
  have hle1 : ⁅B, Zv α⁆ ≤ Zv β := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Zv_le_Vn hα) hBQ).trans (comm_Vn_Qv hS hvβ).le
  have hle2 : Zv β ≤ ⁅B, Zv α⁆ := le_of_ne_bot (hS.cardZ5 β hvβ) hle1 hne
  have hle3 : ⁅B, Zv α⁆ ≤ Vn α' := by
    rw [Subgroup.commutator_le]
    intro b hb' z hz
    have hzs : z ∈ stab α' := (PD_Vn_le_stab hS hp).1 (Zv_le_Vn hα hz)
    have h : z * b⁻¹ * z⁻¹ ∈ Vn α' :=
      (Subgroup.mem_normalizer_iff.mp (Vn_normal α' hzs) _).mp ((Vn α').inv_mem (hB hb'))
    have e : ⁅b, z⁆ = b * (z * b⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Vn α').mul_mem (hB hb') h
  exact hZβ (hle2.trans hle3)

theorem claim10Sym (hS : Sit H M S) (h3a : Claim3a H M) (hTT : ClaimTT H M)
    (h9 : Claim9T H M) (h8a : Claim8a H M) (h16 : Claim16a H M) (h7 : Lemma7s H M) :
    Claim10Sym H M := by
  intro β α' hl
  obtain ⟨m, γ', hm, hγ, h1, h2⟩ := exists_geodesic hS hl.1.dist_eq
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  have hp := hl.1
  have hZβ := hl.2
  have hvβ := hp.vδ
  have hQ := not_Vn_le_Qv hS h3a hl hb
  have hpd : S34.PD α' β :=
    ⟨hp.vδ', hvβ, by rw [CosetGeom.dist_comm]; exact hp.dist_eq, hQ⟩
  refine ⟨hpd, fun hZα' => ?_⟩
  obtain ⟨α, hα, hαZ⟩ := exists_nbr_Zv_not_le hp
  have ht := h16 β α' hl
  have hT := hTT β α' m γ' hp hb ht
  obtain ⟨A, B, hA, hB, hAB, hVA, hW8, hZB⟩ := h8a β α' hp ht
  have hne := hZB α hα hαZ
  have hBQ := not_B_le_Qv hS hp hZβ hα hB hne
  obtain ⟨x, hxB, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hBQ
  obtain ⟨hvm, -, -, -, -, -⟩ := back_facts hS hp hb
  have hxs : x ∈ stab β := (PD_Vn_le_stab hS hp).2 (hB hxB)
  have hBst : B ≤ stab β := hB.trans (PD_Vn_le_stab hS hp).2
  have hWm : Wb β ⊓ stab m ≤ Wb β ⊓ stab α' :=
    fun w hw => ⟨hw.1, Wb_inf_stab_le hS hvm (mem_nbrs_symm.mp hb.1) hZα' hw⟩
  have hK2 : (Wb β ⊓ stab α').relIndex (Wb β) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_left hWm Subgroup.index_ne_zero_of_finite).trans
      (h9 β α' m γ' hp hb hT)
  have hK : ∀ e ∈ Wb β ⊓ stab α', ⁅e, x⁆ ∈ Vn β := by
    intro e he
    have h1 : ⁅e, x⁆ ∈ ⁅Wb β ⊓ stab α', B⁆ := Subgroup.commutator_mem_commutator he hxB
    exact (sup_le hZα' (comm_Vn_le hBst)) (hW8 h1)
  refine h7 β α' hp ht hZα' x (hB hxB) hxQ (Wb β ⊓ stab α')
    (le_inf (Vn_le_Wb_self hS hvβ) (PD_Vn_le_stab hS hp).1) inf_le_left hK2 hK ?_
  intro hW
  refine not_centralizes_Wb hS hvβ hxs hxQ fun w hw => ?_
  have e1 : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e1]
  exact (Vn β).inv_mem (hK w ⟨hw, hW hw⟩)

end S35.A10S

end F53.Stellmacher

end CFSG.Quasithin
