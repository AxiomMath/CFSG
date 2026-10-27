module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Ch2
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.N9

open S35.Std S35.At S35.Fin S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Gen4 : Prop :=
  ∀ {D W : Subgroup (Perm (Fin 5))}, Nat.card D = 8 → IsPGroup 2 W → 3 ≤ D.relIndex W →
    That D ⊔ W = ⊤

omit [Finite G] in
theorem relIndex_preθ2 {δ : Geo H M} (c : Chart2 δ) {A : Subgroup G} (hA : A ≤ stab δ)
    (D : Subgroup (Perm (Fin 5))) : (c.preθ D).relIndex A = D.relIndex (c.bar A) := by
  have e1 : (c.preθ D).subgroupOf (stab δ) = D.comap c.θ := by
    ext x
    rw [Subgroup.mem_subgroupOf, c.mem_preθ_iff]
    rfl
  rw [← Subgroup.relIndex_subgroupOf hA (H := c.preθ D), e1, Subgroup.relIndex_comap]
  rfl

omit [Finite G] in
theorem isPGroup_bar2 {δ : Geo H M} (c : Chart2 δ) {A : Subgroup G} (hA : A ≤ stab δ)
    (h : IsPGroup 2 A) : IsPGroup 2 (c.bar A) := by
  have h1 : IsPGroup 2 (A.subgroupOf (stab δ)) :=
    h.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
  exact h1.map c.θ

theorem mem_normalizer_X {γ : Geo H M} {R Z : Subgroup G} (hZV : Z ≤ Vn γ) {q : G}
    (hq : q ∈ stab γ) (hqR : ∀ r ∈ R, ⁅q, r⁆ ∈ Z) :
    q ∈ Subgroup.normalizer ((R ⊔ Vn γ : Subgroup G) : Set G) := by
  refine mem_normalizer_sup (fun r hr => ?_) (fun v hv => ?_)
  · have e : q * r * q⁻¹ = ⁅q, r⁆ * r := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hZV (hqR r hr))) (Subgroup.mem_sup_left hr)
  · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (Vn_normal γ hq) v).mp hv)

theorem claim9T_core (hS : Sit H M S) (hII : CaseII H M) (h6b : Claim6b H M)
    (hNb : S35.II.NbarThat H M) (h3a : S35.II.Claim3a H M) (hG4 : Gen4) :
    S35.II.Claim9T H M := by
  intro β α' m γ' hp hb hT
  by_contra hcon
  have hcon' : 2 < (Wb β ⊓ stab m).relIndex (Wb β) := not_le.mp hcon
  obtain ⟨hvm, hvγ, hne, -, -⟩ := Back.facts hp hb
  have hvα : vtype α' = false := hp.vδ'
  have hvβ : vtype β = false := hp.vδ
  have hmα : m ∈ nbrs α' := hb.1
  have hml : m ∈ nbrs γ' := mem_nbrs_symm.mp hb.2.1
  have hne' : α' ≠ γ' := fun h => hne h.symm
  have hWst : Wb β ≤ stab γ' := Back.Wb_le_stab hS hp hb
  have hβst : Vn β ≤ stab γ' := (Vn_le_Wb_self hS hvβ).trans hWst
  have hVγst : Vn γ' ≤ stab γ' := (Vn_le_Qv_self hS γ').trans (Ch.Qv_le_stab' γ')
  set R : Subgroup G := ⁅Vn β, Vn α'⁆ with hRdef
  set X : Subgroup G := R ⊔ Vn γ' with hXdef
  have hRle : R ≤ Vn β ⊓ Vn α' := PD_comm_le hS hp
  have hRβ : R ≤ Vn β := hRle.trans inf_le_left
  have hRα : R ≤ Vn α' := hRle.trans inf_le_right
  have hVX : Vn γ' ≤ X := le_sup_right
  have hRX : R ≤ X := le_sup_left
  have hZV : Zv α' ≤ Vn γ' := (Zv_le_Zv_of_nbr hS hvα hmα).trans (Zv_le_Vn hml)
  obtain ⟨c'⟩ := exists_chart2 hS hvα
  have hPl : R ≤ Plane2 α' m := by
    have := c'.commutator_le_Plane2' hS hvα hmα hT
    rwa [Subgroup.commutator_comm] at this
  have hRC : ∀ r ∈ R, ∀ q ∈ That2 α' m, ⁅q, r⁆ ∈ Zv α' := fun r hr q hq =>
    ((mem_That2_iff hS).mp hq).2 r (hPl hr)
  obtain ⟨c⟩ := exists_chart2 hS hvγ
  have hD8 : Nat.card (c.Dl m) = 8 := c.card_Dl hS hml
  have hDpre := c.preθ_Dl hS hvγ hml
  set Nn : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ stab γ' with hNn
  have hWN : Wb β ≤ Nn := fun w hw => ⟨mem_normalizer_X (R := R) (Z := ⊥) bot_le (hWst hw)
    (fun r hr => by
      have h1 : ⁅r, w⁆ ∈ ⁅Vn β, Wb β⁆ := Subgroup.commutator_mem_commutator (hRβ hr) hw
      rw [comm_Vn_Wb hS β, Subgroup.mem_bot] at h1
      rw [← commutatorElement_inv, h1]; simp), hWst hw⟩
  have hAst : Qv α' ⊓ Qv m ≤ stab γ' := inf_le_right.trans (Qv_le_stab hS hb.2.1)
  have hAN : Qv α' ⊓ Qv m ≤ Nn := fun q hq => ⟨mem_normalizer_X (R := R) hZV (hAst hq)
    (fun r hr => by
      have h1 : ⁅r, q⁆ ∈ ⁅Vn α', Qv α'⁆ := Subgroup.commutator_mem_commutator (hRα hr) hq.1
      rw [comm_Vn_Qv hS hvα] at h1
      rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ h1), hAst hq⟩
  have hN₀N : (Qv γ' ⊓ Qv m) ⊓ That2 α' m ≤ Nn := fun q hq =>
    ⟨mem_normalizer_X (R := R) hZV (Ch.Qv_le_stab' γ' hq.1.1) (fun r hr => hRC r hr q hq.2),
      Ch.Qv_le_stab' γ' hq.1.1⟩
  have e1 : Wb β ⊓ stab m = Wb β ⊓ c.preθ (c.Dl m) := by
    rw [hDpre]
    ext g
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, hWst h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hidxW : (Wb β ⊓ stab m).relIndex (Wb β) = (c.Dl m).relIndex (c.bar (Wb β)) := by
    rw [e1, Subgroup.inf_relIndex_left, relIndex_preθ2 c hWst]
  have hWp : IsPGroup 2 (Wb β) := IsPGroup.to_le (pCoreOf_isPGroup 2 (stab β)) (Wb_le_Qv hS β)
  have hgen := hG4 hD8 (isPGroup_bar2 c hWst hWp) (by rw [← hidxW]; omega)
  have hT2 := hNb α' m γ' hvα hmα hml hne
  have hQγst : Qv γ' ≤ stab γ' := Ch.Qv_le_stab' γ'
  set P : Subgroup G := Nn ⊔ Qv γ' with hP
  have hPst : P ≤ stab γ' := sup_le inf_le_right hQγst
  have hT2P : That2 γ' m ≤ P := hT2.trans (sup_le_sup_right hAN _)
  have hbarP : c.bar P = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le ?_ ?_
    · rw [← c.bar_That2' hS hvγ hml]
      exact c.bar_mono hT2P
    · exact c.bar_mono (hWN.trans le_sup_left)
  have hstabP : stab γ' ≤ P := by
    intro x hx
    have h1 : x ∈ c.preθ (c.bar P) := (c.mem_preθ_iff ⟨x, hx⟩).mpr (by rw [hbarP]; trivial)
    rwa [c.preθ_bar hS hvγ hPst le_sup_right] at h1
  have hsup : Nn ⊔ Qv γ' = stab γ' := le_antisymm hPst hstabP
  have hA2 := relIndex_Qv hS hvγ hml
  have hTF := thatFacts hS α' m hvα hmα
  have hAD : Qv γ' ⊓ Qv m ≤ stab α' ⊓ stab m :=
    le_inf (inf_le_right.trans (Qv_le_stab hS (mem_nbrs_symm.mp hmα))) (inf_le_right.trans
      (Ch.Qv_le_stab' m))
  have hN₀idx : ((Qv γ' ⊓ Qv m) ⊓ That2 α' m).relIndex (Qv γ') ≤ 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := (Qv γ' ⊓ Qv m) ⊓ That2 α' m)
      (K := Qv γ' ⊓ Qv m) (L := Qv γ') inf_le_left inf_le_left
    rw [← h1, hA2, Subgroup.inf_relIndex_left]
    have h3 := Subgroup.relIndex_le_of_le_right hAD
      (relIndex_ne_zero' (That2 α' m) (stab α' ⊓ stab m))
    rw [hTF.2.2] at h3
    omega
  have hidxN : Nn.relIndex (stab γ') ≤ 4 :=
    (relIndex_le_of_sup_eq inf_le_right (le_normalizer_pCoreOf 2 (stab γ')) hsup
      (le_inf hN₀N (inf_le_left.trans inf_le_left))).trans hN₀idx
  have hq := quot_stab_five hS.glob.amalg hvγ
  have hLN : Lr γ' ≤ Nn := S35.B5.oTwoRes_le_of_relIndex_le_four hq inf_le_right hidxN
  have hXst : X ≤ stab γ' := sup_le (hRβ.trans hβst) hVγst
  have hLX : Lr γ' ≤ Subgroup.normalizer (X : Set G) := hLN.trans inf_le_left
  have hXc : (Vn γ').relIndex X ≤ 4 := by
    have h1 := F53.Stellmacher.relIndex_inf_eq_relIndex_sup (K := R) (Q := Vn γ')
      ((hRβ.trans hβst).trans (Vn_normal γ'))
    rw [← h1]
    have h2 : R ⊓ Zv α' ≤ R ⊓ Vn γ' := inf_le_inf_left R hZV
    refine (Subgroup.relIndex_le_of_le_left h2 (relIndex_ne_zero' _ _)).trans ?_
    rw [Subgroup.inf_relIndex_left]
    refine (Subgroup.relIndex_le_of_le_right hPl (relIndex_ne_zero' _ _)).trans ?_
    rw [c'.relIndex_Zv_Plane2' hS hvα hmα]
  have hcomm := comm_trivial_of_card_le_four hS hvγ hXst hLX hXc
  have hd2 : dist α' γ' = 2 := dist_eq_two_iff.mpr ⟨m, hml, mem_nbrs_symm.mp hmα, hne'⟩
  have hXW : X ≤ Wb γ' := sup_le (hRα.trans (Vn_le_Wb hd2)) (Vn_le_Wb_self hS hvγ)
  obtain ⟨E, hEn, hVE, hXE, hEW, hEL⟩ := exists_normalClosure hS hVX hXW hcomm
  have h6 := h6b γ' m α' E hvγ hml hmα hne' hEn hVE hEW hEL
  have hR1 : R ≤ Zv m := by
    have h7 : R ≤ Vn α' ⊓ Vn γ' := by rw [← h6]; exact le_inf hRα (hRX.trans hXE)
    rw [← hII γ' m α' hvγ hml hmα hne', inf_comm]
    exact h7
  exact (h3a β α' m γ' hp hb).2 hR1

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
