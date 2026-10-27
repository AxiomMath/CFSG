module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5D1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem smul_swap (hS : Sit H M S) {β l δ δ'' : Geo H M} (hl3 : vtype l = true)
    (hβl : β ∈ nbrs l) (hδl : δ ∈ nbrs l) (hδ''l : δ'' ∈ nbrs l) (hδ : δ ≠ β) (hδ'' : δ'' ≠ β)
    (hne : δ'' ≠ δ) (g : ↥(H ⊔ M)) (hgβ : (g : G) ∈ stab β) (hgl : (g : G) ∈ stab l)
    (hg : (g : G) ∉ Qv l) : g • δ = δ'' := by
  obtain ⟨δ3, h3, h31, h32, hall⟩ := nbrs_S3_third hS hl3 hβl hδl hδ.symm
  have hgβ' : g • β = β := smul_eq_of_mem_stab hgβ
  have key : ∀ x : Geo H M, x ∈ nbrs l → x ≠ β → x ≠ δ → x = δ3 := by
    intro x hx h1 h2
    rcases hall x hx with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  have hsd : g • δ ∈ nbrs l := smul_mem_nbrs_of_stab hgl hδl
  have h1 : g • δ ≠ β := fun h => hδ (MulAction.injective g (h.trans hgβ'.symm))
  have h2 : g • δ ≠ δ := fun h =>
    hg (mem_Qv_of_fix_two hS hl3 hβl hδl hδ.symm hgl hgβ (mem_stab_of_smul_eq h))
  rw [key _ hsd h1 h2, key _ hδ''l hδ'' hne]

omit [Finite G] in
theorem conj_mem_Vn {δ δ'' : Geo H M} (g : ↥(H ⊔ M)) (h : g • δ = δ'') {y : G} (hy : y ∈ Vn δ) :
    (g : G) * y * (g : G)⁻¹ ∈ Vn δ'' := by
  rw [← h, Vn_smul, mem_conjSub]
  simpa [mul_assoc] using hy

omit [Finite G] in
theorem trivAct_mul {A B : Subgroup G} {a b : G} (ha : a ∈ Subgroup.normalizer (A : Set G))
    (hA : ∀ y ∈ B, a * y * a⁻¹ * y⁻¹ ∈ A) (hB : ∀ y ∈ B, b * y * b⁻¹ * y⁻¹ ∈ A) :
    ∀ y ∈ B, (a * b) * y * (a * b)⁻¹ * y⁻¹ ∈ A := by
  intro y hy
  have h1 : (a * b) * y * (a * b)⁻¹ * y⁻¹ =
      (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
  rw [h1]
  exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp ha _).mp (hB y hy)) (hA y hy)

theorem dswap (hC : Ch.Ctx H M S) {β l δ δ'' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hlδ'' : l ∈ nbrs δ'') (hδ : δ ≠ β) (hδ'' : δ'' ≠ β)
    (hne : δ'' ≠ δ) (h : Vn δ'' ≤ Vn β ⊔ Vn δ) :
    ∀ q ∈ Qv β, ∀ y ∈ Vn δ, q * y * q⁻¹ * y⁻¹ ∈ Vn β := by
  have hS := hC.sit
  have hl3 : vtype l = true := vtype_nbr_S5 hβ hl
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mpr hl
  have hδl : δ ∈ nbrs l := mem_nbrs_symm.mp hlδ
  have hδ''l : δ'' ∈ nbrs l := mem_nbrs_symm.mp hlδ''
  have hvδ : vtype δ = false := vtype_nbr_S3 hl3 hδl
  have hvδ'' : vtype δ'' = false := vtype_nbr_S3 hl3 hδ''l
  obtain ⟨h1, h2, -⟩ := hC.hR β l δ δ'' hβ hl hlδ hlδ'' hδ hδ'' hne
  have hAB : ∀ a ∈ Vn β, ∀ b ∈ Vn δ, a * b = b * a := fun a ha b hb =>
    Wl_comm hS l a (Vn_le_Wl hβl ha) b (Vn_le_Wl hδl hb)
  have hAB' : ∀ a ∈ Vn β, ∀ b ∈ Vn δ'', a * b = b * a := fun a ha b hb =>
    Wl_comm hS l a (Vn_le_Wl hβl ha) b (Vn_le_Wl hδ''l hb)
  have hAel := Vn_isElemAbelian hS β
  have hAc : ∀ a ∈ Vn β, ∀ b ∈ Vn β, a * b = b * a := fun a ha b hb =>
    EmptyFaithful.Stellmacher.OrdinaryProofs.comm_of_mem_isMulCommutative hAel.1 ha hb
  have hA2 : ∀ a ∈ Vn β, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAel.2 a ha
  have hR1 : Vn β ⊓ Vn δ ≤ Vn δ'' := by rw [h1]; exact inf_le_right
  have hR2 : Vn δ ⊓ Vn δ'' ≤ Vn β := by rw [← h2]; exact inf_le_left
  have cAB := (hC.caseI β l δ hβ hl hlδ hδ)
  have cB := (hC.caseI δ l β hvδ hlδ hl hδ.symm).2
  have cB' := (hC.caseI δ'' l β hvδ'' hlδ'' hl hδ''.symm).2
  have cAB' : Nat.card ↥(Vn β ⊓ Vn δ'') = 8 := by rw [← h1]; exact cAB.1
  have hord := EmptyFaithful.Stellmacher.OrdinaryProofs.card_sup_mul_card_inf_of_centralizes
    (Y := Vn β) (C := Vn δ) (fun c hc y hy => hAB y hy c hc)
  have hord' := EmptyFaithful.Stellmacher.OrdinaryProofs.card_sup_mul_card_inf_of_centralizes
    (Y := Vn β) (C := Vn δ'') (fun c hc y hy => hAB' y hy c hc)
  rw [cAB.1, cAB.2, cB] at hord
  rw [cAB', cAB.2, cB'] at hord'
  have hsup : Vn β ⊔ Vn δ'' = Vn β ⊔ Vn δ :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left h) (by omega)
  have hBe : Vn δ ≤ Vn β ⊔ Vn δ'' := by rw [hsup]; exact le_sup_right
  have hZ : Zv β ≤ Vn β ⊓ Vn δ :=
    le_inf (Zv_le_Vn_S5 hS hβ) (Zv_le_Vn hlδ |>.trans' (Zv_le_Zv_of_nbr hS hβ hl))
  have key : ∀ q ∈ Qv β, q ∉ Qv l → ∀ y ∈ Vn δ, q * y * q⁻¹ * y⁻¹ ∈ Vn β := by
    intro q hq hql
    have hqβ : q ∈ stab β := Ch.Qv_le_stab' β hq
    have hql' : q ∈ stab l := Qv_le_stab hS hl hq
    let g : ↥(H ⊔ M) := ⟨q, stab_le β hqβ⟩
    have hg1 : g • δ = δ'' :=
      smul_swap hS hl3 hβl hδl hδ''l hδ hδ'' hne g hqβ hql' hql
    have hg2 : g • δ'' = δ :=
      smul_swap hS hl3 hβl hδ''l hδl hδ'' hδ hne.symm g hqβ hql' hql
    refine swap_comm_mem hAB hAB' hAc hA2 hR1 hR2 hBe h ?_ ?_ ?_ ?_
    · intro a ha
      exact (Subgroup.mem_normalizer_iff.mp (Vn_normal β hqβ) a).mp ha
    · intro a ha
      exact hZ (Ch.comm_mem_Zv_of_Qv hS hβ hq ha)
    · exact fun y hy => conj_mem_Vn g hg1 hy
    · exact fun y hy => conj_mem_Vn g hg2 hy
  intro q hq
  by_cases hql : q ∈ Qv l
  · obtain ⟨t, htβ, htl⟩ := IsConcreteLE.not_le_iff_exists.mp (Q_not_le hS hβ hl)
    have h1 := key t⁻¹ ((Qv β).inv_mem htβ) (fun h' => htl ((Qv l).inv_mem_iff.mp h'))
    have h2 := key (t * q) ((Qv β).mul_mem htβ hq)
      (fun h' => htl (by simpa using (Qv l).mul_mem h' ((Qv l).inv_mem hql)))
    have := trivAct_mul (Vn_normal β ((Qv β).inv_mem htβ |> Ch.Qv_le_stab' β)) h1 h2
    simpa using this
  · exact key q hq hql

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
