module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpComm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpComm2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpEnd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_PD (hS : Sit H M S) : ∃ β α' : Geo H M, S34.PD β α' := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Geo H M, vtype δ = false := by
    obtain ⟨e, he⟩ := exists_adj (γ₀ (H ⊔ M) H M)
    have hne := vtype_ne_of_adj he
    by_cases hv : vtype (γ₀ (H ⊔ M) H M) = false
    · exact ⟨_, hv⟩
    · refine ⟨e, ?_⟩
      cases h : vtype e
      · rfl
      · exfalso
        apply hne
        rw [h]
        simpa using hv
  obtain ⟨l, hl⟩ := exists_adj δ
  have hl' : l ∈ nbrs δ := hl
  have hlt := Std.vtype_nbr_S5 hδ hl'
  obtain ⟨α', hc⟩ := exists_critData hS.glob.amalg (hS.glob.crit l hlt)
    (Std.mem_nbrs_symm.mpr hl' : δ ∈ nbrs l)
  obtain ⟨-, -, -, -, hp⟩ := Std.Zv_not_le_Qv_crit hS hc hlt
  exact ⟨δ, α', hp⟩

theorem claimLP_of_dict (hS : Sit H M S)
    (hch : ∀ δ : Geo H M, vtype δ = false → Nonempty (Ch.Chart δ))
    (hPl : ∀ (δ : Geo H M) (c : Ch.Chart δ) (l : Geo H M), vtype δ = false → l ∈ nbrs δ →
      PlaneAt c l)
    (hZl : ∀ (δ : Geo H M) (c : Ch.Chart δ) (l : Geo H M), vtype δ = false → l ∈ nbrs δ →
      ZlAt c l) : ClaimLP H M := by
  by_contra hneg
  obtain ⟨β, α', hp⟩ := exists_PD hS
  obtain ⟨m, γ', hm, hγ, h1, h2, -⟩ := Std.PD_geodesic hS hp
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  obtain ⟨cα⟩ := hch α' hp.vδ'
  have hpl : PlaneAt cα m := hPl α' cα m hp.vδ' hm
  have hnQ := not_Vn_le_Qv hS hneg hp hb cα hpl
  have hp' : S34.PD α' β := hp.symm' hnQ
  obtain ⟨m', γ'', hm', hγ'', h1', h2', -⟩ := Std.PD_geodesic hS hp'
  have hb' : Back H M α' β m' γ'' := ⟨hm', hγ'', h1', h2'⟩
  obtain ⟨cβ⟩ := hch β hp.vδ
  have hpl' : PlaneAt cβ m' := hPl β cβ m' hp.vδ hm'
  have hZR := Zv_le_comm hS hneg hp hb hp' hb' cα cβ hpl hpl'
  have hZα : Zv α' ≤ Vn β := fun x hx => (Std.PD_comm_le hS hp (hZR hx)).1
  obtain ⟨cγ⟩ := hch γ' (back_vtype_γ hp hb)
  have hZγ : ZlAt cγ m :=
    hZl γ' cγ m (back_vtype_γ hp hb) (Std.mem_nbrs_symm.mp hb.2.1)
  have hWQ := Wb_le_Qm hS hneg hp hb cγ hZγ hZα
  have hc := comm_Vn_Wb_le hS hneg hp hb cα hpl hZR hWQ
  exact end_contra hS hp.vδ (Std.PD_Vn_le_stab hS hp).2 hnQ hc

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
