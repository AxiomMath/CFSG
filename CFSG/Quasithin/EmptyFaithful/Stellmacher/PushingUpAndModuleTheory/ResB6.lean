module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB3Model
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem centerOf_stab_le_Qv (hA : F53Amalgam H M S) (δ : Geo H M) :
    centerOf (stab δ) ≤ Qv δ := fun _ hx =>
  charTwo_stab hA δ ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hx.2 q (CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ) hq)⟩

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem Zv_le_Oo_sup (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    Zv δ ≤ OoOf δ ⊔ centerOf (stab δ) := by
  obtain ⟨c, V₀, -, -, -, -, -, -, -, -, hOQ, -, hcentral, hnormO, -, hnormL1, hQsup, hinf, -⟩ :=
    h.A3 hA
  unfold Zv
  refine iSup₂_le fun T hT => ?_
  unfold quasithinOmegaOneCenter
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  have hQT : Qv δ ≤ T := isSylowTwoOf_pCoreOf_le hT
  have hzQ : z ∈ Qv δ := charTwo_stab hA δ ⟨hT.1 hzT,
    Subgroup.mem_centralizer_iff.mpr fun q hq => Subgroup.mem_centralizer_iff.mp hzC q (hQT hq)⟩
  have hL1Q : L1Of δ ≤ Qv δ := inf_le_left
  obtain ⟨o, ho, l, hl, rfl⟩ := mem_sup_of_commute
    (fun o ho l hl => hcentral o ho l (hL1Q hl)) (hQsup ▸ hzQ)
  have hlT : ∀ t ∈ T, t * l = l * t := by
    intro t ht
    have htd : t ∈ stab δ := hT.1 ht
    have h1 : t * o * t⁻¹ ∈ OoOf δ := (Subgroup.mem_normalizer_iff.mp (hnormO htd) o).mp ho
    have h2 : t * l * t⁻¹ ∈ L1Of δ := (Subgroup.mem_normalizer_iff.mp (hnormL1 htd) l).mp hl
    have hc : t * (o * l) = (o * l) * t := (Subgroup.mem_centralizer_iff.mp hzC t ht)
    have hab : (t * o * t⁻¹) * (t * l * t⁻¹) = o * l := by
      calc (t * o * t⁻¹) * (t * l * t⁻¹) = t * (o * l) * t⁻¹ := by group
        _ = (o * l) * t * t⁻¹ := by rw [hc]
        _ = o * l := by group
    have e : o⁻¹ * (t * o * t⁻¹) = l * (t * l * t⁻¹)⁻¹ := by
      calc o⁻¹ * (t * o * t⁻¹) = o⁻¹ * ((t * o * t⁻¹) * (t * l * t⁻¹)) * (t * l * t⁻¹)⁻¹ := by group
        _ = l * (t * l * t⁻¹)⁻¹ := by rw [hab]; group
    have h3 : l * (t * l * t⁻¹)⁻¹ ∈ OoOf δ ⊓ L1Of δ :=
      ⟨e ▸ (OoOf δ).mul_mem ((OoOf δ).inv_mem ho) h1, (L1Of δ).mul_mem hl ((L1Of δ).inv_mem h2)⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
    calc t * l = (t * l * t⁻¹) * t := by group
      _ = l * t := by rw [← h3]
  have hL : ∀ x ∈ pResidualOf 2 (stab δ), x * l = l * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hl.2 x hx
  have hlc : l ∈ centerOf (stab δ) := by
    have hlS : l ∈ stab δ := CFSG.LieType.BorelTits.pCoreOf_le 2 (stab δ) (hL1Q hl)
    refine ⟨hlS, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hle : stab δ ≤ Subgroup.centralizer ({l} : Set G) := by
      have h1 := le_oTwoRes_sup_of_isSylowTwoOf hT
      rw [← pResidualOf_eq_oTwoRes] at h1
      refine h1.trans (sup_le ?_ ?_)
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hL x hx
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hlT x hx)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hlc)

theorem Oo_le_Zv (hA : F53Amalgam H M S) (h : ConfR δ μ U) : OoOf δ ≤ Zv δ := by
  obtain ⟨fr⟩ := h.exists_frame hA
  obtain ⟨w₀, hw₀, hfix⟩ := exists_fixed_Syl
  have hSQ : Qv δ ≤ stab δ ⊓ stab μ := Qv_le_edge hA (h.sig.adj : μ ∈ nbrs δ)
  have hOQ : OoOf δ ≤ Qv δ := by
    obtain ⟨c, V₀, -, -, -, -, -, -, -, -, h9, -⟩ := h.A3 hA
    exact h9
  have hcomm : ∀ s ∈ stab δ ⊓ stab μ, s * fr.γ w₀ = fr.γ w₀ * s := by
    intro s hs
    have hΨ : fr.Ψ ⟨s, hs.1⟩ ∈ S5Syl := by
      rw [← fr.syl]
      exact ⟨⟨s, hs.1⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have := fr.equiv ⟨s, hs.1⟩ w₀
    rw [hfix _ hΨ] at this
    calc s * fr.γ w₀ = (s * fr.γ w₀ * s⁻¹) * s := by group
      _ = fr.γ w₀ * s := by rw [← this]
  have he : fr.γ w₀ ∈ Zv δ := by
    refine ((omegaOneCenter_le_Zv hA (h.sig.adj : μ ∈ nbrs δ)).2.1) ?_
    refine Subgroup.subset_closure ⟨⟨hSQ (hOQ (fr.mem w₀)), ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun s hs => hcomm s hs
    · rw [pow_two, ← map_mul, orth.sq w₀, map_one]
  have hnorm := stab_le_normalizer_Zv hA δ
  have hY : (Zv δ).comap fr.γ = ⊤ := by
    rcases irreducible_orth ((Zv δ).comap fr.γ) (fun σ y hy => by
      obtain ⟨k, rfl⟩ := fr.surjΨ σ
      rw [Subgroup.mem_comap, fr.equiv]
      exact (Subgroup.mem_normalizer_iff.mp (hnorm k.2) _).mp hy) with h0 | h0
    · exact absurd (Subgroup.mem_bot.mp (h0 ▸ (show w₀ ∈ (Zv δ).comap fr.γ from he))) hw₀
    · exact h0
  intro x hx
  obtain ⟨w, rfl⟩ := fr.surj x hx
  exact (Subgroup.mem_comap.mp (hY ▸ Subgroup.mem_top w))

end ConfR

end CFSG.Quasithin.F53
