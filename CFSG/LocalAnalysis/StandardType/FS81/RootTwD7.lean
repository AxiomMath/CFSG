module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem exists_normalizer_conj_of_tori {G : Type} [Group G] [Finite G] {E : Subgroup G} {β : G}
    (hE : IsElemAbelian 3 E)
    (htor : ∀ F : Subgroup G, F ≤ Subgroup.centralizer ({β} : Set G) → IsElemAbelian 3 F →
      Nat.card F = Nat.card E →
      ∃ c ∈ Subgroup.centralizer ({β} : Set G), F.map (MulAut.conj c).toMonoidHom = E)
    {g : G} (hg : g * β * g⁻¹ ∈ E) :
    ∃ n ∈ Subgroup.normalizer (E : Set G), g * β * g⁻¹ = n * β * n⁻¹ := by
  have hF_le : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({β} : Set G) := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hf
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxe : e * (g * β * g⁻¹) = (g * β * g⁻¹) * e :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨g * β * g⁻¹, hg⟩)
    calc β * (g⁻¹ * e * g) = g⁻¹ * ((g * β * g⁻¹) * e) * g := by group
      _ = g⁻¹ * (e * (g * β * g⁻¹)) * g := by rw [hxe]
      _ = (g⁻¹ * e * g) * β := by group
  have hF_elem : IsElemAbelian 3 (E.map (MulAut.conj g⁻¹).toMonoidHom) := hE.map _
  have hF_card : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨c, hcC, hcF⟩ := htor _ hF_le hF_elem hF_card
  have hcβ : c⁻¹ * β * c = β := by
    have hcomm : β * c = c * β := (Subgroup.mem_centralizer_iff.mp hcC) β (Set.mem_singleton β)
    calc c⁻¹ * β * c = c⁻¹ * (β * c) := by group
      _ = c⁻¹ * (c * β) := by rw [hcomm]
      _ = β := by group
  have hcomp : ((MulAut.conj c).toMonoidHom).comp ((MulAut.conj g⁻¹).toMonoidHom) =
      (MulAut.conj (c * g⁻¹)).toMonoidHom := by
    ext x
    change MulAut.conj c (MulAut.conj g⁻¹ x) = MulAut.conj (c * g⁻¹) x
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hEmap : E.map (MulAut.conj (c * g⁻¹)).toMonoidHom = E := by
    conv_rhs => rw [← hcF]
    rw [Subgroup.map_map, hcomp]
  refine ⟨g * c⁻¹, ?_, ?_⟩
  · have hninv : (g * c⁻¹)⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
      rw [show (g * c⁻¹)⁻¹ = c * g⁻¹ by group]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hEmap
    simpa using Subgroup.inv_mem _ hninv
  · have h1 : (g * c⁻¹) * β * (g * c⁻¹)⁻¹ = g * (c⁻¹ * β * c) * g⁻¹ := by group
    rw [h1, hcβ]

theorem RootSetting.exists_conj_eq_of_conj_mem_root {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y) (hA : E8AutAt Row.twD7) (hT : E8TorusAt Row.twD7)
    (hBT : TwD7BetaTorAt)
    (hβC : Subgroup.centralizer ({rowRootElt Row.twD7 B b₀} : Set G) ≤ Y) {g : G}
    (hg : g * rowRootElt Row.twD7 B b₀ * g⁻¹ ∈ Y) :
    ∃ y ∈ Y, g * rowRootElt Row.twD7 B b₀ * g⁻¹ = y * rowRootElt Row.twD7 B b₀ * y⁻¹ := by
  have hE : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by rw [← h.adapted.2.1]; exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hordβ : orderOf (b₀ * B.b 1) = 3 := by
    have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) =
        b₀ * B.b 1 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h.adapted.2.1]
    refine orderOf_eq_prime ?_ ?_
    · rw [← hvec]
      exact hE.2 _ (h.adapted.1 ▸ B.vec_mem_span _)
    · intro h1
      have h1' : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 1) = 1 := by
        rw [hvec, h1]
      have he0 := B.indep _ h1'
      have h0 := congrFun he0 0
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (0 : Fin (Row.twD7.n + 1)) ≠ 1),
        Pi.zero_apply, add_zero] at h0
      exact one_ne_zero h0
  have hfus : ∀ g : G, g * (b₀ * B.b 1) * g⁻¹ ∈ E →
      ∃ n ∈ Subgroup.normalizer (E : Set G),
        g * (b₀ * B.b 1) * g⁻¹ = n * (b₀ * B.b 1) * n⁻¹ := by
    intro g hgE
    refine exists_normalizer_conj_of_tori hE (fun F hF h3 hc => ?_) hgE
    obtain ⟨c, hcC, hcF⟩ := hBT G b₀ K E B Y h F (by rwa [inf_eq_left.mpr hβC]) h3 hc
    exact ⟨c, hcC.1, hcF⟩
  have htor : ∀ g : G, g * (b₀ * B.b 1) * g⁻¹ ∈ Y →
      ∃ y ∈ Y, y * (g * (b₀ * B.b 1) * g⁻¹) * y⁻¹ ∈ E := by
    intro g hgY
    refine hT G b₀ K E B Y h (g * (b₀ * B.b 1) * g⁻¹) hgY ?_
    have hord : orderOf (g * (b₀ * B.b 1) * g⁻¹) = orderOf (b₀ * B.b 1) := by
      simpa using (MulAut.conj g).orderOf_eq (b₀ * B.b 1)
    rw [hord, hordβ]
  have hg' : g * (b₀ * B.b 1) * g⁻¹ ∈ Y := hg
  exact exists_conj_Y_of_toral hβE hfus (hA G b₀ K E B Y h) htor hg'

theorem l3RootFusionAt_twD7_of (hC : RowCentAt Row.twD7) (hR : E8RadicalAt Row.twD7)
    (hA : E8AutAt Row.twD7) (hT : E8TorusAt Row.twD7) (hI : E8InvCommAt Row.twD7)
    (hRC : E8RootCentAt Row.twD7) (hBC : TwD7BetaCentAt) (hBT : TwD7BetaTorAt) :
    L3RootFusionAt Row.twD7 := by
  intro G _ _ b₀ K E hstd hchar B hB hrec hfus Y hY hcap hcore
  have h : RootSetting Row.twD7 b₀ K E B Y := ⟨hstd, hchar, hB, hrec, hfus, hY, hcap, hcore⟩
  have hbC := h.centralizer_le_of_e8 (by decide) hC hR hA
  have hfusY : ∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹ :=
    fun g hg => h.exists_conj_eq_of_conj_mem hA hT hg
  have hβC := hBC G b₀ K E B Y h hbC hfusY
  have hfusβ : ∀ g : G, g * rowRootElt Row.twD7 B b₀ * g⁻¹ ∈ Y →
      ∃ y ∈ Y, g * rowRootElt Row.twD7 B b₀ * g⁻¹ = y * rowRootElt Row.twD7 B b₀ * y⁻¹ :=
    fun g hg => h.exists_conj_eq_of_conj_mem_root hA hT hBT hβC hg
  obtain ⟨S, t, hS, htS, ht2, htc, htC⟩ := hRC G b₀ K E B Y h hbC hfusY hβC hfusβ
  refine ⟨S, t, hS, htS, ht2, htc, fun g hg => ?_⟩
  refine mem_of_conj_mem_of_commute_conj hβC (fun x hx => hfusβ x (htC hx))
    (fun g' hg' => ?_) hg
  refine hI G b₀ K E B Y h _ hg' ?_
  have : orderOf (g' * t * g'⁻¹) = orderOf t := by simpa using (MulAut.conj g').orderOf_eq t
  rw [this, ht2]

end CFSG.StandardType.FrameRoute.FS81
