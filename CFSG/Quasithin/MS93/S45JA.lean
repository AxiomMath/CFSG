module

import CFSG.Quasithin.MS93.S45Phi1
public import CFSG.Quasithin.MS93.S45RG

public section

namespace CFSG.Quasithin.MS93.S45J

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

section Group

variable {𝔾 : Type*} [Group 𝔾]

theorem eq_one_or_eq_of_card_two {C : Subgroup 𝔾} (hC : Nat.card C = 2) {x : 𝔾} (hxC : x ∈ C)
    (hx : x ≠ 1) {y : 𝔾} (hyC : y ∈ C) : y = 1 ∨ y = x := by
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hC
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    have e1 : (⟨y, hyC⟩ : C) = u := hu _ fun h => hy1 (congrArg Subtype.val h)
    have e2 : (⟨x, hxC⟩ : C) = u := hu _ fun h => hx (congrArg Subtype.val h)
    exact congrArg Subtype.val (e1.trans e2.symm)

theorem eq_one_of_mem_of_card_two {A B : Subgroup 𝔾} (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hAB : A ≠ B) {x : 𝔾} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  by_contra hx
  have hle : A ≤ B := fun y hy => by
    rcases eq_one_or_eq_of_card_two hA hxA hx hy with rfl | rfl
    · exact one_mem B
    · exact hxB
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  exact hAB (Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hB]))

def relCen (Q U : Subgroup 𝔾) (hQU : U ≤ Subgroup.centralizer (Q : Set 𝔾)) : Subgroup 𝔾 where
  carrier := {k | k ∈ Q ∧ ∀ s ∈ Q, ⁅k, s⁆ ∈ U}
  one_mem' := ⟨one_mem Q, fun s _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
    refine ⟨mul_mem hk₁ hk₂, fun s hs => ?_⟩
    have hc : k₁ * ⁅k₂, s⁆ = ⁅k₂, s⁆ * k₁ :=
      Subgroup.mem_centralizer_iff.mp (hQU (h₂ s hs)) k₁ hk₁
    have e : ⁅k₁ * k₂, s⁆ = ⁅k₂, s⁆ * ⁅k₁, s⁆ := by
      calc ⁅k₁ * k₂, s⁆ = (k₁ * ⁅k₂, s⁆) * k₁⁻¹ * ⁅k₁, s⁆ := by
            simp only [commutatorElement_def]; group
        _ = (⁅k₂, s⁆ * k₁) * k₁⁻¹ * ⁅k₁, s⁆ := by rw [hc]
        _ = ⁅k₂, s⁆ * ⁅k₁, s⁆ := by group
    rw [e]
    exact mul_mem (h₂ s hs) (h₁ s hs)
  inv_mem' := by
    rintro k ⟨hk, h⟩
    refine ⟨inv_mem hk, fun s hs => ?_⟩
    have hc : k⁻¹ * ⁅k, s⁆⁻¹ = ⁅k, s⁆⁻¹ * k⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hQU (inv_mem (h s hs))) k⁻¹ (inv_mem hk)
    have e : ⁅k⁻¹, s⁆ = ⁅k, s⁆⁻¹ := by
      calc ⁅k⁻¹, s⁆ = (k⁻¹ * ⁅k, s⁆⁻¹) * k := by simp only [commutatorElement_def]; group
        _ = (⁅k, s⁆⁻¹ * k⁻¹) * k := by rw [hc]
        _ = ⁅k, s⁆⁻¹ := by group
    rw [e]
    exact inv_mem (h s hs)

theorem mem_relCen_iff {Q U : Subgroup 𝔾} {hQU : U ≤ Subgroup.centralizer (Q : Set 𝔾)} {k : 𝔾} :
    k ∈ relCen Q U hQU ↔ k ∈ Q ∧ ∀ s ∈ Q, ⁅k, s⁆ ∈ U := Iff.rfl

theorem le_normalizer_relCen {Q U N : Subgroup 𝔾} (hQU : U ≤ Subgroup.centralizer (Q : Set 𝔾))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set 𝔾)) (hNU : N ≤ Subgroup.normalizer (U : Set 𝔾)) :
    N ≤ Subgroup.normalizer (relCen Q U hQU : Set 𝔾) := by
  have key : ∀ g ∈ N, ∀ k ∈ relCen Q U hQU, g * k * g⁻¹ ∈ relCen Q U hQU := by
    rintro g hg k ⟨hk, h⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hNQ hg) k).mp hk, fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hNQ (inv_mem hg)) s).mp hs
    have e : ⁅g * k * g⁻¹, s⁆ = g * ⁅k, g⁻¹ * s * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNU hg) _).mp (h _ hs')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using this

end Group

section Lin

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem eq_zero_of_dot_eq_zero_of_not_mem [Finite F] {H : Submodule F (Fin 3 → F)}
    (hH : Module.finrank F H = 2) {w : Fin 3 → F} (hw : w ∉ H) {y : Fin 3 → F}
    (hy : ∀ x ∈ H, y ⬝ᵥ x = 0) (hyw : y ⬝ᵥ w = 0) : y = 0 := by
  have htop : H ⊔ Submodule.span F {w} = ⊤ := by
    have hlt : H < H ⊔ Submodule.span F {w} := by
      refine lt_of_le_of_ne le_sup_left fun heq => hw ?_
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    have h3 : Module.finrank F ↥(H ⊔ Submodule.span F {w}) = 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      have hle := Submodule.finrank_le (H ⊔ Submodule.span F {w})
      simp only [Module.finrank_fin_fun] at hle
      omega
    exact Submodule.eq_top_of_finrank_eq (by rw [h3]; simp)
  have hall : ∀ x : Fin 3 → F, y ⬝ᵥ x = 0 := by
    intro x
    have hx : x ∈ H ⊔ Submodule.span F {w} := htop ▸ Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [dotProduct_add, hy u hu, dotProduct_smul, hyw, smul_zero, add_zero]
  funext i
  have := hall (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem mem_of_commutator_mem_of_not_le [Finite F] {K X Z A B : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hd : IsSumOfNaturalModulesVia K X Z ψ true 1)
    (hA2 : Module.finrank F ↥(commN (natImage ψ A)) = 2)
    (hBA : ¬ commN (natImage ψ B) ≤ commN (natImage ψ A)) {x : 𝔾} (hx : x ∈ X)
    (hxA : ∀ a : ↥K, (a : 𝔾) ∈ A → ⁅x, (a : 𝔾)⁆ ∈ Z)
    (hxB : ∀ b : ↥K, (b : 𝔾) ∈ B → ⁅x, (b : 𝔾)⁆ ∈ Z) : x ∈ Z := by
  rw [← (NatSec.ofIsSum hd).coord_eq_zero_iff hx]
  obtain ⟨w, hwB, hwA⟩ := IsConcreteLE.not_le_iff_exists.mp hBA
  exact eq_zero_of_dot_eq_zero_of_not_mem hA2 hwA
    (coord_dot_eq_zero_of_commutator_mem hd hx hxA)
    (coord_dot_eq_zero_of_commutator_mem hd hx hxB w hwB)

end Lin

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem zm_le_vhat_iff_of_smul {α γ₁ γ₂ : Vtx (puAmalgam c.hyp.le)}
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab (puAmalgam c.hyp.le) α)
    (hgγ : g • γ₁ = γ₂) :
    ZM (puAmalgam c.hyp.le) α ≤ Vcirc c.hyp.le L γ₁ ⊔ ZM _ γ₁ ↔
      ZM (puAmalgam c.hyp.le) α ≤ Vcirc c.hyp.le L γ₂ ⊔ ZM _ γ₂ := by
  have hgα : g • α = α := (mem_stab _).mp hg
  have hZ : (ZM (puAmalgam c.hyp.le) α).map (MulAut.conj g).toMonoidHom = ZM _ α := by
    rw [← zm_smul, hgα]
  have hW : (Vcirc c.hyp.le L γ₁ ⊔ ZM (puAmalgam c.hyp.le) γ₁).map (MulAut.conj g).toMonoidHom =
      Vcirc c.hyp.le L γ₂ ⊔ ZM _ γ₂ := by
    rw [Subgroup.map_sup, ← vcirc_smul c.hyp, ← zm_smul, hgγ]
  rw [← Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective, hZ, hW]

theorem zm_inf_vhat_le (hq : Fintype.card F = 2) {α β γ : Vtx (puAmalgam c.hyp.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β)
    (hγβ : (puAmalgam c.hyp.le).treeGraph.Adj γ β)
    (hne : ¬ ZM (puAmalgam c.hyp.le) α ≤ Vcirc c.hyp.le L γ ⊔ ZM _ γ) :
    ZM (puAmalgam c.hyp.le) α ⊓ (Vcirc c.hyp.le L γ ⊔ ZM _ γ) ≤ ZM _ γ := by
  rintro y ⟨hyα, hyV⟩
  by_contra hyγ
  apply hne
  have hβγ : ZH (puAmalgam c.hyp.le) β ≤ ZM _ γ := zh_le_zm _ hγβ
  have hyβ : y ∉ ZH (puAmalgam c.hyp.le) β := fun h => hyγ (hβγ h)
  have hidx : ((ZH (puAmalgam c.hyp.le) β).subgroupOf (ZM _ α)).index = 2 := by
    have := c.relIndex_zh hα hαβ
    rw [hq] at this
    exact this
  intro z hz
  by_cases hzβ : z ∈ ZH (puAmalgam c.hyp.le) β
  · exact Subgroup.mem_sup_right (hβγ hzβ)
  · have hmem : (⟨z, hz⟩ : ↥(ZM (puAmalgam c.hyp.le) α)) * ⟨y, hyα⟩ ∈
        (ZH (puAmalgam c.hyp.le) β).subgroupOf (ZM _ α) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp only [Subgroup.mem_subgroupOf]
      exact iff_of_false hzβ hyβ
    rw [Subgroup.mem_subgroupOf] at hmem
    have e : z = (z * y) * y⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (hβγ hmem)) (inv_mem hyV)

theorem mem_usup_geo_of_commute {δ δ' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) δ δ') {u : (puAmalgam c.hyp.le).Universal}
    (hu : u ∈ Uloc c.hyp.le L δ) (hcomm : ∀ z ∈ ZM (puAmalgam c.hyp.le) δ', u * z = z * u) :
    u ∈ Usup (puAmalgam c.hyp.le) δ (geo _ δ δ' 1) := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hc.1
  have hc' := c.isCritical_symm hc
  have hus : u ∈ stab (puAmalgam h.le) δ' :=
    zm_le_stab_of_isCritical _ h.hyp20 c.bpos hc' (uloc_le_zm h c.full hc.1 hu)
  have huC : u ∈ Subgroup.centralizer (Uloc h.le L δ' : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hcomm w (uloc_le_zm h c.full hc'.1 hw)).symm
  have huQ : u ∈ Qv (puAmalgam h.le) δ' := by
    rw [← S4A.stab_inf_centralizer_uloc h c.via hc'.1]
    exact ⟨hus, huC⟩
  rw [← c.uloc_inf_qv hc hψ]
  exact ⟨hu, huQ⟩

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem zm_le_vhat_iff_of_isGoodPath (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x)
    (hxN : x + 10 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) ↔
      ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 10)) ⊔ ZM _ (p (x + 10)) := by
  obtain ⟨g, hg, hgx⟩ := c.straight_of_isGoodPath hp (y := x + 6) (hx.add (by decide)) (by omega)
  rw [show x + 6 + 2 = x + 8 by omega] at hg
  rw [show x + 6 + 4 = x + 10 by omega] at hgx
  exact (zm_le_vhat_iff_of_smul c hg hgx).symm

theorem exists_decomp (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 18 ≤ N) {z : (puAmalgam c.hyp.le).Universal}
    (hz : z ∈ ZM (puAmalgam c.hyp.le) (p (x + 8))) :
    ∃ w ∈ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)), ∃ d ∈ Bloc c.hyp.le L (p (x + 6)),
      ∃ z₁ ∈ ZM (puAmalgam c.hyp.le) (p (x + 6)), z = w * (d * z₁) ∧
        d ∈ Subgroup.centralizer (Ltil c.hyp.le L (p (x + 6)) : Set _) ∧
        ∀ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), ⁅d, g⁆ ∈ Hloc c.hyp.le L (p (x + 6)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  have hγ := c.isMVtx_of_isGoodPath hp (k := x + 6) (by omega) (hx.add (by decide))
  have hα := c.isMVtx_of_isGoodPath hp (k := x + 8) (by omega) (hx.add (by decide))
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have hQγT : Qv (puAmalgam h.le) (p (x + 6)) ≤ Qv _ (p (x + 7)) := qv_le_qv _ h20 hγ hγβ
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) (p (x + 6))
  have hHn := c.stab_le_normalizer_hloc (p (x + 6))
  have hVs : Vv (puAmalgam h.le) (p (x + 6)) ≤ stab _ (p (x + 6)) :=
    (c.vv_le_qv' hγ).trans (qv_le_stab _ _)
  have hZs : ZM (puAmalgam h.le) (p (x + 6)) ≤ stab _ (p (x + 6)) :=
    (zm_le_qv_self _ hγ h.critDist_pos).trans (qv_le_stab _ _)
  set Vh := Vcirc h.le L (p (x + 6)) ⊔ ZM (puAmalgam h.le) (p (x + 6)) with hVh
  have hVhs : Vh ≤ stab (puAmalgam h.le) (p (x + 6)) := sup_le ((c.vcirc_le_vv _).trans hVs) hZs
  have hHU := c.hloc_eq_usup' hp hx h4 (by omega)
  have hZαT : ∀ z ∈ ZM (puAmalgam h.le) (p (x + 8)), ∀ t ∈ Qv (puAmalgam h.le) (p (x + 7)),
      ⁅z, t⁆ ∈ Hloc h.le L (p (x + 6)) := fun z hz t ht => by
    rw [hHU, Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator hz ht
  have hVhQ : ⁅Vh, Qv (puAmalgam h.le) (p (x + 6))⁆ ≤ Hloc h.le L (p (x + 6)) :=
    S45.commutator_sup_left_le (((c.vcirc_le_vv _).trans hVs).trans hHn) (hZs.trans hHn) le_rfl
      (by rw [commutator_zm_qv _ h20 hγ]; exact bot_le)
  have hzV : z ∈ Vv (puAmalgam h.le) (p (x + 6)) :=
    c.zm_le_vv_of_le hα (by
      rw [hp.dist_eq' (i := x + 6) (j := x + 8) (by omega) (by omega)]; omega) hz
  have hBn : Vh ≤ Subgroup.normalizer (Bloc h.le L (p (x + 6)) : Set _) :=
    hVhs.trans (c.stab_le_normalizer_bloc _)
  rw [← c.vhat_sup_bloc hγ, S45R.mem_sup_iff_mul_of_le_normalizer hBn] at hzV
  obtain ⟨w, hw, b, hb, rfl⟩ := hzV
  have hbs : b ∈ stab (puAmalgam h.le) (p (x + 6)) := hVs (bloc_le_vv h _ hb)
  have hDQ : Dloc h.le L (p (x + 6)) ≤ Qv (puAmalgam h.le) (p (x + 6)) :=
    (h.puTrans_Dq hγ).le.trans inf_le_left
  have hbZD := S45R.Ctx.bloc_le_zm_sup_dloc c hp hx h4 hxN hb
  rw [sup_comm, S45R.mem_sup_iff_mul_of_le_normalizer (hDQ.trans ((qv_le_stab _ _).trans hZn))]
    at hbZD
  obtain ⟨d, hd, z₁, hz₁, rfl⟩ := hbZD
  have hdL := ((h.puTrans_Dq hγ).le hd).2
  have hdB : d ∈ Bloc h.le L (p (x + 6)) := by
    have := Subgroup.mul_mem _ hb (Subgroup.inv_mem _ (zm_le_bloc h hb2 hγ hz₁))
    rwa [mul_inv_cancel_right] at this
  have hdq : ∀ q ∈ Qv (puAmalgam h.le) (p (x + 6)), ⁅d, q⁆ ∈ Hloc h.le L (p (x + 6)) := by
    intro q hq
    have hz₁q : ⁅z₁⁻¹, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ h20 hγ (inv_mem hz₁)) q hq).symm
    have hs : w⁻¹ * (w * (d * z₁)) ∈ stab (puAmalgam h.le) (p (x + 6)) := by
      rw [inv_mul_cancel_left]; exact hbs
    rw [show d = w⁻¹ * (w * (d * z₁)) * z₁⁻¹ by group]
    refine S45R.commutator_mul_left_mem (hHn hs) (S45R.commutator_mul_left_mem
      (hHn (inv_mem (hVhs hw))) (hVhQ (Subgroup.commutator_mem_commutator (inv_mem hw) hq))
      (hZαT _ hz q (hQγT hq))) ?_
    rw [hz₁q]
    exact one_mem _
  refine ⟨w, hw, d, hdB, z₁, hz₁, rfl, hdL, fun g hg => ?_⟩
  rw [stab_eq_ltil_sup_qv h c.full hγ, S45R.mem_sup_iff_mul_of_le_normalizer
    ((ltil_le_stab h _).trans (stab_le_normalizer_qv _ _))] at hg
  obtain ⟨l, hl, q, hq, rfl⟩ := hg
  have hld : l * d = d * l := Subgroup.mem_centralizer_iff.mp hdL l hl
  have e : ⁅d, l * q⁆ = l * ⁅d, q⁆ * l⁻¹ := by
    calc ⁅d, l * q⁆ = (d * l) * q * d⁻¹ * q⁻¹ * l⁻¹ := by rw [commutatorElement_def]; group
      _ = (l * d) * q * d⁻¹ * q⁻¹ * l⁻¹ := by rw [hld]
      _ = l * ⁅d, q⁆ * l⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hHn (ltil_le_stab h _ hl)) _).mp (hdq q hq)

end Ctx

end CFSG.Quasithin.MS93.S45J
