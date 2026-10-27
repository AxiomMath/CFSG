module

public import CFSG.Quasithin.EmptyFaithful.S153E57A

public section

namespace CFSG.Quasithin

namespace S153E57

open scoped commutatorElement

variable {Q : Type*} [CommGroup Q]

@[expose] noncomputable def phi (v : MulAut Q) : Q →* Q := (v : Q →* Q) * (MonoidHom.id Q)⁻¹

theorem phi_apply (v : MulAut Q) (q : Q) : phi v q = v q * q⁻¹ := by
  simp [phi]

theorem phi_eq_one_iff {v : MulAut Q} {q : Q} : phi v q = 1 ↔ v q = q := by
  rw [phi_apply, mul_inv_eq_one]

theorem commIn153_eq_map {V : Subgroup (MulAut Q)} {v : MulAut Q} (hv : v ∈ V)
    (hV : ∀ w ∈ V, w = 1 ∨ w = v) (B : Subgroup Q) : commIn153 V B = B.map (phi v) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a, ha, w, hw, rfl⟩
    rcases hV a ha with rfl | rfl
    · refine Subgroup.mem_map.2 ⟨1, B.one_mem, ?_⟩
      simp
    · exact Subgroup.mem_map.2 ⟨w, hw, phi_apply _ _⟩
  · rintro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.subset_closure ⟨v, hv, w, hw, (phi_apply v w).symm⟩

theorem map_phi_le {v : MulAut Q} {B : Subgroup Q} (hB : ∀ x ∈ B, v x ∈ B) :
    B.map (phi v) ≤ B := by
  rintro y hy
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
  rw [phi_apply]
  exact B.mul_mem (hB w hw) (B.inv_mem hw)

theorem card_map_phi_sup {v : MulAut Q} {B₁ B₂ : Subgroup Q} (h₁ : ∀ x ∈ B₁, v x ∈ B₁)
    (h₂ : ∀ x ∈ B₂, v x ∈ B₂) (hdis : B₁ ⊓ B₂ = ⊥) :
    Nat.card ↥((B₁ ⊔ B₂).map (phi v)) =
      Nat.card ↥(B₁.map (phi v)) * Nat.card ↥(B₂.map (phi v)) := by
  rw [Subgroup.map_sup]
  apply card_sup_of_inf_eq_bot
  rw [eq_bot_iff, ← hdis]
  exact inf_le_inf (map_phi_le h₁) (map_phi_le h₂)

theorem card_map_phi_of_inj {v : MulAut Q} {J : Subgroup Q} (h : ∀ x ∈ J, phi v x = 1 → x = 1) :
    Nat.card ↥(J.map (phi v)) = Nat.card J := by
  have hinj : Function.Injective ((phi v).comp J.subtype) := by
    intro a b hab
    have h1 : phi v (a : Q) = phi v b := hab
    have h2 : phi v ((a : Q) * (b : Q)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := h _ (J.mul_mem a.2 (J.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hrange : J.map (phi v) = ((phi v).comp J.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact Nat.card_range_of_injective hinj

theorem map_le_fixSub_iff {d v : MulAut Q} (hd : d * v = v * d) {J : Subgroup Q} :
    J.map (d : Q →* Q) ≤ fixSub v ↔ J ≤ fixSub v := by
  constructor
  · intro h x hx
    have h1 : v (d x) = d x := h (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    have h2 : v (d x) = d (v x) := by
      have := congrArg (fun f : MulAut Q => f x) hd
      exact this.symm
    rw [h2] at h1
    exact d.injective h1
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 : v x = x := h hx
    have h2 : v (d x) = d (v x) := by
      have := congrArg (fun f : MulAut Q => f x) hd
      exact this.symm
    change v (d x) = d x
    rw [h2, h1]

structure Core (H K V P₁ P₂ : Subgroup (MulAut Q)) (v : MulAut Q) (z₀ : Q) : Prop where
  nontriv : Nontrivial Q
  sq : ∀ q : Q, q * q = 1
  irr_H : IsIrrOn153 H ⊤
  normal : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  rank : ∀ W₀ : Subgroup Q, IsIrrOn153 K W₀ → 8 ≤ Nat.card W₀
  v_mem : v ∈ V
  v_ne : v ≠ 1
  V_two : ∀ w ∈ V, w = 1 ∨ w = v
  V_le : V ≤ H
  comm_le : Nat.card ↥(commIn153 V ⊤) ≤ 4
  P₁_two : IsPGroup 2 P₁
  P₂_two : IsPGroup 2 P₂
  P₂_norm : ∀ p ∈ P₂, ∀ a ∈ P₁, p * a * p⁻¹ ∈ P₁
  P₁_le : P₁ ≤ H
  P₂_le : P₂ ≤ H
  P₁_comm : ∀ d ∈ P₁, d * v = v * d
  P₂_comm : ∀ d ∈ P₂, d * v = v * d
  fixed : ∀ x : Q, (∀ d ∈ P₁, d x = x) → (∀ d ∈ P₂, d x = x) → x = 1 ∨ x = z₀

namespace Core

variable {H K V P₁ P₂ : Subgroup (MulAut Q)} {v : MulAut Q} {z₀ : Q}
  (hC : Core H K V P₁ P₂ v z₀)

include hC in
theorem v_mem_H : v ∈ H := hC.V_le hC.v_mem

include hC in
theorem comm_eq_map : commIn153 V ⊤ = (⊤ : Subgroup Q).map (phi v) :=
  commIn153_eq_map hC.v_mem hC.V_two ⊤

section Fin

variable [Finite Q]

include hC

theorem hsum : sSup {J : Subgroup Q | IsIrrOn153 K J} = ⊤ :=
  haveI := hC.nontriv
  sSup_irr_eq_top hC.irr_H hC.normal

theorem v_stable_irr {J : Subgroup Q} (hJ : IsIrrOn153 K J) : ∀ x ∈ J, v x ∈ J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀J, hx₀⟩ := hcon
  have hJ'irr : IsIrrOn153 K (J.map (v : Q →* Q)) := isIrr_map hC.normal hC.v_mem_H hJ
  have hdis : J ⊓ J.map (v : Q →* Q) = ⊥ := by
    rcases hJ.2.2 (J ⊓ J.map (v : Q →* Q)) inf_le_left
      ((irr_inv hJ).inf (irr_inv hJ'irr)) with h | h
    · exact h
    · exfalso
      have hle : J ≤ J.map (v : Q →* Q) := h.symm.le.trans inf_le_right
      have heq : J = J.map (v : Q →* Q) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_eq])
      apply hx₀
      rw [heq]
      exact Subgroup.mem_map.2 ⟨x₀, hx₀J, rfl⟩
  have hinj : ∀ x ∈ J, phi v x = 1 → x = 1 := by
    intro x hx hx1
    have hvx : v x = x := phi_eq_one_iff.1 hx1
    have : x ∈ J ⊓ J.map (v : Q →* Q) := ⟨hx, Subgroup.mem_map.2 ⟨x, hx, hvx⟩⟩
    rw [hdis, Subgroup.mem_bot] at this
    exact this
  have hcard := card_map_phi_of_inj hinj
  have hle : J.map (phi v) ≤ commIn153 V ⊤ := by
    rw [hC.comm_eq_map]
    exact Subgroup.map_mono le_top
  have h4 : Nat.card ↥(J.map (phi v)) ≤ 4 := (Subgroup.card_le_of_le hle).trans hC.comm_le
  have h8 := hC.rank J hJ
  omega

theorem v_stable_inv {B : Subgroup Q} (hB : IsInv K B) : ∀ x ∈ B, v x ∈ B :=
  stable_of_irr hC.hsum (fun _ hJ => hC.v_stable_irr hJ) hB

theorem comm_ne_bot : ⁅K, V⁆ ≠ ⊥ := by
  intro hbot
  have hcent : K ≤ Subgroup.centralizer (V : Set (MulAut Q)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  have hR : IsInv K ((⊤ : Subgroup Q).map (phi v)) := by
    intro k hk y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    have hkv : v * k = k * v := Subgroup.mem_centralizer_iff.1 (hcent hk) v hC.v_mem
    refine Subgroup.mem_map.2 ⟨k x, Subgroup.mem_top _, ?_⟩
    rw [phi_apply, phi_apply, map_mul, map_inv]
    have : k (v x) = v (k x) := by
      have := congrArg (fun f : MulAut Q => f x) hkv
      exact this.symm
    rw [this]
  have hcard : Nat.card ↥((⊤ : Subgroup Q).map (phi v)) ≤ 4 := hC.comm_eq_map ▸ hC.comm_le
  have hne : (⊤ : Subgroup Q).map (phi v) ≠ ⊥ := by
    intro h
    apply hC.v_ne
    ext x
    have hx : phi v x ∈ (⊤ : Subgroup Q).map (phi v) := Subgroup.mem_map.2 ⟨x, Subgroup.mem_top _, rfl⟩
    rw [h, Subgroup.mem_bot] at hx
    exact phi_eq_one_iff.1 hx
  obtain ⟨J, hJR, hJ⟩ := exists_irr_le hR hne
  have h4 : Nat.card J ≤ 4 := (Subgroup.card_le_of_le hJR).trans hcard
  have h8 := hC.rank J hJ
  omega

theorem not_centralized {J₀ : Subgroup Q} (hJ₀ : IsIrrOn153 K J₀) : ¬ J₀ ≤ fixSub v := by
  intro hJ₀c
  let Sc : Set (Subgroup Q) := {J | IsIrrOn153 K J ∧ J ≤ fixSub v}
  let Sn : Set (Subgroup Q) := {J | IsIrrOn153 K J ∧ ¬ J ≤ fixSub v}
  have hcle : sSup Sc ≤ fixSub v := sSup_le fun J hJ => hJ.2
  have hSc_inv : IsInv K (sSup Sc) := isInv_sSup fun J hJ => irr_inv hJ.1
  have hSn_inv : IsInv K (sSup Sn) := isInv_sSup fun J hJ => irr_inv hJ.1
  have hmap : ∀ d ∈ H, d * v = v * d → ∀ J, IsIrrOn153 K J →
      IsIrrOn153 K (J.map (d : Q →* Q)) ∧ (J.map (d : Q →* Q) ≤ fixSub v ↔ J ≤ fixSub v) :=
    fun d hd hdv J hJ => ⟨isIrr_map hC.normal hd hJ, map_le_fixSub_iff hdv⟩
  have hstabc : ∀ d ∈ H, d * v = v * d → ∀ x ∈ sSup Sc, d x ∈ sSup Sc := by
    intro d hd hdv
    refine sSup_stable d fun J hJ x hx => ?_
    have h := hmap d hd hdv J hJ.1
    exact le_sSup (show J.map (d : Q →* Q) ∈ Sc from ⟨h.1, h.2.2 hJ.2⟩)
      (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have hstabn : ∀ d ∈ H, d * v = v * d → ∀ x ∈ sSup Sn, d x ∈ sSup Sn := by
    intro d hd hdv
    refine sSup_stable d fun J hJ x hx => ?_
    have h := hmap d hd hdv J hJ.1
    exact le_sSup (show J.map (d : Q →* Q) ∈ Sn from ⟨h.1, fun hle => hJ.2 (h.2.1 hle)⟩)
      (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have hc_ne : sSup Sc ≠ ⊥ := fun h =>
    hJ₀.1 (le_bot_iff.1 (h ▸ le_sSup (show J₀ ∈ Sc from ⟨hJ₀, hJ₀c⟩)))
  have hn_ne : sSup Sn ≠ ⊥ := by
    intro h
    have hall : ∀ J, IsIrrOn153 K J → J ≤ fixSub v := by
      intro J hJ
      by_contra hJn
      have : J ≤ sSup Sn := le_sSup ⟨hJ, hJn⟩
      rw [h] at this
      exact hJ.1 (le_bot_iff.1 this)
    have : ⊤ ≤ fixSub v := by
      rw [← hC.hsum]
      exact sSup_le fun J hJ => hall J hJ
    apply hC.v_ne
    ext x
    exact this (Subgroup.mem_top x)
  obtain ⟨x, hxc, hx1, hxP₁, hxP₂⟩ := exists_fixed_two hC.P₁_two hC.P₂_two hC.P₂_norm
    (B := sSup Sc) (fun s hs b hb => hstabc s (hC.P₁_le hs) (hC.P₁_comm s hs) b hb)
    (fun s hs b hb => hstabc s (hC.P₂_le hs) (hC.P₂_comm s hs) b hb) hc_ne
    (isPGroup_two_of_mul_self hC.sq _)
  obtain ⟨y, hyn, hy1, hyP₁, hyP₂⟩ := exists_fixed_two hC.P₁_two hC.P₂_two hC.P₂_norm
    (B := sSup Sn) (fun s hs b hb => hstabn s (hC.P₁_le hs) (hC.P₁_comm s hs) b hb)
    (fun s hs b hb => hstabn s (hC.P₂_le hs) (hC.P₂_comm s hs) b hb) hn_ne
    (isPGroup_two_of_mul_self hC.sq _)
  have hxz : x = z₀ := (hC.fixed x hxP₁ hxP₂).resolve_left hx1
  have hyz : y = z₀ := (hC.fixed y hyP₁ hyP₂).resolve_left hy1
  have hmem : x ∈ sSup Sc ⊓ sSup Sn := ⟨hxc, by rw [hxz, ← hyz]; exact hyn⟩
  have hne : sSup Sc ⊓ sSup Sn ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  obtain ⟨J'', hJ''le, hJ''⟩ := exists_irr_le (hSc_inv.inf hSn_inv) hne
  have hJ''fix : J'' ≤ fixSub v := hJ''le.trans (inf_le_left.trans hcle)
  have hJ''n : J'' ≤ sSup Sn := hJ''le.trans inf_le_right
  obtain ⟨C, hCinv, hdis, hsup⟩ := exists_compl hC.hsum (irr_inv hJ'')
  have hCstab : ∀ x ∈ C, v x ∈ C := hC.v_stable_inv hCinv
  have hex : ∃ J, IsIrrOn153 K J ∧ ¬ J ≤ fixSub v ∧ J ⊓ C = ⊥ := by
    by_contra hcon
    push Not at hcon
    have hle : sSup Sn ≤ C := by
      refine sSup_le fun J hJ => ?_
      have h1 := hcon J hJ.1 hJ.2
      rcases hJ.1.2.2 (J ⊓ C) inf_le_left ((irr_inv hJ.1).inf hCinv) with h | h
      · exact absurd h h1
      · exact h.symm.le.trans inf_le_right
    have h2 : J'' ≤ J'' ⊓ C := le_inf le_rfl (hJ''n.trans hle)
    rw [hdis] at h2
    exact hJ''.1 (le_bot_iff.1 h2)
  obtain ⟨J, hJ, hJn, hJC⟩ := hex
  apply hJn
  intro x hx
  have hx' : x ∈ J'' ⊔ C := by
    rw [hsup]
    exact Subgroup.mem_top x
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hx'
  have h1 : v a = a := hJ''fix ha
  have h2 : v (a * c) * (a * c)⁻¹ ∈ C := by
    rw [map_mul, h1, mul_inv_rev]
    have : a * v c * (c⁻¹ * a⁻¹) = (v c * c⁻¹) * (a * a⁻¹) := by ac_rfl
    rw [this, mul_inv_cancel, mul_one]
    exact C.mul_mem (hCstab c hc) (C.inv_mem hc)
  have h3 : v (a * c) * (a * c)⁻¹ ∈ J :=
    J.mul_mem (hC.v_stable_irr hJ _ hx) (J.inv_mem hx)
  have h4 : v (a * c) * (a * c)⁻¹ ∈ J ⊓ C := ⟨h3, h2⟩
  rw [hJC, Subgroup.mem_bot, mul_inv_eq_one] at h4
  exact h4

theorem two_le_card_map {B : Subgroup Q} (hB : IsInv K B) (hne : B ≠ ⊥) :
    2 ≤ Nat.card ↥(B.map (phi v)) := by
  obtain ⟨J, hJB, hJ⟩ := exists_irr_le hB hne
  obtain ⟨x, hxJ, hx⟩ := Set.not_subset.1 (hC.not_centralized hJ)
  have hphi : phi v x ≠ 1 := fun h => hx (phi_eq_one_iff.1 h)
  have hmem : phi v x ∈ B.map (phi v) := Subgroup.mem_map.2 ⟨x, hJB hxJ, rfl⟩
  have hne' : B.map (phi v) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hmem
    exact hphi hmem
  have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne'
  omega

end Fin

end Core

end S153E57

end CFSG.Quasithin
