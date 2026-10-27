module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.PermutationAction

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G W : Subgroup Γ}

namespace Hyp

variable (H : Hyp p A G W)

include H

theorem projIn_eq_of_k1_eq_bot
    (hK1 : k1 G W = ⊥) {J : Subgroup Γ} (hJ : J ∈ lcal (kOf G)) :
    projIn (lcal (kOf G)) J W = J ∧ smear J A ≤ W := by
  rcases H.dichotomy hJ with h | h
  · exact absurd (le_bot_iff.1 (hK1 ▸ H.le_k1_of_mem_tOne ⟨hJ, h⟩)) (ne_bot_of_mem_lcal hJ)
  · exact h

theorem exists_conj_eq_of_cen
    (hK1 : k1 G W = ⊥) {s : Γ} (hs : s ∈ cenIn G W)
    {J : Subgroup Γ} (hJ : J ∈ lcal (kOf G)) :
    ∃ c ∈ A, J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj c).toMonoidHom := by
  have hK := H.hK
  have hSA := H.semisimpleAction
  obtain ⟨hsG, hsW⟩ := Subgroup.mem_inf.1 hs
  have hsN : s ∈ Subgroup.normalizer (kOf G : Set Γ) :=
    mem_normalizer_kOf H.sol_eq (Subgroup.le_normalizer hsG)
  have hperm : ∀ J' ∈ lcal (kOf G), J'.map (MulAut.conj s).toMonoidHom ∈ lcal (kOf G) :=
    fun J' hJ' => map_conj_mem_lcal hJ' hsN
  have hsmear : smear J A ≠ ⊥ := fun h0 => hSA.fittingSubgroupOf_smear_ne_bot hJ
    (le_bot_iff.1 ((Subgroup.map_subtype_le _).trans h0.le))
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hsmear
  have hxW : x ∈ W := (H.projIn_eq_of_k1_eq_bot hK1 hJ).2 hx
  have hxK : x ∈ kOf G := H.le hxW
  have hsx : s * x * s⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hsW x hxW).symm
  have hc1 : hK.coord hJ ⟨x, hxK⟩ ≠ 1 := by
    intro h1
    have h2 : x ∈ sSup (lcal (kOf G) \ {J}) := (hK.coord_eq_one_iff hJ ⟨x, hxK⟩).1 h1
    have h3 : x ∈ smear J A ⊓ sSup (lcal (kOf G) \ {J}) := Subgroup.mem_inf.2 ⟨hx, h2⟩
    rw [hSA.smear_inf_sSup hJ] at h3
    exact hx1 (Subtype.ext (Subgroup.mem_bot.1 h3))
  have key := hK.coord_conj hperm hJ hxK
  have e : (⟨s * x * s⁻¹, hK.conj_mem hperm hxK⟩ : ↥(kOf G)) = ⟨x, hxK⟩ := Subtype.ext hsx
  rw [e] at key
  by_contra hcon
  push Not at hcon
  have hmem : x ∈ sSup (lcal (kOf G) \ {J.map (MulAut.conj s).toMonoidHom}) := by
    have h1 : x ∈ orbitClosure J A := smear_le_orbitClosure J A hx
    rw [← Thm210g.sSup_orbSet] at h1
    have hsub : Thm210g.orbSet A J ⊆ lcal (kOf G) \ {J.map (MulAut.conj s).toMonoidHom} := by
      rintro K ⟨c, hc, rfl⟩
      exact ⟨hSA.permutes_lcal c hc J hJ, fun h => hcon c hc (Set.mem_singleton_iff.1 h).symm⟩
    exact sSup_le_sSup hsub h1
  have h0 := (hK.coord_eq_one_iff (hperm J hJ) ⟨x, hxK⟩).2 hmem
  apply hc1
  rw [h0] at key
  have h2 : s * ((hK.coord hJ ⟨x, hxK⟩ : J) : Γ) * s⁻¹ = 1 := by
    rw [← key]
    rfl
  apply Subtype.ext
  rw [mul_inv_eq_one] at h2
  simpa using h2

theorem cen_le_normalizer
    (hK1 : k1 G W = ⊥) {J : Subgroup Γ} (hJ : J ∈ lcal (kOf G)) :
    cenIn G W ≤ Subgroup.normalizer (J : Set Γ) := by
  have hSA := H.semisimpleAction
  have hAp : IsPGroup p A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A H.near.elemAbelian
  have hcop : Nat.Coprime p (Nat.card (cenIn G (W : Set Γ))) :=
    (signalizerNearPSolvable_iff.1 H.near.nearPSolvable).1.coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hAC : A ≤ Subgroup.normalizer (cenIn G (W : Set Γ) : Set Γ) :=
    admits_cenIn H.near.admits H.admits_A_W
  have hA : ∀ g ∈ A, ∀ J' ∈ Thm210g.orbSet A J,
      J'.map (MulAut.conj g).toMonoidHom ∈ Thm210g.orbSet A J := by
    rintro g hg _ ⟨b, hb, rfl⟩
    exact ⟨g * b, mul_mem hg hb, Thm210.map_conj_map_conj J b g⟩
  have hC : ∀ g ∈ cenIn G (W : Set Γ), ∀ J' ∈ Thm210g.orbSet A J,
      J'.map (MulAut.conj g).toMonoidHom ∈ Thm210g.orbSet A J := by
    rintro g hg _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hgc⟩ := H.exists_conj_eq_of_cen hK1 hg (hSA.permutes_lcal b hb J hJ)
    exact ⟨c * b, mul_mem hc hb, hgc.trans (Thm210.map_conj_map_conj J b c)⟩
  have htrans : ∀ J₁ ∈ Thm210g.orbSet A J, ∀ J₂ ∈ Thm210g.orbSet A J,
      ∃ a ∈ A, J₂ = J₁.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact ⟨c * b⁻¹, mul_mem hc (inv_mem hb), by
      rw [Thm210.map_conj_map_conj, inv_mul_cancel_right]⟩
  exact fun s hs => normalizes_of_isPGroup_transitive_conj H.near.prime hAp hcop hAC
    (fun _ hg => Lemma212.map_conj_mem_of_mem_sup hC hA hg) htrans s hs J
    (Thm210g.self_mem_orbSet A J)

theorem cenIn_eq_bot_of_k1_eq_bot
    (hK1 : k1 G W = ⊥) : cenIn G W = ⊥ := by
  have hK := H.hK
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨hsG, hsW⟩ := Subgroup.mem_inf.1 hs
  have hsN : s ∈ Subgroup.normalizer (kOf G : Set Γ) :=
    mem_normalizer_kOf H.sol_eq (Subgroup.le_normalizer hsG)
  have hperm : ∀ J ∈ lcal (kOf G), J.map (MulAut.conj s).toMonoidHom ∈ lcal (kOf G) :=
    fun J hJ => map_conj_mem_lcal hJ hsN
  have hJc : ∀ J ∈ lcal (kOf G), J ≤ Subgroup.centralizer ({s} : Set Γ) := by
    intro J hJ t ht
    have hsJ : s ∈ Subgroup.normalizer (J : Set Γ) := H.cen_le_normalizer hK1 hJ hs
    have htP : t ∈ projIn (lcal (kOf G)) J W := (H.projIn_eq_of_k1_eq_bot hK1 hJ).1.symm ▸ ht
    obtain ⟨u, huW, hut⟩ := (hK.mem_projIn_iff hJ).1 htP
    have hsu : s * (u : Γ) * s⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.1 hsW u huW).symm
    have h1 := Thm210g.coord_conj_of_normalizer hK hperm hJ hsJ u
    have e : (⟨s * (u : Γ) * s⁻¹, hK.conj_mem hperm u.2⟩ : ↥(kOf G)) = u := Subtype.ext hsu
    rw [e, hut] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * s = (s * t * s⁻¹) * s := by rw [← h1]
      _ = s * t := by group
  have hsK : kOf G ≤ Subgroup.centralizer ({s} : Set Γ) := by
    rw [← hK.sSup_eq]
    exact sSup_le hJc
  have hs1 : s ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) :=
    Subgroup.mem_inf.2 ⟨hsG, Subgroup.mem_centralizer_iff.2 fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.1 (hsK hk)⟩
  rw [centralizer_kOf_eq_bot H.sol_eq] at hs1
  exact hs1

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213
