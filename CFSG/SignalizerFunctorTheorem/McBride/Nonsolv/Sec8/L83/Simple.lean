module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Refine
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.FixedAux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK.Basic

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {G : Type*} [Group G]

theorem le_of_isSimpleGroup_of_commutator_ne_one {R M X : Subgroup G} (hR : IsSimpleGroup R)
    (hRM : R ≤ Subgroup.normalizer (M : Set G)) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hXM : X ≤ M) (h : ∃ x ∈ X, ∃ r ∈ R, ⁅x, r⁆ ≠ 1) : R ≤ M := by
  have hN : ((R ⊓ M).subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_trans (le_inf Subgroup.le_normalizer hRM) Subgroup.inf_normalizer_le_normalizer_inf
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ M).subgroupOf R) with hbot | htop
  · exfalso
    obtain ⟨x, hx, r, hr, hne⟩ := h
    have hmem : ⁅x, r⁆ ∈ M ⊓ R :=
      commutatorElement_mem_inf (hXM hx) hr (hRM hr) (hXR hx)
    have hmemR : (⟨⁅x, r⁆, (Subgroup.mem_inf.mp hmem).2⟩ : R) ∈ (R ⊓ M).subgroupOf R :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hmem).2, (Subgroup.mem_inf.mp hmem).1⟩
    rw [hbot, Subgroup.mem_bot] at hmemR
    exact hne (congrArg Subtype.val hmemR)
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

theorem inf_centralizer_self_eq_bot {R : Subgroup G} (hs : IsSimpleGroup R)
    (hnc : ¬ IsMulCommutative R) : R ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxR⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc g g.2)
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  · exact absurd (isMulCommutative_iff.mpr fun a b => by
      have hb : b ∈ Subgroup.center R := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a) hnc

section Diagonal

variable [Finite G] {Ω : Set (Subgroup G)} {H F Q : Subgroup G}

theorem smear_inf_sSup_diff_eq_bot (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) (hQ : Q ∈ Ω) :
    smear Q F ⊓ sSup (Ω \ {Q}) = ⊥ := by
  have hsub : RegFam.conjOrbit Q F ⊆ Ω := RegFam.conjOrbit_subset hQ hF
  have hS := CentralizerK.isDirectProduct_of_subset hΩ hsub
  have hQS : Q ∈ RegFam.conjOrbit Q F := RegFam.self_mem_conjOrbit Q F
  have hA : ∀ a ∈ F, ∀ J ∈ RegFam.conjOrbit Q F,
      J.map (MulAut.conj a).toMonoidHom ∈ RegFam.conjOrbit Q F := by
    rintro a ha _ ⟨f, hf, rfl⟩
    exact ⟨a * f, mul_mem ha hf, Near.Thm210.map_conj_map_conj Q f a⟩
  have htrans : ∀ K ∈ RegFam.conjOrbit Q F, ∃ a ∈ F, K = Q.map (MulAut.conj a).toMonoidHom :=
    fun K hK => hK
  have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hS hA hQS htrans
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxs, hxΩ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxo, hxF⟩ := Subgroup.mem_inf.mp hxs
  rw [RegFam.orbitClosure_eq_sSup_conjOrbit] at hxo
  have hsup : x ∈ Q ⊔ sSup (RegFam.conjOrbit Q F \ {Q}) := (hS.isDirectPair hQS).sup_eq ▸ hxo
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (hS.commute_sSup_diff hQS)).mp hsup
  have hbΩ : b ∈ sSup (Ω \ {Q}) :=
    sSup_le_sSup (show RegFam.conjOrbit Q F \ {Q} ⊆ Ω \ {Q} from
      fun K hK => ⟨hsub hK.1, hK.2⟩) hb
  have haΩ : a ∈ sSup (Ω \ {Q}) := by
    have : a = a * b * b⁻¹ := by group
    rw [this]
    exact mul_mem hxΩ (inv_mem hbΩ)
  have ha1 : a = 1 := by
    have h1 : a ∈ Q ⊓ sSup (Ω \ {Q}) := Subgroup.mem_inf.mpr ⟨ha, haΩ⟩
    rw [disjoint_iff.mp (hΩ.indep hQ), Subgroup.mem_bot] at h1
    exact h1
  subst ha1
  rw [one_mul] at hxF hxo ⊢
  have hmem : b ∈ sSup (RegFam.conjOrbit Q F) ⊓ Subgroup.centralizer (F : Set G) ⊓
      sSup (RegFam.conjOrbit Q F \ {Q}) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxo, hxF⟩, hb⟩
  rw [hbot] at hmem
  exact hmem

omit [Finite G] in
theorem smear_eq_of_mem_conjOrbit {Q₀ Q : Subgroup G} (hQ : Q ∈ RegFam.conjOrbit Q₀ F) :
    smear Q F = smear Q₀ F := by
  obtain ⟨f, hf, rfl⟩ := hQ
  exact CentralizerK.smear_map_conj_of_mem hf

theorem smear_inf_centralizer_eq_bot (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) {Q₀ R : Subgroup G}
    (hQ₀ : Q₀ ∈ Ω) (hQ : Q ∈ Ω) (hRQ : R ≤ Q) (hQR : Q ⊓ Subgroup.centralizer (R : Set G) = ⊥)
    (hL : ¬ smear Q₀ F ≤ Subgroup.centralizer (R : Set G)) :
    smear Q₀ F ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
  have hmem : Q ∈ RegFam.conjOrbit Q₀ F := by
    by_contra hno
    refine hL fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (RegFam.commute_orbitClosure hΩ hF hQ₀ hQ hno x (smear_le_orbitClosure Q₀ F hx) y
      (le_orbitClosure Q F (hRQ hy))).eq.symm
  have hsm := smear_eq_of_mem_conjOrbit (F := F) hmem
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ H := hΩ.sSup_eq ▸ (show x ∈ sSup Ω from
    (orbitClosure_le fun f hf => le_sSup (hF f hf Q₀ hQ₀)) (smear_le_orbitClosure Q₀ F hxL))
  have hsup : x ∈ Q ⊔ sSup (Ω \ {Q}) := (hΩ.isDirectPair hQ).sup_eq ▸ hxH
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute (hΩ.commute_sSup_diff hQ)).mp hsup
  have hbR : ∀ r ∈ R, r * b = b * r := fun r hr =>
    (hΩ.commute_sSup_diff hQ r (hRQ hr) b hb).eq
  have haC : a ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply mul_right_cancel (b := b)
    calc r * a * b = r * (a * b) := mul_assoc _ _ _
      _ = a * b * r := Subgroup.mem_centralizer_iff.mp hxC r hr
      _ = a * (b * r) := mul_assoc _ _ _
      _ = a * (r * b) := by rw [hbR r hr]
      _ = a * r * b := (mul_assoc _ _ _).symm
  have ha1 : a = 1 := by
    have h1 : a ∈ Q ⊓ Subgroup.centralizer (R : Set G) := Subgroup.mem_inf.mpr ⟨ha, haC⟩
    rw [hQR, Subgroup.mem_bot] at h1
    exact h1
  subst ha1
  rw [one_mul] at hxL ⊢
  have h1 : b ∈ smear Q F ⊓ sSup (Ω \ {Q}) := Subgroup.mem_inf.mpr ⟨hsm ▸ hxL, hb⟩
  rw [smear_inf_sSup_diff_eq_bot hΩ hF hQ] at h1
  exact h1

end Diagonal

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
