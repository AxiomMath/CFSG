module

public import CFSG.Quasithin.MS93.S4ACrit

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Pair

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
include h hfull hC

theorem card_natImage_zm {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {ψ' : ↥(stab (puAmalgam h.le) α') →* ↥(StatedSL 3 F)}
    (hψ' : IsSumOfNaturalModulesVia (stab _ α') (Uloc h.le L α') ⊥ ψ' false 1) :
    Nat.card ↥(natImage ψ' (ZM _ α)) = (Qv _ α').relIndex (ZM _ α) := by
  have hb := h.critDist_pos
  have hα' : IsMVtx _ α' := (ms22_iii _ h.hyp20 hb hC hc).1
  have hZs := zm_le_stab_right _ h.hyp20 hb hC hc
  have h1 := card_natImage_mul hψ' hZs
  have hinf : ZM (puAmalgam h.le) α ⊓ Subgroup.centralizer (Uloc h.le L α' : Set _) =
      Qv _ α' ⊓ ZM _ α := by
    rw [inf_comm (Qv _ α'), ← zm_inf_centralizer_eq_inf_qv _ h.hyp20 hb hC hc]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, (mem_centralizer_zm_iff h hfull hα' (hZs hx)).mpr hxc⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, (mem_centralizer_zm_iff h hfull hα' (hZs hx)).mp hxc⟩
  rw [hinf] at h1
  have h2 := relIndex_mul_card_inf (Qv (puAmalgam h.le) α') (ZM _ α)
  have hβ := adj_geo_one_of_isCritical _ hb hc
  have hfin : Finite ↥(Qv (puAmalgam h.le) (geo _ α α' 1)) :=
    finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hc.1)
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ (geo _ α α' 1) :=
    qv_le_qv _ h.hyp20 hc.1 hβ |>.trans' (zm_le_qv_self _ hc.1 hb)
  have : Finite ↥(Qv (puAmalgam h.le) α' ⊓ ZM _ α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hZQ))
  have hpos : 0 < Nat.card ↥(Qv (puAmalgam h.le) α' ⊓ ZM _ α) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem relIndex_mul_card_fixN [Finite F] {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) :
    (Qv _ α').relIndex (ZM _ α) * Nat.card ↥(fixN (natImage ψ (ZM _ α'))) = Nat.card F ^ 3 := by
  have hb := h.critDist_pos
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb hc
  rw [← card_inf_centralizer_eq hψ hZs, relIndex_zm_eq_uloc h hfull hc,
    ← card_eq_of_natural hψ]
  have hinf : Uloc h.le L α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) =
      Qv _ α' ⊓ Uloc h.le L α := by
    have key := zm_inf_centralizer_eq_inf_qv _ h.hyp20 hb hC hc
    ext x
    constructor
    · rintro ⟨hxU, hxc⟩
      have : x ∈ ZM (puAmalgam h.le) α ⊓ Qv _ α' :=
        key ▸ ⟨uloc_le_zm h hfull hc.1 hxU, hxc⟩
      exact ⟨this.2, hxU⟩
    · rintro ⟨hxQ, hxU⟩
      have : x ∈ ZM (puAmalgam h.le) α ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) :=
        key.symm ▸ ⟨uloc_le_zm h hfull hc.1 hxU, hxQ⟩
      exact ⟨hxU, this.2⟩
  rw [hinf]
  exact relIndex_mul_card_inf _ _

omit hC in
theorem card_commN_eq_card_critR {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) :
    Nat.card ↥(commN (natImage ψ (ZM _ α'))) = Nat.card ↥(critR (puAmalgam h.le) α α') := by
  have hb := h.critDist_pos
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb hc
  rw [← card_commutator_eq hψ hZs, critR, commutator_zm_eq_uloc h hfull hc.1 hZs]

omit hfull hC in
theorem natImage_zm_sq {α' : Vtx (puAmalgam h.le)} (hα' : IsMVtx _ α')
    {K : Subgroup (puAmalgam h.le).Universal} {ψ : ↥K →* ↥(StatedSL 3 F)} :
    ∀ g ∈ natImage ψ (ZM (puAmalgam h.le) α'), g * g = 1 := by
  intro g hg
  obtain ⟨a, haZ, rfl⟩ := mem_natImage.mp hg
  have ha2 := (isElemAbelian_zm _ h.hyp20 h.critDist_pos hα').2 _ haZ
  have : a * a = 1 := Subtype.ext (by simpa [sq] using ha2)
  rw [← map_mul, this, map_one]

omit hfull hC in
theorem natImage_zm_comm {α' : Vtx (puAmalgam h.le)} (hα' : IsMVtx _ α')
    {K : Subgroup (puAmalgam h.le).Universal} {ψ : ↥K →* ↥(StatedSL 3 F)} :
    ∀ g ∈ natImage ψ (ZM (puAmalgam h.le) α'), ∀ g' ∈ natImage ψ (ZM (puAmalgam h.le) α'),
      g * g' = g' * g := by
  intro g hg g' hg'
  obtain ⟨a, haZ, rfl⟩ := mem_natImage.mp hg
  obtain ⟨a', haZ', rfl⟩ := mem_natImage.mp hg'
  have hc := (isElemAbelian_zm _ h.hyp20 h.critDist_pos hα').1
  have : a * a' = a' * a := by
    apply Subtype.ext
    have := hc.is_comm.comm ⟨_, haZ⟩ ⟨_, haZ'⟩
    simpa using congrArg Subtype.val this
  rw [← map_mul, this, map_mul]

end Pair

end CFSG.Quasithin.MS93
