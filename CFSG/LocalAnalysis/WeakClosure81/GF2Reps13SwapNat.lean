module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSecB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_le_stabSub_of_stable {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hxu => by
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hxu
    rwa [show x⁻¹ (x u) = u by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h1,
    h x hx u⟩

private theorem w16f_mem_stabSub_of_maps {t : MulAut W} (ht2 : orderOf t = 2) {U : Subgroup W}
    (h : ∀ u ∈ U, t u ∈ U) : t ∈ stabSub U := by
  have ht : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  rw [mem_stabSub]
  intro u
  exact ⟨fun htu => by
    have h1 := h (t u) htu
    rwa [← MulAut.mul_apply, ht, MulAut.one_apply] at h1, h u⟩

private theorem w16f_map_conj_one {G : Type*} [Group G] (H : Subgroup (MulAut G)) :
    H.map (MulAut.conj (1 : MulAut G)).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hy
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

private theorem w16f_commute_of_commutator_eq_bot {G : Type*} [Group G] {X : Subgroup G}
    (h : ⁅X, X⁆ = ⊥) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro a ha b hb
  have h1 : ⁅a, b⁆ = 1 := by
    have h2 : ⁅a, b⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [h, Subgroup.mem_bot] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem w16f_not_abelian_of_isQuasisimple {G : Type*} [Group G] {X : Subgroup G}
    (hX : IsQuasisimple ↥X) : ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro h
  have hc : Subgroup.center ↥X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h _ y.2 _ x.2)
  obtain ⟨a, b, hab⟩ := hX.2.1.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [QuotientGroup.eq, hc]
      trivial

private theorem w16f_open_isQuasisimple {G : Type*} [Group G] (h : IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨(Group.isPerfect_def).mp h.1, h.2.1⟩

private theorem w16f_isMatTensor2_congr_right {G : Type} [CommGroup G]
    {L L₁ L₂ : Subgroup (MulAut G)} {K : Type} [Field K] (h : L₁ = L₂)
    (hT : IsMatTensor2 L L₁ K) : IsMatTensor2 L L₂ K := by
  subst h
  exact hT

private theorem w16f_sec_hntK {K : Subgroup (MulAut W)} {t : MulAut W} {U₀ U : Subgroup W}
    (hKs : K ≤ secStabAll U U₀) (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hts : t ∈ secStabAll U U₀)
    (hnt : ¬ commSub U (K ⊔ K.map (MulAut.conj t).toMonoidHom) ≤ U₀) :
    ¬ commSub U K ≤ U₀ := by
  intro h
  have hX : K ⊔ K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀ := sup_le hKs hK's
  have hbot : secImg (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀ = ⊥ := by
    rw [secImg_sup hKs hK's]
    have hKbot : secImg K U U₀ = ⊥ := (secImg_eq_bot_iff hKs).mpr h
    have hK'bot : secImg (K.map (MulAut.conj t).toMonoidHom) U U₀ = ⊥ := by
      rw [secImg_map_conj hKs hts, hKbot]
      simp
    rw [hKbot, hK'bot]
    simp
  exact hnt ((secImg_eq_bot_iff hX).mp hbot)

private theorem w16f_sec_stab {K : Subgroup (MulAut W)} {t : MulAut W} {U₀ U : Subgroup W}
    (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀)
    (htU : ∀ u ∈ U, t u ∈ U) (htU₀ : ∀ u ∈ U₀, t u ∈ U₀) (ht2 : orderOf t = 2) :
    K ≤ secStabAll U U₀ ∧ K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀ ∧
      t ∈ secStabAll U U₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact ⟨(w16f_le_stabSub_of_stable hirr.2.1) (Subgroup.mem_sup_left hg),
      (w16f_le_stabSub_of_stable hirr.2.2.1) (Subgroup.mem_sup_left hg)⟩
  · intro g hg
    exact ⟨(w16f_le_stabSub_of_stable hirr.2.1) (Subgroup.mem_sup_right hg),
      (w16f_le_stabSub_of_stable hirr.2.2.1) (Subgroup.mem_sup_right hg)⟩
  · exact ⟨w16f_mem_stabSub_of_maps ht2 htU, w16f_mem_stabSub_of_maps ht2 htU₀⟩

private theorem w16f_sec_false_of_eq {K : Subgroup (MulAut W)} {t : MulAut W}
    {U₀ U : Subgroup W} (hKs : K ≤ secStabAll U U₀)
    (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hKq : IsQuasisimple ↥(secImg K U U₀))
    (hK'eq : secImg (K.map (MulAut.conj t).toMonoidHom) U U₀ = secImg K U U₀) : False := by
  have hcommK' : ⁅secImg K U U₀,
      secImg (K.map (MulAut.conj t).toMonoidHom) U U₀⁆ = ⊥ := by
    rw [secImg_commutator hKs hK's, hcomm]
    simp [secImg]
  have hcommKK : ⁅secImg K U U₀, secImg K U U₀⁆ = ⊥ := by
    rw [hK'eq] at hcommK'
    exact hcommK'
  exact w16f_not_abelian_of_isQuasisimple (X := secImg K U U₀) hKq
    (w16f_commute_of_commutator_eq_bot hcommKK)

private theorem w16f_sec_t_nontrivial {K : Subgroup (MulAut W)} {t : MulAut W}
    {U₀ U : Subgroup W} (hKs : K ≤ secStabAll U U₀)
    (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hts : t ∈ secStabAll U U₀)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hKq : IsQuasisimple ↥(secImg K U U₀)) :
    ¬ commSub U (Subgroup.zpowers t) ≤ U₀ := by
  intro htI
  have hts' : Subgroup.zpowers t ≤ secStabAll U U₀ := Subgroup.zpowers_le.mpr hts
  have hzbot : secImg (Subgroup.zpowers t) U U₀ = ⊥ :=
    (secImg_eq_bot_iff hts').mpr htI
  have hτ1 : secAut U U₀ ⟨t, hts⟩ = 1 := by
    have hmem : secAut U U₀ ⟨t, hts⟩ ∈ secImg (Subgroup.zpowers t) U U₀ :=
      mem_secImg.mpr ⟨⟨t, hts⟩, by simpa using Subgroup.mem_zpowers t, rfl⟩
    rwa [hzbot, Subgroup.mem_bot] at hmem
  have hK'eq : secImg (K.map (MulAut.conj t).toMonoidHom) U U₀ = secImg K U U₀ := by
    rw [secImg_map_conj hKs hts, hτ1, w16f_map_conj_one]
  exact w16f_sec_false_of_eq hKs hK's hcomm hKq hK'eq

private theorem w16f_sec_move {K : Subgroup (MulAut W)} {t : MulAut W}
    {U₀ U : Subgroup W} (hKs : K ≤ secStabAll U U₀)
    (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hts : t ∈ secStabAll U U₀)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hKq : IsQuasisimple ↥(secImg K U U₀)) :
    (secImg K U U₀).map (MulAut.conj (secAut U U₀ ⟨t, hts⟩)).toMonoidHom
      ≠ secImg K U U₀ := by
  intro h
  have hK'eq : secImg (K.map (MulAut.conj t).toMonoidHom) U U₀ = secImg K U U₀ := by
    rw [secImg_map_conj hKs hts, h]
  exact w16f_sec_false_of_eq hKs hK's hcomm hKq hK'eq

private theorem w16f_sec_comm {K : Subgroup (MulAut W)} {t : MulAut W} {U₀ U : Subgroup W}
    (hKs : K ≤ secStabAll U U₀) (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hts : t ∈ secStabAll U U₀)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥) :
    ⁅secImg K U U₀,
      (secImg K U U₀).map (MulAut.conj (secAut U U₀ ⟨t, hts⟩)).toMonoidHom⁆ = ⊥ := by
  rw [← secImg_map_conj hKs hts]
  have h1 : ⁅secImg K U U₀, secImg (K.map (MulAut.conj t).toMonoidHom) U U₀⁆ = ⊥ := by
    rw [secImg_commutator hKs hK's, hcomm]
    simp [secImg]
  exact h1

private theorem w16f_sec_irr {K : Subgroup (MulAut W)} {t : MulAut W} {U₀ U : Subgroup W}
    (hU₀U : U₀ ≤ U) (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀)
    (hKs : K ≤ secStabAll U U₀) (hK's : K.map (MulAut.conj t).toMonoidHom ≤ secStabAll U U₀)
    (hts : t ∈ secStabAll U U₀) :
    IsIrrOn (secImg K U U₀ ⊔ (secImg K U U₀).map
      (MulAut.conj (secAut U U₀ ⟨t, hts⟩)).toMonoidHom) ⊤ ⊥ := by
  rw [← secImg_map_conj hKs hts, ← secImg_sup hKs hK's]
  exact (isIrrOn_secImg_iff hU₀U (sup_le hKs hK's)).mpr hirr

private theorem w16f_sec_exp_two {U₀ U : Subgroup W} (hW : ∀ w : W, w ^ 2 = 1) :
    ∀ f : SecT U U₀, f ^ 2 = 1 := by
  intro f
  induction f using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, show u ^ 2 = 1 from Subtype.ext (by simpa using hW (u : W)),
      QuotientGroup.mk_one]

private theorem w16f_sec_cost_le {t : MulAut W} {U₀ U : Subgroup W}
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) : secCost t U U₀ ≤ 3 := by
  have h2 : rk ↥(commSub U (Subgroup.zpowers t) ⊔ U₀) +
      rk ↥(commSub U (Subgroup.zpowers t) ⊓ U₀) =
      rk ↥(commSub U (Subgroup.zpowers t)) + rk ↥U₀ := rk_sup_add_rk_inf _ _
  have h3 : rk ↥(commSub U (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono (commSub_mono le_top le_rfl)
  unfold secCost
  omega

private theorem w16f_swap_module {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {τ : MulAut V}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hτ2 : orderOf τ = 2)
    (hmove : L.map (MulAut.conj τ).toMonoidHom ≠ L)
    (hcomm : ⁅L, L.map (MulAut.conj τ).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj τ).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers τ), (x * (τ * x * τ⁻¹)) w = w)
    (hrk3 : rkIdx (fixV (Subgroup.zpowers τ)) ≤ 3) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ 3 ∧ rkIdx (fixV (Subgroup.zpowers τ)) = n ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        IsMatTensor2 L (L.map (MulAut.conj τ).toMonoidHom) F := by
  obtain ⟨n, hn2, ⟨e₁⟩⟩ := exists_sl2_equiv (L := L) (t := τ) hV hLq hτ2 hcomm hirr hdiag
  rcases tensor_or_two_mul_le (L := L) (t := τ) hV hτ2 hmove hcomm hirr hdiag hn2 e₁ with
    h2n | ⟨hrk, F, hF, hFin, hcard, hT⟩
  · exfalso
    omega
  · exact ⟨n, hn2, by omega, hrk, F, hF, hFin, hcard, hT⟩

theorem swap_chief_nat (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {t : MulAut W} (hK : IsQuasisimple ↥K) (ht2 : orderOf t = 2)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (htr : ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {U₀ U : Subgroup W}
    (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom) U U₀)
    (htU : ∀ u ∈ U, t u ∈ U) (htU₀ : ∀ u ∈ U₀, t u ∈ U₀)
    (hnt : ¬ commSub U (K ⊔ K.map (MulAut.conj t).toMonoidHom) ≤ U₀) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ 3 ∧ secCost t U U₀ = n ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        IsMatTensor2 (secImg K U U₀) (secImg (K.map (MulAut.conj t).toMonoidHom) U U₀) F := by
  classical
  have hU₀U : U₀ ≤ U := le_of_lt hirr.1
  obtain ⟨hKs, hK's, hts⟩ := w16f_sec_stab hirr htU htU₀ ht2
  have hntK : ¬ commSub U K ≤ U₀ := w16f_sec_hntK hKs hK's hts hnt
  have hKq : IsQuasisimple ↥(secImg K U U₀) := isQuasisimple_secImg hK hKs hntK
  have hnt_t : ¬ commSub U (Subgroup.zpowers t) ≤ U₀ :=
    w16f_sec_t_nontrivial hKs hK's hts hcomm hKq
  have htτ : orderOf (secAut U U₀ ⟨t, hts⟩) = 2 := orderOf_secAut ht2 hts hnt_t
  have hcommSec := w16f_sec_comm hKs hK's hts hcomm
  have hmoveSec := w16f_sec_move hKs hK's hts hcomm hKq
  have hirrSec := w16f_sec_irr hU₀U hirr hKs hK's hts
  have hdiag := secImg_diag hKs hts htr
  have hWs := w16f_sec_exp_two (U₀ := U₀) (U := U) hW
  have hcost_le := w16f_sec_cost_le (U₀ := U₀) (U := U) hrk
  have hcost : rkIdx (fixV (Subgroup.zpowers (secAut U U₀ ⟨t, hts⟩))) = secCost t U U₀ :=
    rkIdx_fixV_secAut hU₀U hts
  obtain ⟨n, hn2, hn3, hrkIdx, F, _, _, hcard, hT⟩ :=
    w16f_swap_module (V := SecT U U₀) (L := secImg K U U₀)
      (τ := secAut U U₀ ⟨t, hts⟩) hWs (w16f_open_isQuasisimple hKq) htτ hmoveSec hcommSec
      hirrSec hdiag (by rw [hcost]; exact hcost_le)
  refine ⟨n, hn2, hn3, ?_, F, ‹Field F›, ‹Finite F›, hcard, ?_⟩
  · rw [← hcost]
    exact hrkIdx
  · exact w16f_isMatTensor2_congr_right (secImg_map_conj hKs hts).symm hT

end CFSG.LocalAnalysis.WeakClosure81
