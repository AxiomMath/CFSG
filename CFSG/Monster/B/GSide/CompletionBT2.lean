module

public import CFSG.Monster.B.GSide.BT2Reduce
public import CFSG.Monster.B.GSide.CompletionSubgroup
public import CFSG.Monster.B.GSide.EdgeData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Recog CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

theorem exists_hom_of_graph {X Y : Type*} [Group X] [Group Y] (K : Subgroup (Y × X))
    (hs : K.map (MonoidHom.snd Y X) = ⊤) (hk : ∀ k ∈ K, k.2 = 1 → k = 1) :
    ∃ Φ : X →* Y, ∀ k ∈ K, Φ k.2 = k.1 := by
  let p : K →* X := (MonoidHom.snd Y X).comp K.subtype
  have hinj : Function.Injective p :=
    (injective_iff_map_eq_one p).2 fun k h => Subtype.ext (hk k k.2 h)
  have hsurj : Function.Surjective p := fun x => by
    have hx : x ∈ K.map (MonoidHom.snd Y X) := by
      rw [hs]
      exact Subgroup.mem_top x
    obtain ⟨k, hk', rfl⟩ := hx
    exact ⟨⟨k, hk'⟩, rfl⟩
  let e : K ≃* X := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨(MonoidHom.fst Y X).comp (K.subtype.comp e.symm.toMonoidHom), fun k hk' => ?_⟩
  have h : e.symm k.2 = ⟨k, hk'⟩ := e.symm_apply_eq.2 rfl
  show ((e.symm k.2 : K) : Y × X).1 = k.1
  rw [h]

variable {G : Type*} [Group G]

theorem eq_one_of_conj_psiInvHom_eq
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (φe : cvSetStab {cv0, cw0} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom ψ ⟨a, ha⟩ = φe ⟨a, hb⟩) {g : G}
    (hv : ∀ a : vStab cv0, psiInvHom ψ a * g * (psiInvHom ψ a)⁻¹ = g)
    (he : ∀ a : cvSetStab {cv0, cw0}, φe a * g * (φe a)⁻¹ = g) : g = 1 := by
  have hc : ∀ x : Subgroup.centralizer {d}, (x : G) * g = g * x := fun x => by
    have h := hv (ψ x)
    rw [psiInvHom_apply, MulEquiv.symm_apply_apply, mul_inv_eq_iff_eq_mul] at h
    exact h
  have hgd : g ∈ Subgroup.centralizer {d} :=
    Subgroup.mem_centralizer_singleton_iff.2 (hc ⟨d, mem_centralizer_singleton_self d⟩).symm
  have hgZ : ψ ⟨g, hgd⟩ ∈ Subgroup.center (vStab cv0) := by
    rw [← mem_center_iff_of_mulEquiv ψ, Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hc x)
  rw [center_vStab_cv0] at hgZ
  rcases eq_one_or_eq_cV0 hgZ with h | h
  · exact congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm))
  ·
    exfalso
    have hg : g = psiInvHom ψ cV0 := by
      rw [psiInvHom_apply, ← h, MulEquiv.symm_apply_apply]
    have hswap := exists_edge_swap
    obtain ⟨s, hs0, hs1⟩ := hswap
    have hsE : s ∈ cvSetStab {cv0, cw0} := swap_mem_cEdgeStab hs0 hs1
    have hcE : (cV0 : Shat) ∈ cvSetStab {cv0, cw0} :=
      cEdgeFix_le_cEdgeStab clabelS_cv0_mem_cEdgeFix
    have hwE : clabelS cw0 ∈ cvSetStab {cv0, cw0} :=
      cEdgeFix_le_cEdgeStab clabelS_cw0_mem_cEdgeFix
    have hwV : clabelS cw0 ∈ vStab cv0 := clabelS_cw0_mem_cEdgeFix.1
    have hconj : s * (cV0 : Shat) * s⁻¹ = clabelS cw0 :=
      congrArg Subtype.val (cEdgeSigma_lamV0 hs0 hs1)
    have hg' : g = φe ⟨cV0, hcE⟩ := hg.trans (hve _ cV0.2 hcE)
    have h5 : psiInvHom ψ ⟨clabelS cw0, hwV⟩ = psiInvHom ψ cV0 :=
      calc psiInvHom ψ ⟨clabelS cw0, hwV⟩ = φe ⟨clabelS cw0, hwE⟩ := hve _ hwV hwE
        _ = φe (⟨s, hsE⟩ * ⟨cV0, hcE⟩ * ⟨s, hsE⟩⁻¹) := congrArg φe (Subtype.ext hconj.symm)
        _ = φe ⟨s, hsE⟩ * φe ⟨cV0, hcE⟩ * (φe ⟨s, hsE⟩)⁻¹ :=
          (map_mul φe _ _).trans (congrArg₂ (· * ·) (map_mul φe _ _) (map_inv φe _))
        _ = φe ⟨s, hsE⟩ * g * (φe ⟨s, hsE⟩)⁻¹ :=
          congrArg (fun y => φe ⟨s, hsE⟩ * y * (φe ⟨s, hsE⟩)⁻¹) hg'.symm
        _ = g := he _
        _ = psiInvHom ψ cV0 := hg
    have h6 := congrArg Subtype.val (psiInvHom_injective ψ h5)
    exact lamV0_ne_lamW0 (Subtype.ext h6.symm)

theorem exists_completion_of_bt2
    (h1 : BT2C1) (h2 : BT2C2) {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (φe : cvSetStab {cv0, cw0} →* G)
    (φt : cvSetStab {cv0, cw0, cu 0} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom ψ ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      psiInvHom ψ ⟨a, ha⟩ = φt ⟨a, hb⟩)
    (het : ∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      φe ⟨a, ha⟩ = φt ⟨a, hb⟩) :
    ∃ Φ : Shat →* G, Function.Injective Φ ∧ (∀ a : vStab cv0, Φ a = psiInvHom ψ a) ∧
      (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) ∧
      ∀ a : cvSetStab {cv0, cw0, cu 0}, Φ a = φt a := by
  have hK := bt2_completion_ker_le_two h1 h2 (psiInvHom ψ) φe φt hve hvt het
  obtain ⟨hKt, hKs, n, hnK, hn2, hker⟩ := hK
  have hn1 : n = 1 := by
    by_contra hn
    have hcent : ∀ k ∈ homGraph (psiInvHom ψ) ⊔ homGraph φe, k * n * k⁻¹ = n := fun k hk => by
      have hm := (homGraph (psiInvHom ψ) ⊔ homGraph φe).mul_mem
        ((homGraph (psiInvHom ψ) ⊔ homGraph φe).mul_mem hk hnK)
        ((homGraph (psiInvHom ψ) ⊔ homGraph φe).inv_mem hk)
      have hm2 : (k * n * k⁻¹).2 = 1 := by
        show k.2 * n.2 * k.2⁻¹ = 1
        rw [hn2, mul_one, mul_inv_cancel]
      rcases hker _ hm hm2 with h | h
      · exact absurd (mul_eq_left.1 (mul_inv_eq_one.1 h)) hn
      · exact h
    have hg := eq_one_of_conj_psiInvHom_eq ψ φe hve (g := n.1)
      (fun a => congrArg Prod.fst
        (hcent _ (Subgroup.mem_sup_left (mk_mem_homGraph (psiInvHom ψ) a))))
      (fun a => congrArg Prod.fst (hcent _ (Subgroup.mem_sup_right (mk_mem_homGraph φe a))))
    exact hn (Prod.ext hg hn2)
  have hk1 : ∀ k ∈ homGraph (psiInvHom ψ) ⊔ homGraph φe, k.2 = 1 → k = 1 := fun k hk hk2 =>
    (hker k hk hk2).elim id fun h => h.trans hn1
  have hΦ := exists_hom_of_graph _ hKs hk1
  obtain ⟨Φ, hΦ⟩ := hΦ
  have hΦv : ∀ a : vStab cv0, Φ a = psiInvHom ψ a := fun a =>
    hΦ _ (Subgroup.mem_sup_left (mk_mem_homGraph (psiInvHom ψ) a))
  refine ⟨Φ, injective_of_map_cV0_ne_one Φ fun h => cV0_ne_one (psiInvHom_injective ψ
      ((hΦv cV0).symm.trans (h.trans (map_one (psiInvHom ψ)).symm))), hΦv,
    fun a => hΦ _ (Subgroup.mem_sup_right (mk_mem_homGraph φe a)), fun a => hΦ _ (hKt a)⟩

theorem gside_reduction_bt2
    [Finite G] (h1 : BT2C1) (h2 : BT2C2) (d₀ : NativeSporadic.B)
    (hd₀ : orderOf d₀ = 2) (hrank : Matrix.rank (d₀.val.val - 1) = 1860) {d : G}
    (φ : Subgroup.centralizer {d} ≃* Subgroup.centralizer {d₀})
    (φe : cvSetStab {cv0, cw0} →* G) (φt : cvSetStab {cv0, cw0, cu 0} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom (psiOf hd₀ hrank φ) ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      psiInvHom (psiOf hd₀ hrank φ) ⟨a, ha⟩ = φt ⟨a, hb⟩)
    (het : ∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
      φe ⟨a, ha⟩ = φt ⟨a, hb⟩)
    (hC : ∀ Φ : Shat →* G, (∀ a : vStab cv0, Φ a = psiInvHom (psiOf hd₀ hrank φ) a) →
      (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) →
      (∀ a : cvSetStab {cv0, cw0, cu 0}, Φ a = φt a) →
      ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range) :
    Nonempty (G ≃* NativeSporadic.B) := by
  have hΦ := exists_completion_of_bt2 h1 h2 (psiOf hd₀ hrank φ) φe φt hve hvt het
  obtain ⟨Φ, hΦ, hΦv, hΦe, hΦt⟩ := hΦ
  exact nonempty_mulEquiv_B_of_range_eq_top Φ hΦ
    (range_eq_top_of_centralizer_le Φ hΦ (hC Φ hΦv hΦe hΦt))

end CFSG.Monster.B.GSide
