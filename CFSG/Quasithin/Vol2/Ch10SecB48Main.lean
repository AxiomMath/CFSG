module

public import CFSG.Quasithin.Vol2.Ch10SecB48
public import CFSG.Quasithin.Background.B4L3Three
public import CFSG.Quasithin.Vol2.Ch10SecE9U

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace B48

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {W C : Subgroup V}
  (hGW : G ≤ stabSub W) (hGC : G ≤ stabSub C)

omit [Finite V] in
theorem binaryNatural (hW : XMod.IsInv ↥G W) (hCW : C ≤ W)
    (hnat : BinaryNaturalSL G (modComm G W ⊔ C) C 3 1) :
    BinaryNaturalSL (B5.secHom G hGW hGC).range (commV (B5.secHom G hGW hGC).range) ⊥ 3 1 := by
  obtain ⟨K, _, _, hKc, π, hπs, -, hkerle, hUinv, -, hsec, hker, β, hβs, hβk, hβe⟩ := hnat
  set ψ := B5.secHom G hGW hGC with hψ
  have hUW : modComm G W ⊔ C ≤ W := sup_le (modComm_le hW) hCW
  set μ := mu C hUW with hμ
  have hrange : μ.range = commV ψ.range := range_mu hGW hGC hW hCW
  have hkle : μ.ker ≤ β.ker := fun u hu => by
    rw [MonoidHom.mem_ker, hβk]
    exact (mu_eq_one_iff hUW u).1 hu
  set β' := (QuotientGroup.lift μ.ker β hkle).comp
    ((QuotientGroup.quotientKerEquivRange μ).symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr hrange.symm).toMonoidHom) with hβ'
  have hmem : ∀ u : ↥(modComm G W ⊔ C), μ u ∈ commV ψ.range := fun u => hrange ▸ ⟨u, rfl⟩
  have hβ'μ : ∀ u : ↥(modComm G W ⊔ C), β' ⟨μ u, hmem u⟩ = β u := by
    intro u
    have h1 : (QuotientGroup.quotientKerEquivRange μ).symm ⟨μ u, ⟨u, rfl⟩⟩ =
        (QuotientGroup.mk u : ↥(modComm G W ⊔ C) ⧸ μ.ker) := by
      apply (QuotientGroup.quotientKerEquivRange μ).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change QuotientGroup.lift μ.ker β hkle
      ((QuotientGroup.quotientKerEquivRange μ).symm ⟨μ u, ⟨u, rfl⟩⟩) = β u
    rw [h1]
    rfl
  have hlift : ∀ t : ↥(commV ψ.range), ∃ u : ↥(modComm G W ⊔ C), μ u = (t : Sec W C) :=
    fun t => (hrange.symm ▸ t.2 : (t : Sec W C) ∈ μ.range)
  refine ⟨K, inferInstance, inferInstance, hKc, ψ.rangeRestrict.comp π,
    ψ.rangeRestrict_surjective.comp hπs, bot_le, hkerle,
    fun h u hu => commV_invariant _ h h.2 u hu, fun h z hz => ?_, hsec, hker, β', ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro m
    obtain ⟨u, hu⟩ := hβs m
    exact ⟨⟨μ u, hmem u⟩, by rw [hβ'μ, hu]⟩
  · intro t
    obtain ⟨u, hu⟩ := hlift t
    have ht : t = ⟨μ u, hmem u⟩ := Subtype.ext hu.symm
    rw [ht, hβ'μ, hβk, Subgroup.mem_bot, ← mu_eq_one_iff hUW u]
  · intro γ t m ht hm htm
    obtain ⟨u, hu⟩ := hlift t
    have ht' : t = ⟨μ u, hmem u⟩ := Subtype.ext hu.symm
    subst ht'
    have hu' : ((π γ : ↥G) : MulAut V) (u : V) ∈ modComm G W ⊔ C := hUinv (π γ) u u.2
    have e : (⟨((ψ.rangeRestrict.comp π γ : ↥ψ.range) : MulAut (Sec W C)) (μ u), ht⟩ :
        ↥(commV ψ.range)) = ⟨μ ⟨_, hu'⟩, hmem ⟨_, hu'⟩⟩ := by
      apply Subtype.ext
      change ψ (π γ) (μ u) = μ ⟨_, hu'⟩
      rw [mu_apply, mu_apply, secHom_mk']
    rw [e, hβ'μ]
    rw [hβ'μ] at htm
    exact hβe γ u m hu' hm htm

end B48

open B48 in
theorem asB4_8Three_holds : AsB4_8Three := by
  intro V _ _ hV G W C _ hCW hW hC hfaith hcard hind hnat a ha ha2 w hw haw
  have hGW := le_stabSub hW
  have hGC := le_stabSub hC
  set ψ := B5.secHom G hGW hGC with hψ
  have hUW : modComm G W ⊔ C ≤ W := sup_le (modComm_le hW) hCW
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [B5.mem_ker_secHom, mem_centSec] at hg
    exact Subgroup.mem_bot.2 (Subtype.ext (hfaith g g.2 hg.2))
  have ha1 : ψ ⟨a, ha⟩ ≠ 1 := by
    intro h
    have h1 : (⟨a, ha⟩ : ↥G) = 1 := hinj (by rw [h, map_one])
    have h2 : a = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at ha2
    omega
  have ha2' : ψ ⟨a, ha⟩ ^ 2 = 1 := by
    have h1 : (⟨a, ha⟩ : ↥G) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← ha2]
      exact pow_orderOf_eq_one a)
    rw [← map_pow, h1, map_one]
  have hfix : (QuotientGroup.mk (⟨w, hw⟩ : ↥W) : Sec W C) ∈
      fixV (Subgroup.zpowers (ψ ⟨a, ha⟩)) := by
    rw [mem_fixV_zpowers_iff, secHom_mk']
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    change ((a w)⁻¹ * w : V) ∈ C
    have h1 := C.inv_mem haw
    rwa [mul_inv_rev, inv_inv, mul_comm] at h1
  obtain ⟨-, -, hB⟩ := B4_8_3 (sq_eq_one hV) (card_sec hCW hcard)
    (binaryNatural hGW hGC hW hCW hnat) (isIndecomp hGW hGC hCW hind)
  have h1 := (hB _ ⟨_, rfl⟩ ha1 ha2').2.2 hfix
  rw [← range_mu hGW hGC hW hCW] at h1
  obtain ⟨u, hu⟩ := h1
  rw [mu_apply] at hu
  have hc := QuotientGroup.eq.mp hu
  rw [Subgroup.mem_subgroupOf] at hc
  have e : w = (u : V) * (((⟨u, hUW u.2⟩ : ↥W)⁻¹ * ⟨w, hw⟩ : ↥W) : V) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ u.2 (Subgroup.mem_sup_right hc)

end CFSG.Quasithin.Vol2.Ch10.SecB
