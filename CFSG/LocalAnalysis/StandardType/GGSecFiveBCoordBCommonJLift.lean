module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJTransfer
import CFSG.LocalAnalysis.StandardType.GGTBJLift
import CFSG.LocalAnalysis.StandardType.GGTCJDescent
import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.HardMathSupport.Solomon.Coordinator

namespace CommonJ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {R : Type} [Group R] {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {γ : ↥Bs →* R}

theorem exists_stdSubPre_of_component (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {z₁ : ↥Bs} (hz₁ : (z₁ : G) ∉ Subgroup.zpowers x)
    {K : Subgroup R} (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({γ z₁} : Set R)))
    (huniq : ∀ K' : Subgroup R,
      CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({γ z₁} : Set R)) → K' = K)
    (hKT : γ.range ⊓ Subgroup.centralizer (K : Set R) = Subgroup.zpowers (γ z₁)) :
    ∃ K₁ : Subgroup G, LargeEvenStdSubPre p B x L (Subgroup.closure {x, (z₁ : G)}) K₁ ∧
      K₁ ≤ L ∧ (K₁.subgroupOf L).map (ggQuotHom θ) = K := by
  let ψ : ↥L →* R := ggQuotHom θ
  have hψ : Function.Surjective ψ := ggQuotHom_surjective θ
  have hker : ψ.ker ≤ Subgroup.center ↥L := le_of_eq (ker_ggQuotHom θ)
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hz1 : (z₁ : G) ≠ 1 := fun h =>
    hz₁ (by simpa [h] using Subgroup.one_mem (Subgroup.zpowers x))
  have hxpow : x ^ p = 1 := hBs.2 x hxBs
  have hzpow : (z₁ : G) ^ p = 1 := hBs.2 (z₁ : G) z₁.2
  have hxord : orderOf x = p := orderOf_eq_prime hxpow hx1
  have hzord : orderOf (z₁ : G) = p := orderOf_eq_prime hzpow hz1
  have hzN : (z₁ : G) ∈ Subgroup.normalizer (L : Set G) := hBsN z₁.2
  let y : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨(z₁ : G), hzN⟩
  have hyapply : ∀ l : ↥L,
      ((y l : ↥L) : G) = (z₁ : G) * (l : G) * (z₁ : G)⁻¹ := by
    intro l
    rw [show y = Subgroup.normalizerMonoidHom (H := L) ⟨(z₁ : G), hzN⟩ from rfl]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hγz : ∀ l : ↥L, ψ (y l) = γ z₁ * ψ l * (γ z₁)⁻¹ := fun l =>
    hγ z₁ l (y l) (hyapply l)
  have hfix_eq : (fixSubgroup y).map L.subtype =
      L ⊓ Subgroup.centralizer ({(z₁ : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨l.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hyapply l
      rw [mem_fixSubgroup.mp hl] at h
      calc (l : G) * (z₁ : G) = ((z₁ : G) * (l : G) * (z₁ : G)⁻¹) * (z₁ : G) := by
            conv_lhs => rw [h]
        _ = (z₁ : G) * (l : G) := by group
    · rintro ⟨hgl, hgc⟩
      refine ⟨⟨g, hgl⟩, ?_, rfl⟩
      change y ⟨g, hgl⟩ = ⟨g, hgl⟩
      apply Subtype.ext
      rw [hyapply]
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hgc
      rw [← hcomm]
      group
  have hCX : ∀ c ∈ fixSubgroup y, ψ c ∈ Subgroup.centralizer ({γ z₁} : Set R) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hγz c
    rw [mem_fixSubgroup.mp hc] at h
    calc ψ c * γ z₁ = (γ z₁ * ψ c * (γ z₁)⁻¹) * γ z₁ := by
          conv_lhs => rw [h]
      _ = γ z₁ * ψ c := by group
  have hSr : K ≤ ψ.range := by
    rw [MonoidHom.range_eq_top.mpr hψ]
    exact le_top
  have hKopen : CFSG.Open.IsComponentOf K
      (Subgroup.centralizer ({γ z₁} : Set R)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hK
  obtain ⟨Q, hQcompO, hQmap⟩ :=
    ggTBJ_exists_component_lift_fix ψ hker y (γ z₁) hγz hKopen hSr hKopen.1 hCX
  have hQcomp : CFSG.Assembly.IsComponentOf Q (fixSubgroup y) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hQcompO
  let K₁ : Subgroup G := Q.map L.subtype
  have hK₁leL : K₁ ≤ L := Subgroup.map_subtype_le Q
  have hK₁compMap : CFSG.Assembly.IsComponentOf K₁ ((fixSubgroup y).map L.subtype) := by
    refine ⟨Subgroup.map_mono hQcomp.1, CFSG.Assembly.IsSubnormal.map L.subtype hQcomp.2.1, ?_⟩
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Q.equivMapOfInjective L.subtype L.subtype_injective).symm hQcomp.2.2
  have hfixconj : ggFixSub (MulAut.conj (γ z₁)) =
      Subgroup.centralizer ({γ z₁} : Set R) := by
    rw [show ggFixSub (MulAut.conj (γ z₁)) = fixSubgroup (MulAut.conj (γ z₁)) from rfl]
    exact ggTBJ_fixSubgroup_conj (γ z₁)
  have huniqQ : ∀ J : Subgroup ↥L, CFSG.Assembly.IsComponentOf J (fixSubgroup y) → J = Q := by
    intro J hJ
    have hφ : ∀ k : ↥L, MulAut.conj (γ z₁) (ψ k) = ψ (y k) := fun k => by
      rw [MulAut.conj_apply]
      exact (hγz k).symm
    have hJmap_comp := (CFSG.StandardType.TCJ.ggTCJ_descent ψ hψ hker y
      (MulAut.conj (γ z₁)) hφ J hJ).1
    have hJmap : CFSG.Assembly.IsComponentOf (J.map ψ)
        (Subgroup.centralizer ({γ z₁} : Set R)) := by
      rwa [hfixconj] at hJmap_comp
    have hJmap_eq : J.map ψ = K := huniq (J.map ψ) hJmap
    have hcomJ : ⁅(J.map ψ).comap ψ, (J.map ψ).comap ψ⁆ = J :=
      CFSG.LocalAnalysis.ComponentInitial.commutator_comap_map_eq (π := ψ) hker hJ.2.2
    have hcomQ : ⁅(Q.map ψ).comap ψ, (Q.map ψ).comap ψ⁆ = Q :=
      CFSG.LocalAnalysis.ComponentInitial.commutator_comap_map_eq (π := ψ) hker hQcomp.2.2
    rw [hJmap_eq] at hcomJ
    rw [hQmap] at hcomQ
    exact hcomJ.symm.trans hcomQ
  let H : Subgroup G := L ⊓ Subgroup.centralizer
    (Subgroup.closure {x, (z₁ : G)} : Set G)
  have hHle : H ≤ L := inf_le_left
  have hH_eq : H = L ⊓ Subgroup.centralizer ({(z₁ : G)} : Set G) := by
    have hcent : Subgroup.centralizer (Subgroup.closure {x, (z₁ : G)} : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({(z₁ : G)} : Set G) := by
      rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure, CFSG.centralizer_sup_eq,
        CFSG.centralizer_zpowers_eq_centralizer_singleton,
        CFSG.centralizer_zpowers_eq_centralizer_singleton]
    rw [show H = L ⊓ Subgroup.centralizer
        (Subgroup.closure {x, (z₁ : G)} : Set G) from rfl, hcent, ← inf_assoc,
      inf_eq_left.mpr hLx]
  have hHmap : H = (fixSubgroup y).map L.subtype := hH_eq.trans hfix_eq.symm
  have hK₁comp : CFSG.Assembly.IsComponentOf K₁ H := by
    rw [hHmap]
    exact hK₁compMap
  have hHsub : H.subgroupOf L = fixSubgroup y := by
    rw [hHmap]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have huniqK₁ : ∀ J : Subgroup G, CFSG.Assembly.IsComponentOf J H → J = K₁ := by
    intro J hJ
    have hJLcomp : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (H.subgroupOf L) := by
      refine ⟨Subgroup.comap_mono hJ.1, CFSG.Assembly.IsSubnormal.comap L.subtype hJ.2.1, ?_⟩
      exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (hJ.1.trans hHle)) hJ.2.2
    have hJLcomp' : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (fixSubgroup y) := by
      rwa [hHsub] at hJLcomp
    have hJLeq : J.subgroupOf L = Q := huniqQ _ hJLcomp'
    have hJmap : (J.subgroupOf L).map L.subtype = J :=
      Subgroup.map_subgroupOf_eq_of_le (hJ.1.trans hHle)
    rw [hJLeq] at hJmap
    exact hJmap.symm
  have hLayer : LargeEvenLayer H = K₁ := by
    rw [show LargeEvenLayer H =
      sSup {J : Subgroup G | CFSG.Assembly.IsComponentOf J H} from rfl]
    exact le_antisymm (sSup_le fun J hJ => (huniqK₁ J hJ).le) (le_sSup hK₁comp)
  have hD₁_le_Bs : Subgroup.closure {x, (z₁ : G)} ≤ Bs := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hxBs
    · exact z₁.2
  have hD₁_le_B : Subgroup.closure {x, (z₁ : G)} ≤ B := by
    rwa [hB]
  have hD₁_elem : CFSG.Open.IsElemAbelian p (Subgroup.closure {x, (z₁ : G)}) := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a (rfl | rfl) b (rfl | rfl)
      · rfl
      · exact hBs.comm hxBs z₁.2
      · exact hBs.comm z₁.2 hxBs
      · rfl
    · rintro a (rfl | rfl)
      · exact hxpow
      · exact hzpow
  have hD₁_eq_sup : Subgroup.closure {x, (z₁ : G)} =
      Subgroup.zpowers x ⊔ Subgroup.zpowers (z₁ : G) := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers (z₁ : G) = ⊥ := by
    have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers (z₁ : G) ≤ Subgroup.zpowers x :=
      inf_le_left
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (z₁ : G) :
        Subgroup G) ∣ p := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hxord] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hge : Nat.card (Subgroup.zpowers x) ≤
          Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers (z₁ : G) : Subgroup G) := by
        rw [hp', Nat.card_zpowers, hxord]
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (z₁ : G) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle hge
      have hle' : Subgroup.zpowers x ≤ Subgroup.zpowers (z₁ : G) := heq ▸ inf_le_right
      have heq2 : Subgroup.zpowers x = Subgroup.zpowers (z₁ : G) :=
        Subgroup.eq_of_le_of_card_ge hle' (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hzord])
      exact hz₁ (heq2.symm ▸ Subgroup.mem_zpowers (z₁ : G))
  have hcommxz : Commute x (z₁ : G) := hBs.comm hxBs z₁.2
  have hnorm : Subgroup.zpowers (z₁ : G) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have hzcent : Subgroup.zpowers (z₁ : G) ≤
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      simpa using (hcommxz.zpow_zpow l 1).eq
    exact hzcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcardD₁ : Nat.card (Subgroup.closure {x, (z₁ : G)}) = p ^ 2 := by
    rw [hD₁_eq_sup,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
        (by rw [disjoint_iff]; exact hdisj),
      Nat.card_zpowers, Nat.card_zpowers, hxord, hzord]
    ring
  have hxD₁ : x ∈ Subgroup.closure {x, (z₁ : G)} := Subgroup.subset_closure (by simp)
  have hD₁_le_cent : Subgroup.closure {x, (z₁ : G)} ≤
      Subgroup.centralizer (K₁ : Set G) :=
    Subgroup.le_centralizer_iff.mp (hK₁comp.1.trans inf_le_right)
  have hD₁_le : Subgroup.closure {x, (z₁ : G)} ≤
      B ⊓ Subgroup.centralizer (K₁ : Set G) := le_inf hD₁_le_B hD₁_le_cent
  have hD₁_rev : B ⊓ Subgroup.centralizer (K₁ : Set G) ≤
      Subgroup.closure {x, (z₁ : G)} := by
    intro b hb
    obtain ⟨hbB, hbCent⟩ := Subgroup.mem_inf.mp hb
    have hbBs : b ∈ Bs := by rwa [hB] at hbB
    let bBs : ↥Bs := ⟨b, hbBs⟩
    have hγbCentK : γ bBs ∈ Subgroup.centralizer (K : Set R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : k ∈ Q.map ψ := by rwa [← hQmap] at hk
      obtain ⟨q, hqQ, hqk⟩ := Subgroup.mem_map.mp hk'
      have hqK₁ : (q : G) ∈ K₁ := Subgroup.mem_map.mpr ⟨q, hqQ, rfl⟩
      have hbc : b * (q : G) = (q : G) * b :=
        (Subgroup.mem_centralizer_iff.mp hbCent (q : G) hqK₁).symm
      have hmemL : b * (q : G) * b⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hBsN hbBs) (q : G)).mp q.2
      let q' : ↥L := ⟨b * (q : G) * b⁻¹, hmemL⟩
      have hq'eq : q' = q := by
        apply Subtype.ext
        change b * (q : G) * b⁻¹ = (q : G)
        rw [hbc]; group
      have h := hγ bBs q q' (by rfl)
      rw [hq'eq, hqk] at h
      calc k * γ bBs = (γ bBs * k * (γ bBs)⁻¹) * γ bBs := by
            conv_lhs => rw [h]
        _ = γ bBs * k := by group
    have hγbMem : γ bBs ∈ γ.range ⊓ Subgroup.centralizer (K : Set R) :=
      Subgroup.mem_inf.mpr ⟨⟨bBs, rfl⟩, hγbCentK⟩
    rw [hKT] at hγbMem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hγbMem
    let c : ↥Bs := bBs * (z₁ ^ m)⁻¹
    have hcγ : γ c = 1 := by
      change γ (bBs * (z₁ ^ m)⁻¹) = 1
      rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
    have hc_mem_x : (c : G) ∈ Subgroup.zpowers x :=
      (gammaHat_eq_one_iff hcfg hB hBsN hR hγ c).mp hcγ
    have hb_eq : b = (c : G) * ((z₁ : G) ^ m) := by
      change b = (b * ((z₁ : G) ^ m)⁻¹) * ((z₁ : G) ^ m)
      group
    rw [hD₁_eq_sup, hb_eq]
    exact Subgroup.mul_mem_sup hc_mem_x (Subgroup.zpow_mem_zpowers (z₁ : G) m)
  have hD₁_eq : Subgroup.closure {x, (z₁ : G)} =
      B ⊓ Subgroup.centralizer (K₁ : Set G) := le_antisymm hD₁_le hD₁_rev
  refine ⟨K₁, ?_, hK₁leL, ?_⟩
  · have hstd : LargeEvenStdSubPre p B x L (Subgroup.closure {x, (z₁ : G)}) K₁ :=
      ⟨hD₁_le_B, hD₁_elem, hcardD₁, hxD₁, by simpa [H] using hLayer.symm,
        by simpa [H] using hK₁comp, hD₁_eq⟩
    exact hstd
  · have hsubQ : K₁.subgroupOf L = Q := by
      rw [show K₁ = Q.map L.subtype from rfl]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q
    rw [hsubQ, hQmap]


end CommonJ

end CFSG.StandardType

end
