module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.GH74.Uniqueness.Section7Lemma711Aux

public section

namespace CFSG.StandardType

theorem ggAutomizer_map_of_coprime_card_ker
    {G G' : Type} [Group G] [Finite G] [Group G']
    {p : ℕ} [Fact p.Prime] {f : G →* G'}
    (hpker : ¬ p ∣ Nat.card f.ker)
    {Bs H : Subgroup G} (hBs : IsPGroup p Bs)
    (hBN : Bs ≤ Subgroup.normalizer (H : Set G))
    {Bs' : Subgroup G'} (hmap : Bs.map f = Bs')
    (e : ↥Bs ≃* ↥Bs')
    (he : ∀ b : ↥Bs, (e b : G') = f b) :
    ggAutomizer (H.map f) Bs' =
      (ggAutomizer H Bs).map (MulAut.congr e).toMonoidHom := by
  subst Bs'
  classical
  let R : Subgroup G := H ⊔ Bs
  let N : Subgroup R := f.ker.subgroupOf R
  have hHR : H ≤ R := le_sup_left
  have hBsR : Bs ≤ R := le_sup_right
  have hRnorm : (H.subgroupOf R).Normal := by
    have hR : R = Bs ⊔ H := by
      change H ⊔ Bs = Bs ⊔ H
      rw [sup_comm]
    rw [hR]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hBN
  have := hRnorm
  have hNnorm : N.Normal := by
    dsimp [N]
    infer_instance
  have := hNnorm
  have hBsRp : IsPGroup p (Bs.subgroupOf R) :=
    hBs.of_equiv (Subgroup.subgroupOfEquivOfLe hBsR).symm
  have hNcard : Nat.card (N.map R.subtype) = Nat.card N :=
    Subgroup.card_map_of_injective R.subtype_injective
  have hNleKer : N.map R.subtype ≤ f.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp hy
  have hdvd : Nat.card N ∣ Nat.card f.ker := by
    rw [← hNcard]
    exact Subgroup.card_dvd_of_le hNleKer
  have hpN : ¬ p ∣ Nat.card N := fun h => hpker (Nat.dvd_trans h hdvd)
  have hquotP : IsPGroup p (↥R ⧸ H.subgroupOf R) :=
    CFSG.GH74.Uniqueness.isPGroup_quotient_sup_of_le_normalizer (p := p) H Bs hBs
  have hQp : IsPGroup p (N.map (QuotientGroup.mk' (H.subgroupOf R))) :=
    hquotP.to_subgroup (N.map (QuotientGroup.mk' (H.subgroupOf R)))
  have hQdvd : Nat.card (N.map (QuotientGroup.mk' (H.subgroupOf R))) ∣ Nat.card N :=
    Subgroup.card_map_dvd (H := N) (f := QuotientGroup.mk' (H.subgroupOf R))
  have hpQ : ¬ p ∣ Nat.card (N.map (QuotientGroup.mk' (H.subgroupOf R))) :=
    fun h => hpN (Nat.dvd_trans h hQdvd)
  have hQcard : Nat.card (N.map (QuotientGroup.mk' (H.subgroupOf R))) = 1 := by
    rcases IsPGroup.card_eq_or_dvd hQp with h | h
    · exact h
    · exact absurd h hpQ
  have hQbot : N.map (QuotientGroup.mk' (H.subgroupOf R)) = ⊥ :=
    Subgroup.card_eq_one.mp hQcard
  have hNleH : N ≤ H.subgroupOf R := by
    have h : N ≤ (QuotientGroup.mk' (H.subgroupOf R)).ker :=
      (Subgroup.map_eq_bot_iff (H := N)
        (f := QuotientGroup.mk' (H.subgroupOf R))).mp hQbot
    simpa [QuotientGroup.ker_mk'] using h
  have hNtoH : ∀ x : R, x ∈ N → (x : G) ∈ H := fun x hx =>
    Subgroup.mem_subgroupOf.mp (hNleH hx)
  have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer (p := p) N hpN
    (Bs.subgroupOf R) hBsRp
  have hconj : ∀ (hR : R), (hR : G) ∈ H →
      f (hR : G) ∈ Subgroup.normalizer (Bs.map f : Set G') →
      ∀ bR : ↥(Bs.subgroupOf R),
        QuotientGroup.mk' N (hR * (bR : R) * hR⁻¹) ∈
          (Bs.subgroupOf R).map (QuotientGroup.mk' N) := by
    intro hR hhH hhn bR
    have hbBs : ((bR : R) : G) ∈ Bs := Subgroup.mem_subgroupOf.mp bR.2
    have hxB : f (((hR * (bR : R) * hR⁻¹ : R) : G)) ∈ Bs.map f := by
      have hmem := (Subgroup.mem_normalizer_iff.mp hhn) (f ((bR : R) : G))
      have hb : f ((bR : R) : G) ∈ Bs.map f := Subgroup.mem_map_of_mem f hbBs
      have := hmem.mp hb
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
    obtain ⟨b', hb'Bs, hfb'⟩ := Subgroup.mem_map.mp hxB
    let b'R : ↥(Bs.subgroupOf R) :=
      ⟨⟨b', hBsR hb'Bs⟩, Subgroup.mem_subgroupOf.mpr hb'Bs⟩
    have hxker : (((hR * (bR : R) * hR⁻¹) * ((b'R : R))⁻¹ : R) : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have hb'Rcoe : ((b'R : R) : G) = b' := rfl
      have hval : f ((((hR * (bR : R) * hR⁻¹) * ((b'R : R))⁻¹ : R) : G)) =
          f (((hR * (bR : R) * hR⁻¹ : R) : G)) * (f b')⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hb'Rcoe]
      rw [hval, hfb']
      exact mul_inv_cancel _
    have hxN : (hR * (bR : R) * hR⁻¹) * ((b'R : R))⁻¹ ∈ N :=
      Subgroup.mem_subgroupOf.mpr hxker
    have hqeq : QuotientGroup.mk' N (hR * (bR : R) * hR⁻¹) =
        QuotientGroup.mk' N ((b'R : R)) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv] using hxN
    rw [hqeq]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) b'R.2
  refine le_antisymm ?_ ?_
  ·
    intro φ' hφ'
    obtain ⟨g', hg'H, hg'N, hφ'g'⟩ := mem_ggAutomizer_iff.mp hφ'
    obtain ⟨h, hhH, hfh⟩ := Subgroup.mem_map.mp hg'H
    let hR : R := ⟨h, hHR hhH⟩
    have hhHR : (hR : G) ∈ H := hhH
    have hhn : f (hR : G) ∈ Subgroup.normalizer (Bs.map f : Set G') := by
      simpa [hR, hfh] using hg'N
    have hq_norm : QuotientGroup.mk' N hR ∈
        Subgroup.normalizer (((Bs.subgroupOf R).map (QuotientGroup.mk' N) :
          Subgroup (R ⧸ N)) : Set (R ⧸ N)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨bR, hbR, rfl⟩ := Subgroup.mem_map.mp hx
        simpa only [map_mul, map_inv] using hconj hR hhHR hhn ⟨bR, hbR⟩
      · intro hx
        obtain ⟨bR, hbR, hbRq⟩ := Subgroup.mem_map.mp hx
        have hxeq : x = QuotientGroup.mk' N (hR⁻¹ * bR * hR) := by
          simp only [map_mul, map_inv, hbRq]
          group
        rw [hxeq]
        simpa only [inv_inv] using
          hconj hR⁻¹ (by simpa using H.inv_mem hhHR) (by
            have hfinv : f ((hR⁻¹ : R) : G) = (f (hR : G))⁻¹ := by simp
            rw [hfinv]
            exact Subgroup.inv_mem _ hhn) ⟨bR, hbR⟩
    have hq_norm' : QuotientGroup.mk' N hR ∈
        (Subgroup.normalizer (Bs.subgroupOf R : Set R)).map (QuotientGroup.mk' N) := by
      rw [hnorm]
      exact hq_norm
    obtain ⟨nR, hnRnorm, hnReq⟩ := Subgroup.mem_map.mp hq_norm'
    have hkR : nR⁻¹ * hR ∈ N := by
      have hq1 : QuotientGroup.mk' N (nR⁻¹ * hR) = 1 := by
        rw [map_mul, map_inv, hnReq, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (nR⁻¹ * hR)).mp hq1
    have hkH : ((nR⁻¹ * hR : R) : G) ∈ H := hNtoH _ hkR
    have hnH : (nR : G) ∈ H := by
      have hcoeeq : (nR : G) = (hR : G) * (((nR⁻¹ * hR : R) : G))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcoeeq]
      exact H.mul_mem hhHR (H.inv_mem hkH)
    have hkker : ((nR⁻¹ * hR : R) : G) ∈ f.ker :=
      Subgroup.mem_subgroupOf.mp hkR
    have hfnR : f (nR : G) = f (hR : G) := by
      have hcoeeq : (hR : G) = (nR : G) * (((nR⁻¹ * hR : R) : G)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcoeeq, map_mul, MonoidHom.mem_ker.mp hkker, mul_one]
    have hnGnorm : (nR : G) ∈ Subgroup.normalizer (Bs : Set G) := by
      have hmem := Subgroup.mem_map_of_mem R.subtype hnRnorm
      have hle := Subgroup.le_normalizer_map R.subtype hmem
      simpa [Subgroup.map_subgroupOf_eq_of_le hBsR] using hle
    have hfn : f (nR : G) = g' := by
      rw [hfnR, hfh]
    refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hnGnorm,
      ggConjAut_mem_ggAutomizer hnH hnGnorm, ?_⟩
    ext b'
    obtain ⟨b, rfl⟩ := e.surjective b'
    calc ((MulAut.congr e (ggConjAut Bs hnGnorm) (e b) : ↥(Bs.map f)) : G')
        = f (ggConjAut Bs hnGnorm b) := by
          rw [MulAut.congr_apply]
          simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
          exact he _
      _ = f ((nR : G) * (b : G) * (nR : G)⁻¹) := by
          rw [ggConjAut_apply]
      _ = f (nR : G) * f (b : G) * (f (nR : G))⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = g' * (e b : G') * g'⁻¹ := by
          rw [hfn, he b]
      _ = ((φ' (e b) : ↥(Bs.map f)) : G') := (hφ'g' (e b)).symm
  ·
    intro φ' hφ'
    obtain ⟨φ, hφA, rfl⟩ := Subgroup.mem_map.mp hφ'
    obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
    refine mem_ggAutomizer_iff.mpr ⟨f g, Subgroup.mem_map_of_mem f hgH, ?_, ?_⟩
    · exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hgN)
    · intro b'
      obtain ⟨b, rfl⟩ := e.surjective b'
      calc ((MulAut.congr e φ (e b) : ↥(Bs.map f)) : G')
          = f (φ b) := by
            rw [MulAut.congr_apply]
            simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
            exact he _
        _ = f (g * (b : G) * g⁻¹) := by
            rw [hφg]
        _ = f g * f (b : G) * (f g)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = f g * (e b : G') * (f g)⁻¹ := by
            rw [he b]

end CFSG.StandardType
