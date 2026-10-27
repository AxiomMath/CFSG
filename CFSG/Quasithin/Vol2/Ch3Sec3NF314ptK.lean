module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313B
public import CFSG.Quasithin.Vol2.Ch3Sec3NFFacts

public section

namespace CFSG.Quasithin.H13.NFConfig

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.BenC CFSG.Quasithin.H13.Lem3313B

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G}

theorem exists_pair (c : NFConfig G T M L D H K) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    ∃ t' ∈ T, t' ∉ Subgroup.normalizer (K : Set G) ∧
      K.map (MulAut.conj t').toMonoidHom ∈ cComp (H ⊔ D) ∧
      K ≠ K.map (MulAut.conj t').toMonoidHom ∧
      conjClosure K T = K ⊔ K.map (MulAut.conj t').toMonoidHom ∧
      ∀ s ∈ T, s ∈ Subgroup.normalizer (K : Set G) ∨
        K.map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj t').toMonoidHom := by
  classical
  have h := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  have hTH : T ≤ H := c.inH.1
  have hK := c.K_comp
  have hO := c.O
  have hTK := c.TK
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := c.isSylowTwoOf_H₀
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set H₀ := H ⊔ D with hH₀
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKc hO
  have h37Q := h37 _ hQ
  have h38Q := h38 _ hQ
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  set Ab := modO2Image H₀ K with hAb
  set Tb := modO2Image H₀ T with hTbdef
  have hAbc : Ab ∈ cComp (⊤ : Subgroup _) := modO2Image_mem_cComp hK
  have hTb : IsSylowTwoOf Tb ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective _)
      (isSylowTwoOf_top_subgroupOf hT₀)
  obtain ⟨-, hT38⟩ := h38Q Ab hAbc
  rcases hT38 Tb hTb with ⟨hnorm, -, -⟩ |
      ⟨tb, htb, htbn, hconjT, -, hcomm, hinf, hTbN, hsupT⟩
  · exfalso
    apply hTK
    intro t ht
    have htH : t ∈ H₀ := hTH₀ ht
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩).trans ?_
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  set Ab' := Ab.map (MulAut.conj tb).toMonoidHom with hAb'
  have hne : Ab ≠ Ab' := fun h1 => htbn (A38.map_conj_eq_iff.mp h1.symm)
  obtain ⟨⟨t₀, ht₀H⟩, ht₀T, rfl⟩ := htb
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H₀ := map_conj_mem_cComp hK ht₀H
  have hK'b : modO2Image H₀ K' = Ab' := modO2Image_conj ⟨t₀, ht₀H⟩
  have ht₀T' : t₀ ∈ T := ht₀T
  have hKK' : K ≠ K' := fun h1 => hne (by rw [← hK'b, ← h1])
  have hKK : conjClosure K T = K ⊔ K' := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (sup_le (le_conjClosure K T) ?_)
    · have htH : t ∈ H₀ := hTH₀ ht
      have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
      have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
        rw [modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩]
        exact ⟨π ⟨t, htH⟩, mk_mem_img _ ht, rfl⟩
      rw [hconjT] at h2
      have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
      rcases h2 with h2 | h2
      · rw [modO2Image_injOn H₀ h1 hK h2] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [Set.mem_singleton_iff, ← hK'b] at h2
        rw [modO2Image_injOn H₀ h1 hK'c h2] at hmem
        exact Subgroup.mem_sup_right hmem
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_conjClosure ht₀T' hk
  refine ⟨t₀, ht₀T', ?_, hK'c, hKK', hKK, ?_⟩
  · intro hn
    exact htbn (by
      have : (⟨t₀, ht₀H⟩ : ↥H₀) ∈ Subgroup.normalizer ((K.subgroupOf H₀ : Subgroup ↥H₀) : Set ↥H₀) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        have := Subgroup.mem_normalizer_iff.mp hn (x : G)
        simpa using this
      exact Subgroup.le_normalizer_map π ⟨_, this, rfl⟩)
  · intro s hs
    have hsH : s ∈ H₀ := hTH₀ hs
    have h1 : K.map (MulAut.conj s).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK hsH
    have h2 : modO2Image H₀ (K.map (MulAut.conj s).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
      rw [modO2Image_conj (H := H₀) (L := K) ⟨s, hsH⟩]
      exact ⟨π ⟨s, hsH⟩, mk_mem_img _ hs, rfl⟩
    rw [hconjT] at h2
    rcases h2 with h2 | h2
    · left
      exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
    · right
      rw [Set.mem_singleton_iff, ← hK'b] at h2
      exact modO2Image_injOn H₀ h1 hK'c h2

end CFSG.Quasithin.H13.NFConfig
