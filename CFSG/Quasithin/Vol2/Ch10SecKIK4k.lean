module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.Vol2.Ch10SecKIK4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique


variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem b42_case5 (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L) (hA : IsFFStarOffender G A)
    (hc : B42Conclusion G L A) (hX : Nat.card ↥L = 2520) (hperf : commutator ↥L = ⊤)
    (hV64 : Nat.card V = 2 ^ 6) :
    ∃ π : Equiv.Perm (Fin 7) →* ↥(ffJ G), (FFModel.symDn 7).RealizesVia (ffJ G) ⊤ ⊥ π ∧
      ∃ T : Set (Equiv.Perm (Fin 7)), (∀ t ∈ T, t.IsSwap) ∧
        A.subgroupOf (ffJ G) = (Subgroup.closure T).map π := by
  have hLJ : L ≤ ffJ G := SecA.le_ffJ_of_two_dvd hV hB (SecA.two_dvd_card_ffJ hA)
  have hLdvd : 2520 ∣ Nat.card ↥(ffJ G) := hX ▸ Subgroup.card_dvd_of_le hLJ
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  rcases hc with ⟨-, ⟨n, K, _, _, hK, π, hR⟩, -, -⟩ | ⟨-, ⟨n, K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨n, hsp, hJ⟩, -⟩ | ⟨⟨n, hg2, -, hJ⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ | ⟨-, -, -, h16, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨π, hR⟩, -⟩ | ⟨-, -, -, -, π, hR, -⟩
  · exact (false_of_sl2 hK hX π hR.1).elim
  · exact (false_of_sl3 hK hX π hR.1).elim
  · exfalso
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le_of_card hK
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn : n = 1 := by omega
      subst hn
      rw [← Nat.card_congr e.toEquiv, SecA.card_Sp4_pow hK] at hLdvd
      norm_num at hLdvd
    · have e' : ↥(StatedSp 2 K) ≃* ↥L := e.trans (MulEquiv.subgroupCongr (hJ (by omega)))
      exact false_of_sp4 hK hX e'.toMonoidHom e'.surjective
  · exfalso
    obtain ⟨K, _, _, hK, π, hR⟩ := hg2
    have h1 := one_le_of_card hK
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn : n = 1 := by omega
      subst hn
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL) h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := SecA.factG2TwoNormal_holds K (by rw [hK]; norm_num) _ π hR.1 _ hLn hq
      rw [Nat.card_congr eL.toEquiv, hX] at h6048
      norm_num at h6048
    · let e : ↥(ffJ G) ≃* ↥L := MulEquiv.subgroupCongr (hJ (by omega))
      exact false_of_g2 hK hX hperf (e.toMonoidHom.comp π) (e.surjective.comp hR.1)
  · obtain ⟨⟨n, hn, π, hR, T, hT, -, hAT⟩, -⟩ := h5
    rcases hn with rfl | rfl
    · exfalso
      have hd := Subgroup.card_dvd_of_surjective hR.1
      have h120 : Nat.card (FFModel.symDn 5).Gam = 120 := by
        show Nat.card (Equiv.Perm (Fin 5)) = 120
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      rw [h120] at hd
      have := Nat.le_of_dvd (by norm_num) (hLdvd.trans hd)
      omega
    · exact ⟨π, hR, T, hT, hAT⟩
  · exact (false_of_alt (n := 6) (by norm_num) (by norm_num) hX π hR.1).elim
  · exfalso
    rw [hV64] at h16
    norm_num at h16
  · exact (false_of_hat6 hhat hX π hR.1).elim
  · exact (false_of_sl45 hn (by rw [hK]; norm_num) hX π hR.1).elim
  · exact (false_of_sl45' (Or.inl rfl) hX π hR.1).elim
  · exact (false_of_sl45' (Or.inr rfl) hX π hR.1).elim

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
