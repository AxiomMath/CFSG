module

public import CFSG.Quasithin.H13.A5W1622x
public import CFSG.Quasithin.H13.A5W1620Ta

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_cases_L32
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    [hsP : IsSimpleGroup ↥(S.plus K)] (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a)
    (h168 : Nat.card ↥(S.plus K) = 168) :
    IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) ∨
      A36Case3 ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set X := modO2Image Gv K with hX
  obtain ⟨ρ, θ, hρs, hθs, hρ1, hθk⟩ := S.exists_rho_theta h1222 h517 hF hK hYz hT hna
  have hnt : Nontrivial ↥(S.plus K) := IsSimpleGroup.toNontrivial
  have hZP : Subgroup.center ↥(S.plus K) = ⊥ := by
    rcases hsP.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(S.plus K)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hbot : θ.ker = ⊥ →
      IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
    intro h
    rintro ⟨k, hkK, hkC⟩
    have h1 : ρ ⟨k, hkK⟩ ∈ θ.ker := (hθk ⟨k, hkK⟩).mpr hkC
    rw [h, Subgroup.mem_bot] at h1
    obtain ⟨n, hn⟩ := hρ1 _ h1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hcardX : Nat.card ↥X = Nat.card ↥θ.ker * 168 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv, h168, mul_comm]
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF) hK
  rcases hA with ⟨-, hsimp, -⟩ | ⟨hcomp, h3, hlist⟩ | h3 | h4
  ·
    left
    refine hbot ?_
    rcases hsimp.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      obtain ⟨x, rfl⟩ := hθs a
      obtain ⟨y, rfl⟩ := hθs b
      have hx : θ x = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
      have hy : θ y = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y)
      exact hab (by rw [hx, hy])
  ·
    exfalso
    have hker1 : θ.ker ≤ Subgroup.center ↥X := ker_le_center_of_isQuasisimple hcomp.1 θ hθs hnt
    have hker2 : Subgroup.center ↥X ≤ θ.ker := by
      intro x hx
      have h1 : θ x ∈ Subgroup.center ↥(S.plus K) := Subgroup.map_center_le_center hθs ⟨x, hx, rfl⟩
      rw [hZP, Subgroup.mem_bot] at h1
      exact h1
    have hkerZ : θ.ker = Subgroup.center ↥X := le_antisymm hker1 hker2
    have h504 : Nat.card ↥X = 504 := by rw [hcardX, hkerZ, h3]
    have hQZ : Nat.card (↥X ⧸ Subgroup.center ↥X) = 168 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
      rw [h504, h3] at h1
      omega
    rcases hlist with ⟨s, p, e, hp, he, -, hSL⟩ | ⟨-, -, ⟨e6⟩⟩ | ⟨-, -, ⟨e7⟩⟩ | ⟨-, -, ⟨e22⟩⟩
    ·
      have hq2 : 2 ≤ p ^ e := by
        calc 2 ≤ p := hp.two_le
          _ ≤ p ^ e := Nat.le_self_pow (by omega) p
      cases s
      · obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
        have h2 := card_statedSU_three_of hK'
        rw [← Nat.card_congr eK.toEquiv, h504] at h2
        exact (sl3_su3_card_ne hq2 (Or.inl rfl)).2 h2.symm
      · obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
        have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
        rw [← Nat.card_congr eK.toEquiv, h504, hK'] at h2
        exact (sl3_su3_card_ne hq2 (Or.inl rfl)).1 h2.symm
    · rw [Nat.card_congr e6.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩] at hQZ
      omega
    · have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      rw [Nat.card_congr e7.toEquiv, h2520] at hQZ
      omega
    · have h22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
        CFSG.Sporadic.Mathieu.card_M22
      rw [Nat.card_congr e22.toEquiv, h22] at hQZ
      omega
  · exact Or.inr h3
  ·
    exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥X) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥X))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥X := by
      ext x
      simp [ψ₄]
    have hq := S.isQuasisimple_plus h1222 h517 hF hYz hT
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq θ hθs hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rw [Nat.card_congr (quotCenterEquivOfEqBot hZP).toEquiv, h168] at hcard
    omega

theorem exists_reduced_L32
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) [hsP : IsSimpleGroup ↥(S.plus K)]
    (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a) (h168 : Nat.card ↥(S.plus K) = 168) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧ K₀ ∈ lFamily S.Tv ∧ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) ∧
      S.Lv ≤ Subgroup.normalizer (K₀ : Set G) ∧ autOn K₀ (S.WK K) = S.plus K ∧
      IsPGroup 2 ↥(K₀ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
  rcases S.kbar_cases_L32 h1222 h517 hF h36 hK hYz hT hna h168 with h2 | h3
  · exact ⟨K, le_rfl, hYz.2.1, hT, S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hK, rfl,
      h2⟩
  · exact S.exists_reduced_of_case3 h1222 h517 hF h37 h38 hK hYz hT hna h168 h3

end Setting

end CFSG.Quasithin.H13.A5
