module

public import CFSG.Quasithin.Background.S1567Gen
public import CFSG.Quasithin.Background.S1567Ctx
public import CFSG.Quasithin.Background.C1PackS15368

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section Gen

variable {G : Type*} [Group G]

theorem le_normalizer_closure_of_conj {S : Set G} {H : Subgroup G}
    (hS : ∀ g ∈ H, ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    H ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ k ∈ H, ∀ y ∈ Subgroup.closure S, k * y * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hS k hk x hx
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (Subgroup.closure S).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (Subgroup.closure S).inv_mem ih
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (H.inv_mem hg) _ hy
  simpa [mul_assoc] using this

@[expose] def oTwoThreeUpper (M : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ M ∧ Nat.Coprime (orderOf x) 6}

theorem oTwoThreeUpper_le (M : Subgroup G) : oTwoThreeUpper M ≤ M :=
  (Subgroup.closure_le M).mpr fun _ hx => hx.1

theorem odd_orderOf_of_coprime_six {x : G} (h : Nat.Coprime (orderOf x) 6) : Odd (orderOf x) := by
  have h2 : Nat.Coprime (orderOf x) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  exact Nat.odd_iff.mpr (by
    rcases Nat.even_or_odd (orderOf x) with he | ho
    · exfalso
      have : 2 ∣ orderOf x := even_iff_two_dvd.mp he
      have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) this
      omega
    · exact Nat.odd_iff.mp ho)

theorem oTwoThreeUpper_le_closure_odd (M : Subgroup G) :
    oTwoThreeUpper M ≤ Subgroup.closure {x | x ∈ oTwoThreeUpper M ∧ Odd (orderOf x)} :=
  Subgroup.closure_mono fun _ hx => ⟨Subgroup.subset_closure hx, odd_orderOf_of_coprime_six hx.2⟩

theorem normalizer_le_normalizer_oTwoThreeUpper (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (oTwoThreeUpper M : Set G) := by
  refine le_normalizer_closure_of_conj fun g hg x hx => Subgroup.subset_closure ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2

end Gen

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem charTwo_M (h : Hyp153 G T Mc M) :
    M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M := by
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  exact h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hS ▸ h.T_le⟩

theorem normalizer_V_eq (h : Hyp153 G T Mc M) :
    Subgroup.normalizer (VZ T M : Set G) = M :=
  (h.isHv_of_inM' h.inM).symm

theorem centralizer_of_coprime (h : Hyp153 G T Mc M) {x : G} (hx : x ∈ M)
    (hc : Nat.Coprime (orderOf x) 6) : x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  obtain ⟨q, L₁, L₂, tb, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hx
  set y : MulAut (IntMod (VZ T M) hV) := convI hV ⟨x, hxN⟩ with hy
  have hyX : y ∈ autI hV M := convI_mem_autI hV hx hxN
  have h1 : orderOf y ∣ orderOf x := by
    have := orderOf_map_dvd (convI hV) (⟨x, hxN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G)))
    simpa [Subgroup.orderOf_coe] using this
  have h2 : orderOf y ∣ 72 := by
    have := orderOf_dvd_natCard (⟨y, hyX⟩ : ↥(autI hV M))
    rw [hS.card_X] at this
    simpa [Subgroup.orderOf_coe] using this
  have hcy : Nat.Coprime (orderOf y) 6 := Nat.Coprime.of_dvd_left h1 hc
  have h3 : orderOf y = 1 :=
    (Nat.Coprime.pow_right 3 hcy).eq_one_of_dvd (h2.trans (by norm_num : 72 ∣ 6 ^ 3))
  have h4 : y = 1 := orderOf_eq_one_iff.mp h3
  exact (convI_eq_one_iff hV ⟨x, hxN⟩).1 h4

theorem conj_mem_of_index (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3)
    {g x : G} (hg : g ∈ Subgroup.normalizer (E : Set G)) (hx : x ∈ M)
    (hc : Nat.Coprime (orderOf x) 6) : g * x * g⁻¹ ∈ M ∧ Nat.Coprime (orderOf (g * x * g⁻¹)) 6 := by
  have hxV := centralizer_of_coprime k.c.hyp hx hc
  have hxE : x ∈ Subgroup.centralizer (E : Set G) := Subgroup.centralizer_le k.L.le_V hxV
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hxE
  have := conj_mem_of_relIndex_three (inf_le_right : M ⊓ Subgroup.normalizer (E : Set G) ≤ _) hidx
    (x := x) ⟨hx, hxN⟩ hc hg
  refine ⟨this.1, ?_⟩
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact hc

theorem oTwoThreeUpper_eq_bot (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    oTwoThreeUpper M = ⊥ := by
  have h := k.c.hyp
  refine eq_bot_of_normalized_by_max_two_local (K := Subgroup.normalizer (E : Set G)) h.inM.1
    (charTwo_M h) k.L.not_le_M (oTwoThreeUpper_le M) ?_ ?_ (oTwoThreeUpper_le_closure_odd M)
  · exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoThreeUpper M)
  · refine le_normalizer_closure_of_conj fun g hg x hx => ?_
    exact Subgroup.subset_closure (conj_mem_of_index k hidx hg hx.1 hx.2)

theorem twoThree_M (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    C1Pack153.TwoThree M := by
  intro p hp hpd
  by_contra hne
  have hp2 : p ≠ 2 := fun h => hne (Or.inl h)
  have hp3 : p ≠ 3 := fun h => hne (Or.inr h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) p hpd
  have hxM : (x : G) ∈ M := x.2
  have hord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hcop : Nat.Coprime p 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h23 : p ∣ 2 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  have hmem : (x : G) ∈ oTwoThreeUpper M := Subgroup.subset_closure ⟨hxM, hord ▸ hcop⟩
  rw [oTwoThreeUpper_eq_bot k hidx, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hord
  exact hp.one_lt.ne hord

theorem isPGroup_two_of_twoThree {K : Subgroup G} (h23 : C1Pack153.TwoThree K)
    (h3 : ¬ 3 ∣ Nat.card K) : IsPGroup 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne fun {p} hp hpd => ?_)
  rcases h23 p hp hpd with h | h
  · exact h
  · exact absurd (h ▸ hpd) h3

theorem centralizer_V_le_T (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Subgroup.centralizer (VZ T M : Set G) ≤ T := by
  have h := k.c.hyp
  have hCM : Subgroup.centralizer (VZ T M : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans (normalizer_V_eq h).le
  have h23 : C1Pack153.TwoThree (Subgroup.centralizer (VZ T M : Set G)) :=
    (twoThree_M k hidx).mono hCM
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer (VZ T M : Set G)) := by
    have := k.r49.threePrime_C
    rwa [IsThreePrimeGroup, inf_eq_right.mpr hCM] at this
  have hp2 := isPGroup_two_of_twoThree h23 h3
  have hnorm : M ≤ Subgroup.normalizer (Subgroup.centralizer (VZ T M : Set G) : Set G) :=
    B2F.le_normalizer_centralizer h.le_normalizer
  exact A4.le_of_normal_of_isSylowTwoOf h.isSylowTwoOf hCM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr hnorm) hp2

theorem R_eq_of_index (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) = Subgroup.centralizer (VZ T M : Set G) :=
  inf_eq_right.mpr (centralizer_V_le_T k hidx)

theorem M_eq_of_index (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    M = Y153 Mc M ⊔ T := by
  have h := k.c.hyp
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  obtain ⟨q, L₁, L₂, tb, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hsyl := h.isSylowTwoOf_autI
  have hYM : Y153 Mc M ⊔ T ≤ M := sup_le (Y153_le Mc M) h.T_le
  refine le_antisymm ?_ hYM
  have hbar : autI hV (Y153 Mc M ⊔ T) = autI hV M := by
    rw [autI_sup hV ((Y153_le Mc M).trans hMN) (h.T_le.trans hMN)]
    have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
    rw [e]
    exact hS.sup_oTwoUpper_eq hsyl
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hm
  have hmbar : convI hV ⟨m, hmN⟩ ∈ autI hV (Y153 Mc M ⊔ T) := hbar ▸ convI_mem_autI hV hm hmN
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hmbar
  have hc1 : convI hV (g⁻¹ * ⟨m, hmN⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
  have hcC : (g : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (convI_eq_one_iff hV _).1 hc1
  have hcT : (g : G)⁻¹ * m ∈ T := centralizer_V_le_T k hidx hcC
  have e : m = (g : G) * ((g : G)⁻¹ * m) := by group
  rw [e]
  exact (Y153 Mc M ⊔ T).mul_mem hgY ((le_sup_right : T ≤ Y153 Mc M ⊔ T) hcT)

end Main

end S1567

end CFSG.Quasithin
