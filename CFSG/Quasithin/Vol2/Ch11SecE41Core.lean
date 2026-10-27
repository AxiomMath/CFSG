module

public import CFSG.Quasithin.Vol2.Ch11SecEBasic
public import CFSG.Quasithin.Vol2.Ch11SecB24Setup
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Vol2.Ch11SecE41One

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem relIndex_le_of_g2 (hG2L : FactG2LongRoot) (hG2 : SecA.FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hk : KindG2 L (fsuV T I) n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {E : Subgroup G}
    (hEV : E ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hE : IsElemAbelian 2 E)
    (hc : Nat.card ↥⁅fsuV T I, E⁆ ≤ 2 ^ (2 * n)) :
    (E ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex E ≤ 2 ^ n := by
  obtain ⟨_, -, -, -, hk'⟩ := h1102 G T L I n h
  have hn : 2 ≤ n := h.one_lt
  have hsq : ∀ x : ↥(fsuV T I), x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 x x.2)
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hnorm : ∀ e ∈ autOn E (fsuV T I), ∀ a ∈ autOn L (fsuV T I),
      e * a * e⁻¹ ∈ autOn L (fsuV T I) := by
    intro e he a ha
    obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp he
    obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp ha
    rw [← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp (hEL hx) y).mp hy) _
  have hcs : Nat.card (commSpace (autOn E (fsuV T I))) ≤ 2 ^ (2 * n) :=
    (card_commSpace_autOn_le E (fsuV T I)).trans hc
  rw [← card_autOn_eq_relIndex hEV]
  rcases hk' with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩ |
      ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
  · exact (SecA.kind_not_SL3_G2 hG2 hn ⟨K, inferInstance, inferInstance, hK, he⟩ hk).elim
  · exact (SecA.kind_not_Sp4_G2 hG2 hn ⟨K, inferInstance, inferInstance, hK, he⟩ hk).elim
  · rw [hZ] at hπ
    exact hG2L K n hn hK _ hsq _ π hπ _ (isElemAbelian_autOn _ hE) hnorm hcs

theorem false_of_g2_sp4 (hF : SecA.NatFacts) (hR2 : SecB.FactR2Gen) (hSp : FactSp4R2Big)
    (hG2L : FactG2LongRoot) (h331 : Stmt3_3_1) (hG2 : SecA.FactG2DerivedOrder)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1132 : Stmt11_3_2)
    {La Ia Lb Ib V₂a V₂b : Subgroup G} (ha : Hyp11 G T La Ia 2) (hb : Hyp11 G T Lb Ib 2)
    (hka : KindG2 La (fsuV T Ia) 2) (hkb : KindSp4 Lb (fsuV T Ib) 2)
    (hV₂a : IsVi T La Ia 2 2 V₂a) (hV₂b : IsVi T Lb Ib 2 2 V₂b)
    (hL₂ : LOf La V₂a = LOf Lb V₂b) (hLb : ¬ Lb ≤ Subgroup.normalizer (La : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₁a, hV₁a, -⟩ := (h1110 G T La Ia 2 ha).1 1 le_rfl (by norm_num)
  obtain ⟨V₁b, hV₁b, -⟩ := (h1110 G T Lb Ib 2 hb).1 1 le_rfl (by norm_num)
  have hcVa := cV_eq_bot h331 hG2 h1103 h1132 ha hV₁a
  have hcVb := cV_eq_bot h331 hG2 h1103 h1132 hb hV₁b
  have hVa := SecA.isElemAbelian_fsuV ha
  have hVb := SecA.isElemAbelian_fsuV hb
  obtain ⟨-, -, h3, h4, -, h5, -⟩ :=
    h1122 G T La Ia 2 4 V₁a V₂a ha hV₁a hV₂a (Or.inl ⟨hka, rfl⟩)
  have hs : E3.sParam hVa = 4 := h4 hVa
  have hr : ((4 : ℕ) : ℕ∞) < E3.rParam (fsuV T Ia) := by
    rcases h3 with h3 | ⟨hsl, -⟩
    · exact h3
    · exact (SecA.kind_not_SL3_G2 hG2 le_rfl hsl hka).elim
  obtain ⟨hW₀C, hW₀N, -⟩ := h5 hka
  have hW₀R : E3.wClos (fsuV T Ia) 0 T ≤ pCoreOf 2 (LOf Lb V₂b ⊔ T) := by
    rw [← hL₂]
    exact hW₀C.trans (inf_centralizer_le_pCoreOf_lOf h3228 ha V₂a)
  have hS : IsSylowIn 2 T (Lb ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hb.fsu.sylow le_sup_right
  have hW₀b : ¬ E3.wClos (fsuV T Ia) 0 T ≤ pCoreOf 2 (Lb ⊔ T) := by
    intro hle
    have hN := E3.e3_15_normalizer (V := fsuV T Ia) hS (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hle
    exact hLb ((le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)).trans
      (hN.trans hW₀N))
  obtain ⟨-, -, hOb⟩ := h3228 G T Lb Ib hb.fsu
  rw [SecA.fsuL0_eq hb] at hOb
  obtain ⟨g, hAT, hAC⟩ : ∃ g : G, conjSubgroup (fsuV T Ia) g ≤ T ∧
      ¬ conjSubgroup (fsuV T Ia) g ≤ Subgroup.centralizer (fsuV T Ib : Set G) := by
    by_contra hno
    push Not at hno
    apply hW₀b
    rw [hOb]
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hA0⟩ := hA
    have hAeq : A = conjSubgroup (fsuV T Ia) g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (SecA.isPGroup_fsuV ha) g) hAg).mp hA0
    subst hAeq
    exact le_inf hAT (hno g hAT)
  set A := conjSubgroup (fsuV T Ia) g with hAdef
  have hAR : A ≤ pCoreOf 2 (LOf Lb V₂b ⊔ T) :=
    (E3.le_wClos ⟨hAT, g, le_rfl, E3.mQuot_self _⟩).trans hW₀R
  have hAel : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hVa g
  have hsA : E3.sParam hAel = 4 := (E3.sParam_conj hVa g hAel).trans hs
  have hm : 4 ≤ E3.mQuot A (A ⊓ Subgroup.centralizer (fsuV T Ib : Set G)) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, -⟩ := E3.e3_6 hAel (inf_le_left : A ⊓ _ ≤ A) le_rfl (by rw [hsA]; exact hlt)
      (SecA.isPGroup_fsuV hb)
    apply hAC
    have hVbC : fsuV T Ib ≤ Subgroup.centralizer (A : Set G) := by
      intro v hv
      have hv' : v ∈ fsuV T Ib ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer (fsuV T Ib : Set G) : Subgroup G) : Set G) :=
        ⟨hv, Subgroup.mem_centralizer_iff.mpr fun a ha =>
          (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm⟩
      rw [← h1] at hv'
      exact hv'.2
    exact Subgroup.le_centralizer_iff.mp hVbC
  have hfl := flag24_of hF h331 h1102 hb (Or.inr hkb) hV₁b hV₂b
  obtain ⟨hcomm, hfix⟩ := hSp G Lb (fsuV T Ib) ⊤ T V₁b V₂b 2 hfl hkb hcVb A hAR hAel (by omega)
  have hgen := hR2 G Lb (fsuV T Ib) ⊤ T V₁b V₂b 2 hfl A hAR
  have hVbN : fsuV T Ib ≤ Subgroup.normalizer (A : Set G) := by
    refine hgen.trans (iSup₂_le fun B hB => inf_le_right.trans ?_)
    by_contra hC
    have h1 := E3.rParam_le_mQuot hB.1 hC
    rw [hAdef, E3.rParam_conj] at h1
    have h2 : E3.rParam (fsuV T Ia) ≤ ((4 : ℕ) : ℕ∞) :=
      h1.trans (by exact_mod_cast hB.2.trans (by norm_num))
    exact absurd hr (not_lt.mpr h2)
  set E := conjSubgroup (fsuV T Ib) g⁻¹ with hEdef
  have hVaA : conjSubgroup A g⁻¹ = fsuV T Ia := E3.conjSubgroup_conj_inv _ _
  have hEV : E ≤ Subgroup.normalizer (fsuV T Ia : Set G) := by
    have h1 := E3.conjSubgroup_mono_left g⁻¹ hVbN
    rwa [E3.conjSubgroup_normalizer, hVaA] at h1
  have hEL : E ≤ Subgroup.normalizer (La : Set G) := hEV.trans (SecA.normalizer_fsuV_le h331 ha)
  have hEel : IsElemAbelian 2 E := E3.isElemAbelian_conjSubgroup hVb g⁻¹
  have hV₂card : Nat.card V₂b = 2 ^ 4 := by
    have := SecA.IsVi.relIndex_eq hV₂b
    rwa [hcVb, Subgroup.relIndex_bot_left] at this
  have hVbcard : Nat.card (fsuV T Ib) = 2 ^ 8 := by
    have := SecB.relIndex_fsuV_of_Sp4 h1102 hb hkb
      (fun hg => SecA.kind_not_Sp4_G2 hG2 le_rfl hkb hg)
    rwa [hcVb, Subgroup.relIndex_bot_left] at this
  have hidx : V₂b.relIndex (fsuV T Ib) = 2 ^ 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ V₂b (fsuV T Ib) bot_le (SecA.IsVi.le_fsuV hV₂b)
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hV₂card, hVbcard] at h1
    have h2 : 2 ^ 4 * V₂b.relIndex (fsuV T Ib) = 2 ^ 4 * 2 ^ 4 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hcard : Nat.card ↥⁅fsuV T Ia, E⁆ ≤ 2 ^ (2 * 2) := by
    have h1 : ⁅fsuV T Ia, E⁆ = conjSubgroup ⁅A, fsuV T Ib⁆ g⁻¹ := by
      rw [E3.conjSubgroup_commutator, hVaA]
    rw [h1, E3.card_conjSubgroup, Subgroup.commutator_comm, hcomm, hV₂card]
  have hle := relIndex_le_of_g2 hG2L hG2 h1102 ha hka hcVa hEV hEL hEel hcard
  have hEC : E ⊓ Subgroup.centralizer (fsuV T Ia : Set G) =
      conjSubgroup (fsuV T Ib ⊓ Subgroup.centralizer (A : Set G)) g⁻¹ := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hVaA]
  rw [hEC, hEdef, E3.relIndex_conjSubgroup, hfix, hidx] at hle
  norm_num at hle

end CFSG.Quasithin.Vol2.Ch11.SecE
