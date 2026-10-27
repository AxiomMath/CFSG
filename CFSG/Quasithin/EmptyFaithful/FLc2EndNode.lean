module

public import CFSG.Quasithin.Background.FLc2Par
public import CFSG.Quasithin.Background.FLcR2C
public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.FLcP0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15129EndNode_holds : Input15129EndNode := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF t ht
  left
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn : n = 4 ∨ n = 5 := hF.n_eq
  have hn4 : 4 ≤ n := by rcases hn with h | h <;> omega
  have h18 := hc.base.h18
  have h25 := hc.base.h25
  have h28 := hc.h28
  have hM := hc.base.ctx.mf
  set S : Subgroup G := s1516 T Z₁ with hSdef
  set P2 : Subgroup G := FLc.parab (L ⊔ S) n W 2 with hP2def
  change conjByElt t (oTwoUpper P2) = oTwoUpper P2
  have hTN : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G) :=
    (hc.base.ctx.setting.extra_small (Or.inl hF.four)).s_normal
  have hTS : conjByElt t S = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN ht)
  have hTS' : conjByElt t⁻¹ S = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN (T.inv_mem ht))
  have hSP2 : S ≤ P2 := D.S_le_parab 2
  have hsyl2 : IsSylowTwoOf S P2 := FLc.isSylowTwoOf_restrict D.syl hSP2 (FLc.parab_le _ _ _ _)
  have hP2eq : P2 = oTwoUpper P2 ⊔ S := eq_oTwoUpper_sup_of_isSylowTwoOf hsyl2
  have hLN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hF.normalizes
  have hO2L : oTwoUpper (L ⊔ S) ≤ L :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLN) D.S2 le_sup_right le_rfl
  have hML1 : mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    h28.2.2.1
  have hML2 : mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := h28.2.2.2
  have hZt : ∀ z ∈ quasithinOmegaOneCenter T, z * t = t * z := by
    intro z hz
    have hzc : z ∈ centerOf T := quasithinOmegaOneCenter_le_center T hz
    exact (Subgroup.mem_centralizer_iff.1 hzc.2 t ht).symm
  have hgen : ∀ x ∈ P2, Odd (orderOf x) →
      t * x * t⁻¹ ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro x hx hodd
    have hxX : x ∈ L ⊔ S := FLc.parab_le _ _ _ _ hx
    have hxL : x ∈ L := hO2L (Subgroup.subset_closure ⟨hxX, hodd⟩)
    have hxN : x ∈ Subgroup.normalizer (W 1 : Set G) :=
      (FLc.mem_parab.1 hx).2 1 le_rfl (by omega) (by omega)
    rw [hF.w1] at hxN
    have hxM : x ∈ mZ1516 Mc Z₁ ⊓ L := by
      rw [hML2]
      exact ⟨hxL, hxN⟩
    have hxC : x ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [← hML1]
      exact hxM
    have hxZ : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hxC.2
    have htxC : t * x * t⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h1 : z * t = t * z := hZt z hz
      have h2 : z * x = x * z := Subgroup.mem_centralizer_iff.1 hxZ z hz
      calc z * (t * x * t⁻¹) = (z * t) * x * t⁻¹ := by group
        _ = t * (z * x) * t⁻¹ := by rw [h1]; group
        _ = t * (x * z) * t⁻¹ := by rw [h2]
        _ = t * x * (z * t⁻¹) := by group
        _ = t * x * t⁻¹ * z := by
          have h3 : z * t⁻¹ = t⁻¹ * z := by
            calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
              _ = t⁻¹ * (z * t) * t⁻¹ := by rw [h1]
              _ = t⁻¹ * z := by group
          rw [h3]; group
    have hord : orderOf (t * x * t⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective x
      simpa [MulAut.conj_apply] using this
    have hodd' : Odd (orderOf (t * x * t⁻¹)) := by rw [hord]; exact hodd
    have hdvd : orderOf (t * x * t⁻¹) ∣ 3 := by
      rw [hord]
      exact D.odd_dvd_three_two hn4 hx hodd
    have hG1 : t * x * t⁻¹ ∈ g1_1516 Z₁ :=
      mZ1516_le_g1 Mc Z₁ (h18.one.2 (Subgroup.subset_closure ⟨htxC, hodd'⟩))
    have hL3 : t * x * t⁻¹ ∈ L := by
      rw [h25.one]
      refine Subgroup.subset_closure ⟨hG1, ?_⟩
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact ⟨hL3, htxC⟩
  have hYt : conjByElt t (oTwoUpper P2) ≤
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    unfold conjByElt
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have := hgen x hx.1 hx.2
    simpa [MulAut.conj_apply] using this
  have hP'eq : conjByElt t P2 = conjByElt t (oTwoUpper P2) ⊔ S := by
    conv_lhs => rw [hP2eq]
    unfold conjByElt at hTS ⊢
    rw [Subgroup.map_sup, hTS]
  have hSP' : S ≤ conjByElt t P2 := by
    rw [hP'eq]
    exact le_sup_right
  have hP'X : conjByElt t P2 ≤ L ⊔ S := by
    rw [hP'eq]
    exact sup_le (hYt.trans (inf_le_left.trans le_sup_left)) le_sup_right
  have hP'N : conjByElt t P2 ≤ Subgroup.normalizer (W 1 : Set G) := by
    rw [hP'eq]
    refine sup_le ?_ (D.W_norm 1 le_rfl (by omega))
    intro y hy
    have hyL : y ∈ mZ1516 Mc Z₁ ⊓ L := by
      rw [hML1]
      exact hYt hy
    rw [hML2] at hyL
    rw [hF.w1]
    exact hyL.2
  obtain ⟨hne2, hmin2⟩ := D.minimal_parab (a := 2) ⟨by norm_num, by omega⟩
  have hP'ne : conjByElt t P2 ≠ S := by
    intro h
    apply hne2
    have := congrArg (conjByElt t⁻¹) h
    rwa [← conjByElt_mul1516, inv_mul_cancel, conjByElt_one1516, hTS'] at this
  have hP'min : ∀ K : Subgroup G, S ≤ K → K ≤ conjByElt t P2 →
      K = S ∨ K = conjByElt t P2 := by
    intro K hSK hKP
    have h1 : S ≤ conjByElt t⁻¹ K := by
      rw [← hTS']
      exact Subgroup.map_mono hSK
    have h2 : conjByElt t⁻¹ K ≤ P2 := by
      have e : conjByElt t⁻¹ (conjByElt t P2) = P2 := by
        rw [← conjByElt_mul1516, inv_mul_cancel, conjByElt_one1516]
      calc conjByElt t⁻¹ K ≤ conjByElt t⁻¹ (conjByElt t P2) := Subgroup.map_mono hKP
        _ = P2 := e
    rcases hmin2 _ h1 h2 with h | h
    · left
      have := congrArg (conjByElt t) h
      rwa [← conjByElt_mul1516, mul_inv_cancel, conjByElt_one1516, hTS] at this
    · right
      have := congrArg (conjByElt t) h
      rwa [← conjByElt_mul1516, mul_inv_cancel, conjByElt_one1516] at this
  obtain ⟨a, ha, hPa⟩ := D.exists_parab_of_minimal hSP' hP'X hP'ne hP'min
  have ha1 : a ≠ 1 := by
    intro h
    subst h
    exact D.not_parab_le_normalizer (hPa ▸ hP'N)
  have ha2 : a = 2 := by
    by_contra hne
    have ha3 : 3 ≤ a := by
      have := ha.1
      omega
    have hQCS := cs15129 G T Mc M Z₁ Z₂ V₁ V₂ L hc hF.four
    have hTM : T ≤ M := hM.1.1.2
    have hQT : T ≤ Subgroup.normalizer
        (pCoreOf 2 (FLc.parab (L ⊔ S) n W 1) : Set G) := by
      rw [D.pCoreOf_eq, hF.w2, hQCS]
      have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
        hTM.trans (le_normalizer_V154 T Mc M)
      have hTC := hTV.trans (normalizer_le_normalizer_centralizer (V154 T Mc M))
      exact fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hTC hx⟩
    have hrank := D.rank2_a_node ha3 ha.2
    apply D.rank2_b hn
    intro x hx
    have hx' : t * x * t⁻¹ ∈ pCoreOf 2 (oTwoUpper (conjByElt t P2)) := by
      have e : oTwoUpper (conjByElt t P2) = conjByElt t (oTwoUpper P2) :=
        oTwoUpper_map (MulAut.conj t).toMonoidHom P2
      rw [e, conjByElt, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t)]
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [hPa] at hx'
    exact (Subgroup.mem_normalizer_iff.mp (hQT ht) x).mpr (hrank hx')
  subst ha2
  have e : oTwoUpper (conjByElt t P2) = conjByElt t (oTwoUpper P2) :=
    oTwoUpper_map (MulAut.conj t).toMonoidHom P2
  rw [← e, hPa]

end CFSG.Quasithin
