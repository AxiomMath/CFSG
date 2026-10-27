module

public import CFSG.Quasithin.EmptyFaithful.FLcMLE
public import CFSG.Quasithin.Background.FLcMLEMat
public import CFSG.Quasithin.Background.FLcLn
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem input15120MLECent_holds : Input15120MLECent := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hE
  obtain ⟨n, hn, e₀⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty (↥L ≃* FLc.SLt n) := by
    rcases hE with h | h
    · exact ⟨4, Or.inl rfl, FLc.nonempty_equiv_SLt_of_isPSL h⟩
    · exact ⟨5, Or.inr rfl, FLc.nonempty_equiv_SLt_of_isPSL h⟩
  obtain ⟨e₀⟩ := e₀
  have hn3 : 3 ≤ n := by omega
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  obtain ⟨D⟩ := FLc.exists_borelIso (by omega) hSyl e₀
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ctx.qtfe.omegaOneCenter_ne_bot
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hyp := hc.h18.six z hzZ hz1
  have hzS : z ∈ s1516 T Z₁ := hyp.z_mem
  have hzC : z ∈ Subgroup.centralizer (s1516 T Z₁ : Set G) := hyp.z_central
  have hzG : z ∈ g1_1516 Z₁ := hyp.z_mem_H
  have hzcz : Subgroup.centralizer ({z} : Set G) ≤ Mc := hyp.centralizer_z_le
  have hzB : ∀ x ∈ s1516 T Z₁, z * x * z⁻¹ = x := fun x hx => by
    have h := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [← h]
    group
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := by
    have hconjG : (g1_1516 Z₁).map (MulAut.conj z).toMonoidHom = g1_1516 Z₁ := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem hzG hv) ((g1_1516 Z₁).inv_mem hzG)
      · intro hw
        refine ⟨z⁻¹ * w * z, (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem
          ((g1_1516 Z₁).inv_mem hzG) hw) hzG, ?_⟩
        show z * (z⁻¹ * w * z) * z⁻¹ = w
        group
    have hsub : IsSubnormal (L.map (MulAut.conj z).toMonoidHom) (g1_1516 Z₁) := by
      have h1 := A3.subnormal_map (MulAut.conj z).toMonoidHom hcomp.2.1
      rwa [hconjG] at h1
    rcases B113.component_le_or_commutator_eq_bot hcomp hsub with hle | hcomm
    · have hcard : Nat.card ↥(L.map (MulAut.conj z).toMonoidHom) = Nat.card ↥L :=
        Subgroup.card_map_of_injective (MulAut.conj z).injective
      have heq : L = L.map (MulAut.conj z).toMonoidHom :=
        Subgroup.eq_of_le_of_card_ge hle hcard.le
      exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
    · exfalso
      have hE01 : FLc.E01 n hn3 ∈ FLc.Ut n := FLc.tv_mem_Ut _
      rw [← D.hB] at hE01
      obtain ⟨b, hb, hbe⟩ := hE01
      have hbS : (b : G) ∈ s1516 T Z₁ := (Subgroup.mem_subgroupOf.1 hb).1
      have hbL : (b : G) ∈ L := b.2
      have hbLz : (b : G) ∈ L.map (MulAut.conj z).toMonoidHom :=
        ⟨b, hbL, by show z * (b : G) * z⁻¹ = b; exact hzB _ hbS⟩
      have hcent : ∀ h : ↥L, h * b = b * h := by
        intro h
        have hLC : L ≤ Subgroup.centralizer ((L.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
        have := Subgroup.mem_centralizer_iff.1 (hLC h.2) (b : G) hbLz
        exact Subtype.ext this.symm
      have hb1 : b = 1 := FLc.center_trivial_of_equiv D.e hcent
      apply FLc.E01_ne_one hn hn3
      rw [← hbe, hb1, map_one]
  have hφfix : ∀ u ∈ FLc.Ut n, D.autOf z hzN u = u := by
    intro u hu
    rw [← D.hB] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have hxS : (x : G) ∈ s1516 T Z₁ := (Subgroup.mem_subgroupOf.1 hx).1
    have hx' : L.normalizerMonoidHom ⟨z, hzN⟩ x = x := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hzB _ hxS
    show D.autOf z hzN (D.e x) = D.e x
    rw [D.autOf_e, hx']
  have hφU : (FLc.Ut n).map (D.autOf z hzN).toMonoidHom = FLc.Ut n := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hφfix u hu]
      exact hu
    · intro hg
      exact ⟨g, hg, hφfix g hg⟩
  rcases FLc.aut_dichotomy hn3 (D.autOf z hzN) hφU with ⟨b, hbU, hbφ⟩ | hswap
  ·
    have hbU' := hbU
    rw [← D.hB] at hbU'
    obtain ⟨b', hb', hbe⟩ := hbU'
    have hb'S : (b' : G) ∈ s1516 T Z₁ ⊓ L := hb'
    have hb'cent : (b' : G) ∈ Subgroup.centralizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      let x' : ↥L := ⟨x, hx.2⟩
      have hx'B : x' ∈ (s1516 T Z₁ ⊓ L).subgroupOf L := hx
      have h1 : D.e x' ∈ FLc.Ut n := by
        rw [← D.hB]
        exact ⟨x', hx'B, rfl⟩
      have h2 := hbφ (D.e x')
      rw [hφfix _ h1, ← hbe] at h2
      have h3 : D.e (b' * x' * b'⁻¹) = D.e x' := by
        rw [map_mul, map_mul, map_inv]
        exact h2.symm
      have h4 : b' * x' * b'⁻¹ = x' := D.e.injective h3
      have h5 : (b' : G) * x * (b' : G)⁻¹ = x := congrArg Subtype.val h4
      rw [mul_inv_eq_iff_eq_mul] at h5
      exact h5.symm
    intro x hx
    obtain ⟨hxL, hxC⟩ := hx
    refine ⟨⟨hcomp.1 hxL, hzcz ?_⟩, hxL⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    let x' : ↥L := ⟨x, hxL⟩
    have h1 := hbφ (D.e x')
    rw [D.autOf_e, ← hbe] at h1
    have h2 : L.normalizerMonoidHom ⟨z, hzN⟩ x' = b' * x' * b'⁻¹ := by
      apply D.e.injective
      rw [h1, map_mul, map_mul, map_inv]
      rfl
    have h3 : z * x * z⁻¹ = (b' : G) * x * (b' : G)⁻¹ := by
      have := congrArg Subtype.val h2
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
      exact this
    have hxb : (b' : G) * x = x * (b' : G) :=
      Subgroup.mem_centralizer_iff.1 hxC (b' : G) ⟨hb'S, hb'cent⟩
    have h4 : (b' : G) * x * (b' : G)⁻¹ = x := by
      rw [hxb]
      group
    rw [h4] at h3
    have h5 : z * x = x * z := calc
      z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [h3]
    exact h5.symm
  · exact (FLc.no_swap_of_fixes hn _ hφfix hswap).elim

theorem input15120MLE_holds : Input15120MLE := input15120MLE_of_cent input15120MLECent_holds

end CFSG.Quasithin
