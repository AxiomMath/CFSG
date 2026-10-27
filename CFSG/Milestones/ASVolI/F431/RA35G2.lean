module

public import CFSG.Milestones.ASVolI.F431.RA35Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2LocMap
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.ATop

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section G2Two

set_option linter.unusedSectionVars false


theorem burnsideF4r_G2Data_not_isConj {G : Type} [Group G] [Finite G] {z : G}
    {T Q Tp : Subgroup G} (D : G2Two.G2Data G z T Q Tp) {v : G} (hvQ : v ∈ Q) (hvTp : v ∉ Tp)
    (hv2 : v * v = 1) : ¬ IsConj z v := by
  have hvne : v ≠ z := fun h => hvTp (h ▸ D.z_mem)
  refine G2Two.not_isConj_of_nf (O := fun v => v ∈ Q ∧ v ∉ Tp ∧ v * v = 1) D.z_sq D.z_ne
    D.T_syl D.Q_le D.T_card D.Q_card D.Q_norm D.Q_comm
    (fun A hAQ hA => G2Two.card_abelian_le_eight D.Q_card D.Q_comm D.Q_Z hAQ hA) ?_ ?_
    ⟨hvQ, hvTp, hv2⟩ hvQ hvne (D.out_pair v hvQ hvTp hv2)
  · rintro h hh w ⟨hwQ, hwTp, hw2⟩
    refine ⟨D.Q_norm h hh w hwQ, fun hmem => hwTp ((D.Tp_norm h hh w hwQ).2 hmem), ?_⟩
    calc h * w * h⁻¹ * (h * w * h⁻¹) = h * (w * w) * h⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · rintro w ⟨hwQ, hwTp, hw2⟩
    exact D.out_t w hwQ hwTp hw2

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4r_G2_nonfused (hyp : HypF_4_31 .G2 f Gp M₁ M₂ β ε z) (hf : f < 2) :
    ∃ v : ↥(M₁ ⊓ M₂), (v : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ∧ v ≠ 1 ∧ v * v = 1 ∧
      ¬ IsConj z (bM β ε v) := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  obtain rfl : f = 1 := by omega
  have hGp : Gp = ⊤ := burnsideF4m_top_G2two hyp.amalgam
  obtain ⟨x, hxZ, hxz, hx1, hx2⟩ := burnsideF4r_zbar hyp (by decide)
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  rcases chart.coordinates with ⟨c, hk, -⟩ |
      ⟨-, hp, hd, K, fK, finK, hcard, marking, h1, h2', h3, h4, h5⟩ |
      ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, e, K', fK', finK', charK', scope, hcase⟩
  · cases c <;> exact absurd hk (by decide)
  · have hcard' : Nat.card K = 2 := by simpa using hcard
    haveI := finK
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
      (by rw [← Nat.card_eq_fintype_card, hcard'])
    have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hcard'
    have hk2 : ∀ c : K, c = 0 ∨ c = 1 := eq_zero_or_eq_one_of_card_two hcard'
    have hψi := burnsideF4gG2TwoInv_psiC_injective marking
    set ψ := burnsideF4gG2TwoInv_psiC marking with hψdef
    have hle : ∀ X : Subgroup E, Gp ⊓ X = X := fun X => inf_eq_right.2 (hGp ▸ le_top)
    have hM1 : M₁ = (G2Native.pointParabolic K).map ψ := by
      rw [← hle M₁, hm.2.1, h2', burnsideF4gG2TwoInv_psiC_map marking]
    have hBo : M₁ ⊓ M₂ = (G2Native.positiveBorel K).map ψ := by
      rw [← hle (M₁ ⊓ M₂), hm.1, h1, burnsideF4gG2TwoInv_psiC_map marking]
    obtain ⟨h, hh⟩ := burnsideF4gG2TwoInv_borel_conj hcard' h2 hk2
    obtain ⟨hPc, -⟩ := burnsideF4gG2TwoInv_Pc_conj hcard' h2 hk2 hh
    have hcent := burnsideF4gG2TwoInv_P₂_cent hcard' h2 hk2 hh
    set L := CFSG.Quasithin.F6.G22Shape.lat h2 hk2 with hL
    have LL : G2Two.G2Loc L.P₂ (CFSG.Quasithin.F6.G22Perm.sEl h2 26) L.S
        (CFSG.Quasithin.F6.G22Shape.R2 h2 hk2) (G2Two.Model.TpSub h2 hk2) :=
      G2Two.Model.g2Loc h2 hk2
    set ψ' : G2Group K →* E := ψ.comp (MulAut.conj h⁻¹).toMonoidHom with hψ'def
    have hψ'apply : ∀ g, ψ' g = ψ (h⁻¹ * g * h) := fun g => by
      show ψ ((MulAut.conj h⁻¹) g) = _
      rw [MulAut.conj_apply, inv_inv]
    have hψ'i : Function.Injective ψ' := hψi.comp (MulAut.conj h⁻¹).injective
    have hP₂M₁ : ∀ {p : G2Group K}, p ∈ L.P₂ → ψ' p ∈ M₁ := by
      intro p hp
      rw [← hPc] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [hψ'apply, hM1]
      refine ⟨q, hq, ?_⟩
      show ψ q = ψ (h⁻¹ * (MulAut.conj h q) * h)
      rw [MulAut.conj_apply]
      congr 1
      group
    have hM₁P₂ : ∀ {m : E}, m ∈ M₁ → ∃ p ∈ L.P₂, ψ' p = m := by
      intro m hmM
      rw [hM1] at hmM
      obtain ⟨q, hq, rfl⟩ := hmM
      refine ⟨h * q * h⁻¹, ?_, ?_⟩
      · rw [← hPc]
        exact ⟨q, hq, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      · rw [hψ'apply]
        congr 1
        group
    have hSB : ∀ {s : G2Group K}, s ∈ L.S → ψ' s ∈ M₁ ⊓ M₂ := by
      intro s hs
      obtain ⟨b, hb, rfl⟩ := (hh s).1 hs
      rw [hψ'apply, hBo]
      exact ⟨b, hb, by congr 1; group⟩
    have hBS : ∀ {m : E}, m ∈ M₁ ⊓ M₂ → ∃ s ∈ L.S, ψ' s = m := by
      intro m hmM
      rw [hBo] at hmM
      obtain ⟨b, hb, rfl⟩ := hmM
      refine ⟨h * b * h⁻¹, (hh _).2 ⟨b, hb, rfl⟩, ?_⟩
      rw [hψ'apply]
      congr 1
      group
    have hBp : IsPGroup 2 (M₁ ⊓ M₂ : Subgroup E) := by
      rw [hBo]
      exact (burnsideF4gG2TwoInv_borel_sylow hcard').1.map ψ
    have hSeq : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = M₁ ⊓ M₂ := by
      rw [hle]
      exact burnsideF4gG2TwoInv_pCoreOf_eq_self hBp
    have hxB : (x : E) ∈ M₁ ⊓ M₂ := x.2
    obtain ⟨s₀, hs₀, hs₀x⟩ := hBS hxB
    have hs₀c : ∀ t ∈ L.S, t * s₀ = s₀ * t := by
      intro t ht
      apply hψ'i
      rw [map_mul, map_mul, hs₀x]
      have hxc := hxZ.2
      rw [hSeq] at hxc
      exact ((Subgroup.mem_centralizer_iff.mp hxc) (ψ' t) (hSB ht))
    have hs₀z : s₀ = CFSG.Quasithin.F6.G22Perm.sEl h2 26 := by
      rcases LL.T_Z s₀ hs₀ hs₀c with h0 | h0
      · exfalso
        apply hx1
        apply Subtype.ext
        rw [← hs₀x, h0, map_one]
        rfl
      · exact h0
    have hψ'z : ψ' (CFSG.Quasithin.F6.G22Perm.sEl h2 26) = (x : E) := by
      rw [← hs₀z, hs₀x]
    let ρ : ↥L.P₂ →* ↥M₁ := (ψ'.comp L.P₂.subtype).codRestrict M₁ (fun p => hP₂M₁ p.2)
    have hρ : ∀ p : ↥L.P₂, ((ρ p : ↥M₁) : E) = ψ' p := fun p => rfl
    have hρi : Function.Injective ρ := by
      intro a b hab
      apply Subtype.ext
      apply hψ'i
      have := congrArg Subtype.val hab
      rwa [hρ, hρ] at this
    let φ : ↥L.P₂ →* M := (burnsideF4d_bOne β ε).comp ρ
    have hφi : Function.Injective φ := (burnsideF4j_bOne_injective hyp).comp hρi
    have hbM : ∀ (p : ↥L.P₂) (hp : ψ' p ∈ M₁ ⊓ M₂), bM β ε ⟨ψ' p, hp⟩ = φ p := by
      intro p hp
      rw [burnsideF4j_bM_eq_bOne]
      rfl
    have hφz : φ ⟨CFSG.Quasithin.F6.G22Perm.sEl h2 26, LL.z_mem_P⟩ = z := by
      have hxe : (⟨ψ' (CFSG.Quasithin.F6.G22Perm.sEl h2 26),
          hψ'z ▸ hxB⟩ : ↥(M₁ ⊓ M₂)) = x := Subtype.ext hψ'z
      rw [← hbM _ (hψ'z ▸ hxB), hxe]
      exact hxz
    have hrange : φ.range = Subgroup.centralizer
        ({φ ⟨CFSG.Quasithin.F6.G22Perm.sEl h2 26, LL.z_mem_P⟩} : Set M) := by
      rw [hφz]
      apply le_antisymm
      · rintro _ ⟨p, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hφz, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent p.2))
      · intro y hy
        have hyM := hyp.hb hy
        rw [burnsideF4d_MiOne_eq, subImg_self] at hyM
        obtain ⟨m, rfl⟩ := hyM
        obtain ⟨p, hp, hpm⟩ := hM₁P₂ m.2
        refine ⟨⟨p, hp⟩, ?_⟩
        show burnsideF4d_bOne β ε (ρ ⟨p, hp⟩) = burnsideF4d_bOne β ε m
        congr 1
        exact Subtype.ext hpm
    have hconj : ∀ w ∈ ((G2Two.Model.TpSub h2 hk2).subgroupOf L.P₂).map φ, w * w = 1 →
        w ≠ 1 → IsConj (φ ⟨CFSG.Quasithin.F6.G22Perm.sEl h2 26, LL.z_mem_P⟩) w := by
      rintro _ ⟨p, hpT, rfl⟩ hw2 hw1
      have hpT' : (p : G2Group K) ∈ G2Two.Model.TpSub h2 hk2 := hpT
      have hp2 : (p : G2Group K) * p = 1 := by
        have : φ (p * p) = φ 1 := by rw [map_mul, hw2, map_one]
        exact congrArg Subtype.val (hφi this)
      have hp1 : (p : G2Group K) ≠ 1 := by
        intro h0
        apply hw1
        have : p = 1 := Subtype.ext h0
        rw [this, map_one]
      have hpJ : (p : G2Group K) ∈ (g2HomC h2).range := by
        obtain ⟨i, hi, hpi⟩ := (G2Two.Model.mem_TpSub h2 hk2).1 hpT'
        rw [hpi]
        refine ⟨u33Tel u33GenPG i, ?_⟩
        simp [CFSG.Quasithin.F6.G22Perm.sEl, hi]
      have hpc := burnsideF4gG2TwoInv_inner_inv_conj h2 hpJ hp1 hp2
      obtain ⟨c, hc⟩ := isConj_iff.mp hpc
      have hpS : (p : G2Group K) ∈ L.S := LL.Tp_le hpT'
      have hpB := hSB hpS
      have hfwd := burnsideF4j_F_4_35_forward hyp ⟨ψ' p, hpB⟩ x (by rw [hSeq]; exact hpB)
        (by rw [hSeq]; exact hxB)
        ⟨ψ' c, by rw [hGp]; exact Subgroup.mem_top _, by
          show ψ' c * ψ' p * (ψ' c)⁻¹ = (x : E)
          rw [← hψ'z, ← hc, map_mul, map_mul, map_inv]⟩
      rw [hbM p hpB, hxz] at hfwd
      rw [hφz]
      exact hfwd.symm
    have D := LL.toData hφi hrange hconj
    obtain ⟨v, hvQ, hvTp, hv2⟩ := LL.out_ex
    have hvP : v ∈ L.P₂ := LL.T_syl.1 (LL.Q_le hvQ)
    have hvS : v ∈ L.S := LL.Q_le hvQ
    have hvB := hSB hvS
    have hnc := burnsideF4r_G2Data_not_isConj D (v := φ ⟨v, hvP⟩) ⟨⟨v, hvP⟩, hvQ, rfl⟩
      (by
        rintro ⟨q, hq, hqv⟩
        apply hvTp
        have hq' : q = ⟨v, hvP⟩ := hφi hqv
        subst hq'
        exact hq)
      (by rw [← map_mul, show (⟨v, hvP⟩ : ↥L.P₂) * ⟨v, hvP⟩ = 1 from Subtype.ext hv2, map_one])
    rw [hφz] at hnc
    refine ⟨⟨ψ' v, hvB⟩, by rw [hSeq]; exact hvB, ?_, ?_, ?_⟩
    · intro h0
      apply hvTp
      have : v = 1 := hψ'i (by rw [map_one]; exact congrArg Subtype.val h0)
      rw [this]
      exact Subgroup.one_mem _
    · apply Subtype.ext
      show ψ' v * ψ' v = 1
      rw [← map_mul, hv2, map_one]
    · rw [hbM ⟨v, hvP⟩ hvB]
      exact hnc
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · rcases hcase with ⟨hk, -⟩ | ⟨hk, -⟩ <;> exact absurd hk (by decide)

theorem burnsideF4r_A35_G2 (hyp : HypF_4_31 .G2 f Gp M₁ M₂ β ε z) (hf : f < 2)
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1)
    (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  obtain ⟨v, hvS, hv1, hv2, hnc⟩ := burnsideF4r_G2_nonfused hyp hf
  exact burnsideF4r_F_4_35_of_nonfused hyp (by decide) (by decide) hvS hv1 hv2 hnc i j hi hj
    hi1 hj1 hi2 hj2

end G2Two

end CFSG.ASVolI
