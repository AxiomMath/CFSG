module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private lemma s16c11_v1_inv_mul_mem_iff {A : Type*} [CommGroup A] {K : Subgroup A} {a b : A} :
    a⁻¹ * b ∈ K ↔ a * b⁻¹ ∈ K := by
  have h : a * b⁻¹ = (a⁻¹ * b)⁻¹ := by
    rw [mul_inv_rev]
    simp only [inv_inv]
    exact mul_comm a b⁻¹
  rw [h]
  exact K.inv_mem_iff.symm

private lemma s16c11_v1_polarQ_comm {J : Type} [CommGroup J] (Q : J → ZMod 2) (x y : J) :
    polarQ Q x y = polarQ Q y x := by
  simp only [polarQ, mul_comm x y]
  abel

private lemma s16c11_v1_quad_mul {J : Type} [CommGroup J] (Q : J → ZMod 2) (x y : J) :
    Q (x * y) = Q x + Q y + polarQ Q x y := by
  simp only [polarQ]
  ring

private lemma s16c11_v1_zmod_two_eq_one {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem s16c11_v1_rf3_of_cover_quad {J : Type} [CommGroup J] [Finite J] {D : FFModel}
    (hD : D.Faithful) (hw : S16C11ModelRF3 D) {H : Subgroup (MulAut J)}
    (hR : D.Realizes H ⊤ (fixV H))
    (hQ : ∃ Q : J → ZMod 2, IsQuadF2 Q ∧ QuadInvariant Q H ∧
      (∀ x : J, (∀ y : J, polarQ Q x y = 0) ↔ x ∈ fixV H) ∧
      (∀ z : J, z ∈ fixV H → z ≠ 1 → Q z ≠ 0)) :
    S16C11RF3 H (⊤ : Subgroup J) := by
  classical
  obtain ⟨Q, -, hQinv, hQrad, hQnz⟩ := hQ
  obtain ⟨π, hπ⟩ := hR
  have hπi : Function.Injective π := FFModel.RealizesVia.injective_of_faithful_on hD hπ
  obtain ⟨hπs, -, hker, -, hHZ, hsec, hkeract, β, hβs, hβk, hβe⟩ := hπ
  obtain ⟨T, X, hTX, hTp, hTi, hTX3, y, hy, hfixT, g₀, hg₀X, hg₀⟩ := hw
  let ι : D.Gam →* MulAut J := H.subtype.comp π
  have hιi : Function.Injective ι := (Subgroup.subtype_injective H).comp hπi
  have hιrange : ι.range = H := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact (π γ).2
    · intro x hx
      obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
      refine ⟨γ, ?_⟩
      show (H.subtype (π γ) : MulAut J) = x
      rw [hγ]
      rfl
  have hιmem : ∀ t : D.Gam, ι t ∈ H := by
    intro t
    rw [← hιrange]
    exact ⟨t, rfl⟩
  obtain ⟨u₀, hu₀⟩ := hβs (QuotientGroup.mk ⟨y, hy⟩)
  have hchoice : ∃ u : ↥(⊤ : Subgroup J),
      β u = QuotientGroup.mk ⟨y, hy⟩ ∧ (fixV H = ⊥ ∨ Q (u : J) = 0) := by
    by_cases hf : fixV H = ⊥
    · exact ⟨u₀, hu₀, Or.inl hf⟩
    · by_cases hQ0 : Q (u₀ : J) = 0
      · exact ⟨u₀, hu₀, Or.inr hQ0⟩
      · obtain ⟨z₀, hz₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hf
        refine ⟨u₀ * ⟨(z₀ : J), Subgroup.mem_top _⟩, ?_, Or.inr ?_⟩
        · have hzβ : β ⟨(z₀ : J), Subgroup.mem_top _⟩ = 1 := (hβk _).2 z₀.2
          rw [map_mul, hzβ, mul_one]
          exact hu₀
        · have hz1 : (z₀ : J) ≠ 1 := fun h => hz₀ (Subtype.ext h)
          have hQz : Q (z₀ : J) = 1 :=
            s16c11_v1_zmod_two_eq_one (hQnz _ z₀.2 hz1)
          have hQu : Q (u₀ : J) = 1 := s16c11_v1_zmod_two_eq_one hQ0
          have hpolar : polarQ Q (u₀ : J) (z₀ : J) = 0 := by
            rw [s16c11_v1_polarQ_comm]
            exact (hQrad (z₀ : J)).2 z₀.2 (u₀ : J)
          change Q ((u₀ : J) * (z₀ : J)) = 0
          rw [s16c11_v1_quad_mul Q, hQu, hQz, hpolar]
          decide
  obtain ⟨u, hu, hQu⟩ := hchoice
  have hfixπ : ∀ t ∈ T, ((π t : ↥H) : MulAut J) (u : J) = (u : J) := by
    intro t ht
    have hzt : ((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹ ∈ fixV H := by
      have h1 := hβe t u ⟨y, hy⟩ (Subgroup.mem_top _) (hsec t y hy) hu
      have hmk : (QuotientGroup.mk (⟨D.act t (y : D.Amb), hsec t y hy⟩ : ↥D.sec) :
          ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk (⟨y, hy⟩ : ↥D.sec) := by
        rw [QuotientGroup.eq]
        exact Subgroup.mem_subgroupOf.2 (by
          simpa using s16c11_v1_inv_mul_mem_iff.2 (hfixT t ht))
      have hβeq :
          β (⟨((π t : ↥H) : MulAut J) (u : J), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup J)) =
            β u := by
        rw [h1, hmk, ← hu]
      have hprod : β (⟨((π t : ↥H) : MulAut J) (u : J), Subgroup.mem_top _⟩ * u⁻¹) = 1 := by
        rw [map_mul, map_inv, hβeq, mul_inv_cancel]
      have := (hβk _).1 hprod
      simpa using this
    by_cases hsame : ((π t : ↥H) : MulAut J) (u : J) = (u : J)
    · exact hsame
    · exfalso
      have hzt1 : ((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹ ≠ 1 := by
        intro h
        apply hsame
        calc ((π t : ↥H) : MulAut J) (u : J)
            = ((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹ * (u : J) := by group
          _ = (u : J) := by rw [h, one_mul]
      have hQu0 : Q (u : J) = 0 := by
        rcases hQu with hf | hq
        · exact absurd (Subgroup.mem_bot.mp (hf ▸ hzt)) hzt1
        · exact hq
      have hQzt : Q (((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹) = 1 :=
        s16c11_v1_zmod_two_eq_one (hQnz _ hzt hzt1)
      have hinv : Q (((π t : ↥H) : MulAut J) (u : J)) = Q (u : J) :=
        hQinv ((π t : ↥H) : MulAut J) (π t).2 (u : J)
      have hpolar : polarQ Q (u : J) (((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹) = 0 := by
        rw [s16c11_v1_polarQ_comm]
        exact (hQrad _).2 hzt (u : J)
      have hmul : ((π t : ↥H) : MulAut J) (u : J)
          = (u : J) * (((π t : ↥H) : MulAut J) (u : J) * (u : J)⁻¹) := by
        rw [← mul_assoc, mul_comm (u : J) (((π t : ↥H) : MulAut J) (u : J)), mul_assoc,
          mul_inv_cancel, mul_one]
      have hone : Q (((π t : ↥H) : MulAut J) (u : J)) = 1 := by
        rw [hmul, s16c11_v1_quad_mul Q, hQu0, hQzt, hpolar]
        decide
      rw [hinv, hQu0] at hone
      exact zero_ne_one hone
  have hfixι : ∀ t ∈ T, ι t (u : J) = (u : J) := by
    intro t ht
    simpa [ι] using hfixπ t ht
  have hmovπ : ((π g₀ : ↥H) : MulAut J) (u : J) ≠ (u : J) := by
    intro hgu
    have h1 := hβe g₀ u ⟨y, hy⟩ (Subgroup.mem_top _) (hsec g₀ y hy) hu
    have hu_eq : (⟨((π g₀ : ↥H) : MulAut J) (u : J), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup J)) = u :=
      Subtype.ext hgu
    have hmk : (QuotientGroup.mk (⟨D.act g₀ (y : D.Amb), hsec g₀ y hy⟩ : ↥D.sec) :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk (⟨y, hy⟩ : ↥D.sec) := by
      rw [← h1, hu_eq, hu]
    have hker' : (D.act g₀ (y : D.Amb))⁻¹ * y ∈ D.ker :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hmk)
    exact hg₀ (s16c11_v1_inv_mul_mem_iff.1 hker')
  have hmovι : ι g₀ (u : J) ≠ (u : J) := by
    simpa [ι] using hmovπ
  haveI : Finite (MulAut J) :=
    Finite.of_injective (fun e : MulAut J => (e : J → J))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T₀ hT₀ hT₀p hT₀i
  let P : Subgroup (MulAut J) := T.map ι
  have hPH : P ≤ H := by
    change T.map ι ≤ H
    rw [← hιrange]
    exact Subgroup.map_le_range ι T
  have hPp : IsPGroup 2 ↥P := hTp.map ι
  have htopmap : (⊤ : Subgroup D.Gam).map ι = H := by
    rw [← MonoidHom.range_eq_map, hιrange]
  have hPi : ¬ 2 ∣ P.relIndex H := by
    change ¬ 2 ∣ (T.map ι).relIndex H
    rw [← htopmap, Subgroup.relIndex_map_map_of_injective T ⊤ hιi,
      Subgroup.relIndex_top_right]
    exact hTi
  have hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 T₀ H :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hT₀, hT₀p, hT₀i⟩
  have hSP : CFSG.ABGLocalTools.IsSylowOf 2 P H :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPH, hPp, hPi⟩
  obtain ⟨k, hkH, hk⟩ := hSP.exists_mem_conj hS₀
  have hT₀conj : T₀ = P.map (MulAut.conj k).toMonoidHom := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_map.2 ⟨k⁻¹ * x * k, (hk x).1 hx, ?_⟩
      change MulAut.conj k (k⁻¹ * x * k) = x
      simp only [MulAut.conj_apply]
      group
    · intro x hx
      apply (hk x).2
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hx
      rw [← hzx]
      convert hz using 1
      change k⁻¹ * MulAut.conj k z * k = z
      simp only [MulAut.conj_apply]
      group
  have hconjfix : ∀ s : D.Gam,
      (MulAut.conj k) (ι s) (k (u : J)) = k (ι s (u : J)) := by
    intro s
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hconjfixT : ∀ s : D.Gam,
      (MulAut.conj k).toMonoidHom (ι s) (k (u : J)) = k (ι s (u : J)) := hconjfix
  refine ⟨(X.map ι).map (MulAut.conj k).toMonoidHom, ?_, ?_, ?_, k (u : J),
    Subgroup.mem_top _, ?_, MulAut.conj k (ι g₀), ?_, ?_⟩
  · have hle : X.map ι ≤ H := by
      rw [← hιrange]
      exact Subgroup.map_le_range ι X
    refine (Subgroup.map_mono hle).trans ?_
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hkH hw) (H.inv_mem hkH)
  · rw [hT₀conj]
    exact Subgroup.map_mono (Subgroup.map_mono hTX)
  · rw [hT₀conj, Subgroup.relIndex_map_map_of_injective (T.map ι) (X.map ι)
      (MulAut.conj k).injective, Subgroup.relIndex_map_map_of_injective T X hιi]
    exact hTX3
  · intro t ht
    rw [hT₀conj] at ht
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hp
    rw [hconjfixT s, hfixι s hs]
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hg₀X)
  · intro h
    rw [hconjfix g₀] at h
    exact hmovι (k.injective h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
