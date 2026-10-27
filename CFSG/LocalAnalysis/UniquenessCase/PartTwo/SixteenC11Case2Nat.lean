module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2NatA
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

private lemma s16c11_case2nat_inv_mul_mem_iff {A : Type*} [CommGroup A] {K : Subgroup A} {a b : A} :
    a⁻¹ * b ∈ K ↔ a * b⁻¹ ∈ K := by
  have h : a * b⁻¹ = (a⁻¹ * b)⁻¹ := by
    rw [mul_inv_rev]
    simp only [inv_inv]
    exact mul_comm a b⁻¹
  rw [h]
  exact K.inv_mem_iff.symm

@[expose] def S16C11ModelRF3 (D : FFModel) : Prop :=
  ∃ T X : Subgroup D.Gam, T ≤ X ∧ IsPGroup 2 ↥T ∧ ¬ 2 ∣ T.index ∧ T.relIndex X = 3 ∧
    ∃ y ∈ D.sec, (∀ t ∈ T, D.act t y * y⁻¹ ∈ D.ker) ∧ ∃ g ∈ X, D.act g y * y⁻¹ ∉ D.ker

theorem s16c11_rf3_of_modelRF3 {W : Type} [CommGroup W] [Finite W] {D : FFModel}
    (hD : D.Faithful) {L₀ : Subgroup (MulAut W)} {J : Subgroup W} (hR : D.Realizes L₀ J ⊥)
    (hw : S16C11ModelRF3 D) : S16C11RF3 L₀ J := by
  obtain ⟨π, hπ⟩ := hR
  have hπi : Function.Injective π := FFModel.RealizesVia.injective_of_faithful_on hD hπ
  obtain ⟨hπs, hZJ, hker, hHU, hHZ, hsec, hkeract, β, hβs, hβk, hβe⟩ := hπ
  obtain ⟨T, X, hTX, hTp, hTi, hTX3, y, hy, hfixT, g₀, hg₀X, hg₀⟩ := hw
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let ι : D.Gam →* MulAut W := L₀.subtype.comp π
  have hιi : Function.Injective ι := (Subgroup.subtype_injective L₀).comp hπi
  have hιrange : ι.range = L₀ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact (π γ).2
    · intro x hx
      obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
      refine ⟨γ, ?_⟩
      show (L₀.subtype (π γ) : MulAut W) = x
      rw [hγ]
      rfl
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, hy⟩)
  have hfixι : ∀ t ∈ T, ι t (u : W) = (u : W) := by
    intro t ht
    have hu' : ((π t : ↥L₀) : MulAut W) (u : W) ∈ J := hHU (π t) (u : W) u.2
    have hact : D.act t (y : D.Amb) ∈ D.sec := hsec t y hy
    have hker' : (D.act t (y : D.Amb))⁻¹ * y ∈ D.ker :=
      s16c11_case2nat_inv_mul_mem_iff.2 (hfixT t ht)
    have hmk : (QuotientGroup.mk (⟨D.act t (y : D.Amb), hact⟩ : ↥D.sec) :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk (⟨y, hy⟩ : ↥D.sec) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.2 (by simpa using hker')
    have h1 := hβe t u ⟨y, hy⟩ hu' hact hu
    have h2 : β (⟨((π t : ↥L₀) : MulAut W) (u : W), hu'⟩ : ↥J) = β u := by
      rw [h1, hmk, ← hu]
    have h3 := congrArg Subtype.val (hβi h2)
    simpa [ι] using h3
  have hmovι : ι g₀ (u : W) ≠ (u : W) := by
    intro hgu
    have hu' : ((π g₀ : ↥L₀) : MulAut W) (u : W) ∈ J := hHU (π g₀) (u : W) u.2
    have hact : D.act g₀ (y : D.Amb) ∈ D.sec := hsec g₀ y hy
    have h1 := hβe g₀ u ⟨y, hy⟩ hu' hact hu
    have hu_eq : (⟨((π g₀ : ↥L₀) : MulAut W) (u : W), hu'⟩ : ↥J) = u := by
      apply Subtype.ext
      simpa [ι] using hgu
    have hmk : (QuotientGroup.mk (⟨D.act g₀ (y : D.Amb), hact⟩ : ↥D.sec) :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk (⟨y, hy⟩ : ↥D.sec) := by
      rw [← h1, hu_eq, hu]
    have hker' : (D.act g₀ (y : D.Amb))⁻¹ * y ∈ D.ker := by
      have h := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hmk)
      simpa using h
    exact hg₀ (s16c11_case2nat_inv_mul_mem_iff.1 hker')
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T₀ hT₀ hT₀p hT₀i
  let P : Subgroup (MulAut W) := T.map ι
  have hPL₀ : P ≤ L₀ := by
    change T.map ι ≤ L₀
    rw [← hιrange]
    exact Subgroup.map_le_range ι T
  have hPp : IsPGroup 2 ↥P := hTp.map ι
  have htopmap : (⊤ : Subgroup D.Gam).map ι = L₀ := by
    rw [← MonoidHom.range_eq_map, hιrange]
  have hPi : ¬ 2 ∣ P.relIndex L₀ := by
    change ¬ 2 ∣ (T.map ι).relIndex L₀
    rw [← htopmap, Subgroup.relIndex_map_map_of_injective T ⊤ hιi,
      Subgroup.relIndex_top_right]
    exact hTi
  have hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 T₀ L₀ :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hT₀, hT₀p, hT₀i⟩
  have hSP : CFSG.ABGLocalTools.IsSylowOf 2 P L₀ :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPL₀, hPp, hPi⟩
  obtain ⟨k, hkL₀, hk⟩ := hSP.exists_mem_conj hS₀
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
      (MulAut.conj k) (ι s) (k (u : W)) = k (ι s (u : W)) := by
    intro s
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hconjfix' : ∀ s : D.Gam,
      (MulAut.conj k).toMonoidHom (ι s) (k (u : W)) = k (ι s (u : W)) :=
    hconjfix
  refine ⟨(X.map ι).map (MulAut.conj k).toMonoidHom, ?_, ?_, ?_, k (u : W),
    hHU ⟨k, hkL₀⟩ (u : W) u.2, ?_, MulAut.conj k (ι g₀), ?_, ?_⟩
  · have hle : X.map ι ≤ L₀ := by
      rw [← hιrange]
      exact Subgroup.map_le_range ι X
    refine (Subgroup.map_mono hle).trans ?_
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    simpa [MulAut.conj_apply] using L₀.mul_mem (L₀.mul_mem hkL₀ hw) (L₀.inv_mem hkL₀)
  · rw [hT₀conj]
    exact Subgroup.map_mono (Subgroup.map_mono hTX)
  · rw [hT₀conj, Subgroup.relIndex_map_map_of_injective (T.map ι) (X.map ι)
      (MulAut.conj k).injective, Subgroup.relIndex_map_map_of_injective T X hιi]
    exact hTX3
  · intro t ht
    rw [hT₀conj] at ht
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hp
    rw [hconjfix' s, hfixι s hs]
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hg₀X)
  · intro h
    rw [hconjfix g₀] at h
    exact hmovι (k.injective h)

theorem s16c11_rf3Odd_of_realizes {W W' : Type} [CommGroup W] [CommGroup W'] {D : FFModel}
    (hD : D.Faithful) {L : Subgroup (MulAut W)} {J : Subgroup W} {L' : Subgroup (MulAut W')}
    {J' : Subgroup W'} (h : D.Realizes L J ⊥) (h' : D.Realizes L' J' ⊥)
    (hM : S16C11RF3Odd L' J') : S16C11RF3Odd L J := by
  obtain ⟨π, hπ⟩ := h
  have hπi : Function.Injective π := FFModel.RealizesVia.injective_of_faithful_on hD hπ
  obtain ⟨hπs, hπZJ, hπker, hLU, hLZ, hπsec, hπkeract, β, hβs, hβk, hβe⟩ := hπ
  obtain ⟨π', hπ'⟩ := h'
  have hπ'i : Function.Injective π' := FFModel.RealizesVia.injective_of_faithful_on hD hπ'
  obtain ⟨hπ's, hπ'ZJ, hπ'ker, hL'U, hL'Z, hπ'sec, hπ'keract, β', hβ's, hβ'k, hβ'e⟩ := hπ'
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have hβ'i : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβ'k u).1 hu))
  let e : D.Gam ≃* ↥L := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let e' : D.Gam ≃* ↥L' := MulEquiv.ofBijective π' ⟨hπ'i, hπ's⟩
  let ψ : ↥L ≃* ↥L' := e.symm.trans e'
  let Mod := ↥D.sec ⧸ D.ker.subgroupOf D.sec
  let eJ : ↥J ≃* Mod := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let eJ' : ↥J' ≃* Mod := MulEquiv.ofBijective β' ⟨hβ'i, hβ's⟩
  let φ : ↥J ≃* ↥J' := eJ.trans eJ'.symm
  have hLJ : ∀ l ∈ L, ∀ y ∈ J, l y ∈ J := fun l hl y hy => hLU ⟨l, hl⟩ y hy
  have hL'J' : ∀ l ∈ L', ∀ y ∈ J', l y ∈ J' := fun l hl y hy => hL'U ⟨l, hl⟩ y hy
  have hint : ∀ (l : ↥L) (u : ↥J),
      (φ ⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : W') =
        ((ψ l : ↥L') : MulAut W') (φ u : W') := by
    intro l u
    have hπγ : π (e.symm l) = l := MulEquiv.ofBijective_apply_symm_apply π ⟨hπi, hπs⟩
    have hπ'γ : π' (e.symm l) = ψ l := rfl
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : β u = QuotientGroup.mk m := hm.symm
    have hact : D.act (e.symm l) (m : D.Amb) ∈ D.sec := hπsec (e.symm l) m m.2
    have hu' : ((π (e.symm l) : ↥L) : MulAut W) (u : W) ∈ J := by
      rw [hπγ]
      exact hLJ l l.2 u u.2
    have h1 := hβe (e.symm l) u m hu' hact hm'
    have h1' : β (⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : ↥J) =
        QuotientGroup.mk (⟨D.act (e.symm l) (m : D.Amb), hact⟩ : ↥D.sec) := by
      have harg : (⟨((π (e.symm l) : ↥L) : MulAut W) (u : W), hu'⟩ : ↥J) =
          ⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ := by
        apply Subtype.ext
        show ((π (e.symm l) : ↥L) : MulAut W) (u : W) = (l : MulAut W) (u : W)
        rw [hπγ]
      rw [← harg]
      exact h1
    have hβ'φu : β' (φ u) = QuotientGroup.mk m := by
      have hkey : eJ' (φ u) = eJ u := by
        simp only [φ, MulEquiv.trans_apply]
        exact MulEquiv.ofBijective_apply_symm_apply β' ⟨hβ'i, hβ's⟩
      have h2 : eJ' (φ u) = β' (φ u) := rfl
      have h3 : eJ u = β u := rfl
      rw [← h2, hkey, h3, hm']
    have hu'' : ((π' (e.symm l) : ↥L') : MulAut W') (φ u : W') ∈ J' := by
      rw [hπ'γ]
      exact hL'J' (ψ l) (ψ l).2 (φ u) (φ u).2
    have h2 := hβ'e (e.symm l) (φ u) m hu'' hact hβ'φu
    have h2' : β' (⟨((ψ l : ↥L') : MulAut W') (φ u : W'),
        hL'J' (ψ l) (ψ l).2 (φ u) (φ u).2⟩ : ↥J') =
        QuotientGroup.mk (⟨D.act (e.symm l) (m : D.Amb), hact⟩ : ↥D.sec) := by
      have harg : (⟨((π' (e.symm l) : ↥L') : MulAut W') (φ u : W'), hu''⟩ : ↥J') =
          ⟨((ψ l : ↥L') : MulAut W') (φ u : W'),
            hL'J' (ψ l) (ψ l).2 (φ u) (φ u).2⟩ := by
        apply Subtype.ext
        show ((π' (e.symm l) : ↥L') : MulAut W') (φ u : W') =
          ((ψ l : ↥L') : MulAut W') (φ u : W')
        rw [hπ'γ]
      rw [← harg]
      exact h2
    have hβeq : β (⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : ↥J) =
        β' (⟨((ψ l : ↥L') : MulAut W') (φ u : W'),
          hL'J' (ψ l) (ψ l).2 (φ u) (φ u).2⟩ : ↥J') := by
      rw [h1', h2']
    have hφeq : φ (⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : ↥J) =
        ⟨((ψ l : ↥L') : MulAut W') (φ u : W'),
          hL'J' (ψ l) (ψ l).2 (φ u) (φ u).2⟩ := by
      apply eJ'.injective
      have hkey : eJ' (φ (⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : ↥J)) =
          eJ (⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : ↥J) := by
        simp [φ, MulEquiv.trans_apply]
      rw [hkey]
      exact hβeq
    exact congrArg Subtype.val hφeq
  obtain ⟨N, T₁', hT₁'L', hT₁'p', hT₁'i', hodd'⟩ := hM
  let T₁ : Subgroup (MulAut W) := ((T₁'.subgroupOf L').map ψ.symm.toMonoidHom).map L.subtype
  have hT₁L : T₁ ≤ L :=
    (Subgroup.map_le_range L.subtype ((T₁'.subgroupOf L').map ψ.symm.toMonoidHom)).trans_eq
      L.range_subtype
  have hA : T₁.subgroupOf L = (T₁'.subgroupOf L').map ψ.symm.toMonoidHom := by
    dsimp only [T₁]
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective
      ((T₁'.subgroupOf L').map ψ.symm.toMonoidHom)]
  have hT₁map : ((T₁.subgroupOf L).map ψ.toMonoidHom).map L'.subtype = T₁' := by
    rw [hA, Subgroup.map_map (g := ψ.toMonoidHom) (f := ψ.symm.toMonoidHom)]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id (↥L') := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id, Subgroup.subgroupOf_map_subtype T₁' L',
      inf_eq_left.mpr hT₁'L']
  have hcard : (S16C11Pairs L J T₁ N).ncard = (S16C11Pairs L' J' T₁' N).ncard := by
    rw [← hT₁map]
    exact s16c11_case2nat_pairs_ncard_eq ψ φ hLJ hL'J' hint T₁ hT₁L N
  have hT₁p : IsPGroup 2 ↥T₁ := by
    have eT : ↥T₁' ≃* ↥T₁ :=
      (Subgroup.subgroupOfEquivOfLe hT₁'L').symm.trans
        ((ψ.symm.subgroupMap (T₁'.subgroupOf L')).trans
          (Subgroup.equivMapOfInjective ((T₁'.subgroupOf L').map ψ.symm.toMonoidHom) L.subtype
            L.subtype_injective))
    exact hT₁'p'.of_equiv eT
  have hT₁i : ¬ 2 ∣ T₁.relIndex L := by
    have hrel : T₁.relIndex L = T₁'.relIndex L' := by
      show (T₁.subgroupOf L).index = (T₁'.subgroupOf L').index
      rw [hA]
      exact Subgroup.index_map_of_bijective ψ.symm.bijective (T₁'.subgroupOf L')
    rw [hrel]
    exact hT₁'i'
  exact ⟨N, T₁, hT₁L, hT₁p, hT₁i, by rw [hcard]; exact hodd'⟩

theorem s16c11_map_conj_eq_of_card_two_mul {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} (hLL₀ : L ≤ L₀) (hcard : Nat.card ↥L₀ = 2 * Nat.card ↥L) :
    ∀ x ∈ L₀, L.map (MulAut.conj x).toMonoidHom = L := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  have hrel : L.relIndex L₀ = 2 := by
    have h := Subgroup.relIndex_mul_card L L₀
    rw [inf_eq_left.mpr hLL₀, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hnormal : (L.subgroupOf L₀).Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact hrel
  have hnorm : L₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLL₀).1 hnormal
  intro x hx
  exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (hnorm hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
