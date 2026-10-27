module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def CentMaxProp (Γ : Type) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 2 ↥P → ¬ 2 ∣ P.index → ∀ W : Subgroup Γ, W ≤ centerOf P → W ≠ ⊥ →
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Γ))

section Transport

variable {Γ Γ' : Type} [Group Γ] [Group Γ']

theorem isMaxSubgroupIn_map (φ : Γ ≃* Γ') {K : Subgroup Γ} (h : IsMaxSubgroupIn ⊤ K) :
    IsMaxSubgroupIn ⊤ (K.map φ.toMonoidHom) := by
  obtain ⟨hlt, hmax⟩ := h
  refine ⟨?_, fun L hKL _ => ?_⟩
  · rw [lt_top_iff_ne_top]
    intro htop
    have h1 := congrArg (Subgroup.comap φ.toMonoidHom) htop
    rw [Subgroup.comap_map_eq_self_of_injective φ.injective, Subgroup.comap_top] at h1
    exact hlt.ne h1
  · have h1 : K < L.comap φ.toMonoidHom := by
      refine lt_of_le_of_ne (fun x hx => hKL.le ⟨x, hx, rfl⟩) fun heq => hKL.ne ?_
      rw [heq, Subgroup.map_comap_eq_self_of_surjective
        (show Function.Surjective φ.toMonoidHom from φ.surjective)]
    have h2 := hmax _ h1 le_top
    rw [← Subgroup.map_comap_eq_self_of_surjective
      (show Function.Surjective φ.toMonoidHom from φ.surjective) L, h2, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr φ.surjective]

theorem centerOf_map_equiv (φ : Γ ≃* Γ') (S : Subgroup Γ) :
    centerOf (S.map φ.toMonoidHom) = (centerOf S).map φ.toMonoidHom := by
  ext x'
  obtain ⟨x, rfl⟩ := φ.surjective x'
  change φ x ∈ S.map φ.toMonoidHom ⊓ Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup Γ') :
      Set Γ') ↔ φ x ∈ (S ⊓ Subgroup.centralizer (S : Set Γ)).map φ.toMonoidHom
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy, hxy⟩ := hx
    have hy' : y = x := φ.injective hxy
    subst hy'
    refine ⟨y, ⟨hy, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (φ s) ⟨s, hs, rfl⟩
    exact φ.injective (by simpa using this)
  · rintro ⟨y, ⟨hy, hc⟩, hxy⟩
    have hy' : y = x := φ.injective hxy
    subst hy'
    refine ⟨⟨y, hy, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun s' hs' => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hs'
    have := Subgroup.mem_centralizer_iff.mp hc s hs
    simpa using congrArg φ this

theorem centralizer_map_equiv (φ : Γ ≃* Γ') (W : Subgroup Γ) :
    Subgroup.centralizer ((W.map φ.toMonoidHom : Subgroup Γ') : Set Γ') =
      (Subgroup.centralizer (W : Set Γ)).map φ.toMonoidHom := by
  ext x'
  obtain ⟨x, rfl⟩ := φ.surjective x'
  constructor
  · intro hc
    refine ⟨x, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (φ w) ⟨w, hw, rfl⟩
    exact φ.injective (by simpa using this)
  · rintro ⟨y, hy, hxy⟩
    have hy' : y = x := φ.injective hxy
    subst hy'
    refine Subgroup.mem_centralizer_iff.mpr fun w' hw' => ?_
    obtain ⟨w, hw, rfl⟩ := hw'
    have := Subgroup.mem_centralizer_iff.mp hy w hw
    simpa using congrArg φ this

theorem CentMaxProp.of_mulEquiv [Finite Γ] (h : CentMaxProp Γ) (φ : Γ ≃* Γ') : CentMaxProp Γ' := by
  intro P' hP2 hPi W' hW hW0
  set e : Γ' ≃* Γ := φ.symm with he
  have hP2' : IsPGroup 2 ↥(P'.map e.toMonoidHom) :=
    hP2.of_equiv (Subgroup.equivMapOfInjective P' e.toMonoidHom e.injective)
  have hPi' : ¬ 2 ∣ (P'.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact hPi
  have hWc : W'.map e.toMonoidHom ≤ centerOf (P'.map e.toMonoidHom) := by
    rw [centerOf_map_equiv e]
    exact Subgroup.map_mono hW
  have hW0' : W'.map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply hW0
    rw [eq_bot_iff]
    intro x hx
    have hmem : e x ∈ W'.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (e.injective (by simpa using hmem))
  have h1 := isMaxSubgroupIn_map φ (h _ hP2' hPi' _ hWc hW0')
  rw [← centralizer_map_equiv φ] at h1
  have hmm : (W'.map e.toMonoidHom).map φ.toMonoidHom = W' := by
    rw [Subgroup.map_map]
    ext x
    simp [he]
  rw [hmm] at h1
  exact h1

end Transport

section Data

variable {Γ : Type} [Group Γ]

theorem centralizer_zpowers_eq (z : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer ({z} : Set Γ) := by
  ext x
  constructor
  · intro h
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.mem_centralizer_iff.mp h z (Subgroup.mem_zpowers z)
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp h
    exact (hc.symm.zpow_left k).eq

theorem centMaxProp_of_data [Finite Γ] {S : Subgroup Γ} {z : Γ} (hS2 : IsPGroup 2 ↥S)
    (hSi : ¬ 2 ∣ S.index) (hz2 : orderOf z = 2) (hcen : centerOf S = Subgroup.zpowers z)
    (hmax : IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({z} : Set Γ))) : CentMaxProp Γ := by
  intro P hP2 hPi W hW hW0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hS2.toSylow hSi) (hP2.toSylow hPi)
  have hPg : P = S.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  have hcenP : centerOf P = (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom := by
    rw [hPg, centerOf_map_equiv (MulAut.conj g), hcen]
  have hcard : Nat.card ↥(centerOf P) = 2 := by
    rw [hcenP, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hz2]
  have hWeq : W = centerOf P := by
    refine Subgroup.eq_of_le_of_card_ge hW ?_
    rw [hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot W).mpr hW0
  rw [hWeq, hcenP, centralizer_map_equiv (MulAut.conj g), centralizer_zpowers_eq]
  exact isMaxSubgroupIn_map (MulAut.conj g) hmax

end Data

end CFSG.Quasithin
