module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative TableBSymp

namespace KGA

theorem kga_card_le_sp {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ} [NeZero N]
    (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (LargeEvenSpGroup K N)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K N))
      (LargeEvenGSpSet K N), ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card A ≤ p ^ N := by
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K N)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot (K := K) (m := N)
  obtain ⟨Λ, _, hΛinj, hΛmap⟩ : ∃ Λ : LargeEvenProj (LargeEvenSpGroup K N) →* MulAut L',
      (∀ {e : LargeEvenProj (LargeEvenSpGroup K N)} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧
      Function.Injective Λ ∧ (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := TableBSymp.sp_I_subset_inn (K := K) (m := N) hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSpGroup K N)) := A.comap Λ
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  set E₁ : Subgroup ↥(LargeEvenSpGroup K N) :=
    E.map (TableBSymp.spProjEquivSp (K := K) (m := N)).toMonoidHom
  have hE₁ab : IsElemAbelian p E₁ := TableB.isElemAbelian_map hEab _
  have hcard₁ : Nat.card E = Nat.card E₁ := Nat.card_congr
    (E.equivMapOfInjective _ (TableBSymp.spProjEquivSp (K := K) (m := N)).injective).toEquiv
  rw [← hcardE, hcard₁]
  exact SpJoin.card_le_pow_of_isElemAbelian (F := K) (n := N) hp hp2
    (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) E₁ hE₁ab

theorem kga_selfCent_split {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} [NeZero m]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hE : IsElemAbelian p E)
    (hsc : ∀ g : LargeEvenProj (LargeEvenSpGroup K m), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 →
      g ∈ E) : p ^ m ≤ Nat.card E := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Subgroup (LargeEvenSpGroup K m),
      E₁ = E.comap (LargeEvenProjMk _) := ⟨_, rfl⟩
  have hmemE₁ : ∀ g, g ∈ E₁ ↔ LargeEvenProjMk _ g ∈ E := fun g => by
    rw [hE₁]; rfl
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Subgroup (GL (Fin m ⊕ Fin m) K),
      E₂ = E₁.map (LargeEvenSpGroup K m).subtype := ⟨_, rfl⟩
  have hE₁ab : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hπi ?_)⟩⟩, fun a ha => hπi ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE ((hmemE₁ _).mp a.2) ((hmemE₁ _).mp b.2)
    · rw [map_pow, map_one]
      exact hE.2 _ ((hmemE₁ _).mp ha)
  have hcard₁ : Nat.card E₁ = Nat.card E := by
    have h1 : E₁.map (LargeEvenProjMk _) = E := by
      rw [hE₁]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
    rw [Nat.card_congr (E₁.equivMapOfInjective _ hπi).toEquiv, h1]
  have hcard₁₂ : Nat.card E₁ = Nat.card E₂ := by
    rw [hE₂]
    exact Nat.card_congr (E₁.equivMapOfInjective _
      (LargeEvenSpGroup K m).subtype_injective).toEquiv
  have hE₂ab : IsElemAbelian p E₂ := by
    rw [hE₂]
    exact TableB.isElemAbelian_map hE₁ab _
  have hE₂Sp : E₂ ≤ LargeEvenSpGroup K m := by
    rw [hE₂]; exact Subgroup.map_subtype_le E₁
  obtain ⟨P, hP, u, hu⟩ := TableBSymp.exists_symplectic_weight_basis_GL (K := K) (m := m)
    (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hζo hE₂Sp hE₂ab
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hle : E₂.map (MulAut.conj P⁻¹).toMonoidHom ≤ (spTorusGL (m := m) hζ).range := by
    rintro _ ⟨a, ha, rfl⟩
    have hk : ∀ i, ∃ k < p, ζ ^ k = u i ⟨a, ha⟩ := fun i =>
      hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr
        (weight_pow_eq_one hE₂ab (u i) ⟨a, ha⟩))
    choose k _ hk using hk
    refine ⟨fun i => Multiplicative.ofAdd ((k i : ℕ) : ZMod p), ?_⟩
    rw [TableBSymp.spTorusGL_apply]
    have h1 : (pairedUnits fun i => zmodPowHom hζ
        (Multiplicative.ofAdd ((k i : ℕ) : ZMod p))) =
        pairedUnits fun i => u i ⟨a, ha⟩ := by
      congr 1
      funext i
      rw [zmodPowHom_natCast, hk]
    rw [h1, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
      show a * P = P * TauCeti.diagGL (pairedUnits fun i => u i ⟨a, ha⟩) from hu ⟨a, ha⟩,
      inv_mul_cancel_left]
  have hge : (spTorusGL (m := m) hζ).range ≤ E₂.map (MulAut.conj P⁻¹).toMonoidHom := by
    rintro _ ⟨f, rfl⟩
    have hgSp : P * spTorusGL hζ f * P⁻¹ ∈ LargeEvenSpGroup K m :=
      (LargeEvenSpGroup K m).mul_mem ((LargeEvenSpGroup K m).mul_mem hP
        (TableBSymp.spTorusGL_mem hζ f)) ((LargeEvenSpGroup K m).inv_mem hP)
    let g : LargeEvenSpGroup K m := ⟨P * spTorusGL hζ f * P⁻¹, hgSp⟩
    have hgcoe : (g : GL (Fin m ⊕ Fin m) K) = P * spTorusGL hζ f * P⁻¹ := rfl
    have hcomm : ∀ e ∈ E, LargeEvenProjMk _ g * e = e * LargeEvenProjMk _ g := by
      intro e he
      obtain ⟨e₁, he₁⟩ : ∃ e₁ : LargeEvenSpGroup K m, LargeEvenProjMk _ e₁ = e :=
        QuotientGroup.mk'_surjective _ e
      have he₁E₁ : e₁ ∈ E₁ := (hmemE₁ e₁).mpr (he₁ ▸ he)
      have he₁E₂ : (e₁ : GL (Fin m ⊕ Fin m) K) ∈ E₂ := by
        rw [hE₂]; exact ⟨e₁, he₁E₁, rfl⟩
      let a₂ : E₂ := ⟨(e₁ : GL (Fin m ⊕ Fin m) K), he₁E₂⟩
      let D : GL (Fin m ⊕ Fin m) K := TauCeti.diagGL (pairedUnits fun i => u i a₂)
      have hD : (e₁ : GL (Fin m ⊕ Fin m) K) * P = P * D := hu a₂
      have hPinv : P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K) * P = D := by
        calc P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K) * P
            = P⁻¹ * ((e₁ : GL (Fin m ⊕ Fin m) K) * P) := by group
          _ = P⁻¹ * (P * D) := by rw [hD]
          _ = D := by group
      have hPinv' : P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K) = D * P⁻¹ := by
        calc P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K)
            = P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K) * P * P⁻¹ := by group
          _ = D * P⁻¹ := by rw [hPinv]
      have hcommD : spTorusGL hζ f * D = D * spTorusGL hζ f := by
        rw [TableBSymp.spTorusGL_apply]
        change TauCeti.diagGL (pairedUnits fun i => zmodPowHom hζ (f i)) * D =
          D * TauCeti.diagGL (pairedUnits fun i => zmodPowHom hζ (f i))
        rw [show D = TauCeti.diagGL (pairedUnits fun i => u i a₂) from rfl,
          ← map_mul, ← map_mul, mul_comm]
      have hGL : (g : GL (Fin m ⊕ Fin m) K) * (e₁ : GL (Fin m ⊕ Fin m) K) =
          (e₁ : GL (Fin m ⊕ Fin m) K) * (g : GL (Fin m ⊕ Fin m) K) := by
        rw [hgcoe]
        calc (P * spTorusGL hζ f * P⁻¹) * (e₁ : GL (Fin m ⊕ Fin m) K)
            = P * (spTorusGL hζ f * (P⁻¹ * (e₁ : GL (Fin m ⊕ Fin m) K))) := by group
          _ = P * (spTorusGL hζ f * (D * P⁻¹)) := by rw [hPinv']
          _ = P * ((spTorusGL hζ f * D) * P⁻¹) := by group
          _ = P * ((D * spTorusGL hζ f) * P⁻¹) := by rw [hcommD]
          _ = (P * D) * spTorusGL hζ f * P⁻¹ := by group
          _ = ((e₁ : GL (Fin m ⊕ Fin m) K) * P) * spTorusGL hζ f * P⁻¹ := by rw [← hD]
          _ = (e₁ : GL (Fin m ⊕ Fin m) K) * (P * spTorusGL hζ f * P⁻¹) := by group
      rw [← he₁, ← map_mul, ← map_mul]
      exact congrArg (LargeEvenProjMk _) (Subtype.ext hGL)
    have htp : spTorusGL hζ f ^ p = 1 := by
      rw [← map_pow, ReflInner.pow_eq_one_of_zmod f, map_one]
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hgcoe]
      rw [show P * spTorusGL hζ f * P⁻¹ = MulAut.conj P (spTorusGL hζ f) from
        (MulAut.conj_apply P _).symm, ← map_pow, htp, map_one]
    have hπgp : (LargeEvenProjMk _ g) ^ p = 1 := by
      rw [← map_pow, hgp, map_one]
    have hgE : LargeEvenProjMk _ g ∈ E := hsc _ hcomm hπgp
    have hgE₁ : g ∈ E₁ := (hmemE₁ g).mpr hgE
    have hgE₂ : (g : GL (Fin m ⊕ Fin m) K) ∈ E₂ := by
      rw [hE₂]; exact ⟨g, hgE₁, rfl⟩
    refine ⟨g, hgE₂, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgcoe]
    group
  have hEq : E₂.map (MulAut.conj P⁻¹).toMonoidHom = (spTorusGL (m := m) hζ).range :=
    le_antisymm hle hge
  have hinj : Function.Injective (spTorusGL (m := m) hζ) := by
    intro f f' h
    apply TableBSymp.spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)
    rw [spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext h
  have hcardE₂map : Nat.card E₂ = Nat.card (E₂.map (MulAut.conj P⁻¹).toMonoidHom) :=
    Nat.card_congr (E₂.equivMapOfInjective _ (MulAut.conj P⁻¹).injective).toEquiv
  have hcardRange : Nat.card (spTorusGL (m := m) hζ).range = p ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
      Nat.card_fin]
  have hcardE : Nat.card E = p ^ m := by
    rw [← hcard₁, hcard₁₂, hcardE₂map, hEq, hcardRange]
  exact le_of_eq hcardE.symm

theorem kga_torusSCRank_split
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusSCRank p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggTorusSCRank_of_selfCent hp TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot
    (ggCenterPrime_sp hp hp2) fun E hE hsc => kga_selfCent_split hp hp2 hpq hE hsc

theorem kga_k_eq {p k N : ℕ} (hp : p.Prime) {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (h1 : p ^ N ≤ Nat.card A)
    (h2 : Nat.card A ≤ p ^ N) : k = N := by
  have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  have hcard : Nat.card A = p ^ k := by
    rw [← Nat.card_congr Θ.toEquiv, hcV]
  have hNk : N ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard ▸ h1)
  have hkN : k ≤ N := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard ▸ h2)
  omega

end KGA

end CFSG.StandardType

end
