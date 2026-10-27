module

public import CFSG.Quasithin.EmptyFaithful.A38c3Perm
public import CFSG.Quasithin.EmptyFaithful.S153G28
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm

theorem exists_hom_perm_extending_alt {Γ : Type*} [Group Γ] (Λ : Subgroup Γ)
    (e : ↥Λ ≃* alternatingGroup (Fin 7)) :
    ∃ ν : ↥(Subgroup.normalizer (Λ : Set Γ)) →* Perm (Fin 7),
      ∀ l : ↥Λ, ν ⟨(l : Γ), Subgroup.le_normalizer l.2⟩ =
        ((e l : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let Φ : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  have hΦ : ∀ (σ : Perm (Fin 7)) (x : alternatingGroup (Fin 7)),
      ((Φ σ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ * (x : Perm (Fin 7)) * σ⁻¹ :=
    fun σ x => MulAut.conjNormal_apply σ x
  refine ⟨Φ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp Λ.normalizerMonoidHom),
    fun l => ?_⟩
  have hκ : (MulAut.congr e) (Λ.normalizerMonoidHom ⟨(l : Γ), Subgroup.le_normalizer l.2⟩) =
      Φ ((e l : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hΦ, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    have h1 : Λ.normalizerMonoidHom ⟨(l : Γ), Subgroup.le_normalizer l.2⟩ (e.symm x) =
        l * e.symm x * l⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  show Φ.symm ((MulAut.congr e) (Λ.normalizerMonoidHom ⟨(l : Γ), Subgroup.le_normalizer l.2⟩)) = _
  rw [hκ, MulEquiv.symm_apply_apply]

theorem isCyclic_of_isPGroup_of_range_le {P G : Type} [Group P] [Finite P] [Group G] [Finite G]
    (hP : IsPGroup 3 P) (ι : P →* G) (hι : Function.Injective ι) {Y : Subgroup G}
    (hle : ι.range ≤ Y) (hr : CFSG.Open.pRank 3 Y ≤ 1) : IsCyclic P := by
  by_contra hcyc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := P) (p := 3) (by norm_num) hcyc
  have := hSel
  have hel : CFSG.IsElementaryAbelian 3 ↥(S.map ι) := CFSG.IsElementaryAbelian.map ι
  have hel' : CFSG.Open.IsElemAbelian 3 (S.map ι) :=
    ⟨hel.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hcard : Nat.card ↥(S.map ι) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hι, hScard]
  have hSY : S.map ι ≤ Y := by
    rintro _ ⟨s, -, rfl⟩
    exact hle ⟨s, rfl⟩
  have := CFSG.SectionRank.le_pRank (by norm_num) hSY hel' hcard
  omega

theorem sylow_eq_top_of_isPGroup_three {E : Type} [Group E] [Finite E] (hE : IsPGroup 3 E)
    (Q : Sylow 3 E) : (Q : Subgroup E) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  have hdvd : (Q : Subgroup E).index ∣ 3 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact Q.not_dvd_index (hk ▸ dvd_pow_self 3 hk0)
  rw [hk0, pow_zero] at hk
  exact Subgroup.index_eq_one.mp hk

theorem input28A7_holds : Input28A7 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hAlt
  classical
  obtain ⟨e⟩ := hAlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c.facts
  have hrank : CFSG.Open.pRank 3 Yp = 1 := c.ctx.rank
  have hHI : Yp ⊔ Sgp153 T V₁ ≤ I := c.ctx.inH.1.1
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hnorm : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hLI : L ≤ I := c.I_eq ▸ le_sup_left
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card ↥(Yp ⊔ Sgp153 T V₁) = 2 ^ a * 6 := by
    obtain ⟨φ, hφs, hφk⟩ := hF.s3
    have hR2 : IsPGroup 2 (R153 T V₁ Yp) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨a, ha⟩ := hR2.exists_card_eq
    have hRle : R153 T V₁ Yp ≤ Yp ⊔ Sgp153 T V₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv, ha] at h1
    have h6 : Nat.card φ.range = 6 := by
      rw [MonoidHom.range_eq_top.mpr hφs, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_perm,
        Nat.card_fin]
      rfl
    rw [h6] at h1
    exact ⟨a, h1.symm⟩
  have h5 : ¬ 5 ∣ Nat.card ↥(Yp ⊔ Sgp153 T V₁) := by
    rw [ha]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
      omega
    · omega
  have h7 : ¬ 7 ∣ Nat.card ↥(Yp ⊔ Sgp153 T V₁) := by
    rw [ha]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
      omega
    · omega
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ _
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hUN
  let act : ↥I →* MulAut ↥(UI153 T I) := A4.actionOn (UI153 T I) I hUN
  have hkey : ∀ y : ↥I, ∀ b ∈ Star153 T I L, act y * b * (act y)⁻¹ ∈ Star153 T I L := by
    intro y b hb
    obtain ⟨ℓ, hℓ⟩ := (A4.mem_autOn_iff hLU).mp hb
    have hyl : (y : G) * (ℓ : G) * (y : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hnorm y.2) ℓ).mp ℓ.2
    refine (A4.mem_autOn_iff hLU).mpr ⟨⟨(y : G) * ℓ * (y : G)⁻¹, hyl⟩, ?_⟩
    rw [← hℓ]
    have h1 : act (y * ⟨(ℓ : G), hLI ℓ.2⟩ * y⁻¹) =
        A4.actionOn (UI153 T I) L hLU ⟨(y : G) * ℓ * (y : G)⁻¹, hyl⟩ := rfl
    rw [← h1, map_mul, map_mul, map_inv]
    rfl
  have hyN : ∀ y : ↥I, act y ∈ Subgroup.normalizer
      ((Star153 T I L : Subgroup (MulAut ↥(UI153 T I))) : Set (MulAut ↥(UI153 T I))) := by
    intro y
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => hkey y b hb, fun hb => ?_⟩
    have h1 := hkey y⁻¹ _ hb
    have e1 : act y⁻¹ * (act y * b * (act y)⁻¹) * (act y⁻¹)⁻¹ = b := by
      rw [map_inv]
      group
    rwa [e1] at h1
  obtain ⟨ν₀, hν₀⟩ := exists_hom_perm_extending_alt (Star153 T I L) e
  let ν : ↥I →* Perm (Fin 7) := ν₀.comp (act.codRestrict _ hyN)
  have hν2 : ∀ σ ∈ alternatingGroup (Fin 7), ∃ x : ↥I, (x : G) ∈ L ∧ ν x = σ := by
    intro σ hσ
    obtain ⟨ℓ, hℓ⟩ := (A4.mem_autOn_iff hLU).mp (e.symm ⟨σ, hσ⟩).2
    refine ⟨⟨(ℓ : G), hLI ℓ.2⟩, ℓ.2, ?_⟩
    have h1 := hν₀ (e.symm ⟨σ, hσ⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : ν ⟨(ℓ : G), hLI ℓ.2⟩ = ν₀ ⟨((e.symm ⟨σ, hσ⟩ : ↥(Star153 T I L)) :
        MulAut ↥(UI153 T I)), Subgroup.le_normalizer (e.symm ⟨σ, hσ⟩).2⟩ := by
      show ν₀ ⟨act ⟨(ℓ : G), hLI ℓ.2⟩, _⟩ = _
      congr 1
      exact Subtype.ext hℓ
    rw [h2]
    exact h1
  let H' : Subgroup ↥I := (Yp ⊔ Sgp153 T V₁).subgroupOf I
  have hcardH' : Nat.card ↥H' = Nat.card ↥(Yp ⊔ Sgp153 T V₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHI).toEquiv
  have h5' : ¬ 5 ∣ Nat.card ↥(H'.map ν) := fun h =>
    h5 ((h.trans (Subgroup.card_map_dvd H' ν)).trans hcardH'.dvd)
  have h7' : ¬ 7 ∣ Nat.card ↥(H'.map ν) := fun h =>
    h7 ((h.trans (Subgroup.card_map_dvd H' ν)).trans hcardH'.dvd)
  obtain ⟨Kb, hHK, hAK, E, hEK, hEp, hEc⟩ := exists_overgroup_of_card_coprime h5' h7'
  let K : Subgroup G := (Kb.comap ν).map I.subtype
  have hYSK : Yp ⊔ Sgp153 T V₁ ≤ K := fun h hh =>
    ⟨⟨h, hHI hh⟩, hHK ⟨⟨h, hHI hh⟩, hh, rfl⟩, rfl⟩
  have hKI : K ≤ I := Subgroup.map_subtype_le _
  have hKne : K ≠ I := by
    intro hKeq
    obtain ⟨σ, hσA, hσK⟩ : ∃ σ ∈ alternatingGroup (Fin 7), σ ∉ Kb := by
      by_contra hcon
      push Not at hcon
      exact hAK hcon
    obtain ⟨x, hxL, hx⟩ := hν2 σ hσA
    have hxK : (x : G) ∈ K := hKeq.symm.le x.2
    obtain ⟨x', hx'K, hx'x⟩ := hxK
    have : x' = x := Subtype.ext hx'x
    rw [this] at hx'K
    exact hσK (hx ▸ hx'K)
  have hKM : K ≤ M ⊓ I := c.unique_max K hYSK (lt_of_le_of_ne hKI hKne)
  let F : Subgroup ↥I := E.comap ν ⊓ L.subgroupOf I
  let ρ : ↥F →* ↥E := (ν.comp F.subtype).codRestrict E (fun x => x.2.1)
  have hρ : Function.Surjective ρ := by
    intro e'
    have hEA : (e' : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := (hEK e'.2).2
    obtain ⟨x, hxL, hx⟩ := hν2 e' hEA
    exact ⟨⟨x, ⟨show ν x ∈ E by rw [hx]; exact e'.2, hxL⟩⟩, Subtype.ext hx⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥F) := inferInstance
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPtop : ((P.mapSurjective hρ : Sylow 3 ↥E) : Subgroup ↥E) = ⊤ :=
    sylow_eq_top_of_isPGroup_three hEp _
  have hPmap : (P : Subgroup ↥F).map ρ = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact hPtop
  let ι : ↥(P : Subgroup ↥F) →* G := I.subtype.comp (F.subtype.comp (P : Subgroup ↥F).subtype)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  have hιY : ι.range ≤ Yp := by
    rintro _ ⟨p, rfl⟩
    have hp3 := (P.isPGroup' : IsPGroup 3 (P : Subgroup ↥F)) p
    obtain ⟨k, hk⟩ := hp3
    have hord : orderOf (ι p) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    have hxK : (ι p) ∈ K := ⟨(p : ↥F).1, (p : ↥F).2.1 |> fun h => hEK h |>.1, rfl⟩
    rw [hF.yp_eq]
    exact Subgroup.subset_closure ⟨hKM hxK, j, hj⟩
  have hcyc : IsCyclic ↥(P : Subgroup ↥F) :=
    isCyclic_of_isPGroup_of_range_le P.isPGroup' ι hι hιY hrank.le
  have hsurj : Function.Surjective (ρ.comp (P : Subgroup ↥F).subtype) := by
    intro e'
    have : e' ∈ (P : Subgroup ↥F).map ρ := by rw [hPmap]; trivial
    obtain ⟨p, hp, hpe⟩ := this
    exact ⟨⟨p, hp⟩, hpe⟩
  exact hEc (isCyclic_of_surjective _ hsurj)

end CFSG.Quasithin
