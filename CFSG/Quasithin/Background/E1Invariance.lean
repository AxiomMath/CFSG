module

public import CFSG.Quasithin.Background.E1Inherit
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

section Transport

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem map_eq_top_iff_mulEquiv (e : Q ≃* Q') (K : Subgroup Q) :
    K.map e.toMonoidHom = ⊤ ↔ K = ⊤ := by
  constructor
  · intro h
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro rfl
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem map_eq_bot_iff_mulEquiv (e : Q ≃* Q') (K : Subgroup Q) :
    K.map e.toMonoidHom = ⊥ ↔ K = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective K (f := e.toMonoidHom) e.injective

theorem map_inj_mulEquiv (e : Q ≃* Q') {K L : Subgroup Q} :
    K.map e.toMonoidHom = L.map e.toMonoidHom ↔ K = L :=
  (Subgroup.map_injective (f := e.toMonoidHom) e.injective).eq_iff

theorem map_le_map_iff_mulEquiv (e : Q ≃* Q') {K L : Subgroup Q} :
    K.map e.toMonoidHom ≤ L.map e.toMonoidHom ↔ K ≤ L :=
  Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective

private theorem map_eq_of_map_le (e : Q ≃* Q') {A : Subgroup Q} {A' : Subgroup Q'}
    (h₁ : A.map e.toMonoidHom ≤ A') (h₂ : A'.map e.symm.toMonoidHom ≤ A) :
    A.map e.toMonoidHom = A' := by
  refine le_antisymm h₁ ?_
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact Subgroup.map_le_iff_le_comap.mp h₂

private theorem map_comap_mk'_congr (e : Q ≃* Q') {N : Subgroup Q} {N' : Subgroup Q'}
    [N.Normal] [N'.Normal] (h : N.map e.toMonoidHom = N') {R : Subgroup (Q ⧸ N)}
    {R' : Subgroup (Q' ⧸ N')} (hR : R.map (QuotientGroup.congr N N' e h).toMonoidHom = R') :
    (R.comap (QuotientGroup.mk' N)).map e.toMonoidHom = R'.comap (QuotientGroup.mk' N') := by
  ext x'
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap, ← hR,
    Subgroup.mem_map_equiv]
  rfl

private theorem map_map_mk'_congr (e : Q ≃* Q') {N : Subgroup Q} {N' : Subgroup Q'}
    [N.Normal] [N'.Normal] (h : N.map e.toMonoidHom = N') (B : Subgroup Q) :
    (B.map (QuotientGroup.mk' N)).map (QuotientGroup.congr N N' e h).toMonoidHom =
      (B.map e.toMonoidHom).map (QuotientGroup.mk' N') := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem exists_subgroup_congr (e : Q ≃* Q') {P : Subgroup Q → Prop}
    {P' : Subgroup Q' → Prop} (h : ∀ L, P L ↔ P' (L.map e.toMonoidHom)) :
    (∃ L, P L) ↔ ∃ L', P' L' := by
  refine ⟨fun ⟨L, hL⟩ => ⟨_, (h L).mp hL⟩, fun ⟨L', hL'⟩ => ⟨L'.map e.symm.toMonoidHom,
    (h _).mpr ?_⟩⟩
  have : (L'.map e.symm.toMonoidHom).map e.toMonoidHom = L' := by
    simpa using CFSG.LocalCores.map_map_symm e.symm L'
  rwa [this]

theorem oTwoP_map_mulEquiv (e : Q ≃* Q') (p : ℕ) :
    (oTwoP Q p).map e.toMonoidHom = oTwoP Q' p :=
  map_comap_mk'_congr e (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv p _)

theorem oTwoPTwo_map_mulEquiv (e : Q ≃* Q') (p : ℕ) :
    (oTwoPTwo Q p).map e.toMonoidHom = oTwoPTwo Q' p :=
  map_comap_mk'_congr e (oTwoP_map_mulEquiv e p)
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 _)

private theorem solvableRadical_map_le (e : Q ≃* Q') :
    (CFSG.solvableRadical Q).map e.toMonoidHom ≤ CFSG.solvableRadical Q' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have : Group.IsSolvable N := hN.2
  refine le_sSup ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap N)
    (e.toMonoidHom.subgroupMap_surjective N)

theorem solvableRadical_map_mulEquiv (e : Q ≃* Q') :
    (CFSG.solvableRadical Q).map e.toMonoidHom = CFSG.solvableRadical Q' :=
  map_eq_of_map_le e (solvableRadical_map_le e) (solvableRadical_map_le e.symm)

theorem layer_map_mulEquiv (e : Q ≃* Q') : (CFSG.layer Q).map e.toMonoidHom = CFSG.layer Q' :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem oInftyE_map_mulEquiv (e : Q ≃* Q') : (oInftyE Q).map e.toMonoidHom = oInftyE Q' :=
  map_comap_mk'_congr e (solvableRadical_map_mulEquiv e) (layer_map_mulEquiv _)

private theorem twoResidual_map_le [Finite Q] [Finite Q'] (e : Q ≃* Q') (H : Subgroup Q) :
    (twoResidual H).map e.toMonoidHom ≤ twoResidual (H.map e.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine twoResidual_le_of_isTwoQuotient ?_ ?_ ?_
  · intro x hx
    have hx' : e x ∈ H.map e.toMonoidHom := twoResidual_le _ hx
    simpa using hx'
  · intro h hh
    have hex : e h ∈ Subgroup.normalizer (twoResidual (H.map e.toMonoidHom) : Set Q') :=
      le_normalizer_twoResidual _ (Subgroup.mem_map_of_mem _ hh)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have := Subgroup.mem_normalizer_iff.mp hex (e n)
    simpa [Subgroup.mem_comap] using this
  · intro y hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (H.map e.toMonoidHom) (e y)
      (Subgroup.mem_map_of_mem _ hy)
    exact ⟨k, by simpa [Subgroup.mem_comap, map_pow] using hk⟩

theorem twoResidual_map_mulEquiv [Finite Q] [Finite Q'] (e : Q ≃* Q') (H : Subgroup Q) :
    (twoResidual H).map e.toMonoidHom = twoResidual (H.map e.toMonoidHom) := by
  refine map_eq_of_map_le e (twoResidual_map_le e H) ?_
  have := twoResidual_map_le e.symm (H.map e.toMonoidHom)
  rwa [CFSG.LocalCores.map_map_symm] at this

theorem isSylowIn_map_of_injective {p : ℕ} {f : Q →* Q'} (hf : Function.Injective f)
    {P H : Subgroup Q} : IsSylowIn p (P.map f) (H.map f) ↔ IsSylowIn p P H := by
  unfold IsSylowIn
  rw [Subgroup.map_le_map_iff_of_injective hf, Subgroup.relIndex_map_map_of_injective _ _ hf]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  exact ⟨fun h => h.of_equiv (Subgroup.equivMapOfInjective P f hf).symm, fun h => h.map _⟩

theorem isSylowIn_map_mulEquiv {p : ℕ} (e : Q ≃* Q') {P H : Subgroup Q} :
    IsSylowIn p (P.map e.toMonoidHom) (H.map e.toMonoidHom) ↔ IsSylowIn p P H :=
  isSylowIn_map_of_injective (f := e.toMonoidHom) e.injective

private theorem isTwoClosed_map (e : Q ≃* Q') {R : Subgroup Q} (h : IsTwoClosed R) :
    IsTwoClosed (R.map e.toMonoidHom) := by
  obtain ⟨P, hP, hn⟩ := h
  refine ⟨P.map e.toMonoidHom, (isSylowIn_map_mulEquiv e).mpr hP, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hP.le] at hn
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hP.le)]
  rintro _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
  exact ⟨k * h * k⁻¹, hn h k hh hk, by rw [map_mul, map_mul, map_inv]⟩

theorem isTwoClosed_map_mulEquiv (e : Q ≃* Q') (R : Subgroup Q) :
    IsTwoClosed (R.map e.toMonoidHom) ↔ IsTwoClosed R := by
  refine ⟨fun h => ?_, isTwoClosed_map e⟩
  have := isTwoClosed_map e.symm h
  rwa [CFSG.LocalCores.map_map_symm] at this

end Transport

section Tau

variable {G G' : Type*} [Group G] [Group G']

theorem tauOf_map_mulEquiv (e : G ≃* G') (H T A : Subgroup G) :
    tauOf (H.map e.toMonoidHom) (T.map e.toMonoidHom) (A.map e.toMonoidHom) =
      (tauOf H T A).map e.toMonoidHom := by
  have hP := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e H
  ext t'
  rw [Subgroup.mem_map_equiv, mem_tauOf, mem_tauOf, hP, ← Subgroup.map_equiv_normalizer_eq]
  simp only [Subgroup.mem_map_equiv]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h a ha
    have h1 := h (e a) (by simpa using ha)
    simpa [map_commutatorElement] using h1
  · intro h a' ha'
    have h1 := h (e.symm a') ha'
    simpa [map_commutatorElement] using h1

theorem tauOf_top_map_mulEquiv (e : G ≃* G') (S B : Subgroup G) :
    (tauOf ⊤ S B).map e.toMonoidHom = tauOf ⊤ (S.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  rw [← tauOf_map_mulEquiv, Subgroup.map_top_of_surjective _ e.surjective]

theorem map_conjSub (f : G →* G') (t : G) (X : Subgroup G) :
    (conjSub t X).map f = conjSub (f t) (X.map f) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem map_biSup_conjSub (e : G ≃* G') (X L : Subgroup G) :
    (⨆ t ∈ X, conjSub t L).map e.toMonoidHom =
      ⨆ t ∈ X.map e.toMonoidHom, conjSub t (L.map e.toMonoidHom) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun t ht => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_conjSub]
    exact le_iSup₂_of_le _ (Subgroup.mem_map_of_mem _ ht) le_rfl
  · refine iSup₂_le fun t' ht' => ?_
    obtain ⟨t, ht, rfl⟩ := ht'
    rw [← map_conjSub]
    exact Subgroup.map_mono (le_iSup₂_of_le t ht le_rfl)

end Tau

section Conditions

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem card_barO2_map (e : Q ≃* Q') (B : Subgroup Q) :
    Nat.card (barO2 Q' (B.map e.toMonoidHom)) = Nat.card (barO2 Q B) := by
  have h := map_map_mk'_congr e (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e) B
  unfold barO2
  rw [← h]
  exact Subgroup.card_map_of_injective (QuotientGroup.congr _ _ e _).injective

theorem card_barRad_map (e : Q ≃* Q') (B : Subgroup Q) :
    Nat.card (barRad Q' (B.map e.toMonoidHom)) = Nat.card (barRad Q B) := by
  have h := map_map_mk'_congr e (solvableRadical_map_mulEquiv e) B
  unfold barRad
  rw [← h]
  exact Subgroup.card_map_of_injective (QuotientGroup.congr _ _ e _).injective

theorem eOne_map (e : Q ≃* Q') (B : Subgroup Q) :
    EOne Q B ↔ EOne Q' (B.map e.toMonoidHom) := by
  have hO : (CFSG.Open.pCore 2 Q).map e.toMonoidHom = CFSG.Open.pCore 2 Q' :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  have hbar : (barO2 Q B).map (QuotientGroup.congr _ _ e hO).toMonoidHom =
      barO2 Q' (B.map e.toMonoidHom) := map_map_mk'_congr e hO B
  unfold EOne
  refine exists_congr fun p => and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_
    (and_congr ?_ (and_congr ?_ ?_))))
  · rw [← oTwoPTwo_map_mulEquiv e p, map_eq_top_iff_mulEquiv]
  · have hp := CFSG.LieType.BorelTits.map_pCore_mulEquiv p (QuotientGroup.congr _ _ e hO)
    rw [← hp, Ne, Ne, map_eq_bot_iff_mulEquiv]
  · have hp := CFSG.LieType.BorelTits.map_pCore_mulEquiv p (QuotientGroup.congr _ _ e hO)
    rw [← hp, ← hbar, ← Subgroup.map_commutator, map_inj_mulEquiv]
  · rw [card_barO2_map]

theorem eTwo_map [Finite Q] [Finite Q'] (e : Q ≃* Q') (S B : Subgroup Q) :
    ETwo Q S B ↔ ETwo Q' (S.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have hR := solvableRadical_map_mulEquiv e
  have hO := oInftyE_map_mulEquiv e
  have hbar : (barRad Q B).map (QuotientGroup.congr _ _ e hR).toMonoidHom =
      barRad Q' (B.map e.toMonoidHom) := map_map_mk'_congr e hR B
  unfold ETwo
  refine and_congr (by rw [← hR, isTwoClosed_map_mulEquiv]) (and_congr ?_ (and_congr ?_ ?_))
  · rw [← map_eq_top_iff_mulEquiv (QuotientGroup.congr _ _ e hO),
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (QuotientGroup.congr _ _ e hO)]
  · have h1 : (twoResidual (⊤ : Subgroup Q)).map e.toMonoidHom = twoResidual (⊤ : Subgroup Q') := by
      rw [twoResidual_map_mulEquiv, Subgroup.map_top_of_surjective _ e.surjective]
    have h2 : (perfectCore (⊤ : Subgroup Q)).map e.toMonoidHom = perfectCore (⊤ : Subgroup Q') := by
      rw [map_perfectCore, Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h1, ← h2, map_inj_mulEquiv]
  · refine exists_subgroup_congr (QuotientGroup.congr _ _ e hR) fun L => ?_
    have hτ : ((tauOf ⊤ S B).map (QuotientGroup.mk' (solvableRadical Q))).map
        (QuotientGroup.congr _ _ e hR).toMonoidHom =
        (tauOf ⊤ (S.map e.toMonoidHom) (B.map e.toMonoidHom)).map
          (QuotientGroup.mk' (solvableRadical Q')) := by
      rw [map_map_mk'_congr e hR, tauOf_top_map_mulEquiv]
    refine and_congr ((CFSG.LocalCores.component_isomorphism _).1 L) (and_congr ?_ ?_)
    · rw [← map_inj_mulEquiv (QuotientGroup.congr _ _ e hR), layer_map_mulEquiv,
        map_biSup_conjSub, hτ]
    · rw [card_barRad_map, ← hbar, ← Subgroup.map_commutator, map_inj_mulEquiv,
        ← Subgroup.map_equiv_normalizer_eq, map_le_map_iff_mulEquiv]

end Conditions

section Ambient

variable {G G' : Type*} [Group G] [Group G']

private abbrev restrictEquiv (e : G ≃* G') (K : Subgroup G) : ↥K ≃* ↥(K.map e.toMonoidHom) :=
  e.subgroupMap K

private theorem map_subgroupOf_restrictEquiv (e : G ≃* G') (A K : Subgroup G) :
    (A.subgroupOf K).map (restrictEquiv e K).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_map_equiv]
  exact Iff.rfl

theorem isE_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') {i : ℕ} {H T A K : Subgroup G} :
    IsE i (H.map e.toMonoidHom) (T.map e.toMonoidHom) (A.map e.toMonoidHom)
      (K.map e.toMonoidHom) ↔ IsE i H T A K := by
  unfold IsE
  rw [← Subgroup.map_inf T K e.toMonoidHom e.injective, tauOf_map_mulEquiv,
    ← map_subgroupOf_restrictEquiv e A K, ← map_subgroupOf_restrictEquiv e (T ⊓ K) K,
    map_le_map_iff_mulEquiv, map_le_map_iff_mulEquiv, isSylowIn_map_mulEquiv,
    ← eOne_map, ← eTwo_map, card_barO2_map, card_barRad_map]

theorem isE_conj [Finite G] (g : G) {i : ℕ} {H T A K : Subgroup G} :
    IsE i (conjSub g H) (conjSub g T) (conjSub g A) (conjSub g K) ↔ IsE i H T A K :=
  isE_map_mulEquiv (MulAut.conj g)

theorem isEAny_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') {H T A K : Subgroup G} :
    IsEAny (H.map e.toMonoidHom) (T.map e.toMonoidHom) (A.map e.toMonoidHom)
      (K.map e.toMonoidHom) ↔ IsEAny H T A K :=
  exists_congr fun _ => isE_map_mulEquiv e

theorem isEAny_conj [Finite G] (g : G) {H T A K : Subgroup G} :
    IsEAny (conjSub g H) (conjSub g T) (conjSub g A) (conjSub g K) ↔ IsEAny H T A K :=
  isEAny_map_mulEquiv (MulAut.conj g)

theorem tauOf_conj (g : G) (H T A : Subgroup G) :
    tauOf (conjSub g H) (conjSub g T) (conjSub g A) = conjSub g (tauOf H T A) :=
  tauOf_map_mulEquiv (MulAut.conj g) H T A

theorem isSylowIn_conj_iff {p : ℕ} (g : G) {P H : Subgroup G} :
    IsSylowIn p (conjSub g P) (conjSub g H) ↔ IsSylowIn p P H :=
  isSylowIn_map_mulEquiv (MulAut.conj g)

theorem weakClosure_map_image_of_injective {f : G →* G'} (hf : Function.Injective f)
    (X : Subgroup G) (Ω : Set (Subgroup G)) :
    weakClosure (X.map f) (Subgroup.map f '' Ω) = (weakClosure X Ω).map f := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'X => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    exact Subgroup.map_mono (le_iSup₂_of_le A hA
      (le_iSup_of_le ((Subgroup.map_le_map_iff_of_injective hf).mp hA'X) le_rfl))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map f) ⟨A, hA, rfl⟩ (le_iSup_of_le (Subgroup.map_mono hAX) le_rfl)

theorem weakClosure_map_image (e : G ≃* G') (X : Subgroup G) (Ω : Set (Subgroup G)) :
    weakClosure (X.map e.toMonoidHom) (Subgroup.map e.toMonoidHom '' Ω) =
      (weakClosure X Ω).map e.toMonoidHom :=
  weakClosure_map_image_of_injective (f := e.toMonoidHom) e.injective X Ω

private theorem exists_map_eq (e : G ≃* G') (K' : Subgroup G') :
    ∃ K : Subgroup G, K.map e.toMonoidHom = K' :=
  ⟨K'.comap e.toMonoidHom, Subgroup.map_comap_eq_self_of_surjective e.surjective K'⟩

theorem mem_sFamily_map_iff (e : G ≃* G') {T X Y K : Subgroup G} :
    K.map e.toMonoidHom ∈
        sFamily (T.map e.toMonoidHom) (X.map e.toMonoidHom) (Y.map e.toMonoidHom) ↔
      K ∈ sFamily T X Y := by
  have hsup : ∀ A B : Subgroup G,
      A.map e.toMonoidHom ⊔ B.map e.toMonoidHom = (A ⊔ B).map e.toMonoidHom :=
    fun A B => (Subgroup.map_sup A B _).symm
  unfold sFamily
  simp only [Set.mem_ofPred_eq, hsup]
  refine and_congr (map_le_map_iff_mulEquiv e) (and_congr (map_le_map_iff_mulEquiv e)
    (and_congr (map_inj_mulEquiv e) ⟨fun h K'' h1 h2 h3 h4 => ?_, fun h K' h1 h2 h3 h4 => ?_⟩))
  · refine (map_inj_mulEquiv e).mp (h (K''.map e.toMonoidHom)
      ((map_le_map_iff_mulEquiv e).mpr h1) ((map_le_map_iff_mulEquiv e).mpr h2) ?_
      ((map_le_map_iff_mulEquiv e).mpr h4))
    rw [hsup, map_inj_mulEquiv]
    exact h3
  · obtain ⟨K'', rfl⟩ := exists_map_eq e K'
    rw [hsup, map_inj_mulEquiv] at h3
    rw [map_le_map_iff_mulEquiv] at h1 h2 h4
    rw [h K'' h1 h2 h3 h4]

theorem sFamily_map_mulEquiv (e : G ≃* G') (T X Y : Subgroup G) :
    sFamily (T.map e.toMonoidHom) (X.map e.toMonoidHom) (Y.map e.toMonoidHom) =
      Subgroup.map e.toMonoidHom '' sFamily T X Y := by
  ext K'
  obtain ⟨K, rfl⟩ := exists_map_eq e K'
  rw [mem_sFamily_map_iff]
  exact ⟨fun h => ⟨K, h, rfl⟩, fun ⟨K₀, hK₀, h⟩ => by rwa [← (map_inj_mulEquiv e).mp h]⟩

theorem sFamily_conj (g : G) (T X Y : Subgroup G) :
    sFamily (conjSub g T) (conjSub g X) (conjSub g Y) = conjSub g '' sFamily T X Y :=
  sFamily_map_mulEquiv (MulAut.conj g) T X Y

theorem eGen_map_image [Finite G] [Finite G'] (e : G ≃* G') (i : ℕ) (H T : Subgroup G)
    (Ω : Set (Subgroup G)) :
    eGen i (H.map e.toMonoidHom) (T.map e.toMonoidHom) (Subgroup.map e.toMonoidHom '' Ω) =
      (eGen i H T Ω).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨K, rfl⟩ := exists_map_eq e K'
    have hK : IsE i H T A K := (isE_map_mulEquiv e).mp hK'
    exact Subgroup.map_mono (le_iSup₂_of_le A hA (le_iSup_of_le
      ((map_le_map_iff_mulEquiv e).mp hA'T) (le_iSup₂_of_le K hK le_rfl)))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map e.toMonoidHom) ⟨A, hA, rfl⟩ (le_iSup_of_le
      (Subgroup.map_mono hAT) (le_iSup₂_of_le (K.map e.toMonoidHom)
        ((isE_map_mulEquiv e).mpr hK) le_rfl))

theorem weakClosure_conj_image (g : G) (X : Subgroup G) (Ω : Set (Subgroup G)) :
    weakClosure (conjSub g X) (conjSub g '' Ω) = conjSub g (weakClosure X Ω) :=
  weakClosure_map_image (MulAut.conj g) X Ω

theorem eGen_conj_image [Finite G] (i : ℕ) (g : G) (H T : Subgroup G) (Ω : Set (Subgroup G)) :
    eGen i (conjSub g H) (conjSub g T) (conjSub g '' Ω) = conjSub g (eGen i H T Ω) :=
  eGen_map_image (MulAut.conj g) i H T Ω

private theorem conjSub_inv_left_cancel (g : G) (X : Subgroup G) :
    conjSub g⁻¹ (conjSub g X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

private theorem conjSub_inv_right_cancel (g : G) (X : Subgroup G) :
    conjSub g (conjSub g⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

private theorem image_conjSub_eq {g : G} {Ω : Set (Subgroup G)} (h₁ : ∀ A ∈ Ω, conjSub g A ∈ Ω)
    (h₂ : ∀ A ∈ Ω, conjSub g⁻¹ A ∈ Ω) : conjSub g '' Ω = Ω := by
  ext A
  exact ⟨by rintro ⟨B, hB, rfl⟩; exact h₁ B hB,
    fun hA => ⟨conjSub g⁻¹ A, h₂ A hA, conjSub_inv_right_cancel g A⟩⟩

private theorem exists_eq_image_conjSub (g : G) (Ω' : Set (Subgroup G)) :
    ∃ Ω : Set (Subgroup G), Ω' = conjSub g '' Ω := by
  refine ⟨conjSub g⁻¹ '' Ω', ?_⟩
  ext A
  exact ⟨fun hA => ⟨conjSub g⁻¹ A, ⟨A, hA, rfl⟩, conjSub_inv_right_cancel g A⟩, by
    rintro ⟨B, ⟨C, hC, rfl⟩, rfl⟩
    rwa [conjSub_inv_right_cancel]⟩

theorem weakClosure_conj (g : G) (X : Subgroup G) {Ω : Set (Subgroup G)}
    (h₁ : ∀ A ∈ Ω, conjSub g A ∈ Ω) (h₂ : ∀ A ∈ Ω, conjSub g⁻¹ A ∈ Ω) :
    weakClosure (conjSub g X) Ω = conjSub g (weakClosure X Ω) := by
  have h := weakClosure_conj_image g X Ω
  rwa [image_conjSub_eq h₁ h₂] at h

theorem eGen_conj [Finite G] (i : ℕ) (g : G) (H T : Subgroup G) {Ω : Set (Subgroup G)}
    (h₁ : ∀ A ∈ Ω, conjSub g A ∈ Ω) (h₂ : ∀ A ∈ Ω, conjSub g⁻¹ A ∈ Ω) :
    eGen i (conjSub g H) (conjSub g T) Ω = conjSub g (eGen i H T Ω) := by
  have h := eGen_conj_image i g H T Ω
  rwa [image_conjSub_eq h₁ h₂] at h

private theorem isElemAbelian_map {p : ℕ} (f : G →* G') {A : Subgroup G}
    (h : IsElemAbelian p A) : IsElemAbelian p (A.map f) := CFSG.Open.IsElemAbelian.map h _

private theorem isInvColl_conj_image {g : G} {H : Subgroup G} {Ω : Set (Subgroup G)}
    (h : IsInvColl H Ω) : IsInvColl (conjSub g H) (conjSub g '' Ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact conjSub_mono g (h.le A hA)
  · rintro _ ⟨A, hA, rfl⟩
    exact isElemAbelian_map _ (h.isElemAbelian A hA)
  · rintro _ ⟨A, hA, rfl⟩ h' hh'
    rw [mem_conjSub_iff] at hh'
    refine ⟨conjSub (g⁻¹ * h' * g) A, h.conj A hA _ hh', ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group

private theorem image_image_conjSub (g : G) (Ω : Set (Subgroup G)) :
    conjSub g⁻¹ '' (conjSub g '' Ω) = Ω := by
  ext A
  exact ⟨by rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩; rwa [conjSub_inv_left_cancel],
    fun hA => ⟨conjSub g A, ⟨A, hA, rfl⟩, conjSub_inv_left_cancel g A⟩⟩

theorem isInvColl_conj (g : G) {H : Subgroup G} {Ω : Set (Subgroup G)} :
    IsInvColl (conjSub g H) (conjSub g '' Ω) ↔ IsInvColl H Ω := by
  refine ⟨fun h => ?_, isInvColl_conj_image⟩
  have := isInvColl_conj_image (g := g⁻¹) h
  rwa [conjSub_inv_left_cancel, image_image_conjSub] at this

private theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup X Y _

private theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf X Y _ (MulAut.conj g).injective

private theorem inEFor_conj_of [Finite G] {i : ℕ} (g : G) {H T : Subgroup G} (h : InEFor i H T) :
    InEFor i (conjSub g H) (conjSub g T) := by
  intro Ω' hΩ'
  obtain ⟨Ω, rfl⟩ := exists_eq_image_conjSub g Ω'
  have key := congrArg (conjSub g) (h Ω ((isInvColl_conj g).mp hΩ'))
  rw [conjSub_sup, conjSub_inf, conjSub_normalizer] at key
  rw [eGen_conj_image, weakClosure_conj_image]
  exact key

theorem inEFor_conj_iff [Finite G] (i : ℕ) (g : G) (H T : Subgroup G) :
    InEFor i (conjSub g H) (conjSub g T) ↔ InEFor i H T := by
  refine ⟨fun h => ?_, inEFor_conj_of g⟩
  have := inEFor_conj_of g⁻¹ h
  rwa [conjSub_inv_left_cancel, conjSub_inv_left_cancel] at this

theorem inEFor_conj [Finite G] {i : ℕ} {H T : Subgroup G} {g : G} (hg : g ∈ H)
    (h : InEFor i H T) : InEFor i H (conjSub g T) := by
  have := inEFor_conj_of g h
  rwa [conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)] at this

theorem inE_iff_inEFor [Finite G] {i : ℕ} {H T : Subgroup G} (hT : IsSylowIn 2 T H) :
    InE i H ↔ InEFor i H T := by
  refine ⟨fun h => h T hT, fun h T' hT' => ?_⟩
  obtain ⟨g, hg, rfl⟩ := B6.isSylowTwoOf_exists_conj hT hT'
  exact inEFor_conj hg h

theorem inE_conj [Finite G] (i : ℕ) (g : G) (H : Subgroup G) :
    InE i (conjSub g H) ↔ InE i H := by
  constructor
  · intro h T hT
    exact (inEFor_conj_iff i g H T).mp (h _ ((isSylowIn_conj_iff g).mpr hT))
  · intro h T' hT'
    have hT : IsSylowIn 2 (conjSub g⁻¹ T') H := by
      have := (isSylowIn_conj_iff g⁻¹).mpr hT'
      rwa [conjSub_inv_left_cancel] at this
    have := (inEFor_conj_iff i g H (conjSub g⁻¹ T')).mpr (h _ hT)
    rwa [conjSub_inv_right_cancel] at this

theorem nParam_conj [Finite G] (g : G) (H : Subgroup G) : nParam (conjSub g H) = nParam H := by
  have hcard : Nat.card ↥(conjSub g H) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  unfold nParam
  simp only [hcard, inE_conj]

theorem exists_isSylowIn_two [Finite G] (H : Subgroup G) : ∃ T : Subgroup G, IsSylowIn 2 T H := by
  obtain ⟨T, hT, -⟩ := exists_isSylowIn_ge 2 (bot_le : (⊥ : Subgroup G) ≤ H) IsPGroup.of_bot
  exact ⟨T, hT⟩

end Ambient

section Restriction

variable {G : Type*} [Group G]

theorem pCoreOf_top_eq (p : ℕ) (X : Type*) [Group X] :
    pCoreOf p (⊤ : Subgroup X) = CFSG.Open.pCore p X := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p (Subgroup.topEquiv (G := X)).symm,
    Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom =
      MonoidHom.id X := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem map_subtype_pCoreOf_top (H : Subgroup G) :
    (pCoreOf 2 (⊤ : Subgroup ↥H)).map H.subtype = pCoreOf 2 H := by
  rw [pCoreOf_top_eq]
  rfl

private theorem subgroupOf_le_subgroupOf_iff {X Y H : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    X.subgroupOf H ≤ Y.subgroupOf H ↔ X ≤ Y := by
  rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

theorem isSylowIn_subgroupOf_iff {p : ℕ} {P K H : Subgroup G} (hP : P ≤ H) (hK : K ≤ H) :
    IsSylowIn p (P.subgroupOf H) (K.subgroupOf H) ↔ IsSylowIn p P K := by
  rw [← isSylowIn_map_of_injective H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hP,
    Subgroup.map_subgroupOf_eq_of_le hK]

theorem tauOf_top_subgroupOf {H T A : Subgroup G} (hT : T ≤ H) (hA : A ≤ H) :
    tauOf (⊤ : Subgroup ↥H) (T.subgroupOf H) (A.subgroupOf H) = (tauOf H T A).subgroupOf H := by
  ext t
  rw [mem_tauOf_of_le le_top]
  show _ ↔ (t : G) ∈ tauOf H T A
  rw [mem_tauOf_of_le hT]
  refine and_congr Iff.rfl ⟨fun h a ha => ?_, fun h a' ha' => ?_⟩
  · have h2 := Subgroup.mem_map_of_mem H.subtype (h ⟨a, hA ha⟩ ha)
    rw [map_subtype_pCoreOf_top] at h2
    simpa [map_commutatorElement] using h2
  · have h2 := h a' ha'
    rw [← map_subtype_pCoreOf_top] at h2
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp
      (by simpa [map_commutatorElement] using h2)

private theorem map_subgroupOf_subgroupOfEquivOfLe {K H : Subgroup G} (hK : K ≤ H)
    (B : Subgroup G) :
    ((B.subgroupOf H).subgroupOf (K.subgroupOf H)).map
        (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom = B.subgroupOf K := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Iff.rfl

theorem isE_subgroupOf [Finite G] {i : ℕ} {H T A K : Subgroup G} (hT : T ≤ H) (hA : A ≤ H)
    (hK : K ≤ H) :
    IsE i H T A K ↔
      IsE i (⊤ : Subgroup ↥H) (T.subgroupOf H) (A.subgroupOf H) (K.subgroupOf H) := by
  have hTK : (T ⊓ K).subgroupOf H = T.subgroupOf H ⊓ K.subgroupOf H := rfl
  have hTKH : T ⊓ K ≤ H := inf_le_left.trans hT
  have htau := tauOf_top_subgroupOf hT hA
  unfold IsE
  rw [← hTK, htau, subgroupOf_le_subgroupOf_iff ((tauOf_le H T A).trans hT) hTKH,
    isSylowIn_subgroupOf_iff hTKH hK,
    ← map_subgroupOf_subgroupOfEquivOfLe hK A, ← map_subgroupOf_subgroupOfEquivOfLe hK (T ⊓ K),
    ← eOne_map, ← eTwo_map, card_barO2_map, card_barRad_map]
  exact and_congr ⟨fun _ => le_top, fun _ => hK⟩ Iff.rfl

private theorem map_subtype_top (H : Subgroup G) : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem subgroupOf_map_subtype_eq (H : Subgroup G) (X' : Subgroup ↥H) :
    (X'.map H.subtype).subgroupOf H = X' :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective X'

theorem isE_map_subtype [Finite G] {i : ℕ} (H : Subgroup G) {T' A' K' : Subgroup ↥H} :
    IsE i H (T'.map H.subtype) (A'.map H.subtype) (K'.map H.subtype) ↔ IsE i ⊤ T' A' K' := by
  rw [isE_subgroupOf (Subgroup.map_subtype_le T') (Subgroup.map_subtype_le A')
    (Subgroup.map_subtype_le K'), subgroupOf_map_subtype_eq, subgroupOf_map_subtype_eq,
    subgroupOf_map_subtype_eq]

private theorem isElemAbelian_of_map_injective {G' : Type*} [Group G'] {p : ℕ} {f : G →* G'}
    (hf : Function.Injective f) {A : Subgroup G} (h : IsElemAbelian p (A.map f)) :
    IsElemAbelian p A := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := commute_of_isElemAbelian h (Subgroup.mem_map_of_mem f x.2)
      (Subgroup.mem_map_of_mem f y.2)
    exact hf (by simpa [map_mul] using this)
  · exact hf (by simpa [map_pow] using h.2 (f x) (Subgroup.mem_map_of_mem f hx))

theorem eGen_map_subtype [Finite G] (i : ℕ) (H : Subgroup G) (T' : Subgroup ↥H)
    (Ω' : Set (Subgroup ↥H)) :
    eGen i H (T'.map H.subtype) (Subgroup.map H.subtype '' Ω') =
      (eGen i ⊤ T' Ω').map H.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨K', rfl⟩ : ∃ K' : Subgroup ↥H, K = K'.map H.subtype :=
      ⟨K.subgroupOf H, (Subgroup.map_subgroupOf_eq_of_le hK.1).symm⟩
    have hK' : IsE i ⊤ T' A' K' := (isE_map_subtype H).mp hK
    exact Subgroup.map_mono (le_iSup₂_of_le A' hA' (le_iSup_of_le
      ((Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hAT)
        (le_iSup₂_of_le K' hK' le_rfl)))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A'.map H.subtype) ⟨A', hA', rfl⟩ (le_iSup_of_le
      (Subgroup.map_mono hA'T) (le_iSup₂_of_le (K'.map H.subtype)
        ((isE_map_subtype H).mpr hK') le_rfl))

private theorem map_subtype_top_inf_normalizer (H : Subgroup G) (W' : Subgroup ↥H) :
    (⊤ ⊓ Subgroup.normalizer (W' : Set ↥H)).map H.subtype =
      H ⊓ Subgroup.normalizer (W'.map H.subtype : Set G) := by
  rw [top_inf_eq]
  have h := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le W')
  rw [subgroupOf_map_subtype_eq] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

private theorem isInvColl_map_subtype {H : Subgroup G} {Ω' : Set (Subgroup ↥H)}
    (h : IsInvColl (⊤ : Subgroup ↥H) Ω') : IsInvColl H (Subgroup.map H.subtype '' Ω') := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨A', -, rfl⟩
    exact Subgroup.map_subtype_le A'
  · rintro _ ⟨A', hA', rfl⟩
    exact isElemAbelian_map _ (h.isElemAbelian A' hA')
  · rintro _ ⟨A', hA', rfl⟩ x hx
    exact ⟨conjSub ⟨x, hx⟩ A', h.conj A' hA' ⟨x, hx⟩ trivial,
      map_conjSub H.subtype ⟨x, hx⟩ A'⟩

private theorem isInvColl_comap_subtype {H : Subgroup G} {Ω : Set (Subgroup G)}
    (h : IsInvColl H Ω) :
    IsInvColl (⊤ : Subgroup ↥H) {A' : Subgroup ↥H | A'.map H.subtype ∈ Ω} := by
  refine ⟨fun _ _ => le_top, fun A' hA' => ?_, fun A' hA' x _ => ?_⟩
  · exact isElemAbelian_of_map_injective H.subtype_injective (h.isElemAbelian _ hA')
  · show (conjSub x A').map H.subtype ∈ Ω
    rw [map_conjSub]
    exact h.conj _ hA' _ x.2

private theorem image_comap_subtype {H : Subgroup G} {Ω : Set (Subgroup G)} (h : IsInvColl H Ω) :
    Subgroup.map H.subtype '' {A' : Subgroup ↥H | A'.map H.subtype ∈ Ω} = Ω := by
  ext A
  refine ⟨by rintro ⟨A', hA', rfl⟩; exact hA', fun hA => ⟨A.subgroupOf H, ?_,
    Subgroup.map_subgroupOf_eq_of_le (h.le A hA)⟩⟩
  show (A.subgroupOf H).map H.subtype ∈ Ω
  rwa [Subgroup.map_subgroupOf_eq_of_le (h.le A hA)]

private theorem map_eGen_sup_normalizer [Finite G] (i : ℕ) (H : Subgroup G) (T' : Subgroup ↥H)
    (Ω' : Set (Subgroup ↥H)) :
    (eGen i ⊤ T' Ω' ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T' Ω' : Set ↥H))).map H.subtype =
      eGen i H (T'.map H.subtype) (Subgroup.map H.subtype '' Ω') ⊔
        (H ⊓ Subgroup.normalizer
          (weakClosure (T'.map H.subtype) (Subgroup.map H.subtype '' Ω') : Set G)) := by
  rw [Subgroup.map_sup, map_subtype_top_inf_normalizer, ← eGen_map_subtype,
    ← weakClosure_map_image_of_injective H.subtype_injective]

theorem inEFor_map_subtype_iff [Finite G] (i : ℕ) (H : Subgroup G) (T' : Subgroup ↥H) :
    InEFor i H (T'.map H.subtype) ↔ InEFor i (⊤ : Subgroup ↥H) T' := by
  constructor
  · intro h Ω' hΩ'
    exact Subgroup.map_injective H.subtype_injective
      ((map_eGen_sup_normalizer i H T' Ω').trans
        ((h _ (isInvColl_map_subtype hΩ')).trans (map_subtype_top H).symm))
  · intro h Ω hΩ
    have key := congrArg (Subgroup.map H.subtype) (h _ (isInvColl_comap_subtype hΩ))
    rw [map_eGen_sup_normalizer, map_subtype_top, image_comap_subtype hΩ] at key
    exact key

theorem inE_subgroupOf [Finite G] (i : ℕ) (H : Subgroup G) :
    InE i H ↔ InE i (⊤ : Subgroup ↥H) := by
  constructor
  · intro h T' hT'
    have hT : IsSylowIn 2 (T'.map H.subtype) H := by
      have := (isSylowIn_map_of_injective H.subtype_injective).mpr hT'
      rwa [map_subtype_top] at this
    exact (inEFor_map_subtype_iff i H T').mp (h _ hT)
  · intro h T hT
    have hTH : T ≤ H := hT.le
    have hT' : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
      rw [← isSylowIn_map_of_injective H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTH,
        map_subtype_top]
      exact hT
    have := (inEFor_map_subtype_iff i H (T.subgroupOf H)).mpr (h _ hT')
    rwa [Subgroup.map_subgroupOf_eq_of_le hTH] at this

theorem nParam_subgroupOf [Finite G] (H : Subgroup G) :
    nParam H = nParam (⊤ : Subgroup ↥H) := by
  have hcard : Nat.card ↥(⊤ : Subgroup ↥H) = Nat.card ↥H := Subgroup.card_top
  have hE : {i : ℕ | 0 < i ∧ InE i H} = {i : ℕ | 0 < i ∧ InE i (⊤ : Subgroup ↥H)} :=
    Set.ext fun i => and_congr Iff.rfl (inE_subgroupOf i H)
  unfold nParam
  rw [hcard, hE]

end Restriction

end E1

end CFSG.Quasithin
