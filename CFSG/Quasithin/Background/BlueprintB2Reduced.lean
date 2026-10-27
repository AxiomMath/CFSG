module

public import CFSG.Quasithin.Background.BlueprintB2Basic
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.Quasithin

open CFSG CFSG.Quasithin.BlueprintB2
open scoped Pointwise

variable {E : Type*} [Group E]

namespace BlueprintB2

theorem pCore_quotient_centralizer_eq_bot_iff {V : Subgroup E} [V.Normal] (p : ℕ) :
    CFSG.pCore p (E ⧸ Subgroup.centralizer (V : Set E)) = ⊥ ↔
      ∀ D : Subgroup E, D.Normal →
        (∀ d ∈ D, ∃ k : ℕ, d ^ p ^ k ∈ Subgroup.centralizer (V : Set E)) →
          D ≤ Subgroup.centralizer (V : Set E) := by
  set C := Subgroup.centralizer (V : Set E) with hC
  constructor
  · intro h D hD hDp
    have hmap : D.map (QuotientGroup.mk' C) ≤ CFSG.pCore p (E ⧸ C) := by
      refine le_sSup ⟨hD.map _ (QuotientGroup.mk'_surjective C), ?_⟩
      intro y
      obtain ⟨d, hd, hdy⟩ := y.2
      obtain ⟨k, hk⟩ := hDp d hd
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (QuotientGroup.mk' C) (d ^ p ^ k) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
      rw [map_pow, hdy] at h1
      simpa using h1
    intro d hd
    have h2 : QuotientGroup.mk' C d ∈ D.map (QuotientGroup.mk' C) := ⟨d, hd, rfl⟩
    have h3 := hmap h2
    rw [h, Subgroup.mem_bot] at h3
    exact (QuotientGroup.eq_one_iff _).mp h3
  · intro h
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    have hDn : (Subgroup.comap (QuotientGroup.mk' C) (CFSG.pCore p (E ⧸ C))).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hdle : Subgroup.comap (QuotientGroup.mk' C) (CFSG.pCore p (E ⧸ C)) ≤ C :=
      h _ hDn fun e he => by
        obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := E ⧸ C)
          ⟨QuotientGroup.mk' C e, he⟩
        refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
        have := congrArg Subtype.val hk
        simpa using this
    have hdC : d ∈ C := hdle hx
    exact (QuotientGroup.eq_one_iff _).mpr hdC

end BlueprintB2

theorem isPrimeReduced_iff_forall {V : Subgroup E} (p : ℕ) :
    IsPrimeReduced p V ↔
      ∃ _ : V.Normal, CFSG.IsElementaryAbelian p V ∧
        ∀ D : Subgroup E, D.Normal →
          (∀ d ∈ D, ∃ k : ℕ, d ^ p ^ k ∈ Subgroup.centralizer (V : Set E)) →
            D ≤ Subgroup.centralizer (V : Set E) := by
  unfold IsPrimeReduced
  refine exists_congr fun hN => and_congr_right fun _ => ?_
  exact BlueprintB2.pCore_quotient_centralizer_eq_bot_iff p

theorem IsPrimeReduced.normal {p : ℕ} {V : Subgroup E} (h : IsPrimeReduced p V) : V.Normal :=
  h.fst

theorem IsPrimeReduced.isElementaryAbelian {p : ℕ} {V : Subgroup E} (h : IsPrimeReduced p V) :
    CFSG.IsElementaryAbelian p V :=
  h.snd.1

theorem pCore_le_centralizer_of_isPrimeReduced {p : ℕ} {V : Subgroup E}
    (hV : IsPrimeReduced p V) : CFSG.pCore p E ≤ Subgroup.centralizer (V : Set E) := by
  obtain ⟨_, _, hD⟩ := (isPrimeReduced_iff_forall p).mp hV
  refine hD _ inferInstance fun d hd => ?_
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := E) ⟨d, hd⟩
  exact ⟨k, by rw [show d ^ p ^ k = 1 from congrArg Subtype.val hk]; exact Subgroup.one_mem _⟩

theorem le_pCore_of_isPrimeReduced {p : ℕ} {V : Subgroup E} (hV : IsPrimeReduced p V) :
    V ≤ CFSG.pCore p E := by
  have := hV.normal
  have := hV.isElementaryAbelian
  exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup p V⟩

theorem isPrimeReduced_le_centerTorsion_pCore {p : ℕ} {V : Subgroup E}
    (hV : IsPrimeReduced p V) : V ≤ centerTorsion p (CFSG.pCore p E) := by
  intro v hv
  rw [mem_centerTorsion_iff]
  refine ⟨le_pCore_of_isPrimeReduced hV hv, fun k hk => ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (pCore_le_centralizer_of_isPrimeReduced hV hk) v hv).symm
  · exact (isElementaryAbelian_iff.mp hV.isElementaryAbelian).2 v hv

theorem isPrimeReduced_bot (p : ℕ) : IsPrimeReduced p (⊥ : Subgroup E) := by
  refine (isPrimeReduced_iff_forall p).mpr ⟨Subgroup.normal_bot, isElementaryAbelian_bot p, ?_⟩
  intro D _ _ d _
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Subgroup.mem_bot.mp hh]
  simp

theorem isPrimeReduced_sup {p : ℕ} {U V : Subgroup E} (hU : IsPrimeReduced p U)
    (hV : IsPrimeReduced p V) : IsPrimeReduced p (U ⊔ V) := by
  have := hU.normal
  have := hV.normal
  have := hU.isElementaryAbelian
  have := hV.isElementaryAbelian
  have hVU : V ≤ Subgroup.centralizer (U : Set E) :=
    (le_pCore_of_isPrimeReduced hV).trans (pCore_le_centralizer_of_isPrimeReduced hU)
  refine (isPrimeReduced_iff_forall p).mpr
    ⟨inferInstance, IsElementaryAbelian.sup_of_le_centralizer hVU, ?_⟩
  intro D hD hDp
  obtain ⟨_, _, hUD⟩ := (isPrimeReduced_iff_forall p).mp hU
  obtain ⟨_, _, hVD⟩ := (isPrimeReduced_iff_forall p).mp hV
  have hDU : D ≤ Subgroup.centralizer (U : Set E) :=
    hUD D hD fun d hd => by
      obtain ⟨k, hk⟩ := hDp d hd
      exact ⟨k, Subgroup.centralizer_le (fun x hx => (le_sup_left : U ≤ U ⊔ V) hx) hk⟩
  have hDV : D ≤ Subgroup.centralizer (V : Set E) :=
    hVD D hD fun d hd => by
      obtain ⟨k, hk⟩ := hDp d hd
      exact ⟨k, Subgroup.centralizer_le (fun x hx => (le_sup_right : V ≤ U ⊔ V) hx) hk⟩
  exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp hDU)
    (Subgroup.le_centralizer_iff.mp hDV))

theorem isPrimeReduced_map {p : ℕ} {E' : Type*} [Group E'] (φ : E ≃* E') {V : Subgroup E}
    (hV : IsPrimeReduced p V) : IsPrimeReduced p (V.map φ.toMonoidHom) := by
  have := hV.normal
  obtain ⟨_, hVe, hVD⟩ := (isPrimeReduced_iff_forall p).mp hV
  have hcent : ∀ x : E', x ∈ Subgroup.centralizer ((V.map φ.toMonoidHom : Subgroup E') : Set E') ↔
      φ.symm x ∈ Subgroup.centralizer (V : Set E) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx v hv
      have := hx (φ v) ⟨v, hv, rfl⟩
      apply φ.injective
      simpa using this
    · rintro hx _ ⟨v, hv, rfl⟩
      have := hx v hv
      apply φ.symm.injective
      simpa using this
  refine (isPrimeReduced_iff_forall p).mpr
    ⟨Subgroup.Normal.map inferInstance _ φ.surjective, isElementaryAbelian_map hVe _, ?_⟩
  intro D hD hDp
  have := hD
  have hD0 : (D.map φ.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hD _ φ.symm.surjective
  have hle : D.map φ.symm.toMonoidHom ≤ Subgroup.centralizer (V : Set E) := by
    refine hVD _ hD0 ?_
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hDp d hd
    exact ⟨k, by simpa using (hcent _).mp hk⟩
  intro d hd
  exact (hcent d).mpr (hle ⟨d, hd, rfl⟩)

theorem le_primeReducedAggregate {p : ℕ} {V : Subgroup E} (hV : IsPrimeReduced p V) :
    V ≤ primeReducedAggregate E p :=
  le_sSup hV

theorem isPrimeReduced_primeReducedAggregate [Finite E] (p : ℕ) :
    IsPrimeReduced p (primeReducedAggregate E p) := by
  obtain ⟨V₀, -, hV₀⟩ := Finite.exists_le_maximal (p := IsPrimeReduced p) (a := (⊥ : Subgroup E))
    (isPrimeReduced_bot p)
  have : primeReducedAggregate E p = V₀ := by
    refine le_antisymm (sSup_le fun V hV => ?_) (le_primeReducedAggregate hV₀.1)
    exact le_sup_left.trans (hV₀.2 (isPrimeReduced_sup hV hV₀.1) le_sup_right)
  rw [this]
  exact hV₀.1

theorem primeReducedAggregate_characteristic [Finite E] (p : ℕ) :
    (primeReducedAggregate E p).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  exact le_primeReducedAggregate (isPrimeReduced_map φ (isPrimeReduced_primeReducedAggregate p))

theorem maximal_primeReducedAggregate [Finite E] (p : ℕ) :
    Maximal (fun V : Subgroup E => IsPrimeReduced p V) (primeReducedAggregate E p) :=
  ⟨isPrimeReduced_primeReducedAggregate p, fun _ hy _ => le_primeReducedAggregate hy⟩

theorem eq_primeReducedAggregate_of_maximal [Finite E] {p : ℕ} {V : Subgroup E}
    (hV : Maximal (fun V : Subgroup E => IsPrimeReduced p V) V) : V = primeReducedAggregate E p :=
  le_antisymm (le_primeReducedAggregate hV.1)
    (hV.2 (isPrimeReduced_primeReducedAggregate p) (le_primeReducedAggregate hV.1))

theorem primeReducedAggregate_normal_elementaryAbelian [Finite E] (p : ℕ) :
    (primeReducedAggregate E p).Normal ∧
      CFSG.IsElementaryAbelian p (primeReducedAggregate E p) ∧
        primeReducedAggregate E p ≤ centerTorsion p (CFSG.pCore p E) := by
  have h := isPrimeReduced_primeReducedAggregate (E := E) p
  exact ⟨h.normal, h.isElementaryAbelian, isPrimeReduced_le_centerTorsion_pCore h⟩

theorem qt_prime_reduced_aggregate_characteristic_maximal (E : Type*) [Group E] [Finite E]
    (p : ℕ) [Fact p.Prime] :
    (∀ V ∈ primeReducedFamily E p, V ≤ centerTorsion p (CFSG.pCore p E)) ∧
      (∀ U ∈ primeReducedFamily E p, ∀ V ∈ primeReducedFamily E p,
        ((U : Set E) * (V : Set E) = ((U ⊔ V : Subgroup E) : Set E)) ∧
          (U ⊔ V) ∈ primeReducedFamily E p) ∧
      primeReducedAggregate E p ∈ primeReducedFamily E p ∧
      (primeReducedAggregate E p).Characteristic ∧
      (∀ V ∈ primeReducedFamily E p, V ≤ primeReducedAggregate E p) ∧
      Maximal (fun V : Subgroup E => V ∈ primeReducedFamily E p) (primeReducedAggregate E p) ∧
      (∀ V : Subgroup E, Maximal (fun V : Subgroup E => V ∈ primeReducedFamily E p) V →
        V = primeReducedAggregate E p) ∧
      ((primeReducedAggregate E p).Normal ∧
        CFSG.IsElementaryAbelian p (primeReducedAggregate E p) ∧
          primeReducedAggregate E p ≤ centerTorsion p (CFSG.pCore p E)) := by
  refine ⟨fun V hV => isPrimeReduced_le_centerTorsion_pCore hV, ?_,
    isPrimeReduced_primeReducedAggregate p, primeReducedAggregate_characteristic p,
    fun V hV => le_primeReducedAggregate hV, maximal_primeReducedAggregate p,
    fun V hV => eq_primeReducedAggregate_of_maximal hV,
    primeReducedAggregate_normal_elementaryAbelian p⟩
  intro U hU V hV
  have := hU.normal
  exact ⟨(Subgroup.normal_mul U V).symm, isPrimeReduced_sup hU hV⟩

end CFSG.Quasithin
