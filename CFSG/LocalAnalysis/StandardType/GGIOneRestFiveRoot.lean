module

public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndLift
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

@[expose] def GGBigLayer {R : Type*} [Group R] (K : Subgroup R) : Prop :=
  7 ∣ Nat.card K ∨ 25920 < Nat.card K

theorem not_largeEvenSmall_of_map_big {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (h : GGBigLayer (K.map f)) : ¬ LargeEvenSmall K := by
  rcases h with h7 | hbig
  · exact IOneOrthEnd.not_largeEvenSmall_of_map f K h7
  · rintro (hU | hA)
    · have h1 := IOneOrthEnd.card_of_isU42 hU
      have h2 : Nat.card (K.map f) ≤ Nat.card K :=
        Nat.le_of_dvd (by omega) (Subgroup.card_map_dvd K f)
      omega
    · obtain ⟨e⟩ := hA
      have h1 : Nat.card K = 360 := by
        rw [Nat.card_congr e.toEquiv, IOneOrthEnd.card_alternatingGroup_six]
      have h2 : Nat.card (K.map f) ≤ Nat.card K :=
        Nat.le_of_dvd (by omega) (Subgroup.card_map_dvd K f)
      omega

@[expose] def GGEndNodeRootEltBig (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∃ t, TableBOrth.IsEndNode A t ∧
      (p = 3 → GGBigLayer (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))) ∧
      ∃ U : Subgroup R, U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)

theorem ggEndNodeRootEltBig_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (φ : R ≃* R') (h : GGEndNodeRootEltBig p r R) : GGEndNodeRootEltBig p r R' := by
  intro A hA hr h3 ⟨U, hU1, hU2, hAU⟩
  set A₀ := A.map φ.symm.toMonoidHom with hA₀
  have hcard : Nat.card A₀ = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  have hU₀1 : U.map φ.symm.toMonoidHom ≠ ⊥ := by
    intro h0
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : φ.symm u ∈ U.map φ.symm.toMonoidHom := ⟨u, hu, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← φ.apply_symm_apply u, this, map_one]
  have hU₀N : A₀ ≤ Subgroup.normalizer ((U.map φ.symm.toMonoidHom : Subgroup R) : Set R) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨a * u * a⁻¹, Subgroup.le_normalizer_iff.mp hAU a ha u hu, ?_⟩
    simp
  obtain ⟨t, hend, hbig, V, hVL, hV1, hV2, hAV⟩ := h A₀ (TableB.isElemAbelian_map hA _)
    (hcard ▸ hr) (hcard ▸ h3) ⟨U.map φ.symm.toMonoidHom, hU₀1, hU2.map _, hU₀N⟩
  have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R' :=
    MonoidHom.ext fun x => φ.apply_symm_apply x
  have hA' : A₀.map φ.toMonoidHom = A := by
    rw [hA₀, Subgroup.map_map, hid, Subgroup.map_id]
  have hend' := hend.map φ
  rw [hA'] at hend'
  have hC : Subgroup.centralizer ({φ t} : Set R') =
      (Subgroup.centralizer ({t} : Set R)).map φ.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton φ t).symm
  have hlay : LargeEvenLayer (Subgroup.centralizer ({φ t} : Set R')) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set R))).map φ.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ φ.injective]
  refine ⟨φ t, hend', fun hp3 => ?_, V.map φ.toMonoidHom, ?_, ?_, hV2.map _, ?_⟩
  · rw [hlay]
    rcases hbig hp3 with h7 | h2
    · refine Or.inl ?_
      rw [Subgroup.card_map_of_injective φ.injective]
      exact h7
    · refine Or.inr ?_
      rw [Subgroup.card_map_of_injective φ.injective]
      exact h2
  · rw [hlay]
    exact Subgroup.map_mono hVL
  · intro hbot
    apply hV1
    rw [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at hbot
    exact hbot
  · have h1 := (Subgroup.map_mono hAV).trans (Subgroup.le_normalizer_map φ.toMonoidHom)
    rwa [hA'] at h1

theorem ggEndNodeRoot_of_eltBig {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥)
    (h : GGEndNodeRootEltBig p r R) : GGEndNodeRoot p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    have hφp : φ ^ p = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := hψ x
      rw [pow_apply_comp_eq hφ p l, hA.2 a a.2, MulAut.one_apply, MulAut.one_apply]
    obtain ⟨t, rfl⟩ := hI φ hφI hφp
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ Ab ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have := hAU a a.2 l hu
    rwa [hχ] at this
  obtain ⟨_, ⟨⟨a₀, rfl⟩, ht1, hcomp, hcent⟩, hbig, V, hVK, hV1, hV2, hAbV⟩ :=
    h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) hUAb
  obtain ⟨t', ht'⟩ := hψ (χ a₀)
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix (a₀ : MulAut L') = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, ha₀, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  rw [← ht'] at hcomp hcent hVK hbig
  obtain ⟨hlayer, hcompL⟩ := layer_centralizer_lift hψ hker hcomp
  set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hmapK : (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L').map ψ = Kb := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hψ, hKbperf]
  refine ⟨a₀, ⟨a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => ?_⟩, fun h3' _ => ?_, ?_⟩
  · have : a₀ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [hfix]
    exact hcompL
  · obtain ⟨s', hs'⟩ := hψ (χ ⟨a', ha'⟩)
    have hinn' := hinner ⟨a', ha'⟩ s' hs'
    have hcent' := hcent (χ ⟨a', ha'⟩) ⟨⟨a', ha'⟩, rfl⟩
    rw [hfix, hlayer]
    constructor
    · intro hj
      have h1 : ∀ j ∈ Kb, χ ⟨a', ha'⟩ * j = j * χ ⟨a', ha'⟩ := by
        intro j hj'
        rw [← hmapK] at hj'
        obtain ⟨k, hk, rfl⟩ := hj'
        have e := hj k hk
        rw [hinn'] at e
        rw [← hs', ← map_mul, ← map_mul]
        congr 1
        calc s' * k = s' * k * s'⁻¹ * s' := by group
          _ = k * s' := by rw [e]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcent'.mp h1)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := hχinj (by rw [map_zpow, ← ht', hn])
      exact congrArg Subtype.val h2
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 : a₀ ^ n = ⟨a', ha'⟩ := Subtype.ext hn
      have h3 : χ ⟨a', ha'⟩ ∈ Subgroup.zpowers (ψ t') :=
        Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [ht', ← map_zpow, h2]⟩
      have h4 := hcent'.mpr h3
      intro j hj
      rw [hinn']
      have hcomm := commute_of_mem_commutator (x := s')
        (Y := Kb.comap ψ) (fun y hy => hker (by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs', h4 (ψ y) hy]
          group)) hj
      rw [hcomm]
      group
  · rw [hfix, hlayer]
    exact not_largeEvenSmall_of_map_big ψ _ (by rw [hmapK]; exact hbig h3')
  · have hVX : V ≤ (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L').map ψ := by
      rw [hmapK]
      exact hVK
    have hAY : ∀ a ∈ (A : Set (MulAut L')), ∀ y ∈ Kb.comap ψ, a y ∈ Kb.comap ψ := by
      intro a ha y hy
      show ψ (a y) ∈ Kb
      rw [hχ ⟨a, ha⟩]
      refine largeEvenLayer_conj_mem ?_ hy
      rw [Subgroup.mem_centralizer_singleton_iff, ht']
      exact (TableB.IsElemAbelian.comm hAbA ⟨⟨a, ha⟩, rfl⟩ ⟨a₀, rfl⟩)
    have hAX : ∀ a ∈ (A : Set (MulAut L')), ∀ x ∈ (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L'),
        a x ∈ (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L') := by
      intro a ha x hx
      have hle : (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L').map (a : L' →* L') ≤
          ⁅Kb.comap ψ, Kb.comap ψ⁆ := by
        rw [Subgroup.map_commutator]
        have hYa : (Kb.comap ψ).map (a : L' →* L') ≤ Kb.comap ψ := by
          rintro _ ⟨y, hy, rfl⟩
          exact hAY a ha y hy
        exact Subgroup.commutator_mono hYa hYa
      exact hle ⟨x, hx, rfl⟩
    have hAV : ∀ a ∈ (A : Set (MulAut L')), ∀ l, ψ l ∈ V → ψ (a l) ∈ V := by
      intro a ha l hl
      rw [hχ ⟨a, ha⟩]
      exact (Subgroup.mem_normalizer_iff.mp (hAbV ⟨⟨a, ha⟩, rfl⟩) _).mp hl
    obtain ⟨P, hPX, hP1, hP2, hAP⟩ := exists_twoSubgroup_lift hker hV1 hV2 hVX hAX hAV
    refine ⟨P, ?_, hP1, hP2, fun a' ha' u hu => hAP a' ha' u hu⟩
    rw [hfix, hlayer]
    exact hPX

theorem ggEndNodeIOne_of_rootEltBig {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥) (hC : GGCenterPrime p R)
    (h : GGEndNodeRootEltBig p r R) : GGEndNodeIOne p r R I :=
  ggEndNodeIOne_of_root_delta (ggEndNodeRoot_of_eltBig hI hZ h)
    (ggEndNodeIOneDelta_of_prime hI hC)

end CFSG.StandardType
