module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcRootAs
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot

public section

namespace CFSG.StandardType.ExcRootAs

open CFSG.Assembly CFSG.StandardType TableBSymp

@[expose] def GGEndNodeRootEltBigAs (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A As : Subgroup R, IsElemAbelian p A → A < As → IsElemAbelian p As →
    Nat.card As ≤ p * Nat.card A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∃ t, TableBOrth.IsEndNode A t ∧
      (p = 3 → GGBigLayer (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))) ∧
      ∃ U : Subgroup R, U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)

theorem ggEndNodeRootEltBigAs_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (φ : R ≃* R') (h : GGEndNodeRootEltBigAs p r R) : GGEndNodeRootEltBigAs p r R' := by
  intro A As hA hAAs hAs hcardAs hr h3 ⟨U, hU1, hU2, hAU⟩
  set A₀ := A.map φ.symm.toMonoidHom with hA₀
  set As₀ := As.map φ.symm.toMonoidHom with hAs₀
  have hcard : Nat.card A₀ = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  have hcards : Nat.card As₀ = Nat.card As :=
    (Nat.card_congr (As.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  have hA₀s : A₀ < As₀ := lt_of_le_of_ne (Subgroup.map_mono hAAs.le) fun heq =>
    hAAs.ne (Subgroup.map_injective φ.symm.injective heq)
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
  obtain ⟨t, hend, hbig, V, hVL, hV1, hV2, hAV⟩ := h A₀ As₀ (TableB.isElemAbelian_map hA _)
    hA₀s (TableB.isElemAbelian_map hAs _) (by rw [hcard, hcards]; exact hcardAs)
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

section Induced

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_mulAut_induced (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) (a : MulAut L') : ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := by
  have hcen : ∀ z ∈ Subgroup.center L', ψ z = 1 := by
    intro z hz
    have h : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) l]
    rw [hZ, Subgroup.mem_bot] at h
    exact h
  have hcenA : ∀ (b : MulAut L'), ∀ z ∈ Subgroup.center L', b z ∈ Subgroup.center L' := by
    intro b z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have h := (Subgroup.mem_center_iff.mp hz) (b.symm g)
    calc g * b z = b (b.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = b (z * b.symm g) := by rw [h]
      _ = b z * g := by rw [map_mul, MulEquiv.apply_symm_apply]
  have hk : ∀ (b : MulAut L'), ψ.ker ≤ (ψ.comp b.toMonoidHom).ker := fun b x hx =>
    hcen _ (hcenA b x (hker hx))
  let α₀ : R →* R := ψ.liftOfSurjective hψ ⟨ψ.comp a.toMonoidHom, hk a⟩
  let α₁ : R →* R := ψ.liftOfSurjective hψ ⟨ψ.comp a.symm.toMonoidHom, hk a.symm⟩
  have h₀ : ∀ x, α₀ (ψ x) = ψ (a x) := fun x =>
    ψ.liftOfRightInverse_comp_apply _ _ ⟨ψ.comp a.toMonoidHom, hk a⟩ x
  have h₁ : ∀ x, α₁ (ψ x) = ψ (a.symm x) := fun x =>
    ψ.liftOfRightInverse_comp_apply _ _ ⟨ψ.comp a.symm.toMonoidHom, hk a.symm⟩ x
  refine ⟨MonoidHom.toMulEquiv α₀ α₁ ?_ ?_, h₀⟩
  · ext k
    obtain ⟨x, rfl⟩ := hψ k
    simp [h₀, h₁]
  · ext k
    obtain ⟨x, rfl⟩ := hψ k
    simp [h₀, h₁]

end Induced

theorem ggEndNodeRootAs_of_eltBigAs {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hInn : GGOutdiagPrime p R Set.univ) (hZ : Subgroup.center R = ⊥)
    (h : GGEndNodeRootEltBigAs p r R) : GGEndNodeRootAs p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcardAs _ hr h3 hα _
  have hex : ∀ a : As, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφ⟩ := exists_mulAut_induced hψ hker hZ (a : MulAut L')
    have hφp : φ ^ p = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := hψ x
      rw [pow_apply_comp_eq hφ p l, hAs.2 a a.2, MulAut.one_apply, MulAut.one_apply]
    obtain ⟨t, rfl⟩ := hInn φ (Set.mem_univ _) hφp
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
  have hχmul : ∀ a b : As, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : As) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χs : As →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχs : ∀ a : As, ∀ l, ψ ((a : MulAut L') l) = χs a * ψ l * (χs a)⁻¹ := hχf
  have hinners : ∀ (a : As) (t' : L'), ψ t' = χs a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχs, ht'])
  have hχsinj : Function.Injective χs := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinners a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  set χ : A →* R := χs.comp (Subgroup.inclusion hAAs.le) with hχdef
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := fun a =>
    hχs (Subgroup.inclusion hAAs.le a)
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a => hinners (Subgroup.inclusion hAAs.le a)
  have hχinj : Function.Injective χ :=
    hχsinj.comp (Subgroup.inclusion_injective hAAs.le)
  set Ab := χ.range with hAb
  set Abs := χs.range with hAbs
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hAbsA : IsElemAbelian p Abs := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hAs a.2 b.2))
    (fun a => Subtype.ext (by simpa using hAs.2 a a.2)) χs
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hcardAbs : Nat.card Abs = Nat.card As :=
    (Nat.card_congr (MonoidHom.ofInjective hχsinj).toEquiv).symm
  have hAbAbs : Ab < Abs := by
    have hle : Ab ≤ Abs := by
      rintro _ ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hAAs.le a, rfl⟩
    refine lt_of_le_of_ne hle fun heq => hAAs.not_ge fun s hs => ?_
    obtain ⟨a, ha⟩ : χs ⟨s, hs⟩ ∈ Ab := heq ▸ ⟨⟨s, hs⟩, rfl⟩
    have e : ((Subgroup.inclusion hAAs.le a : As) : MulAut L') = s :=
      congrArg Subtype.val (hχsinj ha)
    rw [← e]
    exact a.2
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ Ab ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have := hAU a a.2 l hu
    rwa [hχ] at this
  obtain ⟨_, ⟨⟨a₀, rfl⟩, ht1, hcomp, hcent⟩, hbig, V, hVK, hV1, hV2, hAbV⟩ :=
    h Ab Abs hAbA hAbAbs hAbsA (by rw [hcardAb, hcardAbs]; exact hcardAs) (hcardAb ▸ hr)
      (hcardAb ▸ h3) hUAb
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

end CFSG.StandardType.ExcRootAs
