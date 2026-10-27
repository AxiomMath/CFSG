module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeRootElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∃ t, TableBOrth.IsEndNode A t ∧
      ∃ U : Subgroup R, U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)

section Lift

variable {L' R : Type} [Group L'] [Group R] [Finite L']

theorem exists_twoSubgroup_lift {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {X : Subgroup L'} {V : Subgroup R} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVX : V ≤ X.map ψ)
    {S : Set (MulAut L')} (hSX : ∀ a ∈ S, ∀ x ∈ X, a x ∈ X)
    (hSV : ∀ a ∈ S, ∀ l, ψ l ∈ V → ψ (a l) ∈ V) :
    ∃ P : Subgroup L', P ≤ X ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ a ∈ S, ∀ u ∈ P, a u ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup L' := X ⊓ V.comap ψ with hH
  let f : H →* V := (ψ.comp H.subtype).codRestrict V (fun h => h.2.2)
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨x, hx, rfl⟩ := hVX hv
    exact ⟨⟨x, hx, hv⟩, rfl⟩
  have hkerf : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 : (h : L') ∈ Subgroup.center L' := hker h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Finite V := Finite.of_surjective f hf
  have : Group.IsNilpotent V := hV2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hkerf
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have htop : (⊤ : Subgroup V) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hV2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨Q, hQ⟩ := (isPGroup_two_zpowers hk).exists_le_sylow
    have := Sylow.unique_of_normal P hPn
    have hQP : Q = P := Subsingleton.elim Q P
    rw [← hQP]
    exact hQ (Subgroup.mem_zpowers h)
  refine ⟨(P : Subgroup H).map H.subtype, (Subgroup.map_subtype_le _).trans inf_le_left, ?_,
    P.isPGroup'.map _, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ (⊥ : Subgroup V) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · rintro a ha _ ⟨q, hq, rfl⟩
    have haH : a q ∈ H := ⟨hSX a ha q q.2.1, hSV a ha q q.2.2⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨q, hq⟩
    have hqk : (q : L') ^ 2 ^ k = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => ((z : H) : L')) hk
      simpa using this
    refine ⟨⟨a q, haH⟩, hmemP _ k (Subtype.ext ?_), rfl⟩
    show (a q) ^ 2 ^ k = 1
    rw [← map_pow, hqk, map_one]

end Lift

theorem pow_apply_comp_eq {L' R : Type} [Group L'] [Group R] {ψ : L' →* R} {φ : MulAut R}
    {a : MulAut L'} (h : ∀ l, φ (ψ l) = ψ (a l)) (k : ℕ) (l : L') :
    (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, h]

open TableBSymp in
theorem ggEndNodeRoot_of_elt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥) (hp3 : p ≠ 3)
    (h : GGEndNodeRootElt p r R) : GGEndNodeRoot p r R I := by
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
  obtain ⟨_, ⟨⟨a₀, rfl⟩, ht1, hcomp, hcent⟩, V, hVK, hV1, hV2, hAbV⟩ :=
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
  rw [← ht'] at hcomp hcent hVK
  obtain ⟨hlayer, hcompL⟩ := layer_centralizer_lift hψ hker hcomp
  set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hmapK : (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L').map ψ = Kb := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hψ, hKbperf]
  refine ⟨a₀, ⟨a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => ?_⟩, fun h3' => absurd h3' hp3, ?_⟩
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
  ·
    have hVX : V ≤ (⁅Kb.comap ψ, Kb.comap ψ⁆ : Subgroup L').map ψ := by
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

end CFSG.StandardType
