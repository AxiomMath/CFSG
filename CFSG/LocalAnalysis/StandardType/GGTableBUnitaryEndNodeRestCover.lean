module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNode
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace TableBUR

open CFSG.Assembly TableBSymp

section Induced

variable {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (hψ : Function.Surjective ψ)
  (hkc : ψ.ker = Subgroup.center L')

@[expose] noncomputable def indFun (α : MulAut L') : MulAut R :=
  ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.congr ψ.ker ψ.ker α (by rw [hkc]; exact Subgroup.map_center_eq α))).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem indFun_apply (α : MulAut L') (l : L') : indFun ψ hψ hkc α (ψ l) = ψ (α l) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ l) =
      (l : L' ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [indFun, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

@[expose] noncomputable def indAut : MulAut L' →* MulAut R where
  toFun := indFun ψ hψ hkc
  map_one' := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [indFun_apply]
    rfl
  map_mul' α β := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [MulAut.mul_apply, indFun_apply, indFun_apply, indFun_apply, MulAut.mul_apply]

theorem indAut_apply (α : MulAut L') (l : L') : indAut ψ hψ hkc α (ψ l) = ψ (α l) :=
  indFun_apply ψ hψ hkc α l

theorem indAut_injective (hperf : commutator L' = ⊤) : Function.Injective (indAut ψ hψ hkc) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hP : Group.IsPerfect L' := ⟨hperf⟩
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hkc.le hP α.toMonoidHom
    (MonoidHom.id L') (fun u => by
      change ψ (α u) = ψ u
      rw [← indAut_apply ψ hψ hkc α u, hα]
      rfl)
  ext l
  exact key l

theorem indAut_eq_conj (α : MulAut L') (r : R) (h : ∀ l, ψ (α l) = r * ψ l * r⁻¹) :
    indAut ψ hψ hkc α = MulAut.conj r := by
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [indAut_apply, h l]
  rfl

end Induced

@[expose] def GGEndNodeEltAdm (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup (MulAut R), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A.map (MulAut.conj : R →* MulAut R) ≤ Subgroup.normalizer (U : Set (MulAut R))) →
    ∃ t ∈ A, t ≠ 1 ∧
      IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))
        (Subgroup.centralizer ({t} : Set R)) ∧
      ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)), s * j = j * s) ↔
        s ∈ Subgroup.zpowers t)

theorem ker_eq_center_of_surjective {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) : ψ.ker = Subgroup.center L' := by
  refine le_antisymm hker fun z hz => ?_
  have h1 : ψ z ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := hψ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
  rw [hZ, Subgroup.mem_bot] at h1
  exact h1

theorem ggEndNodeAdm_of_eltAdm {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hmult : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ¬ p ∣ Nat.card ψ.ker)
    (h : GGEndNodeEltAdm p r R) : GGEndNodeAdm p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hadm
  have hkc := ker_eq_center_of_surjective hψ hker hZ
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨t, rfl⟩ := hI hφI
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
  have hadmR : ∃ U : Subgroup (MulAut R), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      Ab.map (MulAut.conj : R →* MulAut R) ≤ Subgroup.normalizer (U : Set (MulAut R)) := by
    rcases hadm with ⟨U, hU1, hU2, hAU⟩ | ⟨⟨a, haA, hna⟩, -⟩ | ⟨hpZ, -⟩
    · refine ⟨U.map (indAut ψ hψ hkc), fun hbot => hU1 ?_, hU2.map _, ?_⟩
      · exact (Subgroup.map_eq_bot_iff_of_injective U (indAut_injective ψ hψ hkc hperf)).mp hbot
      · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        have e : MulAut.conj (χ a) = indAut ψ hψ hkc (a : MulAut L') :=
          (indAut_eq_conj ψ hψ hkc (a : MulAut L') (χ a) (hχ a)).symm
        rw [e]
        exact Subgroup.le_normalizer_map (indAut ψ hψ hkc) ⟨(a : MulAut L'), hAU a.2, rfl⟩
    · exfalso
      obtain ⟨t', ht'⟩ := hψ (χ ⟨a, haA⟩)
      refine hna ⟨t', ?_⟩
      ext l
      rw [hinner ⟨a, haA⟩ t' ht' l]
      rfl
    · exfalso
      rw [← hkc] at hpZ
      exact hmult L' ψ hψ hker hperf hpZ
  obtain ⟨_, ⟨a₀, rfl⟩, ht1, hcomp, hcent⟩ := h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) hadmR
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
  rw [← ht'] at hcomp hcent
  obtain ⟨hlayer, hcompL⟩ := layer_centralizer_lift hψ hker hcomp
  refine ⟨a₀, a₀.2, fun h1 => ht1 ?_, ?_, fun a' ha' => ?_⟩
  · have : a₀ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [hfix]
    exact hcompL
  · obtain ⟨s', hs'⟩ := hψ (χ ⟨a', ha'⟩)
    have hinn' := hinner ⟨a', ha'⟩ s' hs'
    set Kb := LargeEvenLayer (Subgroup.centralizer ({ψ t'} : Set R)) with hKb
    have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp hcomp.2.2
    have hKbperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
    have hmapK := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hKbperf
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

end TableBUR

end CFSG.StandardType
