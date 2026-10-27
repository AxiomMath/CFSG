module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace Insp7

theorem le_normalizer_component {G : Type} [Group G] [Finite G] {H S M L : Subgroup G} {z : G}
    (h : Lemma115Hyp H S M z) (hL : IsComponentIn L H) (hzL : z ∈ L) :
    H ≤ Subgroup.normalizer (L : Set G) := by
  set K : Subgroup ↥H := L.subgroupOf H with hK
  have hKc : CFSG.IsComponent K := hL.2
  have hzH : z ∈ H := hL.1 hzL
  have hall : ∀ K' : Subgroup ↥H, CFSG.IsComponent K' → K' = K := by
    intro K' hK'
    rcases CFSG.LocalCores.distinct_components_commute hKc hK' with h1 | h1
    · exact h1.symm
    · exfalso
      set L' : Subgroup G := K'.map H.subtype with hL'
      have hL'H : L' ≤ H := Subgroup.map_subtype_le K'
      have hL'sub : L'.subgroupOf H = K' :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective K'
      have hL'c : IsComponentIn L' H := ⟨hL'H, by rw [hL'sub]; exact hK'⟩
      have hact := (h.component_action hL'c).2.1
      have hcomm : ⁅L', Subgroup.zpowers z⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        have hzK : (⟨z, hzH⟩ : ↥H) ∈ K := Subgroup.mem_subgroupOf.mpr hzL
        have h2 : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.centralizer (K' : Set ↥H) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1) hzK
        have h3 : (x' : G) * z = z * x' := by
          have := Subgroup.mem_centralizer_iff.mp h2 x' hx'
          exact congrArg Subtype.val this
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Commute.zpow_left (show Commute z (x' : G) from h3.symm) k).eq
      rw [hcomm] at hact
      have hbot : K' = ⊥ := by
        rw [← hL'sub, ← hact]
        simp
      have : Nontrivial ↥K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
      exact (Subgroup.nontrivial_iff_ne_bot K').mp this hbot
  have hlayer : CFSG.layer ↥H = K := by
    simp only [CFSG.layer.eq_sSup]
    have : {K' : Subgroup ↥H | CFSG.IsComponent K'} = {K} := by
      ext K'
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨hall K', fun e => e ▸ hKc⟩
    rw [this, sSup_singleton]
  have hKchar : K.Characteristic := hlayer ▸ CFSG.LocalCores.layer_characteristic
  have hKn : K.Normal := by have := hKchar; infer_instance
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro l
  have key : ∀ g ∈ H, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have hlK : (⟨l, hL.1 hl⟩ : ↥H) ∈ K := Subgroup.mem_subgroupOf.mpr hl
    have := hKn.conj_mem _ hlK ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  exact ⟨fun hl => key g hg l hl, fun hl => by simpa [mul_assoc] using key g⁻¹ (H.inv_mem hg) _ hl⟩

theorem centralizer_inf_le_zpowers {G : Type} [Group G] [Finite G] {H S M L : Subgroup G}
    {z d : G} (h : Lemma115Hyp H S M z) (hHd : H ≤ Subgroup.centralizer ({d} : Set G))
    (hd2 : d * d = 1) (hO : pCoreOf 2 H = Subgroup.zpowers d)
    (hLN : H ≤ Subgroup.normalizer (L : Set G)) (hzL : z ∈ L) :
    H ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := H ⊓ Subgroup.centralizer (L : Set G) with hY
  set X : Subgroup G := H ⊓ M with hX
  set R : Subgroup G := pCoreOf 2 X with hR
  have hYX : Y ≤ X := fun y hy => by
    refine ⟨hy.1, h.centralizer_z_le ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw
      exact (Subgroup.mem_centralizer_iff.mp hy.2 w hzL)
  have hRN : X ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 X
  have hYH : Y ≤ H := inf_le_left
  have key : ∀ g ∈ H, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine ⟨H.mul_mem (H.mul_mem hg hy.1) (H.inv_mem hg), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLN (H.inv_mem hg)) l).mp hl
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hy.2 _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = (g * y * g⁻¹) * l := by group
  have hYN : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro h' hh'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨key h' hh' y, fun hy => by simpa [mul_assoc] using key h'⁻¹ (H.inv_mem hh') _ hy⟩
  have hd : ∀ g ∈ H, g * d = d * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (hHd hg) d (Set.mem_singleton d)).symm
  have hYR : Y ⊓ R ≤ Subgroup.zpowers d := by
    have h1 : Y ⊓ R ≤ pCoreOf 2 Y := by
      refine le_pCoreOf 2 inf_le_left ?_ (IsPGroup.to_le (pCoreOf_isPGroup 2 X) inf_le_right)
      refine ⟨fun x hx y => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨?_, ?_⟩
      · exact Y.mul_mem (Y.mul_mem y.2 hx.1) (Y.inv_mem y.2)
      · have hyX : (y : G) ∈ X := hYX y.2
        have := (Subgroup.mem_normalizer_iff.mp (hRN hyX) x).mp hx.2
        simpa using this
    have h2 : pCoreOf 2 Y ≤ pCoreOf 2 H := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
        (hYN.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
    rw [hO] at h2
    exact h1.trans h2
  have hcomm : ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d := by
    intro y hy r hr
    apply hYR
    refine ⟨?_, ?_⟩
    · have hrH : r ∈ H := (pCoreOf_le 2 X hr).1
      have h1 : r * y⁻¹ * r⁻¹ ∈ Y := key r hrH y⁻¹ (Y.inv_mem hy)
      have : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
      rw [this]
      exact Y.mul_mem hy h1
    · have hyX : y ∈ X := hYX hy
      have h1 : y * r * y⁻¹ ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (hRN hyX) r).mp hr
        simpa using this
      exact R.mul_mem h1 (R.inv_mem hr)
  have hd1 : ∀ c ∈ Subgroup.zpowers d, c = 1 ∨ c = d := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hd2' : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd2
    rw [zpow_eq_zpow_emod k hd2']
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; rw [h0]; simp
    · right; rw [h0]; simp
  have hsq : ∀ y ∈ Y, y * y ∈ Subgroup.zpowers d := by
    intro y hy
    apply hYR
    refine ⟨Y.mul_mem hy hy, ?_⟩
    have hyX : y ∈ X := hYX hy
    have hyyX : y * y ∈ X := X.mul_mem hyX hyX
    have hcen : y * y ∈ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
      have hc := hcomm y hy r hr
      have hyH : y ∈ H := hYH hy
      have key2 : y * y * r = r * (y * y) := by
        rcases hd1 _ hc with h1 | h1
        · have : y * r = r * y := by
            have h2 : y * r * y⁻¹ * r⁻¹ = 1 := h1
            calc y * r = (y * r * y⁻¹ * r⁻¹) * (r * y) := by group
              _ = r * y := by rw [h2, one_mul]
          calc y * y * r = y * (y * r) := by group
            _ = y * (r * y) := by rw [this]
            _ = (y * r) * y := by group
            _ = (r * y) * y := by rw [this]
            _ = r * (y * y) := by group
        · have h2 : y * r * y⁻¹ * r⁻¹ = d := h1
          have h3 : y * r = d * (r * y) := by
            calc y * r = (y * r * y⁻¹ * r⁻¹) * (r * y) := by group
              _ = d * (r * y) := by rw [h2]
          have h4 : y * d = d * y := hd y hyH
          calc y * y * r = y * (y * r) := by group
            _ = y * (d * (r * y)) := by rw [h3]
            _ = (y * d) * (r * y) := by group
            _ = (d * y) * (r * y) := by rw [h4]
            _ = d * (y * r) * y := by group
            _ = d * (d * (r * y)) * y := by rw [h3]
            _ = (d * d) * (r * y * y) := by group
            _ = r * (y * y) := by rw [hd2, one_mul]; group
      exact key2.symm
    exact h.charTwo_inf ⟨hyyX, hcen⟩
  have hY4 : ∀ y ∈ Y, y ^ 4 = 1 := by
    intro y hy
    have h1 : y * y ∈ Subgroup.zpowers d := hsq y hy
    have : y ^ 4 = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    rcases hd1 _ h1 with h2 | h2
    · rw [h2, mul_one]
    · rw [h2, hd2]
  have hpY : IsPGroup 2 Y := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h4 : g ^ 4 = 1 := Subtype.ext (hY4 g g.2)
    have hdvd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  have := le_pCoreOf_of_le_normalizer 2 hYH hYN hpY
  rw [hO] at this
  exact this

noncomputable def actOn {G : Type} [Group G] {H L : Subgroup G}
    (hLN : H ≤ Subgroup.normalizer (L : Set G)) : ↥H →* MulAut ↥L :=
  (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hLN)

theorem actOn_apply_coe {G : Type} [Group G] {H L : Subgroup G}
    (hLN : H ≤ Subgroup.normalizer (L : Set G)) (h : ↥H) (l : ↥L) :
    ((actOn hLN h l : ↥L) : G) = (h : G) * (l : G) * (h : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(h : G), hLN h.2⟩ l

theorem mem_ker_actOn {G : Type} [Group G] {H L : Subgroup G}
    (hLN : H ≤ Subgroup.normalizer (L : Set G)) (h : ↥H) :
    h ∈ (actOn hLN).ker ↔ (h : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 l hl
    have := congrArg (fun m : ↥L => (m : G)) (DFunLike.congr_fun h1 ⟨l, hl⟩)
    simp only [actOn_apply_coe, MulAut.one_apply] at this
    calc l * (h : G) = ((h : G) * l * (h : G)⁻¹) * (h : G) := by rw [this]
      _ = (h : G) * l := by group
  · intro h1
    ext l
    rw [actOn_apply_coe]
    have := h1 (l : G) l.2
    show (h : G) * (l : G) * (h : G)⁻¹ = l
    calc (h : G) * (l : G) * (h : G)⁻¹ = ((h : G) * l) * (h : G)⁻¹ := rfl
      _ = (l * h) * (h : G)⁻¹ := by rw [this]
      _ = l := by group

theorem exists_embedding {G : Type} [Group G] {H L : Subgroup G} {d : G}
    (hLN : H ≤ Subgroup.normalizer (L : Set G)) (hLH : L ≤ H)
    (hdc : ∀ g ∈ H, g * d = d * g) {Gc : Type} [Group Gc] (φ : ↥H →* Gc)
    (hφs : Function.Surjective φ) (hker : φ.ker = (Subgroup.zpowers d).subgroupOf H)
    (hY : H ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers d) :
    ∃ ρ : Gc →* MulAut ↥L, Function.Injective ρ ∧ ∀ h : ↥H, ρ (φ h) = actOn hLN h := by
  have hker' : φ.ker = (actOn hLN).ker := by
    ext h
    rw [hker, mem_ker_actOn, Subgroup.mem_subgroupOf]
    constructor
    · intro hd
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      rw [← hk]
      exact (Commute.zpow_left (show Commute d l from (hdc l (hLH hl)).symm) k).eq.symm
    · intro hc
      exact hY ⟨h.2, hc⟩
  have hle : φ.ker ≤ (actOn hLN).ker := hker'.le
  refine ⟨(MonoidHom.liftOfSurjective φ hφs) ⟨actOn hLN, hle⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨h, rfl⟩ := hφs g
    have h1 : actOn hLN h = 1 := by
      rw [← MonoidHom.liftOfRightInverse_comp_apply φ _ (Function.rightInverse_surjInv hφs)
        ⟨actOn hLN, hle⟩ h]
      exact hg
    have h2 : h ∈ φ.ker := by rw [hker']; exact h1
    exact h2
  · intro h
    exact MonoidHom.liftOfRightInverse_comp_apply φ _ (Function.rightInverse_surjInv hφs)
      ⟨actOn hLN, hle⟩ h

set_option maxRecDepth 100000 in
private theorem centralizer_alt_seven :
    ∀ c : Equiv.Perm (Fin 7),
      c * (Equiv.swap 0 1 * Equiv.swap 1 2) = (Equiv.swap 0 1 * Equiv.swap 1 2) * c →
      c * (Equiv.swap 3 4 * Equiv.swap 4 5) = (Equiv.swap 3 4 * Equiv.swap 4 5) * c →
      c * (Equiv.swap 0 1 * Equiv.swap 3 4) = (Equiv.swap 0 1 * Equiv.swap 3 4) * c → c = 1 := by
  decide +kernel

private theorem centralizer_alt_six :
    ∀ c : Equiv.Perm (Fin 6),
      c * (Equiv.swap 0 1 * Equiv.swap 1 2) = (Equiv.swap 0 1 * Equiv.swap 1 2) * c →
      c * (Equiv.swap 3 4 * Equiv.swap 4 5) = (Equiv.swap 3 4 * Equiv.swap 4 5) * c →
      c * (Equiv.swap 0 1 * Equiv.swap 3 4) = (Equiv.swap 0 1 * Equiv.swap 3 4) * c → c = 1 := by
  decide +kernel

private theorem sign_gen_six :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 3 4) = 1 := by
  decide +kernel

private theorem sign_gen_seven :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) = 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 3 4) = 1 := by
  decide +kernel

private theorem alt_outer_impossible {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L)
    {n : ℕ} (hcent : ∀ c : Equiv.Perm (Fin n),
      (∀ g ∈ alternatingGroup (Fin n), c * g = g * c) → c = 1)
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : Equiv.Perm.sign σ = -1)
    (hperm : ∀ x y : ↥L, (y : G) = z⁻¹ * (x : G) * z →
      ((φ (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ⁻¹ * ((φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ) :
    False := by
  set ζ : ↥L := ⟨z, hz⟩ with hζ
  set a : alternatingGroup (Fin n) := φ (QuotientGroup.mk ζ) with ha
  have hc : (σ * (a : Equiv.Perm (Fin n))⁻¹) = 1 := by
    apply hcent
    intro g hg
    obtain ⟨x, hx⟩ := (φ.surjective.comp QuotientGroup.mk_surjective) ⟨g, hg⟩
    have h1 := hperm x (ζ⁻¹ * x * ζ) (by simp [hζ])
    have h2 : ((φ (QuotientGroup.mk (ζ⁻¹ * x * ζ)) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) = (a : Equiv.Perm (Fin n))⁻¹ * g * a := by
      have : φ (QuotientGroup.mk (ζ⁻¹ * x * ζ)) = a⁻¹ * (φ (QuotientGroup.mk x)) * a := by
        simp [ha]
      rw [this]
      have hx' : (φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) = ⟨g, hg⟩ := hx
      rw [hx']
      simp
    have hx2 : ((φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = g := by
      have : (φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) = ⟨g, hg⟩ := hx
      rw [this]
    rw [h2, hx2] at h1
    have h3 : σ * ((a : Equiv.Perm (Fin n))⁻¹ * g * a) = g * σ := by
      rw [h1]; group
    calc σ * (a : Equiv.Perm (Fin n))⁻¹ * g
        = σ * ((a : Equiv.Perm (Fin n))⁻¹ * g * a) * (a : Equiv.Perm (Fin n))⁻¹ := by group
      _ = g * σ * (a : Equiv.Perm (Fin n))⁻¹ := by rw [h3]
      _ = g * (σ * (a : Equiv.Perm (Fin n))⁻¹) := by group
  have hσa : σ = (a : Equiv.Perm (Fin n)) := by
    have := congrArg (· * (a : Equiv.Perm (Fin n))) hc
    simpa using this
  have : Equiv.Perm.sign σ = 1 := by
    rw [hσa]
    exact Equiv.Perm.mem_alternatingGroup.mp a.2
  rw [hσ] at this
  exact absurd this (by decide)

theorem not_lemma115CaseC {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L) :
    ¬ Lemma115CaseC L z := by
  rintro ⟨φ, σ, -, hσ, -, hperm⟩
  refine alt_outer_impossible hz ?_ φ σ ?_ hperm
  · intro c hc
    refine centralizer_alt_six c ?_ ?_ ?_
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_six.1)
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_six.2.1)
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_six.2.2)
  · obtain ⟨x, y, hxy, rfl⟩ := hσ
    exact Equiv.Perm.sign_swap hxy

theorem not_lemma115CaseD {G : Type} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L) :
    ¬ Lemma115CaseD L z := by
  rintro ⟨φ, σ, -, hσ, hperm⟩
  refine alt_outer_impossible hz ?_ φ σ ?_ hperm.2
  · intro c hc
    refine centralizer_alt_seven c ?_ ?_ ?_
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_seven.1)
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_seven.2.1)
    · exact hc _ (Equiv.Perm.mem_alternatingGroup.mpr sign_gen_seven.2.2)
  · rw [Equiv.Perm.sign_of_cycleType, hσ]
    decide

end Insp7

end CFSG.Quasithin
