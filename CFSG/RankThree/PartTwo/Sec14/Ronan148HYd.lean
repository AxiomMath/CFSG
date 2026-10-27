module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HInc
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] def Item464OneA6K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON →
    ∀ P : Subgroup X, Late.IsE27 P → ∀ q ∈ P, q ∉ Subgroup.center X →
    ∀ M F : Subgroup X, P ≤ Subgroup.normalizer (M : Set X) → Group.IsPerfect M →
      IsQuasisimple (M ⧸ aschbacherSolvableCore 3 M) →
      Sec4.IsList46 (M ⧸ aschbacherSolvableCore 3 M) →
      F ≤ M → F ≤ Subgroup.centralizer ({q} : Set X) → Group.IsPerfect F →
      Sec4.IsTripleCover (F ⧸ aschbacherSolvableCore 3 F) (alternatingGroup (Fin 6)) →
      q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M) →
      M = ⊤

@[expose] def Item464OneA5K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON →
    ∀ P : Subgroup X, Late.IsE27 P → ∀ q ∈ P, q ∉ Subgroup.center X →
    ∀ M F : Subgroup X, P ≤ Subgroup.normalizer (M : Set X) → Group.IsPerfect M →
      IsQuasisimple (M ⧸ aschbacherSolvableCore 3 M) →
      Sec4.IsList46 (M ⧸ aschbacherSolvableCore 3 M) →
      F ≤ M → F ≤ Subgroup.centralizer ({q} : Set X) → Group.IsPerfect F →
      Nonempty (F ⧸ aschbacherSolvableCore 3 F ≃* alternatingGroup (Fin 5)) →
      q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M) →
      M = ⊤

section Theta

variable {Q R : Type*} [Group Q] [Group R] [Finite Q]

theorem map_theta_eq_of_ker_le (f : Q →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ aschbacherSolvableCore 3 Q) :
    (aschbacherSolvableCore 3 Q).map f = aschbacherSolvableCore 3 R := by
  haveI : Finite R := Finite.of_surjective f hf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  obtain ⟨hθs', hθc', hθ3', hθmax', -⟩ :=
    solvable_prime_complement_core_characterization (H := R) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 Q).Normal := by haveI := hθc; infer_instance
  haveI : (aschbacherSolvableCore 3 R).Normal := by haveI := hθc'; infer_instance
  apply le_antisymm
  · refine hθmax' _ ((inferInstance : (aschbacherSolvableCore 3 Q).Normal).map f hf) ?_ ?_
    · haveI := hθs
      exact Group.isSolvable_of_surjective (f := f.subgroupMap (aschbacherSolvableCore 3 Q))
        (f.subgroupMap_surjective _)
    · intro h3
      exact hθ3 (h3.trans (Subgroup.card_map_dvd _ f))
  · set T := (aschbacherSolvableCore 3 R).comap f with hT
    have hTn : T.Normal := (inferInstance : (aschbacherSolvableCore 3 R).Normal).comap f
    have hkerT : f.ker ≤ T := fun x hx => by
      rw [hT, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]; exact Subgroup.one_mem _
    have hTs : Group.IsSolvable T := by
      haveI := hθs'
      haveI : Group.IsSolvable f.ker :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hker)
          (Subgroup.inclusion_injective _)
      haveI := hθs
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hkerT)
        ((f.comp T.subtype).codRestrict (aschbacherSolvableCore 3 R) fun t => t.2) ?_
      intro t ht
      rw [MonoidHom.mem_ker] at ht
      have ht' : f t = 1 := congrArg Subtype.val ht
      exact ⟨⟨t, MonoidHom.mem_ker.mpr ht'⟩, rfl⟩
    have hT3 : ¬ 3 ∣ Nat.card T := by
      intro h3
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 h3
      have hft : orderOf (f t) ∣ 3 := by
        rw [← ht]
        have := orderOf_map_dvd f (t : Q)
        rwa [Subgroup.orderOf_coe] at this
      have hf1 : f t = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hft with h1 | h1
        · exact orderOf_eq_one_iff.mp h1
        · exfalso
          apply hθ3'
          have := Subgroup.orderOf_dvd_natCard (aschbacherSolvableCore 3 R) t.2
          rwa [h1] at this
      have htθ : (t : Q) ∈ aschbacherSolvableCore 3 Q := hker (MonoidHom.mem_ker.mpr hf1)
      apply hθ3
      have := Subgroup.orderOf_dvd_natCard (aschbacherSolvableCore 3 Q) htθ
      rwa [Subgroup.orderOf_coe, ht] at this
    have hTθ : T ≤ aschbacherSolvableCore 3 Q := hθmax T hTn hTs hT3
    calc aschbacherSolvableCore 3 R = T.map f := (Subgroup.map_comap_eq_self_of_surjective hf _).symm
      _ ≤ (aschbacherSolvableCore 3 Q).map f := Subgroup.map_mono hTθ

theorem nonempty_thetaQuot_equiv_of_ker_le (f : Q →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ aschbacherSolvableCore 3 Q) :
    Nonempty (Q ⧸ aschbacherSolvableCore 3 Q ≃* R ⧸ aschbacherSolvableCore 3 R) := by
  haveI : Finite R := Finite.of_surjective f hf
  obtain ⟨-, hθc, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  obtain ⟨-, hθc', -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := R) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 Q).Normal := by haveI := hθc; infer_instance
  haveI : (aschbacherSolvableCore 3 R).Normal := by haveI := hθc'; infer_instance
  set g := (QuotientGroup.mk' (aschbacherSolvableCore 3 R)).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = aschbacherSolvableCore 3 Q := by
    rw [hg, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    apply le_antisymm
    · rw [← map_theta_eq_of_ker_le f hf hker]
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hx
      have : y⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      have := Subgroup.mul_mem _ hy (hker this)
      simpa using this
    · rw [← Subgroup.map_le_iff_le_comap, map_theta_eq_of_ker_le f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩


theorem comap_theta_le {C : Type*} [Group C] [Finite C] (ι : Q →* C) (hι : Function.Injective ι) :
    (aschbacherSolvableCore 3 C).comap ι ≤ aschbacherSolvableCore 3 Q := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  obtain ⟨hθs', hθc', hθ3', -, -⟩ :=
    solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 C).Normal := by haveI := hθc'; infer_instance
  set T := (aschbacherSolvableCore 3 C).comap ι with hT
  have hTn : T.Normal := (inferInstance : (aschbacherSolvableCore 3 C).Normal).comap ι
  let j : T →* aschbacherSolvableCore 3 C :=
    { toFun := fun t => ⟨ι t, t.2⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι (x : Q) (y : Q)) }
  have hj : Function.Injective j := fun x y hxy =>
    Subtype.ext (hι (congrArg Subtype.val hxy))
  have hTs : Group.IsSolvable T := by
    haveI := hθs'
    exact Group.isSolvable_of_isSolvable_injective hj
  have hT3 : ¬ 3 ∣ Nat.card T := fun h3 =>
    hθ3' (h3.trans (Subgroup.card_dvd_of_injective j hj))
  exact hθmax T hTn hTs hT3

theorem theta_thetaQuot_eq_bot : aschbacherSolvableCore 3 (Q ⧸ aschbacherSolvableCore 3 Q) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 Q).Normal := by haveI := hθc; infer_instance
  set N := aschbacherSolvableCore 3 Q with hN
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hTs, hTc, hT3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q ⧸ N) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 (Q ⧸ N)).Normal := by haveI := hTc; infer_instance
  set T := aschbacherSolvableCore 3 (Q ⧸ N) with hT
  set T' := T.comap π with hT'
  have hNT' : N ≤ T' := fun x hx => by
    rw [hT', Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact T.one_mem
  have hT'n : T'.Normal := (inferInstance : T.Normal).comap π
  have hT's : Group.IsSolvable T' := by
    haveI := hθs
    haveI := hTs
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNT')
      ((π.comp T'.subtype).codRestrict T fun t => t.2) ?_
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have ht' : π t = 1 := congrArg Subtype.val ht
    exact ⟨⟨t, (QuotientGroup.eq_one_iff (t : Q)).mp ht'⟩, rfl⟩
  have hT'3 : ¬ 3 ∣ Nat.card T' := by
    intro h3
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T') 3 h3
    have hft : orderOf (π t) ∣ 3 := by
      rw [← ht]
      have := orderOf_map_dvd π (t : Q)
      rwa [Subgroup.orderOf_coe] at this
    have hf1 : π t = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hft with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        apply hT3
        have := Subgroup.orderOf_dvd_natCard T t.2
        rwa [h1] at this
    have htN : (t : Q) ∈ N := (QuotientGroup.eq_one_iff (t : Q)).mp hf1
    apply hθ3
    have := Subgroup.orderOf_dvd_natCard N htN
    rwa [Subgroup.orderOf_coe, ht] at this
  have hT'N : T' ≤ N := hθmax T' hT'n hT's hT'3
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have : y ∈ T' := hx
  exact (QuotientGroup.eq_one_iff y).mpr (hT'N this)

end Theta

theorem mem_of_mem_sup_coprime {G : Type*} [Group G] [Finite G] {Y T : Subgroup G} {d : G}
    (hYT : Y ≤ Subgroup.normalizer (T : Set G)) (hT3 : Nat.Coprime 3 (Nat.card T))
    (hd3 : d ^ 3 = 1) (hdT : ∀ t ∈ T, t * d = d * t) (hd : d ∈ Y ⊔ T) : d ∈ Y := by
  have hmul : d ∈ ((Y : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y T hYT]; exact hd
  obtain ⟨y, hy, t, ht, hyt⟩ := hmul
  set s := t⁻¹ with hs
  have hsT : s ∈ T := T.inv_mem ht
  have hyds : y = d * s := by rw [hs, ← hyt]; group
  have hsd : s * d = d * s := hdT s hsT
  set r := orderOf s with hr
  have hr3 : Nat.Coprime 3 r := Nat.Coprime.coprime_dvd_right
    (Subgroup.orderOf_dvd_natCard T hsT) hT3
  have hpow : y ^ (r ^ 2) = d := by
    rw [hyds, (Commute.mul_pow (show Commute d s from hsd.symm) _)]
    have h1 : s ^ (r ^ 2) = 1 := by
      rw [pow_two, pow_mul, pow_orderOf_eq_one, one_pow]
    have h2 : d ^ (r ^ 2) = d := by
      have : r ^ 2 % 3 = 1 := by
        have h3 : r % 3 = 1 ∨ r % 3 = 2 := by
          have := (Nat.coprime_comm.mp hr3)
          have hne : r % 3 ≠ 0 := fun h0 => by
            have : 3 ∣ r := Nat.dvd_of_mod_eq_zero h0
            have h1 := Nat.Coprime.coprime_dvd_right this hr3
            norm_num at h1
          omega
        rcases h3 with h | h <;> simp [Nat.pow_mod, h]
      conv_lhs => rw [← Nat.div_add_mod (r ^ 2) 3, this, pow_add, pow_mul, hd3, one_pow,
        one_mul, pow_one]
    rw [h1, mul_one, h2]
  rw [← hpow]
  exact Y.pow_mem hy _

section Image

variable {G : Type} [Group G] [Finite G]

theorem le_map_of_le_sup {d : G} {K Z : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({d} : Set G)) (hZC : Z ≤ Subgroup.centralizer ({d} : Set G))
    (hZK : Z ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)))
    (z : G) (hz : z ∈ Z) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({d} : Set G)))
        (⟨z, hZC hz⟩ : ↥(Subgroup.centralizer ({d} : Set G))) ∈
      (K.subgroupOf (Subgroup.centralizer ({d} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({d} : Set G)))) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set θC := aschbacherSolvableCore 3 ↥C with hθC
  obtain ⟨-, hθc, -, -, -⟩ := solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  haveI : θC.Normal := by haveI := hθc; infer_instance
  have hmap : (K.subgroupOf C ⊔ θC).map C.subtype = K ⊔ inSubgroup (aschbacherSolvableCore 3) C := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKC]
    rfl
  have hz' : (⟨z, hZC hz⟩ : C) ∈ K.subgroupOf C ⊔ θC := by
    have : z ∈ (K.subgroupOf C ⊔ θC).map C.subtype := by rw [hmap]; exact hZK hz
    obtain ⟨w, hw, hwz⟩ := this
    have : w = ⟨z, hZC hz⟩ := Subtype.ext hwz
    rwa [this] at hw
  have : QuotientGroup.mk' θC (⟨z, hZC hz⟩ : C) ∈ (K.subgroupOf C ⊔ θC).map (QuotientGroup.mk' θC) :=
    ⟨_, hz', rfl⟩
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at this


theorem isTripleCover_yd_of_core (Φ : ∀ (T : Type) [Group T], Prop)
    (hΦ : ∀ {T T' : Type} [Group T] [Group T'], (T ≃* T') → Φ T → Φ T')
    (hres : ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON →
      ∀ P : Subgroup X, Late.IsE27 P → ∀ q ∈ P, q ∉ Subgroup.center X →
      ∀ M F : Subgroup X, P ≤ Subgroup.normalizer (M : Set X) → Group.IsPerfect M →
        IsQuasisimple (M ⧸ aschbacherSolvableCore 3 M) →
        Sec4.IsList46 (M ⧸ aschbacherSolvableCore 3 M) →
        F ≤ M → F ≤ Subgroup.centralizer ({q} : Set X) → Group.IsPerfect F →
        Φ (F ⧸ aschbacherSolvableCore 3 F) →
        q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M) → M = ⊤)
    {d b : G} {A K Yd YB : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d)
    (hON : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) CFSG.Blueprint.NativeSporadic.ON)
    (hA : Late.IsE27 A) (hAK : A ≤ K) (hbA : b ∈ A)
    (hYdC : Yd ≤ Subgroup.centralizer ({d} : Set G)) (hYdp : Group.IsPerfect Yd)
    (hYdq : IsQuasisimple (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd))
    (hYdL : Sec4.IsList46 (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd))
    (hYdK : Yd ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)))
    (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hYBYd : YB ≤ Yd) (hYBb : YB ≤ Subgroup.centralizer ({b} : Set G)) (hYBp : Group.IsPerfect YB)
    (hYBΦ : Φ (↥YB ⧸ aschbacherSolvableCore 3 ↥YB))
    (hbn : b ∉ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd)) :
    Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) CFSG.Blueprint.NativeSporadic.ON ∧
      K ≤ Yd ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) := by
  classical
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set θC := aschbacherSolvableCore 3 ↥C with hθC
  obtain ⟨hθCs, hθCc, hθC3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  haveI : θC.Normal := by haveI := hθCc; infer_instance
  set ρ := QuotientGroup.mk' θC with hρ
  obtain ⟨hKC, hK'⟩ := (mem_thetaComponentsIn_iff (H := C)).mp
    ((thetaComponentsAt_eq_thetaComponentsIn d) ▸ hK)
  set K' := K.subgroupOf C with hK'def
  obtain ⟨-, -, ⟨η, -⟩, -⟩ := CFSG.RankThree.theta_quotient_component_structure hK'
  set X := K'.map ρ with hX
  have eK : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hONX : Sec4.IsTripleCover ↥X CFSG.Blueprint.NativeSporadic.ON :=
    Sec13.isTripleCover_of_mulEquiv ((thetaQuotEquiv eK).symm.trans η) hON
  have hXp : Group.IsPerfect ↥X := by
    haveI : Group.IsPerfect ↥K' := hK'.1
    exact Group.IsPerfect.ofSurjective (f := ρ.subgroupMap K') (ρ.subgroupMap_surjective K')
  have hAC : A ≤ C := hAK.trans hKC
  have hYBC : YB ≤ C := hYBYd.trans hYdC
  have hAX : ∀ a (ha : a ∈ A), ρ ⟨a, hAC ha⟩ ∈ X := fun a ha =>
    ⟨⟨a, hAC ha⟩, Subgroup.mem_subgroupOf.mpr (hAK ha), rfl⟩
  have hYdX : ∀ y (hy : y ∈ Yd), ρ ⟨y, hYdC hy⟩ ∈ X := fun y hy =>
    le_map_of_le_sup hKC hYdC hYdK y hy
  set φ : ↥Yd →* ↥X :=
    (ρ.comp (Subgroup.inclusion hYdC)).codRestrict X fun y => hYdX y y.2 with hφ
  set ψ : ↥A →* ↥X :=
    (ρ.comp (Subgroup.inclusion hAC)).codRestrict X fun a => hAX a a.2 with hψ
  set χ : ↥YB →* ↥X :=
    (ρ.comp (Subgroup.inclusion hYBC)).codRestrict X fun y => hYdX y (hYBYd y.2) with hχ
  have hφv : ∀ y : Yd, ((φ y : X) : ↥C ⧸ θC) = ρ ⟨y, hYdC y.2⟩ := fun _ => rfl
  have hψv : ∀ a : A, ((ψ a : X) : ↥C ⧸ θC) = ρ ⟨a, hAC a.2⟩ := fun _ => rfl
  have hχv : ∀ y : YB, ((χ y : X) : ↥C ⧸ θC) = ρ ⟨y, hYBC y.2⟩ := fun _ => rfl
  have hφker : φ.ker ≤ aschbacherSolvableCore 3 ↥Yd := by
    refine le_trans ?_ (comap_theta_le (Subgroup.inclusion hYdC) (Subgroup.inclusion_injective _))
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ρ ⟨y, hYdC y.2⟩ = 1 := by rw [← hφv]; exact congrArg Subtype.val hy
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hχker : χ.ker ≤ aschbacherSolvableCore 3 ↥YB := by
    refine le_trans ?_ (comap_theta_le (Subgroup.inclusion hYBC) (Subgroup.inclusion_injective _))
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ρ ⟨y, hYBC y.2⟩ = 1 := by rw [← hχv]; exact congrArg Subtype.val hy
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : ρ ⟨a, hAC a.2⟩ = 1 := by rw [← hψv]; exact congrArg Subtype.val ha
    have hmem : (⟨a, hAC a.2⟩ : C) ∈ θC := (QuotientGroup.eq_one_iff _).mp h1
    have ho : orderOf (⟨a, hAC a.2⟩ : C) ∣ 3 := by
      have h3 : (a : G) ^ 3 = 1 := hA.1.2 a a.2
      have : (⟨a, hAC a.2⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using h3)
      exact orderOf_dvd_of_pow_eq_one this
    have ho' : orderOf (⟨a, hAC a.2⟩ : C) ∣ Nat.card θC := Subgroup.orderOf_dvd_natCard θC hmem
    have h1' : orderOf (⟨a, hAC a.2⟩ : C) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp ho with h | h
      · exact h
      · have h' := ho'
        rw [h] at h'
        exact absurd h' hθC3
    have : (⟨a, hAC a.2⟩ : C) = 1 := orderOf_eq_one_iff.mp h1'
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using congrArg (fun z : C => (z : G)) this))
  set M := φ.range with hM
  set P := ψ.range with hP
  set F := χ.range with hF
  set q := ψ ⟨b, hbA⟩ with hq
  have hθM := map_theta_eq_of_ker_le φ.rangeRestrict φ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hφker)
  obtain ⟨eM⟩ := nonempty_thetaQuot_equiv_of_ker_le φ.rangeRestrict φ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hφker)
  obtain ⟨eF⟩ := nonempty_thetaQuot_equiv_of_ker_le χ.rangeRestrict χ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hχker)
  have hMp : Group.IsPerfect M :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hFp : Group.IsPerfect F :=
    Group.IsPerfect.ofSurjective (f := χ.rangeRestrict) χ.rangeRestrict_surjective
  have hMq : IsQuasisimple (↥M ⧸ aschbacherSolvableCore 3 ↥M) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eM hYdq
  have hML : Sec4.IsList46 (↥M ⧸ aschbacherSolvableCore 3 ↥M) :=
    Sec21.Item223PrintProof.isList46_of_mulEquiv eM hYdL
  have hFΦ : Φ (↥F ⧸ aschbacherSolvableCore 3 ↥F) := hΦ eF hYBΦ
  have hPE : Late.IsE27 P := by
    have e : ↥A ≃* ↥P := MonoidHom.ofInjective hψinj
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨x', rfl⟩ := e.surjective x
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hA.1.1.is_comm.comm x' y']
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (hA.1.2 a a.2), map_one]
    · rw [← Nat.card_congr e.toEquiv]; exact hA.2
  have hqP : q ∈ P := ⟨⟨b, hbA⟩, rfl⟩
  have hconj : ∀ (a : A) (y : Yd) (h : (a : G) * y * (a : G)⁻¹ ∈ Yd),
      ψ a * φ y * (ψ a)⁻¹ = φ ⟨_, h⟩ := by
    intro a y h
    apply Subtype.ext
    show ρ ⟨a, hAC a.2⟩ * ρ ⟨y, hYdC y.2⟩ * (ρ ⟨a, hAC a.2⟩)⁻¹ = ρ ⟨_, hYdC h⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hPM : P ≤ Subgroup.normalizer (M : Set ↥X) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · rintro ⟨y, rfl⟩
      have hay : (a : G) * y * (a : G)⁻¹ ∈ Yd :=
        (Subgroup.mem_normalizer_iff.mp (hAYd a.2) y).mp y.2
      exact ⟨⟨_, hay⟩, (hconj a y hay).symm⟩
    · rintro ⟨y, hy⟩
      have hay : (a : G)⁻¹ * y * (a : G)⁻¹⁻¹ ∈ Yd :=
        (Subgroup.mem_normalizer_iff.mp (hAYd (A.inv_mem a.2)) y).mp y.2
      refine ⟨⟨_, hay⟩, ?_⟩
      have h3 : m = ψ a⁻¹ * φ y * (ψ a⁻¹)⁻¹ := by
        rw [hy, map_inv, inv_inv]; group
      rw [h3, hconj a⁻¹ y hay]
      rfl
  have hFM : F ≤ M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨y, hYBYd y.2⟩, rfl⟩
  have hFq : F ≤ Subgroup.centralizer ({q} : Set ↥X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show ρ ⟨y, hYBC y.2⟩ * ρ ⟨b, hAC hbA⟩ = ρ ⟨b, hAC hbA⟩ * ρ ⟨y, hYBC y.2⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYBb y.2)
  have hqsc : q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M) := by
    rintro ⟨-, hqc⟩
    apply hbn
    refine ⟨hbA, fun y hy => ?_⟩
    have hby : (b * y * b⁻¹ * y⁻¹ : G) ∈ Yd :=
      Yd.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAYd hbA) y).mp hy) (Yd.inv_mem hy)
    have h2 : (φ ⟨_, hby⟩ : X) = q * φ ⟨y, hy⟩ * q⁻¹ * (φ ⟨y, hy⟩)⁻¹ := by
      apply Subtype.ext
      show ρ ⟨_, hYdC hby⟩ = ρ ⟨b, hAC hbA⟩ * ρ ⟨y, hYdC hy⟩ * (ρ ⟨b, hAC hbA⟩)⁻¹ *
        (ρ ⟨y, hYdC hy⟩)⁻¹
      rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
      rfl
    have h1 := hqc (φ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    rw [← h2] at h1
    obtain ⟨t, ht, hte⟩ := h1
    rw [← hθM] at ht
    obtain ⟨u, hu, hue⟩ := ht
    have hue' : φ u = φ ⟨_, hby⟩ := by
      have h4 : ((φ.rangeRestrict u : M) : X) = (t : X) := congrArg Subtype.val hue
      rw [← hte]
      exact h4
    have hk : u⁻¹ * ⟨_, hby⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hue', inv_mul_cancel]
    have hθ := Subgroup.mul_mem _ hu (hφker hk)
    rw [mul_inv_cancel_left] at hθ
    exact ⟨_, hθ, rfl⟩
  have hqZ : q ∉ Subgroup.center ↥X := by
    intro hqc
    apply hqsc
    refine ⟨hqP, fun m _ => ?_⟩
    rw [(Subgroup.mem_center_iff.mp hqc m).symm, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hMtop : M = ⊤ := hres ↥X hXp hONX P hPE q hqP hqZ M F hPM hMp hMq hML hFM hFq hFp hFΦ hqsc
  have hθX : aschbacherSolvableCore 3 ↥X = ⊥ := by
    rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three η,
      theta_thetaQuot_eq_bot, Subgroup.map_bot]
  have eMX : ↥M ≃* ↥X := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have e : ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥X :=
    (eM.trans (thetaQuotEquiv eMX)).trans
      ((QuotientGroup.quotientMulEquivOfEq hθX).trans QuotientGroup.quotientBot)
  refine ⟨Sec13.isTripleCover_of_mulEquiv e.symm hONX, fun k hk => ?_⟩
  have hkX : ρ ⟨k, hKC hk⟩ ∈ X := ⟨⟨k, hKC hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hkM : (⟨_, hkX⟩ : X) ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  obtain ⟨y, hy⟩ := hkM
  have hy' : ρ ⟨y, hYdC y.2⟩ = ρ ⟨k, hKC hk⟩ := congrArg Subtype.val hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hy'
  have hk' : k = (y : G) * ((⟨y, hYdC y.2⟩ : C)⁻¹ * ⟨k, hKC hk⟩ : C) := by
    simp
  rw [hk']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right ⟨_, hy', rfl⟩)

end Image

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
