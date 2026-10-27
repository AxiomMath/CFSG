module

public import CFSG.RankThree.PartTwo.KFacts.KF1418MJ
public import CFSG.RankThree.PartTwo.KFacts.KF1418MJModel
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec4.Item47Lift
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1Core
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF1418MJProof

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup
open CFSG.RankThree.LocalRank
  (aschbacherSolvableCore solvable_prime_complement_core_characterization)
open scoped commutatorElement

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (h : center Y = ⊥) : center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : φ z ∈ center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hz y']
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact φ.injective (h1.trans (map_one φ).symm)

theorem kf1418MJ_of (hX : ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* NativeSporadic.M12) ∨ Nonempty (X ≃* NativeSporadic.J2)) →
      center X = ⊥ ∧ Nat.card (MulAut X) = 2 * Nat.card X ∧ KF1418MJModel X) :
    KF1418MJ := by
  intro G _ _ K A R e hiso hA hA27 hAN hAe hR hRθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, hAut, hmodel⟩ := hX _ hiso
  set θK := aschbacherSolvableCore 3 K
  set π : K →* K ⧸ θK := QuotientGroup.mk' θK
  have hπ1 : ∀ k : K, π k = 1 ↔ k ∈ θK := fun k => QuotientGroup.eq_one_iff k
  set ρ : A →* MulAut (K ⧸ θK) :=
    ((Sec4.thetaQuotMulAut K).comp (Sec4.compAction K)).comp (Subgroup.inclusion hAN)
  have hρapp : ∀ (a : A) (k : K), ρ a (π k) =
      π ⟨(a : G) * k * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAN a.2) k).mp k.2⟩ :=
    fun _ _ => rfl
  have heA : e ∈ A := by
    have h : e ∈ A ⊓ Sec4.thetaQuotCentralizer K := by
      rw [hAe]
      exact Subgroup.mem_zpowers e
    exact h.1
  have hker : ∀ a : A, ρ a = 1 → (a : G) ∈ zpowers e := by
    intro a ha
    rw [← hAe]
    exact ⟨a.2, ⟨Subgroup.inclusion hAN a, MonoidHom.mem_ker.mpr ha, rfl⟩⟩
  have hrange9 : 3 ^ 2 ∣ Nat.card ρ.range := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hA27] at h1
    have hk : Nat.card ρ.ker ∣ 3 := by
      have hle : ρ.ker.map A.subtype ≤ zpowers e := by
        rintro _ ⟨a, ha, rfl⟩
        exact hker a ha
      have h2 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective A.subtype_injective, Nat.card_zpowers] at h2
      exact h2.trans (orderOf_dvd_of_pow_eq_one (hA.2 e heA))
    rcases (Nat.dvd_prime Nat.prime_three).mp hk with h | h
    · rw [h, one_mul] at h1
      rw [h1]
      norm_num
    · rw [h] at h1
      have h9 : Nat.card ρ.range = 9 := by omega
      rw [h9]
      norm_num
  have hinner : ρ.range ≤ (MulAut.conj : K ⧸ θK →* MulAut (K ⧸ θK)).range := by
    rintro _ ⟨a, rfl⟩
    have h3 : ρ a ^ 3 = 1 := by
      rw [← map_pow]
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a a.2)
      rw [ha3, map_one]
    have hodd : Odd (orderOf (ρ a)) := Odd.of_dvd_nat ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one h3)
    obtain ⟨w, hw⟩ := GH74.GLS.Stage2.Signalizer.Ivk8.N1Core.inner_of_odd_order hZ hAut hodd
    exact ⟨w, hw.symm⟩
  have hinj : Function.Injective (MulAut.conj : K ⧸ θK →* MulAut (K ⧸ θK)) :=
    GH74.GLS.Stage2.Signalizer.Ivk8.N1Core.conj_injective hZ
  set V' := ρ.range.comap (MulAut.conj : K ⧸ θK →* MulAut (K ⧸ θK)) with hV'
  have hV'card : Nat.card V' = Nat.card ρ.range := by
    have h := Subgroup.card_map_of_injective
      (f := (MulAut.conj : K ⧸ θK →* MulAut (K ⧸ θK))) (K := V') hinj
    rw [hV', Subgroup.map_comap_eq_self hinner] at h
    exact h.symm
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (hV'card ▸ hrange9)
  set V := V₀.map V'.subtype with hVdef
  have hV9 : Nat.card V = 9 := by
    rw [hVdef, Subgroup.card_map_of_injective V'.subtype_injective, hV₀]
    norm_num
  have hVρ : ∀ w ∈ V, ∃ a : A, ρ a = MulAut.conj w := by
    intro w hw
    obtain ⟨a, ha⟩ := (Subgroup.map_subtype_le V₀ hw : MulAut.conj w ∈ ρ.range)
    exact ⟨a, ha⟩
  obtain ⟨hRK, hR2, hAR⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hR
  set T : Subgroup (K ⧸ θK) := (R.subgroupOf K).map π
  have hT2 : IsPGroup 2 T := (hR2.comap_of_injective K.subtype K.subtype_injective).map _
  have hT1 : T ≠ ⊥ := by
    intro h0
    apply hRθ
    intro r hr
    have hr' : (⟨r, hRK hr⟩ : K) ∈ θK := (hπ1 _).mp
      ((Subgroup.map_eq_bot_iff _).mp h0 (Subgroup.mem_subgroupOf.mpr hr))
    exact Sec6.theta_le_thetaQuotCentralizer K ⟨_, hr', rfl⟩
  have hρT : ∀ (a : A), ∀ t ∈ T, ρ a t ∈ T := by
    rintro a _ ⟨r, hr, rfl⟩
    rw [hρapp]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hAR a.2) r).mp
      (Subgroup.mem_subgroupOf.mp hr)), rfl⟩
  have hVT : V ≤ normalizer (T : Set (K ⧸ θK)) := by
    apply Sec6.le_normalizer_of_forall_conj_mem
    intro w hw t ht
    obtain ⟨a, ha⟩ := hVρ w hw
    have h := hρT a t ht
    rwa [ha, MulAut.conj_apply] at h
  obtain ⟨v, hvV, hnot⟩ := hmodel V T hV9 hT2 hT1 hVT
  obtain ⟨x', hx'⟩ := hVρ v hvV
  refine ⟨x', x'.2, fun hcomm => hnot ?_⟩
  set x : G := (x' : G)
  have hxN : x ∈ normalizer (K : Set G) := hAN x'.2
  have hx3 : x ^ 3 = 1 := hA.2 x x'.2
  set C := centralizer ({v} : Set (K ⧸ θK))
  set Q := inSubgroup (CFSG.pCore 2) C
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    rintro c hc _ ⟨q, hq, rfl⟩
    exact ⟨⟨c, hc⟩ * q * ⟨c, hc⟩⁻¹,
      (CFSG.pCore_normal (p := 2) (G := C)).conj_mem q hq _, rfl⟩
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map C.subtype
  have hDC : ∀ k : K, (k : G) * x = x * k → π k ∈ C := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    have h : ρ x' (π k) = π k := by
      rw [hρapp]
      congr 1
      apply Subtype.ext
      change x * k * x⁻¹ = k
      rw [← hk, mul_inv_cancel_right]
    rw [hx', MulAut.conj_apply] at h
    calc π k * v = (v * π k * v⁻¹) * v := by rw [h]
      _ = v * π k := by group
  set H := Sec4.thetaPreimage K Q with hH
  set D := K ⊓ centralizer ({x} : Set G)
  set P₀ := H ⊓ centralizer ({x} : Set G)
  have hP₀D : P₀ ≤ D := fun p hp => ⟨Sec4.thetaPreimage_le Q hp.1, hp.2⟩
  have hDP₀ : D ≤ normalizer (P₀ : Set G) := by
    apply Sec6.le_normalizer_of_forall_conj_mem
    intro d hd p hp
    obtain ⟨hdK, hdx⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hpH, hpx⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨hpK, hpQ⟩ := Sec4.mem_thetaPreimage.mp hpH
    have hdpK : d * p * d⁻¹ ∈ K := mul_mem (mul_mem hdK hpK) (inv_mem hdK)
    refine Subgroup.mem_inf.mpr ⟨Sec4.mem_thetaPreimage.mpr ⟨hdpK, ?_⟩,
      mul_mem (mul_mem hdx hpx) (inv_mem hdx)⟩
    have e : (⟨d * p * d⁻¹, hdpK⟩ : K) = ⟨d, hdK⟩ * ⟨p, hpK⟩ * ⟨d, hdK⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hCQ _ (hDC ⟨d, hdK⟩ (mem_centralizer_singleton_iff.mp hdx)) _ hpQ
  obtain ⟨hθsol, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have hQsol : Group.IsSolvable Q := by
    haveI := hQ2.isNilpotent
    infer_instance
  have hHsol : Group.IsSolvable H := by
    have hle : θK ≤ Q.comap π := fun k hk => by
      rw [Subgroup.mem_comap, (hπ1 k).mpr hk]
      exact one_mem Q
    let f : θK →* Q.comap π := Subgroup.inclusion hle
    let g : Q.comap π →* Q := (π.comp (Q.comap π).subtype).codRestrict Q (fun y => y.2)
    have hfg : g.ker ≤ f.range := by
      intro y hy
      have h1 : π y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      exact ⟨⟨y, (hπ1 _).mp h1⟩, rfl⟩
    haveI : Group.IsSolvable (Q.comap π) := solvable_of_ker_le_range f g hfg
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Q.comap π).equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  have hH3 : ¬ 3 ∣ Nat.card H := by
    rw [hH, Sec4.card_thetaPreimage]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hθ3 h
    · have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at h'
  have hP₀H : P₀ ≤ H := inf_le_left
  have hP₀sol : Group.IsSolvable P₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hP₀H)
  have hP₀3 : ¬ 3 ∣ Nat.card P₀ := fun h => hH3 (h.trans (Subgroup.card_dvd_of_le hP₀H))
  have hP₀θ : P₀ ≤ inSubgroup (aschbacherSolvableCore 3) D :=
    Sec6.le_theta_of_normal hP₀D hDP₀ hP₀sol hP₀3
  have hlift : ∀ q ∈ Q, ∃ k : K, (k : G) ∈ P₀ ∧ π k = q := by
    intro q hq
    have hqfix : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨x, hxN⟩) q = q := by
      have h : ρ x' q = q := by
        rw [hx', MulAut.conj_apply]
        have hqv := mem_centralizer_singleton_iff.mp (hQC hq)
        calc v * q * v⁻¹ = q * v * v⁻¹ := by rw [hqv]
          _ = q := mul_inv_cancel_right q v
      exact h
    have hqbar := (mem_barCentralizer_zpowers_iff hxN q).mpr hqfix
    rw [← imageModTheta_centralizer_eq hxN ⟨1, by rw [pow_one]; exact hx3⟩] at hqbar
    obtain ⟨k, hk, rfl⟩ := hqbar
    exact ⟨k, ⟨Sec4.mem_thetaPreimage.mpr ⟨k.2, hq⟩, (Subgroup.mem_subgroupOf.mp hk).2⟩, rfl⟩
  have hfixQ : ∀ q ∈ Q, ∀ a : A, ρ a q = q := by
    intro q hq a
    obtain ⟨k, hkP, rfl⟩ := hlift q hq
    have hc : ⁅(k : G), (a : G)⁆ ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      hcomm (Subgroup.commutator_mem_commutator (hP₀θ hkP) a.2)
    have hc' : (k : G)⁻¹ * ((a : G) * k * (a : G)⁻¹) ∈
        inSubgroup (aschbacherSolvableCore 3) K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta K (inv_mem k.2))
        _).mp (inv_mem hc)
      rwa [commutatorElement_def, show (k : G)⁻¹ * ((k : G) * a * (k : G)⁻¹ * (a : G)⁻¹)⁻¹ *
        (k : G)⁻¹⁻¹ = (k : G)⁻¹ * ((a : G) * k * (a : G)⁻¹) by group] at h1
    have hakK : (a : G) * k * (a : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAN a.2) k).mp k.2
    obtain ⟨t, ht, hte⟩ := hc'
    have htk : t = k⁻¹ * ⟨(a : G) * k * (a : G)⁻¹, hakK⟩ := Subtype.ext hte
    rw [hρapp]
    exact (QuotientGroup.eq.mpr (htk ▸ ht)).symm
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨a, ha⟩ := hVρ w hw
  have h := hfixQ q hq a
  rw [ha, MulAut.conj_apply] at h
  calc q * w = (w * q * w⁻¹) * w := by rw [h]
    _ = w * q := by group

theorem kf1418MJ_holds :
    KF1418MJ := by
  refine kf1418MJ_of fun X _ _ hX => ?_
  rcases hX with hM | hJ
  · obtain ⟨φ⟩ := hM
    refine ⟨center_eq_bot_of_mulEquiv φ ComponentClassification.M12Cover.m12_center, ?_,
      kf1418MJModel_of_m12 X ⟨φ⟩⟩
    rw [Nat.card_congr (MulAut.congr φ).toEquiv, Nat.card_congr φ.toEquiv,
      ComponentClassification.M12Cover.card_mulAut, Sporadic.Mathieu.card_M12]
  · obtain ⟨φ⟩ := hJ
    refine ⟨KS14.center_eq_bot_of_j2 Sec4.Sporadic.rank3II_4_15 ⟨φ⟩, ?_,
      kf1418MJModel_of_j2 X ⟨φ⟩⟩
    rw [Nat.card_congr (MulAut.congr φ).toEquiv, Nat.card_congr φ.toEquiv]
    exact ComponentClassification.J2Cover.j2_mulAut_card

end CFSG.RankThree.PartTwo.KFacts.KF1418MJProof
