module

public import CFSG.RankThree.PartTwo.Sec11.Item116EiiCoprime
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec4.Item420
import CFSG.Goldschmidt.Steps.Balance
public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOCor

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (fusionIsSylowIn)
open CFSG.Goldschmidt (oddCoreOf)

namespace Eii

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer_of_kMap_ne_one {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ sec11K L x)
    (hKK₀ : sec11K L x ≤ Subgroup.normalizer (K₀ : Set G)) {z : G} (hz : z ∈ K₀)
    (hzθ : z ∉ inSubgroup (aschbacherSolvableCore 3) L) : sec11K L x ≤ K₀ := by
  set K := sec11K L x with hK
  set F := (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
    (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) with hF
  have hrange : (kMap L x).range = F := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  have hmem : ∀ k, kMap L x k ∈ F := fun k => hrange ▸ ⟨k, rfl⟩
  set ψ : K →* F := (kMap L x).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    rw [← hrange] at hf
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, Subtype.ext hk⟩
  set K₀' := K₀.subgroupOf K with hK₀'
  have hK₀'n : K₀'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀).mpr hKK₀
  have hMn : (K₀'.map ψ).Normal := hK₀'n.map ψ hψs
  have hz' : (⟨z, hK₀ hz⟩ : K) ∈ K₀' := Subgroup.mem_subgroupOf.mpr hz
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (K₀'.map ψ) with h | h
  · exfalso
    rw [hZ] at h
    have h1 : ψ ⟨z, hK₀ hz⟩ ∈ K₀'.map ψ := ⟨_, hz', rfl⟩
    have h2 := h h1
    rw [Subgroup.mem_bot] at h2
    have h3 : kMap L x ⟨z, hK₀ hz⟩ = 1 := congrArg Subtype.val h2
    exact hzθ ((kMap_eq_one_iff _).mp h3)
  ·
    have hkerθ : ∀ k : ψ.ker,
        Subgroup.inclusion (sec11K_le L x) (k : K) ∈ aschbacherSolvableCore 3 L := fun k => by
      have h1 : kMap L x (k : K) = 1 := by
        have := MonoidHom.mem_ker.mp k.2
        exact congrArg Subtype.val this
      change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        (Subgroup.inclusion (sec11K_le L x) (k : K)) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    set f : ψ.ker →* aschbacherSolvableCore 3 L :=
      ((Subgroup.inclusion (sec11K_le L x)).comp ψ.ker.subtype).codRestrict _ hkerθ with hf
    have hfinj : Function.Injective f := fun y w hyw => Subtype.ext (Subtype.ext (by
      have := congrArg (fun v : aschbacherSolvableCore 3 L => ((v : L) : G)) hyw
      exact this))
    have hθs := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
    have hkers : Group.IsSolvable ψ.ker := Group.isSolvable_of_isSolvable_injective hfinj
    have hsurj : Function.Surjective ((QuotientGroup.mk' K₀').comp ψ.ker.subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective K₀' q
      have hk : ψ k ∈ K₀'.map ψ := h ▸ Subgroup.mem_top _
      obtain ⟨k₀, hk₀, hk₀k⟩ := hk
      refine ⟨⟨k₀⁻¹ * k, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hk₀k, inv_mul_cancel]
      · change QuotientGroup.mk' K₀' (k₀⁻¹ * k) = QuotientGroup.mk' K₀' k
        have h1 : QuotientGroup.mk' K₀' k₀ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hk₀
        rw [map_mul, map_inv, h1, inv_one, one_mul]
    have hqs : Group.IsSolvable (K ⧸ K₀') := Group.isSolvable_of_surjective hsurj
    have hKp : Group.IsPerfect K :=
      PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
    have htop := Sec4.eq_top_of_isPerfect_of_isSolvable_quotient K₀' hqs
    intro k hk
    have h1 : (⟨k, hk⟩ : K) ∈ K₀' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1

omit [Finite G] in
theorem le_normalizer_map_conj {A K : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer ((K.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  intro g hg
  have hg' : n⁻¹ * g * n ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnW) g).mp hg
    rwa [inv_inv] at this
  refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
  have hKg := GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hAK hg')
  calc (K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj g).toMonoidHom
      = ((K.map (MulAut.conj (n⁻¹ * g * n)).toMonoidHom)).map (MulAut.conj n).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext y
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          MulAut.conj_apply]
        group
    _ = K.map (MulAut.conj n).toMonoidHom := by rw [hKg]

end Eii

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

namespace Eii

theorem le_normalizer_sec11K (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    A ≤ Subgroup.normalizer (sec11K L a : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hAL := Item116Fusion.le_normalizer_L h hdL hdc
  intro g hg
  refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
  have hga : g * a * g⁻¹ = a := by
    have hga' : g * a = a * g := congrArg Subtype.val (hAe.1.is_comm.comm ⟨g, hg⟩ ⟨a, h.a_mem⟩)
    rw [hga', mul_inv_cancel_right]
  rw [TheoremO.map_conj_sec11K, GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hAL hg),
    hga]

end Eii

theorem commutator_KKn_odd_of_Eii (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {n : G}
    (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hna : n * a * n⁻¹ ∈ Subgroup.zpowers a)
    (hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))))
    (hSA : ⁅S, A⁆ = ⊥) :
    Odd (Nat.card (⁅sec11K L a, (sec11K L a).map (MulAut.conj n).toMonoidHom⁆ : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θa := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hθa
  set K := sec11K L a with hK
  set K' := K.map (MulAut.conj n).toMonoidHom with hK'
  set D := ⁅K, K'⁆ with hD
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have haA := h.a_mem
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hYnL : Y.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, TheoremO.thetaComponentsAt_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna hna1)] at h1
  have hDθ : D ≤ θa :=
    (Subgroup.commutator_mono h.sec11K_le (Subgroup.map_mono h.sec11K_le)).trans
      (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y hYnL
        hYn.symm)
  have hθ3 : ¬ 3 ∣ Nat.card θa := not_three_dvd_card_inSubgroup_theta _
  have hD3 : ¬ 3 ∣ Nat.card D := fun h3 => hθ3 (h3.trans (Subgroup.card_dvd_of_le hDθ))
  have hDs : Group.IsSolvable D := by
    have := isSolvable_inSubgroup_theta (Subgroup.centralizer ({a} : Set G))
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDθ)
      (Subgroup.inclusion_injective hDθ)
  have hAK := Eii.le_normalizer_sec11K h hdL hdc
  have hAK' : A ≤ Subgroup.normalizer (K' : Set G) := Eii.le_normalizer_map_conj hAK hnW
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.RankThreeEvenClassification.Helpers.normalizes_commutator_of_normalizes_both A K K'
      hAK hAK'
  have hAθ : A ≤ Subgroup.normalizer (θa : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a
      haA).trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((Subgroup.commutator_comm A S).trans hSA)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨T, hT, -, hAT⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two hA3 hD3 hAD bot_le IsPGroup.of_bot
    (fun g _ => by rw [Subgroup.mem_normalizer_iff]; intro x; simp)
  have hTA : ⁅T, A⁆ = ⊥ := Eii.commutator_eq_bot_of_le_of_sylow hA3 hθ3 hAθ hS hAS hSA
    (hT.1.trans hDθ) hT.2.1 hAT
  have hDA := Eii.commutator_le_oddCoreOf hA3 hD3 hDs hAD hT hTA
  set O := oddCoreOf D with hO
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := Subgroup.normalizer_commutator_ge_left K K'
  have hK'D : K' ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.normalizer_commutator_ge_right K K'
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := hKD.trans Eii.le_normalizer_oddCoreOf
  have hK'O : K' ≤ Subgroup.normalizer (O : Set G) := hK'D.trans Eii.le_normalizer_oddCoreOf
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← Item116Fusion.closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA haA haB
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hdθ : d ∉ inSubgroup (aschbacherSolvableCore 3) L := fun hd =>
    hd1 (eq_one_of_mem_inSubgroup_theta hd (hexp d hdA))
  set K₀ := sectionCentralizerSubgroup K D O hKD hKO with hK₀
  have hK₀K : K₀ ≤ K := fun k hk => hk.1
  have hdK₀ : d ∈ K₀ := by
    refine ⟨hdK, fun y hy => hDA ?_⟩
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hdA hy
  have hKK₀ : K ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro k hk
    have hkD := hKD hk
    have hkO := hKO hk
    refine Goldschmidt.Balance.mem_normalizer_of_conj_mem (fun z hz => ?_) (fun z hz => ?_)
    · refine ⟨K.mul_mem (K.mul_mem hk hz.1) (K.inv_mem hk), fun y hy => ?_⟩
      have hy' : k⁻¹ * y * k ∈ D := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkD) y).mp hy
        rwa [inv_inv] at this
      have h1 := (Subgroup.mem_normalizer_iff.mp hkO _).mp (hz.2 _ hy')
      rwa [show k * (z * (k⁻¹ * y * k) * z⁻¹ * (k⁻¹ * y * k)⁻¹) * k⁻¹ =
        k * z * k⁻¹ * y * (k * z * k⁻¹)⁻¹ * y⁻¹ by group] at h1
    · refine ⟨K.mul_mem (K.mul_mem (K.inv_mem hk) hz.1) hk, fun y hy => ?_⟩
      have hy' : k * y * k⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hkD y).mp hy
      have hkO' := Subgroup.inv_mem _ hkO
      have h1 := (Subgroup.mem_normalizer_iff.mp hkO' _).mp (hz.2 _ hy')
      rwa [inv_inv, show k⁻¹ * (z * (k * y * k⁻¹) * z⁻¹ * (k * y * k⁻¹)⁻¹) * k =
        k⁻¹ * z * k * y * (k⁻¹ * z * k)⁻¹ * y⁻¹ by group] at h1
  have hKle := Eii.le_of_le_normalizer_of_kMap_ne_one hxN hx3 hQ hZ hK₀K hKK₀ hdK₀ hdθ
  have hDK : ⁅D, K⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro y hy k hk
    have h1 := (hKle hk).2 y hy
    have h2 := O.inv_mem h1
    rwa [show (k * y * k⁻¹ * y⁻¹)⁻¹ = y * k * y⁻¹ * k⁻¹ by group] at h2
  have h2 : ⁅⁅K', K⁆, K⁆ ≤ O := by rw [Subgroup.commutator_comm K' K]; exact hDK
  have h3 := Sec6.three_subgroups_mod hKO hK'O hKO hDK h2
  have hKK : ⁅K, K⁆ = K := Sec6.commutator_self_eq_of_isPerfect
    (PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _)
  rw [hKK] at h3
  exact Eii.odd_card_of_le_oddCoreOf h3

end Certified

end CFSG.RankThree.PartTwo.Sec11
