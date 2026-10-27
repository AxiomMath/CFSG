module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section OTwoThree

variable {G : Type*} [Group G]

theorem oTwoThreeIn_le (L : Subgroup G) : oTwoThreeIn L ≤ L :=
  Subgroup.map_subtype_le _

theorem pCoreOf_le_oTwoThreeIn (L : Subgroup G) : pCoreOf 2 L ≤ oTwoThreeIn L := by
  rw [CFSG.openPCoreOf_eq_map_pCore]
  refine Subgroup.map_mono fun q hq => ?_
  have hq1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  rw [Subgroup.mem_comap, hq1]
  exact Subgroup.one_mem _

theorem normalizer_le_normalizer_oTwoThreeIn (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (oTwoThreeIn L : Set G) := by
  have : ((CFSG.pCore 3 (↥L ⧸ CFSG.pCore 2 ↥L)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk inferInstance
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

end OTwoThree

section Abstract

variable {Z : Type*} [Group Z] [Finite Z]

theorem not_sq_dvd_336 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ^ 2 ∣ 336 := by
  intro h
  have hle : r ^ 2 ≤ 336 := Nat.le_of_dvd (by norm_num) h
  have hr18 : r ≤ 18 := by nlinarith
  interval_cases r <;> revert hr hr2 h <;> decide

theorem odd_card_center_of_normal {Lb : Subgroup Z} [Lb.Normal]
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) :
    Odd (Nat.card (center Lb)) := by
  have hZcn : ((center Lb).map Lb.subtype).Normal := inferInstance
  have hcomm : ∀ a ∈ (center Lb).map Lb.subtype, ∀ b ∈ Lb, a * b = b * a := by
    rintro _ ⟨z, hz, rfl⟩ b hb
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hb⟩)).symm
  let K : Subgroup Z :=
    { carrier := {y | y ∈ (center Lb).map Lb.subtype ∧ y ^ 2 = 1}
      one_mem' := ⟨Subgroup.one_mem _, one_pow 2⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [Commute.mul_pow (hcomm a ha.1 b (Subgroup.map_subtype_le _ hb.1)) 2, ha.2, hb.2,
          one_mul]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemK : ∀ y, y ∈ K ↔ y ∈ (center Lb).map Lb.subtype ∧ y ^ 2 = 1 := fun y => Iff.rfl
  have hKn : K.Normal := ⟨fun y hy g => by
    rw [hmemK] at hy ⊢
    exact ⟨hZcn.conj_mem y hy.1 g, by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩
  have hK2 : IsPGroup 2 K := fun y => ⟨1, Subtype.ext (by simpa using ((hmemK _).mp y.2).2)⟩
  have hKbot := hO2 K hKn hK2
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (center Lb) := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : ((z : Lb) : Z) ^ 2 = 1 := by
    have h1 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h3 := congrArg (fun w : center Lb => ((w : Lb) : Z)) h1
    simpa using h3
  have hzK : ((z : Lb) : Z) ∈ K := (hmemK _).mpr ⟨⟨z, z.2, rfl⟩, hz2⟩
  rw [hKbot, Subgroup.mem_bot] at hzK
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hzK)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem le_map_center_of_isPGroup {Lb Hb : Subgroup Z} (hq : CFSG.IsQuasisimple Lb)
    (hHbL : Hb ≤ Lb) (hHbn : ∀ l ∈ Lb, ∀ h ∈ Hb, l * h * l⁻¹ ∈ Hb) {p : ℕ} [Fact p.Prime]
    (hHbp : IsPGroup p Hb) : Hb ≤ (center Lb).map Lb.subtype := by
  have hnorm : (Hb.subgroupOf Lb).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hHbn g g.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnorm with htop | hle
  · exfalso
    have hLH : Lb ≤ Hb := fun l hl => by
      have h : (⟨l, hl⟩ : Lb) ∈ Hb.subgroupOf Lb := htop ▸ mem_top _
      exact h
    have hLp : IsPGroup p Lb := hHbp.to_le hLH
    have : Group.IsPerfect Lb := hq.1
    have : Nontrivial Lb := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isNilpotent Lb hLp.isNilpotent
  · intro h hh
    exact ⟨⟨h, hHbL hh⟩, hle (by rw [mem_subgroupOf]; exact hh), rfl⟩

theorem eq_bot_of_forall_commutator_mem_center {Lb Tb Cb : Subgroup Z}
    (hq : CFSG.IsQuasisimple Lb) [Lb.Normal] (hTb : IsPGroup 2 Tb) (hsup : Lb ⊔ Tb = ⊤)
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) [hCbn : Cb.Normal]
    (hcomm : ∀ c ∈ Cb, ∀ l ∈ Lb, c * l * c⁻¹ * l⁻¹ ∈ (center Lb).map Lb.subtype)
    (hidx : Cb.index ∣ 336) : Cb = ⊥ := by
  have hperfI : Group.IsPerfect Lb := hq.1
  have hperf : commutator Lb = ⊤ := hperfI.commutator_eq_top
  have hZc : ∀ a ∈ (center Lb).map Lb.subtype, ∀ b ∈ Lb, b * a = a * b := by
    rintro _ ⟨z, hz, rfl⟩ b hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hb⟩)
  have hLC : ⁅Lb, Cb⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator hperfI ?_
    have h1 : ⁅Lb, Cb⁆ ≤ (center Lb).map Lb.subtype := by
      rw [Subgroup.commutator_le]
      intro l hl c hc
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hcomm c hc l hl)
    have h2 : ⁅(center Lb).map Lb.subtype, Lb⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => hZc a ha b hb
    exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono_left h1)
  have hcent : ∀ c ∈ Cb, ∀ l ∈ Lb, c * l = l * c := fun c hc l hl =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLC hl) c hc
  have hle : Cb.subgroupOf Lb ≤ center Lb := by
    intro c hc
    rw [mem_subgroupOf] at hc
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hcent c hc l l.2).symm
  have hodd := odd_card_center_of_normal (Lb := Lb) hO2
  have hidxZ : (center Lb).index ∣ 336 :=
    (index_dvd_of_le hle).trans ((relIndex_dvd_index_of_normal Cb Lb).trans hidx)
  have hZbot : center Lb = ⊥ := by
    refine CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes hperf
      (center Lb) rfl hodd ?_
    intro r _ _ hr2 S
    have hdvd : Nat.card S ∣ 336 := by
      refine (Subgroup.card_subgroup_dvd_card (S : Subgroup (Lb ⧸ center Lb))).trans ?_
      rw [← Subgroup.index_eq_card]
      exact hidxZ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hn1 : n ≤ 1 := by
      by_contra hn1
      have h2 : r ^ 2 ∣ 336 := (pow_dvd_pow r (by omega)).trans (hn ▸ hdvd)
      exact not_sq_dvd_336 (Fact.out) hr2 h2
    interval_cases n
    · rw [pow_zero] at hn
      have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hn).1
      infer_instance
    · exact isCyclic_of_prime_card (by rw [hn, pow_one])
  have hinf : ∀ c ∈ Cb, c ∈ Lb → c = 1 := by
    intro c hc hcL
    have h1 : (⟨c, hcL⟩ : Lb) ∈ center Lb := hle (by rw [mem_subgroupOf]; exact hc)
    rw [hZbot, mem_bot] at h1
    exact congrArg Subtype.val h1
  let g : Tb →* Z ⧸ Lb := (QuotientGroup.mk' Lb).comp Tb.subtype
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Lb q
    have hz : z ∈ Lb ⊔ Tb := hsup ▸ mem_top z
    obtain ⟨l, hl, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hz
    refine ⟨⟨t, ht⟩, ?_⟩
    have hl1 : (QuotientGroup.mk' Lb) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    change (QuotientGroup.mk' Lb) t = (QuotientGroup.mk' Lb) (l * t)
    rw [map_mul, hl1, one_mul]
  have hQ2 : IsPGroup 2 (Z ⧸ Lb) := hTb.of_surjective g hgs
  let f : Cb →* Z ⧸ Lb := (QuotientGroup.mk' Lb).comp Cb.subtype
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcL : (c : Z) ∈ Lb := (QuotientGroup.eq_one_iff (c : Z)).mp hc
    exact Subgroup.mem_bot.mpr (Subtype.ext (hinf c c.2 hcL))
  exact hO2 Cb hCbn (hQ2.of_injective f hfi)

end Abstract

section Kernel

variable {G : Type} [Group G] [Finite G]

theorem mem_centSection_iff_mem_pCoreOf {N L T : Subgroup G}
    (hLN : L ≤ N) (hNL : N ≤ normalizer (L : Set G)) (hTN : T ≤ N) (hT2 : IsPGroup 2 T)
    (hsupN : T ⊔ L = N)
    {Z : Type} [Group Z] (ψ : ↥N →* Z) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (hq : CFSG.IsQuasisimple ((L.subgroupOf N).map ψ))
    {A : Type} [Group A] (π : ↥N →* A) (hπs : Function.Surjective π)
    (hπk : ∀ x : ↥N, π x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L))
    (hA : Nat.card A ∣ 336) (x : ↥N) :
    (x : G) ∈ S17.centSection N L (oTwoThreeIn L) ↔ (x : G) ∈ pCoreOf 2 N := by
  constructor
  · intro hx
    have : Finite Z := Finite.of_surjective ψ hψs
    have hLn : (L.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
    have hLbn : ((L.subgroupOf N).map ψ).Normal := hLn.map ψ hψs
    have hCbn : (π.ker.map ψ).Normal := (MonoidHom.normal_ker π).map ψ hψs
    have hTb : IsPGroup 2 ((T.subgroupOf N).map ψ) :=
      (hT2.of_equiv (subgroupOfEquivOfLe hTN).symm).map ψ
    have hsup : (L.subgroupOf N).map ψ ⊔ (T.subgroupOf N).map ψ = ⊤ := by
      have htop : L.subgroupOf N ⊔ T.subgroupOf N = ⊤ := by
        apply Subgroup.map_injective N.subtype_injective
        rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
          Subgroup.map_subgroupOf_eq_of_le hLN, Subgroup.map_subgroupOf_eq_of_le hTN, sup_comm,
          hsupN]
      rw [← Subgroup.map_sup, htop, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective ψ hψs]
    have hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥ := by
      intro K hK hK2
      have hker2 : IsPGroup 2 ψ.ker := by
        have hk : ψ.ker = CFSG.pCore 2 ↥N := by
          ext y
          rw [MonoidHom.mem_ker, hψk, CFSG.mem_openPCoreOf_iff]
        rw [hk]
        exact CFSG.pCore_isPGroup
      have hP2 : IsPGroup 2 (K.comap ψ) := hK2.comap_of_ker_isPGroup ψ hker2
      have hPle : K.comap ψ ≤ CFSG.pCore 2 ↥N := le_sSup ⟨hK.comap ψ, hP2⟩
      rw [eq_bot_iff]
      intro k hk
      obtain ⟨n, rfl⟩ := hψs k
      exact (hψk n).mpr ((CFSG.mem_openPCoreOf_iff n).mpr (hPle hk))
    have hO2L : pCoreOf 2 L ≤ pCoreOf 2 N :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hLN hNL
    have hHb3 : IsPGroup 3 (((oTwoThreeIn L).subgroupOf N).map ψ) := by
      rintro ⟨_, y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      have hw' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) w ∈ CFSG.pCore 3 (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Subgroup.mem_comap.mp hw
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) ⟨_, hw'⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (w ^ 3 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      have hwL : ((w ^ 3 ^ k : ↥L) : G) ∈ pCoreOf 2 L :=
        (CFSG.mem_openPCoreOf_iff _).mpr ((QuotientGroup.eq_one_iff _).mp hk')
      have hyN : ((y ^ 3 ^ k : ↥N) : G) ∈ pCoreOf 2 N := by
        have he : ((y ^ 3 ^ k : ↥N) : G) = ((w ^ 3 ^ k : ↥L) : G) := by
          simp only [Subgroup.coe_pow, Subgroup.coe_subtype] at hwy ⊢
          rw [hwy]
        rw [he]
        exact hO2L hwL
      have h1 := (hψk _).mpr hyN
      rw [map_pow] at h1
      simpa using h1
    have hHbL : ((oTwoThreeIn L).subgroupOf N).map ψ ≤ (L.subgroupOf N).map ψ :=
      Subgroup.map_mono fun y hy => by
        rw [mem_subgroupOf] at hy ⊢
        exact oTwoThreeIn_le L hy
    have hHbn : ∀ l ∈ (L.subgroupOf N).map ψ, ∀ h ∈ ((oTwoThreeIn L).subgroupOf N).map ψ,
        l * h * l⁻¹ ∈ ((oTwoThreeIn L).subgroupOf N).map ψ := by
      rintro _ ⟨l, hl, rfl⟩ _ ⟨h, hh, rfl⟩
      refine ⟨l * h * l⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hl hh ⊢
      have hlN : (l : G) ∈ normalizer (oTwoThreeIn L : Set G) :=
        normalizer_le_normalizer_oTwoThreeIn L (Subgroup.le_normalizer hl)
      simpa using (mem_normalizer_iff.mp hlN h).mp hh
    have hHbZ := le_map_center_of_isPGroup hq hHbL hHbn hHb3
    have hcomm : ∀ c ∈ π.ker.map ψ, ∀ l ∈ (L.subgroupOf N).map ψ,
        c * l * c⁻¹ * l⁻¹ ∈ (center ((L.subgroupOf N).map ψ)).map
          ((L.subgroupOf N).map ψ).subtype := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨l, hl, rfl⟩
      apply hHbZ
      refine ⟨c * l * c⁻¹ * l⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hl ⊢
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hc
      obtain ⟨-, -, -, hcent⟩ := (hπk c).mp hc
      simpa using hcent (l : G) hl
    have hidx : (π.ker.map ψ).index ∣ 336 := by
      refine (Subgroup.index_map_dvd _ hψs).trans ?_
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπs, Subgroup.card_top]
      exact hA
    have hCb := eq_bot_of_forall_commutator_mem_center hq hTb hsup hO2 hcomm hidx
    have hψx : ψ x ∈ π.ker.map ψ := Subgroup.mem_map_of_mem ψ ((hπk x).mpr hx)
    rw [hCb, Subgroup.mem_bot] at hψx
    exact (hψk x).mp hψx
  · intro hx
    have hxN : (x : G) ∈ N := x.2
    have hxL : (x : G) ∈ normalizer (L : Set G) := hNL hxN
    refine ⟨hxN, hxL, normalizer_le_normalizer_oTwoThreeIn L hxL, fun a ha => ?_⟩
    have h1 : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ L :=
      L.mul_mem ((mem_normalizer_iff.mp hxL a).mp ha) (L.inv_mem ha)
    have hNP : N ≤ normalizer (pCoreOf 2 N : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
    have h2 : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ pCoreOf 2 N := by
      have h3 : a * (x : G)⁻¹ * a⁻¹ ∈ pCoreOf 2 N :=
        (mem_normalizer_iff.mp (hNP (hLN ha)) _).mp (inv_mem hx)
      simpa only [mul_assoc] using (pCoreOf 2 N).mul_mem hx h3
    exact pCoreOf_le_oTwoThreeIn L (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLN ⟨h1, h2⟩)

end Kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914
