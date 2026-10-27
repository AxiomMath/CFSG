module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofAlt
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
import CFSG.RankThree.PartTwo.KFacts.KS18OuterCore
import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.RankThree.PartTwo.Sec15.Item155Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153B

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

variable {G : Type} [Group G] [Finite G]

section Action

abbrev Ybar (Y : Subgroup G) : Type := ↥Y ⧸ CFSG.pCore 2 ↥Y

@[expose] noncomputable def conjAutEquiv : ↥A6Models.autA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective (MonoidHom.mk' DoubleA3.conjAut fun a b => MulEquiv.ext fun x =>
    Subtype.ext (by
      show ((a : P10) * (b : P10)) * (x : P10) * ((a : P10) * (b : P10))⁻¹ =
        (a : P10) * ((b : P10) * (x : P10) * (b : P10)⁻¹) * (a : P10)⁻¹
      group))
    ⟨DoubleA3.conjAut_injective, DoubleA3.conjAut_surjective⟩

theorem conjAutEquiv_apply (a : ↥A6Models.autA6) (x : ↥A6Models.psl29) :
    ((conjAutEquiv a x : ↥A6Models.psl29) : P10) = (a : P10) * (x : P10) * (a : P10)⁻¹ := rfl

omit [Finite G] in
@[expose] noncomputable def autAct {Y : Subgroup G}
    (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29) :
    ↥(Subgroup.normalizer (Y : Set G)) →* ↥A6Models.autA6 :=
  conjAutEquiv.symm.toMonoidHom.comp ((MulAut.congr ψ6).toMonoidHom.comp
    ((KFacts.centerDescend (Ybar Y)).comp (barAct Y)))

variable {Y : Subgroup G} (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)

omit [Finite G] in
theorem autAct_spec (g : ↥(Subgroup.normalizer (Y : Set G))) (q : Ybar Y) :
    ((ψ6 ((barAct Y g q : Ybar Y) : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) :
        P10) = (autAct ψ6 g : P10) * (ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) *
      (autAct ψ6 g : P10)⁻¹ := by
  have h : conjAutEquiv (autAct ψ6 g) = MulAut.congr ψ6
      (KFacts.centerDescend (Ybar Y) (barAct Y g)) := by
    rw [autAct, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    rfl
  have h2 := congrArg (fun f : MulAut ↥A6Models.psl29 =>
    ((f (ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y))) : ↥A6Models.psl29) : P10)) h
  simp only [conjAutEquiv_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, KFacts.centerDescend_mk] at h2
  exact h2.symm

omit [Finite G] in
theorem autAct_of_inner {g : ↥(Subgroup.normalizer (Y : Set G))} {q₀ : Ybar Y}
    (hg : barAct Y g = MulAut.conj q₀) :
    (autAct ψ6 g : P10) = (ψ6 (q₀ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) := by
  set a : ↥A6Models.autA6 := ⟨_, A6Facts.psl29_le_autA6 (ψ6 (q₀ :
    Ybar Y ⧸ Subgroup.center (Ybar Y))).2⟩ with ha
  have h : conjAutEquiv (autAct ψ6 g) = conjAutEquiv a := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨q, rfl⟩ := ψ6.surjective x
    obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
    rw [conjAutEquiv_apply, conjAutEquiv_apply, ← autAct_spec, hg, MulAut.conj_apply]
    simp only [ha, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_inv]
  rw [conjAutEquiv.injective h]

omit [Finite G] in
theorem autAct_mem (y : G) (hy : y ∈ Y) :
    (autAct ψ6 ⟨y, Subgroup.le_normalizer hy⟩ : P10) =
      (ψ6 ((QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) :=
  autAct_of_inner ψ6 (barAct_mem Y y hy)

omit [Finite G] in
theorem barAct_eq_one_of_autAct (hperf : commutator (Ybar Y) = ⊤)
    {g : ↥(Subgroup.normalizer (Y : Set G))} (hg : autAct ψ6 g = 1) : barAct Y g = 1 := by
  have hfix : ∀ q : Ybar Y, barAct Y g q * q⁻¹ ∈ Subgroup.center (Ybar Y) := by
    intro q
    have h := autAct_spec ψ6 g q
    rw [hg, OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
    have h' := ψ6.injective (Subtype.ext h)
    have h'' := QuotientGroup.eq_iff_div_mem.mp h'
    rwa [div_eq_mul_inv] at h''
  refine MulEquiv.ext fun q => ?_
  exact KFacts.KS18.eq_of_mul_inv_mem_center hperf _ hfix q

omit [Finite G] in
theorem barAct_mk (g : ↥(Subgroup.normalizer (Y : Set G))) (y : G) (hy : y ∈ Y) :
    barAct Y g (QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) =
      QuotientGroup.mk ⟨(g : G) * y * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 y).mp hy⟩ := by
  rw [barAct, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
  congr 1

omit [Finite G] in
theorem mk_eq_mk_iff {u v : G} (hu : u ∈ Y) (hv : v ∈ Y) :
    (QuotientGroup.mk ⟨u, hu⟩ : Ybar Y) = QuotientGroup.mk ⟨v, hv⟩ ↔
      u * v⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  rw [QuotientGroup.eq_iff_div_mem, Push153.mem_pCore_iff_mem_pCoreOf]
  simp [div_eq_mul_inv]

omit [Finite G] in
theorem mk_eq_one_iff {y : G} (hy : y ∈ Y) :
    (QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) = 1 ↔ y ∈ CFSG.Open.pCoreOf 2 Y := by
  rw [QuotientGroup.eq_one_iff, Push153.mem_pCore_iff_mem_pCoreOf]

omit [Finite G] in
theorem mulAut_mem_center {X : Type*} [Group X] (σ : MulAut X) {z : X}
    (hz : z ∈ Subgroup.center X) : σ z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  have h := hz (σ.symm y)
  have h2 := congrArg σ h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

end Action

section Cover

variable {Y : Subgroup G}

omit [Finite G] in
theorem exists_inner_of_pow_three (hperf : commutator (Ybar Y) = ⊤)
    (e6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* alternatingGroup (Fin 6))
    {g : ↥(Subgroup.normalizer (Y : Set G))} (hg : g ^ 3 = 1) :
    ∃ q₀ : Ybar Y, barAct Y g = MulAut.conj q₀ :=
  KFacts.exists_conj_of_quotient_center hperf e6 (fun τ hτ => by
    obtain ⟨y, hy⟩ := KFacts.mem_range_conj_alternatingGroup_six hτ
    exact ⟨y, hy.symm⟩) (barAct Y g) ⟨1, by rw [pow_one, ← map_pow, hg, map_one]⟩

omit [Finite G] in
theorem pow_three_of_mem_center (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) {z : Ybar Y}
    (hz : z ∈ Subgroup.center (Ybar Y)) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center (Ybar Y)))
  rw [hZ] at h
  exact congrArg Subtype.val h

omit [Finite G] in
theorem pow_three_of_image (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3)
    (e6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* alternatingGroup (Fin 6)) {q : Ybar Y}
    (hq : ((q : Ybar Y ⧸ Subgroup.center (Ybar Y))) ^ 3 = 1) : q ^ 3 = 1 := by
  have hq3 : q ^ 3 ∈ Subgroup.center (Ybar Y) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hq
  refine KFacts.pow_three_eq_one_of_center_card_three hZ e6
    (fun s hs => KFacts.alternatingGroup_six_threeElements s hs) q ⟨2, ?_⟩
  rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
  exact pow_three_of_mem_center hZ hq3

theorem zpowers_eq_center (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) {z₀ : Ybar Y}
    (hz₀ : z₀ ∈ Subgroup.center (Ybar Y)) (hz₁ : z₀ ≠ 1) :
    Subgroup.zpowers z₀ = Subgroup.center (Ybar Y) := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz₀) ?_
  rw [hZ, Nat.card_zpowers]
  have hd : orderOf z₀ ∣ 3 := orderOf_dvd_of_pow_eq_one (pow_three_of_mem_center hZ hz₀)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hz₁
  · exact h.ge

theorem exists_mem_inf_center {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hperf : commutator (Ybar Y) = ⊤)
    (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3)
    (e6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* alternatingGroup (Fin 6)) :
    ∃ (d : G) (hd : d ∈ A ⊓ Y), (QuotientGroup.mk ⟨d, hd.2⟩ : Ybar Y) ∈
      Subgroup.center (Ybar Y) ∧ (QuotientGroup.mk ⟨d, hd.2⟩ : Ybar Y) ≠ 1 := by
  obtain ⟨⟨z₀, hz₀⟩, hz₁⟩ : ∃ z : Subgroup.center (Ybar Y), z ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (Subgroup.center (Ybar Y)) := ⟨fun a b => (h a).trans (h b).symm⟩
    rw [Nat.card_of_subsingleton (1 : Subgroup.center (Ybar Y))] at hZ
    omega
  have hz₁' : z₀ ≠ 1 := fun h => hz₁ (Subtype.ext h)
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective z₀
  have hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro a ha
    obtain ⟨q₀, hq₀⟩ := exists_inner_of_pow_three hperf e6 (g := ⟨a, hAY ha⟩)
      (Subtype.ext (by simpa using hAF.1.2 a ha))
    have h1 := barAct_mk ⟨a, hAY ha⟩ y hy
    rw [hq₀, MulAut.conj_apply, Subgroup.mem_center_iff.mp hz₀ q₀, mul_inv_cancel_right] at h1
    have h2 := (mk_eq_mk_iff _ hy).mp h1.symm
    simpa [mul_assoc] using h2
  have hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y := by
    have h := pow_three_of_mem_center hZ hz₀
    rw [← QuotientGroup.mk_pow] at h
    have : (⟨y, hy⟩ : ↥Y) ^ 3 = ⟨y ^ 3, Y.pow_mem hy 3⟩ := Subtype.ext (by simp)
    rw [this, mk_eq_one_iff] at h
    exact h
  obtain ⟨d, hd, hdV⟩ := exists_mem_inf_of_fixed hAF hAY hy hfix hy3
  refine ⟨d, hd, ?_⟩
  have he : (QuotientGroup.mk ⟨d, hd.2⟩ : Ybar Y) = QuotientGroup.mk ⟨y, hy⟩ :=
    (mk_eq_mk_iff hd.2 hy).mpr hdV
  rw [he]
  exact ⟨hz₀, hz₁'⟩

theorem fixes_center_of_mem_sup {A S : Subgroup G} (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) {d : G} (hd : d ∈ A ⊓ Y)
    (hdZ : (QuotientGroup.mk ⟨d, hd.2⟩ : Ybar Y) ∈ Subgroup.center (Ybar Y))
    (hd1 : (QuotientGroup.mk ⟨d, hd.2⟩ : Ybar Y) ≠ 1) {h : G} (hh : h ∈ Y ⊔ S)
    {z : Ybar Y} (hz : z ∈ Subgroup.center (Ybar Y)) :
    barAct Y ⟨h, sup_le Subgroup.le_normalizer hSY hh⟩ z = z := by
  set z₀ : Ybar Y := QuotientGroup.mk ⟨d, hd.2⟩ with hz₀
  let T : Subgroup ↥(Subgroup.normalizer (Y : Set G)) :=
    { carrier := {g | ∀ z ∈ Subgroup.center (Ybar Y), barAct Y g z = z}
      one_mem' := fun z _ => by rw [map_one, MulAut.one_apply]
      mul_mem' := fun {a b} ha hb z hz => by
        rw [map_mul, MulAut.mul_apply, hb z hz, ha z hz]
      inv_mem' := fun {a} ha z hz => by
        have h1 := ha (barAct Y a⁻¹ z) (mulAut_mem_center _ hz)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
        exact h1.symm }
  have hYT : Y.subgroupOf (Subgroup.normalizer (Y : Set G)) ≤ T := by
    intro g hg z hz
    have hgY : (g : G) ∈ Y := Subgroup.mem_subgroupOf.mp hg
    have : g = ⟨g, Subgroup.le_normalizer hgY⟩ := rfl
    rw [this, barAct_mem Y _ hgY, MulAut.conj_apply, Subgroup.mem_center_iff.mp hz,
      mul_inv_cancel_right]
  have hST : S.subgroupOf (Subgroup.normalizer (Y : Set G)) ≤ T := by
    intro g hg
    have hgS : (g : G) ∈ S := Subgroup.mem_subgroupOf.mp hg
    have hfix₀ : barAct Y g z₀ = z₀ := by
      have hdA : d ∈ Subgroup.normalizer (S : Set G) := hAS hd.1
      have hgdg : (g : G) * d * (g : G)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp g.2 d).mp hd.2
      set w := (g : G) * d * (g : G)⁻¹ * d⁻¹ with hw
      have hwS : w ∈ S := by
        have h1 : d * (g : G)⁻¹ * d⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp hdA _).mp (S.inv_mem hgS)
        have e : w = (g : G) * (d * (g : G)⁻¹ * d⁻¹) := by rw [hw]; group
        rw [e]
        exact S.mul_mem hgS h1
      have hwY : w ∈ Y := Y.mul_mem hgdg (Y.inv_mem hd.2)
      have hmk : (QuotientGroup.mk ⟨w, hwY⟩ : Ybar Y) = barAct Y g z₀ * z₀⁻¹ := by
        rw [hz₀, barAct_mk g d hd.2, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      have hmkZ : (QuotientGroup.mk ⟨w, hwY⟩ : Ybar Y) ∈ Subgroup.center (Ybar Y) := by
        rw [hmk]
        exact Subgroup.mul_mem _ (mulAut_mem_center _ hdZ) (Subgroup.inv_mem _ hdZ)
      obtain ⟨k, hk⟩ := hS2 ⟨w, hwS⟩
      have hk' : (QuotientGroup.mk ⟨w, hwY⟩ : Ybar Y) ^ 2 ^ k = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨w, hwY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by
          simpa using congrArg Subtype.val hk)
        rw [this, QuotientGroup.mk_one]
      have h3 := pow_three_of_mem_center hZ hmkZ
      have h1 : (QuotientGroup.mk ⟨w, hwY⟩ : Ybar Y) = 1 := by
        have ho1 := orderOf_dvd_of_pow_eq_one hk'
        have ho2 := orderOf_dvd_of_pow_eq_one h3
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (Nat.Coprime.pow_left k (by norm_num)) ho1 ho2)
      rw [hmk, mul_inv_eq_one] at h1
      exact h1
    intro z hz
    rw [← zpowers_eq_center hZ hdZ hd1] at hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hfix₀]
  have hle : (Y ⊔ S).subgroupOf (Subgroup.normalizer (Y : Set G)) ≤ T := by
    rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer hSY]
    exact sup_le hYT hST
  exact hle (Subgroup.mem_subgroupOf.mpr hh) z hz

theorem mem_pCoreOf_of_barAct_eq_one {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3)
    {d : G} (hdY : d ∈ Y)
    (hdZ : (QuotientGroup.mk ⟨d, hdY⟩ : Ybar Y) ∈ Subgroup.center (Ybar Y))
    (hd1 : (QuotientGroup.mk ⟨d, hdY⟩ : Ybar Y) ≠ 1) {k : G} (hk : k ∈ Y ⊔ S)
    (hk1 : barAct Y ⟨k, sup_le Subgroup.le_normalizer hSY hk⟩ = 1) {m : ℕ}
    (hkm : k ^ 2 ^ m = 1) : k ∈ CFSG.Open.pCoreOf 2 (Y ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Y ⊔ S with hHdef
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  set V := CFSG.Open.pCoreOf 2 Y with hVdef
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hVY : V ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  set f := (barAct Y).comp (Subgroup.inclusion hHN) with hf
  set K : Subgroup G := f.ker.map H.subtype with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hmemK : ∀ (g : G) (hg : g ∈ H), barAct Y ⟨g, hHN hg⟩ = 1 → g ∈ K :=
    fun g hg h1 => ⟨⟨g, hg⟩, show f ⟨g, hg⟩ = 1 from h1, rfl⟩
  have hKmem : ∀ g ∈ K, ∃ hg : g ∈ H, barAct Y ⟨g, hHN hg⟩ = 1 := by
    rintro _ ⟨⟨g, hg⟩, h1, rfl⟩
    exact ⟨hg, h1⟩
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    Sec15.le_normalizer_map_of_normal155 (MonoidHom.normal_ker f)
  have hYcen : ∀ (y : G) (hy : y ∈ Y), barAct Y ⟨y, Subgroup.le_normalizer hy⟩ = 1 →
      (QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) ∈ Subgroup.center (Ybar Y) := by
    intro y hy h1
    rw [barAct_mem Y y hy] at h1
    rw [Subgroup.mem_center_iff]
    intro r
    have h2 := congrArg (fun σ : MulAut (Ybar Y) => σ r) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc r * (QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) =
        (QuotientGroup.mk ⟨y, hy⟩ * r * (QuotientGroup.mk ⟨y, hy⟩)⁻¹) *
          QuotientGroup.mk ⟨y, hy⟩ := by rw [h2]
      _ = QuotientGroup.mk ⟨y, hy⟩ * r := by group
  have hVK : V ≤ K := by
    intro v hv
    refine hmemK v (Subgroup.mem_sup_left (hVY hv)) ?_
    have : (⟨v, hHN (Subgroup.mem_sup_left (hVY hv))⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
        ⟨v, Subgroup.le_normalizer (hVY hv)⟩ := rfl
    rw [this, barAct_mem Y v (hVY hv), (mk_eq_one_iff (hVY hv)).mpr hv, map_one]
  have hdK : d ∈ K := by
    refine hmemK d (Subgroup.mem_sup_left hdY) ?_
    have : (⟨d, hHN (Subgroup.mem_sup_left hdY)⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
        ⟨d, Subgroup.le_normalizer hdY⟩ := rfl
    rw [this, barAct_mem Y d hdY]
    refine MulEquiv.ext fun q => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hdZ q,
      mul_inv_cancel_right]
  set V' := V.subgroupOf K with hV'
  have hV'n : V'.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mpr ?_
    exact (hKH.trans hHN).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  set dK : ↥K := ⟨d, hdK⟩ with hdKdef
  set π := QuotientGroup.mk' V' with hπ
  have hπeq : ∀ a b : ↥K, π a = π b ↔ (a : G) * (b : G)⁻¹ ∈ V := by
    intro a b
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      Subgroup.mem_subgroupOf]
    simp [div_eq_mul_inv]
  have hdc : π dK ∈ Subgroup.center (↥K ⧸ V') := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V' x
    obtain ⟨haH, ha1⟩ := hKmem a a.2
    have h1 := barAct_mk ⟨(a : G), hHN haH⟩ d hdY
    rw [ha1, MulAut.one_apply] at h1
    have h2 := (mk_eq_mk_iff _ hdY).mp h1.symm
    rw [← map_mul, ← map_mul, hπeq]
    have e : (a : G) * d * ((d : G) * a)⁻¹ = (a : G) * d * (a : G)⁻¹ * d⁻¹ := by group
    show ((a * dK : ↥K) : G) * ((dK * a : ↥K) : G)⁻¹ ∈ V
    simp only [Subgroup.coe_mul, hdKdef]
    rw [e]
    exact h2
  set Db : Subgroup (↥K ⧸ V') := Subgroup.zpowers (π dK) with hDb
  have hDbc : Db ≤ Subgroup.center (↥K ⧸ V') := Subgroup.zpowers_le.mpr hdc
  have hDbn : Db.Normal := Subgroup.normal_of_le_center hDbc
  have h2 : IsPGroup 2 ((↥K ⧸ V') ⧸ Db) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Db x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V' y
    obtain ⟨j, hj⟩ := Push153.exists_pow_two_mem_of_sup hS2 hSY (hKH a.2)
    refine ⟨j, ?_⟩
    have haK : ((a ^ 2 ^ j : ↥K) : G) ∈ Y := by simpa using hj
    obtain ⟨haH, ha1⟩ := hKmem _ (a ^ 2 ^ j).2
    have hcen := hYcen _ haK (by
      have : (⟨((a ^ 2 ^ j : ↥K) : G), Subgroup.le_normalizer haK⟩ :
        ↥(Subgroup.normalizer (Y : Set G))) = ⟨_, hHN haH⟩ := rfl
      rw [this]; exact ha1)
    rw [← zpowers_eq_center hZ hdZ hd1] at hcen
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcen
    have hdn : (QuotientGroup.mk ⟨d, hdY⟩ : Ybar Y) ^ n =
        QuotientGroup.mk ⟨d ^ n, Y.zpow_mem hdY n⟩ := by
      rw [← QuotientGroup.mk_zpow]
      rfl
    rw [hdn] at hn
    have hV := (mk_eq_mk_iff _ _).mp hn
    have hpi : π (a ^ 2 ^ j) = π (dK ^ n) := by
      rw [hπeq]
      have h' := V.inv_mem hV
      have e : ((a ^ 2 ^ j : ↥K) : G) * ((dK ^ n : ↥K) : G)⁻¹ =
          (d ^ n * ((a ^ 2 ^ j : ↥K) : G)⁻¹)⁻¹ := by
        rw [hdKdef, Subgroup.coe_zpow]
        group
      rw [e]
      exact h'
    show (QuotientGroup.mk' Db) (π a) ^ 2 ^ j = 1
    rw [← map_pow, ← map_pow, hpi, map_zpow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.zpow_mem_zpowers _ n
  have : Group.IsNilpotent ((↥K ⧸ V') ⧸ Db) := h2.isNilpotent
  have hnil : Group.IsNilpotent (↥K ⧸ V') :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Db)
      (by rw [QuotientGroup.ker_mk']; exact hDbc)
  obtain ⟨P2⟩ : Nonempty (Sylow 2 (↥K ⧸ V')) := inferInstance
  have hP2n : (P2 : Subgroup (↥K ⧸ V')).Normal := inferInstance
  have : Finite (Sylow 2 (↥K ⧸ V')) := Sylow.finite_of_finiteIndex P2
  have huniq : Unique (Sylow 2 (↥K ⧸ V')) := Sylow.unique_of_normal P2 hP2n
  set Q : Subgroup G := ((P2 : Subgroup (↥K ⧸ V')).comap π).map K.subtype with hQ
  obtain ⟨hkH, hk1'⟩ : ∃ hkH : k ∈ H, barAct Y ⟨k, hHN hkH⟩ = 1 := ⟨hk, hk1⟩
  have hkK : k ∈ K := hmemK k hkH hk1'
  have hkQ : k ∈ Q := by
    refine ⟨⟨k, hkK⟩, ?_, rfl⟩
    have hg : (π ⟨k, hkK⟩) ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨k, hkK⟩ : ↥K) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hkm)
      rw [this, map_one]
    have hz2 : IsPGroup 2 (Subgroup.zpowers (π ⟨k, hkK⟩)) := by
      rintro ⟨x, hx⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨m, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
    obtain ⟨R, hR⟩ := hz2.exists_le_sylow
    have hRP : R = P2 := Subsingleton.elim _ _
    rw [hRP] at hR
    exact hR (Subgroup.mem_zpowers _)
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨_, a, ha, rfl⟩
    obtain ⟨i, hi⟩ := P2.isPGroup' ⟨π a, ha⟩
    have hi' : π (a ^ 2 ^ i) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hi
    have hV : ((a ^ 2 ^ i : ↥K) : G) ∈ V := by
      have := (hπeq (a ^ 2 ^ i) 1).mp (by rw [hi', map_one])
      simpa using this
    obtain ⟨b, hb⟩ := hV2 ⟨_, hV⟩
    refine ⟨i + b, Subtype.ext ?_⟩
    have hb' : ((a : G) ^ 2 ^ i) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_subtype, Subgroup.coe_one, pow_add, pow_mul]
    exact hb'
  have hQK : Q ≤ K := Subgroup.map_subtype_le _
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    Sec15.le_normalizer_map_of_normal155 (hP2n.comap π)
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQK hKQ hQ2
  have hOO : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact hOO (hQO hkQ)

omit [Finite G] in
theorem commutator_mul_center {X : Type*} [Group X] {z₁ z₂ : X} (h1 : z₁ ∈ Subgroup.center X)
    (h2 : z₂ ∈ Subgroup.center X) (a b : X) :
    (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have c1 := Subgroup.mem_center_iff.mp h1
  have c2 := Subgroup.mem_center_iff.mp h2
  calc (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹
      = z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = (a * z₂ * b * a⁻¹) * z₁ * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by rw [← c1 (a * z₂ * b * a⁻¹)]
    _ = a * z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = z₂ * a * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [c2 a]
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z₂ * z₂⁻¹ := by rw [← c2 (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem exists_mem_center_ne_one (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) :
    ∃ z ∈ Subgroup.center (Ybar Y), z ≠ 1 := by
  by_contra h
  push Not at h
  have : Subsingleton (Subgroup.center (Ybar Y)) :=
    ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  rw [Nat.card_of_subsingleton (1 : Subgroup.center (Ybar Y))] at hZ
  omega

theorem not_commute_of_lifts (hperf : commutator (Ybar Y) = ⊤)
    (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) (hcard : Nat.card (Ybar Y) = 1080)
    (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29) {q₁ q₂ : Ybar Y}
    (hq₁ : q₁ ^ 3 = 1) (hq₂ : q₂ ^ 3 = 1)
    (hx1 : ((ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) ≠ 1)
    (hcomm : ((ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) *
        (ψ6 (q₂ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) =
      (ψ6 (q₂ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) *
        (ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10))
    (hn : ((ψ6 (q₂ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) ∉
      Subgroup.zpowers ((ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) :
        P10)) :
    q₁ * q₂ ≠ q₂ * q₁ := by
  intro hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Zc := Subgroup.center (Ybar Y) with hZc
  set x₁ : P10 := ((ψ6 (q₁ : Ybar Y ⧸ Zc) : ↥A6Models.psl29) : P10) with hx₁
  set x₂ : P10 := ((ψ6 (q₂ : Ybar Y ⧸ Zc) : ↥A6Models.psl29) : P10) with hx₂
  set k : Set (Ybar Y) := {q₁, q₂} ∪ (Zc : Set (Ybar Y)) with hk
  have hkc : k.Pairwise Commute := by
    intro a ha b hb _
    have hcen : ∀ {u v : Ybar Y}, v ∈ Zc → Commute u v := fun {u v} hv =>
      (Subgroup.mem_center_iff.mp hv u)
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Commute.refl _
        · exact hq
        · exact hq.symm
        · exact Commute.refl _
      · exact hcen hb
    · exact (hcen ha).symm
  set P := Subgroup.closure k with hP
  have hPc : IsMulCommutative P := Subgroup.isMulCommutative_closure hkc
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with (rfl | rfl) | hx
      · exact hq₁
      · exact hq₂
      · exact pow_three_of_mem_center hZ hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have := hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hP3g : IsPGroup 3 P := fun p => ⟨1, Subtype.ext (by simpa using hP3 p p.2)⟩
  set f : ↥P →* ↥A6Models.psl29 :=
    ψ6.toMonoidHom.comp ((QuotientGroup.mk' Zc).comp P.subtype) with hf
  have hZP : Zc ≤ P := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hker : Zc.subgroupOf P ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp hz)]
    simp
  have hkerc : 3 ≤ Nat.card f.ker := by
    have h := Subgroup.card_le_of_le hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ] at h
  have hq₁P : q₁ ∈ P := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hq₂P : q₂ ∈ P := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hrange : Subgroup.closure ({x₁, x₂} : Set P10) ≤ f.range.map A6Models.psl29.subtype := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨f ⟨q₁, hq₁P⟩, ⟨⟨q₁, hq₁P⟩, rfl⟩, rfl⟩
    · exact ⟨f ⟨q₂, hq₂P⟩, ⟨⟨q₂, hq₂P⟩, rfl⟩, rfl⟩
  have hx₁3 : x₁ ^ 3 = 1 := by
    rw [hx₁, ← Subgroup.coe_pow, ← map_pow, ← QuotientGroup.mk_pow, hq₁]
    simp
  have hx₂3 : x₂ ^ 3 = 1 := by
    rw [hx₂, ← Subgroup.coe_pow, ← map_pow, ← QuotientGroup.mk_pow, hq₂]
    simp
  have h9 := A6.card_closure_pair (ψ6 (q₁ : Ybar Y ⧸ Zc)).2 hx₁3 hx1
    (ψ6 (q₂ : Ybar Y ⧸ Zc)).2 hx₂3 hcomm.symm hn
  have hrangec : 9 ≤ Nat.card f.range := by
    have h := Subgroup.card_le_of_le hrange
    rwa [h9, Subgroup.card_map_of_injective Subtype.val_injective] at h
  have hPcard : 27 ≤ Nat.card P := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    rw [h1]
    nlinarith
  obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp hP3g
  have hdvd : 3 ^ n ∣ 1080 := by
    rw [← hn', ← hcard]
    exact Subgroup.card_subgroup_dvd_card P
  have hn3 : n = 3 := by
    have h27 : 27 ≤ 3 ^ n := hn' ▸ hPcard
    have hle : n ≤ 3 := by
      by_contra hlt
      have : 3 ^ 4 ∣ 1080 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at this
    have hge : 3 ≤ n := by
      by_contra hlt
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hfac : (Nat.card (Ybar Y)).factorization 3 = 3 := by
    rw [hcard, show (1080 : ℕ) = 3 ^ 3 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let PS : Sylow 3 (Ybar Y) := Sylow.ofCard P (by rw [hn', hn3, hfac])
  obtain ⟨z, hz, hz1⟩ := exists_mem_center_ne_one hZ
  have hzo : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (pow_three_of_mem_center hZ hz)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  exact KFacts.not_isMulCommutative_sylow_of_perfect hperf hz hzo PS hPc

theorem autAct_mem_m10 (hperf : commutator (Ybar Y) = ⊤)
    (hZ : Nat.card (Subgroup.center (Ybar Y)) = 3) (hcard : Nat.card (Ybar Y) = 1080)
    (e6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* alternatingGroup (Fin 6))
    (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    {g : ↥(Subgroup.normalizer (Y : Set G))}
    (hfix : ∀ z ∈ Subgroup.center (Ybar Y), barAct Y g z = z) {x : P10}
    (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcomm : (autAct ψ6 g : P10) * x = x * (autAct ψ6 g : P10)) :
    (autAct ψ6 g : P10) ∈ A6Models.m10 := by
  by_contra hm
  obtain ⟨w, hw, hw3, hwx, hwn, hinv⟩ :=
    A6.exists_inv_of_not_mem_m10 hx hx3 hx1 (autAct ψ6 g).2 hcomm hm
  set Zc := Subgroup.center (Ybar Y) with hZc
  obtain ⟨xt, hxt⟩ := ψ6.surjective ⟨x, hx⟩
  obtain ⟨q₁, rfl⟩ := QuotientGroup.mk_surjective xt
  obtain ⟨wt, hwt⟩ := ψ6.surjective ⟨w, hw⟩
  obtain ⟨q₂, rfl⟩ := QuotientGroup.mk_surjective wt
  have hψ1 : ((ψ6 (q₁ : Ybar Y ⧸ Zc) : ↥A6Models.psl29) : P10) = x := by rw [hxt]
  have hψ2 : ((ψ6 (q₂ : Ybar Y ⧸ Zc) : ↥A6Models.psl29) : P10) = w := by rw [hwt]
  have hq₁ : q₁ ^ 3 = 1 := pow_three_of_image hZ e6 (by
    apply ψ6.injective
    rw [map_pow, hxt, map_one]
    exact Subtype.ext (by simpa using hx3))
  have hq₂ : q₂ ^ 3 = 1 := pow_three_of_image hZ e6 (by
    apply ψ6.injective
    rw [map_pow, hwt, map_one]
    exact Subtype.ext (by simpa using hw3))
  have hnc := not_commute_of_lifts hperf hZ hcard ψ6 hq₁ hq₂ (by rw [hψ1]; exact hx1)
    (by rw [hψ1, hψ2]; exact hwx.symm) (by rw [hψ1, hψ2]; exact hwn)
  set c := q₁ * q₂ * q₁⁻¹ * q₂⁻¹ with hcdef
  have hc1 : c ≠ 1 := by
    intro h
    apply hnc
    rw [hcdef] at h
    calc q₁ * q₂ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ * (q₂ * q₁) := by group
      _ = q₂ * q₁ := by rw [h, one_mul]
  have hcZ : c ∈ Zc := by
    rw [← QuotientGroup.eq_one_iff]
    apply ψ6.injective
    apply Subtype.ext
    rw [hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      hψ1, hψ2, map_one, OneMemClass.coe_one]
    calc x * w * x⁻¹ * w⁻¹ = w * x * x⁻¹ * w⁻¹ := by rw [← hwx]
      _ = 1 := by group
  set σ := barAct Y g with hσ
  have hs1 : σ q₁ * q₁⁻¹ ∈ Zc := by
    have h := autAct_spec ψ6 g q₁
    rw [hψ1, hcomm, mul_inv_cancel_right, ← hψ1] at h
    have h' := ψ6.injective (Subtype.ext h)
    have h'' := QuotientGroup.eq_iff_div_mem.mp h'
    rwa [div_eq_mul_inv] at h''
  have hs2 : σ q₂ * q₂ ∈ Zc := by
    have h := autAct_spec ψ6 g q₂
    rw [hψ2, hinv] at h
    have h2 : ((ψ6 ((q₂⁻¹ : Ybar Y) : Ybar Y ⧸ Zc) : ↥A6Models.psl29) : P10) = w⁻¹ := by
      rw [QuotientGroup.mk_inv, map_inv, Subgroup.coe_inv, hψ2]
    rw [← h2] at h
    have h' := ψ6.injective (Subtype.ext h)
    have h'' := QuotientGroup.eq_iff_div_mem.mp h'
    rwa [div_eq_mul_inv, inv_inv] at h''
  set z₁ := σ q₁ * q₁⁻¹ with hz₁
  set z₂ := σ q₂ * q₂ with hz₂
  have e1 : σ q₁ = z₁ * q₁ := by rw [hz₁]; group
  have e2 : σ q₂ = z₂ * q₂⁻¹ := by rw [hz₂]; group
  have hσc : σ c = c⁻¹ := by
    have hci : c⁻¹ ∈ Zc := Zc.inv_mem hcZ
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, e1, e2,
      commutator_mul_center hs1 hs2 q₁ q₂⁻¹, ← hcdef]
    calc q₁ * q₂⁻¹ * q₁⁻¹ * q₂⁻¹⁻¹ = q₂⁻¹ * c⁻¹ * q₂ := by rw [hcdef]; group
      _ = c⁻¹ := by rw [mul_assoc, ← Subgroup.mem_center_iff.mp hci q₂]; group
  have hfixc : σ c = c := hfix c hcZ
  rw [hfixc] at hσc
  have hc2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hσc]
      _ = 1 := mul_inv_cancel c
  have hc3 := pow_three_of_mem_center hZ hcZ
  apply hc1
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hc2]; group

omit [Finite G] in
@[expose] noncomputable def imgP (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    (T : Subgroup G) : Subgroup P10 :=
  (T.subgroupOf (Subgroup.normalizer (Y : Set G))).map
    (A6Models.autA6.subtype.comp (autAct ψ6))

omit [Finite G] in
theorem mem_imgP (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29) {T : Subgroup G}
    {t : G} (ht : t ∈ T) (htN : t ∈ Subgroup.normalizer (Y : Set G)) :
    ((autAct ψ6 ⟨t, htN⟩ : ↥A6Models.autA6) : P10) ∈ imgP ψ6 T :=
  ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩

omit [Finite G] in
theorem exists_of_mem_imgP (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    {T : Subgroup G} {v : P10} (hv : v ∈ imgP ψ6 T) :
    ∃ (t : G) (_ : t ∈ T) (htN : t ∈ Subgroup.normalizer (Y : Set G)),
      v = ((autAct ψ6 ⟨t, htN⟩ : ↥A6Models.autA6) : P10) := by
  obtain ⟨⟨t, htN⟩, ht, rfl⟩ := hv
  exact ⟨t, Subgroup.mem_subgroupOf.mp ht, htN, rfl⟩

omit [Finite G] in
theorem imgP_le_autA6 (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    (T : Subgroup G) : imgP ψ6 T ≤ A6Models.autA6 := by
  rintro _ ⟨t, -, rfl⟩
  exact (autAct ψ6 t).2

omit [Finite G] in
theorem isPGroup_imgP (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    {T : Subgroup G} (hT : IsPGroup 2 T) : IsPGroup 2 (imgP ψ6 T) :=
  (hT.comap_of_injective _ (Subgroup.normalizer (Y : Set G)).subtype_injective).map _

omit [Finite G] in
theorem mem_normalizer_imgP (ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29)
    {T : Subgroup G} {a : ↥(Subgroup.normalizer (Y : Set G))}
    (ha : (a : G) ∈ Subgroup.normalizer (T : Set G)) :
    ((autAct ψ6 a : ↥A6Models.autA6) : P10) ∈ Subgroup.normalizer ((imgP ψ6 T : Subgroup P10) :
      Set P10) := by
  have ha' : a ∈ Subgroup.normalizer
      ((T.subgroupOf (Subgroup.normalizer (Y : Set G)) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp ha b
  exact Subgroup.le_normalizer_map _ ⟨a, ha', rfl⟩

theorem invA315_of_a6 {A S : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S) (hY2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hno : ¬ CharNormal153 Y S) (hq : CFSG.IsQuasisimple (Ybar Y))
    (hT : Sec4.IsTripleCover (Ybar Y) (alternatingGroup (Fin 6))) : InvA315 (Y ⊔ S) S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : commutator (Ybar Y) = ⊤ := by
    have h1 := hq.1
    rwa [Group.isPerfect_def] at h1
  have hcard : Nat.card (Ybar Y) = 1080 := by
    rw [KFacts.card_of_isTripleCover hT, DoubleA3.card_alt6']
  obtain ⟨hZ, ⟨e6⟩⟩ := hT
  obtain ⟨ψ0, -⟩ := DoubleA3.exists_psl_equiv
  set ψ6 : Ybar Y ⧸ Subgroup.center (Ybar Y) ≃* ↥A6Models.psl29 := e6.trans ψ0.symm with hψ6
  set H := Y ⊔ S with hHdef
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  have hSH : S ≤ H := le_sup_right
  obtain ⟨d, hd, hdZ, hd1⟩ := exists_mem_inf_center hAF hAY hperf hZ e6
  have hfixZ : ∀ (h : G) (hh : h ∈ H), ∀ z ∈ Subgroup.center (Ybar Y),
      barAct Y ⟨h, hHN hh⟩ z = z := fun h hh z hz =>
    fixes_center_of_mem_sup hAS hS2 hSY hZ hd hdZ hd1 hh hz
  have hker : ∀ (k : G) (hk : k ∈ H), autAct ψ6 ⟨k, hHN hk⟩ = 1 → (∃ m : ℕ, k ^ 2 ^ m = 1) →
      k ∈ S := by
    rintro k hk h1 ⟨m, hm⟩
    exact hO (mem_pCoreOf_of_barAct_eq_one hS2 hSY hZ hd.2 hdZ hd1 hk
      (barAct_eq_one_of_autAct ψ6 hperf h1) hm)
  have hexcl : ∀ (h : G) (hh : h ∈ H), ∀ x ∈ A6Models.psl29, x ^ 3 = 1 → x ≠ 1 →
      ((autAct ψ6 ⟨h, hHN hh⟩ : ↥A6Models.autA6) : P10) * x =
        x * ((autAct ψ6 ⟨h, hHN hh⟩ : ↥A6Models.autA6) : P10) →
      ((autAct ψ6 ⟨h, hHN hh⟩ : ↥A6Models.autA6) : P10) ∈ A6Models.m10 :=
    fun h hh x hx hx3 hx1 hc => autAct_mem_m10 hperf hZ hcard e6 ψ6 (hfixZ h hh) hx hx3 hx1 hc
  have hinner : ∀ (a : G) (ha : a ∈ A), ∃ q₀ : Ybar Y,
      barAct Y ⟨a, hAY ha⟩ = MulAut.conj q₀ ∧
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) =
        (ψ6 (q₀ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) := by
    intro a ha
    obtain ⟨q₀, hq₀⟩ := exists_inner_of_pow_three hperf e6 (g := ⟨a, hAY ha⟩)
      (Subtype.ext (by simpa using hAF.1.2 a ha))
    exact ⟨q₀, hq₀, autAct_of_inner ψ6 hq₀⟩
  have hlift : ∀ q : Ybar Y, q ^ 3 = 1 → (∀ (a : G) (ha : a ∈ A), barAct Y ⟨a, hAY ha⟩ q = q) →
      ∃ (a₀ : G) (ha₀ : a₀ ∈ A ⊓ Y), (QuotientGroup.mk ⟨a₀, ha₀.2⟩ : Ybar Y) = q := by
    intro q hq3 hqA
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
      intro a ha
      have h1 := hqA a ha
      rw [barAct_mk] at h1
      have h2 := (mk_eq_mk_iff _ hy).mp h1
      simpa [mul_assoc] using h2
    have hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y := by
      rw [← QuotientGroup.mk_pow] at hq3
      have : (⟨y, hy⟩ : ↥Y) ^ 3 = ⟨y ^ 3, Y.pow_mem hy 3⟩ := Subtype.ext (by simp)
      rw [this, mk_eq_one_iff] at hq3
      exact hq3
    obtain ⟨a₀, ha₀, hV⟩ := exists_mem_inf_of_fixed hAF hAY hy hfix hy3
    exact ⟨a₀, ha₀, (mk_eq_mk_iff ha₀.2 hy).mpr hV⟩
  have hlift6 : ∀ x ∈ A6Models.psl29, x ^ 3 = 1 → ∃ q : Ybar Y, q ^ 3 = 1 ∧
      ((ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) = x := by
    intro x hx hx3
    obtain ⟨xt, hxt⟩ := ψ6.surjective ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective xt
    refine ⟨q, pow_three_of_image hZ e6 ?_, by rw [hxt]⟩
    apply ψ6.injective
    rw [map_pow, hxt, map_one]
    exact Subtype.ext (by simpa using hx3)
  have hρY : ∀ (y : G) (hy : y ∈ Y), ((autAct ψ6 ⟨y, Subgroup.le_normalizer hy⟩ :
      ↥A6Models.autA6) : P10) = (ψ6 ((QuotientGroup.mk ⟨y, hy⟩ : Ybar Y) :
        Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) := fun y hy => autAct_mem ψ6 y hy
  have hQ₁ : imgP ψ6 S ≠ ⊥ := by
    intro h0
    have hSO : S ≤ CFSG.Open.pCoreOf 2 H := by
      intro s hs
      have h1 : autAct ψ6 ⟨s, hHN (hSH hs)⟩ = 1 := by
        have := mem_imgP ψ6 hs (hHN (hSH hs))
        rw [h0, Subgroup.mem_bot] at this
        exact Subtype.ext this
      obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
      exact mem_pCoreOf_of_barAct_eq_one hS2 hSY hZ hd.2 hdZ hd1 (hSH hs)
        (barAct_eq_one_of_autAct ψ6 hperf h1) (m := m) (by simpa using congrArg Subtype.val hm)
    have hSeq : S = CFSG.Open.pCoreOf 2 H := le_antisymm hSO hO
    apply hno
    have hYO : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_left)
        (hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    refine ⟨S, fun hS0 => hY2 (le_bot_iff.mp (hS0 ▸ hYO.trans hSeq.ge)), le_rfl, ?_, ?_⟩
    · rw [Subgroup.subgroupOf_self]
      infer_instance
    · have h := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
      rwa [← hSeq] at h
  have hexclP : ∀ {T : Subgroup G}, T ≤ H → ∀ x ∈ A6Models.psl29, x ^ 3 = 1 → x ≠ 1 →
      ∀ u ∈ imgP ψ6 T, u * x = x * u → u ∈ A6Models.m10 := by
    intro T hTH x hx hx3 hx1 u hu hux
    obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_imgP ψ6 hu
    exact hexcl t (hTH ht) x hx hx3 hx1 hux
  by_cases h8a : ∀ (a : G) (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) = 1
  · exfalso
    have hcen : ∀ (a : G) (ha : a ∈ A) (q : Ybar Y), barAct Y ⟨a, hAY ha⟩ q = q := by
      intro a ha q
      have h1 : autAct ψ6 ⟨a, hAY ha⟩ = 1 := Subtype.ext (h8a a ha)
      rw [barAct_eq_one_of_autAct ψ6 hperf h1, MulAut.one_apply]
    obtain ⟨x, hx, y, hy, hx3, hy3, hxy⟩ := A6.exists_noncomm_three
    obtain ⟨qx, hqx3, hqx⟩ := hlift6 x hx hx3
    obtain ⟨qy, hqy3, hqy⟩ := hlift6 y hy hy3
    obtain ⟨ax, hax, hmx⟩ := hlift qx hqx3 (fun a ha => hcen a ha qx)
    obtain ⟨ay, hay, hmy⟩ := hlift qy hqy3 (fun a ha => hcen a ha qy)
    have hcomm : ax * ay = ay * ax :=
      congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨ax, hax.1⟩ ⟨ay, hay.1⟩)
    have hq : qx * qy = qy * qx := by
      rw [← hmx, ← hmy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hcomm
    apply hxy
    rw [← hqx, ← hqy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hq]
  push Not at h8a
  obtain ⟨a₁, ha₁, hx1⟩ := h8a
  set x : P10 := ((autAct ψ6 ⟨a₁, hAY ha₁⟩ : ↥A6Models.autA6) : P10) with hxdef
  obtain ⟨q₁₀, -, hx_eq⟩ := hinner a₁ ha₁
  have hx : x ∈ A6Models.psl29 := by rw [hxdef, hx_eq]; exact (ψ6 _).2
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, ← map_pow]
    have : (⟨a₁, hAY ha₁⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAF.1.2 a₁ ha₁)
    rw [this, map_one, OneMemClass.coe_one]
  have hxn : ∀ {T : Subgroup G}, A ≤ Subgroup.normalizer (T : Set G) → ∀ a (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) ∈
        Subgroup.normalizer ((imgP ψ6 T : Subgroup P10) : Set P10) :=
    fun hT a ha => mem_normalizer_imgP ψ6 (hT ha)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hρcomm : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) *
        ((autAct ψ6 ⟨b, hAY hb⟩ : ↥A6Models.autA6) : P10) =
      ((autAct ψ6 ⟨b, hAY hb⟩ : ↥A6Models.autA6) : P10) *
        ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) := by
    intro a ha b hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hAcomm a ha b hb)
  have hpow3 : ∀ (a : G) (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) ^ 3 = 1 := by
    intro a ha
    rw [← Subgroup.coe_pow, ← map_pow]
    have : (⟨a, hAY ha⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAF.1.2 a ha)
    rw [this, map_one, OneMemClass.coe_one]
  have hpsl : ∀ (a : G) (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) ∈ A6Models.psl29 := by
    intro a ha
    obtain ⟨q, -, hq⟩ := hinner a ha
    rw [hq]
    exact (ψ6 _).2
  by_cases h8b : ∃ (a : G) (ha : a ∈ A),
      ((autAct ψ6 ⟨a, hAY ha⟩ : ↥A6Models.autA6) : P10) ∉ Subgroup.zpowers x
  · exfalso
    obtain ⟨a₂, ha₂, hyn⟩ := h8b
    set y : P10 := ((autAct ψ6 ⟨a₂, hAY ha₂⟩ : ↥A6Models.autA6) : P10) with hydef
    have hxy : x * y = y * x := hρcomm a₁ ha₁ a₂ ha₂
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ₁
    have ht1' : t ≠ 1 := fun h0 => ht1 (Subtype.ext h0)
    obtain ⟨horb, -, hcent⟩ := A6.lattice_a6 hx hx3 hx1 (imgP_le_autA6 ψ6 S)
      (isPGroup_imgP ψ6 hS2) le_rfl ht ht1' (hxn hAS a₁ ha₁) (hxn hAS a₁ ha₁)
      (hexclP hSH x hx hx3 hx1)
    have hyt : y * t * y⁻¹ ∈ imgP ψ6 S :=
      (Subgroup.mem_normalizer_iff.mp (hxn hAS a₂ ha₂) t).mp ht
    have hyt1 : y * t * y⁻¹ ≠ 1 := by
      intro h0
      apply ht1'
      have := congrArg (fun z => y⁻¹ * z * y) h0
      simpa [mul_assoc] using this
    have hxinv : x⁻¹ = x * x := A6.inv_eq_sq hx3
    have hxxx : ∀ u : P10, x * (x * (x * u)) = u := by
      intro u
      rw [← mul_assoc, ← mul_assoc, ← pow_two, ← pow_succ, hx3, one_mul]
    obtain ⟨k, hkdef, hkt⟩ : ∃ k : P10, (k = y ∨ k = x * x * y ∨ k = x * y) ∧ k * t = t * k := by
      have hyt' : ∀ w, y * t * y⁻¹ = w → y * t = w * y := by
        intro w hw
        rw [← hw]
        group
      rcases horb _ hyt hyt1 with h | h | h
      · exact ⟨y, Or.inl rfl, hyt' t h⟩
      · refine ⟨x * x * y, Or.inr (Or.inl rfl), ?_⟩
        calc x * x * y * t = x * x * (y * t) := by simp only [mul_assoc]
          _ = x * x * (x * t * (x * x) * y) := by rw [hyt' _ h]
          _ = t * (x * x * y) := by simp only [mul_assoc, hxxx]
      · refine ⟨x * y, Or.inr (Or.inr rfl), ?_⟩
        calc x * y * t = x * (y * t) := by simp only [mul_assoc]
          _ = x * (x * x * t * (x * x * (x * x)) * y) := by rw [hyt' _ h]
          _ = t * (x * y) := by simp only [mul_assoc, hxxx]
    have hkx : k * x = x * k := by
      rcases hkdef with rfl | rfl | rfl
      · exact hxy.symm
      · calc x * x * y * x = x * x * (y * x) := by group
          _ = x * x * (x * y) := by rw [hxy]
          _ = x * (x * x * y) := by group
      · calc x * y * x = x * (y * x) := by group
          _ = x * (x * y) := by rw [hxy]
    have hk : k ∈ A6Models.psl29 := by
      have hy : y ∈ A6Models.psl29 := hpsl a₂ ha₂
      rcases hkdef with rfl | rfl | rfl
      · exact hy
      · exact A6Models.psl29.mul_mem (A6Models.psl29.mul_mem hx hx) hy
      · exact A6Models.psl29.mul_mem hx hy
    have hy3 : y ^ 3 = 1 := hpow3 a₂ ha₂
    have hk3 : k ^ 3 = 1 := by
      have hc : Commute x y := hxy
      rcases hkdef with rfl | rfl | rfl
      · exact hy3
      · rw [(Commute.mul_left hc hc).mul_pow, (Commute.refl x).mul_pow, hx3, hy3]; group
      · rw [hc.mul_pow, hx3, hy3, one_mul]
    have hk1 : k ≠ 1 := by
      intro h0
      apply hyn
      rcases hkdef with rfl | rfl | rfl
      · rw [h0]; exact Subgroup.one_mem _
      · have : y = x := by
          calc y = (x * x)⁻¹ * (x * x * y) := by group
            _ = (x * x)⁻¹ := by rw [h0, mul_one]
            _ = x := by rw [← hxinv, inv_inv]
        rw [this]; exact Subgroup.mem_zpowers x
      · have : y = x⁻¹ := by
          calc y = x⁻¹ * (x * y) := by group
            _ = x⁻¹ := by rw [h0, mul_one]
        rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    obtain ⟨v, hv, hkv⟩ := hcent k hk hk3 hk1
    apply hkv
    by_cases hv1 : v = 1
    · rw [hv1, one_mul, mul_one]
    have cx : Commute k x := hkx
    have ct : Commute k t := hkt
    rcases horb v hv hv1 with rfl | rfl | rfl
    · exact hkt
    · exact ((cx.mul_right ct).mul_right (cx.mul_right cx)).eq
    · exact (((cx.mul_right cx).mul_right ct).mul_right
        ((cx.mul_right cx).mul_right (cx.mul_right cx))).eq
  push Not at h8b
  obtain ⟨q₁, hq₁3, hq₁x⟩ := hlift6 x hx hx3
  have hmodZ : ∀ q : Ybar Y, ((ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y)) :
      ↥A6Models.psl29) : P10) ∈ Subgroup.zpowers x →
      ∃ (z : Ybar Y) (j : ℤ), z ∈ Subgroup.center (Ybar Y) ∧ q = z * q₁ ^ j := by
    intro q hq
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hq
    have h1 : ((q : Ybar Y) : Ybar Y ⧸ Subgroup.center (Ybar Y)) =
        ((q₁ ^ j : Ybar Y) : Ybar Y ⧸ Subgroup.center (Ybar Y)) := by
      apply ψ6.injective
      apply Subtype.ext
      rw [← hj, ← hq₁x, QuotientGroup.mk_zpow, map_zpow, Subgroup.coe_zpow]
    exact ⟨q / q₁ ^ j, j, QuotientGroup.eq_iff_div_mem.mp h1, (div_mul_cancel q (q₁ ^ j)).symm⟩
  have hcommZ : ∀ (z z' : Ybar Y) (j j' : ℤ), z ∈ Subgroup.center (Ybar Y) →
      z' ∈ Subgroup.center (Ybar Y) → Commute (z * q₁ ^ j) (z' * q₁ ^ j') := by
    intro z z' j j' hz hz'
    have cz : ∀ g, Commute z g := fun g =>
      (show Commute g z from Subgroup.mem_center_iff.mp hz g).symm
    have cz' : ∀ g, Commute g z' := fun g => Subgroup.mem_center_iff.mp hz' g
    exact ((cz z').mul_right (cz _)).mul_left ((cz' _).mul_right
      ((Commute.refl q₁).zpow_zpow j j'))
  have hfixq : ∀ q : Ybar Y, ((ψ6 (q : Ybar Y ⧸ Subgroup.center (Ybar Y)) :
      ↥A6Models.psl29) : P10) ∈ Subgroup.zpowers x →
      ∀ (a : G) (ha : a ∈ A), barAct Y ⟨a, hAY ha⟩ q = q := by
    intro q hq a ha
    obtain ⟨q₀, hq₀, hρq₀⟩ := hinner a ha
    obtain ⟨z, j, hz, rfl⟩ := hmodZ q hq
    obtain ⟨z', j', hz', hq₀'⟩ := hmodZ q₀ (by rw [← hρq₀]; exact h8b a ha)
    rw [hq₀, MulAut.conj_apply, hq₀', (hcommZ z' z j' j hz' hz).eq, mul_inv_cancel_right]
  have hq₁A : ∀ (a : G) (ha : a ∈ A), barAct Y ⟨a, hAY ha⟩ q₁ = q₁ :=
    hfixq q₁ (by rw [hq₁x]; exact Subgroup.mem_zpowers x)
  obtain ⟨b₁, hb₁, hmb₁⟩ := hlift q₁ hq₁3 hq₁A
  have hρb₁ : ((autAct ψ6 ⟨b₁, hAY hb₁.1⟩ : ↥A6Models.autA6) : P10) = x := by
    refine (hρY b₁ hb₁.2).trans ?_
    rw [hmb₁, hq₁x]
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAYY : A ⊓ Y ≤ Y := inf_le_right
  have hAYH : A ⊓ Y ≤ H := hAYY.trans le_sup_left
  refine ⟨(A ⊓ Y).subgroupOf H, ⟨⟨⟨fun u v => Subtype.ext (Subtype.ext
    (hAcomm _ (Subgroup.mem_subgroupOf.mp u.2).1 _ (Subgroup.mem_subgroupOf.mp v.2).1))⟩⟩,
    fun u hu => Subtype.ext (hA3 _ (Subgroup.mem_subgroupOf.mp hu).1)⟩, ?_, ?_⟩
  ·
    intro B hB hAB
    set B' := B.map H.subtype with hB'
    have hB'3 : ∀ u ∈ B', u ^ 3 = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      simpa using congrArg Subtype.val (hB.2 u hu)
    have hB'Y : B' ≤ Y := fun u hu => by
      obtain ⟨u', hu', rfl⟩ := hu
      exact mem_of_pow_three_of_mem_sup hS2 hSY u'.2 (j := 1) (by
        simpa using hB'3 _ ⟨u', hu', rfl⟩)
    have hAYB' : A ⊓ Y ≤ B' := by
      intro u hu
      exact ⟨⟨u, hAYH hu⟩, hAB (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
    have hB'comm : ∀ u ∈ B', ∀ v ∈ B', u * v = v * u := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      have := hB.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
      exact congrArg (fun w : ↥B => ((w : ↥H) : G)) this
    have hB'AY : B' ≤ A ⊓ Y := by
      intro b hb
      have hbY := hB'Y hb
      obtain ⟨qb, hqb⟩ : ∃ q : Ybar Y, q = QuotientGroup.mk ⟨b, hbY⟩ := ⟨_, rfl⟩
      have hqb3 : qb ^ 3 = 1 := by
        rw [hqb, ← QuotientGroup.mk_pow]
        have : (⟨b, hbY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hB'3 b hb)
        rw [this, QuotientGroup.mk_one]
      have hqbq₁ : q₁ * qb = qb * q₁ := by
        rw [← hmb₁, hqb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (hB'comm _ (hAYB' hb₁) _ hb)
      have hxb : ((ψ6 (qb : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) ∈
          Subgroup.zpowers x := by
        by_contra hn
        have hcomm' : ((ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : ↥A6Models.psl29) : P10) *
            (ψ6 (qb : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) =
            (ψ6 (qb : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) *
              (ψ6 (q₁ : Ybar Y ⧸ Subgroup.center (Ybar Y)) : P10) := by
          rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
            ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hqbq₁]
        exact not_commute_of_lifts hperf hZ hcard ψ6 hq₁3 hqb3 (by rw [hq₁x]; exact hx1)
          hcomm' (by rw [hq₁x]; exact hn) hqbq₁
      obtain ⟨a₀, ha₀, hma₀⟩ := hlift qb hqb3 (hfixq qb hxb)
      have hV : b * a₀⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
        (mk_eq_mk_iff hbY ha₀.2).mp (hqb.symm.trans hma₀.symm)
      have hb3 : (b * a₀⁻¹) ^ 3 = 1 := hB'3 _ (B'.mul_mem hb (B'.inv_mem (hAYB' ha₀)))
      obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨_, hV⟩
      have hm' : (b * a₀⁻¹) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h1 : b * a₀⁻¹ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left m (by norm_num)) (orderOf_dvd_of_pow_eq_one hm')
        (orderOf_dvd_of_pow_eq_one hb3))
      rw [mul_inv_eq_one] at h1
      rw [h1]
      exact ha₀
    have heq : A ⊓ Y = B' := le_antisymm hAYB' hB'AY
    have : B = B'.subgroupOf H := by
      rw [hB', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [this, ← heq]
  ·
    refine ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hS2.comap_of_injective H.subtype H.subtype_injective), ?_⟩, ?_⟩
    · intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp (hAS (Subgroup.mem_subgroupOf.mp ha).1) u
    · intro Q hQ hSQ
      set P' := Q.map H.subtype with hP'
      have hP'H : P' ≤ H := Subgroup.map_subtype_le Q
      have hP'2 : IsPGroup 2 P' :=
        ((isPiSubgroup_piOf_iff Nat.prime_two Q).mp hQ.2.1).map H.subtype
      have hSP' : S ≤ P' := fun s hs =>
        ⟨⟨s, hSH hs⟩, hSQ (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
      have hb₁P' : b₁ ∈ Subgroup.normalizer (P' : Set G) :=
        mem_normalizer_map (H := H) (a := ⟨b₁, hAYH hb₁⟩)
          (hQ.2.2 (Subgroup.mem_subgroupOf.mpr hb₁))
      have hle : imgP ψ6 S ≤ imgP ψ6 P' := by
        intro v hv
        obtain ⟨t, ht, htN, rfl⟩ := exists_of_mem_imgP ψ6 hv
        exact mem_imgP ψ6 (hSP' ht) htN
      have hn2 : x ∈ Subgroup.normalizer ((imgP ψ6 P' : Subgroup P10) : Set P10) := by
        rw [← hρb₁]
        exact mem_normalizer_imgP ψ6 hb₁P'
      obtain ⟨hle', -⟩ := A6.le_of_lattice_a6 hx hx3 hx1 (imgP_le_autA6 ψ6 P')
        (isPGroup_imgP ψ6 hP'2) hle hQ₁ (hxn hAS a₁ ha₁) hn2 (hexclP hP'H x hx hx3 hx1)
      have hP'S : P' ≤ S := by
        intro p hp
        obtain ⟨s, hs, hsN, hsp⟩ :=
          exists_of_mem_imgP ψ6 (hle' (mem_imgP ψ6 hp (hHN (hP'H hp))))
        have hsp' : s⁻¹ * p ∈ H := H.mul_mem (H.inv_mem (hSH hs)) (hP'H hp)
        have h1 : autAct ψ6 ⟨s⁻¹ * p, hHN hsp'⟩ = 1 := by
          have e : (⟨s⁻¹ * p, hHN hsp'⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
              (⟨s, hsN⟩ : ↥(Subgroup.normalizer (Y : Set G)))⁻¹ * ⟨p, hHN (hP'H hp)⟩ :=
            Subtype.ext rfl
          rw [e, map_mul, map_inv, inv_mul_eq_one]
          exact (Subtype.ext hsp).symm
        have h2 : ∃ m : ℕ, (s⁻¹ * p) ^ 2 ^ m = 1 := by
          obtain ⟨m, hm⟩ := hP'2 ⟨s⁻¹ * p, P'.mul_mem (P'.inv_mem (hSP' hs)) hp⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩
        have h3 := hker _ hsp' h1 h2
        have e2 : p = s * (s⁻¹ * p) := by group
        rw [e2]
        exact S.mul_mem hs h3
      intro u hu
      exact Subgroup.mem_subgroupOf.mpr (hP'S ⟨u, hu, rfl⟩)

end Cover

end CFSG.RankThree.PartTwo.Sec15.Push153B
