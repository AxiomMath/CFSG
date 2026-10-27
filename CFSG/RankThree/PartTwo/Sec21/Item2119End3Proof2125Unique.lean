module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement Pointwise

namespace Item2119End3Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_bot_of_mem_thetaComponentsIn' {M K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    K ≠ ⊥ := by
  obtain ⟨-, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have : Nontrivial (K.subgroupOf M ⧸ aschbacherSolvableCore 3 (K.subgroupOf M)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hK'.2.2
  rintro rfl
  have hs : Subsingleton ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  obtain ⟨u, v, huv⟩ := exists_pair_ne
    ((⊥ : Subgroup G).subgroupOf M ⧸ aschbacherSolvableCore 3 ((⊥ : Subgroup G).subgroupOf M))
  apply huv
  induction u using QuotientGroup.induction_on with
  | H u =>
  induction v using QuotientGroup.induction_on with
  | H v =>
  rw [Subsingleton.elim u v]

theorem le_thetaQuotCentralizer_of_ne {M K L : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hL : L ∈ thetaComponentsIn M) (hne : K ≠ L) : L ≤ Sec4.thetaQuotCentralizer K := by
  have hKp := isPerfect_of_mem_thetaComponentsIn hK
  have hK1 := ne_bot_of_mem_thetaComponentsIn' hK
  have hK₀ := hK
  have hL₀ := hL
  obtain ⟨K', hK', rfl⟩ := hK
  obtain ⟨L', hL', rfl⟩ := hL
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hK' hL'.2.1 with
    h | ⟨hN, hC⟩
  · exact absurd (Sec6.eq_of_mem_thetaComponentsIn_of_le hK₀ hL₀ hKp hK1 le_rfl
      (Subgroup.map_mono h)) hne
  · intro l hl
    obtain ⟨l', hl', rfl⟩ := hl
    rw [Sec6.mem_thetaQuotCentralizer_iff]
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨k', hk', rfl⟩ := hx
      exact ⟨l' * k' * l'⁻¹, (Subgroup.mem_normalizer_iff.mp (hN hl') k').mp hk', by simp⟩
    · intro k hk
      obtain ⟨k', hk', rfl⟩ := hk
      have hmem : ⁅k'⁻¹, l'⁆ ∈ inSubgroup (aschbacherSolvableCore 3) K' :=
        hC (Subgroup.commutator_mem_commutator (K'.inv_mem hk') hl')
      rw [← Sec6.map_inSubgroup_theta_of_injective M.subtype M.subtype_injective K']
      refine ⟨⁅k'⁻¹, l'⁆, hmem, ?_⟩
      simp only [commutatorElement_def, inv_inv, Subgroup.coe_subtype, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group

omit [Finite G] in
theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h : φ z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [hY, Subgroup.mem_bot] at h
  rw [Subgroup.mem_bot]
  exact φ.injective (by rw [h, map_one])

theorem eq_one_of_mem_thetaQuotCentralizer {Le : Subgroup G}
    (hZ : Subgroup.center (lBar Le) = ⊥) {b : G} (hbL : b ∈ Le)
    (hbC : b ∈ Sec4.thetaQuotCentralizer Le) (hb3 : b ^ 3 = 1) : b = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb := (Sec6.mem_thetaQuotCentralizer_iff.mp hbC).2
  set b' : Le := ⟨b, hbL⟩
  have hcen : (b' : lBar Le) ∈ Subgroup.center (lBar Le) := by
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H l =>
    have h1 := hb l l.2
    obtain ⟨w, hw, hwe⟩ := h1
    have hw' : w = l⁻¹ * (b' * l * b'⁻¹) := Subtype.ext (by simpa using hwe)
    rw [hw'] at hw
    have h2 : ((l : Le) : lBar Le) = ((b' * l * b'⁻¹ : Le) : lBar Le) :=
      QuotientGroup.eq.mpr hw
    have h3 : ((l : Le) : lBar Le) =
        (b' : lBar Le) * (l : lBar Le) * (b' : lBar Le)⁻¹ := by
      conv_lhs => rw [h2]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (l : lBar Le) * (b' : lBar Le) =
        (b' : lBar Le) * (l : lBar Le) * (b' : lBar Le)⁻¹ * b' := by rw [← h3]
      _ = (b' : lBar Le) * l := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 Le) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hb'3 : (b' : Le) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  by_contra hb1
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hord : orderOf (⟨b', hcen⟩ : aschbacherSolvableCore 3 Le) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hb'3 hb'1
  have hdvd := orderOf_dvd_natCard (⟨b', hcen⟩ : aschbacherSolvableCore 3 Le)
  rw [hord] at hdvd
  exact hθ3 hdvd

theorem not_mem_of_mem_thetaComponentsAt {e : G} {Le : Subgroup G}
    (hLe : Le ∈ thetaComponentsAt 3 e) (hZ : Subgroup.center (lBar Le) = ⊥) (he3 : e ^ 3 = 1)
    (he1 : e ≠ 1) : e ∉ Le := by
  intro heL
  apply he1
  have hLC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  refine eq_one_of_mem_thetaQuotCentralizer hZ heL ?_ he3
  rw [Sec6.mem_thetaQuotCentralizer_iff]
  refine ⟨Subgroup.le_normalizer heL, fun l hl => ?_⟩
  have hle : l * e = e * l := Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
  rw [show l⁻¹ * (e * l * e⁻¹) = 1 by rw [← hle]; group]
  exact Subgroup.one_mem _

theorem mem_thetaQuotCentralizer_of_mem_thetaComponentsAt {e : G} {Le : Subgroup G}
    (hLe : Le ∈ thetaComponentsAt 3 e) : e ∈ Sec4.thetaQuotCentralizer Le := by
  have hLC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  rw [Sec6.mem_thetaQuotCentralizer_iff]
  refine ⟨Subgroup.mem_normalizer_fintype fun l hl => ?_, fun l hl => ?_⟩
  · have hle : l * e = e * l := Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
    rw [show e * l * e⁻¹ = l by rw [← hle]; group]
    exact hl
  · have hle : l * e = e * l := Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
    rw [show l⁻¹ * (e * l * e⁻¹) = 1 by rw [← hle]; group]
    exact Subgroup.one_mem _

omit [Finite G] in
theorem isElemAbelian_map' {H H' : Type*} [Group H] [Group H'] {S : Subgroup H}
    (hS : IsElemAbelian 3 S) (φ : H →* H') : IsElemAbelian 3 (S.map φ) :=
  CFSG.SectionRank.isElemAbelian_map hS _

omit [Finite G] in
theorem isElemAbelian_zpowers' {x : G} (hx3 : x ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx3

theorem isElemAbelian_sup_zpowers {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G}
    (hx3 : x ^ 3 = 1) (hxB : ∀ b ∈ B, x * b = b * x) :
    IsElemAbelian 3 (B ⊔ Subgroup.zpowers x) ∧
      (x ∉ B → Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) = 3 * Nat.card B) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ y ∈ B, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute x y from hxB y hy) k).eq).symm
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B _ hc
  have hBc : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hZc : ∀ z ∈ Subgroup.zpowers x, ∀ z' ∈ Subgroup.zpowers x, z * z' = z' * z :=
    fun z hz z' hz' => congrArg Subtype.val
      ((isElemAbelian_zpowers' hx3).1.is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩)
  have hmem : ∀ u ∈ (B ⊔ Subgroup.zpowers x : Subgroup G), ∃ y ∈ B, ∃ z ∈ Subgroup.zpowers x,
      u = y * z := by
    intro u hu
    have hu' : u ∈ ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hu
    rw [hset] at hu'
    obtain ⟨y, hy, z, hz, rfl⟩ := hu'
    exact ⟨y, hy, z, hz, rfl⟩
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩, fun hxB' => ?_⟩
  · obtain ⟨y, hy, z, hz, hu⟩ := hmem u u.2
    obtain ⟨y', hy', z', hz', hv⟩ := hmem v v.2
    apply Subtype.ext
    change (u : G) * v = v * u
    rw [hu, hv]
    have h1 : Commute y y' := hBc y hy y' hy'
    have h2 : Commute y z' := hc y hy z' hz'
    have h3 : Commute z y' := (hc y' hy' z hz).symm
    have h4 : Commute z z' := hZc z hz z' hz'
    exact (Commute.mul_left (h1.mul_right h2) (h3.mul_right h4)).eq
  · obtain ⟨y, hy, z, hz, rfl⟩ := hmem u hu
    have hyz : Commute y z := hc y hy z hz
    rw [hyz.mul_pow, hB.2 y hy, (isElemAbelian_zpowers' hx3).2 z hz, one_mul]
  · have hx1 : x ≠ 1 := fun h => hxB' (h ▸ B.one_mem)
    have hZ3 : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    have hinf : Nat.card (B ⊓ Subgroup.zpowers x : Subgroup G) = 1 := by
      have hdvd : Nat.card (B ⊓ Subgroup.zpowers x : Subgroup G) ∣ 3 :=
        hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso
        have heq : B ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZ3, h])
        have hmx : x ∈ B ⊓ Subgroup.zpowers x := by
          rw [heq]
          exact Subgroup.mem_zpowers x
        exact hxB' hmx.1
    rw [hinf, mul_one, hZ3] at hcard
    rw [hcard, mul_comm]

theorem exists_maximal_elemAbelian {F : Subgroup G} (hF : IsElemAbelian 3 F) :
    ∃ F' : Subgroup G, F ≤ F' ∧ IsElemAbelian 3 F' ∧
      ∀ B : Subgroup G, IsElemAbelian 3 B → F' ≤ B → B = F' := by
  set S : Set (Subgroup G) := {B | IsElemAbelian 3 B ∧ F ≤ B}
  obtain ⟨F', ⟨hF'e, hFF'⟩, hmax⟩ :=
    Set.Finite.exists_maximalFor (fun B : Subgroup G => Nat.card B) S (Set.toFinite S)
      ⟨F, hF, le_rfl⟩
  refine ⟨F', hFF', hF'e, fun B hB hF'B => ?_⟩
  have h := hmax ⟨hB, hFF'.trans hF'B⟩ (Subgroup.card_le_of_le hF'B)
  exact (Subgroup.eq_of_le_of_card_ge hF'B h).symm

theorem exists_elemAbelian_of_quot {Le : Subgroup G} {Eb : Subgroup (lBar Le)}
    (hEc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x) (hE3 : ∀ x ∈ Eb, x ^ 3 = 1)
    (hE9 : Nat.card Eb = 9) :
    ∃ B : Subgroup G, B ≤ Le ∧ IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 Le with hθ
  set π := QuotientGroup.mk' θ with hπ
  set P₀ := Eb.comap π with hP₀
  let f : P₀ →* Eb := (π.comp P₀.subtype).codRestrict Eb (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ y
    exact ⟨⟨l, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 P₀) := inferInstance
  have hEp : IsPGroup 3 Eb := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hSE : (S : Subgroup P₀).map f = ⊤ := by
    have h := ((S.mapSurjective hf).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
    rwa [Sylow.coe_mapSurjective] at h
  set g : (S : Subgroup P₀) →* Eb := f.comp (S : Subgroup P₀).subtype with hg
  have hθ3 : ¬ 3 ∣ Nat.card θ := three_not_dvd_card_aschbacherSolvableCore
  have hginj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hsθ : (((s : P₀) : Le)) ∈ θ := by
      have h1 : π ((s : P₀) : Le) = 1 := congrArg Subtype.val hs
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := S.isPGroup' s
    have h1 : orderOf (((s : P₀) : Le)) ∣ 3 ^ k := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (((s : P₀) : Le)) ∣ Nat.card θ := by
      have h3 := orderOf_dvd_natCard (⟨((s : P₀) : Le), hsθ⟩ : θ)
      rwa [Subgroup.orderOf_mk] at h3
    have hcop : Nat.Coprime (3 ^ k) (Nat.card θ) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    have h4 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff] at h4
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h4)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : y ∈ (S : Subgroup P₀).map f := hSE ▸ Subgroup.mem_top y
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨⟨s, hs⟩, rfl⟩
  have hS9 : Nat.card (S : Subgroup P₀) = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Equiv.ofBijective g ⟨hginj, hgsurj⟩)
  have hSe : IsElemAbelian 3 (S : Subgroup P₀) := by
    refine ⟨⟨⟨fun a b => hginj ?_⟩⟩, fun s hs => ?_⟩
    · rw [map_mul, map_mul]
      exact Subtype.ext (hEc _ (g a).2 _ (g b).2)
    · have h1 : g ⟨s, hs⟩ ^ 3 = 1 := Subtype.ext (hE3 _ (g ⟨s, hs⟩).2)
      have h2 : g (⟨s, hs⟩ ^ 3) = g 1 := by rw [map_pow, h1, map_one]
      have h3 := congrArg Subtype.val (hginj h2)
      simpa using h3
  refine ⟨((S : Subgroup P₀).map P₀.subtype).map Le.subtype, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · exact isElemAbelian_map' (isElemAbelian_map' hSe P₀.subtype) Le.subtype
  · rw [Subgroup.card_map_of_injective Le.subtype_injective,
      Subgroup.card_map_of_injective P₀.subtype_injective, hS9]

theorem exists_elemAbelian_quot_of_le {L B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9) :
    ∃ Eb : Subgroup (lBar L), (∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x) ∧ (∀ x ∈ Eb, x ^ 3 = 1) ∧
      Nat.card Eb = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B' := B.subgroupOf L with hB'
  have hB'e : IsElemAbelian 3 B' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact congrArg Subtype.val
        (hB.1.is_comm.comm ⟨((a : L) : G), a.2⟩ ⟨((b : L) : G), b.2⟩)
    · apply Subtype.ext
      simpa using hB.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hB'p : IsPGroup 3 B' := fun x => ⟨1, Subtype.ext (by simpa using hB'e.2 x x.2)⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hB'p
  refine ⟨B'.map π, ?_, ?_, ?_⟩
  · intro x hx y hy
    have h := (isElemAbelian_map' hB'e π).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val h
  · exact (isElemAbelian_map' hB'e π).2
  · have hinj' : Function.Injective (π.comp B'.subtype) := fun a b h =>
      Subtype.ext (hinj a.2 b.2 h)
    have hrange : (π.comp B'.subtype).range = B'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card (B'.map π) = Nat.card B' := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
    rw [h1, hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB9]

theorem card_lBar_dvd_card_residual {K B : Subgroup G} (hKp : Group.IsPerfect K)
    (hB3 : IsPGroup 3 B) (hBK : B ≤ Sec4.thetaQuotCentralizer K) :
    Nat.card (lBar K) ∣
      Nat.card (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer (B : Set G))) := by
  set Z := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer (B : Set G)) with hZ
  have hZK : Z ≤ K := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  set ρ : Z →* lBar K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (Subgroup.inclusion hZK)
  have hcov := Sec6.le_residual_inf_centralizer_sup_theta hKp hB3 hBK
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) q
    have hl : (l : G) ∈ (Z : Set G) * (inSubgroup (aschbacherSolvableCore 3) K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z _
        (hZK.trans (Sec6.le_normalizer_theta K))]
      exact hcov l.2
    obtain ⟨z, hz, t, ht, hzt⟩ := hl
    refine ⟨⟨z, hz⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 K) (Subgroup.inclusion hZK ⟨z, hz⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hZK ⟨z, hz⟩)⁻¹ * l = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hzt]
      simp
    rw [this]
    exact ht'
  exact Subgroup.card_dvd_of_surjective (f := ρ) hsurj

end Item2119End3Proof

open Item2119End3Proof

theorem item2125UniqueOf_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2125UniqueOf := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 e he hed Le hLe hLeL hdLe hdTLe K hK hK3
  obtain ⟨eLe⟩ := hLeL
  by_contra hKne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, hn0, hne, ⟨eL⟩⟩ := hcfg.lthree
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have he3 : e ^ 3 = 1 := h3 e he
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hZLe : Subgroup.center (lBar Le) = ⊥ :=
    center_eq_bot_of_mulEquiv' (eLe.trans eL)
      (Item21Early2Proof.center_projSL_three_eq_bot hn0 hne)
  have heLe : e ∉ Le := not_mem_of_mem_thetaComponentsAt hLe hZLe he3 he1
  have hKLe : K ≤ Sec4.thetaQuotCentralizer Le :=
    le_thetaQuotCentralizer_of_ne hLe hK (Ne.symm hKne)
  have hLeK : Le ≤ Sec4.thetaQuotCentralizer K := le_thetaQuotCentralizer_of_ne hK hLe hKne
  have heC : e ∈ Sec4.thetaQuotCentralizer Le :=
    mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLe
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  obtain ⟨-, d₀, hd₀AL, hd₀1, -, -, -, -, -, ⟨w, ⟨hwL, -⟩, hw3, hwd₀, -, ⟨a', ha'A, hwa'⟩⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  have hd₀3 : d₀ ^ 3 = 1 := h3 d₀ hd₀AL.1
  have hwZ : ∀ b ∈ Subgroup.zpowers d₀, w * b = b * w := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute w d₀ := by
      calc w * d₀ = w * d₀ * w⁻¹ * w := by group
        _ = d₀ * w := by rw [hwd₀]
    exact (hc.zpow_right k).eq
  have hwd : w ∉ Subgroup.zpowers d₀ := by
    intro h
    apply hwa'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc : Commute (d₀ ^ k) a' := (Commute.zpow_left (hcomm d₀ hd₀AL.1 a' ha'A) k)
    rw [hc.eq]
    group
  obtain ⟨hB0e, hB0card⟩ := isElemAbelian_sup_zpowers (isElemAbelian_zpowers' hd₀3) hw3 hwZ
  have hB0L : Subgroup.zpowers d₀ ⊔ Subgroup.zpowers w ≤ L :=
    sup_le (Subgroup.zpowers_le.mpr hd₀AL.2) (Subgroup.zpowers_le.mpr hwL)
  have hB09 : Nat.card (Subgroup.zpowers d₀ ⊔ Subgroup.zpowers w : Subgroup G) = 9 := by
    rw [hB0card hwd, Nat.card_zpowers, orderOf_eq_prime hd₀3 hd₀1]
  obtain ⟨Eb, hEbc, hEb3, hEb9⟩ := exists_elemAbelian_quot_of_le hB0L hB0e hB09
  obtain ⟨B, hBLe, hBe, hB9⟩ := exists_elemAbelian_of_quot (Le := Le)
    (Eb := Eb.map eLe.symm.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hEbc x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hEb3 x hx, map_one])
    (by rw [Subgroup.card_map_of_injective eLe.symm.injective, hEb9])
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  have hBK : B ≤ Sec4.thetaQuotCentralizer K := hBLe.trans hLeK
  have hKp : Group.IsPerfect K := Sec6.isPerfect_of_mem_thetaComponentsAt hK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  set Z := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer (B : Set G)) with hZdef
  have hZp : Group.IsPerfect Z := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hZ1 : Z ≠ ⊥ := Sec6.residual_inf_centralizer_ne_bot hKp hKq hB3 hBK
  have hZK : Z ≤ K := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hZB : Z ≤ Subgroup.centralizer (B : Set G) :=
    (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_right
  have hZ3 : 3 ∣ Nat.card Z := by
    refine dvd_trans ?_ (card_lBar_dvd_card_residual hKp hB3 hBK)
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K)
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
      three_not_dvd_card_aschbacherSolvableCore
    rw [hc] at hK3
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp hK3 |>.resolve_right hθ3
  have hZ2 : 2 ∣ Nat.card Z := by
    by_contra h2
    have hodd : Odd (Nat.card Z) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have hsol : Group.IsSolvable Z := CFSG.FeitThompson.isSolvable_of_odd_natCard Z hodd
    have htop : (⊤ : Subgroup Z) = ⊥ :=
      GroupTheory.eq_bot_of_isPerfect_of_isSolvable
        (Group.IsPerfect.top_iff.mpr hZp) (by
          have := hsol
          exact Group.isSolvable_of_isSolvable_injective
            (f := (⊤ : Subgroup Z).subtype) (Subgroup.subtype_injective _))
    apply hZ1
    rw [eq_bot_iff]
    intro z hz
    have h1 : (⟨z, hz⟩ : Z) ∈ (⊤ : Subgroup Z) := Subgroup.mem_top _
    rw [htop, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  have hZe : Subgroup.zpowers e ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hZK hz)))
  obtain ⟨x, hxZ, hx3, hxe⟩ := Sec6.exists_pow_three_eq_one_not_mem hZp hZ3 hZe
  have heB : ∀ b ∈ B, e * b = b * e := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLeC (hBLe hb))).symm
  obtain ⟨hEe, hEcard⟩ := isElemAbelian_sup_zpowers hBe he3 heB
  have heB' : e ∉ B := fun h => heLe (hBLe h)
  set EE := B ⊔ Subgroup.zpowers e with hEE
  have hE27 : Nat.card EE = 27 := by rw [hEcard heB', hB9]
  have htE : EE ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    refine sup_le (fun b hb => ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hZB t.2) b hb
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hZK t.2))).symm
  have hEmem : EE ∈ partTwoE G := by
    refine ⟨hEe, hE27, Subgroup.zpowers (t : G), ?_, ?_, ?_⟩
    · intro h
      have h1 : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
      rw [h, Subgroup.mem_bot] at h1
      have h2 : t = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at ht
      norm_num at ht
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
    · intro g hg
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgt : g * (t : G) = (t : G) * g :=
        Subgroup.mem_centralizer_singleton_iff.mp (htE hg)
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hgt, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ k
  have hxEE : ∀ y ∈ EE, x * y = y * x := by
    intro y hy
    have hxC : x ∈ Subgroup.centralizer (EE : Set G) := by
      have h1 : EE ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (fun b hb => ?_) ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp (hZB hxZ) b hb
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp (hKC (hZK hxZ))).symm
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 hz))
    exact (Subgroup.mem_centralizer_iff.mp hxC y hy).symm
  obtain ⟨hFe, hFcard⟩ := isElemAbelian_sup_zpowers hEe hx3 hxEE
  have hxnot : x ∉ EE := by
    intro hxE
    apply hxe
    have hc : ∀ y ∈ B, ∀ z ∈ Subgroup.zpowers e, y * z = z * y := by
      intro y hy z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ((Commute.zpow_left (show Commute e y from heB y hy) k).eq).symm
    have hx' : x ∈ ((B ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := hxE
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B _ hc).2] at hx'
    obtain ⟨b, hb, z, hz, hbz⟩ := hx'
    have hbz : b * z = x := hbz
    have hbC : b ∈ Sec4.thetaQuotCentralizer Le := by
      have h1 : b = x * z⁻¹ := by rw [← hbz]; group
      rw [h1]
      refine Subgroup.mul_mem _ (hKLe (hZK hxZ)) (Subgroup.inv_mem _ ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Subgroup.zpow_mem _ heC k
    have hb1 := eq_one_of_mem_thetaQuotCentralizer hZLe (hBLe hb) hbC (hBe.2 b hb)
    have hxz : x = z := by rw [← hbz, hb1, one_mul]
    rw [hxz]
    exact hz
  have hF81 : Nat.card (EE ⊔ Subgroup.zpowers x : Subgroup G) = 81 := by
    rw [hFcard hxnot, hE27]
  obtain ⟨F', hFF', hF'e, hF'max⟩ := exists_maximal_elemAbelian hFe
  have hF'F : F' ∈ partTwoF G := ⟨hF'e, hF'max, EE, hEmem, le_sup_left.trans hFF'⟩
  have hAE : A ∈ partTwoE G := by
    obtain ⟨-, -, E₀, hE₀, hE₀A⟩ := hpair.mem_S.1
    have hA27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
    have hEq : E₀ = A := Subgroup.eq_of_le_of_card_ge hE₀A (by rw [hA27, hE₀.2.1])
    rw [← hEq]
    exact hE₀
  have hEF := hpair.side hAE
  rw [← hEF] at hF'F
  have h1 := Subgroup.card_le_of_le hFF'
  rw [hF81, hF'F.2.1] at h1
  norm_num at h1

theorem item2125Unique_of_generic
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hGen : Item2125Generic) : Item2125Unique :=
  item2125Unique_of h211 h2116 h45 h66 (item2125UniqueOf_of h45 h66) hGen

end CFSG.RankThree.PartTwo.Sec21
