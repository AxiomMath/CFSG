module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.Quasithin.EmptyFaithful.LRed5Quot
public import CFSG.Quasithin.Background.InternalSecB56

public section

namespace CFSG.Quasithin.H13.KGFFZ

open CFSG.Open (pCoreOf quasithinGenFitting)
open CFSG.Quasithin CFSG.Quasithin.EmptyFaithfulMultiple CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

section Dichotomy

variable {G : Type} [Group G]

theorem commute_of_commutator_mem_center {L : Subgroup G} (hperf : ⁅L, L⁆ = L) {x : G}
    (hc : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ L ∧
      ∀ m ∈ L, (l * x * l⁻¹ * x⁻¹) * m = m * (l * x * l⁻¹ * x⁻¹)) :
    ∀ l ∈ L, l * x = x * l := by
  have hconj : ∀ a ∈ L, x * a * x⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ * a := fun a _ => by group
  have hcentral : ∀ a ∈ L, ∀ m ∈ L, (a * x * a⁻¹ * x⁻¹)⁻¹ * m = m * (a * x * a⁻¹ * x⁻¹)⁻¹ := by
    intro a ha m hm
    have h1 := (hc a ha).2 m hm
    calc (a * x * a⁻¹ * x⁻¹)⁻¹ * m
        = (a * x * a⁻¹ * x⁻¹)⁻¹ * (m * (a * x * a⁻¹ * x⁻¹)) * (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
      _ = (a * x * a⁻¹ * x⁻¹)⁻¹ * ((a * x * a⁻¹ * x⁻¹) * m) * (a * x * a⁻¹ * x⁻¹)⁻¹ := by
          rw [h1]
      _ = m * (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
  have hconjc : ∀ z : G, (∀ m ∈ L, z * m = m * z) → ∀ m ∈ L, z * m * z⁻¹ = m := by
    intro z hz m hm
    rw [hz m hm, mul_inv_cancel_right]
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, x * (a * b * a⁻¹ * b⁻¹) * x⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    intro a ha b hb
    have hza := hcentral a ha
    have hzb := hcentral b hb
    set za := (a * x * a⁻¹ * x⁻¹)⁻¹ with hzadef
    set zb := (b * x * b⁻¹ * x⁻¹)⁻¹ with hzbdef
    have hzbL : zb ∈ L := L.inv_mem (hc b hb).1
    have e1 : x * (a * b * a⁻¹ * b⁻¹) * x⁻¹ =
        (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by group
    have hm1 : a * zb * b * a⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ha hzbL) hb) (L.inv_mem ha)
    have hm2 : a * b * a⁻¹ * b⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
    have hazb : a * zb = zb * a := (hzb a ha).symm
    rw [e1, hconj a ha, hconj b hb]
    calc za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹
        = (za * (a * zb * b * a⁻¹) * za⁻¹) * (zb * b)⁻¹ := by group
      _ = (a * zb * b * a⁻¹) * (zb * b)⁻¹ := by rw [hconjc za hza _ hm1]
      _ = (zb * a * b * a⁻¹) * (zb * b)⁻¹ := by rw [hazb]
      _ = zb * (a * b * a⁻¹ * b⁻¹) * zb⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := hconjc zb hzb _ hm2
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm a ha b hb
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ * x = (x * (a * b * a⁻¹ * b⁻¹) * x⁻¹) * x := by rw [h]
      _ = x * (a * b * a⁻¹ * b⁻¹) := by group
  intro l hl
  have h1 : l ∈ Subgroup.centralizer {x} := hle (hperf.symm ▸ hl)
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1

theorem le_or_le_centralizer {Γ L H : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) (hHΓ : H ≤ Γ)
    (hLH : L ≤ Subgroup.normalizer (H : Set G)) (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    L ≤ H ∨ H ≤ Γ ⊓ Subgroup.centralizer (L : Set G) := by
  have hN : (H.subgroupOf L).Normal := by
    constructor
    intro n hn l
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hLH l.2) n).mp hn
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (H.subgroupOf L) with
    h | h
  · right
    intro x hx
    refine ⟨hHΓ hx, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
    have hc : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ L ∧
        ∀ m ∈ L, (l * x * l⁻¹ * x⁻¹) * m = m * (l * x * l⁻¹ * x⁻¹) := by
      intro l hl
      have h1 : l * x * l⁻¹ * x⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hHL hx) l⁻¹).mp (L.inv_mem hl)
        rw [show l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) by group]
        exact L.mul_mem hl this
      have h2 : l * x * l⁻¹ * x⁻¹ ∈ H :=
        H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLH hl) x).mp hx) (H.inv_mem hx)
      have h3 : (⟨_, h1⟩ : ↥L) ∈ H.subgroupOf L := h2
      have h4 := Subgroup.mem_center_iff.mp (h h3)
      refine ⟨h1, fun m hm => ?_⟩
      have := h4 ⟨m, hm⟩
      exact (congrArg Subtype.val this).symm
    exact commute_of_commutator_mem_center hperf hc l hl
  · left
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this

theorem centralizer_le_of_two_quotient [Finite G] {Γ L T₀ : Subgroup G} (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hT₀Γ : T₀ ≤ Γ) (hT₀ : IsPGroup 2 T₀) (hΓ : Γ = L ⊔ T₀)
    (hO2 : pCoreOf 2 Γ = ⊥) : Γ ⊓ Subgroup.centralizer (L : Set G) ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := Γ ⊓ Subgroup.centralizer (L : Set G) with hD
  set L' := L.subgroupOf Γ with hL'
  set q : ↥Γ →* ↥Γ ⧸ L' := QuotientGroup.mk' L' with hq
  have hT₀' : IsPGroup 2 (T₀.subgroupOf Γ) :=
    hT₀.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀Γ).symm
  have hqs : Function.Surjective ((q.comp (T₀.subgroupOf Γ).subtype)) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L' c
    obtain ⟨l, hl, t, ht, hlt⟩ := LRed5.exists_mul_of_mem_sup_of_le_normalizer hn hLΓ hT₀Γ
      (show (g : G) ∈ L ⊔ T₀ by rw [← hΓ]; exact g.2)
    refine ⟨⟨⟨t, hT₀Γ ht⟩, ht⟩, ?_⟩
    have hg : g = ⟨l, hLΓ hl⟩ * ⟨t, hT₀Γ ht⟩ := Subtype.ext hlt.symm
    show q ⟨t, hT₀Γ ht⟩ = q g
    rw [hg, map_mul, show q ⟨l, hLΓ hl⟩ = 1 from (QuotientGroup.eq_one_iff _).2 hl, one_mul]
  have hQ2 : IsPGroup 2 (↥Γ ⧸ L') := hT₀'.of_surjective _ hqs
  have hDΓ : D ≤ Γ := inf_le_left
  have hDn : (D.subgroupOf Γ).Normal := by
    constructor
    intro n hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hn' ⊢
    obtain ⟨hnΓ, hnC⟩ := hn'
    refine ⟨Γ.mul_mem (Γ.mul_mem g.2 hnΓ) (Γ.inv_mem g.2),
      Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : (g : G)⁻¹ * l * g ∈ L := by
      have := Subgroup.mem_subgroupOf.1
        (hn.conj_mem ⟨l, hLΓ hl⟩ (Subgroup.mem_subgroupOf.2 hl) g⁻¹)
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 hnC _ hl'
    calc l * ((g : G) * (n : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * l * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * l * (g : G))) * (g : G)⁻¹ := by rw [h2]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * l := by group
  set f : ↥D →* ↥Γ ⧸ L' := q.comp (Subgroup.inclusion hDΓ) with hf
  have hker : f.ker ≤ Subgroup.center ↥D := by
    intro d hd
    have h1 : (Subgroup.inclusion hDΓ d) ∈ L' := (QuotientGroup.eq_one_iff _).1 hd
    have hdL : (d : G) ∈ L := h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 y.2.2 _ hdL).symm
  have hrange : IsPGroup 2 f.range := hQ2.to_subgroup _
  have : Group.IsNilpotent f.range := hrange.isNilpotent
  have : Group.IsNilpotent ↥D := by
    have hk : f.rangeRestrict.ker ≤ Subgroup.center ↥D := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    exact Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict hk
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥D))
  have hPchar : (P : Subgroup ↥D).Characteristic := Sylow.characteristic_of_normal P inferInstance
  set P' : Subgroup G := (P : Subgroup ↥D).map D.subtype with hP'
  have hP'D : P' ≤ D := Subgroup.map_subtype_le _
  have hP'n : Γ ≤ Subgroup.normalizer (P' : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hDnorm : ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
      intro x hx
      have := Subgroup.mem_subgroupOf.1 (hDn.conj_mem ⟨x, hDΓ hx⟩ (Subgroup.mem_subgroupOf.2 hx)
        ⟨g, hg⟩)
      simpa using this
    have hDnorm' : ∀ x ∈ D, g⁻¹ * x * g ∈ D := by
      intro x hx
      have := hDnorm x hx
      have := Subgroup.mem_subgroupOf.1 (hDn.conj_mem ⟨x, hDΓ hx⟩ (Subgroup.mem_subgroupOf.2 hx)
        ⟨g⁻¹, Γ.inv_mem hg⟩)
      simpa using this
    let φ : ↥D ≃* ↥D :=
      { toFun := fun x => ⟨g * x * g⁻¹, hDnorm x x.2⟩
        invFun := fun x => ⟨g⁻¹ * x * g, hDnorm' x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    have hφ : (P : Subgroup ↥D).comap φ.toMonoidHom = P := hPchar.fixed φ
    have hmemφ : ∀ y : ↥D, φ y ∈ (P : Subgroup ↥D) ↔ y ∈ (P : Subgroup ↥D) := by
      intro y
      have : y ∈ (P : Subgroup ↥D).comap φ.toMonoidHom ↔ φ y ∈ (P : Subgroup ↥D) := Iff.rfl
      rw [← this, hφ]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ y, (hmemφ y).2 hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : (y : G) = g * x * g⁻¹ := hyx
      have hxD : x ∈ D := by
        have := hDnorm' _ y.2
        rw [hyx'] at this
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      have hyφ : y = φ ⟨x, hxD⟩ := Subtype.ext hyx'
      exact (hmemφ ⟨x, hxD⟩).1 (hyφ ▸ hy)
  have hP'2 : IsPGroup 2 P' :=
    (P.isPGroup').of_equiv ((P : Subgroup ↥D).equivMapOfInjective _ D.subtype_injective)
  have hP'Γ : P' ≤ Γ := hP'D.trans hDΓ
  have hP'le : P' ≤ pCoreOf 2 Γ := le_pCoreOf_of_le_normalizer 2 hP'Γ hP'n hP'2
  rw [hO2, le_bot_iff] at hP'le
  have hPbot : (P : Subgroup ↥D) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : (y : G) ∈ P' := ⟨y, hy, rfl⟩
    rw [hP'le, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hDodd : ¬ 2 ∣ Nat.card ↥D := by
    intro h2
    have := P.not_dvd_index
    rw [hPbot, Subgroup.index_bot] at this
    exact this h2
  intro d hd
  have hfd : f ⟨d, hd⟩ = 1 := by
    have h1 : orderOf (f ⟨d, hd⟩) ∣ Nat.card ↥D :=
      (orderOf_map_dvd f ⟨d, hd⟩).trans (orderOf_dvd_natCard _)
    obtain ⟨k, hk⟩ := hQ2 (f ⟨d, hd⟩)
    have h2 : orderOf (f ⟨d, hd⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (f ⟨d, hd⟩) = 1 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 h2 with ⟨j, -, hj⟩
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [hj, pow_succ] at h1
        exact hDodd (dvd_trans (dvd_mul_left 2 _) h1)
    exact orderOf_eq_one_iff.mp h3
  have := (QuotientGroup.eq_one_iff _).1 hfd
  exact this

end Dichotomy

theorem not_isSolvable_of_isQuasisimple' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hsol
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  obtain ⟨n, hn⟩ := hsol.solvable
  have htop : ∀ m, derivedSeries Q m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact hperf.commutator_eq_top
  rw [htop] at hn
  have hall : ∀ x : Q, x = 1 := fun x => Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top x)
  apply hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [hall a, hall b]

section B56

variable {V : Type} [CommGroup V]

theorem eq_bot_of_isPGroup_of_le_odd [Finite V] {X C : Subgroup (MulAut V)} (hX : IsPGroup 2 X)
    (hXC : X ≤ C) (hC : Odd (Nat.card ↥C)) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  have hdvd : Nat.card ↥X ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hXC
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exfalso
    rw [hk, pow_succ] at hdvd
    exact (Nat.not_even_iff_odd.mpr hC) (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_left 2 _) hdvd))

theorem b53Hyp_ffJ' [Finite V] {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ)
    (hq : CFSG.IsQuasisimple ↥L)
    (hC : Odd (Nat.card ↥(Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)))))
    (hLΓ : L ≤ Γ) (hn : (L.subgroupOf Γ).Normal)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    L ≤ ffJ Γ ∧ B53Hyp (ffJ Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΓL := FFL.le_normalizer_of_normal hLΓ hn
  have hJΓ := FFL.ffJ_le Γ
  have hLJ : L ≤ ffJ Γ := by
    rcases le_or_le_centralizer hq hJΓ (hLΓ.trans (FFL.le_normalizer_ffJ Γ)) (hJΓ.trans hΓL) with
      h | h
    · exact h
    · exfalso
      obtain ⟨A, hA⟩ := hoff
      have hA2 : IsPGroup 2 A := IsElemAbelian2.isPGroup hA.2.2.1
      exact hA.2.1 (eq_bot_of_isPGroup_of_le_odd hA2 ((B19.le_ffJ hA).trans h) hC)
  refine ⟨hLJ, ?_, (FFL.ffJ_ffJ Γ).symm, ?_⟩
  · have hP := pCoreOf_le 2 (ffJ Γ)
    rcases le_or_le_centralizer hq (hP.trans hJΓ) (hLJ.trans (le_normalizer_pCoreOf 2 _))
      ((hP.trans hJΓ).trans hΓL) with h | h
    · exfalso
      have hL2 : IsPGroup 2 ↥L := (pCoreOf_isPGroup 2 (ffJ Γ)).to_le h
      have : Group.IsNilpotent ↥L := hL2.isNilpotent
      exact not_isSolvable_of_isQuasisimple' hq inferInstance
    · exact eq_bot_of_isPGroup_of_le_odd (pCoreOf_isPGroup 2 _) h hC
  · obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := G64.isQuotientOfSQTKCat_of_le hJΓ hQ
    exact ⟨Y, inferInstance, inferInstance, N, inferInstance, G64.sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

theorem even_card_statedSL_two {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : Even (Nat.card ↥(StatedSL 2 K)) := by
  have := Fintype.ofFinite K
  rw [FFL.card_statedSL_two, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right _

theorem even_card_statedSL_three {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) : Even (Nat.card ↥(StatedSL 3 K)) := by
  have := Fintype.ofFinite K
  rw [FFL.card_statedSL_three, ← Nat.card_eq_fintype_card, hK, mul_assoc]
  refine Even.mul_right ?_ _
  rw [← pow_mul]
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem even_card_of_factorList [Finite V] {H : Subgroup (MulAut V)} (h : B56FactorList ↥H) :
    Even (Nat.card ↥H) := by
  rcases h with ⟨n, K, _, _, hn, hK, he⟩ | he | ⟨m, K, _, _, hm, -, hK, he⟩
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact even_card_statedSL_two hn hK
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact even_card_statedSL_three hm hK

theorem false_of_case3' [Finite V] {G L : Subgroup (MulAut V)} (hL : L ≠ ⊥)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ Odd (Nat.card ↥H))
    (h : B56Case3 G) : False := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, h₁, h₂, -⟩ := h
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hn₁ : G ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
    hsup.symm.le.trans (FFL.sup_le_normalizer hcomm)
  have hn₂ : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
    hsup.symm.le.trans ((sup_comm G₁ G₂).le.trans (FFL.sup_le_normalizer hcomm'))
  have he₁ := even_card_of_factorList h₁
  have he₂ := even_card_of_factorList h₂
  rcases hdich G₁ (le_sup_left.trans hsup.le) hn₁ with hL₁ | hc₁
  · rcases hdich G₂ (le_sup_right.trans hsup.le) hn₂ with hL₂ | hc₂
    · exact hL (le_bot_iff.mp (hinf ▸ le_inf hL₁ hL₂))
    · exact (Nat.not_even_iff_odd.mpr hc₂) he₂
  · exact (Nat.not_even_iff_odd.mpr hc₁) he₁

theorem false_of_case4' [Finite V] {G L : Subgroup (MulAut V)} (hL : 360 < Nat.card ↥L)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ Odd (Nat.card ↥H))
    (h : B56Case4 G) : False := by
  obtain ⟨G₁, G₂, t, hG, -, hcomm, ⟨e⟩, -, -, -, -, -, -, ht₁, -, -, -⟩ := h
  have hG₁ : G₁ ≤ G := (le_sup_left.trans le_sup_left).trans hG.symm.le
  have hn : G ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
    rw [hG]
    refine sup_le (sup_le Subgroup.le_normalizer (le_sup_right.trans
      (FFL.sup_le_normalizer hcomm))) ?_
    rw [Subgroup.zpowers_le]
    exact ht₁
  have h360 : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  rcases hdich G₁ hG₁ hn with hL₁ | hc
  · have := Subgroup.card_le_of_le hL₁
    omega
  · rw [h360] at hc
    exact absurd hc (by decide)

theorem false_of_case5' [Finite V] {G L : Subgroup (MulAut V)} (hL : 360 < Nat.card ↥L)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ Odd (Nat.card ↥H))
    (h : B56Case5 G) : False := by
  obtain ⟨G₁, G₂, hsup, -, hcomm, -, ⟨e₁⟩, -, -, -⟩ := h
  have hn₁ : G ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
    hsup.symm.le.trans (FFL.sup_le_normalizer hcomm)
  have h168 : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e₁.toEquiv, FFL.card_statedSL_three, ← Nat.card_eq_fintype_card,
      Nat.card_zmod]
    norm_num
  rcases hdich G₁ (le_sup_left.trans hsup.le) hn₁ with hL₁ | hc
  · have := Subgroup.card_le_of_le hL₁
    omega
  · rw [h168] at hc
    exact absurd hc (by decide)

theorem false_of_ff_center (h56 : AsB56) [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hq : CFSG.IsQuasisimple ↥L)
    (hC : Odd (Nat.card ↥(Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)))))
    (hL360 : 360 < Nat.card ↥L) (hlist : ¬ B56QuasisimpleList ↥L)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) : False := by
  obtain ⟨hLJ, hB53⟩ := b53Hyp_ffJ' hQ hq hC hLΓ hn hoff
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := FFL.nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hG1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLJ))
  have hΓL := FFL.le_normalizer_of_normal hLΓ hn
  have hdich : ∀ H ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (H : Set (MulAut V)) →
      L ≤ H ∨ Odd (Nat.card ↥H) := by
    intro H hH hGH
    rcases le_or_le_centralizer hq (hH.trans (FFL.ffJ_le Γ)) (hLJ.trans hGH)
      ((hH.trans (FFL.ffJ_le Γ)).trans hΓL) with h | h
    · exact Or.inl h
    · exact Or.inr (Odd.of_dvd_nat hC (Subgroup.card_dvd_of_le h))
  have hcard6 : 6 < Nat.card ↥L := by omega
  rcases h56 V hV (ffJ Γ) hG1 hB53 with ⟨hqF, -, hlF⟩ | h2 | h3 | h4 | h5
  ·
    have hLn : ∀ x ∈ ffJ Γ, ∀ k ∈ L, x * k * x⁻¹ ∈ L := fun x hx k hk =>
      (Subgroup.mem_normalizer_iff.mp (hΓL (FFL.ffJ_le Γ hx)) k).mp hk
    have hFL : quasithinGenFitting (ffJ Γ) = L :=
      InternalSec.eq_of_le_quasisimple hLJ hLn hq hqF
    rw [hFL] at hlF
    exact hlist hlF
  · exact FFL.false_of_case2 hLJ hcard6 h2
  · exact false_of_case3' hL1 hdich h3
  · exact false_of_case4' hL360 hdich h4
  · exact false_of_case5' hL360 hdich h5

end B56

end CFSG.Quasithin.H13.KGFFZ
