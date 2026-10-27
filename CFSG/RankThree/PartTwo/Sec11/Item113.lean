module

public import CFSG.RankThree.PartTwo.Sec11.Omega
public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec10.Steps
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec12.Item123
public import CFSG.RankThree.PartTwo.Sec13.Naturality
public import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Lemmas

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isPGroup_of_le_centralizer (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ Subgroup.centralizer ({c} : Set G)) :
    ∀ L ∈ thetaComponentsAt 3 c, Q ≤ Subgroup.normalizer (L : Set G) := by
  have := hG.isSimpleGroup
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hCtop : C ≠ ⊤ := by
    intro hC
    have hcz : c ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hC ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0, Subgroup.mem_bot] at hcz
      exact hc1 hcz
    · obtain ⟨x, y, hxy⟩ := hG.nonabelian
      have hx : x ∈ Subgroup.center G := h0 ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.mp hx y).symm
  have hC4 : SectionFourHyp C := hG.sectionFourHyp hCtop
  have hQ' : IsPGroup 3 (Q.subgroupOf C) := hQ.comap_subtype
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcore : CFSG.pCore 3 C ≠ ⊥ := by
    set c' : C := ⟨c, hcC⟩
    have hc'3 : orderOf c' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hZn : (Subgroup.zpowers c').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hgc : g * c' = c' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * c' ^ k * g⁻¹ = c' ^ k := by
        rw [(Commute.zpow_right hgc k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers c' k
    have hZ3 : IsPGroup 3 (Subgroup.zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
    have hZle : Subgroup.zpowers c' ≤ CFSG.pCore 3 C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have hc'1 : c' = 1 := by
      have := hZle (Subgroup.mem_zpowers c')
      rwa [hbot, Subgroup.mem_bot] at this
    exact hc1 (congrArg Subtype.val hc'1)
  intro L hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hN := Sec6.item45_of_item4_5 h45 C hC4 (Q.subgroupOf C) hQ' (Or.inl hcore) L' hL'
  intro q hq
  have hqN : (⟨q, hQC hq⟩ : C) ∈ Subgroup.normalizer (L' : Set C) :=
    hN (Subgroup.mem_subgroupOf.mpr hq)
  rw [Subgroup.mem_normalizer_iff] at hqN ⊢
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨_, (hqN x').mp hx', rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : G) = q * x * q⁻¹ := hyx
    have hxC : x ∈ C := by
      have hx' : x = q⁻¹ * (y : G) * q := by
        rw [hyx']
        group
      rw [hx']
      exact C.mul_mem (C.mul_mem (C.inv_mem (hQC hq)) y.2) (hQC hq)
    refine ⟨⟨x, hxC⟩, (hqN ⟨x, hxC⟩).mpr ?_, rfl⟩
    have : (⟨q, hQC hq⟩ : C) * ⟨x, hxC⟩ * (⟨q, hQC hq⟩ : C)⁻¹ = y := Subtype.ext hyx'.symm
    rw [this]
    exact hy

omit [Finite G] in
theorem le_centralizer_of_le_normalizer_zpowers {c : G} (hc : orderOf c = 3) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  intro q hq
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hk' : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : q * c * q⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (hQN hq) c).mp (Subgroup.mem_zpowers c)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Sec12.commute_of_conj_mem_zpowers hc h1 hk'

theorem mem_sectionCentralizer_of_mem_thetaQuotCentralizer {A L : Subgroup G} {z : G}
    (hzA : z ∈ A) (hz : z ∈ Sec4.thetaQuotCentralizer L) :
    z ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
  obtain ⟨-, hzl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hz
  refine ⟨hzA, fun x hx => ?_⟩
  have h1 := hzl x hx
  have h2 : (z * x * z⁻¹ * x⁻¹) = x * (x⁻¹ * (z * x * z⁻¹)) * x⁻¹ := by group
  rw [h2]
  exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hx) _).mp h1

theorem mem_theta_of_mem_thetaQuotCentralizer {L : Subgroup G}
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {l : G} (hlL : l ∈ L)
    (hl : l ∈ Sec4.thetaQuotCentralizer L) : (⟨l, hlL⟩ : L) ∈ aschbacherSolvableCore 3 L := by
  obtain ⟨-, hll⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hl
  set u : L ⧸ aschbacherSolvableCore 3 L := ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
    with hu
  have hcen : u ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨t, ht, hteq⟩ := hll x x.2
      have hteq' : (t : G) = (x : G)⁻¹ * (l * x * l⁻¹) := hteq
      have h1 : (x⁻¹ * (⟨l, hlL⟩ * x * (⟨l, hlL⟩ : L)⁻¹) : L) = t :=
        Subtype.ext (by rw [hteq']; simp)
      have h2 : ((x⁻¹ * (⟨l, hlL⟩ * x * (⟨l, hlL⟩ : L)⁻¹) : L) :
          L ⧸ aschbacherSolvableCore 3 L) = 1 := by
        rw [h1, QuotientGroup.eq_one_iff]
        exact ht
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, ← hu] at h2
      have h3 : (x : L ⧸ aschbacherSolvableCore 3 L) = u * x * u⁻¹ := inv_mul_eq_one.mp h2
      calc (x : L ⧸ aschbacherSolvableCore 3 L) * u = u * x * u⁻¹ * u := by rw [← h3]
        _ = u * x := by group
  rw [hZ, Subgroup.mem_bot, hu, QuotientGroup.eq_one_iff] at hcen
  exact hcen

theorem eq_one_of_mem_theta_of_pow_eq_one {L : Subgroup G} {l : L}
    (hl : l ∈ aschbacherSolvableCore 3 L) {k : ℕ} (hk : l ^ 3 ^ k = 1) : l = 1 := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have h1 : orderOf l ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf l ∣ Nat.card (aschbacherSolvableCore 3 L) := by
    have := Subgroup.orderOf_dvd_natCard _ hl
    exact this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem commutator_mem_thetaQuotCentralizer {L : Subgroup G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G)) {t t' : G}
    (ht : t ∈ Subgroup.closure {y | y ∈ Q ∧ y ^ 3 = 1})
    (ht' : t' ∈ Subgroup.closure {y | y ∈ Q ∧ y ^ 3 = 1}) :
    t * t' * t⁻¹ * t'⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hρ
  set S : Set G := {y | y ∈ Q ∧ y ^ 3 = 1} with hS
  set SN : Set N := N.subtype ⁻¹' S with hSN
  have hcl : Subgroup.closure S = (Subgroup.closure SN).map N.subtype := by
    rw [MonoidHom.map_closure, hSN, Set.image_preimage_eq_of_subset]
    rintro y ⟨hyQ, -⟩
    exact ⟨⟨y, hQN hyQ⟩, rfl⟩
  set P : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := (Q.subgroupOf N).map ρ with hP
  have hP3 : IsPGroup 3 P := (hQ.comap_subtype (K := N)).map ρ
  have hcomm : (ρ '' SN).Pairwise Commute := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ -
    have hyP : ρ y ∈ P := ⟨y, Subgroup.mem_subgroupOf.mpr hy.1, rfl⟩
    have hy'P : ρ y' ∈ P := ⟨y', Subgroup.mem_subgroupOf.mpr hy'.1, rfl⟩
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hy.2)
    have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy'.2)
    exact commute_of_pow_three_eq_one_of_isList1016 hL hP3 hyP hy'P
      (by rw [← map_pow, hy3, map_one]) (by rw [← map_pow, hy'3, map_one])
  rw [hcl] at ht ht'
  obtain ⟨tN, htN, rfl⟩ := ht
  obtain ⟨tN', htN', rfl⟩ := ht'
  have hρt : ρ tN ∈ Subgroup.closure (ρ '' SN) := by
    rw [← MonoidHom.map_closure]
    exact ⟨tN, htN, rfl⟩
  have hρt' : ρ tN' ∈ Subgroup.closure (ρ '' SN) := by
    rw [← MonoidHom.map_closure]
    exact ⟨tN', htN', rfl⟩
  have h1 : ρ tN * ρ tN' = ρ tN' * ρ tN :=
    congrArg Subtype.val ((Subgroup.isMulCommutative_closure hcomm).is_comm.comm ⟨_, hρt⟩
      ⟨_, hρt'⟩)
  show _ ∈ ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom).ker.map N.subtype
  refine ⟨tN * tN' * tN⁻¹ * tN'⁻¹, ?_, by simp⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  change ρ (tN * tN' * tN⁻¹ * tN'⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
  group

theorem isList1016_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X)
    (h : Sec9.IsList1016 X) : Sec9.IsList1016 Y := by
  rcases h with ⟨p, e', hp, hp3, he, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, hL⟩
  · exact Or.inl ⟨p, e', hp, hp3, he, ⟨e.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans φ⟩⟩)
  · refine Or.inr (Or.inr ⟨n, hn, ?_⟩)
    rcases hL with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact Or.inl ⟨hq, ⟨e.trans φ⟩⟩
    · exact Or.inr ⟨hq, ⟨e.trans φ⟩⟩

end Lemmas

@[expose] def Item111First : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ g : G,
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ A →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≠ Subgroup.zpowers c →
        c ∉ Sec4.thetaQuotCentralizer (L.map (MulAut.conj g).toMonoidHom)

theorem item113_of_item111First (h97 : Sec9.Item97) (h112 : Item112) (h45 : Sec4.Item4_5)
    (h111 : Item111First) : Item113 := by
  intro G _ _ A c L a R Y h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have hc1 := h.ne_one
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hΩ : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A := fun x hx3 hx =>
    Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
  have hcAL : ∀ z ∈ A, z ∈ Sec4.thetaQuotCentralizer L → z ∈ Subgroup.zpowers c := by
    intro z hzA hz
    have h1 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer hzA hz
    rw [h.sectionCentralizer_eq] at h1
    exact h1
  obtain ⟨d, hdL, -, -⟩ := Sec10.exists_inf_eq_zpowers h97 h.toHyp91
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  obtain ⟨g, hgle, hgne⟩ := h112 G A c L a R Y h d hdL
  set b := g * c * g⁻¹ with hb
  have hbcd : b ∈ Subgroup.closure ({c, d} : Set G) :=
    hgle ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact hdAL.1
  obtain ⟨Rs, hRs⟩ := h.isSylowOf
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [← hRs]
    exact Subgroup.map_subtype_le _
  have hR3 : IsPGroup 3 R := by
    rw [← hRs]
    exact Rs.isPGroup'.map _
  have hAR : A ≤ R := by
    set HW := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) with hHW
    obtain ⟨Ws, hWs⟩ := h.isSylowOf_inf
    have hAHW : A ≤ HW := by
      refine le_inf (fun x hx => ?_) (fun x hx => Subgroup.le_normalizer hx)
      have hxc : x * c = c * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcA⟩)
      have hconj : ∀ k : ℤ, x * c ^ k * x⁻¹ = c ^ k := fun k => by
        rw [(Commute.zpow_right hxc k).eq, mul_inv_cancel_right]
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [hconj k]
        exact Subgroup.zpow_mem_zpowers c k
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hyk : y = c ^ k := by
          calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
            _ = x⁻¹ * c ^ k * x := by rw [← hk]
            _ = c ^ k := by
              rw [((Commute.zpow_right hxc k).inv_left).eq, inv_mul_cancel_right]
        rw [hyk]
        exact Subgroup.zpow_mem_zpowers c k
    have hAn : (A.subgroupOf HW).Normal := by
      constructor
      intro n hn w
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (w.2.2) _).mp hn
    have hA3 : IsPGroup 3 (A.subgroupOf HW) := by
      have hA3' : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
      exact hA3'.comap_subtype
    have h1 := hA3.le_sylow_of_normal Ws
    intro x hx
    have h2 : (⟨x, hAHW hx⟩ : HW) ∈ (Ws : Subgroup HW) := h1 (Subgroup.mem_subgroupOf.mpr hx)
    have h3 : x ∈ R ⊓ Subgroup.normalizer (A : Set G) := by
      rw [← hWs]
      exact ⟨⟨x, hAHW hx⟩, h2, rfl⟩
    exact h3.1
  have hRC := le_centralizer_of_le_normalizer_zpowers hcord hR3 hRH
  have hRN : R ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 hc1 hR3 hRC L
      h.mem_thetaComponentsAt
  set S : Set G := {y | y ∈ R ∧ y ^ 3 = 1} with hS
  set T := Subgroup.closure S with hT
  have hTR : T ≤ R := (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hAT : A ≤ T := fun x hx => Subgroup.subset_closure ⟨hAR hx, hexp x hx⟩
  have hT3 : IsPGroup 3 T := hR3.to_le hTR
  have hTL : ∀ t ∈ T, ∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ Sec4.thetaQuotCentralizer L :=
    fun t ht t' ht' => commutator_mem_thetaQuotCentralizer h.isList1016 hR3 hRN ht ht'
  have hZ := center_eq_bot_of_isList1016 h.isList1016
  have hdT' : d ∈ T := hAT hdAL.1
  have hdT : ∀ t ∈ T, t * d = d * t := by
    intro t ht
    have h1 := hTL t ht d hdT'
    have hlL : t * d * t⁻¹ * d⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRN (hTR ht)) d).mp hdAL.2) (L.inv_mem hdAL.2)
    have h2 := mem_theta_of_mem_thetaQuotCentralizer hZ hlL h1
    obtain ⟨k, hk⟩ := hT3 ⟨_, T.mul_mem (T.mul_mem (T.mul_mem ht hdT') (T.inv_mem ht))
      (T.inv_mem hdT')⟩
    have h3 : (⟨t * d * t⁻¹ * d⁻¹, hlL⟩ : L) = 1 :=
      eq_one_of_mem_theta_of_pow_eq_one h2 (k := k)
        (Subtype.ext (by simpa using congrArg Subtype.val hk))
    have h4 : t * d * t⁻¹ * d⁻¹ = 1 := congrArg Subtype.val h3
    calc t * d = t * d * t⁻¹ * d⁻¹ * (d * t) := by group
      _ = d * t := by rw [h4, one_mul]
  have hcT : ∀ t ∈ T, t * c = c * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC (hTR ht))
  have hbT : ∀ t ∈ T, t * b = b * t := by
    have hcl : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rcases hy with rfl | rfl
      · exact hcT
      · exact hdT
    exact Subgroup.mem_centralizer_iff.mp (hcl hbcd)
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hLgb : Lg ∈ thetaComponentsAt 3 b := map_mem_thetaComponentsAt (MulAut.conj g)
    h.mem_thetaComponentsAt
  have hb3 : b ^ 3 = 1 := by
    rw [hb, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hc1
    calc c = g⁻¹ * b * g := by rw [hb]; group
      _ = 1 := by rw [hb1]; group
  have hTb : T ≤ Subgroup.centralizer ({b} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hbT t ht)
  have hTN : T ≤ Subgroup.normalizer (Lg : Set G) :=
    le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hT3 hTb Lg hLgb
  have hLgList : Sec9.IsList1016 (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
    isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm h.isList1016
  have hTT : ∀ t ∈ T, t ∈ Subgroup.closure {y | y ∈ T ∧ y ^ 3 = 1} := fun t ht =>
    Subgroup.closure_mono (show S ⊆ {y | y ∈ T ∧ y ^ 3 = 1} from fun y hy =>
      ⟨Subgroup.subset_closure hy, hy.2⟩) ht
  have hTLg : ∀ t ∈ T, ∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ Sec4.thetaQuotCentralizer Lg :=
    fun t ht t' ht' => commutator_mem_thetaQuotCentralizer hLgList hT3 hTN (hTT t ht) (hTT t' ht')
  have hTab : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t := by
    by_contra hna
    push Not at hna
    obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := hna
    have hTnil : Group.IsNilpotent T := hT3.isNilpotent
    have hcomm1 : commutator T ≠ ⊥ := by
      intro hbot
      have hmem : ⁅(⟨t₁, ht₁⟩ : T), ⟨t₂, ht₂⟩⁆ ∈ commutator T :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact h12 (congrArg Subtype.val hmem)
    have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hcomm1
    set K : Subgroup T := commutator T ⊓ Subgroup.center T with hKdef
    have hK3 : IsPGroup 3 K := hT3.to_subgroup K
    have hKnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
    have h3K : 3 ∣ Nat.card K := by
      obtain ⟨n, hn⟩ := hK3.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact (Finite.one_lt_card_iff_nontrivial.mpr hKnt).ne' hn
      rw [hn]
      exact dvd_pow_self 3 hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
    set w : G := ((z : T) : G) with hw
    have hz3 : z ^ 3 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    have hw3 : w ^ 3 = 1 := by
      have := congrArg (fun u : K => ((u : T) : G)) hz3
      simpa [hw] using this
    have hw1 : w ≠ 1 := by
      intro hw1
      have hz1 : z = 1 := Subtype.ext (Subtype.ext hw1)
      rw [hz1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hwZ : ∀ t ∈ T, t * w = w * t := by
      intro t ht
      have := Subgroup.mem_center_iff.mp z.2.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    have hwA : w ∈ A := hΩ w hw3 fun y hy => hwZ y (hAT hy)
    have hTTL : commutator T ≤ (Sec4.thetaQuotCentralizer L).subgroupOf T := by
      rw [commutator_def, Subgroup.commutator_le]
      rintro t₁ - t₂ -
      rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      simpa using hTL t₁ t₁.2 t₂ t₂.2
    have hTTLg : commutator T ≤ (Sec4.thetaQuotCentralizer Lg).subgroupOf T := by
      rw [commutator_def, Subgroup.commutator_le]
      rintro t₁ - t₂ -
      rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      simpa using hTLg t₁ t₁.2 t₂ t₂.2
    have hwc : w ∈ Subgroup.zpowers c :=
      hcAL w hwA (Subgroup.mem_subgroupOf.mp (hTTL z.2.1))
    have heq : Subgroup.zpowers w = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hcord, orderOf_eq_prime hw3 hw1])
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w ^ k = c :=
      Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers c)
    have hzk : (z : T) ^ k ∈ commutator T := Subgroup.zpow_mem _ z.2.1 k
    have hcLg := Subgroup.mem_subgroupOf.mp (hTTLg hzk)
    rw [Subgroup.coe_zpow, ← hw, hk] at hcLg
    exact h111 G A c L a R Y h g (hgle.trans hcdA) hgne hcLg
  have hTA : T ≤ A := (Subgroup.closure_le _).mpr fun y hy =>
    hΩ y hy.2 fun x hx => (hTab x (hAT hx) y (Subgroup.subset_closure hy))
  refine ⟨le_antisymm hAT hTA, ?_⟩
  have hcR : c ∈ R := hAR hcA
  have hcyc := CFSG.RankThree.Coprime.isCyclic_of_forall_pow_eq_one_mem (P := R) (by norm_num)
    hR3 ((Sec4.thetaQuotCentralizer L).subgroupOf R) ((Subgroup.zpowers c).subgroupOf R)
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.zpowers_le.mpr hcR)).toEquiv, Nat.card_zpowers, hcord])
    (by
      intro x hx hx3
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hx3' : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
      exact hcAL _ (hTA (Subgroup.subset_closure ⟨x.2, hx3'⟩)) hx)
  rw [← Subgroup.inf_subgroupOf_left] at hcyc
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : R ⊓ Sec4.thetaQuotCentralizer L ≤ R)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : R ⊓ Sec4.thetaQuotCentralizer L ≤ R)).surjective

end CFSG.RankThree.PartTwo.Sec11
