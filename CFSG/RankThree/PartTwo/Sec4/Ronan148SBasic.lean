module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof
public import CFSG.RankThree.PartTwo.Sec13.Item136E

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429

@[expose] def IsType425 (X : Type) [Group X] : Prop :=
  IsSLThreePi X ∨ IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
    IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)) ∨
    IsExtOf X Blueprint.NativeSporadic.M22 (Multiplicative (ZMod 3))

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem isSLThreePi_congr (e : X ≃* Y) (h : IsSLThreePi X) : IsSLThreePi Y := by
  obtain ⟨q, F, _, _, ⟨hF, hq, ⟨f⟩⟩ | ⟨hF, hq, ⟨f⟩⟩⟩ := h
  · exact ⟨q, F, inferInstance, inferInstance, Or.inl ⟨hF, hq, ⟨e.symm.trans f⟩⟩⟩
  · exact ⟨q, F, inferInstance, inferInstance, Or.inr ⟨hF, hq, ⟨e.symm.trans f⟩⟩⟩

theorem isExtOf_congr {S B : Type*} [Group S] [Group B] (e : X ≃* Y) (h : IsExtOf X S B) :
    IsExtOf Y S B := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := h
  haveI : (N.map (e : X →* Y)).Normal := hN.map _ e.surjective
  refine ⟨N.map (e : X →* Y), inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · exact (N.equivMapOfInjective (e : X →* Y) e.injective).symm.trans eN
  · exact (QuotientGroup.congr N (N.map (e : X →* Y)) e rfl).symm.trans eQ

theorem isType425_congr (e : X ≃* Y) (h : IsType425 X) : IsType425 Y := by
  rcases h with h | h | h | h
  · exact Or.inl (isSLThreePi_congr e h)
  · exact Or.inr (Or.inl (isExtOf_congr e h))
  · exact Or.inr (Or.inr (Or.inl (isExtOf_congr e h)))
  · exact Or.inr (Or.inr (Or.inr (isExtOf_congr e h)))

theorem isType425_theta_congr [Finite X] (e : X ≃* Y)
    (h : IsType425 (X ⧸ aschbacherSolvableCore 3 X)) :
    IsType425 (Y ⧸ aschbacherSolvableCore 3 Y) :=
  isType425_congr (thetaQuotCongr e) h

end Transport

section Center

variable {X : Type} [Group X]

theorem center_alternatingGroup_eq_bot {n : ℕ} (hn : 4 ≤ n) :
    Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simpa using hn)

theorem card_center_of_isExtOf {Y : Type*} [Group Y] (hX : IsQuasisimple X)
    (hY : Subgroup.center Y = ⊥) (h : IsExtOf X Y (Multiplicative (ZMod 3))) :
    Nat.card (Subgroup.center X) = 3 :=
  ((isTripleCover_iff_isExtOf hX hY).mpr h).1

theorem card_center_of_isType425
    (hX : IsQuasisimple X) (h : IsType425 X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases h with h | h | h | h
  · exact Sec13.card_center_of_isSLThreePi h
  · exact card_center_of_isExtOf hX (center_alternatingGroup_eq_bot (by norm_num)) h
  · exact card_center_of_isExtOf hX (center_alternatingGroup_eq_bot (by norm_num)) h
  · exact card_center_of_isExtOf hX CFSG.Sporadic.Schreier.m22_center_eq_bot' h

theorem isQuasisimple_theta_quot [Finite X] (hX : IsQuasisimple X) :
    IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X) :=
  (CFSG.LocalCores.quasisimple_central_quotient hX _ (aschbacherSolvableCore_le_center hX)).1

end Center

structure CC425 {S : Type} [Group S] (s : S) (K : Subgroup S) : Prop where
  orderOf_eq : orderOf s = 3
  mem : s ∈ K
  le_centralizer : K ≤ Subgroup.centralizer {s}
  isQuasisimple : IsQuasisimple K
  isSubnormal : (K.subgroupOf (Subgroup.centralizer {s})).IsSubnormal
  isType : IsType425 (K ⧸ aschbacherSolvableCore 3 K)

@[expose] def NoCC425 (S : Type) [Group S] : Prop :=
  ∀ (s : S) (K : Subgroup S), ¬ CC425 s K

@[expose] def NoCQ425 (S : Type) [Group S] : Prop :=
  ∀ (s : S) (K : Subgroup S), orderOf s = 3 → s ∈ K → K ≤ Subgroup.centralizer {s} →
    IsQuasisimple K → IsType425 (K ⧸ aschbacherSolvableCore 3 K) → False

theorem NoCQ425.noCC425 {S : Type} [Group S] (h : NoCQ425 S) : NoCC425 S :=
  fun s K hc => h s K hc.orderOf_eq hc.mem hc.le_centralizer hc.isQuasisimple hc.isType

section Map

variable {S T : Type} [Group S] [Group T] [Finite S]

theorem map_centralizer_singleton_equiv (e : S ≃* T) (s : S) :
    (Subgroup.centralizer ({s} : Set S)).map (e : S →* T) =
      Subgroup.centralizer ({e s} : Set T) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem CC425.map (e : S ≃* T) {s : S} {K : Subgroup S} (h : CC425 s K) :
    CC425 (e s) (K.map (e : S →* T)) := by
  haveI : Finite T := Finite.of_equiv S e.toEquiv
  have eK : K ≃* K.map (e : S →* T) := K.equivMapOfInjective _ e.injective
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq, ⟨s, h.mem, rfl⟩, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK h.isQuasisimple, ?_,
    isType425_theta_congr eK h.isType⟩
  · rw [← map_centralizer_singleton_equiv e s]
    exact Subgroup.map_mono h.le_centralizer
  ·
    set C := Subgroup.centralizer ({s} : Set S)
    have hC : C.map (e : S →* T) = Subgroup.centralizer ({e s} : Set T) :=
      map_centralizer_singleton_equiv e s
    let eC : C ≃* Subgroup.centralizer ({e s} : Set T) :=
      (C.equivMapOfInjective _ e.injective).trans (MulEquiv.subgroupCongr hC)
    have hsurj : Function.Surjective (eC : C →* Subgroup.centralizer ({e s} : Set T)) :=
      eC.surjective
    have hmap := h.isSubnormal.map hsurj
    have heq : (K.subgroupOf C).map (eC : C →* Subgroup.centralizer ({e s} : Set T)) =
        (K.map (e : S →* T)).subgroupOf (Subgroup.centralizer ({e s} : Set T)) := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
      constructor
      · rintro ⟨x, hxK, hxy⟩
        refine ⟨x, hxK, ?_⟩
        have := congrArg Subtype.val hxy
        exact this
      · rintro ⟨x, hxK, rfl⟩
        refine ⟨⟨x, h.le_centralizer hxK⟩, hxK, ?_⟩
        rfl
    rwa [heq] at hmap

theorem NoCC425.of_mulEquiv (e : S ≃* T) (h : NoCC425 T) : NoCC425 S :=
  fun s K hc => h (e s) (K.map (e : S →* T)) (hc.map e)

end Map

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem descAut_eq_conj {L : Subgroup G} {c : G} (hcL : c ∈ L) :
    descAut L ⟨c, Subgroup.le_normalizer hcL⟩ =
      MulAut.conj (((⟨c, hcL⟩ : L) : L ⧸ Subgroup.center L)) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H l =>
    rw [descAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem mk_eq_one_iff {L : Subgroup G} {c : G} (hcL : c ∈ L) :
    (((⟨c, hcL⟩ : L) : L ⧸ Subgroup.center L)) = 1 ↔ L ≤ Subgroup.centralizer {c} := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  constructor
  · intro h l hl
    have := congrArg Subtype.val (h ⟨l, hl⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  · intro h l
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h l.2))


theorem exists_cc425
    (hθ : aschbacherSolvableCore 3 G = ⊥) {A L : Subgroup G} (hA : Late.IsE27 A)
    (hL : IsComponent L) {c : G} (hcL : ¬ L ≤ Subgroup.centralizer {c})
    {K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)} (hK : IsComponent K)
    {K' : Subgroup G} (hK' : K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype)
    (htype : IsType425 (K ⧸ aschbacherSolvableCore 3 K))
    (hAZ : A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) = Subgroup.zpowers c) :
    ∃ hc : c ∈ L, K'.subgroupOf L ⊓ Subgroup.center L = ⊥ ∧
      CC425 (((⟨c, hc⟩ : L) : L ⧸ Subgroup.center L))
        ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcmem : c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) :=
    hAZ ▸ Subgroup.mem_zpowers c
  obtain ⟨hcA, hcK', hcC⟩ := hcmem
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {c} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'c : K' ≤ Subgroup.centralizer {c} := hK'M.trans inf_le_right
  have hcL' : c ∈ L := hK'L hcK'
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hcL fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  let eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have htype' : IsType425 (K' ⧸ aschbacherSolvableCore 3 K') := isType425_theta_congr eK htype
  have hZ3 : Nat.card (Subgroup.center (K' ⧸ aschbacherSolvableCore 3 K')) = 3 :=
    card_center_of_isType425 (isQuasisimple_theta_quot hK'q) htype'
  have hO3 := Sec10.Step1012ClaimKProof.pCore_center_eq_zpowers hK'c hcK' hco hZ3
  have hZL : IsPGroup 3 (Subgroup.center L) := isPGroup_center_of_isComponent hθ hL
  have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxZ⟩
    rw [Subgroup.mem_bot]
    have hxK' : (x : G) ∈ K' := hxK
    have hxC : (x : G) ∈ Subgroup.centralizer (K' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨k, hK'L hk⟩)
    set Z := K' ⊓ Subgroup.centralizer (K' : Set G) with hZdef
    have hxZ' : (x : G) ∈ Z := ⟨hxK', hxC⟩
    have hZcomm : ∀ u v : Z, u * v = v * u := fun u v =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp v.2.2 u u.2.1)
    obtain ⟨k, hk⟩ := hZL ⟨x, hxZ⟩
    have hxk : (x : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : Subgroup.center L => ((y : L) : G)) hk
      simpa using this
    have hxP : (x : G) ∈ inSubgroup (CFSG.pCore 3) Z := by
      refine ⟨⟨x, hxZ'⟩, ?_, rfl⟩
      have hN : (Subgroup.zpowers (⟨x, hxZ'⟩ : Z)).Normal :=
        ⟨fun n hn g => by rw [hZcomm g n, mul_inv_cancel_right]; exact hn⟩
      have hp : IsPGroup 3 (Subgroup.zpowers (⟨x, hxZ'⟩ : Z)) := by
        have hord : orderOf (⟨x, hxZ'⟩ : Z) ∣ 3 ^ k := by
          rw [Subgroup.orderOf_mk]
          exact orderOf_dvd_of_pow_eq_one hxk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      exact (le_sSup ⟨hN, hp⟩ : Subgroup.zpowers _ ≤ CFSG.pCore 3 Z) (Subgroup.mem_zpowers _)
    rw [hO3] at hxP
    by_contra hx1
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hcx : c ∈ Subgroup.zpowers (x : G) := by
      have hle : Subgroup.zpowers (x : G) ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hxP
      have hcard : Nat.card (Subgroup.zpowers c) ≤ Nat.card (Subgroup.zpowers (x : G)) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hco]
        have hdvd : orderOf (x : G) ∣ 3 := by
          rw [← hco, ← Nat.card_zpowers, ← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le hle
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1'
        · omega
      exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers c
    apply hcL
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcx
    rw [← hm]
    have hxl : (x : G) * l = l * x :=
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨l, hl⟩)).symm
    exact ((Commute.zpow_left hxl m)).symm.eq
  refine ⟨hcL', hinf, ?_⟩
  set s : L ⧸ Subgroup.center L := ((⟨c, hcL'⟩ : L) : L ⧸ Subgroup.center L) with hs
  have hfix : autFix (descAut L ⟨c, Subgroup.le_normalizer hcL'⟩) =
      Subgroup.centralizer ({s} : Set (L ⧸ Subgroup.center L)) := by
    rw [descAut_eq_conj hcL']
    exact RonanK429H.autFix_conj s
  let eB := equivBar hK'L hinf
  have hs1 : s ≠ 1 := fun h => hcL ((mk_eq_one_iff hcL').mp h)
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← QuotientGroup.mk_pow]
    have : (⟨c, hcL'⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, QuotientGroup.mk_one]
  refine ⟨orderOf_eq_prime hs3 hs1, ⟨⟨c, hcL'⟩, hcK', rfl⟩, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q, ?_, isType425_theta_congr eB htype'⟩
  · rw [← hfix]
    exact map_le_autFix (Subgroup.le_normalizer hcL') hK'c
  · have hsn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal := by
      have hKeq : K'.subgroupOf (L ⊓ Subgroup.centralizer {c}) = K := by
        rw [hK']
        exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) K
      rw [hKeq]
      exact hK.2
    have h := isSubnormal_bar (Subgroup.le_normalizer hcL') hK'M hsn
    rwa [hfix] at h

end Transfer

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
