module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Gen
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Prod

variable {Γ : Type} [Group Γ]

theorem exists_pow_mul_eq_pow_mul {C : Subgroup Γ} {s c : Γ}
    (hs : s ∈ Subgroup.normalizer (C : Set Γ)) (hc : c ∈ C) :
    ∀ n : ℕ, ∃ c' ∈ C, (s * c) ^ n = s ^ n * c' := by
  intro n
  induction n with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨s⁻¹ * c' * s * c, C.mul_mem ?_ hc, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) c').mp hc'
      simpa using this
    · rw [pow_succ, h, pow_succ]
      group

variable [Finite Γ]

theorem mem_normalizer_of_commute {R K C S : Subgroup Γ} (hR : R = K ⊔ C)
    (hc : ∀ x ∈ K, ∀ y ∈ C, x * y = y * x) (hKC : K ⊓ C = ⊥) (hS : IsSylowTwoOf S R)
    {m : Γ} (hm : m ∈ K) (hmN : m ∈ Subgroup.normalizer ((S ⊓ K : Subgroup Γ) : Set Γ)) :
    m ∈ Subgroup.normalizer (S : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset : ((K ⊔ C : Subgroup Γ) : Set Γ) = (K : Set Γ) * (C : Set Γ) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K C hc).2
  have hCK : C ≤ Subgroup.normalizer (K : Set Γ) :=
    le_trans (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy)
      (Subgroup.centralizer_le_normalizer _)
  have hKC' : K ≤ Subgroup.normalizer (C : Set Γ) :=
    le_trans (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hc x hx y hy).symm)
      (Subgroup.centralizer_le_normalizer _)
  have hRK : R ≤ Subgroup.normalizer (K : Set Γ) := hR ▸ sup_le Subgroup.le_normalizer hCK
  have hRC : R ≤ Subgroup.normalizer (C : Set Γ) := hR ▸ sup_le hKC' Subgroup.le_normalizer
  have hKR : K ≤ R := hR ▸ le_sup_left
  have hSK : IsSylowTwoOf (S ⊓ K) K := A4.isSylowTwoOf_inf_normal hS hKR hRK
  have hSC : S ≤ Subgroup.normalizer (C : Set Γ) := hS.1.trans hRC
  have hproj : ∀ a ∈ K, ∀ c ∈ C, a * c ∈ S → a ∈ S := by
    intro a ha c hc' hac
    set A := (S ⊔ C) ⊓ K with hA
    have hA2 : IsPGroup 2 A := by
      intro x
      have hx : (x : Γ) ∈ ((S ⊔ C : Subgroup Γ) : Set Γ) := x.2.1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S C hSC] at hx
      obtain ⟨s', hs', c', hc'', hx'⟩ := hx
      obtain ⟨e, he⟩ := hS.2.1 ⟨s', hs'⟩
      have he' : s' ^ 2 ^ e = 1 := congrArg Subtype.val he
      obtain ⟨c₁, hc₁, hpow⟩ := exists_pow_mul_eq_pow_mul (hSC hs') hc'' (2 ^ e)
      have h1 : (x : Γ) ^ 2 ^ e ∈ K ⊓ C := by
        refine ⟨K.pow_mem x.2.2 _, ?_⟩
        rw [← hx', hpow, he', one_mul]
        exact hc₁
      rw [hKC, Subgroup.mem_bot] at h1
      exact ⟨e, Subtype.ext (by simpa using h1)⟩
    have hAeq : A = S ⊓ K :=
      hSK.eq_of_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right) inf_le_right hA2
    have haA : a ∈ A := by
      refine ⟨?_, ha⟩
      have : a = (a * c) * c⁻¹ := by group
      rw [this]
      exact (S ⊔ C).mul_mem (Subgroup.mem_sup_left hac) (Subgroup.mem_sup_right (C.inv_mem hc'))
    rw [hAeq] at haA
    exact haA.1
  have key : ∀ x ∈ S, m * x * m⁻¹ ∈ S := by
    intro x hx
    have hxR : x ∈ ((K ⊔ C : Subgroup Γ) : Set Γ) := hR ▸ hS.1 hx
    rw [hset] at hxR
    obtain ⟨a, ha, c, hc', rfl⟩ := hxR
    have haS : a ∈ S := hproj a ha c hc' hx
    have hcS : c ∈ S := by
      have : c = a⁻¹ * (a * c) := by group
      rw [this]
      exact S.mul_mem (S.inv_mem haS) hx
    have hma : m * a * m⁻¹ ∈ S ⊓ K := (Subgroup.mem_normalizer_iff.mp hmN a).mp ⟨haS, ha⟩
    have hmc : m * c = c * m := hc m hm c hc'
    have hmc' : m⁻¹ * c = c * m⁻¹ := (show Commute m c from hmc).inv_left.eq
    have e : m * (a * c) * m⁻¹ = (m * a * m⁻¹) * c := by
      calc m * (a * c) * m⁻¹ = m * a * (c * m⁻¹) := by group
        _ = m * a * (m⁻¹ * c) := by rw [hmc']
        _ = (m * a * m⁻¹) * c := by group
    rw [e]
    exact S.mul_mem hma.1 hcS
  exact mem_normalizer_of_conj_mem' key

end Prod

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_psl2_or_sz {X : Type} [Group X] {k : ℕ}
    (h : IsPSL 2 2 k X ∨ IsSz k X) : IsSimpleGroup X := by
  rcases h with h | h
  · exact isSimpleGroup_of_lieModel_PSL2 (Or.inl ⟨by simp [classicalTags], h⟩)
  · obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := h
    have := (CFSG.LieType.Ree.suzuki_simple ha (show Nat.card F = 2 ^ (2 * a + 1) by
      rw [hF, hf])).2.2
    exact e.isSimpleGroup

omit [Finite G] in
theorem star_cjSub_eq {M' H Y : Subgroup G} {t : G} (ht : t ∈ H) :
    E2.star M' H (cjSub t Y) =
      (E2.star M' H Y).map (MulAut.conj (starPi M' H ⟨t, ht⟩)).toMonoidHom := by
  ext y
  rw [mem_star510_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cjSub] at hx
    refine ⟨starPi M' H (⟨t, ht⟩⁻¹ * x * ⟨t, ht⟩), starPi_mem_star (by simpa using hx), ?_⟩
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hz
    refine ⟨⟨t, ht⟩ * x * ⟨t, ht⟩⁻¹, ?_, ?_⟩
    · rw [mem_cjSub]
      simpa [mul_assoc] using hx
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

namespace Set510

variable {T M L H B D K : Subgroup G} {n k : ℕ} (s : Set510 G T M L H B D K n k)
include s

theorem case_one_data (hT : ¬ T ≤ Subgroup.normalizer (K : Set G)) :
    kerIn (H ⊓ M) H = pCoreOf 2 H ∧
      (∃ t ∈ T, cjSub t K ≠ K ∧ H ⊓ M = H ⊓ M ⊓ K ⊔ cjSub t (H ⊓ M ⊓ K) ⊔ T) ∧
      (IsPSL 2 2 k ↥(E2.star (H ⊓ M) H K) ∨ IsSz k ↥(E2.star (H ⊓ M) H K)) := by
  have hc := s.cases
  dsimp only [E22FieldCases] at hc
  rcases hc with ⟨hker, t, ht, hcj, hMeq, -, htype, -⟩ | ⟨hTK, -, -⟩
  · exact ⟨hker, ⟨t, ht, hcj, hMeq⟩, htype⟩
  · exact absurd hTK hT

theorem o2q_equiv_star (hJ : kerIn (H ⊓ M) H = pCoreOf 2 H) :
    Nonempty (O2Q K ≃* ↥(E2.star (H ⊓ M) H K)) := by
  have hker : (starRes (H ⊓ M) H K s.K_le_H).ker = CFSG.pCore 2 ↥K := by
    ext x
    rw [MonoidHom.mem_ker, starRes_eq_one_iff, hJ]
    constructor
    · intro hx
      obtain ⟨x', hx', hxx'⟩ :=
        Vol2.Ch11.SecB.inf_pCoreOf_le_pCoreOf s.K_le_H ⟨x.2, hx⟩
      rwa [show x = x' from Subtype.ext hxx'.symm]
    · intro hx
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp s.comp) ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (starRes_surjective s.K_le_H))⟩

omit s in
theorem isComponent_star (hJ : kerIn (H ⊓ M) H = pCoreOf 2 H) {L : Subgroup G}
    (hL : L ∈ cComp H) (hq : CFSG.IsQuasisimple ↥(E2.star (H ⊓ M) H L)) :
    CFSG.IsComponent (E2.star (H ⊓ M) H L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (starPi (H ⊓ M) H).ker = (pCoreOf 2 H).subgroupOf H := by
    unfold starPi
    rw [QuotientGroup.ker_mk', hJ]
  have h2 : IsPGroup 2 (starPi (H ⊓ M) H).ker := by
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).symm
  have : Group.IsNilpotent (starPi (H ⊓ M) H).ker := h2.isNilpotent
  have h1 := map_mem_cComp_top (starPi (H ⊓ M) H) (starPi_surjective _ _) inferInstance
    (subgroupOf_mem_cComp hL)
  exact ⟨hq, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp h1)⟩

theorem inf_le_normalizer_R (hJ : kerIn (H ⊓ M) H = pCoreOf 2 H)
    (hsimple : IsSimpleGroup ↥(E2.star (H ⊓ M) H K)) :
    H ⊓ M ⊓ K ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  set X := H ⊓ M with hX
  set R := oTwoUpper H with hRdef
  set π := starPi X H with hπ
  set Ks := E2.star X H K with hKs
  set Rs := E2.star X H R with hRs
  set Cs := Rs ⊓ Subgroup.centralizer (Ks : Set (E2.StarQuot X H)) with hCs
  set Ss := E2.star X H T ⊓ Rs with hSs
  have hKR : K ≤ R := s.K_le_oTwoUpper
  have hRH : R ≤ H := oTwoUpper_le H
  have hKperf : Group.IsPerfect ↥Ks := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 s.perfect
    exact Group.IsPerfect.ofSurjective (starRes_surjective (M' := X) s.K_le_H)
  have hKq : CFSG.IsQuasisimple ↥Ks := isQuasisimple_of_isSimpleGroup_of_isPerfect
  have hcomp : ∀ t ∈ T, CFSG.IsComponent (E2.star X H (cjSub t K)) := by
    intro t ht
    have h1 : cjSub t K ∈ cComp H := by
      have := cComp_map_mulEquiv (MulAut.conj t) s.comp
      rwa [Vol2.Ch11.SecB.map_conj_eq_self_of_mem_normalizer
        (Subgroup.le_normalizer (s.T_le_H ht))] at this
    refine isComponent_star hJ h1 ?_
    rw [star_cjSub_eq (s.T_le_H ht)]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective) hKq
  have hKc := isComponent_star hJ s.comp hKq
  have hRKC : Rs = Ks ⊔ Cs := by
    refine le_antisymm ?_ (sup_le (Subgroup.map_mono fun x hx => hKR hx) inf_le_left)
    have hgen : R ≤ ((Ks ⊔ Cs).comap π).map H.subtype := by
      rw [hRdef, s.oTwoUpper_eq]
      refine conjClosure_le fun t ht k hk => ?_
      have htH := s.T_le_H ht
      have hkH := s.K_le_H hk
      refine ⟨⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹, ?_, rfl⟩
      show π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ Ks ⊔ Cs
      have hgt : π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ E2.star X H (cjSub t K) :=
        starPi_mem_star (by rw [mem_cjSub]; simpa [mul_assoc] using hk)
      have hgR : π (⟨t, htH⟩ * ⟨k, hkH⟩ * ⟨t, htH⟩⁻¹) ∈ Rs := by
        refine starPi_mem_star ?_
        rw [hRdef, s.oTwoUpper_eq]
        simpa using mem_conjClosure ht hk
      rcases CFSG.LocalCores.distinct_components_commute hKc (hcomp t ht) with h | h
      · refine Subgroup.mem_sup_left ?_
        rw [hKs, h]
        exact hgt
      · refine Subgroup.mem_sup_right ⟨hgR, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have h1 := Subgroup.commutator_mem_commutator hx hgt
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
    obtain ⟨x', hx', hxx'⟩ := hgen hx
    rw [show x = x' from Subtype.ext hxx'.symm]
    exact hx'
  have hc : ∀ x ∈ Ks, ∀ y ∈ Cs, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hZ : Subgroup.center ↥Ks = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Ks) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have ha : (a' : ↥Ks ⧸ Subgroup.center ↥Ks) = 1 :=
        (QuotientGroup.eq_one_iff a').mpr (h ▸ Subgroup.mem_top a')
      have hb : (b' : ↥Ks ⧸ Subgroup.center ↥Ks) = 1 :=
        (QuotientGroup.eq_one_iff b').mpr (h ▸ Subgroup.mem_top b')
      rw [ha, hb]
  have hKC : Ks ⊓ Cs = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, -, hxC⟩
    have hx : (⟨x, hxK⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
  have hS : IsSylowTwoOf Ss Rs := by
    have hT1 : IsSylowTwoOf (E2.star X H T) ⊤ := by
      have h1 := Setup.Family.isSylowTwoOf_map_range π s.sylowH
      rwa [MonoidHom.range_eq_top_of_surjective _ (starPi_surjective _ _)] at h1
    refine A4.isSylowTwoOf_inf_normal hT1 le_top fun y _ => ?_
    obtain ⟨h, rfl⟩ := starPi_surjective X H y
    exact starPi_mem_normalizer (le_normalizer_oTwoUpper H h.2)
  have hSK : Ss ⊓ Ks = E2.star X H (T ⊓ K) := by
    have hKsR : Ks ≤ Rs := Subgroup.map_mono fun x hx => hKR hx
    rw [hSs, inf_assoc, inf_eq_right.mpr hKsR]
    have hker : π.ker ≤ T.subgroupOf H := by
      intro x hx
      rw [MonoidHom.mem_ker, hπ, starPi_eq_one_iff, hX, hJ] at hx
      exact Subgroup.mem_subgroupOf.mpr (s.pCoreOf_le_T hx)
    have h1 := Vol2.Ch11.SecB.map_inf_eq_of_ker_le π (Q := K.subgroupOf H) hker
    rw [← Vol2.Ch11.SecB.inf_subgroupOf'] at h1
    exact h1.symm
  intro m hm
  have hmH : m ∈ H := hm.1.1
  have hmN : π ⟨m, hmH⟩ ∈ Subgroup.normalizer ((Ss ⊓ Ks : Subgroup _) : Set (E2.StarQuot X H)) := by
    have h1 : π ⟨m, hmH⟩ ∈ E2.star X H (X ⊓ K) := starPi_mem_star hm
    rw [s.borel_eq] at h1
    rw [hSK]
    exact h1.2
  have hmS := mem_normalizer_of_commute hRKC hc hKC hS (starPi_mem_star hm.2) hmN
  refine mem_normalizer_of_conj_mem' fun x hx => ⟨?_, ?_⟩
  · have hxH : x ∈ H := s.T_le_H hx.1
    have h1 : π ⟨x, hxH⟩ ∈ Ss := ⟨starPi_mem_star hx.1, starPi_mem_star hx.2⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hmS _).mp h1
    rw [← map_mul, ← map_inv, ← map_mul] at h2
    obtain ⟨y, hy, hyx⟩ := mem_star510_iff.mp h2.1
    have h3 := starPi_eq_iff.mp hyx
    rw [hX, hJ] at h3
    have h4 : (y : G) * ((y : G)⁻¹ * (m * x * m⁻¹)) ∈ T :=
      T.mul_mem hy (s.pCoreOf_le_T (by simpa using h3))
    simpa using h4
  · exact R.mul_mem (R.mul_mem (hKR hm.2) hx.2) (R.inv_mem (hKR hm.2))

theorem concl_one (hT : ¬ T ≤ Subgroup.normalizer (K : Set G)) :
    E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) ∧ K < oTwoUpper H ∧
      (LieModel (O2Q K) .PSL 2 2 k ∨ SuzukiModel (O2Q K) 2 k) := by
  obtain ⟨hJ, ⟨t, ht, hcj, hMeq⟩, htype⟩ := s.case_one_data hT
  have hA := s.inf_le_normalizer_R hJ (isSimpleGroup_of_psl2_or_sz htype)
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    intro t' ht'
    refine mem_normalizer_of_conj_mem' fun x hx => ⟨T.mul_mem (T.mul_mem ht' hx.1) (T.inv_mem ht'),
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (s.T_le_H ht')) x).mp hx.2⟩
  have hXN : H ⊓ M ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hMeq]
    refine sup_le (sup_le hA ?_) hTN
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN ht) (hA ha)) (Subgroup.inv_mem _ (hTN ht))
  refine ⟨s.isBorelIn_of fun x hx => hXN hx.1, ?_, ?_⟩
  · refine lt_of_le_of_ne s.K_le_oTwoUpper fun h => hcj ?_
    have hle : cjSub t K ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      rw [h, s.oTwoUpper_eq]
      exact mem_conjClosure ht hk
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [cjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective])
  · obtain ⟨e⟩ := s.o2q_equiv_star hJ
    rcases htype with ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ | ⟨h2, a, ha, F, _, _, hf, hF, ⟨eF⟩⟩
    · exact Or.inl (Or.inl ⟨by simp [classicalTags],
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans eF⟩⟩⟩)
    · exact Or.inr ⟨h2, a, ha, F, inferInstance, inferInstance, hf, hF, ⟨e.trans eF⟩⟩

end Set510

end CFSG.Quasithin.H13
