module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inn
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs
public import CFSG.Quasithin.Vol2.Ch7Sec77Coord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_le_of_subnormal' {K H : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) : oddCoreIn K ≤ oddCoreIn H := by
  intro y hy
  have hyK : y ∈ K := oddCoreIn_le K hy
  have hyH : y ∈ H := hKH hyK
  let π : Set Nat.Primes := {q | q.val ≠ 2}
  have h1 : (⟨y, hyK⟩ : K) ∈ CFSG.oddCore ↥K := (mem_oddCoreIn_iff K ⟨y, hyK⟩).mp hy
  rw [CFSG.oddCore_eq_piCore] at h1
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have h2 : e.symm ⟨y, hyK⟩ ∈ CFSG.piCore π ↥(K.subgroupOf H) := by
    have := CFSG.LocalCores.piCore_map_mulEquiv π e.symm
    rw [← this]
    exact ⟨_, h1, rfl⟩
  have hmem : (⟨y, hyH⟩ : H) ∈ (K.subgroupOf H) ⊓ CFSG.piCore π H := by
    rw [← CFSG.LocalCores.prime_set_core_subnormal_intersection π hsub]
    exact ⟨e.symm ⟨y, hyK⟩, h2, rfl⟩
  have hodd' : (⟨y, hyH⟩ : H) ∈ CFSG.oddCore H := by
    rw [CFSG.oddCore_eq_piCore]
    exact hmem.2
  exact (mem_oddCoreIn_iff H ⟨y, hyH⟩).mpr hodd'

theorem isPGroup_center_of_isComponentIn {H K : Subgroup G} (hK : IsComponentIn K H)
    (hodd : oddCoreIn H = ⊥) : IsPGroup 2 ↥(Subgroup.center ↥K) := by
  have hK1 : oddCoreIn K = ⊥ :=
    le_bot_iff.mp ((oddCoreIn_le_of_subnormal' hK.1 hK.2.2).trans hodd.le)
  rintro ⟨z, hz⟩
  obtain ⟨k, hk, -⟩ := exists_odd_pow ((z : ↥K) : G)
  set w : G := ((z : ↥K) : G) ^ 2 ^ k with hw
  have hwK : w ∈ K := K.pow_mem z.2 _
  have hcent : ∀ x ∈ K, Commute x w := fun x hx => by
    have h1 : x * ((z : ↥K) : G) = ((z : ↥K) : G) * x :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
    exact Commute.pow_right h1 _
  have hle : Subgroup.zpowers w ≤ oddCoreIn K := by
    refine DoubleA3.le_oddCoreIn_of_odd ((Subgroup.zpowers_le).mpr hwK) (fun x hx => ?_) ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        change w ^ j = x * w ^ j * x⁻¹
        rw [((hcent x hx).zpow_right j).eq, mul_inv_cancel_right]
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        change w ^ j = y
        have hj' : w ^ j = x * y * x⁻¹ := hj
        have hc := ((hcent x hx).zpow_right j).eq
        calc w ^ j = x⁻¹ * (x * w ^ j) := by group
          _ = x⁻¹ * (w ^ j * x) := by rw [hc]
          _ = x⁻¹ * (x * y * x⁻¹ * x) := by rw [hj']
          _ = y := by group
    · rw [Nat.card_zpowers]
      exact hk
  rw [hK1, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa [hw] using hle

theorem pCore_le_center {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) :
    CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.pCore_normal (p := 2) (G := ↥K)) with h | h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 ↥K := by
      have h0 := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
      rw [h] at h0
      exact h0.of_equiv Subgroup.topEquiv
    have hQ := CFSG.LocalCores.quasisimple_central_quotient hq (Subgroup.center ↥K) le_rfl
    have hbot : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := by
      rw [hQ.2.2, QuotientGroup.map_mk'_self]
    have h2' : IsPGroup 2 (↥K ⧸ Subgroup.center ↥K) :=
      h2.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hq.2.1.toNontrivial
    have hnt := h2'.center_nontrivial
    rw [hbot] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot (⊥ : Subgroup (↥K ⧸ Subgroup.center ↥K))).mp hnt rfl
  · exact h

theorem isQuasisimple_KQ {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) :
    CFSG.IsQuasisimple (KQ K) :=
  (CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.pCore 2 ↥K) (pCore_le_center hq)).1

theorem ker_piK {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) :
    (piK K).ker = Subgroup.center ↥K := by
  have hQ := CFSG.LocalCores.quasisimple_central_quotient hq (CFSG.pCore 2 ↥K)
    (pCore_le_center hq)
  ext x
  rw [MonoidHom.mem_ker, ← hQ.2.1, Subgroup.mem_comap]
  change ((QuotientGroup.mk' (CFSG.pCore 2 ↥K) x : KQ K) : KBar K) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

theorem exists_kbarEquiv {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) :
    ∃ e : ↥K ⧸ Subgroup.center ↥K ≃* KBar K, ∀ x : ↥K, e (x : ↥K ⧸ Subgroup.center ↥K) =
      piK K x := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (ker_piK hq).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (piK K) (piK_surjective K)), fun x => rfl⟩

theorem isLieChar2Big_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLieChar2Big Y) : IsLieChar2Big X := by
  obtain ⟨k, hk, h⟩ := h
  refine ⟨k, hk, ?_⟩
  simp only [A315.IsLieChar2, IsPSL, IsPSU, IsPSp4, IsG2, Is3D4, IsSz, Is2F4] at h ⊢
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl (SectionRank.statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (Or.inl (SectionRank.statedClassicalModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (SectionRank.statedClassicalModel_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (SectionRank.statedClassicalModel_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (SectionRank.chevalleyExceptionalModel_of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (SectionRank.chevalleyExceptionalModel_of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (SectionRank.suzukiModel_of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (SectionRank.reeTitsModel_of_mulEquiv e h)))))))

omit [Finite G] in
theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {E : Subgroup X}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem center_eq_bot_of_lie (hmult : LieMultiplierFact) {H K : Subgroup G}
    (hK : IsComponentIn K H) (hodd : oddCoreIn H = ⊥) (hLie : IsLieChar2Big (KBar K))
    {P E : Subgroup (KBar K)} (hP : IsSylowTwoOf P ⊤) (hEP : E ≤ P) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 16) (hEZ : E ≤ Subgroup.centralizer (P : Set (KBar K))) :
    Subgroup.center ↥K = ⊥ := by
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  obtain ⟨e, -⟩ := exists_kbarEquiv hq
  refine hmult ↥K hq.1 (Subgroup.center ↥K) le_rfl (isPGroup_center_of_isComponentIn hK hodd)
    (isLieChar2Big_of_mulEquiv e hLie) (P.map e.symm.toMonoidHom) (E.map e.symm.toMonoidHom)
    (isSylowTwoOf_map_top e.symm.toMonoidHom e.symm.surjective hP) (Subgroup.map_mono hEP)
    (isElemAbelian_map _ hE) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp (hEZ hx) y hy
    change e.symm y * e.symm x = e.symm x * e.symm y
    rw [← map_mul, ← map_mul, h]

omit [Finite G] in
theorem phiK_map_eq {K W : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    ((W.subgroupOf K).map (piK K)).map (phiK K ⟨g, hg⟩).toMonoidHom = (W.subgroupOf K).map (piK K) := by
  have hinv : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hinvW : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hgW
  have key : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Subgroup.normalizer (W : Set G) →
      ((W.subgroupOf K).map (piK K)).map (phiK K ⟨x, hx⟩).toMonoidHom ≤
        (W.subgroupOf K).map (piK K) := by
    rintro x hx hxW _ ⟨_, ⟨⟨s, hsK⟩, hs, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
    refine ⟨⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx s).mp hsK⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hxW s).mp hs), ?_⟩
    change _ = phiK K ⟨x, hx⟩ (piK K ⟨s, hsK⟩)
    rw [phiK_piK_mk]
  refine le_antisymm (key g hg hgW) ?_
  intro y hy
  have h1 : (phiK K ⟨g⁻¹, hinv⟩) y ∈ (W.subgroupOf K).map (piK K) := key g⁻¹ hinv hinvW ⟨y, hy, rfl⟩
  refine ⟨(phiK K ⟨g⁻¹, hinv⟩) y, h1, ?_⟩
  change (phiK K ⟨g, hg⟩) ((phiK K ⟨g⁻¹, hinv⟩) y) = y
  rw [← MulAut.mul_apply, ← map_mul]
  have e : (⟨g, hg⟩ * ⟨g⁻¹, hinv⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 :=
    Subtype.ext (mul_inv_cancel g)
  rw [e, map_one, MulAut.one_apply]

theorem exists_phiK_eq_conj (kf1 : OutTwoNilpotentFact) {K : Subgroup G}
    (hq : CFSG.IsQuasisimple (KQ K)) (hlist : A23List (KBar K)) {V : Subgroup G} {θ : G}
    (hVN : V ≤ Subgroup.normalizer (K : Set G)) (hθN : θ ∈ Subgroup.normalizer (K : Set G))
    (hθo : Odd (orderOf θ)) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVθ : ⁅V, Subgroup.zpowers θ⁆ = V)
    {P : Subgroup (KBar K)} (hP : IsSylowTwoOf P ⊤)
    (hVP : ∀ v (hv : v ∈ V), P.map (phiK K ⟨v, hVN hv⟩).toMonoidHom = P) :
    ∀ v (hv : v ∈ V), ∃ s ∈ P, phiK K ⟨v, hVN hv⟩ = MulAut.conj s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hnab⟩ := isSimpleGroup_KBar hq
  obtain ⟨N, hNn, hInnN, hodd, h2⟩ := kf1 (KBar K) hs hnab hlist
  have hcenter : Subgroup.center (KBar K) = ⊥ := center_eq_bot_of_simple_ch625 hs hnab
  have hθN' : ∀ j : ℤ, phiK K ⟨θ ^ j, Subgroup.zpow_mem _ hθN j⟩ ∈ N := by
    have h0 : phiK K ⟨θ, hθN⟩ ∈ N := by
      obtain ⟨k, hk⟩ := h2 (phiK K ⟨θ, hθN⟩)
      have hpow : (phiK K ⟨θ, hθN⟩) ^ orderOf θ = 1 := by
        rw [← map_pow]
        have e : (⟨θ, hθN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf θ = 1 :=
          Subtype.ext (by simp [pow_orderOf_eq_one])
        rw [e, map_one]
      refine mem_of_pow_mem_of_coprime (hpow ▸ N.one_mem) hk ?_
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hθo)
    intro j
    have e : (⟨θ ^ j, Subgroup.zpow_mem _ hθN j⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨θ, hθN⟩ ^ j := Subtype.ext (by simp)
    rw [e, map_zpow]
    exact N.zpow_mem h0 j
  set Pr : Subgroup G := (N.comap (phiK K)).map (Subgroup.normalizer (K : Set G)).subtype with hPr
  have hmemP : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (K : Set G)),
      phiK K ⟨y, hy⟩ ∈ N → y ∈ Pr := fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hVPr : V ≤ Pr := by
    rw [← hVθ, Subgroup.commutator_le]
    intro y hy x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hyN := hVN hy
    have hxN : θ ^ j ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hθN j
    have hcN : ⁅y, θ ^ j⁆ ∈ Subgroup.normalizer (K : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hxN)
        (Subgroup.inv_mem _ hyN)) (Subgroup.inv_mem _ hxN)
    refine hmemP _ hcN ?_
    have e : (⟨⁅y, θ ^ j⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⁅(⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨θ ^ j, hxN⟩⁆ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e, map_commutatorElement, commutatorElement_def]
    exact N.mul_mem (hNn.conj_mem _ (hθN' j) _) (N.inv_mem (hθN' j))
  intro v hv
  obtain ⟨⟨y, hyN⟩, hyP, hyv⟩ := hVPr hv
  have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨v, hVN hv⟩ := Subtype.ext hyv
  rw [e] at hyP
  have hvN : phiK K ⟨v, hVN hv⟩ ∈ N := hyP
  have hφ2 : (phiK K ⟨v, hVN hv⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have e2 : (⟨v, hVN hv⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simp [hV2 v hv])
    rw [e2, map_one]
  have hInn : phiK K ⟨v, hVN hv⟩ ∈ innAut (KBar K) := by
    have := innAut_normal (KBar K)
    have hsub : ((innAut (KBar K)).subgroupOf N).Normal := Subgroup.Normal.subgroupOf this N
    have h3 := Subgroup.pow_index_mem ((innAut (KBar K)).subgroupOf N)
      (⟨phiK K ⟨v, hVN hv⟩, hvN⟩ : ↥N)
    rw [Subgroup.mem_subgroupOf] at h3
    refine mem_of_pow_mem_of_coprime (by simpa using h3) (hφ2 ▸ Subgroup.one_mem _) ?_
    exact Nat.coprime_two_right.mpr hodd
  obtain ⟨kb, hkb⟩ := hInn
  have hkb2 : kb ^ (2 ^ 1) = 1 := by
    have h4 : MulAut.conj (kb ^ (2 ^ 1)) = 1 := by
      rw [map_pow, hkb, pow_one, hφ2]
    have h5 := mem_center_of_conj_eq_one h4
    rw [hcenter, Subgroup.mem_bot] at h5
    exact h5
  have hkbN : kb ∈ Subgroup.normalizer (P : Set (KBar K)) := by
    apply mem_normalizer_of_map_conj_eq_ch625
    rw [hkb]
    exact hVP v hv
  exact ⟨kb, mem_of_isSylowTwoOf_of_mem_normalizer hP ⟨1, hkb2⟩ hkbN, hkb.symm⟩

omit [Finite G] in
theorem phiK_eq_one_of_mem_centralizer {K : Subgroup G} (hqQ : CFSG.IsQuasisimple (KQ K)) {a : G}
    (ha : a ∈ Subgroup.centralizer (K : Set G)) (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    phiK K ⟨a, haN⟩ = 1 := by
  refine (phiK_eq_one_iff hqQ _).mpr fun k hk => ?_
  have h := Subgroup.mem_centralizer_iff.mp ha k hk
  change a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K
  rw [← h, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem mem_centralizer_of_phiK_eq_one {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc : phiK K ⟨c, hcN⟩ = 1) :
    c ∈ Subgroup.centralizer (K : Set G) := by
  have hqQ := isQuasisimple_KQ hq
  have h1 := (phiK_eq_one_iff hqQ ⟨c, hcN⟩).mp hc
  have hβ : K.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
    refine eq_one_of_mul_inv_mem_center hq.1 _ fun q => ?_
    have h2 := h1 q q.2
    rw [pCoreOf_two_eq_map_ch625] at h2
    obtain ⟨x, hx, hxq⟩ := h2
    have hxc := pCore_le_center hq hx
    have e : K.normalizerMonoidHom ⟨c, hcN⟩ q * q⁻¹ = x := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_coe]
      exact hxq.symm
    rw [e]
    exact hxc
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h3 := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : G)) hβ
  simp only [MulAut.one_apply] at h3
  rw [normalizerMonoidHom_coe] at h3
  calc k * c = (c * k * c⁻¹) * c := by rw [h3]
    _ = c * k := by group

omit [Finite G] in
theorem isElemAbelian_comap {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {E : Subgroup Y} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.comap f) := CFSG.Open.IsElemAbelian.comap hE hf

omit [Finite G] in
theorem relIndex_map_le_of_finite {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (A B : Subgroup X) : (A.map f).relIndex (B.map f) ≤ A.relIndex B := by
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_le_of_le_left (Subgroup.le_comap_map f A)
    (Subgroup.index_ne_zero_of_finite (H := A.subgroupOf B))

end CFSG.Quasithin.H13.Sec77
