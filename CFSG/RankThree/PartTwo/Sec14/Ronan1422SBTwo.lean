module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SBFit
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open scoped Pointwise

theorem eq_one_of_mem_of_mem_two_group {G : Type} [Group G] {B R : Subgroup G}
    (hB9 : Nat.card B = 9) (hR2 : IsPGroup 2 R) {x : G} (hxB : x ∈ B) (hxR : x ∈ R) :
    x = 1 := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hR2) ⟨x, hxR⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h9 : x ^ 9 = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hxB)
    rwa [hB9] at h
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : x ^ Nat.gcd 9 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h9, hk'⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1

theorem card_map_eq_of_injective_comp_subtype {K : Type} [Group K]
    (f : K →* alternatingGroup (Fin 6)) (B' : Subgroup K)
    (hinj : Function.Injective (f.comp B'.subtype)) :
    Nat.card (B'.map f) = Nat.card B' := by
  have hrange : (f.comp B'.subtype).range = B'.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hrange] at h1
  exact h1.symm

theorem sylow_conj_mem_of_card_eq {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P A T : Subgroup X} (hAP : A ≤ P) (hTP : T ≤ P)
    (hA : Nat.card A = p ^ (Nat.card P).factorization p)
    (hT : Nat.card T = p ^ (Nat.card P).factorization p) :
    ∃ y ∈ P, ∀ t ∈ T, y⁻¹ * t * y ∈ A := by
  have hAs : Nat.card (A.subgroupOf P) = p ^ (Nat.card P).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv).trans hA
  have hTs : Nat.card (T.subgroupOf P) = p ^ (Nat.card P).factorization p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv).trans hT
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq P (Sylow.ofCard (A.subgroupOf P) hAs)
    (Sylow.ofCard (T.subgroupOf P) hTs)
  have hcoe : MulAut.conj m • (A.subgroupOf P) = T.subgroupOf P := by
    have h : ((m • Sylow.ofCard (A.subgroupOf P) hAs : Sylow p P) : Subgroup P) =
        ((Sylow.ofCard (T.subgroupOf P) hTs : Sylow p P) : Subgroup P) := by
      rw [hm]
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  refine ⟨(m : X), m.2, fun t ht => ?_⟩
  have htP : (⟨t, hTP ht⟩ : P) ∈ T.subgroupOf P := Subgroup.mem_subgroupOf.mpr ht
  rw [← hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at htP
  have h2 := Subgroup.mem_subgroupOf.mp htP
  exact h2

theorem card_comap_eq_card_ker_mul_card {K : Type} [Group K] [Finite K]
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (B : Subgroup (alternatingGroup (Fin 6))) :
    Nat.card (B.comap f) = Nat.card f.ker * Nat.card B := by
  have h1 := Subgroup.card_mul_index (B.comap f)
  rw [Subgroup.index_comap_of_surjective B hf] at h1
  have h3 := Subgroup.index_mul_card B
  have h4 := Subgroup.card_ker_mul_card_of_surjective hf
  have hpos : 0 < B.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h4, ← h3]
  ring

theorem pCore_two_quotient_bot_1422S (H : Type) [Group H] [Finite H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup H :=
    (CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H)).comap (QuotientGroup.mk' (CFSG.pCore 2 H))
  have hMp : IsPGroup 2 M := by
    intro x
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := H ⧸ CFSG.pCore 2 H)
      ⟨QuotientGroup.mk' (CFSG.pCore 2 H) (x : H), x.2⟩
    have hn' : QuotientGroup.mk' (CFSG.pCore 2 H) ((x : H) ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have hmem : (x : H) ^ 2 ^ n ∈ CFSG.pCore 2 H := (QuotientGroup.eq_one_iff _).mp hn'
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := H) ⟨(x : H) ^ 2 ^ n, hmem⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : ((x : H) ^ 2 ^ n) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    show (x : H) ^ 2 ^ (n + m) = 1
    rw [pow_add, pow_mul]
    exact hm'
  have hMle : M ≤ CFSG.pCore 2 H := le_sSup ⟨inferInstance, hMp⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact (QuotientGroup.eq_one_iff x).mpr (hMle hq)

theorem card_le_sq_of_isElemAbelian_le {G : Type} [Group G] (V : Subgroup G) (r : ℕ)
    (hrank : ∀ E : Subgroup G, E ≤ V → CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2)
    (E : Subgroup V) (hE : CFSG.Assembly.IsElemAbelian r E) : Nat.card E ≤ r ^ 2 := by
  obtain ⟨hcomm, hexp⟩ : IsMulCommutative E ∧ ∀ x ∈ E, x ^ r = 1 := hE
  have hE' : CFSG.Assembly.IsElemAbelian r (E.map V.subtype) := by
    show IsMulCommutative (E.map V.subtype) ∧ ∀ x ∈ E.map V.subtype, x ^ r = 1
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hexp y hy, map_one]
  have hcard : Nat.card (E.map V.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have h1 := hrank _ (Subgroup.map_subtype_le E) hE'
  rw [hcard] at h1
  exact h1

theorem isElemAbelian_quotient_card_le {H : Type} [Group H] [Finite H] (r : ℕ) (hr : r.Prime)
    (hr5 : 5 ≤ r)
    (hrank : ∀ E : Subgroup H, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2)
    (E : Subgroup (H ⧸ CFSG.pCore 2 H)) (hE : CFSG.Assembly.IsElemAbelian r E) :
    Nat.card E ≤ r ^ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ r ∣ Nat.card (CFSG.pCore 2 H) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := H))
    rw [hn]
    intro hd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨S, -, hS, hScard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift
    (CFSG.pCore 2 H) hndvd hE
  rw [← hScard]
  exact hrank S hS

theorem mem_R_of_mem_K_inter_V {G : Type} [Group G] [Finite G] {K R V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker = R.subgroupOf K) {x : G} (hxK : x ∈ K) (hxV : x ∈ V) : x ∈ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWn : (V.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hKV g.2) _).mp hn
  haveI : ((V.subgroupOf K).map f).Normal := Subgroup.Normal.map hWn f hf
  haveI hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V.subgroupOf K).map f) with hbot | htop
  · have hxW : (⟨x, hxK⟩ : K) ∈ V.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxV
    have hfx : f ⟨x, hxK⟩ = 1 := by
      have hmem : f ⟨x, hxK⟩ ∈ (V.subgroupOf K).map f := Subgroup.mem_map_of_mem f hxW
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hker' : (⟨x, hxK⟩ : K) ∈ f.ker := MonoidHom.mem_ker.mpr hfx
    rw [hker] at hker'
    exact Subgroup.mem_subgroupOf.mp hker'
  · exfalso
    have hσ : ∃ σ : alternatingGroup (Fin 6), orderOf σ = 3 := by
      have hmem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide
      have hc1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ≠ 1 := by decide
      have hc3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
      refine ⟨⟨_, hmem⟩, orderOf_eq_prime ?_ ?_⟩
      · exact Subtype.ext hc3
      · intro h
        exact hc1 (congrArg Subtype.val h)
    obtain ⟨σ, hσ3⟩ := hσ
    have hσmem : σ ∈ (V.subgroupOf K).map f := by
      rw [htop]
      exact Subgroup.mem_top σ
    obtain ⟨w, hw, hwσ⟩ := Subgroup.mem_map.mp hσmem
    have h3 : orderOf (f w) ∣ orderOf w := orderOf_map_dvd f w
    rw [hwσ, hσ3] at h3
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have h4 : orderOf (w : G) ∣ Nat.card V := Subgroup.orderOf_dvd_natCard V hwV
    rw [Subgroup.orderOf_coe] at h4
    exact hV3 (dvd_trans h3 h4)

theorem le_normalizer_of_conj_mem_1422S {G : Type} [Group G] {S N : Subgroup G}
    (h : ∀ g ∈ S, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : S ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h g hg n, fun hn => ?_⟩
  have h' := h g⁻¹ (S.inv_mem hg) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at h'

theorem le_of_isPerfect_quotient {G : Type} [Group G] {J K V N : Subgroup G}
    (hJp : Group.IsPerfect J) (hVs : Group.IsSolvable V) (hVJ : V ≤ J)
    (hJKV : J ≤ K ⊔ V) (hKN : K ≤ N) (hNJ : N ≤ J)
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) : J ≤ N := by
  haveI : Group.IsPerfect J := hJp
  haveI : Group.IsSolvable V := hVs
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := hVJ.trans hJN
  haveI hnorm : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mpr hJN
  haveI : Group.IsPerfect (J ⧸ N.subgroupOf J) := Group.IsPerfect.instQuotientSubgroup
  let ψ : V →* J ⧸ N.subgroupOf J :=
    (QuotientGroup.mk' (N.subgroupOf J)).comp (Subgroup.inclusion hVJ)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
    have hKVN : K ⊔ V ≤ V ⊔ N := sup_le (hKN.trans le_sup_right) le_sup_left
    have hjVN : (j : G) ∈ (V : Set G) * (N : Set G) := by
      have hj : (j : G) ∈ V ⊔ N := hKVN (hJKV j.2)
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V N hVN]
      exact hj
    obtain ⟨v, hv, n, hn, hvn⟩ := Set.mem_mul.mp hjVN
    refine ⟨⟨v, hv⟩, ?_⟩
    show QuotientGroup.mk (⟨v, hVJ hv⟩ : J) = QuotientGroup.mk j
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : v⁻¹ * (j : G) = n := by
      rw [← hvn]
      group
    show v⁻¹ * (j : G) ∈ N
    rw [e]
    exact hn
  haveI : Group.IsSolvable (J ⧸ N.subgroupOf J) := Group.isSolvable_of_surjective hψ
  have hsub : Subsingleton (J ⧸ N.subgroupOf J) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact (Group.IsPerfect.not_isSolvable (J ⧸ N.subgroupOf J)) inferInstance
  intro j hj
  have h1 := Subsingleton.elim (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ N.subgroupOf J) 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem exists_inverting_of_A6 (hA6 : KF1422AutA6) {G : Type} [Group G] [Finite G]
    {K R B : Subgroup G} (hRK : R ≤ K) (f : ↥K →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker = R.subgroupOf K) (hR2 : IsPGroup 2 R)
    (hBK : B ≤ K) (hB9 : Nat.card B = 9) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    ∃ h ∈ K, ∀ b ∈ B, h * b * h⁻¹ = b⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB'card : Nat.card (B.subgroupOf K) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv).trans hB9
  have hinj : Function.Injective (f.comp (B.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfa : f (a : K) = 1 := ha
    have haR : ((a : K) : G) ∈ R := by
      have hmem : (a : K) ∈ f.ker := MonoidHom.mem_ker.mpr hfa
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have haB : ((a : K) : G) ∈ B := Subgroup.mem_subgroupOf.mp a.2
    exact Subtype.ext (Subtype.ext (eq_one_of_mem_of_mem_two_group hB9 hR2 haB haR))
  have hBfcard : Nat.card ((B.subgroupOf K).map f) = 9 := by
    rw [card_map_eq_of_injective_comp_subtype f _ hinj, hB'card]
  have hBfc : ∀ x ∈ (B.subgroupOf K).map f, ∀ y ∈ (B.subgroupOf K).map f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hb) _ (Subgroup.mem_subgroupOf.mp hb'))
  obtain ⟨g, hg⟩ := hA6.2.2.2 ((B.subgroupOf K).map f) hBfcard
  obtain ⟨k₀, hk₀⟩ := hf g
  set Bf : Subgroup (alternatingGroup (Fin 6)) := (B.subgroupOf K).map f with hBf
  set P : Subgroup K := Bf.comap f with hP
  have hB'P : B.subgroupOf K ≤ P := fun b hb =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem f hb)
  have hk₀P : ∀ x ∈ P, k₀ * x * k₀⁻¹ ∈ P := by
    intro x hx
    rw [hP, Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv, hk₀, hg _ hx]
    exact Bf.inv_mem hx
  have hPcard : Nat.card P = Nat.card f.ker * 9 := by
    rw [hP, card_comap_eq_card_ker_mul_card f hf Bf, hBfcard]
  have h3ndvd : ¬ 3 ∣ Nat.card f.ker := by
    have hker2 : IsPGroup 2 f.ker := by
      rw [hker]
      exact IsPGroup.comap_subtype hR2
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker2
    rw [hm]
    intro hd
    have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at h3
  have hfac : (Nat.card P).factorization 3 = 2 := by
    have hne : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
    rw [hPcard, Nat.factorization_mul hne (by norm_num : (9 : ℕ) ≠ 0), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3ndvd, zero_add]
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  set T : Subgroup K := (B.subgroupOf K).map (MulAut.conj k₀).toMonoidHom with hT
  have hTP : T ≤ P := by
    rintro _ ⟨b, hb, rfl⟩
    exact hk₀P b (hB'P hb)
  have hTcard : Nat.card T = 9 := by
    rw [hT, Subgroup.card_map_of_injective (f := (MulAut.conj k₀).toMonoidHom)
      (fun a b hab => (MulAut.conj k₀).injective hab), hB'card]
  obtain ⟨y, hyP, hy⟩ := sylow_conj_mem_of_card_eq (p := 3) hB'P hTP
    (by rw [hB'card, hfac]; norm_num) (by rw [hTcard, hfac]; norm_num)
  have key : ∀ b' : K, (b' : G) ∈ B → (y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹ = b'⁻¹ := by
    intro b' hb'
    have hb'B : b' ∈ B.subgroupOf K := Subgroup.mem_subgroupOf.mpr hb'
    have hmemT : k₀ * b' * k₀⁻¹ ∈ T := Subgroup.mem_map.mpr ⟨b', hb'B, rfl⟩
    have hinB : (y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹ ∈ B.subgroupOf K := by
      have e : (y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹ = y⁻¹ * (k₀ * b' * k₀⁻¹) * y := by group
      rw [e]
      exact hy _ hmemT
    have hfy : f y ∈ Bf := Subgroup.mem_comap.mp hyP
    have hcomm : f y * f b' = f b' * f y :=
      hBfc _ hfy _ (Subgroup.mem_map_of_mem f hb'B)
    have hfconj : f ((y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹) = (f b')⁻¹ := by
      have hb'g : g * f b' * g⁻¹ = (f b')⁻¹ := hg _ (Subgroup.mem_map_of_mem f hb'B)
      have hcm : Commute (f y) (f b') := hcomm
      simp only [map_mul, map_inv, hk₀]
      calc (f y)⁻¹ * g * f b' * ((f y)⁻¹ * g)⁻¹ = (f y)⁻¹ * (g * f b' * g⁻¹) * f y := by group
        _ = (f y)⁻¹ * (f b')⁻¹ * f y := by rw [hb'g]
        _ = (f b')⁻¹ := by
          rw [mul_assoc, ← (hcm.inv_right).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hfeq : (f.comp (B.subgroupOf K).subtype) ⟨(y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹, hinB⟩ =
        (f.comp (B.subgroupOf K).subtype) ⟨b'⁻¹, (B.subgroupOf K).inv_mem hb'B⟩ := by
      show f ((y⁻¹ * k₀) * b' * (y⁻¹ * k₀)⁻¹) = f b'⁻¹
      rw [hfconj, map_inv]
    exact congrArg Subtype.val (hinj hfeq)
  refine ⟨((y⁻¹ * k₀ : K) : G), (y⁻¹ * k₀ : K).2, fun b hb => ?_⟩
  exact congrArg Subtype.val (key ⟨b, hBK hb⟩ hb)

theorem isPGroup_two_of_A6_ext
    (hQ : ∀ (Q : Type) [Group Q] [Finite Q] (r : ℕ), r.Prime → 5 ≤ r → IsPGroup r Q →
      (∀ E : Subgroup Q, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2) →
      ∀ E : Subgroup (MulAut Q), (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) → (∀ e ∈ E, e ^ 3 = 1) →
        Nat.card E = 9 → ∀ h : MulAut Q, (∀ e ∈ E, h * e * h⁻¹ = e⁻¹) → False)
    {G : Type} [Group G] [Finite G] {J K R V B : Subgroup G}
    (hKJ : K ≤ J) (hVJ : V ≤ J) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hJKV : J ≤ K ⊔ V) (hJp : Group.IsPerfect J) (hVs : Group.IsSolvable V)
    (hV3 : ¬ 3 ∣ Nat.card V)
    (hrank : ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ E : Subgroup G, E ≤ V →
      CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2)
    (hRK : R ≤ K) (hR2 : IsPGroup 2 R) (hKp : Group.IsPerfect K)
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker = R.subgroupOf K) (hBK : B ≤ K) (hB9 : Nat.card B = 9)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    {h : G} (hhK : h ∈ K) (hinv : ∀ b ∈ B, h * b * h⁻¹ = b⁻¹) : IsPGroup 2 V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable V := hVs
  let ρ : ↥K →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hKV)
  let φ : ↥K →* MulAut (↥V ⧸ CFSG.pCore 2 V) := (CFSG.pCoreQuotMulAut V).comp ρ
  have hV1solv : Group.IsSolvable (↥V ⧸ CFSG.pCore 2 V) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have hV1three : ¬ 3 ∣ Nat.card (↥V ⧸ CFSG.pCore 2 V) := fun hd =>
    hV3 (dvd_trans hd (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _)))
  have hV1rank : ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ E : Subgroup (↥V ⧸ CFSG.pCore 2 V),
      CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2 := fun r hr hr5 E hE =>
    isElemAbelian_quotient_card_le r hr hr5
      (fun E' hE' => card_le_sq_of_isElemAbelian_le V r (hrank r hr hr5) E' hE') E hE
  have hR : IsPGroup 2 f.ker := by
    rw [hker]
    exact IsPGroup.comap_subtype hR2
  have hB9' : Nat.card (B.subgroupOf K) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv).trans hB9
  have hBc' : ∀ b ∈ B.subgroupOf K, ∀ b' ∈ B.subgroupOf K, b * b' = b' * b := by
    intro b hb b' hb'
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hb) _ (Subgroup.mem_subgroupOf.mp hb'))
  have hB3' : ∀ b ∈ B.subgroupOf K, b ^ 3 = 1 := by
    intro b hb
    exact Subtype.ext (by simpa using hB3 _ (Subgroup.mem_subgroupOf.mp hb))
  have hinv' : ∀ b ∈ B.subgroupOf K, (⟨h, hhK⟩ : K) * b * (⟨h, hhK⟩ : K)⁻¹ = b⁻¹ := by
    intro b hb
    exact Subtype.ext (by simpa using hinv _ (Subgroup.mem_subgroupOf.mp hb))
  have hφ : φ = 1 := eq_one_of_A6_act_solvable hQ hV1solv hV1three
    (pCore_two_quotient_bot_1422S V) hV1rank hKp f hf hR (B.subgroupOf K) hB9' hBc' hB3'
    ⟨h, hhK⟩ hinv' φ
  let U : Subgroup G := (CFSG.pCore 2 V).map V.subtype
  have hUV' : U ≤ V := Subgroup.map_subtype_le _
  have hUmem : ∀ y ∈ CFSG.pCore 2 V, (y : G) ∈ U := fun y hy =>
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hUdec : ∀ u ∈ U, ∃ y ∈ CFSG.pCore 2 V, (y : G) = u := fun u hu => by
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu
    exact ⟨y, hy, hyu⟩
  have hb0 : ∀ k ∈ K, ∀ x ∈ V, (k * x * k⁻¹)⁻¹ * x ∈ U := by
    intro k hk x hx
    have hφk : φ ⟨k, hk⟩ = 1 := by
      rw [hφ]
      rfl
    have hfix : φ ⟨k, hk⟩ ((⟨x, hx⟩ : V) : V ⧸ CFSG.pCore 2 V) =
        ((⟨x, hx⟩ : V) : V ⧸ CFSG.pCore 2 V) := by
      rw [hφk]
      rfl
    have hmk : ((ρ ⟨k, hk⟩ ⟨x, hx⟩ : V) : V ⧸ CFSG.pCore 2 V) =
        ((⟨x, hx⟩ : V) : V ⧸ CFSG.pCore 2 V) := by
      rw [← CFSG.pCoreQuotMulAut_mk (ρ ⟨k, hk⟩) ⟨x, hx⟩]
      exact hfix
    have hmem := hUmem _ (QuotientGroup.eq.mp hmk)
    have e : (((ρ ⟨k, hk⟩ ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ : V) : G) = (k * x * k⁻¹)⁻¹ * x := rfl
    rwa [e] at hmem
  have hb : ∀ k ∈ K, ∀ v ∈ V, k⁻¹ * v * k * v⁻¹ ∈ U := by
    intro k hk v hv
    have h1 := hb0 k⁻¹ (K.inv_mem hk) v⁻¹ (V.inv_mem hv)
    have e : (k⁻¹ * v⁻¹ * k⁻¹⁻¹)⁻¹ * v⁻¹ = k⁻¹ * v * k * v⁻¹ := by group
    rwa [e] at h1
  have hKU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    intro k hk u hu
    obtain ⟨y, hy, rfl⟩ := hUdec u hu
    have hchar := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥V)) (Subgroup.normalizerMonoidHom V ⟨k, hKV hk⟩)
    have hy' : (Subgroup.normalizerMonoidHom V ⟨k, hKV hk⟩) y ∈ CFSG.pCore 2 V := by
      rw [← hchar]
      exact Subgroup.mem_map_of_mem _ hy
    exact hUmem _ hy'
  have hUV : ∀ v ∈ V, ∀ u ∈ U, v * u * v⁻¹ ∈ U := by
    intro v hv u hu
    obtain ⟨y, hy, rfl⟩ := hUdec u hu
    exact hUmem _ (Subgroup.Normal.conj_mem inferInstance y hy (⟨v, hv⟩ : V))
  have hKUn : K ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_conj_mem_1422S fun g hg u hu => hKU g hg u hu
  have hdecN : ∀ n ∈ K ⊔ U, ∃ k ∈ K, ∃ u ∈ U, k * u = n := by
    intro n hn
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right K U hKUn
    have hn' : n ∈ (K : Set G) * (U : Set G) := by
      rw [← hset]
      exact hn
    obtain ⟨k, hk, u, hu, hku⟩ := Set.mem_mul.mp hn'
    exact ⟨k, hk, u, hu, hku⟩
  have hKN : K ≤ Subgroup.normalizer ((K ⊔ U : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem_1422S
    intro g hg n hn
    obtain ⟨k, hk, u, hu, rfl⟩ := hdecN n hn
    have e : g * (k * u) * g⁻¹ = (g * k * g⁻¹) * (g * u * g⁻¹) := by group
    rw [e]
    exact (K ⊔ U).mul_mem
      ((le_sup_left : K ≤ K ⊔ U) (K.mul_mem (K.mul_mem hg hk) (K.inv_mem hg)))
      ((le_sup_right : U ≤ K ⊔ U) (hKU g hg u hu))
  have hVN : V ≤ Subgroup.normalizer ((K ⊔ U : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem_1422S
    intro g hg n hn
    obtain ⟨k, hk, u, hu, rfl⟩ := hdecN n hn
    have e : g * (k * u) * g⁻¹ = k * ((k⁻¹ * g * k * g⁻¹) * (g * u * g⁻¹)) := by group
    rw [e]
    exact (K ⊔ U).mul_mem ((le_sup_left : K ≤ K ⊔ U) hk)
      ((le_sup_right : U ≤ K ⊔ U) (U.mul_mem (hb k hk g hg) (hUV g hg u hu)))
  have hNJ : K ⊔ U ≤ J := sup_le hKJ (hUV'.trans hVJ)
  have hJN : J ≤ Subgroup.normalizer ((K ⊔ U : Subgroup G) : Set G) :=
    hJKV.trans (sup_le hKN hVN)
  have hJeq : J ≤ K ⊔ U :=
    le_of_isPerfect_quotient hJp hVs hVJ hJKV (le_sup_left : K ≤ K ⊔ U) hNJ hJN
  have hKVR : ∀ x : G, x ∈ K → x ∈ V → x ∈ R := fun x hxK hxV =>
    mem_R_of_mem_K_inter_V hKV hV3 f hf hker hxK hxV
  have hdecV : ∀ x : V, ∃ z : V, (z : G) ∈ R ∧ x⁻¹ * z ∈ CFSG.pCore 2 V := by
    intro x
    obtain ⟨k, hk, u, hu, hku⟩ := hdecN (x : G) (hJeq (hVJ x.2))
    obtain ⟨y, hy, hyu⟩ := hUdec u hu
    have hkV : k ∈ V := by
      have e : k = (x : G) * (y : G)⁻¹ := by
        rw [← hku, ← hyu]
        group
      rw [e]
      exact V.mul_mem x.2 (V.inv_mem y.2)
    refine ⟨⟨k, hkV⟩, hKVR k hk hkV, ?_⟩
    have e2 : x⁻¹ * (⟨k, hkV⟩ : V) = y⁻¹ := by
      apply Subtype.ext
      show (x : G)⁻¹ * k = (y : G)⁻¹
      rw [← hku, ← hyu]
      group
    rw [e2]
    exact (CFSG.pCore 2 V).inv_mem hy
  have hquot2 : IsPGroup 2 (↥V ⧸ CFSG.pCore 2 V) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hzR, hxz⟩ := hdecV x
    obtain ⟨n, hn⟩ := (isPGroup_iff_pow_pow_eq_one.mp hR2) ⟨(z : G), hzR⟩
    have hzn : z ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    have hxz' : (QuotientGroup.mk x : ↥V ⧸ CFSG.pCore 2 V) = QuotientGroup.mk z :=
      QuotientGroup.eq.mpr hxz
    have hq1 : (QuotientGroup.mk z : ↥V ⧸ CFSG.pCore 2 V) ^ 2 ^ n = 1 := by
      have hh := map_pow (QuotientGroup.mk' (CFSG.pCore 2 V)) z (2 ^ n)
      rw [hzn, map_one] at hh
      exact hh.symm
    refine ⟨n, ?_⟩
    rw [hxz']
    exact hq1
  intro x
  obtain ⟨n, hn⟩ := hquot2 (QuotientGroup.mk x)
  have hxn : x ^ 2 ^ n ∈ CFSG.pCore 2 V := by
    apply (QuotientGroup.eq_one_iff _).mp
    have hh := map_pow (QuotientGroup.mk' (CFSG.pCore 2 V)) x (2 ^ n)
    exact hh.trans hn
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥V) ⟨x ^ 2 ^ n, hxn⟩
  refine ⟨n + m, ?_⟩
  have hm' : (x ^ 2 ^ n) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [pow_add, pow_mul]
  exact hm'

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
