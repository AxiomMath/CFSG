module

public import CFSG.Quasithin.EmptyFaithful.S143RB
public import CFSG.Quasithin.EmptyFaithful.S143PC
public import CFSG.Quasithin.EmptyFaithful.S143RA
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.EmptyFaithful.S143IE
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch
open scoped commutatorElement

namespace S143

open A6Model

section KPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}

theorem not_mem_kOf_of_dOf
    (c : Counter T M g) (c18 : Concl14318 T M g A t)
    (hΓ : Subgroup.centralizer (A : Set G) = A) {d : G} (hd : d ∈ dOf T M)
    (hdZ : d ∉ quasithinOmegaOneCenter T) : d ∉ kOf T M A := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  obtain ⟨x, z, a, r1, hS⟩ := c.exists_setup hrW hrV hr2 c18.a
  have htT := c18.b.t_mem
  have htRQ := c18.b.t_nmem
  obtain ⟨y, cm, Vl, Vr, s, hM, hP, hVl, hVr⟩ := hS.exists_KModel3 htT htRQ
  have hB := hS.basis
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  have hcd : cmat z a r r1 d = Tz := by
    rcases D_cmat hS hd with h | h
    · exfalso
      have h1 : d ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
        (hB.cmat_eq_one_iff_mem_centralizer hdN).mp h
      rw [hΓ] at h1
      exact hdZ (D_inf_Ac_le_Z hd h1)
    · exact h
  intro hdK
  have hq : ∀ e ∈ c.Ac hrW hrV hr2,
      n6Act (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)) (psiA cm z a r r1 e) =
        n6Act s (psiA cm z a r r1 e) := by
    intro e he
    have h1 := psiA_conj hB hdN he (σ := (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)))
      (fun w => hM.q_act ⟨d, hdK⟩ w)
    have h2 := psiA_conj_d hS hP hdN hcd he
    exact h1.symm.trans h2
  have hperm : (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)) = s := by
    refine perm_eq_of_n6Act_eq fun b => ?_
    obtain ⟨e, he, rfl⟩ := psiA_surj hB hM.inj b
    exact hq e he
  have h1 : s.sign = 1 := by
    rw [← hperm]
    exact Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2
  have h2 := hP.conf.s_sign
  rw [h1] at h2
  exact absurd h2 (by decide)

end KPart

section TNPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G}

theorem inf_T_oTwoUpper_le_U (c : Counter T M g) {t' : G} (ht' : t' ∈ T)
    (ho : t' ∈ oTwoUpper (mcOf T)) : t' ∈ uOfL22 T M := by
  have hH : t' ∈ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H ht'
  have hT2 : IsPGroup 2 ↥T := c.hyp.sylow.1
  obtain ⟨k, hk⟩ := hT2 ⟨t', ht'⟩
  have hk' : (⟨t', hH⟩ : ↥(mcOf T)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h3 := c.actK_cube_of_mem_oTwoUpper (x := ⟨t', hH⟩) ho
  have h2k : c.actK ⟨t', hH⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
  have hone : c.actK ⟨t', hH⟩ = 1 := by
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have hd1 : orderOf (c.actK ⟨t', hH⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hd2 : orderOf (c.actK ⟨t', hH⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hg : orderOf (c.actK ⟨t', hH⟩) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hd1 hd2
    rw [hcop] at hg
    have : orderOf (c.actK ⟨t', hH⟩) = 1 := Nat.dvd_one.mp hg
    exact orderOf_eq_one_iff.mp this
  have hq : t' ∈ qOf T := c.mem_qOf_of_actK_eq_one hone
  exact inf_qOf_le_uOfL22 c ⟨ho, hq⟩

end TNPart

section CommPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}

omit [Finite G] in
theorem conj_mem_sup_of_conj {A B : Subgroup G} {t : G} (hA : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hB : ∀ b ∈ B, t * b * t⁻¹ ∈ B) : ∀ x ∈ A ⊔ B, t * x * t⁻¹ ∈ A ⊔ B := by
  intro x hx
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj t).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (hA a ha))
    · exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (hB b hb))
  exact Subgroup.mem_comap.mp (h hx)

omit [Finite G] in
theorem mem_normalizer_of_conj_closed {T P : Subgroup G} (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P)
    {t : G} (ht : t ∈ T) : t ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hPn t ht h hh, fun hh => ?_⟩
  have := hPn t⁻¹ (T.inv_mem ht) _ hh
  simpa [mul_assoc] using this

theorem commutator_T_le (c : Counter T M g) (c18 : Concl14318 T M g A t) (c19 : Concl14319 T M A)
    {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ rOf T M ⊔ uOfL22 T M := by
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hTM : T ≤ M := c.hyp.m_max.1.2
  have hRn : ∀ t ∈ T, ∀ r ∈ rOf T M, t * r * t⁻¹ ∈ rOf T M := fun t ht r hr =>
    (Subgroup.mem_normalizer_iff.mp (M_le_normalizer_rOf c (hTM ht)) r).mp hr
  have hUn : ∀ t ∈ T, ∀ u ∈ uOfL22 T M, t * u * t⁻¹ ∈ uOfL22 T M := fun t ht u hu =>
    (Subgroup.mem_normalizer_iff.mp (c.hHU (hTH ht)) u).mp hu
  have hQn : ∀ t ∈ T, ∀ q ∈ qOf T, t * q * t⁻¹ ∈ qOf T := fun t ht q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (hTH ht)) q).mp hq
  have hPn : ∀ t ∈ T, ∀ p ∈ rOf T M ⊔ uOfL22 T M, t * p * t⁻¹ ∈ rOf T M ⊔ uOfL22 T M :=
    fun t ht => conj_mem_sup_of_conj (hRn t ht) (hUn t ht)
  have hQ'n : ∀ t ∈ T, ∀ q ∈ rOf T M ⊔ qOf T, t * q * t⁻¹ ∈ rOf T M ⊔ qOf T :=
    fun t ht => conj_mem_sup_of_conj (hRn t ht) (hQn t ht)
  have hdD : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hdQ : d ∈ qOf T := hdD.1
  have hdT : d ∈ T := qOf_le_T_of_hyp c.h1281 hdQ
  have hQ'T : rOf T M ⊔ qOf T ≤ T := rq_le_of_hyp c.h1281
  have hdQ' : d ∈ rOf T M ⊔ qOf T := (le_sup_right : qOf T ≤ rOf T M ⊔ qOf T) hdQ
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer ((rOf T M ⊔ uOfL22 T M : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_closed hPn hdT)
  have hd2 : d * d ∈ rOf T M ⊔ uOfL22 T M := by
    have hz : d * d ∈ quasithinOmegaOneCenter T := sq_mem_omegaOneCenter c hD hd4
    exact Subgroup.mem_sup_right (Hyp1281Two.VZ_le_uOfL22 T M
      (Hyp1281Two.omegaOneCenter_le_VZ T M hz))
  have hQ'eq : rOf T M ⊔ qOf T = (rOf T M ⊔ uOfL22 T M) ⊔ Subgroup.zpowers d := by
    rw [c19.a.q_eq, hD, sup_assoc]
  have hQP : ∀ q ∈ rOf T M ⊔ qOf T, q ∈ rOf T M ⊔ uOfL22 T M ∨ d⁻¹ * q ∈ rOf T M ⊔ uOfL22 T M := by
    intro q hq
    rw [hQ'eq] at hq
    obtain ⟨p, hp, δ, hδ, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hdN).1 hq
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' j
    · left
      have : d ^ j = (d * d) ^ m := by rw [hm, zpow_mul, zpow_two]
      rw [this]
      exact Subgroup.mul_mem _ hp (Subgroup.zpow_mem _ hd2 m)
    · right
      have h1 : d⁻¹ * (p * d ^ j) = (d⁻¹ * p * d) * (d * d) ^ m := by
        have : d ^ j = (d * d) ^ m * d := by
          rw [hm, zpow_add_one, zpow_mul, zpow_two]
        rw [this]
        have hc : Commute d ((d * d) ^ m) := (Commute.refl d).mul_right (Commute.refl d) |>.zpow_right m
        calc d⁻¹ * (p * ((d * d) ^ m * d)) = d⁻¹ * p * ((d * d) ^ m * d) := by group
          _ = d⁻¹ * p * (d * (d * d) ^ m) := by rw [hc.eq]
          _ = (d⁻¹ * p * d) * (d * d) ^ m := by group
      rw [h1]
      refine Subgroup.mul_mem _ ?_ (Subgroup.zpow_mem _ hd2 m)
      have := hPn d⁻¹ (T.inv_mem hdT) p hp
      simpa using this
  have hTQ : ∀ a ∈ T, a ∈ rOf T M ⊔ qOf T ∨ t⁻¹ * a ∈ rOf T M ⊔ qOf T := by
    intro a ha
    have hidx : ((rOf T M ⊔ qOf T).subgroupOf T).index = 2 := c18.a.rq_index
    by_cases h : a ∈ rOf T M ⊔ qOf T
    · exact Or.inl h
    · right
      have hmul := Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨t, c18.b.t_mem⟩ : T)⁻¹) (b := ⟨a, ha⟩)
      have ht' : (⟨t, c18.b.t_mem⟩ : T)⁻¹ ∉ (rOf T M ⊔ qOf T).subgroupOf T := by
        intro hm
        apply c18.b.t_nmem
        have := (rOf T M ⊔ qOf T).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        simpa using this
      have ha' : (⟨a, ha⟩ : T) ∉ (rOf T M ⊔ qOf T).subgroupOf T := fun hm =>
        h (Subgroup.mem_subgroupOf.mp hm)
      have hin := hmul.mpr ⟨fun hh => absurd hh ht', fun hh => absurd hh ha'⟩
      simpa using Subgroup.mem_subgroupOf.mp hin
  exact commutator_mem_of_two_steps hPn hQ'n hQ'T c18.b.t_mem hTQ hQP hdQ'

end CommPart

section MainPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t : G}

theorem conj_mem_RU (c : Counter T M g) {τ p : G} (hτ : τ ∈ T) (hp : p ∈ rOf T M ⊔ uOfL22 T M) :
    τ * p * τ⁻¹ ∈ rOf T M ⊔ uOfL22 T M := by
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hTM : T ≤ M := c.hyp.m_max.1.2
  exact conj_mem_sup_of_conj (fun r hr => (Subgroup.mem_normalizer_iff.mp
    (M_le_normalizer_rOf c (hTM hτ)) r).mp hr) (fun u hu => (Subgroup.mem_normalizer_iff.mp
    (c.hHU (hTH hτ)) u).mp hu) p hp

theorem wOfX_not_mem_RU
    (c : Counter T M g) (c18 : Concl14318 T M g A t) (hΓ : Subgroup.centralizer (A : Set G) = A)
    {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4) {x : G}
    (hxL : x ∈ yOfL22 T M) : wOfX d x ∉ rOf T M ⊔ uOfL22 T M := by
  have hdD : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hdZ : d ∉ quasithinOmegaOneCenter T := by
    intro hd
    have h2 := sq_eq_one_of_mem_omegaOneCenter T hd
    rw [pow_two] at h2
    exact (dd_facts hd4).2 h2
  have hdK := not_mem_kOf_of_dOf c c18 hΓ hdD hdZ
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  have hRU := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hxK : x ∈ kOf T M (c.Ac hrW hrV hr2) := (le_sup_right : yOfL22 T M ≤ _) hxL
  have hxK' : x⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) := (kOf T M (c.Ac hrW hrV hr2)).inv_mem hxK
  have hdxd : d * x * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    (Subgroup.mem_normalizer_iff.mp (c.dOf_le_normalizer_kOf hrW hrV hr2 hdD) x).mp hxK
  have hzK : d * d ∈ kOf T M (c.Ac hrW hrV hr2) :=
    hRU (Subgroup.mem_sup_left (c.Ac_le_rOf hrW hrV hr2 (c.VZ_le_Ac hrW hrV hr2
      (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ))))
  have hd12 : (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) ∈ kOf T M (c.Ac hrW hrV hr2) := by
    have e : (x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = x * (d * x * d⁻¹) * (d * d) * x⁻¹ * x⁻¹ := by
      group
    rw [e]
    exact (kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem
      ((kOf T M (c.Ac hrW hrV hr2)).mul_mem ((kOf T M (c.Ac hrW hrV hr2)).mul_mem hxK hdxd) hzK) hxK') hxK'
  intro hw
  apply hdK
  have hwK : wOfX d x ∈ kOf T M (c.Ac hrW hrV hr2) := hRU hw
  have e : d = wOfX d x * ((x * d * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹))⁻¹ := by
    unfold wOfX
    group
  rw [e]
  exact (kOf T M (c.Ac hrW hrV hr2)).mul_mem hwK ((kOf T M (c.Ac hrW hrV hr2)).inv_mem hd12)

@[expose] def Lemma14322TailFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A → Concl14321 T M →
        ∀ d : G, dOf T M = Subgroup.zpowers d → orderOf d = 4 →
          ∀ x ∈ yOfL22 T M, orderOf x = 3 →
            ∀ y : G, y * wOfX d x * y⁻¹ ∈ mcOf T →
              ∃ h ∈ mcOf T, y * wOfX d x * y⁻¹ = h * wOfX d x * h⁻¹

theorem lemma14322Tail_of_fusion
    (hF : Lemma14322TailFusion) : Lemma14322Tail := by
  intro G _ _ T M g A t c c18 c19 hΓ c21 d hD hd4
  obtain ⟨x, hxL, hx3⟩ := c.exists_x
  have hTH : T ≤ mcOf T := c.h1281.almostSpecialHyp_g1.T_le_H
  have hdD : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hwT : wOfX d x ∈ T := wOfX_mem_T c hD hxL
  have hw2 : wOfX d x * wOfX d x = 1 := wOfX_sq c hD hd4 hxL hx3
  have hwRU := wOfX_not_mem_RU c c18 hΓ hD hd4 hxL
  have hw1 : wOfX d x ≠ 1 := fun h => hwRU (h ▸ (rOf T M ⊔ uOfL22 T M).one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (wOfX d x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo c.hyp.sylow
  have hindex : Nat.Coprime 2 (T.relIndex ⊤) := by
    have h := S.not_dvd_index
    rw [hS] at h
    rw [Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h
  have hKT : rOf T M ⊔ uOfL22 T M ≤ T :=
    sup_le (rOf_le_T_of_hyp c.h1281) ((uOfL22_le_qOf c).trans (qOf_le_T_of_hyp c.h1281))
  have habel : ⁅T, T⁆ ≤ rOf T M ⊔ uOfL22 T M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_T_le c c18 c19 hD hd4 a ha b hb
  have hSyl : IsSylowTwoOf T (mcOf T) := sylow_G1_of_hyp c.h1281
  have hHeq := eq_oTwoUpper_sup_of_isSylowTwoOf hSyl
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper (mcOf T) : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper (mcOf T))
  have hcond : ∀ a ∈ (⊤ : Subgroup G), a⁻¹ * wOfX d x * a ∈ T →
      (wOfX d x)⁻¹ * (a⁻¹ * wOfX d x * a) ∈ rOf T M ⊔ uOfL22 T M := by
    intro a _ hmem
    have hmemH : a⁻¹ * wOfX d x * a ∈ mcOf T := hTH hmem
    obtain ⟨h, hhH, hh⟩ := hF G T M g A t c c18 c19 hΓ c21 d hD hd4 x hxL hx3 a⁻¹
      (by simpa using hmemH)
    simp only [inv_inv] at hh
    have hhmem : h ∈ oTwoUpper (mcOf T) ⊔ T := by rw [← hHeq]; exact hhH
    obtain ⟨n, hn, τ, hτ, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hTN).1 hhmem
    set w := wOfX d x with hwdef
    set w' := τ * w * τ⁻¹ with hw'def
    have hw'T : w' ∈ T := T.mul_mem (T.mul_mem hτ hwT) (T.inv_mem hτ)
    set u₁ := (a⁻¹ * w * a) * w'⁻¹ with hu₁def
    have hy : a⁻¹ * w * a = n * w' * n⁻¹ := by
      rw [hh]; simp only [hw'def]; group
    have hu₁N : u₁ ∈ oTwoUpper (mcOf T) := by
      have e : u₁ = n * (w' * n⁻¹ * w'⁻¹) := by rw [hu₁def, hy]; group
      rw [e]
      refine (oTwoUpper (mcOf T)).mul_mem hn ?_
      exact (Subgroup.mem_normalizer_iff.mp (hTN hw'T) n⁻¹).mp ((oTwoUpper (mcOf T)).inv_mem hn)
    have hu₁T : u₁ ∈ T := T.mul_mem hmem (T.inv_mem hw'T)
    have hu₁U : u₁ ∈ uOfL22 T M := inf_T_oTwoUpper_le_U c hu₁T hu₁N
    have hwinv : w⁻¹ ∈ T := T.inv_mem hwT
    have hU' : w⁻¹ * u₁ * w⁻¹⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (c.hHU (hTH hwinv)) u₁).mp hu₁U
    have hcomm := commutator_T_le c c18 c19 hD hd4 w⁻¹ hwinv τ hτ
    have e : w⁻¹ * (a⁻¹ * w * a) = (w⁻¹ * u₁ * w⁻¹⁻¹) * (w⁻¹ * τ * w⁻¹⁻¹ * τ⁻¹) := by
      rw [hu₁def, hy, hw'def]; group
    rw [e]
    exact (rOf T M ⊔ uOfL22 T M).mul_mem (Subgroup.mem_sup_right hU') hcomm
  have key := generalized_thompson_transfer_two_subgroup (X := ⊤) (H := T)
    (K := rOf T M ⊔ uOfL22 T M) le_top hindex hKT (fun h hh k hk => conj_mem_RU c hh hk) habel hwT hwRU
    hord hcond
  rw [commutator_top_eq_top_of_simple c.hyp.simple c.hyp.nonabelian] at key
  exact key (Subgroup.mem_top _)

end MainPart

end S143

end CFSG.Quasithin
