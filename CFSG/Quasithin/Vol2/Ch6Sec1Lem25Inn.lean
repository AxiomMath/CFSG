module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Act
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

theorem mem_of_pow_mem_of_coprime {X : Type*} [Group X] {A : Subgroup X} {x : X} {a b : ℕ}
    (ha : x ^ a ∈ A) (hb : x ^ b ∈ A) (hab : Nat.Coprime a b) : x ∈ A := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ a) ^ Nat.gcdA a b * (x ^ b) ^ Nat.gcdB a b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact A.mul_mem (A.zpow_mem ha _) (A.zpow_mem hb _)

theorem center_eq_bot_of_simple_ch625 {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : b ∈ Subgroup.center Q := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp this a)

theorem isSylowTwoOf_map_top {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) {P : Subgroup X} (hP : IsSylowTwoOf P ⊤) :
    IsSylowTwoOf (P.map f) ⊤ := by
  refine ⟨le_top, hP.2.1.map f, fun h2 => hP.2.2 ?_⟩
  have h1 : ((P.map f).subgroupOf ⊤).index = (P.map f).index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  have h3 : (P.subgroupOf ⊤).index = P.index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [h1] at h2
  rw [h3]
  exact h2.trans (Subgroup.index_map_dvd P hf)

theorem isSylowTwoOf_subgroupOf_top {G : Type*} [Group G] {K P : Subgroup G}
    (h : IsSylowTwoOf P K) : IsSylowTwoOf (P.subgroupOf K) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact h.2.1.comap_of_injective K.subtype K.subtype_injective
  · intro h2
    apply h.2.2
    have e : ((P.subgroupOf K).subgroupOf ⊤).index = (P.subgroupOf K).index := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    rwa [e] at h2

theorem mem_of_isSylowTwoOf_of_mem_normalizer {Q : Type*} [Group Q] [Finite Q]
    {P : Subgroup Q} (hP : IsSylowTwoOf P ⊤) {x : Q} (hx : ∃ m : ℕ, x ^ (2 ^ m) = 1)
    (hxN : x ∈ Subgroup.normalizer (P : Set Q)) : x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hx
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨m, Subtype.ext ?_⟩
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]
  have hsup : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers x) :=
    hP.2.1.to_sup_of_normal_left' hz (Subgroup.zpowers_le.mpr hxN)
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hP).2.2 _ le_top hsup le_sup_left
  exact hmax (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem innAut_normal (S : Type) [Group S] : (innAut S).Normal := by
  constructor
  rintro _ ⟨s, rfl⟩ α
  refine ⟨α s, ?_⟩
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply]
  rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_center_of_conj_eq_one {S : Type*} [Group S] {z : S} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun α : MulAut S => α x) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * z = (z * x * z⁻¹) * z := by rw [h1]
    _ = z * x := by group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem phiK_piK_mk {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {k : G}
    (hk : k ∈ K) :
    phiK K ⟨g, hg⟩ (piK K ⟨k, hk⟩) =
      piK K ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp hk⟩ := by
  rw [phiK_piK]
  congr 1

@[expose] noncomputable def SBar (T L V K : Subgroup G) : Subgroup (KBar K) :=
  ((ch6S T L V ⊓ K).subgroupOf K).map (piK K)

omit [Finite G] in
theorem phi_mem_normalizer_SBar {T L V K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hgS : g ∈ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G)) :
    (SBar T L V K).map (phiK K ⟨g, hg⟩).toMonoidHom = SBar T L V K := by
  have hinv : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hinvS : g⁻¹ ∈ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hgS
  have key : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) →
      (SBar T L V K).map (phiK K ⟨x, hx⟩).toMonoidHom ≤ SBar T L V K := by
    rintro x hx hxS _ ⟨_, ⟨⟨s, hsK⟩, hs, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
    refine ⟨⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx s).mp hsK⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hxS s).mp hs), ?_⟩
    show _ = phiK K ⟨x, hx⟩ (piK K ⟨s, hsK⟩)
    rw [phiK_piK_mk]
  refine le_antisymm (key g hg hgS) ?_
  intro y hy
  have h1 : (phiK K ⟨g⁻¹, hinv⟩) y ∈ SBar T L V K := key g⁻¹ hinv hinvS ⟨y, hy, rfl⟩
  refine ⟨(phiK K ⟨g⁻¹, hinv⟩) y, h1, ?_⟩
  show (phiK K ⟨g, hg⟩) ((phiK K ⟨g⁻¹, hinv⟩) y) = y
  rw [← MulAut.mul_apply, ← map_mul]
  have e : (⟨g, hg⟩ * ⟨g⁻¹, hinv⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 :=
    Subtype.ext (mul_inv_cancel g)
  rw [e, map_one, MulAut.one_apply]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem K_le_H : K ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
  d.K_le_I.trans (Subgroup.centralizer_le_normalizer _)

theorem a23List_KBar (h23 : A23SQTKListFact) : A23List (KBar K) := by
  have : IsSimpleGroup G := d.hyp.simple
  set Hn := Subgroup.normalizer (ch6ZS T L V : Set G) with hHn
  have hSQ : SQTKGroup ↥Hn := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH d.hyp.qtke d.hyp.simple d.hyp.nonabelian
      ⟨d.hyp.toHyp611Nat.T_le_normalizer_ZS, d.hyp.pCoreOf_H_ne_bot⟩
    exact ⟨hq, hk⟩
  set ψ : ↥(K.subgroupOf Hn) →* KBar K :=
    (piK K).comp (Subgroup.subgroupOfEquivOfLe d.K_le_H).toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (piK_surjective K).comp (Subgroup.subgroupOfEquivOfLe d.K_le_H).surjective
  set e : ↥(K.subgroupOf Hn) ⧸ ψ.ker ≃* KBar K :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs with he
  obtain ⟨hs, a, b, hab⟩ := isSimpleGroup_KBar d.quasi
  have hs' : IsSimpleGroup (↥(K.subgroupOf Hn) ⧸ ψ.ker) := by
    have := hs
    exact e.isSimpleGroup
  have hab' : ∃ a b : ↥(K.subgroupOf Hn) ⧸ ψ.ker, a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h0 => hab (by simpa using congrArg e h0)⟩
  exact A36A.a23List_of_mulEquiv e.symm (h23 ↥Hn hSQ (K.subgroupOf Hn) ψ.ker hs' hab')

theorem isSylowTwoOf_SK (hI432 : Stmt4_3_2) : IsSylowTwoOf (ch6S T L V ⊓ K) K := by
  have hS := (stmt6_1_9 hI432 G T M L V n d.hyp.toHyp611Nat).1.2
  exact A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp d.comp) hS

theorem isSylowTwoOf_SBar (h432 : Stmt4_3_2) : IsSylowTwoOf (SBar T L V K) ⊤ :=
  isSylowTwoOf_map_top (piK K) (piK_surjective K)
    (isSylowTwoOf_subgroupOf_top (d.isSylowTwoOf_SK h432))

theorem center_KBar : Subgroup.center (KBar K) = ⊥ :=
  center_eq_bot_of_simple_ch625 (isSimpleGroup_KBar d.quasi).1 (isSimpleGroup_KBar d.quasi).2

include hI in
theorem exists_phi_R_eq_conj (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) {r : G}
    (hr : r ∈ ch6R T L V l) :
    ∃ s ∈ SBar T L V K, phiK K ⟨r, d.R_le_NK hI hr⟩ = MulAut.conj s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hnab⟩ := isSimpleGroup_KBar d.quasi
  obtain ⟨N, hNn, hInnN, hodd, h2⟩ := kf1 (KBar K) hs hnab (d.a23List_KBar h23)
  have hDN : ∀ (x : G) (hx : x ∈ DL), phiK K ⟨x, d.DL_le_NK hI hx⟩ ∈ N := by
    intro x hx
    obtain ⟨k, hk⟩ := h2 (phiK K ⟨x, d.DL_le_NK hI hx⟩)
    have hodd' : Odd (orderOf x) := by
      refine Odd.of_dvd_nat d.hall.2.1 ?_
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    have hpow : (phiK K ⟨x, d.DL_le_NK hI hx⟩) ^ orderOf x = 1 := by
      rw [← map_pow]
      have e : (⟨x, d.DL_le_NK hI hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf x = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [e, map_one]
    refine mem_of_pow_mem_of_coprime (hpow ▸ N.one_mem) hk ?_
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd')
  set P : Subgroup G := (N.comap (phiK K)).map (Subgroup.normalizer (K : Set G)).subtype with hP
  have hmemP : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (K : Set G)),
      phiK K ⟨y, hy⟩ ∈ N → y ∈ P := fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hR24 := (d.hyp.lemma_6_1_24_two hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).2.2 DL d.hall
    DL le_rfl (d.hyp.DL_ne_bot d.hall)
  have hRP : ch6R T L V l ≤ P := by
    have hR' : ch6R T L V l = ⁅ch6R T L V l, DL⁆ ⊔
        (ch6U T L V ⊓ Subgroup.centralizer (V : Set G)) := hR24
    rw [hR']
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro y hy x hx
      have hyN := d.R_le_NK hI hy
      have hxN := d.DL_le_NK hI hx
      have hcN : ⁅y, x⁆ ∈ Subgroup.normalizer (K : Set G) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hxN)
          (Subgroup.inv_mem _ hyN)) (Subgroup.inv_mem _ hxN)
      refine hmemP _ hcN ?_
      have e : (⟨⁅y, x⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⁅(⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))), ⟨x, hxN⟩⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e, map_commutatorElement, commutatorElement_def]
      exact N.mul_mem (hNn.conj_mem _ (hDN x hx) _) (N.inv_mem (hDN x hx))
    · intro y hy
      have hyO : y ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
        (d.hyp.lemma_6_1_20_one hI.h432).1 hy.1
      refine hmemP _ (d.O2_le_NK hyO) ?_
      rw [d.phi_eq_one_of_mem_pCoreOf hyO]
      exact N.one_mem
  obtain ⟨⟨y, hyN⟩, hyP, hyr⟩ := hRP hr
  have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨r, d.R_le_NK hI hr⟩ :=
    Subtype.ext hyr
  rw [e] at hyP
  have hrN : phiK K ⟨r, d.R_le_NK hI hr⟩ ∈ N := hyP
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ : IsPGroup 2 ↥(ch6R T L V l))) ⟨r, hr⟩
  have hrm : r ^ (2 ^ m) = 1 := by
    rw [← hm]
    simp
  have hφm : (phiK K ⟨r, d.R_le_NK hI hr⟩) ^ (2 ^ m) = 1 := by
    rw [← map_pow]
    have e2 : (⟨r, d.R_le_NK hI hr⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (2 ^ m) = 1 :=
      Subtype.ext (by simp [hrm])
    rw [e2, map_one]
  have hInn : phiK K ⟨r, d.R_le_NK hI hr⟩ ∈ innAut (KBar K) := by
    have := innAut_normal (KBar K)
    have hsub : ((innAut (KBar K)).subgroupOf N).Normal := Subgroup.Normal.subgroupOf this N
    have h3 := Subgroup.pow_index_mem ((innAut (KBar K)).subgroupOf N)
      (⟨phiK K ⟨r, d.R_le_NK hI hr⟩, hrN⟩ : ↥N)
    rw [Subgroup.mem_subgroupOf] at h3
    refine mem_of_pow_mem_of_coprime (by simpa using h3) (hφm ▸ Subgroup.one_mem _) ?_
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  obtain ⟨kb, hkb⟩ := hInn
  have hkb2 : kb ^ (2 ^ m) = 1 := by
    have h4 : MulAut.conj (kb ^ (2 ^ m)) = 1 := by
      rw [map_pow, hkb, hφm]
    have h5 := mem_center_of_conj_eq_one h4
    rw [d.center_KBar, Subgroup.mem_bot] at h5
    exact h5
  have hrS : r ∈ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (d.hyp.R_le_S hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not hr),
        d.R_le_NK hI hr⟩
  have hkbN : kb ∈ Subgroup.normalizer (SBar T L V K : Set (KBar K)) := by
    apply mem_normalizer_of_map_conj_eq_ch625
    have h6 := phi_mem_normalizer_SBar (d.R_le_NK hI hr) hrS
    rwa [← hkb] at h6
  exact ⟨kb, mem_of_isSylowTwoOf_of_mem_normalizer (d.isSylowTwoOf_SBar hI.h432) ⟨m, hkb2⟩ hkbN,
    hkb.symm⟩

end Dat625

end CFSG.Quasithin.H13
