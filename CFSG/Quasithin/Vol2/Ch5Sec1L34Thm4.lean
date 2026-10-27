module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34V2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Z1
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

section General

variable {G : Type} [Group G]

theorem conj_ne_mul_of_odd {x v z : G} (hxz : x * z = z * x) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hodd : Odd (orderOf x)) : x * v * x⁻¹ ≠ z * v := by
  intro h
  have key : ∀ k : ℕ, x ^ k * v * (x ^ k)⁻¹ = z ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : x * z ^ k * x⁻¹ = z ^ k := by
        rw [(Commute.pow_right hxz k).eq, mul_assoc, mul_inv_cancel, mul_one]
      calc x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ = x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (z ^ k * v) * x⁻¹ := by rw [ih]
        _ = (x * z ^ k * x⁻¹) * (x * v * x⁻¹) := by group
        _ = z ^ (k + 1) * v := by rw [hc, h, pow_succ, mul_assoc]
  have h1 := key (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hzo : z ^ orderOf x = 1 := by
    have := congrArg (· * v⁻¹) h1
    simpa using this.symm
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hdvd : orderOf z ∣ orderOf x := orderOf_dvd_of_pow_eq_one hzo
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

variable [Finite G]

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem'
  intro x hx
  exact ⟨(Subgroup.mem_normalizer_iff.mp (hA hg) x).mp hx.1,
    (Subgroup.mem_normalizer_iff.mp (hB hg) x).mp hx.2⟩

theorem le_normalizer_inf_of_le_normalizer {H X : Subgroup G}
    (hX : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer ((H ⊓ X : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem'
  intro x hx
  exact ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg),
    (Subgroup.mem_normalizer_iff.mp (hX hg) x).mp hx.2⟩

theorem le_normalizer_inf_centralizer_pCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem'
  intro c hc
  obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hg hcH) (H.inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hp' : g⁻¹ * p * g ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hg)) p).mp hp
    simpa using this
  have hcomm := Subgroup.mem_centralizer_iff.mp hcC _ hp'
  calc p * (g * c * g⁻¹) = g * ((g⁻¹ * p * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * p * g)) * g⁻¹ := by rw [hcomm]
    _ = g * c * g⁻¹ * p := by group

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem H_eq_sup : H = oTwoUpper H ⊔ T :=
  eq_oTwoUpper_sup_of_isSylowTwoOf' (h.hyp.isSylowTwoOf h.hyp.hStar.1.1)

theorem inf_centralizerModO2_le
    : H ⊓ centralizerModO2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left
    (le_normalizer_inf_of_le_normalizer
      (hKN.trans (normalizer_le_normalizer_centralizerModO2 _))) ?_
  rintro ⟨x, hxH, hxC⟩
  have hset : ((oTwoUpper H ⊔ T : Subgroup G) : Set G) =
      (oTwoUpper H : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (h.hyp.hStar.1.1.trans hKN)
  have hx' : x ∈ (oTwoUpper H : Set G) * (T : Set G) := by
    rw [← hset, ← h.H_eq_sup]; exact hxH
  obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := h.hyp.sylow.1 ⟨t, ht⟩
  have htj : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨k', hk', he⟩ := pow_mul_mem_of_mem_normalizer hk (h.hyp.hStar.1.1.trans hKN ht) (2 ^ j)
  rw [htj, mul_one] at he
  have hmem : (k * t) ^ 2 ^ j ∈ pCoreOf 2 (oTwoUpper H) := by
    rw [he]
    refine mem_pCoreOf_of_mem_centralizerModO2 h.center_K_eq_bot hk' ?_
    rw [← he]
    exact Subgroup.pow_mem _ hxC _
  obtain ⟨i, hi⟩ := pCoreOf_isPGroup 2 (oTwoUpper H) ⟨_, hmem⟩
  refine ⟨j + i, Subtype.ext ?_⟩
  have hi' : ((k * t) ^ 2 ^ j) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul, hi']

end Hyp5_1_14

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem H_le_centralizer (h5114 : Stmt5_1_14_first) :
    H ≤ Subgroup.centralizer (Z₁ : Set G) := by
  have hZH := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.1
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hZC (s.Z₁_le_Z hy)) x hx).symm

theorem ker_le
    (h5114 : Stmt5_1_14_first)
    (hCM : Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M) :
    coreIn (centralizerMod Z₁ H (conjClosure Z₁ D₃)) H ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := coreIn (centralizerMod Z₁ H (conjClosure Z₁ D₃)) H with hNdef
  set K := oTwoUpper H with hKdef
  have hNH : N ≤ H := coreIn_le_left _ _
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_coreIn _ _
  have hNC : N ≤ centralizerMod Z₁ H (conjClosure Z₁ D₃) := coreIn_le_right _ _
  have hKN : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hKH : K ≤ H := oTwoUpper_le H
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hHC := s.H_le_centralizer h5114
  have hodd : ∀ y ∈ N, Odd (orderOf y) → y ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
    intro y hy hyo
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hc := ((mem_centralizerMod.mp (hNC hy)).2.2) v hv
    have hyz : y * z = z * y :=
      (Subgroup.mem_centralizer_iff.mp (hHC (hNH hy)) z hz).symm
    rcases s.eq_one_or_eq hz hz1 hc with h1 | h1
    · have : y * v * y⁻¹ = v := by
        have := congrArg (· * v) h1
        simpa using this
      have e : y * v = v * y := by
        have := congrArg (· * y) this
        simpa [mul_assoc] using this
      exact e.symm
    · exfalso
      have e : y * v * y⁻¹ = z * v := by
        rw [← h1]; group
      exact conj_ne_mul_of_odd hyz hz2 hz1 hyo e
  have hNK : N ⊓ K ≤ pCoreOf 2 K := by
    have hsimp := s.hyp.isSimple_K
    have hNKn : ((N ⊓ K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        (le_normalizer_inf (hKH.trans hHN) Subgroup.le_normalizer)
    rcases hsimp.eq_bot_or_eq_top_of_normal (((N ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      intro x hx
      have hxN : (⟨x, hx.2⟩ : ↥K) ∈ (N ⊓ K).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have hxP : (⟨x, hx.2⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
        exact hb hxN
      exact ⟨_, hxP, rfl⟩
    · exfalso
      have hall : ∀ y ∈ H, Odd (orderOf y) → y ∈ N := by
        intro y hyH hyo
        have hyK : y ∈ K := mem_oTwoUpper_of_odd hyH hyo
        have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨y, hyK⟩ ∈
            ((N ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
          rw [ht]; exact Subgroup.mem_top _
        obtain ⟨c, hc, hcy⟩ := hmem
        have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (c⁻¹ * ⟨y, hyK⟩) = 1 := by
          rw [map_mul, map_inv, hcy, inv_mul_cancel]
        have ho : c⁻¹ * ⟨y, hyK⟩ ∈ CFSG.pCore 2 ↥K := by
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
        obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, ho⟩
        have hk' : (c⁻¹ * ⟨y, hyK⟩) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hσc : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) c = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hc
        have hσy : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) ⟨y, hyK⟩ =
            (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) (c⁻¹ * ⟨y, hyK⟩) := by
          rw [map_mul, map_inv, hσc, inv_one, one_mul]
        have hpow : (QuotientGroup.mk' ((N ⊓ K).subgroupOf K)) ((⟨y, hyK⟩ : ↥K) ^ 2 ^ k) = 1 := by
          rw [map_pow, hσy, ← map_pow, hk', map_one]
        have hmemN : (⟨y, hyK⟩ : ↥K) ^ 2 ^ k ∈ (N ⊓ K).subgroupOf K := by
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
        rw [Subgroup.mem_subgroupOf] at hmemN
        have hyk : y ^ 2 ^ k ∈ N := by simpa using hmemN.1
        obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
          (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hyo) : Nat.Coprime (2 ^ k) (orderOf y))
        rw [← hm]
        exact N.pow_mem hyk m
      have hKC : K ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro y ⟨hyH, hyo⟩
        exact hodd y (hall y hyH hyo) hyo
      have hHM : H ≤ M := by
        rw [s.hyp.H_eq_sup]
        exact sup_le (hKC.trans hCM) s.hyp.hyp.T_le
      exact s.hyp.hyp.hStar.2.1 hHM
  have hNCK : N ≤ H ⊓ centralizerModO2 K := by
    intro x hx
    refine ⟨hNH hx, hKN (hNH hx), normalizer_le_normalizer_pCoreOf 2 K (hKN (hNH hx)),
      fun u hu => hNK ⟨?_, ?_⟩⟩
    · have h1 : u * x⁻¹ * u⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hHN (hKH hu)) x⁻¹).mp (N.inv_mem hx)
      have := N.mul_mem hx h1
      simpa [mul_assoc] using this
    · have h1 : x * u * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKN (hNH hx)) u).mp hu
      exact K.mul_mem h1 (K.inv_mem hu)
  exact hNCK.trans s.hyp.inf_centralizerModO2_le

theorem hypF81
    (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (hCM : Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ≤ M)
    (hab : IsMulCommutative
      ↥(conjClosure (conjClosure Z₁ D₃) (Subgroup.centralizer (Z₁ : Set G))))
    (hO : pCoreOf 2 (H ⊔ D₃) = ⊥) :
    HypF81 T (conjClosure Z₁ D₃) (conjClosure D₃ T) Z₁ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set L₂ := conjClosure D₃ T with hL₂def
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hTV₂ := s.T_le_normalizer_V₂ hF
  have hD₃V₂ : D₃ ≤ Subgroup.normalizer (V₂ : Set G) := le_normalizer_conjClosure Z₁ D₃
  have hL₂V₂ : L₂ ≤ Subgroup.normalizer (V₂ : Set G) := conjClosure_le fun t ht g hg =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTV₂ ht) (hD₃V₂ hg)) (Subgroup.inv_mem _ (hTV₂ ht))
  have hLTV₂ : L₂ ⊔ T ≤ Subgroup.normalizer (V₂ : Set G) := sup_le hL₂V₂ hTV₂
  have hV₂L₂ := s.V₂_le_L₂ h5114 hF
  have hV₂p : IsPGroup 2 V₂ := isPGroup_of_isElemAbelian s.isElemAbelian_V₂
  have hV₂O : V₂ ≤ pCoreOf 2 L₂ := le_pCoreOf_of_le_normalizer 2 hV₂L₂ hL₂V₂ hV₂p
  have hV₂O' : V₂ ≤ pCoreOf 2 (L₂ ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hV₂L₂.trans le_sup_left) hLTV₂ hV₂p
  have hD₃L₂ : D₃ ≤ L₂ := le_conjClosure D₃ T
  obtain ⟨-, hred⟩ := isTwoReducedIn_conjClosure_of_isSylowTwoOf
    (hh.isSylowTwoOf (le_sup_right : T ≤ L₂ ⊔ T)) ((le_conjClosure Z₁ D₃).trans hV₂O') s.Z₁_le_Z
  have heqV : conjClosure Z₁ (L₂ ⊔ T) = V₂ := by
    refine le_antisymm (conjClosure_le fun g hg y hy => ?_)
      (conjClosure_mono le_rfl (hD₃L₂.trans le_sup_left))
    exact (Subgroup.mem_normalizer_iff.mp (hLTV₂ hg) y).mp (le_conjClosure Z₁ D₃ hy)
  rw [heqV] at hred
  have hCT : T ⊓ Subgroup.centralizer (V₂ : Set G) =
      (L₂ ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) :=
    le_antisymm (inf_le_inf_right _ le_sup_right)
      (fun x hx => ⟨s.inf_centralizer_V₂_le_T h5114 hF hx, hx.2⟩)
  refine
    { sylow := hh.isSylowTwoOf le_top
      elemAbelian := s.isElemAbelian_V₂
      normalizes_L := le_normalizer_conjClosure D₃ T
      oTwoRes_eq := by rw [oTwoRes_eq_oTwoUpper]; exact s.oTwoUpper_L₂
      charTwo_L := ?_
      reduced := hred
      cT := ?_
      V₁_ne_bot := fun hb => hz1 (by rw [hb] at hz; exact Subgroup.mem_bot.mp hz)
      V₁_le_V := le_conjClosure Z₁ D₃
      T_normalizes_V₁ := s.T_le_normalizer_Z₁
      weak_a := ?_
      V₁_lt_V := s.Z₁_lt_V₂ hz hz1 hd hd1 h5114
      irred := fun W hW1 hW2 _ => s.eq_or_eq hz hz1 hd hd1 h5114 hF hW1 hW2
      H_normalizes_V₁ := (s.H_le_centralizer h5114).trans (Subgroup.centralizer_le_normalizer _)
      L₁T_le_H := sup_le ((oTwoRes_le _).trans ((s.inf_normalizer_le_T h5114 hF).trans hTH)) hTH
      charTwo_H := charTwo_of_inH' hh.qtke hh.sylow s.hyp.hyp.hStar.1
      ker_le := s.ker_le h5114 hCM
      o2_trivial := ?_ }
  ·
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_centralizer_pCoreOf L₂) ?_
    refine hh.sylow.1.to_le fun x hx => s.inf_centralizer_V₂_le_T h5114 hF ⟨?_, ?_⟩
    · exact Subgroup.mem_sup_left hx.1
    · exact Subgroup.centralizer_le hV₂O hx.2
  ·
    refine le_antisymm ?_ (le_inf (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (hh.isSylowTwoOf le_sup_right)) (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hred))
    refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) ?_
      (hh.sylow.1.to_le inf_le_left)
    rw [hCT]
    exact Hyp5_0_1.le_normalizer_inf_centralizer hLTV₂
  ·
    intro g hg
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
    have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
    obtain ⟨hyZ, hyV⟩ := Subgroup.mem_inf.mp hy
    rcases s.eq_one_or_eq hz hz1 hyZ with rfl | rfl
    · exact absurd rfl hy1'
    rw [mem_conjSub, inv_inv] at hyV
    have hw1 : g * y * g⁻¹ ≠ 1 := by
      intro hw
      apply hy1'
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, hw]; group
    obtain ⟨e, he, hez⟩ := s.exists_conj_eq hz hz1 hd hd1 h5114 hF hyV hw1
    have hcC : e * g ∈ Subgroup.centralizer (Z₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rcases s.eq_one_or_eq hz hz1 hu with rfl | rfl
      · group
      · have e1 : e * g * u * (e * g)⁻¹ = u := by
          rw [show e * g * u * (e * g)⁻¹ = e * (g * u * g⁻¹) * e⁻¹ by group, hez]
        calc u * (e * g) = e * g * u * (e * g)⁻¹ * (e * g) := by rw [e1]
          _ = e * g * u := by group
    have hle : conjSub g⁻¹ V₂ ≤ conjClosure V₂ (Subgroup.centralizer (Z₁ : Set G)) := by
      intro x hx
      rw [mem_conjSub, inv_inv] at hx
      have hv : (e * g) * x * (e * g)⁻¹ ∈ V₂ := by
        have := (Subgroup.mem_normalizer_iff.mp (hD₃V₂ he) _).mp hx
        rwa [show e * (g * x * g⁻¹) * e⁻¹ = (e * g) * x * (e * g)⁻¹ by group] at this
      have e2 : x = (e * g)⁻¹ * ((e * g) * x * (e * g)⁻¹) * (e * g)⁻¹⁻¹ := by group
      rw [e2]
      exact mem_conjClosure (Subgroup.inv_mem _ hcC) hv
    have hV₂W : V₂ ≤ conjClosure V₂ (Subgroup.centralizer (Z₁ : Set G)) := le_conjClosure _ _
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hab.is_comm.comm ⟨a, hV₂W ha⟩ ⟨b, hle hb⟩)
  ·
    have heq : (L₂ ⊔ T) ⊔ H = H ⊔ D₃ := by
      refine le_antisymm (sup_le (sup_le (conjClosure_le fun t ht g hg => ?_)
        (hTH.trans le_sup_left)) le_sup_left)
        (sup_le le_sup_right (hD₃L₂.trans (le_sup_left.trans le_sup_left)))
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hTH ht))
        (Subgroup.mem_sup_right hg)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left (hTH ht)))
    rw [heq]
    exact hO

end Setup521

end Setting

theorem stmt5_1_14_four_of_inputs
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1)
    (h517 : Stmt5_1_17) (h519 : Stmt5_1_19) (h520 : Stmt5_1_20) (h522 : Stmt5_1_22)
    (h523 : Stmt5_1_23) (hF : L2TorusFact) (hFix : L2ModFixTwoFact) (hSum : L4NatSumFact)
    (hq : Stmt5_1_14_qBound) : Stmt5_1_14_four := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  by_contra hnot
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have hh := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hDcard⟩ := hh.isCyclic_card_of_isHall hF hN.2.1
  obtain ⟨k, hk⟩ := h517 G T M L V H B D n hyp hN hV hK
  have h3D : 3 ∣ Nat.card D := by
    rw [hDcard, hk, ← two_mul, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 k
    rw [one_pow] at this
    norm_num at this ⊢
    exact this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3 h3D
  have hD₃ : Subgroup.zpowers (x : G) ≤ D := Subgroup.zpowers_le.mpr x.2
  have h3 : Nat.card (Subgroup.zpowers (x : G)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨hD₃M, hO⟩ := h520 G T M L V H B D n hyp hN hV hK hnot _ hD₃ h3
  obtain ⟨Z₁, hZ1⟩ := h.exists_isZ1Choice h5114 h331 h519 h520 hF hFix hSum hnot hD₃ h3
  have s : Setup521 G T M L V H B D (Subgroup.zpowers (x : G)) Z₁ n := ⟨h, hD₃, h3, hD₃M, hZ1⟩
  have hCM := (h522 G T M L V H B D _ Z₁ n hyp hN hV hK hnot hD₃ h3 hZ1).1.2
  have hab := h523 G T M L V H B D _ Z₁ n hyp hN hV hK hnot hD₃ h3 hZ1
  have hF98 := (s.hypF81 h5114 hF hCM hab hO).toHypF98 s.card_Z₁
  exact absurd hF98.F916_3.1
    (not_le.mpr (hq G T M L V H B D _ Z₁ n hyp hN hV hK hnot hD₃ h3 hZ1 _))

end CFSG.Quasithin.H13
