module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules (fixSub)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22p22vd_squarefree_lcm {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) :
    Squarefree (Nat.lcm m n) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero hm0 hn0)]
  rw [Nat.squarefree_iff_factorization_le_one hm0] at hm
  rw [Nat.squarefree_iff_factorization_le_one hn0] at hn
  intro p
  rw [Nat.factorization_lcm hm0 hn0, Finsupp.sup_apply]
  exact max_le (hm p) (hn p)

private theorem uc22p22vd_dvd_of_squarefree {r m k : ℕ} (hr : r.Prime) (hm : Squarefree m)
    (hd : m ∣ r ^ k) : m ∣ r := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 hd
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · simp
    · simp
  · exfalso
    have h2 : r * r ∣ r ^ i := by
      rw [← pow_two]
      exact pow_dvd_pow r hi
    exact hr.one_lt.ne' (Nat.isUnit_iff.1 (hm r h2))

private theorem uc22p22vd_squarefree_orderOf_sylow {C : Type*} [Group C] [Finite C]
    [IsMulCommutative C]
    (hCsyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∃ P : Sylow p C, Nat.card P = p ^ 2 ∧ ¬ IsCyclic ↥P)
    (γ : C) : Squarefree (orderOf γ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ^ 2 ∣ orderOf γ := by simpa [pow_two] using hdvd
  have hpC : p ∣ Nat.card C :=
    (dvd_trans (dvd_pow_self p two_ne_zero) hp2).trans (orderOf_dvd_natCard γ)
  obtain ⟨P, hPcard, hPnc⟩ := hCsyl p hp hpC
  have hδ : orderOf (γ ^ (orderOf γ / p ^ 2)) = p ^ 2 :=
    orderOf_pow_orderOf_div (orderOf_pos γ).ne' hp2
  have hZcard : Nat.card ↥(Subgroup.zpowers (γ ^ (orderOf γ / p ^ 2))) = p ^ 2 := by
    rw [Nat.card_zpowers, hδ]
  have hZp : IsPGroup p ↥(Subgroup.zpowers (γ ^ (orderOf γ / p ^ 2))) := IsPGroup.of_card hZcard
  obtain ⟨Q, hZQ⟩ := hZp.exists_le_sylow
  haveI : Unique (Sylow p C) := Sylow.unique_of_normal P inferInstance
  have hQP : Q = P := Subsingleton.elim Q P
  subst hQP
  have hZeq : Subgroup.zpowers (γ ^ (orderOf γ / p ^ 2)) = (Q : Subgroup C) :=
    Subgroup.eq_of_le_of_card_ge hZQ (by rw [hZcard, hPcard])
  apply hPnc
  have hcyc : IsCyclic ↥(Q : Subgroup C) := by
    rw [← hZeq]
    infer_instance
  exact hcyc

private theorem uc22p22vd_squarefree_orderOf_sup {A B C : Subgroup G} (hA : A = B ⊔ C)
    (hAc : IsMulCommutative ↥A) (hB : Squarefree (Nat.card B)) (hCc : IsMulCommutative ↥C)
    (hCsyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card C →
      ∃ P : Sylow p ↥C, Nat.card P = p ^ 2 ∧ ¬ IsCyclic ↥P) :
    ∀ a ∈ A, Squarefree (orderOf a) := by
  intro a ha
  have hBA : B ≤ A := hA ▸ le_sup_left
  have hCA : C ≤ A := hA ▸ le_sup_right
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (mul_comm' (⟨b, hBA hb⟩ : ↥A) ⟨c, hCA hc⟩)
  have hBN : B ≤ normalizer (C : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (C : Set G)
      (Subgroup.mem_centralizer_iff.2 fun c hc => (hcomm b hb c hc).symm)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right B C hBN
  rw [← hA] at hmul
  have ha' : a ∈ (B : Set G) * (C : Set G) := hmul ▸ ha
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Set.mem_mul.1 ha'
  have h1 : Squarefree (orderOf β) :=
    hB.squarefree_of_dvd (Subgroup.orderOf_dvd_natCard B hβ)
  have h2 : Squarefree (orderOf γ) := by
    have := uc22p22vd_squarefree_orderOf_sylow hCsyl (⟨γ, hγ⟩ : ↥C)
    rwa [Subgroup.orderOf_mk] at this
  exact (uc22p22vd_squarefree_lcm h1 h2).squarefree_of_dvd
    (Commute.orderOf_mul_dvd_lcm (hcomm β hβ γ hγ))

theorem uc22p22vd_mbarImage_basic (M V T A : Subgroup G) (hTM : T ≤ M) (hAM : A ≤ M) :
    (IsPGroup 2 ↥T → IsPGroup 2 ↥(mbarImage M V T)) ∧
    (IsMulCommutative ↥A → IsMulCommutative ↥(mbarImage M V A)) ∧
    (Odd (Nat.card A) → Odd (Nat.card (mbarImage M V A))) ∧
    (Permutes A T → Permutes (mbarImage M V A) (mbarImage M V T)) := by
  set π : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore
  refine ⟨fun hT => ?_, fun hA => ?_, fun hodd => ?_, fun hperm => ?_⟩
  · have hT' : IsPGroup 2 ↥(T.subgroupOf M) := hT.comap_subtype
    exact hT'.map π
  · haveI := hA
    haveI : IsMulCommutative ↥(A.subgroupOf M) := inferInstance
    exact (inferInstance : IsMulCommutative ↥((A.subgroupOf M).map π))
  · have h1 : Nat.card ↥(mbarImage M V A) ∣ Nat.card ↥(A.subgroupOf M) :=
      Subgroup.card_map_dvd (A.subgroupOf M) π
    have h2 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hodd h1
  · have key : ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) * (T.subgroupOf M : Set ↥M) =
        (T.subgroupOf M : Set ↥M) * (A.subgroupOf M : Set ↥M) := by
      apply Set.image_injective.2 M.subtype_injective
      have hA' : M.subtype '' (A.subgroupOf M : Set ↥M) = (A : Set G) := by
        rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hAM]
      have hT' : M.subtype '' (T.subgroupOf M : Set ↥M) = (T : Set G) := by
        rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hTM]
      rw [Set.image_mul M.subtype, Set.image_mul M.subtype, hA', hT']
      exact hperm
    unfold Permutes mbarImage
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, key]

theorem uc22p22vd_isSylow_mbarImage (D : Data G) (V : Subgroup G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (mbarImage D.M V D.T) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  let S : Sylow 2 (MBar D.M V) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (MBar D.M V)) = mbarImage D.M V D.T := by
    rw [Sylow.coe_mapSurjective, hQ]
    rfl
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right, ← hS]
  exact S.not_dvd_index

theorem uc22p22vd_hyp11 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (hV : S22_V D Ch)
    (c : Ctx22b D Ch) : F11.Hyp11 D ⊥ c.V :=
  uc22p22c_hyp11 D (hV h1930 c).1
    (uc22p22o_not_isTI_of_hC D (uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM) c.hC)

theorem uc22p22vd_hyp53_centralizesZ (D : Data G) (Ch : Choice2011 G) (_h1930 : H1930 D)
    (c : Ctx22b D Ch) {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥c.V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M c.V) Vmod)
    (hc : ConjModule D.M c.V e ρ) :
    fixSub ρ (mbarImage D.M c.V D.T) ≤ fixSub ρ (mbarImage D.M c.V c.B0) := by
  intro v hv
  have hV : InCalV D.M c.V := uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM
  set g : ↥c.V := e.symm (Multiplicative.ofAdd v) with hg
  have hgv : Multiplicative.toAdd (e g) = v := by
    rw [hg, MulEquiv.apply_symm_apply]
    rfl
  have hgT : ∀ t ∈ D.T, t * (g : G) * t⁻¹ = (g : G) := by
    intro t ht
    have htM : t ∈ D.M := D.sylowM.le ht
    have hw : t * (g : G) * t⁻¹ ∈ c.V := (Subgroup.mem_normalizer_iff.1 (c.hVM htM) (g : G)).1 g.2
    have h1 := hc ⟨t, htM⟩ g ⟨_, hw⟩ rfl
    have h2 : ρ (QuotientGroup.mk ⟨t, htM⟩) v = v :=
      hv _ (Subgroup.mem_map.2 ⟨⟨t, htM⟩, ht, rfl⟩)
    rw [hgv, h2] at h1
    have h3 : (⟨t * (g : G) * t⁻¹, hw⟩ : ↥c.V) = g := by
      apply e.injective
      rw [h1, ← hgv]
      rfl
    exact congrArg Subtype.val h3
  have hgZ : (g : G) ∈ D.Z := by
    refine CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2
      ⟨uc22p22na_le_T_of_inCalV D hV g.2, fun k hk => ?_, hV.2.2.2.2 g g.2⟩
    calc k * (g : G) = (k * (g : G) * k⁻¹) * k := by group
      _ = (g : G) * k := by rw [hgT k hk]
  have hBC : c.B0 ≤ centralizer (D.Z : Set G) := c.hB0.1.trans (c.hLge.trans c.hL.2.le)
  intro b hb
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
  have hyB : (y : G) ∈ c.B0 := hy
  have hcomm : (g : G) = (y : G) * (g : G) * (y : G)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.1 (hBC hyB) (g : G) hgZ
    calc (g : G) = ((g : G) * (y : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * (g : G) * (y : G)⁻¹ := by rw [this]
  have h1 := hc y g g hcomm
  rw [hgv] at h1
  have h4 := congrArg Multiplicative.toAdd h1
  rw [hgv] at h4
  exact h4.symm

theorem uc22p22vd_hyp51_piB (D : Data G) (Ch : Choice2011 G)
    (_h1930 : H1930 D) (c : Ctx22b D Ch) (hinj : c.B0 ⊓ centralizer (c.V : Set G) = ⊥) (r : ℕ)
    (hr : r.Prime) :
    r ∣ Nat.card (mbarImage D.M c.V c.B0) ↔ r ∣ 2 ^ c.n - 1 := by
  have hker : (centralizer (c.V : Set G)).subgroupOf c.B0 = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨b, hb⟩ hbc
    have hb1 : b ∈ c.B0 ⊓ centralizer (c.V : Set G) := ⟨hb, hbc⟩
    rw [hinj, Subgroup.mem_bot] at hb1
    exact Subgroup.mem_bot.2 (Subtype.ext hb1)
  have hcard : Nat.card (mbarImage D.M c.V c.B0) = Nat.card c.B0 := by
    rw [uc22br4_card_mbarImage D.M c.V c.B0 c.hVM c.hBM, hker, Subgroup.index_bot]
  rw [hcard]
  have h := Set.ext_iff.1 c.hpi r
  exact ⟨fun hd => (h.1 ⟨hr, hd⟩).2, fun hd => (h.2 ⟨hr, hd⟩).2⟩

theorem uc22p22vd_hyp51_exp_normT (D : Data G) (Ch : Choice2011 G) (_h1930 : H1930 D)
    (c : Ctx22b D Ch) :
    (∀ r : ℕ, r.Prime → r ∣ Nat.card (mbarImage D.M c.V c.B0) →
      ∀ x ∈ pCoreOf r (mbarImage D.M c.V c.B0), x ^ r = 1) ∧
    (Odd c.n → mbarImage D.M c.V c.B0 ≤
      normalizer ((mbarImage D.M c.V D.T : Subgroup (MBar D.M c.V)) : Set (MBar D.M c.V))) := by
  refine ⟨fun r hr _ x hx => ?_, fun hodd => ?_⟩
  · obtain ⟨-, hAc, _, _, hB, hCc, -, hCsyl, hA, -, -, -⟩ := c.hB0
    have hsq : ∀ a ∈ c.B0, Squarefree (orderOf a) :=
      uc22p22vd_squarefree_orderOf_sup hA hAc hB.2.2.1 hCc hCsyl
    rw [CFSG.Open.pCoreOf] at hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := r) (G := ↥(mbarImage D.M c.V c.B0)))
      ⟨z, hz⟩
    have hzk : ((z : MBar D.M c.V)) ^ (r ^ k) = 1 := by
      have := congrArg (fun w : ↥(CFSG.pCore r ↥(mbarImage D.M c.V c.B0)) =>
        (((w : ↥(mbarImage D.M c.V c.B0))) : MBar D.M c.V)) hk
      simpa using this
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 z.2
    have hyB : (y : G) ∈ c.B0 := hy
    have hord : orderOf (z : MBar D.M c.V) ∣ orderOf y := by
      rw [← hyz]
      exact orderOf_map_dvd _ y
    have hsqz : Squarefree (orderOf (z : MBar D.M c.V)) := by
      refine (hsq (y : G) hyB).squarefree_of_dvd ?_
      calc orderOf (z : MBar D.M c.V) ∣ orderOf y := hord
        _ = orderOf (y : G) := (Subgroup.orderOf_coe y).symm
    have hdvd : orderOf (z : MBar D.M c.V) ∣ r :=
      uc22p22vd_dvd_of_squarefree hr hsqz (orderOf_dvd_of_pow_eq_one hzk)
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  · have hA : c.B0 ≤ normalizer (D.T : Set G) := by
      have h1 : oPi {p | p.Prime ∧ p ∣ 2 ^ c.n - 1} c.B0 ≤ normalizer (D.T : Set G) :=
        c.hα 0 c.n hodd (by simp)
      refine le_trans ?_ h1
      refine le_iSup₂_of_le (f := fun (N : Subgroup G) (_ : N ≤ c.B0 ∧ (N.subgroupOf c.B0).Normal ∧
        piSet N ⊆ {p | p.Prime ∧ p ∣ 2 ^ c.n - 1}) => N) c.B0 ⟨le_rfl, ?_, c.hpi.subset⟩ le_rfl
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    have hBT : c.B0.subgroupOf D.M ≤
        normalizer ((D.T.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact Subgroup.mem_normalizer_iff.1 (hA hy) (z : G)
    exact (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map _)

end CFSG.LocalAnalysis.UniquenessCase.UC22
