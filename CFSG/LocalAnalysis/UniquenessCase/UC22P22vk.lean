module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ve
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vf
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem uc22p22vk_conj_cent {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G)) {x y : G}
    (hx : x ∈ M) (hy : y ∈ centralizer (V : Set G)) : x * y * x⁻¹ ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (hV (M.inv_mem hx)) v).1 hv
    simpa using this
  have h := hy _ hv'
  calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [h]
    _ = (x * y * x⁻¹) * v := by group

private theorem uc22p22vk_phi_injective (M V Q : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hQM : Q ≤ M) (hQV : Q ⊓ centralizer (V : Set G) = ⊥) :
    Function.Injective (uc22br4_phi M V Q hQM) := by
  rw [← MonoidHom.ker_eq_bot_iff, uc22br4_ker_phi M V Q hV hQM, eq_bot_iff]
  intro x hx
  have hx1 : (x : G) ∈ Q ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨x.2, hx⟩
  rw [hQV] at hx1
  exact Subtype.ext (Subgroup.mem_bot.1 hx1)

private theorem uc22p22vk_prime_pow {X : Type*} [Group X] [Finite X] {x : X} (hx : x ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ ∃ k : ℕ, orderOf (x ^ k) = r := by
  have h1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.1 h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  exact ⟨r, hr, orderOf x / r, orderOf_pow_orderOf_div (orderOf_pos x).ne' hrd⟩

private theorem uc22p22vk_rpart {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y) {m : X}
    {r : ℕ} (hr : r.Prime) (hfm : orderOf (f m) = r) :
    ∃ b ∈ Subgroup.zpowers m, f b = f m ∧ ∃ k : ℕ, b ^ (r ^ k) = 1 := by
  obtain ⟨k, s, hs, hos⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' r hr.ne_one
  have hcop : Nat.Coprime s r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hs).symm
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  refine ⟨m ^ (s * a), Subgroup.pow_mem _ (Subgroup.mem_zpowers m) _, ?_, k, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, hfm, ha, pow_one]
  · have h1 : s * a * r ^ k = orderOf m * a := by
      rw [hos]
      ring
    rw [← pow_mul, h1, pow_mul, pow_orderOf_eq_one, one_pow]

private theorem uc22p22vk_cyclic_of_le {X : Type*} [Group X] {H K : Subgroup X} (h : H ≤ K)
    (hK : IsCyclic ↥K) : IsCyclic ↥H := by
  haveI := hK
  haveI : IsCyclic ↥(H.subgroupOf K) := inferInstance
  exact (Subgroup.subgroupOfEquivOfLe h).isCyclic.1 this

private theorem uc22p22vk_core (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D)
    (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D) (h77 : F07.R77Eq D) (hSg : UC6S846.SigmaStd D)
    (c : Ctx22b D Ch) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Qb : Subgroup (MBar D.M c.V)}
    (hQb : Qb ∈ F05.calQ (G := MBar D.M c.V) q) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {b : G}
    (hb : b ∈ c.B0) (hb1 : b ≠ 1) (hbr : IsPGroup r ↥(Subgroup.zpowers b)) :
    ∃ Q : Subgroup G, Q ≤ D.M ∧ mbarImage D.M c.V Q = Qb ∧
      Q ⊓ centralizer (c.V : Set G) = ⊥ ∧ ¬ IsCyclic ↥Q ∧ b ∈ normalizer (Q : Set G) ∧
      IsCyclic ↥(Q ⊓ centralizer ({b} : Set G)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hAM : Subgroup.zpowers b ≤ D.M := (Subgroup.zpowers_le.2 hb).trans c.hBM
  have hA : (Odd (Nat.card (Subgroup.zpowers b)) ∧ IsMulCommutative ↥(Subgroup.zpowers b) ∧
      ¬ q ∣ Nat.card (Subgroup.zpowers b)) ∨ IsPGroup q ↥(Subgroup.zpowers b) := by
    by_cases hrq : r = q
    · subst hrq
      exact Or.inr hbr
    · left
      obtain ⟨j, hj⟩ := hbr.exists_card_eq
      refine ⟨?_, inferInstance, ?_⟩
      · rw [hj]
        exact (hr.odd_of_ne_two hr2).pow
      · rw [hj]
        intro hdvd
        exact hrq ((Nat.prime_dvd_prime_iff_eq hq hr).1 (hq.dvd_of_dvd_pow hdvd)).symm
  obtain ⟨Q, hQM, hQp, -, -, hQn, hQV, hmb, hQexp, hQcl, hQnc, hAQ⟩ :=
    uc22p22ve_exists_lift D Ch h1930 hV h10 h1110 c q hq hq2 Qb hQb (Subgroup.zpowers b) hAM hA
  have hΓ : rankThreeGamma 1 q Q ≤ D.M :=
    uc22p22vf_gamma_le D Ch h77 hSg.sig1_sp h8 hSg.nonempty hSg.three_le h1930 c q hq hq2 Q hQM hQp
      hQexp hQcl hQnc hQn
  exact ⟨Q, hQM, hmb, hQV, hQnc, hAQ (Subgroup.mem_zpowers b),
    uc22p22vf_cyclic_cent D Ch h1930 hV h8 h63 h67 hSg c hq hq2 hQM hQp hΓ hb hb1⟩

private theorem uc22p22vk_transfer (M V Q : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hQM : Q ≤ M) (hQV : Q ⊓ centralizer (V : Set G) = ⊥) {b : G} (hbM : b ∈ M)
    (hbQ : b ∈ normalizer (Q : Set G)) (hcyc : IsCyclic ↥(Q ⊓ centralizer ({b} : Set G))) :
    IsCyclic ↥(mbarImage M V Q ⊓
      centralizer ({(QuotientGroup.mk ⟨b, hbM⟩ : MBar M V)} : Set (MBar M V))) := by
  classical
  set φ := uc22br4_phi M V Q hQM with hφ
  have hinj : Function.Injective φ := uc22p22vk_phi_injective M V Q hV hQM hQV
  have hrange : φ.range = mbarImage M V Q := uc22br4_range_phi M V Q hQM
  set H' : Subgroup ↥Q := (Q ⊓ centralizer ({b} : Set G)).subgroupOf Q with hH'
  haveI hH'cyc : IsCyclic ↥H' :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ centralizer ({b} : Set G) ≤ Q)).isCyclic.2 hcyc
  haveI hIcyc : IsCyclic ↥(H'.map φ) :=
    isCyclic_of_surjective (φ.subgroupMap H') (φ.subgroupMap_surjective H')
  refine uc22p22vk_cyclic_of_le (K := H'.map φ) ?_ hIcyc
  intro y hy
  obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.1 hy
  rw [← hrange] at hyQ
  obtain ⟨x, rfl⟩ := hyQ
  refine Subgroup.mem_map.2 ⟨x, ?_, rfl⟩
  show (x : G) ∈ Q ⊓ centralizer ({b} : Set G)
  refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y' hy' => ?_⟩
  rw [Set.mem_singleton_iff] at hy'
  rw [hy']
  have hxQ : (b * (x : G) * b⁻¹) * (x : G)⁻¹ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.1 hbQ x).1 x.2) (Q.inv_mem x.2)
  have hcomm : (QuotientGroup.mk ⟨b, hbM⟩ : MBar M V) * φ x =
      φ x * (QuotientGroup.mk ⟨b, hbM⟩ : MBar M V) :=
    Subgroup.mem_centralizer_iff.1 hyC _ (Set.mem_singleton _)
  have hφx : φ x = (QuotientGroup.mk ⟨(x : G), hQM x.2⟩ : MBar M V) := uc22br4_phi_apply M V Q hQM x
  have hw1 : φ ⟨(b * (x : G) * b⁻¹) * (x : G)⁻¹, hxQ⟩ = 1 := by
    rw [uc22br4_phi_apply]
    have e : (⟨(b * (x : G) * b⁻¹) * (x : G)⁻¹, hQM hxQ⟩ : ↥M) =
        ⟨b, hbM⟩ * ⟨(x : G), hQM x.2⟩ * (⟨b, hbM⟩ : ↥M)⁻¹ * (⟨(x : G), hQM x.2⟩ : ↥M)⁻¹ :=
      Subtype.ext rfl
    rw [e]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hφx] at hcomm
    calc (QuotientGroup.mk ⟨b, hbM⟩ : MBar M V) * QuotientGroup.mk ⟨(x : G), hQM x.2⟩ *
          (QuotientGroup.mk ⟨b, hbM⟩ : MBar M V)⁻¹ * (QuotientGroup.mk ⟨(x : G), hQM x.2⟩ : MBar M V)⁻¹
        = (QuotientGroup.mk ⟨(x : G), hQM x.2⟩ * QuotientGroup.mk ⟨b, hbM⟩ : MBar M V) *
          (QuotientGroup.mk ⟨b, hbM⟩ : MBar M V)⁻¹ *
          (QuotientGroup.mk ⟨(x : G), hQM x.2⟩ : MBar M V)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have h1 := congrArg Subtype.val (hinj (hw1.trans (map_one φ).symm))
  have h1' : (b * (x : G) * b⁻¹) * (x : G)⁻¹ = 1 := h1
  calc b * (x : G) = ((b * (x : G) * b⁻¹) * (x : G)⁻¹) * ((x : G) * b) := by group
    _ = (x : G) * b := by rw [h1', one_mul]

theorem uc22p22vk_b0_inter_ker (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D)
    (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D) (h77 : F07.R77Eq D) (hSg : UC6S846.SigmaStd D)
    (c : Ctx22b D Ch) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (Qb : Subgroup (MBar D.M c.V))
    (hQb : Qb ∈ F05.calQ (G := MBar D.M c.V) q) :
    c.B0 ⊓ centralizer (c.V : Set G) = ⊥ := by
  classical
  by_contra hne
  obtain ⟨⟨b, hbmem⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbB : b ∈ c.B0 := (Subgroup.mem_inf.1 hbmem).1
  have hbC : b ∈ centralizer (c.V : Set G) := (Subgroup.mem_inf.1 hbmem).2
  obtain ⟨r, hr, k, hk⟩ := uc22p22vk_prime_pow hb1'
  have hb'B : b ^ k ∈ c.B0 := Subgroup.pow_mem _ hbB _
  have hb'C : b ^ k ∈ centralizer (c.V : Set G) := Subgroup.pow_mem _ hbC _
  have hb'1 : b ^ k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    exact hr.one_lt.ne hk
  have hodd : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  have hdvd : r ∣ Nat.card c.B0 := by
    have h1 : orderOf (⟨b ^ k, hb'B⟩ : ↥c.B0) = r := by
      rw [Subgroup.orderOf_mk]
      exact hk
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hbr : IsPGroup r ↥(Subgroup.zpowers (b ^ k)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
  obtain ⟨Q, hQM, -, hQV, hQnc, hbQ, hcyc⟩ :=
    uc22p22vk_core D Ch h1930 hV h8 h10 h1110 h63 h67 h77 hSg c hq hq2 hQb hr hr2 hb'B hb'1 hbr
  have hQle : Q ≤ centralizer ({b ^ k} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hwQ : (b ^ k) * (x * (b ^ k)⁻¹ * x⁻¹) ∈ Q := by
      have h1 : (b ^ k * x * (b ^ k)⁻¹) * x⁻¹ ∈ Q :=
        Q.mul_mem ((Subgroup.mem_normalizer_iff.1 hbQ x).1 hx) (Q.inv_mem hx)
      have e : (b ^ k) * (x * (b ^ k)⁻¹ * x⁻¹) = (b ^ k * x * (b ^ k)⁻¹) * x⁻¹ := by group
      rw [e]
      exact h1
    have hwC : (b ^ k) * (x * (b ^ k)⁻¹ * x⁻¹) ∈ centralizer (c.V : Set G) :=
      Subgroup.mul_mem _ hb'C
        (uc22p22vk_conj_cent c.hVM (hQM hx) (Subgroup.inv_mem _ hb'C))
    have hw1 : (b ^ k) * (x * (b ^ k)⁻¹ * x⁻¹) ∈ Q ⊓ centralizer (c.V : Set G) :=
      Subgroup.mem_inf.2 ⟨hwQ, hwC⟩
    rw [hQV, Subgroup.mem_bot] at hw1
    calc b ^ k * x = ((b ^ k) * (x * (b ^ k)⁻¹ * x⁻¹)) * (x * b ^ k) := by group
      _ = x * b ^ k := by rw [hw1, one_mul]
  rw [inf_eq_left.2 hQle] at hcyc
  exact hQnc hcyc

theorem uc22p22vk_hyp515_cyclic (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (hV : S22_V D Ch) (h8 : S22_8 D Ch) (h10 : S22_10 D Ch) (h1110 : R1110W D)
    (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D) (h77 : F07.R77Eq D) (hSg : UC6S846.SigmaStd D)
    (c : Ctx22b D Ch) :
    ∀ q ∈ F05.alphaSet (MBar D.M c.V), ∀ Q ∈ F05.calQ (G := MBar D.M c.V) q,
      ∀ b ∈ mbarImage D.M c.V c.B0, b ≠ 1 →
        IsCyclic ↥(Q ⊓ centralizer ({b} : Set (MBar D.M c.V))) := by
  classical
  intro q hqα Qb hQb b hb hb1
  have hq : q.Prime := hqα.1
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ :=
    (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 (hV h1930 c).1.2.2
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hle : Qb ≤ CFSG.pCore 2 (MBar D.M c.V) := le_sSup ⟨hQb.1, hQb.2.2.1⟩
    rw [hO2, le_bot_iff] at hle
    rw [hle] at hQb
    exact hQb.2.1 inferInstance
  obtain ⟨r, hr, k, hk⟩ := uc22p22vk_prime_pow hb1
  have hb₁mem : b ^ k ∈ mbarImage D.M c.V c.B0 := Subgroup.pow_mem _ hb _
  have hb₁1 : b ^ k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    exact hr.one_lt.ne hk
  have hle1 : Qb ⊓ centralizer ({b} : Set (MBar D.M c.V)) ≤
      Qb ⊓ centralizer ({b ^ k} : Set (MBar D.M c.V)) := by
    refine inf_le_inf_left _ ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ((Commute.pow_left (show Commute b x from (hx b (Set.mem_singleton _))) k).eq)
  refine uc22p22vk_cyclic_of_le hle1 ?_
  obtain ⟨m, hmB, hmb⟩ := Subgroup.mem_map.1 hb₁mem
  have hmB' : (m : G) ∈ c.B0 := hmB
  obtain ⟨b₀, hb₀m, hb₀f, j, hj⟩ := uc22p22vk_rpart
    (QuotientGroup.mk' (kerAct D.M c.V).normalCore) hr
    (show orderOf ((QuotientGroup.mk' (kerAct D.M c.V).normalCore) m) = r by rw [hmb]; exact hk)
  have hb₀B : (b₀ : G) ∈ c.B0 := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hb₀m
    have : (b₀ : G) = (m : G) ^ z := by rw [← hz]; simp
    rw [this]
    exact Subgroup.zpow_mem _ hmB' z
  have hb₀1 : (b₀ : G) ≠ 1 := by
    intro h
    have : b₀ = 1 := Subtype.ext h
    rw [this, map_one] at hb₀f
    exact hb₁1 (by rw [← hmb, ← hb₀f])
  have hodd : Odd (Nat.card c.B0) :=
    uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)
  have hdvd : r ∣ Nat.card c.B0 := by
    have h1 : r ∣ orderOf (m : G) := by
      rw [← hk, ← hmb, Subgroup.orderOf_coe m]
      exact orderOf_map_dvd _ m
    have h2 : orderOf (⟨(m : G), hmB'⟩ : ↥c.B0) ∣ Nat.card c.B0 := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    exact h1.trans h2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hbr : IsPGroup r ↥(Subgroup.zpowers (b₀ : G)) := by
    have hpow : (b₀ : G) ^ (r ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hdv : orderOf (b₀ : G) ∣ r ^ j := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 hdv
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQM, hmbQ, hQV, hQnc, hbQ, hcyc⟩ :=
    uc22p22vk_core D Ch h1930 hV h8 h10 h1110 h63 h67 h77 hSg c hq hq2 hQb hr hr2 hb₀B hb₀1 hbr
  have htr := uc22p22vk_transfer D.M c.V Q c.hVM hQM hQV b₀.2 hbQ hcyc
  rw [hmbQ] at htr
  have hbeq : (QuotientGroup.mk ⟨(b₀ : G), b₀.2⟩ : MBar D.M c.V) = b ^ k := by
    rw [← hmb, ← hb₀f]
    rfl
  rw [hbeq] at htr
  exact htr

end CFSG.LocalAnalysis.UniquenessCase.UC22
