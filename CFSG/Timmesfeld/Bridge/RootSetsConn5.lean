module

public import CFSG.Timmesfeld.Bridge.RootSetsConn4
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import CFSG.Timmesfeld.Bridge.Asc72Central

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

section PCore

variable {H : Type*} [Group H]

theorem card_comap_mk'_eq (J : Subgroup H) [J.Normal] (O : Subgroup (H ⧸ J)) :
    Nat.card (O.comap (QuotientGroup.mk' J)) = Nat.card J * Nat.card O := by
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hJF : J ≤ O.comap π := fun x hx => by
    have h1 : (x : H ⧸ J) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show (x : H ⧸ J) ∈ O
    rw [h1]
    exact one_mem _
  have h := Subgroup.card_ker_mul_card_range (π.comp (O.comap π).subtype)
  have hker : (π.comp (O.comap π).subtype).ker = J.subgroupOf (O.comap π) := by
    ext x
    simp [hπ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : (π.comp (O.comap π).subtype).range = O := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.map_comap_eq_self_of_surjective hπs]
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJF).toEquiv] at h
  exact h.symm

theorem pCore_two_quotient_pCore_eq_bot [Finite H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set J := CFSG.pCore 2 H with hJ
  set O := CFSG.pCore 2 (H ⧸ J) with hO
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hK : IsPGroup 2 (O.comap π) := by
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 J).exists_card_eq
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 O).exists_card_eq
    exact IsPGroup.of_card (n := a + c) (by rw [card_comap_mk'_eq, ha, hc, pow_add])
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKJ : O.comap π ≤ J := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ J.map π := Subgroup.map_mono hKJ
    _ = ⊥ := QuotientGroup.map_mk'_self J

theorem eq_bot_of_isPGroup_quotient_pCore [Finite H] {M : Subgroup (H ⧸ CFSG.pCore 2 H)}
    (hM : M.Normal) (h2 : IsPGroup 2 M) : M = ⊥ := by
  rw [eq_bot_iff, ← pCore_two_quotient_pCore_eq_bot]
  exact le_sSup ⟨hM, h2⟩

end PCore

theorem isCyclic_sylow_transfer {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B)
    {r : ℕ} [Fact r.Prime] (h : ∀ R : Sylow r A, IsCyclic (R : Subgroup A)) (R : Sylow r B) :
    IsCyclic (R : Subgroup B) := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  have hs : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  have hQ := h (R.mapSurjective hs)
  have hmap : ((R.mapSurjective hs : Sylow r A) : Subgroup A) =
      (R : Subgroup B).map e.symm.toMonoidHom := rfl
  rw [hmap] at hQ
  let iso := Subgroup.equivMapOfInjective (R : Subgroup B) e.symm.toMonoidHom e.symm.injective
  exact isCyclic_of_surjective iso.symm.toMonoidHom iso.symm.surjective

theorem Asc72.IsOddTransp.isRootInvolutionSet {K : Type*} [Group K] {E : Set K}
    (hE : Asc72.IsOddTransp E) : IsRootInvolutionSet E := by
  refine ⟨hE.1, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
  · rcases hE.2 d hd e he with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
      · exact Or.inr (Or.inr (by rw [h1]; exact odd_one))
      · exact Or.inl h1
    · exact Or.inr (Or.inr h)
  · exfalso
    rcases hE.2 d hd e he with h | h
    · rw [h4] at h
      exact absurd h (by decide)
    · rw [h4] at h
      exact absurd h (by decide)

namespace Step6

variable {G : Type} [Group G] {D : Set G} {a b c x z : G} {P : Subgroup G}

theorem isCyclic_sylow (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P)
    (r : ℕ) [Fact r.Prime] (hr : r ≠ 2)
    (R : Sylow r (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P))) : IsCyclic R := by
  have := hC.setting.finite
  rcases h.psl2_or_sz hB hC with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv _ e.toEquiv
    exact isCyclic_sylow_transfer e.symm
      (fun R' => CFSG.Timmesfeld.RankOne.isCyclic_sylow_psl2 hn r hr R') R
  · exact CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv
      (e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n)))
      r hr R

theorem solvableRadical_eq_pCore (hB : OddTranspBender) (hC : ConnCex D)
    (h : Step6 D a b c x z P) :
    CFSG.solvableRadical (lsub D x P) = CFSG.pCore 2 (lsub D x P) := by
  have := hC.setting.finite
  set X := lsub D x P with hX
  set R := CFSG.solvableRadical X with hR
  set N := CFSG.pCore 2 X with hN
  have hNR : N ≤ R := by
    have : Group.IsNilpotent N := (CFSG.pCore_isPGroup : IsPGroup 2 N).isNilpotent
    exact le_solvableRadical' CFSG.pCore_normal inferInstance
  refine le_antisymm ?_ hNR
  set ρ := QuotientGroup.mk' N with hρ
  have hS := h.setup hC
  have hER := h.not_mem_solvableRadical hC
  have hSY : Asc72.Setup (X ⧸ N) (ρ '' lclass D x P) :=
    hS.map ρ (QuotientGroup.mk'_surjective N) fun d hd h1 =>
      hER d hd (hNR ((QuotientGroup.eq_one_iff d).1 h1))
  obtain ⟨e, he, f, hf, heP, hfP, -, hefD⟩ := h.hLL
  have hu₁ : ρ ⟨e, mem_lsub_of_mem he heP⟩ ∈ ρ '' lclass D x P :=
    ⟨_, h.mem_lclass hC he heP, rfl⟩
  have hu₂ : ρ ⟨f, mem_lsub_of_mem hf hfP⟩ ∈ ρ '' lclass D x P :=
    ⟨_, h.mem_lclass hC hf hfP, rfl⟩
  have hu₃ : ρ ⟨e, mem_lsub_of_mem he heP⟩ * ρ ⟨f, mem_lsub_of_mem hf hfP⟩ ∈
      ρ '' lclass D x P := by
    rw [← map_mul]
    exact ⟨_, h.mem_lclass hC hefD (P.mul_mem heP hfP), rfl⟩
  have hc : Commute (ρ ⟨e, mem_lsub_of_mem he heP⟩) (ρ ⟨f, mem_lsub_of_mem hf hfP⟩) := by
    have hef : Commute (⟨e, mem_lsub_of_mem he heP⟩ : X) ⟨f, mem_lsub_of_mem hf hfP⟩ :=
      Subtype.ext (h.commute_of_mem hC he hf heP hfP).eq
    exact hef.map ρ
  have hne : ρ ⟨e, mem_lsub_of_mem he heP⟩ ≠ ρ ⟨f, mem_lsub_of_mem hf hfP⟩ := fun heq =>
    hSY.oddT.ne_one hu₃ (by rw [← heq]; exact hSY.oddT.mul_self_eq_one hu₁)
  set K := R.map ρ with hK
  have hKn : K.Normal := Subgroup.Normal.map inferInstance ρ (QuotientGroup.mk'_surjective N)
  have hKs : Group.IsSolvable K := by
    have : Group.IsSolvable R := isSolvable_solvableRadical'
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective R)
  have hKc : K ≤ Subgroup.center (X ⧸ N) :=
    le_center_of_isSolvable hSY.isClass hSY.oddT.isRootInvolutionSet hSY.gen hu₁ hu₂ hne hc hu₃
      (fun M hM h2 => eq_bot_of_isPGroup_quotient_pCore hM h2) hKn hKs
  have hKodd : Odd (Nat.card K) := by
    rcases Nat.even_or_odd (Nat.card K) with hev | hodd
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 hev)
      have hkc : (k : X ⧸ N) ∈ Subgroup.center (X ⧸ N) := hKc k.2
      have hk2 : orderOf (k : X ⧸ N) = 2 := by rw [Subgroup.orderOf_coe]; exact hk
      have hMn : (Subgroup.zpowers (k : X ⧸ N)).Normal := ⟨fun m hm g => by
        have hmc : m ∈ Subgroup.center (X ⧸ N) := (Subgroup.zpowers_le.2 hkc) hm
        rw [Subgroup.mem_center_iff.1 hmc g, mul_inv_cancel_right]
        exact hm⟩
      have hM2 : IsPGroup 2 (Subgroup.zpowers (k : X ⧸ N)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk2, pow_one])
      have hbot := eq_bot_of_isPGroup_quotient_pCore hMn hM2
      have hk1 : (k : X ⧸ N) = 1 := by
        have hmem : (k : X ⧸ N) ∈ Subgroup.zpowers (k : X ⧸ N) := Subgroup.mem_zpowers _
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      rw [hk1, orderOf_one] at hk2
      exact absurd hk2 (by decide)
    · exact hodd
  have hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ Rr : Sylow r ((X ⧸ N) ⧸ K), IsCyclic Rr :=
    fun r _ hr Rr => isCyclic_sylow_transfer
      (QuotientGroup.quotientQuotientEquivQuotient N R hNR).symm
      (fun R' => h.isCyclic_sylow hB hC r hr R') Rr
  have hK1 : K = ⊥ := CFSG.Timmesfeld.RankOne.eq_bot_of_isCyclic_sylow hKc hKodd hSY.gen
    (fun s hs => hSY.oddT.mul_self_eq_one hs) hcyc
  intro w hw
  have hρw : ρ w ∈ K := ⟨w, hw, rfl⟩
  rw [hK1, Subgroup.mem_bot] at hρw
  exact (QuotientGroup.eq_one_iff w).1 hρw

theorem z_mul_self (hC : ConnCex D) (h : Step6 D a b c x z P) : z * z = 1 := by
  have hD := hC.setting.root
  have h1 : Commute (a * b) c := h.hca.symm.mul_left h.hcb.symm
  rw [h.hz]
  calc c * (a * b) * (c * (a * b)) = c * (a * b * c) * (a * b) := by group
    _ = c * c * (a * (b * a) * b) := by rw [h1.eq]; group
    _ = 1 := by
      rw [← h.hcab.eq]
      simp only [← mul_assoc]
      rw [hD.mul_self_eq_one h.hc, one_mul, hD.mul_self_eq_one h.ha, one_mul,
        hD.mul_self_eq_one h.hb]

theorem z_mem_lsub (h : Step6 D a b c x z P) : z ∈ lsub D x P := by
  rw [h.hz]
  exact (lsub D x P).mul_mem (mem_lsub_of_mem h.hc h.hcP)
    ((lsub D x P).mul_mem (mem_lsub_of_mem h.ha h.haP) (mem_lsub_of_mem h.hb h.hbP))

theorem z_mem_center (h : Step6 D a b c x z P) :
    (⟨z, h.z_mem_lsub⟩ : lsub D x P) ∈ Subgroup.center (lsub D x P) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (h.lsub_le_centralizer g.2))

theorem z_mem_pCore (hC : ConnCex D) (h : Step6 D a b c x z P) :
    (⟨z, h.z_mem_lsub⟩ : lsub D x P) ∈ CFSG.pCore 2 (lsub D x P) := by
  set w : lsub D x P := ⟨z, h.z_mem_lsub⟩
  have hw2 : w * w = 1 := Subtype.ext (h.z_mul_self hC)
  have hc := h.z_mem_center
  have hMn : (Subgroup.zpowers w).Normal := ⟨fun m hm g => by
    have hmc : m ∈ Subgroup.center (lsub D x P) := (Subgroup.zpowers_le.2 hc) hm
    rw [Subgroup.mem_center_iff.1 hmc g, mul_inv_cancel_right]
    exact hm⟩
  have hM2 : IsPGroup 2 (Subgroup.zpowers w) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hw2, one_zpow]
  exact (le_sSup ⟨hMn, hM2⟩ : Subgroup.zpowers w ≤ CFSG.pCore 2 (lsub D x P))
    (Subgroup.mem_zpowers w)

theorem commutator_eq_top (hC : ConnCex D) (h : Step6 D a b c x z P) :
    commutator (lsub D x P) = ⊤ := by
  by_contra hne
  obtain ⟨e, he, f, hf, heP, hfP, -, hefD⟩ := h.hLL
  exact (h.setup hC).mul_not_mem_of_commutator_ne_top hne (h.mem_lclass hC he heP)
    (h.mem_lclass hC hf hfP) (h.mem_lclass hC hefD (P.mul_mem heP hfP))

theorem isBenderGroup_pCore (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    CFSG.BenderSuzuki.IsBenderGroup (lsub D x P ⧸ CFSG.pCore 2 (lsub D x P)) := by
  have e := QuotientGroup.quotientMulEquivOfEq (h.solvableRadical_eq_pCore hB hC)
  rcases h.isBenderGroup hB hC with ⟨n, hn, f⟩ | ⟨n, hn, f⟩ | ⟨n, hn, f⟩
  · exact .isPSL2 n hn (e.symm.trans f)
  · exact .isSuzuki n hn (e.symm.trans f)
  · exact .isPSU3 n hn (e.symm.trans f)

theorem pCore_not_le_center (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ¬ CFSG.pCore 2 (lsub D x P) ≤ Subgroup.center (lsub D x P) := by
  intro hle
  have := hC.setting.finite
  have hinf := Asc72.inf_commutator_eq_bot_of_isBenderGroup (h.setup hC) hle
    CFSG.pCore_isPGroup (h.isBenderGroup_pCore hB hC)
  rw [h.commutator_eq_top hC, inf_top_eq] at hinf
  have hz := h.z_mem_pCore hC
  rw [hinf, Subgroup.mem_bot] at hz
  exact h.hz1 (congrArg Subtype.val hz)

end Step6

end CFSG.Timmesfeld.Bridge
