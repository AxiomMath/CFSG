module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

namespace HS6

section Abs

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] noncomputable def sylowOfLe {S U : Subgroup Γ} (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2) : Sylow 2 S :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (U.subgroupOf S) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
    exact hcard)

theorem coe_sylowOfLe {S U : Subgroup Γ} (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2) :
    ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S) = U.subgroupOf S := rfl

theorem frattini_two {S U : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2) :
    Subgroup.normalizer (U : Set Γ) ⊔ S = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sylow.normalizer_sup_eq_top (sylowOfLe hUS hcard)
  have e : (sylowOfLe hUS hcard : Sylow 2 S).map S.subtype = U := by
    rw [coe_sylowOfLe, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left hUS
  rwa [e] at h


private theorem finite_sylow (G : Type*) [Group G] [Finite G] (p : ℕ) : Finite (Sylow p G) :=
  Finite.of_injective (fun S : Sylow p G => ((S : Subgroup G) : Set G))
    (fun S T hST => Sylow.ext (SetLike.coe_injective hST))

private theorem card_dvd_sub_one {H X : Type*} [Group H] [Finite H] [MulAction H X] [Finite X]
    (x₀ : X) (hx₀ : ∀ h : H, h • x₀ = x₀)
    (hfree : ∀ (x : X) (h : H), x ≠ x₀ → h • x = x → h = 1) :
    Nat.card H ∣ Nat.card X - 1 := by
  classical
  haveI instH : Fintype H := Fintype.ofFinite H
  haveI instX : Fintype X := Fintype.ofFinite X
  haveI instΩ : Fintype (Quotient (MulAction.orbitRel H X)) := Fintype.ofFinite _
  haveI instFix : ∀ g : H, Fintype (MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  have hfix1 : Fintype.card (MulAction.fixedBy X (1 : H)) = Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      (Equiv.subtypeUnivEquiv fun x => MulAction.mem_fixedBy.mpr (one_smul H x))
  have hfixne : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1 := by
    intro g hg
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨x₀, MulAction.mem_fixedBy.mpr (hx₀ g)⟩, fun y => ?_⟩
    apply Subtype.ext
    by_contra hne
    exact hg (hfree y.1 g hne (MulAction.mem_fixedBy.mp y.2))
  have hBurn : ∑ g : H, Fintype.card (MulAction.fixedBy X g)
      = Fintype.card (Quotient (MulAction.orbitRel H X)) * Fintype.card H :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H X
  have hsplit : ∑ g : H, Fintype.card (MulAction.fixedBy X g)
      = Fintype.card X + (Fintype.card H - 1) := by
    have h1 : ∑ g ∈ (Finset.univ : Finset H).erase 1, Fintype.card (MulAction.fixedBy X g)
        = ∑ _g ∈ (Finset.univ : Finset H).erase 1, (1 : ℕ) :=
      Finset.sum_congr rfl fun g hg => hfixne g (Finset.ne_of_mem_erase hg)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H)), h1, hfix1]
    simp [Finset.card_erase_of_mem]
  have hcardX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x₀⟩
  have hcardH : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨1⟩
  have key : Fintype.card X + (Fintype.card H - 1)
      = Fintype.card (Quotient (MulAction.orbitRel H X)) * Fintype.card H :=
    hsplit.symm.trans hBurn
  have h2 : Fintype.card X - 1
      = Fintype.card (Quotient (MulAction.orbitRel H X)) * Fintype.card H
        - Fintype.card H := by
    omega
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h2, ← Nat.sub_one_mul]
  exact dvd_mul_left _ _

private theorem eq_succ_of_modEq_one_of_dvd {q n : ℕ} (hq : 2 ≤ q) (hmod : n ≡ 1 [MOD q])
    (hdvd : n ∣ q ^ 2 - 1) (hn : n ≠ 1) : n = q + 1 := by
  have hsq : q ^ 2 = q * q := by ring
  have hq4 : 4 ≤ q * q := by nlinarith
  rw [hsq] at hdvd
  obtain ⟨e, he⟩ := hdvd
  have h5 : n * e + 1 = q * q := by omega
  have hmod' : n % q = 1 % q := hmod
  have hn1 : n % q = 1 := by
    rw [hmod']
    exact Nat.mod_eq_of_lt (by omega)
  have hkex : ∃ k, n = q * k + 1 := by
    refine ⟨n / q, ?_⟩
    have := Nat.div_add_mod n q
    rw [hn1] at this
    omega
  obtain ⟨k, hk⟩ := hkex
  have hk1 : 1 ≤ k := by
    by_contra hcon
    have hk0 : k = 0 := by omega
    subst hk0
    exact hn (by omega)
  have hqn : q + 1 ≤ n := by nlinarith
  have heq : e < q := by
    by_contra hcon
    have hqe : q ≤ e := by omega
    have h1 : (q + 1) * q ≤ n * e := Nat.mul_le_mul hqn hqe
    nlinarith
  have hdvd2 : q ∣ e + 1 := by
    have h3 : q * q - 1 = q * (k * e) + e := by
      rw [he, hk]
      ring
    have h2 : q * (k * e) + (e + 1) = q * q := by omega
    have h4 : q ∣ q * (k * e) + (e + 1) := by
      rw [h2]
      exact dvd_mul_right q q
    exact (Nat.dvd_add_right (dvd_mul_right q (k * e))).mp h4
  have hle : q ≤ e + 1 := Nat.le_of_dvd (by omega) hdvd2
  have hq1 : e + 1 = q := by omega
  have h6 : q * q = q * e + q := by
    rw [← hq1]
    ring
  have h7 : n * e = (q + 1) * e := by linarith
  have he_pos : 0 < e := by omega
  exact Nat.eq_of_mul_eq_mul_right he_pos h7

theorem sylow_inf_eq_bot {S U : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hTI : ∀ g : Γ, U ⊓ conjSubgroup g U = ⊥ ∨ conjSubgroup g U = U)
    (Q : Sylow 2 S) (hQ : Q ≠ sylowOfLe hUS hcard) :
    ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S) ⊓ (Q : Subgroup S) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_sylow S 2
  set P := sylowOfLe hUS hcard with hP
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq S P Q
  have hmem : ∀ z : S, z ∈ ((g • P : Sylow 2 S) : Subgroup S) ↔
      ∃ s : S, (s : Γ) ∈ U ∧ g * s * g⁻¹ = z := by
    intro z
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, Subgroup.mem_subgroupOf.mp hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [eq_bot_iff]
  intro x ⟨hxP, hxQ⟩
  rw [Subgroup.mem_bot]
  have hxU : (x : Γ) ∈ U := Subgroup.mem_subgroupOf.mp hxP
  obtain ⟨s, hsU, hsx⟩ := (hmem x).mp hxQ
  have hxc : (x : Γ) ∈ conjSubgroup (g : Γ) U := by
    rw [mem_conjSubgroup]
    have : (g : Γ)⁻¹ * (x : Γ) * g = s := by
      rw [← hsx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact hsU
  rcases hTI (g : Γ) with h | h
  · have : (x : Γ) ∈ U ⊓ conjSubgroup (g : Γ) U := ⟨hxU, hxc⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  · exfalso
    apply hQ
    have hPeq : g • P = P := by
      refine Sylow.ext (le_antisymm ?_ ?_)
      · intro z hz
        obtain ⟨s', hs', hsz⟩ := (hmem z).mp hz
        refine Subgroup.mem_subgroupOf.mpr ?_
        have : (z : Γ) ∈ conjSubgroup (g : Γ) U := by
          rw [mem_conjSubgroup]
          have : (g : Γ)⁻¹ * (z : Γ) * g = s' := by
            rw [← hsz]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [this]
          exact hs'
        rwa [h] at this
      · intro z hz
        refine (hmem z).mpr ⟨⟨(g : Γ)⁻¹ * (z : Γ) * g, ?_⟩, ?_, ?_⟩
        · exact S.mul_mem (S.mul_mem (S.inv_mem g.2) z.2) g.2
        · have hzU : (z : Γ) ∈ U := Subgroup.mem_subgroupOf.mp hz
          have : (z : Γ) ∈ conjSubgroup (g : Γ) U := by rw [h]; exact hzU
          exact mem_conjSubgroup.mp this
        · apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
    exact hPeq


theorem sylow_free {S U : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hTI : ∀ g : Γ, U ⊓ conjSubgroup g U = ⊥ ∨ conjSubgroup g U = U)
    (Q : Sylow 2 S) (hQ : Q ≠ sylowOfLe hUS hcard) (h : S) (hh : (h : Γ) ∈ U)
    (hhQ : h • Q = Q) : h = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := sylowOfLe hUS hcard with hP
  have h1 : h ∈ Subgroup.normalizer (Q : Set S) := Sylow.smul_eq_iff_mem_normalizer.mp hhQ
  have hhP : h ∈ (P : Subgroup S) := Subgroup.mem_subgroupOf.mpr hh
  have h2 : h ∈ (P : Subgroup S) ⊓ Subgroup.normalizer (Q : Set S) := ⟨hhP, h1⟩
  rw [P.isPGroup'.inf_normalizer_sylow Q, sylow_inf_eq_bot hUS hcard hTI Q hQ] at h2
  exact Subgroup.mem_bot.mp h2

theorem sylow_not_normal {S U : Subgroup Γ} (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hScard : Nat.card S = Nat.card U * (Nat.card U ^ 2 - 1)) (hq4 : 4 ≤ Nat.card U)
    (hSsimple : IsSimpleGroup S) :
    ¬ ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S).Normal := by
  intro hN
  have hPcard : Nat.card ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S) = Nat.card U := by
    rw [coe_sylowOfLe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  rcases hSsimple.eq_bot_or_eq_top_of_normal ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S)
    with h | h
  · have : Nat.card ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S) = 1 := by
      rw [h]; exact Subgroup.card_bot
    omega
  · have h3 : Nat.card ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S) = Nat.card S := by
      rw [h]; exact Subgroup.card_top
    rw [hPcard, hScard] at h3
    have hqpos : 0 < Nat.card U := Nat.card_pos
    have h4 : Nat.card U ^ 2 - 1 = 1 := by
      have h5 : Nat.card U * 1 = Nat.card U * (Nat.card U ^ 2 - 1) := by rw [mul_one]; exact h3
      exact (Nat.eq_of_mul_eq_mul_left hqpos h5).symm
    have : 16 ≤ Nat.card U ^ 2 := by nlinarith
    omega

theorem card_sylow_two {S U : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hScard : Nat.card S = Nat.card U * (Nat.card U ^ 2 - 1)) (hq4 : 4 ≤ Nat.card U)
    (hSsimple : IsSimpleGroup S)
    (hTI : ∀ g : Γ, U ⊓ conjSubgroup g U = ⊥ ∨ conjSubgroup g U = U) :
    Nat.card (Sylow 2 S) = Nat.card U + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_sylow S 2
  set P := sylowOfLe hUS hcard with hP
  have hPcard : Nat.card (P : Subgroup S) = Nat.card U := by
    rw [coe_sylowOfLe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  have hmod : Nat.card (Sylow 2 S) ≡ 1 [MOD Nat.card U] := by
    have hd : Nat.card (P : Subgroup S) ∣ Nat.card (Sylow 2 S) - 1 :=
      card_dvd_sub_one (H := ↥(P : Subgroup S)) (X := Sylow 2 S) P
        (fun h => Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer h.2))
        (fun x h hx hhx => Subtype.ext (sylow_free hUS hcard hTI x hx h
          (Subgroup.mem_subgroupOf.mp h.2) hhx))
    rw [hPcard] at hd
    have hpos : 0 < Nat.card (Sylow 2 S) := Nat.card_pos
    exact ((Nat.modEq_iff_dvd' hpos).mpr hd).symm
  have hdvd : Nat.card (Sylow 2 S) ∣ Nat.card U ^ 2 - 1 := by
    have h1 := Sylow.card_dvd_index P
    have h2 : (P : Subgroup S).index * Nat.card (P : Subgroup S) = Nat.card S :=
      Subgroup.index_mul_card _
    rw [hPcard, hScard] at h2
    have hqpos : 0 < Nat.card U := Nat.card_pos
    have : (P : Subgroup S).index = Nat.card U ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_right hqpos (by rw [h2, mul_comm])
    rwa [this] at h1
  have hne : Nat.card (Sylow 2 S) ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow 2 S) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact sylow_not_normal hUS hcard hScard hq4 hSsimple (Sylow.normal_of_subsingleton P)
  exact eq_succ_of_modEq_one_of_dvd (by omega) hmod hdvd hne


theorem centralizes_of_perfect {S U Y : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hScard : Nat.card S = Nat.card U * (Nat.card U ^ 2 - 1)) (hq4 : 4 ≤ Nat.card U)
    (hSsimple : IsSimpleGroup S)
    (hTI : ∀ g : Γ, U ⊓ conjSubgroup g U = ⊥ ∨ conjSubgroup g U = U)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u = u * y) (hYperf : ⁅Y, Y⁆ = Y) :
    ∀ y ∈ Y, ∀ s ∈ S, y * s = s * y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_sylow S 2
  letI : MulAction Γ (Sylow 2 S) := MulAction.compHom _ (MulAut.conjNormal : Γ →* MulAut S)
  set P := sylowOfLe hUS hcard with hP
  have hn₂ := card_sylow_two hUS hcard hScard hq4 hSsimple hTI
  have hPcard : Nat.card (P : Subgroup S) = Nat.card U := by
    rw [hP, coe_sylowOfLe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  have hSact : ∀ (s : S) (Q : Sylow 2 S), ((s : Γ) • Q : Sylow 2 S) = s • Q := by
    intro s Q
    show (MulAut.conjNormal (s : Γ) : MulAut S) • Q = s • Q
    rw [MulAut.conjNormal_val]
    rfl
  have hYP : ∀ y ∈ Y, (y • P : Sylow 2 S) = P := by
    intro y hy
    refine Sylow.ext (le_antisymm ?_ ?_)
    · intro z hz
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hz
      have hhU : (h : Γ) ∈ U := Subgroup.mem_subgroupOf.mp hh
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : ((MulAut.conjNormal y : MulAut S) h : Γ) = y * h * y⁻¹ := by
        rw [MulAut.conjNormal_apply]
      show (((MulAut.conjNormal y : MulAut S) • h : S) : Γ) ∈ U
      rw [MulAut.smul_def, this, hYU y hy h hhU]
      simpa using hhU
    · intro z hz
      refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, hz, ?_⟩
      have hzU : (z : Γ) ∈ U := Subgroup.mem_subgroupOf.mp hz
      apply Subtype.ext
      show ((MulAut.conjNormal y : MulAut S) z : Γ) = z
      rw [MulAut.conjNormal_apply, hYU y hy z hzU]
      simp
  have hcomm : ∀ y ∈ Y, ∀ (u : S), (u : Γ) ∈ U → ∀ Q : Sylow 2 S,
      (y • (u • Q) : Sylow 2 S) = u • (y • Q) := by
    intro y hy u hu Q
    rw [← hSact u Q, ← hSact u (y • Q), ← mul_smul, ← mul_smul, hYU y hy u hu]
  have hfree : ∀ (Q : Sylow 2 S), Q ≠ P → ∀ (u : S), (u : Γ) ∈ U → u • Q = Q → u = 1 :=
    fun Q hQ u hu hq => sylow_free hUS hcard hTI Q hQ u hu hq
  have hPfix : ∀ (u : S), (u : Γ) ∈ U → u • P = P := fun u hu =>
    Sylow.smul_eq_iff_mem_normalizer.mpr
      (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mpr hu))
  have hUinv : ∀ (u : S), (u : Γ) ∈ U → ((u⁻¹ : S) : Γ) ∈ U := fun u hu => by
    simpa using U.inv_mem hu
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : Sylow 2 S, Q₀ ≠ P := by
    haveI : Nontrivial (Sylow 2 S) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne P
  have hne_of_smul : ∀ (u : S), (u : Γ) ∈ U → ∀ Q : Sylow 2 S, Q ≠ P → u • Q ≠ P := by
    intro u hu Q hQ h
    apply hQ
    rw [← inv_smul_smul u Q, h]
    exact hPfix _ (hUinv u hu)
  have hcardΩ₀ : Nat.card {Q : Sylow 2 S // Q ≠ P} = Nat.card U := by
    letI := Fintype.ofFinite (Sylow 2 S)
    classical
    have h1 := Fintype.card_subtype_compl (fun Q : Sylow 2 S => Q = P)
    have h2 := Fintype.card_subtype_eq P
    rw [Nat.card_eq_fintype_card] at hn₂ ⊢
    simp only [ne_eq] at h1 ⊢
    omega
  have hsurj : ∀ Q : Sylow 2 S, Q ≠ P → ∃ u : S, (u : Γ) ∈ U ∧ u • Q₀ = Q := by
    let f : ↥(P : Subgroup S) → {Q : Sylow 2 S // Q ≠ P} := fun u =>
      ⟨(u : S) • Q₀, hne_of_smul u (Subgroup.mem_subgroupOf.mp u.2) Q₀ hQ₀⟩
    have hf : Function.Injective f := by
      intro u u' h
      have h1 : (u : S) • Q₀ = (u' : S) • Q₀ := congrArg Subtype.val h
      have h2 : ((u : S)⁻¹ * (u' : S)) • Q₀ = Q₀ := by
        rw [mul_smul, ← h1, inv_smul_smul]
      have h3 : ((u : S)⁻¹ * (u' : S)) = 1 := by
        refine hfree Q₀ hQ₀ _ ?_ h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact U.mul_mem (U.inv_mem (Subgroup.mem_subgroupOf.mp u.2))
          (Subgroup.mem_subgroupOf.mp u'.2)
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    have hbij : Function.Bijective f :=
      hf.bijective_of_nat_card_le (by rw [hcardΩ₀, hPcard])
    intro Q hQ
    obtain ⟨u, hu⟩ := hbij.2 ⟨Q, hQ⟩
    exact ⟨u, Subgroup.mem_subgroupOf.mp u.2, congrArg Subtype.val hu⟩
  have hy_ne : ∀ y ∈ Y, (y • Q₀ : Sylow 2 S) ≠ P := by
    intro y hy h
    apply hQ₀
    rw [← inv_smul_smul y Q₀, h]
    exact hYP y⁻¹ (Y.inv_mem hy)
  have hcomm2 : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ((y₁ * y₂ : Γ) • Q₀ : Sylow 2 S) = (y₂ * y₁ : Γ) • Q₀ := by
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨u₁, hu₁, hu₁Q⟩ := hsurj (y₁ • Q₀) (hy_ne y₁ hy₁)
    obtain ⟨u₂, hu₂, hu₂Q⟩ := hsurj (y₂ • Q₀) (hy_ne y₂ hy₂)
    have hu₂u₁ : u₂ * u₁ = u₁ * u₂ := Subtype.ext (by simpa using hUab _ hu₂ _ hu₁)
    calc ((y₁ * y₂ : Γ) • Q₀ : Sylow 2 S) = y₁ • (y₂ • Q₀) := mul_smul _ _ _
      _ = y₁ • (u₂ • Q₀) := by rw [hu₂Q]
      _ = u₂ • (y₁ • Q₀) := hcomm y₁ hy₁ u₂ hu₂ Q₀
      _ = u₂ • (u₁ • Q₀) := by rw [hu₁Q]
      _ = (u₂ * u₁) • Q₀ := (mul_smul _ _ _).symm
      _ = (u₁ * u₂) • Q₀ := by rw [hu₂u₁]
      _ = u₁ • (u₂ • Q₀) := mul_smul _ _ _
      _ = u₁ • (y₂ • Q₀) := by rw [hu₂Q]
      _ = y₂ • (u₁ • Q₀) := (hcomm y₂ hy₂ u₁ hu₁ Q₀).symm
      _ = y₂ • (y₁ • Q₀) := by rw [hu₁Q]
      _ = ((y₂ * y₁ : Γ) • Q₀ : Sylow 2 S) := (mul_smul _ _ _).symm
  have hYstab : ∀ y ∈ Y, (y • Q₀ : Sylow 2 S) = Q₀ := by
    have hle : ⁅Y, Y⁆ ≤ MulAction.stabilizer Γ Q₀ := by
      rw [Subgroup.commutator_le]
      intro y₁ hy₁ y₂ hy₂
      rw [MulAction.mem_stabilizer_iff]
      have h := hcomm2 y₁⁻¹ (Y.inv_mem hy₁) y₂⁻¹ (Y.inv_mem hy₂)
      have e : ⁅y₁, y₂⁆ = (y₁ * y₂) * (y₁⁻¹ * y₂⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      have e2 : (y₁ * y₂) * (y₂⁻¹ * y₁⁻¹) = 1 := by group
      rw [e, mul_smul, h, ← mul_smul, e2, one_smul]
    rw [hYperf] at hle
    intro y hy
    exact MulAction.mem_stabilizer_iff.mp (hle hy)
  have hYall : ∀ y ∈ Y, ∀ Q : Sylow 2 S, (y • Q : Sylow 2 S) = Q := by
    intro y hy Q
    by_cases hQ : Q = P
    · rw [hQ]
      exact hYP y hy
    · obtain ⟨u, hu, rfl⟩ := hsurj Q hQ
      rw [hcomm y hy u hu, hYstab y hy]
  intro y hy s hs
  have hcS : y * s * y⁻¹ * s⁻¹ ∈ S := S.mul_mem (‹S.Normal›.conj_mem s hs y) (S.inv_mem hs)
  let c : S := ⟨y * s * y⁻¹ * s⁻¹, hcS⟩
  let κ : S →* Equiv.Perm (Sylow 2 S) := MulAction.toPermHom S (Sylow 2 S)
  have hcK : c ∈ κ.ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun Q => ?_
    show c • Q = Q
    rw [← hSact c Q]
    show (y * s * y⁻¹ * s⁻¹ : Γ) • Q = Q
    rw [mul_smul, mul_smul, mul_smul, hYall y⁻¹ (Y.inv_mem hy), smul_inv_smul, hYall y hy]
  have hKtop : κ.ker ≠ ⊤ := by
    intro htop
    apply sylow_not_normal hUS hcard hScard hq4 hSsimple
    haveI : ((sylowOfLe hUS hcard : Sylow 2 S) : Subgroup S).Normal := by
      refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => ?_)
      have hg : g ∈ κ.ker := by rw [htop]; exact Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp (congrArg (fun π => π P) (MonoidHom.mem_ker.mp hg))
    exact this
  have hKbot : κ.ker = ⊥ :=
    (hSsimple.eq_bot_or_eq_top_of_normal κ.ker).resolve_right hKtop
  rw [hKbot, Subgroup.mem_bot] at hcK
  have h1 : y * s * y⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hcK
  exact commutatorElement_eq_one_iff_mul_comm.mp h1


private theorem arith_normalizer (c x : ℕ) (hc : 1 ≤ c) (h : (c + 1) * x = c * (c ^ 2 - 1)) :
    x = c * (c - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have h5 : (d + 1) ^ 2 - 1 = (d + 1 + 1) * d := by
    have : (d + 1) ^ 2 = (d + 1 + 1) * d + 1 := by ring
    omega
  rw [h5] at h
  have h6 : (d + 1 + 1) * x = (d + 1 + 1) * ((d + 1) * d) := by rw [h]; ring
  rw [Nat.eq_of_mul_eq_mul_left (by omega) h6]
  simp

theorem card_normalizer_inf {S U : Subgroup Γ} [S.Normal] (hUS : U ≤ S)
    (hcard : Nat.card U = 2 ^ (Nat.card S).factorization 2)
    (hScard : Nat.card S = Nat.card U * (Nat.card U ^ 2 - 1)) (hq4 : 4 ≤ Nat.card U)
    (hSsimple : IsSimpleGroup S)
    (hTI : ∀ g : Γ, U ⊓ conjSubgroup g U = ⊥ ∨ conjSubgroup g U = U) :
    Nat.card ↥(Subgroup.normalizer (U : Set Γ) ⊓ S) = Nat.card U * (Nat.card U - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_sylow S 2
  set P := sylowOfLe hUS hcard with hP
  have hn₂ := card_sylow_two hUS hcard hScard hq4 hSsimple hTI
  have hPS : ∀ x : S, x ∈ (P : Subgroup S) ↔ (x : Γ) ∈ U := fun x => Subgroup.mem_subgroupOf
  have h1 : Subgroup.normalizer ((P : Subgroup S) : Set S) =
      (Subgroup.normalizer (U : Set Γ)).subgroupOf S := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h y
      constructor
      · intro hy
        have hyS : y ∈ S := hUS hy
        have := (h ⟨y, hyS⟩).mp ((hPS _).mpr hy)
        exact (hPS _).mp this
      · intro hy
        have hyS : (g : Γ)⁻¹ * ((g : Γ) * y * (g : Γ)⁻¹) * (g : Γ) ∈ S :=
          S.mul_mem (S.mul_mem (S.inv_mem g.2) (hUS hy)) g.2
        have hyS' : y ∈ S := by
          have e : (g : Γ)⁻¹ * ((g : Γ) * y * (g : Γ)⁻¹) * (g : Γ) = y := by group
          rwa [e] at hyS
        have := (h ⟨y, hyS'⟩).mpr ((hPS _).mpr hy)
        exact (hPS _).mp this
    · intro h x
      rw [hPS, hPS]
      exact h x
  have h2 : Nat.card ↥(Subgroup.normalizer (U : Set Γ) ⊓ S) =
      Nat.card ↥((Subgroup.normalizer (U : Set Γ)).subgroupOf S) := by
    have := Subgroup.subgroupOf_map_subtype (Subgroup.normalizer (U : Set Γ)) S
    rw [← this]
    exact Subgroup.card_map_of_injective S.subtype_injective
  have h3 := Subgroup.index_mul_card (Subgroup.normalizer ((P : Subgroup S) : Set S))
  have h4 : (Subgroup.normalizer ((P : Subgroup S) : Set S)).index = Nat.card U + 1 := by
    rw [← hn₂]
    exact (Sylow.card_eq_index_normalizer P).symm
  rw [h4, hScard] at h3
  rw [h2, ← h1]
  exact arith_normalizer _ _ (by omega) h3

end Abs

end HS6

end CFSG.RankThree.GF2n.Stroth80
