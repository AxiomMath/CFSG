module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Core
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix
open scoped MatrixGroups

variable {X : Type*} [Group X]

theorem card_eq_card_map_mul_card_ker [Finite X] {Y : Type*} [Group Y] (f : X →* Y)
    {H : Subgroup X} (hH : f.ker ≤ H) : Nat.card H = Nat.card (H.map f) * Nat.card f.ker := by
  set g := f.subgroupMap H
  have hg : Function.Surjective g := f.subgroupMap_surjective H
  have hkerg : g.ker = f.ker.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hker : Nat.card g.ker = Nat.card f.ker := by
    rw [hkerg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker]

theorem card_eq_card_mul_card_ker [Finite X] {Y : Type*} [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) : Nat.card X = Nat.card Y * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

section Perfect

variable [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

omit [Finite X] in
theorem le_of_nontrivial_quotient (hK : Group.IsSolvable K) {N : Subgroup X} [N.Normal]
    (hN : Nontrivial (X ⧸ N)) : N ≤ K := by
  by_contra h
  have htop := eq_top_of_not_le hK h
  exact (QuotientGroup.nontrivial_iff.mp hN) htop

omit [Finite X] in
theorem map_eq_center (hK : Group.IsSolvable K) {J : Type*} [Group J] (hJ : IsQuasisimple J)
    (f : X →* J) (hf : Function.Surjective f) (hfK : f.ker ≤ K) : K.map f = Subgroup.center J := by
  apply le_antisymm
  · have hM : (K.map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases LocalCores.quasisimple_normal_subgroups hJ hM with h | h
    · exfalso
      have hKtop : K = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : f x ∈ K.map f := by
          rw [h]
          trivial
        obtain ⟨k, hk, hkx⟩ := hx
        have hkx' : k⁻¹ * x ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
        simpa using K.mul_mem hk (hfK hkx')
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) hKtop
    · exact h
  · set L := (Subgroup.center J).comap f
    have hL : L.Normal := Subgroup.Normal.comap inferInstance f
    set g : L →* Subgroup.center J := (f.comp L.subtype).codRestrict (Subgroup.center J)
      (fun x => x.2)
    have hKL : Group.IsSolvable (K ⊓ L : Subgroup X) := by
      have := hK
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : K ⊓ L ≤ K))
    have hker : g.ker ≤ (Subgroup.inclusion (inf_le_right : K ⊓ L ≤ L)).range := by
      intro x hx
      have hx' : f x = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
      exact ⟨⟨x, hfK hx', x.2⟩, rfl⟩
    have hLsol : Group.IsSolvable L := Group.isSolvable_of_ker_le_range _ g hker
    have hLK := le_of_isSolvable_of_normal (K := K) hL hLsol
    intro z hz
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨x, hLK hz, rfl⟩

theorem card_quotient_mul_card_center (hK : Group.IsSolvable K) {N : Subgroup X} [N.Normal]
    (hNK : N ≤ K) {J : Type*} [Group J] (hJ : IsQuasisimple J) (e : X ⧸ N ≃* J) :
    Nat.card (X ⧸ K) * Nat.card (Subgroup.center J) = Nat.card J := by
  set f : X →* J := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : f.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ N
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hfK : f.ker ≤ K := hker ▸ hNK
  have hmap := map_eq_center hK hJ f hf hfK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have h2 := card_eq_card_map_mul_card_ker f hfK
  have h3 := card_eq_card_mul_card_ker f hf
  rw [hmap] at h2
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h3, h1, h2, mul_assoc]

end Perfect

theorem pCore_le_ker [Finite X] {J : Type*} [Group J] (hJ : IsQuasisimple J)
    (hZ : Nat.card (Subgroup.center J) ∣ 2) (f : X →* J) (hf : Function.Surjective f) {q : ℕ}
    [hq : Fact q.Prime] (hq2 : q ≠ 2) : pCore q X ≤ f.ker := by
  have : Finite J := Finite.of_surjective f hf
  have : (pCore q X).Normal := pCore_normal
  have hM : ((pCore q X).map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hMq : IsPGroup q ((pCore q X).map f) := pCore_isPGroup.map f
  rcases LocalCores.quasisimple_normal_subgroups hJ hM with h | h
  · exfalso
    have hJq : IsPGroup q J := fun j => by
      obtain ⟨k, hk⟩ := hMq ⟨j, h ▸ Subgroup.mem_top j⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Group.IsNilpotent J := hJq.isNilpotent
    have := hJ.1
    have : Nontrivial (J ⧸ Subgroup.center J) := hJ.2.1.toNontrivial
    have : Nontrivial J := (QuotientGroup.mk'_surjective (Subgroup.center J)).nontrivial
    exact Group.IsPerfect.not_isSolvable J inferInstance
  · rw [← Subgroup.map_eq_bot_iff]
    obtain ⟨k, hk⟩ := hMq.exists_card_eq
    have hdvd : Nat.card ((pCore q X).map f) ∣ 2 := (Subgroup.card_dvd_of_le h).trans hZ
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have : q ∣ 2 := (dvd_pow_self q hk0).trans hdvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk

theorem fittingSubgroup_le_ker [Finite X] (hO2 : pCore 2 X = ⊥) {J : Type*} [Group J]
    (hJ : IsQuasisimple J) (hZ : Nat.card (Subgroup.center J) ∣ 2) (f : X →* J)
    (hf : Function.Surjective f) : fittingSubgroup X ≤ f.ker := by
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2, hO2]
    exact bot_le
  · exact pCore_le_ker hJ hZ f hf hq2

theorem pCore_eq_fittingSubgroup [Finite X] [Group.IsPerfect X] {p : ℕ} [hp : Fact p.Prime]
    (hO2 : pCore 2 X = ⊥) (hF : fittingSubgroup X ≤ pCore p X ⊔ Subgroup.center X)
    {J : Type*} [Group J] (e : X ⧸ fittingSubgroup X ≃* J)
    (hcyc : ∀ r : ℕ, ∀ _ : Fact r.Prime, r ≠ 2 → r ≠ p → ∃ Q : Sylow r J, IsCyclic Q) :
    pCore p X = fittingSubgroup X := by
  set P := pCore p X with hPdef
  have : P.Normal := pCore_normal
  have hPF : P ≤ fittingSubgroup X := pCore_le_fitting X p
  set φ : X ⧸ P →* X ⧸ fittingSubgroup X :=
    QuotientGroup.map P (fittingSubgroup X) (MonoidHom.id X) (by simpa using hPF)
  set f : X ⧸ P →* J := e.toMonoidHom.comp φ
  have hf : Function.Surjective f := by
    intro j
    obtain ⟨x, hx⟩ := e.surjective j
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk y, hx⟩
  have hker : ∀ y : X, (QuotientGroup.mk y : X ⧸ P) ∈ f.ker ↔ y ∈ fittingSubgroup X := by
    intro y
    rw [MonoidHom.mem_ker]
    change e (φ (QuotientGroup.mk y)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    change (QuotientGroup.mk (MonoidHom.id X y) : X ⧸ fittingSubgroup X) = 1 ↔ _
    rw [MonoidHom.id_apply, QuotientGroup.eq_one_iff]
  have hcen : f.ker ≤ Subgroup.center (X ⧸ P) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hF ((hker y).mp hx))
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hz g')]
  have hprime : ∀ x ∈ f.ker, ∀ r : ℕ, r.Prime → orderOf x ≠ r := by
    intro x hx r hr hxr
    have : Fact r.Prime := ⟨hr⟩
    by_cases hr2p : r = 2 ∨ r = p
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy := (hker y).mp hx
      obtain ⟨a, b, hab, ha, hb, haz, hbz⟩ := exists_mul_eq_isPGroup_coprime y hr
      have hzF : Subgroup.zpowers y ≤ fittingSubgroup X := Subgroup.zpowers_le.mpr hy
      have haP : a ∈ P := by
        have haO := mem_pCore_of_mem_fittingSubgroup (hzF haz) ha
        rcases hr2p with rfl | rfl
        · rw [hO2] at haO
          rw [Subgroup.mem_bot.mp haO]
          exact P.one_mem
        · exact haO
      have hmk : (QuotientGroup.mk y : X ⧸ P) = QuotientGroup.mk b := by
        rw [← hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr haP, one_mul]
      have hdvd : orderOf (QuotientGroup.mk b : X ⧸ P) ∣ orderOf b :=
        orderOf_map_dvd (QuotientGroup.mk' P) b
      rw [← hmk, hxr] at hdvd
      have := Nat.Coprime.coprime_dvd_left hdvd hb
      rw [Nat.coprime_self] at this
      exact hr.one_lt.ne' this
    · push Not at hr2p
      obtain ⟨Q, hQ⟩ := hcyc r ⟨hr⟩ hr2p.1 hr2p.2
      have hpg : IsPGroup r (Subgroup.zpowers (⟨x, hx⟩ : f.ker)) := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hxr]
      obtain ⟨C, hC⟩ := hpg.exists_le_sylow
      have hCbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hf hcen
        C Q hQ
      have hx1 : (⟨x, hx⟩ : f.ker) = 1 := by
        have := hC (Subgroup.mem_zpowers _)
        rw [hCbot] at this
        exact Subgroup.mem_bot.mp this
      have : x = 1 := congrArg Subtype.val hx1
      rw [this, orderOf_one] at hxr
      exact hr.one_lt.ne hxr
  have hbot : f.ker = ⊥ := by
    by_contra hne
    have : Nontrivial f.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := f.ker)).ne'
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) r hrd
    exact hprime x x.2 r hr (by rw [← Subgroup.orderOf_coe] at hx; exact hx)
  refine le_antisymm hPF fun y hy => ?_
  have := (hker y).mpr hy
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
  exact this

theorem mul_sq_sub_one_lt {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    n * (n ^ 2 - 1) < m * (m ^ 2 - 1) := by
  have h1 : n ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hnm two_ne_zero
  have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · simp only [one_pow, Nat.sub_self, mul_zero]
    have : 1 < m ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  · exact Nat.mul_lt_mul'' hnm (by omega)

theorem eq_of_mul_sq_sub_one_eq {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : n * (n ^ 2 - 1) = m * (m ^ 2 - 1)) : n = m := by
  rcases lt_trichotomy n m with hnm | hnm | hnm
  · exact absurd h (mul_sq_sub_one_lt hn hnm).ne
  · exact hnm
  · exact absurd h (mul_sq_sub_one_lt hm hnm).ne'

theorem mul_sq_sub_one_ne_11232 (n : ℕ) : n * (n ^ 2 - 1) ≠ 11232 := by
  intro h
  rcases Nat.lt_or_ge n 23 with hn | hn
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp at h
    rcases Nat.lt_or_ge n 22 with hn' | hn'
    · have := mul_sq_sub_one_lt hn0 hn'
      norm_num at this
      omega
    · have : n = 22 := by omega
      subst this
      norm_num at h
  · rcases Nat.eq_or_lt_of_le hn with rfl | hn'
    · norm_num at h
    · have := mul_sq_sub_one_lt (by norm_num : 1 ≤ 23) hn'
      norm_num at this
      omega

section Perfect

variable [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem eq_of_SL25 (hK : Group.IsSolvable K) {N₁ N₂ : Subgroup X} [N₁.Normal] [N₂.Normal]
    (e₁ : X ⧸ N₁ ≃* SL(2, ZMod 5)) (e₂ : X ⧸ N₂ ≃* SL(2, ZMod 5)) : N₁ = N₂ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJ : IsQuasisimple SL(2, ZMod 5) := isQuasisimple_SL2 le_rfl
  have hZ : Nat.card (Subgroup.center SL(2, ZMod 5)) = 2 := card_center_SL2 (by norm_num)
  have hJc : Nat.card SL(2, ZMod 5) = 120 := by
    rw [card_SL2]
    norm_num
  have hnt : Nontrivial SL(2, ZMod 5) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hJc]
    norm_num
  have hnt₁ : Nontrivial (X ⧸ N₁) := e₁.toEquiv.nontrivial
  have hnt₂ : Nontrivial (X ⧸ N₂) := e₂.toEquiv.nontrivial
  have hN₁K : N₁ ≤ K := le_of_nontrivial_quotient hK hnt₁
  have hN₂K : N₂ ≤ K := le_of_nontrivial_quotient hK hnt₂
  have hXK : Nat.card (X ⧸ K) = 60 := by
    have := card_quotient_mul_card_center hK hN₁K hJ e₁
    rw [hZ, hJc] at this
    omega
  have hX₁ : Nat.card X = 120 * Nat.card N₁ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₁, Nat.card_congr e₁.toEquiv, hJc]
  have hX₂ : Nat.card X = 120 * Nat.card N₂ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₂, Nat.card_congr e₂.toEquiv, hJc]
  have hXK' : Nat.card X = 60 * Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, hXK]
  have hc12 : Nat.card N₁ = Nat.card N₂ := by omega
  by_contra hne
  have h12 : ¬ N₁ ≤ N₂ := fun h => hne (Subgroup.eq_of_le_of_card_ge h hc12.symm.le)
  have hq₁ : IsQuasisimple (X ⧸ N₁) := LocalCores.isQuasisimple_of_mulEquiv e₁.symm hJ
  have hq₂ : IsQuasisimple (X ⧸ N₂) := LocalCores.isQuasisimple_of_mulEquiv e₂.symm hJ
  have hK₁ := map_eq_center hK hq₁ (QuotientGroup.mk' N₁) (QuotientGroup.mk'_surjective N₁)
    (by rw [QuotientGroup.ker_mk']; exact hN₁K)
  have hK₂ := map_eq_center hK hq₂ (QuotientGroup.mk' N₂) (QuotientGroup.mk'_surjective N₂)
    (by rw [QuotientGroup.ker_mk']; exact hN₂K)
  have hZ₂ : Nat.card (Subgroup.center (X ⧸ N₂)) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e₂).toEquiv, hZ]
  set I := N₁ ⊓ N₂ with hI
  have hIK : I ≤ K := inf_le_left.trans hN₁K
  have hN₁I : Nat.card N₁ = 2 * Nat.card I := by
    set g : N₁ →* X ⧸ N₂ := (QuotientGroup.mk' N₂).comp N₁.subtype
    have hrange : g.range = N₁.map (QuotientGroup.mk' N₂) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hA : Nat.card g.range = 2 := by
      have hle : g.range ≤ Subgroup.center (X ⧸ N₂) := by
        rw [hrange, ← hK₂]
        exact Subgroup.map_mono hN₁K
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [hZ₂] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exfalso
        apply h12
        intro x hx
        have h1 : g.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h
        have : g ⟨x, hx⟩ = 1 := by
          have hmem : g ⟨x, hx⟩ ∈ g.range := ⟨⟨x, hx⟩, rfl⟩
          rw [h1, Subgroup.mem_bot] at hmem
          exact hmem
        exact (QuotientGroup.eq_one_iff x).mp this
      · exact h
    have hkerg : Nat.card g.ker = Nat.card I := by
      have : g.ker = N₂.subgroupOf N₁ := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact QuotientGroup.eq_one_iff (x : X)
      rw [this, ← Subgroup.card_map_of_injective N₁.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    have := card_eq_card_mul_card_ker g.rangeRestrict g.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict, hkerg, hA] at this
    exact this
  have hKI : Nat.card K = 4 * Nat.card I := by omega
  set f₂ : X →* SL(2, ZMod 5) := e₂.toMonoidHom.comp (QuotientGroup.mk' N₂)
  have hf₂ : Function.Surjective f₂ := e₂.surjective.comp (QuotientGroup.mk'_surjective N₂)
  have hkerf₂ : f₂.ker = N₂ := by
    ext x
    rw [MonoidHom.mem_ker]
    change e₂ (QuotientGroup.mk x) = 1 ↔ x ∈ N₂
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hKf₂ := map_eq_center hK hJ f₂ hf₂ (hkerf₂ ▸ hN₂K)
  set φ : X →* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) :=
    (QuotientGroup.mk' (Subgroup.center SL(2, ZMod 5))).comp f₂
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf₂
  have hkerφ : φ.ker = K := by
    have : φ.ker = (Subgroup.center SL(2, ZMod 5)).comap f₂ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      exact QuotientGroup.eq_one_iff (f₂ x)
    rw [this, ← hKf₂, Subgroup.comap_map_eq, hkerf₂, sup_eq_left.mpr hN₂K]
  set f' : X ⧸ I →* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) :=
    QuotientGroup.lift I φ (hkerφ ▸ hIK)
  have hf' : Function.Surjective f' := by
    intro z
    obtain ⟨x, rfl⟩ := hφ z
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hkerf' : f'.ker = K.map (QuotientGroup.mk' I) := by
    rw [QuotientGroup.ker_lift, hkerφ]
  have hcen : f'.ker ≤ Subgroup.center (X ⧸ I) := by
    rw [hkerf']
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    have hc₁ : (QuotientGroup.mk' N₁ k) ∈ Subgroup.center (X ⧸ N₁) := hK₁ ▸ ⟨k, hk, rfl⟩
    have hc₂ : (QuotientGroup.mk' N₂ k) ∈ Subgroup.center (X ⧸ N₂) := hK₂ ▸ ⟨k, hk, rfl⟩
    have h₁ : g' * k * (k * g')⁻¹ ∈ N₁ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      have := Subgroup.mem_center_iff.mp hc₁ (QuotientGroup.mk g')
      change (QuotientGroup.mk g' : X ⧸ N₁) * QuotientGroup.mk k =
        QuotientGroup.mk k * QuotientGroup.mk g' at this
      rw [this, mul_inv_cancel]
    have h₂ : g' * k * (k * g')⁻¹ ∈ N₂ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      have := Subgroup.mem_center_iff.mp hc₂ (QuotientGroup.mk g')
      change (QuotientGroup.mk g' : X ⧸ N₂) * QuotientGroup.mk k =
        QuotientGroup.mk k * QuotientGroup.mk g' at this
      rw [this, mul_inv_cancel]
    change (QuotientGroup.mk (g' * k) : X ⧸ I) = QuotientGroup.mk (k * g')
    have hc : g' * k * (k * g')⁻¹ ∈ I := ⟨h₁, h₂⟩
    have hIn : I.Normal := inferInstance
    have := hIn.conj_mem _ (I.inv_mem hc) (g' * k)⁻¹
    rw [QuotientGroup.eq, show (g' * k)⁻¹ * (k * g') = (g' * k)⁻¹ * (g' * k * (k * g')⁻¹)⁻¹ *
      ((g' * k)⁻¹)⁻¹ by group]
    exact this
  have hcard : Nat.card f'.ker = 4 := by
    rw [hkerf']
    have := card_eq_card_map_mul_card_ker (QuotientGroup.mk' I) (H := K)
      (by rw [QuotientGroup.ker_mk']; exact hIK)
    rw [QuotientGroup.ker_mk', hKI] at this
    have hIpos : 0 < Nat.card I := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hIpos this.symm
  obtain ⟨Q, hQe, hQc⟩ := exists_sylow_two_PSL25
  obtain ⟨C⟩ : Nonempty (Sylow 2 f'.ker) := inferInstance
  have hbound := (CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
    f' hf' hcen C Q hQe hQc).2
  have hC : Nat.card C = 4 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    have : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [this]
    norm_num
  omega

end Perfect

@[expose] def LinearOutcome (X : Type*) [Group X] (p : ℕ) (N : Subgroup X) [N.Normal] : Prop :=
  (∀ y ∈ N, Nat.Coprime (orderOf y) p → ∀ x ∈ pCore p X, y * x = x * y) ∧
    ((3 < p ∧ Nonempty (X ⧸ N ≃* SL(2, ZMod p))) ∨ Nonempty (X ⧸ N ≃* SL(2, ZMod 5)) ∨
      (p = 3 ∧ Nonempty (X ⧸ N ≃* SL(3, ZMod 3))))

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by norm_num)

theorem eq_fittingSubgroup_of_forall [Finite X] (hO2 : pCore 2 X = ⊥)
    (hCF : Subgroup.centralizer (fittingSubgroup X : Set X) ≤ fittingSubgroup X)
    {N : Subgroup X} [N.Normal]
    (hcop : ∀ r : ℕ, r.Prime → ∀ y ∈ N, Nat.Coprime (orderOf y) r →
      ∀ x ∈ pCore r X, y * x = x * y)
    {J : Type*} [Group J] (hJ : IsQuasisimple J) (hZ : Nat.card (Subgroup.center J) ∣ 2)
    (e : X ⧸ N ≃* J) : N = fittingSubgroup X := by
  refine le_antisymm (le_fittingSubgroup_of_forall_coprime hCF hcop) ?_
  have hf : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' N)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ N
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have := fittingSubgroup_le_ker hO2 hJ hZ _ hf
  rwa [hker] at this

section Endgame

variable [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem card_quotient_of_SL2 (hK : Group.IsSolvable K) {N : Subgroup X} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (e : X ⧸ N ≃* SL(2, ZMod p)) :
    Nat.card (X ⧸ K) * 2 = p * (p ^ 2 - 1) := by
  have hJ := isQuasisimple_SL2 (p := p) hp5
  have : Nontrivial (SL(2, ZMod p) ⧸ Subgroup.center SL(2, ZMod p)) := hJ.2.1.toNontrivial
  have : Nontrivial SL(2, ZMod p) :=
    (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ZMod p))).nontrivial
  have hnt : Nontrivial (X ⧸ N) := e.toEquiv.nontrivial
  have := card_quotient_mul_card_center hK (le_of_nontrivial_quotient hK hnt) hJ e
  rwa [card_center_SL2 (by omega), card_SL2] at this

theorem card_quotient_of_SL3 (hK : Group.IsSolvable K) {N : Subgroup X} [N.Normal]
    (e : X ⧸ N ≃* SL(3, ZMod 3)) : Nat.card (X ⧸ K) = 5616 := by
  have hJ := isQuasisimple_SL3_three
  have : Nontrivial (SL(3, ZMod 3) ⧸ Subgroup.center SL(3, ZMod 3)) := hJ.2.1.toNontrivial
  have : Nontrivial SL(3, ZMod 3) :=
    (QuotientGroup.mk'_surjective (Subgroup.center SL(3, ZMod 3))).nontrivial
  have hnt : Nontrivial (X ⧸ N) := e.toEquiv.nontrivial
  have := card_quotient_mul_card_center hK (le_of_nontrivial_quotient hK hnt) hJ e
  rwa [center_SL3_three, Subgroup.card_bot, mul_one, card_SL3_three] at this

theorem linear_endgame (hK : Group.IsSolvable K) (hO2 : pCore 2 X = ⊥) {p₀ : ℕ}
    (hp₀ : p₀.Prime) (hS₀ : Subgroup.centralizer (pCore p₀ X : Set X) ≤ K)
    (hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p X : Set X) ≤ K →
      ∃ (N : Subgroup X) (_ : N.Normal), LinearOutcome X p N) :
    Nonempty (X ⧸ fittingSubgroup X ≃* SL(2, ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ Nonempty (X ⧸ pCore p X ≃* SL(2, ZMod p))) ∨
      Nonempty (X ⧸ pCore 3 X ≃* SL(3, ZMod 3)) := by
  have : Fact p₀.Prime := ⟨hp₀⟩
  have hCF := centralizer_fittingSubgroup_le hK hS₀
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcen : ∀ r : ℕ, r.Prime → ¬ Subgroup.centralizer (pCore r X : Set X) ≤ K →
      ∀ y : X, ∀ x ∈ pCore r X, y * x = x * y := by
    intro r hr hrS y x hx
    have : Fact r.Prime := ⟨hr⟩
    exact Subgroup.mem_center_iff.mp (pCore_le_center_of_not_le hK r hrS hx) y
  have hord : ∀ q : ℕ, q.Prime → Subgroup.centralizer (pCore q X : Set X) ≤ K →
      (3 < q ∧ Nat.card (X ⧸ K) * 2 = q * (q ^ 2 - 1)) ∨ Nat.card (X ⧸ K) = 60 ∨
        (q = 3 ∧ Nat.card (X ⧸ K) = 5616) := by
    intro q hq hqS
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨N, hN, hl⟩ := hlin q hq hqS
    rcases hl.2 with ⟨hq3, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
    · exact Or.inl ⟨hq3, card_quotient_of_SL2 hK (five_le_of_prime hq hq3) e⟩
    · have := card_quotient_of_SL2 hK (p := 5) le_rfl e
      norm_num at this
      exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr ⟨rfl, card_quotient_of_SL3 hK e⟩)
  by_cases hA : ∃ p : ℕ, p.Prime ∧ Subgroup.centralizer (pCore p X : Set X) ≤ K ∧
      ∃ (N : Subgroup X) (_ : N.Normal), LinearOutcome X p N ∧
        ((3 < p ∧ p ≠ 5 ∧ Nonempty (X ⧸ N ≃* SL(2, ZMod p))) ∨
          (p = 3 ∧ Nonempty (X ⧸ N ≃* SL(3, ZMod 3))))
  · obtain ⟨p, hp, hpS, N, hN, hlinN, htype⟩ := hA
    have : Fact p.Prime := ⟨hp⟩
    have hSp : ∀ q : ℕ, q.Prime → Subgroup.centralizer (pCore q X : Set X) ≤ K → q = p := by
      intro q hq hqS
      rcases htype with ⟨hp3, hp5, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
      · have hp' := card_quotient_of_SL2 hK (five_le_of_prime hp hp3) e
        rcases hord q hq hqS with ⟨hq3, hq'⟩ | h60 | ⟨rfl, h5616⟩
        · exact eq_of_mul_sq_sub_one_eq (by omega) (by omega) (hq'.symm.trans hp')
        · exfalso
          rw [h60] at hp'
          exact hp5 (eq_of_mul_sq_sub_one_eq (by omega) (by norm_num) (by rw [← hp']; norm_num))
        · exfalso
          rw [h5616] at hp'
          exact mul_sq_sub_one_ne_11232 p (by rw [← hp'])
      · have h3 := card_quotient_of_SL3 hK e
        rcases hord q hq hqS with ⟨hq3, hq'⟩ | h60 | ⟨rfl, -⟩
        · exfalso
          rw [h3] at hq'
          exact mul_sq_sub_one_ne_11232 q (by rw [← hq'])
        · omega
        · rfl
    have hcop : ∀ r : ℕ, r.Prime → ∀ y ∈ N, Nat.Coprime (orderOf y) r →
        ∀ x ∈ pCore r X, y * x = x * y := by
      intro r hr y hy hyr x hx
      by_cases hrS : Subgroup.centralizer (pCore r X : Set X) ≤ K
      · have hrp := hSp r hr hrS
        subst hrp
        exact hlinN.1 y hy hyr x hx
      · exact hcen r hr hrS y x hx
    have hFZ : fittingSubgroup X ≤ pCore p X ⊔ Subgroup.center X := by
      rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
      refine iSup_le fun q => ?_
      have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
      have : Fact (q : ℕ).Prime := ⟨hq⟩
      by_cases hqp : (q : ℕ) = p
      · rw [hqp]
        exact le_sup_left
      · exact (pCore_le_center_of_not_le hK q fun h => hqp (hSp q hq h)).trans le_sup_right
    rcases htype with ⟨hp3, -, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
    · have hNF := eq_fittingSubgroup_of_forall hO2 hCF hcop
        (isQuasisimple_SL2 (five_le_of_prime hp hp3)) (by rw [card_center_SL2 (by omega)]) e
      have e' : X ⧸ fittingSubgroup X ≃* SL(2, ZMod p) :=
        (QuotientGroup.quotientMulEquivOfEq hNF.symm).trans e
      have hPF := pCore_eq_fittingSubgroup hO2 hFZ e' fun r _ hr2 hrp =>
        ⟨Classical.arbitrary _, isCyclic_sylow_SL2 hr2 hrp _⟩
      exact Or.inr (Or.inl ⟨p, hp, hp3, ⟨(QuotientGroup.quotientMulEquivOfEq hPF).trans e'⟩⟩)
    · have hNF := eq_fittingSubgroup_of_forall hO2 hCF hcop isQuasisimple_SL3_three
        (by rw [center_SL3_three, Subgroup.card_bot]; exact one_dvd 2) e
      have e' : X ⧸ fittingSubgroup X ≃* SL(3, ZMod 3) :=
        (QuotientGroup.quotientMulEquivOfEq hNF.symm).trans e
      have hPF := pCore_eq_fittingSubgroup hO2 hFZ e' fun r _ hr2 hr3 =>
        ⟨Classical.arbitrary _, isCyclic_sylow_SL3_three hr2 hr3 _⟩
      exact Or.inr (Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq hPF).trans e'⟩)
  ·
    push Not at hA
    have h5 : ∀ q : ℕ, q.Prime → Subgroup.centralizer (pCore q X : Set X) ≤ K →
        ∃ (N : Subgroup X) (_ : N.Normal), LinearOutcome X q N ∧
          Nonempty (X ⧸ N ≃* SL(2, ZMod 5)) := by
      intro q hq hqS
      obtain ⟨N, hN, hl⟩ := hlin q hq hqS
      refine ⟨N, hN, hl, ?_⟩
      rcases hl.2 with ⟨hq3, ⟨e⟩⟩ | h | ⟨hq3, ⟨e⟩⟩
      · by_cases hq5 : q = 5
        · subst hq5
          exact ⟨e⟩
        · exact (((hA q hq hqS N hN hl).1 hq3 hq5).false e).elim
      · exact h
      · exact (((hA q hq hqS N hN hl).2 hq3).false e).elim
    obtain ⟨N₀, hN₀, hl₀, ⟨e₀⟩⟩ := h5 p₀ hp₀ hS₀
    have hcop : ∀ r : ℕ, r.Prime → ∀ y ∈ N₀, Nat.Coprime (orderOf y) r →
        ∀ x ∈ pCore r X, y * x = x * y := by
      intro r hr y hy hyr x hx
      by_cases hrS : Subgroup.centralizer (pCore r X : Set X) ≤ K
      · obtain ⟨N, hN, hl, ⟨e⟩⟩ := h5 r hr hrS
        have hNN : N₀ = N := eq_of_SL25 hK e₀ e
        exact hl.1 y (hNN ▸ hy) hyr x hx
      · exact hcen r hr hrS y x hx
    have hNF := eq_fittingSubgroup_of_forall hO2 hCF hcop (isQuasisimple_SL2 (p := 5) le_rfl)
      (by rw [card_center_SL2 (by norm_num)]) e₀
    exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hNF.symm).trans e₀⟩

end Endgame

end CFSG.RankThree.PartTwo.Sec4.Census
