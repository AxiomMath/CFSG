module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rc
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_commutator_le_self {X : Type*} [Group X] (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem uc22p22r_pgrp2210_holds (D : Data G) (Ch : Choice2011 G) :
    H1930 D → ∀ c : Ctx22b D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf q Q (barPreimage D.M (CFSG.pCore q (Bar2 D.M))) →
      1 < CFSG.Open.pRank q Q → Q ⊓ centralizer (c.V : Set G) ≠ ⊥ →
      ∃ P : Subgroup G, P ≤ Q ∧ IsPGroup q ↥P ∧ (∀ x ∈ P, x ^ q = 1) ∧ ⁅⁅P, P⁆, P⁆ = ⊥ ∧
        ¬ IsCyclic ↥P ∧ (barImage D.M P).Normal ∧ P ⊓ centralizer (c.V : Set G) ≠ ⊥ := by
  classical
  intro _h1930 c q hq hq2 Q hQ hrank hQV
  haveI : Fact q.Prime := ⟨hq⟩
  set π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) with hπ
  set R : Subgroup (Bar2 D.M) := CFSG.pCore q (Bar2 D.M) with hRdef
  haveI hRn : R.Normal := CFSG.pCore_normal
  have hRq : IsPGroup q ↥R := CFSG.pCore_isPGroup
  have hQM : Q ≤ D.M := hQ.le.trans (uc22p21c_barPreimage_le _ _)
  have hQq : IsPGroup q ↥Q := hQ.isPGroup
  set Q' : Subgroup ↥D.M := Q.subgroupOf D.M with hQ'
  have hQ'q : IsPGroup q ↥Q' := hQq.comap_subtype
  have hkercop : q.Coprime (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have hinj : Function.Injective (π.comp Q'.subtype) :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup q hq π hkercop Q' hQ'q
  have hinj' : ∀ a ∈ Q', ∀ b ∈ Q', π a = π b → a = b := fun a ha b hb h =>
    congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)
  have hQ'R : Q'.map π ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨_, hxR⟩ := uc22p21c_mem_barPreimage.1 (hQ.le hx)
    exact hxR
  have hcardQ' : Nat.card ↥(Q'.map π) = Nat.card ↥Q := by
    have h1 : Nat.card ↥(Q'.map π) = Nat.card ↥Q' := by
      refine (Nat.card_congr (Equiv.ofBijective
        (fun x : ↥Q' => (⟨π x, (x : ↥D.M), x.2, rfl⟩ : ↥(Q'.map π))) ⟨?_, ?_⟩)).symm
      · intro a b hab
        exact hinj (congrArg Subtype.val hab)
      · rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hRle : Nat.card ↥R ≤ Nat.card ↥Q := by
    obtain ⟨R', hR'map, hR'inj⟩ :=
      uc22p22f_exists_lift π (QuotientGroup.mk'_surjective _) hkercop R hRq
    let φ : ↥R' →* ↥R := (π.comp R'.subtype).codRestrict R (fun x => by
      have : π (x : ↥D.M) ∈ R'.map π := ⟨x, x.2, rfl⟩
      rw [hR'map] at this
      exact this)
    have hφinj : Function.Injective φ := fun a b hab => hR'inj (congrArg Subtype.val hab)
    have hφsurj : Function.Surjective φ := by
      intro r
      have : (r : Bar2 D.M) ∈ R'.map π := by rw [hR'map]; exact r.2
      obtain ⟨x, hx, hxr⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxr⟩
    have hR'card : Nat.card ↥R' = Nat.card ↥R := Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
    have hR'q : IsPGroup q ↥R' := hRq.of_injective φ hφinj
    set W : Subgroup G := barPreimage D.M R with hWdef
    set R'' : Subgroup G := R'.map D.M.subtype with hR''
    have hR''W : R'' ≤ W := by
      rintro _ ⟨r, hr, rfl⟩
      refine uc22p21c_mem_barPreimage.2 ⟨r.2, ?_⟩
      have : π r ∈ R'.map π := ⟨r, hr, rfl⟩
      rw [hR'map] at this
      exact this
    have hR''q : IsPGroup q ↥R'' := hR'q.map D.M.subtype
    obtain ⟨S, hS⟩ := (hR''q.comap_subtype : IsPGroup q ↥(R''.subgroupOf W)).exists_le_sylow
    set Q₀ : Subgroup G := (S : Subgroup ↥W).map W.subtype with hQ₀def
    have hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀ W := ⟨S, rfl⟩
    have hR''Q₀ : R'' ≤ Q₀ := by
      intro x hx
      have : (⟨x, hR''W hx⟩ : ↥W) ∈ R''.subgroupOf W := hx
      exact ⟨_, hS this, rfl⟩
    calc Nat.card ↥R = Nat.card ↥R' := hR'card.symm
      _ = Nat.card ↥R'' := (Subgroup.card_map_of_injective D.M.subtype_injective).symm
      _ ≤ Nat.card ↥Q₀ := Subgroup.card_le_of_le hR''Q₀
      _ = Nat.card ↥Q := by rw [hQ₀.card_eq, hQ.card_eq]
  have hQR : Q'.map π = R := Subgroup.eq_of_le_of_card_ge hQ'R (hRle.trans hcardQ'.ge)
  have hRnc : ¬ IsCyclic ↥R := by
    intro hcyc
    let ψ : ↥Q →* ↥R :=
      ((π.comp Q'.subtype).comp (Subgroup.subgroupOfEquivOfLe hQM).symm.toMonoidHom).codRestrict R
        (fun x => hQ'R ⟨_, ((Subgroup.subgroupOfEquivOfLe hQM).symm x).2, rfl⟩)
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h1 := hinj (congrArg Subtype.val hab)
      exact (Subgroup.subgroupOfEquivOfLe hQM).symm.injective h1
    have hQcyc : IsCyclic ↥Q := isCyclic_of_injective ψ hψ
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hq hQcyc
    omega
  obtain ⟨Ps, hPsR, hPsn, hPsexp, hPscl, hPsnc, hPsZ⟩ := uc22p22r_exists_omega_two hq hq2 R hRq hRnc
  set P' : Subgroup ↥D.M := Q' ⊓ Ps.comap π with hP'
  set P : Subgroup G := P'.map D.M.subtype with hP
  have hP'Q' : P' ≤ Q' := inf_le_left
  have hPQ : P ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hP'map : P'.map π = Ps := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      have hyR : y ∈ Q'.map π := hQR ▸ hPsR hy
      obtain ⟨x, hx, rfl⟩ := hyR
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hPsub : P.subgroupOf D.M = P' := by
    rw [hP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective]
  have hbar : barImage D.M P = Ps := by
    unfold barImage
    rw [hPsub, hP'map]
  refine ⟨P, hPQ, hQq.to_le hPQ, ?_, ?_, ?_, hbar ▸ hPsn, ?_⟩
  ·
    rintro _ ⟨x, hx, rfl⟩
    have h1 : π (x ^ q) = 1 := by
      rw [map_pow]
      exact hPsexp _ hx.2
    have h2 : x ^ q = 1 := hinj' _ (Q'.pow_mem hx.1 q) _ Q'.one_mem (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  ·
    have hP'cl : ⁅⁅P', P'⁆, P'⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxP' : x ∈ P' := (uc22p22r_commutator_le_self P').trans' (Subgroup.commutator_mono
        (uc22p22r_commutator_le_self P') le_rfl) hx
      have hπx : π x ∈ ⁅⁅Ps, Ps⁆, Ps⁆ := by
        have : π x ∈ (⁅⁅P', P'⁆, P'⁆).map π := ⟨x, hx, rfl⟩
        rw [Subgroup.map_commutator, Subgroup.map_commutator, hP'map] at this
        exact this
      rw [hPscl] at hπx
      exact Subgroup.mem_bot.2
        (hinj' _ (hP'Q' hxP') _ Q'.one_mem (by rw [Subgroup.mem_bot.1 hπx, map_one]))
    rw [hP, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hP'cl, Subgroup.map_bot]
  ·
    intro hcyc
    apply hPsnc
    have h1 : IsCyclic ↥P' :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective P' D.M.subtype D.M.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    have h2 : IsCyclic ↥(P'.map π) := isCyclic_of_surjective (π.subgroupMap P') (π.subgroupMap_surjective P')
    rw [hP'map] at h2
    exact h2
  ·
    set W : Subgroup ↥D.M := (Q ⊓ centralizer (c.V : Set G)).subgroupOf D.M with hW
    have hWQ' : W ≤ Q' := fun x hx => hx.1
    have hWne : W ≠ ⊥ := by
      intro h
      apply hQV
      rw [eq_bot_iff]
      intro x hx
      have hxM : x ∈ D.M := hQM hx.1
      have hxW : (⟨x, hxM⟩ : ↥D.M) ∈ W := hx
      rw [h, Subgroup.mem_bot] at hxW
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hxW)
    have hWR : W.map π ≤ R := (Subgroup.map_mono hWQ').trans hQ'R
    set Wb : Subgroup ↥R := (W.map π).subgroupOf R with hWb
    have hWbn : Wb.Normal := by
      constructor
      intro y hy r
      have hr : (r : Bar2 D.M) ∈ Q'.map π := by
        rw [hQR]
        exact r.2
      obtain ⟨x, hxQ', hxr⟩ := hr
      obtain ⟨w, hwW, hwy⟩ := (hy : (y : Bar2 D.M) ∈ W.map π)
      show ((r * y * r⁻¹ : ↥R) : Bar2 D.M) ∈ W.map π
      refine ⟨x * w * x⁻¹, ?_, ?_⟩
      · have hwW' : (w : G) ∈ Q ⊓ centralizer (c.V : Set G) := hwW
        have hxQ : (x : G) ∈ Q := hxQ'
        show (x : G) * (w : G) * (x : G)⁻¹ ∈ Q ⊓ centralizer (c.V : Set G)
        refine ⟨Q.mul_mem (Q.mul_mem hxQ hwW'.1) (Q.inv_mem hxQ), ?_⟩
        exact (Subgroup.mem_normalizer_iff.1 (uc22p22r_le_normalizer_centralizer c.hVM x.2) _).1 hwW'.2
      · rw [map_mul, map_mul, map_inv, hxr, hwy]
        simp
    have hWbne : Wb ≠ ⊥ := by
      intro h
      apply hWne
      rw [eq_bot_iff]
      intro w hw
      have h1 : π w ∈ W.map π := ⟨w, hw, rfl⟩
      have h2 : (⟨π w, hWR h1⟩ : ↥R) ∈ Wb := h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : π w = 1 := congrArg Subtype.val h2
      exact Subgroup.mem_bot.2 (hinj' _ (hWQ' hw) _ Q'.one_mem (by rw [h3, map_one]))
    haveI : Group.IsNilpotent ↥R := hRq.isNilpotent
    have hcent := Group.IsNilpotent.inf_center_ne_bot_of_normal hWbne
    have hqdvd : q ∣ Nat.card ↥(Wb ⊓ Subgroup.center ↥R) := by
      have hpg : IsPGroup q ↥(Wb ⊓ Subgroup.center ↥R) := hRq.to_subgroup _
      obtain ⟨k, hk⟩ := hpg.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hcent (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
      rw [hk]
      exact dvd_pow_self q hk0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Wb ⊓ Subgroup.center ↥R)) q hqdvd
    have hyWb : ((y : ↥R) : Bar2 D.M) ∈ W.map π := y.2.1
    have hyZ : (y : ↥R) ∈ Subgroup.center ↥R := y.2.2
    have hyq : ((y : ↥R) : Bar2 D.M) ^ q = 1 := by
      have h1 : y ^ q = 1 := hy ▸ pow_orderOf_eq_one y
      have h2 := congrArg (fun t : ↥(Wb ⊓ Subgroup.center ↥R) => ((t : ↥R) : Bar2 D.M)) h1
      simpa using h2
    have hy1 : ((y : ↥R) : Bar2 D.M) ≠ 1 := by
      intro h
      have h1 : y = 1 := Subtype.ext (Subtype.ext h)
      rw [h1, orderOf_one] at hy
      exact hq.one_lt.ne hy
    have hyPs : ((y : ↥R) : Bar2 D.M) ∈ Ps := by
      refine hPsZ _ (y : ↥R).2 (fun r hr => ?_) hyq
      have := Subgroup.mem_center_iff.1 hyZ ⟨r, hr⟩
      exact (congrArg Subtype.val this).symm
    obtain ⟨w, hwW, hwy⟩ := hyWb
    have hwW' : (w : G) ∈ Q ⊓ centralizer (c.V : Set G) := hwW
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨(w : G), ⟨w, ⟨hWQ' hwW, ?_⟩, rfl⟩, hwW'.2⟩, ?_⟩
    · show π w ∈ Ps
      rw [hwy]
      exact hyPs
    · intro h1
      have h2 : (w : G) = 1 := congrArg Subtype.val h1
      have hw1 : w = 1 := Subtype.ext h2
      apply hy1
      rw [← hwy, hw1, map_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22
