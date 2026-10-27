module

public import CFSG.Quasithin.EmptyFaithful.E111RSemi

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R
  CFSG.Quasithin.Vol2.Ch11.SecB

variable {Q : Type} [Group Q]

structure SemisimpleMod (T D Y : Subgroup Q) (𝒟 : Set (Subgroup Q)) : Prop where
  Y_le : ∀ S ∈ 𝒟, Y ≤ S
  le_D : ∀ S ∈ 𝒟, S ≤ D
  simple : ∀ S ∈ 𝒟, ∀ N : Subgroup Q, Y ≤ N → N ≤ S → (N.subgroupOf S).Normal → N = Y ∨ N = S
  nonab : ∀ S ∈ 𝒟, ¬ ⁅S, S⁆ ≤ Y
  comm : ∀ S ∈ 𝒟, ∀ S' ∈ 𝒟, S ≠ S' → ⁅S, S'⁆ ≤ Y
  gen : ⨆ S ∈ 𝒟, S = D
  conj : ∀ S ∈ 𝒟, ∀ t ∈ T, A1b.conjSub t S ∈ 𝒟
  trans : ∀ S ∈ 𝒟, ∀ S' ∈ 𝒟, ∃ t ∈ T, A1b.conjSub t S = S'

section Image

variable {Y S : Subgroup Q} [Y.Normal]

omit [Y.Normal] in
theorem normal_subgroupOf_of_conj {N S : Subgroup Q} (hNS : N ≤ S)
    (h : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) : (N.subgroupOf S).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNS]
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h s hs x hx, fun hx => by
    have := h s⁻¹ (S.inv_mem hs) _ hx
    simpa [mul_assoc] using this⟩

theorem isSimpleGroup_map_of_le (hYS : Y ≤ S)
    (hsimple : ∀ N : Subgroup Q, Y ≤ N → N ≤ S → (N.subgroupOf S).Normal → N = Y ∨ N = S)
    (hnab : ¬ ⁅S, S⁆ ≤ Y) : IsSimpleGroup ↥(S.map (QuotientGroup.mk' Y)) := by
  set π := QuotientGroup.mk' Y with hπ
  rw [Subgroup.isSimpleGroup_iff]
  refine ⟨?_, fun H' hH'S hH'n => ?_⟩
  · intro hbot
    apply hnab
    refine (E111R.commutator_le_self S).trans ?_
    intro x hx
    have : π x ∈ S.map π := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · set N : Subgroup Q := H'.comap π ⊓ S with hN
    have hYN : Y ≤ N := fun y hy => by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr ?_, hYS hy⟩
      show (QuotientGroup.mk y : Q ⧸ Y) ∈ H'
      rw [(QuotientGroup.eq_one_iff y).mpr hy]
      exact H'.one_mem
    have hNS : N ≤ S := inf_le_right
    have hnorm : (N.subgroupOf S).Normal := by
      refine normal_subgroupOf_of_conj hNS fun s hs n hn => ?_
      refine ⟨?_, S.mul_mem (S.mul_mem hs (hNS hn)) (S.inv_mem hs)⟩
      have hs' : π s ∈ S.map π := ⟨s, hs, rfl⟩
      have hn' : (⟨π n, ⟨n, hNS hn, rfl⟩⟩ : ↥(S.map π)) ∈ H'.subgroupOf (S.map π) :=
        Subgroup.mem_subgroupOf.mpr hn.1
      have := hH'n.conj_mem _ hn' ⟨π s, hs'⟩
      have := Subgroup.mem_subgroupOf.mp this
      simpa [Subgroup.mem_comap] using this
    rcases hsimple N hYN hNS hnorm with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hH'S hx
      have hsN : s ∈ N := ⟨hx, hs⟩
      rw [h] at hsN
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff s).mpr hsN
    · right
      refine le_antisymm hH'S ?_
      rintro _ ⟨s, hs, rfl⟩
      have : s ∈ N := h ▸ hs
      exact this.1

theorem nonabelian_map_of_not_le (hnab : ¬ ⁅S, S⁆ ≤ Y) :
    ∃ a b : ↥(S.map (QuotientGroup.mk' Y)), a * b ≠ b * a := by
  set π := QuotientGroup.mk' Y with hπ
  by_contra hc
  push Not at hc
  apply hnab
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have := hc ⟨π a, a, ha, rfl⟩ ⟨π b, b, hb, rfl⟩
  have h2 := congrArg Subtype.val this
  simp only [Subgroup.coe_mul] at h2
  have key : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : Q ⧸ Y) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    change π a * π b * (π a)⁻¹ * (π b)⁻¹ = 1
    rw [h2]
    group
  rw [commutatorElement_def]
  exact (QuotientGroup.eq_one_iff _).mp key

end Image

section Reduced

variable {Q' : Type} [Group Q'] [Finite Q'] {T D C : Subgroup Q'} {𝒟 : Set (Subgroup Q')}

theorem reduced_quot_of_semiFam [D.Normal] [C.Normal] (hC : C = Subgroup.centralizer (D : Set Q'))
    (hT : IsSylowIn 2 T ⊤) (hsf : SemiFam 𝒟) (hD : sSup 𝒟 = D) (hQ : D ⊔ T = ⊤)
    (hne : 𝒟.Nonempty) (hconj : ∀ S ∈ 𝒟, ∀ t ∈ T, A1b.conjSub t S ∈ 𝒟)
    (htr : ∀ S ∈ 𝒟, ∀ S' ∈ 𝒟, ∃ t ∈ T, A1b.conjSub t S = S') :
    E111Reduced (Q' ⧸ C) (D.map (QuotientGroup.mk' C)) (T.map (QuotientGroup.mk' C)) := by
  set π := QuotientGroup.mk' C with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hDC : D ⊓ C = ⊥ := by
    rw [hC, ← hD]
    exact inf_centralizer_eq_bot hsf
  obtain ⟨S₀, hS₀⟩ := hne
  have hS₀D : S₀ ≤ D := hD ▸ le_sSup hS₀
  have hDn' : (D.map π).Normal := Subgroup.Normal.map ‹D.Normal› π hπs
  have hne' : D.map π ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hsf.nonabelian S₀ hS₀
    apply hab
    have hDle : D ≤ C := by
      intro x hx
      have : π x ∈ D.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    have h1 : (a : Q') ∈ D := hS₀D a.2
    have h2 : (b : Q') ∈ D := hS₀D b.2
    have := Subgroup.mem_centralizer_iff.mp (hC ▸ hDle h2 : (b : Q') ∈ Subgroup.centralizer (D : Set Q')) a h1
    exact Subtype.ext this
  have hmin : ∀ N' : Subgroup (Q' ⧸ C), N'.Normal → N' ≤ D.map π → N' = ⊥ ∨ N' = D.map π := by
    intro N' hN'n hN'D
    set Ñ : Subgroup Q' := N'.comap π ⊓ D with hÑ
    have hÑn : Ñ.Normal := by
      haveI : (N'.comap π).Normal := Subgroup.normal_comap π
      exact Subgroup.normal_inf_normal _ _
    by_cases hÑbot : Ñ = ⊥
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨d, hd, hdx⟩ := hN'D hx
      have hdÑ : d ∈ Ñ := ⟨Subgroup.mem_comap.mpr (by rw [show π d = x from hdx]; exact hx), hd⟩
      rw [hÑbot, Subgroup.mem_bot] at hdÑ
      rw [Subgroup.mem_bot, ← hdx, hdÑ, map_one]
    · right
      obtain ⟨⟨d, hdÑ⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÑbot
      have hdD : d ∈ D := hdÑ.2
      obtain ⟨S, hS, s, hs, hds⟩ : ∃ S ∈ 𝒟, ∃ s ∈ S, d * s ≠ s * d := by
        by_contra hcon
        push Not at hcon
        have hdC : d ∈ C := by
          rw [hC]
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rw [← hD] at hx
          have hle : sSup 𝒟 ≤ Subgroup.centralizer ({d} : Set Q') := by
            refine sSup_le fun S' hS' y hy => ?_
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff.mp hz]
            exact hcon S' hS' y hy
          have := Subgroup.mem_centralizer_iff.mp (hle hx) d (Set.mem_singleton _)
          exact this.symm
        have : d ∈ D ⊓ C := ⟨hdD, hdC⟩
        rw [hDC, Subgroup.mem_bot] at this
        exact hd1 (Subtype.ext this)
      have hcomm : d * s * d⁻¹ * s⁻¹ ∈ Ñ := by
        have := hÑn.conj_mem d⁻¹ (Ñ.inv_mem hdÑ) s
        have h2 := Ñ.mul_mem hdÑ this
        simpa [mul_assoc] using h2
      have hcommS : d * s * d⁻¹ * s⁻¹ ∈ S := by
        have h1 : d * s * d⁻¹ ∈ S := by
          have := (Subgroup.mem_normalizer_iff.mp (hsf.le_normalizer hS (hD ▸ hdD)) s).mp hs
          exact this
        exact S.mul_mem h1 (S.inv_mem hs)
      have hnot1 : d * s * d⁻¹ * s⁻¹ ≠ 1 := by
        intro h
        apply hds
        have : d * s = s * d := by
          have := congrArg (fun z => z * s * d) h
          simpa [mul_assoc] using this
        exact this
      have hSn : ((Ñ ⊓ S).subgroupOf S).Normal := by
        rw [Subgroup.inf_subgroupOf_right]
        infer_instance
      have := hsf.simple S hS
      have hSÑ : S ≤ Ñ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Ñ ⊓ S).subgroupOf S) with h | h
        · exfalso
          rw [Subgroup.subgroupOf_eq_bot] at h
          have := Subgroup.disjoint_def.mp h (Subgroup.mem_inf.mpr ⟨hcomm, hcommS⟩) hcommS
          exact hnot1 this
        · rw [Subgroup.subgroupOf_eq_top] at h
          exact h.trans inf_le_left
      have hDÑ : D ≤ Ñ := by
        rw [← hD]
        refine sSup_le fun S' hS' => ?_
        obtain ⟨t, ht, rfl⟩ := htr S hS S' hS'
        intro y hy
        rw [A1b.mem_conjSub_iff] at hy
        have := hÑn.conj_mem _ (hSÑ hy) t
        simpa [mul_assoc] using this
      refine le_antisymm hN'D ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (hDÑ hx).1
  have hnab : ∃ a b : ↥(D.map π), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hsf.nonabelian S₀ hS₀
    refine ⟨⟨π a, a, hS₀D a.2, rfl⟩, ⟨π b, b, hS₀D b.2, rfl⟩, fun he => hab ?_⟩
    have h2 := congrArg Subtype.val he
    simp only [Subgroup.coe_mul] at h2
    have hmem : (a : Q') * b * (a : Q')⁻¹ * (b : Q')⁻¹ ∈ D ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact D.mul_mem (D.mul_mem (D.mul_mem (hS₀D a.2) (hS₀D b.2)) (D.inv_mem (hS₀D a.2)))
          (D.inv_mem (hS₀D b.2))
      · have key : π ((a : Q') * b * (a : Q')⁻¹ * (b : Q')⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [h2]
          group
        exact (QuotientGroup.eq_one_iff _).mp key
    rw [hDC, Subgroup.mem_bot] at hmem
    have h3 : (a : Q') * (b : Q') = (b : Q') * (a : Q') := by
      have := congrArg (fun z => z * (b : Q') * (a : Q')) hmem
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hcent : Subgroup.centralizer ((D.map π : Subgroup (Q' ⧸ C)) : Set (Q' ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨q', rfl⟩ := hπs q
    rw [Subgroup.mem_bot, show (1 : Q' ⧸ C) = π 1 from (map_one π).symm]
    rw [Subgroup.mem_centralizer_iff] at hq
    have hq' : q' ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := hq (π d) ⟨d, hd, rfl⟩
      have hmem : d * q' * d⁻¹ * q'⁻¹ ∈ D ⊓ C := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h2 : q' * d⁻¹ * q'⁻¹ ∈ D := ‹D.Normal›.conj_mem d⁻¹ (D.inv_mem hd) q'
          have := D.mul_mem hd h2
          simpa [mul_assoc] using this
        · have key : π (d * q' * d⁻¹ * q'⁻¹) = 1 := by
            simp only [map_mul, map_inv]
            rw [h1]
            group
          exact (QuotientGroup.eq_one_iff _).mp key
      rw [hDC, Subgroup.mem_bot] at hmem
      have := congrArg (fun z => z * q' * d) hmem
      simpa [mul_assoc] using this
    exact (QuotientGroup.eq_one_iff q').mpr hq'
  have hSyl : IsSylowIn 2 (T.map π) ⊤ := E1.isSylowIn_two_map_top hπs hT
  have hsup : D.map π ⊔ T.map π = ⊤ := by
    rw [← Subgroup.map_sup, hQ, Subgroup.map_top_of_surjective _ hπs]
  exact ⟨hDn', hne', hmin, hnab, hcent, hSyl, hsup⟩

end Reduced

namespace SemisimpleMod

open scoped commutatorElement

variable {T D Y : Subgroup Q} {𝒟 : Set (Subgroup Q)}

theorem le_normalizer_of_ne (h : SemisimpleMod T D Y 𝒟) {S S' : Subgroup Q} (hS : S ∈ 𝒟)
    (hS' : S' ∈ 𝒟) (hne : S ≠ S') : S ≤ Subgroup.normalizer (S' : Set Q) := by
  have key : ∀ x ∈ S, ∀ y ∈ S', x * y * x⁻¹ ∈ S' := by
    intro x hx y hy
    have hc : ⁅x, y⁆ ∈ Y := h.comm S hS S' hS' hne (Subgroup.commutator_mem_commutator hx hy)
    have hc' : x * y * x⁻¹ * y⁻¹ ∈ S' := h.Y_le S' hS' (by simpa [commutatorElement_def] using hc)
    have := S'.mul_mem hc' hy
    simpa [mul_assoc] using this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (S.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem D_le_normalizer (h : SemisimpleMod T D Y 𝒟) {S : Subgroup Q} (hS : S ∈ 𝒟) :
    D ≤ Subgroup.normalizer (S : Set Q) := by
  rw [← h.gen]
  refine iSup₂_le fun S' hS' => ?_
  by_cases hSS : S' = S
  · rw [hSS]
    exact Subgroup.le_normalizer
  · exact h.le_normalizer_of_ne hS' hS hSS

theorem conjSub_eq_of_mem_D (h : SemisimpleMod T D Y 𝒟) {S : Subgroup Q} (hS : S ∈ 𝒟) {d : Q}
    (hd : d ∈ D) : A1b.conjSub d S = S :=
  E111R.conjSub_eq_of_mem_normalizer (h.D_le_normalizer hS hd)

theorem conj_of_sup_top (h : SemisimpleMod T D Y 𝒟) [D.Normal] (hDT : D ⊔ T = ⊤) (q : Q)
    {S : Subgroup Q} (hS : S ∈ 𝒟) : A1b.conjSub q S ∈ 𝒟 := by
  have hq : q ∈ D ⊔ T := hDT ▸ Subgroup.mem_top q
  obtain ⟨d, hd, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
  rw [A1b.conjSub_mul, h.conjSub_eq_of_mem_D (h.conj S hS t ht) hd]
  exact h.conj S hS t ht

theorem semiFam_map [Y.Normal] (h : SemisimpleMod T D Y 𝒟) :
    E111R.SemiFam ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact isSimpleGroup_map_of_le (h.Y_le S hS) (h.simple S hS) (h.nonab S hS)
  · rintro _ ⟨S, hS, rfl⟩
    exact nonabelian_map_of_not_le (h.nonab S hS)
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩ hne x hx y hy
    have hSS : S ≠ S' := fun hh => hne (by rw [hh])
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hc : ⁅x', y'⁆ ∈ Y := h.comm S hS S' hS' hSS (Subgroup.commutator_mem_commutator hx' hy')
    have h1 : QuotientGroup.mk' Y (x' * y' * x'⁻¹ * y'⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by simpa [commutatorElement_def] using hc)
    simp only [map_mul, map_inv] at h1
    have h2 : (QuotientGroup.mk' Y x') * (QuotientGroup.mk' Y y') =
        (QuotientGroup.mk' Y y') * (QuotientGroup.mk' Y x') := by
      have := congrArg (fun z => z * (QuotientGroup.mk' Y y') * (QuotientGroup.mk' Y x')) h1
      simpa [mul_assoc] using this
    exact h2

theorem sSup_map [Y.Normal] (h : SemisimpleMod T D Y 𝒟) :
    sSup ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟) =
      D.map (QuotientGroup.mk' Y) := by
  rw [sSup_image, ← h.gen, Subgroup.map_iSup]
  simp only [Subgroup.map_iSup]

end SemisimpleMod

end CFSG.Quasithin.RonanE111
