module

public import CFSG.Quasithin.Background.RonanE111Sec
public import CFSG.Quasithin.Background.RonanE111Gen

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

section Transport

variable {Q H : Type} [Group Q] [Group H]

theorem e2_conjSub_map (ι : Q →* H) (t : Q) (S : Subgroup Q) :
    A1b.conjSub (ι t) (S.map ι) = (A1b.conjSub t S).map ι := by
  unfold A1b.conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem e2_semisimple_map (ι : Q →* H) (hι : Function.Injective ι) {T D Y : Subgroup Q}
    {𝒟 : Set (Subgroup Q)} (h : SemisimpleMod T D Y 𝒟) :
    SemisimpleMod (T.map ι) (D.map ι) (Y.map ι) ((fun L : Subgroup Q => L.map ι) '' 𝒟) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.map_mono (h.Y_le S hS)
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.map_mono (h.le_D S hS)
  · rintro _ ⟨S, hS, rfl⟩ N hYN hNS hnorm
    have hYN₀ : Y ≤ N.comap ι := fun y hy => hYN (Subgroup.mem_map_of_mem ι hy)
    have hN₀S : N.comap ι ≤ S := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp (hNS (show ι x ∈ N from hx))
      rw [hι hsx] at hs
      exact hs
    have hN₀n : ((N.comap ι).subgroupOf S).Normal := by
      refine normal_subgroupOf_of_conj hN₀S fun s hs n hn => ?_
      have hn' : ι n ∈ N := hn
      have hsS : ι s ∈ S.map ι := Subgroup.mem_map_of_mem ι hs
      have hnS : ι n ∈ S.map ι := hNS hn'
      have key : ι s * ι n * (ι s)⁻¹ ∈ N :=
        Subgroup.mem_subgroupOf.mp
          (hnorm.conj_mem ⟨ι n, hnS⟩ (Subgroup.mem_subgroupOf.mpr hn') ⟨ι s, hsS⟩)
      show s * n * s⁻¹ ∈ N.comap ι
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact key
    have hNr : N ≤ ι.range := fun x hx => by
      obtain ⟨y, _, hy⟩ := Subgroup.mem_map.mp (hNS hx)
      exact MonoidHom.mem_range.mpr ⟨y, hy⟩
    have hNeq : (N.comap ι).map ι = N := Subgroup.map_comap_eq_self hNr
    rcases h.simple S hS (N.comap ι) hYN₀ hN₀S hN₀n with hN | hN
    · left
      rw [← hNeq, hN]
    · right
      rw [← hNeq, hN]
  · rintro _ ⟨S, hS, rfl⟩ hle
    rw [← Subgroup.map_commutator] at hle
    exact h.nonab S hS ((Subgroup.map_le_map_iff_of_injective hι).mp hle)
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    have hST : S ≠ T := fun e => hne (congrArg (fun L : Subgroup Q => L.map ι) e)
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (h.comm S hS T hT hST)
  · have hG : ⨆ S ∈ (fun L : Subgroup Q => L.map ι) '' 𝒟, S = (⨆ S ∈ 𝒟, S).map ι := by
      rw [iSup_image]
      simp only [Subgroup.map_iSup]
    rw [hG, h.gen]
  · rintro _ ⟨S, hS, rfl⟩ t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    exact ⟨A1b.conjSub t₀ S, h.conj S hS t₀ ht₀, (e2_conjSub_map ι t₀ S).symm⟩
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩
    obtain ⟨t, ht, hts⟩ := h.trans S hS T hT
    exact ⟨ι t, Subgroup.mem_map_of_mem ι ht, by rw [e2_conjSub_map, hts]⟩

theorem e2_mem_normalizer_map_iff (ι : Q →* H) (hι : Function.Injective ι) (L : Subgroup Q)
    (q : Q) :
    ι q ∈ Subgroup.normalizer ((L.map ι : Subgroup H) : Set H) ↔
      q ∈ Subgroup.normalizer (L : Set Q) := by
  constructor
  · intro hq
    rw [Subgroup.mem_normalizer_iff] at hq ⊢
    intro g
    have e : ι q * ι g * (ι q)⁻¹ = ι (q * g * q⁻¹) := by simp [map_mul, map_inv]
    have h1 := hq (ι g)
    rw [e, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at h1
    exact h1
  · intro hq
    exact Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι hq)

theorem e2_normalizer_map_le [Finite H] (ι : Q →* H) {A B : Subgroup Q}
    (hAB : A ≤ Subgroup.normalizer (B : Set Q)) :
    A.map ι ≤ Subgroup.normalizer ((B.map ι : Subgroup H) : Set H) := by
  refine sec_le_normalizer_of_conj fun a ha g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
  have h1 := (Subgroup.mem_normalizer_iff.mp (hAB hx) y).mp hy
  have e : ι x * ι y * (ι x)⁻¹ = ι (x * y * x⁻¹) := by simp [map_mul, map_inv]
  rw [e]
  exact Subgroup.mem_map_of_mem ι h1

theorem e2_secData_map [Finite H] (ι : Q →* H) (hι : Function.Injective ι) {M XM YM : Subgroup Q}
    {ℒ : Set (Subgroup Q)} (hS : SecData M XM YM ℒ) :
    SecData (M.map ι) (XM.map ι) (YM.map ι) ((fun L : Subgroup Q => L.map ι) '' ℒ) := by
  obtain ⟨hSM, ⟨L₀, hL₀⟩, hX, hMX, hMY, hsol⟩ := hS
  have hsolY := hsol
  refine ⟨e2_semisimple_map ι hι hSM, ⟨L₀.map ι, Set.mem_image_of_mem _ hL₀⟩,
    e2_normalizer_map_le ι hX, e2_normalizer_map_le ι hMX, e2_normalizer_map_le ι hMY, ?_⟩
  exact Group.isSolvable_of_surjective (f := (YM.equivMapOfInjective ι hι).toMonoidHom)
    (YM.equivMapOfInjective ι hι).surjective

end Transport

section PerfectCore

instance e2_perfectCore_top_normal (X : Type) [Group X] :
    (perfectCore (⊤ : Subgroup X)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have htop : Subgroup.normalizer ((⊤ : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hg : g ∈ Subgroup.normalizer ((⊤ : Subgroup X) : Set X) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_perfectCore ⊤ hg) n).mp hn

theorem e2_conj_mem_perfectCore {X : Type} [Group X] (x : X) {y : X}
    (hy : y ∈ perfectCore (⊤ : Subgroup X)) : x * y * x⁻¹ ∈ perfectCore (⊤ : Subgroup X) :=
  (inferInstance : (perfectCore (⊤ : Subgroup X)).Normal).conj_mem y hy x

theorem e2_conj_mem_radical {X : Type} [Group X] (x : X) {y : X}
    (hy : y ∈ CFSG.solvableRadical X) : x * y * x⁻¹ ∈ CFSG.solvableRadical X :=
  (inferInstance : (CFSG.solvableRadical X).Normal).conj_mem y hy x

theorem e2q_map_perfectCore_eq_layer {Q : Type} [Group Q] [Finite Q]
    (hA : CFSG.Open.pCore 2 (Q ⧸ oInftyE Q) = ⊤) :
    (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) =
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q) := by
  haveI : (CFSG.layer (Q ⧸ CFSG.solvableRadical Q)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Q ⧸ CFSG.solvableRadical Q)
    infer_instance
  have hpow : ∀ z : Q ⧸ oInftyE Q, ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    intro z
    have hz : z ∈ CFSG.pCore 2 (Q ⧸ oInftyE Q) := by
      rw [hA]
      exact Subgroup.mem_top z
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Q ⧸ oInftyE Q)) ⟨z, hz⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hle : perfectCore (⊤ : Subgroup (Q ⧸ CFSG.solvableRadical Q)) ≤
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q) := by
    refine perfectCore_top_le_of_two_quotient _ fun y => ?_
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical Q) y
    obtain ⟨k, hk⟩ := hpow (QuotientGroup.mk q)
    refine ⟨k, ?_⟩
    have h1 : ((q ^ 2 ^ k : Q) : Q ⧸ oInftyE Q) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk
    have h2 : q ^ 2 ^ k ∈ oInftyE Q := (QuotientGroup.eq_one_iff _).mp h1
    rw [← map_pow]
    exact h2
  have hperf : perfectCore (⊤ : Subgroup (Q ⧸ CFSG.solvableRadical Q)) =
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q) :=
    le_antisymm hle (le_perfectCore_of_perfect le_top CFSG.LocalCores.layer_perfect)
  rw [map_perfectCore, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), hperf]

theorem e2q_sup_eq_top {Q : Type} [Group Q] [Finite Q] {Mq : Subgroup Q}
    (hM : IsSylowIn 2 Mq ⊤)
    (hB : twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q)) :
    Mq ⊔ perfectCore (⊤ : Subgroup Q) = ⊤ := by
  have h := sup_twoResidual_eq hM
  rwa [hB] at h

theorem e2_isSimpleGroup_of_component {X : Type} [Group X] [Finite X]
    (hX : CFSG.solvableRadical X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    IsSimpleGroup ↥K := by
  have hK' : K ∈ cComp (⊤ : Subgroup X) := mem_cComp_top_of_isComponent hK
  have hrad : solvRad K = ⊥ := by
    have h1 := solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hK')
    rw [← A3.solvableRadical_eq_solvRad_top, hX] at h1
    exact le_bot_iff.mp h1
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  refine ⟨fun T hT => ?_⟩
  rcases normal_eq_top_or_map_le_solvRad hK' T with h | h
  · exact Or.inr h
  · left
    rw [hrad, le_bot_iff] at h
    rw [eq_bot_iff]
    intro x hx
    have hx' : K.subtype x ∈ T.map K.subtype := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hx'
    exact K.subtype_injective (hx'.trans (map_one K.subtype).symm)

theorem e2_isComponent_conjSub {X : Type} [Group X] {K : Subgroup X} (hK : CFSG.IsComponent K)
    (g : X) : CFSG.IsComponent (A1b.conjSub g K) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

end PerfectCore

section Members

noncomputable def e2Mem (Q : Type) [Group Q] (K : Subgroup (Q ⧸ CFSG.solvableRadical Q)) :
    Subgroup Q :=
  perfectCore (⊤ : Subgroup Q) ⊓ K.comap (QuotientGroup.mk' (CFSG.solvableRadical Q))

theorem e2Mem_le (Q : Type) [Group Q] (K : Subgroup (Q ⧸ CFSG.solvableRadical Q)) :
    e2Mem Q K ≤ perfectCore (⊤ : Subgroup Q) := by
  unfold e2Mem
  exact inf_le_left

theorem e2_Y_le (Q : Type) [Group Q] (K : Subgroup (Q ⧸ CFSG.solvableRadical Q)) :
    perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q ≤ e2Mem Q K := by
  intro y hy
  unfold e2Mem
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, Subgroup.mem_comap.mpr ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.solvableRadical Q) y = 1 :=
    (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_inf.mp hy).2
  rw [h1]
  exact K.one_mem

theorem e2Mem_conjSub (Q : Type) [Group Q] (t : Q) (K : Subgroup (Q ⧸ CFSG.solvableRadical Q)) :
    A1b.conjSub t (e2Mem Q K) =
      e2Mem Q (A1b.conjSub (QuotientGroup.mk' (CFSG.solvableRadical Q) t) K) := by
  ext x
  have hX : t⁻¹ * x * t ∈ perfectCore (⊤ : Subgroup Q) ↔
      x ∈ perfectCore (⊤ : Subgroup Q) := by
    constructor
    · intro h
      have h' := (inferInstance : (perfectCore (⊤ : Subgroup Q)).Normal).conj_mem _ h t
      rwa [show t * (t⁻¹ * x * t) * t⁻¹ = x by group] at h'
    · intro h
      have h' := (inferInstance : (perfectCore (⊤ : Subgroup Q)).Normal).conj_mem _ h t⁻¹
      rwa [inv_inv] at h'
  unfold e2Mem
  simp only [A1b.mem_conjSub_iff, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
  exact and_congr hX Iff.rfl

theorem e2Mem_map (Q : Type) [Group Q] {K : Subgroup (Q ⧸ CFSG.solvableRadical Q)}
    (hK : K ≤ CFSG.layer (Q ⧸ CFSG.solvableRadical Q))
    (hl : (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) =
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q)) :
    (e2Mem Q K).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = K := by
  unfold e2Mem
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).2
  · intro k hk
    have hk' : k ∈ (perfectCore (⊤ : Subgroup Q)).map
        (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
      rw [hl]
      exact hK hk
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hk'
    refine ⟨x, Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_comap.mpr ?_⟩, hxk⟩
    rw [hxk]
    exact hk

theorem e2Mem_simple (Q : Type) [Group Q] [Finite Q] {K : Subgroup (Q ⧸ CFSG.solvableRadical Q)}
    (hK : IsSimpleGroup ↥K)
    (hmap : (e2Mem Q K).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = K) {N : Subgroup Q}
    (hYN : perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q ≤ N) (hNS : N ≤ e2Mem Q K)
    (hnorm : (N.subgroupOf (e2Mem Q K)).Normal) :
    N = perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q ∨ N = e2Mem Q K := by
  have hNX : N ≤ perfectCore (⊤ : Subgroup Q) := hNS.trans (e2Mem_le Q K)
  have hN'K : N.map (QuotientGroup.mk' (CFSG.solvableRadical Q)) ≤ K := by
    rw [← hmap]
    exact Subgroup.map_mono hNS
  have hN'n : ((N.map (QuotientGroup.mk' (CFSG.solvableRadical Q))).subgroupOf K).Normal := by
    refine normal_subgroupOf_of_conj hN'K fun k hk n hn => ?_
    have hk' : k ∈ (e2Mem Q K).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
      rw [hmap]
      exact hk
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk'
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have hsm : s * m * s⁻¹ ∈ N :=
      Subgroup.mem_subgroupOf.mp
        (hnorm.conj_mem ⟨m, hNS hm⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨s, hs⟩)
    have e : QuotientGroup.mk' (CFSG.solvableRadical Q) (s * m * s⁻¹) =
        QuotientGroup.mk' (CFSG.solvableRadical Q) s *
          QuotientGroup.mk' (CFSG.solvableRadical Q) m *
          (QuotientGroup.mk' (CFSG.solvableRadical Q) s)⁻¹ := by
      simp [map_mul, map_inv]
    rw [← e]
    exact Subgroup.mem_map_of_mem _ hsm
  haveI := hN'n
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N.map (QuotientGroup.mk' (CFSG.solvableRadical Q))).subgroupOf K) with hbot | htop
  · left
    apply le_antisymm ?_ hYN
    intro n hn
    have hmem : (⟨QuotientGroup.mk' (CFSG.solvableRadical Q) n,
        hN'K (Subgroup.mem_map_of_mem _ hn)⟩ : K) ∈
        (N.map (QuotientGroup.mk' (CFSG.solvableRadical Q))).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hn)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical Q) n = 1 := congrArg Subtype.val hmem
    exact Subgroup.mem_inf.mpr ⟨hNX hn, (QuotientGroup.eq_one_iff n).mp h1⟩
  · right
    apply le_antisymm hNS
    have hKN : K ≤ N.map (QuotientGroup.mk' (CFSG.solvableRadical Q)) :=
      Subgroup.subgroupOf_eq_top.mp htop
    intro x hx
    have hx2 : x ∈ perfectCore (⊤ : Subgroup Q) ⊓
        K.comap (QuotientGroup.mk' (CFSG.solvableRadical Q)) := hx
    have hxX : x ∈ perfectCore (⊤ : Subgroup Q) := (Subgroup.mem_inf.mp hx2).1
    have hxK : QuotientGroup.mk' (CFSG.solvableRadical Q) x ∈ K :=
      Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx2).2
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp (hKN hxK)
    have hr : n⁻¹ * x ∈ CFSG.solvableRadical Q := QuotientGroup.eq.mp hnx
    have hY : n⁻¹ * x ∈ perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q :=
      Subgroup.mem_inf.mpr
        ⟨(perfectCore (⊤ : Subgroup Q)).mul_mem ((perfectCore (⊤ : Subgroup Q)).inv_mem (hNX hn))
          hxX, hr⟩
    have h2 := N.mul_mem hn (hYN hY)
    simpa using h2

theorem e2Mem_nonab (Q : Type) [Group Q] {K : Subgroup (Q ⧸ CFSG.solvableRadical Q)}
    (hK : CFSG.IsComponent K)
    (hmap : (e2Mem Q K).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = K) :
    ¬ ⁅e2Mem Q K, e2Mem Q K⁆ ≤ perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q := by
  intro h
  have hc : (⁅e2Mem Q K, e2Mem Q K⁆).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) =
      ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, hmap]
  have h1 : ⁅K, K⁆ ≤ ⊥ := by
    rw [← hc]
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_inf.mp (h hz)).2)
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hne : K ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hK.1)
  exact hne (le_bot_iff.mp (hperf ▸ h1))

theorem e2Mem_comm (Q : Type) [Group Q] [Finite Q] {K K' : Subgroup (Q ⧸ CFSG.solvableRadical Q)}
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hne : K ≠ K')
    (hmap : (e2Mem Q K).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = K)
    (hmap' : (e2Mem Q K').map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = K') :
    ⁅e2Mem Q K, e2Mem Q K'⁆ ≤ perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q := by
  have hcomm : ⁅K, K'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hne
  have hc : (⁅e2Mem Q K, e2Mem Q K'⁆).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = ⊥ := by
    rw [Subgroup.map_commutator, hmap, hmap', hcomm]
  have hle : ⁅e2Mem Q K, e2Mem Q K'⁆ ≤ perfectCore (⊤ : Subgroup Q) := by
    calc ⁅e2Mem Q K, e2Mem Q K'⁆ ≤ ⁅perfectCore (⊤ : Subgroup Q), perfectCore (⊤ : Subgroup Q)⁆ :=
          Subgroup.commutator_mono (e2Mem_le Q K) (e2Mem_le Q K')
      _ = perfectCore (⊤ : Subgroup Q) := perfectCore_perfect ⊤
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨hle hz, ?_⟩
  have hz' : QuotientGroup.mk' (CFSG.solvableRadical Q) z ∈
      (⊥ : Subgroup (Q ⧸ CFSG.solvableRadical Q)) := by
    rw [← hc]
    exact Subgroup.mem_map_of_mem _ hz
  rw [Subgroup.mem_bot] at hz'
  exact (QuotientGroup.eq_one_iff z).mp hz'

theorem e2_iSup_eq (Q : Type) [Group Q] (ℒ : Set (Subgroup Q)) (hne : ℒ.Nonempty)
    (hℒ : ∀ S ∈ ℒ, S ≤ perfectCore (⊤ : Subgroup Q) ∧
      perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q ≤ S)
    (hcov : (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) ≤
      (⨆ S ∈ ℒ, S).map (QuotientGroup.mk' (CFSG.solvableRadical Q))) :
    ⨆ S ∈ ℒ, S = perfectCore (⊤ : Subgroup Q) := by
  have hHX : (⨆ S ∈ ℒ, S) ≤ perfectCore (⊤ : Subgroup Q) :=
    iSup₂_le fun S hS => (hℒ S hS).1
  apply le_antisymm hHX
  intro x hx
  have hπx := hcov (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hπx
  have hr : h⁻¹ * x ∈ CFSG.solvableRadical Q := QuotientGroup.eq.mp hhx
  have hrX : h⁻¹ * x ∈ perfectCore (⊤ : Subgroup Q) :=
    (perfectCore (⊤ : Subgroup Q)).mul_mem ((perfectCore (⊤ : Subgroup Q)).inv_mem (hHX hh)) hx
  obtain ⟨S₀, hS₀⟩ := hne
  have hYH : perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q ≤ ⨆ S ∈ ℒ, S :=
    (hℒ S₀ hS₀).2.trans (le_iSup₂ (f := fun S (_ : S ∈ ℒ) => S) S₀ hS₀)
  have hm := (⨆ S ∈ ℒ, S).mul_mem hh (hYH (Subgroup.mem_inf.mpr ⟨hrX, hr⟩))
  rwa [mul_inv_cancel_left] at hm

end Members

section Estimates

theorem e2q_rank {Q : Type} [Group Q] [Finite Q] {Vq : Subgroup Q} {n : ℕ}
    (hbar : Nat.card (E1.barRad Q Vq) ≤ 2 ^ n) {L : Subgroup Q}
    (hL : L ≤ perfectCore (⊤ : Subgroup Q)) :
    ∃ B ≤ Vq ⊓ Subgroup.normalizer (L : Set Q),
      (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ perfectCore (⊤ : Subgroup Q) ⊓
        CFSG.solvableRadical Q) ∧
        B.relIndex (Vq ⊓ Subgroup.normalizer (L : Set Q)) ≤ 2 ^ n := by
  refine ⟨(Vq ⊓ Subgroup.normalizer (L : Set Q)) ⊓ CFSG.solvableRadical Q, inf_le_left,
    fun b hb s hs => ?_, ?_⟩
  · obtain ⟨hbK, hbρ⟩ := Subgroup.mem_inf.mp hb
    have hbN : b ∈ Subgroup.normalizer (L : Set Q) := (Subgroup.mem_inf.mp hbK).2
    have hbsL : b * s * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hbN s).mp hs
    refine Subgroup.mem_inf.mpr ⟨hL (L.mul_mem hbsL (L.inv_mem hs)), ?_⟩
    have h1 : s * b⁻¹ * s⁻¹ ∈ CFSG.solvableRadical Q :=
      e2_conj_mem_radical s ((CFSG.solvableRadical Q).inv_mem hbρ)
    have h2 := (CFSG.solvableRadical Q).mul_mem hbρ h1
    simpa [mul_assoc] using h2
  · set K := Vq ⊓ Subgroup.normalizer (L : Set Q) with hK
    let g : K →* Q ⧸ CFSG.solvableRadical Q :=
      (QuotientGroup.mk' (CFSG.solvableRadical Q)).comp K.subtype
    have hker : (K ⊓ CFSG.solvableRadical Q).subgroupOf K = g.ker := by
      ext x
      constructor
      · intro hx'
        have h1 : (x : Q) ∈ K ⊓ CFSG.solvableRadical Q := Subgroup.mem_subgroupOf.mp hx'
        exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (x : Q)).mpr
          (Subgroup.mem_inf.mp h1).2)
      · intro hx'
        have h2 : (QuotientGroup.mk' (CFSG.solvableRadical Q) (x : Q)) = 1 :=
          MonoidHom.mem_ker.mp hx'
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mpr ⟨x.2, (QuotientGroup.eq_one_iff (x : Q)).mp h2⟩)
    have hidx : (K ⊓ CFSG.solvableRadical Q).relIndex K = Nat.card g.range := by
      rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    have hrange : g.range ≤ E1.barRad Q Vq := by
      intro y hy
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hy
      exact Subgroup.mem_map.mpr ⟨(k : Q), (inf_le_left : K ≤ Vq) k.2, rfl⟩
    rw [hidx]
    exact le_trans (Subgroup.card_le_of_le hrange) hbar

theorem e2q_move {Q : Type} [Group Q] [Finite Q] {Vq : Subgroup Q}
    {Lb : Subgroup (Q ⧸ CFSG.solvableRadical Q)} (hLb : CFSG.IsComponent Lb)
    (hl : (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) =
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q))
    (hd : Lb = ⁅Lb, E1.barRad Q Vq⁆ ∨ (¬ E1.barRad Q Vq ≤
      Subgroup.normalizer (Lb : Set (Q ⧸ CFSG.solvableRadical Q)) ∧
        Nat.card (E1.barRad Q Vq) = 2)) :
    ∃ v ∈ Vq, ∃ s ∈ e2Mem Q Lb, v * s * v⁻¹ * s⁻¹ ∉
      perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q := by
  have hLle : Lb ≤ CFSG.layer (Q ⧸ CFSG.solvableRadical Q) :=
    CFSG.LocalCores.component_le_layer hLb
  have hLb1 : Lb ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Lb).mp (CFSG.LocalCores.isQuasisimple_nontrivial hLb.1)
  have hC : ∃ x ∈ Vq, ∃ l ∈ Lb, QuotientGroup.mk' (CFSG.solvableRadical Q) x * l *
      (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹ * l⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rcases hd with hd | ⟨hnot, -⟩
    · apply hLb1
      have hbot : ⁅Lb, E1.barRad Q Vq⁆ = ⊥ := by
        rw [eq_bot_iff]
        refine Subgroup.commutator_le.mpr fun l hl' b hb => ?_
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
        have h1 := hcon x hx l hl'
        refine Subgroup.mem_bot.mpr ?_
        rw [commutatorElement_def]
        calc l * QuotientGroup.mk' (CFSG.solvableRadical Q) x * l⁻¹ *
              (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹
            = ((QuotientGroup.mk' (CFSG.solvableRadical Q) x) * l *
                (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹ * l⁻¹)⁻¹ := by group
          _ = 1 := by rw [h1, inv_one]
      calc Lb = ⁅Lb, E1.barRad Q Vq⁆ := hd
        _ = ⊥ := hbot
    · apply hnot
      refine sec_le_normalizer_of_conj fun b hb l hl' => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
      have h1 := hcon x hx l hl'
      have h2 : QuotientGroup.mk' (CFSG.solvableRadical Q) x * l *
          (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹ = l := by
        calc QuotientGroup.mk' (CFSG.solvableRadical Q) x * l *
              (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹
            = (QuotientGroup.mk' (CFSG.solvableRadical Q) x * l *
                (QuotientGroup.mk' (CFSG.solvableRadical Q) x)⁻¹ * l⁻¹) * l := by group
          _ = l := by rw [h1, one_mul]
      rw [h2]
      exact hl'
  obtain ⟨x, hx, l, hl', hne⟩ := hC
  have hmapL : (e2Mem Q Lb).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) = Lb :=
    e2Mem_map Q hLle hl
  have hl'' : l ∈ (e2Mem Q Lb).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
    rw [hmapL]
    exact hl'
  obtain ⟨s, hs, hsl⟩ := Subgroup.mem_map.mp hl''
  refine ⟨x, hx, s, hs, fun hmem => hne ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.solvableRadical Q) (x * s * x⁻¹ * s⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_inf.mp hmem).2
  simp only [map_mul, map_inv, hsl] at h1
  exact h1

end Estimates

section QSection

theorem e2q_secData {Q : Type} [Group Q] [Finite Q] {Mq τ : Subgroup Q}
    {Lb : Subgroup (Q ⧸ CFSG.solvableRadical Q)}
    (hA : CFSG.Open.pCore 2 (Q ⧸ oInftyE Q) = ⊤) (hLb : CFSG.IsComponent Lb) (hτ : τ ≤ Mq)
    (hlay : CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
      ⨆ t ∈ τ.map (QuotientGroup.mk' (CFSG.solvableRadical Q)), A1b.conjSub t Lb) :
    SecData Mq (perfectCore (⊤ : Subgroup Q))
      (perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q)
      {L : Subgroup Q | ∃ m ∈ Mq, A1b.conjSub m (e2Mem Q Lb) = L} := by
  have hl := e2q_map_perfectCore_eq_layer hA
  have hmem : ∀ S ∈ {L : Subgroup Q | ∃ m ∈ Mq, A1b.conjSub m (e2Mem Q Lb) = L},
      ∃ K, CFSG.IsComponent K ∧ S = e2Mem Q K := by
    rintro S ⟨m, -, rfl⟩
    exact ⟨A1b.conjSub (QuotientGroup.mk' (CFSG.solvableRadical Q) m) Lb,
      e2_isComponent_conjSub hLb _, e2Mem_conjSub Q m Lb⟩
  have hYn : ∀ x : Q, ∀ y ∈ perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q,
      x * y * x⁻¹ ∈ perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q := fun x y hy =>
    Subgroup.mem_inf.mpr ⟨e2_conj_mem_perfectCore x (Subgroup.mem_inf.mp hy).1,
      e2_conj_mem_radical x (Subgroup.mem_inf.mp hy).2⟩
  have hcov : (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) ≤
      (⨆ S ∈ {L : Subgroup Q | ∃ m ∈ Mq, A1b.conjSub m (e2Mem Q Lb) = L}, S).map
        (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
    rw [hl, hlay]
    refine iSup₂_le fun t ht => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hKle : A1b.conjSub (QuotientGroup.mk' (CFSG.solvableRadical Q) x) Lb ≤
        CFSG.layer (Q ⧸ CFSG.solvableRadical Q) :=
      CFSG.LocalCores.component_le_layer (e2_isComponent_conjSub hLb _)
    have hLx : A1b.conjSub (QuotientGroup.mk' (CFSG.solvableRadical Q) x) Lb =
        (A1b.conjSub x (e2Mem Q Lb)).map (QuotientGroup.mk' (CFSG.solvableRadical Q)) := by
      rw [e2Mem_conjSub, e2Mem_map Q hKle hl]
    rw [hLx]
    refine Subgroup.map_mono (le_iSup₂ (f := fun S
      (_ : S ∈ {L : Subgroup Q | ∃ m ∈ Mq, A1b.conjSub m (e2Mem Q Lb) = L}) => S)
      (A1b.conjSub x (e2Mem Q Lb)) ⟨x, hτ hx, rfl⟩)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨e2Mem Q Lb, 1, Mq.one_mem, A1b.conjSub_one _⟩,
    ?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨K, -, rfl⟩ := hmem S hS
    exact e2_Y_le Q K
  · intro S hS
    obtain ⟨K, -, rfl⟩ := hmem S hS
    exact e2Mem_le Q K
  · intro S hS N hYN hNS hnorm
    obtain ⟨K, hK, rfl⟩ := hmem S hS
    exact e2Mem_simple Q (e2_isSimpleGroup_of_component (A3.solvableRadical_quotient_eq_bot Q) hK)
      (e2Mem_map Q (CFSG.LocalCores.component_le_layer hK) hl) hYN hNS hnorm
  · intro S hS
    obtain ⟨K, hK, rfl⟩ := hmem S hS
    exact e2Mem_nonab Q hK (e2Mem_map Q (CFSG.LocalCores.component_le_layer hK) hl)
  · intro S hS S' hS' hne
    obtain ⟨K, hK, rfl⟩ := hmem S hS
    obtain ⟨K', hK', rfl⟩ := hmem S' hS'
    have hKK : K ≠ K' := fun e => hne (congrArg (e2Mem Q) e)
    exact e2Mem_comm Q hK hK' hKK (e2Mem_map Q (CFSG.LocalCores.component_le_layer hK) hl)
      (e2Mem_map Q (CFSG.LocalCores.component_le_layer hK') hl)
  · refine e2_iSup_eq Q _ ⟨e2Mem Q Lb, 1, Mq.one_mem, A1b.conjSub_one _⟩ ?_ hcov
    intro S hS
    obtain ⟨K, -, rfl⟩ := hmem S hS
    exact ⟨e2Mem_le Q K, e2_Y_le Q K⟩
  · intro S hS t ht
    obtain ⟨m, hm, rfl⟩ := hS
    exact ⟨t * m, Mq.mul_mem ht hm, A1b.conjSub_mul t m _⟩
  · intro S hS S' hS'
    obtain ⟨m, hm, rfl⟩ := hS
    obtain ⟨m', hm', rfl⟩ := hS'
    refine ⟨m' * m⁻¹, Mq.mul_mem hm' (Mq.inv_mem hm), ?_⟩
    rw [← A1b.conjSub_mul, inv_mul_cancel_right]
  · exact sec_le_normalizer_of_conj fun x _ y hy => hYn x y hy
  · exact sec_le_normalizer_of_conj fun x _ h hh => e2_conj_mem_perfectCore x hh
  · exact sec_le_normalizer_of_conj fun m _ y hy => hYn m y hy
  · haveI : Group.IsSolvable (CFSG.solvableRadical Q) := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : perfectCore (⊤ : Subgroup Q) ⊓
        CFSG.solvableRadical Q ≤ CFSG.solvableRadical Q))
      (Subgroup.inclusion_injective _)

theorem e2q_main {Q : Type} [Group Q] [Finite Q] {Mq Vq : Subgroup Q} {n : ℕ}
    (hM : IsSylowIn 2 Mq ⊤) (hE2 : E1.ETwo Q Mq Vq)
    (hbar : Nat.card (E1.barRad Q Vq) ≤ 2 ^ n) :
    ∃ (YQ : Subgroup Q) (ℒ : Set (Subgroup Q)) (L₁ : Subgroup Q),
      YQ ≤ perfectCore (⊤ : Subgroup Q) ∧ SecData Mq (perfectCore (⊤ : Subgroup Q)) YQ ℒ ∧
      L₁ ∈ ℒ ∧ Mq ⊔ perfectCore (⊤ : Subgroup Q) = ⊤ ∧
      (∃ v ∈ Vq, ∃ s ∈ L₁, v * s * v⁻¹ * s⁻¹ ∉ YQ) ∧
      (∀ L ∈ ℒ, ∃ B ≤ Vq ⊓ Subgroup.normalizer (L : Set Q),
        (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YQ) ∧
          B.relIndex (Vq ⊓ Subgroup.normalizer (L : Set Q)) ≤ 2 ^ n) := by
  unfold E1.ETwo at hE2
  obtain ⟨-, hA, hB, Lb, hLb, hlay, hd⟩ := hE2
  have hτ : E1.tauOf ⊤ Mq Vq ≤ Mq := E1.tauOf_le ⊤ Mq Vq
  have hsec := e2q_secData hA hLb hτ hlay
  have hl := e2q_map_perfectCore_eq_layer hA
  refine ⟨perfectCore (⊤ : Subgroup Q) ⊓ CFSG.solvableRadical Q,
    {L : Subgroup Q | ∃ m ∈ Mq, A1b.conjSub m (e2Mem Q Lb) = L}, e2Mem Q Lb, inf_le_left, hsec,
    ⟨1, Mq.one_mem, A1b.conjSub_one _⟩, e2q_sup_eq_top hM hB,
    e2q_move hLb hl hd, ?_⟩
  rintro L hL
  exact e2q_rank hbar (hsec.SM.le_D L hL)

end QSection

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem e2_sylow_subgroupOf_top {P S' : Subgroup G} (h : IsSylowIn 2 S' P) :
    IsSylowIn 2 (S'.subgroupOf P) ⊤ := by
  refine ⟨le_top, h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact h.not_dvd_relIndex

theorem e2_top_map_subtype {P : Subgroup G} : (⊤ : Subgroup P).map P.subtype = P := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem e2_sec {P S V : Subgroup G} {n : ℕ} (hVP : V ≤ P) (hSyl : IsSylowIn 2 (S ⊓ P) P)
    (hE2 : E1.ETwo ↥P ((S ⊓ P).subgroupOf P) (V.subgroupOf P))
    (hbar : Nat.card (E1.barRad ↥P (V.subgroupOf P)) ≤ 2 ^ n) :
    ∃ (XM YM : Subgroup G) (ℒ : Set (Subgroup G)) (L₁ : Subgroup G),
      XM = perfectCore P ∧ YM ≤ XM ∧ SecData (S ⊓ P) XM YM ℒ ∧ L₁ ∈ ℒ ∧ ⁅XM, XM⁆ = XM ∧
      IsSylowIn 2 (S ⊓ XM) XM ∧ P = XM ⊔ (S ⊓ P) ∧
      (∃ v ∈ V, ∃ s ∈ L₁, v * s * v⁻¹ * s⁻¹ ∉ YM) ∧
      (∀ L ∈ ℒ, (∃ v ∈ V ⊓ Subgroup.normalizer (L : Set G), ∃ s ∈ L, v * s * v⁻¹ * s⁻¹ ∉ YM) →
        ∃ B ≤ V ⊓ Subgroup.normalizer (L : Set G),
          (∀ b ∈ B, ∀ s ∈ L, b * s * b⁻¹ * s⁻¹ ∈ YM) ∧
            B.relIndex (V ⊓ Subgroup.normalizer (L : Set G)) ≤ 2 ^ n) := by
  have hMsyl : IsSylowIn 2 ((S ⊓ P).subgroupOf P) ⊤ := e2_sylow_subgroupOf_top hSyl
  obtain ⟨YQ, ℒQ, L₁Q, hYQ, hSecQ, hL₁Q, hfacQ, hmoveQ, hrankQ⟩ :=
    e2q_main hMsyl hE2 hbar
  have hι : Function.Injective P.subtype := P.subtype_injective
  have hXM : (perfectCore (⊤ : Subgroup P)).map P.subtype = perfectCore P := by
    rw [map_perfectCore, e2_top_map_subtype]
  have hMq : ((S ⊓ P).subgroupOf P).map P.subtype = S ⊓ P :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hsec := e2_secData_map P.subtype hι hSecQ
  rw [hXM, hMq] at hsec
  have hYM : YQ.map P.subtype ≤ perfectCore P := by
    have h := Subgroup.map_mono (f := P.subtype) hYQ
    rwa [hXM] at h
  have hsyl : IsSylowIn 2 (S ⊓ perfectCore P) (perfectCore P) := by
    have h := hSyl.inf_normal (perfectCore_le P) (perfectCore_normal P)
    have e : (S ⊓ P) ⊓ perfectCore P = S ⊓ perfectCore P := by
      rw [inf_assoc, inf_eq_right.mpr (perfectCore_le P)]
    rwa [e] at h
  have hfac : P = perfectCore P ⊔ (S ⊓ P) := by
    have h := congrArg (Subgroup.map P.subtype) hfacQ
    rw [Subgroup.map_sup, e2_top_map_subtype, hXM, hMq] at h
    rw [sup_comm]
    exact h.symm
  have hmove : ∃ v ∈ V, ∃ s ∈ L₁Q.map P.subtype, v * s * v⁻¹ * s⁻¹ ∉ YQ.map P.subtype := by
    obtain ⟨v, hv, s, hs, hns⟩ := hmoveQ
    refine ⟨(v : G), Subgroup.mem_subgroupOf.mp hv, (s : G), Subgroup.mem_map_of_mem _ hs, ?_⟩
    intro h
    apply hns
    have e : P.subtype (v * s * v⁻¹ * s⁻¹) = (v : G) * (s : G) * (v : G)⁻¹ * (s : G)⁻¹ := by
      simp
    have h' : P.subtype (v * s * v⁻¹ * s⁻¹) ∈ YQ.map P.subtype := by
      rw [e]
      exact h
    exact (Subgroup.mem_map_iff_mem hι).mp h'
  have hKeq : ∀ L' : Subgroup P, V ⊓ Subgroup.normalizer
      ((L'.map P.subtype : Subgroup G) : Set G) =
        ((V.subgroupOf P) ⊓ Subgroup.normalizer (L' : Set P)).map P.subtype := by
    intro L'
    ext g
    constructor
    · rintro ⟨hgV, hgN⟩
      have hgP : g ∈ P := hVP hgV
      refine ⟨⟨g, hgP⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hgV, ?_⟩, rfl⟩
      exact (e2_mem_normalizer_map_iff P.subtype hι L' ⟨g, hgP⟩).mp hgN
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqV, hqN⟩ := Subgroup.mem_inf.mp hq
      exact ⟨Subgroup.mem_subgroupOf.mp hqV,
        (e2_mem_normalizer_map_iff P.subtype hι L' q).mpr hqN⟩
  refine ⟨perfectCore P, YQ.map P.subtype, _, L₁Q.map P.subtype, rfl, hYM, hsec,
    Set.mem_image_of_mem _ hL₁Q, ?_, hsyl, hfac, hmove, ?_⟩
  · rw [perfectCore_perfect P]
  · rintro _ ⟨L', hL', rfl⟩ -
    obtain ⟨B, hB, hBrank, hBidx⟩ := hrankQ L' hL'
    refine ⟨B.map P.subtype, ?_, ?_, ?_⟩
    · rw [hKeq L']
      exact Subgroup.map_mono hB
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨s, hs, rfl⟩
      have h := Subgroup.mem_map_of_mem P.subtype (hBrank b hb s hs)
      simpa using h
    · rw [hKeq L', Subgroup.relIndex_map_map_of_injective _ _ hι]
      exact hBidx

end GLevel

end CFSG.Quasithin.RonanE111
