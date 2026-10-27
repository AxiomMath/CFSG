module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndNormal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Inf

variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

private lemma endgB_sup_split {Y N : Subgroup X} (hYN : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y) :
    ∀ x ∈ Y ⊔ N, ∃ y ∈ Y, ∃ n ∈ N, y * n = x := by
  let T : Subgroup X :=
    { carrier := {x | ∃ y ∈ Y, ∃ n ∈ N, y * n = x}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, n₁, hn₁, rfl⟩ ⟨y₂, hy₂, n₂, hn₂, rfl⟩
        refine ⟨y₁ * y₂, Y.mul_mem hy₁ hy₂, n₁ * n₂, N.mul_mem hn₁ hn₂, ?_⟩
        calc y₁ * y₂ * (n₁ * n₂) = y₁ * (y₂ * n₁) * n₂ := by group
          _ = y₁ * (n₁ * y₂) * n₂ := by rw [hYN y₂ hy₂ n₁ hn₁]
          _ = y₁ * n₁ * (y₂ * n₂) := by group
      one_mem' := ⟨1, Y.one_mem, 1, N.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨y, hy, n, hn, rfl⟩
        refine ⟨y⁻¹, Y.inv_mem hy, n⁻¹, N.inv_mem hn, ?_⟩
        rw [mul_inv_rev, hYN y⁻¹ (Y.inv_mem hy) n⁻¹ (N.inv_mem hn)] }
  intro x hx
  have hle : Y ⊔ N ≤ T :=
    sup_le (fun y hy => ⟨y, hy, 1, N.one_mem, mul_one y⟩)
      (fun n hn => ⟨1, Y.one_mem, n, hn, one_mul n⟩)
  exact hle hx

private lemma endgB_pCore_bot {Y : Subgroup X} (hY : Y.Normal) (ho : CFSG.pCore 2 X = ⊥) :
    CFSG.pCore 2 ↥Y = ⊥ := by
  have hQ : ((CFSG.pCore 2 ↥Y).map Y.subtype).Normal := by
    haveI := hY
    exact ConjAct.normal_of_characteristic_of_normal
  have hQp : IsPGroup 2 ↥((CFSG.pCore 2 ↥Y).map Y.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).of_equiv
      (Subgroup.equivMapOfInjective _ _ Y.subtype_injective)
  have hle : (CFSG.pCore 2 ↥Y).map Y.subtype ≤ CFSG.pCore 2 X := le_sSup ⟨hQ, hQp⟩
  rw [ho, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro y hy
  have h1 : Y.subtype y ∈ (CFSG.pCore 2 ↥Y).map Y.subtype := Subgroup.mem_map_of_mem _ hy
  rw [hle, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext h1

private lemma endgB_conj_mem_N (h : EndgameHyp X A R N H t) {r n : X} (hr : r ∈ R) (hn : n ∈ N) :
    r * n * r⁻¹ ∈ N := by
  have h1 := h.N_normal.conj_mem ⟨n, h.N_le hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨r, hr⟩
  exact Subgroup.mem_subgroupOf.1 h1

theorem endg_false_of_split (h : EndgameHyp X A R N H t) {Y : Subgroup X} (hYR : Y ≤ R)
    (hYN : ∀ y ∈ Y, ∀ n ∈ N, y * n = n * y) (hR : R ≤ Y ⊔ N) : False := by
  obtain ⟨L, hLab, hNgen⟩ := h.N_gen
  have hdec : ∀ r ∈ R, ∃ y ∈ Y, ∃ n ∈ N, y * n = r := fun r hr =>
    endgB_sup_split hYN r (hR hr)
  have hKN : L ⊓ N = N := by
    by_contra hne
    have hnt : (L ⊓ N).subgroupOf N ≠ ⊤ := by
      intro htop
      apply hne
      exact le_antisymm inf_le_right (Subgroup.subgroupOf_eq_top.1 htop)
    haveI : Finite (Subgroup N) :=
      Finite.of_injective (fun K : Subgroup N => (K : Set N)) SetLike.coe_injective
    rcases eq_top_or_exists_le_coatom ((L ⊓ N).subgroupOf N) with htop | ⟨M₀, hM₀, hKM₀⟩
    · exact hnt htop
    haveI : Group.IsNilpotent N := h.N_pgroup.isNilpotent
    have hM₀n : M₀.Normal :=
      Subgroup.NormalizerCondition.normal_of_coatom M₀ Group.normalizerCondition_of_isNilpotent hM₀
    have hconj : ∀ n ∈ N, ∀ m ∈ M₀.map N.subtype, n * m * n⁻¹ ∈ M₀.map N.subtype := by
      rintro n hn _ ⟨u, hu, rfl⟩
      refine ⟨⟨n, hn⟩ * u * ⟨n, hn⟩⁻¹, hM₀n.conj_mem u hu ⟨n, hn⟩, ?_⟩
      simp
    have hKle : L ⊓ N ≤ M₀.map N.subtype := by
      intro k hk
      have hk' : (⟨k, (Subgroup.mem_inf.1 hk).2⟩ : N) ∈ (L ⊓ N).subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        exact hk
      exact Subgroup.mem_map.2 ⟨⟨k, (Subgroup.mem_inf.1 hk).2⟩, hKM₀ hk', rfl⟩
    have hNM : N ≤ M₀.map N.subtype := by
      refine hNgen.trans_le ?_
      refine iSup₂_le fun g hg => ?_
      intro x hx
      obtain ⟨hxc, hxN⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨y, hy, n, hn, rfl⟩ := hdec g hg
      rw [mem_conjSubgroup] at hxc
      have hyx : y⁻¹ * x * y = x := by
        calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
          _ = y⁻¹ * (y * x) := by rw [hYN y hy x hxN]
          _ = x := by group
      have e : (y * n)⁻¹ * x * (y * n) = n⁻¹ * x * n := by
        calc (y * n)⁻¹ * x * (y * n) = n⁻¹ * (y⁻¹ * x * y) * n := by group
          _ = n⁻¹ * x * n := by rw [hyx]
      rw [e] at hxc
      have hmN : n⁻¹ * x * n ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hn) hxN) hn
      have hm := hconj n hn (n⁻¹ * x * n) (hKle ⟨hxc, hmN⟩)
      rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at hm
    have hMtop : M₀ = ⊤ := by
      rw [eq_top_iff]
      intro u _
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 (hNM u.2)
      have hvu' : v = u := Subtype.ext hvu
      rw [← hvu']
      exact hv
    exact hM₀.1 hMtop
  have hNL : N ≤ L := (le_of_eq hKN.symm).trans inf_le_left
  have hNA : N ≤ A := by
    intro m hm
    refine h.cent_le m (h.N_le hm) ?_
    intro r hr
    obtain ⟨y, hy, n, hn, rfl⟩ := hdec r hr
    calc m * (y * n) = (m * y) * n := by group
      _ = (y * m) * n := by rw [← hYN y hy m hm]
      _ = y * (m * n) := by group
      _ = y * (n * m) := by rw [hLab m (hNL hm) n (hNL hn)]
      _ = y * n * m := by group
  have hcard := Subgroup.card_le_of_le hNA
  exact absurd hcard (not_le.2 h.N_large)

theorem endg_inf_R_eq_bot (h : EndgameHyp X A R N H t) {Y : Subgroup X} (hY : Y.Normal)
    (hYt : ∀ y ∈ Y, y * t = t * y) : Y ⊓ R = ⊥ := by
  have hYnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    exact (Subgroup.mem_normalizer_iff.1 (h.F0 y (hYt y hy)).2 n).1 hn
  have hYN : Y ⊓ N = ⊥ := by
    have hpY : CFSG.pCore 2 ↥Y = ⊥ := endgB_pCore_bot hY h.o2
    have hnorm : ((Y ⊓ N).subgroupOf Y).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have ha' := Subgroup.mem_inf.1 ha
      exact Subgroup.mem_inf.2 ⟨hY.conj_mem _ ha'.1 _, hYnorm _ g.2 _ ha'.2⟩
    have hp : IsPGroup 2 ((Y ⊓ N).subgroupOf Y) := by
      intro g
      have hgN : ((g : Y) : X) ∈ N := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 g.2)).2
      obtain ⟨k, hk⟩ := h.N_pgroup ⟨((g : Y) : X), hgN⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have hle : (Y ⊓ N).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hnorm, hp⟩
    rw [hpY] at hle
    rw [eq_bot_iff]
    intro m hm
    have hm' := Subgroup.mem_inf.1 hm
    have hmem : (⟨m, hm'.1⟩ : ↥Y) ∈ (Y ⊓ N).subgroupOf Y :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 hm')
    have h1 := hle hmem
    rw [Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  have hcomm : ∀ y ∈ Y ⊓ R, ∀ n ∈ N, y * n = n * y := by
    intro y hy n hn
    have hmem : y * n * y⁻¹ * n⁻¹ ∈ Y ⊓ N := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 : y * n * y⁻¹ * n⁻¹ = y * (n * y⁻¹ * n⁻¹) := by group
        rw [h1]
        exact Y.mul_mem (Subgroup.mem_inf.1 hy).1
          (hY.conj_mem _ (Y.inv_mem (Subgroup.mem_inf.1 hy).1) n)
      · exact N.mul_mem (endgB_conj_mem_N h (Subgroup.mem_inf.1 hy).2 hn) (N.inv_mem hn)
    rw [hYN, Subgroup.mem_bot] at hmem
    have h2 : y * n * y⁻¹ = n := mul_inv_eq_one.1 hmem
    calc y * n = y * n * y⁻¹ * y := by group
      _ = n * y := by rw [h2]
  by_contra hne
  obtain ⟨S, hSgrp, q, hqsurj, hqker, hSsimp, -, -⟩ := h.quot
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1 : (a : X) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  have hYRn : (Y.subgroupOf R).Normal := by
    refine ⟨fun v hv g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact hY.conj_mem _ hv _
  have himage_ne : (Y.subgroupOf R).map q ≠ ⊥ := by
    intro hbot
    have hu : q ⟨(a : X), (Subgroup.mem_inf.1 a.2).2⟩ ∈ (Y.subgroupOf R).map q :=
      Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 a.2).1)
    rw [hbot, Subgroup.mem_bot] at hu
    have haN : (a : X) ∈ N := (hqker _).1 hu
    have h3 : (a : X) ∈ Y ⊓ N := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 a.2).1, haN⟩
    rw [hYN, Subgroup.mem_bot] at h3
    exact ha1 h3
  haveI : ((Y.subgroupOf R).map q).Normal := hYRn.map q hqsurj
  have htop : (Y.subgroupOf R).map q = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y.subgroupOf R).map q)).resolve_left himage_ne
  have hR' : R ≤ (Y ⊓ R) ⊔ N := by
    intro r hr
    have hmem : q ⟨r, hr⟩ ∈ (Y.subgroupOf R).map q := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hvr⟩ := Subgroup.mem_map.1 hmem
    have hN' : (v : X)⁻¹ * r ∈ N := by
      have h4 : q (v⁻¹ * ⟨r, hr⟩) = 1 := by
        rw [map_mul, map_inv, hvr, inv_mul_cancel]
      have h5 := (hqker _).1 h4
      simpa using h5
    have hv' : (v : X) ∈ Y ⊓ R := Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hv, v.2⟩
    have key := Subgroup.mul_mem _ (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right hN')
    have e : (v : X) * ((v : X)⁻¹ * r) = r := by group
    rwa [e] at key
  exact endg_false_of_split h inf_le_right hcomm hR'

theorem endg_R_inf_centralizer_eq_bot (h : EndgameHyp X A R N H t) {Y : Subgroup X}
    (hY : Y.Normal) (hYA : Y ⊓ A ≠ ⊥) : R ⊓ Subgroup.centralizer (Y : Set X) = ⊥ := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYA
  have ha1 : (a : X) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  have haY : (a : X) ∈ Y := (Subgroup.mem_inf.1 a.2).1
  have haA : (a : X) ∈ A := (Subgroup.mem_inf.1 a.2).2
  haveI := hY
  have hC : (Subgroup.centralizer (Y : Set X)).Normal := Subgroup.normal_centralizer
  have hZn : (Subgroup.centralizer (Y : Set X) ⊓ H).Normal := by
    refine ⟨fun z hz g => ?_⟩
    exact Subgroup.mem_inf.2 ⟨hC.conj_mem z (Subgroup.mem_inf.1 hz).1 g,
      h.H_normal.conj_mem z (Subgroup.mem_inf.1 hz).2 g⟩
  have hZt : ∀ z ∈ Subgroup.centralizer (Y : Set X) ⊓ H, z * t = t * z := by
    intro z hz
    obtain ⟨hzC, hzH⟩ := Subgroup.mem_inf.1 hz
    have hcomm : z * (a : X) = (a : X) * z :=
      (Subgroup.mem_centralizer_iff.1 hzC (a : X) haY).symm
    exact h.N2 z hzH (a : X) haA ha1 hcomm t h.t_mem
  have hZR : (Subgroup.centralizer (Y : Set X) ⊓ H) ⊓ R = ⊥ :=
    endg_inf_R_eq_bot h hZn hZt
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxH : x ∈ H := h.R_le_H hxR
  have hxZ : x ∈ (Subgroup.centralizer (Y : Set X) ⊓ H) ⊓ R :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxC, hxH⟩, hxR⟩
  rw [hZR, Subgroup.mem_bot] at hxZ
  rw [Subgroup.mem_bot]
  exact hxZ

end Inf

section PerfCore

variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

private theorem endgF_perfect_of_simple (S : Type) [Group S] [IsSimpleGroup S]
    (h16 : 16 ∣ Nat.card S) : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ with hb | ht
  · exfalso
    haveI : IsMulCommutative S := ⟨⟨fun a b => by
      have hab : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
      exact hab⟩⟩
    have hp : (Nat.card S).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rcases hp.eq_one_or_self_of_dvd 2 (dvd_trans (by norm_num : (2 : ℕ) ∣ 16) h16) with h1 | h2
    · norm_num at h1
    · rw [← h2] at h16
      norm_num at h16
  · exact ht

theorem endg_perfCore_spec (h : EndgameHyp X A R N H t) :
    ∃ K : Subgroup X, K ≤ R ∧ ⁅K, K⁆ = K ∧ K ≠ ⊥ ∧ R ≤ K ⊔ N ∧
      (∀ g : X, g ∈ Subgroup.normalizer (R : Set X) → g ∈ Subgroup.normalizer (K : Set X)) ∧
      ∀ J : Subgroup X, J ≤ K → (J.subgroupOf K).Normal → J ≠ K →
        16 ∣ (J.subgroupOf K).index := by
  obtain ⟨S, hSg, π, hπs, hπk, hS, h16, -⟩ := h.quot
  have hperf := endgF_perfect_of_simple S h16
  obtain ⟨K, hKR, hKperf, hnorm, hcover⟩ := endg_exists_perfCore R
  have hRK : R ≤ K ⊔ N := hcover S π hπs hperf N hπk
  have hKne : K ≠ ⊥ := by
    intro hK
    rw [hK, bot_sup_eq] at hRK
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨r, rfl⟩ := hπs s
    exact hs ((hπk r).mpr (hRK r.2))
  refine ⟨K, hKR, hKperf, hKne, hRK, hnorm, ?_⟩
  intro J hJK hJn hJne
  have hN2 : IsPGroup 2 ↥(K ⊓ N) := h.N_pgroup.to_le inf_le_right
  let πK : ↥K →* S := π.comp (Subgroup.inclusion hKR)
  have hπK_apply : ∀ k : ↥K, πK k = π ⟨(k : X), hKR k.2⟩ := fun k => rfl
  have hker : πK.ker = (K ⊓ N).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, hπK_apply, hπk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩
  have hπK_surj : Function.Surjective πK := by
    have hsup : K.subgroupOf R ⊔ N.subgroupOf R = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKR h.N_le, Subgroup.subgroupOf_eq_top]
      exact hRK
    have hmap : (K.subgroupOf R).map π = ⊤ := by
      have h1 : (K.subgroupOf R ⊔ N.subgroupOf R).map π = ⊤ := by
        rw [hsup]
        exact Subgroup.map_top_of_surjective π hπs
      have h2 : (N.subgroupOf R).map π = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        exact (hπk y).mpr (Subgroup.mem_subgroupOf.mp hy)
      rw [Subgroup.map_sup, h2, sup_bot_eq] at h1
      exact h1
    intro s
    have hs : s ∈ (K.subgroupOf R).map π := by
      rw [hmap]
      exact Subgroup.mem_top s
    obtain ⟨r, hr, hrs⟩ := Subgroup.mem_map.mp hs
    refine ⟨⟨(r : X), Subgroup.mem_subgroupOf.mp hr⟩, ?_⟩
    rw [hπK_apply]
    exact hrs
  have hPidx : ((K ⊓ N).subgroupOf K).index = Nat.card S := by
    rw [← hker, Subgroup.index_ker, πK.range_eq_top_of_surjective hπK_surj, Subgroup.card_top]
  have hJN : J ≤ N := by
    have hJmap : ((J.subgroupOf K).map πK).Normal := Subgroup.Normal.map hJn πK hπK_surj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J.subgroupOf K).map πK) with hb | ht
    · intro x hx
      have hxK : x ∈ K := hJK hx
      have h1 : πK ⟨x, hxK⟩ ∈ (J.subgroupOf K).map πK :=
        Subgroup.mem_map_of_mem πK (Subgroup.mem_subgroupOf.mpr hx)
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : (⟨x, hxK⟩ : ↥K) ∈ πK.ker := h1
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      exact h2.2
    · exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hPgrp : IsPGroup 2 ↥((K ⊓ N).subgroupOf K) :=
        hN2.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ N ≤ K)).symm
      haveI : Group.IsNilpotent ↥((K ⊓ N).subgroupOf K) := hPgrp.isNilpotent
      let f : ↥((K ⊓ N).subgroupOf K) →* ↥K ⧸ (J.subgroupOf K) :=
        (QuotientGroup.mk' (J.subgroupOf K)).comp ((K ⊓ N).subgroupOf K).subtype
      have hf : Function.Surjective f := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        have hx : πK x ∈ (J.subgroupOf K).map πK := by
          rw [ht]
          exact Subgroup.mem_top _
        obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp hx
        have hp : x * j⁻¹ ∈ (K ⊓ N).subgroupOf K := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hjx, mul_inv_cancel]
        refine ⟨⟨x * j⁻¹, hp⟩, ?_⟩
        show (QuotientGroup.mk (x * j⁻¹) : ↥K ⧸ (J.subgroupOf K)) = QuotientGroup.mk x
        rw [QuotientGroup.eq]
        have hjj : (x * j⁻¹)⁻¹ * x = j := by group
        rw [hjj]
        exact hj
      haveI : Group.IsSolvable (↥K ⧸ (J.subgroupOf K)) := Group.isSolvable_of_surjective hf
      have hall := endg_perfect_hom_trivial hKperf (QuotientGroup.mk' (J.subgroupOf K))
      have hKJ : K ≤ J := by
        intro x hx
        have h1 := hall ⟨x, hx⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
        exact h1
      exact hJne (le_antisymm hJK hKJ)
  have hJP : J.subgroupOf K ≤ (K ⊓ N).subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨x.2, hJN hx⟩
  have hdvd : ((K ⊓ N).subgroupOf K).index ∣ (J.subgroupOf K).index :=
    Subgroup.index_dvd_of_le hJP
  rw [hPidx] at hdvd
  exact dvd_trans h16 hdvd

end PerfCore

end CFSG.RankThree.GF2n.Stroth80
