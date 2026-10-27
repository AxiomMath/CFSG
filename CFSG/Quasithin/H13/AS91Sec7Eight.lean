module

public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Plane
public import CFSG.Quasithin.H13.AS91Sec7Zfix

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet IsOctad M24g S24)

namespace M24G

abbrev sextE0 : Finset (Finset (Fin 24)) := (Native.baseSext.map maskFin).toFinset

theorem sextFin_zero_eq : sextFin 0 = sextE0 := by
  unfold sextFin sextOfL
  rw [sextList_zero]

theorem isSextet_sextE0 : IsSextet sextE0 := by
  rw [← sextFin_zero_eq]
  exact isSextet_sextFin (by norm_num)

theorem isOctad_of_mem_octsOf {S : Finset (Finset (Fin 24))} (hS : IsSextet S)
    {O : Finset (Fin 24)} (hO : O ∈ octsOf S) : IsOctad O := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsOf.1 hO
  obtain ⟨-, -, -, -, h5⟩ := hS
  exact h5 a ha b hb hab

abbrev trioA : Finset (Finset (Fin 24)) := {maskFin 255, maskFin 986880, maskFin 15790080}

abbrev trioB : Finset (Finset (Fin 24)) := {maskFin 3855, maskFin 983280, maskFin 15790080}

abbrev trioC : Finset (Finset (Fin 24)) := {maskFin 255, maskFin 65280, maskFin 16711680}

theorem sub_trioA : trioA ⊆ octsOf sextE0 := by decide +kernel

theorem sub_trioB : trioB ⊆ octsOf sextE0 := by decide +kernel

theorem sub_trioC : trioC ⊆ octsOf sextE0 := by decide +kernel

theorem sub_trioC_W : trioC ⊆ octsOf (lPerm 0 • sextE0) := by decide +kernel

theorem isTrio_trioA : IsTrio trioA :=
  isTrio_of_three (A := maskFin 255) (B := maskFin 986880) (C := maskFin 15790080)
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem isTrio_trioB : IsTrio trioB :=
  isTrio_of_three (A := maskFin 3855) (B := maskFin 983280) (C := maskFin 15790080)
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem isTrio_trioC : IsTrio trioC :=
  isTrio_of_three (A := maskFin 255) (B := maskFin 65280) (C := maskFin 16711680)
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (isOctad_of_mem_octsOf isSextet_sextE0 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem kappa_one_base :
    Kappa sextE0 (lPerm 0 • trioA) 1 := by
  show ((lPerm 0 • trioA) ∩ octsOf sextE0).card = 1
  decide +kernel

theorem kappa_two_base :
    Kappa sextE0 (lPerm 0 • trioB) 2 := by
  refine ⟨by decide +kernel, lPerm 0 • sextE0,
    (isSextet_smul_iff (lPerm_mem 0)).2 isSextet_sextE0, ?_,
    (trioIn_smul_iff (lPerm 0)).2 sub_trioB⟩
  show ((octsOf (lPerm 0 • sextE0)) ∩ octsOf sextE0).card = 3
  decide +kernel

theorem coplanar_one_base :
    Coplanar (lPerm 0 • trioA) trioC :=
  ⟨lPerm 0 • sextE0, (isSextet_smul_iff (lPerm_mem 0)).2 isSextet_sextE0,
    (trioIn_smul_iff (lPerm 0)).2 sub_trioA, sub_trioC_W⟩

theorem coplanar_two_base :
    Coplanar (lPerm 0 • trioB) trioC :=
  ⟨lPerm 0 • sextE0, (isSextet_smul_iff (lPerm_mem 0)).2 isSextet_sextE0,
    (trioIn_smul_iff (lPerm 0)).2 sub_trioB, sub_trioC_W⟩

theorem base_kappa_one :
    ∃ t k : Finset (Finset (Fin 24)), IsTrio t ∧ Kappa (sextFin 0) t 1 ∧
      k ∈ triosOf (sextFin 0) ∧ Coplanar t k := by
  rw [sextFin_zero_eq]
  exact ⟨lPerm 0 • trioA, trioC, isTrio_smul (lPerm_mem 0) isTrio_trioA, kappa_one_base,
    mem_triosOf.2 ⟨isTrio_trioC, sub_trioC⟩, coplanar_one_base⟩

theorem base_kappa_two :
    ∃ t k : Finset (Finset (Fin 24)), IsTrio t ∧ Kappa (sextFin 0) t 2 ∧
      k ∈ triosOf (sextFin 0) ∧ Coplanar t k := by
  rw [sextFin_zero_eq]
  exact ⟨lPerm 0 • trioB, trioC, isTrio_smul (lPerm_mem 0) isTrio_trioB, kappa_two_base,
    mem_triosOf.2 ⟨isTrio_trioC, sub_trioC⟩, coplanar_two_base⟩

theorem exists_coplanar_of_base
    {i : Fin 4} {t₀ k₀ : Finset (Finset (Fin 24))} (ht₀ : IsTrio t₀)
    (hk₀ : k₀ ∈ triosOf (sextFin 0)) (hi : Kappa (sextFin 0) t₀ i) (hc : Coplanar t₀ k₀)
    {U t : Finset (Finset (Fin 24))} (hU : IsSextet U) (ht : IsTrio t) (hκ : Kappa U t i) :
    ∃ k ∈ triosOf U, Coplanar t k := by
  obtain ⟨h, hh, hhU⟩ := sextet_transitive hU
  have hg : h⁻¹ ∈ M24g := M24g.inv_mem hh
  have hgU : h⁻¹ • sextFin 0 = U := by rw [← hhU, inv_smul_smul]
  have hl : Kappa U (h⁻¹ • t₀) i := by
    rw [← hgU]
    exact (kappa_smul_iff hg i).2 hi
  have hkU : h⁻¹ • k₀ ∈ triosOf U := by
    rw [← hgU, triosOf_smul hg]
    exact Finset.smul_mem_smul_finset hk₀
  have hcU : Coplanar (h⁻¹ • t₀) (h⁻¹ • k₀) := (coplanar_smul_iff hg).2 hc
  obtain ⟨g, hg', hgU', hgt⟩ := kappa_orbit hU (isTrio_smul hg ht₀) ht hl hκ
  refine ⟨g • (h⁻¹ • k₀), ?_, ?_⟩
  · have h1 : g • (h⁻¹ • k₀) ∈ g • triosOf U := Finset.smul_mem_smul_finset hkU
    rwa [← triosOf_smul hg', hgU'] at h1
  · rw [← hgt]
    exact (coplanar_smul_iff hg').2 hcU

theorem exists_coplanar_kappa_one
    {U t : Finset (Finset (Fin 24))} (hU : IsSextet U) (ht : IsTrio t) (hκ : Kappa U t 1) :
    ∃ k ∈ triosOf U, Coplanar t k := by
  obtain ⟨t₀, k₀, ht₀, hi, hk₀, hc⟩ := base_kappa_one
  exact exists_coplanar_of_base ht₀ hk₀ hi hc hU ht hκ

theorem exists_coplanar_kappa_two
    {U t : Finset (Finset (Fin 24))} (hU : IsSextet U) (ht : IsTrio t) (hκ : Kappa U t 2) :
    ∃ k ∈ triosOf U, Coplanar t k := by
  obtain ⟨t₀, k₀, ht₀, hi, hk₀, hc⟩ := base_kappa_two
  exact exists_coplanar_of_base ht₀ hk₀ hi hc hU ht hκ

theorem kappa_three_iff
    {U t : Finset (Finset (Fin 24))} (hU : IsSextet U) (ht : IsTrio t) :
    Kappa U t 3 ↔ ∀ k ∈ triosOf U, ¬ Coplanar t k := by
  constructor
  · rintro ⟨hdisj, hnot⟩ k hk ⟨S, hS, htS, hkS⟩
    obtain ⟨hkT, hkU⟩ := mem_triosOf.1 hk
    obtain ⟨o, ho⟩ := Finset.card_pos.1 (by rw [ht.1]; norm_num : 0 < t.card)
    obtain ⟨o', ho'⟩ := Finset.card_pos.1 (by rw [hkT.1]; norm_num : 0 < k.card)
    obtain ⟨i, hi, -⟩ := xi_existsUnique hU hS
    match i, hi with
    | 0, h =>
      have hSU : S = U := h
      have hoS : o ∈ octsOf S := htS ho
      rw [hSU] at hoS
      exact Finset.disjoint_left.1 hdisj ho hoS
    | 1, h => exact hnot ⟨S, hS, h, htS⟩
    | 2, h =>
      have h1 : (octsOf S ∩ octsOf U).card = 1 := h
      have hk3 : k.card = 3 := hkT.1
      have h3 : k.card ≤ (octsOf S ∩ octsOf U).card :=
        Finset.card_le_card (Finset.subset_inter hkS hkU)
      omega
    | 3, h =>
      have h1 : Disjoint (octsOf S) (octsOf U) := h
      exact Finset.disjoint_left.1 h1 (hkS ho') (hkU ho')
  · intro H
    obtain ⟨i, hi, -⟩ := kappa_existsUnique hU ht
    match i, hi with
    | 0, h =>
      exact absurd ⟨U, hU, h, h⟩ (H t (mem_triosOf.2 ⟨ht, h⟩))
    | 1, h =>
      obtain ⟨k, hk, hc⟩ := exists_coplanar_kappa_one hU ht h
      exact absurd hc (H k hk)
    | 2, h =>
      obtain ⟨k, hk, hc⟩ := exists_coplanar_kappa_two hU ht h
      exact absurd hc (H k hk)
    | 3, h => exact h

end M24G

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem coL_smul_equiv (g : G) (m n : G ⧸ c.G2) : c.CoL (g • m) (g • n) ↔ c.CoL m n := by
  constructor
  · rintro ⟨σ, h1, h2⟩
    refine ⟨g⁻¹ • σ, ?_, ?_⟩
    · exact (cInc_smul c.G2 c.G3 g m (g⁻¹ • σ)).1 (by rwa [smul_inv_smul])
    · exact (cInc_smul c.G2 c.G3 g n (g⁻¹ • σ)).1 (by rwa [smul_inv_smul])
  · rintro ⟨σ, h1, h2⟩
    exact ⟨g • σ, (cInc_smul c.G2 c.G3 g m σ).2 h1, (cInc_smul c.G2 c.G3 g n σ).2 h2⟩

theorem exists_transport_G3 {h : G} (hh : h ∈ c.G3) (n : G ⧸ c.G2) :
    (∃ l', c.OnL c.x0 l' ∧ c.LnP l' c.pi0 ∧ c.CoL l' (h⁻¹ • n)) ↔
      ∃ l, c.OnL (h • c.x0) l ∧ c.LnP l c.pi0 ∧ c.CoL l n := by
  have hinv : h⁻¹ ∈ c.G3 := inv_mem hh
  constructor
  · rintro ⟨l', h1, h2, h3⟩
    refine ⟨h • l', (cInc_smul c.G1 c.G2 h c.x0 l').2 h1, ?_, ?_⟩
    · have := cInc_smul c.G2 c.G3 h l' c.pi0
      rw [c.G3_smul_pi0 hh] at this
      exact this.2 h2
    · have := (c.coL_smul_equiv h l' (h⁻¹ • n)).2 h3
      rwa [smul_inv_smul] at this
  · rintro ⟨l, h1, h2, h3⟩
    refine ⟨h⁻¹ • l, ?_, ?_, (c.coL_smul_equiv h⁻¹ l n).2 h3⟩
    · have := (cInc_smul c.G1 c.G2 h⁻¹ (h • c.x0) l).2 h1
      rwa [inv_smul_smul] at this
    · have := cInc_smul c.G2 c.G3 h⁻¹ l c.pi0
      rw [c.G3_smul_pi0 hinv] at this
      exact this.2 h2

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem z_smul_of_exists_coL
    (hI : Sec7Inputs) (hJ : HypJ4 G z)
    {y : G ⧸ c.G1} {n : G ⧸ c.G2} (hy : c.Delta.Adj c.x0 y) (hna : c.OnL c.x0 n)
    (hny : c.OnL y n) {l : G ⧸ c.G2} (hl : c.OnL c.x0 l) (hlπ : c.LnP l c.pi0)
    (hcl : c.CoL l n) : z • y = y := by
  by_cases hln : l = n
  · subst hln
    exact c.z_smul_of_onP (c.inc_pt_plane hny hlπ)
  · have hδ : n ∈ c.deltaAt 0 c.x0 l ∨ n ∈ c.deltaAt 1 c.x0 l ∨ n ∈ c.deltaAt 2 c.x0 l :=
      (ρ.coL_iff_deltaAt hl hna).1 hcl
    have hyx : y ≠ c.x0 := hy.1.symm
    obtain ⟨u, huL, huy, hux⟩ : ∃ u, c.OnL u l ∧ c.Delta.Adj y u ∧ u ≠ c.x0 := by
      rcases hδ with h0 | h1 | h2
      · exact absurd ((ρ.mem_deltaAt_zero_iff hl hna).1 h0).symm hln
      · have hδ1 : l ∈ c.deltaAt 1 c.x0 n := ρ.deltaAt_symm 1 hl hna h1
        have hcard := c.stmt7_1_one hI.s54 hJ hna hny hyx hδ1
        obtain ⟨b, hb, hbx⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hcard]; norm_num) c.x0
        exact ⟨b, hb.1, hb.2, hbx⟩
      · have hδ2 : l ∈ c.deltaAt 2 c.x0 n := ρ.deltaAt_symm 2 hl hna h2
        have h5 : 1 < {a | c.OnL a l}.ncard := by rw [c.ncard_onL l]; norm_num
        obtain ⟨b, hb, hbx⟩ := Set.exists_ne_of_one_lt_ncard h5 c.x0
        exact ⟨b, hb, c.stmt7_1_two hI.s54 hJ hna hny hyx hδ2 hb, hbx⟩
    have huπ : c.OnP u c.pi0 := c.inc_pt_plane huL hlπ
    obtain ⟨-, m', hym', hum'⟩ := huy
    have hzm' : z • m' = m' := ρ.z_smul_line_of_onP huπ hum'
    have hzn : z • n = n := ρ.E_smul_line c.z_mem_E hna
    have hm'n : m' ≠ n := by
      rintro rfl
      exact hln (c.eq_of_onL hI.lineU hJ hux huL hl hum' hna)
    by_contra hne
    have h1 : c.OnL (z • y) n := by
      have := (cInc_smul c.G1 c.G2 z y n).2 hny
      rwa [hzn] at this
    have h2 : c.OnL (z • y) m' := by
      have := (cInc_smul c.G1 c.G2 z y m').2 hym'
      rwa [hzm'] at this
    exact hm'n (c.eq_of_onL hI.lineU hJ hne h1 hny h2 hym').symm

include ρ in
theorem kappa_three_trio
    {m : G ⧸ c.G2} (hm : c.OnL c.x0 m)
    (H : ∀ l, c.OnL c.x0 l → c.LnP l c.pi0 → ¬ c.CoL l m) :
    M24G.Kappa ρ.U₀ (ρ.trio m) 3 := by
  refine (M24G.kappa_three_iff ρ.isSextet_U₀ (ρ.isTrio_trio hm)).2 ?_
  intro k hk hcop
  rw [← ρ.sext_pi0] at hk
  obtain ⟨l, hl, hlπ, hlk⟩ := ρ.exists_line_of_mem_triosOf (g := 1) (x := c.x0) (π := c.pi0)
    (one_smul G c.x0) c.x0_mem_ptsP (by simpa using hk)
  simp only [inv_one, one_smul] at hlk
  rw [← hlk] at hcop
  obtain ⟨σ, h1, h2⟩ := (ρ.coplanar_iff hm hl).2 hcop
  exact H l hl hlπ ⟨σ, h2, h1⟩

include ρ in
theorem fix_of_kappa3
    {y : G ⧸ c.G1} {n n' : G ⧸ c.G2} (hzy : z • y = y) (hyn : c.OnL y n) (hnx : c.OnL c.x0 n)
    (hκ : M24G.Kappa ρ.U₀ (ρ.trio n) 3) (hn' : c.OnL c.x0 n')
    (hκ' : M24G.Kappa ρ.U₀ (ρ.trio n') 3) (hyx : y ≠ c.x0) {p : G ⧸ c.G1}
    (hpn' : c.OnL p n') (hpx : p ≠ c.x0) : z • p = p := by
  obtain ⟨g, hg, hgU, hgt⟩ := M24G.kappa_orbit ρ.isSextet_U₀ (ρ.isTrio_trio hnx)
    (ρ.isTrio_trio hn') hκ hκ'
  obtain ⟨h₁, hφ⟩ := ρ.exists_φ_eq hg
  have hh₁ : (h₁ : G) ∈ c.G3 := (ρ.stab₃ h₁).2 (by rw [hφ]; exact hgU)
  have htr : ρ.trio ((h₁ : G) • n) = ρ.trio n' := by
    rw [ρ.trio_smul_line h₁ hnx, hφ, hgt]
  have hx : CInc c.G1 c.G2 c.x0 ((h₁ : G) • n) := by
    have := (cInc_smul c.G1 c.G2 (h₁ : G) c.x0 n).2 hnx
    rwa [c.smul_x0_of_mem h₁.2] at this
  have hmn : (h₁ : G) • n = n' := ρ.trio_injOn hx hn' htr
  have hy' : c.OnL ((h₁ : G) • y) n' := by
    have := (cInc_smul c.G1 c.G2 (h₁ : G) y n).2 hyn
    rwa [hmn] at this
  have hy'x : (h₁ : G) • y ≠ c.x0 := by
    intro hc0
    apply hyx
    apply MulAction.injective (h₁ : G)
    dsimp only
    rw [hc0, c.smul_x0_of_mem h₁.2]
  obtain ⟨e, he, hep⟩ := c.E_transitive_line hn' hy' hy'x hpn' hpx
  have hh : e * (h₁ : G) ∈ c.G3 := mul_mem (c.E_le_G3 he) hh₁
  have hcomm := c.z_mul_of_mem_G3 hh
  have hpe : (e * (h₁ : G)) • y = p := by rw [mul_smul, hep]
  rw [← hpe, ← mul_smul, hcomm, mul_smul, hzy]

include ρ in
theorem exists_coL_of_z_smul
    (hI : Sec7Inputs) (hJ : HypJ4 G z)
    {y : G ⧸ c.G1} {n : G ⧸ c.G2} (hy : c.Delta.Adj c.x0 y) (hna : c.OnL c.x0 n)
    (hny : c.OnL y n) (hzy : z • y = y) : ∃ l, c.OnL c.x0 l ∧ c.LnP l c.pi0 ∧ c.CoL l n := by
  by_contra H
  have H' : ∀ l, c.OnL c.x0 l → c.LnP l c.pi0 → ¬ c.CoL l n :=
    fun l h1 h2 h3 => H ⟨l, h1, h2, h3⟩
  have hκ : M24G.Kappa ρ.U₀ (ρ.trio n) 3 := kappa_three_trio ρ hna H'
  have hall : ∀ p, c.Delta.Adj c.x0 p → z • p = p := by
    intro p hp
    have hp0 := hp
    obtain ⟨hne, m, hxm, hpm⟩ := hp
    by_cases hco : ∃ l, c.OnL c.x0 l ∧ c.LnP l c.pi0 ∧ c.CoL l m
    · obtain ⟨l, h1, h2, h3⟩ := hco
      exact z_smul_of_exists_coL ρ hI hJ hp0 hxm hpm h1 h2 h3
    · have H'' : ∀ l, c.OnL c.x0 l → c.LnP l c.pi0 → ¬ c.CoL l m :=
        fun l h1 h2 h3 => hco ⟨l, h1, h2, h3⟩
      have hκm := kappa_three_trio ρ hxm H''
      exact fix_of_kappa3 ρ hzy hny hna hκ hxm hκm hy.1.symm hpm hne.symm
  obtain ⟨y₀, hy₀, hz₀⟩ := ρ.exists_adj_z_smul_ne
  exact hz₀ (hall y₀ hy₀)

include ρ in
theorem stmt7_8_x0
    (hI : Sec7Inputs) (hJ : HypJ4 G z)
    {y : G ⧸ c.G1} {n : G ⧸ c.G2} (hy : c.Delta.Adj c.x0 y) (hna : c.OnL c.x0 n)
    (hny : c.OnL y n) :
    z • y = y ↔ ∃ l, c.OnL c.x0 l ∧ c.LnP l c.pi0 ∧ c.CoL l n :=
  ⟨fun hzy => exists_coL_of_z_smul ρ hI hJ hy hna hny hzy,
    fun ⟨_, h1, h2, h3⟩ => z_smul_of_exists_coL ρ hI hJ hy hna hny h1 h2 h3⟩

include ρ in
theorem stmt7_8
    (hI : Sec7Inputs) (hJ : HypJ4 G z) {a y : G ⧸ c.G1}
    (ha : c.OnP a c.pi0) (hy : c.Delta.Adj a y) {n : G ⧸ c.G2} (hna : c.OnL a n)
    (hny : c.OnL y n) :
    z • y = y ↔ ∃ l, c.OnL a l ∧ c.LnP l c.pi0 ∧ c.CoL l n := by
  obtain ⟨h, hh, rfl⟩ := c.exists_G3_smul_x0 ha
  have hinv : h⁻¹ ∈ c.G3 := inv_mem hh
  have hy' : c.Delta.Adj c.x0 (h⁻¹ • y) := by
    have := CFSG.Quasithin.GraphAction.adj_smul (H := G) (Γ := c.Delta) h⁻¹ (h • c.x0) y
    rw [inv_smul_smul] at this
    exact this.2 hy
  have hn' : c.OnL c.x0 (h⁻¹ • n) := by
    have := (cInc_smul c.G1 c.G2 h⁻¹ (h • c.x0) n).2 hna
    rwa [inv_smul_smul] at this
  have hny' : c.OnL (h⁻¹ • y) (h⁻¹ • n) := (cInc_smul c.G1 c.G2 h⁻¹ y n).2 hny
  have e1 : z • (h⁻¹ • y) = h⁻¹ • (z • y) := by
    rw [← mul_smul, c.z_mul_of_mem_G3 hinv, mul_smul]
  have key1 : z • (h⁻¹ • y) = h⁻¹ • y ↔ z • y = y := by
    rw [e1]
    exact (MulAction.injective h⁻¹).eq_iff
  exact key1.symm.trans ((stmt7_8_x0 ρ hI hJ hy' hn' hny').trans (c.exists_transport_G3 hh n))

end ResM24

end CFSG.Quasithin.H13.AS91

end
