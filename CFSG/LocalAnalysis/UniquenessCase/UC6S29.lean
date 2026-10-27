module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S25

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

theorem mem_normalizer_of_forward_uc6 {G : Type*} [Group G] [Finite G] {W : Subgroup G} {k : G}
    (h : ∀ w ∈ W, k * w * k⁻¹ ∈ W) : k ∈ normalizer (W : Set G) := by
  have hle : W.map (MulAut.conj k).toMonoidHom ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using h w hw
  have heq : W.map (MulAut.conj k).toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    rw [← heq] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = x := by
      have h2 : k * w * k⁻¹ = k * x * k⁻¹ := by simpa [MulAut.conj_apply] using hwx
      simpa using h2
    exact this ▸ hw

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C626 : Prop :=
  ∀ p ∈ uniqueFourSigma m.M, ¬ p ∣ Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G))

@[expose] def C628b : Prop :=
  ∀ p ∈ uniqueFourSigma m.M, ¬ p ∣ Nat.card ↥(CFSG.pPrimeCore m.r ↥m.K)

@[expose] def U : Subgroup G := (CFSG.pPrimeCore m.r ↥m.K).map m.K.subtype

theorem U_le_K : m.U ≤ m.K := Subgroup.map_subtype_le _

theorem card_U : Nat.card m.U = Nat.card (CFSG.pPrimeCore m.r ↥m.K) :=
  Subgroup.card_map_of_injective m.K.subtype_injective

theorem coprime_card_U : Nat.Coprime m.r (Nat.card m.U) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rw [m.card_U]
  exact CFSG.pPrimeCore_coprime_card

theorem mem_normalizer_K {g : G} (hg : g ∈ m.M) : g ∈ normalizer (m.K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact m.conj_mem_K hg hx
  · intro hx
    have := m.conj_mem_K (m.M.inv_mem hg) hx
    simpa [mul_assoc] using this

theorem K_le_normalizer_U : m.K ≤ normalizer (m.U : Set G) := by
  intro k hk
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.K)
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(⟨k, hk⟩ : ↥m.K) * u * (⟨k, hk⟩ : ↥m.K)⁻¹, ?_, by simp⟩
    exact (inferInstance : (CFSG.pPrimeCore m.r ↥m.K).Normal).conj_mem u hu ⟨k, hk⟩
  · rintro ⟨u, hu, hux⟩
    refine ⟨(⟨k, hk⟩ : ↥m.K)⁻¹ * u * (⟨k, hk⟩ : ↥m.K), ?_, ?_⟩
    · have := (inferInstance : (CFSG.pPrimeCore m.r ↥m.K).Normal).conj_mem u hu ⟨k, hk⟩⁻¹
      simpa using this
    · have h2 : k * x * k⁻¹ = (u : G) := hux.symm ▸ rfl
      show k⁻¹ * (u : G) * k = x
      rw [← h2]
      group

theorem le_U_of_normal_coprime {N : Subgroup G} (hNK : N ≤ m.K)
    (hn : m.K ≤ normalizer (N : Set G)) (hc : Nat.Coprime m.r (Nat.card N)) : N ≤ m.U := by
  have hN' : (N.subgroupOf m.K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hn
  have hcard : Nat.card (N.subgroupOf m.K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle := CFSG.le_pPrimeCore_of_normal_coprime (p := m.r) hN' (by rw [hcard]; exact hc)
  have := Subgroup.map_mono (f := m.K.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNK] at this

theorem conj_U_le {g : G} (hg : g ∈ m.M) : ∀ u ∈ m.U, g * u * g⁻¹ ∈ m.U := by
  set W : Subgroup G := m.U.map (MulAut.conj g).toMonoidHom with hW
  have hWK : W ≤ m.K := by
    rintro _ ⟨u, hu, rfl⟩
    exact m.conj_mem_K hg (m.U_le_K hu)
  have hKW : m.K ≤ normalizer (W : Set G) := by
    intro k hk
    refine mem_normalizer_of_forward_uc6 ?_
    rintro _ ⟨u, hu, rfl⟩
    have hk' : g⁻¹ * k * g ∈ m.K := by
      simpa using m.conj_mem_K (m.M.inv_mem hg) hk
    have hmem := (mem_normalizer_iff.1 (m.K_le_normalizer_U hk') u).1 hu
    refine ⟨_, hmem, ?_⟩
    show g * ((g⁻¹ * k * g) * u * (g⁻¹ * k * g)⁻¹) * g⁻¹ = k * (g * u * g⁻¹) * k⁻¹
    group
  have hWc : Nat.Coprime m.r (Nat.card W) := by
    rw [hW, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact m.coprime_card_U
  have hWU := m.le_U_of_normal_coprime hWK hKW hWc
  intro u hu
  exact hWU ⟨u, hu, rfl⟩

theorem isCyclic_of_isSylowOf (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) {S : Subgroup G}
    (hS : IsSylowOf m.r S m.K) : IsCyclic ↥S := by
  obtain ⟨Q, rfl⟩ := hS
  haveI := hcyc Q
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥m.K) m.K.subtype m.K.subtype_injective).toMonoidHom
    (MulEquiv.surjective _)

theorem Z_le_of_normal_gt_U (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) {N : Subgroup G}
    (hNK : N ≤ m.K) (hn : m.K ≤ normalizer (N : Set G)) (hlt : m.U < N) : m.Z ≤ N := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hrN : m.r ∣ Nat.card N := by
    by_contra h
    exact absurd (m.le_U_of_normal_coprime hNK hn
      ((Nat.Prime.coprime_iff_not_dvd m.hr).2 h)) (not_le_of_gt hlt)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' m.r hrN
  have hxo : orderOf (x : G) = m.r := by rw [Subgroup.orderOf_coe]; exact hx
  set Y : Subgroup G := Subgroup.zpowers (x : G) with hY
  have hYcard : Nat.card Y = m.r := by rw [hY, Nat.card_zpowers, hxo]
  have hYN : Y ≤ N := (Subgroup.zpowers_le).2 x.2
  have hYK : Y ≤ m.K := hYN.trans hNK
  have hYp : IsPGroup m.r Y := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hYcard)
  have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z)
  obtain ⟨S, hS, hZS⟩ := exists_isSylowOf_ge m.Z_le_K hZp
  have hScyc : IsCyclic S := m.isCyclic_of_isSylowOf hcyc hS
  obtain ⟨k, hkK, hk⟩ := exists_conj_le_of_isSylowOf hS hYK hYp
  set Y' : Subgroup G := Y.map (MulAut.conj k⁻¹).toMonoidHom with hY'
  have hY'S : Y' ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    have := hk y hy
    simpa [MulAut.conj_apply] using this
  have hY'card : Nat.card Y' = m.r := by
    rw [hY', Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hYcard]
  have hYZ : Y' = m.Z :=
    eq_of_card_eq_of_isCyclic hScyc hY'S hZS (by rw [hY'card, m.card_Z])
  intro z hz
  rw [← hYZ] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hkinv : k⁻¹ ∈ normalizer (N : Set G) := hn (m.K.inv_mem hkK)
  have := (mem_normalizer_iff.1 hkinv y).1 (hYN hy)
  simpa [MulAut.conj_apply] using this

theorem eq_K_of_normal_gt_U (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) {N : Subgroup G}
    (hNK : N ≤ m.K) (hn : m.K ≤ normalizer (N : Set G)) (hlt : m.U < N) : N = m.K := by
  refine le_antisymm hNK ?_
  refine (closure_le _).2 ?_
  rintro _ ⟨g, hg, z, hz, rfl⟩
  set N' : Subgroup G := N.map (MulAut.conj g⁻¹).toMonoidHom with hN'
  have hN'K : N' ≤ m.K := by
    rintro _ ⟨n, hn', rfl⟩
    simpa [MulAut.conj_apply] using m.conj_mem_K (m.M.inv_mem hg) (hNK hn')
  have hKN' : m.K ≤ normalizer (N' : Set G) := by
    intro k hk
    refine mem_normalizer_of_forward_uc6 ?_
    rintro _ ⟨n, hn', rfl⟩
    have hk' : g * k * g⁻¹ ∈ m.K := m.conj_mem_K hg hk
    have hmem := (mem_normalizer_iff.1 (hn hk') n).1 hn'
    refine ⟨_, hmem, ?_⟩
    show g⁻¹ * ((g * k * g⁻¹) * n * (g * k * g⁻¹)⁻¹) * g⁻¹⁻¹ = k * (g⁻¹ * n * g⁻¹⁻¹) * k⁻¹
    group
  have hUN' : m.U ≤ N' := by
    intro u hu
    refine ⟨g * u * g⁻¹, hlt.le (m.conj_U_le hg u hu), ?_⟩
    show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u
    group
  have hlt' : m.U < N' := by
    refine lt_of_le_of_ne hUN' (fun h => ?_)
    apply (not_le_of_gt hlt)
    intro n hn'
    have h1 : g⁻¹ * n * g ∈ N' := ⟨n, hn', by simp [MulAut.conj_apply]⟩
    rw [← h] at h1
    have h2 := m.conj_U_le hg _ h1
    simpa [mul_assoc] using h2
  have hZN' := m.Z_le_of_normal_gt_U hcyc hN'K hKN' hlt' hz
  obtain ⟨n, hn', hnz⟩ := hZN'
  have : g * z * g⁻¹ = n := by
    have h3 : g⁻¹ * n * g = z := by simpa [MulAut.conj_apply] using hnz
    rw [← h3]
    group
  rw [this]
  exact hn'

theorem not_Z_le_U : ¬ m.Z ≤ m.U := by
  intro h
  have : m.r ∣ Nat.card m.U := by
    have := Subgroup.card_dvd_of_le h
    rwa [m.card_Z] at this
  exact m.hr.ne_one (m.coprime_card_U.eq_one_of_dvd this)

theorem Kbar_isSimple (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) : IsSimpleGroup m.Kbar := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 m.not_Z_le_U
  have hzne : (QuotientGroup.mk (⟨z, m.Z_le_K hzZ⟩ : ↥m.K) : m.Kbar) ≠ 1 := by
    intro h
    apply hzU
    have h2 := (QuotientGroup.eq_one_iff _).1 h
    exact ⟨_, h2, rfl⟩
  haveI hnt : Nontrivial m.Kbar :=
    ⟨⟨(QuotientGroup.mk (⟨z, m.Z_le_K hzZ⟩ : ↥m.K) : m.Kbar), 1, hzne⟩⟩
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun Nb hNb => ?_ }
  set N' : Subgroup ↥m.K := Nb.comap (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.K)) with hN'
  haveI : N'.Normal := Subgroup.Normal.comap hNb _
  set N : Subgroup G := N'.map m.K.subtype with hN
  have hNK : N ≤ m.K := Subgroup.map_subtype_le _
  have hsub : N.subgroupOf m.K = N' := Subgroup.comap_map_eq_self_of_injective m.K.subtype_injective N'
  have hn : m.K ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).1 (by rw [hsub]; infer_instance)
  by_cases hNU : N ≤ m.U
  · left
    rw [eq_bot_iff]
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxN : (x : G) ∈ N := ⟨x, hxb, rfl⟩
    obtain ⟨u, hu, hux⟩ := hNU hxN
    have : x = u := Subtype.ext hux.symm
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact this ▸ hu
  · right
    have hUN : m.U ≤ N := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨u, ?_, rfl⟩
      have h1 : ((u : ↥m.K) : m.Kbar) = 1 := (QuotientGroup.eq_one_iff u).2 hu
      show ((u : ↥m.K) : m.Kbar) ∈ Nb
      rw [h1]
      exact Nb.one_mem
    have hlt : m.U < N := lt_of_le_of_ne hUN (fun h => hNU (h ▸ le_rfl))
    have hNK' : N = m.K := m.eq_K_of_normal_gt_U hcyc hNK hn hlt
    rw [eq_top_iff]
    intro xb _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxK : (x : G) ∈ N := by rw [hNK']; exact x.2
    obtain ⟨y, hy, hyx⟩ := hxK
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem dvd_card_M_of_mem_sigma {p : ℕ} (hp : p ∈ uniqueFourSigma m.M) : p ∣ Nat.card m.M := by
  have hpr : p.Prime := hp.1.1
  obtain ⟨E, hEM, -, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hpr (m.M)
  have h4 := four_le_pRank_of_sigma hp
  have h1 : p ^ Open.pRank p m.M ∣ Nat.card m.M := hEcard ▸ Subgroup.card_dvd_of_le hEM
  exact (dvd_pow_self p (by omega)).trans h1

theorem false_of_Kbar_comm (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626)
    (h628b : m.C628b) (hcomm : ∀ a b : m.Kbar, a * b = b * a) : False := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI hsimple := m.Kbar_isSimple hcyc
  set U' := CFSG.pPrimeCore m.r ↥m.K with hU'
  set Zb : Subgroup m.Kbar := (m.Z.subgroupOf m.K).map (QuotientGroup.mk' U') with hZb
  haveI hZbn : Zb.Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 m.not_Z_le_U
  have hZbne : Zb ≠ ⊥ := by
    intro h
    have hmem : (QuotientGroup.mk' U' (⟨z, m.Z_le_K hzZ⟩ : ↥m.K)) ∈ Zb :=
      ⟨⟨z, m.Z_le_K hzZ⟩, hzZ, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hzU ⟨_, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  have hZbtop : Zb = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal Zb).resolve_left hZbne
  have hZ'card : Nat.card (m.Z.subgroupOf m.K) = m.r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_K).toEquiv]
    exact m.card_Z
  have hKbcard : Nat.card m.Kbar = m.r := by
    have hdvd : Nat.card Zb ∣ m.r := by
      have := Subgroup.card_map_dvd (m.Z.subgroupOf m.K) (QuotientGroup.mk' U')
      rwa [hZ'card] at this
    rw [hZbtop, Subgroup.card_top] at hdvd
    rcases (Nat.dvd_prime m.hr).1 hdvd with h1 | h1
    · exfalso
      have := Finite.one_lt_card (α := m.Kbar)
      omega
    · exact h1
  have hKcard : Nat.card m.K = m.r * Nat.card m.U := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup U']
    show Nat.card m.Kbar * Nat.card U' = _
    rw [hKbcard, ← m.card_U]
  have hZsyl : IsSylowOf m.r m.Z m.K := by
    rw [isSylowOf_iff]
    refine ⟨m.Z_le_K, IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := m.Z) (K := m.K)
    rw [inf_of_le_left m.Z_le_K, m.card_Z, hKcard] at h1
    have h2 : m.Z.relIndex m.K = Nat.card m.U :=
      Nat.eq_of_mul_eq_mul_right m.hr.pos (by rw [h1, mul_comm])
    intro hdvd
    rw [h2] at hdvd
    exact m.hr.ne_one (m.coprime_card_U.eq_one_of_dvd hdvd)
  have hFr : m.M = m.K ⊔ (m.M ⊓ normalizer (m.Z : Set G)) :=
    frattini_of_isSylowOf m.K_le_M (fun g hg => m.mem_normalizer_K hg) hZsyl
  have hp : m.S.p ∈ uniqueFourSigma m.M := m.S.hp
  set p := m.S.p with hpdef
  have hpr : p.Prime := hp.1.1
  have hpr_ne : p ≠ m.r := fun h => m.hrσ (h ▸ hp)
  have hpU : ¬ p ∣ Nat.card m.U := by rw [m.card_U]; exact h628b p hp
  have hpK : ¬ p ∣ Nat.card m.K := by
    rw [hKcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hpr).1 hd with h | h
    · exact hpr_ne ((Nat.prime_dvd_prime_iff_eq hpr m.hr).1 h)
    · exact hpU h
  have hpN : ¬ p ∣ Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) := h626 p hp
  set K' : Subgroup ↥m.M := m.K.subgroupOf m.M with hK'
  set N' : Subgroup ↥m.M := (m.M ⊓ normalizer (m.Z : Set G)).subgroupOf m.M with hN'
  haveI hK'n : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer m.K_le_M).2
      (fun g hg => m.mem_normalizer_K hg)
  have htop : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  have hKN' : K' ⊔ N' = ⊤ := by
    apply Subgroup.map_injective m.M.subtype_injective
    rw [Subgroup.map_sup, hK', hN', Subgroup.map_subgroupOf_eq_of_le m.K_le_M,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, htop]
    exact hFr.symm
  have hidx : K'.index = K'.relIndex N' := by
    rw [← Subgroup.relIndex_top_right, ← hKN', Subgroup.relIndex_sup_left]
  have hidxdvd : K'.index ∣ Nat.card N' := by
    rw [hidx]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := K') (K := N'))
  have hN'card : Nat.card N' = Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hK'card : Nat.card K' = Nat.card m.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.K_le_M).toEquiv
  have hMcard : Nat.card K' * K'.index = Nat.card ↥m.M := Subgroup.card_mul_index K'
  have hpM : ¬ p ∣ Nat.card ↥m.M := by
    rw [← hMcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hpr).1 hd with h | h
    · exact hpK (hK'card ▸ h)
    · exact hpN (hN'card ▸ (h.trans hidxdvd))
  exact hpM (m.dvd_card_M_of_mem_sigma hp)

theorem six29 (h625 : m.C625) (h626 : m.C626) (h628b : m.C628b) : m.C629 := by
  have hcyc := m.sylow_cyclic_of_pRank_eq_one h625 (m.hr.odd_of_ne_two m.d.odd)
  refine ⟨m.Kbar_isSimple hcyc, ?_⟩
  by_contra hne
  push Not at hne
  exact m.false_of_Kbar_comm hcyc h626 h628b hne

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
