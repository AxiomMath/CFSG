module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB4G

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU CFSG.Quasithin.H.LU24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.B42Alt6 CFSG.Quasithin.S143
open scoped commutatorElement

theorem le_pCoreOf_mb4 {G : Type*} [Group G] {P K : Subgroup G} (hKP : K ≤ P)
    (hK2 : IsPGroup 2 ↥K) (hn : P ≤ Subgroup.normalizer (K : Set G)) : K ≤ pCoreOf 2 P := by
  have hnorm : (K.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).2 hn
  have hp : IsPGroup 2 ↥(K.subgroupOf P) := hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKP).symm
  have hle : K.subgroupOf P ≤ CFSG.pCore 2 ↥P := le_sSup ⟨hnorm, hp⟩
  have h2 := Subgroup.map_mono (f := P.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hKP] at h2
  exact h2

theorem mem_normalizer_pCoreOf_mb4 {G : Type*} [Group G] {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    n ∈ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
  have h1 : H.map (MulAut.conj n).toMonoidHom = H := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hn x).1 hx
    · intro hy
      refine ⟨n⁻¹ * y * n, ?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
        rwa [inv_inv] at h
      · show n * (n⁻¹ * y * n) * n⁻¹ = y
        group
  have h2 : (pCoreOf 2 H).map (MulAut.conj n).toMonoidHom = pCoreOf 2 H := by
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj n) H, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h2] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h3 : n * y * n⁻¹ = n * x * n⁻¹ := hyx
      simpa using h3
    rwa [this] at hy

theorem mem_centSub_of_comm_mb4
    (hρ : (alternatingGroup (Fin 6)).map (rhoOf usTheta) = autSub (imgCd sxP0) US)
    (hP : imgCd sxP0 ≤ stabSub US) {z : MulAut W11} (hz : z ∈ imgCd sxP0)
    (hc : ∀ g ∈ imgCd sxP0, ⁅z, g⁆ ∈ centSub US) : z ∈ centSub US := by
  have hzs : z ∈ stabSub US := hP hz
  have hφz : resHom US ⟨z, hzs⟩ ∈ autSub (imgCd sxP0) US :=
    mem_autSub.2 ⟨⟨z, hzs⟩, hz, rfl⟩
  rw [← hρ] at hφz
  obtain ⟨σ, hσ, hσz⟩ := Subgroup.mem_map.1 hφz
  have hcomm : ∀ τ ∈ alternatingGroup (Fin 6), σ * τ = τ * σ := by
    intro τ hτ
    have hτ' : rhoOf usTheta τ ∈ autSub (imgCd sxP0) US := by
      rw [← hρ]; exact Subgroup.mem_map_of_mem _ hτ
    obtain ⟨g, hg, hgτ⟩ := mem_autSub.1 hτ'
    apply rhoOf_injective usTheta
    rw [map_mul, map_mul, hσz, ← hgτ]
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show z (g.1 u) = g.1 (z u)
    have hgs : g.1 ∈ stabSub US := g.2
    have h1 : g.1 (z u) ∈ US := (hgs (z u)).2 ((hzs u).2 u.2)
    have h2 : (⁅z, g.1⁆ : MulAut W11) (g.1 (z u)) = g.1 (z u) := hc g.1 hg (g.1 (z u)) h1
    have h3 : (⁅z, g.1⁆ : MulAut W11) (g.1 (z u)) = z (g.1 u) := by
      show z (g.1 (z⁻¹ (g.1⁻¹ (g.1 (z u))))) = z (g.1 u)
      have e1 : g.1⁻¹ (g.1 (z u)) = z u := g.1.symm_apply_apply (z u)
      have e2 : z⁻¹ (z u) = u := z.symm_apply_apply u
      rw [e1, e2]
    rw [h3] at h2
    exact h2
  have hcen : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 6))) ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
    Subgroup.mem_center_iff.2 fun τ => Subtype.ext (hcomm τ τ.2).symm
  rw [alternatingGroup.center_eq_bot (by simp)] at hcen
  have hσ1 : σ = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
  rw [hσ1, map_one] at hσz
  intro u hu
  have := congrArg (fun φ : MulAut ↥US => ((φ ⟨u, hu⟩ : ↥US) : W11)) hσz
  exact this.symm

theorem rhoCd_comm_mb4 {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) (hτ : τ ∈ AutPerm)
    (h : ⁅σ, τ⁆ ∈ AutPerm) : rhoCd h = ⁅rhoCd hσ, rhoCd hτ⁆ := by
  unfold rhoCd
  rw [← map_commutatorElement]
  rfl

theorem card_imgCd_KS_mb4
    (hS : Nat.card ↥((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) ≤ 138240)
    (hρ : (alternatingGroup (Fin 6)).map (rhoOf usTheta) = autSub (imgCd sxP0) US)
    (hCK : Nat.card ↥(imgCd sxP0 ⊓ centSub US) = 3 * Nat.card ↥(imgCd sxKS)) :
    Nat.card ↥(imgCd sxKS) = 64 := by
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hP0 : Nat.card ↥(imgCd sxP0) = Nat.card ↥sxP0 := card_imgCd sxP0_le
  have hle : Nat.card ↥sxP0 ≤ 69120 := by
    have h1 := two_mul_card_P0_le
    have h2 : Nat.card ↥sxGen ≤ Nat.card ↥stabUSP := Subgroup.card_le_of_le sxGen_le
    have h3 := card_stabUSP
    omega
  have hcardA : Nat.card ↥((alternatingGroup (Fin 6)).map (rhoOf usTheta)) = 360 :=
    (Subgroup.card_map_of_injective (rhoOf_injective usTheta)).trans card_alt6
  have hA' : Nat.card ↥(autSub (imgCd sxP0) US) = 360 :=
    (congrArg (fun K : Subgroup (MulAut ↥US) => Nat.card ↥K) hρ).symm.trans hcardA
  have hA : Nat.card ↥(autSub (imgCd sxP0) US) * Nat.card ↥(imgCd sxP0 ⊓ centSub US) =
      Nat.card ↥(imgCd sxP0) := card_autSub_mul imgCd_P0_le_stab
  rw [hA'] at hA
  have h64 := le_card_imgCd_KS
  omega

def commModK {G : Type*} [Group G] (K : Subgroup G) (z : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅z, g⁆ ∈ K}
  one_mem' := ⟨Subgroup.one_mem _, by simpa [commutatorElement_def] using K.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have h : ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h]
    exact K.mul_mem hza ((Subgroup.mem_normalizer_iff.1 ha _).1 hzb)
  inv_mem' := by
    rintro a ⟨ha, hza⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    have h : ⁅z, a⁻¹⁆ = a⁻¹ * ⁅z, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [h]
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) _).1 (K.inv_mem hza)
    rwa [inv_inv] at this

theorem sxZ_comm_g2_mb4 : sxZ * sxG2 = sxG2 * sxZ := by
  simp only [sxZ, wPerm, List.getD_cons_succ, List.getD_cons_zero]
  group

theorem mb4_std_b_of
    (hcomm : ⁅sxZ, sxG1⁆ ∈ sxKS)
    (hb4 : ∃ b ∈ maskSub 11 mb3L10, rhoCd sxZ_autPerm b * b⁻¹ ∉ US) :
    ∃ z ∈ imgCd sxP0, z ^ 3 = 1 ∧ (∀ g ∈ imgCd sxP0, ⁅z, g⁆ ∈ pCoreOf 2 (imgCd sxP0)) ∧
      ∃ b ∈ maskSub 11 mb3L10, z b * b⁻¹ ∉ US := by
  have hS := card_stab_US_le
  obtain ⟨-, -, -, hKP, hKn, hK2, -, -⟩ := lu_code_std hS
  have hzP : rhoCd sxZ_autPerm ∈ imgCd sxP0 := rhoCd_mem_imgCd sxZ_autPerm sxZ_mem_P0
  have hz3 : rhoCd sxZ_autPerm ^ 3 = 1 := by
    have : (⟨sxZ, sxZ_autPerm⟩ : ↥AutPerm) ^ 3 = 1 := Subtype.ext (by simpa using sxZ_cube)
    show rhoC11 AutPerm le_rfl _ ^ 3 = 1
    rw [← map_pow, this, map_one]
  have hgen : ({sxG1, sxG2} : Set (Equiv.Perm (Fin 24))) ⊆ AutPerm := by
    rintro _ (rfl | rfl)
    · exact sxG1_mem
    · exact sxG2_mem
  have hmem : imgCd sxP0 ≤ commModK (imgCd sxKS) (rhoCd sxZ_autPerm) := by
    refine imgCd_closure_le (S := {sxG1, sxG2}) hgen ?_
    rintro _ (rfl | rfl)
    · refine ⟨imgCd_le_normalizer sxP0_le_normalizer (rhoCd_mem_imgCd sxG1_mem sxG1_mem_P0), ?_⟩
      have hc : ⁅sxZ, sxG1⁆ ∈ AutPerm := sxP0_le (sxKS_le_P0 hcomm)
      rw [← rhoCd_comm_mb4 sxZ_autPerm sxG1_mem hc]
      exact rhoCd_mem_imgCd hc hcomm
    · refine ⟨imgCd_le_normalizer sxP0_le_normalizer (rhoCd_mem_imgCd sxG2_mem sxG2_mem_P0), ?_⟩
      have h1 : ⁅sxZ, sxG2⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]; exact sxZ_comm_g2_mb4
      have hc : ⁅sxZ, sxG2⁆ ∈ AutPerm := h1 ▸ AutPerm.one_mem
      rw [← rhoCd_comm_mb4 sxZ_autPerm sxG2_mem hc]
      exact rhoCd_mem_imgCd hc (h1 ▸ sxKS.one_mem)
  exact ⟨_, hzP, hz3, fun g hg => le_pCoreOf_mb4 hKP hK2 hKn (hmem hg).2, hb4⟩

theorem rhoCd_conj_mb4 {g t : Equiv.Perm (Fin 24)} (hg : g ∈ AutPerm) (ht : t ∈ AutPerm)
    (h : g * t * g⁻¹ ∈ AutPerm) : rhoCd h = rhoCd hg * rhoCd ht * (rhoCd hg)⁻¹ := by
  unfold rhoCd
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem mb4_std_c_of
    (hD : ∃ (t0 g0 : Equiv.Perm (Fin 24)) (ht0 : t0 ∈ AutPerm) (hg0 : g0 ∈ AutPerm),
      t0 * t0 = 1 ∧ rhoCd ht0 ∈ stabSub US ∧ t0 * sxZ * t0⁻¹ * sxZ ∈ sxKS ∧
        g0 * t0 * g0⁻¹ ∈ sxKS)
    (hcentP : (rhoC11 AutPerm le_rfl).range ⊓ centSub US ≤ imgCd sxP0)
    (Xs : Subgroup (MulAut W11)) (hXH : Xs ≤ (rhoC11 AutPerm le_rfl).range)
    (hX2 : IsPGroup 2 ↥Xs) (hXc : Nat.card ↥Xs = 2 ^ 6) (hU : fixV Xs = US) :
    ∀ S : Subgroup (MulAut W11), S ≤ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US →
      IsPGroup 2 ↥S → ¬ 2 ∣ (S.subgroupOf ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US)).index →
      ∃ t ∈ S, t ^ 2 = 1 ∧ (∃ g ∈ (rhoC11 AutPerm le_rfl).range, g * t * g⁻¹ ∈ Xs) ∧
        ∀ z ∈ imgCd sxP0, (∀ g ∈ imgCd sxP0, ⁅z, g⁆ ∈ pCoreOf 2 (imgCd sxP0)) →
          t * z * t⁻¹ * z ∈ pCoreOf 2 (imgCd sxP0) := by
  have hS0 := card_stab_US_le
  obtain ⟨hPS, hρ, -, hKP, hKn, hK2, hKC, hCK⟩ := lu_code_std hS0
  obtain ⟨t0, g0, ht0, hg0, ht0sq, ht0stab, ht0inv, hconj⟩ := hD
  have : Finite (MulAut W11) := finite_mulAut_z (V := W11)
  have hOs : pCoreOf 2 (imgCd sxP0) = imgCd sxKS :=
    le_antisymm (pCoreOf_sxP0_le hS0) (le_pCoreOf_mb4 hKP hK2 hKn)
  have hK64 := card_imgCd_KS_mb4 hS0 hρ hCK
  have hPN : imgCd sxP0 ≤ stabSub US := imgCd_P0_le_stab
  have hPS' : perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) = imgCd sxP0 := hPS
  have e1 : pCoreOf 2 (perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US)) =
      imgCd sxKS := (congrArg (pCoreOf 2) hPS').trans hOs
  have hKC' : imgCd sxKS ≤ imgCd sxP0 ⊓ centSub US := fun k hk => ⟨hKP hk, hKC hk⟩
  have hKn' : ∀ c ∈ imgCd sxP0 ⊓ centSub US, ∀ k ∈ imgCd sxKS, c * k * c⁻¹ ∈ imgCd sxKS := by
    intro c hc k hk
    exact (Subgroup.mem_normalizer_iff.1 (hKn hc.1) k).1 hk
  have hXC : Xs ≤ imgCd sxP0 ⊓ centSub US := by
    intro x hx
    refine ⟨hcentP ⟨hXH hx, ?_⟩, ?_⟩ <;>
    · intro u hu
      exact (mem_fixV.1 (hU ▸ hu)) x hx
  have hXK : Xs = imgCd sxKS :=
    eq_of_le_of_isPGroup_mb4 (C := imgCd sxP0 ⊓ centSub US) hKC' hKn' hCK hXC hX2
      (by rw [hXc, hK64]; norm_num)
  have hNsP : ∀ n ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US,
      n ∈ Subgroup.normalizer (imgCd sxP0 : Set (MulAut W11)) := by
    intro n hn
    have h : n ∈ Subgroup.normalizer
        (perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) : Set (MulAut W11)) :=
      normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hn)
    rwa [hPS'] at h
  have hNsK : ∀ n ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US,
      n ∈ Subgroup.normalizer (imgCd sxKS : Set (MulAut W11)) := by
    intro n hn
    rw [← hOs]
    exact mem_normalizer_pCoreOf_mb4 (hNsP n hn)
  have hCn : ∀ n ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US, ∀ c ∈ imgCd sxP0 ⊓ centSub US,
      n * c * n⁻¹ ∈ imgCd sxP0 ⊓ centSub US := by
    intro n hn c hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hNsP n hn) c).1 hc.1, ?_⟩
    intro u hu
    have hn' : ∀ w, n⁻¹ w ∈ US ↔ w ∈ US := Subgroup.inv_mem _ hn.2
    show n (c (n⁻¹ u)) = u
    have h1 : c (n⁻¹ u) = n⁻¹ u := hc.2 (n⁻¹ u) ((hn' u).2 hu)
    calc n (c (n⁻¹ u)) = n (n⁻¹ u) := congrArg n h1
      _ = u := n.apply_symm_apply u
  have ht0sq' : rhoCd ht0 * rhoCd ht0 = 1 := by
    have : (⟨t0, ht0⟩ : ↥AutPerm) * ⟨t0, ht0⟩ = 1 := Subtype.ext ht0sq
    show rhoC11 AutPerm le_rfl ⟨t0, ht0⟩ * rhoC11 AutPerm le_rfl ⟨t0, ht0⟩ = 1
    rw [← map_mul, this, map_one]
  have ht0N : rhoCd ht0 ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US :=
    ⟨⟨⟨t0, ht0⟩, rfl⟩, ht0stab⟩
  have hz3 : rhoCd sxZ_autPerm ^ 3 = 1 := by
    have : (⟨sxZ, sxZ_autPerm⟩ : ↥AutPerm) ^ 3 = 1 := Subtype.ext (by simpa using sxZ_cube)
    show rhoC11 AutPerm le_rfl _ ^ 3 = 1
    rw [← map_pow, this, map_one]
  have hzK : rhoCd sxZ_autPerm ∉ imgCd sxKS := by
    intro h
    obtain ⟨k, hk⟩ := isPGroup_imgCd_KS ⟨_, h⟩
    have h1 : orderOf (rhoCd sxZ_autPerm) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [orderOf_rho_sxZ] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hinvZ : rhoCd ht0 * rhoCd sxZ_autPerm * (rhoCd ht0)⁻¹ * rhoCd sxZ_autPerm ∈ imgCd sxKS := by
    have hm : t0 * sxZ * t0⁻¹ * sxZ ∈ AutPerm := sxP0_le (sxKS_le_P0 ht0inv)
    have h1 := rhoCd_mem_imgCd hm ht0inv
    have h2 : rhoCd hm = rhoCd ht0 * rhoCd sxZ_autPerm * (rhoCd ht0)⁻¹ * rhoCd sxZ_autPerm := by
      unfold rhoCd
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rwa [h2] at h1
  intro S hSN hSp hidx
  obtain ⟨n, hn, hnS⟩ := exists_conj_mem_sylow_mb4 (N := (rhoC11 AutPerm le_rfl).range ⊓ stabSub US)
    (S := S) (t := rhoCd ht0) ht0N (by rw [pow_two]; exact ht0sq') hSN hSp hidx
  refine ⟨n * rhoCd ht0 * n⁻¹, hnS, ?_, ?_, ?_⟩
  · have h : (n * rhoCd ht0 * n⁻¹) ^ 2 = n * (rhoCd ht0 * rhoCd ht0) * n⁻¹ := by
      rw [pow_two]; group
    rw [h, ht0sq']; group
  · refine ⟨rhoCd hg0 * n⁻¹, Subgroup.mul_mem _ ⟨⟨g0, hg0⟩, rfl⟩ (Subgroup.inv_mem _ hn.1), ?_⟩
    rw [hXK]
    have heq : (rhoCd hg0 * n⁻¹) * (n * rhoCd ht0 * n⁻¹) * (rhoCd hg0 * n⁻¹)⁻¹ =
        rhoCd hg0 * rhoCd ht0 * (rhoCd hg0)⁻¹ := by group
    rw [heq]
    have hm : g0 * t0 * g0⁻¹ ∈ AutPerm := sxP0_le (sxKS_le_P0 hconj)
    have h1 := rhoCd_mem_imgCd hm hconj
    rwa [rhoCd_conj_mb4 hg0 ht0 hm] at h1
  · intro z hz hzc
    rw [hOs]
    rw [hOs] at hzc
    have hzcent : z ∈ centSub US :=
      mem_centSub_of_comm_mb4 hρ hPN hz (fun g hg => hKC (hzc g hg))
    have hzC : z ∈ imgCd sxP0 ⊓ centSub US := ⟨hz, hzcent⟩
    have hn' : n⁻¹ ∈ (rhoC11 AutPerm le_rfl).range ⊓ stabSub US := Subgroup.inv_mem _ hn
    have hz'C : n⁻¹ * z * n⁻¹⁻¹ ∈ imgCd sxP0 ⊓ centSub US := hCn n⁻¹ hn' z hzC
    have hkey := inv_mod_of_generator_mb4 (C := imgCd sxP0 ⊓ centSub US) (K := imgCd sxKS)
      (t := rhoCd ht0) (z := rhoCd sxZ_autPerm) hKC' hCK hKn'
      (fun k hk => (Subgroup.mem_normalizer_iff.1 (hNsK _ ht0N) k).1 hk)
      (hCn _ ht0N) ⟨rhoCd_mem_imgCd sxZ_autPerm sxZ_mem_P0, sxZ_cent⟩ hz3 hzK hinvZ
      (n⁻¹ * z * n⁻¹⁻¹) hz'C
    have h2 := (Subgroup.mem_normalizer_iff.1 (hNsK n hn) _).1 hkey
    have heq : n * rhoCd ht0 * n⁻¹ * z * (n * rhoCd ht0 * n⁻¹)⁻¹ * z =
        n * (rhoCd ht0 * (n⁻¹ * z * n⁻¹⁻¹) * (rhoCd ht0)⁻¹ * (n⁻¹ * z * n⁻¹⁻¹)) * n⁻¹ := by
      group
    rw [heq]
    exact h2

end CFSG.Quasithin.H13.Mat
