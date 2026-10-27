module

import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Plane
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsL62

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem eq_zero_or_forall_ne_zero_of_signed_perm (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) (hT : ∃ u : Fin 3 → ZMod 3, (fun i => ε i * u (σ i)) ≠ u)
    (h3 : ∀ u : Fin 3 → ZMod 3,
      (fun i => ε i * (ε (σ i) * (ε (σ (σ i)) * u (σ (σ (σ i)))))) = u)
    {v : Fin 3 → ZMod 3} (hv : (fun i => ε i * v (σ i)) = v) : v = 0 ∨ ∀ i, v i ≠ 0 := by
  revert σ ε hε hT h3 v hv
  decide +kernel

namespace Case811Sylow

variable {c : Ctx82E3 D} {h : Case811Sylow c}

private theorem P_le_normalizer_A : h.P ≤ Subgroup.normalizer (h.A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hB : h.A.map (MulAut.conj g).toMonoidHom ≤ h.P := by
    rintro _ ⟨a, ha, rfl⟩
    exact h.P.mul_mem (h.P.mul_mem hg (h.A_le ha)) (h.P.inv_mem hg)
  have hBab : IsElemAbelian 3 (h.A.map (MulAut.conj g).toMonoidHom) :=
    h.elemAbelian.map (MulAut.conj g).toMonoidHom
  have hBcard : Nat.card (h.A.map (MulAut.conj g).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_A]
  exact h.unique _ hB hBab hBcard

private theorem pow_three_mem_A_of_mem_P (hP : Nat.card h.P = 81) {t : G} (htP : t ∈ h.P) :
    t ^ 3 ∈ h.A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let N : Subgroup ↥h.P := h.A.subgroupOf h.P
  haveI : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.A_le).mpr P_le_normalizer_A
  have hcardN : Nat.card ↥N = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le).toEquiv, h.card_A]
  have hcardP : Nat.card ↥h.P = 81 := by simpa using hP
  have hcardQ : Nat.card (↥h.P ⧸ N) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcardP, hcardN] at h
    omega
  let x : ↥h.P := ⟨t, htP⟩
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 3 := by
    have := orderOf_dvd_natCard (QuotientGroup.mk' N x)
    rwa [hcardQ] at this
  have hone : (QuotientGroup.mk' N x) ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hx3N : x ^ 3 ∈ N := (QuotientGroup.eq_one_iff (x ^ 3)).mp (by
    change (QuotientGroup.mk' N x) ^ 3 = 1
    exact hone)
  have hx3 : ((x ^ 3 : ↥h.P) : G) ∈ h.A := Subgroup.mem_subgroupOf.mp hx3N
  simpa [x] using hx3

private theorem mem_Abar_of_mem_centralizer (hCA : K7L6TwoCentA)
    (hlie : IsLie811 c.Lbar .l6 2 1) {y : c.Lbar}
    (hy : y ∈ Subgroup.centralizer (h.Abar : Set c.Lbar)) : y ∈ h.Abar := by
  have hcardC : Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) = 27 :=
    hCA c.Lbar hlie h.Abar h.isElemAbelian_Abar h.card_Abar
  have hAbar_le : h.Abar ≤ Subgroup.centralizer (h.Abar : Set c.Lbar) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    simpa using congrArg Subtype.val
      ((h.isElemAbelian_Abar.1.is_comm).comm (⟨b, hb⟩ : h.Abar) (⟨a, ha⟩ : h.Abar))
  have heq : Subgroup.centralizer (h.Abar : Set c.Lbar) = h.Abar :=
    (Subgroup.eq_of_le_of_card_ge hAbar_le (by rw [hcardC, h.card_Abar])).symm
  exact heq.le hy

private theorem mem_A_of_mem_Abar_of_mem_P (hP : Nat.card h.P = 81) {t : G} (htP : t ∈ h.P)
    (htbar : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩ ∈ h.Abar) :
    t ∈ h.A := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let tL : ↥c.L := ⟨t, h.P_le_L htP⟩
  obtain ⟨xL, hxL, hxeq⟩ := Subgroup.mem_map.mp htbar
  have haA : (xL : G) ∈ h.A := Subgroup.mem_subgroupOf.mp hxL
  have hπeq : π xL = π tL := by simpa [N, π, tL] using hxeq
  have hNmem : xL⁻¹ * tL ∈ N := QuotientGroup.eq.mp hπeq
  have hPmem : xL⁻¹ * tL ∈ h.P.subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]
    change (xL : G)⁻¹ * t ∈ h.P
    exact h.P.mul_mem (h.P.inv_mem (h.A_le haA)) htP
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hPsubCard : Nat.card ↥(h.P.subgroupOf c.L) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.P_le_L).toEquiv, hP]
  have hdisj : Disjoint (h.P.subgroupOf c.L) N := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hPsubCard, hn]
    exact (by norm_num : Nat.Coprime 81 2).pow_right n
  have hx1 : xL⁻¹ * tL = 1 := by
    have hmem : xL⁻¹ * tL ∈ h.P.subgroupOf c.L ⊓ N := ⟨hPmem, hNmem⟩
    rw [hdisj.eq_bot] at hmem
    simpa using hmem
  have ht_eq : t = (xL : G) := by
    have h := congrArg (fun z : ↥c.L => (z : G)) hx1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h
    calc t = (xL : G) * ((xL : G)⁻¹ * t) := by group
      _ = (xL : G) := by rw [h]; group
  rw [ht_eq]
  exact haA

private theorem card_inf_normalizer_eq_eighty_one (hP : Nat.card h.P = 81)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) {S : Subgroup G}
    (hS : IsPGroup 3 S) (hAS : h.A ≤ S)
    (hlt : h.A < S ⊓ Subgroup.normalizer (h.A : Set G)) :
    Nat.card ↥(S ⊓ Subgroup.normalizer (h.A : Set G)) = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q : Subgroup G := S ⊓ Subgroup.normalizer (h.A : Set G)
  have hQ3 : IsPGroup 3 Q := hS.to_inf_left
  have hQM : Q ≤ D.M := (inf_le_right : Q ≤ Subgroup.normalizer (h.A : Set G)).trans hNA
  obtain ⟨R, hR, hQR⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge
    (p := 3) hQM hQ3
  have hRcard : Nat.card R = 81 := by
    have hReq : Nat.card R = 3 ^ (Nat.card ↥D.M).factorization 3 :=
      CFSG.ABGLocalTools.IsSylowOf.card_eq hR
    have hPeq : Nat.card h.P = 3 ^ (Nat.card ↥D.M).factorization 3 :=
      CFSG.ABGLocalTools.IsSylowOf.card_eq h.sylow
    rw [hReq, ← hPeq, hP]
  have hQlt : 27 < Nat.card Q := by
    have hcard := Subgroup.card_lt_of_lt hlt
    rwa [h.card_A] at hcard
  have hQle : Nat.card Q ≤ 81 := by
    calc Nat.card Q ≤ Nat.card R := Subgroup.card_le_of_le hQR
      _ = 81 := hRcard
  obtain ⟨n, hn⟩ := hQ3.exists_card_eq
  rw [hn] at hQlt hQle ⊢
  have hle4 : n ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ n := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 3) h5
    norm_num at hpow
    omega
  have hge4 : 4 ≤ n := by
    by_contra h
    have h3le : n ≤ 3 := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 3) h3le
    norm_num at hpow
    omega
  interval_cases n <;> norm_num at hQlt hQle ⊢

end Case811Sylow

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem tbar_mem_normalizer_Abar {t : G} (htP : t ∈ h.P) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩ ∈
      Subgroup.normalizer (h.Abar : Set c.Lbar) := by
  classical
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let tL : ↥c.L := ⟨t, h.P_le_L htP⟩
  haveI : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hN2 Fact.out (by norm_num)
  have hAsubP : IsPGroup 3 (h.A.subgroupOf c.L) :=
    h.elemAbelian.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.A_le_L).symm
  have ht_norm_sub : tL ∈ Subgroup.normalizer (h.A.subgroupOf c.L : Set ↥c.L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.A_le_L]
    exact P_le_normalizer_A htP
  have hEqmap : (Subgroup.normalizer (h.A.subgroupOf c.L : Set ↥c.L)).map π =
      Subgroup.normalizer (h.Abar : Set c.Lbar) := by
    simpa [N, π] using
      (CFSG.GroupTheory.normal_coprime_quotient_normalizer (G := ↥c.L) 3 N hN3
        (h.A.subgroupOf c.L) hAsubP)
  have hmem : π tL ∈ (Subgroup.normalizer (h.A.subgroupOf c.L : Set ↥c.L)).map π :=
    Subgroup.mem_map_of_mem π ht_norm_sub
  rwa [hEqmap] at hmem

private theorem exists_signed_perm_of_mem_P {t : G} (htP : t ∈ h.P) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ u : Multiplicative (Fin 3 → ZMod 3),
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩ * s.c₀ u *
            (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩)⁻¹ =
          s.c₀ (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd u (σ i)) := by
  obtain ⟨σ, ε, hε, hsig⟩ := s.signed.2.2.1
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩)
    (tbar_mem_normalizer_Abar htP)
  exact ⟨σ, ε, hε, hsig⟩

private theorem tbar_pow_three_centralizes (hP : Nat.card h.P = 81) {t : G} (htP : t ∈ h.P) :
    ∀ u : Multiplicative (Fin 3 → ZMod 3),
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩) ^ 3 * s.c₀ u *
          ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩) ^ 3)⁻¹ =
        s.c₀ u := by
  classical
  let tbar : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩
  have ht3A : t ^ 3 ∈ h.A := pow_three_mem_A_of_mem_P hP htP
  have htbar3Abar : tbar ^ 3 ∈ h.Abar := by
    have h1 : tbar ^ 3 =
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t ^ 3, h.A_le_L ht3A⟩ := by
      change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩) ^ 3 =
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t ^ 3, h.A_le_L ht3A⟩
      rw [← map_pow]
      congr 1
    rw [h1]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht3A)
  intro u
  have hc0Abar : s.c₀ u ∈ h.Abar := by
    rw [← s.signed.2.1]
    exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hcomm := congrArg Subtype.val
    ((h.isElemAbelian_Abar.1.is_comm).comm (⟨tbar ^ 3, htbar3Abar⟩ : h.Abar)
      (⟨s.c₀ u, hc0Abar⟩ : h.Abar))
  have hcomm' : tbar ^ 3 * s.c₀ u = s.c₀ u * tbar ^ 3 := by simpa using hcomm
  have hfin : tbar ^ 3 * s.c₀ u * (tbar ^ 3)⁻¹ = s.c₀ u := by rw [hcomm']; group
  simpa [tbar] using hfin

private theorem signed_perm_pow_three (hP : Nat.card h.P = 81) {t : G} (htP : t ∈ h.P)
    {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod 3}
    (hsig : ∀ u : Multiplicative (Fin 3 → ZMod 3),
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩ * s.c₀ u *
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩)⁻¹ =
        s.c₀ (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd u (σ i))) :
    ∀ w : Fin 3 → ZMod 3,
      (fun i => ε i * (ε (σ i) * (ε (σ (σ i)) * w (σ (σ (σ i)))))) = w := by
  classical
  let tbar : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩
  let Tf : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) := fun u i => ε i * u (σ i)
  let T : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
    fun u => Multiplicative.ofAdd (Tf (Multiplicative.toAdd u))
  have hTact : ∀ u, tbar * s.c₀ u * tbar⁻¹ = s.c₀ (T u) := by
    intro u
    simpa [T, Tf, tbar] using hsig u
  have hcomm3 : ∀ u, tbar ^ 3 * s.c₀ u * (tbar ^ 3)⁻¹ = s.c₀ u := by
    intro u
    simpa [tbar] using tbar_pow_three_centralizes (s := s) hP htP u
  intro w
  have hpow3 : tbar ^ 3 = tbar * tbar * tbar := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  have h1 : tbar ^ 3 * s.c₀ (Multiplicative.ofAdd w) * (tbar ^ 3)⁻¹ =
      s.c₀ (T (T (T (Multiplicative.ofAdd w)))) := by
    rw [hpow3]
    calc
      (tbar * tbar * tbar) * s.c₀ (Multiplicative.ofAdd w) * (tbar * tbar * tbar)⁻¹
          = tbar * (tbar * (tbar * s.c₀ (Multiplicative.ofAdd w) * tbar⁻¹) * tbar⁻¹) *
              tbar⁻¹ := by group
      _ = tbar * (tbar * s.c₀ (T (Multiplicative.ofAdd w)) * tbar⁻¹) * tbar⁻¹ := by
          rw [hTact (Multiplicative.ofAdd w)]
      _ = tbar * s.c₀ (T (T (Multiplicative.ofAdd w))) * tbar⁻¹ := by
          rw [hTact (T (Multiplicative.ofAdd w))]
      _ = s.c₀ (T (T (T (Multiplicative.ofAdd w)))) :=
          hTact (T (T (Multiplicative.ofAdd w)))
  rw [hcomm3 (Multiplicative.ofAdd w)] at h1
  have h2 : Multiplicative.ofAdd w = Multiplicative.ofAdd (Tf (Tf (Tf w))) := by
    have := s.signed.1 h1
    simpa [T, Tf] using this
  have h3 : Tf (Tf (Tf w)) = w := (Multiplicative.ofAdd.injective h2).symm
  simpa [Tf] using h3

private theorem signed_perm_ne_one (hCA : K7L6TwoCentA) (hlie : IsLie811 c.Lbar .l6 2 1)
    (hP : Nat.card h.P = 81) {t : G} (htP : t ∈ h.P) (htA : t ∉ h.A)
    {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod 3}
    (hsig : ∀ u : Multiplicative (Fin 3 → ZMod 3),
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩ * s.c₀ u *
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩)⁻¹ =
        s.c₀ (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd u (σ i))) :
    ∃ u : Fin 3 → ZMod 3, (fun i => ε i * u (σ i)) ≠ u := by
  classical
  let tbar : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩
  let Tf : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) := fun u i => ε i * u (σ i)
  let T : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
    fun u => Multiplicative.ofAdd (Tf (Multiplicative.toAdd u))
  have hTact : ∀ u, tbar * s.c₀ u * tbar⁻¹ = s.c₀ (T u) := by
    intro u
    simpa [T, Tf, tbar] using hsig u
  by_contra hT1
  simp only [not_exists, not_not] at hT1
  have hcent : tbar ∈ Subgroup.centralizer (h.Abar : Set c.Lbar) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← s.signed.2.1] at hy
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
    have hTu : Tf (Multiplicative.toAdd u) = Multiplicative.toAdd u :=
      hT1 (Multiplicative.toAdd u)
    have h2 : T u = u := by simp [T, hTu]
    have h1 := hTact u
    rw [h2] at h1
    rw [← hu]
    calc s.c₀ u * tbar = (tbar * s.c₀ u * tbar⁻¹) * tbar := by rw [h1]
      _ = tbar * s.c₀ u := by group
  have htbarAbar : tbar ∈ h.Abar :=
    mem_Abar_of_mem_centralizer hCA hlie hcent
  have htA' : t ∈ h.A :=
    mem_A_of_mem_Abar_of_mem_P hP htP (by simpa [tbar] using htbarAbar)
  exact htA htA'

theorem forall_ne_zero_of_commute_of_l62 (hCA : K7L6TwoCentA) (hlie : IsLie811 c.Lbar .l6 2 1)
    (hP : Nat.card h.P = 81) {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    (hc : ∀ g ∈ h.P, g * s.pt v = s.pt v * g) : ∀ i, v i ≠ 0 := by
  classical
  have hAP : h.A < h.P := by
    refine lt_of_le_of_ne h.A_le ?_
    intro hEq
    have hcard := congrArg (fun K : Subgroup G => Nat.card K) hEq
    rw [h.card_A, hP] at hcard
    norm_num at hcard
  obtain ⟨t, htP, htA⟩ := SetLike.exists_of_lt hAP
  obtain ⟨σ, ε, hε, hsig⟩ := s.exists_signed_perm_of_mem_P htP
  let tbar : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨t, h.P_le_L htP⟩
  let Tf : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) := fun u i => ε i * u (σ i)
  have htL_eq : (⟨t, h.P_le_L htP⟩ : ↥c.L) * s.a (Multiplicative.ofAdd v) *
      (⟨t, h.P_le_L htP⟩ : ↥c.L)⁻¹ = s.a (Multiplicative.ofAdd v) := by
    apply Subtype.ext
    change t * s.pt v * t⁻¹ = s.pt v
    rw [hc t htP]
    group
  have hstep : tbar * s.c₀ (Multiplicative.ofAdd v) * tbar⁻¹ =
      s.c₀ (Multiplicative.ofAdd v) := by
    have h := congrArg (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) htL_eq
    rw [← s.apply (Multiplicative.ofAdd v)]
    simpa [tbar, map_mul, map_inv] using h
  have hfix : Tf v = v := by
    have h := hsig (Multiplicative.ofAdd v)
    rw [hstep] at h
    have := s.signed.1 h
    exact (Multiplicative.ofAdd.injective (by simpa [tbar, Tf] using this)).symm
  have h3 := s.signed_perm_pow_three hP htP hsig
  have hTne := s.signed_perm_ne_one hCA hlie hP htP htA hsig
  have hfin := eq_zero_or_forall_ne_zero_of_signed_perm σ ε hε hTne h3 hfix
  rcases hfin with h0 | h
  · exact absurd h0 hv
  · exact h

private theorem exists_conj_maps_of_l62 (hP : Nat.card h.P = 81)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) {S : Subgroup G}
    (hS : IsPGroup 3 S) (hAS : h.A ≤ S)
    (hlt : h.A < S ⊓ Subgroup.normalizer (h.A : Set G)) :
    ∃ k ∈ D.M,
      (S ⊓ Subgroup.normalizer (h.A : Set G)).map (MulAut.conj k⁻¹).toMonoidHom = h.P ∧
        h.A.map (MulAut.conj k⁻¹).toMonoidHom = h.A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q : Subgroup G := S ⊓ Subgroup.normalizer (h.A : Set G)
  have hQM : Q ≤ D.M := (inf_le_right : Q ≤ Subgroup.normalizer (h.A : Set G)).trans hNA
  have hQ3 : IsPGroup 3 Q := hS.to_inf_left
  have hQcard : Nat.card Q = 81 := card_inf_normalizer_eq_eighty_one hP hNA hS hAS hlt
  obtain ⟨k, hkM, hk⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf
    (p := 3) h.sylow hQM hQ3
  have hQmap : Q.map (MulAut.conj k⁻¹).toMonoidHom = h.P := by
    apply Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply] using hk q hq
    · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hQcard, hP]
  refine ⟨k, hkM, hQmap, ?_⟩
  refine h.unique (h.A.map (MulAut.conj k⁻¹).toMonoidHom) ?_ ?_ ?_
  · exact (Subgroup.map_mono (le_inf hAS Subgroup.le_normalizer)).trans (le_of_eq hQmap)
  · exact h.elemAbelian.map _
  · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, h.card_A]

private theorem commute_conj_of_mem_centralizer {x : G} {S Q P : Subgroup G} {k : G}
    (hSx : S ≤ Subgroup.centralizer ({x} : Set G)) (hQS : Q ≤ S)
    (hQmap : Q.map (MulAut.conj k⁻¹).toMonoidHom = P) :
    ∀ p ∈ P, p * (k⁻¹ * x * k) = (k⁻¹ * x * k) * p := by
  intro p hp
  have hpQ : p ∈ Q.map (MulAut.conj k⁻¹).toMonoidHom := by rw [hQmap]; exact hp
  obtain ⟨q, hqQ, hqeq⟩ := Subgroup.mem_map.mp hpQ
  have hqS : q ∈ S := hQS hqQ
  have hqx : x * q = q * x :=
    (Subgroup.mem_centralizer_iff.mp (hSx hqS)) x (Set.mem_singleton x)
  have hqeq' : k⁻¹ * q * k = p := by simpa [MulAut.conj_apply] using hqeq
  calc p * (k⁻¹ * x * k) = (k⁻¹ * q * k) * (k⁻¹ * x * k) := by rw [hqeq']
    _ = k⁻¹ * (q * x) * k := by group
    _ = k⁻¹ * (x * q) * k := by rw [hqx]
    _ = (k⁻¹ * x * k) * (k⁻¹ * q * k) := by group
    _ = (k⁻¹ * x * k) * p := by rw [hqeq']

theorem good_of_lt_normalizer_of_l62 (hCA : K7L6TwoCentA) (hlie : IsLie811 c.Lbar .l6 2 1)
    (hP : Nat.card h.P = 81)
    (hgood : ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) → GoodPoint D.M (s.pt v))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) {x : G} (hx : x ∈ h.A) (hx1 : x ≠ 1)
    {S : Subgroup G} (hS : IsPGroup 3 S) (hAS : h.A ≤ S)
    (hSx : S ≤ Subgroup.centralizer ({x} : Set G))
    (hlt : h.A < S ⊓ Subgroup.normalizer (h.A : Set G)) : GoodPoint D.M x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q : Subgroup G := S ⊓ Subgroup.normalizer (h.A : Set G)
  obtain ⟨k, hkM, hQmap, hA_map⟩ := exists_conj_maps_of_l62 hP hNA hS hAS hlt
  let x' : G := k⁻¹ * x * k
  have hx'A : x' ∈ h.A := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hx
    rw [hA_map] at hmem
    simpa [x', MulAut.conj_apply] using hmem
  have hx'comm : ∀ p ∈ h.P, p * x' = x' * p :=
    commute_conj_of_mem_centralizer (Q := Q) hSx (show Q ≤ S from inf_le_left) hQmap
  obtain ⟨w, hw⟩ := s.exists_pt_of_mem hx'A
  have hw0 : w ≠ 0 := by
    intro hw0
    have hx'1 : x' = 1 := by rw [← hw, hw0, s.pt_zero]
    have hx1' : x = 1 := by
      calc x = k * x' * k⁻¹ := by
            rw [show x' = k⁻¹ * x * k from rfl]
            group
        _ = k * 1 * k⁻¹ := by rw [hx'1]
        _ = 1 := by group
    exact hx1 hx1'
  have hc : ∀ g ∈ h.P, g * s.pt w = s.pt w * g := by
    intro g hg
    rw [hw]
    exact hx'comm g hg
  have hwne : ∀ i, w i ≠ 0 := s.forall_ne_zero_of_commute_of_l62 hCA hlie hP hw0 hc
  have hgw : GoodPoint D.M (s.pt w) := hgood w hwne
  have hx_eq : k * s.pt w * k⁻¹ = x := by
    rw [hw]
    change k * (k⁻¹ * x * k) * k⁻¹ = x
    group
  have := hgw.conj hkM
  rwa [hx_eq] at this

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
