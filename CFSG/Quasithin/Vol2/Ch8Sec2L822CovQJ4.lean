module

public import CFSG.Quasithin.Background.SmithC27RHat6Lin
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovArith
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovG
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQDef
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovZ
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3ListNum
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3LzCore
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1b

public section

namespace CFSG.Quasithin.H13

theorem cover_Q_false_J4 (hJ4 : J4CoverFacts)
    (hcard : Nat.card CFSG.Blueprint.NativeSporadic.J4 = 86775571046077562880)
    (hM22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520)
    {Q : Type} [Group Q] [Finite Q] (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J4))
    {S P Kt B : Subgroup Q} {yt : Q} (hd : CoverQData Q S P Kt B yt) : False := by
  have hQcard : Nat.card Q = 86775571046077562880 := by
    obtain ⟨e⟩ := hQ
    rw [Nat.card_congr e.toEquiv, hcard]
  have hS21 : Nat.card S = 2 ^ 21 :=
    card_two_subgroup_of_card_cv (e := 21) (m := 41377816699065) S hd.S2 hd.Sodd
      (hQcard.trans (by norm_num)) (by norm_num)
  obtain ⟨z₁, -, -, -, -, ha, hb, R, hRg, hRf, ρ, -, hρk, N₀, hN₀n, hN₀i, hN₀hat⟩ :=
    hJ4 Q hQ S hd.S2 hS21
  let C : Subgroup Q := Subgroup.centralizer ({z₁} : Set Q)
  obtain ⟨φ, hφs, hφy0⟩ := hd.Kphi
  have hK5 : 5 ∣ Nat.card Kt := by
    have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card Kt := by
      rw [← Subgroup.index_ker φ, Subgroup.card_mul_index]
    have h2 : Nat.card φ.range = 60 := by
      rw [MonoidHom.range_eq_top.2 hφs, Subgroup.card_top, card_alternatingGroup_five_kz3]
    rw [← h1, h2]
    exact Dvd.dvd.mul_left (by norm_num) _
  have h5P : 5 ∣ Nat.card P := dvd_trans hK5 (Subgroup.card_dvd_of_le hd.KP)
  have hPC : P ≤ C := ha P hd.SP h5P hd.P9
  have hKC : Kt ≤ C := hd.KP.trans hPC
  have hBC : B ≤ C := hb B hd.Bperf hd.SB hd.Bhat
  have hyC : yt ∈ C := hKC hd.ytK
  have hKperfC : ⁅Kt.subgroupOf C, Kt.subgroupOf C⁆ = Kt.subgroupOf C :=
    perfect_comap_subtype_kz3 hKC hd.Kperf
  have hBperfC : ⁅B.subgroupOf C, B.subgroupOf C⁆ = B.subgroupOf C :=
    perfect_comap_subtype_kz3 hBC hd.Bperf
  have hKN : (Kt.subgroupOf C).map ρ ≤ N₀ := by
    apply perfect_le_of_index_two_cv N₀ hN₀i
    rw [← Subgroup.map_commutator, hKperfC]
  have hBN : (B.subgroupOf C).map ρ ≤ N₀ := by
    apply perfect_le_of_index_two_cv N₀ hN₀i
    rw [← Subgroup.map_commutator, hBperfC]
  have hρK : ∀ d : ↥C, d ∈ Kt.subgroupOf C → ρ d ∈ N₀ := fun d hd' =>
    hKN (Subgroup.mem_map_of_mem ρ hd')
  have hBx : ∀ x : ↥B, ρ (Subgroup.inclusion hBC x) ∈ N₀ := fun x =>
    hBN (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 x.2))
  let ρB0 : ↥B →* R := ρ.comp (Subgroup.inclusion hBC)
  let ρB : ↥B →* ↥N₀ := ρB0.codRestrict N₀ (fun x => hBx x)
  have hkerB : ∀ b ∈ ρB.ker, b ∈ CFSG.pCore 2 ↥B := by
    have hp : IsPGroup 2 ↥(ρB.ker) := by
      intro g
      have hg : ρ (Subgroup.inclusion hBC g.1) = 1 := by
        have h1 : ρB g.1 = 1 := MonoidHom.mem_ker.1 g.2
        exact congrArg Subtype.val h1
      obtain ⟨n, hn⟩ := hρk (Subgroup.inclusion hBC g.1) (MonoidHom.mem_ker.2 hg)
      refine ⟨n, ?_⟩
      have h2 : g.1 ^ (2 ^ n) = 1 := by
        apply Subgroup.inclusion_injective hBC
        rw [map_pow, hn, map_one]
      exact Subtype.ext (by simpa using h2)
    intro b hb
    exact (le_sSup ⟨inferInstance, hp⟩ : ρB.ker ≤ CFSG.pCore 2 ↥B) hb
  have h1080 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1080 :=
    CFSG.Quasithin.SmithC27.card_of_isHat_alt6 hd.Bhat
  have h27B : 27 ∣ Nat.card ↥B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), h1080]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨-, hZB, -⟩ := hd.Bhat
  have hN27 : ¬ 27 ∣ Nat.card (↥N₀ ⧸ Subgroup.center ↥N₀) := by
    obtain ⟨-, -, ⟨eN⟩⟩ := hN₀hat
    have hM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 := hM22
    rw [Nat.card_congr eN.toEquiv, hM]
    norm_num
  have hu3 : (⟨yt, hd.ytB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hd.yt3)
  have hu1 : (⟨yt, hd.ytB⟩ : ↥B) ∉ CFSG.pCore 2 ↥B := by
    intro hmem
    have h1 : (⟨yt, hd.ytB⟩ : ↥B) = 1 :=
      kzEqOnePowThreeMem_kz3 CFSG.pCore_isPGroup hu3 hmem
    have hyt1 : yt = 1 := congrArg Subtype.val h1
    have h2 : (⟨yt, hd.ytK⟩ : ↥Kt) = 1 := Subtype.ext hyt1
    rw [h2, map_one] at hφy0
    exact hφy0 rfl
  have hZu : ρB ⟨yt, hd.ytB⟩ ∈ Subgroup.center ↥N₀ :=
    central_image_of_hat_cv ρB (CFSG.pCore 2 ↥B) CFSG.pCore_isPGroup hkerB hZB h27B hN27
      ⟨yt, hd.ytB⟩ hu3 hd.ytc hu1
  have hyK : (⟨yt, hyC⟩ : ↥C) ∈ Kt.subgroupOf C := Subgroup.mem_subgroupOf.2 hd.ytK
  have hy3 : (⟨yt, hyC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hd.yt3)
  have hnorm : ∀ d ∈ Kt.subgroupOf C,
      ρ d * ρ ⟨yt, hyC⟩ * (ρ d)⁻¹ ∈ Subgroup.zpowers (ρ ⟨yt, hyC⟩) := by
    intro d hd'
    have hc := Subgroup.mem_center_iff.1 hZu ⟨ρ d, hρK d hd'⟩
    have hc' : ρ d * ρ ⟨yt, hyC⟩ = ρ ⟨yt, hyC⟩ * ρ d := congrArg Subtype.val hc
    rw [hc', mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  let φ' : ↥(Kt.subgroupOf C) →* alternatingGroup (Fin 5) :=
    φ.comp (Subgroup.subgroupOfEquivOfLe hKC).toMonoidHom
  have hφ's : Function.Surjective φ' := by
    intro a
    obtain ⟨x, hx⟩ := hφs a
    refine ⟨(Subgroup.subgroupOfEquivOfLe hKC).symm x, ?_⟩
    show φ ((Subgroup.subgroupOfEquivOfLe hKC) ((Subgroup.subgroupOfEquivOfLe hKC).symm x)) = a
    rw [MulEquiv.apply_symm_apply, hx]
  have hφ'y : φ' ⟨⟨yt, hyC⟩, hyK⟩ ≠ 1 := hφy0
  have hperf : ⁅(⊤ : Subgroup ↥(Kt.subgroupOf C)), (⊤ : Subgroup ↥(Kt.subgroupOf C))⁆ = ⊤ :=
    kzTopCommutatorOfPerfect_kz3 hKperfC
  exact false_of_centrality_trap_cv (D := ↥C) (Kt.subgroupOf C) hperf φ' hφ's ⟨yt, hyC⟩ hyK
    hy3 hφ'y ρ hρk hnorm

end CFSG.Quasithin.H13
