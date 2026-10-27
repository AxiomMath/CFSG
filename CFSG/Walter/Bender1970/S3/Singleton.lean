module

public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S1.Burnside
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.Open CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem BenderCounterexample.mem_of_benderM_eq_singleton (hG : BenderCounterexample G)
    {H : Subgroup G} (hH : IsCoatom H) {s g : G} (hs : benderM s = {H})
    (hs' : benderM (g⁻¹ * s * g) = {H}) : g ∈ H := by
  have h := benderM_conj_eq_singleton g hs'
  have hgs : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rw [hgs, hs] at h
  exact hG.mem_of_map_conj_eq hH (Set.singleton_eq_singleton_iff.mp h).symm

theorem BenderCounterexample.three_le_rank_sylow (hG : BenderCounterexample G) (T : Sylow 2 G) :
    3 ≤ rank (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup', (pRank_sylow T).1]
  exact hG.three_le_twoRank

theorem exists_involution_mem_inf_conj {T : Subgroup G} (hTp : IsPGroup 2 T)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {R : Subgroup G} (hRT : R ≤ T)
    (hrank : Open.pRank 2 R + 1 = Open.pRank 2 T) (h3 : 3 ≤ Open.pRank 2 T) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ s ∈ R, orderOf s = 2 ∧ g⁻¹ * s * g ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => hcommT x (hRT hx) y (hRT hy)
  set E := omegaOneOfComm 2 T hcommT with hEdef
  set A := omegaOneOfComm 2 R hcommR with hAdef
  set B := A.map (MulAut.conj g).toMonoidHom with hBdef
  have hcardE : Nat.card E = 2 ^ Open.pRank 2 T := card_omegaOneOfComm hp2 T hcommT hTp
  have hcardA : Nat.card A = 2 ^ Open.pRank 2 R :=
    card_omegaOneOfComm hp2 R hcommR (hTp.to_le hRT)
  have hcardB : Nat.card B = 2 ^ Open.pRank 2 R := by
    rw [hBdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardA]
  have hAE : A ≤ E := fun x hx => ⟨hRT hx.1, hx.2⟩
  have hBE : B ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hRT hx.1)
    · rw [← map_pow, hx.2, map_one]
  set H₁ : Subgroup E := A.subgroupOf E
  set H₂ : Subgroup E := B.subgroupOf E
  have hc₁ : Nat.card H₁ = 2 ^ Open.pRank 2 R :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv).trans hcardA
  have hc₂ : Nat.card H₂ = 2 ^ Open.pRank 2 R :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv).trans hcardB
  have hidx : ∀ K : Subgroup E, Nat.card K = 2 ^ Open.pRank 2 R → K.index = 2 := by
    intro K hK
    have h := K.card_mul_index
    rw [hK, hcardE, ← hrank, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h
  have hle : (H₁ ⊓ H₂).index ≤ 4 :=
    (Subgroup.index_inf_le).trans (by rw [hidx H₁ hc₁, hidx H₂ hc₂])
  have hcardI : 2 ≤ Nat.card (H₁ ⊓ H₂ : Subgroup E) := by
    have h := (H₁ ⊓ H₂).card_mul_index
    rw [hcardE] at h
    have h8 : 8 ≤ 2 ^ Open.pRank 2 T :=
      (Nat.pow_le_pow_right two_pos h3 : 2 ^ 3 ≤ 2 ^ Open.pRank 2 T)
    by_contra hlt
    push Not at hlt
    have : Nat.card (H₁ ⊓ H₂ : Subgroup E) * (H₁ ⊓ H₂).index ≤ 1 * 4 :=
      Nat.mul_le_mul (by omega) hle
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hcardI)
  obtain ⟨hxA, hxB⟩ := x.2
  have hxA' : ((x : E) : G) ∈ A := hxA
  have hxB' : ((x : E) : G) ∈ B := hxB
  refine ⟨((x : E) : G), hxA'.1, ?_, ?_⟩
  · refine orderOf_eq_prime hxA'.2 ?_
    intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  · obtain ⟨y, hy, hyx⟩ := hxB'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    rw [← hyx]
    simpa [mul_assoc] using hy.1

theorem exists_conj_mem_sylow_of_le {H : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {s : G} (hsH : s ∈ H) (hs : orderOf s = 2) :
    ∃ h ∈ H, h⁻¹ * s * h ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s' : H := ⟨s, hsH⟩
  have hp : IsPGroup 2 (Subgroup.zpowers s') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (T.subtype hTH) Q
  have hsQ : s' ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers s')
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Sylow.coe_subtype,
    Subgroup.mem_subgroupOf] at hsQ
  refine ⟨h, h.2, ?_⟩
  convert hsQ using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]
  rfl

theorem BenderCounterexample.isStronglyEmbeddedOrder_of_forall_benderM_eq
    (hG : BenderCounterexample G) {H : Subgroup G} (hH : IsCoatom H) {t : G}
    (htH : t ∈ H) (ht : orderOf t = 2)
    (hall : ∀ s ∈ H, orderOf s = 2 → benderM s = {H}) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hH.1, ?_, fun g hg => ?_⟩
  · have h2 : orderOf (⟨t, htH⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ht] at h2
    exact even_iff_two_dvd.mpr h2
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ H.map (MulAut.conj g).toMonoidHom))
      2 (even_iff_two_dvd.mp hodd)
    have hxs : orderOf (x : G) = 2 := by rw [← hx, Subgroup.orderOf_coe]
    obtain ⟨hxH, y, hyH, hyx⟩ := x.2
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hy : orderOf y = 2 := by
      rw [← hxs, ← hyx, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hyx' : y = g⁻¹ * (x : G) * g := by rw [← hyx]; group
    exact hg (hG.mem_of_benderM_eq_singleton hH (hall _ hxH hxs) (hyx' ▸ hall y hyH hy))

theorem BenderCounterexample.exists_benderM_ne_singleton (hG : BenderCounterexample G)
    {H : Subgroup G} (hH : IsCoatom H) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    {R : Subgroup G} (hRT : R ≤ T) (hR : rank R = rank (T : Subgroup G) - 1) :
    ∃ s ∈ R, orderOf s = 2 ∧ benderM s ≠ {H} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hG.isSimpleGroup
  have hTab := hG.hasAbelianSylowTwo T
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 := hG.three_le_rank_sylow T
  have hTp : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hrT : rank (T : Subgroup G) = Open.pRank 2 (T : Subgroup G) :=
    rank_eq_pRank_of_isPGroup Nat.prime_two hTp
  have hrR : rank R = Open.pRank 2 R := rank_eq_pRank_of_isPGroup Nat.prime_two (hTp.to_le hRT)
  by_contra hcon
  push Not at hcon
  have hN : Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H := by
    intro g hg
    obtain ⟨s, hsR, hs, hs'⟩ := exists_involution_mem_inf_conj hTp hcommT hRT (by omega)
      (by omega) hg
    have hs'o : orderOf (g⁻¹ * s * g) = 2 := by
      have : g⁻¹ * s * g = MulAut.conj g⁻¹ s := by rw [MulAut.conj_apply, inv_inv]
      rw [this, MulEquiv.orderOf_eq, hs]
    exact hG.mem_of_benderM_eq_singleton hH (hcon s hsR hs) (hcon _ hs' hs'o)
  have hall : ∀ s ∈ H, orderOf s = 2 → benderM s = {H} := by
    intro s hsH hs
    obtain ⟨h, hh, hhs⟩ := exists_conj_mem_sylow_of_le T hTH hsH hs
    have hs₁ : orderOf (h⁻¹ * s * h) = 2 := by
      have : h⁻¹ * s * h = MulAut.conj h⁻¹ s := by rw [MulAut.conj_apply, inv_inv]
      rw [this, MulEquiv.orderOf_eq, hs]
    obtain ⟨n, hn, hnR⟩ := bender1970_1_3 hG.nonabelian T hTab hRT hR hhs hs₁
    have hs₂ : orderOf (n * (h⁻¹ * s * h) * n⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs₁]
    have h1 := benderM_conj_eq_singleton (h * n⁻¹) (hcon _ hnR hs₂)
    have he : h * n⁻¹ * (n * (h⁻¹ * s * h) * n⁻¹) * (h * n⁻¹)⁻¹ = s := by group
    rw [he] at h1
    rw [h1, map_conj_eq_self_of_mem (H.mul_mem hh (H.inv_mem (hN hn)))]
  obtain ⟨t, htT, ht⟩ : ∃ t ∈ (T : Subgroup G), orderOf t = 2 := by
    obtain ⟨E, hET, hE, hcard⟩ := exists_pRank one_lt_two (T : Subgroup G)
    have h2 : 2 ∣ Nat.card E := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 h2
    exact ⟨x, hET x.2, by rw [← hx, Subgroup.orderOf_coe]⟩
  exact hG.not_stronglyEmbedded ⟨H, hG.isStronglyEmbeddedOrder_of_forall_benderM_eq hH (hTH htT)
    ht hall⟩

theorem bender1970_3_3 (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {R : Subgroup G} (hRT : R ≤ T) (hR : rank R = rank (T : Subgroup G) - 1) :
    ∃ s ∈ R, orderOf s = 2 ∧ benderM s ≠ {H} :=
  have _ := ht
  hG.exists_benderM_ne_singleton (isCoatom_of_mem_benderM hH) T
    (hG.sylow_le_of_mem_benderM T htT hH) hRT hR

end CFSG.Walter
