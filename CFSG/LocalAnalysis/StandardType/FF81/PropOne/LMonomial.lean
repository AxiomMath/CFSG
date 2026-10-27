module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLift
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)

structure TauC {G : Type} [Group G] {L : Subgroup G} (z : Fin 3 → ↥L) (τ c : G) : Prop where
  tau_mem : τ ∈ L
  c_mem : c ∈ L
  tau_sq : τ ^ 2 = 1
  c_cube : c ^ 3 = 1
  comm : c * τ = τ * c
  inv : ∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹
  cyc₀ : c * GGFF.zs z 0 * c⁻¹ = GGFF.zs z 1
  cyc₁ : c * GGFF.zs z 1 * c⁻¹ = GGFF.zs z 2
  cyc₂ : c * GGFF.zs z 2 * c⁻¹ = GGFF.zs z 0

private theorem inv_pow_val_eq {G : Type} [Group G] {z : Fin 3 → G} (hp : ∀ i, z i ^ 3 = 1)
    (hc : ∀ i j, z i * z j = z j * z i) (i : Fin 3) (a : ZMod 3) :
    (z i)⁻¹ ^ a.val = z i ^ (-a).val := by
  rw [inv_pow, ← vecElt_single i a, ← vecElt_single i (-a)]
  have hneg : -(Pi.single i a) = (Pi.single i (-a) : Fin 3 → ZMod 3) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Pi.neg_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj]
      exact neg_zero
  rw [← hneg]
  exact (GGFF.vecElt_neg hp hc (Pi.single i a)).symm

private theorem conj_vecElt_all_inv {G : Type} [Group G] {z : Fin 3 → G}
    (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    {ι : G} (hι : ∀ i, ι * z i * ι⁻¹ = (z i)⁻¹) (v : Fin 3 → ZMod 3) :
    ι * vecElt z v * ι⁻¹ = vecElt z (-v) := by
  have hc' : ∀ x : G, ι * x * ι⁻¹ = MulAut.conj ι x := fun x => rfl
  rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
    hι 0, hι 1, hι 2, vecElt]
  rw [inv_pow_val_eq hp hc 0 (v 0), inv_pow_val_eq hp hc 1 (v 1),
    inv_pow_val_eq hp hc 2 (v 2)]
  simp only [Pi.neg_apply]

private theorem conj_vecElt_update {G : Type} [Group G] {z : Fin 3 → G}
    (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    {ι : G} {i : Fin 3} (hι : ι * z i * ι⁻¹ = (z i)⁻¹)
    (hfix : ∀ j, j ≠ i → ι * z j * ι⁻¹ = z j) (v : Fin 3 → ZMod 3) :
    ι * vecElt z v * ι⁻¹ = vecElt z (Function.update v i (-(v i))) := by
  have hsq := inv_pow_val_eq hp hc i (v i)
  have hc' : ∀ x : G, ι * x * ι⁻¹ = MulAut.conj ι x := fun x => rfl
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hcases with rfl | rfl | rfl
  · have hι' : ι * z 0 * ι⁻¹ = (z 0)⁻¹ := by simpa using hι
    have h1 : ι * z 1 * ι⁻¹ = z 1 := by simpa using hfix 1 (by decide)
    have h2 : ι * z 2 * ι⁻¹ = z 2 := by simpa using hfix 2 (by decide)
    rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
      hι', h1, h2, vecElt]
    simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    rw [hsq]
  · have h0 : ι * z 0 * ι⁻¹ = z 0 := by simpa using hfix 0 (by decide)
    have hι' : ι * z 1 * ι⁻¹ = (z 1)⁻¹ := by simpa using hι
    have h2 : ι * z 2 * ι⁻¹ = z 2 := by simpa using hfix 2 (by decide)
    rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
      h0, hι', h2, vecElt]
    simp only [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
    rw [hsq]
  · have h0 : ι * z 0 * ι⁻¹ = z 0 := by simpa using hfix 0 (by decide)
    have h1 : ι * z 1 * ι⁻¹ = z 1 := by simpa using hfix 1 (by decide)
    have hι' : ι * z 2 * ι⁻¹ = (z 2)⁻¹ := by simpa using hι
    rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
      h0, h1, hι', vecElt]
    simp only [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2), Function.update_self]
    rw [hsq]

private theorem sign_mem {G : Type} [Group G] {z : Fin 3 → G}
    (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    {H : Subgroup G} {ι : G} (hιH : ∀ x ∈ H, ι * x * ι⁻¹ ∈ H)
    {i : Fin 3} (hι : ι * z i * ι⁻¹ = (z i)⁻¹)
    (hfix : ∀ j, j ≠ i → ι * z j * ι⁻¹ = z j)
    {v : Fin 3 → ZMod 3} (hxH : vecElt z v ∈ H) (hvi : v i ≠ 0) :
    z i ∈ H := by
  have hconj : vecElt z (Function.update v i (-(v i))) ∈ H := by
    have h := hιH _ hxH
    rwa [conj_vecElt_update hp hc hι hfix v] at h
  have hy : vecElt z v * (vecElt z (Function.update v i (-(v i))))⁻¹ ∈ H :=
    H.mul_mem hxH (H.inv_mem hconj)
  have hyz : vecElt z v * (vecElt z (Function.update v i (-(v i))))⁻¹ =
      z i ^ (2 * (v i)).val := by
    rw [← GGFF.vecElt_neg hp hc, ← GGFF.vecElt_add hp hc]
    have hvec : v + -(Function.update v i (-(v i))) = Pi.single i (2 * (v i)) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.neg_apply, Function.update_self, Pi.single_eq_same]
        rw [two_mul]
        abel
      · rw [Pi.add_apply, Pi.neg_apply, Function.update_of_ne hj, Pi.single_eq_of_ne hj]
        exact add_neg_cancel (v j)
    change vecElt z (v + -(Function.update v i (-(v i)))) = z i ^ (2 * (v i)).val
    rw [hvec, vecElt_single]
  rw [hyz] at hy
  have hcases : (2 * (v i)).val = 1 ∨ (2 * (v i)).val = 2 := by
    have hne : (2 * (v i)).val ≠ 0 := by
      intro h0
      have hzero : (2 : ZMod 3) * v i = 0 := (ZMod.val_eq_zero _).mp h0
      rcases mul_eq_zero.mp hzero with h2 | hv
      · exact absurd h2 (by decide)
      · exact hvi hv
    have hlt : (2 * (v i)).val < 3 := ZMod.val_lt _
    omega
  rcases hcases with h1 | h2
  · rwa [h1, pow_one] at hy
  · have hz2 : z i ^ 2 ∈ H := by rwa [h2] at hy
    have he : (z i ^ 2) ^ 2 = z i := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hp i, one_mul]
    rw [← he]
    exact H.pow_mem hz2 2

private theorem exists_mul_centralizer_of_conj_mem_coset' {G : Type} [Group G] (Y : Subgroup G)
    (hY : Odd (Nat.card Y)) {τ : G} (hτ : τ ^ 2 = 1) {g : G}
    (hg : g⁻¹ * τ * g * τ⁻¹ ∈ Y) :
    ∃ y ∈ Y, ∃ w ∈ Subgroup.centralizer ({τ} : Set G), g = w * y := by
  set u := g⁻¹ * τ * g * τ⁻¹ with hu
  have huY : u ∈ Y := hg
  have hτ2 : τ * τ = 1 := by rwa [pow_two] at hτ
  have hτi : τ⁻¹ = τ := by rw [inv_eq_iff_mul_eq_one, hτ2]
  have h1 : u * τ = g⁻¹ * τ * g := by rw [hu]; group
  have h2 : τ * u⁻¹ = g⁻¹ * τ * g := by
    rw [hu, hτi]
    have h3 : (g⁻¹ * τ * g * τ)⁻¹ = τ * g⁻¹ * τ * g := by
      rw [show (g⁻¹ * τ * g * τ)⁻¹ = τ⁻¹ * g⁻¹ * τ⁻¹ * g by group, hτi]
    rw [h3]
    calc τ * (τ * g⁻¹ * τ * g) = (τ * τ) * (g⁻¹ * τ * g) := by group
      _ = g⁻¹ * τ * g := by rw [hτ2, one_mul]
  have hτu : τ * u * τ⁻¹ = u⁻¹ := by
    rw [hτi]
    calc τ * u * τ = τ * (u * τ) := by group
      _ = τ * (g⁻¹ * τ * g) := by rw [h1]
      _ = u⁻¹ := by rw [← h2, ← mul_assoc, hτ2, one_mul]
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat hY (Subgroup.orderOf_dvd_natCard Y huY)
  obtain ⟨k, hk⟩ := hodd
  set m : ℕ := (orderOf u - 1) / 2 with hm
  have hm2 : m * 2 = orderOf u - 1 := by rw [hm]; omega
  set y : G := u ^ m with hy
  have hyY : y ∈ Y := by rw [hy]; exact Y.pow_mem huY m
  have hy2 : y ^ 2 = u⁻¹ := by
    rw [hy, ← pow_mul, hm2]
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', show orderOf u - 1 + 1 = orderOf u by omega, pow_orderOf_eq_one]
  have hτy : τ * y * τ⁻¹ = y⁻¹ := by
    rw [hy]
    have hτu' : MulAut.conj τ u = u⁻¹ := by rw [MulAut.conj_apply]; exact hτu
    have h := map_pow (MulAut.conj τ) u m
    rw [hτu'] at h
    rw [inv_pow] at h
    simpa [MulAut.conj_apply] using h
  have hτyi : τ * y⁻¹ = y * τ := by
    have h : τ * y⁻¹ * τ = y := by
      have h2 := congrArg Inv.inv hτy
      rw [show (τ * y * τ⁻¹)⁻¹ = τ * y⁻¹ * τ⁻¹ by group, hτi] at h2
      simpa using h2
    calc τ * y⁻¹ = τ * y⁻¹ * τ * τ := by rw [mul_assoc, hτ2, mul_one]
      _ = y * τ := by rw [h]
  have hgτ : τ * g = g * u * τ := by
    have h : g⁻¹ * τ * g = u * τ := by rw [hu]; group
    calc τ * g = g * (g⁻¹ * τ * g) := by group
      _ = g * (u * τ) := by rw [h]
      _ = g * u * τ := by group
  have huy : u * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc u * y * y = u * (y * y) := by group
      _ = u * y ^ 2 := by rw [pow_two]
      _ = u * u⁻¹ := by rw [hy2]
      _ = 1 := mul_inv_cancel u
  have hwy' : τ * (g * y⁻¹) = (g * y⁻¹) * τ := by
    calc τ * (g * y⁻¹) = τ * g * y⁻¹ := by group
      _ = g * u * τ * y⁻¹ := by rw [hgτ]
      _ = g * u * (τ * y⁻¹) := by group
      _ = g * u * (y * τ) := by rw [hτyi]
      _ = g * (u * y) * τ := by group
      _ = g * y⁻¹ * τ := by rw [huy]
      _ = (g * y⁻¹) * τ := by group
  exact ⟨y, hyY, g * y⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hwy'.symm,
    by group⟩

private theorem mem_nor_BB_of_tor {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {g : G} (hg : g ∈ L)
    (hgz : ∀ i, g * GGFF.zs z i * g⁻¹ ∈ GGFF.tor (GGFF.zs z)) :
    g ∈ Subgroup.normalizer
      ((CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BB b (GGFF.zs z 0) (GGFF.zs z 1)
        (GGFF.zs z 2) : Subgroup G) : Set G) := by
  have hBB : (CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BB b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) : Subgroup G) = GGFF.Bt b z :=
    (GGFF.SettingCore.Bt_eq_closure b z).symm
  rw [hBB]
  refine GGFF.SettingCore.mem_nor_Bt ?_ (fun i => GGFF.SettingCore.tor_le_Bt b z (hgz i))
  rw [h.settingCore.conj_b hg]
  exact GGFF.SettingCore.b_mem_Bt b z

theorem exists_tauC {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : ∃ τ c : G, TauC z τ c := by
  have hs := h.settingCore
  have hcen := cen_of_model h.hypA.n_cases h.hypA.model h.model
  obtain ⟨g₀, hg₀⟩ := h.model.mono 1 (fun _ => (2 : ZMod 3)) (by decide)
  have hsq : ∀ i, z i ^ 2 = (z i)⁻¹ := by
    intro i
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, h.model.pow_z i]
  have hg₀inv : ∀ i, g₀ * z i * g₀⁻¹ = (z i)⁻¹ := by
    intro i
    have h : g₀ * z i * g₀⁻¹ = z i ^ 2 := by
      have h0 := hg₀ i
      rw [show (1 : Equiv.Perm (Fin 3)) i = i from rfl] at h0
      rw [show ((fun _ => (2 : ZMod 3)) i).val = 2 from rfl] at h0
      exact h0
    exact h.trans (hsq i)
  set τL : ↥L := g₀ ^ 3 with hτL
  have hτL_sq : τL ^ 2 = 1 := by
    have h6 : (g₀ ^ 2) ^ 3 = 1 := by
      have hcomm : ∀ i, (g₀ ^ 2) * z i = z i * (g₀ ^ 2) := by
        intro i
        have h2 : (g₀ ^ 2) * z i * (g₀ ^ 2)⁻¹ = z i := by
          calc (g₀ ^ 2) * z i * (g₀ ^ 2)⁻¹
              = (g₀ * g₀) * z i * (g₀ * g₀)⁻¹ := by rw [pow_two]
            _ = g₀ * (g₀ * z i * g₀⁻¹) * g₀⁻¹ := by group
            _ = g₀ * (z i)⁻¹ * g₀⁻¹ := by rw [hg₀inv i]
            _ = (g₀ * z i * g₀⁻¹)⁻¹ := by group
            _ = z i := by rw [hg₀inv i, inv_inv]
        exact mul_inv_eq_iff_eq_mul.mp h2
      obtain ⟨v, hv⟩ := hcen (g₀ ^ 2) hcomm
      rw [hv]
      exact h.model.isElemAbelian_tor'.2 (vecElt z v) (GGFF.vecElt_mem_tor z v)
    rw [hτL, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
    exact h6
  have hτL_inv : ∀ i, τL * z i * τL⁻¹ = (z i)⁻¹ := by
    intro i
    rw [hτL]
    exact CFSG.RankThree.PartTwo.Sec21.FF81.Lift.pow_conj_inv (hg₀inv i) ⟨1, by norm_num⟩
  have hτL_tor : ∀ x ∈ GGFF.tor z, τL * x * τL⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨v, hv⟩ := h.model.mem_tor'.mp hx
    rw [hv, conj_vecElt_all_inv h.model.pow_z h.model.comm_z hτL_inv v]
    exact (h.model.vecElt_inv v).symm
  obtain ⟨g₁, hg₁⟩ := h.model.mono (finRotate 3) (fun _ => (1 : ZMod 3)) (by decide)
  have hg₁_conj : ∀ i, g₁ * z i * g₁⁻¹ = z (finRotate 3 i) := by
    intro i
    simpa [ZMod.val_one] using hg₁ i
  set u : ↥L := g₁⁻¹ * τL * g₁ * τL⁻¹ with hu
  have hu_comm : ∀ i, u * z i = z i * u := by
    intro i
    have hτLi' : ∀ j, τL⁻¹ * z j * τL = (z j)⁻¹ := by
      intro j
      have h := CFSG.RankThree.PartTwo.Sec21.FF81.Lift.inv_conj_of_conj (hτL_inv j)
      have h2 := congrArg Inv.inv h
      rw [show (τL⁻¹ * (z j)⁻¹ * τL)⁻¹ = τL⁻¹ * z j * τL by group] at h2
      simpa using h2
    have hg₁inv : ∀ j, g₁⁻¹ * z j * g₁ = z ((finRotate 3).symm j) := by
      intro j
      have h := CFSG.RankThree.PartTwo.Sec21.FF81.Lift.inv_conj_of_conj
        (hg₁_conj ((finRotate 3).symm j))
      rwa [Equiv.apply_symm_apply] at h
    have hτLinv_inv : τL * (z (finRotate 3 i))⁻¹ * τL⁻¹ = z (finRotate 3 i) := by
      have h := congrArg Inv.inv (hτL_inv (finRotate 3 i))
      rw [show (τL * z (finRotate 3 i) * τL⁻¹)⁻¹ =
        τL * (z (finRotate 3 i))⁻¹ * τL⁻¹ by group] at h
      simpa using h
    have hconj : u * z i * u⁻¹ = z i := by
      calc u * z i * u⁻¹
          = g₁⁻¹ * τL * g₁ * (τL⁻¹ * z i * τL) * g₁⁻¹ * τL⁻¹ * g₁ := by rw [hu]; group
        _ = g₁⁻¹ * τL * g₁ * (z i)⁻¹ * g₁⁻¹ * τL⁻¹ * g₁ := by rw [hτLi' i]
        _ = g₁⁻¹ * τL * (g₁ * (z i)⁻¹ * g₁⁻¹) * τL⁻¹ * g₁ := by group
        _ = g₁⁻¹ * τL * (z (finRotate 3 i))⁻¹ * τL⁻¹ * g₁ := by
              rw [show g₁ * (z i)⁻¹ * g₁⁻¹ = (g₁ * z i * g₁⁻¹)⁻¹ by group, hg₁_conj i]
        _ = g₁⁻¹ * (τL * (z (finRotate 3 i))⁻¹ * τL⁻¹) * g₁ := by group
        _ = g₁⁻¹ * z (finRotate 3 i) * g₁ := by rw [hτLinv_inv]
        _ = z ((finRotate 3).symm (finRotate 3 i)) := hg₁inv (finRotate 3 i)
        _ = z i := by rw [Equiv.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  obtain ⟨vu, hvu⟩ := hcen u hu_comm
  have hu_tor : u ∈ GGFF.tor z := h.model.mem_tor'.mpr ⟨vu, hvu⟩
  have hodd : Odd (Nat.card (GGFF.tor z)) := by rw [h.model.card_tor']; norm_num
  obtain ⟨y, hy_tor, cL, hcL_mem, hg₁_eq⟩ :=
    exists_mul_centralizer_of_conj_mem_coset' (GGFF.tor z) hodd hτL_sq hu_tor
  have hcL_comm : cL * τL = τL * cL := Subgroup.mem_centralizer_singleton_iff.mp hcL_mem
  have hcL_cyc : ∀ i, cL * z i * cL⁻¹ = z (finRotate 3 i) := by
    intro i
    have hcomm_i : y * z i = z i * y := by
      have h := h.model.isElemAbelian_tor'.1.is_comm.comm ⟨y, hy_tor⟩
        ⟨z i, Subgroup.subset_closure ⟨i, rfl⟩⟩
      simpa using congrArg Subtype.val h
    calc cL * z i * cL⁻¹ = cL * (y * z i * y⁻¹) * cL⁻¹ := by rw [hcomm_i]; group
      _ = cL * y * z i * y⁻¹ * cL⁻¹ := by group
      _ = g₁ * z i * g₁⁻¹ := by rw [hg₁_eq]; group
      _ = z (finRotate 3 i) := hg₁_conj i
  have hcL3_comm : ∀ i, (cL ^ 3) * z i = z i * (cL ^ 3) := by
    intro i
    have hconj : cL ^ 3 * z i * (cL ^ 3)⁻¹ = z i := by
      have h3 : cL ^ 3 = cL * cL * cL := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      have h3i : (cL ^ 3)⁻¹ = cL⁻¹ * cL⁻¹ * cL⁻¹ := by
        rw [h3, mul_inv_rev, mul_inv_rev, mul_assoc]
      rw [h3i, h3,
        show cL * cL * cL * z i * (cL⁻¹ * cL⁻¹ * cL⁻¹) =
          cL * (cL * (cL * z i * cL⁻¹) * cL⁻¹) * cL⁻¹ by group]
      rw [hcL_cyc i, hcL_cyc (finRotate 3 i), hcL_cyc (finRotate 3 (finRotate 3 i))]
      have h3' : finRotate 3 (finRotate 3 (finRotate 3 i)) = i := by
        fin_cases i <;> decide
      rw [h3']
    exact mul_inv_eq_iff_eq_mul.mp hconj
  obtain ⟨v3, hv3⟩ := hcen (cL ^ 3) hcL3_comm
  have hcL3_tor : cL ^ 3 ∈ GGFF.tor z := h.model.mem_tor'.mpr ⟨v3, hv3⟩
  have hcL9 : (cL ^ 3) ^ 3 = 1 := by
    rw [hv3]
    exact h.model.isElemAbelian_tor'.2 (vecElt z v3) (GGFF.vecElt_mem_tor z v3)
  have hcL3_eq_inv : cL ^ 3 = (cL ^ 3)⁻¹ := by
    have h1 : τL * (cL ^ 3) * τL⁻¹ = (cL ^ 3)⁻¹ := hτL_tor _ hcL3_tor
    have h2 : τL * (cL ^ 3) * τL⁻¹ = cL ^ 3 := by
      have hcomm : Commute τL cL := hcL_comm.symm
      have hcomm3 : τL * cL ^ 3 = cL ^ 3 * τL := (hcomm.pow_right 3).eq
      rw [hcomm3, mul_inv_cancel_right]
    rw [← h1, h2]
  have hcL_cube : cL ^ 3 = 1 := by
    have h2 : (cL ^ 3) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hcL3_eq_inv]
      exact inv_mul_cancel _
    have h := pow_gcd_eq_one.mpr ⟨h2, hcL9⟩
    rwa [show Nat.gcd 2 3 = 1 from rfl, pow_one] at h
  have hcL_cyc0 : cL * z 0 * cL⁻¹ = z 1 := by
    have h := hcL_cyc 0
    rwa [show finRotate 3 (0 : Fin 3) = 1 from by decide] at h
  have hcL_cyc1 : cL * z 1 * cL⁻¹ = z 2 := by
    have h := hcL_cyc 1
    rwa [show finRotate 3 (1 : Fin 3) = 2 from by decide] at h
  have hcL_cyc2 : cL * z 2 * cL⁻¹ = z 0 := by
    have h := hcL_cyc 2
    rwa [show finRotate 3 (2 : Fin 3) = 0 from by decide] at h
  refine ⟨(τL : G), (cL : G), τL.2, cL.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hτL_sq
  · simpa using congrArg Subtype.val hcL_cube
  · simpa using congrArg Subtype.val hcL_comm
  · intro i
    simpa [GGFF.zs] using congrArg Subtype.val (hτL_inv i)
  · simpa [GGFF.zs] using congrArg Subtype.val hcL_cyc0
  · simpa [GGFF.zs] using congrArg Subtype.val hcL_cyc1
  · simpa [GGFF.zs] using congrArg Subtype.val hcL_cyc2

theorem exists_mono_irreducible {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G,
      (∀ g ∈ ({τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), g ∈ L) ∧
      CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono b (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2)
        τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ ∧
      ∀ H : Subgroup G,
        H ≤ CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BO (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) →
        H ≠ ⊥ → (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
          H = CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BO
            (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) := by
  obtain ⟨τ, c, hTauC⟩ := exists_tauC h
  have hs := h.settingCore
  obtain ⟨t₁, ht₁⟩ := h.model.mono 1 ![2, 1, 1] (by decide)
  obtain ⟨s, hsg⟩ := h.model.mono (Equiv.swap 0 1) (fun _ => (1 : ZMod 3)) (by decide)
  let ι₁ : G := (t₁ : G)
  let ι₂ : G := (s : G) * (t₁ : G) * (s : G)⁻¹
  let ι₃ : G := c * ι₂ * c⁻¹
  let σ₁₂ : G := (s : G)
  let σ₂₃ : G := c * (s : G) * c⁻¹
  let γ : G := c
  have hτL : τ ∈ L := hTauC.tau_mem
  have hcL : c ∈ L := hTauC.c_mem
  have ht₁L : (t₁ : G) ∈ L := t₁.2
  have hsL : (s : G) ∈ L := s.2
  have hι₁L : ι₁ ∈ L := ht₁L
  have hι₂L : ι₂ ∈ L := L.mul_mem (L.mul_mem hsL ht₁L) (L.inv_mem hsL)
  have hι₃L : ι₃ ∈ L := L.mul_mem (L.mul_mem hcL hι₂L) (L.inv_mem hcL)
  have hσ₁₂L : σ₁₂ ∈ L := hsL
  have hσ₂₃L : σ₂₃ ∈ L := L.mul_mem (L.mul_mem hcL hsL) (L.inv_mem hcL)
  have hγL : γ ∈ L := hcL
  have hfixb_of_mem : ∀ g ∈ L, g * b * g⁻¹ = b := fun g hg =>
    (by rw [Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hg), mul_inv_cancel_right])
  have hc_cyc : ∀ i, c * GGFF.zs z i * c⁻¹ = GGFF.zs z (finRotate 3 i) := by
    intro i
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcases with rfl | rfl | rfl
    · rw [show finRotate 3 (0 : Fin 3) = 1 from by decide]; exact hTauC.cyc₀
    · rw [show finRotate 3 (1 : Fin 3) = 2 from by decide]; exact hTauC.cyc₁
    · rw [show finRotate 3 (2 : Fin 3) = 0 from by decide]; exact hTauC.cyc₂
  have ht₁_conj : ∀ i, (t₁ : G) * GGFF.zs z i * (t₁ : G)⁻¹ =
      GGFF.zs z i ^ ((![2, 1, 1] : Fin 3 → ZMod 3) i).val := by
    intro i
    simpa [GGFF.zs] using congrArg Subtype.val (ht₁ i)
  have hs_conj : ∀ i, (s : G) * GGFF.zs z i * (s : G)⁻¹ = GGFF.zs z (Equiv.swap 0 1 i) := by
    intro i
    simpa [GGFF.zs, ZMod.val_one] using congrArg Subtype.val (hsg i)
  have hN : ∀ g ∈ ({τ, (t₁ : G), (s : G), c} : Set G),
      g ∈ Subgroup.normalizer
        ((CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BB b (GGFF.zs z 0) (GGFF.zs z 1)
          (GGFF.zs z 2) : Subgroup G) : Set G) ∧ g * b * g⁻¹ = b := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨mem_nor_BB_of_tor h hτL (fun i => by
        rw [hTauC.inv i]
        exact (GGFF.tor (GGFF.zs z)).inv_mem (Subgroup.subset_closure ⟨i, rfl⟩)),
        hfixb_of_mem _ hτL⟩
    · exact ⟨mem_nor_BB_of_tor h ht₁L (fun i => by
        rw [ht₁_conj i]
        exact (GGFF.tor (GGFF.zs z)).pow_mem (Subgroup.subset_closure ⟨_, rfl⟩) _),
        hfixb_of_mem _ ht₁L⟩
    · exact ⟨mem_nor_BB_of_tor h hsL (fun i => by
        rw [hs_conj i]
        exact Subgroup.subset_closure ⟨_, rfl⟩),
        hfixb_of_mem _ hsL⟩
    · exact ⟨mem_nor_BB_of_tor h hcL (fun i => by
        rw [hc_cyc i]
        exact Subgroup.subset_closure ⟨_, rfl⟩),
        hfixb_of_mem _ hcL⟩
  have hτ : τ * GGFF.zs z 0 * τ⁻¹ = (GGFF.zs z 0)⁻¹ ∧
      τ * GGFF.zs z 1 * τ⁻¹ = (GGFF.zs z 1)⁻¹ ∧
      τ * GGFF.zs z 2 * τ⁻¹ = (GGFF.zs z 2)⁻¹ :=
    ⟨hTauC.inv 0, hTauC.inv 1, hTauC.inv 2⟩
  have ht₁' : (t₁ : G) * GGFF.zs z 0 * (t₁ : G)⁻¹ = (GGFF.zs z 0)⁻¹ ∧
      (t₁ : G) * GGFF.zs z 1 * (t₁ : G)⁻¹ = GGFF.zs z 1 ∧
      (t₁ : G) * GGFF.zs z 2 * (t₁ : G)⁻¹ = GGFF.zs z 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ht₁_conj 0]; simpa using hs.zs_sq 0
    · rw [ht₁_conj 1]; simp [ZMod.val_one]
    · rw [ht₁_conj 2]; simp [ZMod.val_one]
  have hs' : (s : G) * GGFF.zs z 0 * (s : G)⁻¹ = GGFF.zs z 1 ∧
      (s : G) * GGFF.zs z 1 * (s : G)⁻¹ = GGFF.zs z 0 ∧
      (s : G) * GGFF.zs z 2 * (s : G)⁻¹ = GGFF.zs z 2 := by
    refine ⟨?_, ?_, ?_⟩
    · have h : (Equiv.swap 0 1) (0 : Fin 3) = 1 := by decide
      rw [hs_conj 0, h]
    · have h : (Equiv.swap 0 1) (1 : Fin 3) = 0 := by decide
      rw [hs_conj 1, h]
    · have h : (Equiv.swap 0 1) (2 : Fin 3) = 2 := by decide
      rw [hs_conj 2, h]
  have hc' : c * GGFF.zs z 0 * c⁻¹ = GGFF.zs z 1 ∧
      c * GGFF.zs z 1 * c⁻¹ = GGFF.zs z 2 ∧
      c * GGFF.zs z 2 * c⁻¹ = GGFF.zs z 0 :=
    ⟨hTauC.cyc₀, hTauC.cyc₁, hTauC.cyc₂⟩
  have hMono : CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono b (GGFF.zs z 0) (GGFF.zs z 1)
      (GGFF.zs z 2) τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.Lift.Mono.of_gens hN hτ ht₁' hs' hc'
  refine ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, ?_, hMono, ?_⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hτL, hι₁L, hι₂L, hι₃L, hσ₁₂L, hσ₂₃L, hγL]
  · intro H hHle hHne hstab
    have hHle' : H ≤ GGFF.tor (GGFF.zs z) := by
      rw [GGFF.SettingCore.tor_eq_closure]
      exact hHle
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hHne
    have hxH : (x : G) ∈ H := x.2
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨v, hv⟩ := h.settingCore.mem_torG.mp (hHle' hxH)
    have hv0 : v ≠ 0 := by
      intro h0
      apply hx1'
      rw [hv, h0]
      exact GGFF.vecElt_zero (GGFF.zs z)
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    have hxH' : vecElt (GGFF.zs z) v ∈ H := by rwa [← hv]
    have hγ_stab : ∀ x ∈ H, γ * x * γ⁻¹ ∈ H := fun x hx => hstab γ (by simp) x hx
    have hγ2_stab : ∀ x ∈ H, γ ^ 2 * x * (γ ^ 2)⁻¹ ∈ H := by
      have hNγ : γ ∈ Subgroup.normalizer (H : Set G) := GGFF.mem_nor_of_conj_mem hγ_stab
      intro x hx
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (H : Set G)).pow_mem hNγ 2) x).mp hx
    have hγ_cyc : ∀ j, γ * GGFF.zs z j * γ⁻¹ = GGFF.zs z (finRotate 3 j) := hc_cyc
    have hstep : ∀ j, GGFF.zs z j ∈ H → GGFF.zs z (finRotate 3 j) ∈ H := by
      intro j hj
      rw [← hγ_cyc j]
      exact hγ_stab _ hj
    have hstep2 : ∀ j, GGFF.zs z j ∈ H → GGFF.zs z (finRotate 3 (finRotate 3 j)) ∈ H :=
      fun j hj => hstep _ (hstep j hj)
    have hzi : GGFF.zs z i ∈ H := by
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hcases with rfl | rfl | rfl
      · exact sign_mem hs.zs_pow hs.zs_comm (fun x hx => hstab ι₁ (by simp) x hx)
          hMono.s₁.1 (fun j hj => by
            fin_cases j
            · exact absurd rfl hj
            · exact hMono.s₁.2.1
            · exact hMono.s₁.2.2) hxH' hi
      · exact sign_mem hs.zs_pow hs.zs_comm (fun x hx => hstab ι₂ (by simp) x hx)
          hMono.s₂.2.1 (fun j hj => by
            fin_cases j
            · exact hMono.s₂.1
            · exact absurd rfl hj
            · exact hMono.s₂.2.2) hxH' hi
      · exact sign_mem hs.zs_pow hs.zs_comm (fun x hx => hstab ι₃ (by simp) x hx)
          hMono.s₃.2.2 (fun j hj => by
            fin_cases j
            · exact hMono.s₃.1
            · exact hMono.s₃.2.1
            · exact absurd rfl hj) hxH' hi
    have hcases_all : ∀ i j : Fin 3,
        j = i ∨ j = finRotate 3 i ∨ j = finRotate 3 (finRotate 3 i) := by
      decide
    have hfin : ∀ j, GGFF.zs z j ∈ H := by
      intro j
      have h1 := hstep i hzi
      have h2 := hstep2 i hzi
      rcases hcases_all i j with rfl | rfl | rfl
      exacts [hzi, h1, h2]
    refine le_antisymm hHle ?_
    refine (Subgroup.closure_le (K := H)).mpr fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hfin 0, hfin 1, hfin 2]

end CFSG.StandardType.FF81.PropOne

end
