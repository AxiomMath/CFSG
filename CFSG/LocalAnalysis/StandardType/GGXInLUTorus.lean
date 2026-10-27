module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
import CFSG.Assembly.GL83StatedBridge

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

private theorem mem_frameT_iff {H : Type} [Group H] {N : Subgroup H} [N.Normal]
    {L' E' : Subgroup H} {n : ℕ} {K : Type} [Field K] [Finite K]
    (F : lup8f_UFrame3 H N L' E' n K) {t : H ⧸ N} :
    t ∈ lup8f_frameT F ↔
      ∃ u : ↥(L'.map (QuotientGroup.mk' N)),
        (F.eps u : GL (Fin n) K) ∈ lup8f_frameTorusGL n K F.P ∧
          (u : H ⧸ N) = t := by
  rw [lup8f_frameT, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_comap] at hu
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr hu), rfl⟩

private theorem mem_frameTorusGL_iff {n : ℕ} {K : Type} [Field K] (P : GL (Fin n) K)
    {g : GL (Fin n) K} :
    g ∈ lup8f_frameTorusGL n K P ↔
      ∃ σ ∈ lup8f_prodOne n K, P * lup8f_diagGL n K σ * P⁻¹ = g := by
  rw [lup8f_frameTorusGL, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨σ, hσ, rfl⟩ := hh
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨lup8f_diagGL n K σ, Subgroup.mem_map_of_mem _ hσ, rfl⟩

private theorem diagGL_const_eq_scalar {n : ℕ} {K : Type} [Field K] (c : Kˣ) :
    lup8f_diagGL n K (fun _ => c) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  apply Units.ext
  simp [lup8f_diagGL, Matrix.scalar_apply]

private theorem conj_scalar_eq {n : ℕ} {K : Type} [Field K] (P : GL (Fin n) K) (c : Kˣ) :
    P * Matrix.GeneralLinearGroup.scalar (Fin n) c * P⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff.mp hc P, mul_assoc, mul_inv_cancel, mul_one]

private theorem diagGL_mul_comm {n : ℕ} {K : Type} [Field K] (σ τ : Fin n → Kˣ) :
    lup8f_diagGL n K σ * lup8f_diagGL n K τ = lup8f_diagGL n K τ * lup8f_diagGL n K σ := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem lup8f_frame_torus (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (F : lup8f_UFrame3 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K)
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    lup8f_TorusData ((lup8f_HT L Bs) ⧸ C.N)
      ((lup8f_E' L Bs).map (QuotientGroup.mk' C.N))
      ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) (lup8f_frameT F)
      (QuotientGroup.mk' C.N ⟨x, Subgroup.mem_sup_left hxL⟩) := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hSStar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSStar.2.2.2.1.1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxne : x ≠ 1 := hSStar.2.2.1
  have hxpow : x ^ p = 1 := hSStar.1.1.2 x hSStar.2.1
  have hLperf : commutator ↥L = ⊤ := hSStar.2.2.2.1.2.2.1
  let xt : lup8f_HT L Bs := ⟨x, Subgroup.mem_sup_left hxL⟩
  let z : ((lup8f_HT L Bs) ⧸ C.N) := QuotientGroup.mk' C.N xt
  change lup8f_TorusData ((lup8f_HT L Bs) ⧸ C.N)
    ((lup8f_E' L Bs).map (QuotientGroup.mk' C.N))
    ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) (lup8f_frameT F) z
  have hx3 : x ^ 3 = 1 := by rw [← hp]; exact hxpow
  have hxt3 : xt ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxtne : xt ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  have hxtord : orderOf xt = 3 := orderOf_eq_prime hxt3 hxtne
  have hz3 : z ^ 3 = 1 := by
    change (QuotientGroup.mk' C.N xt) ^ 3 = 1
    rw [← map_pow, hxt3, map_one]
  have hzne : z ≠ 1 := by
    intro hz1
    have hxtN : xt ∈ C.N := (QuotientGroup.eq_one_iff xt).mp hz1
    have h3dvd : 3 ∣ Nat.card C.N := by
      have h := Subgroup.orderOf_dvd_natCard (s := C.N) (x := xt) hxtN
      simpa [hxtord] using h
    have h31 : (3 : ℕ) = 1 := Nat.eq_one_of_dvd_coprimes C.coprime (dvd_refl 3) h3dvd
    norm_num at h31
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hzne
  have hz_mem_L0 : z ∈ (lup8f_L' L Bs).map (QuotientGroup.mk' C.N) := by
    change QuotientGroup.mk' C.N xt ∈ (lup8f_L' L Bs).map (QuotientGroup.mk' C.N)
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)
  have hz_center : ∀ l ∈ (lup8f_L' L Bs).map (QuotientGroup.mk' C.N), l * z = z * l := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
    change QuotientGroup.mk' C.N l' * QuotientGroup.mk' C.N xt =
      QuotientGroup.mk' C.N xt * QuotientGroup.mk' C.N l'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxcent (l' : G) (Subgroup.mem_subgroupOf.mp hl'))
  have hL0perf : commutator ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) = ⊤ := by
    let φ : ↥L →* ((lup8f_HT L Bs) ⧸ C.N) :=
      (QuotientGroup.mk' C.N).comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs))
    have hperfL : Group.IsPerfect ↥L := ⟨hLperf⟩
    have hmap : (⊤ : Subgroup ↥L).map φ = (lup8f_L' L Bs).map (QuotientGroup.mk' C.N) := by
      ext y
      constructor
      · rintro ⟨l, -, rfl⟩
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr l.2)
      · intro hy
        obtain ⟨l', hl', hml'⟩ := Subgroup.mem_map.mp hy
        refine ⟨⟨(l' : G), Subgroup.mem_subgroupOf.mp hl'⟩, Subgroup.mem_top _, ?_⟩
        rw [show φ ⟨(l' : G), Subgroup.mem_subgroupOf.mp hl'⟩ =
            QuotientGroup.mk' C.N l' from
          congrArg (QuotientGroup.mk' C.N) (Subtype.ext rfl)]
        exact hml'
    rw [← hmap]
    exact (Group.IsPerfect.map (H := ⊤) φ).commutator_eq_top
  have hframe_pow_three : ∀ u : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)),
      (F.eps u : GL (Fin n) K) ∈ lup8f_frameTorusGL n K F.P → u ^ 3 = 1 := by
    intro u hu
    obtain ⟨σ, _, hσeq⟩ := (mem_frameTorusGL_iff F.P).mp hu
    have hKunits : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, M.card_K]
    have hσ3 : ∀ i, σ i ^ 3 = 1 := by
      intro i
      simpa [hKunits] using pow_card_eq_one' (x := σ i)
    have hσpow : σ ^ 3 = 1 := by
      funext i
      simpa using hσ3 i
    have hd3 : lup8f_diagGL n K σ ^ 3 = 1 := by
      rw [← map_pow, hσpow, map_one]
    have heps3 : (F.eps u) ^ 3 = 1 := by
      apply Subtype.ext
      have hGL : ((F.eps u : GL (Fin n) K)) ^ 3 = 1 := by
        rw [← hσeq]
        calc (F.P * lup8f_diagGL n K σ * F.P⁻¹) ^ 3
            = F.P * (lup8f_diagGL n K σ) ^ 3 * F.P⁻¹ := conj_pow
          _ = F.P * 1 * F.P⁻¹ := by rw [hd3]
          _ = 1 := by simp
      simpa using hGL
    apply F.eps.injective
    rw [map_pow, map_one]
    exact heps3
  refine ⟨?_, Subgroup.map_subtype_le _, ?_, hz_mem_L0, hz_center, ?_, hzord, hL0perf⟩
  ·
    intro t ht
    obtain ⟨u, hu, hut⟩ := (mem_frameT_iff F).mp ht
    obtain ⟨l, hl, hml⟩ := Subgroup.mem_map.mp u.2
    have hu_eq : (⟨QuotientGroup.mk' C.N l, Subgroup.mem_map_of_mem _ hl⟩ : ↥
        ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N))) = u := by
      apply Subtype.ext
      exact hml
    have hu3 : u ^ 3 = 1 := hframe_pow_three u hu
    have hmat_eq : ∀ b : ↥(lup8f_E' L Bs), ∃ σ : Fin n → Kˣ,
        F.mat b = F.P * lup8f_diagGL n K σ * F.P⁻¹ := by
      intro b
      obtain ⟨σ, hσ⟩ := F.diag b
      refine ⟨σ, ?_⟩
      have hGL : (F.P⁻¹ : GL (Fin n) K) * F.mat b * F.P = lup8f_diagGL n K σ := by
        apply Units.ext
        simpa [lup8f_diagGL] using hσ
      rw [← hGL]
      group
    have hcomm_mat : ∀ b : ↥(lup8f_E' L Bs),
        F.mat b * (F.eps u : GL (Fin n) K) =
          (F.eps u : GL (Fin n) K) * F.mat b := by
      intro b
      obtain ⟨σ, hσ⟩ := hmat_eq b
      obtain ⟨τ, _, hτ⟩ := (mem_frameTorusGL_iff F.P).mp hu
      calc F.mat b * (F.eps u : GL (Fin n) K)
          = (F.P * lup8f_diagGL n K σ * F.P⁻¹) *
              (F.P * lup8f_diagGL n K τ * F.P⁻¹) := by rw [hσ, hτ]
        _ = F.P * (lup8f_diagGL n K σ * lup8f_diagGL n K τ) * F.P⁻¹ := by group
        _ = F.P * (lup8f_diagGL n K τ * lup8f_diagGL n K σ) * F.P⁻¹ := by
              rw [diagGL_mul_comm]
        _ = (F.P * lup8f_diagGL n K τ * F.P⁻¹) *
              (F.P * lup8f_diagGL n K σ * F.P⁻¹) := by group
        _ = (F.eps u : GL (Fin n) K) * F.mat b := by rw [hσ, hτ]
    have hconj_rep : ∀ (l' : ↥(lup8f_L' L Bs)),
        (QuotientGroup.mk' C.N (l' : lup8f_HT L Bs) : (lup8f_HT L Bs) ⧸ C.N) =
          (u : (lup8f_HT L Bs) ⧸ C.N) →
        ∀ b : ↥(lup8f_E' L Bs),
          (QuotientGroup.mk' C.N
            ((b : lup8f_HT L Bs) * (l' : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹) :
              (lup8f_HT L Bs) ⧸ C.N) =
            (u : (lup8f_HT L Bs) ⧸ C.N) := by
      intro l' hl' b
      have hu'_eq : (⟨QuotientGroup.mk' C.N (l' : lup8f_HT L Bs),
          Subgroup.mem_map_of_mem _ l'.2⟩ : ↥
            ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N))) = u := by
        apply Subtype.ext
        exact hl'
      have hstep := F.mat_ind b l'
      have hcancel : (F.eps (lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs)
          C.E'_le_norm b l') : GL (Fin n) K) = (F.eps u : GL (Fin n) K) := by
        rw [hstep, hu'_eq, MulAut.conj_apply, hcomm_mat b, mul_assoc, mul_inv_cancel,
          mul_one]
      have heq : lup8f_conjLQ C.N (lup8f_L' L Bs) (lup8f_E' L Bs) C.E'_le_norm b l' = u := by
        apply F.eps.injective
        exact Subtype.ext hcancel
      have hcoe := congrArg (fun x : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) =>
        (x : (lup8f_HT L Bs) ⧸ C.N)) heq
      simpa [lup8f_conjLQ] using hcoe
    have hmk_l3 : QuotientGroup.mk' C.N ((l : lup8f_HT L Bs) ^ 3) = 1 := by
      have hu3' : ((⟨QuotientGroup.mk' C.N (l : lup8f_HT L Bs),
          Subgroup.mem_map_of_mem _ hl⟩ : ↥
            ((lup8f_L' L Bs).map (QuotientGroup.mk' C.N))) ^ 3) = 1 := by
        rw [hu_eq]
        exact hu3
      have hcoe := congrArg (fun x : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) =>
        (x : (lup8f_HT L Bs) ⧸ C.N)) hu3'
      simpa using hcoe
    have hl3N : (l : lup8f_HT L Bs) ^ 3 ∈ C.N := (QuotientGroup.eq_one_iff _).mp hmk_l3
    obtain ⟨a, ha⟩ := IsPGroup.exists_orderOf_eq_pow C.two_group
      (⟨(l : lup8f_HT L Bs) ^ 3, hl3N⟩ : ↥C.N)
    have hordl3 : orderOf ((l : lup8f_HT L Bs) ^ 3) = 2 ^ a := by
      simpa using ha
    have h4mod : ∀ k : ℕ, ∃ j, 4 ^ k = 3 * j + 1 := by
      intro k
      induction k with
      | zero => exact ⟨0, by norm_num⟩
      | succ k ih =>
          obtain ⟨j, hj⟩ := ih
          refine ⟨4 * j + 1, ?_⟩
          rw [pow_succ, hj]
          ring
    let l₁ : ↥(lup8f_L' L Bs) :=
      ⟨(l : lup8f_HT L Bs) ^ (4 ^ a), pow_mem hl (4 ^ a)⟩
    have hl₁3 : ((l₁ : lup8f_HT L Bs) ^ 3) = 1 := by
      have hdiv : 2 ^ a ∣ 4 ^ a := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      change ((l : lup8f_HT L Bs) ^ (4 ^ a)) ^ 3 = 1
      rw [← pow_mul, show 4 ^ a * 3 = 3 * 4 ^ a by omega, pow_mul,
        ← orderOf_dvd_iff_pow_eq_one, hordl3]
      exact hdiv
    have hmk_l₁ : (QuotientGroup.mk' C.N (l₁ : lup8f_HT L Bs) :
        (lup8f_HT L Bs) ⧸ C.N) = (u : (lup8f_HT L Bs) ⧸ C.N) := by
      change QuotientGroup.mk' C.N ((l : lup8f_HT L Bs) ^ (4 ^ a)) = _
      rw [map_pow, hml]
      have hpow : u ^ (4 ^ a) = u := by
        obtain ⟨j, hj⟩ := h4mod a
        rw [hj, pow_add, pow_mul, hu3, one_pow, one_mul, pow_one]
      simpa using congrArg (fun x : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) =>
        (x : (lup8f_HT L Bs) ⧸ C.N)) hpow
    have hl₁_comm : ∀ b : ↥(lup8f_E' L Bs),
        (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) =
          (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs) := by
      intro b
      have hconj := hconj_rep l₁ hmk_l₁ b
      have hcN : ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
          (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) ∈ C.N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change (QuotientGroup.mk' C.N) ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
          (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) = 1
        rw [map_mul, hconj, map_inv, hmk_l₁]
        exact mul_inv_cancel _
      have hc3 : ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
          (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) ^ 3 = 1 := by
        have hcentral : Commute ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
            (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) (l₁ : lup8f_HT L Bs) :=
          (C.central _ hcN (l₁ : lup8f_HT L Bs) l₁.2).symm
        have hc_eq : (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ =
            ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ *
              (l₁ : lup8f_HT L Bs)⁻¹) * (l₁ : lup8f_HT L Bs) := by group
        calc ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ *
              (l₁ : lup8f_HT L Bs)⁻¹) ^ 3
            = ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ *
                (l₁ : lup8f_HT L Bs)⁻¹) ^ 3 * (l₁ : lup8f_HT L Bs) ^ 3 := by
                rw [hl₁3, mul_one]
          _ = (((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ *
                (l₁ : lup8f_HT L Bs)⁻¹) * (l₁ : lup8f_HT L Bs)) ^ 3 := by
                rw [hcentral.mul_pow]
          _ = ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹) ^ 3 := by
                rw [← hc_eq]
          _ = (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) ^ 3 * (b : lup8f_HT L Bs)⁻¹ :=
                conj_pow
          _ = 1 := by rw [hl₁3]; simp
      have hc1 : (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ *
          (l₁ : lup8f_HT L Bs)⁻¹ = 1 := by
        have hord : orderOf ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
            (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) ∣ 3 :=
          orderOf_dvd_of_pow_eq_one hc3
        have hcard : orderOf ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) *
            (b : lup8f_HT L Bs)⁻¹ * (l₁ : lup8f_HT L Bs)⁻¹) ∣ Nat.card C.N :=
          Subgroup.orderOf_dvd_natCard C.N hcN
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes C.coprime hord hcard)
      have h2 : (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹ =
          (l₁ : lup8f_HT L Bs) := mul_inv_eq_one.mp hc1
      calc (b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs)
          = ((b : lup8f_HT L Bs) * (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs)⁻¹) *
              (b : lup8f_HT L Bs) := by group
        _ = (l₁ : lup8f_HT L Bs) * (b : lup8f_HT L Bs) := by rw [h2]
    have hcentral_G : ((l₁ : lup8f_HT L Bs) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbH : b ∈ (L ⊔ Bs : Subgroup G) := Subgroup.mem_sup_right hb
      let b' : ↥(lup8f_E' L Bs) :=
        ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb⟩
      have hcomm := hl₁_comm b'
      simpa using congrArg (fun x : lup8f_HT L Bs => (x : G)) hcomm
    have hl₁_pow_G : (((l₁ : lup8f_HT L Bs) : G)) ^ 3 = 1 := by
      simpa using congrArg (fun x : lup8f_HT L Bs => (x : G)) hl₁3
    have hl₁_Bs : ((l₁ : lup8f_HT L Bs) : G) ∈ Bs :=
      hcfg.2.1.2.2.2 _ hcentral_G (by rw [hp]; exact hl₁_pow_G)
    have hl₁_E' : (l₁ : lup8f_HT L Bs) ∈ lup8f_E' L Bs :=
      Subgroup.mem_subgroupOf.mpr hl₁_Bs
    rw [← hut, ← hmk_l₁]
    exact Subgroup.mem_map_of_mem _ hl₁_E'
  · intro t ht
    obtain ⟨u, hu, hut⟩ := (mem_frameT_iff F).mp ht
    have hu3 : u ^ 3 = 1 := hframe_pow_three u hu
    have hord : orderOf t ∣ 3 := by
      rw [← hut, Subgroup.orderOf_coe u]
      exact orderOf_dvd_of_pow_eq_one hu3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hord with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  ·
    refine (mem_frameT_iff F).mpr ⟨⟨z, hz_mem_L0⟩, ?_, rfl⟩
    have hzSUcenter : F.eps ⟨z, hz_mem_L0⟩ ∈
        Subgroup.center ↥(LargeEvenSUGroup (Fin n) K 2) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := F.eps.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg F.eps (by
        apply Subtype.ext
        exact hz_center u u.2)
    have hcenter_le : Subgroup.center ↥(LargeEvenSUGroup (Fin n) K 2) ≤
        (CFSG.Open.StatedScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K 2) := by
      have hK : Nat.card K = (2 ^ 1) ^ 2 := by
        rw [M.card_K]
        norm_num
      have hn3 : 3 ≤ n := by omega
      have hnq : (n, 2 ^ 1) ≠ (3, 2) := by
        intro h
        have h1 : n = 3 := by simpa using congrArg Prod.fst h
        omega
      have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (F := K) (p := 2) (f := 1) (n := n) hK hn3 hnq).2
      rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
      simpa using le_of_eq h
    have hscalar : (F.eps ⟨z, hz_mem_L0⟩ : GL (Fin n) K) ∈ CFSG.Open.StatedScalars (Fin n) K :=
      Subgroup.mem_subgroupOf.mp (hcenter_le hzSUcenter)
    have hscalar' : (F.eps ⟨z, hz_mem_L0⟩ : GL (Fin n) K) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin n)).range := hscalar
    obtain ⟨c, hc⟩ := hscalar'
    have hc3 : c ^ 3 = 1 := by
      have hKunits : Nat.card Kˣ = 3 := by
        rw [Nat.card_units, M.card_K]
      simpa [hKunits] using pow_card_eq_one' (x := c)
    have hcn : c ^ n = 1 := by
      obtain ⟨k, rfl⟩ := hdvd
      rw [pow_mul, hc3, one_pow]
    refine (mem_frameTorusGL_iff F.P).mpr ⟨fun _ => c, ?_, ?_⟩
    · show (∏ i : Fin n, c) = 1
      rw [Finset.prod_const]
      simp [Finset.card_univ, hcn]
    · rw [diagGL_const_eq_scalar, conj_scalar_eq]
      exact hc

end CFSG.StandardType.GGXInL

end
