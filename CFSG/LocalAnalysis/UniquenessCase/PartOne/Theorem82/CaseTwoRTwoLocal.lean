module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRArgument
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem commutator_mem_inf_N_of_mem (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {F : Subgroup G}
    (hFM : F ≤ c.S.M) (hKF : t.Ky ≤ Subgroup.normalizer (F : Set G))
    (h3 : ¬ 3 ∣ Nat.card F) {f : G} (hfM : f ∈ c.S.M)
    (hfK : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ F) :
    ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ c.L ⊓ t.d.N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPi : ⁅F, t.Ky⁆ ≤ F ⊓ (c.L ⊓ t.d.N) :=
    t.commutator_Ky_le_inf_N hK32 hGA hSp hFM hKF h3
  let Fq : Subgroup ↥t.M := F.subgroupOf t.M
  let Fbar : Subgroup t.Mb := Fq.map t.qmk
  have hFq_card : Nat.card ↥Fq = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
  have hFbar_dvd : Nat.card ↥Fbar ∣ Nat.card F := by
    rw [← hFq_card]
    exact Subgroup.card_map_dvd Fq t.qmk
  have hFbar3 : ¬ 3 ∣ Nat.card ↥Fbar := fun h => h3 (h.trans hFbar_dvd)
  have hcommute : ∀ x ∈ Fbar, ∀ y ∈ (t.Ky.subgroupOf t.M).map t.qmk,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨xM, hxM, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨yM, hyM, rfl⟩ := Subgroup.mem_map.mp hy
    have hxG : (xM : G) ∈ F := Subgroup.mem_subgroupOf.mp hxM
    have hyG : (yM : G) ∈ t.Ky := Subgroup.mem_subgroupOf.mp hyM
    have hmem : ⁅(xM : G), (yM : G)⁆ ∈ c.L ⊓ t.d.N :=
      (hPi (Subgroup.commutator_mem_commutator hxG hyG)).2
    have hKq : ⁅xM, yM⁆ ∈ t.Kq := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅xM, yM⁆ : ↥t.M) : G) = ⁅(xM : G), (yM : G)⁆ := by
        change t.M.subtype ⁅xM, yM⁆ = ⁅t.M.subtype xM, t.M.subtype yM⁆
        exact map_commutatorElement t.M.subtype xM yM
      rw [hcoe]
      exact hmem
    have h1 : t.qmk ⁅xM, yM⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hKq
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  let fM : ↥t.M := ⟨f, hfM⟩
  let ψ : ↥t.Ky →* t.Mb :=
    MonoidHom.mk' (fun k => t.qmk (fM * kM t k * fM⁻¹ * (kM t k)⁻¹)) (by
      intro k₁ k₂
      let a : ↥t.M := fM
      let x : ↥t.M := kM t k₁
      let y : ↥t.M := kM t k₂
      let C : ↥t.M := a * y * a⁻¹ * y⁻¹
      change t.qmk (a * (x * y) * a⁻¹ * (x * y)⁻¹) =
        t.qmk (a * x * a⁻¹ * x⁻¹) * t.qmk C
      have hψ₂ : t.qmk C ∈ Fbar := by
        refine Subgroup.mem_map.mpr ⟨C, ?_, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        exact hfK k₂ k₂.2
      have hq₁ : t.qmk x ∈ (t.Ky.subgroupOf t.M).map t.qmk :=
        Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr k₁.2, rfl⟩
      have hcomm₁ : t.qmk x * t.qmk C = t.qmk C * t.qmk x :=
        (hcommute (t.qmk C) hψ₂ (t.qmk x) hq₁).symm
      have hA : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * C * x⁻¹) := by
        rw [show C = a * y * a⁻¹ * y⁻¹ from rfl]
        group
      have step3 : t.qmk (x * C * x⁻¹) =
          t.qmk x * t.qmk C * (t.qmk x)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      calc
        t.qmk (a * (x * y) * a⁻¹ * (x * y)⁻¹)
            = t.qmk ((a * x * a⁻¹ * x⁻¹) * (x * C * x⁻¹)) := by rw [hA]
        _ = t.qmk (a * x * a⁻¹ * x⁻¹) * t.qmk (x * C * x⁻¹) := map_mul _ _ _
        _ = t.qmk (a * x * a⁻¹ * x⁻¹) *
              (t.qmk x * t.qmk C * (t.qmk x)⁻¹) := by rw [step3]
        _ = t.qmk (a * x * a⁻¹ * x⁻¹) * t.qmk C := by
            rw [hcomm₁]; group)
  have hψ_range : ψ.range ≤ Fbar := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mem_map.mpr ⟨fM * kM t k * fM⁻¹ * (kM t k)⁻¹, by
      rw [Subgroup.mem_subgroupOf]
      exact hfK k k.2, rfl⟩
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Ky
  have hZker : t.Z.subgroupOf t.Ky ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz3 : z ^ 3 = 1 := by
      have hcardZ : Nat.card ↥(t.Z.subgroupOf t.Ky) = 3 := by
        rw [← t.card_Z]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZKy).toEquiv
      have hord : orderOf z ∣ 3 := by
        have h1 := Subgroup.orderOf_dvd_natCard (t.Z.subgroupOf t.Ky) hz
        rwa [hcardZ] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
      · rw [orderOf_eq_one_iff.mp h, one_pow]
      · rw [← h]
        exact pow_orderOf_eq_one z
    have hψ3 : (ψ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
    have hψF : ψ z ∈ Fbar := hψ_range ⟨z, rfl⟩
    have hdvd3 : orderOf (ψ z) ∣ 3 := orderOf_dvd_of_pow_eq_one hψ3
    have hdvdF : orderOf (ψ z) ∣ Nat.card ↥Fbar :=
      Subgroup.orderOf_dvd_natCard Fbar hψF
    have hcop3 : Nat.Coprime 3 (Nat.card ↥Fbar) :=
      Nat.prime_three.coprime_iff_not_dvd.mpr hFbar3
    have hgd : orderOf (ψ z) ∣ Nat.gcd 3 (Nat.card ↥Fbar) :=
      Nat.dvd_gcd hdvd3 hdvdF
    rw [hcop3.gcd_eq_one] at hgd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgd)
  let κ : Subgroup ↥t.Ky := ψ.ker
  let N' : Subgroup G := κ.map t.Ky.subtype
  have hκnormal : κ.Normal := inferInstance
  have hsub : N'.subgroupOf t.Ky = κ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hakeq⟩
      have hax : a = x := Subtype.ext hakeq
      rwa [hax] at ha
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hN'norm : t.Ky ≤ Subgroup.normalizer (N' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := N') (K := t.Ky)
      (Subgroup.map_subtype_le κ)).mp (hsub ▸ hκnormal)
  have hZ_N' : t.Z ≤ N' := by
    intro x hx
    let y : ↥t.Ky := ⟨x, hZKy hx⟩
    have hy : y ∈ t.Z.subgroupOf t.Ky := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨y, hZker hy, rfl⟩
  rcases t.le_N_or_eq_Ky hK32 hGA hSp (Subgroup.map_subtype_le κ) hN'norm with
    hle | heq
  · exfalso
    have hZbot : t.Z = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxN : x ∈ t.d.N := hle (hZ_N' hx)
      have hmem : x ∈ t.Z ⊓ t.d.N := Subgroup.mem_inf.mpr ⟨hx, hxN⟩
      rwa [t.Z_inf_N_eq_bot] at hmem
    have hcard : Nat.card t.Z = 1 := by rw [hZbot, Subgroup.card_bot]
    rw [t.card_Z] at hcard
    norm_num at hcard
  · have hker_top : ψ.ker = ⊤ := by
      apply le_antisymm le_top
      intro k _
      have hk : t.Ky.subtype k ∈ κ.map t.Ky.subtype := by
        rw [heq]
        exact k.2
      obtain ⟨a, ha, hakeq⟩ := Subgroup.mem_map.mp hk
      have hak : a = k := Subtype.ext hakeq
      rwa [hak] at ha
    intro k hk
    have hψ1 : ψ ⟨k, hk⟩ = 1 := by
      have hmem : (⟨k, hk⟩ : ↥t.Ky) ∈ ψ.ker := by
        rw [hker_top]
        exact Subgroup.mem_top _
      simpa [MonoidHom.mem_ker] using hmem
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hψ1)

private theorem permHom_eq_one_of_coprime_six {m : G} (hm : m ∈ c.S.M)
    (hcop : Nat.Coprime 6 (orderOf m)) :
    t.d.permHom t.hinj (hperm_d t) ⟨m, t.hdM.symm ▸ hm⟩ = 1 := by
  have hmM : m ∈ t.d.M := t.hdM.symm ▸ hm
  let σ : Equiv.Perm (Fin 3) := t.d.permHom t.hinj (hperm_d t) ⟨m, hmM⟩
  have hdvd6 : orderOf σ ∣ 6 := by
    have h := orderOf_dvd_natCard σ
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    norm_num at h
    exact h
  have hdvdm : orderOf σ ∣ orderOf m := by
    have hord : orderOf (⟨m, hmM⟩ : ↥t.d.M) = orderOf m := by
      rw [← Subgroup.orderOf_coe (⟨m, hmM⟩ : ↥t.d.M)]
    have hpow : σ ^ orderOf (⟨m, hmM⟩ : ↥t.d.M) = 1 := by
      change (t.d.permHom t.hinj (hperm_d t) ⟨m, hmM⟩) ^
        orderOf (⟨m, hmM⟩ : ↥t.d.M) = 1
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hgd : orderOf σ ∣ Nat.gcd 6 (orderOf m) := Nat.dvd_gcd hdvd6 hdvdm
  rw [hcop.gcd_eq_one] at hgd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgd)

private theorem normalizes_Lf_of_coprime_six {m : G} (hm : m ∈ c.S.M)
    (hcop : Nat.Coprime 6 (orderOf m)) (i : Fin 3) :
    m ∈ Subgroup.normalizer (t.d.Lf i : Set G) := by
  have hmM : m ∈ t.d.M := t.hdM.symm ▸ hm
  have h1 := permHom_eq_one_of_coprime_six t hm hcop
  rw [t.d.mem_normalizer_Lf_iff t.hinj (hperm_d t) ⟨m, hmM⟩ i, h1]
  rfl

private noncomputable def fM {f : G} (hfM : f ∈ c.S.M) : ↥t.M := ⟨f, hfM⟩

private noncomputable def fbar {f : G} (hfM : f ∈ c.S.M) : t.Mb := t.qmk (fM t hfM)

private theorem fbar_commute_phiKy (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {f : G}
    (hfM : f ∈ c.S.M)
    (hfK : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ c.L ⊓ t.d.N) {z : t.Mb}
    (hz : z ∈ t.phiKy.range) : fbar t hfM * z * (fbar t hfM)⁻¹ = z := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hz
  have hKq : fM t hfM * kM t k * (fM t hfM)⁻¹ * (kM t k)⁻¹ ∈ t.Kq := by
    rw [Subgroup.mem_subgroupOf]
    exact hfK k k.2
  have hq : t.qmk (fM t hfM * kM t k * (fM t hfM)⁻¹ * (kM t k)⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hKq
  have h1 : fbar t hfM * t.qmk (kM t k) * (fbar t hfM)⁻¹ *
      (t.qmk (kM t k))⁻¹ = 1 := by
    change t.qmk (fM t hfM) * t.qmk (kM t k) * (t.qmk (fM t hfM))⁻¹ *
      (t.qmk (kM t k))⁻¹ = 1
    rw [← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [show t.phiKy k = t.qmk (kM t k) from rfl]
  calc fbar t hfM * t.qmk (kM t k) * (fbar t hfM)⁻¹ =
      (fbar t hfM * t.qmk (kM t k) * (fbar t hfM)⁻¹ *
        (t.qmk (kM t k))⁻¹) * t.qmk (kM t k) := by group
    _ = t.qmk (kM t k) := by rw [h1, one_mul]

private theorem centralizes_Lhat_of_normalizes_of_centralizes_delta
    (hmuL : Function.Injective (t.muL)) {g : t.Mb}
    (hnorm : ∀ i : Fin 3, ∀ x ∈ t.Lhat i, g * x * g⁻¹ ∈ t.Lhat i)
    (hdelta : ∀ u : ↥(t.Lhat 0), g * t.delta u * g⁻¹ = t.delta u)
    (i : Fin 3) : ∀ x ∈ t.Lhat i, g * x * g⁻¹ = x := by
  classical
  have key : ∀ u : ↥(t.Lhat 0),
      g * (u : t.Mb) * g⁻¹ = (u : t.Mb) ∧
      g * ((MulAut.conj t.ybar) (u : t.Mb)) * g⁻¹ = (MulAut.conj t.ybar) (u : t.Mb) ∧
      g * ((MulAut.conj (t.ybar ^ 2)) (u : t.Mb)) * g⁻¹ =
        (MulAut.conj (t.ybar ^ 2)) (u : t.Mb) := by
    intro u
    let u1 : ↥(t.Lhat 1) :=
      ⟨(MulAut.conj t.ybar) (u : t.Mb), t.conj_ybar_mem_Lhat_one u.2⟩
    let u2 : ↥(t.Lhat 2) :=
      ⟨(MulAut.conj (t.ybar ^ 2)) (u : t.Mb), t.conj_ybar_sq_mem_Lhat_two u.2⟩
    let v0 : ↥(t.Lhat 0) := ⟨g * (u : t.Mb) * g⁻¹, hnorm 0 (u : t.Mb) u.2⟩
    let v1 : ↥(t.Lhat 1) := ⟨g * (u1 : t.Mb) * g⁻¹, hnorm 1 (u1 : t.Mb) u1.2⟩
    let v2 : ↥(t.Lhat 2) := ⟨g * (u2 : t.Mb) * g⁻¹, hnorm 2 (u2 : t.Mb) u2.2⟩
    have hmu : t.muL ((u, u1), u2) = t.delta u := by
      rw [t.muL_apply, t.delta_apply]
    have hconj : g * t.delta u * g⁻¹ = t.muL ((v0, v1), v2) := by
      rw [← hmu, t.muL_apply, t.muL_apply]
      change g * ((u : t.Mb) * (u1 : t.Mb) * (u2 : t.Mb)) * g⁻¹ =
        (v0 : t.Mb) * (v1 : t.Mb) * (v2 : t.Mb)
      simp only [v0, v1, v2]
      group
    have hfix : t.muL ((v0, v1), v2) = t.muL ((u, u1), u2) := by
      rw [← hconj, hdelta u, hmu]
    have heq := hmuL hfix
    have e0 : v0 = u :=
      congrArg (fun x : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) => x.1.1) heq
    have e1 : v1 = u1 :=
      congrArg (fun x : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) => x.1.2) heq
    have e2 : v2 = u2 :=
      congrArg (fun x : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) => x.2) heq
    exact ⟨congrArg Subtype.val e0, congrArg Subtype.val e1, congrArg Subtype.val e2⟩
  fin_cases i
  · intro x hx
    exact (key ⟨x, hx⟩).1
  · intro x hx
    have hx' : x ∈ (t.Lhat 0).map (MulAut.conj t.ybar).toMonoidHom := by
      rw [t.Lhat_conj 0]
      exact hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
    exact (key ⟨u, hu⟩).2.1
  · intro x hx
    have hx' : x ∈ (t.Lhat 0).map (MulAut.conj (t.ybar ^ 2)).toMonoidHom := by
      have hcomp : (MulAut.conj (t.ybar ^ 2)).toMonoidHom =
          (MulAut.conj t.ybar).toMonoidHom.comp (MulAut.conj t.ybar).toMonoidHom := by
        ext z
        simp [MulAut.conj_apply, pow_two]
      rw [hcomp, ← Subgroup.map_map, t.Lhat_conj 0]
      change x ∈ (t.Lhat 1).map (MulAut.conj t.ybar).toMonoidHom
      rw [t.Lhat_conj 1]
      exact hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
    exact (key ⟨u, hu⟩).2.2

private theorem not_mem_Kq_of_orderOf_eq_prime {x : ↥t.M} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hx : orderOf x = r) : x ∉ t.Kq := by
  intro hmem
  obtain ⟨n, hn⟩ := t.Kq_isPGroup.exists_card_eq
  have hd : orderOf x ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.orderOf_dvd_natCard t.Kq hmem
  rw [hx] at hd
  have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

theorem le_M_of_commutator_mem (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrK : r ∣ Nat.card t.Ky) {f : G} (hfM : f ∈ c.S.M) (hf : orderOf f = r)
    (hfK : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ c.L ⊓ t.d.N) {H : Subgroup G}
    (hH : CFSG.Open.IsTwoLocal H) (hKH : t.Ky ≤ H) (hfH : f ∈ H) : H ≤ c.S.M := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hcop : Nat.Coprime 6 (orderOf f) := by
    rw [hf, Nat.coprime_comm, hr.coprime_iff_not_dvd]
    intro hdvd
    have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hr' : r = 5 ∨ r = 6 := by omega
    rcases hr' with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · rw [h] at hr
      norm_num at hr
  have hnorm : ∀ i : Fin 3, ∀ x ∈ t.Lhat i, fbar t hfM * x * (fbar t hfM)⁻¹ ∈ t.Lhat i := by
    intro i x hx
    obtain ⟨aM, haM, rfl⟩ := Subgroup.mem_map.mp hx
    have haLf : (aM : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp haM
    have hfa : f * (aM : G) * f⁻¹ ∈ t.d.Lf i :=
      (Subgroup.mem_normalizer_iff.mp
        (normalizes_Lf_of_coprime_six t hfM hcop i) (aM : G)).mp haLf
    have hfaM : f * (aM : G) * f⁻¹ ∈ t.M :=
      t.M.mul_mem (t.M.mul_mem hfM aM.2) (t.M.inv_mem hfM)
    refine Subgroup.mem_map.mpr ⟨⟨f * (aM : G) * f⁻¹, hfaM⟩,
      Subgroup.mem_subgroupOf.mpr hfa, ?_⟩
    change t.qmk ⟨f * (aM : G) * f⁻¹, hfaM⟩ =
      fbar t hfM * t.qmk aM * (fbar t hfM)⁻¹
    rw [fbar, ← map_mul, ← map_inv]
    rfl
  have hdelta : ∀ u : ↥(t.Lhat 0),
      fbar t hfM * t.delta u * (fbar t hfM)⁻¹ = t.delta u := by
    intro u
    have hz : t.delta u ∈ t.phiKy.range := by
      have hz' : t.delta u ∈ (t.Ky.subgroupOf t.M).map t.qmk :=
        t.delta_range_le_image_Ky ⟨u, rfl⟩
      rwa [← t.phiKy_range] at hz'
    exact fbar_commute_phiKy t hK32 hGA hSp hfM hfK hz
  have hmuL := t.muL_injective hK32 hGA hSp
  have hcent_Lhat : ∀ i : Fin 3, ∀ x ∈ t.Lhat i,
      fbar t hfM * x * (fbar t hfM)⁻¹ = x :=
    centralizes_Lhat_of_normalizes_of_centralizes_delta t hmuL hnorm hdelta
  have hcent_L : ∀ z ∈ (c.L.subgroupOf t.M).map t.qmk,
      fbar t hfM * z * (fbar t hfM)⁻¹ = z := by
    intro z hz
    rw [← t.muL_range] at hz
    obtain ⟨⟨⟨a, b⟩, e⟩, rfl⟩ := MonoidHom.mem_range.mp hz
    rw [t.muL_apply]
    have ha := hcent_Lhat 0 (a : t.Mb) a.2
    have hb := hcent_Lhat 1 (b : t.Mb) b.2
    have he := hcent_Lhat 2 (e : t.Mb) e.2
    calc fbar t hfM * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) * (fbar t hfM)⁻¹
        = (fbar t hfM * (a : t.Mb) * (fbar t hfM)⁻¹) *
            (fbar t hfM * (b : t.Mb) * (fbar t hfM)⁻¹) *
            (fbar t hfM * (e : t.Mb) * (fbar t hfM)⁻¹) := by group
      _ = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) := by rw [ha, hb, he]
  have hfM_ord : orderOf (fM t hfM) = r := by
    rw [← Subgroup.orderOf_coe (fM t hfM)]
    exact hf
  have hfM_notKq : fM t hfM ∉ t.Kq :=
    not_mem_Kq_of_orderOf_eq_prime t hr hr2 hfM_ord
  have hfbar_ne : fbar t hfM ≠ 1 := fun h1 =>
    hfM_notKq ((QuotientGroup.eq_one_iff _).mp h1)
  have hfbar_not_mem : fbar t hfM ∉ (c.L.subgroupOf t.M).map t.qmk := by
    intro hmem
    have hzC : ∀ w ∈ (c.L.subgroupOf t.M).map t.qmk,
        fbar t hfM * w = w * fbar t hfM := by
      intro w hw
      have h := hcent_L w hw
      calc fbar t hfM * w = (fbar t hfM * w * (fbar t hfM)⁻¹) * fbar t hfM := by
            group
        _ = w * fbar t hfM := by rw [h]
    have h1 : fbar t hfM = 1 :=
      eq_one_of_mem_image_L_of_centralizes t hK32 hGA hSp hmem hzC
    exact hfbar_ne h1
  have hfbar_ord : orderOf (fbar t hfM) = r := by
    have hdvd : orderOf (fbar t hfM) ∣ r := by
      have h := orderOf_map_dvd t.qmk (fM t hfM)
      rwa [hfM_ord] at h
    rcases hr.eq_one_or_self_of_dvd (orderOf (fbar t hfM)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hfbar_ne
    · exact h
  have hr_dvd_range : r ∣ Nat.card ↥t.phiKy.range := by
    have hr_not_dvd_inf : ¬ r ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
      have hN : IsPGroup 2 ↥(t.Ky ⊓ t.d.N) := by
        have hN2 : IsPGroup 2 ↥t.d.N :=
          CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.d.M
        exact hN2.to_le inf_le_right
      obtain ⟨n, hn⟩ := hN.exists_card_eq
      intro hrdvd
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hn] at hrdvd)
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    have hker_le : (t.phiKy.ker : Subgroup ↥t.Ky) ≤
        (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk
      have hq : t.qmk (⟨(k : G), t.Ky_le_M k.2⟩ : ↥t.M) = 1 := by
        change t.phiKy k = 1
        exact hk
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨k.2, ?_⟩)
      exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)).2
    have hker_dvd : Nat.card ↥(t.phiKy.ker) ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
      have h1 := Subgroup.card_dvd_of_le hker_le
      have hcard_sub : Nat.card ↥((t.Ky ⊓ t.d.N).subgroupOf t.Ky) =
          Nat.card ↥(t.Ky ⊓ t.d.N) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : t.Ky ⊓ t.d.N ≤ t.Ky)).toEquiv
      rwa [hcard_sub] at h1
    have hnot : ¬ r ∣ Nat.card ↥(t.phiKy.ker) :=
      fun h => hr_not_dvd_inf (h.trans hker_dvd)
    have hprod : r ∣ Nat.card ↥(t.phiKy.ker) * Nat.card ↥(t.phiKy.range) := by
      rw [Subgroup.card_ker_mul_card_range]
      exact hrK
    rcases hr.dvd_mul.mp hprod with h | h
    · exact absurd h hnot
    · exact h
  have hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0) := by
    have hcard : Nat.card ↥(t.Lhat 0) = Nat.card ↥(t.phiKy.range) := by
      rw [t.phiKy_range_eq_delta_range hK32 hGA hSp]
      exact Nat.card_congr (MonoidHom.ofInjective (t.delta_injective hmuL)).toEquiv
    rwa [hcard]
  have h3rank : 3 ≤ CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) :=
    three_le_pRank_image_L t hr2 hrLhat0
  obtain ⟨E3, hE3_le, hE3_abel, hE3_card⟩ :=
    CFSG.SectionRank.exists_pRank (p := r) hr.one_lt ((c.L.subgroupOf t.M).map t.qmk)
  have hfbar_not_E3 : fbar t hfM ∉ E3 := fun h => hfbar_not_mem (hE3_le h)
  have hfbar_pow : (fbar t hfM) ^ r = 1 := by
    rw [← hfbar_ord]
    exact pow_orderOf_eq_one _
  have hfbar_comm_E3 : ∀ a ∈ E3, a * fbar t hfM = fbar t hfM * a := by
    intro a ha
    have h := hcent_L a (hE3_le ha)
    have h' : fbar t hfM * a = a * fbar t hfM := by
      calc fbar t hfM * a = (fbar t hfM * a * (fbar t hfM)⁻¹) * fbar t hfM := by
            group
        _ = a * fbar t hfM := by rw [h]
    exact h'.symm
  obtain ⟨hE4_abel, hE4_card⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers (p := r) (A := E3)
      hE3_abel hfbar_not_E3 hfbar_pow hfbar_comm_E3
  have h4top : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) := by
    have hle := CFSG.SectionRank.le_pRank (p := r) hr.one_lt
      (H := (⊤ : Subgroup (t.Mb))) (E := E3 ⊔ Subgroup.zpowers (fbar t hfM))
      le_top hE4_abel (k := CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) + 1) ?_
    · omega
    · rw [hE4_card, hE3_card, pow_succ]
  have hnotdvd_Kq : ¬ r ∣ Nat.card ↥(t.Kq) := by
    obtain ⟨k, hk⟩ := t.Kq_isPGroup.exists_card_eq
    intro hrdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hk] at hrdvd)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  have hEq : CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) = CFSG.Open.pRank r c.S.M := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r (t.Mb),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr (t.Kq) hnotdvd_Kq,
      CFSG.SectionRank.pRank_coe_eq_openPRank r (t.M)]
  have h4M : 4 ≤ CFSG.Open.pRank r c.S.M := hEq ▸ h4top
  have hrσ : r ∈ c.sig := c.four_le_imp_mem r hr hr2 h4M
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card' (G := ↥t.Ky) r hrK
  let X : Subgroup G := H ⊓ c.S.M
  have hX_le_M : X ≤ t.M := inf_le_right
  have hX_le_H : X ≤ H := inf_le_left
  let qX : ↥X →* t.Mb := (t.qmk).comp (Subgroup.inclusion hX_le_M)
  let fX : ↥X := ⟨f, Subgroup.mem_inf.mpr ⟨hfH, hfM⟩⟩
  have hKyM : t.Ky ≤ t.M := (t.Ky_le.trans inf_le_left).trans c.hyp81.1
  let vX : ↥X := ⟨v, Subgroup.mem_inf.mpr ⟨hKH v.2, hKyM v.2⟩⟩
  have hqg : qX fX = fbar t hfM := rfl
  have hqv : qX vX = t.qmk (kM t v) := rfl
  have hvM_ord : orderOf (kM t v) = r := by
    rw [← Subgroup.orderOf_coe (kM t v)]
    have hcoe : ((kM t v : ↥t.M) : G) = (v : G) := by simp [kM]
    rw [hcoe, Subgroup.orderOf_coe, hvord]
  have hvM_notKq : kM t v ∉ t.Kq :=
    not_mem_Kq_of_orderOf_eq_prime t hr hr2 hvM_ord
  have hvbar_ord : orderOf (t.qmk (kM t v)) = r :=
    orderOf_qmk_eq_of_not_mem_Kq t hr hr2 hvM_ord hvM_notKq
  have hvbar_mem_imageL : t.qmk (kM t v) ∈ (c.L.subgroupOf t.M).map t.qmk :=
    Subgroup.mem_map.mpr ⟨kM t v, (t.Ky_le v.2).1, rfl⟩
  have hvbar_mem_range : t.qmk (kM t v) ∈ qX.range := ⟨vX, hqv⟩
  have hfbar_mem_range : fbar t hfM ∈ qX.range := ⟨fX, hqg⟩
  have hfbar_not_zpowers : fbar t hfM ∉ Subgroup.zpowers (t.qmk (kM t v)) :=
    fun hmem => hfbar_not_mem (Subgroup.zpowers_le.mpr hvbar_mem_imageL hmem)
  have hcomm_gv : fbar t hfM * t.qmk (kM t v) = t.qmk (kM t v) * fbar t hfM := by
    have hz : t.qmk (kM t v) ∈ t.phiKy.range := by
      rw [t.phiKy_range]
      exact Subgroup.mem_map.mpr ⟨kM t v, Subgroup.mem_subgroupOf.mpr v.2, rfl⟩
    have h := fbar_commute_phiKy t hK32 hGA hSp hfM hfK hz
    calc fbar t hfM * t.qmk (kM t v) =
        (fbar t hfM * t.qmk (kM t v) * (fbar t hfM)⁻¹) * fbar t hfM := by group
      _ = t.qmk (kM t v) * fbar t hfM := by rw [h]
  have hcomm_zpowers : ∀ a ∈ Subgroup.zpowers (t.qmk (kM t v)),
      a * fbar t hfM = fbar t hfM * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (show Commute (t.qmk (kM t v)) (fbar t hfM) from hcomm_gv.symm).zpow_left n
      |>.eq
  have hEbar := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := r) (X := Subgroup.zpowers (t.qmk (kM t v))) (v := fbar t hfM)
    (by rw [Nat.card_zpowers, hvbar_ord]) hfbar_ord hfbar_not_zpowers hcomm_zpowers
  have h2range : 2 ≤ CFSG.Open.pRank r qX.range := by
    have hEbar_le : Subgroup.zpowers (t.qmk (kM t v)) ⊔
        Subgroup.zpowers (fbar t hfM) ≤ qX.range :=
      sup_le (Subgroup.zpowers_le.mpr hvbar_mem_range)
        (Subgroup.zpowers_le.mpr hfbar_mem_range)
    exact CFSG.SectionRank.le_pRank hr.one_lt hEbar_le hEbar.1 (k := 2) hEbar.2
  have hker2 : IsPGroup 2 ↥qX.ker := by
    have hcomap2 : IsPGroup 2 ↥((t.Kq).comap (Subgroup.inclusion hX_le_M)) :=
      t.Kq_isPGroup.comap_of_injective (Subgroup.inclusion hX_le_M)
        (Subgroup.inclusion_injective hX_le_M)
    refine hcomap2.to_le ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hrank_eq : CFSG.Open.pRank r (⊤ : Subgroup ↥X) =
      CFSG.Open.pRank r qX.range := by
    have hquot := CFSG.SectionRank.pRank_quotient_two_group (G := ↥X) qX.ker hker2 hr hr2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
        (QuotientGroup.quotientKerEquivRange qX)] at hquot
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r qX.range,
      CFSG.SectionRank.pRank_coe_eq_openPRank r qX.range] at hquot
    exact hquot.symm
  have h2X : 2 ≤ CFSG.Open.pRank r X := by
    have hXeq : CFSG.Open.pRank r X = CFSG.Open.pRank r (⊤ : Subgroup ↥X) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank r X,
        CFSG.SectionRank.pRank_eq_open_pRank_top r ↥X]
    rw [hXeq, hrank_eq]
    exact h2range
  exact c.u2 r hrσ H hH h2X

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
