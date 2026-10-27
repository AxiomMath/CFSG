module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameLine
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndLift

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.StandardType CFSG.StandardType.SpFrame CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G] [Finite G]

private lemma mul_comm_of_mem {p : ℕ} {Bs : Subgroup G} (h : IsElemAbelian p Bs)
    {a b : G} (ha : a ∈ Bs) (hb : b ∈ Bs) : a * b = b * a :=
  congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private lemma zpowers_le_of_mem_zpowers_of_prime {p : ℕ} (hp : p.Prime) {y z : G}
    (hpow : y ^ p = 1) (hz1 : z ≠ 1) (hz : z ∈ Subgroup.zpowers y) :
    Subgroup.zpowers y ≤ Subgroup.zpowers z := by
  have hy1 : y ≠ 1 := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [hy] at hk
    exact hz1 (by simpa using hk.symm)
  have hop : orderOf y = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hzord : orderOf z = p := by
    have hdvd : orderOf z ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers y) hz
      rwa [Nat.card_zpowers, hop] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hz
  have hcard : Nat.card ↥(Subgroup.zpowers y) ≤ Nat.card ↥(Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hop, hzord]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge

theorem spEnd_eq_one_of_frame_inv {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hrank : Nat.card Bs = p ^ (m + 1))
    {A : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1)) A)
    {X Y : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) (hYA : ggAutomizer Y Bs ≤ A)
    (hXc : 2 ^ m * m.factorial ≤ Nat.card (ggAutomizer X Bs))
    (hYc : 2 ^ m * m.factorial ≤ Nat.card (ggAutomizer Y Bs)) {z₁ z : G} (hz₁ : z₁ ∈ Bs)
    (hz : z ∈ Bs) (hz₁X : z₁ ∈ Subgroup.centralizer (X : Set G))
    (hzY : z ∈ Subgroup.centralizer (Y : Set G)) (hz₁1 : z₁ ≠ 1)
    (hzz₁ : z ∉ Subgroup.zpowers z₁) {u c s : G} (hu : u ∈ Bs) (hc : c ∈ Subgroup.zpowers z₁)
    (hzuc : z = u * c) (hsX : s ∈ X) (hsN : s ∈ Subgroup.normalizer (Bs : Set G))
    (hsu : s * u * s⁻¹ = u⁻¹) : c = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcB : c ∈ Bs := (Subgroup.zpowers_le.mpr hz₁) hc
  set z' : G := s * z * s⁻¹ with hz'def
  have hz' : z' ∈ Bs := by
    rw [hz'def]
    exact (Subgroup.mem_normalizer_iff.mp hsN z).mp hz
  have hsz₁ : s * z₁ * s⁻¹ = z₁ := by
    rw [Subgroup.mem_centralizer_iff.mp hz₁X s hsX]
    group
  have hcX : c ∈ Subgroup.centralizer (X : Set G) := (Subgroup.zpowers_le.mpr hz₁X) hc
  have hsc : s * c * s⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hcX s hsX]
    group
  have hz'_eq : z' = u⁻¹ * c := by
    rw [hz'def, hzuc]
    calc s * (u * c) * s⁻¹ = (s * u * s⁻¹) * (s * c * s⁻¹) := by group
      _ = u⁻¹ * c := by rw [hsu, hsc]
  let σ : MulAut ↥Bs := Subgroup.normalizerMonoidHom (H := Bs) ⟨s, hsN⟩
  have hσA : σ ∈ A :=
    hXA (Subgroup.subset_closure ⟨s, hsX, hsN, fun b => rfl⟩)
  have hz'σ : σ ⟨z, hz⟩ = ⟨z', hz'⟩ := by
    apply Subtype.ext
    show s * z * s⁻¹ = z'
    exact hz'def.symm
  have hσinz : σ⁻¹ ⟨z', hz'⟩ = ⟨z, hz⟩ := by
    apply (MulEquiv.injective σ)
    change σ (σ.symm ⟨z', hz'⟩) = σ ⟨z, hz⟩
    rw [MulEquiv.apply_symm_apply]
    exact hz'σ.symm
  let Hz : Subgroup (MulAut ↥Bs) := (ggAutomizer Y Bs).map (MulAut.conj σ).toMonoidHom
  have hHz : Hz ≤ A := by
    intro ψ hψ
    rcases Subgroup.mem_map.mp hψ with ⟨φ, hφ, rfl⟩
    change σ * φ * σ⁻¹ ∈ A
    exact A.mul_mem (A.mul_mem hσA (hYA hφ)) (A.inv_mem hσA)
  have hcz : 2 ^ m * m.factorial ≤ Nat.card Hz := by
    have hcard : Nat.card Hz = Nat.card (ggAutomizer Y Bs) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj σ).toMonoidHom)
        (fun a b hab => (MulEquiv.injective (MulAut.conj σ)) hab)
    rw [hcard]
    exact hYc
  have hfz : ∀ ψ ∈ Hz, ((ψ ⟨z', hz'⟩ : ↥Bs) : G) = z' := by
    intro ψ hψ
    rcases Subgroup.mem_map.mp hψ with ⟨φ, hφ, rfl⟩
    have hφfix : φ ⟨z, hz⟩ = ⟨z, hz⟩ := by
      apply Subtype.ext
      exact ggAutomizer_fixes_of_mem_centralizer hz hzY φ hφ
    have h1 : ((MulAut.conj σ).toMonoidHom) φ = (MulAut.conj σ) φ := rfl
    have h2 : (σ * φ * σ⁻¹) ⟨z', hz'⟩ = σ ⟨z, hz⟩ := by
      rw [show (σ * φ * σ⁻¹) ⟨z', hz'⟩ = σ (φ (σ⁻¹ ⟨z', hz'⟩)) from rfl,
        hσinz, hφfix]
    rw [h1, MulAut.conj_apply, h2]
    exact congrArg (fun w : ↥Bs => (w : G)) hz'σ
  have hz'not : z' ∉ Subgroup.zpowers z₁ := by
    intro hmem
    apply hzz₁
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    have hz1conj' : s⁻¹ * z₁ * s = z₁ := by
      calc s⁻¹ * z₁ * s = s⁻¹ * (s * z₁ * s⁻¹) * s := by rw [hsz₁]
        _ = z₁ := by group
    have hz_eq : z = s⁻¹ * z' * s := by
      rw [hz'def]
      group
    rw [hz_eq, ← hk]
    have hconj : s⁻¹ * z₁ ^ k * s = (s⁻¹ * z₁ * s) ^ k := by
      have h := map_zpow (MulAut.conj s⁻¹) z₁ k
      simpa [MulAut.conj_apply] using h
    rw [hconj, hz1conj']
  have hzD : z' ∈ Subgroup.closure ({z₁, z} : Set G) := by
    have hz₁D : z₁ ∈ Subgroup.closure ({z₁, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzD' : z ∈ Subgroup.closure ({z₁, z} : Set G) := Subgroup.subset_closure (by simp)
    have hcD : c ∈ Subgroup.closure ({z₁, z} : Set G) := (Subgroup.zpowers_le.mpr hz₁D) hc
    have hu_eq : u = z * c⁻¹ := by
      rw [hzuc]
      group
    have huD : u ∈ Subgroup.closure ({z₁, z} : Set G) := by
      rw [hu_eq]
      exact Subgroup.mul_mem _ hzD' (Subgroup.inv_mem _ hcD)
    rw [hz'_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huD) hcD
  have hframe : Subgroup.zpowers z' = Subgroup.zpowers z :=
    zpowers_eq_of_frame (Hx := ggAutomizer X Bs) (Hy := ggAutomizer Y Bs) (Hz := Hz)
      (x := z₁) (y := z) (z := z')
      hp hp2 hm hBs hrank hA hXA hYA hHz hz₁ hz hz'
      (ggAutomizer_fixes_of_mem_centralizer hz₁ hz₁X)
      (ggAutomizer_fixes_of_mem_centralizer hz hzY) hfz hXc hYc hcz hz₁1 hzz₁ hz'not hzD
  have hz'z : z' ∈ Subgroup.zpowers z := by
    have hmem := Subgroup.mem_zpowers z'
    rwa [hframe] at hmem
  have hcu : c * u⁻¹ = u⁻¹ * c := mul_comm_of_mem hBs hcB (Subgroup.inv_mem Bs hu)
  have hzc : z * z' = c ^ 2 := by
    rw [hzuc, hz'_eq]
    calc (u * c) * (u⁻¹ * c) = u * (c * u⁻¹) * c := by group
      _ = u * (u⁻¹ * c) * c := by rw [hcu]
      _ = c ^ 2 := by
        rw [pow_two]
        group
  have hc2_z : c ^ 2 ∈ Subgroup.zpowers z := by
    rw [← hzc]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers z) hz'z
  have hc2_z1 : c ^ 2 ∈ Subgroup.zpowers z₁ := Subgroup.pow_mem (Subgroup.zpowers z₁) hc 2
  have hc2_eq_one : c ^ 2 = 1 := by
    by_contra hne
    have hzmem : z ∈ Subgroup.zpowers (c ^ 2) :=
      zpowers_le_of_mem_zpowers_of_prime hp (hBs.2 z hz) hne hc2_z (Subgroup.mem_zpowers z)
    have hle : Subgroup.zpowers (c ^ 2) ≤ Subgroup.zpowers z₁ := Subgroup.zpowers_le.mpr hc2_z1
    exact hzz₁ (hle hzmem)
  have hop1 : orderOf z₁ = p := orderOf_eq_prime (hBs.2 z₁ hz₁) hz₁1
  have hdvd_p : orderOf c ∣ p := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z₁) hc
    rwa [Nat.card_zpowers, hop1] at h
  have hdvd_2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2_eq_one
  rcases (Nat.dvd_prime hp).mp hdvd_p with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have hp_dvd_two : p ∣ 2 := h1 ▸ hdvd_2
    have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two
    have hpge2 : 2 ≤ p := hp.two_le
    omega

theorem spEnd_mem_of_counting_frame {F : Type} [Field F] [Finite F] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 3 ≤ m) (h2 : (2 : F) = 0) {B Bs X Y : Subgroup G} (hBs : GGBstar p B Bs)
    (φ' : StatedSp (m + 1) F →* G) (hinj : Function.Injective φ') (hrange : φ'.range = X)
    (hNX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : Nat.card Bs = p ^ (m + 1 + 1)) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) A) (hXA : ggAutomizer X Bs ≤ A)
    (hYA : ggAutomizer Y Bs ≤ A)
    (hXc : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer X Bs))
    (hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer Y Bs)) {z z₁ : G}
    (hz : z ∈ Bs) (hzY : z ∈ Subgroup.centralizer (Y : Set G))
    (hzX : z ∉ Subgroup.centralizer (X : Set G)) (hz₁ : z₁ ∈ Bs)
    (hz₁X : z₁ ∈ Subgroup.centralizer (X : Set G)) (hz₁1 : z₁ ≠ 1)
    (hBsC : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z₁)
    (hzz₁ : z ∉ Subgroup.zpowers z₁) : z ∈ X := by
  classical
  obtain ⟨ψ, g, c, _hψinj, hψrange, hcCX, hcBs, hz_eq, s, hsX, hsN, hsu⟩ :=
    spEnd_exists_lift_lam_zero_mul_inv hp hp2 hm h2 hBs φ' hinj hrange hNX hinner hcent
      hrank.ge hA hXA hYA hY hz hzY hzX
  have huBs : ψ (lam (0 : Fin (m + 1)) g) ∈ Bs := by
    have : ψ (lam (0 : Fin (m + 1)) g) = z * c⁻¹ := by
      rw [hz_eq]
      group
    rw [this]
    exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hcBs)
  have hc_z1 : c ∈ Subgroup.zpowers z₁ := by
    have hmem : c ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := ⟨hcBs, hcCX⟩
    rwa [hBsC] at hmem
  have hc1 : c = 1 :=
    spEnd_eq_one_of_frame_inv (m := m + 1) hp hp2 (by omega) hBs.2.1 hrank hA hXA hYA hXc hY
      hz₁ hz hz₁X hzY hz₁1 hzz₁ huBs hc_z1 hz_eq hsX hsN hsu
  rw [hc1, mul_one] at hz_eq
  rw [← hψrange]
  exact ⟨lam (0 : Fin (m + 1)) g, hz_eq.symm⟩

end CFSG.StandardType.SpJoin
