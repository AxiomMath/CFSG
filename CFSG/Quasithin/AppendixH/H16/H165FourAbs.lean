module

public import CFSG.Quasithin.AppendixH.H16.Vocab
public import CFSG.Quasithin.Background.RonanH163Tconj
public import CFSG.Quasithin.Background.F6Basic

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.Quasithin CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
open CFSG.ASVolI.ChH (cenMS)

variable {V V' : Type*} [CommGroup V] [CommGroup V'] {Γ Γ' : Subgroup P24}

theorem mem_cenMS_iff (ρ : ↥Γ →* MulAut V) (W : Subgroup V) (x : P24) :
    x ∈ cenMS ρ W ↔ ∃ hx : x ∈ Γ, ∀ w ∈ W, ρ ⟨x, hx⟩ w = w := by
  unfold cenMS CFSG.ASVolI.ChH.cenM
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    refine ⟨hyx ▸ y.2, ?_⟩
    intro w hw
    have h1 : ρ y w = w := mem_centSub.mp hy w hw
    have : (⟨x, hyx ▸ y.2⟩ : ↥Γ) = y := Subtype.ext hyx.symm
    rw [this]
    exact h1
  · rintro ⟨hx, hxw⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, mem_centSub.mpr hxw, rfl⟩

theorem mem_fixV_rImg_zpowers (ρ : ↥Γ →* MulAut V) {z : P24} (hz : z ∈ Γ) (w : V) :
    w ∈ fixV (rImg ρ (Subgroup.zpowers z)) ↔ ρ ⟨z, hz⟩ w = w := by
  have hmap : rImg ρ (Subgroup.zpowers z) = Subgroup.zpowers (ρ ⟨z, hz⟩) := by
    unfold rImg
    have hsub : (Subgroup.zpowers z).subgroupOf Γ = Subgroup.zpowers (⟨z, hz⟩ : ↥Γ) := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [hsub, MonoidHom.map_zpowers]
  rw [hmap, mem_fixV]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h x hx
    have hle : Subgroup.zpowers (ρ ⟨z, hz⟩) ≤ MulAction.stabilizer (MulAut V) w := by
      rw [Subgroup.zpowers_le]
      exact h
    exact hle hx

theorem h165_conjSubg_zpowers (c z : P24) :
    conjSubg c (Subgroup.zpowers z) = Subgroup.zpowers (c * z * c⁻¹) := by
  unfold conjSubg
  rw [MonoidHom.map_zpowers]
  congr 1

theorem conjSubg_centralizer (c : P24) (H : Subgroup P24) :
    conjSubg c (Subgroup.centralizer (H : Set P24)) =
      Subgroup.centralizer ((conjSubg c H : Subgroup P24) : Set P24) := by
  ext x
  rw [mem_conjSubg_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hcomm y hy
    have hy' : c⁻¹ * y * c ∈ H := mem_conjSubg_iff.mp hy
    calc y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [hcomm (c⁻¹ * y * c) hy']
      _ = x * y := by group
  · intro hcomm a ha
    calc a * (c⁻¹ * x * c) = c⁻¹ * ((c * a * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * a * c⁻¹)) * c := by
            rw [hcomm (c * a * c⁻¹) (mem_conjSubg_iff.mpr
              (by rw [show c⁻¹ * (c * a * c⁻¹) * c = a by group]; exact ha))]
      _ = (c⁻¹ * x * c) * a := by group

theorem conjSubg_centralizer_singleton (c z : P24) :
    conjSubg c (Subgroup.centralizer ({z} : Set P24)) =
      Subgroup.centralizer ({c * z * c⁻¹} : Set P24) := by
  ext x
  rw [mem_conjSubg_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (c * z * c⁻¹) = c * ((c⁻¹ * x * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = (c * z * c⁻¹) * x := by group
  · intro h
    calc (c⁻¹ * x * c) * z = c⁻¹ * (x * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [h]
      _ = z * (c⁻¹ * x * c) := by group

theorem twoResidual_conjSubg (c : P24) (H : Subgroup P24) :
    twoResidual (conjSubg c H) = conjSubg c (twoResidual H) := by
  have key : ∀ c' : P24, ∀ K : Subgroup P24,
      twoResidual (conjSubg c' K) ≤ conjSubg c' (twoResidual K) := by
    intro c' K
    have hψ' : ∀ t : P24, (MulAut.conj c'⁻¹) t = c'⁻¹ * t * c' := by
      intro t
      rw [MulAut.conj_apply, inv_inv]
    refine twoResidual_le_of_isTwoQuotient ?_ ?_ ?_
    · exact conjSubg_le_conjSubg_iff.mpr (twoResidual_le K)
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_conjSubg_iff, mem_conjSubg_iff]
      have ha : c'⁻¹ * x * c' ∈ K := mem_conjSubg_iff.mp hx
      have hnorm := Subgroup.mem_normalizer_iff.mp
        (le_normalizer_twoResidual K ha) (c'⁻¹ * y * c')
      rw [show c'⁻¹ * (x * y * x⁻¹) * c'
            = (c'⁻¹ * x * c') * (c'⁻¹ * y * c') * (c'⁻¹ * x * c')⁻¹ by group]
      exact hnorm
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient K (c'⁻¹ * y * c')
        (mem_conjSubg_iff.mp hy)
      refine ⟨k, ?_⟩
      rw [mem_conjSubg_iff, ← hψ' (y ^ 2 ^ k), map_pow, hψ' y]
      exact hk
  apply le_antisymm
  · exact key c H
  · have h := key c⁻¹ (conjSubg c H)
    rw [conjSubg_conjSubg_inv] at h
    have h2 : conjSubg c (twoResidual H)
        ≤ conjSubg c (conjSubg c⁻¹ (twoResidual (conjSubg c H))) :=
      conjSubg_le_conjSubg_iff.mpr h
    rwa [conjSubg_inv_conjSubg] at h2

@[expose] def Cen4 (ρ : ↥Γ →* MulAut V) (z : P24) : Prop :=
  cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))) =
      Γ ⊓ Subgroup.centralizer ((twoResidual (Γ ⊓ Subgroup.centralizer ({z} : Set P24)) :
        Subgroup P24) : Set P24) ∧
    IsE2k 2 (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))))

theorem conjSubg_cenMS (c : P24) (hΓ : conjSubg c Γ = Γ') (ρ : ↥Γ →* MulAut V)
    (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ') (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹)
    (e : V ≃* V') (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (W : Subgroup V) :
    conjSubg c (cenMS ρ W) = cenMS ρ' (W.map e.toMonoidHom) := by
  subst hΓ
  ext x
  rw [mem_conjSubg_iff, mem_cenMS_iff, mem_cenMS_iff]
  constructor
  · rintro ⟨hy, hfix⟩
    refine ⟨mem_conjSubg_iff.mpr hy, ?_⟩
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'
    have hxeq : (⟨x, mem_conjSubg_iff.mpr hy⟩ : ↥(conjSubg c Γ)) = φ ⟨c⁻¹ * x * c, hy⟩ := by
      apply Subtype.ext
      rw [hφ]
      group
    rw [hxeq]
    change ρ' (φ ⟨c⁻¹ * x * c, hy⟩) (e w) = e w
    rw [← he ⟨c⁻¹ * x * c, hy⟩ w]
    exact congrArg e (hfix w hw)
  · rintro ⟨hx', hfix'⟩
    refine ⟨mem_conjSubg_iff.mp hx', ?_⟩
    intro w hw
    apply e.injective
    have hxeq : (⟨x, hx'⟩ : ↥(conjSubg c Γ)) =
        φ ⟨c⁻¹ * x * c, mem_conjSubg_iff.mp hx'⟩ := by
      apply Subtype.ext
      rw [hφ]
      group
    rw [he ⟨c⁻¹ * x * c, mem_conjSubg_iff.mp hx'⟩ w, ← hxeq]
    exact hfix' (e w) (Subgroup.mem_map_of_mem e.toMonoidHom hw)

theorem Cen4_of_transport (c : P24) (hΓ : conjSubg c Γ = Γ') (ρ : ↥Γ →* MulAut V)
    (ρ' : ↥Γ' →* MulAut V') (φ : ↥Γ →* ↥Γ') (hφ : ∀ g : ↥Γ, (φ g : P24) = c * g * c⁻¹)
    (e : V ≃* V') (he : ∀ (g : ↥Γ) (v : V), e (ρ g v) = ρ' (φ g) (e v)) (z : P24) :
    Cen4 ρ' (c * z * c⁻¹) → Cen4 ρ z := by
  intro h
  unfold Cen4 at h ⊢
  have hA : (fixV (rImg ρ (Subgroup.zpowers z))).map e.toMonoidHom
      = fixV (rImg ρ' (Subgroup.zpowers (c * z * c⁻¹))) := by
    rw [← h165_conjSubg_zpowers c z, ← rImg_comp c hΓ ρ' φ hφ (Subgroup.zpowers z),
      ← rImg_map ρ (ρ'.comp φ) e he (Subgroup.zpowers z), fixV_map]
  have hB : conjSubg c (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))))
      = cenMS ρ' (fixV (rImg ρ' (Subgroup.zpowers (c * z * c⁻¹)))) := by
    rw [conjSubg_cenMS c hΓ ρ ρ' φ hφ e he (fixV (rImg ρ (Subgroup.zpowers z))), hA]
  have hC : conjSubg c (Γ ⊓ Subgroup.centralizer
        ((twoResidual (Γ ⊓ Subgroup.centralizer ({z} : Set P24)) : Subgroup P24) : Set P24))
      = Γ' ⊓ Subgroup.centralizer
        ((twoResidual (Γ' ⊓ Subgroup.centralizer ({c * z * c⁻¹} : Set P24)) :
          Subgroup P24) : Set P24) := by
    rw [conjSubg_inf, hΓ, conjSubg_centralizer, ← twoResidual_conjSubg, conjSubg_inf, hΓ,
      conjSubg_centralizer_singleton]
  constructor
  · apply conjSubg_inj.mp
    rw [hB, h.1, hC]
  · have h2 := h.2
    rw [← hB] at h2
    exact (IsE2k_conjSubg_iff c 2 (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))))).mp h2

theorem mem_twoResidual_of_pow_eq_one {H : Subgroup P24} {x : P24} (hx : x ∈ H) {n : ℕ}
    (hn : Odd n) (hxn : x ^ n = 1) : x ∈ twoResidual H := by
  exact CFSG.Quasithin.F6.mem_twoResidual_of_odd hx
    (Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one hxn))

theorem le_centralizer_twoResidual_of_sq (H E : Subgroup P24)
    (hHE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E)
    (hsq : ∀ h ∈ H, ∀ e ∈ E, (h * h) * e = e * (h * h)) :
    E ≤ Subgroup.centralizer ((twoResidual H : Subgroup P24) : Set P24) := by
  let N : Subgroup P24 := H ⊓ Subgroup.centralizer (E : Set P24)
  have hNH : N ≤ H := inf_le_left
  have hforward : ∀ a ∈ H, ∀ m ∈ N, a * m * a⁻¹ ∈ N := by
    intro a ha m hm
    refine ⟨H.mul_mem (H.mul_mem ha hm.1) (H.inv_mem ha), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro e he
    have he' : a⁻¹ * e * a ∈ E := by
      have := hHE a⁻¹ (H.inv_mem ha) e he
      simpa using this
    have hm' : (a⁻¹ * e * a) * m = m * (a⁻¹ * e * a) :=
      (Subgroup.mem_centralizer_iff.mp hm.2) (a⁻¹ * e * a) he'
    have hconj : (a * m * a⁻¹) * e * (a * m * a⁻¹)⁻¹ = e := by
      calc (a * m * a⁻¹) * e * (a * m * a⁻¹)⁻¹
          = a * (m * (a⁻¹ * e * a)) * m⁻¹ * a⁻¹ := by group
        _ = a * ((a⁻¹ * e * a) * m) * m⁻¹ * a⁻¹ := by rw [← hm']
        _ = e := by group
    have hcomm : (a * m * a⁻¹) * e = e * (a * m * a⁻¹) := by
      calc (a * m * a⁻¹) * e
          = ((a * m * a⁻¹) * e * (a * m * a⁻¹)⁻¹) * (a * m * a⁻¹) := by group
        _ = e * (a * m * a⁻¹) := by rw [hconj]
    exact hcomm.symm
  have hnorm : H ≤ Subgroup.normalizer (N : Set P24) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hforward h hh n hn
    · intro hn
      have hh' := hforward h⁻¹ (H.inv_mem hh) (h * n * h⁻¹) hn
      simpa [mul_assoc] using hh'
  have h2 : ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y hy
    refine ⟨1, ?_⟩
    have hy2 : y ^ 2 ^ 1 = y * y := by rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
    rw [hy2]
    exact ⟨H.mul_mem hy hy,
      Subgroup.mem_centralizer_iff.mpr (fun e he => (hsq y hy e he).symm)⟩
  have hle : twoResidual H ≤ N := twoResidual_le_of_isTwoQuotient hNH hnorm h2
  intro e he
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro r hr
  have hrN : r ∈ N := hle hr
  exact ((Subgroup.mem_centralizer_iff.mp hrN.2) e he).symm

theorem klein_sq_comm {z d h : P24} {E : Subgroup P24}
    (hE : ∀ x, x ∈ E ↔ x = 1 ∨ x = z ∨ x = d ∨ x = z * d) (hzd : z * d = d * z)
    (hz : z * z = 1) (hd : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z)
    (hhE : ∀ e ∈ E, h * e * h⁻¹ ∈ E) (hhz : h * z = z * h) :
    ∀ e ∈ E, (h * h) * e = e * (h * h) := by
  have hcomm_z : (h * h) * z = z * (h * h) := by
    rw [mul_assoc, hhz, ← mul_assoc, hhz, mul_assoc]
  have hz' : h⁻¹ * z * h = z := by
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [← hhz]
      _ = z := by group
  have hd_mem : h * d * h⁻¹ ∈ E :=
    hhE d ((hE d).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hcomm_d : (h * h) * d = d * (h * h) := by
    rcases (hE (h * d * h⁻¹)).mp hd_mem with h1 | h1 | h1 | h1
    · exfalso
      have hd_eq : d = h⁻¹ * (h * d * h⁻¹) * h := by group
      rw [h1] at hd_eq
      exact hd1 (by simpa using hd_eq)
    · exfalso
      have hd_eq : d = h⁻¹ * (h * d * h⁻¹) * h := by group
      rw [h1, hz'] at hd_eq
      exact hdz hd_eq
    · have hcomm : h * d = d * h := by
        have := congrArg (fun t => t * h) h1
        simpa [mul_assoc] using this
      calc (h * h) * d = h * (h * d) := by group
        _ = h * (d * h) := by rw [hcomm]
        _ = (h * d) * h := by group
        _ = (d * h) * h := by rw [hcomm]
        _ = d * (h * h) := by group
    · have hcomm : h * d = (z * d) * h := by
        have := congrArg (fun t => t * h) h1
        simpa [mul_assoc] using this
      calc (h * h) * d = h * (h * d) := by group
        _ = h * ((z * d) * h) := by rw [hcomm]
        _ = (h * (z * d)) * h := by group
        _ = ((h * z) * d) * h := by group
        _ = ((z * h) * d) * h := by rw [hhz]
        _ = (z * (h * d)) * h := by group
        _ = (z * ((z * d) * h)) * h := by rw [hcomm]
        _ = ((z * z) * d) * (h * h) := by group
        _ = d * (h * h) := by rw [hz]; group
  have hcomm_zd : (h * h) * (z * d) = (z * d) * (h * h) := by
    calc (h * h) * (z * d) = ((h * h) * z) * d := by group
      _ = (z * (h * h)) * d := by rw [hcomm_z]
      _ = z * ((h * h) * d) := by group
      _ = z * (d * (h * h)) := by rw [hcomm_d]
      _ = (z * d) * (h * h) := by group
  intro e he
  rcases (hE e).mp he with rfl | rfl | rfl | rfl
  · group
  · exact hcomm_z
  · exact hcomm_d
  · exact hcomm_zd

theorem conj_mem_cenMS_fixV (ρ : ↥Γ →* MulAut V) {z h x : P24} (hz : z ∈ Γ) (hh : h ∈ Γ)
    (hhz : h * z = z * h) (hx : x ∈ cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z)))) :
    h * x * h⁻¹ ∈ cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))) := by
  set W : Subgroup V := fixV (rImg ρ (Subgroup.zpowers z)) with hW
  obtain ⟨hxΓ, hfix⟩ := (mem_cenMS_iff ρ W x).mp hx
  have hhinv : h⁻¹ ∈ Γ := Γ.inv_mem hh
  have hmem : h * x * h⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hh hxΓ) hhinv
  refine (mem_cenMS_iff ρ W (h * x * h⁻¹)).mpr ⟨hmem, ?_⟩
  intro w hw
  set w' : V := ρ ⟨h⁻¹, hhinv⟩ w with hw'def
  have hw' : w' ∈ W := by
    rw [hW, mem_fixV_rImg_zpowers ρ hz]
    have hzh : (⟨z, hz⟩ : ↥Γ) * ⟨h⁻¹, hhinv⟩ = ⟨h⁻¹, hhinv⟩ * ⟨z, hz⟩ := by
      apply Subtype.ext
      have hzh' : z * h⁻¹ = h⁻¹ * z := by
        calc z * h⁻¹ = h⁻¹ * (h * z) * h⁻¹ := by group
          _ = h⁻¹ * (z * h) * h⁻¹ := by rw [hhz]
          _ = h⁻¹ * z := by group
      simpa using hzh'
    calc ρ ⟨z, hz⟩ w'
        = ρ (⟨z, hz⟩ * ⟨h⁻¹, hhinv⟩) w := by rw [map_mul, MulAut.mul_apply]
      _ = ρ (⟨h⁻¹, hhinv⟩ * ⟨z, hz⟩) w := by rw [hzh]
      _ = ρ ⟨h⁻¹, hhinv⟩ (ρ ⟨z, hz⟩ w) := by rw [map_mul, MulAut.mul_apply]
      _ = ρ ⟨h⁻¹, hhinv⟩ w := by rw [(mem_fixV_rImg_zpowers ρ hz w).mp hw]
  calc ρ ⟨h * x * h⁻¹, hmem⟩ w
      = ρ ⟨h, hh⟩ (ρ ⟨x, hxΓ⟩ (ρ ⟨h⁻¹, hhinv⟩ w)) := by
        rw [show (⟨h * x * h⁻¹, hmem⟩ : ↥Γ)
              = ⟨h, hh⟩ * ⟨x, hxΓ⟩ * ⟨h⁻¹, hhinv⟩ by apply Subtype.ext; rfl,
          map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    _ = ρ ⟨h, hh⟩ w' := by rw [hfix w' hw']
    _ = w := by
        rw [hw'def]
        rw [← MulAut.mul_apply, ← map_mul,
          show (⟨h, hh⟩ * ⟨h⁻¹, hhinv⟩ : ↥Γ) = 1 by ext; simp, map_one]
        rfl

theorem klein_mul_mem {X : Type*} [Group X] {z d : X} (hz : z * z = 1) (hd : d * d = 1)
    (hzd : z * d = d * z) {a b : X} (ha : a = 1 ∨ a = z ∨ a = d ∨ a = z * d)
    (hb : b = 1 ∨ b = z ∨ b = d ∨ b = z * d) :
    a * b = 1 ∨ a * b = z ∨ a * b = d ∨ a * b = z * d := by
  have hzd' : d * z = z * d := hzd.symm
  have hzzd : z * (z * d) = d := by rw [← mul_assoc, hz, one_mul]
  have hdzd : d * (z * d) = z := by rw [← mul_assoc, ← hzd, mul_assoc, hd, mul_one]
  have hzdz : (z * d) * z = d := by rw [hzd, mul_assoc, hz, mul_one]
  have hzdd : (z * d) * d = z := by rw [mul_assoc, hd, mul_one]
  have hzdzd : (z * d) * (z * d) = 1 := by rw [← mul_assoc, hzdz, hd]
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;>
    rw [ha, hb] <;>
    simp [hz, hd, hzd', hzzd, hdzd, hzdz, hzdd, hzdzd]

theorem klein_inv_mem {X : Type*} [Group X] {z d : X} (hz : z * z = 1) (hd : d * d = 1)
    (hzd : z * d = d * z) {a : X} (ha : a = 1 ∨ a = z ∨ a = d ∨ a = z * d) :
    a⁻¹ = 1 ∨ a⁻¹ = z ∨ a⁻¹ = d ∨ a⁻¹ = z * d := by
  rcases ha with rfl | rfl | rfl | rfl
  · left; simp
  · right; left
    exact inv_eq_of_mul_eq_one_right hz
  · right; right; left
    exact inv_eq_of_mul_eq_one_right hd
  · right; right; right
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right hd]
    exact hzd.symm

@[expose] def kleinSubgroup {X : Type*} [Group X] (z d : X) (hz : z * z = 1) (hd : d * d = 1)
    (hzd : z * d = d * z) : Subgroup X where
  carrier := {a | a = 1 ∨ a = z ∨ a = d ∨ a = z * d}
  mul_mem' := fun {_ _} ha hb => klein_mul_mem hz hd hzd ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {_} ha => klein_inv_mem hz hd hzd ha

theorem mem_kleinSubgroup_iff {X : Type*} [Group X] {z d : X} (hz : z * z = 1) (hd : d * d = 1)
    (hzd : z * d = d * z) (a : X) :
    a ∈ kleinSubgroup z d hz hd hzd ↔ a = 1 ∨ a = z ∨ a = d ∨ a = z * d := Iff.rfl

theorem isE2k_kleinSubgroup {z d : P24} (hz : z * z = 1) (hd : d * d = 1) (hzd : z * d = d * z)
    (hz1 : z ≠ 1) (hd1 : d ≠ 1) (hdz : d ≠ z) : IsE2k 2 (kleinSubgroup z d hz hd hzd) := by
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzd1 : z * d ≠ 1 := by
    intro h
    have hdz_eq : d = z := by rw [← inv_eq_of_mul_eq_one_right h, hz_inv]
    exact hdz hdz_eq
  have hzzd : z ≠ z * d := by
    intro h
    have h2 : z * 1 = z * d := by simpa using h
    exact hd1 ((mul_left_cancel_iff.mp h2).symm)
  have hdzd : d ≠ z * d := by
    intro h
    have h2 : d * d⁻¹ = (z * d) * d⁻¹ := congrArg (fun t => t * d⁻¹) h
    have : (1 : P24) = z := by simpa [mul_assoc] using h2
    exact hz1 this.symm
  have hset : (kleinSubgroup z d hz hd hzd : Set P24) = {1, z, d, z * d} := by
    ext x
    change x ∈ kleinSubgroup z d hz hd hzd ↔ x ∈ ({1, z, d, z * d} : Set P24)
    rw [mem_kleinSubgroup_iff]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  unfold IsE2k CFSG.Open.IsElemAbelian
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hzd' : d * z = z * d := hzd.symm
    have hzzd : z * (z * d) = d := by rw [← mul_assoc, hz, one_mul]
    have hdzd : d * (z * d) = z := by rw [← mul_assoc, ← hzd, mul_assoc, hd, mul_one]
    have hzdz : (z * d) * z = d := by rw [hzd, mul_assoc, hz, mul_one]
    have hzdd : (z * d) * d = z := by rw [mul_assoc, hd, mul_one]
    have hzdzd : (z * d) * (z * d) = 1 := by rw [← mul_assoc, hzdz, hd]
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    change (a : P24) * (b : P24) = (b : P24) * (a : P24)
    rcases (mem_kleinSubgroup_iff hz hd hzd a.1).mp a.2 with ha | ha | ha | ha <;>
      rcases (mem_kleinSubgroup_iff hz hd hzd b.1).mp b.2 with hb | hb | hb | hb <;>
      rw [ha, hb] <;>
      simp [hz, hd, hzd', hzzd, hdzd, hzdz, hzdd, hzdzd]
  · intro x hx
    rcases (mem_kleinSubgroup_iff hz hd hzd x).mp hx with h | h | h | h
    · rw [h]; simp
    · rw [h, pow_two]; exact hz
    · rw [h, pow_two]; exact hd
    · rw [h, pow_two]
      calc (z * d) * (z * d) = z * (d * z) * d := by group
        _ = z * (z * d) * d := by rw [← hzd]
        _ = (z * z) * (d * d) := by group
        _ = 1 := by rw [hz, hd, one_mul]
  · change Nat.card ↥(kleinSubgroup z d hz hd hzd : Set P24) = 2 ^ 2
    rw [Nat.card_coe_set_eq, hset]
    have h1 : (1 : P24) ∉ ({z, d, z * d} : Set P24) := by
      intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · exact hz1 h.symm
      · exact hd1 h.symm
      · exact hzd1 h.symm
    have h2 : z ∉ ({d, z * d} : Set P24) := by
      intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact hdz h.symm
      · exact hzzd h
    have h3 : d ∉ ({z * d} : Set P24) := by
      intro hx
      simp only [Set.mem_singleton_iff] at hx
      exact hdzd hx
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
    norm_num

end CFSG.ASVolI.H16
