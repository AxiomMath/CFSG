module

public import CFSG.Quasithin.Recognition.HSType17d
public import CFSG.Quasithin.Recognition.HSTypeL12j

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem perm_five_no_q8 : ∀ σ τ : Equiv.Perm (Fin 5), σ ^ 4 = 1 → σ ^ 2 = τ ^ 2 →
    τ * σ = σ⁻¹ * τ → σ ^ 2 = 1 := by
  decide +kernel

theorem quaternion_gens :
    (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 ∧
      (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.xa 0 ^ 2 ∧
      (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
        (QuaternionGroup.a 1)⁻¹ * QuaternionGroup.xa 0 ∧
      (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by
  decide

theorem quaternion_center :
    ∀ x : QuaternionGroup 2, x * QuaternionGroup.a 1 ^ 2 = QuaternionGroup.a 1 ^ 2 * x := by
  decide

theorem quaternion_rel {G : Type*} [Group G] {ψ : QuaternionGroup 2 →* G}
    (hψ : Function.Injective ψ) :
    ψ (QuaternionGroup.a 1) ^ 4 = 1 ∧
      ψ (QuaternionGroup.a 1) ^ 2 = ψ (QuaternionGroup.xa 0) ^ 2 ∧
      ψ (QuaternionGroup.xa 0) * ψ (QuaternionGroup.a 1) =
        (ψ (QuaternionGroup.a 1))⁻¹ * ψ (QuaternionGroup.xa 0) ∧
      ψ (QuaternionGroup.a 1) ^ 2 ≠ 1 := by
  obtain ⟨h4, h2, hji, h1⟩ := quaternion_gens
  refine ⟨by rw [← map_pow, h4, map_one], by rw [← map_pow, ← map_pow, h2],
    by rw [← map_mul, hji, map_mul, map_inv], fun he => h1 (hψ ?_)⟩
  rw [map_pow, he, map_one]

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

section SPrimeQ

variable (h : HSSetting z V) {t s : G} (htK : t ∈ hsK z) (htQ : t ∉ hsQ z)
  (htt : t * t = 1) {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)}
  (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) (hφt : φ ⟨t, htK.1⟩ = t₅)

include h htQ htt hker hφt in
theorem mem_Q_or_of_mem_sPrime [Finite G] (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z)
    (hss : s * s = 1) (hst : s * t = t * s) (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1) {y : G}
    (hy : y ∈ sPrime φ t) (hy2 : y * y ≠ 1) : y ∈ hsQ z ∨ t⁻¹ * y ∈ hsQ z := by
  obtain ⟨hyt, hyH, hyV⟩ := hy
  have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
  have hmem : ∀ a : ↥(hsH z), φ a = 1 ↔ (a : G) ∈ hsQ z := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hinvq : ∀ q : G, q ∈ hsQ z → q * t = t * q → s * q * s⁻¹ = q⁻¹ := fun q hq hqt =>
    h.inv_of_mem_CQt htK htQ htt hsmemH hsK hss hst hq hqt
  rcases inV5_cases hyV with h1 | h1 | h1 | h1
  · exact Or.inl ((hmem _).mp h1)
  ·
    exfalso
    apply hy2
    have hq : s⁻¹ * y ∈ hsQ z := by
      have : φ ⟨s⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ hsmemH) hyH⟩ = 1 := by
        rw [show (⟨s⁻¹ * y, _⟩ : ↥(hsH z)) = (⟨s, hsmemH⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul,
          map_inv, hφs, h1, inv_mul_cancel]
      exact (hmem _).mp this
    have hqt : s⁻¹ * y * t = t * (s⁻¹ * y) := by
      rw [hsinv, mul_assoc, hyt', ← mul_assoc, hst, mul_assoc]
    have e := hinvq _ hq hqt
    calc y * y = s * (s⁻¹ * y) * (s * (s⁻¹ * y)) := by group
      _ = (s * (s⁻¹ * y) * s⁻¹) * (s * s) * (s⁻¹ * y) := by group
      _ = 1 := by rw [e, hss, mul_one, inv_mul_cancel]
  ·
    exfalso
    apply hy2
    have hq : (s * t)⁻¹ * y ∈ hsQ z := by
      have : φ ⟨(s * t)⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _
          (Subgroup.mul_mem _ hsmemH htK.1)) hyH⟩ = 1 := by
        rw [show (⟨(s * t)⁻¹ * y, _⟩ : ↥(hsH z)) =
            (⟨s, hsmemH⟩ * ⟨t, htK.1⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul, map_inv, map_mul, hφs,
          hφt, h1, swap23_eq, inv_mul_cancel]
      exact (hmem _).mp this
    set q := (s * t)⁻¹ * y with hqdef
    have hqt : q * t = t * q := by
      rw [hqdef, mul_inv_rev, htinv, hsinv]
      calc t * s * y * t = t * s * (y * t) := by group
        _ = t * s * (t * y) := by rw [hyt']
        _ = t * (s * t) * y := by group
        _ = t * (t * s) * y := by rw [hst]
        _ = t * (t * s * y) := by group
    have e := hinvq _ hq hqt
    have hy' : y = s * t * q := by rw [hqdef]; group
    rw [hy']
    have hsq : s * q = q⁻¹ * s := by
      calc s * q = s * q * s⁻¹ * s := by group
        _ = q⁻¹ * s := by rw [e]
    calc s * t * q * (s * t * q) = s * (t * q) * s * (t * q) := by group
      _ = s * (q * t) * s * (q * t) := by rw [hqt]
      _ = (s * q) * (t * s) * q * t := by group
      _ = (q⁻¹ * s) * (s * t) * q * t := by rw [hsq, hst]
      _ = q⁻¹ * (s * s) * t * q * t := by group
      _ = q⁻¹ * (t * q) * t := by rw [hss]; group
      _ = q⁻¹ * (q * t) * t := by rw [hqt]
      _ = 1 := by rw [← mul_assoc, inv_mul_cancel, one_mul, htt]
  · right
    have : φ ⟨t⁻¹ * y, Subgroup.mul_mem _ (Subgroup.inv_mem _ htK.1) hyH⟩ = 1 := by
      rw [show (⟨t⁻¹ * y, _⟩ : ↥(hsH z)) = (⟨t, htK.1⟩)⁻¹ * ⟨y, hyH⟩ from rfl, map_mul,
        map_inv, hφt, h1, inv_mul_cancel]
    exact (hmem _).mp this

include h htK htQ htt in
theorem comm_of_mem_CQt [Finite G] (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z) (hss : s * s = 1)
    (hst : s * t = t * s) {q₁ q₂ : G} (hq₁ : q₁ ∈ hsQ z) (hq₂ : q₂ ∈ hsQ z)
    (hq₁t : q₁ * t = t * q₁) (hq₂t : q₂ * t = t * q₂) : q₁ * q₂ = q₂ * q₁ := by
  have e1 := h.inv_of_mem_CQt htK htQ htt hsmemH hsK hss hst hq₁ hq₁t
  have e2 := h.inv_of_mem_CQt htK htQ htt hsmemH hsK hss hst hq₂ hq₂t
  have e12 := h.inv_of_mem_CQt htK htQ htt hsmemH hsK hss hst ((hsQ z).mul_mem hq₁ hq₂)
    (by rw [mul_assoc, hq₂t, ← mul_assoc, hq₁t, mul_assoc])
  have hinv : (q₁ * q₂)⁻¹ = q₁⁻¹ * q₂⁻¹ := by
    rw [← e12, ← e1, ← e2]
    group
  calc q₁ * q₂ = ((q₁ * q₂)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (q₁⁻¹ * q₂⁻¹)⁻¹ := by rw [hinv]
    _ = q₂ * q₁ := by group

include h htQ htt hker hφt in
theorem comm_of_mem_sPrime [Finite G] (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z)
    (hss : s * s = 1) (hst : s * t = t * s) (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1) {a b : G}
    (ha : a ∈ sPrime φ t) (hb : b ∈ sPrime φ t) (ha2 : a * a ≠ 1) (hb2 : b * b ≠ 1) :
    a * b = b * a := by
  have key : ∀ y : G, y ∈ sPrime φ t → y * y ≠ 1 →
      ∃ q ∈ hsQ z, q * t = t * q ∧ (y = q ∨ y = t * q) := by
    intro y hy hy2
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy.1
    rcases h.mem_Q_or_of_mem_sPrime htK htQ htt hker hφt hsmemH hsK hss hst hφs hy hy2 with
      hq | hq
    · exact ⟨y, hq, hyt, Or.inl rfl⟩
    · refine ⟨t⁻¹ * y, hq, ?_, Or.inr (by group)⟩
      rw [mul_assoc, hyt]
      group
  obtain ⟨p, hp, hpt, hap⟩ := key a ha ha2
  obtain ⟨q, hq, hqt, hbq⟩ := key b hb hb2
  have hpq : Commute p q := h.comm_of_mem_CQt htK htQ htt hsmemH hsK hss hst hp hq hpt hqt
  have hpt' : Commute p t := hpt
  have hqt' : Commute q t := hqt
  have hc : Commute a b := by
    rcases hap with rfl | rfl <;> rcases hbq with rfl | rfl
    · exact hpq
    · exact hpt'.mul_right hpq
    · exact hqt'.symm.mul_left hpq
    · exact ((Commute.refl t).mul_right hqt'.symm).mul_left (hpt'.mul_right hpq)
  exact hc.eq

end SPrimeQ

theorem exists_conj_mem_CHt [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t) {E : Subgroup G}
    (hE : IsPGroup 2 E) (hEC : E ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G),
      ∀ x ∈ E, c * x * c⁻¹ ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set T := hsH z ⊓ C with hT
  have hT64 := h.card_centralizer_H_of_invol_K htK htQ htt
  have hTp : IsPGroup 2 (T.subgroupOf C) := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hT64]
    norm_num
  have hodd := h.not_two_dvd_relIndex_T htK htQ htt htz
  set ST : Sylow 2 ↥C := hTp.toSylow hodd with hST
  have hEp : IsPGroup 2 (E.subgroupOf C) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  obtain ⟨P, hP⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P ST
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxP : (⟨x, hEC hx⟩ : ↥C) ∈ P := hP (Subgroup.mem_subgroupOf.mpr hx)
  have hmem : c * ⟨x, hEC hx⟩ * c⁻¹ ∈ c • P := by
    rw [mem_smul_sylow', show c⁻¹ * (c * ⟨x, hEC hx⟩ * c⁻¹) * c = ⟨x, hEC hx⟩ by group]
    exact hxP
  rw [hc] at hmem
  have hmem' : c * ⟨x, hEC hx⟩ * c⁻¹ ∈ T.subgroupOf C := hmem
  rw [Subgroup.mem_subgroupOf] at hmem'
  simpa using hmem'

theorem exists_e_of_quaternion [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    (hφt : φ ⟨t, htK.1⟩ = t₅) {s : G} (hsmemH : s ∈ hsH z) (hsK : s ∉ hsK z)
    (hss : s * s = 1) (hst : s * t = t * s) (hφs : φ ⟨s, hsmemH⟩ = Equiv.swap 0 1)
    {E : Subgroup G} (hEC : E ≤ Subgroup.centralizer ({t} : Set G))
    (eE : ↥E ≃* QuaternionGroup 2) :
    ∃ e ∈ hsH z ⊓ Subgroup.centralizer ({t} : Set G), e ∉ sPrime φ t ∧ e ^ 4 = 1 ∧
      IsConj z (e * e) ∧
        (e * e = z ∨ ∀ g ∈ Subgroup.centralizer ({t} : Set G), g * z * g⁻¹ ≠ e * e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set T := hsH z ⊓ C with hT
  set ia : QuaternionGroup 2 := QuaternionGroup.a 1 with hia
  set ja : QuaternionGroup 2 := QuaternionGroup.xa 0 with hja
  set ψ : QuaternionGroup 2 →* G := E.subtype.comp eE.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := E.subtype_injective.comp eE.symm.injective
  have hψE : ∀ x, ψ x ∈ E := fun x => (eE.symm x).2
  have hEp : IsPGroup 2 E := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr eE.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨c, hcC, hcT⟩ := h.exists_conj_mem_CHt htK htQ htt htz hEp hEC
  set ψ₁ : QuaternionGroup 2 →* G := (MulAut.conj c).toMonoidHom.comp ψ with hψ₁
  have hψ₁inj : Function.Injective ψ₁ := (MulAut.conj c).injective.comp hψinj
  have hψ₁T : ∀ x, ψ₁ x ∈ T := fun x => hcT _ (hψE x)
  obtain ⟨ψ₂, hψ₂inj, hψ₂T, hψ₂z⟩ : ∃ ψ₂ : QuaternionGroup 2 →* G, Function.Injective ψ₂ ∧
      (∀ x, ψ₂ x ∈ T) ∧ (ψ₂ ia ^ 2 = z ∨ ∀ g ∈ C, g * z * g⁻¹ ≠ ψ₂ ia ^ 2) := by
    by_cases hconj : ∃ a ∈ C, a * z * a⁻¹ = ψ₁ ia ^ 2
    · obtain ⟨a, haC, ha⟩ := hconj
      set ψ₂ : QuaternionGroup 2 →* G := (MulAut.conj a⁻¹).toMonoidHom.comp ψ₁ with hψ₂
      have hψ₂a : ∀ x, ψ₂ x = a⁻¹ * ψ₁ x * a := fun x => by
        simp [hψ₂]
      have hz : ψ₂ ia ^ 2 = z := by
        rw [← map_pow, hψ₂a, map_pow, ← ha]
        group
      refine ⟨ψ₂, (MulAut.conj a⁻¹).injective.comp hψ₁inj, fun x => ?_, Or.inl hz⟩
      have hxC : ψ₂ x ∈ C := by
        rw [hψ₂a]
        exact C.mul_mem (C.mul_mem (C.inv_mem haC) (hψ₁T x).2) haC
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hxC⟩
      rw [← hz, ← map_pow, ← map_mul, ← map_mul, quaternion_center]
    · push Not at hconj
      exact ⟨ψ₁, hψ₁inj, hψ₁T, Or.inr hconj⟩
  obtain ⟨hi4, hij, hji, hi1⟩ := quaternion_rel hψ₂inj
  set i := ψ₂ ia with hi
  set j := ψ₂ ja with hj
  have hiT : i ∈ T := hψ₂T ia
  have hjT : j ∈ T := hψ₂T ja
  have hiQ : i ^ 2 ∈ hsQ z := by
    set σ := φ ⟨i, hiT.1⟩ with hσ
    set τ := φ ⟨j, hjT.1⟩ with hτ
    have e4 : (⟨i, hiT.1⟩ : ↥(hsH z)) ^ 4 = 1 := Subtype.ext (by simpa using hi4)
    have e2 : (⟨i, hiT.1⟩ : ↥(hsH z)) ^ 2 = (⟨j, hjT.1⟩ : ↥(hsH z)) ^ 2 :=
      Subtype.ext (by simpa using hij)
    have e3 : (⟨j, hjT.1⟩ : ↥(hsH z)) * ⟨i, hiT.1⟩ = (⟨i, hiT.1⟩ : ↥(hsH z))⁻¹ * ⟨j, hjT.1⟩ :=
      Subtype.ext (by simpa using hji)
    have hσ2 : σ ^ 2 = 1 := perm_five_no_q8 σ τ (by rw [hσ, ← map_pow, e4, map_one])
      (by rw [hσ, hτ, ← map_pow, ← map_pow, e2]) (by rw [hσ, hτ, ← map_mul, e3, map_mul, map_inv])
    have hk : (⟨i, hiT.1⟩ : ↥(hsH z)) ^ 2 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hσ2
    rw [hker, Subgroup.mem_subgroupOf] at hk
    simpa using hk
  have hi2 : i * i ≠ 1 := by rw [← sq]; exact hi1
  have hj2 : j * j ≠ 1 := by rw [← sq, ← hij]; exact hi1
  have hii : i ^ 2 * i ^ 2 = 1 := by rw [← pow_add]; exact hi4
  have hiz : IsConj z (i ^ 2) := by
    by_cases hZ : i ^ 2 ∈ hsZQ z
    · rw [h.eq_z_of_mem_ZQ hZ hii hi1]
    · obtain ⟨g, hg⟩ := h.exists_conj_z_of_invol_Q hiQ hii hZ
      exact isConj_iff.mpr ⟨g, hg⟩
  have hnot : i ∉ sPrime φ t ∨ j ∉ sPrime φ t := by
    by_contra hboth
    push Not at hboth
    have hc := h.comm_of_mem_sPrime htK htQ htt hker hφt hsmemH hsK hss hst hφs hboth.1
      hboth.2 hi2 hj2
    apply hi2
    have h1 : i = i⁻¹ := by
      have := hji
      rw [← hc] at this
      exact mul_right_cancel this
    calc i * i = i * i⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel i
  have hfin : ∀ e ∈ T, e ∉ sPrime φ t → e ^ 2 = i ^ 2 →
      ∃ e ∈ T, e ∉ sPrime φ t ∧ e ^ 4 = 1 ∧ IsConj z (e * e) ∧
        (e * e = z ∨ ∀ g ∈ C, g * z * g⁻¹ ≠ e * e) := by
    intro e heT heS he2
    refine ⟨e, heT, heS, ?_, ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, he2]
      exact hii
    · rw [← sq, he2]
      exact hiz
    · rw [← sq, he2]
      exact hψ₂z
  rcases hnot with hiS | hjS
  · exact hfin i hiT hiS rfl
  · exact hfin j hjT hjS hij.symm

end HSSetting

end CFSG.Quasithin.HSType
