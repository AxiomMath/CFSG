module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Recognition.HSTypeL12h

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem exists_v_of_invol_K [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) : ∃ v ∈ hsQ z, v * t * v⁻¹ = z * t := by
  obtain ⟨t₀, ht₀K, ht₀Q, ht₀t, ⟨v₀, hv₀V, hv₀⟩, -, -⟩ := h.two_classes
  obtain ⟨k, hkK, hk⟩ :=
    h.exists_K_conj_of_invol ht₀K ht₀Q ht₀t (h.two.le hv₀V) hv₀ htK htQ htt
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkK.1
  refine ⟨k⁻¹ * v₀ * k, ?_, ?_⟩
  · have := conj_mem_Q ((hsH z).inv_mem hkK.1) (h.two.le hv₀V)
    rwa [inv_inv] at this
  · have ht : t = k⁻¹ * t₀ * k := by rw [← hk]; group
    rw [ht]
    calc k⁻¹ * v₀ * k * (k⁻¹ * t₀ * k) * (k⁻¹ * v₀ * k)⁻¹ = k⁻¹ * (v₀ * t₀ * v₀⁻¹) * k := by
          group
      _ = k⁻¹ * (z * t₀) * k := by rw [hv₀]
      _ = k⁻¹ * (z * k) * (k⁻¹ * t₀ * k) := by group
      _ = k⁻¹ * (k * z) * (k⁻¹ * t₀ * k) := by rw [hkz]
      _ = z * (k⁻¹ * t₀ * k) := by group

theorem card_centralizer_H_of_invol_K [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({t} : Set G)) = 64 := by
  obtain ⟨v, hvQ, hvt⟩ := h.exists_v_of_invol_K htK htQ htt
  exact h.card_centralizer_H_invol_K htK htQ htt hvQ hvt

theorem le_of_two_pow_dvd_96 {k : ℕ} (hk : 2 ^ k ∣ 96) : 2 ^ k ≤ 32 := by
  have h3 : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have : 2 ^ k ∣ 32 := h3.dvd_of_dvd_mul_right (by simpa using hk)
  exact Nat.le_of_dvd (by norm_num) this

theorem card_le_of_two_subgroup_H [Finite G] (h : HSSetting z V) {t' : G}
    (ht'H : t' ∈ hsH z) (ht't' : t' * t' = 1) (ht'1 : t' ≠ 1) (ht'z : ∀ g : G, g * z * g⁻¹ ≠ t')
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPle : P ≤ hsH z ⊓ Subgroup.centralizer ({t'} : Set G)) : Nat.card P ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := Subgroup.card_dvd_of_le hPle
  by_cases ht'K : t' ∈ hsK z
  · have ht'Q : t' ∉ hsQ z := by
      intro hQ
      by_cases hZ : t' ∈ hsZQ z
      · apply ht'z 1
        rw [h.eq_z_of_mem_ZQ hZ ht't' ht'1]
        group
      · obtain ⟨c, hc⟩ := h.exists_conj_z_of_invol_Q hQ ht't' hZ
        exact ht'z c hc
    rw [h.card_centralizer_H_of_invol_K ht'K ht'Q ht't'] at hle
    exact Nat.le_of_dvd (by norm_num) hle
  ·
    obtain ⟨w, hwZ, hw1, hwz', hww⟩ := h.exists_mem_ZQ_ne
    have hwz : w ∉ Subgroup.zpowers z := by
      intro hwz
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
      · exact hw1 h1
      · exact hwz' h1
    obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
    have hsnotK := h.not_mem_K_of_inverts hsinv
    have hnc : ∀ g : G, g * t' * g⁻¹ ≠ t' * w := by
      intro g hg
      obtain ⟨k, hkK, hk⟩ := h.exists_K_conj_of_invol_not_K hsmemH hsnotK hss hwZ hwz ht'H
        ht'K ht't'
      rcases hk with hk | hk
      · refine ht'z (k⁻¹ * g₀) ?_
        calc k⁻¹ * g₀ * z * (k⁻¹ * g₀)⁻¹ = k⁻¹ * (g₀ * z * g₀⁻¹) * k := by group
          _ = k⁻¹ * (k * t' * k⁻¹) * k := by rw [hg₀, hk]
          _ = t' := by group
      ·
        have hkw : k * w * k⁻¹ = w := by
          have := Subgroup.mem_centralizer_iff.mp hkK.2 w hwZ
          rw [← this]; group
        have hsz : k * (t' * w) * k⁻¹ = s * z := by
          calc k * (t' * w) * k⁻¹ = (k * t' * k⁻¹) * (k * w * k⁻¹) := by group
            _ = s * w * w := by rw [hk, hkw]
            _ = s * z := by rw [mul_assoc, hww]
        have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) :=
          ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
        obtain ⟨r, -, hr⟩ := h.exists_conj_eq_mul_of_invol hsmemH hsnotK hss hzC
        apply ht'z ((k * g)⁻¹ * r * g₀)
        calc (k * g)⁻¹ * r * g₀ * z * ((k * g)⁻¹ * r * g₀)⁻¹ =
            (k * g)⁻¹ * (r * (g₀ * z * g₀⁻¹) * r⁻¹) * (k * g) := by group
          _ = (k * g)⁻¹ * (s * z) * (k * g) := by rw [hg₀, ← hr]
          _ = (k * g)⁻¹ * (k * (t' * w) * k⁻¹) * (k * g) := by rw [hsz]
          _ = g⁻¹ * (t' * w) * g := by group
          _ = g⁻¹ * (g * t' * g⁻¹) * g := by rw [hg]
          _ = t' := by group
    have h96 := h.card_centralizer_H_of_not_conj ht'H ht'K ht't' hwZ hwz hnc
    rw [h96] at hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hk] at hle ⊢
    exact (le_of_two_pow_dvd_96 hle).trans (by norm_num)

theorem card_two_subgroup_centralizer_le [Finite G] (h : HSSetting z V) {t : G}
    (htt : t * t = 1) (ht1 : t ≠ 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPt : P ≤ Subgroup.centralizer ({t} : Set G)) : Nat.card P ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun p => ?_
    have : ∀ q ∈ P, t * q * t⁻¹ = q := fun q hq => by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hPt hq)).symm, mul_inv_cancel_right]
    constructor
    · intro hp; rw [this p hp]; exact hp
    · intro hp
      have hqt : (t * p * t⁻¹) * t = t * (t * p * t⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hPt hp)
      have e : p = t * p * t⁻¹ := by
        calc p = t⁻¹ * ((t * p * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * p * t⁻¹)) := by rw [hqt]
          _ = t * p * t⁻¹ := by group
      rw [e]
      exact hp
  set P' := P ⊔ Subgroup.zpowers t with hP'
  have hP'p : IsPGroup 2 P' := hP.to_sup_of_normal_left' htp hnorm
  have hP't : P' ≤ Subgroup.centralizer ({t} : Set G) :=
    sup_le hPt (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have htP' : t ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨T, hT⟩ := h.exists_isSylowTwoOf
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo (h.isSylowTwo_T hT)
  obtain ⟨S', hS'⟩ := hP'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hconjT : ∀ x ∈ P', g * x * g⁻¹ ∈ T := by
    intro x hx
    rw [← hS, ← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hS' hx, by simp [MulAut.smul_def]⟩
  set P'' := P'.map (MulAut.conj g).toMonoidHom with hP''
  have hP''H : P'' ≤ hsH z ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hT.1.trans inf_le_left (hconjT x hx), ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hP't hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  have ht'H : g * t * g⁻¹ ∈ hsH z := hT.1.trans inf_le_left (hconjT t htP')
  have hcard := h.card_le_of_two_subgroup_H ht'H
    (by calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [htt]; group)
    (fun h1 => ht1 (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group))
    (fun c hc => htz (g⁻¹ * c) (by
      calc g⁻¹ * c * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hc]
        _ = t := by group))
    (hP'p.map _) hP''H
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hcard
  exact (Subgroup.card_le_of_le le_sup_left).trans hcard

theorem not_two_dvd_relIndex_T [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) (htz : ∀ g : G, g * z * g⁻¹ ≠ t) :
    ¬ 2 ∣ (hsH z ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
      (Subgroup.centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ (hsQ z).one_mem)
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set T := hsH z ⊓ C with hTdef
  have hT64 := h.card_centralizer_H_of_invol_K htK htQ htt
  have hTp : IsPGroup 2 (T.subgroupOf C) := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hT64]
    norm_num
  obtain ⟨S, hS⟩ := hTp.exists_le_sylow
  have hSC : ((S : Subgroup ↥C).map C.subtype) ≤ C := Subgroup.map_subtype_le _
  have hScard : Nat.card ((S : Subgroup ↥C).map C.subtype) ≤ 64 :=
    h.card_two_subgroup_centralizer_le htt ht1 htz (S.isPGroup'.map _) hSC
  rw [Subgroup.card_map_of_injective C.subtype_injective] at hScard
  have heq : T.subgroupOf C = S := by
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hT64]
    exact hScard
  rw [Subgroup.relIndex, heq]
  exact Sylow.not_dvd_index S

end HSSetting

end CFSG.Quasithin.HSType
