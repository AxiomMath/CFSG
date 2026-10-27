module

public import CFSG.Quasithin.Recognition.HSType17h
public import CFSG.Quasithin.Recognition.HSType17i
public import CFSG.Quasithin.Recognition.HSType18e

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem ncard_orbit_H_mul [Finite G] (h : HSSetting z V) (u : G) :
    (@MulAction.orbit ↥(hsH z) G (hAction z).toSMul u).ncard *
      Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({u} : Set G)) = 64 * 120 := by
  let := hAction z
  have hstab : MulAction.stabilizer ↥(hsH z) u =
      (Subgroup.centralizer ({u} : Set G)).subgroupOf (hsH z) := by
    ext q
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    change (q : G) * u * (q : G)⁻¹ = u ↔ _
    constructor
    · intro hq
      calc (q : G) * u = (q : G) * u * (q : G)⁻¹ * (q : G) := by group
        _ = u * (q : G) := by rw [hq]
    · intro hq
      rw [hq, mul_inv_cancel_right]
  have hcardstab : Nat.card (MulAction.stabilizer ↥(hsH z) u) =
      Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [hstab, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(hsH z) u)
  rw [MulAction.index_stabilizer, hcardstab, h.card_H] at hmul
  rw [← Nat.card_coe_set_eq, mul_comm]
  exact hmul

theorem card_conj_comm_t_le [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) :
    Nat.card {v : G // IsConj t v ∧ v * z = z * v} ≤ 200 := by
  let := hAction z
  obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
  have hsnotK := h.not_mem_K_of_inverts hsinv
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have htz : ∀ g : G, g * z * g⁻¹ ≠ t := fun g hg => htQ (by
    rw [← hg]
    exact h.mem_Q_of_conj_mem_K (hg ▸ htK))
  obtain ⟨v₀, hv₀Q, hv₀t⟩ := h.exists_v_of_invol_K htK htQ htt
  have hC96 := (h.card_centralizer_H_invol_not_K hsmemH hsnotK hss hwZ hwz hg₀).2
  have hC64 := h.card_centralizer_H_of_invol_K htK htQ htt
  have hsub : {v : G | IsConj t v ∧ v * z = z * v} ⊆
      MulAction.orbit ↥(hsH z) t ∪ MulAction.orbit ↥(hsH z) (s * w) := by
    rintro v ⟨hv, hvz⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hv
    have hv2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hv1 : g * t * g⁻¹ ≠ 1 := fun h1 => htQ (by
      have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [this]
      exact (hsQ z).one_mem)
    have hvH : g * t * g⁻¹ ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr hvz
    have hvz' : ∀ c : G, c * z * c⁻¹ ≠ g * t * g⁻¹ := fun c hc => htz (g⁻¹ * c) (by
      calc g⁻¹ * c * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
        _ = t := by rw [hc]; group)
    by_cases hvK : g * t * g⁻¹ ∈ hsK z
    · left
      have hvQ : g * t * g⁻¹ ∉ hsQ z := by
        intro hQ
        by_cases hZ : g * t * g⁻¹ ∈ hsZQ z
        · exact hvz' 1 (by rw [h.eq_z_of_mem_ZQ hZ hv2 hv1]; group)
        · obtain ⟨c, hc⟩ := h.exists_conj_z_of_invol_Q hQ hv2 hZ
          exact hvz' c hc
      obtain ⟨k, hkK, hk⟩ := h.exists_K_conj_of_invol htK htQ htt hv₀Q hv₀t hvK hvQ hv2
      refine ⟨⟨k⁻¹, (hsH z).inv_mem hkK.1⟩, ?_⟩
      change k⁻¹ * t * k⁻¹⁻¹ = g * t * g⁻¹
      calc k⁻¹ * t * k⁻¹⁻¹ = k⁻¹ * (k * (g * t * g⁻¹) * k⁻¹) * k := by rw [hk, inv_inv]
        _ = g * t * g⁻¹ := by group
    · right
      obtain ⟨k, hkK, hk⟩ :=
        h.exists_K_conj_of_invol_not_K hsmemH hsnotK hss hwZ hwz hvH hvK hv2
      rcases hk with hk | hk
      · exfalso
        apply hvz' (k⁻¹ * g₀)
        calc k⁻¹ * g₀ * z * (k⁻¹ * g₀)⁻¹ = k⁻¹ * (g₀ * z * g₀⁻¹) * k := by group
          _ = k⁻¹ * (k * (g * t * g⁻¹) * k⁻¹) * k := by rw [hg₀, hk]
          _ = g * t * g⁻¹ := by group
      · refine ⟨⟨k⁻¹, (hsH z).inv_mem hkK.1⟩, ?_⟩
        change k⁻¹ * (s * w) * k⁻¹⁻¹ = _
        rw [← hk]
        group
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hle2 := Set.ncard_union_le (MulAction.orbit ↥(hsH z) t)
    (MulAction.orbit ↥(hsH z) (s * w))
  have ho1 := h.ncard_orbit_H_mul t
  have ho2 := h.ncard_orbit_H_mul (s * w)
  rw [hC64] at ho1
  rw [hC96] at ho2
  rw [← Nat.card_coe_set_eq] at hle
  change Nat.card {v : G // IsConj t v ∧ v * z = z * v} ≤ _ at hle
  omega

end HSSetting

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

include C in
theorem exists_quaternion
    (hGF : FactAutL34GraphField) :
    ∀ t : G, t * t = 1 → t ≠ 1 → (∀ g : G, g * C.z * g⁻¹ ≠ t) →
      ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) ∧
        Nonempty (↥E ≃* QuaternionGroup 2) := by
  obtain ⟨c, hcc, hc1, ⟨E, hEc, ⟨eE⟩⟩, F, hFc, hF9⟩ := C.exists_graph_field hGF
  have hcz : ∀ g : G, g * C.z * g⁻¹ ≠ c := by
    intro g hg
    have hle : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ hsH C.z := by
      rintro _ ⟨f, hf, rfl⟩
      have hfc := Subgroup.mem_centralizer_singleton_iff.mp (hFc hf)
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hz : C.z = g⁻¹ * c * g := by rw [← hg]; group
      rw [hz]
      calc g⁻¹ * f * g * (g⁻¹ * c * g) = g⁻¹ * (f * c) * g := by group
        _ = g⁻¹ * (c * f) * g := by rw [hfc]
        _ = g⁻¹ * c * g * (g⁻¹ * f * g) := by group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hF9, C.h.card_H] at hdvd
    norm_num at hdvd
  obtain ⟨t₀, -, -, -, -, -, hcl⟩ := C.h.two_classes
  obtain ⟨g₁, hg₁⟩ : ∃ g : G, g * c * g⁻¹ = t₀ := by
    rcases hcl c hcc hc1 with ⟨g, hg⟩ | h'
    · exfalso
      exact hcz g⁻¹ (by rw [← hg]; group)
    · exact h'
  intro t htt ht1 htz
  obtain ⟨g₂, hg₂⟩ : ∃ g : G, g * t * g⁻¹ = t₀ := by
    rcases hcl t htt ht1 with ⟨g, hg⟩ | h'
    · exfalso
      exact htz g⁻¹ (by rw [← hg]; group)
    · exact h'
  set a := g₂⁻¹ * g₁ with ha
  have hat : a * c * a⁻¹ = t := by
    rw [ha]
    calc g₂⁻¹ * g₁ * c * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * c * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * t * g₂⁻¹) * g₂ := by rw [hg₁, hg₂]
      _ = t := by group
  refine ⟨E.map (MulAut.conj a).toMonoidHom, ?_,
    ⟨(Subgroup.equivMapOfInjective E _ (MulAut.conj a).injective).symm.trans eE⟩⟩
  rintro _ ⟨e, he, rfl⟩
  have hec := Subgroup.mem_centralizer_singleton_iff.mp (hEc he)
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← hat]
  calc a * e * a⁻¹ * (a * c * a⁻¹) = a * (e * c) * a⁻¹ := by group
    _ = a * (c * e) * a⁻¹ := by rw [hec]
    _ = a * c * a⁻¹ * (a * e * a⁻¹) := by group

theorem card_conj_comm_le_82
    (hGF : FactAutL34GraphField) {t : G} (htK : t ∈ hsK C.z) (htQ : t ∉ hsQ C.z)
    (htt : t * t = 1) : Nat.card {u : G // IsConj C.z u ∧ u * t = t * u} ≤ 82 := by
  have hCt := C.h.card_centralizer_le_2880 (C.exists_quaternion hGF) htK htQ htt
  have hm := C.h.card_conj_comm_t_le htK htQ htt
  have heq := RuType.A65.card_centralizer_mul_eq C.z t
  have hH : Nat.card (Subgroup.centralizer ({C.z} : Set G)) = 64 * 120 := C.h.card_H
  rw [hH] at heq
  have hprod := Nat.mul_le_mul hCt hm
  omega

end HSCtx

theorem statementI48_of_facts
    (hfact : FactAutL34) (hGF : FactAutL34GraphField) (hF : FactM22SubgroupIndex) :
    StatementI48 :=
  statementI48_of_card hfact fun _ _ _ _ C =>
    C.card_quot_eq_100_of_le hF fun _ htK htQ htt => C.card_conj_comm_le_82 hGF htK htQ htt

end CFSG.Quasithin.HSType
