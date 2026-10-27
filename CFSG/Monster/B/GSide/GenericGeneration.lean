module

public import CFSG.Goldschmidt.Steps.StrongEmb
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Monster.B.GSide

open CFSG.BenderSuzuki

variable {G : Type*} [Group G]

theorem isConj_of_mem_of_isStronglyEmbeddedOrder [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) {t u : G} (ht : orderOf t = 2) (hu : orderOf u = 2)
    (htM : t ∈ M) (huM : u ∈ M) : IsConj t u := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra h
    push Not at h
    exact hM.1 (eq_top_iff.2 fun g _ => h g)
  have hgu : g * u * g⁻¹ ∉ M := fun h => by
    have h' := CFSG.Goldschmidt.mem_of_involution_conj_mem hM hu huM (g := g⁻¹)
      (by rwa [inv_inv])
    exact hg (by simpa using M.inv_mem h')
  have hgu2 : orderOf (g * u * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  exact (CFSG.Goldschmidt.isConj_of_mem_of_not_mem hM ht hgu2 htM hgu).trans
    (isConj_iff.2 ⟨g⁻¹, by group⟩)

theorem exists_conj_eq_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) {t u : G} (ht : orderOf t = 2) (htM : t ∈ M) (huM : u ∈ M)
    (htu : IsConj t u) : ∃ m ∈ M, m * t * m⁻¹ = u := by
  obtain ⟨c, hc⟩ := isConj_iff.1 htu
  refine ⟨c, ?_, hc⟩
  have h := CFSG.Goldschmidt.mem_of_involution_conj_mem hM ht htM (g := c⁻¹)
    (by rw [inv_inv, hc]; exact huM)
  simpa using M.inv_mem h

theorem isStronglyEmbeddedOrder_fusion [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) :
    (∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M) ∧
    (∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → orderOf u = 2 → IsConj t u) ∧
    (∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → IsConj t u → ∃ m ∈ M, m * t * m⁻¹ = u) :=
  ⟨fun _ htM ht => CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hM ht htM,
    fun _ htM _ huM ht hu => isConj_of_mem_of_isStronglyEmbeddedOrder hM ht hu htM huM,
    fun _ htM _ huM ht htu => exists_conj_eq_of_isStronglyEmbeddedOrder hM ht htM huM htu⟩

theorem isStronglyEmbeddedOrder_of_fusion [Finite G] {M : Subgroup G}
    (hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M)
    (hF : ∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → IsConj t u → ∃ m ∈ M, m * t * m⁻¹ = u)
    (hne : M ≠ ⊤) (h2 : ∃ t ∈ M, orderOf t = 2) : IsStronglyEmbeddedOrder M := by
  obtain ⟨t, htM, ht⟩ := h2
  refine ⟨hne, ?_, fun g hg => ?_⟩
  · have h := orderOf_dvd_natCard (⟨t, htM⟩ : M)
    rw [Subgroup.orderOf_mk, ht] at h
    exact even_iff_two_dvd.2 h
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom))
      2 (even_iff_two_dvd.1 hodd)
    have hs2 : orderOf (s : G) = 2 := by rwa [Subgroup.orderOf_coe]
    obtain ⟨hsM, x, hxM, hxs⟩ := s.2
    have hxs' : g * x * g⁻¹ = s := by simpa [MulAut.conj_apply] using hxs
    obtain ⟨m, hmM, hm⟩ := hF s hsM x hxM hs2 (isConj_iff.2 ⟨g⁻¹, by rw [← hxs']; group⟩)
    have hcent : g * m ∈ Subgroup.centralizer {(s : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * m * s = g * (m * s * m⁻¹) * m := by group
        _ = (g * x * g⁻¹) * (g * m) := by rw [hm]; group
        _ = s * (g * m) := by rw [hxs']
    exact hg (by simpa using M.mul_mem (hC s hsM hs2 hcent) (M.inv_mem hmM))

theorem eq_top_of_not_conj_mem [Finite G] {M : Subgroup G}
    (hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M)
    (hF : ∀ t ∈ M, ∀ u ∈ M, orderOf t = 2 → IsConj t u → ∃ m ∈ M, m * t * m⁻¹ = u)
    {t u : G} (htM : t ∈ M) (huM : u ∈ M) (ht : orderOf t = 2) (hu : orderOf u = 2)
    (htu : ¬ ∃ m ∈ M, m * t * m⁻¹ = u) : M = ⊤ := by
  by_contra hne
  have hM := isStronglyEmbeddedOrder_of_fusion hC hF hne ⟨t, htM, ht⟩
  exact htu (hF t htM u huM ht (isConj_of_mem_of_isStronglyEmbeddedOrder hM ht hu htM huM))

theorem mem_of_conj_mem_of_centralizer_le {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {g a : G} (ha : a ∈ D₀)
    (hga : g * a * g⁻¹ ∈ D₀) : g ∈ M := by
  obtain ⟨m, hmM, hm⟩ := hD₀ a ha _ hga
  have hcent : m⁻¹ * g ∈ Subgroup.centralizer {a} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * g * a = m⁻¹ * (g * a * g⁻¹) * g := by group
      _ = m⁻¹ * (m * a * m⁻¹) * g := by rw [hm]
      _ = a * (m⁻¹ * g) := by group
  simpa using M.mul_mem hmM (hC₀ a ha hcent)

theorem normalizer_le_of_conj_class {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {D : Set G}
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀) {X : Subgroup G} (hXM : X ≤ M) (hXD : ∃ a ∈ X, a ∈ D₀) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  intro n hn
  obtain ⟨a, haX, haD₀⟩ := hXD
  have hnaX : n * a * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn a).1 haX
  exact mem_of_conj_mem_of_centralizer_le hD₀ hC₀ haD₀
    (hDM _ (hDconj a (hD₀D haD₀) n) (hXM hnaX))

theorem isPGroup_of_map_subtype_le {p : ℕ} {H : Subgroup G} {K : Subgroup H} {L : Subgroup G}
    (hL : IsPGroup p L) (hK : K.map H.subtype ≤ L) : IsPGroup p K :=
  (hL.comap_of_injective H.subtype H.subtype_injective).to_le (Subgroup.map_le_iff_le_comap.1 hK)

theorem le_of_baerSuzuki_pCore [Finite G] {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {D : Set G}
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀) {H : Subgroup G} {a : G} (haH : a ∈ H) (haD₀ : a ∈ D₀)
    (h2 : ∀ c ∈ H, IsPGroup 2 (Subgroup.closure ({a, c * a * c⁻¹} : Set G)))
    (hO : (CFSG.pCore 2 H).map H.subtype ≤ M) : H ≤ M := by
  let x : H := ⟨a, haH⟩
  have hx : IsPGroup 2 (Subgroup.zpowers x) := by
    refine isPGroup_of_map_subtype_le (h2 1 H.one_mem) ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact zpow_mem (Subgroup.subset_closure (Set.mem_insert a _)) n
  have hall : ∀ g : H, IsPGroup 2 (Subgroup.closure ({x, g * x * g⁻¹} : Set H)) := fun g => by
    refine isPGroup_of_map_subtype_le (h2 g g.2) ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact Set.mem_insert a _
    · exact Set.mem_insert_of_mem a rfl
  have haO : a ∈ (CFSG.pCore 2 H).map H.subtype := ⟨x, CFSG.BaerSuzuki.baer_suzuki x hx hall, rfl⟩
  refine le_trans ?_ (normalizer_le_of_conj_class hD₀ hC₀ hDconj hD₀D hDM hO ⟨a, haO, haD₀⟩)
  intro h hh
  refine Subgroup.le_normalizer_map H.subtype ?_
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_top ⟨h, hh⟩)

theorem le_of_baerSuzuki [Finite G] {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {D : Set G}
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀) {H : Subgroup G} {a : G} (haH : a ∈ H) (haD₀ : a ∈ D₀)
    (h2 : ∀ c ∈ H, IsPGroup 2 (Subgroup.closure ({a, c * a * c⁻¹} : Set G)))
    (hS : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype ≤ M) : H ≤ M := by
  obtain ⟨S, hSM⟩ := hS
  exact le_of_baerSuzuki_pCore hD₀ hC₀ hDconj hD₀D hDM haH haD₀ h2
    ((Subgroup.map_mono (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup S)).trans hSM)

theorem centralizer_le_of_baerSuzuki [Finite G] {M : Subgroup G} {D₀ : Set G}
    (hD₀ : ∀ a ∈ D₀, ∀ b ∈ D₀, ∃ m ∈ M, m * a * m⁻¹ = b)
    (hC₀ : ∀ a ∈ D₀, Subgroup.centralizer {a} ≤ M) {D : Set G}
    (hDconj : ∀ x ∈ D, ∀ g : G, g * x * g⁻¹ ∈ D) (hD₀D : D₀ ⊆ D)
    (hDM : ∀ x ∈ D, x ∈ M → x ∈ D₀) {t a : G} (hat : a ∈ Subgroup.centralizer {t})
    (haD₀ : a ∈ D₀)
    (h2 : ∀ c ∈ Subgroup.centralizer {t},
      IsPGroup 2 (Subgroup.closure ({a, c * a * c⁻¹} : Set G)))
    (hS : ∃ S : Sylow 2 (Subgroup.centralizer {t}),
      (S : Subgroup (Subgroup.centralizer {t})).map (Subgroup.centralizer {t}).subtype ≤ M) :
    Subgroup.centralizer {t} ≤ M :=
  le_of_baerSuzuki hD₀ hC₀ hDconj hD₀D hDM hat haD₀ h2 hS

end CFSG.Monster.B.GSide
