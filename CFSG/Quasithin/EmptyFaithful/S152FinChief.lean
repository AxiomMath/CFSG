module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem exists_noncentral_of_series {H U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : 1 ≤ n) :
    ∃ L₁ N₁ : Subgroup G, IsChiefStep H U L₁ N₁ ∧ ¬ IsCentralStep H L₁ N₁ ∧ N₁ ≤ N := by
  induction h with
  | bot => omega
  | central hs hc h ih =>
    obtain ⟨L₁, N₁, a, b, c⟩ := ih hn
    exact ⟨L₁, N₁, a, b, c.trans hs.2.2.1.le⟩
  | noncentral hs hnc h ih => exact ⟨_, _, hs, hnc, le_rfl⟩

theorem exists_two_noncentral_of_series {H U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : 2 ≤ n) :
    ∃ L₁ N₁ L₂ N₂ : Subgroup G, IsChiefStep H U L₁ N₁ ∧ ¬ IsCentralStep H L₁ N₁ ∧
      IsChiefStep H U L₂ N₂ ∧ ¬ IsCentralStep H L₂ N₂ ∧ N₁ ≤ L₂ := by
  induction h with
  | bot => omega
  | central hs hc h ih =>
    obtain ⟨L₁, N₁, L₂, N₂, a, b, c, d, e⟩ := ih hn
    exact ⟨L₁, N₁, L₂, N₂, a, b, c, d, e⟩
  | @noncentral N L n hs hnc h ih =>
    obtain ⟨L₁, N₁, a, b, c⟩ := exists_noncentral_of_series h (by omega)
    exact ⟨L₁, N₁, L, N, a, b, hs, hnc, c⟩

theorem le_normalizer_of_isNormalIn {H U N : Subgroup G} (h : IsNormalIn H U N) :
    H ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h.2 g hg x hx, fun hx => ?_⟩
  have := h.2 g⁻¹ (H.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem commutator_pCoreOf_le {H U L N : Subgroup G} [Finite G] (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) :
    ∀ p ∈ pCoreOf 2 H, ∀ w ∈ N, p * w * p⁻¹ * w⁻¹ ∈ L := by
  have hNU : N ≤ U := hs.1.1
  have hLN : L ≤ N := hs.2.2.1.le
  have hNN : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_isNormalIn hs.1
  have hLL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isNormalIn hs.2.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := F7.isElemAbelian_comm hU (hNU hn) (hNU (hLN hx))
      have : n * x * n⁻¹ = x := by rw [hc]; group
      rw [this]; exact hx
    · intro hx
      have hc := F7.isElemAbelian_comm hU (hNU (N.inv_mem hn)) (hNU (hLN hx))
      have : x = n * x * n⁻¹ := by
        calc x = (n⁻¹ * (n * x * n⁻¹)) * n := by group
          _ = ((n * x * n⁻¹) * n⁻¹) * n := by rw [hc]
          _ = n * x * n⁻¹ := by group
      rw [this]; exact hx
  refine commutator_le_of_irreducible (X := H) (W := N) (W₁ := L) (P := pCoreOf 2 H)
    (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hNN hLL (le_normalizer_pCoreOf 2 H) hLN
    ((F7.isPGroup_of_isElemAbelian hU).to_le hNU) hNL ?_
  intro K hLK hKN hHK
  refine hs.2.2.2 K ⟨hKN.trans hNU, fun g hg x hx => ?_⟩ hLK hKN
  exact (Subgroup.mem_normalizer_iff.mp (hHK hg) x).mp hx

@[expose] def fixMod (X L N : Subgroup G) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hLN : L ≤ N) :
    Subgroup G where
  carrier := {n | n ∈ N ∧ ∀ x ∈ X, x * n * x⁻¹ * n⁻¹ ∈ L}
  one_mem' := ⟨N.one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro n₁ n₂ ⟨hn₁, h₁⟩ ⟨hn₂, h₂⟩
    refine ⟨N.mul_mem hn₁ hn₂, fun x hx => ?_⟩
    have ha := h₁ x hx
    have hb := h₂ x hx
    have hcomm : n₁ * (x * n₂ * x⁻¹ * n₂⁻¹) * n₁⁻¹ = x * n₂ * x⁻¹ * n₂⁻¹ := by
      have := hab n₁ hn₁ _ (hLN hb)
      rw [this]; group
    have e : x * (n₁ * n₂) * x⁻¹ * (n₁ * n₂)⁻¹ =
        (x * n₁ * x⁻¹ * n₁⁻¹) * (n₁ * (x * n₂ * x⁻¹ * n₂⁻¹) * n₁⁻¹) := by group
    rw [e, hcomm]
    exact L.mul_mem ha hb
  inv_mem' := by
    rintro n ⟨hn, h⟩
    refine ⟨N.inv_mem hn, fun x hx => ?_⟩
    have ha := h x hx
    have hcomm : n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n = (x * n * x⁻¹ * n⁻¹)⁻¹ := by
      have := hab n⁻¹ (N.inv_mem hn) _ (hLN (L.inv_mem ha))
      rw [this]; group
    have e : x * n⁻¹ * x⁻¹ * n⁻¹⁻¹ = n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n := by group
    rw [e, hcomm]
    exact L.inv_mem ha

variable {X L N : Subgroup G} {hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a} {hLN : L ≤ N}

theorem mem_fixMod {n : G} :
    n ∈ fixMod X L N hab hLN ↔ n ∈ N ∧ ∀ x ∈ X, x * n * x⁻¹ * n⁻¹ ∈ L := Iff.rfl

theorem fixMod_le : fixMod X L N hab hLN ≤ N := fun _ h => h.1

theorem inf_centralizer_le_fixMod :
    N ⊓ Subgroup.centralizer (X : Set G) ≤ fixMod X L N hab hLN := by
  rintro n ⟨hnN, hnC⟩
  refine ⟨hnN, fun x hx => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hnC x hx
  have : x * n * x⁻¹ * n⁻¹ = 1 := by rw [h1]; group
  rw [this]
  exact L.one_mem

theorem le_fixMod (hXL : X ≤ Subgroup.normalizer (L : Set G)) : L ≤ fixMod X L N hab hLN := by
  intro l hl
  refine ⟨hLN hl, fun x hx => ?_⟩
  have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hXL hx) l).mp hl
  exact L.mul_mem h1 (L.inv_mem hl)

theorem fixMod_anti {X' : Subgroup G} (h : X' ≤ X) :
    fixMod X L N hab hLN ≤ fixMod X' L N hab hLN :=
  fun _ hn => ⟨hn.1, fun x hx => hn.2 x (h hx)⟩

theorem relIndex_chain_aux [Finite G] {C L F N : Subgroup G} (hLF : L ≤ F) (hFN : F ≤ N)
    (hCF : N ⊓ C ≤ F) : C.relIndex L * F.relIndex N ≤ C.relIndex N := by
  have h1 : C.relIndex L ≤ C.relIndex F :=
    Subgroup.relIndex_le_of_le_right hLF Subgroup.index_ne_zero_of_finite
  have h2 : C.relIndex F ≤ (N ⊓ C).relIndex F :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_of_le_left F (inf_le_right : N ⊓ C ≤ C))
  have h3 : (N ⊓ C).relIndex F * F.relIndex N = (N ⊓ C).relIndex N :=
    Subgroup.relIndex_mul_relIndex _ _ _ hCF hFN
  have h4 : (N ⊓ C).relIndex N = C.relIndex N := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right C N
  calc C.relIndex L * F.relIndex N ≤ (N ⊓ C).relIndex F * F.relIndex N :=
        Nat.mul_le_mul (h1.trans h2) le_rfl
    _ = (N ⊓ C).relIndex N := h3
    _ = C.relIndex N := h4

theorem relIndex_fixMod_le_centralizer [Finite G] :
    (fixMod X L N hab hLN).relIndex N ≤ (Subgroup.centralizer (X : Set G)).relIndex N := by
  have h1 : (fixMod X L N hab hLN).relIndex N ∣ (N ⊓ Subgroup.centralizer (X : Set G)).relIndex N :=
    Subgroup.relIndex_dvd_of_le_left N inf_centralizer_le_fixMod
  have h4 : (N ⊓ Subgroup.centralizer (X : Set G)).relIndex N =
      (Subgroup.centralizer (X : Set G)).relIndex N := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right _ N
  rw [h4] at h1
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1

@[expose] def fixU (H U L N X : Subgroup G) (hU : IsElemAbelian 2 U) (hs : IsChiefStep H U L N) :
    Subgroup G :=
  fixMod X L N (fun _ ha _ hb => F7.isElemAbelian_comm hU (hs.1.1 ha) (hs.1.1 hb)) hs.2.2.1.le

theorem relIndex_centralizer_ge_sixteen [Finite G] {H U X L₁ N₁ L₂ N₂ : Subgroup G}
    (hU : IsElemAbelian 2 U) (hX : X ≤ H)
    (hs₁ : IsChiefStep H U L₁ N₁) (hs₂ : IsChiefStep H U L₂ N₂) (h12 : N₁ ≤ L₂)
    (h₁ : 4 ≤ (fixU H U L₁ N₁ X hU hs₁).relIndex N₁)
    (h₂ : 4 ≤ (fixU H U L₂ N₂ X hU hs₂).relIndex N₂) :
    16 ≤ (Subgroup.centralizer (X : Set G)).relIndex U := by
  have hXL₂ : X ≤ Subgroup.normalizer (L₂ : Set G) :=
    hX.trans (le_normalizer_of_isNormalIn hs₂.2.1)
  have hC2 := relIndex_chain_aux (C := Subgroup.centralizer (X : Set G))
    (le_fixMod (hab := fun _ ha _ hb => F7.isElemAbelian_comm hU (hs₂.1.1 ha) (hs₂.1.1 hb))
      (hLN := hs₂.2.2.1.le) hXL₂)
    (fixMod_le (hab := fun _ ha _ hb => F7.isElemAbelian_comm hU (hs₂.1.1 ha) (hs₂.1.1 hb))
      (hLN := hs₂.2.2.1.le))
    (inf_centralizer_le_fixMod (hab := fun _ ha _ hb => F7.isElemAbelian_comm hU (hs₂.1.1 ha) (hs₂.1.1 hb))
      (hLN := hs₂.2.2.1.le))
  have hC1 := relIndex_fixMod_le_centralizer (X := X) (L := L₁) (N := N₁)
    (hab := fun _ ha _ hb => F7.isElemAbelian_comm hU (hs₁.1.1 ha) (hs₁.1.1 hb))
    (hLN := hs₁.2.2.1.le)
  have hm1 : (Subgroup.centralizer (X : Set G)).relIndex N₁ ≤
      (Subgroup.centralizer (X : Set G)).relIndex L₂ :=
    Subgroup.relIndex_le_of_le_right h12 Subgroup.index_ne_zero_of_finite
  have hm2 : (Subgroup.centralizer (X : Set G)).relIndex N₂ ≤
      (Subgroup.centralizer (X : Set G)).relIndex U :=
    Subgroup.relIndex_le_of_le_right hs₂.1.1 Subgroup.index_ne_zero_of_finite
  unfold fixU at h₁ h₂
  calc 16 = 4 * 4 := by norm_num
    _ ≤ (Subgroup.centralizer (X : Set G)).relIndex L₂ *
        (fixMod X L₂ N₂ _ hs₂.2.2.1.le).relIndex N₂ := Nat.mul_le_mul (h₁.trans (hC1.trans hm1)) h₂
    _ ≤ (Subgroup.centralizer (X : Set G)).relIndex N₂ := hC2
    _ ≤ _ := hm2

end S152Fin

end CFSG.Quasithin
