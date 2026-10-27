module

public import CFSG.Quasithin.Background.C118PartnerB

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Transport

variable {T G' : Type*} [Group T] [Group G']

theorem isElemAbelian_of_map_injective {f : T →* G'} (hf : Function.Injective f) {A : Subgroup T}
    (h : CFSG.Open.IsElemAbelian 2 (A.map f)) : CFSG.Open.IsElemAbelian 2 A := by
  obtain ⟨hc, hp⟩ := isElemAbelian_iff.mp h
  refine isElemAbelian_iff.mpr ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
  · rw [map_mul, map_mul]
    exact hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  · rw [map_pow, map_one]
    exact hp _ ⟨a, ha, rfl⟩

theorem isMaxElemAbelian_map_iff {f : T →* G'} (hf : Function.Injective f) {S A : Subgroup T} :
    IsMaxElemAbelian (S.map f) (A.map f) ↔ IsMaxElemAbelian S A := by
  constructor
  · rintro ⟨hle, hel, hmax⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).mp hle,
      isElemAbelian_of_map_injective hf hel, fun B hBS hB => ?_⟩
    have := hmax (B.map f) (Subgroup.map_mono hBS) (isElemAbelian_map hB f)
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at this
  · rintro ⟨hle, hel, hmax⟩
    refine ⟨Subgroup.map_mono hle, isElemAbelian_map hel f, fun B' hB'S hB' => ?_⟩
    have hB'r : B' ≤ f.range := hB'S.trans (Subgroup.map_le_range f S)
    have hmap : (B'.comap f).map f = B' := Subgroup.map_comap_eq_self hB'r
    have hBS : B'.comap f ≤ S := by
      intro x hx
      obtain ⟨s, hs, hfs⟩ := hB'S hx
      rw [← hf hfs]
      exact hs
    have h1 := hmax (B'.comap f) hBS (isElemAbelian_of_map_injective hf (by rw [hmap]; exact hB'))
    have h2 : Nat.card B' = Nat.card (B'.comap f) := by
      conv_lhs => rw [← hmap]
      exact Subgroup.card_map_of_injective hf
    rw [Subgroup.card_map_of_injective hf, h2]
    exact h1

theorem exists_of_isMaxElemAbelian_map {f : T →* G'} (hf : Function.Injective f) {S : Subgroup T}
    {A' : Subgroup G'} (h : IsMaxElemAbelian (S.map f) A') :
    ∃ A : Subgroup T, IsMaxElemAbelian S A ∧ A.map f = A' := by
  have hr : A' ≤ f.range := h.1.trans (Subgroup.map_le_range f S)
  refine ⟨A'.comap f, ?_, Subgroup.map_comap_eq_self hr⟩
  rw [← isMaxElemAbelian_map_iff hf, Subgroup.map_comap_eq_self hr]
  exact h

theorem thompsonJ_map_of_injective' {f : T →* G'} (hf : Function.Injective f) (S : Subgroup T) :
    thompsonJ (S.map f) = (thompsonJ S).map f := by
  apply le_antisymm
  · refine thompsonJ_le_of_forall fun A' hA' => ?_
    obtain ⟨A, hA, rfl⟩ := exists_of_isMaxElemAbelian_map hf hA'
    exact Subgroup.map_mono (maxElem_le_thompsonJ hA)
  · rw [Subgroup.map_le_iff_le_comap]
    refine thompsonJ_le_of_forall fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact maxElem_le_thompsonJ ((isMaxElemAbelian_map_iff hf).mpr hA)

theorem map_inf_centralizer {f : T →* G'} (hf : Function.Injective f) (A F : Subgroup T) :
    (A ⊓ Subgroup.centralizer (F : Set T)).map f =
      A.map f ⊓ Subgroup.centralizer ((F.map f : Subgroup G') : Set G') := by
  ext y
  constructor
  · rintro ⟨a, ⟨ha, hac⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hac x hx]
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ⟨ha, Subgroup.mem_centralizer_iff.mpr fun x hx => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hc (f x) ⟨x, hx, rfl⟩

namespace PartnerCore

variable {f : T →* G'} {S F Z : Subgroup T}

theorem map (hf : Function.Injective f) (h : PartnerCore S F Z) :
    PartnerCore (S.map f) (F.map f) (Z.map f) where
  normal := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨s * x * s⁻¹, h.normal s hs x hx, by simp⟩
  zcentral := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, h.zcentral s hs z hz]
  commJ := by
    rw [thompsonJ_map_of_injective' hf, ← Subgroup.map_commutator, h.commJ]
  commA := by
    intro A' hA'
    obtain ⟨A, hA, rfl⟩ := exists_of_isMaxElemAbelian_map hf hA'
    rw [← Subgroup.map_commutator]
    rcases h.commA A hA with h1 | h1
    · left
      rw [h1, Subgroup.map_bot]
    · right
      rw [h1]
  sup_max := by
    intro A' hA'
    obtain ⟨A, hA, rfl⟩ := exists_of_isMaxElemAbelian_map hf hA'
    have := (isMaxElemAbelian_map_iff hf).mpr (h.sup_max A hA)
    rwa [Subgroup.map_sup, map_inf_centralizer hf] at this

theorem of_map (hf : Function.Injective f) (h : PartnerCore (S.map f) (F.map f) (Z.map f)) :
    PartnerCore S F Z where
  normal := by
    intro s hs x hx
    have := h.normal (f s) ⟨s, hs, rfl⟩ (f x) ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact (Subgroup.mem_map_iff_mem hf).mp this
  zcentral := by
    intro s hs z hz
    apply hf
    rw [map_mul, map_mul]
    exact h.zcentral (f s) ⟨s, hs, rfl⟩ (f z) ⟨z, hz, rfl⟩
  commJ := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_commutator, ← thompsonJ_map_of_injective' hf]
    exact h.commJ
  commA := by
    intro A hA
    have h1 := h.commA (A.map f) ((isMaxElemAbelian_map_iff hf).mpr hA)
    rw [← Subgroup.map_commutator] at h1
    rcases h1 with h1 | h1
    · left
      apply Subgroup.map_injective hf
      rw [h1, Subgroup.map_bot]
    · right
      exact Subgroup.map_injective hf h1
  sup_max := by
    intro A hA
    have := h.sup_max (A.map f) ((isMaxElemAbelian_map_iff hf).mpr hA)
    rw [← map_inf_centralizer hf, ← Subgroup.map_sup] at this
    exact (isMaxElemAbelian_map_iff hf).mp this

end PartnerCore

structure NatLike (S Q V Z : Subgroup T) (q : ℕ) : Prop where
  Q_le : Q ≤ S
  V_le : V ≤ S
  Q_normal : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q
  V_normal : ∀ s ∈ S, ∀ x ∈ V, s * x * s⁻¹ ∈ V
  V_elem : CFSG.Open.IsElemAbelian 2 V
  Z_le : Z ≤ V
  Z_central : ∀ s ∈ S, ∀ z ∈ Z, s * z = z * s
  Q_comm : ∀ s ∈ Q, ∀ v ∈ V, s * v = v * s
  cent_le : ∀ s ∈ S, (∀ v ∈ V, s * v = v * s) → s ∈ Q
  fix : ∀ s ∈ S, s ∉ Q → ∀ v ∈ V, s * v = v * s → v ∈ Z
  comm_le : ⁅S, V⁆ ≤ Z
  one_lt : 1 < q
  card_S : Nat.card S = q * Nat.card Q
  card_V : Nat.card V = q * Nat.card Z

namespace NatLike

variable {f : T →* G'} {S Q V Z : Subgroup T} {q : ℕ}

theorem map (hf : Function.Injective f) (h : NatLike S Q V Z q) :
    NatLike (S.map f) (Q.map f) (V.map f) (Z.map f) q where
  Q_le := Subgroup.map_mono h.Q_le
  V_le := Subgroup.map_mono h.V_le
  Q_normal := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨s * x * s⁻¹, h.Q_normal s hs x hx, by simp⟩
  V_normal := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨s * x * s⁻¹, h.V_normal s hs x hx, by simp⟩
  V_elem := isElemAbelian_map h.V_elem f
  Z_le := Subgroup.map_mono h.Z_le
  Z_central := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, h.Z_central s hs z hz]
  Q_comm := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, h.Q_comm s hs v hv]
  cent_le := by
    rintro _ ⟨s, hs, rfl⟩ hc
    refine ⟨s, h.cent_le s hs fun v hv => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hc (f v) ⟨v, hv, rfl⟩
  fix := by
    rintro _ ⟨s, hs, rfl⟩ hsQ _ ⟨v, hv, rfl⟩ hc
    refine ⟨v, h.fix s hs (fun hsQ' => hsQ ⟨s, hsQ', rfl⟩) v hv (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact hc
  comm_le := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono h.comm_le
  one_lt := h.one_lt
  card_S := by
    rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]
    exact h.card_S
  card_V := by
    rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]
    exact h.card_V

theorem of_map (hf : Function.Injective f) (h : NatLike (S.map f) (Q.map f) (V.map f) (Z.map f) q) :
    NatLike S Q V Z q where
  Q_le := (Subgroup.map_le_map_iff_of_injective hf).mp h.Q_le
  V_le := (Subgroup.map_le_map_iff_of_injective hf).mp h.V_le
  Q_normal := by
    intro s hs x hx
    have := h.Q_normal (f s) ⟨s, hs, rfl⟩ (f x) ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact (Subgroup.mem_map_iff_mem hf).mp this
  V_normal := by
    intro s hs x hx
    have := h.V_normal (f s) ⟨s, hs, rfl⟩ (f x) ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact (Subgroup.mem_map_iff_mem hf).mp this
  V_elem := isElemAbelian_of_map_injective hf h.V_elem
  Z_le := (Subgroup.map_le_map_iff_of_injective hf).mp h.Z_le
  Z_central := by
    intro s hs z hz
    apply hf
    rw [map_mul, map_mul]
    exact h.Z_central (f s) ⟨s, hs, rfl⟩ (f z) ⟨z, hz, rfl⟩
  Q_comm := by
    intro s hs v hv
    apply hf
    rw [map_mul, map_mul]
    exact h.Q_comm (f s) ⟨s, hs, rfl⟩ (f v) ⟨v, hv, rfl⟩
  cent_le := by
    intro s hs hc
    have := h.cent_le (f s) ⟨s, hs, rfl⟩ (by
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hc v hv])
    exact (Subgroup.mem_map_iff_mem hf).mp this
  fix := by
    intro s hs hsQ v hv hc
    have := h.fix (f s) ⟨s, hs, rfl⟩ (fun hmem => hsQ ((Subgroup.mem_map_iff_mem hf).mp hmem))
      (f v) ⟨v, hv, rfl⟩ (by rw [← map_mul, ← map_mul, hc])
    exact (Subgroup.mem_map_iff_mem hf).mp this
  comm_le := by
    have h1 := h.comm_le
    rw [← Subgroup.map_commutator] at h1
    exact (Subgroup.map_le_map_iff_of_injective hf).mp h1
  one_lt := h.one_lt
  card_S := by
    have := h.card_S
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at this
  card_V := by
    have := h.card_V
    rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at this

end NatLike

def PartnerRep (S F V : Subgroup T) : Prop :=
  ∀ Y : Subgroup T, Adm S Y → F = V ⊔ (F ⊓ Subgroup.centralizer (Y : Set T))

namespace PartnerRep

variable {f : T →* G'} {S F V : Subgroup T}

theorem map (hf : Function.Injective f) (h : PartnerRep S F V) :
    PartnerRep (S.map f) (F.map f) (V.map f) := by
  rintro Y' ⟨A', hA', hYA'⟩
  obtain ⟨A, hA, rfl⟩ := exists_of_isMaxElemAbelian_map hf hA'
  have hYr : Y' ≤ f.range := hYA'.trans (Subgroup.map_le_range f A)
  have hYmap : (Y'.comap f).map f = Y' := Subgroup.map_comap_eq_self hYr
  have hYA : Y'.comap f ≤ A := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hYA' hx
    rw [← hf hax]
    exact ha
  have := h (Y'.comap f) ⟨A, hA, hYA⟩
  conv_lhs => rw [this]
  rw [Subgroup.map_sup, map_inf_centralizer hf, hYmap]

theorem of_map (hf : Function.Injective f) (h : PartnerRep (S.map f) (F.map f) (V.map f)) :
    PartnerRep S F V := by
  rintro Y ⟨A, hA, hYA⟩
  have h1 := h (Y.map f) ⟨A.map f, (isMaxElemAbelian_map_iff hf).mpr hA, Subgroup.map_mono hYA⟩
  rw [← map_inf_centralizer hf, ← Subgroup.map_sup] at h1
  exact Subgroup.map_injective hf h1

end PartnerRep

structure PartnerData (S Q F V Z : Subgroup T) (q : ℕ) : Prop where
  core : PartnerCore S F Z
  nat : NatLike S Q V Z q
  rep : PartnerRep S F V

namespace PartnerData

variable {f : T →* G'} {S Q F V Z : Subgroup T} {q : ℕ}

theorem map (hf : Function.Injective f) (h : PartnerData S Q F V Z q) :
    PartnerData (S.map f) (Q.map f) (F.map f) (V.map f) (Z.map f) q :=
  ⟨h.core.map hf, h.nat.map hf, h.rep.map hf⟩

theorem of_map (hf : Function.Injective f)
    (h : PartnerData (S.map f) (Q.map f) (F.map f) (V.map f) (Z.map f) q) :
    PartnerData S Q F V Z q :=
  ⟨h.core.of_map hf, h.nat.of_map hf, h.rep.of_map hf⟩

end PartnerData

end Transport

section Seed

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem PartnerCore.ofSeed (h : IsSeed S ρ (Ecore G) ψ) :
    PartnerCore (S : Subgroup G) (Fcore G) (Zfix S) where
  normal := fun s _ x hx => (inferInstance : (Fcore G).Normal).conj_mem x hx s
  zcentral := fun s hs z hz => IsSeed.Zfix_central hz hs
  commJ := h.commutator_thompsonJ_Fcore
  commA := by
    intro A hA
    by_cases hAQ : A ≤ CFSG.pCore 2 G
    · left
      exact IsSeed.commutator_A_Fcore_of_le hA hAQ
    · right
      exact h.commutator_A_Fcore hA hAQ
  sup_max := by
    intro A hA
    have h1 := (h.isMaxElemAbelian_core_sup_Fcore hA).2
    rw [← h.inf_centralizer_Fcore hA, sup_comm] at h1
    exact h1

theorem NatLike.ofSeed (h : IsSeed S ρ (Ecore G) ψ) :
    NatLike (S : Subgroup G) (CFSG.pCore 2 G) (Vmod G) (Zfix S) (Nat.card k) where
  Q_le := core_le_sylow S
  V_le := Vmod_le_sylow
  Q_normal := fun s _ x hx => (inferInstance : (CFSG.pCore 2 G).Normal).conj_mem x hx s
  V_normal := fun s _ x hx => (inferInstance : (Vmod G).Normal).conj_mem x hx s
  V_elem := isElemAbelian_Vmod
  Z_le := inf_le_left
  Z_central := fun s hs z hz => IsSeed.Zfix_central hz hs
  Q_comm := fun s hs v hv => Ecore_commute_core hs (Vmod_le_Ecore hv)
  cent_le := fun s hs hc => by
    have : s ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (Vmod G : Set G) :=
      ⟨hs, Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
    rwa [h.sylow_inf_centralizer_Vmod] at this
  fix := fun s hs hsQ v hv hc => h.sylow_not_core_comm_Vmod hs hsQ hv hc
  comm_le := (h.sylow_commutator_Vmod).le
  one_lt := by
    obtain ⟨n, hn, hk⟩ := h.card_k
    rw [hk]
    exact Nat.one_lt_two_pow (by omega)
  card_S := h.card_k_mul_card_core.symm
  card_V := h.card_k_mul_card_Zfix.symm

theorem PartnerRep.ofSeed (h : IsSeed S ρ (Ecore G) ψ) :
    PartnerRep (S : Subgroup G) (Fcore G) (Vmod G) :=
  fun _ ⟨_, hA, hYA⟩ => h.Fcore_eq_Vmod_sup_cent hA hYA

theorem PartnerData.ofSeed (h : IsSeed S ρ (Ecore G) ψ) :
    PartnerData (S : Subgroup G) (CFSG.pCore 2 G) (Fcore G) (Vmod G) (Zfix S) (Nat.card k) :=
  ⟨PartnerCore.ofSeed h, NatLike.ofSeed h, PartnerRep.ofSeed h⟩

theorem PartnerData.fp_le_core {Q' Fp Vp Zp : Subgroup G} {q' : ℕ}
    (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerData (S : Subgroup G) Q' Fp Vp Zp q')
    (hV : Vp ≤ CFSG.pCore 2 G) : Fp ≤ CFSG.pCore 2 G := by
  have h1 := hp.rep (Fcore G) h.adm_Fcore
  have h2 : Fp ⊓ Subgroup.centralizer (Fcore G : Set G) ≤ CFSG.pCore 2 G := fun x hx =>
    h.sylow_inf_centralizer_Fcore_le ⟨hp.core.fp_le hx.1, hx.2⟩
  calc Fp = Vp ⊔ (Fp ⊓ Subgroup.centralizer (Fcore G : Set G)) := h1
    _ ≤ CFSG.pCore 2 G := sup_le hV h2

end Seed

section Outside

variable {P : Type*} [Group P] {Q₁ V₁ Z₁ Q₂ V₂ Z₂ : Subgroup P} {q₁ q₂ : ℕ}

theorem NatLike.normal_top (h : NatLike ⊤ Q₁ V₁ Z₁ q₁) : Q₁.Normal :=
  ⟨fun x hx g => h.Q_normal g trivial x hx⟩

theorem NatLike.inf_eq_of_not_le (h₁ : NatLike ⊤ Q₁ V₁ Z₁ q₁) (h₂ : NatLike ⊤ Q₂ V₂ Z₂ q₂)
    (hV : ¬ V₁ ≤ Q₂) : V₁ ⊓ Q₂ = Z₁ ∧ ¬ V₂ ≤ Q₁ := by
  obtain ⟨w, hw, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hV
  have hex : ∃ v ∈ V₂, w * v ≠ v * w := by
    by_contra hall
    push Not at hall
    exact hwQ (h₂.cent_le w trivial fun v hv => hall v hv)
  obtain ⟨v, hv, hne⟩ := hex
  have hvQ : v ∉ Q₁ := fun hvQ => hne (h₁.Q_comm v hvQ w hw).symm
  refine ⟨le_antisymm ?_ ?_, fun hle => hvQ (hle hv)⟩
  · rintro x ⟨hx1, hx2⟩
    exact h₁.fix v trivial hvQ x hx1 (h₂.Q_comm x hx2 v hv).symm
  · intro z hz
    refine ⟨h₁.Z_le hz, h₂.cent_le z trivial fun v' _ => ?_⟩
    exact h₁.Z_central v' trivial z hz |>.symm

variable [Finite P]

theorem NatLike.card_quot_of_inf_eq [Q₂.Normal] (h₁ : NatLike ⊤ Q₁ V₁ Z₁ q₁)
    (h₂ : NatLike ⊤ Q₂ V₂ Z₂ q₂) (hinf : V₁ ⊓ Q₂ = Z₁) :
    Nat.card (V₁.map (QuotientGroup.mk' Q₂)) = q₁ ∧ Nat.card (P ⧸ Q₂) = q₂ := by
  have hker : (QuotientGroup.mk' Q₂).ker = Q₂ := QuotientGroup.ker_mk' Q₂
  have h1 := card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' Q₂) V₁
  rw [hker, hinf, h₁.card_V] at h1
  have hpos : 0 < Nat.card Z₁ := Nat.card_pos
  refine ⟨?_, ?_⟩
  · exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← h1, mul_comm])).symm
  · have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup Q₂
    have h3 := h₂.card_S
    rw [Subgroup.card_top] at h3
    have hpos2 : 0 < Nat.card Q₂ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos2 (by rw [← h2, h3, mul_comm])

theorem NatLike.outside (h₁ : NatLike ⊤ Q₁ V₁ Z₁ q₁) (h₂ : NatLike ⊤ Q₂ V₂ Z₂ q₂)
    (hV : ¬ V₁ ≤ Q₂) : q₁ = q₂ ∧ V₁ ⊓ Q₂ = Z₁ ∧ Q₂ ⊔ V₁ = ⊤ := by
  obtain ⟨hinf, hV'⟩ := h₁.inf_eq_of_not_le h₂ hV
  obtain ⟨hinf', -⟩ := h₂.inf_eq_of_not_le h₁ hV'
  have := h₁.normal_top
  have := h₂.normal_top
  obtain ⟨hc1, hc2⟩ := h₁.card_quot_of_inf_eq h₂ hinf
  obtain ⟨hc1', hc2'⟩ := h₂.card_quot_of_inf_eq h₁ hinf'
  have hle1 : q₁ ≤ q₂ :=
    calc q₁ = Nat.card (V₁.map (QuotientGroup.mk' Q₂)) := hc1.symm
      _ ≤ Nat.card (P ⧸ Q₂) := Subgroup.card_le_card_group _
      _ = q₂ := hc2
  have hle2 : q₂ ≤ q₁ :=
    calc q₂ = Nat.card (V₂.map (QuotientGroup.mk' Q₁)) := hc1'.symm
      _ ≤ Nat.card (P ⧸ Q₁) := Subgroup.card_le_card_group _
      _ = q₁ := hc2'
  have hq : q₁ = q₂ := le_antisymm hle1 hle2
  refine ⟨hq, hinf, ?_⟩
  have htop : V₁.map (QuotientGroup.mk' Q₂) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hc1, hc2, hq]
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' Q₂ x ∈ V₁.map (QuotientGroup.mk' Q₂) := by rw [htop]; trivial
  obtain ⟨v, hv, hvx⟩ := hx
  have : v⁻¹ * x ∈ Q₂ := (QuotientGroup.eq (a := v) (b := x)).mp hvx
  have hx' : x = v * (v⁻¹ * x) := by group
  rw [hx']
  exact mul_mem (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left this)

end Outside

end CFSG.Quasithin
