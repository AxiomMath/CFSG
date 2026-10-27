module

public import CFSG.Quasithin.EmptyFaithful.S152NPairB
public import CFSG.Quasithin.EmptyFaithful.S14117Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem exists_sq_eq_one {K : Type} [Group K] {P₁ P₂ : Subgroup K}
    (hc : ∀ u ∈ P₁, ∀ v ∈ P₂, u * v = v * u) (hinf : P₁ ⊓ P₂ = ⊥) {s : K}
    (h₁ : ∀ u ∈ P₁, s * u * s⁻¹ ∈ P₂) (h₂ : ∀ v ∈ P₂, s * v * s⁻¹ ∈ P₁)
    (hs : s ^ 2 ∈ P₁ ⊔ P₂) : ∃ u ∈ P₁, (s * u⁻¹) ^ 2 = 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_mem_sup_of_normalizes (K := P₁) (M := P₂)
    (fun k hk m hm => by rw [hc k hk m hm, mul_inv_cancel_right]; exact hm) hs
  have hx : s * v * s⁻¹ ∈ P₁ := h₂ v hv
  have hy : s * u * s⁻¹ ∈ P₂ := h₁ u hu
  have hxy : (s * v * s⁻¹) * (s * u * s⁻¹) = u * v := by
    have e : (s * v * s⁻¹) * (s * u * s⁻¹) = s * (v * u) * s⁻¹ := by group
    rw [e, ← hc u hu v hv]
    have e2 : s * (u * v) * s⁻¹ = s ^ 2 := by
      rw [← huv]; group
    exact e2.trans huv
  have key : u⁻¹ * (s * v * s⁻¹) = v * (s * u * s⁻¹)⁻¹ := by
    calc u⁻¹ * (s * v * s⁻¹)
        = u⁻¹ * ((s * v * s⁻¹) * (s * u * s⁻¹)) * (s * u * s⁻¹)⁻¹ := by group
      _ = u⁻¹ * (u * v) * (s * u * s⁻¹)⁻¹ := by rw [hxy]
      _ = v * (s * u * s⁻¹)⁻¹ := by group
  have hmem : u⁻¹ * (s * v * s⁻¹) ∈ P₁ ⊓ P₂ := by
    refine ⟨P₁.mul_mem (P₁.inv_mem hu) hx, ?_⟩
    rw [key]
    exact P₂.mul_mem hv (P₂.inv_mem hy)
  rw [hinf, Subgroup.mem_bot] at hmem
  have hyv : s * u * s⁻¹ = v := by
    have h' : v * (s * u * s⁻¹)⁻¹ = 1 := by rw [← key]; exact hmem
    exact (mul_inv_eq_one.mp h').symm
  refine ⟨u, hu, ?_⟩
  have e : (s * u⁻¹) ^ 2 = (s * u⁻¹ * s⁻¹) * s ^ 2 * u⁻¹ := by
    rw [pow_two (s * u⁻¹), pow_two s]; group
  have h1 : s * u⁻¹ * s⁻¹ = v⁻¹ := by rw [← hyv]; group
  rw [e, h1, huv]
  have hcomm := hc u hu v hv
  calc v⁻¹ * (u * v) * u⁻¹ = v⁻¹ * (v * u) * u⁻¹ := by rw [hcomm]
    _ = 1 := by group

section Quot

variable {H : Subgroup G}

abbrev mkq (H : Subgroup G) (g : G) (hg : g ∈ H) : OTwoQuot H := QuotientGroup.mk ⟨g, hg⟩

theorem mkq_mul {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    mkq H (a * b) (H.mul_mem ha hb) = mkq H a ha * mkq H b hb := rfl

theorem mkq_inv {a : G} (ha : a ∈ H) : mkq H a⁻¹ (H.inv_mem ha) = (mkq H a ha)⁻¹ := rfl

theorem mkq_eq_one_iff {a : G} (ha : a ∈ H) : mkq H a ha = 1 ↔ a ∈ pCoreOf 2 H := by
  unfold mkq
  rw [QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]

theorem imageOTwoQuot_equiv {F : Subgroup G} (hFH : F ≤ H) (θ : ↥F →* Equiv.Perm (Fin 3))
    (hθs : Function.Surjective θ) (hker : ∀ f : ↥F, θ f = 1 ↔ (f : G) ∈ pCoreOf 2 H) :
    Nonempty (↥(imageOTwoQuot H (F ⊔ pCoreOf 2 H)) ≃* Equiv.Perm (Fin 3)) := by
  let π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  have hmem : ∀ f : ↥F, π (Subgroup.inclusion hFH f) ∈ imageOTwoQuot H (F ⊔ pCoreOf 2 H) :=
    fun f => mem_imageOTwoQuot_iff.mpr ⟨f, hFH f.2, Subgroup.mem_sup_left f.2, rfl⟩
  let ρ : ↥F →* ↥(imageOTwoQuot H (F ⊔ pCoreOf 2 H)) :=
    (π.comp (Subgroup.inclusion hFH)).codRestrict _ hmem
  have hρs : Function.Surjective ρ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hw
    obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_normalizes
      (fun k hk m hm => (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (hFH hk)) m).mp hm) hx
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    have hqH : q ∈ H := pCoreOf_le 2 H hq
    have h1 : mkq H q hqH = 1 := (mkq_eq_one_iff hqH).mpr hq
    have h2 : mkq H (f * q) hxH = mkq H f (hFH hf) * mkq H q hqH := mkq_mul (hFH hf) hqH
    show mkq H f (hFH hf) = mkq H (f * q) hxH
    rw [h2, h1, mul_one]
  have hker' : ρ.ker = θ.ker := by
    ext f
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker f]
    constructor
    · intro h
      have h' : mkq H f (hFH f.2) = 1 := congrArg Subtype.val h
      exact (mkq_eq_one_iff _).mp h'
    · intro h
      exact Subtype.ext ((mkq_eq_one_iff (hFH f.2)).mpr h)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs))⟩

end Quot

variable {H U L N B F₁ F₂ X₁ X₂ : Subgroup G}

namespace PairStep

variable (P : PairStep H U L N B F₁ F₂ X₁ X₂)

include P in
theorem F₁_le_B : F₁ ≤ B := le_sup_left.trans P.FFB.le

include P in
theorem F₂_le_B : F₂ ≤ B := le_sup_right.trans P.FFB.le

include P in
theorem mem_cSecIn_B {Y : Subgroup G} {f : G} :
    f ∈ cSecIn B L Y ↔ f ∈ B ∧ ∀ y ∈ Y, f * y * f⁻¹ * y⁻¹ ∈ L :=
  ⟨fun h => mem_cSecIn P.B_le_normalizer_L h, fun h => Subgroup.subset_closure h⟩

include P in
theorem card_X₁ [Finite G] : Nat.card X₁ = 4 * Nat.card L := by
  have := Subgroup.relIndex_mul_card (H := L) (K := X₁)
  rw [P.card₁, inf_eq_left.mpr P.L_le₁] at this
  exact this.symm

include P in
theorem card_X₂ [Finite G] : Nat.card X₂ = 4 * Nat.card L := by
  have := Subgroup.relIndex_mul_card (H := L) (K := X₂)
  rw [P.card₂, inf_eq_left.mpr P.L_le₂] at this
  exact this.symm

include P in
theorem stab {σ : G} (hσH : σ ∈ H) (hσ : ∀ x ∈ X₁, σ * x * σ⁻¹ ∈ X₁) : σ ∈ B := by
  by_contra hσB
  obtain ⟨a, haH, haB, ha⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp P.B_idx
  have hσa : σ * a ∈ B := (ha σ hσH).resolve_right hσB
  have hall : ∀ h ∈ H, ∀ x ∈ X₁, h * x * h⁻¹ ∈ X₁ := by
    intro h hh x hx
    by_cases hhB : h ∈ B
    · exact P.B_norm₁ h hhB x hx
    · have hha : h * a ∈ B := (ha h hh).resolve_right hhB
      have hb : h * σ⁻¹ ∈ B := by
        have := B.mul_mem hha (B.inv_mem hσa)
        have e : h * a * (σ * a)⁻¹ = h * σ⁻¹ := by group
        rwa [e] at this
      have e2 : h * x * h⁻¹ = (h * σ⁻¹) * (σ * x * σ⁻¹) * (h * σ⁻¹)⁻¹ := by group
      rw [e2]
      exact P.B_norm₁ _ hb _ (hσ x hx)
  have hIN : IsNormalIn H U X₁ := ⟨P.X₁_le.trans P.step.1.1, hall⟩
  rcases P.step.2.2.2 X₁ hIN P.L_le₁ P.X₁_le with h | h
  · have h4 := P.card₁
    rw [h, Subgroup.relIndex_self] at h4
    omega
  · have : X₂ ≤ X₁ := h ▸ P.X₂_le
    have h5 := P.inf_eq
    rw [inf_eq_right.mpr this] at h5
    have h4 := P.card₂
    rw [h5, Subgroup.relIndex_self] at h4
    omega

include P in
theorem conj_comm_mul {f a b : G} (hf : f ∈ H) (ha : a ∈ N) (hb : b ∈ N) :
    f * (a * b) * f⁻¹ * (a * b)⁻¹ = (f * a * f⁻¹ * a⁻¹) * (f * b * f⁻¹ * b⁻¹) := by
  have hq : f * b * f⁻¹ ∈ N := P.H_norm_N f hf b hb
  have hc : Commute (f * b * f⁻¹) a⁻¹ := P.N_abelian _ hq _ (N.inv_mem ha)
  have hab : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    rw [mul_inv_rev]
    exact (P.N_abelian a⁻¹ (N.inv_mem ha) b⁻¹ (N.inv_mem hb)).symm
  have e : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
  rw [e, hab]
  exact hc.mul_mul_mul_comm (f * a * f⁻¹) b⁻¹

include P in
theorem conj_dichotomy [Finite G] {t : G} (ht : t ∈ H) :
    conjSub t X₁ = X₁ ∨ conjSub t X₁ = X₂ := by
  set Y := conjSub t X₁ with hY
  have hLY : L ≤ Y := fun l hl => mem_conjSub.mpr (P.L_le₁ (by
    simpa using P.H_norm_L t⁻¹ (H.inv_mem ht) l hl))
  have hYN : Y ≤ N := fun y hy => by
    have h1 : t⁻¹ * y * t ∈ X₁ := mem_conjSub.mp hy
    have h2 := P.H_norm_N t ht _ (P.X₁_le h1)
    have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
    rwa [e] at h2
  have hYB : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y := by
    intro b hb y hy
    refine mem_conjSub.mpr ?_
    have hb' : t⁻¹ * b * t ∈ B := by simpa using P.B_normal t⁻¹ (H.inv_mem ht) b hb
    have h1 := P.B_norm₁ _ hb' _ (mem_conjSub.mp hy)
    have e : t⁻¹ * (b * y * b⁻¹) * t = (t⁻¹ * b * t) * (t⁻¹ * y * t) * (t⁻¹ * b * t)⁻¹ := by group
    rw [e]
    exact h1
  have hcardY : Nat.card Y = Nat.card X₁ :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj t))
  have hYX₁comm : ∀ k ∈ Y, ∀ m ∈ X₁, k * m * k⁻¹ ∈ X₁ := fun k hk m hm => by
    rw [P.N_abelian k (hYN hk) m (P.X₁_le hm), mul_inv_cancel_right]
    exact hm
  have hA₁ : Y ⊓ X₁ = L ∨ Y ⊓ X₁ = X₁ := by
    refine P.irr₁ (Y ⊓ X₁) (le_inf hLY P.L_le₁) inf_le_right ?_
    intro f hf y hy
    exact ⟨hYB f (P.F₁_le_B hf) y hy.1, P.F₁_norm f hf y hy.2⟩
  rcases hA₁ with hA₁ | hA₁
  · have hA₂ : Y ⊓ X₂ = L ∨ Y ⊓ X₂ = X₂ := by
      refine P.irr₂ (Y ⊓ X₂) (le_inf hLY P.L_le₂) inf_le_right ?_
      intro f hf y hy
      exact ⟨hYB f (P.F₂_le_B hf) y hy.1, P.F₂_norm f hf y hy.2⟩
    rcases hA₂ with hA₂ | hA₂
    · exfalso
      have hZ : ∀ f ∈ F₂, ∀ z ∈ Y ⊔ X₁, f * z * f⁻¹ ∈ Y ⊔ X₁ := by
        intro f hf z hz
        obtain ⟨y, hy, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_normalizes hYX₁comm hz
        have e : f * (y * x) * f⁻¹ = (f * y * f⁻¹) * (f * x * f⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hYB f (P.F₂_le_B hf) y hy))
          (Subgroup.mem_sup_right (P.B_norm₁ f (P.F₂_le_B hf) x hx))
      have hA₃ : (Y ⊔ X₁) ⊓ X₂ = L ∨ (Y ⊔ X₁) ⊓ X₂ = X₂ := by
        refine P.irr₂ ((Y ⊔ X₁) ⊓ X₂) (le_inf (hLY.trans le_sup_left) P.L_le₂) inf_le_right ?_
        intro f hf w hw
        exact ⟨hZ f hf w hw.1, P.F₂_norm f hf w hw.2⟩
      have hX₂Z : X₂ ≤ Y ⊔ X₁ := by
        rcases hA₃ with hA₃ | hA₃
        · exfalso
          have hYX₁ : Y ≤ X₁ := by
            intro y hy
            obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_of_mem_sup_of_normalizes
              (K := X₁) (M := X₂) (fun k hk m hm => by
                rw [P.N_abelian k (P.X₁_le hk) m (P.X₂_le hm), mul_inv_cancel_right]
                exact hm) (P.sup_eq ▸ hYN hy)
            have hu₂Z : u₂ ∈ (Y ⊔ X₁) ⊓ X₂ := by
              refine ⟨?_, hu₂⟩
              have := Subgroup.mul_mem _ (Subgroup.mem_sup_right (X₁.inv_mem hu₁))
                (Subgroup.mem_sup_left hy : u₁ * u₂ ∈ Y ⊔ X₁)
              simpa using this
            rw [hA₃] at hu₂Z
            exact X₁.mul_mem hu₁ (P.L_le₁ hu₂Z)
          have hYL : Y = L := by
            rw [← hA₁]
            exact (inf_eq_left.mpr hYX₁).symm
          have h1 := hcardY
          rw [hYL, P.card_X₁] at h1
          have := Nat.card_pos (α := L)
          omega
        · intro x hx
          have : x ∈ (Y ⊔ X₁) ⊓ X₂ := by rw [hA₃]; exact hx
          exact this.1
      have htriv : ∀ f ∈ F₂, ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L := by
        intro f hf x hx
        obtain ⟨y, hy, x₁, hx₁, rfl⟩ := exists_mul_of_mem_sup_of_normalizes hYX₁comm (hX₂Z hx)
        have hfH : f ∈ H := P.F₂_le hf
        rw [P.conj_comm_mul hfH (hYN hy) (P.X₁_le hx₁)]
        refine L.mul_mem ?_ (P.F₂_triv f hf x₁ hx₁)
        have hfy : f * y * f⁻¹ * y⁻¹ ∈ Y ⊓ X₂ := by
          refine ⟨Y.mul_mem (hYB f (P.F₂_le_B hf) y hy) (Y.inv_mem hy), ?_⟩
          obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_of_mem_sup_of_normalizes
            (K := X₁) (M := X₂) (fun k hk m hm => by
              rw [P.N_abelian k (P.X₁_le hk) m (P.X₂_le hm), mul_inv_cancel_right]
              exact hm) (P.sup_eq ▸ hYN hy)
          rw [P.conj_comm_mul hfH (P.X₁_le hu₁) (P.X₂_le hu₂)]
          exact X₂.mul_mem (P.L_le₂ (P.F₂_triv f hf u₁ hu₁))
            (by
              have := X₂.mul_mem (P.F₂_norm f hf u₂ hu₂) (X₂.inv_mem hu₂)
              exact this)
        rw [hA₂] at hfy
        exact hfy
      obtain ⟨θ, hθs, hθk⟩ := P.θ₂
      have hall : ∀ f : ↥F₂, θ f = 1 := by
        intro f
        have hmem : (f : G) ∈ cSecIn F₂ L X₂ :=
          Subgroup.subset_closure ⟨f.2, htriv f f.2⟩
        have : f ∈ θ.ker := by
          rw [hθk]
          exact Subgroup.mem_subgroupOf.mpr hmem
        exact this
      obtain ⟨f, hf⟩ := hθs (Equiv.swap (0 : Fin 3) 1)
      have h01 : (Equiv.swap (0 : Fin 3) 1) ≠ 1 := by decide
      exact h01 (hf.symm.trans (hall f))
    · right
      have hle : X₂ ≤ Y := fun x hx => by
        have : x ∈ Y ⊓ X₂ := by rw [hA₂]; exact hx
        exact this.1
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hcardY, P.card_X₁, P.card_X₂]
  · left
    have hle : X₁ ≤ Y := fun x hx => by
      have : x ∈ Y ⊓ X₁ := by rw [hA₁]; exact hx
      exact this.1
    exact (Subgroup.eq_of_le_of_card_ge hle hcardY.le).symm

include P in
theorem conjSub_eq_of_not_mem [Finite G] {t : G} (ht : t ∈ H) (htB : t ∉ B) :
    conjSub t X₁ = X₂ := by
  rcases P.conj_dichotomy ht with h | h
  · exfalso
    exact htB (P.stab ht fun x hx => by
      have := mul_mem_conjSub (g := t) hx
      rwa [h] at this)
  · exact h

include P in
theorem conjSub_eq_of_not_mem' [Finite G] {t : G} (ht : t ∈ H) (htB : t ∉ B) :
    conjSub t X₂ = X₁ := by
  have htB' : t⁻¹ ∉ B := fun h => htB (by simpa using B.inv_mem h)
  have h1 := P.conjSub_eq_of_not_mem (H.inv_mem ht) htB'
  rw [← h1, conjSub_inv_conjSub]

include P in
theorem conjSub_cSecIn {t : G} (ht : t ∈ H) (Y : Subgroup G) :
    conjSub t (cSecIn B L Y) = cSecIn B L (conjSub t Y) := by
  ext g
  rw [mem_conjSub, P.mem_cSecIn_B, P.mem_cSecIn_B]
  constructor
  · rintro ⟨hgB, hg⟩
    refine ⟨?_, fun y hy => ?_⟩
    · have := P.B_normal t ht _ hgB
      have e : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
      rwa [e] at this
    · have hy' : t⁻¹ * y * t ∈ Y := mem_conjSub.mp hy
      have h3 := hg _ hy'
      have h4 := P.H_norm_L t ht _ h3
      have e : t * (t⁻¹ * g * t * (t⁻¹ * y * t) * (t⁻¹ * g * t)⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹
          = g * y * g⁻¹ * y⁻¹ := by group
      rwa [e] at h4
  · rintro ⟨hgB, hg⟩
    refine ⟨?_, fun y hy => ?_⟩
    · simpa using P.B_normal t⁻¹ (H.inv_mem ht) _ hgB
    · have hy' : t * y * t⁻¹ ∈ conjSub t Y := mul_mem_conjSub hy
      have h3 := hg _ hy'
      have h4 := P.H_norm_L t⁻¹ (H.inv_mem ht) _ h3
      have e : t⁻¹ * (g * (t * y * t⁻¹) * g⁻¹ * (t * y * t⁻¹)⁻¹) * t⁻¹⁻¹
          = t⁻¹ * g * t * y * (t⁻¹ * g * t)⁻¹ * y⁻¹ := by group
      rwa [e] at h4

include P in
theorem sq_mem_B {t : G} (ht : t ∈ H) : t * t ∈ B := by
  have hB' : (B.subgroupOf H).index = 2 := P.B_idx
  have : (⟨t, ht⟩ * ⟨t, ht⟩ : ↥H) ∈ B.subgroupOf H :=
    (Subgroup.mul_mem_iff_of_index_two hB').mpr Iff.rfl
  exact Subgroup.mem_subgroupOf.mp this

include P in
theorem mul_inv_mem_B {a b : G} (ha : a ∈ H) (hb : b ∈ H) (haB : a ∉ B) (hbB : b ∉ B) :
    a * b⁻¹ ∈ B := by
  obtain ⟨c, hcH, hcB, hc⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp P.B_idx
  have h1 : a * c ∈ B := (hc a ha).resolve_right haB
  have h2 : b * c ∈ B := (hc b hb).resolve_right hbB
  have := B.mul_mem h1 (B.inv_mem h2)
  have e : a * c * (b * c)⁻¹ = a * b⁻¹ := by group
  rwa [e] at this

include P in
theorem swap [Finite G] : ∃ t ∈ H, t ^ 2 ∈ pCoreOf 2 H ∧
    conjSub t (F₁ ⊔ pCoreOf 2 H) = F₂ ⊔ pCoreOf 2 H ∧
    H = ((F₁ ⊔ pCoreOf 2 H) ⊔ (F₂ ⊔ pCoreOf 2 H)) ⊔ Subgroup.zpowers t := by
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hH₁H : F₁ ⊔ pCoreOf 2 H ≤ H := sup_le P.F₁_le hQH
  have hH₂H : F₂ ⊔ pCoreOf 2 H ≤ H := sup_le P.F₂_le hQH
  have hH₁B : F₁ ⊔ pCoreOf 2 H ≤ B := sup_le P.F₁_le_B P.Q_le_B
  have hBH₁₂ : B ≤ (F₁ ⊔ pCoreOf 2 H) ⊔ (F₂ ⊔ pCoreOf 2 H) :=
    P.FFB.symm.le.trans (sup_le_sup le_sup_left le_sup_left)
  have hsw₁ : ∀ t ∈ H, t ∉ B → conjSub t (F₁ ⊔ pCoreOf 2 H) = F₂ ⊔ pCoreOf 2 H := by
    intro t ht htB
    rw [← P.C₂_eq, P.conjSub_cSecIn ht, P.conjSub_eq_of_not_mem' ht htB, P.C₁_eq]
  have hsw₂ : ∀ t ∈ H, t ∉ B → conjSub t (F₂ ⊔ pCoreOf 2 H) = F₁ ⊔ pCoreOf 2 H := by
    intro t ht htB
    rw [← P.C₁_eq, P.conjSub_cSecIn ht, P.conjSub_eq_of_not_mem ht htB, P.C₂_eq]
  obtain ⟨a₀, ha₀H, ha₀B, -⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp P.B_idx
  have hc : ∀ u ∈ imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H), ∀ v ∈ imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H),
      u * v = v * u := by
    intro u hu v hv
    obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨y, hyH, hy, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H := P.comm_H hx hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)) (H.inv_mem hyH)
    have h1 : mkq H (x * y * x⁻¹ * y⁻¹) hmem = 1 := (mkq_eq_one_iff hmem).mpr hcomm
    have h2 : mkq H (x * y * x⁻¹ * y⁻¹) hmem =
        mkq H x hxH * mkq H y hyH * (mkq H x hxH)⁻¹ * (mkq H y hyH)⁻¹ := rfl
    rw [h2] at h1
    show mkq H x hxH * mkq H y hyH = mkq H y hyH * mkq H x hxH
    calc mkq H x hxH * mkq H y hyH
        = (mkq H x hxH * mkq H y hyH * (mkq H x hxH)⁻¹ * (mkq H y hyH)⁻¹) *
          (mkq H y hyH * mkq H x hxH) := by group
      _ = mkq H y hyH * mkq H x hxH := by rw [h1, one_mul]
  have hinf : imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H) ⊓ imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw₁, hw₂⟩
    obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hw₁
    obtain ⟨y, hyH, hy, hxy⟩ := mem_imageOTwoQuot_iff.mp hw₂
    have hmem : x * y⁻¹ ∈ H := H.mul_mem hxH (H.inv_mem hyH)
    have hxy' : mkq H y hyH = mkq H x hxH := hxy
    have h1 : mkq H (x * y⁻¹) hmem = 1 := by
      rw [mkq_mul hxH (H.inv_mem hyH), mkq_inv hyH, hxy', mul_inv_cancel]
    have hq : x * y⁻¹ ∈ pCoreOf 2 H := (mkq_eq_one_iff hmem).mp h1
    have hxH₂ : x ∈ F₂ ⊔ pCoreOf 2 H := by
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_right hq : x * y⁻¹ ∈ F₂ ⊔ pCoreOf 2 H) hy
      simpa using this
    have hxQ : x ∈ pCoreOf 2 H := by
      rw [← P.inf_H]
      exact ⟨hx, hxH₂⟩
    rw [Subgroup.mem_bot]
    exact (mkq_eq_one_iff hxH).mpr hxQ
  have h₁ : ∀ u ∈ imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H),
      mkq H a₀ ha₀H * u * (mkq H a₀ ha₀H)⁻¹ ∈ imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H) := by
    intro u hu
    obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hconj : a₀ * x * a₀⁻¹ ∈ F₂ ⊔ pCoreOf 2 H := by
      have := mul_mem_conjSub (g := a₀) hx
      rwa [hsw₁ a₀ ha₀H ha₀B] at this
    have hmem : a₀ * x * a₀⁻¹ ∈ H := H.mul_mem (H.mul_mem ha₀H hxH) (H.inv_mem ha₀H)
    exact mem_imageOTwoQuot_iff.mpr ⟨a₀ * x * a₀⁻¹, hmem, hconj, rfl⟩
  have h₂ : ∀ v ∈ imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H),
      mkq H a₀ ha₀H * v * (mkq H a₀ ha₀H)⁻¹ ∈ imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H) := by
    intro v hv
    obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    have hconj : a₀ * x * a₀⁻¹ ∈ F₁ ⊔ pCoreOf 2 H := by
      have := mul_mem_conjSub (g := a₀) hx
      rwa [hsw₂ a₀ ha₀H ha₀B] at this
    have hmem : a₀ * x * a₀⁻¹ ∈ H := H.mul_mem (H.mul_mem ha₀H hxH) (H.inv_mem ha₀H)
    exact mem_imageOTwoQuot_iff.mpr ⟨a₀ * x * a₀⁻¹, hmem, hconj, rfl⟩
  have hs : (mkq H a₀ ha₀H) ^ 2 ∈ imageOTwoQuot H (F₁ ⊔ pCoreOf 2 H) ⊔
      imageOTwoQuot H (F₂ ⊔ pCoreOf 2 H) := by
    have hmem : a₀ * a₀ ∈ H := H.mul_mem ha₀H ha₀H
    have h12 : a₀ * a₀ ∈ (F₁ ⊔ pCoreOf 2 H) ⊔ (F₂ ⊔ pCoreOf 2 H) := hBH₁₂ (P.sq_mem_B ha₀H)
    have := (mem_imageOTwoQuot_iff (M := H)).mpr ⟨a₀ * a₀, hmem, h12, rfl⟩
    rw [imageOTwoQuot_sup hH₁H hH₂H] at this
    have e : (mkq H a₀ ha₀H) ^ 2 = mkq H (a₀ * a₀) hmem := by rw [pow_two]; rfl
    rw [e]
    exact this
  obtain ⟨u, hu, hu2⟩ := exists_sq_eq_one hc hinf h₁ h₂ hs
  obtain ⟨a, haH, haH₁, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  have htH : a₀ * a⁻¹ ∈ H := H.mul_mem ha₀H (H.inv_mem haH)
  have htB : a₀ * a⁻¹ ∉ B := by
    intro h
    apply ha₀B
    have := B.mul_mem h (hH₁B haH₁)
    simpa using this
  refine ⟨a₀ * a⁻¹, htH, ?_, ?_, ?_⟩
  · have e : mkq H ((a₀ * a⁻¹) ^ 2) (H.pow_mem htH 2) = 1 := by
      have e' : mkq H ((a₀ * a⁻¹) ^ 2) (H.pow_mem htH 2) =
          (mkq H a₀ ha₀H * (mkq H a haH)⁻¹) ^ 2 := rfl
      rw [e']
      exact hu2
    exact (mkq_eq_one_iff _).mp e
  · have hH₁a : conjSub a⁻¹ (F₁ ⊔ pCoreOf 2 H) = F₁ ⊔ pCoreOf 2 H := by
      ext x
      rw [mem_conjSub, inv_inv]
      constructor
      · intro h
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haH₁) h) haH₁
        simpa [mul_assoc] using this
      · intro h
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haH₁ h) (Subgroup.inv_mem _ haH₁)
    rw [conjSub_mul, hH₁a, hsw₁ a₀ ha₀H ha₀B]
  · apply le_antisymm
    · intro h hh
      by_cases hhB : h ∈ B
      · exact Subgroup.mem_sup_left (hBH₁₂ hhB)
      · have hB' : h * (a₀ * a⁻¹)⁻¹ ∈ B := P.mul_inv_mem_B hh htH hhB htB
        have e : h = (h * (a₀ * a⁻¹)⁻¹) * (a₀ * a⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hBH₁₂ hB'))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact sup_le (sup_le hH₁H hH₂H) ((Subgroup.zpowers_le).mpr htH)

end PairStep

end S152Fin

end CFSG.Quasithin
