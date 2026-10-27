module

public import CFSG.Quasithin.EmptyFaithful.S153VCore
public import CFSG.Quasithin.EmptyFaithful.S153WJFin
public import CFSG.Quasithin.EmptyFaithful.S153WJOff
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.Quasithin.W153 Equiv

variable {G : Type} [Group G] {I S Iz K₁ K₂ Λ : Subgroup G}

theorem conj_mem_blockU_of_conjSub_eq {a : G} {L L' : Subgroup G} (h : B6.conjSub a L = L')
    {u : G} (hu : u ∈ blockU L) : a * u * a⁻¹ ∈ blockU L' := by
  subst h
  have e : blockU (B6.conjSub a L) = B6.conjSub a (blockU L) :=
    CFSG.QuasithinUnique.Lin2.blockU_map_equiv (MulAut.conj a) L
  rw [e, B6.mem_conjSub]
  simpa [mul_assoc] using hu

theorem conj_mem_pCoreOf_of_conjSub_eq {a : G} {L L' : Subgroup G} (h : B6.conjSub a L = L')
    {u : G} (hu : u ∈ pCoreOf 2 L) : a * u * a⁻¹ ∈ pCoreOf 2 L' := by
  subst h
  have e : pCoreOf 2 (B6.conjSub a L) = B6.conjSub a (pCoreOf 2 L) :=
    pCoreOf_map_equiv 2 (MulAut.conj a) L
  rw [e, B6.mem_conjSub]
  simpa [mul_assoc] using hu

namespace A5Cfg

variable [Finite G] (c : A5Cfg I S Iz K₁ K₂)
include c

theorem blockU_inf_blockU : blockU K₁ ⊓ blockU K₂ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hZ : x ∈ blockZ K₁ := ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun k hk =>
    c.comm k hk x (c.U₂_le_K₂ hx.2)⟩
  rw [AppC.blockZ_eq_bot_of_alt5 c.blk₁.1 c.a5₁] at hZ
  exact hZ

theorem card_blockU₁ : Nat.card (blockU K₁) = 16 := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  exact P.toPiData.card_blockU

omit [Finite G] in
theorem isElemAbelian_blockU_sup : IsElemAbelian 2 (blockU K₁ ⊔ blockU K₂) :=
  B2F.isElemAbelian_sup_of_commute (AppC.isElemAbelian_blockU c.blk₁.1)
    (AppC.isElemAbelian_blockU c.blk₂.1) fun x hx y hy =>
      c.comm x (c.U₁_le_K₁ hx) y (c.U₂_le_K₂ hy)

theorem blockU_sup_le_S : blockU K₁ ⊔ blockU K₂ ≤ S :=
  sup_le (c.U₁_le_pCoreI.trans c.sylow.pCoreOf_le) (c.U₂_le_pCoreI.trans c.sylow.pCoreOf_le)

omit [Finite G] in
theorem conjSub_eq₂_of_not_mem {a : G} (ha : a ∈ S)
    (hn : a ∉ Subgroup.normalizer (K₁ : Set G)) : B6.conjSub a K₁ = K₂ := by
  rcases c.perm₁ a ha with h | h
  · exact absurd (mem_normalizer_of_conjSub_eq h) hn
  · exact h

theorem sixteen_mul_card_le {a : G} (h : B6.conjSub a K₁ = K₂) :
    16 * Nat.card ↥((blockU K₁ ⊔ blockU K₂) ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      Nat.card ↥(blockU K₁ ⊔ blockU K₂) := by
  set U₁ := blockU K₁ with hU₁
  set U₂ := blockU K₂ with hU₂
  set C := (U₁ ⊔ U₂) ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hUe := c.isElemAbelian_blockU_sup
  have hcomm : ∀ x ∈ U₁, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hUe (Subgroup.mem_sup_left hx) hy.1
  have hinf : U₁ ⊓ C = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hax : a * x = x * a := Subgroup.mem_centralizer_iff.1 hx.2.2 a (Set.mem_singleton a)
    have hx₂ : x ∈ U₂ := by
      have := conj_mem_blockU_of_conjSub_eq h hx.1
      have e : a * x * a⁻¹ = x := by rw [hax]; group
      rwa [e] at this
    have : x ∈ U₁ ⊓ U₂ := ⟨hx.1, hx₂⟩
    rw [c.blockU_inf_blockU] at this
    exact this
  have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, c.card_blockU₁] at h1
  have h2 : Nat.card ↥(U₁ ⊔ C) ≤ Nat.card ↥(U₁ ⊔ U₂) :=
    Subgroup.card_le_of_le (sup_le le_sup_left inf_le_left)
  omega

theorem card_le_eight_mul {A : Subgroup G} (hA : IsMaxElemAbelian S A) {a : G} (haA : a ∈ A)
    (hn : a ∉ Subgroup.normalizer (K₁ : Set G)) :
    Nat.card A ≤
      8 * Nat.card ↥(A ⊓ Subgroup.centralizer ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G)) := by
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₁ = K₂ := c.conjSub_eq₂_of_not_mem haS hn
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [pow_two] at this
  have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj₂ : B6.conjSub a K₂ = K₁ := by
    rw [← hconj₁, ← B6.conjSub_mul, ha2, B6.conjSub_one]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hA.2.1 hx hy
  set A₀ := A ⊓ Subgroup.normalizer (K₁ : Set G) with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have h2 : Nat.card A ≤ 2 * Nat.card A₀ := by
    refine card_le_two_mul_of_forall hA₀A hcommA haA ha2 fun x hx => ?_
    by_cases hxN : x ∈ Subgroup.normalizer (K₁ : Set G)
    · exact Or.inl ⟨hx, hxN⟩
    · right
      refine ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
      have hx' := c.conjSub_eq₂_of_not_mem (hA.1 hx) hxN
      apply mem_normalizer_of_conjSub_eq
      rw [B6.conjSub_mul, hx', haInv, hconj₂]
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  have hA₀e : IsElemAbelian 2 A₀ := B2F.isElemAbelian_mono hA₀A hA.2.1
  have hAN : A₀ ≤ Subgroup.normalizer (K₁ : Set G) := inf_le_right
  obtain ⟨hsq, hco⟩ := P.toPiData.im_elemAbelian hA₀e
  have him : IsElemAbelian 2 (P.toPiData.im A₀) :=
    ⟨⟨⟨fun g h => Subtype.ext (hco g.1 g.2 h.1 h.2)⟩⟩, fun g hg => by
      rw [pow_two]
      exact hsq g hg⟩
  have h4 : Nat.card (P.toPiData.im A₀) ≤ 4 := card_le_four_of_isElemAbelian_perm5 _ him
  have hcard := P.toPiData.card_im_mul hAN
  have hle : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (blockU K₁ : Set G)) ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.1.1, ?_⟩
    have hxU₁ : ∀ u ∈ blockU K₁, x * u = u * x := fun u hu =>
      (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm
    have hxa : x * a = a * x := hcommA x hx.1.1 a haA
    have hxU₂ : ∀ u ∈ blockU K₂, x * u = u * x := by
      intro u hu
      have hu' : ∃ w ∈ blockU K₁, u = a * w * a⁻¹ := ⟨a * u * a⁻¹,
        conj_mem_blockU_of_conjSub_eq hconj₂ hu, by
          rw [haInv]
          calc u = (a * a) * u * (a * a) := by rw [ha2]; simp
            _ = a * (a * u * a) * a := by group⟩
      obtain ⟨w, hw, rfl⟩ := hu'
      have hxw : x * w = w * x := hxU₁ w hw
      have hxa' : x * a⁻¹ = a⁻¹ * x := by rw [haInv]; exact hxa
      calc x * (a * w * a⁻¹) = (x * a) * w * a⁻¹ := by group
        _ = (a * x) * w * a⁻¹ := by rw [hxa]
        _ = a * (x * w) * a⁻¹ := by group
        _ = a * (w * x) * a⁻¹ := by rw [hxw]
        _ = a * w * (x * a⁻¹) := by group
        _ = a * w * (a⁻¹ * x) := by rw [hxa']
        _ = (a * w * a⁻¹) * x := by group
    have hle : blockU K₁ ⊔ blockU K₂ ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun v hv => Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact hxU₁ v hv)
        (fun v hv => Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact hxU₂ v hv)
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) x (Set.mem_singleton x)).symm
  calc Nat.card A ≤ 2 * Nat.card A₀ := h2
    _ = 2 * (Nat.card (P.toPiData.im A₀) *
          Nat.card ↥(A₀ ⊓ Subgroup.centralizer (blockU K₁ : Set G))) := by rw [hcard]
    _ ≤ 2 * (4 * Nat.card ↥(A ⊓ Subgroup.centralizer
          ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G))) := by gcongr
    _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer
          ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G)) := by ring

theorem isMaxElemAbelian_le_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ≤ Subgroup.normalizer (K₁ : Set G) := by
  intro a haA
  by_contra hn
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₁ = K₂ := c.conjSub_eq₂_of_not_mem haS hn
  have hi := card_mul_le_of_isMaxElemAbelian hA c.isElemAbelian_blockU_sup c.blockU_sup_le_S
  have hii := c.sixteen_mul_card_le hconj₁
  have hiii := c.card_le_eight_mul hA haA hn
  have hAU : Nat.card ↥(A ⊓ (blockU K₁ ⊔ blockU K₂)) ≤
      Nat.card ↥((blockU K₁ ⊔ blockU K₂) ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact (B2F.isElemAbelian_comm hA.2.1 haA hx.1)⟩
  have hp₁ : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer
      ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G)) := Nat.card_pos
  have hp₂ : 0 < Nat.card ↥((blockU K₁ ⊔ blockU K₂) ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_pos
  have h1 := Nat.mul_le_mul_right (Nat.card ↥(A ⊓ Subgroup.centralizer
      ((blockU K₁ ⊔ blockU K₂ : Subgroup G) : Set G))) hii
  have h2 := Nat.mul_le_mul hiii hAU
  have h3 := Nat.mul_pos hp₂ hp₁
  nlinarith

theorem thompsonJ_le_normalizer : thompsonJ S ≤ Subgroup.normalizer (K₁ : Set G) :=
  GammaExtra.thompsonJ_le fun _ hA => c.isMaxElemAbelian_le_normalizer hA

theorem mem_pCoreOf_of_comm_pCore {x : G} (hxS : x ∈ S)
    (h₁ : ∀ k ∈ K₁, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 K₁)
    (h₂ : ∀ k ∈ K₂, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 K₂) : x ∈ pCoreOf 2 I := by
  have hxI : x ∈ I := c.sylow.le hxS
  refine mem_pCoreOf_of_conj_mem c.sylow.isPGroup hxI fun y hy => ?_
  have hy' : y ∈ ((S : Subgroup G) : Set G) * ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₁ ⊔ K₂) c.S_le_normalizer_sup, ← c.gen]
    exact hy
  obtain ⟨s, hs, k, hk, rfl⟩ := hy'
  have hk' : k ∈ ((K₁ : Subgroup G) : Set G) * ((K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ c.K₁_le_normalizer₂]
    exact hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  have q₁ := h₁ k₁ hk₁
  have q₂ := h₂ k₂ hk₂
  have hq₂K : k₂ * x * k₂⁻¹ * x⁻¹ ∈ K₂ := pCoreOf_le 2 K₂ q₂
  have hcomm : k₁ * (k₂ * x * k₂⁻¹ * x⁻¹) = (k₂ * x * k₂⁻¹ * x⁻¹) * k₁ := c.comm k₁ hk₁ _ hq₂K
  have e : s * (k₁ * k₂) * x * (s * (k₁ * k₂))⁻¹ =
      s * ((k₂ * x * k₂⁻¹ * x⁻¹) * (k₁ * x * k₁⁻¹ * x⁻¹) * x) * s⁻¹ := by
    have h1 : s * (k₁ * k₂) * x * (s * (k₁ * k₂))⁻¹ =
        s * (k₁ * ((k₂ * x * k₂⁻¹ * x⁻¹) * x) * k₁⁻¹) * s⁻¹ := by group
    rw [h1]
    have h2 : k₁ * ((k₂ * x * k₂⁻¹ * x⁻¹) * x) * k₁⁻¹ =
        (k₁ * (k₂ * x * k₂⁻¹ * x⁻¹) * k₁⁻¹) * (k₁ * x * k₁⁻¹) := by group
    rw [h2]
    have h3 : k₁ * (k₂ * x * k₂⁻¹ * x⁻¹) * k₁⁻¹ = k₂ * x * k₂⁻¹ * x⁻¹ := by
      rw [hcomm]; group
    rw [h3]
    group
  rw [e]
  have hq₁S : k₁ * x * k₁⁻¹ * x⁻¹ ∈ S := (c.pCore_le₁ q₁).1
  have hq₂S : k₂ * x * k₂⁻¹ * x⁻¹ ∈ S := (c.symm.pCore_le₁ q₂).1
  exact S.mul_mem (S.mul_mem hs (S.mul_mem (S.mul_mem hq₂S hq₁S) hxS)) (S.inv_mem hs)

theorem not_thompsonJ_le_pCoreOf (hΛ : Λ ≤ Subgroup.normalizer (S : Set G))
    (hb : ∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (Λ ⊔ I ≤ Subgroup.normalizer (R₀ : Set G))) :
    ¬ thompsonJ S ≤ pCoreOf 2 I := by
  intro hJ
  have hQS : pCoreOf 2 I ≤ S := c.sylow.pCoreOf_le
  have hJQ : thompsonJ (pCoreOf 2 I) = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJ hQS
  have hΛJ : Λ ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    hΛ.trans (GammaExtra.normalizer_le_normalizer_thompsonJ S)
  have hIJ : I ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← hJQ]
    exact (le_normalizer_pCoreOf 2 I).trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hJne : thompsonJ S ≠ ⊥ := by
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
    intro hbot
    have hAbot : A = ⊥ := le_bot_iff.mp (hbot ▸ GammaExtra.le_thompsonJ hA)
    have h16 : Nat.card (blockU K₁) ≤ Nat.card A :=
      hA.2.2 (blockU K₁) (c.U₁_le_pCoreI.trans hQS) (AppC.isElemAbelian_blockU c.blk₁.1)
    rw [c.card_blockU₁, hAbot, Subgroup.card_bot] at h16
    omega
  exact hb (thompsonJ S) (GammaExtra.thompsonJ_le_self S) hJne (sup_le hΛJ hIJ)

theorem commutator_thompsonJ_eq (hΛ : Λ ≤ Subgroup.normalizer (S : Set G))
    (hb : ∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (Λ ⊔ I ≤ Subgroup.normalizer (R₀ : Set G)))
    (ht : ∃ t ∈ S, B6.conjSub t K₁ = K₂) : ⁅K₁, thompsonJ S⁆ = K₁ := by
  obtain ⟨t, htS, htK⟩ := ht
  set J := thompsonJ S with hJdef
  have hJ₁ : J ≤ Subgroup.normalizer (K₁ : Set G) := c.thompsonJ_le_normalizer
  have hJS : J ≤ S := GammaExtra.thompsonJ_le_self S
  have hJn : ∀ g ∈ S, ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.1 (GammaExtra.normalizer_le_normalizer_thompsonJ S
      (Subgroup.le_normalizer hg)) j).1 hj
  have hWK : ⁅K₁, J⁆ ≤ K₁ := by
    refine Subgroup.commutator_le.2 fun k hk j hj => ?_
    have h1 : j * k⁻¹ * j⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.1 (hJ₁ hj) k⁻¹).1 (K₁.inv_mem hk)
    have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact K₁.mul_mem hk h1
  have hWn : ∀ l ∈ K₁, ∀ w ∈ ⁅K₁, J⁆, l * w * l⁻¹ ∈ ⁅K₁, J⁆ := by
    intro l hl w hw
    rw [Subgroup.commutator_def] at hw ⊢
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, j, hj, rfl⟩ := hx
      have e : l * ⁅k, j⁆ * l⁻¹ = ⁅l * k, j⁆ * ⁅l, j⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨l * k, K₁.mul_mem hl hk, j, hj, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l, hl, j, hj, rfl⟩))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  rcases AppCS2.normal_le_or_eq_alt5 c.blk₁.1 c.a5₁ hWK hWn with h | h
  · exfalso
    have h₁ : ∀ j ∈ J, ∀ k ∈ K₁, k * j * k⁻¹ * j⁻¹ ∈ pCoreOf 2 K₁ := fun j hj k hk =>
      h (Subgroup.commutator_mem_commutator hk hj)
    have h₂ : ∀ j ∈ J, ∀ k ∈ K₂, k * j * k⁻¹ * j⁻¹ ∈ pCoreOf 2 K₂ := by
      intro j hj k hk
      have hk' : k ∈ B6.conjSub t K₁ := by rw [htK]; exact hk
      have hk₁ : t⁻¹ * k * t ∈ K₁ := B6.mem_conjSub.1 hk'
      have hj' : t⁻¹ * j * t ∈ J := by
        have := hJn t⁻¹ (S.inv_mem htS) j hj
        simpa using this
      have := conj_mem_pCoreOf_of_conjSub_eq htK (h₁ _ hj' _ hk₁)
      convert this using 1
      group
    have hJQ : J ≤ pCoreOf 2 I := fun j hj =>
      c.mem_pCoreOf_of_comm_pCore (hJS hj) (h₁ j hj) (h₂ j hj)
    exact c.not_thompsonJ_le_pCoreOf hΛ hb hJQ
  · exact h

end A5Cfg

end CFSG.Quasithin.ModF
