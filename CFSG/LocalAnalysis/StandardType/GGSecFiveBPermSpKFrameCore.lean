module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKToral
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKSigned
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKAlign
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusSign
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem ggSecFiveBPermSpK_zmodPowHom_injective {L' : Type} [Group L'] {p : ℕ} [NeZero p]
    {t : L'} (ht : t ^ p = 1) (hto : orderOf t = p) :
    Function.Injective (TableBSymp.zmodPowHom ht) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact (TableBSymp.zmodPowHom_eq_one_iff ht hto).mp ha

theorem ggSecFiveBPermSpK_zeta_injective {F : Type} [Field F] {p r : ℕ}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hD : Function.Injective (SpJoin.spPlaneTorus (r + 1) ζ)) : Function.Injective ζ := by
  intro a b hab
  have h : SpJoin.spPlaneTorus (r + 1) ζ (Pi.mulSingle 0 a) =
      SpJoin.spPlaneTorus (r + 1) ζ (Pi.mulSingle 0 b) := by
    rw [SpJoin.spPlaneTorus_mulSingle, SpJoin.spPlaneTorus_mulSingle, hab]
  exact (Pi.mulSingle_inj (0 : Fin (r + 1))).mp (hD h)

theorem ggSecFiveBPermSpK_center_statedSp_galoisField_eq_bot (f n : ℕ) :
    Subgroup.center (StatedSp n (GaloisField 2 f)) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

private theorem ggSecFiveBPermSpK_equivStatedSp_diagonal {F : Type} [Field F] {n : ℕ}
    (s : Fin n → Fˣ) :
    CFSG.LieType.Universal.Symplectic.equivStatedSp n F
        (TauCeti.GLSymplecticFin.diagonal s) =
      CFSG.SeitzReduction.SymplecticPilot.diagSp F n s := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [CFSG.SeitzReduction.SymplecticPilot.mat_diagSp,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_equiv_diagonal]
  rfl

theorem ggSecFiveBPermSpK_eq_of_conj_eq {G S : Type} [Group G] [Group S] {p r : ℕ}
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S} (hD : Function.Injective D)
    (hcenter : Subgroup.center S = ⊥) {κ : S →* G} (hκ : Function.Injective κ) :
    ∀ t t' : Fin (r + 1) → Multiplicative (ZMod p),
      (∀ s, κ (D t * s * (D t)⁻¹) = κ (D t' * s * (D t')⁻¹)) → t = t' := by
  intro t t' h
  have h1 : ∀ s, D t * s * (D t)⁻¹ = D t' * s * (D t')⁻¹ := fun s => hκ (h s)
  have hz : (D t')⁻¹ * D t ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hs := h1 s
    have hzs : ((D t')⁻¹ * D t) * s = s * ((D t')⁻¹ * D t) := by
      calc ((D t')⁻¹ * D t) * s
          = (D t')⁻¹ * (D t * s * (D t)⁻¹) * D t := by group
        _ = (D t')⁻¹ * (D t' * s * (D t')⁻¹) * D t := by rw [hs]
        _ = s * ((D t')⁻¹ * D t) := by group
    exact hzs.symm
  rw [hcenter, Subgroup.mem_bot] at hz
  have hdt : D t = D t' := by
    have := congrArg (fun z => D t' * z) hz
    simpa [mul_assoc] using this
  exact hD hdt

theorem ggSecFiveBPermSpK_toralHom_ker_mem {G S : Type} [Group G] [Group S] {p r : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G} {κ : S →* G} (hκrange : κ.range = X)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (D (T b) * s * (D (T b))⁻¹)) :
    ∀ (b : ↥Bs), T b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨s, rfl⟩ : x ∈ κ.range := by rwa [hκrange]
  have h : (b : G) * κ s * (b : G)⁻¹ = κ s := by
    simpa [hb] using hT b s
  have h' : (b : G) * κ s = κ s * (b : G) := by
    calc (b : G) * κ s = (b : G) * κ s * (b : G)⁻¹ * (b : G) := by group
      _ = κ s * (b : G) := by rw [h]
  exact h'.symm

theorem ggSecFiveBPermSpK_toralHom_surjective_of_card {G : Type} [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] [NeZero p] {Bs X : Subgroup G}
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs)
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hker : ∀ (b : ↥Bs), T b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G)) :
    Function.Surjective T := by
  classical
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcard_cod : Nat.card (Fin (r + 1) → Multiplicative (ZMod p)) = p ^ (r + 1) := by
    rw [Nat.card_fun, hcardZ, Nat.card_fin]
  have hker_card : Nat.card T.ker ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    refine Nat.card_le_card_of_injective (fun b : T.ker => ?_) ?_
    · exact ⟨(b.1 : G), b.1.2, hker b.1 (MonoidHom.mem_ker.mp b.2)⟩
    · intro b c h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) => (z : G)) h))
  have hcard_ker_range : Nat.card T.ker * Nat.card T.range = Nat.card ↥Bs := by
    rw [← Subgroup.index_ker T]
    exact Subgroup.card_mul_index T.ker
  have hbound : p ^ (r + 1) * Nat.card T.ker ≤ Nat.card T.range * Nat.card T.ker :=
    calc p ^ (r + 1) * Nat.card T.ker
        ≤ p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
          Nat.mul_le_mul_left _ hker_card
      _ ≤ Nat.card ↥Bs := hcard
      _ = Nat.card T.range * Nat.card T.ker := by rw [← hcard_ker_range, mul_comm]
  have hge : p ^ (r + 1) ≤ Nat.card T.range := Nat.le_of_mul_le_mul_right hbound Nat.card_pos
  have hle : Nat.card T.range ≤ p ^ (r + 1) := by
    rw [← hcard_cod]
    exact Nat.card_le_card_of_injective (Subgroup.subtype T.range)
      (Subgroup.subtype_injective T.range)
  refine MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq T.range ?_)
  rw [hcard_cod]
  exact le_antisymm hle hge

private theorem ggSecFiveBPermSpK_card_bound_of_le {G : Type} [Group G] {p r : ℕ}
    {Bs X : Subgroup G} (hcardBs : Nat.card ↥Bs = p ^ (r + 2))
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs := by
  rw [hcardBs, show r + 2 = r + 1 + 1 from rfl, pow_succ]
  exact Nat.mul_le_mul_left _ hcent

theorem ggSecFiveBPermSpK_toralHom_surjective {G : Type} [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] [NeZero p] {Bs X : Subgroup G}
    (hcardBs : Nat.card ↥Bs = p ^ (r + 2))
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hker : ∀ (b : ↥Bs), T b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G)) :
    Function.Surjective T :=
  ggSecFiveBPermSpK_toralHom_surjective_of_card
    (ggSecFiveBPermSpK_card_bound_of_le hcardBs hcent) hker

theorem ggSecFiveBPermSpK_exists_toralHom_of_card {G S : Type} [Group G] [Group S] [Finite G]
    {p r : ℕ} [Fact p.Prime] [NeZero p] {Bs X : Subgroup G} {κ : S →* G}
    (hκ : Function.Injective κ) (hκX : κ.range = X)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hD : Function.Injective D) (hcenter : Subgroup.center S = ⊥)
    (htor : ∀ b ∈ Bs, ∃ t, ∀ s, b * κ s * b⁻¹ = κ (D t * s * (D t)⁻¹))
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) :
    ∃ T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p)),
      Function.Surjective T ∧
      (∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (D (T b) * s * (D (T b))⁻¹)) ∧
      (∀ (b : ↥Bs), T b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G)) := by
  classical
  let t : ↥Bs → (Fin (r + 1) → Multiplicative (ZMod p)) :=
    fun b => Classical.choose (htor b b.2)
  have hspec : ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ =
      κ (D (t b) * s * (D (t b))⁻¹) :=
    fun b => Classical.choose_spec (htor b b.2)
  have huniq := ggSecFiveBPermSpK_eq_of_conj_eq hD hcenter hκ
  have huniq_b : ∀ (b : ↥Bs) (u : Fin (r + 1) → Multiplicative (ZMod p)),
      (∀ s, (b : G) * κ s * (b : G)⁻¹ = κ (D u * s * (D u)⁻¹)) → u = t b := by
    intro b u hu
    refine huniq u (t b) ?_
    intro s
    rw [← hu s, hspec b s]
  let T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p)) :=
    MonoidHom.mk' t (fun b b' => by
      refine (huniq_b (b * b') (t b * t b') ?_).symm
      intro s
      calc ((b * b' : ↥Bs) : G) * κ s * (((b * b' : ↥Bs) : G))⁻¹
          = (b : G) * ((b' : G) * κ s * (b' : G)⁻¹) * (b : G)⁻¹ := by
              simp only [Subgroup.coe_mul]
              group
        _ = (b : G) * κ (D (t b') * s * (D (t b'))⁻¹) * (b : G)⁻¹ := by rw [hspec b' s]
        _ = κ (D (t b) * (D (t b') * s * (D (t b'))⁻¹) * (D (t b))⁻¹) := hspec b _
        _ = κ (D (t b * t b') * s * (D (t b * t b'))⁻¹) := by
              rw [map_mul D]
              congr 1
              group)
  have hTspec : ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ =
      κ (D (T b) * s * (D (T b))⁻¹) := fun b s => hspec b s
  have hker := ggSecFiveBPermSpK_toralHom_ker_mem hκX hTspec
  refine ⟨T, ?_, hTspec, hker⟩
  exact ggSecFiveBPermSpK_toralHom_surjective_of_card hcard hker

theorem ggSecFiveBPermSpK_exists_toralHom {G S : Type} [Group G] [Group S] [Finite G] {p r : ℕ}
    [Fact p.Prime] [NeZero p] {Bs X : Subgroup G} {κ : S →* G} (hκ : Function.Injective κ)
    (hκX : κ.range = X) {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    (hD : Function.Injective D) (hcenter : Subgroup.center S = ⊥)
    (htor : ∀ b ∈ Bs, ∃ t, ∀ s, b * κ s * b⁻¹ = κ (D t * s * (D t)⁻¹))
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hcardBs : Nat.card ↥Bs = p ^ (r + 2)) :
    ∃ T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p)),
      Function.Surjective T ∧
      (∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (D (T b) * s * (D (T b))⁻¹)) ∧
      (∀ (b : ↥Bs), T b = 1 → (b : G) ∈ Subgroup.centralizer (X : Set G)) :=
  ggSecFiveBPermSpK_exists_toralHom_of_card hκ hκX hD hcenter htor
    (ggSecFiveBPermSpK_card_bound_of_le hcardBs hcent)

private theorem ggSecFiveBPermSpK_signedPerm_of_automizer {G S : Type} [Group G] [Group S]
    {p r : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    {κ : S →* G} (hκ : Function.Injective κ) (hκX : κ.range = X)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S} (hZ : Subgroup.center S = ⊥)
    (hN : ∀ u : S, (∀ f, ∃ f', u * D f * u⁻¹ = D f') →
      ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', u * D f * u⁻¹ = D f' →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))} (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (D (T b) * s * (D (T b))⁻¹))
    (T' : (Fin (r + 2) → Multiplicative (ZMod p)) →*
      (Fin (r + 1) → Multiplicative (ZMod p)))
    (hT' : T' = T.comp eta.symm.toMonoidHom)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer X Bs)
    (w : MulAut (Fin (r + 2) → Multiplicative (ZMod p)))
    (hwφ : (MulAut.congr eta).toMonoidHom φ = w) :
    ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T' (w x) (π i)) = ε i * Multiplicative.toAdd (T' x i) := by
  obtain ⟨π, ε, hε, hπ⟩ :=
    ggSecFiveBPermSpK_signedPerm_of_mem_automizer_of_normalizes hκ hκX hZ hN T hTs hT hφ
  refine ⟨π, ε, hε, fun x i => ?_⟩
  have hx : T' (w x) = T (φ (eta.symm x)) := by
    rw [hT']
    show T (eta.symm (w x)) = T (φ (eta.symm x))
    have hwapply : w x = eta (φ (eta.symm x)) := by
      rw [← hwφ]
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hwapply, MulEquiv.symm_apply_apply]
  rw [hx]
  simpa [hT'] using hπ (eta.symm x) i

theorem ggSecFiveBPermSpK_sign_mul_eq {p : ℕ} {c e x y : ZMod p} (he : e = 1 ∨ e = -1)
    (h : x = e * c * y) : e * x = c * y := by
  rw [h]
  calc e * (e * c * y) = (e * e) * (c * y) := by ring
    _ = c * y := by rw [SpCoord.coord_sign_mul_self he, one_mul]

private theorem ggSecFiveBPermSpK_torus_eq {G : Type} [Group G] {p r f : ℕ} [Fact p.Prime]
    [NeZero p] {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    {π' : Fin (r + 2) ≃ Fin (r + 2)} {c : ZMod p} {ε : Fin (r + 1) → ZMod p}
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))} (b : ↥Bs)
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1)
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hχ : ∀ a, χ a = TableBSymp.zmodPowHom hω
      (Multiplicative.ofAdd (c * Multiplicative.toAdd a)))
    (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (halign : ∀ k, Multiplicative.toAdd (T b k) =
      ε k * c * Multiplicative.toAdd (eta b (π' k.succ))) :
    ggSecFiveBPermSpKTorus eta π' χ b =
      SpJoin.spPlaneTorus (r + 1) (SpJoin.spPlaneZetaSplit ω hω)
        (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) := by
  have hbase : ∀ k, χ (eta b (π' k.succ)) =
      TableBSymp.zmodPowHom hω
        (Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) := by
    intro k
    rw [hχ, ggSecFiveBPermSpK_sign_mul_eq (hε k) (halign k)]
  rw [ggSecFiveBPermSpKTorus, ggSecFiveBPermSpK_equivStatedSp_diagonal,
    SpJoin.spPlaneTorus_spPlaneZetaSplit (r + 1) hω, TableBSymp.spTorusSt_eq_diagSp]
  congr 1
  funext k
  exact hbase k

private theorem ggSecFiveBPermSpK_frame_eq {G S : Type} [Group G] [Group S] {p r : ℕ}
    {Bs : Subgroup G} {ε : Fin (r + 1) → ZMod p}
    {κ₀ κ : S →* G}
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    {τ : ↥Bs → S}
    {α : MulAut S}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ = κ₀ (D (T b) * s * (D (T b))⁻¹))
    (hτ : ∀ b : ↥Bs,
      τ b = D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))))
    (hα : ∀ t, α (D t) =
      D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))))
    (hκ : κ = κ₀.comp α.symm.toMonoidHom) :
    ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (τ b * s * (τ b)⁻¹) := by
  intro b s
  have hDconj : D (T b) = α.symm (τ b) := by
    rw [hτ b, ← hα (T b), MulEquiv.symm_apply_apply]
  calc (b : G) * κ s * (b : G)⁻¹
      = (b : G) * κ₀ (α.symm s) * (b : G)⁻¹ := by
          simp only [hκ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    _ = κ₀ (D (T b) * α.symm s * (D (T b))⁻¹) := hT b (α.symm s)
    _ = κ₀ (α.symm (τ b) * α.symm s * (α.symm (τ b))⁻¹) := by rw [hDconj]
    _ = κ₀ (α.symm (τ b * s * (τ b)⁻¹)) := by
        simp only [map_mul, map_inv]
    _ = κ (τ b * s * (τ b)⁻¹) := by
        simp only [hκ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem ggSecFiveBPermSpK_exists_signFree_of_conj {G S : Type} [Group G] [Group S] {p r : ℕ}
    {Bs X : Subgroup G} {κ₀ : S →* G} (hκ₀ : Function.Injective κ₀) (hκ₀X : κ₀.range = X)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S}
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ = κ₀ (D (T b) * s * (D (T b))⁻¹))
    {ε : Fin (r + 1) → ZMod p} {α : MulAut S}
    (hα : ∀ t, α (D t) = D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))))
    {τ : ↥Bs → S}
    (hτ : ∀ b, τ b = D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))) :
    ∃ κ : S →* G, Function.Injective κ ∧ κ.range = X ∧
      ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (τ b * s * (τ b)⁻¹) := by
  let κ : S →* G := κ₀.comp α.symm.toMonoidHom
  have hκinj : Function.Injective κ := hκ₀.comp α.symm.injective
  have hκX : κ.range = X := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hmem : κ s ∈ κ₀.range := ⟨α.symm s, rfl⟩
      rwa [hκ₀X] at hmem
    · intro hx
      have hx' : x ∈ κ₀.range := by rwa [hκ₀X]
      obtain ⟨u, hu⟩ := hx'
      refine ⟨α u, ?_⟩
      show κ₀ (α.symm (α u)) = x
      rw [MulEquiv.symm_apply_apply, hu]
  exact ⟨κ, hκinj, hκX, ggSecFiveBPermSpK_frame_eq hT hτ hα rfl⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem ggSecFiveBPermSpK_exists_signFree {G : Type} [Group G] {p r f : ℕ}
    {Bs X : Subgroup G}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {κ₀ : StatedSp (r + 1) (GaloisField 2 f) →* G} (hκ₀ : Function.Injective κ₀)
    (hκ₀X : κ₀.range = X)
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ =
      κ₀ (SpJoin.spPlaneTorus (r + 1) ζ (T b) * s * (SpJoin.spPlaneTorus (r + 1) ζ (T b))⁻¹))
    {ε : Fin (r + 1) → ZMod p} (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    {τ : ↥Bs → StatedSp (r + 1) (GaloisField 2 f)}
    (hτ : ∀ b : ↥Bs, τ b = SpJoin.spPlaneTorus (r + 1) ζ
      (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))) :
    ∃ κ : StatedSp (r + 1) (GaloisField 2 f) →* G, Function.Injective κ ∧ κ.range = X ∧
      ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (τ b * s * (τ b)⁻¹) := by
  obtain ⟨W, hWconj⟩ :=
    SpJoin.exists_conj_spPlaneTorus_sign (F := GaloisField 2 f) (n := r + 1) hζw ε hε
  refine ggSecFiveBPermSpK_exists_signFree_of_conj hκ₀ hκ₀X hT
    (α := MulAut.conj W⁻¹) ?_ hτ
  intro t
  simpa only [MulAut.conj_apply, inv_inv] using hWconj t

theorem ggSecFiveBPermSpK_exists_frame_char {p f : ℕ} [Fact p.Prime] [NeZero p]
    {c : ZMod p} (hc : c ≠ 0) {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1)
    (hωo : orderOf ω = p) :
    ∃ χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ,
      Function.Injective χ ∧
      (∀ a, χ a = TableBSymp.zmodPowHom hω
        (Multiplicative.ofAdd (c * Multiplicative.toAdd a))) := by
  let mulc : ZMod p →+ ZMod p :=
    { toFun := fun a => c * a
      map_zero' := mul_zero c
      map_add' := fun a b => mul_add c a b }
  let χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ :=
    (TableBSymp.zmodPowHom hω).comp (AddMonoidHom.toMultiplicative mulc)
  have hχapp : ∀ a, χ a = TableBSymp.zmodPowHom hω
      (Multiplicative.ofAdd (c * Multiplicative.toAdd a)) := by
    intro a
    rfl
  have hχinj : Function.Injective χ := by
    intro a b hab
    have hab' : TableBSymp.zmodPowHom hω
          (Multiplicative.ofAdd (c * Multiplicative.toAdd a)) =
        TableBSymp.zmodPowHom hω
          (Multiplicative.ofAdd (c * Multiplicative.toAdd b)) := by
      simpa only [hχapp] using hab
    have h1 : Multiplicative.ofAdd (c * Multiplicative.toAdd a) =
        Multiplicative.ofAdd (c * Multiplicative.toAdd b) :=
      ggSecFiveBPermSpK_zmodPowHom_injective hω hωo hab'
    have h2 : c * Multiplicative.toAdd a = c * Multiplicative.toAdd b :=
      Multiplicative.ofAdd.injective h1
    exact Multiplicative.toAdd.injective (mul_left_cancel₀ hc h2)
  exact ⟨χ, hχinj, hχapp⟩

private theorem ggSecFiveBPermSpK_exists_frame_of_align {G : Type} [Group G] {p r f : ℕ}
    [Fact p.Prime] [NeZero p] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1) (hωo : orderOf ω = p)
    {κ₀ : StatedSp (r + 1) (GaloisField 2 f) →* G} (hκ₀ : Function.Injective κ₀)
    (hκ₀X : κ₀.range = X)
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ =
      κ₀ (SpJoin.spPlaneTorus (r + 1) (SpJoin.spPlaneZetaSplit ω hω) (T b) * s *
        (SpJoin.spPlaneTorus (r + 1) (SpJoin.spPlaneZetaSplit ω hω) (T b))⁻¹))
    {π' : Fin (r + 2) ≃ Fin (r + 2)}
    {c : ZMod p} (hc : c ≠ 0) {ε : Fin (r + 1) → ZMod p} (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (halign : ∀ x k, Multiplicative.toAdd (T.comp eta.symm.toMonoidHom x k) =
      ε k * c * Multiplicative.toAdd (x (π' k.succ))) :
    ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame Bs X eta π' κ χ := by
  obtain ⟨χ, hχinj, hχapp⟩ := ggSecFiveBPermSpK_exists_frame_char hc hω hωo
  have hτ : ∀ b : ↥Bs, ggSecFiveBPermSpKTorus eta π' χ b =
      SpJoin.spPlaneTorus (r + 1) (SpJoin.spPlaneZetaSplit ω hω)
        (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) := by
    intro b
    refine ggSecFiveBPermSpK_torus_eq b hω hχapp hε fun k => ?_
    simpa [MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using halign (eta b) k
  obtain ⟨κ, hκinj, hκX, hframe⟩ := ggSecFiveBPermSpK_exists_signFree
    (SpJoin.spPlaneZetaSplit_conj_sl2W hω) hκ₀ hκ₀X hT hε hτ
  exact ⟨κ, χ, hκinj, hκX, hχinj, hframe⟩

theorem ggSecFiveBPermSpK_exists_calibratedZeta {H : Type} [Group H] {p : ℕ}
    [Fact p.Prime] {c : ZMod p} (hc : c ≠ 0) {ζ : Multiplicative (ZMod p) →* H}
    (hζ : Function.Injective ζ) :
    ∃ ζ' : Multiplicative (ZMod p) →* H, Function.Injective ζ' ∧ ζ'.range = ζ.range ∧
      ∀ a, ζ' a = ζ (Multiplicative.ofAdd (c * Multiplicative.toAdd a)) := by
  let mulc : ZMod p →+ ZMod p :=
    { toFun := fun a => c * a
      map_zero' := mul_zero c
      map_add' := fun a b => mul_add c a b }
  let ζ' : Multiplicative (ZMod p) →* H := ζ.comp (AddMonoidHom.toMultiplicative mulc)
  have happ : ∀ a, ζ' a = ζ (Multiplicative.ofAdd (c * Multiplicative.toAdd a)) := fun _ => rfl
  refine ⟨ζ', fun a b hab => ?_, ?_, happ⟩
  · rw [happ, happ] at hab
    exact Multiplicative.toAdd.injective
      (mul_left_cancel₀ hc (Multiplicative.ofAdd.injective (hζ hab)))
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (happ a).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd a), ?_⟩
      rw [happ, toAdd_ofAdd, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, ofAdd_toAdd]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
private theorem ggSecFiveBPermSpK_exists_planeFrame_of_align {G : Type} [Group G] {p r f : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζ : Function.Injective ζ) (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {κ₀ : StatedSp (r + 1) (GaloisField 2 f) →* G} (hκ₀ : Function.Injective κ₀)
    (hκ₀X : κ₀.range = X)
    {T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p))}
    (hT : ∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ =
      κ₀ (SpJoin.spPlaneTorus (r + 1) ζ (T b) * s * (SpJoin.spPlaneTorus (r + 1) ζ (T b))⁻¹))
    {π' : Fin (r + 2) ≃ Fin (r + 2)}
    {c : ZMod p} (hc : c ≠ 0) {ε : Fin (r + 1) → ZMod p} (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (halign : ∀ x k, Multiplicative.toAdd (T.comp eta.symm.toMonoidHom x k) =
      ε k * c * Multiplicative.toAdd (x (π' k.succ))) :
    ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
      (ζ' : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      ζ'.range = ζ.range ∧ GGSecFiveBPermSpPlaneFrame Bs X eta π' κ ζ' := by
  obtain ⟨ζ', hζ'inj, hζ'range, hζ'app⟩ := ggSecFiveBPermSpK_exists_calibratedZeta hc hζ
  have hτ : ∀ b : ↥Bs, SpJoin.spPlaneTorus (r + 1) ζ' (fun m => eta b (π' m.succ)) =
      SpJoin.spPlaneTorus (r + 1) ζ
        (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) := by
    intro b
    refine TorC.spPlaneTorus_eq_of_forall fun k => ?_
    have halign_b : Multiplicative.toAdd (T b k) =
        ε k * c * Multiplicative.toAdd (eta b (π' k.succ)) := by
      simpa [MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using halign (eta b) k
    show ζ' (eta b (π' k.succ)) = ζ (Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))
    rw [hζ'app, ggSecFiveBPermSpK_sign_mul_eq (hε k) halign_b]
  obtain ⟨κ, hκinj, hκX, hframe⟩ := ggSecFiveBPermSpK_exists_signFree
    (τ := fun b => SpJoin.spPlaneTorus (r + 1) ζ' (fun m => eta b (π' m.succ)))
    hζw hκ₀ hκ₀X hT hε hτ
  exact ⟨κ, ζ', hζ'range, hκinj, hκX, hζ'inj, hframe⟩

theorem ggSecFiveBPermSpK_exists_align_of_toral {G S : Type} [Group G] [Group S] [Finite G]
    {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : 2 ≤ r) {Bs X : Subgroup G}
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0)
    {κ₀ : S →* G} (hκ₀ : Function.Injective κ₀) (hκ₀X : κ₀.range = X)
    {D : (Fin (r + 1) → Multiplicative (ZMod p)) →* S} (hD : Function.Injective D)
    (hZ : Subgroup.center S = ⊥)
    (htor : ∀ b ∈ Bs, ∃ t, ∀ s, b * κ₀ s * b⁻¹ = κ₀ (D t * s * (D t)⁻¹))
    (hN : ∀ u : S, (∀ f, ∃ f', u * D f * u⁻¹ = D f') →
      ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', u * D f * u⁻¹ = D f' →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i)) :
    ∃ T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p)),
      (∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ = κ₀ (D (T b) * s * (D (T b))⁻¹)) ∧
      ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
        ∃ ε : Fin (r + 1) → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧
          ∀ x k, Multiplicative.toAdd (T.comp eta.symm.toMonoidHom x k) =
            ε k * c * Multiplicative.toAdd (x (π' k.succ)) := by
  classical
  have hcent := ggSecFiveBPermSpK_card_inf_centralizer_le hp2 hA
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardBs : Nat.card ↥Bs = p ^ (r + 2) := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, hcardZ, Nat.card_fin]
  obtain ⟨T, hTs, hTspec, hker⟩ :=
    ggSecFiveBPermSpK_exists_toralHom hκ₀ hκ₀X hD hZ htor hcent hcardBs
  let T' := T.comp eta.symm.toMonoidHom
  have hTs' : Function.Surjective T' := by
    intro y
    obtain ⟨b, hb⟩ := hTs y
    refine ⟨eta b, ?_⟩
    simpa [T'] using hb
  have hker' : ∀ x, T' x = 1 → ∀ j, j ≠ i0 → x j = 1 := by
    intro x hx j hj
    have hmem : (eta.symm x : G) ∈ Subgroup.centralizer (X : Set G) :=
      hker (eta.symm x) hx
    have h := ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer hp2 hA hmem hj
    simpa using h
  have hW : ∀ w ∈ bCoordinateBlock (r + 2) p i0,
      ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ x i, Multiplicative.toAdd (T' (w x) (π i)) = ε i * Multiplicative.toAdd (T' x i) := by
    intro w hw
    have hw' : w ∈ (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom := by rwa [hA]
    obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp hw'
    exact ggSecFiveBPermSpK_signedPerm_of_automizer hκ₀ hκ₀X hZ hN hTs hTspec T' rfl hφ w hφw
  obtain ⟨π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align hp2 hr T' hTs' hker' hW
  exact ⟨T, hTspec, π', hπ'0, c, hc, ε, hε, by simpa only [T'] using halign⟩



private theorem ggSecFiveBPermSpK_exists_alignedChart (hMp : GGInnerDiagMpInput) {G : Type}
    [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζc : SpJoin.SpPlaneConj (GaloisField 2 f) p ζ) :
    Function.Injective ζ ∧ ∃ κ₀ : StatedSp (r + 1) (GaloisField 2 f) →* G,
      Function.Injective κ₀ ∧ κ₀.range = X ∧
      ∃ T : ↥Bs →* (Fin (r + 1) → Multiplicative (ZMod p)),
        (∀ (b : ↥Bs) s, (b : G) * κ₀ s * (b : G)⁻¹ =
          κ₀ (SpJoin.spPlaneTorus (r + 1) ζ (T b) * s *
            (SpJoin.spPlaneTorus (r + 1) ζ (T b))⁻¹)) ∧
        ∃ π' : Fin (r + 2) ≃ Fin (r + 2), π' 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
          ∃ ε : Fin (r + 1) → ZMod p, (∀ k, ε k = 1 ∨ ε k = -1) ∧
            ∀ x k, Multiplicative.toAdd (T.comp eta.symm.toMonoidHom x k) =
              ε k * c * Multiplicative.toAdd (x (π' k.succ)) := by
  classical
  have hcard := ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le (K := X) hp2 hA
  obtain ⟨hDin, κ₀, hκ₀inj, hκ₀range, htor⟩ :=
    ggSecFiveBPermSpK_exists_toral hMp hf hr hBs hmark e hcard hζc
  have hζ : Function.Injective ζ := ggSecFiveBPermSpK_zeta_injective hDin
  have hcenter : Subgroup.center (StatedSp (r + 1) (GaloisField 2 f)) = ⊥ :=
    ggSecFiveBPermSpK_center_statedSp_galoisField_eq_bot f (r + 1)
  obtain ⟨T, hTspec, π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align_of_toral hp2 hr eta hA hκ₀inj hκ₀range hDin hcenter htor
      (fun u hu => TorC.exists_signedPerm_of_normalizes (F := GaloisField 2 f) (p := p)
        (Fact.out) hp2 hζ u hu)
  exact ⟨hζ, κ₀, hκ₀inj, hκ₀range, T, hTspec, π', hπ'0, c, hc, ε, hε, halign⟩

theorem ggSecFiveBPermSpK_exists_frame (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0)
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1) (hωo : orderOf ω = p) :
    ∃ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 ∧
      ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
        (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), GGSecFiveBPermSpKFrame Bs X eta π κ χ := by
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hpF : (p : GaloisField 2 f) ≠ 0 := SpJoin.natCast_ne_zero_of_two_eq_zero h2 hp2 Fact.out
  obtain ⟨-, κ₀, hκ₀inj, hκ₀range, T, hTspec, π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_alignedChart hMp hp2 hf hr hBs hmark e eta hA
      (SpJoin.spPlaneConj_split (F := GaloisField 2 f) hp2 hpF hω hωo)
  exact ⟨π', hπ'0,
    ggSecFiveBPermSpK_exists_frame_of_align hω hωo hκ₀inj hκ₀range hTspec hc hε halign⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem ggSecFiveBPermSpK_exists_planeFrame (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (hζc : SpJoin.SpPlaneConj (GaloisField 2 f) p ζ) :
    ∃ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 ∧
      ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
        (ζ' : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
        ζ'.range = ζ.range ∧ GGSecFiveBPermSpPlaneFrame Bs X eta π κ ζ' := by
  obtain ⟨hζ, κ₀, hκ₀inj, hκ₀range, T, hTspec, π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_alignedChart hMp hp2 hf hr hBs hmark e eta hA hζc
  exact ⟨π', hπ'0,
    ggSecFiveBPermSpK_exists_planeFrame_of_align hζ hζw hκ₀inj hκ₀range hTspec hc hε halign⟩

theorem ggSecFiveBPermSpK_exists_planeFrame_of_conj (hMp : GGInnerDiagMpInput) {G : Type}
    [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0) :
    ∃ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 ∧
      ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
        (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
        GGSecFiveBPermSpPlaneFrame Bs X eta π κ ζ := by
  obtain ⟨ζ, hζw, hζc⟩ := SpJoin.exists_spPlaneConj (F := GaloisField 2 f) (p := p)
    (CharP.cast_eq_zero (GaloisField 2 f) 2) Fact.out hp2
  obtain ⟨π, hπ0, κ, ζ', -, hframe⟩ :=
    ggSecFiveBPermSpK_exists_planeFrame hMp hp2 hf hr hBs hmark e eta hA hζw hζc
  exact ⟨π, hπ0, κ, ζ', hframe⟩

end CFSG.StandardType

end
