module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F53Mod

namespace F53B3

namespace N37

variable {G : Type} [Group G]

theorem fixSecIn_le (A L N : Subgroup G) : fixSecIn A L N ≤ N :=
  (Subgroup.closure_le N).mpr fun _ hx => hx.1

theorem mem_fixSecIn_iff {A L N : Subgroup G} (hLN : L ≤ N)
    (hN : N ≤ Subgroup.normalizer (L : Set G)) {x : G} :
    x ∈ fixSecIn A L N ↔ x ∈ N ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L := by
  have : (L.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hN
  exact X1512.mem_fixSecIn hLN

theorem mem_cSecIn_iff {F L X : Subgroup G} (hF : F ≤ Subgroup.normalizer (L : Set G)) {f : G} :
    f ∈ cSecIn F L X ↔ f ∈ F ∧ ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ L :=
  ⟨X1512.mem_cSecIn_of_normalizes hF, fun h => Subgroup.subset_closure h⟩

theorem commutator_le_of_central_steps [Finite G] {H U W N : Subgroup G}
    (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) (hW : IsNormalIn H U W) (hN : IsNormalIn H U N)
    (hWN : W ≤ N)
    (key : ∀ A B : Subgroup G, IsChiefStep H U A B → W ≤ A → IsCentralStep H A B) :
    ⁅N, oTwoUpper H⁆ ≤ W := by
  obtain ⟨n, hn⟩ := F112W.exists_isChiefSeriesBetween hW N hN hWN
  have h0 : ∀ {N' : Subgroup G} {m : ℕ}, F112W.IsChiefSeriesBetween H U W N' m → m = 0 := by
    intro N' m hm
    induction hm with
    | refl => rfl
    | central hstep hc hs ih => exact ih
    | noncentral hstep hnc hs ih => exact absurd (key _ _ hstep hs.le) hnc
  have := h0 hn
  subst this
  exact (F112W.isChiefSeriesBetween_zero_iff hUH hUQ hW hN hWN).mp hn

theorem relIndex_sup_eq_four {F L X R Y : Subgroup G} {a : G}
    (hLX : L ≤ X) (hXF : X ≤ F) (hFL : F ≤ Subgroup.normalizer (L : Set G))
    (hRX : R ≤ X) (hRY : R ≤ Y) (hY : ∀ u ∈ Y, ∀ w ∈ Y, u * w = w * u)
    (haY : a ∈ Y) (haF : a ∈ F) (hcomm : ⁅X, Y⁆ ≤ R)
    (h16 : L.relIndex X = 16)
    (h4 : secIdx (Subgroup.zpowers a) L X = 4 ∧
      L.relIndex (commSec (Subgroup.zpowers a) L X) = 4) :
    L.relIndex (R ⊔ L) = 4 := by
  have hXn : X ≤ Subgroup.normalizer (L : Set G) := hXF.trans hFL
  have hzF : Subgroup.zpowers a ≤ F := Subgroup.zpowers_le.mpr haF
  have hzY : Subgroup.zpowers a ≤ Y := Subgroup.zpowers_le.mpr haY
  set Fx := fixSecIn (Subgroup.zpowers a) L X with hFx
  have hLFx : L ≤ Fx := by
    intro l hl
    refine (mem_fixSecIn_iff hLX hXn).mpr ⟨hLX hl, fun b hb => ?_⟩
    have h1 : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hFL (hzF hb)) l).mp hl
    exact L.mul_mem h1 (L.inv_mem hl)
  have hRFx : R ≤ Fx := by
    intro r hr
    refine (mem_fixSecIn_iff hLX hXn).mpr ⟨hRX hr, fun b hb => ?_⟩
    have := hY b (hzY hb) r (hRY hr)
    rw [this]
    simp
  have hRL : R ⊔ L ≤ Fx := sup_le hRFx hLFx
  have hCm : commSec (Subgroup.zpowers a) L X ≤ R ⊔ L :=
    sup_le_sup_right ((Subgroup.commutator_mono le_rfl hzY).trans hcomm) L
  have e1 : L.relIndex Fx * Fx.relIndex X = L.relIndex X :=
    Subgroup.relIndex_mul_relIndex L Fx X hLFx (fixSecIn_le _ _ _)
  have e2 : Fx.relIndex X = 4 := h4.1
  have e3 : L.relIndex Fx = 4 := by rw [e2, h16] at e1; omega
  have e4 : L.relIndex (R ⊔ L) * (R ⊔ L).relIndex Fx = L.relIndex Fx :=
    Subgroup.relIndex_mul_relIndex L (R ⊔ L) Fx le_sup_right hRL
  have e5 : L.relIndex (commSec (Subgroup.zpowers a) L X) *
      (commSec (Subgroup.zpowers a) L X).relIndex (R ⊔ L) = L.relIndex (R ⊔ L) :=
    Subgroup.relIndex_mul_relIndex L _ (R ⊔ L) le_sup_right hCm
  have d1 : L.relIndex (R ⊔ L) ∣ 4 := Dvd.intro _ (e4.trans e3)
  have d2 : 4 ∣ L.relIndex (R ⊔ L) :=
    ⟨(commSec (Subgroup.zpowers a) L X).relIndex (R ⊔ L), by rw [← e5, h4.2]⟩
  exact Nat.dvd_antisymm d1 d2

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem relIndex_sup_le_two [Finite G] {K T Q W : Subgroup G} (hKT : K ≤ T)
    (hQ : Q.relIndex T = 4) (hWK : W ≤ K) (hWQ : ¬ W ≤ Q) :
    ((K ⊓ Q) ⊔ W).relIndex K ≤ 2 := by
  have h1 : (K ⊓ Q).relIndex K ≤ 4 := by
    have h := Subgroup.relIndex_le_of_le_right (H := Q) hKT (by rw [hQ]; norm_num)
    rw [hQ] at h
    rwa [inf_comm, Subgroup.inf_relIndex_right]
  have hYK : (K ⊓ Q) ⊔ W ≤ K := sup_le inf_le_left hWK
  have h2 := Subgroup.relIndex_mul_relIndex (K ⊓ Q) ((K ⊓ Q) ⊔ W) K le_sup_left hYK
  have h3 : 2 ≤ (K ⊓ Q).relIndex ((K ⊓ Q) ⊔ W) := by
    have hne0 := relIndex_ne_zero_of_finite (K ⊓ Q) ((K ⊓ Q) ⊔ W)
    have hne1 : (K ⊓ Q).relIndex ((K ⊓ Q) ⊔ W) ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      exact hWQ (((le_sup_right : W ≤ (K ⊓ Q) ⊔ W).trans h).trans inf_le_right)
    omega
  by_contra hcon
  have hcon' := not_le.mp hcon
  nlinarith

theorem secIdx_le_of_centralizes [Finite G] {A B K Y W Vb : Subgroup G} {v : G}
    (hBK : B ≤ K) (hVA : Vb ≤ A) (hv : v ∈ W)
    (hY : ∀ y ∈ Y, ∀ u ∈ W, y * u * y⁻¹ * u⁻¹ ∈ Vb) :
    secIdx (Subgroup.zpowers v) A B ≤ Y.relIndex K := by
  have hzW : Subgroup.zpowers v ≤ W := Subgroup.zpowers_le.mpr hv
  have hle : Y ⊓ B ≤ fixSecIn (Subgroup.zpowers v) A B := by
    intro y hy
    refine Subgroup.subset_closure ⟨hy.2, fun a ha => ?_⟩
    have h1 := hVA (hY y hy.1 a (hzW ha))
    have e : a * y * a⁻¹ * y⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact A.inv_mem h1
  unfold secIdx
  calc (fixSecIn (Subgroup.zpowers v) A B).relIndex B ≤ (Y ⊓ B).relIndex B :=
        Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)
    _ = Y.relIndex B := Subgroup.inf_relIndex_right Y B
    _ ≤ Y.relIndex K := Subgroup.relIndex_le_of_le_right hBK (relIndex_ne_zero_of_finite _ _)

theorem le_cSecIn_sup {S₀ F L R A : Subgroup G} (hA : A ≤ S₀) (hS₀F : S₀ ≤ F)
    (hFL : F ≤ Subgroup.normalizer (L : Set G)) (hR : R ≤ Subgroup.normalizer (L : Set G))
    (hRA : ∀ r ∈ R, ∀ c ∈ A, c * r * c⁻¹ * r⁻¹ ∈ L) :
    A ≤ cSecIn S₀ L (R ⊔ L) := by
  have hZ : R ⊔ L ≤ centralizerMod L ⊤ A := by
    refine sup_le (fun r hr => ⟨trivial, hR hr, fun u hu => ?_⟩)
      (fun l hl => ⟨trivial, Subgroup.le_normalizer hl, fun u hu => ?_⟩)
    · have e : r * u * r⁻¹ * u⁻¹ = (u * r * u⁻¹ * r⁻¹)⁻¹ := by group
      rw [e]
      exact L.inv_mem (hRA r hr u hu)
    · have h1 : u * l⁻¹ * u⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hFL (hS₀F (hA hu))) l⁻¹).mp (L.inv_mem hl)
      have e : l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
  intro c hc
  refine Subgroup.subset_closure ⟨hA hc, fun x hx => ?_⟩
  have h1 := (hZ hx).2.2 c hc
  have e : c * x * c⁻¹ * x⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ := by group
  rw [e]
  exact L.inv_mem h1

theorem cSecIn_eq_pCoreOf_of_nat [Finite G] {F L X : Subgroup G}
    (hq : Nonempty (OTwoQuot F ≃* Equiv.Perm (Fin 5))) (hN : IsNatSec F L X)
    (hle : pCoreOf 2 F ≤ cSecIn F L X) : cSecIn F L X = pCoreOf 2 F := by
  obtain ⟨_, θ, β, hθs, hθk, _⟩ := hN
  have hc : ((cSecIn F L X).subgroupOf F).index = 120 := by
    rw [← hθk, Subgroup.index_ker, θ.range_eq_top_of_surjective hθs, Subgroup.card_top]
    exact S152Fin.card_Perm_five
  have hp := SzF53A1.index_pCoreOf_eq hq
  have hsub : (pCoreOf 2 F).subgroupOf F ≤ (cSecIn F L X).subgroupOf F := fun x hx => hle hx
  have hrel := Subgroup.relIndex_mul_index hsub
  rw [hc, hp] at hrel
  have h1 : ((pCoreOf 2 F).subgroupOf F).relIndex ((cSecIn F L X).subgroupOf F) = 1 := by
    omega
  have h2 := Subgroup.relIndex_eq_one.mp h1
  refine le_antisymm (fun x hx => ?_) hle
  have hxF : x ∈ F := S152Fin.cSecIn_le_left F L X hx
  exact h2 (show (⟨x, hxF⟩ : ↥F) ∈ (cSecIn F L X).subgroupOf F from hx)

end N37

end F53B3

end CFSG.Quasithin
