module

public import CFSG.Quasithin.H13.A6S1372Fin
public import CFSG.Quasithin.H13.A6S1372Aut
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

@[expose] def Key13721 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsElemAbelian 2 (conjClosure V S.G1) →
    ∃ K ∈ cComp S.G1, ∃ hL1K : S.L1 ≤ K,
      K ≤ Subgroup.centralizer ((conjClosure S.V3 S.G1 ⊓
        Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) : Subgroup G) : Set G) ∧
      ⁅conjClosure S.V3 S.G1, K⁆ ⊔ fsuV1 T V = conjClosure S.V3 S.G1 ∧
      ∃ (α : ↥K →* alternatingGroup (Fin 6)) (β : ↥(conjClosure S.V3 S.G1) →* ↥W4),
        Function.Surjective α ∧ (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 S.G1) ∧
        Function.Surjective β ∧
        (∀ u : ↥(conjClosure S.V3 S.G1),
          β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V) ∧
        (∀ (k : ↥K) (u : ↥(conjClosure S.V3 S.G1))
          (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1),
          β ⟨_, hku⟩ = act4 (α k : Perm (Fin 6)) (β u)) ∧
        ∀ c (hc : c ∈ S.L1), c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 →
          ∀ w : ↥W4, act4 (α ⟨c, hL1K hc⟩ : Perm (Fin 6)) w = w → w = 1

namespace A6Key

theorem inv_conj_mem {G : Type} [Group G] {H : Subgroup G} {y k : G} (hy : y ∈ H) (hk : k ∈ H)
    (hyk : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : k⁻¹ * (y⁻¹ * k * y) ∈ pCoreOf 2 H := by
  have h1 : (y * k * y⁻¹ * k⁻¹)⁻¹ ∈ pCoreOf 2 H := Subgroup.inv_mem _ hyk
  have h2 : (k⁻¹ * y⁻¹) * (y * k * y⁻¹ * k⁻¹)⁻¹ * (k⁻¹ * y⁻¹)⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H
      (H.mul_mem (H.inv_mem hk) (H.inv_mem hy))) _).mp h1
  have e : k⁻¹ * (y⁻¹ * k * y) = (k⁻¹ * y⁻¹) * (y * k * y⁻¹ * k⁻¹)⁻¹ * (k⁻¹ * y⁻¹)⁻¹ := by
    group
  rw [e]
  exact h2

theorem card_mulAut_alt6 : Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  rw [← Nat.card_congr (MulAut.congr ψ).toEquiv,
    ← Nat.card_congr AutA6Rank.conjAutEquiv.toEquiv]
  exact CFSG.QuasithinUnique.A6Facts.card_autA6

theorem card_le_four_of_sq {X : Subgroup (alternatingGroup (Fin 6))}
    (h2 : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 4 := by
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  set X' : Subgroup (Equiv.Perm (Fin 10)) :=
    (X.map ψ.symm.toMonoidHom).map A6Models.psl29.subtype with hX'def
  have hX' : X' ≤ A6Models.psl29 := Subgroup.map_subtype_le _
  have h2' : ∀ x ∈ X', x * x = 1 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, h2 y hy, map_one, map_one]
  have hc : Nat.card X' = Nat.card X := by
    rw [hX'def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective ψ.symm.injective]
  rw [← hc]
  exact AutA6Rank.card_le_four_of_le_psl29 hX' h2'

theorem card_W4 : Nat.card ↥W4 = 16 := by
  have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

end A6Key

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V1_comm_of_mem_Hz {H : Subgroup G} (hH : H ∈ S.Hz) {v h : G} (hv : v ∈ fsuV1 T V)
    (hh : h ∈ H) : h * v = v * h := by
  rcases S.mem_V1_iff.1 hv with rfl | rfl
  · simp
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hH.2.1 hh)

structure KeyData (H K : Subgroup G) where
  le : K ≤ H
  α : ↥K →* alternatingGroup (Fin 6)
  β : ↥(conjClosure S.V3 H) →* ↥W4
  αs : Function.Surjective α
  αk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H
  βs : Function.Surjective β
  βk : ∀ u : ↥(conjClosure S.V3 H),
    β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V
  βα : ∀ (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H),
    β ⟨_, hku⟩ = act4 (α k : Perm (Fin 6)) (β u)
  comm : ⁅conjClosure S.V3 H, K⁆ ⊔ fsuV1 T V = conjClosure S.V3 H

variable {S}

namespace KeyData

variable {H K : Subgroup G} (D : S.KeyData H K)

theorem beta_V1 (hH : H ∈ S.Hz) {v : G} (hv : v ∈ fsuV1 T V) :
    D.β ⟨v, S.V1_le_UH hv⟩ = 1 := by
  rw [D.βk]
  intro k hk
  have h := S.V1_comm_of_mem_Hz hH hv (D.le hk)
  have e : k * v * k⁻¹ * v⁻¹ = 1 := by rw [h, mul_inv_cancel_right, mul_inv_cancel]
  rw [e]
  exact Subgroup.one_mem _

@[expose] def conjU {y : G} (hy : y ∈ H) (x : ↥(conjClosure S.V3 H)) :
    ↥(conjClosure S.V3 H) :=
  ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hy) x).mp x.2⟩

omit D in
theorem conjU_coe {y : G} (hy : y ∈ H) (x : ↥(conjClosure S.V3 H)) :
    ((conjU (S := S) hy x : ↥(conjClosure S.V3 H)) : G) = y * x * y⁻¹ := rfl

omit D in
theorem comm_QH_mem (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {q x : G} (hq : q ∈ pCoreOf 2 H)
    (hx : x ∈ conjClosure S.V3 H) : q * x * q⁻¹ * x⁻¹ ∈ fsuV1 T V := by
  rw [hF.pCoreOf_eq_centralizerMod] at hq
  exact hq.2.2 x hx

theorem beta_conjU_eq_one (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {x : ↥(conjClosure S.V3 H)}
    (hx : D.β x = 1) : D.β (conjU hy x) = 1 := by
  rw [D.βk] at hx ⊢
  intro k hk
  have hkH := D.le hk
  set q' := k⁻¹ * (y⁻¹ * k * y) with hq'
  have hq'Q : q' ∈ pCoreOf 2 H := A6Key.inv_conj_mem hy hkH (hyK k hk)
  have hw := comm_QH_mem hF hq'Q x.2
  have hwc := S.V1_comm_of_mem_Hz hH hw hkH
  have h1 : (k * q') * x * (k * q')⁻¹ * (x : G)⁻¹ =
      (q' * x * q'⁻¹ * (x : G)⁻¹) * (k * x * k⁻¹ * (x : G)⁻¹) := by
    calc (k * q') * x * (k * q')⁻¹ * (x : G)⁻¹ =
        (k * (q' * x * q'⁻¹ * (x : G)⁻¹)) * k⁻¹ * (k * x * k⁻¹ * (x : G)⁻¹) := by group
      _ = ((q' * x * q'⁻¹ * (x : G)⁻¹) * k) * k⁻¹ * (k * x * k⁻¹ * (x : G)⁻¹) := by rw [hwc]
      _ = _ := by group
  have h2 : (k * q') * x * (k * q')⁻¹ * (x : G)⁻¹ ∈ fsuV1 T V := by
    rw [h1]
    exact Subgroup.mul_mem _ hw (hx k hk)
  have e : k * (y * x * y⁻¹) * k⁻¹ * (y * x * y⁻¹)⁻¹ =
      y * ((k * q') * x * (k * q')⁻¹ * (x : G)⁻¹) * y⁻¹ := by
    rw [hq']
    group
  rw [conjU_coe, e, S.V1_comm_of_mem_Hz hH h2 hy, mul_inv_cancel_right]
  exact h2

theorem beta_conjU_congr (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {x x' : ↥(conjClosure S.V3 H)} (h : D.β x = D.β x') :
    D.β (conjU hy x) = D.β (conjU hy x') := by
  have h1 : D.β (x⁻¹ * x') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := D.beta_conjU_eq_one hH hF hy hyK h1
  have e : conjU hy (x⁻¹ * x') = (conjU hy x)⁻¹ * conjU hy x' := by
    apply Subtype.ext
    simp only [conjU_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

@[expose] noncomputable def gY (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : ↥W4 →* ↥W4 :=
  MonoidHom.mk' (fun w => D.β (conjU hy (Function.surjInv D.βs w))) fun w w' => by
    obtain ⟨x, rfl⟩ := D.βs w
    obtain ⟨x', rfl⟩ := D.βs w'
    rw [D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x)),
      D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x')), ← map_mul,
      D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β (x * x'))), ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [conjU_coe, Subgroup.coe_mul]
    group

theorem gY_apply (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (x : ↥(conjClosure S.V3 H)) : D.gY hH hF hy hyK (D.β x) = D.β (conjU hy x) :=
  D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x))

theorem beta_conj_QH (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {q : G}
    (hq : q ∈ pCoreOf 2 H) (x : ↥(conjClosure S.V3 H)) :
    D.β (conjU ((pCoreOf_le 2 H) hq) x) = D.β x := by
  have hw := comm_QH_mem hF hq x.2
  have e : conjU ((pCoreOf_le 2 H) hq) x = ⟨_, S.V1_le_UH hw⟩ * x := by
    apply Subtype.ext
    simp only [conjU_coe, Subgroup.coe_mul]
    group
  rw [e, map_mul, D.beta_V1 hH hw, one_mul]

theorem gY_comm (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∀ σ ∈ alternatingGroup (Fin 6), ∀ w, D.gY hH hF hy hyK (act4 σ w) =
      act4 σ (D.gY hH hF hy hyK w) := by
  intro σ hσ w
  obtain ⟨k, hk⟩ := D.αs ⟨σ, hσ⟩
  obtain ⟨x, rfl⟩ := D.βs w
  have hσk : σ = (D.α k : Perm (Fin 6)) := by rw [hk]
  have hkH := D.le k.2
  have e1 : act4 σ (D.β x) = D.β (conjU hkH x) := by
    rw [hσk]
    exact (D.βα k x (conjU hkH x).2).symm
  have e2 : act4 σ (D.β (conjU hy x)) = D.β (conjU hkH (conjU hy x)) := by
    rw [hσk]
    exact (D.βα k (conjU hy x) (conjU hkH (conjU hy x)).2).symm
  rw [e1, gY_apply, gY_apply, e2]
  set q := y * k * y⁻¹ * (k : G)⁻¹ with hqdef
  have hqQ : q ∈ pCoreOf 2 H := hyK k k.2
  have h1 := D.beta_conj_QH hH hF hqQ (conjU hkH (conjU hy x))
  rw [← h1]
  congr 1
  apply Subtype.ext
  simp only [conjU_coe]
  rw [hqdef]
  group

theorem beta_conjU_eq (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) (x : ↥(conjClosure S.V3 H)) :
    D.β (conjU hy x) = D.β x := by
  rcases A6Fin.end_W4 (D.gY hH hF hy hyK) (D.gY_comm hH hF hy hyK) with h0 | h1
  · exfalso
    obtain ⟨x', hx'⟩ := D.βs (A6Fin.dvW 1)
    have hyinv : y⁻¹ ∈ H := H.inv_mem hy
    have e : conjU hy (conjU hyinv x') = x' := by
      apply Subtype.ext
      simp only [conjU_coe]
      group
    have h2 := h0 (D.β (conjU hyinv x'))
    rw [gY_apply, e, hx'] at h2
    exact (dv_zero_facts.1 1 (by decide)) (congrArg Subtype.val h2)
  · rw [← gY_apply D hH hF hy hyK]
    exact h1 _

include D in
theorem comm_conj_mem (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {u k : G}
    (hu : u ∈ conjClosure S.V3 H) (hk : k ∈ K) :
    y * ⁅u, k⁆ * y⁻¹ * ⁅u, k⁆⁻¹ ∈ fsuV1 T V := by
  have hkH := D.le hk
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  set U := conjClosure S.V3 H with hU
  set c := u⁻¹ * (y * u * y⁻¹) with hc
  have hyu : y * u * y⁻¹ ∈ U := (conjU hy ⟨u, hu⟩).2
  have hcU : c ∈ U := U.mul_mem (U.inv_mem hu) hyu
  have hc1 : D.β ⟨c, hcU⟩ = 1 := by
    have e : (⟨c, hcU⟩ : ↥U) = (⟨u, hu⟩ : ↥U)⁻¹ * conjU hy ⟨u, hu⟩ := rfl
    rw [e, map_mul, map_inv, D.beta_conjU_eq hH hF hy hyK, inv_mul_cancel]
  have hw₁ : k * c * k⁻¹ * c⁻¹ ∈ fsuV1 T V := (D.βk _).1 hc1 k hk
  set q := y * k * y⁻¹ * k⁻¹ with hq
  have hqQ : q ∈ pCoreOf 2 H := hyK k hk
  set X := k * (u * c)⁻¹ * k⁻¹ with hX
  have hXU : X ∈ U := by
    have h1 : (u * c)⁻¹ ∈ U := U.inv_mem (U.mul_mem hu hcU)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hkH) _).mp h1
  have hw₂ : q * X * q⁻¹ * X⁻¹ ∈ fsuV1 T V := comm_QH_mem hF hqQ hXU
  set w₁ := k * c * k⁻¹ * c⁻¹ with hw₁def
  set w₂ := q * X * q⁻¹ * X⁻¹ with hw₂def
  have hcw₂ : (u * c) * w₂ = w₂ * (u * c) :=
    (S.V1_comm_of_mem_Hz hH hw₂ (hUH (U.mul_mem hu hcU)))
  have hcw₁ : u * w₁⁻¹ = w₁⁻¹ * u :=
    (S.V1_comm_of_mem_Hz hH ((fsuV1 T V).inv_mem hw₁) (hUH hu))
  have key : y * ⁅u, k⁆ * y⁻¹ = w₂ * w₁⁻¹ * ⁅u, k⁆ := by
    calc y * ⁅u, k⁆ * y⁻¹ = (u * c) * (q * X * q⁻¹) := by
          rw [commutatorElement_def, hX, hc, hq]
          group
      _ = (u * c) * w₂ * X := by rw [hw₂def]; group
      _ = w₂ * ((u * c) * X) := by rw [hcw₂, mul_assoc]
      _ = w₂ * (u * w₁⁻¹ * (k * u⁻¹ * k⁻¹)) := by rw [hX, hw₁def]; group
      _ = w₂ * (w₁⁻¹ * u * (k * u⁻¹ * k⁻¹)) := by rw [hcw₁]
      _ = w₂ * w₁⁻¹ * ⁅u, k⁆ := by rw [commutatorElement_def]; group
  rw [key, mul_inv_cancel_right]
  exact (fsuV1 T V).mul_mem hw₂ ((fsuV1 T V).inv_mem hw₁)

include D in
theorem mem_pCoreOf_of_comm (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : y ∈ pCoreOf 2 H := by
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  set U := conjClosure S.V3 H with hU
  have hcen : ∀ v ∈ fsuV1 T V, ∀ h ∈ H, h * v = v * h := fun v hv h hh =>
    S.V1_comm_of_mem_Hz hH hv hh
  let Dy : Subgroup G :=
    { carrier := {x | x ∈ U ∧ y * x * y⁻¹ * x⁻¹ ∈ fsuV1 T V}
      one_mem' := ⟨U.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
        refine ⟨U.mul_mem haU hbU, ?_⟩
        have hyaU : y * a * y⁻¹ ∈ U := (conjU hy ⟨a, haU⟩).2
        have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
            (y * a * y⁻¹) * (y * b * y⁻¹ * b⁻¹) * (y * a * y⁻¹)⁻¹ * (y * a * y⁻¹ * a⁻¹) := by
          group
        rw [e, hcen _ hb _ (hUH hyaU), mul_inv_cancel_right]
        exact (fsuV1 T V).mul_mem hb ha
      inv_mem' := by
        rintro a ⟨haU, ha⟩
        refine ⟨U.inv_mem haU, ?_⟩
        have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e, hcen _ ((fsuV1 T V).inv_mem ha) _ (hUH (U.inv_mem haU)), mul_assoc,
          inv_mul_cancel, mul_one]
        exact (fsuV1 T V).inv_mem ha }
  have hle : ⁅U, K⁆ ⊔ fsuV1 T V ≤ Dy := by
    refine sup_le ?_ fun v hv => ⟨S.V1_le_UH hv, ?_⟩
    · rw [Subgroup.commutator_le]
      intro u hu k hk
      refine ⟨?_, D.comm_conj_mem hH hF hy hyK hu hk⟩
      have hku : k * u⁻¹ * k⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (D.le hk)) _).mp
          (U.inv_mem hu)
      have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact U.mul_mem hu hku
    · rw [hcen v hv y hy, mul_inv_cancel_right, mul_inv_cancel]
      exact (fsuV1 T V).one_mem
  rw [D.comm] at hle
  rw [hF.pCoreOf_eq_centralizerMod]
  exact ⟨hy, hF.H_normalizes_V₁ hy, fun u hu => (hle hu).2⟩

include D in
theorem le_normalizer_of_key
    (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) (hKc : K ∈ cComp H) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  intro h hh
  have hO2 : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have := S.h13.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have h37 := QuasithinUnique.Vol2Native.a37ForSQTKCat_proved _ hQs
  by_contra hn
  have hne : K.map (MulAut.conj h).toMonoidHom ≠ K := fun he =>
    hn (A38.map_conj_eq_iff.mp he)
  have hK'c : K.map (MulAut.conj h).toMonoidHom ∈ cComp H :=
    LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer hh)
  have hcomm := commutator_le_pCoreOf_of_ne h37 hK'c hKc hne
  have hle : K.map (MulAut.conj h).toMonoidHom ≤ pCoreOf 2 H := by
    intro y hy
    refine D.mem_pCoreOf_of_comm hH hF (le_of_mem_cComp hK'c hy) fun k hk => ?_
    exact hcomm (Subgroup.commutator_mem_commutator hy hk)
  apply not_isSolvable_of_mem_cComp hK'c
  have : Group.IsSolvable ↥(pCoreOf 2 H) := isSolvable_pCoreOf_two H
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

include D in
theorem sup_eq_of_key (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : K ⊔ T = H := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    D.le.trans (le_normalizer_pCoreOf 2 H)
  set Γ := AutA6Rank.gam hHK (le_normalizer_pCoreOf 2 H) D.αs D.αk with hΓ
  have hker : Γ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext e
    rw [AutA6Rank.mem_ker_gam_iff hKQ hHK (le_normalizer_pCoreOf 2 H) D.αs D.αk
      (fun e he hk => D.mem_pCoreOf_of_comm hH hF he hk), Subgroup.mem_subgroupOf]
  have h1 : (pCoreOf 2 H).relIndex H ∣ 1440 := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, ← A6Key.card_mulAut_alt6]
    exact Subgroup.card_subgroup_dvd_card _
  have hkerα : D.α.ker = (pCoreOf 2 H).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, D.αk, Subgroup.mem_subgroupOf]
  have h2 : (pCoreOf 2 H).relIndex K = 360 := by
    rw [Subgroup.relIndex, ← hkerα, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr D.αs, Subgroup.card_top]
    exact CFSG.QuasithinUnique.DoubleA3.card_alt6'
  have hQn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr (le_normalizer_pCoreOf 2 H)
  have h3 : (pCoreOf 2 H).relIndex (K ⊔ pCoreOf 2 H) = 360 := by
    rw [← Subgroup.relIndex_subgroupOf (sup_le D.le hQH), Subgroup.subgroupOf_sup D.le hQH,
      Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf D.le, h2]
  have hKTH : K ⊔ T ≤ H := sup_le D.le hTH
  have h4 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (K ⊔ pCoreOf 2 H) (K ⊔ T) le_sup_right
    (sup_le_sup_left hQT K)
  have h5 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (K ⊔ T) H (hQT.trans le_sup_right)
    hKTH
  rw [← h4, h3] at h5
  set b := (K ⊔ T).relIndex H with hb
  have hb4 : b ∣ 4 := by
    rw [← h5, mul_assoc, show (1440 : ℕ) = 360 * 4 from rfl] at h1
    exact (dvd_mul_left b _).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
  have hbodd : ¬ 2 ∣ b := fun h2b =>
    hTs.2.2 (h2b.trans (Subgroup.relIndex_dvd_of_le_left H le_sup_right))
  have hb1 : b = 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl] at hb4
    obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb4
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hbj
    · exact absurd (hbj ▸ dvd_pow_self 2 hj0.ne') hbodd
  exact le_antisymm hKTH ((Subgroup.relIndex_eq_one).mp hb1)

theorem sixteen_le_nu_of_key {c : G} (hcK : c ∈ K)
    (hfix : ∀ w : ↥W4, act4 (D.α ⟨c, hcK⟩ : Perm (Fin 6)) w = w → w = 1) :
    4 ^ 2 ≤ nu c (conjClosure S.V3 H) := by
  set U := conjClosure S.V3 H with hU
  set Cβ : Subgroup G := D.β.ker.map U.subtype with hCβ
  have hle : cfix c U ≤ Cβ := by
    intro x hx
    obtain ⟨hxU, hxc⟩ := mem_cfix.1 hx
    have hcx : c * x * c⁻¹ = x := by rw [hxc, mul_inv_cancel_right]
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    show (⟨x, hxU⟩ : ↥U) ∈ D.β.ker
    rw [MonoidHom.mem_ker]
    apply hfix
    have hxU' : (c : G) * x * (c : G)⁻¹ ∈ U := by rw [hcx]; exact hxU
    have h1 := D.βα ⟨c, hcK⟩ ⟨x, hxU⟩ hxU'
    rw [← h1]
    congr 1
    exact Subtype.ext hcx
  have h16 : Cβ.relIndex U = 16 := by
    rw [Subgroup.relIndex, hCβ, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr D.βs, Subgroup.card_top, A6Key.card_W4]
  have hdvd := Subgroup.relIndex_dvd_of_le_left U hle
  rw [h16] at hdvd
  have hne : (cfix c U).relIndex U ≠ 0 := Subgroup.index_ne_zero_of_finite
  unfold nu
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  omega

theorem exists_comm_not_mem_of_key (hhat : ¬ IsHatA6 L)
    (hH : H ∈ S.Hz) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : S.L1 ≤ K) {c : G}
    (hc : c ∈ S.L1) (hc3 : c ^ 3 = 1)
    (hfix : ∀ w : ↥W4, act4 (D.α ⟨c, hL1K hc⟩ : Perm (Fin 6)) w = w → w = 1) :
    ∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set α := D.α with hαdef
  set γ : ↥K := ⟨c, hL1K hc⟩ with hγ
  set σ : Perm (Fin 6) := (α γ : Perm (Fin 6)) with hσ
  have hσA : σ ∈ alternatingGroup (Fin 6) := (α γ).2
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : γ ^ 3 = 1 := Subtype.ext (by simpa [hγ] using hc3)
    have h2 : (α γ) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    rw [hσ, ← Subgroup.coe_pow, h2, Subgroup.coe_one]
  have hfixP : ∀ w : P6, InW4 w → act4f σ w = w → w = 1 := by
    intro w hw h
    have h1 := hfix ⟨w, hw⟩ (Subtype.ext (by rw [act4_coe]; exact h))
    exact congrArg Subtype.val h1
  have hα1 : α γ ≠ 1 := by
    intro h1
    have hσ1 : σ = 1 := by rw [hσ, h1]; rfl
    have h2 := hfix (A6Fin.dvW 1) (by rw [hσ1, map_one, MulAut.one_apply])
    exact (dv_zero_facts.1 1 (by decide)) (congrArg Subtype.val h2)
  have hO1 : ∀ o (ho : o ∈ pCoreOf 2 S.L1), α ⟨o, hL1K (pCoreOf_le 2 S.L1 ho)⟩ = 1 := by
    intro o ho
    set ω : ↥K := ⟨o, hL1K (pCoreOf_le 2 S.L1 ho)⟩ with hω
    have hcomm : α (γ * ω * γ⁻¹ * ω⁻¹) = 1 := (D.αk _).2 (hall o ho)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hcomm
    have hc' : (α ω : Perm (Fin 6)) * σ = σ * α ω := by
      have h1 : α γ * α ω = α ω * α γ := by
        calc α γ * α ω = (α γ * α ω * (α γ)⁻¹ * (α ω)⁻¹) * α ω * α γ := by group
          _ = α ω * α γ := by rw [hcomm, one_mul]
      exact (congrArg Subtype.val h1).symm
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1 ⟨o, ho⟩
    have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hτk : (α ω : Perm (Fin 6)) ^ 2 ^ k = 1 := by
      have h1 : ω ^ 2 ^ k = 1 := Subtype.ext (by simpa [hω] using hok)
      have h2 : (α ω) ^ 2 ^ k = 1 := by rw [← map_pow, h1, map_one]
      rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
    exact Subtype.ext (A6Fin.eq_one_of_commute hσA hσ3 hfixP (α ω).2 hc' hτk)
  set c₀ : G := (S.cL1 hhat : G) with hc₀
  have hc₀L : c₀ ∈ S.L1 := S.cL1_mem hhat
  set a := α ⟨c₀, hL1K hc₀L⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    have h1 : (⟨c₀, hL1K hc₀L⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
    rw [ha, ← map_pow, h1, map_one]
  have hcases : ∀ x (hx : x ∈ S.L1), α ⟨x, hL1K hx⟩ ≠ 1 →
      α ⟨x, hL1K hx⟩ = a ∨ α ⟨x, hL1K hx⟩ = a * a := by
    intro x hx hx1
    rcases S.L1_decomp hhat hx with h | h | h
    · exact absurd (hO1 x h) hx1
    · have h1 := hO1 _ h
      have e : (⟨c₀ * c₀ * x, hL1K (pCoreOf_le 2 S.L1 h)⟩ : ↥K) =
          ⟨c₀, hL1K hc₀L⟩ * ⟨c₀, hL1K hc₀L⟩ * ⟨x, hL1K hx⟩ := rfl
      rw [e, map_mul, map_mul] at h1
      left
      calc α ⟨x, hL1K hx⟩ = a ^ 3 * α ⟨x, hL1K hx⟩ := by rw [ha3, one_mul]
        _ = a * (a * a * α ⟨x, hL1K hx⟩) := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a := by rw [h1, mul_one]
    · have h1 := hO1 _ h
      have e : (⟨c₀ * x, hL1K (pCoreOf_le 2 S.L1 h)⟩ : ↥K) =
          ⟨c₀, hL1K hc₀L⟩ * ⟨x, hL1K hx⟩ := rfl
      rw [e, map_mul] at h1
      right
      calc α ⟨x, hL1K hx⟩ = a ^ 3 * α ⟨x, hL1K hx⟩ := by rw [ha3, one_mul]
        _ = a * a * (a * α ⟨x, hL1K hx⟩) := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a * a := by rw [h1, mul_one]
  have hca : α γ = a ∨ α γ = a * a := hcases c hc hα1
  have hnorm : ∀ t : ↥K, (t : G) ∈ T →
      (α t : Perm (Fin 6)) * σ = σ * α t ∨ (α t : Perm (Fin 6)) * σ = σ * σ * α t := by
    intro t htT
    set d := α t with hd
    have hxL : (t : G) * c * (t : G)⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) c).mp hc
    have hαx : α ⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ = d * α γ * d⁻¹ := by
      have e : (⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ : ↥K) = t * γ * t⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    have hx1 : α ⟨(t : G) * c * (t : G)⁻¹, hL1K hxL⟩ ≠ 1 := by
      rw [hαx]
      intro h
      apply hα1
      calc α γ = d⁻¹ * (d * α γ * d⁻¹) * d := by group
        _ = 1 := by rw [h]; group
    have hxa := hcases _ hxL hx1
    rw [hαx] at hxa
    have ha4 : a * a * (a * a) = a := by
      calc a * a * (a * a) = a ^ 3 * a := by rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = a := by rw [ha3, one_mul]
    have key : d * α γ * d⁻¹ = α γ ∨ d * α γ * d⁻¹ = α γ * α γ := by
      rcases hca with h | h <;> rcases hxa with h' | h'
      · exact Or.inl (h'.trans h.symm)
      · exact Or.inr (by rw [h', h])
      · exact Or.inr (by rw [h', h, ha4])
      · exact Or.inl (h'.trans h.symm)
    rcases key with h | h
    · left
      have h1 : d * α γ = α γ * d := by
        calc d * α γ = (d * α γ * d⁻¹) * d := by group
          _ = α γ * d := by rw [h]
      exact congrArg Subtype.val h1
    · right
      have h1 : d * α γ = α γ * α γ * d := by
        calc d * α γ = (d * α γ * d⁻¹) * d := by group
          _ = α γ * α γ * d := by rw [h]
      exact congrArg Subtype.val h1
  set Dα : Subgroup (alternatingGroup (Fin 6)) := ((T ⊓ K).subgroupOf K).map α with hDα
  have hsq : ∀ x ∈ Dα, x * x = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp ht
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨t, ht'.1⟩
    have htk : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hdk : (α t : Perm (Fin 6)) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, htk, map_one, Subgroup.coe_one]
    have h2 := A6Fin.sq_eq_one_of_normalizes hσA hσ3 hfixP (α t).2 (hnorm t ht'.1) hdk
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← pow_two, h2, Subgroup.coe_one]
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer D.le).mpr hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs D.le hKn.isSubnormal
  have hodd : ¬ 2 ∣ Dα.index := fun h => hTK.2.2 (h.trans (Subgroup.index_map_dvd _ D.αs))
  have hcard : Nat.card Dα * Dα.index = 360 := by
    rw [Subgroup.card_mul_index, CFSG.QuasithinUnique.DoubleA3.card_alt6']
  have hcop : Nat.Coprime (2 ^ 3) Dα.index :=
    Nat.Coprime.pow_left 3
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  have h8 : 2 ^ 3 ∣ Nat.card Dα := hcop.dvd_of_dvd_mul_right (by rw [hcard]; norm_num)
  have h4 := A6Key.card_le_four_of_sq hsq
  have hpos : 0 < Nat.card Dα := Nat.card_pos
  have := Nat.le_of_dvd hpos h8
  omega

end KeyData

end Setting4

theorem input13721K_of_key
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hKey : Key13721) : Input13721K := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab hna
  obtain ⟨K, hKc, hL1K, hKU0, hUK, α, β, hαs, hαk, hβs, hβk, hβα, hfix⟩ :=
    hKey G T L V S hNS hNU hhat hG1 hab hna
  have hF := S.hypF91 hNS h13315 h1356two hG1
  let D : S.KeyData S.G1 K := ⟨le_of_mem_cComp hKc, α, β, hαs, hαk, hβs, hβk, hβα, hUK⟩
  have hHK := D.le_normalizer_of_key hG1 hF hKc
  refine ⟨K, hHK, hL1K, D.sup_eq_of_key hG1 hF hHK, hKU0, ⟨α, hαs, hαk⟩,
    fun h hh hk => D.mem_pCoreOf_of_comm hG1 hF hh hk, fun c hc hc3 hcO => ⟨?_, ?_⟩⟩
  · exact D.exists_comm_not_mem_of_key hhat hG1 hHK hL1K hc hc3 (hfix c hc hc3 hcO)
  · exact D.sixteen_le_nu_of_key (hL1K hc) (hfix c hc hc3 hcO)

end CFSG.Quasithin.H13.A6
