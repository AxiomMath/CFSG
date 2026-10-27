module

public import CFSG.Quasithin.H13.A6S1372Key
public import CFSG.Quasithin.H13.A6S1372L24a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace A6L76D

@[expose] def EndTriv {Γ W : Type} [Group Γ] [CommGroup W] (act : Γ →* MulAut W) : Prop :=
  ∀ f : W →* W, (∀ γ w, f (act γ w) = act γ (f w)) → (∀ w, f w = 1) ∨ (∀ w, f w = w)

end A6L76D

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

structure KeyDataG (H K : Subgroup G) (Γ W : Type) [Group Γ] [CommGroup W]
    (act : Γ →* MulAut W) where
  le : K ≤ H
  α : ↥K →* Γ
  β : ↥(conjClosure S.V3 H) →* W
  αs : Function.Surjective α
  αk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H
  βs : Function.Surjective β
  βk : ∀ u : ↥(conjClosure S.V3 H),
    β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V
  βα : ∀ (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H),
    β ⟨_, hku⟩ = act (α k) (β u)
  comm : ⁅conjClosure S.V3 H, K⁆ ⊔ fsuV1 T V = conjClosure S.V3 H

variable {S}

namespace KeyDataG

variable {H K : Subgroup G} {Γ W : Type} [Group Γ] [CommGroup W] {act : Γ →* MulAut W}
  (D : S.KeyDataG H K Γ W act)

theorem beta_V1 (hH : H ∈ S.Hz) {v : G} (hv : v ∈ fsuV1 T V) :
    D.β ⟨v, S.V1_le_UH hv⟩ = 1 := by
  rw [D.βk]
  intro k hk
  have h := S.V1_comm_of_mem_Hz hH hv (D.le hk)
  have e : k * v * k⁻¹ * v⁻¹ = 1 := by rw [h, mul_inv_cancel_right, mul_inv_cancel]
  rw [e]
  exact Subgroup.one_mem _

theorem beta_conjU_eq_one (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {x : ↥(conjClosure S.V3 H)} (hx : D.β x = 1) : D.β (KeyData.conjU hy x) = 1 := by
  rw [D.βk] at hx ⊢
  intro k hk
  have hkH := D.le hk
  set q' := k⁻¹ * (y⁻¹ * k * y) with hq'
  have hq'Q : q' ∈ pCoreOf 2 H := A6Key.inv_conj_mem hy hkH (hyK k hk)
  have hw := KeyData.comm_QH_mem hF hq'Q x.2
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
  rw [KeyData.conjU_coe, e, S.V1_comm_of_mem_Hz hH h2 hy, mul_inv_cancel_right]
  exact h2

theorem beta_conjU_congr (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {x x' : ↥(conjClosure S.V3 H)} (h : D.β x = D.β x') :
    D.β (KeyData.conjU hy x) = D.β (KeyData.conjU hy x') := by
  have h1 : D.β (x⁻¹ * x') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := D.beta_conjU_eq_one hH hF hy hyK h1
  have e : KeyData.conjU hy (x⁻¹ * x') = (KeyData.conjU hy x)⁻¹ * KeyData.conjU hy x' := by
    apply Subtype.ext
    simp only [KeyData.conjU_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

@[expose] noncomputable def gY (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : W →* W :=
  MonoidHom.mk' (fun w => D.β (KeyData.conjU hy (Function.surjInv D.βs w))) fun w w' => by
    obtain ⟨x, rfl⟩ := D.βs w
    obtain ⟨x', rfl⟩ := D.βs w'
    rw [D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x)),
      D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x')), ← map_mul,
      D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β (x * x'))), ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [KeyData.conjU_coe, Subgroup.coe_mul]
    group

theorem gY_apply (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (x : ↥(conjClosure S.V3 H)) : D.gY hH hF hy hyK (D.β x) = D.β (KeyData.conjU hy x) :=
  D.beta_conjU_congr hH hF hy hyK (Function.surjInv_eq D.βs (D.β x))

theorem beta_conj_QH (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {q : G}
    (hq : q ∈ pCoreOf 2 H) (x : ↥(conjClosure S.V3 H)) :
    D.β (KeyData.conjU ((pCoreOf_le 2 H) hq) x) = D.β x := by
  have hw := KeyData.comm_QH_mem hF hq x.2
  have e : KeyData.conjU ((pCoreOf_le 2 H) hq) x = ⟨_, S.V1_le_UH hw⟩ * x := by
    apply Subtype.ext
    simp only [KeyData.conjU_coe, Subgroup.coe_mul]
    group
  rw [e, map_mul, D.beta_V1 hH hw, one_mul]

theorem gY_comm (hH : H ∈ S.Hz) (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∀ γ w, D.gY hH hF hy hyK (act γ w) = act γ (D.gY hH hF hy hyK w) := by
  intro γ w
  obtain ⟨k, rfl⟩ := D.αs γ
  obtain ⟨x, rfl⟩ := D.βs w
  have hkH := D.le k.2
  have e1 : act (D.α k) (D.β x) = D.β (KeyData.conjU hkH x) :=
    (D.βα k x (KeyData.conjU hkH x).2).symm
  have e2 : act (D.α k) (D.β (KeyData.conjU hy x)) =
      D.β (KeyData.conjU hkH (KeyData.conjU hy x)) :=
    (D.βα k (KeyData.conjU hy x) (KeyData.conjU hkH (KeyData.conjU hy x)).2).symm
  rw [e1, gY_apply, gY_apply, e2]
  set q := y * k * y⁻¹ * (k : G)⁻¹ with hqdef
  have hqQ : q ∈ pCoreOf 2 H := hyK k k.2
  have h1 := D.beta_conj_QH hH hF hqQ (KeyData.conjU hkH (KeyData.conjU hy x))
  rw [← h1]
  congr 1
  apply Subtype.ext
  simp only [KeyData.conjU_coe]
  rw [hqdef]
  group

theorem beta_conjU_eq (hEnd : A6L76D.EndTriv act) [Nontrivial W] (hH : H ∈ S.Hz)
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G} (hy : y ∈ H)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) (x : ↥(conjClosure S.V3 H)) :
    D.β (KeyData.conjU hy x) = D.β x := by
  rcases hEnd (D.gY hH hF hy hyK) (D.gY_comm hH hF hy hyK) with h0 | h1
  · exfalso
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    obtain ⟨x', hx'⟩ := D.βs w
    have hyinv : y⁻¹ ∈ H := H.inv_mem hy
    have e : KeyData.conjU hy (KeyData.conjU hyinv x') = x' := by
      apply Subtype.ext
      simp only [KeyData.conjU_coe]
      group
    have h2 := h0 (D.β (KeyData.conjU hyinv x'))
    rw [gY_apply, e, hx'] at h2
    exact hw h2
  · rw [← gY_apply D hH hF hy hyK]
    exact h1 _

include D in
theorem comm_conj_mem (hEnd : A6L76D.EndTriv act) [Nontrivial W] (hH : H ∈ S.Hz)
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
    (hy : y ∈ H) (hyK : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {u k : G}
    (hu : u ∈ conjClosure S.V3 H) (hk : k ∈ K) :
    y * ⁅u, k⁆ * y⁻¹ * ⁅u, k⁆⁻¹ ∈ fsuV1 T V := by
  have hkH := D.le hk
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  set U := conjClosure S.V3 H with hU
  set c := u⁻¹ * (y * u * y⁻¹) with hc
  have hyu : y * u * y⁻¹ ∈ U := (KeyData.conjU hy ⟨u, hu⟩).2
  have hcU : c ∈ U := U.mul_mem (U.inv_mem hu) hyu
  have hc1 : D.β ⟨c, hcU⟩ = 1 := by
    have e : (⟨c, hcU⟩ : ↥U) = (⟨u, hu⟩ : ↥U)⁻¹ * KeyData.conjU hy ⟨u, hu⟩ := rfl
    rw [e, map_mul, map_inv, D.beta_conjU_eq hEnd hH hF hy hyK, inv_mul_cancel]
  have hw₁ : k * c * k⁻¹ * c⁻¹ ∈ fsuV1 T V := (D.βk _).1 hc1 k hk
  set q := y * k * y⁻¹ * k⁻¹ with hq
  have hqQ : q ∈ pCoreOf 2 H := hyK k hk
  set X := k * (u * c)⁻¹ * k⁻¹ with hX
  have hXU : X ∈ U := by
    have h1 : (u * c)⁻¹ ∈ U := U.inv_mem (U.mul_mem hu hcU)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hkH) _).mp h1
  have hw₂ : q * X * q⁻¹ * X⁻¹ ∈ fsuV1 T V := KeyData.comm_QH_mem hF hqQ hXU
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
theorem mem_pCoreOf_of_comm (hEnd : A6L76D.EndTriv act) [Nontrivial W] (hH : H ∈ S.Hz)
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) {y : G}
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
        have hyaU : y * a * y⁻¹ ∈ U := (KeyData.conjU hy ⟨a, haU⟩).2
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
      refine ⟨?_, D.comm_conj_mem hEnd hH hF hy hyK hu hk⟩
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
theorem sup_eq [Finite Γ] (hEnd : A6L76D.EndTriv act) [Nontrivial W] {a : ℕ}
    (hAut : Nat.card (MulAut Γ) = Nat.card Γ * 2 ^ a) (hH : H ∈ S.Hz)
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    K ⊔ T = H := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    D.le.trans (le_normalizer_pCoreOf 2 H)
  set Ψ := A6L24.gamX hHK (le_normalizer_pCoreOf 2 H) D.αs D.αk with hΨ
  have hker : Ψ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext e
    rw [A6L24.mem_ker_gamX_iff hKQ hHK (le_normalizer_pCoreOf 2 H) D.αs D.αk
      (fun e he hk => D.mem_pCoreOf_of_comm hEnd hH hF he hk), Subgroup.mem_subgroupOf]
  have h1 : (pCoreOf 2 H).relIndex H ∣ Nat.card Γ * 2 ^ a := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, ← hAut]
    exact Subgroup.card_subgroup_dvd_card _
  have hkerα : D.α.ker = (pCoreOf 2 H).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, D.αk, Subgroup.mem_subgroupOf]
  have h2 : (pCoreOf 2 H).relIndex K = Nat.card Γ := by
    rw [Subgroup.relIndex, ← hkerα, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr D.αs, Subgroup.card_top]
  have h3 : (pCoreOf 2 H).relIndex (K ⊔ pCoreOf 2 H) = Nat.card Γ := by
    rw [← Subgroup.relIndex_subgroupOf (sup_le D.le hQH), Subgroup.subgroupOf_sup D.le hQH,
      Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf D.le, h2]
  have hKTH : K ⊔ T ≤ H := sup_le D.le hTH
  have h4 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (K ⊔ pCoreOf 2 H) (K ⊔ T) le_sup_right
    (sup_le_sup_left hQT K)
  have h5 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (K ⊔ T) H (hQT.trans le_sup_right)
    hKTH
  rw [← h4, h3] at h5
  set b := (K ⊔ T).relIndex H with hb
  have hΓ0 : 0 < Nat.card Γ := Nat.card_pos
  have hba : b ∣ 2 ^ a := by
    rw [← h5, mul_assoc] at h1
    exact (dvd_mul_left b _).trans (Nat.dvd_of_mul_dvd_mul_left hΓ0 h1)
  have hbodd : ¬ 2 ∣ b := fun h2b =>
    hTs.2.2 (h2b.trans (Subgroup.relIndex_dvd_of_le_left H le_sup_right))
  have hb1 : b = 1 := by
    obtain ⟨j, -, hbj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hba
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hbj
    · exact absurd (hbj ▸ dvd_pow_self 2 hj0.ne') hbodd
  exact le_antisymm hKTH ((Subgroup.relIndex_eq_one).mp hb1)

end KeyDataG

end Setting4

end CFSG.Quasithin.H13.A6
