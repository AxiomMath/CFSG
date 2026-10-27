module

public import CFSG.Quasithin.H13.A6S13833l
public import CFSG.Quasithin.H13.A6S13833k

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section CoverLt3

variable (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L)
include h13315 hhat

theorem U2_cube (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    {x : G} (hxL2 : x ∈ S.L2) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) {v₀ : G}
    (hv₀ : v₀ ∈ S.V3) (hxv₀ : x * v₀ * x⁻¹ ∉ S.V3) :
    ∀ u ∈ S.U2, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ S.V2 := by
  have hxL : x ∈ L := S.L2_le_L hxL2
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
  have hxV2 : x ∈ Subgroup.normalizer (S.V2 : Set G) := S.L2_le_NV2 hxL2
  have hU2L := S.U2_le_UL h13315 hhat
  have hUab : ∀ a ∈ conjClosure (conjClosure S.V3 S.G1) L,
      ∀ b ∈ conjClosure (conjClosure S.V3 S.G1) L, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hV2U : S.V2 ≤ conjClosure (conjClosure S.V3 S.G1) L :=
    S.V2_le_V.trans (S.V_le_U2.trans hU2L)
  have hconjV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have hconjV2 : ∀ v ∈ S.V2, x * v * x⁻¹ ∈ S.V2 := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxV2 v).mp hv
  have hVc : ∀ v ∈ V, v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ S.V2 := by
    intro v hv
    have hst : StabW2 (S.frame.ρ ⟨x, hxV⟩) := S.stabW2_of_mem (x := ⟨x, hxV⟩) hxV2
    have h45 : (S.frame.ρ ⟨x, hxV⟩) ^ 45 = 1 := by
      refine pow_45_of_odd hm ?_
      rw [← map_pow]
      have : (⟨x, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ m = 1 :=
        Subtype.ext (by simpa using hxm)
      rw [this, map_one]
    have hmv : ¬ (∀ y : P6, InW4 y → InW3 y → InW3 (act4f (S.frame.ρ ⟨x, hxV⟩) y)) := by
      intro hall
      apply hxv₀
      obtain ⟨hv₀V, hv₀3⟩ := S.mem_pre.1 hv₀
      refine S.mem_pre.2 ⟨hconjV v₀ hv₀V, ?_⟩
      have e : S.frame.ψ ⟨x * v₀ * x⁻¹, hconjV v₀ hv₀V⟩ =
          act4 (S.frame.ρ ⟨x, hxV⟩) (S.frame.ψ ⟨v₀, hv₀V⟩) := S.psi_conj ⟨x, hxV⟩ ⟨v₀, hv₀V⟩
      show InW3 ((S.frame.ψ ⟨x * v₀ * x⁻¹, hconjV v₀ hv₀V⟩ : ↥W4) : P6)
      rw [e]
      exact hall _ (S.frame.ψ ⟨v₀, hv₀V⟩).2 hv₀3
    have key := cube_W2 _ hst h45 hmv _ (S.frame.ψ ⟨v, hv⟩).2
    have hv1 := hconjV v hv
    have hv2 := hconjV _ hv1
    have hmem : v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ V :=
      V.mul_mem (V.mul_mem hv hv1) hv2
    refine S.mem_V2_of (v := ⟨_, hmem⟩) ?_
    have e : (⟨_, hmem⟩ : ↥V) = ⟨v, hv⟩ * ⟨_, hv1⟩ * ⟨_, hv2⟩ := rfl
    have e1 : S.frame.ψ ⟨x * v * x⁻¹, hv1⟩ =
        act4 (S.frame.ρ ⟨x, hxV⟩) (S.frame.ψ ⟨v, hv⟩) := S.psi_conj ⟨x, hxV⟩ ⟨v, hv⟩
    have e2 : S.frame.ψ ⟨x * (x * v * x⁻¹) * x⁻¹, hv2⟩ =
        act4 (S.frame.ρ ⟨x, hxV⟩) (S.frame.ψ ⟨x * v * x⁻¹, hv1⟩) :=
      S.psi_conj ⟨x, hxV⟩ ⟨_, hv1⟩
    rw [e, map_mul, map_mul, e2, e1]
    exact key
  have hcV2 : ∀ c ∈ L, c ∈ Subgroup.centralizer (S.V2 : Set G) →
      ∀ v ∈ V, v * (c * v * c⁻¹)⁻¹ ∈ S.V2 := by
    intro c hcL hcC v hv
    have hcV : c ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hcL
    have hfix : ∀ y : P6, InW2 y → act4f (S.frame.ρ ⟨c, hcV⟩) y = y := by
      intro y hy
      obtain ⟨w, hw⟩ := S.frame.ψ.surjective ⟨y, inW4_of_inW2 y hy⟩
      have hw2 : (w : G) ∈ S.V2 := S.mem_V2_of (v := w) (by rw [hw]; exact hy)
      have hcw : c * (w : G) * c⁻¹ = w := by
        have h1 := Subgroup.mem_centralizer_iff.mp hcC _ hw2
        calc c * (w : G) * c⁻¹ = (w : G) * c * c⁻¹ := by rw [h1]
          _ = w := by group
      have h2 := (S.conj_eq_iff ⟨c, hcV⟩ w).1 hcw
      rw [hw] at h2
      exact congrArg Subtype.val h2
    have ht := trivModW2_of_fix _ hfix _ (S.frame.ψ ⟨v, hv⟩).2
    have hcv : c * v * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcV v).mp hv
    have hmem : v * (c * v * c⁻¹)⁻¹ ∈ V := V.mul_mem hv (V.inv_mem hcv)
    refine S.mem_V2_of (v := ⟨_, hmem⟩) ?_
    have e : (⟨_, hmem⟩ : ↥V) = ⟨v, hv⟩ * (⟨_, hcv⟩)⁻¹ := rfl
    have e1 : S.frame.ψ ⟨c * v * c⁻¹, hcv⟩ =
        act4 (S.frame.ρ ⟨c, hcV⟩) (S.frame.ψ ⟨v, hv⟩) := S.psi_conj ⟨c, hcV⟩ ⟨v, hv⟩
    rw [e, map_mul, map_inv, e1]
    exact ht
  have hkey : ∀ k ∈ S.K2, ∀ v ∈ V, ∃ n ∈ S.V2,
      x * (k * v * k⁻¹) * x⁻¹ = n * (k * (x * v * x⁻¹) * k⁻¹) := by
    intro k hk v hv
    have hkN2 : k ∈ Subgroup.normalizer (S.L2 : Set G) :=
      S.normalizer_V2_le_normalizer_L2 h13315 hhat (S.K2_le_normalizer_V2 hk)
    have hxK : x⁻¹ ∈ Subgroup.normalizer (S.K2 : Set G) :=
      S.normalizer_V2_le_normalizer_K2 (S.L2_le_NV2 (S.L2.inv_mem hxL2))
    have hcL : x⁻¹ * (k⁻¹ * x * k) ∈ L := by
      have h1 : k⁻¹ * x * k ∈ S.L2 := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN2) x).mp hxL2
        simpa using this
      exact L.mul_mem (L.inv_mem hxL) (S.L2_le_L h1)
    have hcK : x⁻¹ * (k⁻¹ * x * k) ∈ S.K2 := by
      have h1 : x⁻¹ * k⁻¹ * x ∈ S.K2 := by
        have := (Subgroup.mem_normalizer_iff.mp hxK k⁻¹).mp (S.K2.inv_mem hk)
        simpa using this
      have e : x⁻¹ * (k⁻¹ * x * k) = (x⁻¹ * k⁻¹ * x) * k := by group
      rw [e]
      exact S.K2.mul_mem h1 hk
    have h0 := hcV2 _ hcL (S.K2_le_centralizer hcK) v hv
    obtain ⟨n₀, hn₀e⟩ : ∃ n₀ : G,
        n₀ = (x⁻¹ * (k⁻¹ * x * k)) * v * (x⁻¹ * (k⁻¹ * x * k))⁻¹ * v⁻¹ := ⟨_, rfl⟩
    have hn₀ : n₀ ∈ S.V2 := by
      have := S.V2.inv_mem h0
      have e : (v * ((x⁻¹ * (k⁻¹ * x * k)) * v * (x⁻¹ * (k⁻¹ * x * k))⁻¹)⁻¹)⁻¹ = n₀ := by
        rw [hn₀e]; group
      rwa [e] at this
    have hn := hconjV2 _ hn₀
    refine ⟨x * n₀ * x⁻¹, hn, ?_⟩
    have hkfix : k * (x * n₀ * x⁻¹) * k⁻¹ = x * n₀ * x⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.mp (S.K2_le_centralizer hk) _ hn
      calc k * (x * n₀ * x⁻¹) * k⁻¹ = (x * n₀ * x⁻¹) * k * k⁻¹ := by rw [h1]
        _ = x * n₀ * x⁻¹ := by group
    calc x * (k * v * k⁻¹) * x⁻¹ = k * (x * (n₀ * v) * x⁻¹) * k⁻¹ := by rw [hn₀e]; group
      _ = (k * (x * n₀ * x⁻¹) * k⁻¹) * (k * (x * v * x⁻¹) * k⁻¹) := by group
      _ = (x * n₀ * x⁻¹) * (k * (x * v * x⁻¹) * k⁻¹) := by rw [hkfix]
  have hmemUL : ∀ k ∈ S.K2, ∀ w ∈ V, k * w * k⁻¹ ∈ conjClosure (conjClosure S.V3 S.G1) L :=
    fun k hk w hw => hU2L ((HypF91.conjSub_le_conjClosure (Z := V) hk) (mul_mem_conjSub hw))
  have hgen : ∀ k ∈ S.K2, ∀ v ∈ V,
      (k * v * k⁻¹) * (x * (k * v * k⁻¹) * x⁻¹) * (x * (x * (k * v * k⁻¹) * x⁻¹) * x⁻¹) ∈
        S.V2 := by
    intro k hk v hv
    have hv1 := hconjV v hv
    have hv2 := hconjV _ hv1
    obtain ⟨n₁, hn₁, e1⟩ := hkey k hk v hv
    obtain ⟨n₂, hn₂, e2⟩ := hkey k hk _ hv1
    have e3 : x * (x * (k * v * k⁻¹) * x⁻¹) * x⁻¹ =
        (x * n₁ * x⁻¹) * (n₂ * (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹)) := by
      rw [e1, show x * (n₁ * (k * (x * v * x⁻¹) * k⁻¹)) * x⁻¹ =
        (x * n₁ * x⁻¹) * (x * (k * (x * v * x⁻¹) * k⁻¹) * x⁻¹) by group, e2]
    rw [e3, e1]
    have hn₁' := hconjV2 _ hn₁
    have hN : n₁ * (x * n₁ * x⁻¹) * n₂ ∈ S.V2 := S.V2.mul_mem (S.V2.mul_mem hn₁ hn₁') hn₂
    have h1 := hUab _ (hV2U hn₁) _ (hmemUL k hk _ hv1)
    have h2 := hUab _ (hV2U hN) _ (hmemUL k hk _ hv2)
    have e4 : (k * v * k⁻¹) * (n₁ * (k * (x * v * x⁻¹) * k⁻¹)) *
        ((x * n₁ * x⁻¹) * (n₂ * (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹))) =
        (k * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * k⁻¹) *
          (n₁ * (x * n₁ * x⁻¹) * n₂) := by
      calc (k * v * k⁻¹) * (n₁ * (k * (x * v * x⁻¹) * k⁻¹)) *
            ((x * n₁ * x⁻¹) * (n₂ * (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹))) =
            (k * v * k⁻¹) * (n₁ * (k * (x * v * x⁻¹) * k⁻¹)) * (x * n₁ * x⁻¹) * n₂ *
              (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹) := by group
        _ = (k * v * k⁻¹) * ((k * (x * v * x⁻¹) * k⁻¹) * n₁) * (x * n₁ * x⁻¹) * n₂ *
              (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹) := by rw [h1]
        _ = (k * v * k⁻¹) * (k * (x * v * x⁻¹) * k⁻¹) *
              ((n₁ * (x * n₁ * x⁻¹) * n₂) * (k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹)) := by
            group
        _ = (k * v * k⁻¹) * (k * (x * v * x⁻¹) * k⁻¹) *
              ((k * (x * (x * v * x⁻¹) * x⁻¹) * k⁻¹) * (n₁ * (x * n₁ * x⁻¹) * n₂)) := by
            rw [h2]
        _ = (k * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * k⁻¹) *
              (n₁ * (x * n₁ * x⁻¹) * n₂) := by group
    rw [e4]
    refine S.V2.mul_mem ?_ hN
    have hv3 := hVc v hv
    have hkfix : k * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * k⁻¹ =
        v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) := by
      have h1 := Subgroup.mem_centralizer_iff.mp (S.K2_le_centralizer hk) _ hv3
      calc k * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * k⁻¹ =
          (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * k * k⁻¹ := by rw [h1]
        _ = v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) := by group
    rw [hkfix]
    exact hv3
  have hU2N : ∀ u ∈ S.U2, x * u * x⁻¹ ∈ S.U2 := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (S.normalizes_U2 hxV2 hxV) u).mp hu
  let P : Subgroup G :=
    { carrier := {u | u ∈ S.U2 ∧ u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ S.V2}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨S.U2.mul_mem ha hb, ?_⟩
        have e : (a * b) * (x * (a * b) * x⁻¹) * (x * (x * (a * b) * x⁻¹) * x⁻¹) =
            a * b * ((x * a * x⁻¹) * (x * b * x⁻¹)) *
              ((x * (x * a * x⁻¹) * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹)) := by group
        rw [e, mul_rearrange6 hUab (hU2L hb) (hU2L (hU2N a ha)) (hU2L (hU2N b hb))
          (hU2L (hU2N _ (hU2N a ha)))]
        exact S.V2.mul_mem ha' hb'
      one_mem' := ⟨S.U2.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        have hinv : a⁻¹ = a := by
          have h2 := isElemAbelian_pow_eq_one hUL (hU2L ha)
          rw [pow_two] at h2
          exact inv_eq_of_mul_eq_one_right h2
        refine ⟨S.U2.inv_mem ha, ?_⟩
        rw [hinv]
        exact ha' }
  have hle : S.U2 ≤ P := conjClosure_le fun k hk v hv =>
    ⟨(HypF91.conjSub_le_conjClosure (Z := V) hk) (mul_mem_conjSub hv), hgen k hk v hv⟩
  exact fun u hu => (hle hu).2

end CoverLt3

end Setting4


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section CoverLt4

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
  (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L)
  (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
  {W : Subgroup G} (hUW : S.U0c β ≤ W) (hWU : W < conjClosure (conjClosure S.V3 S.G1) L)
  (hLW : L ≤ Subgroup.normalizer (W : Set G))

include hβs hβk hβe hρ' hN' honto' hUL hUW hWU hLW in
theorem card_U2_sup_W_le {x : G} (hxL2 : x ∈ S.L2) {v₀ : G} (hv₀ : v₀ ∈ S.V3)
    (hxv₀ : x * v₀ * x⁻¹ ∉ S.V3) :
    Nat.card ↥(S.U2 ⊔ W) ≤ 4 * Nat.card W := by
  have hUab : ∀ a ∈ conjClosure (conjClosure S.V3 S.G1) L,
      ∀ b ∈ conjClosure (conjClosure S.V3 S.G1) L, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hWle : W ≤ conjClosure (conjClosure S.V3 S.G1) L := hWU.le
  have hDUL : S.UHperp β ≤ conjClosure (conjClosure S.V3 S.G1) L :=
    S.UHperp_le_UH.trans (le_conjClosure _ L)
  have hU1W : S.U1c β ≤ W := (le_conjClosure (S.U1c β) L).trans hUW
  have hVW : V ≤ W := (S.V_le_U0c hβk).trans hUW
  have hA : Nat.card ↥(S.UHperp β ⊔ W) ≤ 2 * Nat.card W := by
    have hDN : S.UHperp β ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWle hw) a (hDUL ha))
    have h := card_sup_mul_card_inf' hDN
    have hle16 : 16 ≤ Nat.card ↥(S.UHperp β ⊓ W) := by
      rw [← S.card_V3_sup_U1c hβs hβk hβe hρ' hN' honto']
      exact Subgroup.card_le_of_le (le_inf (sup_le (S.V3_le_UHperp hβk hβe hρ' hN' honto')
        S.U1c_le_UHperp) (sup_le (S.V3_le_V.trans hVW) hU1W))
    have hD32 := S.card_UHperp_le hβs hβk hβe hρ' hN' honto'
    have h1 : Nat.card ↥(S.UHperp β ⊔ W) * 16 ≤
        Nat.card ↥(S.UHperp β ⊔ W) * Nat.card ↥(S.UHperp β ⊓ W) := Nat.mul_le_mul_left _ hle16
    have h2 : Nat.card (S.UHperp β) * Nat.card W ≤ 32 * Nat.card W := Nat.mul_le_mul_right _ hD32
    omega
  have hxL : x ∈ L := S.L2_le_L hxL2
  have hWx : conjSub x W = W := F7.conjSub_eq_of_mem_normalizer (hLW hxL)
  have hULx : conjSub x (conjClosure (conjClosure S.V3 S.G1) L) =
      conjClosure (conjClosure S.V3 S.G1) L :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure _ L hxL)
  have hAUL : S.UHperp β ⊔ W ≤ conjClosure (conjClosure S.V3 S.G1) L := sup_le hDUL hWle
  have hBUL : conjSub x (S.UHperp β ⊔ W) ≤ conjClosure (conjClosure S.V3 S.G1) L :=
    (conjSub_mono x hAUL).trans hULx.le
  have hWB : W ≤ conjSub x (S.UHperp β ⊔ W) := hWx.symm.le.trans (conjSub_mono x le_sup_right)
  have hAB : S.UHperp β ⊔ W ≤ Subgroup.normalizer (conjSub x (S.UHperp β ⊔ W) : Set G) :=
    fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => hUab b (hBUL hb) a (hAUL ha))
  have hprod := card_sup_mul_le hAB le_sup_right hWB
  rw [CosetGeom.card_conjSub] at hprod
  have hW0 : 0 < Nat.card W := Nat.card_pos
  have hsup : Nat.card ↥((S.UHperp β ⊔ W) ⊔ conjSub x (S.UHperp β ⊔ W)) ≤ 4 * Nat.card W := by
    have h3 : Nat.card ↥(S.UHperp β ⊔ W) * Nat.card ↥(S.UHperp β ⊔ W) ≤
        (2 * Nat.card W) * (2 * Nat.card W) := Nat.mul_le_mul hA hA
    have h4 : Nat.card ↥((S.UHperp β ⊔ W) ⊔ conjSub x (S.UHperp β ⊔ W)) * Nat.card W ≤
        (4 * Nat.card W) * Nat.card W := by
      calc _ ≤ Nat.card ↥(S.UHperp β ⊔ W) * Nat.card ↥(S.UHperp β ⊔ W) := hprod
        _ ≤ (2 * Nat.card W) * (2 * Nat.card W) := h3
        _ = (4 * Nat.card W) * Nat.card W := by ring
    exact Nat.le_of_mul_le_mul_right h4 hW0
  have hD21 := S.U21_le_UHperp hβk hβe hρ' hN' honto'
  have hU2 : S.U2 ⊔ W ≤ (S.UHperp β ⊔ W) ⊔ conjSub x (S.UHperp β ⊔ W) :=
    sup_le ((S.U2_le_sup hxL2 hv₀ hxv₀).trans (sup_le_sup (hD21.trans le_sup_left)
      (conjSub_mono x (hD21.trans le_sup_left)))) (le_sup_right.trans le_sup_left)
  exact (Subgroup.card_le_of_le hU2).trans hsup

include hβs hβk hβe hρ' hN' honto' hUW in
theorem U2_not_le_W (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ)
    (hUHW : Nat.card ↥(conjClosure S.V3 S.G1 ⊓ W) = 16) : ¬ S.U2 ≤ W := by
  intro hU2W
  obtain ⟨k, hk, hwU, hnL, hw4⟩ := S.exists_K2_moves_cover hβk hβe hρ' hN' honto' honto
  have hU1W : S.U1c β ≤ W := (le_conjClosure (S.U1c β) L).trans hUW
  have hVW : V ≤ W := (S.V_le_U0c hβk).trans hUW
  have hle : S.V3 ⊔ S.U1c β ≤ conjClosure S.V3 S.G1 ⊓ W :=
    sup_le (le_inf S.V3_le_UH (S.V3_le_V.trans hVW)) (le_inf S.U1c_le_UH hU1W)
  have heq : conjClosure S.V3 S.G1 ⊓ W = S.V3 ⊔ S.U1c β :=
    (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hUHW, S.card_V3_sup_U1c hβs hβk hβe hρ' hN' honto'])).symm
  have hwW : k * S.u2 * k⁻¹ ∈ conjClosure S.V3 S.G1 ⊓ W :=
    ⟨hwU, hU2W (S.U21_le_U2 ((HypF91.conjSub_le_conjClosure (Z := S.V3) hk)
      (mul_mem_conjSub S.u2_mem_V3)))⟩
  rw [heq] at hwW
  obtain ⟨hw', hln⟩ := (S.mem_UHline).1 (S.V3_sup_U1c_le_UHline hβk hwW)
  obtain ⟨wa, wb, wab⟩ := S.cover_weights hβk hβe hρ' hN' honto'
  exact hnL (inL_of_inLn_four wa wb wab hln hw4)

include hβs hβk hβe hρ' hN' honto' h13315 hhat hUL hUW hWU hLW in
theorem relIndex_U2_sup_W (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ)
    (hUHW : Nat.card ↥(conjClosure S.V3 S.G1 ⊓ W) = 16) : W.relIndex (S.U2 ⊔ W) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxL2, ⟨m, hm, hxm⟩, v₀, hv₀, hxv₀⟩ := S.exists_L2_not_NV3 h13315 hhat
  have hU2L := S.U2_le_UL h13315 hhat
  have hUab : ∀ a ∈ conjClosure (conjClosure S.V3 S.G1) L,
      ∀ b ∈ conjClosure (conjClosure S.V3 S.G1) L, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hU2N : S.U2 ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWU.le hw) a (hU2L ha))
  have h1 := relIndex_sup_mul_card_inf hU2N
  have h2 := Subgroup.relIndex_mul_card W (S.U2 ⊔ W)
  rw [inf_eq_left.2 le_sup_right] at h2
  have hle := S.card_U2_sup_W_le hβs hβk hβe hρ' hN' honto' hUL hUW hWU hLW hxL2 hv₀ hxv₀
  have hW0 : 0 < Nat.card W := Nat.card_pos
  have hr4 : W.relIndex (S.U2 ⊔ W) ≤ 4 := by
    have : W.relIndex (S.U2 ⊔ W) * Nat.card W ≤ 4 * Nat.card W := by rw [h2]; exact hle
    exact Nat.le_of_mul_le_mul_right this hW0
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
    ((isPGroup_of_isElemAbelian hUL).to_le hU2L)
  have hrd : W.relIndex (S.U2 ⊔ W) ∣ 2 ^ k := ⟨_, by rw [← hk, ← h1]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrd
  have hj2 : j ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hnot := S.U2_not_le_W hβs hβk hβe hρ' hN' honto' hUW honto hUHW
  interval_cases j
  ·
    exfalso
    rw [hj, pow_zero, one_mul] at h1
    exact hnot ((Subgroup.eq_of_le_of_card_ge inf_le_left h1.ge).symm.le.trans inf_le_right)
  ·
    exfalso
    have hX2 : (S.U2 ⊓ W).relIndex S.U2 = 2 := by
      have h3 := Subgroup.relIndex_mul_card (S.U2 ⊓ W) S.U2
      rw [inf_eq_left.2 (inf_le_left : S.U2 ⊓ W ≤ S.U2)] at h3
      rw [hj] at h1
      have hpos : 0 < Nat.card ↥(S.U2 ⊓ W) := Nat.card_pos
      have : (S.U2 ⊓ W).relIndex S.U2 * Nat.card ↥(S.U2 ⊓ W) =
          2 ^ 1 * Nat.card ↥(S.U2 ⊓ W) := by rw [h3, h1]
      have := Nat.eq_of_mul_eq_mul_right hpos this
      simpa using this
    have hxL : x ∈ L := S.L2_le_L hxL2
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
    have hxU2 : x ∈ Subgroup.normalizer (S.U2 : Set G) :=
      S.normalizes_U2 (S.L2_le_NV2 hxL2) hxV
    have hcube := S.U2_cube h13315 hhat hUL hxL2 hm hxm hv₀ hxv₀
    have hVW : V ≤ W := (S.V_le_U0c hβk).trans hUW
    have hV2X : S.V2 ≤ S.U2 ⊓ W := le_inf (S.V2_le_V.trans S.V_le_U2) (S.V2_le_V.trans hVW)
    refine false_of_relIndex_two_cube (x := x) (mem_normalizer_inf_two hxU2 (hLW hxL))
      (fun y hy => (Subgroup.mem_normalizer_iff.mp hxU2 y).mp hy) (fun y hy => ?_)
      (fun y hy => hV2X (hcube y hy)) hX2
    have h2' := isElemAbelian_pow_eq_one hUL (hU2L hy)
    rw [pow_two] at h2'
    rw [h2']
    exact Subgroup.one_mem _
  · rw [hj]; norm_num

end CoverLt4

end Setting4


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_coverLt (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (hhat : ¬ IsHatA6 L) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hG52 : StmtG52)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K)
    {ρ : ↥S.G1 →* Perm (Fin 6)} (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)} (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
    (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V))
    (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1)
    (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    (hLt : S.U0c β ≠ conjClosure (conjClosure S.V3 S.G1) L) : False := by
  have hL1H : S.L1 ≤ S.G1 := hL1K.trans (hKT ▸ le_sup_left)
  obtain ⟨τ, ρ', hρ', hN', hker', -, honto', -, -⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto (Or.inr ⟨β, hβs, hβk, hβe⟩)
  have honto₀ : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ := fun σ hσ =>
    (honto σ hσ).imp fun _ hk => hk.2
  have hcL1 : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hc3 : (S.cL1 hhat : G) ^ 3 = 1 := S.cL1_cube hhat
  have hcH : (S.cL1 hhat : G) ∈ S.G1 := hL1H hcL1
  have hc1 : (S.cL1 hhat : G) ≠ 1 := by
    intro h
    have h1 : S.cL1 hhat = 1 := Subtype.ext h
    have := S.cL1_rho hhat
    rw [h1, map_one] at this
    exact absurd this.symm (by decide)
  have hfp : ∀ i, ρ ⟨(S.cL1 hhat : G), hcH⟩ i ≠ i := by
    have hC3 : (⟨(S.cL1 hhat : G), hcH⟩ : ↥S.G1) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    have hC1 : (⟨(S.cL1 hhat : G), hcH⟩ : ↥S.G1) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hcl : ρ' ⟨(S.cL1 hhat : G), hcH⟩ ∈ cList :=
      (hN' _).2 (S.L1T_le_NV3 (Subgroup.mem_sup_left hcL1))
    have hc3' : ρ' ⟨(S.cL1 hhat : G), hcH⟩ ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
    have hc1' : ρ' ⟨(S.cL1 hhat : G), hcH⟩ ≠ 1 := S.rho_ne_one_of_cube hker' hC3 hC1
    have hfp' := cList_fpf _ hcl hc3' hc1'
    intro i hi
    apply hfp' (τ⁻¹ i)
    rw [hρ']
    simp [Perm.mul_apply, hi]
  have hUab : ∀ a ∈ conjClosure (conjClosure S.V3 S.G1) L,
      ∀ b ∈ conjClosure (conjClosure S.V3 S.G1) L, a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hYUL := S.LT_le_NUL
  obtain ⟨W, hUW, hWU, hWN, hmax⟩ :=
    exists_maximal_invariant (lt_of_le_of_ne S.U0c_le_UL hLt) (S.LT_le_normalizer_U0c hβe hβk)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hWN
  have hULN : conjClosure (conjClosure S.V3 S.G1) L ≤ Subgroup.normalizer (W : Set G) :=
    fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hUab w (hWU.le hw) a ha)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQW := comm_mem_of_maximal (pCoreOf_isPGroup 2 (L ⊔ T))
    (S.UL_le_Q hNS h13315 h1356two hG1 hF) hWU (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
    hYUL hWN hmax
  have hUHW := S.card_UH_inf_W hβs hβk hβe hρ' hN' honto' hUW hWU hLW hcH
    (S.L1_le_L hcL1) hc3 hfp
  have hUN : conjClosure S.V3 S.G1 ≤ Subgroup.normalizer (W : Set G) :=
    (le_conjClosure _ L).trans hULN
  have hW₁ := relIndex_sup_mul_card_inf hUN
  rw [hUHW, S.card_UH_cover hβs hβk] at hW₁
  have hW₂ := S.relIndex_U2_sup_W hβs hβk hβe hρ' hN' honto' h13315 hhat hUL hUW hWU hLW
    honto₀ hUHW
  have hU2L := S.U2_le_UL h13315 hhat
  obtain ⟨x, hxU, hx⟩ := S.exists_Uγ_swap45 h13315 hF s hDH hDγ htr
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hQT := S.pCoreOf_G1_le_T
  rw [hg1] at hQT
  have hxT : (x : G) ∈ T := hQT (S.Uγ_le_QH_case1 hF s hDγ hxU)
  have hA : conjSub (g : G) (fsuV1 T V) ≤ conjClosure (conjClosure S.V3 S.G1) L :=
    hA1.trans (le_conjClosure _ L)
  have h16 := S.relIndex_UL_inf_le hker hUL hA
  have hAP : conjSub (g : G) (fsuV1 T V) ≤
      conjClosure (conjClosure S.V3 S.G1) L ⊓ conjSub (g : G) (pCoreOf 2 S.G1) :=
    le_inf hA (conjSub_mono _ hF.toHypF91.V₁_le_pCoreOf)
  have hcard : Nat.card (conjSub (g : G) (fsuV1 T V)) = 2 := by
    rw [CosetGeom.card_conjSub, S.card_V1]
  have h32 := relIndex_centralizerMod_le hUab inf_le_left h16 hWU.le hcard hAP
    (fun u hu => S.comm_mem_A1 hF hxU hu.2)
  refine S.false_of_steinberg hhat hG52 hUL hWU hWN hmax hQW
    ⟨le_sup_right, sup_le (le_conjClosure _ L) hWU.le, by omega, fun y hyN hy => ?_⟩
    ⟨le_sup_right, sup_le hU2L hWU.le, hW₂, fun y hyN hy => ?_⟩ hxT hx
    (lt_of_le_of_lt h32 (by norm_num))
  · exact Subgroup.inf_normalizer_le_normalizer_sup _ W
      ⟨le_normalizer_conjClosure S.V3 S.G1 (S.mem_G1_of_g5G1 hy), hWN hyN⟩
  · exact Subgroup.inf_normalizer_le_normalizer_sup S.U2 W
      ⟨S.normalizes_U2 (S.mem_NV2_of_cA6 hy) y.2, hWN hyN⟩

end Setting4

theorem input13833CoverLt_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hG52 : StmtG52) : Input13833CoverLt := by
  intro G _ _ T L V S hNS _ hG1 _ hF hst hhat K _ hKT hL1K _ ρ hker hKA honto β hβs hβk
    hβe γ γ' g s hDγ hUL hLt
  obtain ⟨-, -, -, -, -, -, h3⟩ := hst
  obtain ⟨hDH, -, htr, -, hnQ⟩ := h3 γ γ' g s (Or.inl hDγ)
  have hn : ¬ F8.Uγ V S.G1 (g : G) ≤ ballStab 1 (F8.γ₁ T L S.G1) := fun h =>
    hnQ (h.trans (S.ballStab_γ₁_le_QH hF hKT hL1K ρ hker hKA honto
      (Or.inr ⟨β, hβs, hβk, hβe⟩)))
  obtain ⟨hA1, -⟩ := S.case1_symm hF s hn h3 hDH
  exact S.false_coverLt hNS h13315 hhat h1356two hG1 hF hG52 hKT hL1K hker hKA honto hβs hβk hβe
    s hDH hDγ htr hA1 hUL hLt

theorem input13833AbCover_holds (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (hG52 : StmtG52) : Input13833AbCover :=
  input13833AbCover_of h13315 (input13833CoverZH_of h13314)
    (input13833CoverLt_of h13315 h1356two hG52)

end CFSG.Quasithin.H13.A6
