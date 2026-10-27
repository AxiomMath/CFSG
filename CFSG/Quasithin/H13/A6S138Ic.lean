module

public import CFSG.Quasithin.H13.A6S138Ib

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem exists_rho {M : Type} [AddGroup M] (D : A6Nrm.Model M) {H K : Subgroup G}
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {β : ↥(conjClosure S.V3 H) →* Multiplicative M} (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 H)), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) = D.act (α k : Perm (Fin 6)) (Multiplicative.toAdd (β u))) :
    ∃ ρ : ↥H →* Perm (Fin 6), (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (∀ (h : ↥H) (hk : (h : G) ∈ K), ρ h = (α ⟨h, hk⟩ : Perm (Fin 6))) ∧
      ∀ (h : ↥H) (u v : ↥(conjClosure S.V3 H)), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (β v) = D.act (ρ h) (Multiplicative.toAdd (β u)) := by
  have hUN : ∀ h ∈ H, ∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ ∈ conjClosure S.V3 H :=
    fun h hh u hu => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) u).mp hu
  have hV1N : ∀ h ∈ H, ∀ v ∈ fsuV1 T V, h * v * h⁻¹ ∈ fsuV1 T V :=
    fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ hh) v).mp hv
  have hQN : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 H, h * q * h⁻¹ ∈ pCoreOf 2 H :=
    fun h hh q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) q).mp hq
  have hKN : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K :=
    fun h hh k hk => (Subgroup.mem_normalizer_iff.mp (hHK hh) k).mp hk
  have hβeq : ∀ u w : ↥(conjClosure S.V3 H), β u = β w ↔ (u : G) * (w : G)⁻¹ ∈ fsuV1 T V := by
    intro u w
    rw [show (u : G) * (w : G)⁻¹ = ((u * w⁻¹ : ↥(conjClosure S.V3 H)) : G) from rfl, ← hβk,
      map_mul, map_inv, mul_inv_eq_one]
  set P : ↥H → Perm (Fin 6) → Prop := fun h σ => ∀ u v : ↥(conjClosure S.V3 H),
    (v : G) = h * u * h⁻¹ → Multiplicative.toAdd (β v) = D.act σ (Multiplicative.toAdd (β u))
    with hP
  have uniq : ∀ h σ σ', P h σ → P h σ' → σ = σ' := by
    intro h σ σ' h1 h2
    have hall : ∀ m : M, D.act σ m = D.act σ' m := by
      intro m
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd m)
      have hm : m = Multiplicative.toAdd (β u) := by rw [hu]; rfl
      rw [hm, ← h1 u ⟨_, hUN h h.2 u u.2⟩ rfl, ← h2 u ⟨_, hUN h h.2 u u.2⟩ rfl]
    have h3 : σ⁻¹ * σ' = 1 := D.faithful _ fun m => by
      rw [D.act_mul, ← hall, ← D.act_mul, inv_mul_cancel, D.act_one]
    calc σ = σ * (σ⁻¹ * σ') := by rw [h3, mul_one]
      _ = σ' := by group
  have key : ∀ h : ↥H, ∃ σ, P h σ := by
    intro h
    let cU : ↥(conjClosure S.V3 H) →* ↥(conjClosure S.V3 H) :=
      { toFun := fun u => ⟨h * u * (h : G)⁻¹, hUN h h.2 u u.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let cK : ↥K →* ↥K :=
      { toFun := fun k => ⟨h * k * (h : G)⁻¹, hKN h h.2 k k.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let cK' : ↥K →* ↥K :=
      { toFun := fun k => ⟨(h : G)⁻¹ * k * (h : G)⁻¹⁻¹, hKN _ (H.inv_mem h.2) k k.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hcU : ∀ u : ↥(conjClosure S.V3 H), ((cU u : ↥(conjClosure S.V3 H)) : G) =
        h * u * (h : G)⁻¹ := fun _ => rfl
    have hcK : ∀ k : ↥K, ((cK k : ↥K) : G) = h * k * (h : G)⁻¹ := fun _ => rfl
    have hcKK' : ∀ k : ↥K, cK (cK' k) = k := fun k => Subtype.ext (by
      show (h : G) * ((h : G)⁻¹ * k * (h : G)⁻¹⁻¹) * (h : G)⁻¹ = k
      group)
    have hdepK : ∀ k k' : ↥K, α k = α k' → α (cK k) = α (cK k') := by
      intro k k' he
      have h1 : ((k'⁻¹ * k : ↥K) : G) ∈ pCoreOf 2 H := (hαk _).1 (by
        rw [map_mul, map_inv, he, inv_mul_cancel])
      have h2 : α (cK (k'⁻¹ * k)) = 1 := (hαk _).2 (by
        rw [hcK]
        exact hQN h h.2 _ h1)
      rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
    obtain ⟨ψ, hψα⟩ : ∃ ψ : A6Coc.Γ →* A6Coc.Γ, ∀ k : ↥K, ψ (α k) = α (cK k) := by
      refine ⟨MonoidHom.mk' (fun x => α (cK (Function.surjInv hαs x))) ?_,
        fun k => hdepK _ _ (Function.surjInv_eq hαs (α k))⟩
      intro x y
      obtain ⟨k, rfl⟩ := hαs x
      obtain ⟨k', rfl⟩ := hαs y
      have h1 := hdepK _ _ (Function.surjInv_eq hαs (α k))
      have h2 := hdepK _ _ (Function.surjInv_eq hαs (α k'))
      have h3 : α (cK (Function.surjInv hαs (α k * α k'))) = α (cK (k * k')) :=
        hdepK _ _ (by rw [Function.surjInv_eq hαs, map_mul])
      show α (cK (Function.surjInv hαs (α k * α k'))) =
        α (cK (Function.surjInv hαs (α k))) * α (cK (Function.surjInv hαs (α k')))
      rw [h1, h2, h3, map_mul, map_mul]
    have hψs : Function.Surjective ψ := by
      intro y
      obtain ⟨k, rfl⟩ := hαs y
      exact ⟨α (cK' k), by rw [hψα, hcKK']⟩
    have hdepU : ∀ u u' : ↥(conjClosure S.V3 H), β u = β u' → β (cU u) = β (cU u') := by
      intro u u' he
      rw [hβeq] at he ⊢
      rw [hcU, hcU]
      have e : (h : G) * u * (h : G)⁻¹ * ((h : G) * u' * (h : G)⁻¹)⁻¹ =
          (h : G) * ((u : G) * (u' : G)⁻¹) * (h : G)⁻¹ := by group
      rw [e]
      exact hV1N h h.2 _ he
    obtain ⟨φ, hφβ⟩ : ∃ φ : M →+ M, ∀ u : ↥(conjClosure S.V3 H),
        φ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (cU u)) := by
      let w : M → ↥(conjClosure S.V3 H) := fun y => Function.surjInv hβs (Multiplicative.ofAdd y)
      have hw : ∀ y, β (w y) = Multiplicative.ofAdd y := fun y => Function.surjInv_eq hβs _
      refine ⟨{ toFun := fun y => Multiplicative.toAdd (β (cU (w y))),
                map_zero' := ?_, map_add' := ?_ }, fun u => ?_⟩
      · have h1 : β (cU (w 0)) = β (cU 1) := hdepU _ _ (by rw [hw, map_one]; rfl)
        show Multiplicative.toAdd (β (cU (w 0))) = 0
        rw [h1, map_one, map_one]
        rfl
      · intro y y'
        have h1 : β (cU (w (y + y'))) = β (cU (w y * w y')) :=
          hdepU _ _ (by rw [hw, map_mul, hw, hw]; rfl)
        show Multiplicative.toAdd (β (cU (w (y + y')))) =
          Multiplicative.toAdd (β (cU (w y))) + Multiplicative.toAdd (β (cU (w y')))
        rw [h1, map_mul, map_mul, toAdd_mul]
      · show Multiplicative.toAdd (β (cU (w (Multiplicative.toAdd (β u))))) = _
        rw [hdepU _ u (by rw [hw, ofAdd_toAdd])]
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd y)
      have e1 : y = Multiplicative.toAdd (β u) := by rw [hu]; rfl
      rw [e1, hφβ] at hy
      have hy' : β (cU u) = 1 := Multiplicative.toAdd.injective hy
      rw [hβk, hcU] at hy'
      have h2 := hV1N _ (H.inv_mem h.2) _ hy'
      have e3 : (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) * (h : G)⁻¹⁻¹ = u := by group
      rw [e3] at h2
      rw [e1, (hβk u).2 h2]
      rfl
    have hφψ : ∀ (x : A6Coc.Γ) (m : M),
        φ (D.act (x : Perm (Fin 6)) m) = D.act (ψ x : Perm (Fin 6)) (φ m) := by
      intro x m
      obtain ⟨k, rfl⟩ := hαs x
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd m)
      have e1 : m = Multiplicative.toAdd (β u) := by rw [hu]; rfl
      have h1 := hβe k u ⟨_, hUN k (hKH k.2) u u.2⟩ rfl
      have h2 := hβe (cK k) (cU u) ⟨_, hUN _ (hKH (cK k).2) _ (cU u).2⟩ rfl
      have e2 : cU ⟨_, hUN k (hKH k.2) u u.2⟩ = ⟨_, hUN _ (hKH (cK k).2) _ (cU u).2⟩ :=
        Subtype.ext (by
          show (h : G) * ((k : G) * u * (k : G)⁻¹) * (h : G)⁻¹ =
            (h : G) * k * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) * ((h : G) * k * (h : G)⁻¹)⁻¹
          group)
      rw [e1, ← h1, hφβ, e2, h2, hψα, hφβ]
    obtain ⟨σ, hσ⟩ := D.nrm φ hφinj ψ hψs hφψ
    refine ⟨σ, fun u v huv => ?_⟩
    have e : v = cU u := Subtype.ext huv
    rw [e, ← hφβ, hσ]
  choose ρf hρf using key
  have hmul : ∀ h h' : ↥H, ρf (h * h') = ρf h * ρf h' := by
    intro h h'
    refine uniq _ _ _ (hρf (h * h')) fun u v huv => ?_
    set w : ↥(conjClosure S.V3 H) := ⟨h' * u * (h' : G)⁻¹, hUN h' h'.2 u u.2⟩ with hw
    have h1 := hρf h' u w rfl
    have h2 := hρf h w v (by
      rw [huv, hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group)
    rw [h2, h1, D.act_mul]
  let ρ : ↥H →* Perm (Fin 6) :=
    { toFun := ρf
      map_one' := uniq _ _ _ (hρf 1) fun u v huv => by
        have e : v = u := Subtype.ext (by rw [huv]; simp)
        rw [e, D.act_one]
      map_mul' := hmul }
  have hρ : ∀ h, ρ h = ρf h := fun _ => rfl
  refine ⟨ρ, fun h => ?_, fun h hk => ?_, fun h u v huv => by rw [hρ]; exact hρf h u v huv⟩
  · constructor
    · intro h1
      have hP1 := hρf h
      rw [← hρ, h1] at hP1
      rw [hF.pCoreOf_eq_centralizerMod]
      refine ⟨h.2, hF.H_normalizes_V₁ h.2, fun u hu => ?_⟩
      have := hP1 ⟨u, hu⟩ ⟨_, hUN h h.2 u hu⟩ rfl
      rw [D.act_one] at this
      have h2 : β ⟨_, hUN h h.2 u hu⟩ = β ⟨u, hu⟩ := Multiplicative.toAdd.injective this
      exact (hβeq _ _).1 h2
    · intro hq
      rw [hF.pCoreOf_eq_centralizerMod] at hq
      obtain ⟨-, -, hc⟩ := hq
      rw [hρ]
      refine (uniq _ _ _ (hρf h) fun u v huv => ?_).trans rfl
      rw [D.act_one]
      congr 1
      exact (hβeq v u).2 (by rw [huv]; exact hc u u.2)
  · rw [hρ]
    refine uniq _ _ _ (hρf h) fun u v huv => ?_
    exact hβe ⟨h, hk⟩ u v huv

end Setting4

end CFSG.Quasithin.H13.A6
