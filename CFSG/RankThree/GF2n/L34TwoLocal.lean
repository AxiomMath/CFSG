module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.Assembly.Defs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Matrix
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LieType.BorelTits.SpecialLinear
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.Foundations

public section

namespace CFSG.RankThree.GF2n.L34

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.RankThree.GF2n

variable {K : Type} [Field K] [Finite K]

local notation "Γ" => StatedSL 3 K
local notation "V" => Fin 3 → K

noncomputable abbrev ρ : Γ →* Module.End K V := natRep (StatedSL 3 K)

omit [Finite K] in
theorem ρ_injective : Function.Injective (ρ (K := K)) := natRep_injective _

omit [Finite K] in
theorem ρ_mul_apply (g h : Γ) (v : V) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul, Module.End.mul_apply]

omit [Finite K] in
theorem ρ_apply_inv_apply (g : Γ) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← ρ_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]

@[expose] def fixSpace (R : Subgroup Γ) : Submodule K V where
  carrier := {v | ∀ g ∈ R, ρ g v = v}
  add_mem' := fun ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg]

@[expose] def stab (W : Submodule K V) : Subgroup Γ where
  carrier := {g | ∀ w ∈ W, ρ g w ∈ W ∧ ρ g⁻¹ w ∈ W}
  one_mem' := fun w hw => by simpa using hw
  mul_mem' := fun {g h} hg hh w hw => by
    refine ⟨?_, ?_⟩
    · rw [map_mul, Module.End.mul_apply]
      exact (hg _ (hh w hw).1).1
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact (hh _ (hg w hw).2).2
  inv_mem' := fun {g} hg w hw => ⟨(hg w hw).2, by rw [inv_inv]; exact (hg w hw).1⟩

@[expose] def unip (W : Submodule K V) : Subgroup Γ where
  carrier := {g | (∀ w ∈ W, ρ g w = w) ∧ ∀ v, ρ g v - v ∈ W}
  one_mem' := ⟨fun w _ => by simp, fun v => by simp⟩
  mul_mem' := fun {g h} hg hh => by
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hh.1 w hw, hg.1 w hw]
    · rw [map_mul, Module.End.mul_apply]
      have := W.add_mem (hg.2 (ρ h v)) (hh.2 v)
      rwa [sub_add_sub_cancel] at this
  inv_mem' := fun {g} hg => by
    have hgw : ∀ w ∈ W, ρ g⁻¹ w = w := fun w hw => by
      have h1 : ρ g⁻¹ (ρ g w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rwa [hg.1 w hw] at h1
    refine ⟨hgw, fun v => ?_⟩
    have h1 := hg.2 (ρ g⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
    have := W.neg_mem h1
    rwa [neg_sub] at this

variable [CharP K 2]

omit [Finite K] in
theorem isElemAbelian_unip (W : Submodule K V) : Assembly.IsElemAbelian 2 (unip W) := by
  have key : ∀ g ∈ unip W, ∀ h ∈ unip W, ∀ v, ρ (g * h) v = v + (ρ g v - v) + (ρ h v - v) := by
    intro g hg h hh v
    rw [map_mul, Module.End.mul_apply]
    have e : ρ h v = v + (ρ h v - v) := by abel
    have h2 : ρ g (ρ h v - v) = ρ h v - v := hg.1 _ (hh.2 v)
    calc ρ g (ρ h v) = ρ g (v + (ρ h v - v)) := by rw [← e]
      _ = ρ g v + (ρ h v - v) := by rw [map_add, h2]
      _ = v + (ρ g v - v) + (ρ h v - v) := by abel
  refine ⟨⟨⟨fun a b => Subtype.ext (ρ_injective (LinearMap.ext fun v => ?_))⟩⟩, fun g hg => ?_⟩
  · show ρ ((a : Γ) * (b : Γ)) v = ρ ((b : Γ) * (a : Γ)) v
    rw [key _ a.2 _ b.2, key _ b.2 _ a.2]
    abel
  · apply ρ_injective
    refine LinearMap.ext fun v => ?_
    rw [pow_two, key _ hg _ hg, map_one, Module.End.one_apply, add_assoc, ← two_smul ℕ,
      two_nsmul, CharTwo.add_self_eq_zero, add_zero]

omit [Finite K] [CharP K 2] in
theorem exists_transvection_mem_unip {W : Submodule K V} {x : V} (hx : x ∈ W)
    {φ : Module.Dual K V} (hφ : ∀ w ∈ W, φ w = 0) :
    ∃ t ∈ unip W, ∀ v, ρ t v = v + φ v • x := by
  obtain ⟨t, ht⟩ := containsTransvections_natRep_statedSL 3 K x φ (hφ x hx)
  refine ⟨t, ⟨fun w hw => by rw [ht, hφ w hw, zero_smul, add_zero], fun v => ?_⟩, ht⟩
  rw [ht, add_sub_cancel_left]
  exact W.smul_mem _ hx

omit [Finite K] [CharP K 2] in
theorem exists_transvection_mem_stab {W : Submodule K V} {x : V} {φ : Module.Dual K V}
    (hφx : φ x = 0) (hφ : ∀ w ∈ W, φ w = 0) :
    ∃ t ∈ stab W, ∀ v, ρ t v = v + φ v • x := by
  obtain ⟨t, ht⟩ := containsTransvections_natRep_statedSL 3 K x φ hφx
  have hfix : ∀ w ∈ W, ρ t w = w := fun w hw => by rw [ht, hφ w hw, zero_smul, add_zero]
  refine ⟨t, fun w hw => ⟨by rw [hfix w hw]; exact hw, ?_⟩, ht⟩
  have h1 : ρ t⁻¹ (ρ t w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hfix w hw] at h1
  rw [h1]
  exact hw

omit [Finite K] [CharP K 2] in
theorem exists_dual {W : Submodule K V} {v : V} (hv : v ∉ W) :
    ∃ φ : Module.Dual K V, φ v ≠ 0 ∧ ∀ w ∈ W, φ w = 0 := by
  obtain ⟨φ, hφv, hφW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  refine ⟨φ, hφv, fun w hw => ?_⟩
  have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
  rw [hφW] at this
  exact this

omit [Finite K] [CharP K 2] in
theorem fixSpace_unip {W : Submodule K V} (hW : W ≠ ⊥) : fixSpace (unip W) = W := by
  refine le_antisymm (fun v hv => ?_) (fun w hw g hg => hg.1 w hw)
  by_contra hvW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨φ, hφv, hφW⟩ := exists_dual hvW
  obtain ⟨t, ht, htv⟩ := exists_transvection_mem_unip hxW hφW
  have h1 := hv t ht
  rw [htv, add_eq_left, smul_eq_zero] at h1
  rcases h1 with h | h
  · exact hφv h
  · exact hx0 h

omit [Finite K] [CharP K 2] in
theorem unip_ne_bot {W : Submodule K V} (hW : W ≠ ⊥) (hWtop : W ≠ ⊤) : unip W ≠ ⊥ := by
  intro hbot
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ W := by
    by_contra h
    push Not at h
    exact hWtop (eq_top_iff.mpr fun v _ => h v)
  have := fixSpace_unip hW
  rw [hbot] at this
  apply hv
  rw [← this]
  intro g hg
  rw [Subgroup.mem_bot] at hg
  rw [hg, map_one, Module.End.one_apply]

omit [Finite K] [CharP K 2] in
theorem conj_mem_unip {W : Submodule K V} {g : Γ} (hg : g ∈ stab W) {u : Γ} (hu : u ∈ unip W) :
    g * u * g⁻¹ ∈ unip W := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [ρ_mul_apply, ρ_mul_apply, hu.1 _ (hg w hw).2, ρ_apply_inv_apply]
  · rw [ρ_mul_apply, ρ_mul_apply]
    have h1 := (hg _ (hu.2 (ρ g⁻¹ v))).1
    rwa [map_sub, ρ_apply_inv_apply] at h1

omit [Finite K] [CharP K 2] in
theorem normalizer_unip {W : Submodule K V} (hW : W ≠ ⊥) :
    Subgroup.normalizer (unip W : Set Γ) = stab W := by
  apply le_antisymm
  · have hfix : ∀ g ∈ Subgroup.normalizer (unip W : Set Γ), ∀ w ∈ W, ρ g w ∈ W := by
      intro g hg w hw
      rw [← fixSpace_unip hW]
      intro u hu
      have hu' : g⁻¹ * u * g ∈ unip W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
        rwa [inv_inv] at this
      have h1 := hu'.1 w hw
      rw [ρ_mul_apply, ρ_mul_apply] at h1
      calc ρ u (ρ g w) = ρ g (ρ g⁻¹ (ρ u (ρ g w))) := (ρ_apply_inv_apply g _).symm
        _ = ρ g w := by rw [h1]
    exact fun g hg w hw => ⟨hfix g hg w hw, hfix g⁻¹ (Subgroup.inv_mem _ hg) w hw⟩
  · intro g hg
    refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => conj_mem_unip hg hu, fun hu => ?_⟩
    have := conj_mem_unip ((stab W).inv_mem hg) hu
    rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at this

omit [Finite K] [CharP K 2] in
theorem normalizer_le_stab_fixSpace (R : Subgroup Γ) :
    Subgroup.normalizer (R : Set Γ) ≤ stab (fixSpace R) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set Γ), ∀ w ∈ fixSpace R, ρ g w ∈ fixSpace R := by
    intro g hg w hw r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) r).mp hr
      rwa [inv_inv] at this
    calc ρ r (ρ g w) = ρ g (ρ (g⁻¹ * r * g) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2
          group
      _ = ρ g w := by rw [hw _ hr']
  exact fun g hg w hw => ⟨key g hg w hw, key g⁻¹ (Subgroup.inv_mem _ hg) w hw⟩

theorem fixSpace_ne_bot_ne_top {R : Subgroup Γ} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    fixSpace R ≠ ⊥ ∧ fixSpace R ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun hbot => ?_, fun htop => hR ?_⟩
  · obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero (ρ (K := K)) 2 R hR2
    have : v ∈ fixSpace R := hv
    rw [hbot] at this
    exact hv0 this
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    apply ρ_injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ fixSpace R := htop ▸ Submodule.mem_top
    rw [this g hg, map_one, Module.End.one_apply]

omit [Finite K] [CharP K 2] in
theorem finrank_V : Module.finrank K V = 3 := Module.finrank_fin_fun K

theorem isElemAbelian_pCore_of_isMaximalTwoLocal {M : Subgroup Γ} (hM : IsMaximalTwoLocal M) :
    Assembly.IsElemAbelian 2 (inSubgroup (pCore 2) M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  obtain ⟨R, hR, hR2, hMR⟩ := hM.1
  have hRQ : R ≤ Q := Tim78.le_inSubgroup_pCore (hMR ▸ Subgroup.le_normalizer) (hMR ▸ le_refl _)
    hR2
  have hQne : Q ≠ ⊥ := fun h => hR (le_bot_iff.mp (h ▸ hRQ))
  have hMNQ : M = Subgroup.normalizer (Q : Set Γ) := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne hMQ hne) ⟨Q, hQne, hQ2, rfl⟩
  set W := fixSpace Q with hW
  obtain ⟨hWbot, hWtop⟩ := fixSpace_ne_bot_ne_top hQne hQ2
  have hMW : M ≤ stab W := hMNQ ▸ normalizer_le_stab_fixSpace Q
  have hU2 : IsPGroup 2 (unip W) := fun x => ⟨1, Subtype.ext (by
    simpa using (isElemAbelian_unip W).2 x x.2)⟩
  have hMS : stab W ≤ M := by
    have hMU : M ≤ Subgroup.normalizer (unip W : Set Γ) := by rw [normalizer_unip hWbot]; exact hMW
    have heq : M = Subgroup.normalizer (unip W : Set Γ) := by
      by_contra hne
      exact hM.2 _ (lt_of_le_of_ne hMU hne) ⟨unip W, unip_ne_bot hWbot hWtop, hU2, rfl⟩
    rw [heq, normalizer_unip hWbot]
  let W₂ : Submodule K V :=
    { carrier := {v | ∀ q ∈ Q, ρ q v - v ∈ W}
      add_mem' := fun {a b} ha hb q hq => by
        have := W.add_mem (ha q hq) (hb q hq)
        rwa [map_add, add_sub_add_comm]
      zero_mem' := fun q _ => by rw [map_zero, sub_zero]; exact W.zero_mem
      smul_mem' := fun c v hv q hq => by
        rw [map_smul, ← smul_sub]
        exact W.smul_mem c (hv q hq) }
  have hWW₂ : W ≤ W₂ := fun w hw q hq => by rw [hw q hq, sub_self]; exact W.zero_mem
  have hW₂ne : W₂ ≠ W := by
    intro heq
    have hQW : ∀ g ∈ Q, ∀ v ∈ W, ρ g v ∈ W := fun g hg v hv => by rw [hv g hg]; exact hv
    obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ∉ W := by
      by_contra h
      push Not at h
      exact hWtop (eq_top_iff.mpr fun v _ => h v)
    have : Nontrivial (V ⧸ W) := ⟨⟨0, Submodule.Quotient.mk v₀, fun h =>
      hv₀ ((Submodule.Quotient.mk_eq_zero W).mp h.symm)⟩⟩
    have : Finite (V ⧸ W) := Finite.of_surjective (Submodule.mkQ W) (Submodule.mkQ_surjective W)
    obtain ⟨vq, hvq0, hvq⟩ := exists_fixed_ne_zero (quotRep (ρ (K := K)) Q W hQW) 2 ⊤
      (hQ2.of_equiv (Subgroup.topEquiv).symm)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W vq
    apply hvq0
    rw [Submodule.Quotient.mk_eq_zero, ← heq]
    intro q hq
    have h1 := hvq ⟨q, hq⟩ (Subgroup.mem_top _)
    rw [quotRep_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at h1
    exact h1
  have hW₂inv : ∀ m ∈ M, ∀ v ∈ W₂, ρ m v ∈ W₂ := by
    intro m hm v hv q hq
    have hq' : m⁻¹ * q * m ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hm)) q).mp hq
      rwa [inv_inv] at this
    have h1 := (hMW hm _ (hv _ hq')).1
    have e : ρ q (ρ m v) - ρ m v = ρ m (ρ (m⁻¹ * q * m) v - v) := by
      rw [map_sub, ρ_mul_apply, ρ_mul_apply, ρ_apply_inv_apply]
    rw [e]
    exact h1
  have hW₂top : W₂ = ⊤ := by
    have hlt : W < W₂ := lt_of_le_of_ne hWW₂ (Ne.symm hW₂ne)
    have hfW : Module.finrank K W < Module.finrank K W₂ := Submodule.finrank_lt_finrank_of_lt hlt
    have hfW0 : 0 < Module.finrank K W :=
      Nat.pos_of_ne_zero fun h => hWbot (Submodule.finrank_eq_zero.mp h)
    have hf2 : Module.finrank K W₂ ≤ 3 := (Submodule.finrank_le W₂).trans_eq finrank_V
    by_contra hne
    have hf2' : Module.finrank K W₂ < 3 := (Submodule.finrank_lt hne).trans_eq finrank_V
    obtain ⟨y, hyW₂, hyW⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨φ, hφy, hφW⟩ := exists_dual hyW
    have hker : ¬ LinearMap.ker φ ≤ W₂ := by
      intro hle
      have hfk : Module.finrank K (LinearMap.ker φ) = 2 := by
        have h1 := LinearMap.finrank_range_add_finrank_ker φ
        have h2 : Module.finrank K (LinearMap.range φ) = 1 := by
          have hr : LinearMap.range φ = ⊤ := by
            refine LinearMap.range_eq_top.mpr fun c => ⟨(c / φ y) • y, ?_⟩
            rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hφy]
          rw [hr, finrank_top, Module.finrank_self]
        rw [finrank_V] at h1
        omega
      have heq : LinearMap.ker φ = W₂ := Submodule.eq_of_le_of_finrank_le hle (by omega)
      exact hφy (heq ▸ hyW₂ : y ∈ LinearMap.ker φ)
    obtain ⟨x, hxk, hxW₂⟩ := Set.not_subset.mp hker
    obtain ⟨t, htS, htv⟩ := exists_transvection_mem_stab (W := W) (x := x) (φ := φ) hxk hφW
    have h1 := hW₂inv t (hMS htS) y hyW₂
    rw [htv] at h1
    apply hxW₂
    have h2 : φ y • x ∈ W₂ := by
      have := W₂.sub_mem h1 hyW₂
      rwa [add_sub_cancel_left] at this
    have h3 := W₂.smul_mem (φ y)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hφy, one_smul] at h3
  have hQU : Q ≤ unip W := fun q hq =>
    ⟨fun w hw => hw q hq, fun v => (hW₂top ▸ Submodule.mem_top : v ∈ W₂) q hq⟩
  obtain ⟨hUc, hU2'⟩ := isElemAbelian_unip W
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hU2' x (hQU hx)⟩
  have := congrArg Subtype.val (hUc.is_comm.comm ⟨a, hQU a.2⟩ ⟨b, hQU b.2⟩)
  exact this

end CFSG.RankThree.GF2n.L34
