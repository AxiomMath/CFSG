module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Prod
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Edge

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace XSetup

variable {F : FanTree Γ G} {α β : V} {x : G} (S : XSetup F α β x)

include S

theorem eq_bot_of_normalized (L : LocalFacts F) {y : G} (hy : y ∈ MulAction.stabilizer G β)
    (hyo : orderOf y = pval Γ β) {K : Subgroup G} (hK : K ≤ nbrStab Γ G β)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    K = ⊥ := by
  refine F.eq_bot_of_locTrans (Subgroup.normalizer (K : Set G)) S.adj ?_ le_rfl ?_ ?_
  · intro u hu
    exact ⟨mem_nbrStab.1 (hK hu) α S.adj.symm, F.nbrStab_le_stabilizer β (hK hu)⟩
  · intro a b ha hb
    obtain ⟨i, hi⟩ := L.pow_smul_eq S.mem S.ord ha hb
    exact ⟨x ^ i, Subgroup.pow_mem _ hxK i, MulAction.mem_stabilizer_iff.1
      (Subgroup.pow_mem _ S.mem i), hi⟩
  · intro a b ha hb
    obtain ⟨j, hj⟩ := L.pow_smul_eq hy hyo ha hb
    exact ⟨y ^ j, Subgroup.pow_mem _ hyK j, MulAction.mem_stabilizer_iff.1
      (Subgroup.pow_mem _ hy j), hj⟩

end XSetup

theorem conj_mem_map_of_characteristic {E H : Subgroup G} (hEH : E ≤ H) (K : Subgroup ↥H)
    (hKE : K ≤ E.subgroupOf H) (hchar : (K.subgroupOf (E.subgroupOf H)).Characteristic) {y : G}
    (hy : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hy' : ∀ e ∈ E, y⁻¹ * e * y ∈ E) :
    ∀ u ∈ K.map H.subtype, y * u * y⁻¹ ∈ K.map H.subtype := by
  set P := E.subgroupOf H with hP
  let ψ : ↥P ≃* ↥P :=
    { toFun := fun p => ⟨⟨y⁻¹ * (p : G) * y, hEH (hy' _ p.2)⟩, hy' _ p.2⟩
      invFun := fun p => ⟨⟨y * (p : G) * y⁻¹, hEH (hy _ p.2)⟩, hy _ p.2⟩
      left_inv := fun p => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
      right_inv := fun p => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
      map_mul' := fun p q => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
  have hfix := Subgroup.characteristic_iff_comap_eq.1 hchar ψ
  rintro _ ⟨k, hk, rfl⟩
  have hkP : k ∈ P := hKE hk
  let q : ↥P := ⟨⟨y * (k : G) * y⁻¹, hEH (hy _ hkP)⟩, hy _ hkP⟩
  have hψq : ψ q = ⟨k, hkP⟩ := Subtype.ext (Subtype.ext (by simp [ψ, q, mul_assoc]))
  have hmem : ψ q ∈ K.subgroupOf P := by
    rw [hψq, Subgroup.mem_subgroupOf]
    exact hk
  have : q ∈ (K.subgroupOf P).comap ψ.toMonoidHom := hmem
  rw [hfix, Subgroup.mem_subgroupOf] at this
  exact ⟨_, this, rfl⟩

theorem mem_normalizer_map_of_normal {H : Subgroup G} (K : Subgroup ↥H) [K.Normal] {g : G}
    (hg : g ∈ H) : g ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g' : ↥H, ∀ u ∈ K.map H.subtype, (g' : G) * u * (g' : G)⁻¹ ∈ K.map H.subtype := by
    rintro g' _ ⟨k, hk, rfl⟩
    exact ⟨g' * k * g'⁻¹, Subgroup.Normal.conj_mem inferInstance k hk g', by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key ⟨g, hg⟩ u, fun hu => ?_⟩
  have := key ⟨g, hg⟩⁻¹ _ hu
  simpa [mul_assoc] using this

theorem conj_mem_zpowers_of_normal {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hn : (Subgroup.zpowers (⟨x, hx⟩ : ↥H)).Normal) {h : G} (hh : h ∈ H) :
    h * x * h⁻¹ ∈ Subgroup.zpowers x := by
  have := Subgroup.Normal.conj_mem hn ⟨x, hx⟩ (Subgroup.mem_zpowers _) ⟨h, hh⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

end CFSG.Quasithin.Fan86
