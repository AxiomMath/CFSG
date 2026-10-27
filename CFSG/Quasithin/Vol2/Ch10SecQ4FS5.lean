module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5

@[expose] def fixSub (σ : Equiv.Perm (Fin 5)) : Subgroup (Multiplicative ↥(evenWeight 5)) where
  carrier := {δ | pact σ ((Multiplicative.toAdd δ : evenWeight 5) : Fin 5 → ZMod 2) =
    ((Multiplicative.toAdd δ : evenWeight 5) : Fin 5 → ZMod 2)}
  mul_mem' := fun {a b} ha hb => by
    show pact σ (((Multiplicative.toAdd a : evenWeight 5) : Fin 5 → ZMod 2) +
      ((Multiplicative.toAdd b : evenWeight 5) : Fin 5 → ZMod 2)) = _ + _
    rw [pact_add, ha, hb]
  one_mem' := by
    show pact σ 0 = 0
    rfl
  inv_mem' := fun {a} ha => by
    show pact σ (-((Multiplicative.toAdd a : evenWeight 5) : Fin 5 → ZMod 2)) = -_
    funext i
    have h := congrFun ha i
    simp only [pact, Pi.neg_apply] at h ⊢
    rw [h]

theorem card_delta5 : Nat.card (Multiplicative ↥(evenWeight 5)) = 16 := by
  classical
  have hmem : ∀ x : Fin 5 → ZMod 2, x ∈ evenWeight 5 ↔ ∑ i, x i = 0 := fun _ => Iff.rfl
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr (Equiv.subtypeEquivRight hmem),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_fixSub_three {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card ↥(fixSub σ) = 4 := by
  classical
  let e : ↥(fixSub σ) ≃ {x : Fin 5 → ZMod 2 // x ∈ fixSet σ} :=
    { toFun := fun δ => ⟨((Multiplicative.toAdd (δ : Multiplicative ↥(evenWeight 5)) :
          evenWeight 5) : Fin 5 → ZMod 2),
        mem_fixSet.mpr ⟨(Multiplicative.toAdd (δ : Multiplicative ↥(evenWeight 5))).2, δ.2⟩⟩
      invFun := fun x => ⟨Multiplicative.ofAdd ⟨x.1, (mem_fixSet.mp x.2).1⟩,
        (mem_fixSet.mp x.2).2⟩
      left_inv := fun δ => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_fixSet_three σ h3 h1]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_blockZ (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (blockZ K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [blockZ_eq_lit]
  refine ⟨fun hz => CGT.PushingUpLit.conj_mem_blockZ hg hz, fun hz => ?_⟩
  have := CGT.PushingUpLit.conj_mem_blockZ (Subgroup.inv_mem _ hg) hz
  simpa [mul_assoc] using this

theorem relIndex_centralizer_blockU_le {K : Subgroup G} (hKs : IsShort2 K)
    (hKa : IsAltType K 5) {q : G} (hqK : q ∈ K) (hq3 : orderOf q = 3) :
    (Subgroup.centralizer ({q} : Set G)).relIndex (blockU K) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  obtain ⟨α, -, hαk, β, hβs, hβk, hβe⟩ := hKa
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hZC : blockZ K ≤ Subgroup.centralizer ({q} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 q hqK).symm
  have hUK : blockU K ≤ K :=
    hKs.2.2.1.1.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have hZ2 : IsPGroup 2 (blockZ K) := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le
    (hZU.trans (hKs.2.2.1.1.trans inf_le_left))
  have hqU : q ∈ Subgroup.normalizer (blockU K : Set G) := le_normalizer_blockU K hqK
  have hqZ : q ∈ Subgroup.normalizer (blockZ K : Set G) :=
    normalizer_le_normalizer_blockZ K (Subgroup.le_normalizer hqK)
  have hN : blockU K ⊓ Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.normalizer (blockZ K : Set G) := fun x hx =>
    normalizer_le_normalizer_blockZ K (Subgroup.le_normalizer (hUK hx.1))
  rw [relIndex_centralizer_eq_mul hZU hN, Subgroup.relIndex_eq_one.mpr hZC, one_mul]
  have hkerA : β.ker ≤ (blockZ K ⊔ blockU K ⊓ Subgroup.centralizer ({q} : Set G)).subgroupOf
      (blockU K) := by
    rw [hβk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (le_sup_left : blockZ K ≤ _) hx
  have hAidx : (blockZ K ⊔ blockU K ⊓ Subgroup.centralizer ({q} : Set G)).relIndex (blockU K) =
      (((blockZ K ⊔ blockU K ⊓ Subgroup.centralizer ({q} : Set G)).subgroupOf
        (blockU K)).map β).index := by
    rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ hβs,
      Subgroup.comap_map_eq_self hkerA]
  set σ : Equiv.Perm (Fin 5) := ((α ⟨q, hqK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
    with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← Subgroup.coe_pow, ← map_pow]
    have : (⟨q, hqK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hq3')
    rw [this, map_one, Subgroup.coe_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hk : (⟨q, hqK⟩ : ↥K) ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [hαk] at hk
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hk⟩
    have hqn : q ^ 2 ^ n = 1 := by
      simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : ↥K) : G)) hn
    have h3 := orderOf_dvd_of_pow_eq_one hqn
    rw [hq3] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hfix : fixSub σ ≤ ((blockZ K ⊔ blockU K ⊓ Subgroup.centralizer ({q} : Set G)).subgroupOf
      (blockU K)).map β := by
    intro δ hδ
    obtain ⟨u, rfl⟩ := hβs δ
    have hquU : q * (u : G) * q⁻¹ ∈ blockU K := (Subgroup.mem_normalizer_iff.mp hqU _).mp u.2
    have hβq : β ⟨q * u * q⁻¹, hquU⟩ = β u := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      have h1 := hβe ⟨q, hqK⟩ u ⟨q * u * q⁻¹, hquU⟩ rfl i
      rw [h1]
      exact congrFun hδ i
    have hy : q * (u : G) * q⁻¹ * (u : G)⁻¹ ∈ blockZ K := by
      have h1 : (⟨q * u * q⁻¹, hquU⟩ * u⁻¹ : ↥(blockU K)) ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hβq, mul_inv_cancel]
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      exact h1
    obtain ⟨n, hn, hnfix⟩ := exists_fixed_mul hq3' hZ2 hqZ hy
    have hnuU : n * (u : G) ∈ blockU K := (blockU K).mul_mem (hZU hn) u.2
    refine ⟨⟨n * u, hnuU⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · refine Subgroup.mem_sup_right ⟨hnuU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc n * (u : G) * q = q * (n * u) * q⁻¹ * q := by rw [hnfix]
        _ = q * (n * u) := by group
    · have hnk : (⟨n, hZU hn⟩ : ↥(blockU K)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact hn
      have e : (⟨n * u, hnuU⟩ : ↥(blockU K)) = ⟨n, hZU hn⟩ * u := rfl
      rw [e, map_mul, hnk, one_mul]
  have hidx : (fixSub σ).index = 4 := by
    have h := Subgroup.card_mul_index (fixSub σ)
    rw [card_fixSub_three hσ3 hσ1, card_delta5] at h
    omega
  rw [hAidx, ← hidx]
  exact Nat.le_of_dvd (by rw [hidx]; norm_num) (Subgroup.index_dvd_of_le hfix)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
