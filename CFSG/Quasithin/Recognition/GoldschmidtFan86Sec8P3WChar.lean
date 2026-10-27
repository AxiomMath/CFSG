module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2
public import CFSG.Quasithin.EmptyFaithful.S1422Sz

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Open CFSG.Quasithin

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_conjChar_spec {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) :
    ∃ ψ : MulAction.stabilizer G v →* (ZMod (Fan86.valence Γ v))ˣ,
      (∀ g : MulAction.stabilizer G v, (g : G) ∈ nbrStab Γ G v ↔
        ψ g = 1 ∧ ∃ a, Γ.Adj v a ∧ (g : G) • a = a) ∧ ψ ⟨x, hx⟩ = 1 ∧
      ∀ g : MulAction.stabilizer G v,
        (g : G) * x * (g : G)⁻¹ * (x ^ ((ψ g : (ZMod (Fan86.valence Γ v))ˣ) :
          ZMod (Fan86.valence Γ v)).val)⁻¹ ∈ nbrStab Γ G v := by
  have hp := F.valence_isPrime v
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  have := F.finite_neighborSet v
  let D : FrobPrime.Data (Γ.neighborSet v) (Fan86.valence Γ v) :=
    { Q := (F.localHom v).range
      σ := F.localHom v ⟨x, hx⟩
      σ_mem := MonoidHom.mem_range.2 ⟨_, rfl⟩
      card_eq := rfl
      orderOf_σ := F.orderOf_localHom hx hxo
      conj := FrobPrime.conj_pow_of_frobenius hp rfl (F.localHom v).range
        (F.localHom_frobenius v) (MonoidHom.mem_range.2 ⟨_, rfl⟩) (F.orderOf_localHom hx hxo) }
  refine ⟨D.conjChar.comp (F.localHom v).rangeRestrict, fun g => ⟨fun hK => ?_, ?_⟩, ?_,
    fun g => ?_⟩
  · have hker : F.localHom v g = 1 := MonoidHom.mem_ker.1 ((F.mem_ker_localHom v g).2 hK)
    have h1 : (F.localHom v).rangeRestrict g = 1 := Subtype.ext hker
    obtain ⟨a, ha⟩ := F.exists_adj v
    exact ⟨by rw [MonoidHom.comp_apply, h1, map_one], a, ha, hK a ha⟩
  · rintro ⟨h1, a, ha, h2⟩
    have h3 := D.eq_one_of_conjChar_eq_one (q := (F.localHom v).rangeRestrict g) h1
      (a := ⟨a, ha⟩) (Subtype.ext h2)
    exact (F.mem_ker_localHom v g).1 (MonoidHom.mem_ker.2 h3)
  · have : Fact (1 < Fan86.valence Γ v) := ⟨hp.one_lt⟩
    show D.conjChar ((F.localHom v).rangeRestrict ⟨x, hx⟩) = 1
    have hspec := D.conjChar_spec ((F.localHom v).rangeRestrict ⟨x, hx⟩)
    have h1 : D.σ ^ ((D.conjChar ((F.localHom v).rangeRestrict ⟨x, hx⟩) : (ZMod _)ˣ) :
        ZMod (Fan86.valence Γ v)).val = D.σ ^ (1 : ZMod (Fan86.valence Γ v)).val := by
      rw [← hspec, ZMod.val_one]
      change D.σ * D.σ * D.σ⁻¹ = D.σ ^ 1
      group
    exact Units.ext (D.eq_of_pow_val_eq h1)
  · show (g : G) * x * (g : G)⁻¹ * (x ^ ((D.conjChar ((F.localHom v).rangeRestrict g) :
      (ZMod (Fan86.valence Γ v))ˣ) : ZMod (Fan86.valence Γ v)).val)⁻¹ ∈ nbrStab Γ G v
    set m := ((D.conjChar ((F.localHom v).rangeRestrict g) : (ZMod (Fan86.valence Γ v))ˣ) :
      ZMod (Fan86.valence Γ v)).val with hm
    have hq := D.conjChar_spec ((F.localHom v).rangeRestrict g)
    have hmem : (g * ⟨x, hx⟩ * g⁻¹ * (⟨x, hx⟩ ^ m)⁻¹ : ↥(MulAction.stabilizer G v)) ∈
        (F.localHom v).ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, map_pow]
      have : F.localHom v g * F.localHom v ⟨x, hx⟩ * (F.localHom v g)⁻¹ =
          F.localHom v ⟨x, hx⟩ ^ m := hq
      rw [this, mul_inv_cancel]
    have := (F.mem_ker_localHom v _).1 hmem
    simpa using this

theorem nbrStab_subgroupOf_le_pCore (v : V) :
    (nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v) ≤
      Open.pCore 2 ↥(MulAction.stabilizer G v) := by
  have hnorm : ((nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (F.nbrStab_le_stabilizer v)]
    intro g hg
    have hg' : g • v = v := MulAction.mem_stabilizer_iff.1 hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => nbrStab_conj_mem F hg' hh, fun hh => ?_⟩
    have := nbrStab_conj_mem F (g := g⁻¹) (by rw [inv_smul_eq_iff]; exact hg'.symm) hh
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥((nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v)) :=
    (F.nbrStab_isPGroup v).of_equiv (Subgroup.subgroupOfEquivOfLe (F.nbrStab_le_stabilizer v)).symm
  exact CFSG.LieType.BorelTits.le_pCore 2 hnorm hp

theorem relIndex_edge_eq_four (h65 : Fan65 F) {α β : V} (hα : Fan86.valence Γ α = 5)
    (hαβ : Γ.Adj α β) :
    (nbrStab Γ G α).relIndex (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 4 := by
  obtain ⟨e⟩ := h65.2 α hα
  have h20 : (Open.pCore 2 ↥(MulAction.stabilizer G α)).index = 20 := by
    have : Nat.card (oTwoQuot ↥(MulAction.stabilizer G α)) = 20 := by
      rw [Nat.card_congr e.toEquiv, card_Sz_zero]
    exact this
  have hdvd : (Open.pCore 2 ↥(MulAction.stabilizer G α)).index ∣
      ((nbrStab Γ G α).subgroupOf (MulAction.stabilizer G α)).index :=
    Subgroup.index_dvd_of_le (F.nbrStab_subgroupOf_le_pCore α)
  have hE : (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex
      (MulAction.stabilizer G α) = 5 := by
    rw [Subgroup.inf_relIndex_left, F.relIndex_stabilizer_eq_valence hαβ le_rfl
      (fun u w hu hw => F.loc_trans α u w hu hw), hα]
  have hKE : nbrStab Γ G α ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := fun g hg =>
    ⟨F.nbrStab_le_stabilizer α hg, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg β hαβ)⟩
  have hmul := Subgroup.relIndex_mul_relIndex (nbrStab Γ G α)
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) (MulAction.stabilizer G α) hKE inf_le_left
  rw [hE] at hmul
  have hd : 20 ∣
      (nbrStab Γ G α).relIndex (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) * 5 := by
    rw [hmul]
    exact h20 ▸ hdvd
  have h4 := F.relIndex_nbrStab_mem_two_four hαβ
  rcases h4 with h | h
  · rw [h] at hd
    omega
  · exact h

theorem exists_edge_conj_two (h65 : Fan65 F) {α β : V} (hα : Fan86.valence Γ α = 5)
    (hαβ : Γ.Adj α β) {x : G} (hx : x ∈ MulAction.stabilizer G α)
    (hxo : orderOf x = Fan86.valence Γ α) :
    ∃ ψ : MulAction.stabilizer G α →* (ZMod (Fan86.valence Γ α))ˣ,
      (∀ g : MulAction.stabilizer G α, (g : G) ∈ nbrStab Γ G α ↔
        ψ g = 1 ∧ ∃ a, Γ.Adj α a ∧ (g : G) • a = a) ∧ ψ ⟨x, hx⟩ = 1 ∧
      (∀ g : MulAction.stabilizer G α,
        (g : G) * x * (g : G)⁻¹ * (x ^ ((ψ g : (ZMod (Fan86.valence Γ α))ˣ) :
          ZMod (Fan86.valence Γ α)).val)⁻¹ ∈ nbrStab Γ G α) ∧
      ∃ e : MulAction.stabilizer G α, (e : G) • β = β ∧
        ((ψ e : (ZMod (Fan86.valence Γ α))ˣ) : ZMod (Fan86.valence Γ α)).val = 2 := by
  obtain ⟨ψ, h1, h2, h3⟩ := F.exists_conjChar_spec hx hxo
  have hp := F.valence_isPrime α
  have : Fact (Fan86.valence Γ α).Prime := ⟨hp⟩
  refine ⟨ψ, h1, h2, h3, ?_⟩
  set E : Subgroup G := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β with hE
  let ψE : ↥E →* (ZMod (Fan86.valence Γ α))ˣ := ψ.comp (Subgroup.inclusion inf_le_left)
  have hker : ψE.ker = (nbrStab Γ G α).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      exact (h1 (Subgroup.inclusion inf_le_left e)).2 ⟨he, β, hαβ,
        MulAction.mem_stabilizer_iff.1 e.2.2⟩
    · intro he
      exact ((h1 (Subgroup.inclusion inf_le_left e)).1 he).1
  have hrange : Nat.card ψE.range = 4 := by
    rw [← Subgroup.index_ker, hker]
    exact F.relIndex_edge_eq_four h65 hα hαβ
  have htop : ψE.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hrange, Nat.card_eq_fintype_card, ZMod.card_units, hα]
  have hcop : Nat.Coprime 2 (Fan86.valence Γ α) := by
    rw [hα]
    norm_num
  have hu : ZMod.unitOfCoprime 2 hcop ∈ ψE.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨e, he⟩ := hu
  refine ⟨Subgroup.inclusion inf_le_left e, MulAction.mem_stabilizer_iff.1 e.2.2, ?_⟩
  have he' : ψ (Subgroup.inclusion inf_le_left e) = ZMod.unitOfCoprime 2 hcop := he
  rw [he', ZMod.coe_unitOfCoprime, ZMod.val_natCast, hα]

end FanTree

end CFSG.Quasithin.Fan86
