module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G]

namespace T4213N

omit [Finite G] in
private theorem isSylowTwoOf_map_hom' {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

omit [Finite G] in
theorem isSylowTwoOf_cjSub {S X : Subgroup G} (hS : IsSylowTwoOf S X) {a : G} (ha : a ∈ X) :
    IsSylowTwoOf (cjSub a S) X := by
  have hcj : cjSub a X = X := by
    ext x
    rw [mem_cjSub]
    constructor
    · intro hx
      have h1 := X.mul_mem (X.mul_mem ha hx) (X.inv_mem ha)
      simpa [mul_assoc] using h1
    · intro hx
      exact X.mul_mem (X.mul_mem (X.inv_mem ha) hx) ha
  refine ⟨?_, hS.2.1.map _, ?_⟩
  · rw [← hcj]
    exact Subgroup.map_mono hS.1
  · have h1 : (cjSub a S).relIndex (cjSub a X) = S.relIndex X :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj a).toMonoidHom) S X
        (MulEquiv.injective _)
    rw [hcj] at h1
    show ¬ 2 ∣ (cjSub a S).relIndex X
    rw [h1]
    exact hS.2.2

end T4213N

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem exists_sylow_acts :
    ∃ S : Subgroup G, IsSylowTwoOf S (perfectCore (L ⊓ H)) ∧
      (∀ s ∈ S, ∃ t ∈ T ⊓ L, ∀ v ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
        s * v * s⁻¹ = t * v * t⁻¹) ∧
      (∀ t ∈ T ⊓ L, ∃ s ∈ S, ∀ v ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
        t * v * t⁻¹ = s * v * s⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLHdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  have hLHL : LH ≤ L := (perfectCore_le _).trans inf_le_left
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := c.L_le_normalizer_V
  have hLHV : LH ≤ Subgroup.normalizer (V : Set G) := hLHL.trans hLV
  have hconjV : ∀ g ∈ L, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLV hg) v).mp hv
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_normal (isSylowTwoOf_of_le c.hyp421.sylow c.hyp421.T_le) c.hyp421.L_le
      c.normal
  obtain ⟨S₀, hS₀, -⟩ := exists_isSylowTwoOf_ge (P := ⊥) (H := LH) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨h, hhL, hle⟩ := exists_conj_le_of_isSylowTwoOf hTL (hS₀.1.trans hLHL) hS₀.2.1
  obtain ⟨a, haLH, hact⟩ := c.exists_act_L hhL
  have hact' : ∀ v ∈ V, h⁻¹ * v * h = a⁻¹ * v * a := by
    intro v hv
    have hw : a⁻¹ * v * a ∈ V := by
      have h1 := hconjV a⁻¹ (L.inv_mem (hLHL haLH)) v hv
      simpa using h1
    have h1 := hact _ hw
    have h2 : a * (a⁻¹ * v * a) * a⁻¹ = v := by group
    rw [h2] at h1
    calc h⁻¹ * v * h = h⁻¹ * (h * (a⁻¹ * v * a) * h⁻¹) * h := by rw [h1]
      _ = a⁻¹ * v * a := by group
  set S := cjSub a S₀ with hSdef
  have hS : IsSylowTwoOf S LH := T4213N.isSylowTwoOf_cjSub hS₀ haLH
  have hdir1 : ∀ s ∈ S, ∃ t ∈ T ⊓ L, ∀ v ∈ V, s * v * s⁻¹ = t * v * t⁻¹ := by
    intro s hs
    rw [hSdef, mem_cjSub] at hs
    set s₀ := a⁻¹ * s * a with hs₀
    have hss : s = a * s₀ * a⁻¹ := by rw [hs₀]; group
    refine ⟨h * s₀ * h⁻¹, hle (mem_cjSub.mpr (by simpa [mul_assoc] using hs)), fun v hv => ?_⟩
    have hs₀N : s₀ ∈ Subgroup.normalizer (V : Set G) := hLHV (hS₀.1 hs)
    have hw : s₀ * (h⁻¹ * v * h) * s₀⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hs₀N _).mp
        (by simpa using hconjV h⁻¹ (L.inv_mem hhL) v hv)
    have e1 := hact _ hw
    calc s * v * s⁻¹ = a * (s₀ * (a⁻¹ * v * a) * s₀⁻¹) * a⁻¹ := by rw [hss]; group
      _ = a * (s₀ * (h⁻¹ * v * h) * s₀⁻¹) * a⁻¹ := by rw [hact' v hv]
      _ = h * (s₀ * (h⁻¹ * v * h) * s₀⁻¹) * h⁻¹ := e1.symm
      _ = h * s₀ * h⁻¹ * v * (h * s₀ * h⁻¹)⁻¹ := by group
  refine ⟨S, hS, hdir1, ?_⟩
  let ρ : ↥L →* MulAut ↥V := (autOn L V).subtype.comp (T4213N.rhoAut hLV)
  let σ : ↥LH →* MulAut ↥V := (autOn LH V).subtype.comp (T4213N.rhoAut hLHV)
  have hρ : ∀ (l : ↥L) (v : ↥V), ((ρ l v : ↥V) : G) = l * v * (l : G)⁻¹ := fun l v =>
    T4213N.rhoAut_apply hLV l v
  have hσ : ∀ (x : ↥LH) (v : ↥V), ((σ x v : ↥V) : G) = x * v * (x : G)⁻¹ := fun x v =>
    T4213N.rhoAut_apply hLHV x v
  have hρσ : ∀ (l : ↥L) (x : ↥LH),
      (∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = x * v * (x : G)⁻¹) → ρ l = σ x := by
    intro l x hlx
    ext v
    rw [hρ, hσ]
    exact hlx v v.2
  have hrange : σ.range = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨⟨x, hLHL x.2⟩, hρσ _ _ fun v _ => rfl⟩
    · rintro _ ⟨l, rfl⟩
      obtain ⟨a', ha', hact''⟩ := c.exists_act_L l.2
      exact ⟨⟨a', ha'⟩, (hρσ l ⟨a', ha'⟩ hact'').symm⟩
  have hP' := T4213N.isSylowTwoOf_map_hom' hTL ρ
  have hS' := T4213N.isSylowTwoOf_map_hom' hS σ
  rw [hrange] at hS'
  have hS'P' : (S.subgroupOf LH).map σ ≤ ((T ⊓ L).subgroupOf L).map ρ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, htx⟩ := hdir1 x hx
    exact ⟨⟨t, ht.2⟩, ht, hρσ ⟨t, ht.2⟩ x fun v hv => (htx v hv).symm⟩
  have heq := IsSylowTwoOf.eq_of_le hS' hS'P' hP'.1 hP'.2.1
  intro t ht
  have h1 : ρ ⟨t, ht.2⟩ ∈ (S.subgroupOf LH).map σ := by
    rw [← heq]
    exact ⟨⟨t, ht.2⟩, ht, rfl⟩
  obtain ⟨x, hx, hxt⟩ := h1
  refine ⟨x, hx, fun v hv => ?_⟩
  have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hxt
  simp only [hρ, hσ] at h2
  exact h2.symm

end Conf4212

end CFSG.Quasithin.H13.Ch4
