module

public import CFSG.Monster.GMS.Leech.TypeUniqueFiber
public import CFSG.Monster.GMS.Facts.LeechType
public import CFSG.Sporadic.Co1.Module.InvReps

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem exists_isCo1TwoB :
    ∃ s : Co1, IsCo1TwoB s := by
  obtain ⟨-, sB, -, -, hoB, -, -, hfB, -, -, hqB, -, -⟩ := CFSG.Sporadic.Co1.Module.rep_facts
  refine ⟨sB, hoB, hfB, fun v hv => ?_⟩
  have hfin : {v : CFSG.Sporadic.Co1.Module.Vec24 |
      CFSG.Sporadic.Co1.Module.co1Act sB v = v ∧ CFSG.Sporadic.Co1.Module.q₀ v = 1}.Finite :=
    Set.toFinite _
  have hempty := (Set.ncard_eq_zero hfin).1 hqB
  by_contra hne
  have h1 : CFSG.Sporadic.Co1.Module.q₀ v = 1 :=
    (CFSG.Sporadic.Co1.Module.zmod2_cases _).resolve_left hne
  have hmem : v ∈ {v : CFSG.Sporadic.Co1.Module.Vec24 |
      CFSG.Sporadic.Co1.Module.co1Act sB v = v ∧ CFSG.Sporadic.Co1.Module.q₀ v = 1} := ⟨hv, h1⟩
  rw [hempty] at hmem
  exact hmem

theorem IsCo1TwoB.ne_one {s : Co1} (hs : IsCo1TwoB s) : s ≠ 1 := fun h => by
  have h2 := hs.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

namespace TypeUnique

variable {H H' : Type} [Group H] [Group H'] {S : LeechTypeSystem H} {S' : LeechTypeSystem H'}

theorem exists_lift_sq_eq_z
    (S : LeechTypeSystem H)
    (h2B : ∀ t : H, orderOf t = 2 → ¬ IsCo1TwoB (S.φ t)) {s : Co1} (hs : IsCo1TwoB s) :
    ∃ x : H, S.φ x = s ∧ x * x = S.z := by
  obtain ⟨hord, -, hq0⟩ := id hs
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hord, pow_two] at h
    exact h
  have hs1 : s ≠ 1 := hs.ne_one
  obtain ⟨x0, hx0⟩ := S.φ_surj s
  have hx0sq : S.φ (x0 * x0) = 1 := by rw [map_mul, hx0, hss]
  have hu_fix : co1Act s (S.vec (x0 * x0)) = S.vec (x0 * x0) := by
    have h := S.vec_conj x0 (x0 * x0) hx0sq
    rw [hx0] at h
    have e : x0 * (x0 * x0) * x0⁻¹ = x0 * x0 := by group
    rw [e] at h
    exact h.symm
  have hu : ∀ v, co1Act s v = v → CFSG.Sporadic.Co1.Module.bil₀ (S.vec (x0 * x0)) v = 0 := by
    intro v hv
    have h1 := CFSG.Sporadic.Co1.Module.q₀_add (S.vec (x0 * x0)) v
    have hfix : co1Act s (S.vec (x0 * x0) + v) = S.vec (x0 * x0) + v := by
      rw [map_add, hu_fix, hv]
    have e1 : CFSG.Sporadic.Co1.Module.q₀ (S.vec (x0 * x0)) = 0 := hq0 _ hu_fix
    have e2 : CFSG.Sporadic.Co1.Module.q₀ v = 0 := hq0 _ hv
    have e3 : CFSG.Sporadic.Co1.Module.q₀ (S.vec (x0 * x0) + v) = 0 := hq0 _ hfix
    rw [e1, e2, e3] at h1
    simpa using h1.symm
  obtain ⟨w, hw⟩ := Leech.exists_add_eq_of_forall_bil₀_eq_zero hss hu
  obtain ⟨q, hq, hqw⟩ := S.vec_surj w
  have hφx : S.φ (x0 * q) = s := by rw [map_mul, hx0, hq, mul_one]
  refine ⟨x0 * q, hφx, ?_⟩
  have hxsq : S.φ (x0 * q * (x0 * q)) = 1 := by rw [map_mul, hφx, hss]
  have hA : S.φ (x0 * q * x0⁻¹) = 1 := by rw [map_mul, map_mul, hx0, hq, mul_one, map_inv, hx0,
    mul_inv_cancel]
  have hvec : S.vec (x0 * q * (x0 * q)) = 0 := by
    have e : x0 * q * (x0 * q) = (x0 * q * x0⁻¹ * (x0 * x0)) * q := by group
    have hAB : S.φ (x0 * q * x0⁻¹ * (x0 * x0)) = 1 := by rw [map_mul, hA, hx0sq, mul_one]
    rw [e, S.vec_mul _ _ hAB hq, S.vec_mul _ _ hA hx0sq, S.vec_conj x0 q hq, hx0, hqw,
      add_right_comm, hw]
    exact CFSG.Sporadic.Co1.Module.vec_add_self _
  rcases (S.vec_eq_zero _ hxsq).1 hvec with h | h
  · exfalso
    have hx1 : x0 * q ≠ 1 := fun h1 => hs1 (by rw [← hφx, h1, map_one])
    have hox : orderOf (x0 * q) = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hx1
    exact h2B _ hox (by rw [hφx]; exact hs)
  · exact h

namespace Glue

variable (G : Glue S S')

abbrev Δ' : Subgroup ↥G.P := G.Δ.subgroupOf G.P

instance Δ'_normal : G.Δ'.Normal :=
  (Subgroup.normal_subgroupOf_iff G.Δ_le_P).2 fun _ _ hh hk => G.conj_mem_Δ hk hh

abbrev Cover : Type := ↥G.P ⧸ G.Δ'

noncomputable def π : G.Cover →* Co1 :=
  QuotientGroup.lift G.Δ' ((S.φ.comp (MonoidHom.fst H H')).comp G.P.subtype) fun _ hx =>
    (mem_F.1 (G.mem_Δ.1 (Subgroup.mem_subgroupOf.1 hx)).1).1

def ζ : G.Cover := QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩

theorem π_surj
    [Finite H] [Finite H'] : Function.Surjective G.π := by
  intro s
  obtain ⟨x, rfl⟩ := S.φ_surj s
  obtain ⟨y, hy⟩ := G.exists_mem_P x
  exact ⟨QuotientGroup.mk ⟨(x, y), hy⟩, rfl⟩

theorem one_z_mem_P : ((1 : H), S'.z) ∈ G.P := by
  have e : ((1 : H), S'.z) = (S.z, (1 : H')) * (S.z, S'.z) := by simp [S.z_mul_self]
  rw [e]
  exact mul_mem G.z1_mem_P (G.Δ_le_P G.zz_mem_Δ)

theorem mk_one_z : (QuotientGroup.mk ⟨((1 : H), S'.z), G.one_z_mem_P⟩ : G.Cover) = G.ζ := by
  have e : (⟨((1 : H), S'.z), G.one_z_mem_P⟩ : ↥G.P) =
      ⟨(S.z, 1), G.z1_mem_P⟩ * ⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ := by
    apply Subtype.ext
    simp [S.z_mul_self]
  have h1 : (QuotientGroup.mk ⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ : G.Cover) = 1 :=
    (QuotientGroup.eq_one_iff (⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ : ↥G.P)).2
      (Subgroup.mem_subgroupOf.2 G.zz_mem_Δ)
  rw [e, QuotientGroup.mk_mul, h1, mul_one]
  rfl

theorem π_ζ : G.π G.ζ = 1 := S.φ_z

theorem π_ker : G.π.ker = Subgroup.zpowers G.ζ := by
  refine le_antisymm (fun c hc => ?_) (Subgroup.zpowers_le.2 G.π_ζ)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have h1 : S.φ (g : H × H').1 = 1 := hc
  have hgF := G.mem_F_of_mem_P g.2 h1
  rcases G.mem_Δ_or_z1_mul hgF with h | h
  · have : (QuotientGroup.mk g : G.Cover) = 1 :=
      (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_subgroupOf.2 h)
    rw [this]
    exact one_mem _
  · have h2 : (QuotientGroup.mk (⟨(S.z, 1), G.z1_mem_P⟩ * g) : G.Cover) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)
    rw [QuotientGroup.mk_mul] at h2
    have h3 : (QuotientGroup.mk g : G.Cover) = G.ζ⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [h3]
    exact inv_mem (Subgroup.mem_zpowers _)

theorem ζ_mem_center : G.ζ ∈ Subgroup.center G.Cover := by
  rw [Subgroup.mem_center_iff]
  intro c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  show (QuotientGroup.mk g : G.Cover) * QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ = _
  rw [← QuotientGroup.mk_mul]
  show _ = (QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ : G.Cover) * QuotientGroup.mk g
  rw [← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (z1_comm (g : H × H')).symm)

theorem ζ_orderOf : orderOf G.ζ = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have e : (⟨(S.z, 1), G.z1_mem_P⟩ * ⟨(S.z, 1), G.z1_mem_P⟩ : ↥G.P) = 1 :=
      Subtype.ext (by simp [S.z_mul_self])
    show (QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ : G.Cover) ^ 2 = 1
    rw [pow_two, ← QuotientGroup.mk_mul, e]
    rfl
  · intro h
    exact G.z1_not_mem_Δ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))

theorem exists_involution
    [Finite H] [Finite H']
    (h2B : ∀ t : H, orderOf t = 2 → ¬ IsCo1TwoB (S.φ t))
    (h2B' : ∀ t : H', orderOf t = 2 → ¬ IsCo1TwoB (S'.φ t)) {s : Co1} (hs : IsCo1TwoB s) :
    ∃ c : G.Cover, c * c = 1 ∧ G.π c = s := by
  obtain ⟨x, hxs, hxz⟩ := exists_lift_sq_eq_z S h2B hs
  obtain ⟨y, hy⟩ := G.exists_mem_P x
  have hyφ : S'.φ y = s := by
    have : S.φ x = S'.φ y := mem_P0.1 (G.P_le_P0 hy)
    rw [← this, hxs]
  have hsq : ((x, y) : H × H') * (x, y) = (S.z, y * y) := by rw [Prod.mk_mul_mk, hxz]
  have hsqP : (S.z, y * y) ∈ G.P := by
    rw [← hsq]
    exact mul_mem hy hy
  obtain ⟨-, hF2, hF3⟩ := mem_F.1 (G.mem_F_of_mem_P hsqP S.φ_z)
  have hvec : S'.vec (y * y) = 0 := by
    rw [← hF3]
    exact S.vec_z
  have hy2 : y * y = S'.z := by
    rcases (S'.vec_eq_zero (y * y) hF2).1 hvec with h | h
    · exfalso
      have hy1 : y ≠ 1 := fun h1 => hs.ne_one (by rw [← hyφ, h1, map_one])
      have hoy : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hy1
      exact h2B' y hoy (by rw [hyφ]; exact hs)
    · exact h
  refine ⟨QuotientGroup.mk ⟨(x, y), hy⟩, ?_, hxs⟩
  rw [← QuotientGroup.mk_mul]
  refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ?_)
  show ((x, y) : H × H') * (x, y) ∈ G.Δ
  rw [hsq, hy2]
  exact G.zz_mem_Δ

end Glue

theorem exists_mulEquiv
    [Finite H] [Finite H'] (hDC : Co1DoubleCoverTwoB) (G : Glue S S')
    (h2B : ∀ t : H, orderOf t = 2 → ¬ IsCo1TwoB (S.φ t))
    (h2B' : ∀ t : H', orderOf t = 2 → ¬ IsCo1TwoB (S'.φ t))
    (hcard : Nat.card H = Nat.card H') : Nonempty (H ≃* H') := by
  obtain ⟨s, hs⟩ := exists_isCo1TwoB
  obtain ⟨c, hc1, hcs⟩ := G.exists_involution h2B h2B' hs
  obtain ⟨K, hK⟩ := hDC G.Cover G.π G.ζ G.π_surj G.π_ker G.ζ_mem_center G.ζ_orderOf
    ⟨c, hc1, by rw [hcs]; exact hs⟩
  let mk : ↥G.P →* G.Cover := QuotientGroup.mk' G.Δ'
  let T : Subgroup ↥G.P := K.comap mk
  let ψ₁ : ↥T →* H := (MonoidHom.fst H H').comp (G.P.subtype.comp T.subtype)
  let ψ₂ : ↥T →* H' := (MonoidHom.snd H H').comp (G.P.subtype.comp T.subtype)
  have hker : ∀ t : ↥T, S.φ (t.1 : H × H').1 = 1 → (t.1 : H × H') ∈ G.Δ := by
    intro t ht
    have h1 : (⟨mk t.1, t.2⟩ : K) = ⟨1, K.one_mem⟩ := by
      apply hK.1
      show G.π (mk t.1) = G.π 1
      rw [map_one]
      exact ht
    exact Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff t.1).1 (congrArg Subtype.val h1))
  have hψ₁inj : Function.Injective ψ₁ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨⟨a, b⟩, hP⟩, hT⟩ ht
    have ha : a = 1 := ht
    subst ha
    have hb : b = 1 := G.eq_one_of_one_mem_Δ (hker ⟨⟨(1, b), hP⟩, hT⟩ (map_one S.φ))
    subst hb
    rfl
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨⟨a, b⟩, hP⟩, hT⟩ ht
    have hb : b = 1 := ht
    subst hb
    have hφ : S.φ a = 1 := by
      have h := mem_P0.1 (G.P_le_P0 hP)
      rw [h, map_one]
    have ha : a = 1 := G.eq_one_of_mem_Δ_one (hker ⟨⟨(a, 1), hP⟩, hT⟩ hφ)
    subst ha
    rfl
  have hψ₁surj : Function.Surjective ψ₁ := by
    intro x
    obtain ⟨y, hy⟩ := G.exists_mem_P x
    obtain ⟨k, hk⟩ := hK.2 (G.π (mk ⟨(x, y), hy⟩))
    have hk' : G.π (k : G.Cover) = G.π (mk ⟨(x, y), hy⟩) := hk
    have hmem : (mk ⟨(x, y), hy⟩)⁻¹ * (k : G.Cover) ∈ Subgroup.zpowers G.ζ := by
      rw [← G.π_ker, MonoidHom.mem_ker, map_mul, map_inv, hk', inv_mul_cancel]
    rcases (mem_zpowers_iff_of_orderOf_two G.ζ_orderOf).1 hmem with h1 | h1
    · refine ⟨⟨⟨(x, y), hy⟩, ?_⟩, rfl⟩
      show mk ⟨(x, y), hy⟩ ∈ K
      rw [inv_mul_eq_one.1 h1]
      exact k.2
    · refine ⟨⟨⟨(x, y), hy⟩ * ⟨((1 : H), S'.z), G.one_z_mem_P⟩, ?_⟩, by simp [ψ₁]⟩
      show mk (⟨(x, y), hy⟩ * ⟨((1 : H), S'.z), G.one_z_mem_P⟩) ∈ K
      have e : mk ⟨((1 : H), S'.z), G.one_z_mem_P⟩ = G.ζ := G.mk_one_z
      rw [map_mul, e]
      have e2 : mk ⟨(x, y), hy⟩ * G.ζ = (k : G.Cover) := by
        rw [← h1]
        group
      rw [e2]
      exact k.2
  have hψ₁bij : Function.Bijective ψ₁ := ⟨hψ₁inj, hψ₁surj⟩
  have hcardT : Nat.card ↥T = Nat.card H := Nat.card_congr (Equiv.ofBijective ψ₁ hψ₁bij)
  have hψ₂bij : Function.Bijective ψ₂ :=
    hψ₂inj.bijective_of_nat_card_le (by rw [hcardT, hcard])
  exact ⟨(MulEquiv.ofBijective ψ₁ hψ₁bij).symm.trans (MulEquiv.ofBijective ψ₂ hψ₂bij)⟩

end TypeUnique

end CFSG.Monster.GMS
