module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourHalf
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  (quotCenterHom quotCenterHom_mk quotCenterHom_injective)

variable {V : Type*} [CommGroup V]

private theorem quotCenterHom_conj {G : Type*} [Group G] (x : G) :
    quotCenterHom G (MulAut.conj x : MulAut G) =
      (MulAut.conj (QuotientGroup.mk x) : MulAut (G ⧸ Subgroup.center G)) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [quotCenterHom_mk, MulAut.conj_apply, MulAut.conj_apply]
    simp

private theorem mul_inv_mem_centralizer_of_quotCenterHom_conj {V : Type*} [CommGroup V]
    {L : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L) {a : MulAut V}
    {ψ : MulAut ↥L}
    (hψ_apply : ∀ m : ↥L, ((ψ m : ↥L) : MulAut V) = a * (m : MulAut V) * a⁻¹)
    {x : ↥L} (h : quotCenterHom ↥L ψ = MulAut.conj (QuotientGroup.mk x)) :
    a * (x : MulAut V)⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
  have hψ : ψ = MulAut.conj x := by
    have h1 : quotCenterHom ↥L (ψ * (MulAut.conj x)⁻¹) = 1 := by
      rw [map_mul, map_inv, h, quotCenterHom_conj]
      simp
    have h2 : ψ * (MulAut.conj x)⁻¹ = 1 :=
      quotCenterHom_injective hperf.1 (by rw [h1, map_one])
    have h3 := congrArg (fun z => z * MulAut.conj x) h2
    simpa [mul_assoc] using h3
  have hpoint : ∀ m ∈ L, a * m * a⁻¹ =
      (x : MulAut V) * m * (x : MulAut V)⁻¹ := by
    intro m hm
    have hψm := congrArg (fun f : MulAut ↥L => (f ⟨m, hm⟩ : ↥L)) hψ
    have h2 : ((ψ ⟨m, hm⟩ : ↥L) : MulAut V) = a * m * a⁻¹ := hψ_apply ⟨m, hm⟩
    have h3 : ((MulAut.conj x ⟨m, hm⟩ : ↥L) : MulAut V) =
        (x : MulAut V) * m * (x : MulAut V)⁻¹ := rfl
    rw [← h2, hψm]
    exact h3
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h5 : a * (x : MulAut V)⁻¹ * m * (x * a⁻¹) = m := by
    have h6 : a * (x : MulAut V)⁻¹ * m * (x * a⁻¹) =
        a * ((x : MulAut V)⁻¹ * m * x) * a⁻¹ := by group
    rw [h6, hpoint _ (L.mul_mem (L.mul_mem (L.inv_mem x.2) hm) x.2)]
    group
  calc m * (a * (x : MulAut V)⁻¹)
      = (a * (x : MulAut V)⁻¹ * m * (x * a⁻¹)) * (a * (x : MulAut V)⁻¹) := by rw [h5]
    _ = (a * (x : MulAut V)⁻¹) * m := by group

private theorem orderOf_mul_conj_inv_mul_conj {G : Type*} [Group G] {a : G}
    (ha : a * a = 1) (g : G) :
    orderOf (a * (g⁻¹ * a * g)) = orderOf (a * (g * a * g⁻¹)) := by
  set b := g * a * g⁻¹ with hb
  have hb2 : b * b = 1 := by
    rw [hb]
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; simp
  have hconj : g * (a * (g⁻¹ * a * g)) * g⁻¹ = b * a := by
    rw [hb]
    group
  have hba : b * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha]
  calc orderOf (a * (g⁻¹ * a * g))
      = orderOf (g * (a * (g⁻¹ * a * g)) * g⁻¹) :=
        SemiconjBy.orderOf_eq g (by
          show g * (a * (g⁻¹ * a * g)) = (g * (a * (g⁻¹ * a * g)) * g⁻¹) * g
          group)
    _ = orderOf (b * a) := by rw [hconj]
    _ = orderOf (a * b) := by rw [hba, orderOf_inv]
    _ = orderOf (a * (g * a * g⁻¹)) := by rw [hb]

private theorem conj_mul_pow_half {G : Type*} [Group G] (a g : G)
    (ha : a * a = 1) (ho : Even (orderOf (a * (g * a * g⁻¹))))
    (hord : orderOf (a * (g⁻¹ * a * g)) = orderOf (a * (g * a * g⁻¹))) :
    g * (a * (a * (g⁻¹ * a * g)) ^ (orderOf (a * (g⁻¹ * a * g)) / 2)) * g⁻¹ =
      (g * a * g⁻¹) * (a * (g * a * g⁻¹)) ^ (orderOf (a * (g * a * g⁻¹)) / 2) := by
  have ho' : Even (orderOf (a * (g⁻¹ * a * g))) := by rw [hord]; exact ho
  have hhalfb : orderOf (a * (g * a * g⁻¹)) / 2 + orderOf (a * (g * a * g⁻¹)) / 2 =
      orderOf (a * (g * a * g⁻¹)) := by
    obtain ⟨t, ht⟩ := ho
    omega
  have halph : orderOf (a * (g⁻¹ * a * g)) / 2 + orderOf (a * (g⁻¹ * a * g)) / 2 =
      orderOf (a * (g⁻¹ * a * g)) := by
    obtain ⟨t, ht⟩ := ho'
    omega
  have hzsq : (a * (g * a * g⁻¹)) ^ (orderOf (a * (g * a * g⁻¹)) / 2) *
      (a * (g * a * g⁻¹)) ^ (orderOf (a * (g * a * g⁻¹)) / 2) = 1 := by
    rw [← pow_add, hhalfb, pow_orderOf_eq_one]
  have hz_inv : ((a * (g * a * g⁻¹)) ^ (orderOf (a * (g * a * g⁻¹)) / 2))⁻¹ =
      (a * (g * a * g⁻¹)) ^ (orderOf (a * (g * a * g⁻¹)) / 2) :=
    inv_eq_of_mul_eq_one_right hzsq
  have hb2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; simp
  have hconj : g * (a * (g⁻¹ * a * g)) * g⁻¹ = (a * (g * a * g⁻¹))⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha]
    group
  have hpow : g * (a * (g⁻¹ * a * g)) ^ (orderOf (a * (g⁻¹ * a * g)) / 2) * g⁻¹ =
      (g * (a * (g⁻¹ * a * g)) * g⁻¹) ^ (orderOf (a * (g⁻¹ * a * g)) / 2) := by
    simp
  calc g * (a * (a * (g⁻¹ * a * g)) ^ (orderOf (a * (g⁻¹ * a * g)) / 2)) * g⁻¹
      = (g * a * g⁻¹) *
          (g * (a * (g⁻¹ * a * g)) ^ (orderOf (a * (g⁻¹ * a * g)) / 2) * g⁻¹) := by
        group
    _ = (g * a * g⁻¹) * ((g * (a * (g⁻¹ * a * g)) * g⁻¹) ^
          (orderOf (a * (g⁻¹ * a * g)) / 2)) := by rw [hpow]
    _ = (g * a * g⁻¹) * (((a * (g * a * g⁻¹))⁻¹) ^
          (orderOf (a * (g⁻¹ * a * g)) / 2)) := by rw [hconj]
    _ = (g * a * g⁻¹) * (((a * (g * a * g⁻¹)) ^
          (orderOf (a * (g⁻¹ * a * g)) / 2))⁻¹) := by rw [inv_pow]
    _ = (g * a * g⁻¹) * (((a * (g * a * g⁻¹)) ^
          (orderOf (a * (g * a * g⁻¹)) / 2))⁻¹) := by rw [hord]
    _ = (g * a * g⁻¹) * ((a * (g * a * g⁻¹)) ^
          (orderOf (a * (g * a * g⁻¹)) / 2)) := by rw [hz_inv]

theorem inner_of_fourFacts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hX : FourFacts (↥L ⧸ center ↥L))
    (hAL : ∀ u ∈ A, ∀ l ∈ L, u * l * u⁻¹ ∈ L) (hA4 : Nat.card A = 4)
    (hA2 : ∀ u ∈ A, u * u = 1) (hA : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥) :
    ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set (MulAut V)) := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite ↥L := Finite.of_injective ((↑) : ↥L → MulAut V) Subtype.coe_injective
  have : Finite ↥A := Finite.of_injective ((↑) : ↥A → MulAut V) Subtype.coe_injective
  let X := ↥L ⧸ center ↥L
  let π : ↥L →* X := QuotientGroup.mk' (center ↥L)
  have hAL' : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hAL u hu l hl, fun hl => by
      have h1 : u⁻¹ * (u * l * u⁻¹) * (u⁻¹)⁻¹ ∈ L := hAL u⁻¹ (A.inv_mem hu) _ hl
      have h2 : l = u⁻¹ * (u * l * u⁻¹) * (u⁻¹)⁻¹ := by group
      rw [h2]
      exact h1⟩
  let ψ : ↥A →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hAL')
  let φ : ↥A →* MulAut X := (quotCenterHom ↥L).comp ψ
  have hφ_mk : ∀ (u : ↥A) (l : ↥L),
      φ u (π l) = π ⟨(u : MulAut V) * (l : MulAut V) * (u : MulAut V)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAL' u.2) (l : MulAut V)).mp l.2⟩ := by
    intro u l
    change quotCenterHom ↥L (ψ u) (QuotientGroup.mk l) = _
    rw [quotCenterHom_mk]
    rfl
  have hφker : ∀ u : ↥A, φ u = 1 →
      (u : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    intro u hu
    have hψu : ψ u = 1 := quotCenterHom_injective hL.1 (by rw [map_one]; exact hu)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ((ψ u ⟨l, hl⟩ : ↥L) : MulAut V) = l := by
      have h := congrArg (fun α : MulAut ↥L => α ⟨l, hl⟩) hψu
      simpa using congrArg (fun y : ↥L => (y : MulAut V)) h
    have h2 : (u : MulAut V) * l * (u : MulAut V)⁻¹ = l := by
      simpa [ψ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
    calc l * (u : MulAut V) = ((u : MulAut V) * l * (u : MulAut V)⁻¹) * (u : MulAut V) := by
          rw [h2]
      _ = (u : MulAut V) * l := by group
  have hφinj : Function.Injective φ := by
    intro u v huv
    have h1 : φ (u⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, huv]
      simp
    have h2 : ((u⁻¹ * v : ↥A) : MulAut V) ∈
        A ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
      ⟨(u⁻¹ * v).2, hφker (u⁻¹ * v) h1⟩
    rw [hAC] at h2
    have h3 : (u⁻¹ * v : ↥A) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp h2)
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  let B : Subgroup (MulAut X) := φ.range
  have hBcard : Nat.card B = 4 := by
    have h1 : Nat.card B = Nat.card ↥A := by
      rw [show B = φ.range from rfl, MonoidHom.range_eq_map]
      calc Nat.card ↥((⊤ : Subgroup ↥A).map φ) = Nat.card ↥(⊤ : Subgroup ↥A) :=
            Subgroup.card_map_of_injective (K := ⊤) hφinj
        _ = Nat.card ↥A := Subgroup.card_top
    rw [h1]
    simpa using hA4
  have hBsq : ∀ β ∈ B, β * β = 1 := by
    intro β hβ
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hβ
    have hu : u * u = 1 := Subtype.ext (hA2 (u : MulAut V) u.2)
    rw [← map_mul, hu, map_one]
  have hperfL : Group.IsPerfect ↥L := ⟨hL.1⟩
  intro a₀ ha₀A
  by_contra hcon
  push Not at hcon
  have hBnotInn : ¬ B ≤ (MulAut.conj : X →* MulAut X).range := by
    intro hle
    have hmem : φ ⟨a₀, ha₀A⟩ ∈ (MulAut.conj : X →* MulAut X).range := by
      exact hle ⟨⟨a₀, ha₀A⟩, rfl⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
    obtain ⟨l, hπl⟩ : ∃ l : ↥L, π l = x := QuotientGroup.mk'_surjective (center ↥L) x
    have hψ_apply : ∀ m : ↥L, ((ψ ⟨a₀, ha₀A⟩ m : ↥L) : MulAut V) =
        (a₀ : MulAut V) * (m : MulAut V) * (a₀ : MulAut V)⁻¹ := by
      intro m
      simp [ψ]
    have hquot : quotCenterHom ↥L (ψ ⟨a₀, ha₀A⟩) =
        MulAut.conj (QuotientGroup.mk l : X) := by
      have hx' : MulAut.conj (π l) = φ ⟨a₀, ha₀A⟩ := by rw [hπl]; exact hx
      change quotCenterHom ↥L (ψ ⟨a₀, ha₀A⟩) = MulAut.conj (π l)
      rw [hx']
      rfl
    exact hcon l l.2 (mul_inv_mem_centralizer_of_quotCenterHom_conj hperfL hψ_apply hquot)
  obtain ⟨β, hβB, x, hmx, h4x, hg1x, hg2x⟩ := hX B hBcard hBsq hBnotInn
  obtain ⟨aA, hφa⟩ := MonoidHom.mem_range.mp hβB
  obtain ⟨g, hπg⟩ : ∃ g : ↥L, π g = x := QuotientGroup.mk'_surjective (center ↥L) x
  have hm : Even (orderOf (β * (MulAut.conj (π g) * β * (MulAut.conj (π g))⁻¹))) := by
    rw [hπg]; exact hmx
  have h4 : 4 ≤ orderOf (β * (MulAut.conj (π g) * β * (MulAut.conj (π g))⁻¹)) := by
    rw [hπg]; exact h4x
  have hg1 : FourGen B β (π g) := by rw [hπg]; exact hg1x
  have hβ : ∀ l : ↥L, β (π l) =
      π ⟨(aA : MulAut V) * (l : MulAut V) * (aA : MulAut V)⁻¹, hAL aA aA.2 l l.2⟩ := by
    intro l
    rw [← hφa]
    simpa using hφ_mk aA l
  have hB : ∀ b ∈ B, ∃ u, ∃ hu : u ∈ A, ∀ l : ↥L, b (π l) =
      π ⟨(u : MulAut V) * (l : MulAut V) * (u : MulAut V)⁻¹, hAL u hu l l.2⟩ := by
    intro b hb
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hb
    exact ⟨u, u.2, fun l => by simpa using hφ_mk u l⟩
  let gV : MulAut V := (g : MulAut V)
  let aV : MulAut V := (aA : MulAut V)
  let bV : MulAut V := gV * aV * gV⁻¹
  let a'' : MulAut V := gV⁻¹ * aV * gV
  let o : ℕ := orderOf (aV * bV)
  let o'' : ℕ := orderOf (aV * a'')
  obtain ⟨r, hr, horder⟩ := exists_odd_orderOf_mul_conj_eq hL hZ hAL aA.2
    (hA2 aA aA.2) hβ g
  have horder' : o = orderOf (β * (MulAut.conj (π g) * β *
      (MulAut.conj (π g))⁻¹)) * r := horder
  have hme : Even o := by
    obtain ⟨k, hk⟩ := hm
    refine ⟨k * r, ?_⟩
    rw [horder', hk]
    ring
  have h4o : 4 ≤ o := by
    rw [horder']
    calc 4 ≤ orderOf (β * (MulAut.conj (π g) * β * (MulAut.conj (π g))⁻¹)) := h4
      _ = orderOf (β * (MulAut.conj (π g) * β * (MulAut.conj (π g))⁻¹)) * 1 :=
          (mul_one _).symm
      _ ≤ orderOf (β * (MulAut.conj (π g) * β * (MulAut.conj (π g))⁻¹)) * r :=
          Nat.mul_le_mul_left _ (Odd.pos hr)
  have ha_part : commV (zpowers aV) ⊓ commV (zpowers (aV * (aV * bV) ^ (o / 2))) = ⊥ := by
    have h := commV_inf_commV_mul_pow_half_eq_bot hL hZ hAL hA hfix aA.2
      (hA2 aA aA.2) hβ hB hm hg1
    simpa [aV, bV, gV, o] using h
  have hπg_inv : π g⁻¹ = x⁻¹ := by rw [map_inv, hπg]
  have hm_inv : Even (orderOf (β * (MulAut.conj (π g⁻¹) * β *
      (MulAut.conj (π g⁻¹))⁻¹))) := by
    rw [hπg_inv, map_inv, inv_inv]
    rw [orderOf_mul_conj_inv_mul_conj (hBsq β hβB) (MulAut.conj x)]
    exact hmx
  have hg2' : FourGen B β (π g⁻¹) := by rw [hπg_inv]; exact hg2x
  have hraw := commV_inf_commV_mul_pow_half_eq_bot hL hZ hAL hA hfix aA.2
    (hA2 aA aA.2) hβ hB hm_inv hg2'
  have hraw' : commV (zpowers aV) ⊓ commV (zpowers (aV * (aV * a'') ^ (o'' / 2))) = ⊥ := hraw
  have hmap := congrArg (fun S : Subgroup V => S.map gV.toMonoidHom) hraw'
  rw [Subgroup.map_inf_eq _ _ gV.toMonoidHom gV.injective, Subgroup.map_bot] at hmap
  rw [← commV_zpowers_conj_eq aV gV,
    ← commV_zpowers_conj_eq (aV * (aV * a'') ^ (o'' / 2)) gV] at hmap
  have hord : orderOf (aV * a'') = orderOf (aV * bV) := by
    simpa [a'', bV] using orderOf_mul_conj_inv_mul_conj (hA2 aA aA.2) gV
  have haV : aV * aV = 1 := hA2 aA aA.2
  have hconj_eq := conj_mul_pow_half aV gV haV (by simpa [o] using hme) hord
  rw [hconj_eq] at hmap
  have hb_part : commV (zpowers bV) ⊓ commV (zpowers (bV * (aV * bV) ^ (o / 2))) = ⊥ := by
    simpa [bV, o] using hmap
  exact false_of_inf_commV_eq_bot hV hme h4o ha_part hb_part

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
