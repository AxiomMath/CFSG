module

public import CFSG.Quasithin.Background.F918Z4bDef
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.ComponentClassification.PerfectAutomorphisms
open scoped IsMulCommutative

section Tools

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [← hZ, Subgroup.mem_center_iff]
  intro b
  have h1 := congrArg (fun e : MulAut S => e b) (MonoidHom.mem_ker.mp ha)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc b * a = a * b * a⁻¹ * a := by rw [h1]
    _ = a * b := by group

theorem IsElemAb2.isElemAbelian {S : Type} [Group S] {E : Subgroup S} (hE : IsElemAb2 E) :
    CFSG.Open.IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hE.1 a a.2 b b.2)⟩⟩, hE.2⟩

theorem card_le_mul_card_inf_ker {Γ Q : Type*} [Group Γ] [Group Q] [Finite Q] (θ : Γ →* Q)
    (E : Subgroup Γ) : Nat.card E ≤ Nat.card Q * Nat.card ↥(E ⊓ θ.ker) := by
  set ρ : ↥E →* Q := θ.comp E.subtype with hρ
  have hcard : Nat.card ↥E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hker : ρ.ker.map E.subtype = E ⊓ θ.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)⟩
    · rintro ⟨hx, hk⟩
      exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hk), rfl⟩
  rw [hcard, ← hker, Subgroup.card_map_of_injective E.subtype_injective]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_card_group _)

theorem card_comap_of_le_range {Γ Δ : Type*} [Group Γ] [Group Δ] {f : Γ →* Δ}
    (hf : Function.Injective f) {E : Subgroup Δ} (hE : E ≤ f.range) :
    Nat.card ↥(E.comap f) = Nat.card E := by
  rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq, inf_eq_right.mpr hE]

end Tools

section Reduction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAb2_top {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    IsElemAb2 (⊤ : Subgroup ↥E) := by
  have := hE.1
  exact ⟨fun a _ b _ => mul_comm a b, fun a _ => Subtype.ext (by simpa using hE.2 a a.2)⟩

theorem rk_le_add {L E : Subgroup G} (hL : Group.IsPerfect ↥L)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hE : CFSG.Open.IsElemAbelian 2 E) {m : ℕ}
    (hAut : AutRankLe (↥L ⧸ Subgroup.center ↥L) m) :
    rk ↥E ≤ m + rk ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥E →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hψ
  set φ : ↥E →* MulAut (↥L ⧸ Subgroup.center ↥L) := (centerQuotientHom ↥L).comp ψ with hφ
  have hker : φ.ker = (E ⊓ Subgroup.centralizer (L : Set G)).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply,
      ← (centerQuotientHom ↥L).map_one, (centerQuotientHom_injective ↥L).eq_iff]
    constructor
    · intro h
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨l, hl⟩ : ↥L) : G)) h
      change (x : G) * l * (x : G)⁻¹ = l at h1
      calc l * x = (x : G) * l * (x : G)⁻¹ * x := by rw [h1]
        _ = x * l := by group
    · rintro ⟨-, hx⟩
      refine MulEquiv.ext fun l => Subtype.ext ?_
      change (x : G) * l * (x : G)⁻¹ = l
      rw [← Subgroup.mem_centralizer_iff.mp hx l l.2, mul_inv_cancel_right]
  have hcard : Nat.card ↥E = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hrange : rk ↥φ.range ≤ m := by
    rw [MonoidHom.range_eq_map]
    exact hAut.rk_map_le (isElemAb2_top hE) φ
  have hkerc : Nat.card ↥φ.ker = Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  unfold rk at hrange ⊢
  rw [hcard, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hkerc]
  exact Nat.add_le_add_right hrange _

end Reduction

section TwoQuot

variable {L : Type} [Group L] [Finite L]

theorem exists_twoQuot (hL : CFSG.IsQuasisimple L) :
    ∃ N : Subgroup L, ∃ _ : N.Normal, N ≤ Subgroup.center L ∧ Odd (Nat.card N) ∧
      CFSG.Open.IsQuasisimple (L ⧸ N) ∧ IsPGroup 2 ↥(Subgroup.center (L ⧸ N)) ∧
      Nonempty ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N) ≃* L ⧸ Subgroup.center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hZ⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥(Subgroup.center L))).ne'
  let N : Subgroup L :=
    { carrier := {z | z ∈ Subgroup.center L ∧ z ^ m = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
        refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
        have hc : Commute x y := Subgroup.mem_center_iff.mp hy x
        rw [hc.mul_pow, hxm, hym, one_mul]
      one_mem' := ⟨Subgroup.one_mem _, one_pow m⟩
      inv_mem' := by
        rintro x ⟨hx, hxm⟩
        exact ⟨Subgroup.inv_mem _ hx, by rw [inv_pow, hxm, inv_one]⟩ }
  have hNZ : N ≤ Subgroup.center L := fun z hz => hz.1
  have hNn : N.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hNZ hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hodd : Odd (Nat.card N) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxm : (x : L) ^ m = 1 := x.2.2
    have h1 : orderOf (x : L) ∣ m := orderOf_dvd_of_pow_eq_one hxm
    rw [Subgroup.orderOf_coe, hx] at h1
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h1)
  obtain ⟨hqN, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hL N hNZ
  have h2 : IsPGroup 2 ↥(Subgroup.center (L ⧸ N)) := by
    rintro ⟨y, hy⟩
    rw [hcen] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨a, Subtype.ext ?_⟩
    have hz1 : (⟨z, hz⟩ : ↥(Subgroup.center L)) ^ Nat.card ↥(Subgroup.center L) = 1 :=
      pow_card_eq_one'
    rw [hZ, pow_mul] at hz1
    have hz2 : (z ^ 2 ^ a) ^ m = 1 := by simpa using congrArg Subtype.val hz1
    have hmem : z ^ 2 ^ a ∈ N := ⟨Subgroup.pow_mem _ hz _, hz2⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  exact ⟨N, hNn, hNZ, hodd, ⟨Group.isPerfect_def.mp hqN.1, hqN.2.1⟩, h2,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center L) hNZ)⟩⟩

end TwoQuot

@[expose] def CenterRankLe (S : Type) [Group S] (r : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* S) →
      ∀ E₀ : Subgroup K, E₀ ≤ Subgroup.center K → CFSG.Open.IsElemAbelian 2 E₀ →
        Nat.card E₀ ≤ 2 ^ r

theorem CenterRankLe.of_card_dvd {S : Type} [Group S] {r : ℕ}
    (h : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 2 ↥(Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* S) →
        Nat.card ↥(Subgroup.center K) ∣ 2 ^ r) : CenterRankLe S r := by
  intro K _ _ hK hZ he E₀ hE₀ _
  exact Nat.le_of_dvd (by positivity) ((Subgroup.card_dvd_of_le hE₀).trans (h K hK hZ he))

theorem card_le_two_of_le_cyclic {K : Type} [Group K] [Finite K] {Z E₀ : Subgroup K}
    (hZ : IsCyclic ↥Z) (hE₀ : E₀ ≤ Z) (hE : CFSG.Open.IsElemAbelian 2 E₀) : Nat.card E₀ ≤ 2 := by
  have hc : IsCyclic ↥(E₀.subgroupOf Z) := Subgroup.isCyclic _
  have hc' : IsCyclic ↥E₀ := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hE₀).toMonoidHom (Subgroup.subgroupOfEquivOfLe hE₀).surjective
  obtain ⟨g, hg⟩ := hc'.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd (by norm_num)
    (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2)))

theorem CenterRankLe.of_cyclic {S : Type} [Group S]
    (h : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 2 ↥(Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* S) →
        IsCyclic ↥(Subgroup.center K)) : CenterRankLe S 1 := by
  intro K _ _ hK hZ he E₀ hE₀ hE
  rw [pow_one]
  exact card_le_two_of_le_cyclic (h K hK hZ he) hE₀ hE

section Rank

variable {G : Type} [Group G] [Finite G]

theorem rk_inf_centralizer_le {L E : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hEL : E ⊓ Subgroup.centralizer (L : Set G) ≤ L) {r : ℕ}
    (hZ : CenterRankLe (↥L ⧸ Subgroup.center ↥L) r) :
    rk ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ r := by
  obtain ⟨N, hNn, hNZ, hodd, hqK, h2, ⟨e⟩⟩ := exists_twoQuot hq
  set C := E ⊓ Subgroup.centralizer (L : Set G) with hC
  set E₀ : Subgroup ↥L := C.subgroupOf L with hE₀
  have hsq : ∀ x ∈ E₀, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
  have hE₀Z : E₀ ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hx).2 y y.2)
  set f : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N with hf
  set g : ↥E₀ →* ↥L ⧸ N := f.comp E₀.subtype with hg
  have hginj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, hf, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : orderOf (⟨(x : ↥L), hx⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
    have h2 : orderOf (⟨(x : ↥L), hx⟩ : ↥N) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (hsq x x.2))
    have h3 : orderOf (⟨(x : ↥L), hx⟩ : ↥N) = 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd), Nat.dvd_one] at this
    rw [orderOf_eq_one_iff] at h3
    have h4 : (x : ↥L) = 1 := congrArg Subtype.val h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h4)
  have hgZ : g.range ≤ Subgroup.center (↥L ⧸ N) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [hg, MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp (hE₀Z x.2) y]
  have hgel : CFSG.Open.IsElemAbelian 2 g.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨-, ha⟩ := a
      obtain ⟨-, hb⟩ := b
      exact Subgroup.mem_center_iff.mp (hgZ hb) _
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (hsq x x.2), map_one]
  have hcard := hZ (↥L ⧸ N) hqK h2 ⟨e⟩ g.range hgZ hgel
  have hgc : Nat.card ↥g.range = Nat.card ↥C := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  rw [hgc] at hcard
  exact rk_le_of_card_le_two_pow
    (isPGroup_two_of_sq_eq_one fun c => Subtype.ext (by simpa using hE.2 _ c.2.1)) hcard

theorem inf_centralizer_eq_bot {L E : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hEL : E ⊓ Subgroup.centralizer (L : Set G) ≤ L)
    (hZ : CenterRankLe (↥L ⧸ Subgroup.center ↥L) 0) :
    E ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have h := rk_inf_centralizer_le hq hE hEL hZ
  have hp : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (L : Set G)) :=
    isPGroup_two_of_sq_eq_one fun c => Subtype.ext (by simpa using hE.2 _ c.2.1)
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [card_eq_two_pow_of_isPGroup hp, Nat.le_zero.mp h, pow_zero]

theorem rk_le_of_autRankLe {L E : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hEL : E ⊓ Subgroup.centralizer (L : Set G) ≤ L) {m r : ℕ}
    (hAut : AutRankLe (↥L ⧸ Subgroup.center ↥L) m)
    (hZ : CenterRankLe (↥L ⧸ Subgroup.center ↥L) r) : rk ↥E ≤ m + r :=
  (rk_le_add hq.1 hEN hE hAut).trans (Nat.add_le_add_left (rk_inf_centralizer_le hq hE hEL hZ) m)

end Rank

end CFSG.Quasithin.H13.Ch9.KGFF
