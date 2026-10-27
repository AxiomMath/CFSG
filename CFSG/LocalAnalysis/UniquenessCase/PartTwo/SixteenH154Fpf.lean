module

public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeHyperplanes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

theorem s16h_card_le_mul_cent_of_fpf {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {E : Subgroup (MulAut V)} (hE : IsElemAbelian q E) {U : Subgroup V}
    (hUE : ∀ x ∈ E, ∀ u ∈ U, x u ∈ U)
    (hfpf : ∀ x ∈ E, x ∈ centSub U ∨ U ⊓ fixV (Subgroup.zpowers x) = ⊥) :
    Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ centSub U) := by
  have hEstab : E ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have := hUE x⁻¹ (E.inv_mem hx) (x u) hu
        simpa using this,
      fun hu => hUE x hx u hu⟩
  have hcard := card_autSub_mul hEstab
  have hEab : IsElemAbelian q (autSub E U) :=
    (hE.subgroupOf (stabSub U)).map (resHom U)
  suffices hEbar : Nat.card (autSub E U) ≤ q by
    calc Nat.card ↥E = Nat.card (autSub E U) * Nat.card ↥(E ⊓ centSub U) := hcard.symm
      _ ≤ q * Nat.card ↥(E ⊓ centSub U) := Nat.mul_le_mul_right _ hEbar
  by_cases hcyc : IsCyclic (autSub E U)
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(autSub E U))
    have hgq : g ^ q = 1 :=
      Subtype.ext (by simpa using hEab.2 (g : MulAut U) g.2)
    have horder : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one hgq
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd hq.pos horder
  · have hUbot : U ≠ ⊥ := by
      intro hU
      apply hcyc
      haveI : Subsingleton ↥U := by
        rw [hU]
        exact ⟨fun a b => Subtype.ext (by
          rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      haveI : Subsingleton (MulAut ↥U) :=
        ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
      exact isCyclic_of_subsingleton
    haveI : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUbot
    have hW2 : IsPGroup 2 ↥U :=
      isPGroup_two_of_sq_eq_one fun u => Subtype.ext (by simpa using hV (u : V))
    haveI : CFSG.IsElementaryAbelian q ↥(autSub E U) := hEab.isElementaryAbelian
    obtain ⟨a, ha1, x, hx1, hax⟩ :=
      exists_nonidentity_actor_with_nonidentity_fixed_two_group
        (W := ↥U) (A := ↥(autSub E U)) hq (hq.odd_of_ne_two hq2) hcyc hW2
    obtain ⟨g, hgE, hgres⟩ := mem_autSub.mp a.2
    have hgcent : (g : MulAut V) ∉ centSub U := by
      intro hgc
      have hker : g ∈ (centSub U).subgroupOf (stabSub U) := by
        rw [Subgroup.mem_subgroupOf]; exact hgc
      have h1 : resHom U g = 1 :=
        MonoidHom.mem_ker.mp (by rw [ker_resHom U]; exact hker)
      exact ha1 (Subtype.ext (by rw [← hgres, h1]; rfl))
    rcases hfpf (g : MulAut V) hgE with hgc | hfix
    · exact absurd hgc hgcent
    · have hgx : (g : MulAut V) (x : V) = (x : V) := by
        have h1 : ((a • x : ↥U) : V) = (g : MulAut V) (x : V) := by
          rw [Subgroup.smul_def, MulAut.smul_def, ← hgres, resHom_apply]
        rw [← h1]
        exact congrArg Subtype.val hax
      have hxmem : (x : V) ∈ U ⊓ fixV (Subgroup.zpowers (g : MulAut V)) :=
        Subgroup.mem_inf.mpr ⟨x.2, mem_fixV_zpowers_iff_apply.mpr hgx⟩
      exact absurd (Subtype.ext (Subgroup.mem_bot.mp (hfix ▸ hxmem))) hx1

section Helpers

variable {V : Type*} [CommGroup V]

private lemma s16h_commute_zpowers {x g : MulAut V} (hxg : g * x = x * g) {y : MulAut V}
    (hy : y ∈ Subgroup.zpowers x) : g * y = y * g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute g x from hxg).zpow_right n

private lemma s16h_commSub_zpowers_invariant {x g : MulAut V} {U : Subgroup V}
    (hxg : g * x = x * g) (hU : ∀ u ∈ U, g u ∈ U) {c : V}
    (hc : c ∈ commSub U (Subgroup.zpowers x)) :
    g c ∈ commSub U (Subgroup.zpowers x) := by
  refine Subgroup.closure_induction (p := fun c _ => g c ∈ commSub U (Subgroup.zpowers x))
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, w, hw, rfl⟩
    have hyg : g * y = y * g := s16h_commute_zpowers hxg hy
    have h1 : g (y w) = y (g w) := by rw [← MulAut.mul_apply, hyg, MulAut.mul_apply]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨y, hy, g w, hU w hw, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

private lemma s16h_inf_fixV_zpowers_invariant {x g : MulAut V} {U : Subgroup V}
    (hxg : g * x = x * g) (hU : ∀ u ∈ U, g u ∈ U) {c : V}
    (hc : c ∈ U ⊓ fixV (Subgroup.zpowers x)) :
    g c ∈ U ⊓ fixV (Subgroup.zpowers x) := by
  obtain ⟨hcU, hcfix⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨hU c hcU, ?_⟩
  rw [mem_fixV] at hcfix ⊢
  intro y hy
  have hyg : y * g = g * y := (s16h_commute_zpowers hxg hy).symm
  rw [← MulAut.mul_apply, hyg, MulAut.mul_apply, hcfix y hy]

private lemma s16h_centSub_sup (U₁ U₂ : Subgroup V) :
    centSub (U₁ ⊔ U₂) = centSub U₁ ⊓ centSub U₂ := by
  ext g
  rw [mem_centSub, Subgroup.mem_inf, mem_centSub, mem_centSub]
  exact ⟨fun h => ⟨fun u hu => h u (Subgroup.mem_sup_left hu),
      fun u hu => h u (Subgroup.mem_sup_right hu)⟩,
    fun h u hu => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul, h.1 a ha, h.2 b hb]⟩

end Helpers

theorem s16h_card_le_pow_mul_cent {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) {B E : Subgroup (MulAut V)} (hB : IsPGroup p ↥B) (hE : IsElemAbelian q E)
    (hBE : ∀ b ∈ B, ∀ x ∈ E, b * x = x * b) {U : Subgroup V}
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b u ∈ U) (hUE : ∀ x ∈ E, ∀ u ∈ U, x u ∈ U)
    (hfix : U ⊓ fixV B = ⊥) :
    Nat.card ↥E ≤
      q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
        Nat.card ↥(E ⊓ centSub U) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  set ℓ : ℕ := Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q)) with hℓ
  have key : ∀ n : ℕ, ∀ (E : Subgroup (MulAut V)) (U : Subgroup V), rk ↥U = n →
      IsElemAbelian q E →
      (∀ b ∈ B, ∀ x ∈ E, b * x = x * b) →
      (∀ b ∈ B, ∀ u ∈ U, b u ∈ U) →
      (∀ x ∈ E, ∀ u ∈ U, x u ∈ U) →
      U ⊓ fixV B = ⊥ →
      Nat.card ↥E ≤ q ^ (rk ↥U / ℓ) * Nat.card ↥(E ⊓ centSub U) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E U hrn hE hBE hUB hUE hfix
      by_cases hcent : E ≤ centSub U
      · rw [inf_eq_left.mpr hcent]
        exact Nat.le_mul_of_pos_left _ (pow_pos hq.pos _)
      · obtain ⟨x₀, hxE, hxcent⟩ : ∃ x ∈ E, x ∉ centSub U := by
          by_contra h
          exact hcent fun y hy => by
            by_contra hyc
            exact h ⟨y, hy, hyc⟩
        by_cases hcase2 : ∃ y ∈ E, y ∉ centSub U ∧ U ⊓ fixV (Subgroup.zpowers y) ≠ ⊥
        · obtain ⟨x, hxE, hxcent, hxfix⟩ := hcase2
          set U₁ : Subgroup V := commSub U (Subgroup.zpowers x) with hU₁
          set U₂ : Subgroup V := U ⊓ fixV (Subgroup.zpowers x) with hU₂
          have hxne : x ≠ 1 := fun h => hxcent (h ▸ (centSub U).one_mem)
          have hxq : orderOf x = q := by
            have hdvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one (hE.2 x hxE)
            rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
            · exact absurd (orderOf_eq_one_iff.mp h1) hxne
            · exact h1
          have hPodd : Odd (Nat.card (Subgroup.zpowers x)) := by
            rw [Nat.card_zpowers, hxq]
            exact hq.odd_of_ne_two hq2
          have hstabx : Subgroup.zpowers x ≤ stabSub U := by
            rw [Subgroup.zpowers_le, mem_stabSub]
            intro u
            exact ⟨fun hu => by
                have := hUE x⁻¹ (E.inv_mem hxE) (x u) hu
                simpa using this,
              fun hu => hUE x hxE u hu⟩
          have hUinv : ∀ y ∈ Subgroup.zpowers x, ∀ u ∈ U, y u ∈ U := fun y hy u hu =>
            ((mem_stabSub.mp (hstabx hy)) u).mpr hu
          obtain ⟨hsup, _⟩ := coprime_decomp hPodd hV hUinv
          have hsup' : U₁ ⊔ U₂ = U := hsup
          have hrk : rk ↥U = rk ↥U₁ + rk ↥U₂ := by
            rw [hU₁, hU₂]
            exact (rk_commSub_add_rk_inf_fixV hUinv).symm
          have hU1ne : U₁ ≠ ⊥ := by
            intro h
            apply hxcent
            rw [mem_centSub]
            intro u hu
            exact mem_fixV_zpowers_iff_apply.mp ((commSub_eq_bot_iff.mp h) hu)
          have hU2ne : U₂ ≠ ⊥ := by rw [hU₂]; exact hxfix
          have hrk1pos : 1 ≤ rk ↥U₁ := Nat.pos_of_ne_zero fun h0 =>
            hU1ne ((rk_eq_zero_iff hV).mp h0)
          have hrk2pos : 1 ≤ rk ↥U₂ := Nat.pos_of_ne_zero fun h0 =>
            hU2ne ((rk_eq_zero_iff hV).mp h0)
          have hrk1lt : rk ↥U₁ < n := by omega
          have hrk2lt : rk ↥U₂ < n := by omega
          have hU1leU : U₁ ≤ U := by
            rw [hU₁]; exact commSub_le_of_invariant hUinv
          have hU2leU : U₂ ≤ U := by rw [hU₂]; exact inf_le_left
          have hEx : ∀ y ∈ E, y * x = x * y := by
            intro y hy
            have := hE.1.is_comm.comm (⟨y, hy⟩ : E) (⟨x, hxE⟩ : E)
            simpa using congrArg Subtype.val this
          have hUB1 : ∀ b ∈ B, ∀ u ∈ U₁, b u ∈ U₁ := by
            intro b hb u hu
            rw [hU₁] at hu ⊢
            exact s16h_commSub_zpowers_invariant (hBE b hb x hxE) (hUB b hb) hu
          have hUE1 : ∀ y ∈ E, ∀ u ∈ U₁, y u ∈ U₁ := by
            intro y hy u hu
            rw [hU₁] at hu ⊢
            exact s16h_commSub_zpowers_invariant (hEx y hy) (hUE y hy) hu
          have hUB2 : ∀ b ∈ B, ∀ u ∈ U₂, b u ∈ U₂ := by
            intro b hb u hu
            rw [hU₂] at hu ⊢
            exact s16h_inf_fixV_zpowers_invariant (hBE b hb x hxE) (hUB b hb) hu
          have hUE2 : ∀ y ∈ E, ∀ u ∈ U₂, y u ∈ U₂ := by
            intro y hy u hu
            rw [hU₂] at hu ⊢
            exact s16h_inf_fixV_zpowers_invariant (hEx y hy) (hUE y hy) hu
          have hfix1 : U₁ ⊓ fixV B = ⊥ :=
            le_bot_iff.mp ((inf_le_inf_right (fixV B) hU1leU).trans hfix.le)
          have hfix2 : U₂ ⊓ fixV B = ⊥ :=
            le_bot_iff.mp ((inf_le_inf_right (fixV B) hU2leU).trans hfix.le)
          have h1 := ih (rk ↥U₁) hrk1lt E U₁ rfl hE hBE hUB1 hUE1 hfix1
          have hE1 : IsElemAbelian q (E ⊓ centSub U₁) := hE.mono inf_le_left
          have hBE1 : ∀ b ∈ B, ∀ y ∈ E ⊓ centSub U₁, b * y = y * b :=
            fun b hb y hy => hBE b hb y (Subgroup.mem_inf.mp hy).1
          have hUE12 : ∀ y ∈ E ⊓ centSub U₁, ∀ u ∈ U₂, y u ∈ U₂ :=
            fun y hy u hu => hUE2 y (Subgroup.mem_inf.mp hy).1 u hu
          have h2 := ih (rk ↥U₂) hrk2lt (E ⊓ centSub U₁) U₂ rfl hE1 hBE1 hUB2 hUE12 hfix2
          have hle_cent : (E ⊓ centSub U₁) ⊓ centSub U₂ ≤ E ⊓ centSub U := by
            intro g hg
            rw [Subgroup.mem_inf] at hg
            obtain ⟨hgE1, hg2⟩ := hg
            rw [Subgroup.mem_inf] at hgE1
            obtain ⟨hgE, hg1⟩ := hgE1
            refine Subgroup.mem_inf.mpr ⟨hgE, ?_⟩
            have hthis : g ∈ centSub (U₁ ⊔ U₂) := by
              rw [s16h_centSub_sup]
              exact Subgroup.mem_inf.mpr ⟨hg1, hg2⟩
            rwa [hsup'] at hthis
          have hcardle : Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) ≤
              Nat.card ↥(E ⊓ centSub U) := Subgroup.card_le_of_le hle_cent
          have hsum : rk ↥U₁ / ℓ + rk ↥U₂ / ℓ ≤ rk ↥U / ℓ := by
            have h := Nat.div_add_div_le_add_div (x := rk ↥U₁) (y := rk ↥U₂) (z := ℓ)
            rwa [← hrk] at h
          have hpoweq : q ^ (rk ↥U₁ / ℓ) *
                (q ^ (rk ↥U₂ / ℓ) * Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂)) =
              q ^ (rk ↥U₁ / ℓ + rk ↥U₂ / ℓ) *
                Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) := by
            rw [pow_add]; ring
          calc Nat.card ↥E
              ≤ q ^ (rk ↥U₁ / ℓ) * Nat.card ↥(E ⊓ centSub U₁) := h1
            _ ≤ q ^ (rk ↥U₁ / ℓ) * (q ^ (rk ↥U₂ / ℓ) *
                  Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂)) :=
                Nat.mul_le_mul_left _ h2
            _ = q ^ (rk ↥U₁ / ℓ + rk ↥U₂ / ℓ) *
                  Nat.card ↥((E ⊓ centSub U₁) ⊓ centSub U₂) := hpoweq
            _ ≤ q ^ (rk ↥U / ℓ) * Nat.card ↥(E ⊓ centSub U) :=
                Nat.mul_le_mul (Nat.pow_le_pow_right hq.pos hsum) hcardle
        · have hfpf : ∀ y ∈ E, y ∈ centSub U ∨ U ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
            intro y hy
            by_cases hyc : y ∈ centSub U
            · exact Or.inl hyc
            · exact Or.inr (by
                by_contra hne
                exact hcase2 ⟨y, hy, hyc, hne⟩)
          have hbound := s16h_card_le_mul_cent_of_fpf hV hq hq2 hE hUE hfpf
          have hx₀ne : x₀ ≠ 1 := fun h => hxcent (h ▸ (centSub U).one_mem)
          have hx₀q : orderOf x₀ = q := by
            have hdvd : orderOf x₀ ∣ q := orderOf_dvd_of_pow_eq_one (hE.2 x₀ hxE)
            rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
            · exact absurd (orderOf_eq_one_iff.mp h1) hx₀ne
            · exact h1
          have hUbot : U ≠ ⊥ := by
            intro hU
            apply hxcent
            rw [hU, mem_centSub]
            intro u hu
            rw [Subgroup.mem_bot.mp hu, map_one]
          have hrkpos : 0 < rk ↥U := Nat.pos_of_ne_zero fun h0 =>
            hUbot ((rk_eq_zero_iff hV).mp h0)
          have hstabx : Subgroup.zpowers x₀ ≤ stabSub U := by
            rw [Subgroup.zpowers_le, mem_stabSub]
            intro u
            exact ⟨fun hu => by
                have := hUE x₀⁻¹ (E.inv_mem hxE) (x₀ u) hu
                simpa using this,
              fun hu => hUE x₀ hxE u hu⟩
          have hUinv : ∀ y ∈ Subgroup.zpowers x₀, ∀ u ∈ U, y u ∈ U := fun y hy u hu =>
            ((mem_stabSub.mp (hstabx hy)) u).mpr hu
          have hx₀fix : U ⊓ fixV (Subgroup.zpowers x₀) = ⊥ := by
            rcases hfpf x₀ hxE with h | h
            · exact absurd h hxcent
            · exact h
          have hq_dvd : orderOf (2 : ZMod q) ∣ rk ↥U :=
            CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hV
              (isElemAbelian_zpowers (hE.2 x₀ hxE)).isPGroup hUinv hx₀fix
          have hp_dvd : orderOf (2 : ZMod p) ∣ rk ↥U :=
            CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hV hB hUB hfix
          have hℓdvd : ℓ ∣ rk ↥U := by
            rw [hℓ]; exact Nat.lcm_dvd hp_dvd hq_dvd
          have hle : ℓ ≤ rk ↥U := Nat.le_of_dvd hrkpos hℓdvd
          have hℓpos : 0 < ℓ := Nat.pos_of_dvd_of_pos hℓdvd hrkpos
          have hdivpos : 1 ≤ rk ↥U / ℓ := Nat.div_pos hle hℓpos
          have hqle : q ≤ q ^ (rk ↥U / ℓ) :=
            le_self_pow hq.one_lt.le (by omega)
          exact hbound.trans (Nat.mul_le_mul_right _ hqle)
  exact key (rk ↥U) E U rfl hE hBE hUB hUE hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
