module

public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Background.E2Thirteen

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem relIndex_sup_eq {D T : Subgroup G} (hT : T ≤ Subgroup.normalizer (D : Set G)) :
    D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

@[expose] def cenMod (N R V : Subgroup G) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) : Subgroup G where
  carrier := {n | n ∈ N ∧ ∀ r ∈ R, n * r * n⁻¹ * r⁻¹ ∈ V}
  one_mem' := ⟨N.one_mem, fun r _ => by simp⟩
  mul_mem' := by
    rintro n n' ⟨hn, hnV⟩ ⟨hn', hn'V⟩
    refine ⟨N.mul_mem hn hn', fun r hr => ?_⟩
    have h1 := hn'V r hr
    have h2 := hnV r hr
    have e : n * n' * r * (n * n')⁻¹ * r⁻¹ =
        (n * (n' * r * n'⁻¹ * r⁻¹) * n⁻¹) * (n * r * n⁻¹ * r⁻¹) := by group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNV hn) _).mp h1) h2
  inv_mem' := by
    rintro n ⟨hn, hnV⟩
    refine ⟨N.inv_mem hn, fun r hr => ?_⟩
    have hr' : n⁻¹ * r * n ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hNR (N.inv_mem hn)) r).mp hr
    have h1 := hnV _ hr'
    have e : n⁻¹ * r * n⁻¹⁻¹ * r⁻¹ = (n * (n⁻¹ * r * n) * n⁻¹ * (n⁻¹ * r * n)⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem h1

variable {N R V : Subgroup G} {hNV : N ≤ Subgroup.normalizer (V : Set G)}
  {hNR : N ≤ Subgroup.normalizer (R : Set G)}

theorem cenMod_le : cenMod N R V hNV hNR ≤ N := fun _ h => h.1

theorem conj_mem_cenMod {g n : G} (hg : g ∈ N) (hn : n ∈ cenMod N R V hNV hNR) :
    g * n * g⁻¹ ∈ cenMod N R V hNV hNR := by
  obtain ⟨hnN, hnV⟩ := hn
  refine ⟨N.mul_mem (N.mul_mem hg hnN) (N.inv_mem hg), fun r hr => ?_⟩
  have hr' : g⁻¹ * r * g ∈ R := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hNR (N.inv_mem hg)) r).mp hr
  have h1 := hnV _ hr'
  have e : g * n * g⁻¹ * r * (g * n * g⁻¹)⁻¹ * r⁻¹ =
      g * (n * (g⁻¹ * r * g) * n⁻¹ * (g⁻¹ * r * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hNV hg) _).mp h1

theorem le_normalizer_cenMod : N ≤ Subgroup.normalizer (cenMod N R V hNV hNR : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => conj_mem_cenMod hg hn, fun hn => ?_⟩
  have := conj_mem_cenMod (N.inv_mem hg) hn
  simpa [mul_assoc] using this

theorem eq_one_of_odd_of_cenMod [Finite G] (hpN : pCoreOf 2 N = R) (hch : CharTwo N)
    (hR2 : IsPGroup 2 R) (hV2 : ∀ v ∈ V, v * v = 1) {y : G}
    (hy : y ∈ cenMod N R V hNV hNR) (hyC : y ∈ Subgroup.centralizer (V : Set G))
    (hodd : Odd (orderOf y)) : y = 1 := by
  have hyR : y ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨v, hv⟩ : ∃ v, v = y * r * y⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have hvV : v ∈ V := hv ▸ hy.2 r hr
    have hyv : ∀ j : ℕ, y * v ^ j * y⁻¹ = v ^ j := by
      intro j
      have hc := Subgroup.mem_centralizer_iff.mp hyC (v ^ j) (V.pow_mem hvV j)
      rw [← hc]
      group
    have hyr : y * r * y⁻¹ = v * r := by rw [hv]; group
    have hpow : ∀ j : ℕ, y ^ j * r * (y ^ j)⁻¹ = v ^ j * r := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have e : y ^ (j + 1) * r * (y ^ (j + 1))⁻¹ = y * (y ^ j * r * (y ^ j)⁻¹) * y⁻¹ := by
          rw [pow_succ']
          group
        have e2 : y * (v ^ j * r) * y⁻¹ = (y * v ^ j * y⁻¹) * (y * r * y⁻¹) := by group
        rw [e, ih, e2, hyv j, hyr, pow_succ, mul_assoc]
    have h1 := hpow (orderOf y)
    rw [pow_orderOf_eq_one] at h1
    have h2 : v ^ orderOf y = 1 := by
      have : v ^ orderOf y * r = 1 * r := by rw [← h1]; group
      simpa using this
    obtain ⟨m, hm⟩ := hodd
    have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hV2 v hvV
    have hv1 : v = 1 := by
      rw [hm, pow_succ, pow_mul, hv2, one_pow, one_mul] at h2
      exact h2
    have : y * r * y⁻¹ * r⁻¹ = 1 := by rw [← hv]; exact hv1
    calc r * y = (y * r * y⁻¹ * r⁻¹)⁻¹ * (y * r) := by group
      _ = y * r := by rw [this]; group
  have hyN : y ∈ N := hy.1
  have hyR' : y ∈ R := by
    rw [← hpN]
    exact hch ⟨hyN, by rwa [hpN]⟩
  obtain ⟨k, hk⟩ := hR2 ⟨y, hyR'⟩
  exact E2.eq_one_of_odd_orderOf_of_pow_two_pow hodd (k := k)
    (by simpa using congrArg Subtype.val hk)

theorem mem_normalizer_centralizer {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ x ∈ Subgroup.centralizer (V : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        g⁻¹ * x * g ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    constructor
    · intro v hv
      have h1 : g⁻¹ * v * g ∈ V := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
      have h2 := hx _ h1
      calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
        _ = g * x * g⁻¹ * v := by group
    · intro v hv
      have h1 : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
      have h2 := hx _ h1
      calc v * (g⁻¹ * x * g) = g⁻¹ * ((g * v * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * v * g⁻¹)) * g := by rw [h2]
        _ = g⁻¹ * x * g * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => (key x hx).1, fun hx => ?_⟩
  have := (key _ hx).2
  simpa [mul_assoc] using this

theorem isPGroup_cenMod_inf [Finite G] (hpN : pCoreOf 2 N = R) (hch : CharTwo N)
    (hR2 : IsPGroup 2 R) (hV2 : ∀ v ∈ V, v * v = 1) :
    IsPGroup 2 ↥(cenMod N R V hNV hNR ⊓ Subgroup.centralizer (V : Set G)) := by
  intro ⟨y, hy⟩
  obtain ⟨a, b, hyab, ha, hb, ⟨k, hk⟩, hbo⟩ := E2.exists_two_part_odd_part y
  have hbA : b ∈ cenMod N R V hNV hNR ⊓ Subgroup.centralizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hy) hb
  have hb1 : b = 1 := eq_one_of_odd_of_cenMod hpN hch hR2 hV2 hbA.1 hbA.2 hbo
  refine ⟨k, Subtype.ext ?_⟩
  have : y = a := by rw [hyab, hb1, one_mul]
  simpa [this] using hk

theorem le_normalizer_cenMod_inf :
    N ≤ Subgroup.normalizer
      ((cenMod N R V hNV hNR ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have h1 := le_normalizer_cenMod (hNV := hNV) (hNR := hNR) hg
  have h3 := mem_normalizer_centralizer (hNV hg)
  rw [Subgroup.mem_normalizer_iff] at h1 h3 ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [h1 x, h3 x]

theorem cenMod_inf_le [Finite G] (hpN : pCoreOf 2 N = R) (hch : CharTwo N)
    (hR2 : IsPGroup 2 R) (hV2 : ∀ v ∈ V, v * v = 1) :
    cenMod N R V hNV hNR ⊓ Subgroup.centralizer (V : Set G) ≤ R := by
  have h2 := isPGroup_cenMod_inf (hNV := hNV) (hNR := hNR) hpN hch hR2 hV2
  have hle : cenMod N R V hNV hNR ⊓ Subgroup.centralizer (V : Set G) ≤ N :=
    inf_le_left.trans cenMod_le
  have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
    (le_normalizer_cenMod_inf (hNV := hNV) (hNR := hNR)) h2
  rwa [hpN] at this

end Y15111

end CFSG.Quasithin
