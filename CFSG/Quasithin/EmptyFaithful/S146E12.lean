module

public import CFSG.Quasithin.EmptyFaithful.S146E11
public import CFSG.Quasithin.EmptyFaithful.S146E10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Four

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.mem_T_of_commutator_mem (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x v : G}
    (hxH : x ∈ mcOf T) (hv : v ∈ VZ T M) (hvZ : v ∉ Zz) (hxv : x * v * x⁻¹ * v⁻¹ ∈ Zz) :
    x ∈ T := by
  have hVcard : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hZcard : Nat.card Zz = 2 := S.card_Z
  have hZV : Zz ≤ VZ T M := le_conjClosure _ _
  have hcent : ∀ h ∈ mcOf T, ∀ z ∈ Zz, h * z * h⁻¹ = z := fun h hh z hz => by
    have := S146T.comm_Z hh hz
    calc h * z * h⁻¹ = (h * z) * h⁻¹ := rfl
      _ = (z * h) * h⁻¹ := by rw [← this]
      _ = z := by group
  have hle : conjSub x (VZ T M) ≤ VZ T M := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ VZ T M, y = x * w * x⁻¹ :=
      ⟨x⁻¹ * y * x, mem_conjSub.mp hy, by group⟩
    by_cases hwZ : w ∈ Zz
    · rw [hcent x hxH w hwZ]
      exact hZV hwZ
    · have hz : v⁻¹ * w ∈ Zz := inv_mul_mem_of_card_four hZV hVcard hZcard hv hw hvZ hwZ
      have e : x * w * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v * (v⁻¹ * w) := by
        calc x * w * x⁻¹ = (x * v * x⁻¹) * (x * (v⁻¹ * w) * x⁻¹) := by group
          _ = (x * v * x⁻¹) * (v⁻¹ * w) := by rw [hcent x hxH _ hz]
          _ = (x * v * x⁻¹ * v⁻¹) * v * (v⁻¹ * w) := by group
      rw [e]
      exact (VZ T M).mul_mem ((VZ T M).mul_mem (hZV hxv) hv) (hZV hz)
  have hxN : x ∈ Subgroup.normalizer ((VZ T M : Subgroup G) : Set G) :=
    mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_conjSub_eq]))
  have hVN : Subgroup.normalizer ((VZ T M : Subgroup G) : Set G) = M := S.hyp1281.normalizer_VZ
  have hxM : x ∈ M := by
    rw [← hVN]
    exact hxN
  have hT : T = M ⊓ mcOf T := c.hc23.2.1.2
  rw [hT]
  exact ⟨hxM, hxH⟩

theorem not_mem_tZero_of_orderOf_three (S : Setting146 G T M) {p : G} (hp : orderOf p = 3) :
    p ∉ tZero T u := by
  intro h
  have hT₀T : tZero T u ≤ T := centralizerMod_le_left _ _ _
  have hT₀p : IsPGroup 2 (tZero T u) := S.hyp.sylow.1.to_le hT₀T
  obtain ⟨k, hk⟩ := hT₀p ⟨p, h⟩
  have h1 : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := hp ▸ orderOf_dvd_of_pow_eq_one h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem FCtx.inv_mul_conj_mem (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {v : G}
    (hv : v ∈ VZ T M) (hvZ : v ∉ Zz) {h : G}
    (hh : h ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u)) :
    u⁻¹ * (h * v * h⁻¹) ∈ uxOf T M U₂ := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hZX : Zz ≤ uxOf T M U₂ := c.hZU₂.trans le_sup_left
  have hUXU : uxOf T M U₂ ≤ uOfL22 T M := sup_le c.hU₂U (cuOf_le T M)
  have hVU : VZ T M ≤ uOfL22 T M := le_conjClosure _ _
  have hhH : h ∈ mcOf T := centralizerMod_le_left _ _ _ hh
  have huH : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (c.hU₁U c.huU)
  have hhU₁ : h ∈ Subgroup.normalizer (U₁ : Set G) :=
    c.hSec.mem_normalizer_of_mem_centralizerMod c.hKn c.huU c.huZ hh
  have hhX : h ∈ Subgroup.normalizer ((uxOf T M U₂ : Subgroup G) : Set G) :=
    c.mem_normalizer_of_mem S (c.le_normalizer_uxOf S) hZX hUXU hhH hhU₁
  have hcent : ∀ g ∈ mcOf T, ∀ z ∈ Zz, g * z * g⁻¹ = z := fun g hg z hz => by
    have := S146T.comm_Z hg hz
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have hcent' : ∀ g ∈ mcOf T, ∀ z ∈ Zz, g⁻¹ * z * g = z := fun g hg z hz => by
    have := hcent g⁻¹ ((mcOf T).inv_mem hg) z hz
    simpa using this
  obtain ⟨y₁, hy₁, r, hr, hvyr⟩ := c.exists_decomp S (hVU hv)
  have hz0 : u⁻¹ * y₁ ∈ Zz := c.inv_mul_mem_of_decomp S hv hvZ hy₁ hr hvyr
  have hw : h * u * h⁻¹ * u⁻¹ ∈ Zz := hh.2.2 u (Subgroup.mem_zpowers u)
  have hrh : h * r * h⁻¹ ∈ uxOf T M U₂ := (Subgroup.mem_normalizer_iff.mp hhX r).mp hr
  have e1 : u⁻¹ * (h * y₁ * h⁻¹) =
      (u⁻¹ * (h * u * h⁻¹ * u⁻¹) * u) * (h * (u⁻¹ * y₁) * h⁻¹) := by group
  have hA : u⁻¹ * (h * y₁ * h⁻¹) ∈ Zz := by
    rw [e1, hcent h hhH _ hz0, hcent' u huH _ hw]
    exact (quasithinOmegaOneCenter T).mul_mem hw hz0
  have e2 : u⁻¹ * (h * v * h⁻¹) = (u⁻¹ * (h * y₁ * h⁻¹)) * (h * r * h⁻¹) := by
    rw [hvyr]
    group
  rw [e2]
  exact (uxOf T M U₂).mul_mem (hZX hA) hrh

theorem FCtx.card_conjClosure_oTwoUpper (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u)
    (e : OTwoQuot (centralizerMod Zz (mcOf T) (Subgroup.zpowers u)) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (conjClosure (VZ T M)
      (oTwoUpper (centralizerMod Zz (mcOf T) (Subgroup.zpowers u)))) = 2 ^ 4 := by
  classical
  set H₂ := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hH₂
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hVcard : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hZcard : Nat.card Zz = 2 := S.card_Z
  have hZV : Zz ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ uOfL22 T M := le_conjClosure _ _
  have hZX : Zz ≤ uxOf T M U₂ := c.hZU₂.trans le_sup_left
  have hUXU : uxOf T M U₂ ≤ uOfL22 T M := sup_le c.hU₂U (cuOf_le T M)
  have hG₁U : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hH₂H : H₂ ≤ mcOf T := centralizerMod_le_left _ _ _
  have hcent : ∀ g ∈ mcOf T, ∀ z ∈ Zz, g * z * g⁻¹ = z := fun g hg z hz => by
    have := S146T.comm_Z hg hz
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have hcent' : ∀ g ∈ mcOf T, ∀ z ∈ Zz, g⁻¹ * z * g = z := fun g hg z hz => by
    have := hcent g⁻¹ ((mcOf T).inv_mem hg) z hz
    simpa using this
  obtain ⟨p, hpX, hp3, hcos⟩ := c.exists_coset_rep S e
  have hp3' : p ^ 3 = 1 := by rw [← hp3]; exact pow_orderOf_eq_one p
  have hpH : p ∈ mcOf T := hH₂H hpX
  have hpI : p ∈ oTwoUpper H₂ := mem_oTwoUpper_of_odd hpX (by rw [hp3]; exact ⟨1, rfl⟩)
  have hp2X : p ^ 2 ∈ H₂ := H₂.pow_mem hpX 2
  have hp2H : p ^ 2 ∈ mcOf T := hH₂H hp2X
  have hp2I : p ^ 2 ∈ oTwoUpper H₂ := (oTwoUpper H₂).pow_mem hpI 2
  have hpT₀ : p ∉ tZero T u := not_mem_tZero_of_orderOf_three S hp3
  have hp2T₀ : p ^ 2 ∉ tZero T u := fun h =>
    hpT₀ (mem_of_pow_mem_of_pow_three hp3' (k := 2) (by omega) h)
  obtain ⟨v, hv, hvZ⟩ := exists_mem_not_mem_of_card_four hVcard hZcard
  have hvH : v ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hVU hv)
  have hcomm_ne : ∀ x ∈ H₂, x ∉ tZero T u → x * v * x⁻¹ * v⁻¹ ∉ Zz := by
    intro x hx hxT₀ hxv
    exact hxT₀ ⟨c.mem_T_of_commutator_mem S (hH₂H hx) hv hvZ hxv, hx.2.1, hx.2.2⟩
  have hconj : ∀ x : G, v⁻¹ * (x * v * x⁻¹) ∈ Zz → x * v * x⁻¹ * v⁻¹ ∈ Zz := by
    intro x hx
    have e : x * v * x⁻¹ * v⁻¹ = v * (v⁻¹ * (x * v * x⁻¹)) * v⁻¹ := by group
    rw [e, hcent v hvH _ hx]
    exact hx
  have hab : v⁻¹ * (p * v * p⁻¹) ∉ Zz := fun h => hcomm_ne p hpX hpT₀ (hconj p h)
  have hac : v⁻¹ * (p ^ 2 * v * (p ^ 2)⁻¹) ∉ Zz := fun h =>
    hcomm_ne (p ^ 2) hp2X hp2T₀ (hconj (p ^ 2) h)
  have hbc : (p * v * p⁻¹)⁻¹ * (p ^ 2 * v * (p ^ 2)⁻¹) ∉ Zz := by
    intro h
    apply hab
    have e : v⁻¹ * (p * v * p⁻¹) = p⁻¹ * ((p * v * p⁻¹)⁻¹ * (p ^ 2 * v * (p ^ 2)⁻¹)) * p := by
      group
    rw [e, hcent' p hpH _ h]
    exact h
  have hua : u⁻¹ * v ∈ uxOf T M U₂ := by
    have := c.inv_mul_conj_mem S hv hvZ (h := 1) H₂.one_mem
    simpa using this
  have hub : u⁻¹ * (p * v * p⁻¹) ∈ uxOf T M U₂ := c.inv_mul_conj_mem S hv hvZ hpX
  have huc : u⁻¹ * (p ^ 2 * v * (p ^ 2)⁻¹) ∈ uxOf T M U₂ := c.inv_mul_conj_mem S hv hvZ hp2X
  have huX : u ∉ uxOf T M U₂ := fun h => c.huZ (c.inf_uxOf_le S ⟨c.huU, h⟩)
  have huU : u ∈ uOfL22 T M := c.hU₁U c.huU
  have hbU : p * v * p⁻¹ ∈ uOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (hG₁U hpH) v).mp (hVU hv)
  have hcU : p ^ 2 * v * (p ^ 2)⁻¹ ∈ uOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (hG₁U hp2H) v).mp (hVU hv)
  have hel : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hcard := card_sup_closure_three (fun x hx y hy => S.comm_of_mem_conjClosure hx hy)
    (fun x hx => by simpa [pow_two] using isElemAbelian_pow_eq_one hel hx) hZX hUXU hZcard huU huX
    (hVU hv) hbU hcU hua hub huc hab hac hbc
  have hsub : conjClosure (VZ T M) (oTwoUpper H₂) ≤
      Zz ⊔ Subgroup.closure ({v, p * v * p⁻¹, p ^ 2 * v * (p ^ 2)⁻¹} : Set G) := by
    refine conjClosure_le fun h hh w hw => ?_
    have hhX : h ∈ H₂ := oTwoUpper_le H₂ hh
    have hhH : h ∈ mcOf T := hH₂H hhX
    obtain ⟨n, hn, ht⟩ := hcos h hhX
    obtain ⟨t, htT₀, hht⟩ : ∃ t ∈ tZero T u, h = p ^ n * t := ⟨(p ^ n)⁻¹ * h, ht, by group⟩
    subst hht
    have htT : t ∈ T := htT₀.1
    have hpn : p ^ n ∈ mcOf T := (mcOf T).pow_mem hpH n
    by_cases hwZ : w ∈ Zz
    · rw [hcent _ hhH w hwZ]
      exact Subgroup.mem_sup_left hwZ
    · have hz : v⁻¹ * w ∈ Zz := inv_mul_mem_of_card_four hZV hVcard hZcard hv hw hvZ hwZ
      have hz₁ : t * v * t⁻¹ * v⁻¹ ∈ Zz := S.commutator_VZ_mem (hTM htT) (hTH htT) hv
      have e : p ^ n * t * w * (p ^ n * t)⁻¹ =
          (p ^ n * (t * v * t⁻¹ * v⁻¹) * (p ^ n)⁻¹) * (p ^ n * v * (p ^ n)⁻¹) *
            (p ^ n * t * (v⁻¹ * w) * (p ^ n * t)⁻¹) := by group
      rw [e, hcent (p ^ n) hpn _ hz₁, hcent (p ^ n * t) hhH _ hz]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hz₁) ?_)
        (Subgroup.mem_sup_left hz)
      apply Subgroup.mem_sup_right
      apply Subgroup.subset_closure
      have hn3 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hn3 with rfl | rfl | rfl <;> simp
  have hsup : Zz ⊔ Subgroup.closure ({v, p * v * p⁻¹, p ^ 2 * v * (p ^ 2)⁻¹} : Set G) ≤
      conjClosure (VZ T M) (oTwoUpper H₂) := by
    refine sup_le (hZV.trans (le_conjClosure _ _)) ?_
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact le_conjClosure _ _ hv
    · exact mem_conjClosure hpI hv
    · exact mem_conjClosure hp2I hv
  rw [le_antisymm hsub hsup, hcard]
  norm_num

end Four

theorem stage146FFour_proof : Stage146FFour := by
  intro G _ _ T M S hB K U₁ U₂ s u hd
  obtain ⟨e⟩ := stage146FH2S3_proof G T M S hB K U₁ U₂ s u hd
  exact (FCtx.ofBData S hd).card_conjClosure_oTwoUpper S e

end CFSG.Quasithin
