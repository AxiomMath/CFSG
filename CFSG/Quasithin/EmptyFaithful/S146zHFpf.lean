module

public import CFSG.Quasithin.EmptyFaithful.S14612EF
public import CFSG.Quasithin.EmptyFaithful.S146zHCls

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Split

theorem split_hom' {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (ρ : Hh →* MulAut W) (P0 T0 : Subgroup Hh) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hPn : P0.Normal) (hpp : ∀ x ∈ P0, ∃ k : ℕ, ρ (x ^ q ^ k) = 1)
    (hHeq : P0 ⊔ T0 = ⊤) {w₀ : W} (hw₀ : ∀ t ∈ T0, ρ t w₀ = w₀)
    (hgen : Subgroup.closure {w | ∃ h : Hh, w = ρ h w₀} = ⊤) :
    kOf ρ = commV (P0.map ρ) ∧ commV (P0.map ρ) ⊓ fixV (P0.map ρ) = ⊥ := by
  classical
  set X : Subgroup (MulAut W) := ρ.range with hX
  set P : Subgroup (MulAut W) := P0.map ρ with hP
  set Tb : Subgroup (MulAut W) := T0.map ρ with hTb
  have hPX : P ≤ X := Subgroup.map_le_range ρ P0
  have hXeq : X = P ⊔ Tb := by
    rw [hX, hP, hTb, MonoidHom.range_eq_map, ← hHeq, Subgroup.map_sup]
  have hPn' : NormalIn X P := by
    rintro _ ⟨h, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨h * a * h⁻¹, hPn.conj_mem a ha h, by simp⟩
  have hPodd : Odd (Nat.card P) := by
    have : Fact q.Prime := ⟨hq⟩
    have hpg : IsPGroup q ↥P := by
      rintro ⟨x, a, ha, rfl⟩
      obtain ⟨k, hk⟩ := hpp a ha
      exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hpg
    rw [hn]
    exact Odd.pow (hq.eq_two_or_odd'.resolve_left hq2)
  have hv : w₀ ∈ fixV Tb := by
    rintro _ ⟨t, ht, rfl⟩
    exact hw₀ t ht
  have hgen' : Subgroup.closure {w | ∃ x ∈ X, w = x w₀} = ⊤ := by
    rw [← hgen]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, hw⟩
      exact ⟨h, hw⟩
    · rintro ⟨h, hw⟩
      exact ⟨ρ h, ⟨h, rfl⟩, hw⟩
  obtain ⟨v', hv', c, hc, hvv, hv'T, hcommX, hsup, hinf, hK⟩ :=
    exists_split14612 hW hPodd hPn' hPX hXeq hv hgen'
  exact ⟨hcommX, commV_inf_fixV_eq_bot hW hPodd⟩

end Split

section Cfp

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem clsU_mem_kOf {T V L V₁ Vp : Subgroup G} (h : HypF91 T V L V₁ Vp H) {k : G}
    (hk : k ∈ ⁅conjClosure Vp H, H⁆) :
    clsU h (S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure Vp H) hk) ∈
      kOf (rhoH h) := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure _ _
  have huK_le : ⁅conjClosure Vp H, H⁆ ≤ conjClosure Vp H :=
    S145.commutator_le_of_le_normalizer hHU
  refine Subgroup.closure_induction
    (p := fun g (hg : g ∈ ⁅conjClosure Vp H, H⁆) => clsU h (huK_le hg) ∈ kOf (rhoH h))
    ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    have hyx : y * x⁻¹ * y⁻¹ ∈ conjClosure Vp H := conj_mem_UH hy ((conjClosure Vp H).inv_mem hx)
    have e : clsU h (huK_le (Subgroup.commutator_mem_commutator hx hy)) =
        (rhoH h ⟨y, hy⟩ (clsU h hx) * (clsU h hx)⁻¹)⁻¹ := by
      have h1 : rhoH h ⟨y, hy⟩ (clsU h ((conjClosure Vp H).inv_mem hx)) = clsU h hyx :=
        rhoH_clsU h ⟨y, hy⟩ ((conjClosure Vp H).inv_mem hx)
      calc clsU h (huK_le (Subgroup.commutator_mem_commutator hx hy))
          = clsU h ((conjClosure Vp H).mul_mem hx hyx) :=
            clsU_congr h _ _ (by simp only [commutatorElement_def]; group)
        _ = clsU h hx * clsU h hyx := (clsU_mul h hx hyx).symm
        _ = clsU h hx * (rhoH h ⟨y, hy⟩ (clsU h hx))⁻¹ := by
            rw [← h1, ← clsU_inv h hx, map_inv]
        _ = (rhoH h ⟨y, hy⟩ (clsU h hx) * (clsU h hx)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [e]
    exact (kOf (rhoH h)).inv_mem
      (Subgroup.subset_closure ⟨rhoH h ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, clsU h hx, rfl⟩)
  · exact (clsU_one h) ▸ (kOf (rhoH h)).one_mem
  · intro a b ha hb ka kb
    rw [← clsU_mul h (huK_le ha) (huK_le hb)] at *
    exact (kOf (rhoH h)).mul_mem ka kb
  · intro a ha ka
    rw [← clsU_inv h (huK_le ha)]
    exact (kOf (rhoH h)).inv_mem ka

theorem Setting146.cfpMod (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    ∀ w ∈ kOf (rhoH h), (∀ y : ↥H, (y : G) ∈ PQ → rhoH h y w = w) → w = 1 := by
  classical
  intro w hwK hfix
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hPQH : PQ ≤ H := hred.le
  have hker : ∀ x : ↥H, rhoH h x = 1 ↔ (x : G) ∈ pCoreOf 2 H := rhoH_eq_one_iff h
  have hPQn : (PQ.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPQH).mpr hred.normal
  have hHeq : PQ.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPQH hTH, ← hred.eq, Subgroup.subgroupOf_self]
  have hpp : ∀ x ∈ PQ.subgroupOf H, ∃ k : ℕ, rhoH h (x ^ p ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hred.pSec (x : G) (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨k, (hker _).mpr (by simpa using hk)⟩
  obtain ⟨w₀, hw₀, hgen⟩ := exists_gen_vector S h
  have hw₀' : ∀ t ∈ T.subgroupOf H, rhoH h t w₀ = w₀ :=
    fun t ht => hw₀ t (Subgroup.mem_subgroupOf.mp ht)
  obtain ⟨hK, hinf⟩ := split_hom' IntMod.sq_eq_one (rhoH h) (PQ.subgroupOf H) (T.subgroupOf H)
    hred.prime hred.odd hPQn hpp hHeq hw₀' hgen
  have hwfix : w ∈ fixV (Subgroup.map (rhoH h) (PQ.subgroupOf H)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfix y (Subgroup.mem_subgroupOf.mp hy)
  have hw1 : w ∈ commV (Subgroup.map (rhoH h) (PQ.subgroupOf H)) ⊓
      fixV (Subgroup.map (rhoH h) (PQ.subgroupOf H)) := ⟨hK ▸ hwK, hwfix⟩
  rw [hinf, Subgroup.mem_bot] at hw1
  exact hw1

end Cfp

end CFSG.Quasithin
