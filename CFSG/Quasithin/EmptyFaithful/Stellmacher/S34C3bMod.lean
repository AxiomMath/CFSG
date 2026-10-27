module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Mod1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Mod2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

namespace C3b

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem isSwap_of_sq_of_not_alt (σ : Perm (Fin 5)) (h : σ * σ = 1)
    (ha : σ ∉ alternatingGroup (Fin 5)) : σ.IsSwap := by
  have key : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ ≠ 1 →
      ∃ x y : Fin 5, x ≠ y ∧ σ = swap x y := by
    decide +kernel
  exact key σ h (fun h1 => ha (Equiv.Perm.mem_alternatingGroup.mpr h1))

theorem IsSwap.ne_one' {t : Perm (Fin 5)} (ht : t.IsSwap) : t ≠ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := ht
  intro h
  have := congrArg (fun f : Perm (Fin 5) => f x) h
  simp at this
  exact hxy this.symm

theorem mem_oTwoRes_sup_of_alt' {δ : Geo H M} {θ : ↥(stab δ) →* Perm (Fin 5)}
    (hθ : Function.Surjective θ) (hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) {g : G}
    (hg : g ∈ stab δ) (hA : θ ⟨g, hg⟩ ∈ alternatingGroup (Fin 5)) :
    g ∈ oTwoRes (stab δ) ⊔ pCoreOf 2 (stab δ) :=
  mem_oTwoRes_sup_of_alt hθ hker hg hA

theorem overInv_of_alt {δ : Geo H M} {θ : ↥(stab δ) →* Perm (Fin 5)}
    (hθ : Function.Surjective θ) (hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ)
    {g : ↥(stab δ)} (hA : θ g ∈ alternatingGroup (Fin 5)) (h1 : θ g ≠ 1)
    (h23 : θ g ^ 2 = 1 ∨ θ g ^ 3 = 1) : OverInv δ (g : G) := by
  refine ⟨mem_oTwoRes_sup_of_alt' hθ hker g.2 hA, fun h => h1 ((hker g).mpr h), ?_⟩
  rcases h23 with h | h
  · left
    exact (hker (g ^ 2)).mp (by rw [map_pow]; exact h)
  · right
    exact (hker (g ^ 3)).mp (by rw [map_pow]; exact h)

structure C3Data (δ μ : Geo H M) where
  θ : ↥(stab δ) →* Perm (Fin 5)
  surj : Function.Surjective θ
  sec : IsSec (stab δ) (Cb δ) (Vn δ)
  ker_le : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ)
  ker_iff : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ
  map_syl : ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ = S5Syl
  shape1 : ShapeMod1 (secModule sec θ surj ker_le)
  shape2 : ShapeMod2 (secModule sec θ surj ker_le)

theorem nonempty_c3Data (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') {μ : Geo H M} (hμ : μ ∈ nbrs δ) : Nonempty (C3Data δ μ) := by
  have hδ := hp.vδ
  obtain ⟨θ, hθ, hs, hk, hker, hPS, -, hfix, hnt, hgen⟩ := exists_vmodel hG hδ hμ
  have hrk : ∀ g : ↥(stab δ), rk δ (g : G) = idx (secModule hs θ hθ hk) (θ g) := fun g =>
    rk_eq_idx hG hδ hθ hs hk hker g.2
  have hCE : CEMod (secModule hs θ hθ hk) :=
    { nt := hnt
      fix := hfix
      gen := hgen
      red := fun h => hng δ hδ ((good_iff_iso hG hδ hθ hs hk hker).mpr h)
      big := fun d hdA hd1 hd23 => by
        obtain ⟨g, rfl⟩ := hθ d
        rw [← hrk]
        exact NG.rk_gt hG hirr hng hδ g.2
          (overInv_of_alt hθ hker hdA hd1 (by simpa using hd23))
      swap4 := fun t ht => by
        obtain ⟨g, rfl⟩ := hθ t
        rw [← hrk]
        refine NG.four_le_rk hG h15 hng hδ g.2 fun hgQ => IsSwap.ne_one' ht ((hker g).mpr hgQ)
      small := by
        obtain ⟨-, hnle, -⟩ := case3_data hG hirr h15 hng hp
        obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp hnle
        have hyS : y ∈ stab δ := (pd_Vn_le_stab hG hp).2 hyV
        have hy2 : (⟨y, hyS⟩ : ↥(stab δ)) * ⟨y, hyS⟩ = 1 := by
          have := (isElemAbelian_Vn' hG δ').2 y hyV
          exact Subtype.ext (by simpa [pow_two] using this)
        have hr4 := (c3_rk_le_four hG hirr h15 hng hp).1 y hyV
        have hnA : θ ⟨y, hyS⟩ ∉ alternatingGroup (Fin 5) := fun hA => by
          have hov : OverInv δ y := by
            refine ⟨mem_oTwoRes_sup_of_alt' hθ hker hyS hA, hyQ, Or.inl ?_⟩
            exact (hker ⟨y ^ 2, (stab δ).pow_mem hyS 2⟩).mp
              (by simpa [pow_two] using congrArg θ hy2)
          have := NG.rk_gt hG hirr hng hδ hyS hov
          omega
        refine ⟨θ ⟨y, hyS⟩, isSwap_of_sq_of_not_alt _ ?_ hnA, ?_⟩
        · rw [← map_mul, hy2, map_one]
        · rw [← hrk ⟨y, hyS⟩]; exact hr4 }
  have h1 := shapeMod1_of_CEMod hCE
  exact ⟨⟨θ, hθ, hs, hk, hker, hPS, h1, shapeMod2_of_CEMod hCE h1⟩⟩

end C3b

end S34

end F53.Stellmacher

end CFSG.Quasithin
