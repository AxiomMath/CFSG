module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Sec7
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Transport

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

omit [Finite G] in
theorem wParam_conj (T V : Subgroup G) (g : G) :
    wParam (conjSubgroup T g) (conjSubgroup V g) = wParam T V := by
  unfold wParam
  have hset : {j : ℕ | ¬ wClos (conjSubgroup V g) j (conjSubgroup T g) ≤
        conjSubgroup T g ⊓ Subgroup.centralizer ((conjSubgroup V g : Subgroup G) : Set G)} =
      {j : ℕ | ¬ wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)} := by
    ext j
    simp only [Set.mem_ofPred_eq]
    rw [wClos_conjV, wClos_conj, ← conjSubgroup_centralizer, ← conjSubgroup_inf,
      conjSubgroup_le_conjSubgroup_iff]
  rw [hset]

omit [Finite G] in
theorem hypE322_conj {T V : Subgroup G} (h : HypE322 T V) (g : G) :
    HypE322 (conjSubgroup T g) (conjSubgroup V g) where
  sylow := by
    have h1 := (E1.isSylowIn_conj_iff (p := 2) g⁻¹ (P := T) (H := ⊤)).2 h.sylow
    rw [← conjSubgroup_eq_conjSub, ← conjSubgroup_eq_conjSub, conjSubgroup_top] at h1
    exact h1
  le := conjSubgroup_mono_left g h.le
  normal := by
    rw [← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left g h.normal

end Transport

section PRank

variable {M M' : Type*} [Group M] [Finite M] [Group M'] [Finite M']

theorem pRank_le_pRank_map (f : M →* M') (hf : Function.Injective f) {p : ℕ} (hp : p.Prime)
    (X : Subgroup M) : CFSG.Open.pRank p X ≤ CFSG.Open.pRank p (X.map f) := by
  unfold CFSG.Open.pRank
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEX, hE, hk⟩ := hk
  exact le_pRank hp (Subgroup.map_mono hEX) (E1.isElemAbelian_map' f hE)
    (by rw [Subgroup.card_map_of_injective hf, hk])

theorem pRank_map_mulEquiv' (e : M ≃* M') {p : ℕ} (hp : p.Prime) (X : Subgroup M) :
    CFSG.Open.pRank p (X.map e.toMonoidHom) = CFSG.Open.pRank p X := by
  refine le_antisymm ?_ (pRank_le_pRank_map e.toMonoidHom e.injective hp X)
  have h := pRank_le_pRank_map e.symm.toMonoidHom e.symm.injective hp (X.map e.toMonoidHom)
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id M := by
    ext x
    simp
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h

end PRank

section PRankAut

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem pRank_autI_conj (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) :
    CFSG.Open.pRank 2 (autI hVg ⊤) = CFSG.Open.pRank 2 (autI hV ⊤) := by
  rw [autI_top_conj hV g hVg]
  exact pRank_map_mulEquiv' (MulAut.congr (conjMod hV g hVg)) Nat.prime_two _

end PRankAut

section FF

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem isFFModule_map_congr (φ : W ≃* W') {X : Subgroup (MulAut W)} (h : IsFFModule X) :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) := by
  obtain ⟨A, hAX, hA1, hAab, hcard⟩ := h
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  refine ⟨A.map (MulAut.congr φ).toMonoidHom, Subgroup.map_mono hAX, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact hA1 ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAab.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAab.2 a ha, map_one]
  · rw [fixV_map_congr, Subgroup.card_map_of_injective hinj,
      Subgroup.card_map_of_injective φ.injective, Nat.card_congr φ.toEquiv.symm]
    exact hcard

theorem isFFModule_map_congr_iff (φ : W ≃* W') {X : Subgroup (MulAut W)} :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) ↔ IsFFModule X := by
  refine ⟨fun h => ?_, isFFModule_map_congr φ⟩
  have h' := isFFModule_map_congr φ.symm h
  have hcomp : (MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h'

end FF

section HypConj

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem isFFModule_autI_conj (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) :
    IsFFModule (autI hVg ⊤) ↔ IsFFModule (autI hV ⊤) := by
  rw [autI_top_conj hV g hVg]
  exact isFFModule_map_congr_iff _

theorem hypE324_conj {T : Subgroup G} (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) (h : HypE324 T V hV) :
    HypE324 (conjSubgroup T g) (conjSubgroup V g) hVg := by
  unfold HypE324 at h ⊢
  rw [wParam_conj, isFFModule_autI_conj hV g hVg]
  exact h

end HypConj

end E3

end CFSG.Quasithin
