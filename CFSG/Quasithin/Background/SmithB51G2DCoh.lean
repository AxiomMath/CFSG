module

public import CFSG.Quasithin.Background.SmithB51G2DOct
public import CFSG.Quasithin.Background.JonesParshallG2TwoH1
public import CFSG.Quasithin.Background.JonesParshallG2H1
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.Quasithin.Background.B5FinOut

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open
open scoped Matrix

theorem eq_zero_of_vanish_normal {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    {μ : G →* AddMonoid.End M} {h : G → M} (hh : h ∈ Z1A μ) {N : Subgroup G} [N.Normal]
    (hN : ∀ n ∈ N, h n = 0) (hfix : ∀ m : M, (∀ n ∈ N, μ n m = m) → m = 0) : h = 0 := by
  funext g
  refine hfix _ fun n hn => ?_
  have hn' : g⁻¹ * n * g ∈ N := by
    have := Subgroup.Normal.conj_mem ‹N.Normal› n hn g⁻¹
    simpa using this
  have h1 := hh n g
  have h2 := hh g (g⁻¹ * n * g)
  rw [hN n hn, zero_add] at h1
  rw [hN _ hn', map_zero, add_zero, show g * (g⁻¹ * n * g) = n * g by group] at h2
  rw [← h1, h2]

section Two


theorem mem_subG2_iff (g : ↥(cayleyGroup (ZMod 2))) :
    (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) ∈ subG2 ↔
      g ∈ commutator ↥(cayleyGroup (ZMod 2)) := by
  rw [← g2Two_commutator_eq, ← Subgroup.map_subtype_commutator]
  constructor
  · rintro ⟨g', hg', hgg⟩
    rw [Subtype.ext hgg] at hg'
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem eq_zero_of_fix_subG2 (m : Ix3 → ZMod 2)
    (hm : ∀ n ∈ commutator ↥(cayleyGroup (ZMod 2)), g2Act n m = m) : m = 0 := by
  have hA : matA6 *ᵥ m = m := by
    have h1 := hm (Subgroup.inclusion subG2_le (gensK 0))
      ((mem_subG2_iff _).1 (gensK 0).2)
    rw [← muK_gens0]
    exact h1
  have hB : matB6 *ᵥ m = m := by
    have h1 := hm (Subgroup.inclusion subG2_le (gensK 1))
      ((mem_subG2_iff _).1 (gensK 1).2)
    rw [← muK_gens1]
    exact h1
  have key : ∀ m : Ix3 → ZMod 2, matA6 *ᵥ m = m → matB6 *ᵥ m = m → m = 0 := by decide
  exact key m hA hB

theorem exists_sub_fG_mem_B1A_two {f : ↥(cayleyGroup (ZMod 2)) → (Ix3 → ZMod 2)}
    (hf : f ∈ Z1A (g2Act (F := ZMod 2))) :
    ∃ α : ZMod 2, f - α • fG ∈ B1A (g2Act (F := ZMod 2)) := by
  have hfK : f ∘ Subgroup.inclusion subG2_le ∈ Z1A muK := Z1A_comp _ hf
  have hvan : ∀ (α : ZMod 2) (w : Ix3 → ZMod 2),
      (∀ n : ↥subG2, f (Subgroup.inclusion subG2_le n) - α • cocK n = muK n w - w) →
      f - α • fG ∈ B1A (g2Act (F := ZMod 2)) := by
    intro α w hw
    have hh : f - α • fG - coboundaryA g2Act w ∈ Z1A (g2Act (F := ZMod 2)) :=
      sub_mem (sub_mem hf (smul_fG_mem α)) (B1A_le_Z1A _ ⟨w, rfl⟩)
    have hzero := eq_zero_of_vanish_normal (N := commutator ↥(cayleyGroup (ZMod 2))) hh
      (fun n hn => by
        obtain ⟨n', rfl⟩ : ∃ n' : ↥subG2, Subgroup.inclusion subG2_le n' = n :=
          ⟨⟨n, (mem_subG2_iff n).2 hn⟩, rfl⟩
        have h1 := hw n'
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [show fG (Subgroup.inclusion subG2_le n') = cocK n' from rfl, h1]
        exact sub_self _)
      eq_zero_of_fix_subG2
    exact ⟨w, (sub_eq_zero.1 hzero).symm⟩
  rcases Z1A_K_cases hfK with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine ⟨0, hvan 0 w fun n => ?_⟩
    have h1 := congrFun hw n
    rw [cobK_apply] at h1
    rw [h1]
    simp
  · refine ⟨1, hvan 1 w fun n => ?_⟩
    have h1 := congrFun hw n
    rw [cobK_apply] at h1
    simp only [one_smul]
    rw [h1]
    rfl

end Two

section Transport

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem zornMap_zE' (e : K ≃+* ZMod 2) : zornMap e (zE' K) = zE' (ZMod 2) := by
  simp only [zornMap, zE', zmk]
  refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ (by simp))) <;> funext i <;>
    fin_cases i <;> simp

omit [CharP K 2] in
theorem zornMap_sub (e : K ≃+* ZMod 2) (x y : quasithinZorn K) :
    zornMap e (x - y) = zornMap e x - zornMap e y := by
  simp only [zornMap]
  refine Prod.ext (by exact map_sub e _ _) (Prod.ext (funext fun i => by exact map_sub e _ _)
    (Prod.ext (funext fun i => by exact map_sub e _ _) (by exact map_sub e _ _)))

omit [CharP K 2] in
theorem fG_zornConj (e : K ≃+* ZMod 2) (g : ↥(cayleyGroup K)) :
    fG ⟨zornConj e g, zornConj_mem e g.2⟩ =
      (RingEquiv.piCongrRight fun _ : Ix3 => e) (fG g) := by
  rw [fG_eq_zP, fG_eq_zP]
  change zP (zornMap e ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (zornMap e.symm (zE' (ZMod 2)))) - zE' (ZMod 2)) = _
  have h1 : zornMap e.symm (zE' (ZMod 2)) = zE' K := by
    simp only [zornMap, zE', zmk]
    refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ (by simp))) <;> funext i <;>
      fin_cases i <;> simp
  rw [h1, ← zornMap_zE' e, ← zornMap_sub, zP_zornMap]
  rfl


theorem exists_sub_fG_mem_B1A_card_two [Fintype K] (hK : Fintype.card K = 2)
    {f : ↥(cayleyGroup K) → (Ix3 → K)} (hf : f ∈ Z1A (g2Act (F := K))) :
    ∃ α : K, f - α • fG ∈ B1A (g2Act (F := K)) := by
  set e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK).symm
  set E := RingEquiv.piCongrRight fun _ : Ix3 => e
  let Θ : ↥(cayleyGroup K) ≃* ↥(cayleyGroup (ZMod 2)) :=
    ((zornConj e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_cayleyGroup e))
  have hΘ : ∀ g, Θ g = ⟨zornConj e g, zornConj_mem e g.2⟩ := fun g => rfl
  have hact : ∀ g w, E (g2Act g w) = g2Act (Θ g) (E w) := fun g w => by
    rw [hΘ]
    exact g2Act_zornConj e g w
  set f' : ↥(cayleyGroup (ZMod 2)) → (Ix3 → ZMod 2) := fun g => E (f (Θ.symm g)) with hf'
  have hf'Z : f' ∈ Z1A (g2Act (F := ZMod 2)) := by
    intro g h
    simp only [hf', map_mul]
    rw [hf, map_add, hact, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨α, w, hw⟩ := exists_sub_fG_mem_B1A_two hf'Z
  refine ⟨e.symm α, E.symm w, funext fun g => ?_⟩
  have h1 := congrFun hw (Θ g)
  simp only [hf', Pi.sub_apply, Pi.smul_apply, MulEquiv.symm_apply_apply] at h1
  change g2Act (Θ g) w - w = _ at h1
  change g2Act g (E.symm w) - E.symm w = f g - e.symm α • fG g
  apply E.injective
  rw [map_sub, hact, RingEquiv.apply_symm_apply]
  refine h1.trans ?_
  rw [map_sub, hΘ, fG_zornConj]
  congr 1
  funext i
  simp [E]

theorem exists_sub_fG_mem_B1A_all [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (hn : 1 ≤ n) {f : ↥(cayleyGroup K) → (Ix3 → K)} (hf : f ∈ Z1A (g2Act (F := K))) :
    ∃ α : K, f - α • fG ∈ B1A (g2Act (F := K)) := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact exists_sub_fG_mem_B1A hK h1 hf
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    exact exists_sub_fG_mem_B1A_card_two (by rw [hK, pow_one]) hf

end Transport

end CFSG.Quasithin.B5.G2D
