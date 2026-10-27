module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

private lemma s168e3_cyc_centralizer_map_conj {L : Subgroup (MulAut W)} {g : MulAut W}
    (hLg : L.map (MulAut.conj g).toMonoidHom = L) :
    (Subgroup.centralizer (L : Set (MulAut W))).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (L : Set (MulAut W)) := by
  have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLg
  have hgNinv : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hgN
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hgN l).mp hl
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [hy _ hl']
      _ = (g * y * g⁻¹) * l := by group
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro l hl
      have hl' : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff''.mp hgNinv l).mp hl
      calc l * (g⁻¹ * x * g) = g⁻¹ * ((g * l * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * l * g⁻¹)) * g := by rw [hx _ hl']
        _ = (g⁻¹ * x * g) * l := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma s168e3_cyc_stabSub_map_conj (g : MulAut W) (U : Subgroup W) :
    (stabSub U).map (MulAut.conj g).toMonoidHom = stabSub (U.map g.toMonoidHom) := by
  have hginj : Function.Injective g.toMonoidHom := fun a b h => g.injective h
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_stabSub] at hy ⊢
    intro v
    have hkey : ((MulAut.conj g) y) v = g (y (g⁻¹ v)) := by simp [MulAut.mul_apply]
    have hA : ((MulAut.conj g) y) v ∈ U.map g.toMonoidHom ↔ y (g⁻¹ v) ∈ U := by
      rw [hkey]
      exact Subgroup.mem_map_iff_mem hginj
    have hB : v ∈ U.map g.toMonoidHom ↔ g⁻¹ v ∈ U := by
      simpa using (Subgroup.mem_map_iff_mem hginj (x := g⁻¹ v))
    exact hA.trans ((hy (g⁻¹ v)).trans hB.symm)
  · intro hx
    rw [mem_stabSub] at hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_stabSub]
      intro u
      have hkey : (g⁻¹ * x * g) u = g⁻¹ (x (g u)) := by simp [MulAut.mul_apply]
      have hA : (g⁻¹ * x * g) u ∈ U ↔ x (g u) ∈ U.map g.toMonoidHom := by
        rw [hkey]
        simpa using (Subgroup.mem_map_iff_mem hginj (x := g⁻¹ (x (g u)))).symm
      have hB : g u ∈ U.map g.toMonoidHom ↔ u ∈ U :=
        Subgroup.mem_map_iff_mem hginj
      exact hA.trans ((hx (g u)).trans hB)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma s168e3_cyc_centSub_map_conj (g : MulAut W) (U : Subgroup W) :
    (centSub U).map (MulAut.conj g).toMonoidHom = centSub (U.map g.toMonoidHom) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centSub] at hy ⊢
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.inv_apply_self]
    rw [hy u hu]
  · intro hx
    rw [mem_centSub] at hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_centSub]
      intro u hu
      have hgu : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map_of_mem g.toMonoidHom hu
      change g⁻¹ (x (g u)) = u
      rw [hx (g u) hgu]
      simp
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem s168e3_cyc_conc [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    {Z₁ Z₂ : Subgroup W} {p d : ℕ} (hpd : (p = 3 ∧ d = 2) ∨ (p = 7 ∧ d = 3))
    (hZ : Z₁ ⊓ Z₂ = ⊥) (hZtop : Z₁ ⊔ Z₂ = ⊤) (hrk : rk ↥Z₁ = d)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hperm : ∀ g ∈ A, (Z₁.map g.toMonoidHom = Z₁ ∧ Z₂.map g.toMonoidHom = Z₂) ∨
      (Z₁.map g.toMonoidHom = Z₂ ∧ Z₂.map g.toMonoidHom = Z₁))
    (hswap : ∃ g ∈ A, Z₁.map g.toMonoidHom = Z₂) {B K : Subgroup (MulAut W)}
    (hB : B = A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓ stabSub Z₁ ⊓ stabSub Z₂)
    (hK : K = B ⊓ centSub Z₂) (hBp : IsPGroup p ↥B) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hKc : IsCyclicOrd ↥K p) (hKW : commSub ⊤ K = Z₁) (hKt : ⁅K, Subgroup.zpowers t⁆ ≠ ⊥) :
    Conc4_136W A t K ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} = 2 := by
  have hp : p.Prime := by
    rcases hpd with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Nat.prime_three
    · exact Nat.prime_seven
  have hZbot : Z₁ ≠ ⊥ := by
    intro h
    have h0 : rk ↥Z₁ = 0 := by rw [h]; exact rk_bot
    rw [hrk] at h0
    rcases hpd with ⟨_, hd⟩ | ⟨_, hd⟩ <;> omega
  have hZne : Z₁ ≠ Z₂ := by
    intro h
    exact hZbot (by rw [← hZ, ← h, inf_idem])
  have hKbot : K ≠ ⊥ := by
    intro h
    exact hKt (by rw [h, Subgroup.commutator_bot_left])
  have hBA : B ≤ A := by
    rw [hB]
    intro x hx
    simp only [Subgroup.mem_inf] at hx
    exact hx.1.1.1
  have hBmap : ∀ g ∈ A, B.map (MulAut.conj g).toMonoidHom = B := by
    intro g hgA
    have hAconj : A.map (MulAut.conj g).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgA)
    have hCconj : (Subgroup.centralizer (L : Set (MulAut W))).map
        (MulAut.conj g).toMonoidHom = Subgroup.centralizer (L : Set (MulAut W)) :=
      s168e3_cyc_centralizer_map_conj (hLn g hgA)
    rw [hB,
      Subgroup.map_inf ((A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ⊓ stabSub Z₁)
        (stabSub Z₂) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      Subgroup.map_inf (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) (stabSub Z₁)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      Subgroup.map_inf A (Subgroup.centralizer (L : Set (MulAut W)))
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      hAconj, hCconj, s168e3_cyc_stabSub_map_conj g Z₁,
      s168e3_cyc_stabSub_map_conj g Z₂]
    rcases hperm g hgA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      ac_rfl
  have hBnorm : (B.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    intro g hgA
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hBmap g hgA
  have hKB : K ≤ B := by rw [hK]; exact inf_le_left
  have hKpCore : K ≤ pCoreOf p A :=
    hKB.trans (CFSG.LocalAnalysis.UniquenessCase.UCK.le_pCoreOf_of_normal hBA hBnorm hBp)
  have hconjZ : conjSubs A Z₁ = ({Z₁, Z₂} : Set (Subgroup W)) := by
    ext X
    constructor
    · rintro ⟨g, hgA, rfl⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hperm g hgA with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · intro hX
      rcases hX with rfl | rfl
      · refine ⟨1, A.one_mem, ?_⟩
        have h1 : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by
          ext x
          simp
        rw [h1, Subgroup.map_id]
      · obtain ⟨g, hgA, hg⟩ := hswap
        exact ⟨g, hgA, hg.symm⟩
  have hmapK : ∀ g ∈ A, K.map (MulAut.conj g).toMonoidHom =
      B ⊓ centSub (Z₂.map g.toMonoidHom) := by
    intro g hgA
    rw [hK, Subgroup.map_inf B (centSub Z₂) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective, hBmap g hgA, s168e3_cyc_centSub_map_conj g Z₂]
  have hK_ne_K' : K ≠ B ⊓ centSub Z₁ := by
    intro heq
    apply hKbot
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hkZ₁ : k ∈ centSub Z₁ := by
      have hle : K ≤ centSub Z₁ := by rw [heq]; exact inf_le_right
      exact hle hk
    have hkZ₂ : k ∈ centSub Z₂ := by
      rw [hK] at hk
      exact (Subgroup.mem_inf.mp hk).2
    refine MulEquiv.ext fun w => ?_
    have hw : w ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    change k (y * z) = y * z
    rw [map_mul, (mem_centSub.mp hkZ₁) y hy, (mem_centSub.mp hkZ₂) z hz]
  have h133 : Conc4_133 A t K := by
    refine ⟨p, hp, hKpCore, hKt, ?_, ?_⟩
    · rw [hKW, hconjZ, sSupIndep_pair hZne, disjoint_iff]
      exact hZ
    · rcases hpd with ⟨hp3, hd2⟩ | ⟨hp7, hd3⟩
      · left
        refine ⟨?_, Or.inl ?_⟩
        · rw [hp3] at hKc
          exact hKc
        · rw [hKW]
          rw [hd2] at hrk
          exact hrk
      · right; right; right; right; left
        refine ⟨?_, Or.inl ?_⟩
        · rw [hp7] at hKc
          exact hKc
        · rw [hKW]
          rw [hd3] at hrk
          exact hrk
  have hspan : (⨆ X ∈ conjSubs A (commSub ⊤ K), X) = ⊤ := by
    rw [hKW, hconjZ, iSup_pair]
    exact hZtop
  have hcomm : ∀ g ∈ A, g ∉ normalizer (K : Set (MulAut W)) →
      ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub ⊤ K) (K.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    intro g hgA hgn
    have hmg := hmapK g hgA
    have hZ2 : Z₂.map g.toMonoidHom = Z₁ := by
      rcases hperm g hgA with ⟨_, h2⟩ | ⟨_, h2⟩
      · exfalso
        apply hgn
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change K.map (MulAut.conj g).toMonoidHom = K
        rw [hmg, h2, ← hK]
      · exact h2
    have hconj : K.map (MulAut.conj g).toMonoidHom = B ⊓ centSub Z₁ := by
      rw [hmg, hZ2]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hconj] at hy
      exact (hBc x (hKB hx) y (Subgroup.mem_inf.mp hy).1).symm
    · rw [hKW, hconj, commSub_eq_bot_iff]
      intro z hz
      rw [mem_fixV]
      intro y hy
      exact (Subgroup.mem_inf.mp hy).2 z hz
  have hS : {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} =
      ({K, B ⊓ centSub Z₁} : Set (Subgroup (MulAut W))) := by
    ext X
    constructor
    · rintro ⟨g, hgA, rfl⟩
      rw [hmapK g hgA]
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hperm g hgA with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inl (by rw [h2, ← hK])
      · exact Or.inr (by rw [h2])
    · intro hX
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · refine ⟨1, A.one_mem, ?_⟩
        have h1 : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
          ext x
          simp
        rw [h1, Subgroup.map_id]
      · obtain ⟨g, hgA, hg⟩ := hswap
        have hg2 : Z₂.map g.toMonoidHom = Z₁ := by
          rcases hperm g hgA with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd (h1.symm.trans hg) hZne
          · exact h2
        exact ⟨g, hgA, by rw [hmapK g hgA, hg2]⟩
  exact ⟨⟨hspan, hcomm, Or.inl h133⟩, by rw [hS, Set.ncard_pair hK_ne_K']⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
