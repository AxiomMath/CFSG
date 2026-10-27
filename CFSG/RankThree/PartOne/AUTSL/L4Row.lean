module

public import CFSG.RankThree.PartOne.AUTSL.L4Parabolic
public import CFSG.RankThree.PartOne.AUTSL.Narrow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AUTSL

section Transport

variable {X : Type*} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem congr_apply_apply {Y : Type*} [Group Y] (e : X ≃* Y) (α : MulAut X) (x : X) :
    MulAut.congr e α (e x) = e (α x) := by
  simp [MulAut.congr_apply]

theorem l4_of_equiv (e : X ≃* SpecialLinearGroup (Fin 4) K) [Finite X]
    {S : Subgroup X} (hS : IsPGroup 2 S)
    (hsyl : ∃ S₀ : Sylow 2 X, Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤
      Subgroup.normalizer (S : Set X))
    {E B : Subgroup X} (hE : IsElementaryAbelian 5 E) (hBE : B ≤ E)
    (hBN : B ≤ Subgroup.normalizer (S : Set X)) (hB : Nat.card B = 25) (α : MulAut X)
    (hαB : B.map α.toMonoidHom = B) (hα3 : ∀ b ∈ B, (α ^ 3) b = b) (hα1 : ∃ b ∈ B, α b ≠ b)
    (x : MulAut X) (hxB : ∀ b ∈ B, b⁻¹ * x b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set X) ∧ ∀ g ∈ E, g⁻¹ * x g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hNmap : ∀ T : Subgroup X, (Subgroup.normalizer (T : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K)) := fun T =>
    Subgroup.map_equiv_normalizer_eq T e
  have hS' : IsPGroup 2 (S.map e.toMonoidHom) :=
    hS.of_surjective (e.toMonoidHom.subgroupMap S) (e.toMonoidHom.subgroupMap_surjective S)
  have hsyl' : ∃ S₀ : Sylow 2 (SpecialLinearGroup (Fin 4) K),
      Subgroup.normalizer ((S₀ : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K)) ≤
        Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 4) K)) :
          Set (SpecialLinearGroup (Fin 4) K)) := by
    obtain ⟨S₀, hS₀⟩ := hsyl
    refine ⟨Sylow.mapSurjective hsurj S₀, ?_⟩
    rw [Sylow.coe_mapSurjective hsurj S₀, ← hNmap, ← hNmap]
    exact Subgroup.map_mono hS₀
  have hEexp : ∀ g ∈ E, g ^ 5 = 1 := fun g hg => by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  have hEcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have hEc' : ∀ g ∈ E.map e.toMonoidHom, ∀ h ∈ E.map e.toMonoidHom, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg e (hEcomm a ha b hb)
  have hE5' : ∀ g ∈ E.map e.toMonoidHom, g ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hEexp a ha, map_one]
  have hBE' : B.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hBE
  have hBN' : B.map e.toMonoidHom ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 4) K)) :
        Set (SpecialLinearGroup (Fin 4) K)) := by
    rw [← hNmap]
    exact Subgroup.map_mono hBN
  have hB' : Nat.card (B.map e.toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective e.injective, hB]
  have hαB' : (B.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = B.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have : (MulAut.congr e α).toMonoidHom (e.toMonoidHom b) = e (α b) :=
        congr_apply_apply e α b
      rw [this]
      refine ⟨α b, ?_, rfl⟩
      rw [← hαB]
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← hαB] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      refine ⟨e c, ⟨c, hc, rfl⟩, ?_⟩
      exact congr_apply_apply e α c
  have hα3' : ∀ b ∈ B.map e.toMonoidHom, ((MulAut.congr e α) ^ 3) b = b := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    have := congr_apply_apply e (α ^ 3) b
    change (MulAut.congr e (α ^ 3)) (e b) = e b
    rw [this, hα3 b hb]
  have hα1' : ∃ b ∈ B.map e.toMonoidHom, (MulAut.congr e α) b ≠ b := by
    obtain ⟨b, hb, hne⟩ := hα1
    refine ⟨e b, ⟨b, hb, rfl⟩, ?_⟩
    rw [congr_apply_apply]
    exact fun h => hne (e.injective h)
  have hxB' : ∀ b ∈ B.map e.toMonoidHom, b⁻¹ * (MulAut.congr e x) b ∈ S.map e.toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩
    have := congr_apply_apply e x b
    change (e b)⁻¹ * (MulAut.congr e x) (e b) ∈ _
    rw [this, ← map_inv, ← map_mul]
    exact ⟨_, hxB b hb, rfl⟩
  obtain ⟨hEN, hEx⟩ := l4_sl hS' hsyl' hEc' hE5' hBE' hBN' hB' (MulAut.congr e α) hαB' hα3' hα1'
    (MulAut.congr e x) hxB'
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have h1 := hEN ⟨g, hg, rfl⟩
    rw [← hNmap] at h1
    obtain ⟨n, hn, hng⟩ := h1
    have : n = g := e.injective hng
    rwa [← this]
  · have h1 := hEx _ ⟨g, hg, rfl⟩
    change (e g)⁻¹ * (MulAut.congr e x) (e g) ∈ _ at h1
    rw [congr_apply_apply, ← map_inv, ← map_mul] at h1
    obtain ⟨s, hs, hse⟩ := h1
    have : s = g⁻¹ * x g := e.injective hse
    rwa [← this]

theorem kf1511BTEL4_holds : KF1511BTEL4 := by
  intro X _ _ f hmodel S _ hS2 _ _ hsyl E hE _ B hBE hBN hBcard α _ hαB hα3 hα1 Q _ _ ρ _ _ hρB
  obtain ⟨K, hF, hFin, hcard, ⟨e₀⟩⟩ := exists_projectiveSL_equiv_of_lieModel hmodel
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have h1 : ringChar K ∣ 2 ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self _ n.ne_zero
    have h3 : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    exact CharP.congr (ringChar K) h3
  have hinj : Function.Injective (proj 4 K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, scalars_eq_bot_of_charTwo])
  let ψ : SpecialLinearGroup (Fin 4) K ≃* projectiveSL 4 K :=
    MulEquiv.ofBijective (proj 4 K) ⟨hinj, proj_surjective 4 K⟩
  let e : X ≃* SpecialLinearGroup (Fin 4) K := e₀.trans ψ.symm
  have main : ∀ x : MulAut X, (∀ b ∈ B, b⁻¹ * x b ∈ S) →
      E ≤ Subgroup.normalizer (S : Set X) ∧ ∀ g ∈ E, g⁻¹ * x g ∈ S := fun x hx =>
    l4_of_equiv e hS2 hsyl hE hBE hBN hBcard α hαB hα3 hα1 x hx
  exact ⟨(main 1 fun b _ => by simp).1, fun q g hg => (main (ρ q) (hρB q)).2 g hg⟩

end Transport

end AUTSL

end CFSG.RankThree.PartOne
