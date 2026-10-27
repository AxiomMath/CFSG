module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineSocle
public import CFSG.LocalAnalysis.WeakClosure81.W18Five
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5SOS
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

@[expose] def Socle185Shape (S : Type) [Group S] : Prop :=
  (∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 9 < p ^ e ∧ F6.IsL2 p e S) ∨
  (∃ p f : ℕ, p.Prime ∧ 5 ≤ p ∧
    ((p ^ f % 3 = 2 ∧ p ^ f % 4 = 3 ∧ LieModel S .PSL 3 p f) ∨
     (p ^ f % 3 = 1 ∧ p ^ f % 4 = 1 ∧ LieModel S .PSU 3 p f))) ∨
  F6.IsL2 7 1 S

theorem Socle185Shape.isSimpleGroup {S : Type} [Group S] [Finite S] (h : Socle185Shape S) :
    IsSimpleGroup S := by
  refine (asch5_simpOutSolv_holds S ?_).1
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | h
  · exact Or.inl ⟨p, e, hp, by omega, by omega, hS⟩
  · refine Or.inr ⟨p, f, hp, by omega, ?_⟩
    rcases h with ⟨-, -, hS⟩ | ⟨-, -, hS⟩
    exacts [Or.inl hS, Or.inr hS]
  · exact Or.inl ⟨7, 1, by norm_num, by norm_num, by norm_num, h⟩

theorem Socle185Shape.exists_not_commute {S : Type} [Group S] [Finite S] (h : Socle185Shape S) :
    ∃ a b : S, a * b ≠ b * a := by
  refine (asch5_simpOutSolv_holds S ?_).2.1
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | h
  · exact Or.inl ⟨p, e, hp, by omega, by omega, hS⟩
  · refine Or.inr ⟨p, f, hp, by omega, ?_⟩
    rcases h with ⟨-, -, hS⟩ | ⟨-, -, hS⟩
    exacts [Or.inl hS, Or.inr hS]
  · exact Or.inl ⟨7, 1, by norm_num, by norm_num, by norm_num, h⟩

variable {G : Type} [Group G] [Finite G]

theorem hasQuotShape_fStarMod_socle185 {H : Subgroup G} (hH : Shape185 H) :
    HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set G) Socle185Shape := by
  obtain ⟨hS, hnot⟩ := hH
  rcases hS with ⟨p, e, hp, hp5, he, ⟨X, instX, φ, hφs, hφk, hX⟩⟩ |
    ⟨p, f, hp, hp5, ⟨h3, h4, X, instX, φ, hφs, hφk, hX⟩ | ⟨h3, h4, X, instX, φ, hφs, hφk, hX⟩⟩ |
    ⟨⟨X, instX, φ, hφs, hφk, hX⟩, -⟩ | h4
  · exact ⟨X, instX, φ, hφs, hφk, Or.inl ⟨p, e, hp, hp5, he, hX⟩⟩
  · exact ⟨X, instX, φ, hφs, hφk, Or.inr (Or.inl ⟨p, f, hp, hp5, Or.inl ⟨h3, h4, hX⟩⟩)⟩
  · exact ⟨X, instX, φ, hφs, hφk, Or.inr (Or.inl ⟨p, f, hp, hp5, Or.inr ⟨h3, h4, hX⟩⟩)⟩
  · exact ⟨X, instX, φ, hφs, hφk, Or.inr (Or.inr hX)⟩
  · exact absurd h4 hnot

theorem exists_simpleSocleMod_of_hasQuotShape {H : Subgroup G}
    (hH : HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set G)
      Socle185Shape) :
    ∃ (Kk F : Subgroup ↥H) (S : Type) (_ : Group S) (φ : ↥F →* S),
      SimpleSocleMod Kk F ∧ Function.Surjective φ ∧
        (∀ k : ↥F, φ k = 1 ↔ (k : ↥H) ∈ Kk) ∧ Socle185Shape S ∧
        ∀ j : ↥H, j ∈ Kk ↔ (j : G) ∈ relPPrimeCore 3 H := by
  obtain ⟨X, instX, φ₀, hφ₀s, hφ₀k, hX⟩ := hH
  have hKn : ((relPPrimeCore 3 H).subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      (p := 3) (by norm_num) H
  haveI := hKn
  have hLH : fStarMod (relPPrimeCore 3 H) H ≤ H := Subgroup.map_subtype_le _
  haveI : Finite X := Finite.of_surjective φ₀ hφ₀s
  have hsimple : IsSimpleGroup X := hX.isSimpleGroup
  have hnc : ∃ a b : X, a * b ≠ b * a := hX.exists_not_commute
  set C : Subgroup ↥H := ((relPPrimeCore 3 H).subgroupOf H).normalCore with hC
  have hCeq : C = (relPPrimeCore 3 H).subgroupOf H := Subgroup.normalCore_eq_self _
  set π : ↥H →* ↥H ⧸ C := QuotientGroup.mk' C with hπ
  have hπk : ∀ j : ↥H, π j = 1 ↔ j ∈ (relPPrimeCore 3 H).subgroupOf H := fun j => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCeq]
  have hFeq : (fStarMod (relPPrimeCore 3 H) H).subgroupOf H =
      (genFittingFStar (↥H ⧸ C)).comap π := by
    rw [fStarMod]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hmemF : ∀ j : ↥H, j ∈ (fStarMod (relPPrimeCore 3 H) H).subgroupOf H ↔
      π j ∈ genFittingFStar (↥H ⧸ C) := fun j => by
    rw [hFeq, Subgroup.mem_comap]
  set F : Subgroup ↥H := (fStarMod (relPPrimeCore 3 H) H).subgroupOf H with hF
  set Kk : Subgroup ↥H := (relPPrimeCore 3 H).subgroupOf H with hKk
  have hFnorm : F.Normal := by
    rw [hFeq]
    exact (CFSG.ComponentClassification.GeneralizedFitting.normal _).comap π
  let ι : ↥F →* ↥(fStarMod (relPPrimeCore 3 H) H) :=
    ((H.subtype).comp F.subtype).codRestrict (fStarMod (relPPrimeCore 3 H) H) (fun k => k.2)
  let φ : ↥F →* X := φ₀.comp ι
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨l, rfl⟩ := hφ₀s x
    exact ⟨⟨⟨l, hLH l.2⟩, l.2⟩, rfl⟩
  have hφk : ∀ k : ↥F, φ k = 1 ↔ (k : ↥H) ∈ Kk := fun k => hφ₀k (ι k)
  have hcenter : Subgroup.center X = ⊥ := by
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  refine ⟨Kk, F, X, instX, φ, ⟨hKn, hFnorm, ?_, ?_, ?_, ?_⟩, hφs, hφk, hX, fun j => Iff.rfl⟩
  ·
    intro k hk
    rw [hF, hmemF, (hπk k).2 hk]
    exact (genFittingFStar _).one_mem
  ·
    intro T hKT hTF hTn
    haveI hTn' : ((T.subgroupOf F).map φ).Normal := hTn.map φ hφs
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T.subgroupOf F).map φ) with hbot | htop
    · left
      refine le_antisymm (fun t ht => ?_) hKT
      have htF : t ∈ F := hTF ht
      have h1 : φ ⟨t, htF⟩ ∈ (T.subgroupOf F).map φ := ⟨⟨t, htF⟩, ht, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (hφk ⟨t, htF⟩).mp h1
    · right
      refine le_antisymm hTF (fun f hf => ?_)
      have h1 : φ ⟨f, hf⟩ ∈ (T.subgroupOf F).map φ := by rw [htop]; trivial
      obtain ⟨⟨t, htF⟩, ht, hteq⟩ := h1
      have hker : φ ((⟨t, htF⟩ : ↥F)⁻¹ * ⟨f, hf⟩) = 1 := by
        rw [map_mul, map_inv, hteq, inv_mul_cancel]
      have hKt : t⁻¹ * f ∈ Kk := (hφk _).mp hker
      have hft : f = t * (t⁻¹ * f) := by simp
      rw [hft]
      exact T.mul_mem ht (hKT hKt)
  ·
    obtain ⟨x₁, x₂, hx⟩ := hnc
    obtain ⟨f₁, rfl⟩ := hφs x₁
    obtain ⟨f₂, rfl⟩ := hφs x₂
    refine ⟨f₁, f₁.2, f₂, f₂.2, fun hmem => hx ?_⟩
    have h1 : φ ⁅f₁, f₂⁆ = 1 := (hφk _).mpr hmem
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  ·
    intro y hy
    have hcent : π y ∈ Subgroup.centralizer (genFittingFStar (↥H ⧸ C) : Set (↥H ⧸ C)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective C q
      have hfF : f ∈ F := (hmemF f).2 hq
      have h2 : π ⁅y, f⁆ = 1 := (hπk _).2 (hy f hfF)
      rw [map_commutatorElement] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
    have hyF : y ∈ F :=
      (hmemF y).2 (CFSG.ComponentClassification.GeneralizedFitting.centralizer_le _ hcent)
    have hcentral : φ ⟨y, hyF⟩ ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨f, rfl⟩ := hφs x
      have h2 : φ ⁅(⟨y, hyF⟩ : ↥F), f⁆ = 1 := (hφk _).2 (hy f f.2)
      rw [map_commutatorElement] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
    rw [hcenter, Subgroup.mem_bot] at hcentral
    exact (hφk _).mp hcentral

theorem ModDataE.exists_surjective_img {H E : Subgroup G} (M : ModDataE H E) :
    ∃ π : ↥H →* ↥(M.img H), Function.Surjective π ∧
      (∀ j : ↥H, ((π j : ↥(M.img H)) : LGL 2 M.W) = M.ρ j) ∧
      ∀ j : ↥H, π j = 1 ↔ (j : G) ∈ Subgroup.centralizer (E : Set G) := by
  refine ⟨M.ρ.codRestrict (M.img H) (fun j => M.mem_img.2 ⟨j, j.2, rfl⟩), ?_, fun j => rfl, ?_⟩
  · intro r
    obtain ⟨j, -, hj⟩ := M.mem_img.1 r.2
    exact ⟨j, Subtype.ext hj⟩
  · intro j
    rw [← M.ρ_eq_one_iff]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1

theorem ModDataE.exists_simpleSocleMod {H E : Subgroup G} (M : ModDataE H E)
    (hker : H ⊓ Subgroup.centralizer (E : Set G) ≤ relPPrimeCore 3 H) (hH : Shape185 H) :
    ∃ (Kk F : Subgroup ↥(M.img H)) (S : Type) (_ : Group S) (φ : ↥F →* S),
      SimpleSocleMod Kk F ∧ Function.Surjective φ ∧
        (∀ k : ↥F, φ k = 1 ↔ (k : ↥(M.img H)) ∈ Kk) ∧ Socle185Shape S ∧
        ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
          (r ∈ Kk ↔ (j : G) ∈ relPPrimeCore 3 H) := by
  obtain ⟨Kk₀, F₀, S, _, φ₀, hsoc₀, hφ₀s, hφ₀k, hS, hKk₀⟩ :=
    exists_simpleSocleMod_of_hasQuotShape (hasQuotShape_fStarMod_socle185 hH)
  obtain ⟨π, hπs, hπ, hπk⟩ := M.exists_surjective_img
  have hker' : π.ker ≤ Kk₀ := by
    intro j hj
    rw [MonoidHom.mem_ker, hπk] at hj
    exact (hKk₀ j).2 (hker ⟨j.2, hj⟩)
  obtain ⟨ψ, hψs, hψk⟩ := exists_hom_map_of_ker_le π hker' hsoc₀.le hφ₀s hφ₀k
  refine ⟨Kk₀.map π, F₀.map π, S, _, ψ, hsoc₀.map π hπs hker', hψs, hψk, hS, ?_⟩
  intro j r hr
  have hrj : r = π j := Subtype.ext (hr.trans (hπ j).symm)
  rw [hrj]
  constructor
  · intro hmem
    obtain ⟨j', hj'K, hj'⟩ := Subgroup.mem_map.mp hmem
    have hjj : j'⁻¹ * j ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hj', inv_mul_cancel]
    have h1 : j'⁻¹ * j ∈ Kk₀ := hker' hjj
    have h2 : j ∈ Kk₀ := by
      have := Kk₀.mul_mem hj'K h1
      simpa using this
    exact (hKk₀ j).1 h2
  · intro hjK
    exact Subgroup.mem_map_of_mem π ((hKk₀ j).2 hjK)

theorem isCompositionFactor_of_simpleSocleMod {Y : Type} [Group Y] [Finite Y]
    {Kk F : Subgroup Y} (h : SimpleSocleMod Kk F) {S : Type} [Group S] (hS : Socle185Shape S)
    (φ : ↥F →* S) (hφ : Function.Surjective φ) (hker : ∀ k : ↥F, φ k = 1 ↔ (k : Y) ∈ Kk)
    {N : Subgroup Y} (hN : N.Normal) (hnot : ¬ N ≤ Kk) :
    CFSG.Quasithin.E1.IsCompositionFactor ↥N S := by
  have hNN : (N.subgroupOf N).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hFN : F ≤ N ⊔ Kk := h.le_sup_of_not_le hN le_rfl hNN hnot
  obtain ⟨ψ, hψs, -⟩ := exists_hom_subgroupOf_of_le_sup hN h.le hFN hφ hker
  haveI : Finite S := Finite.of_surjective φ hφ
  have hsub : (F.subgroupOf N).IsSubnormal :=
    Subgroup.Normal.isSubnormal (h.normal_right.subgroupOf N)
  exact CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection hsub
    hS.isSimpleGroup ψ hψs

end CFSG.LocalAnalysis.WeakClosure81

end
