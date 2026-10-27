module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenFibre
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm Subgroup CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem exists_conjHom {X : Subgroup K} {n : ℕ} (hn : 7 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) :
    ∃ ρ : ↥(normalizer (X : Set K)) →* Perm (Fin n),
      ∀ g : ↥(normalizer (X : Set K)), ∀ x y : X, (y : K) = (g : K) * x * (g : K)⁻¹ →
        ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) = ρ g * e x * (ρ g)⁻¹ := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)
  let c : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let e' : ↥(X.subgroupOf (normalizer (X : Set K))) ≃* alternatingGroup (Fin n) :=
    (Subgroup.subgroupOfEquivOfLe le_normalizer).trans e
  let φ : ↥(normalizer (X : Set K)) →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr e').toMonoidHom.comp MulAut.conjNormal
  refine ⟨c.symm.toMonoidHom.comp φ, fun g x y hxy => ?_⟩
  have hcπ : c (c.symm (φ g)) = φ g := c.apply_symm_apply _
  have key : MulAut.conjNormal (c.symm (φ g)) (e x) = e y := by
    change c (c.symm (φ g)) (e x) = e y
    rw [hcπ]
    change e' (MulAut.conjNormal g (e'.symm (e x))) = e y
    have h1 : e'.symm (e x) = ⟨⟨x, le_normalizer x.2⟩, x.2⟩ := by
      apply e'.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [h1]
    have h2 : MulAut.conjNormal g (⟨⟨x, le_normalizer x.2⟩, x.2⟩ :
        ↥(X.subgroupOf (normalizer (X : Set K)))) = ⟨⟨y, le_normalizer y.2⟩, y.2⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp [MulAut.conjNormal_apply, hxy]
    rw [h2]
    rfl
  have := congrArg Subtype.val key
  rw [MulAut.conjNormal_apply] at this
  simpa using this.symm

private theorem isElemAbelian_map {G H : Type} [Group G] [Group H] (f : G →* H) {p : ℕ}
    {A : Subgroup G} (hA : IsElemAbelian p A) : IsElemAbelian p (A.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
    have h := congrArg (fun w : A => f (w : G)) (hA.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    simp only [Subgroup.coe_mul, map_mul] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hzb]
    exact h
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hA.2 x hx, map_one]

private theorem isElemAbelian_of_map {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p (A.map f)) :
    IsElemAbelian p A := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have h := congrArg Subtype.val (hA.1.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
    simp only [Subgroup.coe_mul] at h
    simp only [Subgroup.coe_mul, map_mul]
    exact h
  · rw [map_pow, hA.2 (f x) (Subgroup.mem_map_of_mem f hx), map_one]

theorem exists_fibre_subgroup_of_mulEquiv {X S : Subgroup K} {n : ℕ} (hn : 8 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) (hS : IsPGroup 2 S)
    (hSX : S ≤ normalizer (X : Set K)) :
    ∃ J : Subgroup K, J ≤ X ∧ S ≤ normalizer (J : Set K) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) ∧
      (∀ P : Subgroup K, P ≤ J → IsPGroup 3 P → IsElemAbelian 3 P) ∧
      9 ∣ Nat.card J ∧ (12 ≤ n → 27 ∣ Nat.card J) := by
  obtain ⟨ρ, hρ⟩ := exists_conjHom (by omega : 7 ≤ n) e
  have hS' : IsPGroup 2 (S.subgroupOf (normalizer (X : Set K))) :=
    hS.of_equiv (subgroupOfEquivOfLe hSX).symm
  obtain ⟨J₀, hJ₀A, hQJ₀, h23, hel, h9, h27⟩ :=
    exists_fibre_subgroup (hS'.map ρ) (by rw [Fintype.card_fin]; exact hn)
  set φ : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ :=
    (alternatingGroup (Fin n)).subtype_injective.comp e.injective
  have hJ₀φ : J₀ ≤ φ.range := fun g hg => ⟨e.symm ⟨g, hJ₀A hg⟩, by simp [hφ]⟩
  set J : Subgroup K := (J₀.comap φ).map X.subtype with hJ
  have hcard : Nat.card J = Nat.card J₀ := by
    rw [hJ, Subgroup.card_map_of_injective X.subtype_injective,
      ← Subgroup.card_map_of_injective hφinj, Subgroup.map_comap_eq_self hJ₀φ]
  refine ⟨J, map_subtype_le _, ?_, fun p hp hpJ => h23 p hp (hcard ▸ hpJ), ?_, hcard ▸ h9,
    fun h12 => hcard ▸ h27 (by rw [Fintype.card_fin]; exact h12)⟩
  · intro s hs
    refine mem_normalizer_fintype fun k hk => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hk
    have hsN := hSX hs
    have hy' : s * (y : K) * s⁻¹ ∈ X := (mem_normalizer_iff.1 hsN y).1 y.2
    have hconj := hρ ⟨s, hsN⟩ y ⟨_, hy'⟩ rfl
    have hρs : ρ ⟨s, hsN⟩ ∈ (S.subgroupOf (normalizer (X : Set K))).map ρ :=
      Subgroup.mem_map_of_mem ρ
        (show (⟨s, hsN⟩ : normalizer (X : Set K)) ∈ S.subgroupOf _ from hs)
    have hmem : φ ⟨_, hy'⟩ ∈ J₀ := by
      change ((e ⟨_, hy'⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ J₀
      rw [hconj]
      exact (mem_normalizer_iff.1 (hQJ₀ hρs) _).1 hy
    exact Subgroup.mem_map.2 ⟨⟨_, hy'⟩, hmem, rfl⟩
  · intro P hPJ hP
    have hPX : P ≤ X := hPJ.trans (map_subtype_le _)
    have hP' : IsPGroup 3 (P.subgroupOf X) := hP.of_equiv (subgroupOfEquivOfLe hPX).symm
    have hle : (P.subgroupOf X).map φ ≤ J₀ := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hPJ hy)
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz
    have h1 : IsElemAbelian 3 (P.subgroupOf X) :=
      isElemAbelian_of_map hφinj (hel _ hle (hP'.map φ))
    have h2 := isElemAbelian_map X.subtype h1
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPX] at h2

theorem exists_injective_hom {X T : Subgroup K} {n : ℕ} (hn : 7 ≤ n) (hXn : X.Normal)
    (hO : CFSG.pCore 2 K = ⊥) (hT : IsPGroup 2 T) (hXT : X ⊔ T = ⊤)
    (e : X ≃* alternatingGroup (Fin n)) :
    ∃ ρ : K →* Perm (Fin n), Function.Injective ρ ∧ X.map ρ = alternatingGroup (Fin n) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_conjHom hn e
  have hN : ∀ g : K, g ∈ normalizer (X : Set K) := fun g => by
    rw [normalizer_eq_top_iff.2 hXn]
    exact mem_top g
  set ρ : K →* Perm (Fin n) := ρ₀.comp (MonoidHom.codRestrict (MonoidHom.id K) _ hN) with hρdef
  have hconj : ∀ (g : K) (x : X) (hx : g * x * g⁻¹ ∈ X),
      ((e ⟨_, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = ρ g * e x * (ρ g)⁻¹ :=
    fun g x hx => hρ₀ ⟨g, hN g⟩ x ⟨_, hx⟩ rfl
  have hρX : ∀ x : X, ρ x = ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro x
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    obtain ⟨y, rfl⟩ := e.surjective a
    have hx : (x : K) * y * (x : K)⁻¹ ∈ X := X.mul_mem (X.mul_mem x.2 y.2) (X.inv_mem x.2)
    rw [← hconj x y hx]
    have hxy : (⟨_, hx⟩ : X) = x * y * x⁻¹ := rfl
    rw [hxy, map_mul, map_mul, map_inv]
    rfl
  have hCX : centralizer (X : Set K) ≤ CFSG.pCore 2 K := by
    haveI := hXn
    refine le_sSup ⟨inferInstance, ?_⟩
    have hQ : IsPGroup 2 (K ⧸ X) := by
      refine IsPGroup.of_surjective hT ((QuotientGroup.mk' X).comp T.subtype) ?_
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective X q
      have hk : k ∈ ((X ⊔ T : Subgroup K) : Set K) := by
        rw [hXT]
        exact mem_top k
      rw [normal_mul] at hk
      obtain ⟨x, hx, t, ht, rfl⟩ := Set.mem_mul.1 hk
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have := hXn.conj_mem x hx t⁻¹
      rwa [inv_inv, mul_assoc] at this
    refine IsPGroup.of_injective hQ ((QuotientGroup.mk' X).comp (centralizer (X : Set K)).subtype)
      ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hc
    have hcen : e ⟨c, hc⟩ ∈ center (alternatingGroup (Fin n)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.1 c.2 y y.2)
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
      mem_bot, ← map_one e, e.injective.eq_iff] at hcen
    have h1 := congrArg (fun y : X => (y : K)) hcen
    exact Subtype.ext h1
  have hker : ∀ g : K, ρ g = 1 → g ∈ centralizer (X : Set K) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : g * x * g⁻¹ ∈ X := (mem_normalizer_iff.1 (hN g) x).1 hx
    have h := hconj g ⟨x, hx⟩ hx'
    rw [hg, one_mul, inv_one, mul_one] at h
    have h3 : g * x * g⁻¹ = x := congrArg Subtype.val (e.injective (Subtype.ext h))
    calc x * g = g * x * g⁻¹ * g := by rw [h3]
      _ = g * x := by group
  refine ⟨ρ, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have := hCX (hker g hg)
    rwa [hO] at this
  · ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show ρ x = _ from hρX ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro hg
      refine ⟨(e.symm ⟨g, hg⟩ : K), (e.symm ⟨g, hg⟩).2, ?_⟩
      rw [hρX (e.symm ⟨g, hg⟩), MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
