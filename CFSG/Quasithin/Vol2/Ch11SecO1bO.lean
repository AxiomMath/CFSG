module

public import CFSG.Quasithin.Vol2.Ch11SecO1A
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 SecA
open scoped IsMulCommutative

theorem eq_of_le_mul_of_perfect {G : Type} [Group G] [Finite G] {L M P : Subgroup G}
    (hLp : ⁅L, L⁆ = L) (hML : M ≤ L) (hP : IsPGroup 2 ↥P)
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hdec : ∀ l ∈ L, ∃ m ∈ M, m⁻¹ * l ∈ P) :
    M = L := by
  classical
  have hNn : (M.subgroupOf L).Normal := ⟨fun a ha l => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨m, hm, hp⟩ := hdec l l.2
    have e : ((l * a * l⁻¹ : ↥L) : G) = m * ((m⁻¹ * l) * a * (m⁻¹ * l)⁻¹) * m⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact M.mul_mem (M.mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hPM hp) _).mp ha))
      (M.inv_mem hm)⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hQ2 : IsPGroup 2 (↥L ⧸ M.subgroupOf L) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, hp⟩ := hdec l l.2
    obtain ⟨k, hk⟩ := hP ⟨_, hp⟩
    refine ⟨k, ?_⟩
    have hl : l = ⟨m, hML hm⟩ * ⟨m⁻¹ * l, L.mul_mem (L.inv_mem (hML hm)) l.2⟩ :=
      Subtype.ext (by simp)
    have hz2 : (⟨m⁻¹ * l, L.mul_mem (L.inv_mem (hML hm)) l.2⟩ : ↥L) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hl, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hm), one_mul,
      ← QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (↥L ⧸ M.subgroupOf L) := hQ2.isNilpotent
  have hsub : Subsingleton (↥L ⧸ M.subgroupOf L) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ M.subgroupOf L) ‹_›
  refine le_antisymm hML fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ M.subgroupOf L) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem le_normalizer_sup {G : Type} [Group G] {A B C : Subgroup G}
    (hA : C ≤ Subgroup.normalizer (A : Set G)) (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun c hc => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hc),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hc)]

theorem autOn_mono' {G : Type} [Group G] {A B V : Subgroup G} (h : A ≤ B) :
    autOn A V ≤ autOn B V :=
  Subgroup.map_mono fun _ hx => h hx

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem eq_of_autOn_le (hS : SecD.NatSetting11 G T L I n) {M : Subgroup G} (hML : M ≤ L)
    (hCM : L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hA : autOn L (fsuV T I) ≤ autOn M (fsuV T I)) : M = L := by
  refine eq_of_le_mul_of_perfect hS.perfect hML (SecO1.isPGroup_inf_centralizer hS) hCM
    fun l hl => ?_
  obtain ⟨m, hm, hmV, he⟩ :=
    SecA.mem_autOn_iff.mp (hA (SecA.conjV_mem_autOn hl (hS.le_normalizer hl)))
  exact ⟨m, hm, L.mul_mem (L.inv_mem (hML hm)) hl, SecS.inv_mul_mem_centralizer he.symm⟩

theorem inf_centralizer_le_normalizer_conj (hS : SecD.NatSetting11 G T L I n)
    {V₁ : Subgroup G} (hV₁V : V₁ ≤ fsuV T I) {y : G} (hy : y ∈ L) :
    L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (conjSubgroup (LOf L V₁) y : Set G) := by
  intro c hc
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
  have hc'L : y * c * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hy hcL) (L.inv_mem hy)
  have hc'C : y * c * y⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : y⁻¹ * v * y ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hS.le_normalizer hy)) v).mp hv
      simpa using this
    have h := Subgroup.mem_centralizer_iff.mp hcC _ hv'
    calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [h]
      _ = y * c * y⁻¹ * v := by group
  have hc'N : y * c * y⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV₁V) hc'C)
  have hc'L₁ : y * c * y⁻¹ ∈ Subgroup.normalizer (LOf L V₁ : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
      (Subgroup.mem_inf.mpr ⟨hc'L, hc'N⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have e : y * (c * x * c⁻¹) * y⁻¹ =
      (y * c * y⁻¹) * (y * x * y⁻¹) * (y * c * y⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hc'L₁ _

theorem sup_conj_eq_of_sup_eq_top (hS : SecD.NatSetting11 G T L I n) {V₁ : Subgroup G}
    (hV₁V : V₁ ≤ fsuV T I) {Γ : Type} [Group Γ] (ρ : Γ →* MulAut ↥(fsuV T I))
    (hρ : ∀ x ∈ autOn L (fsuV T I), ∃ γ, ρ γ = x) {S₀ : Subgroup Γ}
    (hS₀ : ∀ γ ∈ S₀, ρ γ ∈ autOn (LOf L V₁) (fsuV T I)) {y₁ y₂ : G} (hy₁ : y₁ ∈ L)
    (hy₂ : y₂ ∈ L) {δ₁ δ₂ : Γ} (hδ₁ : ρ δ₁ = conjV (fsuV T I) y₁ (hS.le_normalizer hy₁))
    (hδ₂ : ρ δ₂ = conjV (fsuV T I) y₂ (hS.le_normalizer hy₂))
    (htop : conjSubgroup S₀ δ₁ ⊔ conjSubgroup S₀ δ₂ = ⊤) :
    conjSubgroup (LOf L V₁) y₁ ⊔ conjSubgroup (LOf L V₁) y₂ = L := by
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hconjL : ∀ y ∈ L, conjSubgroup (LOf L V₁) y ≤ L := fun y hy x hx => by
    have h := hL₁L (mem_conjSubgroup_iff.mp hx)
    have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    rw [e]
    exact L.mul_mem (L.mul_mem (L.inv_mem hy) h) hy
  have hpart : ∀ (y : G) (hy : y ∈ L) (δ : Γ),
      ρ δ = conjV (fsuV T I) y (hS.le_normalizer hy) →
      conjSubgroup S₀ δ ≤ (autOn (conjSubgroup (LOf L V₁) y) (fsuV T I)).comap ρ := by
    intro y hy δ hδ γ hγ
    obtain ⟨l, hl, hlV, hle⟩ := SecA.mem_autOn_iff.mp (hS₀ _ (mem_conjSubgroup_iff.mp hγ))
    have hyV := hS.le_normalizer hy
    have hxV : y⁻¹ * l * y ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyV) hlV) hyV
    have hx : y⁻¹ * l * y ∈ conjSubgroup (LOf L V₁) y := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hl
    have hconj : conjV (fsuV T I) (y⁻¹ * l * y) hxV =
        (conjV (fsuV T I) y hyV)⁻¹ * conjV (fsuV T I) l hlV * conjV (fsuV T I) y hyV := by
      rw [← SecA.conjV_inv (fsuV T I) hyV, ← SecA.conjV_mul, ← SecA.conjV_mul]
    rw [Subgroup.mem_comap]
    have e : ρ γ = conjV (fsuV T I) (y⁻¹ * l * y) hxV := by
      calc ρ γ = (ρ δ)⁻¹ * ρ (δ * γ * δ⁻¹) * ρ δ := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = _ := by rw [hδ, hle, hconj]
    rw [e]
    exact SecA.conjV_mem_autOn hx hxV
  refine eq_of_autOn_le hS (sup_le (hconjL y₁ hy₁) (hconjL y₂ hy₂))
    (le_normalizer_sup (inf_centralizer_le_normalizer_conj hS hV₁V hy₁)
      (inf_centralizer_le_normalizer_conj hS hV₁V hy₂)) fun x hx => ?_
  obtain ⟨γ, rfl⟩ := hρ x hx
  have hle : (⊤ : Subgroup Γ) ≤ (autOn (conjSubgroup (LOf L V₁) y₁ ⊔
      conjSubgroup (LOf L V₁) y₂) (fsuV T I)).comap ρ := by
    rw [← htop]
    exact sup_le ((hpart y₁ hy₁ δ₁ hδ₁).trans (Subgroup.comap_mono (autOn_mono' le_sup_left)))
      ((hpart y₂ hy₂ δ₂ hδ₂).trans (Subgroup.comap_mono (autOn_mono' le_sup_right)))
  exact hle (Subgroup.mem_top γ)

end CFSG.Quasithin.Vol2.Ch11.SecO1b
