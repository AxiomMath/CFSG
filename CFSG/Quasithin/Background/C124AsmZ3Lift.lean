module

public import CFSG.Quasithin.Background.C124AsmZ3Quot
public import CFSG.Quasithin.Background.C124AsmPre
public import CFSG.Quasithin.Background.C124AsmZ3Avg
public import CFSG.Quasithin.Background.C124AsmZ3Real

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV) {Γ : Type} [Group Γ] (B : XBar X V hV E.hXN Γ)

include E

theorem exists_A {Ys : Subgroup (MulAut (IntMod V hV))} (h : StarZ3 X V L R hV Ys)
    (hm : 5 ≤ m) (e : ↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) :
    ∃ A : Subgroup Γ, Nat.card A = 3 ∧
      (∀ a ∈ A, ∃ (l : G) (hl : l ∈ L), B.π ⟨l, E.hLX hl⟩ = a) ∧
      (∀ (s : G) (hs : s ∈ baum R), ∀ a ∈ A,
        B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩ * a * (B.π ⟨s, E.R_le_X (E.baum_le_R hs)⟩)⁻¹ ∈ A) ∧
      (∀ φ ∈ Ys, ∃ a ∈ A, B.ρ a = φ) ∧ (∃ a ∈ Ys, ∃ b ∈ autI hV L, a * b ≠ b * a) := by
  obtain ⟨x, hxYs, hx3, hx1, hYsx⟩ := exists_generator_three h.card
  have hxL : x ∈ autI hV L := h.le_L hxYs
  obtain ⟨t', ht'L, ht'x⟩ : ∃ t' ∈ autI hV L, t' * x * t'⁻¹ = x⁻¹ := by
    set x' : ↥(autI hV L) := ⟨x, hxL⟩ with hx'
    have hσ3 : (e x') ^ 3 = 1 := by
      rw [← map_pow]
      have : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hσ1 : e x' ≠ 1 := by
      intro hh
      apply hx1
      have := e.injective (hh.trans (map_one e).symm)
      exact congrArg Subtype.val this
    obtain ⟨τ, hτ⟩ := exists_inv_conj_alt hm hσ3 hσ1
    refine ⟨((e.symm τ : ↥(autI hV L)) : MulAut (IntMod V hV)), (e.symm τ).2, ?_⟩
    have h2 := congrArg e.symm hτ
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  have hnc : ∃ a ∈ Ys, ∃ b ∈ autI hV L, a * b ≠ b * a := by
    refine ⟨x, hxYs, t', ht'L, fun hc => ?_⟩
    have h1 : t' * x * t'⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    rw [ht'x] at h1
    exact ne_inv_of_order_three hx3 hx1 h1.symm
  obtain ⟨⟨t, htN⟩, htL, hte⟩ := (mem_autI hV).1 ht'L
  obtain ⟨⟨y₀, hy₀N⟩, hy₀L, hy₀e⟩ := (mem_autI hV).1 hxL
  set Y₁ := preI hV L E.hLN Ys with hY₁
  have hY₁L : Y₁ ≤ L := preI_le hV
  have hY₁X : Y₁ ≤ X := hY₁L.trans E.hLX
  have hρK : ∀ (g : G) (hg : g ∈ Y₁), B.ρ (B.π ⟨g, hY₁X hg⟩) ∈ Ys := by
    intro g hg
    obtain ⟨hgL, hgB⟩ := (mem_preI hV).1 hg
    rw [B.act]
    exact hgB
  have hy₀Y : y₀ ∈ Y₁ := (mem_preI hV).2 ⟨hy₀L, by
    show convI hV ⟨y₀, E.hLN hy₀L⟩ ∈ Ys
    rw [hy₀e]
    exact hxYs⟩
  let K : Subgroup Γ := (Y₁.subgroupOf X).map B.π
  have hKmem : ∀ a ∈ K, ∃ (g : G) (hg : g ∈ Y₁), B.π ⟨g, hY₁X hg⟩ = a := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨g, Subgroup.mem_subgroupOf.1 hg, rfl⟩
  have hKin : ∀ (g : G) (hg : g ∈ Y₁), B.π ⟨g, hY₁X hg⟩ ∈ K := fun g hg =>
    Subgroup.mem_map.2 ⟨⟨g, hY₁X hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hKx : ∀ a ∈ K, B.ρ a ∈ Subgroup.zpowers x := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := hKmem a ha
    rw [← hYsx]
    exact hρK g hg
  have hKker : ∀ a ∈ K, B.ρ a = 1 → ∃ (g : G) (hg : g ∈ Y₁),
      g ∈ Subgroup.centralizer (V : Set G) ∧ B.π ⟨g, hY₁X hg⟩ = a := by
    intro a ha hρa
    obtain ⟨g, hg, rfl⟩ := hKmem a ha
    refine ⟨g, hg, ?_, rfl⟩
    rw [B.act] at hρa
    exact (convI_eq_one_iff hV _).1 hρa
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    let f : ↥K →* ↥(Subgroup.zpowers x) :=
      (B.ρ.comp K.subtype).codRestrict _ (fun a => hKx a a.2)
    have hf : f.ker ≤ Subgroup.center ↥K := by
      intro d hd
      rw [Subgroup.mem_center_iff]
      intro b
      have hρd : B.ρ d = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
      obtain ⟨g, hg, hgC, hgd⟩ := hKker d d.2 hρd
      obtain ⟨g', hg', hgb⟩ := hKmem b b.2
      apply Subtype.ext
      show (b : Γ) * d = d * b
      rw [← hgd, ← hgb]
      exact (E.pi_comm B (hY₁L hg) hgC (hY₁L hg')).symm
    intro a ha b hb
    have := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥K) ⟨b, hb⟩)
  have hnormY₁ : ∀ (s : G) (hs : s ∈ X), convI hV ⟨s, E.hXN hs⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) → ∀ g ∈ Y₁, s * g * s⁻¹ ∈ Y₁ := by
    intro s hs hsn g hg
    exact (Subgroup.mem_normalizer_iff.1 (E.mem_normalizer_preI hs hsn) g).1 hg
  have hKconj : ∀ (s : G) (hs : s ∈ X), convI hV ⟨s, E.hXN hs⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) →
      ∀ a ∈ K, B.π ⟨s, hs⟩ * a * (B.π ⟨s, hs⟩)⁻¹ ∈ K := by
    intro s hs hsn a ha
    obtain ⟨g, hg, rfl⟩ := hKmem a ha
    rw [E.pi_conj B hs (hY₁X hg)]
    exact hKin _ (hnormY₁ s hs hsn g hg)
  have htX : t ∈ X := E.hLX htL
  have ht'N : t' ∈ Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) := by
    rw [hYsx]
    exact mem_normalizer_zpowers (Or.inr ht'x)
  have htn : convI hV ⟨t, E.hXN htX⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) := by
    rw [show convI hV ⟨t, E.hXN htX⟩ = t' from hte]
    exact ht'N
  have hρy : B.ρ (B.π ⟨y₀, hY₁X hy₀Y⟩) = x := by
    rw [B.act]
    exact hy₀e
  have hρt : B.ρ (B.π ⟨t, htX⟩) = t' := by
    rw [B.act]
    exact hte
  have hD : ∀ d ∈ K, B.ρ d = 1 → B.π ⟨t, htX⟩ * d * (B.π ⟨t, htX⟩)⁻¹ = d := by
    intro d hd hρd
    obtain ⟨g, hg, hgC, rfl⟩ := hKker d hd hρd
    exact mul_inv_eq_iff_eq_mul.2 (E.pi_comm B (hY₁L hg) hgC htL).symm
  have hSX : baum R ≤ X := E.baum_le_R.trans E.R_le_X
  let ψ : ↥(baum R) →* Γ := B.π.comp (Subgroup.inclusion hSX)
  have hact : ∀ p : ↥(baum R), B.ρ (ψ p) = convI hV ⟨p, E.hXN (hSX p.2)⟩ := fun p => B.act _
  have hSn : ∀ p : ↥(baum R), convI hV ⟨p, E.hXN (hSX p.2)⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) := fun p =>
    h.S_norm (convI_mem_autI hV p.2 _)
  have hψ : ∀ (p : ↥(baum R)), ∀ a ∈ K, ψ p * a * (ψ p)⁻¹ ∈ K := fun p a ha =>
    hKconj p (hSX p.2) (hSn p) a ha
  have hn : ∀ p : ↥(baum R), B.ρ (ψ p) * x * (B.ρ (ψ p))⁻¹ = x ∨
      B.ρ (ψ p) * x * (B.ρ (ψ p))⁻¹ = x⁻¹ := by
    intro p
    have h1 := (Subgroup.mem_normalizer_iff.1 (hSn p) x).1 hxYs
    rw [hYsx] at h1
    rw [hact p]
    exact conj_dichotomy hx3 hx1 h1
  obtain ⟨z, hzK, hz3, hzS, hρz⟩ := exists_invariant_order_three B.ρ hKc hx3 hx1 hKx
    (hKin y₀ hy₀Y) hρy (hKconj t htX htn) (by rw [hρt]; exact ht'x) hD ψ hψ hn
  obtain ⟨k, hk⟩ := (E.R_pGroup.to_le E.baum_le_R).exists_card_eq
  have hn2 : 2 * Nat.card ↥(baum R) = 2 ^ (k + 1) := by rw [hk, pow_succ']
  rw [hn2] at hρz
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcop : ¬ 3 ∣ 2 ^ (k + 1) := fun hd =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hρz1 : B.ρ z ≠ 1 := by
    intro h1
    rw [hρz] at h1
    exact hcop (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  have hz1 : z ≠ 1 := fun h => hρz1 (by rw [h, map_one])
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hnn : x ^ (((2 : ℤ) ^ (k + 1)) * (2 ^ (k + 1))) = x := by
    have h4 : ((2 : ℤ) ^ (k + 1)) * (2 ^ (k + 1)) % 3 = 1 := by
      have e4 : ((2 : ℤ) ^ (k + 1)) * (2 ^ (k + 1)) = 4 ^ (k + 1) := by
        rw [← mul_pow]
        norm_num
      rw [e4]
      have := Int.ModEq.pow (k + 1) (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide)
      simpa [Int.ModEq] using this
    have := zpow_mod_orderOf x (((2 : ℤ) ^ (k + 1)) * (2 ^ (k + 1)))
    rw [hord, Nat.cast_ofNat, h4, zpow_one] at this
    exact this.symm
  refine ⟨Subgroup.zpowers z, ?_, ?_, ?_, ?_, hnc⟩
  · rw [Nat.card_zpowers, hzord]
  · intro a ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨g, hg, hgz⟩ := hKmem z hzK
    refine ⟨g ^ j, L.zpow_mem (hY₁L hg) j, ?_⟩
    rw [← hgz, ← map_zpow]
    rfl
  · intro s hs a ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have := hzS ⟨s, hs⟩
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ this j
  · intro φ hφ
    rw [hYsx] at hφ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    refine ⟨z ^ (((2 : ℤ) ^ (k + 1)) * i), Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩, ?_⟩
    have e1 : (x ^ (2 ^ (k + 1)) : MulAut (IntMod V hV)) = x ^ ((2 : ℤ) ^ (k + 1)) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [map_zpow, hρz, e1, ← zpow_mul, ← mul_assoc, zpow_mul, hnn]

end EntryPlus

end CFSG.Quasithin.C124
