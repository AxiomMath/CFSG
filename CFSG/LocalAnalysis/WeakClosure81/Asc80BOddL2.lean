module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddL2Gen
import CFSG.Quasithin.Vol2.F134L2
import CFSG.Models.Blueprint
import CFSG.GH74.GLS.IVK.L2.ExistNotation
import CFSG.GH74.GLS.C3.Layer1.St1P89Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup L2Seitz CFSG.Open

theorem seitzFour_psl2 :
    SeitzFour fun X _ => (∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .PSL 2 p f) ∧
      ¬ CFSG.Models.LieModel X .PSL 2 5 1 ∧ ¬ CFSG.Models.LieModel X .PSL 2 3 2 := by
  intro G _ _ L E hLn hLs hnab ⟨⟨p, f, hp2, hm⟩, h5, h9⟩ hC hE hE4 hexc
  classical
  have hm' : CFSG.Models.LieModel ↥L .PSL 2 p f := hm
  obtain ⟨hp, hf, hrest⟩ := hm.1
  have hne3 : ((2 : ℕ), p ^ f) ≠ (2, 3) := hrest.2.2
  have : Fact p.Prime := ⟨hp⟩
  have := hLn
  have sc := CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by decide) hm'
  obtain ⟨eP⟩ := CFSG.Quasithin.F134.nonempty_mulEquiv_psl2 sc
  set F := GaloisField p f
  have hcardF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hF : L2Field F := by
    refine ⟨hcardF ▸ hpodd.pow, ?_⟩
    rw [hcardF]
    have h3 : 3 ≤ p ^ f := by
      calc 3 ≤ p := by have := hp.two_le; obtain ⟨k, hk⟩ := hpodd; omega
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    have : p ^ f ≠ 3 := fun h => hne3 (by rw [h])
    omega
  let e₀ : ↥L ≃* L2 F := eP.trans (L2.equivPSL F).symm
  obtain ⟨e, N, -⟩ := ivk_1_2a_exists F hF ↥L e₀
    (inferInstance : Nonempty (Sylow 2 (MulAut ↥L))).some
  have hq5 : Nat.card F ≠ 5 := by
    rw [hcardF]; intro h
    obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).mp h
    exact h5 hm'
  have hq9 : Nat.card F ≠ 9 := by
    rw [hcardF]; intro h
    have h3 : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = p ^ f by rw [h]; norm_num]
      exact dvd_pow_self p (by omega)
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow h3)
    subst hp3
    have : f = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (show 3 ^ f = 3 ^ 2 by rw [h])
    subst this
    exact h9 hm'
  let φ : G →* MulAut ↥L := MulAut.conjNormal
  have hφ : ∀ x : G, ∀ y : ↥L, ((φ x y : ↥L) : G) = x * y * x⁻¹ := fun x y => rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hy⟩ : ↥L) : G)) hx
      simp only [hφ, MulAut.one_apply] at this
      calc y * x = (x * y * x⁻¹) * x := by rw [this]
        _ = x * y := by group
    rwa [hC] at this
  have hfix : ∀ x : G, (fixedSubgroup ↥L (φ x)).map L.subtype ≤ L ⊓ centralizer ({x} : Set G) := by
    rintro x _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h1 : ((φ x y : ↥L) : G) = y := congrArg Subtype.val hy
    rw [hφ] at h1
    calc (y : G) * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  have hEne : E ≠ ⊥ := fun h => by rw [h] at hE4; simp at hE4
  obtain ⟨⟨a, haE⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨b, hbE, hb1, hba⟩ := exists_mem_ne_one_ne_of_four_le_card (A := E) (by omega) a
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hE.2 a haE
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hE.2 b hbE
  have hab : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have hab1 : a * b ≠ 1 := fun h => hba (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left ha2])
  set σ := φ a
  set τ := φ b
  have hσ2 : σ ^ 2 = 1 := by rw [pow_two, ← map_mul, ha2, map_one]
  have hτ2 : τ ^ 2 = 1 := by rw [pow_two, ← map_mul, hb2, map_one]
  have hσ1 : σ ≠ 1 := fun h => ha1 (hφinj (h.trans (map_one φ).symm))
  have hτ1 : τ ≠ 1 := fun h => hb1 (hφinj (h.trans (map_one φ).symm))
  have hστ : σ ≠ τ := fun h => hba (hφinj h).symm
  have hc : σ * τ = τ * σ := by rw [← map_mul, ← map_mul, hab]
  have hinner : ∀ x : G, φ x ∈ innAut ↥L → x ∈ L := by
    rintro x ⟨l, hl⟩
    have : (l : G)⁻¹ * x ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hy⟩ : ↥L) : G)) hl
      simp only [hφ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
      calc y * ((l : G)⁻¹ * x) = (l : G)⁻¹ * ((l * y * (l : G)⁻¹) * x) := by group
        _ = (l : G)⁻¹ * ((x * y * x⁻¹) * x) := by rw [this]
        _ = (l : G)⁻¹ * x * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at this
    rw [← this]; exact l.2
  have hexc' : ¬ (σ ∈ innAut ↥L ∧ τ ∈ innAut ↥L ∧ Nat.card F = 7) := by
    rintro ⟨hσI, hτI, h7⟩
    apply hexc
    refine ⟨?_, Or.inr (Or.inl ?_)⟩
    · have hKl : zpowers a ⊔ zpowers b = E := by
        refine Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr haE) (zpowers_le.mpr hbE)) ?_
        rw [hE4, CFSG.GH74.GLS.C3.Layer1.P89.card_klein (by rw [pow_two]; exact ha2)
          (by rw [pow_two]; exact hb2) hab ha1 hb1 (Ne.symm hba)]
      rw [← hKl]
      exact sup_le (zpowers_le.mpr (hinner a hσI)) (zpowers_le.mpr (hinner b hτI))
    · rw [hcardF] at h7
      obtain ⟨rfl, rfl⟩ := (Nat.prime_seven.pow_eq_iff).mp h7
      exact hm'
  have hgen := fix_sup_eq_top hF e N hσ2 hτ2 hσ1 hτ1 hστ hc hq5 hq9 hexc'
    (fun h7 => small7 hF e h7)
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  have hle : ∀ x ∈ E, x ≠ 1 → L ⊓ centralizer ({x} : Set G) ≤
      ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) :=
    fun x hx hx1 => le_iSup₂_of_le x hx (le_iSup_of_le hx1 le_rfl)
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top _
  rw [← hgen] at hy'
  have hmap : (fixedSubgroup ↥L σ ⊔ fixedSubgroup ↥L τ ⊔ fixedSubgroup ↥L (σ * τ)).map L.subtype ≤
      ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ((hfix a).trans (hle a haE ha1)) ((hfix b).trans (hle b hbE hb1))) ?_
    rw [show σ * τ = φ (a * b) from (map_mul φ a b).symm]
    exact (hfix (a * b)).trans (hle _ habE hab1)
  exact hmap ⟨⟨y, hy⟩, hy', rfl⟩

end CFSG.LocalAnalysis.WeakClosure81
