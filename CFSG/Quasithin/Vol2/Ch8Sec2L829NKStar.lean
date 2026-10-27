module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKPre
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRep
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Star

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

theorem nk_star_step (hmod : StmtFSUModule) (hD4 : StmtD4L3M22) (hS3 : Step828Three)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8)
    {G : Type} [Group G] [Finite G] {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k)
    (hrow' : Row711L3Nine T L I 1 ∨ Row711M22Code T L I)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥(E2.star (H ⊓ fsuM T L) H K))
    (hsolv : Group.IsSolvable ↥(K ⊓ kerIn (H ⊓ fsuM T L) H)) :
    ∀ a ∈ E2.star (H ⊓ fsuM T L) H (fsuV T I), ∀ b ∈ E2.star (H ⊓ fsuM T L) H K,
      (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∨ (a * b * a⁻¹ * b⁻¹) ^ 4 = 1 ∨
        (a * b * a⁻¹ * b⁻¹) ^ 5 = 1 := by
  obtain ⟨hVT, -, -, -⟩ := asf_V_basic hmod hyp
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hTH : T ≤ H := hT.1
  obtain ⟨hKG, W₀, W₁, W, hWa, hWm, hWf, SW, hcfg, hKne⟩ :=
    nk_prelude hmod hD4 hS3 h825 h828 hyp h731 h821 hrow hH hh hC hrow' hKc
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hker := proper_normal_le_ker_star hKH hKperf hs hsolv
  have hHΛ : H ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := le_sup_right
  have hKΛ : K ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hKH.trans hHΛ
  set N₀ : Subgroup ↥K := (SW.ρ.comp (Subgroup.inclusion hKΛ)).ker with hN₀
  have hN₀n : N₀.Normal := MonoidHom.normal_ker _
  have hN₀ne : N₀ ≠ ⊤ := by
    intro htop
    apply hKne
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (SW.mem_img).mp hg
    have hmem : (⟨(y : G), hy⟩ : ↥K) ∈ N₀ := by rw [htop]; exact Subgroup.mem_top _
    have : SW.ρ (Subgroup.inclusion hKΛ ⟨(y : G), hy⟩) = 1 := hmem
    exact Subgroup.mem_bot.mpr this
  have hN₀ψ := hker N₀ hN₀n hN₀ne
  intro a ha b hb
  obtain ⟨av, hav, rfl⟩ := mem_star_cs5.mp ha
  obtain ⟨bk, hbk, rfl⟩ := mem_star_cs5.mp hb
  set v : G := (av : G) with hv
  set kk : G := (bk : G) with hkk
  have hvΛ : v ∈ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hHΛ av.2
  have hkΛ : kk ∈ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hHΛ bk.2
  have hyK : v * kk * v⁻¹ * kk⁻¹ ∈ K := by
    have h1 : v * kk * v⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hTK (hVT hav)) kk).mp hbk
    exact K.mul_mem h1 (K.inv_mem hbk)
  have hρv : SW.ρ ⟨v, hvΛ⟩ ∈ SW.img (fsuV T I) := (SW.mem_img).mpr ⟨⟨v, hvΛ⟩, hav, rfl⟩
  have hρk : SW.ρ ⟨kk, hkΛ⟩ ∈ SW.img (conjClosure (fsuV T I) H) :=
    (SW.mem_img).mpr ⟨⟨kk, hkΛ⟩, hKG hbk, rfl⟩
  have hbound := nk_star_bound hcfg (SW.ρ ⟨v, hvΛ⟩) (SW.ρ ⟨kk, hkΛ⟩) hρv hρk
  set yK : ↥K := ⟨v * kk * v⁻¹ * kk⁻¹, hyK⟩ with hyKdef
  have hρy : SW.ρ (Subgroup.inclusion hKΛ yK) =
      SW.ρ ⟨v, hvΛ⟩ * SW.ρ ⟨kk, hkΛ⟩ * (SW.ρ ⟨v, hvΛ⟩)⁻¹ * (SW.ρ ⟨kk, hkΛ⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hpow : ∀ m : ℕ, (SW.ρ ⟨v, hvΛ⟩ * SW.ρ ⟨kk, hkΛ⟩ * (SW.ρ ⟨v, hvΛ⟩)⁻¹ *
      (SW.ρ ⟨kk, hkΛ⟩)⁻¹) ^ m = 1 →
      ((QuotientGroup.mk av : E2.StarQuot (H ⊓ fsuM T L) H) * QuotientGroup.mk bk *
        (QuotientGroup.mk av)⁻¹ * (QuotientGroup.mk bk)⁻¹) ^ m = 1 := by
    intro m hm
    have hmem : yK ^ m ∈ N₀ := by
      show SW.ρ (Subgroup.inclusion hKΛ (yK ^ m)) = 1
      rw [map_pow, map_pow, hρy]
      exact hm
    have h1 := hN₀ψ hmem
    have h2 : ((yK ^ m : ↥K) : G) ∈ kerIn (H ⊓ fsuM T L) H :=
      (mem_ker_starHom _ _ _ hKH (yK ^ m)).mp (MonoidHom.mem_ker.mp h1)
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have e : (((av * bk * av⁻¹ * bk⁻¹) ^ m : ↥H) : G) = ((yK ^ m : ↥K) : G) := by
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [e]
    exact h2
  rcases hbound with h3 | h4 | h5
  · exact Or.inl (hpow 3 h3)
  · exact Or.inr (Or.inl (hpow 4 h4))
  · exact Or.inr (Or.inr (hpow 5 h5))

end CFSG.Quasithin.H13.L829NK
