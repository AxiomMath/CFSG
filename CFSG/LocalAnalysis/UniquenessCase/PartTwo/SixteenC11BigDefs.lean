module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

structure S16C11AltSetup (n : ℕ) (X L K L₀ : Subgroup (MulAut W)) (J₀ J₁ : Subgroup W) :
    Prop where
  cfg : Cfg2Setting X L J₀ J₁
  kx : K ≤ X
  kl : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k
  ksym : IsSym ↥K 3
  e₀ : Z391.EndUnitsTrivial L J₀
  e₁ : Z391.EndUnitsTrivial L J₁
  dir : IsInternalDirect K L₀ X
  ll₀ : L ≤ L₀
  sym : IsSym ↥L₀ n
  alt : IsAlt ↥L n
  nat₀ : AlternatingNatural L J₀ ⊥ n
  nat₁ : AlternatingNatural L J₁ ⊥ n

theorem S16C11AltSetup.model [Finite W] {n : ℕ} {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) : S16C11Model X K J₀ :=
  s16c11_model_of_cfg2 h.cfg h.kx h.kl h.ksym h.e₀ h.e₁

theorem S16C11AltSetup.l₀_le {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) : L₀ ≤ X :=
  h.dir.2.2 ▸ le_sup_right

theorem S16C11AltSetup.l_le {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) : L ≤ X :=
  h.ll₀.trans h.l₀_le

theorem S16C11AltSetup.stable [Finite W] {n : ℕ} {X L K L₀ : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h : S16C11AltSetup n X L K L₀ J₀ J₁) :
    ∀ x ∈ L₀, ∀ y ∈ J₀, x y ∈ J₀ := by
  have hcomm := s16c11_comm_of_isInternalDirect h.dir
  exact fun x hx y hy => s16c11_mem_of_model h.cfg.sq h.model (h.l₀_le hx)
    (fun k hk => (hcomm k hk x hx).symm) hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
