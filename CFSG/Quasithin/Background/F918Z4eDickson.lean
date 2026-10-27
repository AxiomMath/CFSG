module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.Z4e

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson

theorem exists_card_eq_two_pow {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem card_eq_sixty_or_two_pow_of_simple_subgroup {F : Type}
    [Field F] [Finite F] [CharP F 2] (H : Subgroup (PSL2MatrixGroup F)) [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) :
    Nat.card H = 60 ∨ ∃ m : ℕ, 1 ≤ m ∧ Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨f, hf1, hf⟩ := exists_card_eq_two_pow (K := F)
  have hcomm : ¬ ∀ a b : H, a * b = b * a := fun h => by
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (h a b)
  have hsolv : ¬ Group.IsSolvable H := fun hs => hcomm (IsSimpleGroup.comm_iff_isSolvable.mpr hs)
  rcases dickson_psl2_subgroup_list hf H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, hm1, -, -, -, E, C, hE, hEel, hEcard, -⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  ·
    exact absurd (fun a b => IsMulCommutative.is_comm.comm a b) hcomm
  ·
    exact absurd (fun a b => IsMulCommutative.is_comm.comm a b) hcomm
  ·
    have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hsolv
  ·
    have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hsolv
  ·
    have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hsolv
  ·
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  ·
    have := hE
    have := hEel
    exfalso
    rcases Subgroup.Normal.eq_bot_or_eq_top E with h | h
    · have h1 : Nat.card E = 1 := by rw [h]; exact Subgroup.card_bot
      rw [hEcard] at h1
      exact (Nat.one_lt_two_pow (by omega)).ne' h1
    · apply hcomm
      intro a b
      have ha : a ∈ E := h ▸ Subgroup.mem_top a
      have hb : b ∈ E := h ▸ Subgroup.mem_top b
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    right
    exact ⟨m, Nat.one_le_iff_ne_zero.mpr hm0,
      (Nat.card_congr e.toEquiv).trans (CFSG.Walter.psl2_even_card hm0)⟩
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    right
    refine ⟨m, Nat.one_le_iff_ne_zero.mpr hm0, ?_⟩
    rw [Nat.card_congr e.toEquiv, show Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) =
      Nat.card (GaloisField 2 m) * (Nat.card (GaloisField 2 m) ^ 2 - 1) from
      CFSG.GorensteinWalter.pgl2_card_formula (GaloisField 2 m), GaloisField.card 2 m hm0]

theorem det_eq_one_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) {F : Type*} [Field F] {n : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) F) (g : G) :
    ((ρ g : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  set ψ : G →* Fˣ := Matrix.GeneralLinearGroup.det.comp ρ with hψ
  have hker : ψ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp h
      apply hab
      apply hinj
      rw [map_mul, map_mul, mul_comm]
    · exact h
  have h1 : ψ g = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
  have h2 := congrArg (fun u : Fˣ => (u : F)) h1
  simpa [hψ, Matrix.GeneralLinearGroup.val_det_apply] using h2

def toSpecialLinear {G : Type*} [Group G] {F : Type} [Field F]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hdet : ∀ g, ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1) :
    G →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨(ρ g : Matrix (Fin 2) (Fin 2) F), hdet g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp; rfl)

theorem card_eq_sixty_or_two_pow_of_faithful_two {G : Type}
    [Group G] [IsSimpleGroup G] (hnc : ∃ a b : G, a * b ≠ b * a) {F : Type} [Field F] [Finite F]
    [CharP F 2] (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    Nat.card G = 60 ∨ ∃ m : ℕ, 1 ≤ m ∧ Nat.card G = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hdet := det_eq_one_of_simple_nonabelian hnc ρ
  set φ : G →* PSL2MatrixGroup F :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.toMonoidHom.comp
      (toSpecialLinear ρ hdet) with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 := (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.injective hab
    apply hρ
    apply Units.ext
    exact congrArg Subtype.val h1
  let e : G ≃* φ.range := MonoidHom.ofInjective hφinj
  have : IsSimpleGroup φ.range := e.symm.isSimpleGroup
  have hnc' : ∃ a b : φ.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  rw [Nat.card_congr e.toEquiv]
  exact card_eq_sixty_or_two_pow_of_simple_subgroup φ.range hnc'

end CFSG.Quasithin.Z4e
