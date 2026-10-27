
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

abbrev ModO2 {G : Type} [Group G] (B : Subgroup G) : Type := ↥B ⧸ CFSG.pCore 2 ↥B

@[expose] def IsZ4StarExtra2 (V : Type) [Group V] : Prop :=
  ∃ Z E : Subgroup V, Nat.card Z = 4 ∧ IsCyclic ↥Z ∧ IsExtraspecial2 2 ↥E ∧
    Z ≤ Subgroup.center V ∧ Z ⊔ E = ⊤ ∧ Nat.card ↥(Z ⊓ E) = 2

@[expose] def IsZ4Cubed (V : Type) [Group V] : Prop :=
  Nonempty (V ≃* Multiplicative (Fin 3 → ZMod 4))

@[expose] def IsRank2LieChar2 (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, (1 ≤ f ∧ IsPSL 3 2 f X) ∨ (1 ≤ f ∧ IsSL3 (2 ^ f) X) ∨ (2 ≤ f ∧ IsPSp4 2 f X) ∨
    (2 ≤ f ∧ IsG2 2 f X) ∨ (1 ≤ f ∧ Is3D4 2 f X) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f X)) ∨ IsTits X

@[expose] def A312C2 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (∃ n, IsPSL 2 2 n (ModO2 B)) ∧ IsRank2LieChar2 ↥L ∧ ∃ P, IsMaxParabolic2 L P ∧ B = perfectCore P

@[expose] def A312C3 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ∃ f, IsSz f (ModO2 B) ∧ Is2F4 f ↥L ∧ ∃ P, IsParabolic2 L P ∧ B = perfectCore P

@[expose] def A312C4 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsPSL 3 2 1 (ModO2 B) ∧ (IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L) ∧
    ∃ P, IsParabolic2 L P ∧ B = perfectCore P

@[expose] def A312C5 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsPSL 4 2 1 (ModO2 B) ∧ IsPSL 5 2 1 ↥L ∧ ∃ P, IsParabolic2 L P ∧ B = perfectCore P

@[expose] def A312C6 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsAlt 5 ↥B ∨ IsPSL 3 2 1 ↥B) ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7)))

@[expose] def A312C7 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsAlt 6 ↥B ∧ IsAlt 7 ↥L) ∨
    (IsHat ↥B (alternatingGroup (Fin 6)) ∧ IsHat ↥L (alternatingGroup (Fin 7)))

@[expose] def A312C8 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 1 ↥B ∧ IsPSL 2 p 2 ↥L) ∨
    (IsAlt 5 ↥B ∧ ∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 ↥L ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5))

@[expose] def A312C9 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (∃ (s : Bool) (p : ℕ), p.Prime ∧ 3 < p ∧ IsSL2 p ↥B ∧
      (IsPSLEps3 s p 1 ↥L ∨ IsSLEps3 s p ↥L)) ∨
    (IsAlt 6 ↥B ∧ IsPSU 3 5 1 ↥L) ∨ (IsHat ↥B (alternatingGroup (Fin 6)) ∧ IsSU3 5 ↥L)

@[expose] def A312C10 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ 3 < p ∧
    IsExt ↥B (fun V _ => IsElemAbelianOfRank p 2 V) (fun Y _ => IsSL2 p Y) ∧
    (IsPSL 3 p 1 ↥L ∨ IsSL3 p ↥L)

@[expose] def A312C11 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsAlt 6 ↥B ∧ IsSporadic .M11 ↥L

@[expose] def A312C12 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ((IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 6 Y)) ∧ IsSporadic .M22 ↥L) ∨
    ((IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6)))) ∧
      IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))

@[expose] def A312C13 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsSporadic .M22 ↥B ∨ IsPSL 3 2 2 ↥B ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 7 Y) ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsE2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 6 Y) ∨
        IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) ∧ IsSporadic .M23 ↥L

@[expose] def A312C14 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6)))) ∧
      IsSporadic .M24 ↥L

@[expose] def A312C15 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsAlt 5 ↥B ∧ IsSporadic .J1 ↥L

@[expose] def A312C16 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y) ∧ IsSporadic .J2 ↥L

@[expose] def A312C17 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  IsSporadic .J4 ↥L ∧
      (IsExt ↥B (fun V _ => IsExtraspecial2 6 V)
          (fun Y _ => IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ∨
        IsExt ↥B (fun V _ => IsE2 11 V) (fun Y _ => IsSporadic .M24 Y) ∨
        IsAlt 5 (ModO2 B) ∨ IsHat (ModO2 B) (alternatingGroup (Fin 6)) ∨
        IsPSL 4 2 1 (ModO2 B) ∨ IsPSL 3 2 1 (ModO2 B))

@[expose] def A312C18 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y) ∨
        IsExt ↥B (fun V _ => IsZ4Cubed V) (fun Y _ => IsPSL 3 2 1 Y)) ∧ IsSporadic .HS ↥L

@[expose] def A312C19 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
        IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6)))) ∧
      IsSporadic .He ↥L

@[expose] def A312C20 {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  (IsAlt 5 (ModO2 B) ∨ IsPSL 3 2 1 (ModO2 B)) ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 ∧
      IsSporadic .Ru ↥L

@[expose] def A312Case {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  A312C2 B L ∨ A312C3 B L ∨ A312C4 B L ∨ A312C5 B L ∨ A312C6 B L ∨ A312C7 B L ∨ A312C8 B L ∨
    A312C9 B L ∨ A312C10 B L ∨ A312C11 B L ∨ A312C12 B L ∨ A312C13 B L ∨ A312C14 B L ∨
    A312C15 B L ∨ A312C16 B L ∨ A312C17 B L ∨ A312C18 B L ∨ A312C19 B L ∨ A312C20 B L

@[expose] def A312Nonquasi {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  let OL : Subgroup G := (CFSG.oddCore ↥L).map L.subtype
  (⁅OL, L⁆ ≠ ⊥ ∧ L = B ⊔ OL ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)) ∨
  (⁅OL, L⁆ ≠ ⊥ ∧
    (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      IsSL2 p (↥L ⧸ CFSG.oddCore ↥L)) ∧
    ∃ (N : Subgroup ↥(B ⊔ OL)) (_ : N.Normal), N = OL.subgroupOf (B ⊔ OL) ∧
      IsSL2 5 (↥(B ⊔ OL) ⧸ N))

@[expose] def A312Statement (G : Type) [Group G] : Prop :=
  ∀ T : Subgroup G, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T,
    ∃ L ∈ cComp (⊤ : Subgroup G), B ≤ L ∧ (∀ L' ∈ cComp (⊤ : Subgroup G), B ≤ L' → L' = L) ∧
      (B = L ∨ A312Case B L ∨ A312Nonquasi B L)

end CFSG.Quasithin
