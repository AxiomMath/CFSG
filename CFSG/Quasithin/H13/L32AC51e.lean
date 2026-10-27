module

public import CFSG.Quasithin.H13.L32AC51c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lin

theorem pCore_sl3_eq_bot : CFSG.Open.pCore 2 (SLn 3) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two card_zmod_two
    (m := 3) le_rfl
  have := CFSG.LieType.BorelTits.pCore_normal (G := SLn 3) 2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 (SLn 3)) with h | h
  · exact h
  · exfalso
    have hp := CFSG.LieType.BorelTits.pCore_isPGroup (G := SLn 3) 2
    rw [h] at hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [Subgroup.card_top, CFSG.QuasithinUnique.Vol2Native.L239.card_sl_three card_zmod_two] at hk
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem ker_eq_pCore_of_sl3 {Γ : Type*} [Group Γ] [Finite Γ] (g : Γ →* SLn 3)
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) : g.ker = CFSG.Open.pCore 2 Γ := by
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker g) hker
  · intro x hx
    have h1 : g x ∈ (CFSG.Open.pCore 2 Γ).map g := Subgroup.mem_map_of_mem g hx
    have h2 := CFSG.LieType.BorelTits.map_pCore_le 2 g hg h1
    rw [pCore_sl3_eq_bot, Subgroup.mem_bot] at h2
    exact h2

end Lin

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

@[expose] def preimG {Y : Type*} [Group Y] (ψ : ↥H →* Y) (X : Subgroup Y) : Subgroup G :=
  (X.comap ψ).map H.subtype

omit [Finite G] in
theorem mem_preimG {Y : Type*} [Group Y] {ψ : ↥H →* Y} {X : Subgroup Y} {g : G} :
    g ∈ preimG ψ X ↔ ∃ hg : g ∈ H, ψ ⟨g, hg⟩ ∈ X := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxR, rfl⟩
    exact ⟨hx, hxR⟩
  · rintro ⟨hg, hR⟩
    exact ⟨⟨g, hg⟩, hR, rfl⟩

omit [Finite G] in
theorem preimG_le {Y : Type*} [Group Y] (ψ : ↥H →* Y) (X : Subgroup Y) : preimG ψ X ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem preimG_mono {Y : Type*} [Group Y] (ψ : ↥H →* Y) {X X' : Subgroup Y} (h : X ≤ X') :
    preimG ψ X ≤ preimG ψ X' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

@[expose] noncomputable def restrG {Y : Type*} [Group Y] (ψ : ↥H →* Y) (X : Subgroup Y) :
    ↥(preimG ψ X) →* ↥X :=
  (ψ.comp (Subgroup.inclusion (preimG_le ψ X))).codRestrict X fun x => by
    obtain ⟨hg, hR⟩ := mem_preimG.mp x.2
    exact hR

omit [Finite G] in
theorem restrG_coe {Y : Type*} [Group Y] (ψ : ↥H →* Y) (X : Subgroup Y) (x : ↥(preimG ψ X)) :
    ((restrG ψ X x : ↥X) : Y) = ψ (Subgroup.inclusion (preimG_le ψ X) x) := rfl

omit [Finite G] in
theorem restrG_surjective {Y : Type*} [Group Y] {ψ : ↥H →* Y} (hψ : Function.Surjective ψ)
    (X : Subgroup Y) : Function.Surjective (restrG ψ X) := by
  rintro ⟨y, hy⟩
  obtain ⟨h, rfl⟩ := hψ y
  exact ⟨⟨h, mem_preimG.mpr ⟨h.2, hy⟩⟩, Subtype.ext rfl⟩

section Kernel

variable {Y : Type*} [Group Y] {ψ : ↥H →* Y} (hker : ψ.ker = CFSG.Open.pCore 2 ↥H)
include hker

omit [Finite G] in
theorem pCoreOf_le_preimG (X : Subgroup Y) : pCoreOf 2 H ≤ preimG ψ X := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_preimG.mpr ⟨x.2, ?_⟩
  have : ψ x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hx
  show ψ x ∈ X
  rw [this]
  exact X.one_mem

omit [Finite G] in
theorem isPGroup_ker_restrG (X : Subgroup Y) : IsPGroup 2 (restrG ψ X).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥H) := by
    exact CFSG.pCore_isPGroup
  rintro ⟨x, hx⟩
  have hx' : Subgroup.inclusion (preimG_le ψ X) x ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [restrG_coe] at this
    exact this
  rw [hker] at hx'
  obtain ⟨k, hk⟩ := hp ⟨_, hx'⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥(CFSG.Open.pCore 2 ↥H) => ((z : ↥H) : G)) hk
  simpa using this

theorem isSolvable_preimG (X : Subgroup Y) (hX : Group.IsSolvable ↥X) :
    Group.IsSolvable ↥(preimG ψ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Group.IsSolvable (restrG ψ X).ker := by
    have := (isPGroup_ker_restrG hker X).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (restrG ψ X).ker.subtype (restrG ψ X)
    (by rw [Subgroup.range_subtype])

end Kernel

theorem quotIso_preimG_blk3 {n : ℕ} {ψ : ↥H →* Lin.SLn n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = CFSG.Open.pCore 2 ↥H) {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    quasithinO2QuotientIso (preimG ψ (Lin.par2 n i (i + 1))) (Lin.SLn 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (Lin.blk3 (n := n) hi hin).comp (restrG ψ (Lin.par2 n i (i + 1))) with hφ
  have hφs : Function.Surjective φ :=
    (Lin.blk3_surjective hi hin).comp (restrG_surjective hψ _)
  have hk3 : IsPGroup 2 (Lin.blk3 (n := n) hi hin).ker :=
    CFSG.QuasithinUnique.Vol2Native.A312L.isPGroup_ker_of_unitriangular (by omega) _
      (Lin.blk3_ker hi hin)
  have hkφ : IsPGroup 2 φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker]
    exact hk3.comap_of_ker_isPGroup _ (isPGroup_ker_restrG hker _)
  exact ⟨φ, hφs, Lin.ker_eq_pCore_of_sl3 φ hφs hkφ⟩

end CFSG.Quasithin.H13.L32A.C
