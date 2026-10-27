module

public import CFSG.Quasithin.H13.U3S13227H
public import CFSG.Quasithin.H13.VolIC113d
public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

theorem const_iff_P6 : ∀ y : P6, (∀ i j : Fin 6, Multiplicative.toAdd y i =
    Multiplicative.toAdd y j) ↔ (y = 1 ∨ y = G6.allOnes 6) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_V_le_L (S : A6.Setting134 G T L V) : V ≤ L := by
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  rw [← hcomm, commutator_le]
  intro v hv l hl
  rw [commutatorElement_def]
  have hvl : v * l * v⁻¹ ∈ L := (mem_normalizer_iff.mp (S.T_le_NL (S.V_le_T hv)) l).mp hl
  exact L.mul_mem hvl (L.inv_mem hl)

theorem s134_V_le_pCoreOf_L (S : A6.Setting134 G T L V) : V ≤ pCoreOf 2 L :=
  le_pCoreOf_of_le_normalizer 2 (s134_V_le_L S) S.frame.L_le S.isPGroup_V

theorem s134_blockU_eq_V (S : A6.Setting134 G T L V) (hL : IsShort2 L) : blockU L = V := by
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  have hle : ⁅V, L⁆ ≤ blockU L := commutator_mono (s134_V_le_pCoreOf_L S) le_rfl
  have hne : ⁅V, L⁆ ≠ ⊥ := by
    rw [hcomm]
    exact S.irr.2.1
  have h := L246C127.blockU_le_commutator_of_ne_bot hL S.frame.L_le S.isPGroup_V hle hne
  rw [hcomm] at h hle
  exact le_antisymm h hle

theorem s134_pCoreOf_L_eq (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    pCoreOf 2 L = L ⊓ centralizer (V : Set G) :=
  le_antisymm (le_inf (pCoreOf_le 2 L) (s134_pCoreOf_L_le S))
    fun _ hx => o2Z_le_pCoreOf_of_a6 he (s134_centralizer_le_o2Z S hx)

@[expose] noncomputable def s134Alpha (S : A6.Setting134 G T L V) :
    ↥L →* alternatingGroup (Fin 6) :=
  (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict (alternatingGroup (Fin 6))
    fun l => (S.frame.image_L _).1 ⟨Subgroup.inclusion S.frame.L_le l, l.2, rfl⟩

theorem s134Alpha_coe (S : A6.Setting134 G T L V) (l : ↥L) :
    (s134Alpha S l : Perm (Fin 6)) = S.frame.ρ (Subgroup.inclusion S.frame.L_le l) := rfl

theorem s134Alpha_surjective (S : A6.Setting134 G T L V) : Function.Surjective (s134Alpha S) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
  refine ⟨⟨g, hgL⟩, Subtype.ext ?_⟩
  rw [s134Alpha_coe]
  exact (congrArg S.frame.ρ (Subtype.ext rfl)).trans hg

theorem s134Alpha_ker (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    (s134Alpha S).ker = CFSG.pCore 2 ↥L := by
  ext l
  rw [MonoidHom.mem_ker, AppC.mem_pCore_iff_mem_blockQ]
  show _ ↔ (l : G) ∈ pCoreOf 2 L
  rw [s134_pCoreOf_L_eq S he]
  constructor
  · intro h
    have h1 : S.frame.ρ (Subgroup.inclusion S.frame.L_le l) = 1 := congrArg Subtype.val h
    exact ⟨l.2, (s134_rho_eq_one_iff S _).1 h1⟩
  · rintro ⟨-, hc⟩
    exact Subtype.ext ((s134_rho_eq_one_iff S (Subgroup.inclusion S.frame.L_le l)).2 hc)

@[expose] noncomputable def s134Beta (S : A6.Setting134 G T L V) (hU : blockU L ≤ V) :
    ↥(blockU L) →* Multiplicative (AltHeart 6) :=
  (C124.altHeartHom 6).comp (S.frame.ψ.toMonoidHom.comp (Subgroup.inclusion hU))

theorem s134_isAltBlockType (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    IsAltBlockType L 6 := by
  have hUV := s134_blockU_eq_V S hL
  refine ⟨hL, s134Alpha S, s134Alpha_surjective S, s134Alpha_ker S he, s134Beta S hUV.le,
    ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := C124.altHeartHom_surjective 6 y
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    exact ⟨⟨v, hUV.ge v.2⟩, rfl⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show C124.altHeartHom 6 (S.frame.ψ (Subgroup.inclusion hUV.le u)) = 1 ↔
      (u : G) ∈ blockU L ⊓ centralizer (L : Set G)
    rw [C124.altHeartHom_eq_one_iff, const_iff_P6, mem_inf]
    have hcen := S.mem_centralizer_L_iff (Subgroup.inclusion hUV.le u)
    have key : ((S.frame.ψ (Subgroup.inclusion hUV.le u) : P6) = 1 ∨
        (S.frame.ψ (Subgroup.inclusion hUV.le u) : P6) = G6.allOnes 6) ↔
        (Subgroup.inclusion hUV.le u = 1 ∨
          Subgroup.inclusion hUV.le u = ⟨S.zV, S.zV_mem_V⟩) := by
      constructor
      · rintro (h | h)
        · left
          apply S.frame.ψ.injective
          rw [map_one]
          exact Subtype.ext h
        · right
          apply S.frame.ψ.injective
          rw [S.psi_zV]
          exact Subtype.ext h
      · rintro (h | h)
        · left
          rw [h, map_one]
          rfl
        · right
          rw [h, S.psi_zV]
    rw [key, ← hcen]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  · intro ℓ u v hv x hx
    have hψv : S.frame.ψ (Subgroup.inclusion hUV.le v) =
        G6.coreAct 6 (s134Alpha S ℓ : Perm (Fin 6)) (S.frame.ψ (Subgroup.inclusion hUV.le u)) := by
      rw [s134Alpha_coe, ← S.psi_conj]
      congr 1
      exact Subtype.ext hv
    have h2 : Multiplicative.toAdd (s134Beta S hUV.le v) = (QuotientAddGroup.mk
        (permWeight 6 (s134Alpha S ℓ : Perm (Fin 6)) (Multiplicative.toAdd
          (C124.coreEvenEquiv 6 (S.frame.ψ (Subgroup.inclusion hUV.le u))))) : AltHeart 6) := by
      show Multiplicative.toAdd (C124.altHeartHom 6 (S.frame.ψ (Subgroup.inclusion hUV.le v))) = _
      rw [C124.altHeartHom_apply, hψv]
      rfl
    rw [h2]
    have h3 : (QuotientAddGroup.mk x : AltHeart 6) = QuotientAddGroup.mk (Multiplicative.toAdd
        (C124.coreEvenEquiv 6 (S.frame.ψ (Subgroup.inclusion hUV.le u)))) := by
      rw [hx]
      rfl
    rw [QuotientAddGroup.eq] at h3 ⊢
    exact C124.permWeight_sub_mem _ h3

theorem s134_pCoreOf_LT_le_centralizer (S : A6.Setting134 G T L V) (hL : IsShort2 L)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    pCoreOf 2 (L ⊔ T) ≤ centralizer (pCoreOf 2 L : Set G) :=
  VolI.pCoreOf_le_centralizer_of_alt6 hL (A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right)
    S.T_le_NL (s134_isAltBlockType S hL he)

theorem s134_commutator_mem_V (S : A6.Setting134 G T L V) (hL : IsShort2 L) {q l : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L) : q * l * q⁻¹ * l⁻¹ ∈ V :=
  s134_blockU_eq_V S hL ▸ VolI.commutator_mem_blockU hL S.T_le_NL hq hl

omit [Finite G] in
theorem L1Of_le (L V₁ : Subgroup G) : L₁Of L V₁ ≤ L := (oTwoRes_le _).trans inf_le_left

theorem s134_exists_L1_cube (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {σ : Perm (Fin 6)}
    (hσA : σ ∈ alternatingGroup (Fin 6)) (hσ3 : σ ^ 3 = 1) (hσ : InA4 σ) :
    ∃ c ∈ L₁Of L (fsuV1 T V), c ^ 3 = 1 ∧
      ∃ hc : c ∈ normalizer (V : Set G), S.frame.ρ ⟨c, hc⟩ = σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyL1, hyN, hyσ⟩ := s134_exists_mem_L1 S hσA hσ3 hσ
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcm : (y ^ 4 ^ a) ^ m = 1 := by
    have h1 : (y ^ 4 ^ a) ^ m = (y ^ (2 ^ a * m)) ^ 2 ^ a := by
      rw [← pow_mul, ← pow_mul, show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by
        rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]]
      ring_nf
    rw [h1, ← hn, pow_orderOf_eq_one, one_pow]
  have hcN : y ^ 4 ^ a ∈ normalizer (V : Set G) := pow_mem hyN _
  have hcσ : S.frame.ρ ⟨y ^ 4 ^ a, hcN⟩ = σ := by
    have h1 : (⟨y ^ 4 ^ a, hcN⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyN⟩ ^ 4 ^ a :=
      Subtype.ext (by simp)
    rw [h1, map_pow, hyσ]
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ a = 3 * k + 1 := ⟨4 ^ a / 3, by
      have := Nat.div_add_mod (4 ^ a) 3
      rw [four_pow_mod_three] at this
      omega⟩
    rw [hk, pow_succ, pow_mul, hσ3, one_pow, one_mul]
  refine ⟨y ^ 4 ^ a, pow_mem hyL1 _, ?_, hcN, hcσ⟩
  have hc3N : (y ^ 4 ^ a) ^ 3 ∈ normalizer (V : Set G) := pow_mem hcN 3
  have hc3C : (y ^ 4 ^ a) ^ 3 ∈ centralizer (V : Set G) := by
    refine (s134_rho_eq_one_iff S ⟨_, hc3N⟩).1 ?_
    have h1 : (⟨(y ^ 4 ^ a) ^ 3, hc3N⟩ : ↥(normalizer (V : Set G))) = ⟨y ^ 4 ^ a, hcN⟩ ^ 3 :=
      Subtype.ext (by simp)
    rw [h1, map_pow, hcσ, hσ3]
  have hc3O : (y ^ 4 ^ a) ^ 3 ∈ pCoreOf 2 L := by
    rw [s134_pCoreOf_L_eq S he]
    exact ⟨pow_mem (L1Of_le L _ (pow_mem hyL1 _)) 3, hc3C⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, hc3O⟩
  have h2 : ((y ^ 4 ^ a) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm3 : ((y ^ 4 ^ a) ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hcm, one_pow]
  have hg : ((y ^ 4 ^ a) ^ 3) ^ Nat.gcd m (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨hm3, h2⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (Odd.coprime_two_right hm)),
    pow_one] at hg

end CFSG.Quasithin.H13.U3
