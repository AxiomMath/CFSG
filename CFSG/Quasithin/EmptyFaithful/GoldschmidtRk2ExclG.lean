module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclUp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtInner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclLev

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Levi

variable {X : Type} [Group X]

theorem levi_modO2 {B : Subgroup X} {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ k) (g : ↥B →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) [Finite X] :
    IsPSL 2 2 k (↥B ⧸ CFSG.pCore 2 ↥B) ∧ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
  have hK4 := exists_finset_card_four_of_pow hK hk
  have hsimple := sl2_isSimple hK4
  have hnab := sl2_nonabelian hK4
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  let e : ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) K := modO2EquivOfHom hnab g hg hker
  refine ⟨⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans sl2EquivStatedProj⟩⟩, ?_⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · have : IsSimpleGroup (ModO2 B) := e.isSimpleGroup
    obtain ⟨a, b, hab⟩ := hnab
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩).1

end Levi

section Data

variable {G : Type} [Group G] [Finite G] {Y : Type} [Group Y] [Finite Y]

structure RkData (L SL : Subgroup G) (ρ : ↥L →* Y) (U : Subgroup Y)
    (P : Fin 2 → Subgroup Y) : Prop where
  surj : Function.Surjective ρ
  q_le : CFSG.Open.pCore 2 ↥L ≤ ρ.ker
  cent : ∀ x ∈ ρ.ker, ∀ g : ↥L, ⁅x, g⁆ ∈ CFSG.Open.pCore 2 ↥L
  sylow : IsSylowTwoOf SL L
  hU : (SL.subgroupOf L).map ρ = U
  pkg : Rank2Pkg Y U P
  kerTwo : ∀ j, ∀ x ∈ lev ρ (P j), ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1

variable {L SL : Subgroup G} {ρ : ↥L →* Y} {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

@[expose] def parUp (L : Subgroup G) (ρ : ↥L →* Y) (B : Subgroup Y) : Subgroup G :=
  up L (B.comap ρ)

@[expose] def levUp (L : Subgroup G) (ρ : ↥L →* Y) (B : Subgroup Y) : Subgroup G :=
  up L (lev ρ B)

theorem parUp_le (B : Subgroup Y) : parUp L ρ B ≤ L := up_le _

theorem levUp_le (B : Subgroup Y) : levUp L ρ B ≤ L := up_le _

theorem levUp_le_parUp (B : Subgroup Y) : levUp L ρ B ≤ parUp L ρ B := up_mono (lev_le ρ B)

theorem perfectCore_parUp (B : Subgroup Y) : perfectCore (parUp L ρ B) = levUp L ρ B :=
  perfectCore_up _

theorem levUp_perfect (B : Subgroup Y) : ⁅levUp L ρ B, levUp L ρ B⁆ = levUp L ρ B := by
  rw [levUp, up_commutator, lev_perfect]

theorem parUp_le_normalizer_levUp (B : Subgroup Y) :
    parUp L ρ B ≤ Subgroup.normalizer (levUp L ρ B : Set G) := by
  rw [← perfectCore_parUp]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le _)).1 (perfectCore_normal _)

theorem pCoreOf_le_parUp (h : RkData L SL ρ U P) (j : Fin 2) : pCoreOf 2 L ≤ parUp L ρ (P j) :=
  up_mono (h.q_le.trans (Subgroup.ker_le_comap ρ (P j)))

theorem inf_normalizer_le_parUp (h : RkData L SL ρ U P) (j : Fin 2) :
    L ⊓ Subgroup.normalizer (SL : Set G) ≤ parUp L ρ (P j) := by
  rintro x ⟨hxL, hxN⟩
  refine mem_up.2 ⟨hxL, ?_⟩
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((SL.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 hxN y.1
    simpa [Subgroup.mem_subgroupOf] using this
  have h2 := Subgroup.le_normalizer_map ρ ⟨_, h1, rfl⟩
  rw [h.hU] at h2
  exact h.pkg.norm j h2

theorem isMaxParabolic2_parUp (h : RkData L SL ρ U P) (j : Fin 2) :
    IsMaxParabolic2 L (parUp L ρ (P j)) := by
  have hpar : IsParabolic2 L (parUp L ρ (P j)) :=
    ⟨parUp_le _, SL, h.sylow, inf_normalizer_le_parUp h j⟩
  refine ⟨hpar, ?_, ?_⟩
  · intro heq
    have h1 : (P j).comap ρ = ⊤ := up_injective (heq.trans up_top.symm)
    apply h.pkg.ne_top j
    rw [← Subgroup.map_comap_eq_self_of_surjective h.surj (P j), h1,
      Subgroup.map_top_of_surjective _ h.surj]
  · intro Q' hQ' hne hPQ
    have hQL : Q' ≤ L := hQ'.1
    set X : Subgroup ↥L := Q'.subgroupOf L with hX
    have hQX : Q' = up L X := (Subgroup.map_subgroupOf_eq_of_le hQL).symm
    have hcomap : (P j).comap ρ ≤ X := by
      have : up L ((P j).comap ρ) ≤ up L X := by
        rw [← hQX]
        exact hPQ
      exact up_le_up_iff.1 this
    have hkerX : ρ.ker ≤ X := (Subgroup.ker_le_comap ρ (P j)).trans hcomap
    have hmapX : P j ≤ X.map ρ := by
      rw [← Subgroup.map_comap_eq_self_of_surjective h.surj (P j)]
      exact Subgroup.map_mono hcomap
    have hcov := h.pkg.covBy j
    by_cases hlt : P j < X.map ρ
    · have htop : X.map ρ = ⊤ := by
        by_contra hnt
        exact hcov.2 hlt (lt_top_iff_ne_top.2 hnt)
      have hXtop : X = ⊤ := by
        rw [← Subgroup.comap_map_eq_self hkerX, htop, Subgroup.comap_top]
      exact absurd (by rw [hQX, hXtop, up_top]) hne
    · have heq : X.map ρ = P j := ((hmapX.lt_or_eq).resolve_left hlt).symm
      have hXe : X = (P j).comap ρ := by
        rw [← Subgroup.comap_map_eq_self hkerX, heq]
      rw [hQX, hXe]
      rfl

theorem levUp_sup_eq (h : RkData L SL ρ U P)
    (hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤) :
    levUp L ρ (P 0) ⊔ levUp L ρ (P 1) ⊔ SL ⊔ pCoreOf 2 L = L := by
  have h1 := sup_lev_eq_top h.surj h.pkg h.hU h.cent hperf
  have h2 := congrArg (up L) h1
  rw [up_top, up_sup, up_sup, up_sup] at h2
  have e1 : up L (SL.subgroupOf L) = SL := Subgroup.map_subgroupOf_eq_of_le h.sylow.1
  have e2 : up L (CFSG.Open.pCore 2 ↥L) = pCoreOf 2 L := rfl
  rw [e1, e2] at h2
  exact h2

theorem perfect_sup_pCore_of_quasi (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤ := by
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ⁅(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)), ⊤⁆ = ⊤ := hq.1.commutator_eq_top
  have h2 : Subgroup.map π ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπs]
    exact h1
  have h3 := Subgroup.comap_map_eq π ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆
  rw [h2, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h3
  exact h3.symm

theorem charTwo_parUp (h : RkData L SL ρ U P) (hch : CharTwo L) (j : Fin 2) :
    CharTwo (parUp L ρ (P j)) :=
  charTwo_of_pCore_centralizer_le hch (parUp_le _) fun _ hx => pCoreOf_le_parUp h j hx.1

theorem charTwo_levUp (h : RkData L SL ρ U P) (hch : CharTwo L) (j : Fin 2) :
    CharTwo (levUp L ρ (P j)) := by
  have hn : ((levUp L ρ (P j)).subgroupOf (parUp L ρ (P j))).Normal := by
    rw [← perfectCore_parUp]
    exact perfectCore_normal _
  exact CharTwo.of_normal (charTwo_parUp h hch j) (levUp_le_parUp _) hn

theorem levUp_modO2 (h : RkData L SL ρ U P) (j : Fin 2) :
    ∃ n : ℕ, 2 ≤ n ∧
      IsPSL 2 2 n (↥(levUp L ρ (P j)) ⧸ CFSG.pCore 2 ↥(levUp L ρ (P j))) ∧
      CFSG.IsQuasisimple (↥(levUp L ρ (P j)) ⧸ CFSG.pCore 2 ↥(levUp L ρ (P j))) := by
  obtain ⟨K, hF, hFin, hCh, n, hK, hn, g, hg, hker⟩ := h.pkg.levi j
  let θ : ↥(lev ρ (P j)) →* Matrix.SpecialLinearGroup (Fin 2) K := g.comp (levHom h.surj (P j))
  have hθ : Function.Surjective θ := hg.comp (levHom_surjective h.surj _)
  have hθk : IsPGroup 2 θ.ker := by
    have h1 : θ.ker = g.ker.comap (levHom h.surj (P j)) := (MonoidHom.comap_ker _ _).symm
    rw [h1]
    exact hker.comap_of_ker_isPGroup (levHom h.surj (P j))
      (isPGroup_ker_levHom h.surj (h.kerTwo j))
  let e : ↥(lev ρ (P j)) ≃* ↥(levUp L ρ (P j)) :=
    (lev ρ (P j)).equivMapOfInjective L.subtype L.subtype_injective
  let θ' : ↥(levUp L ρ (P j)) →* Matrix.SpecialLinearGroup (Fin 2) K := θ.comp e.symm.toMonoidHom
  have hθ' : Function.Surjective θ' := hθ.comp e.symm.surjective
  have hθ'k : IsPGroup 2 θ'.ker := by
    intro x
    obtain ⟨k, hk⟩ := hθk ⟨e.symm x.1, x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (e.symm x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : e ((e.symm x.1) ^ 2 ^ k) = 1 := by rw [h1, map_one]
    rw [map_pow, MulEquiv.apply_symm_apply] at h2
    exact h2
  obtain ⟨hpsl, hq⟩ := levi_modO2 hn hK θ' hθ' hθ'k
  exact ⟨n, hn, hpsl, hq⟩

theorem not_isShort2_levUp (h : RkData L SL ρ U P) (hch : CharTwo L) (j : Fin 2) :
    ¬ IsShort2 (levUp L ρ (P j)) := fun hshort =>
  not_blockIrred_lev h.surj h.q_le (charTwo_iff_internal.1 hch) h.pkg j (h.kerTwo j)
    (BlockIrred.of_map L.subtype L.subtype_injective (IsShort2.blockIrred hshort))

end Data

end CFSG.Quasithin.Rk2
