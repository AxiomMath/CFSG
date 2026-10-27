module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Split
public import CFSG.Quasithin.H13.VolIC129BorelMain

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lin2_single {L R : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (L : Set G))
    (hsyl : IsSylowTwoOf (R ⊓ L) L) (hJ : ⁅L, thompsonJ R⁆ = L) :
    IsSylowTwoOf (baum R) (L ⊔ baum R) ∧
      baum R ≤ (baum R ⊓ L) ⊔ pCoreOf 2 (L ⊔ baum R) := by
  have hmod : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧
      0 < m ∧ ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
    obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    exact ⟨F, hF, hFin, n, hcard, by omega, α, hαs, hαk⟩
  have hmin : IsMinimalParabolic R (L ⊔ R) :=
    CFSG.Quasithin.H13.VolI.isMinimalParabolic_sup hR2 hRN hsyl hmod
  have hLn : (L.subgroupOf (L ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le Subgroup.le_normalizer hRN)
  have hblk : IsChi0Block (L ⊔ R) L :=
    ⟨⟨hL, le_sup_left, hLn.isSubnormal⟩, Or.inl ⟨n, hn, hlin⟩⟩
  exact ⟨(C56.baumann_single hmin hblk (Or.inl ⟨n, hn, hlin⟩) hJ rfl hRN).2,
    C56.baumann_c542 hmin hblk hn hlin hJ rfl hRN⟩

section A5

variable {L S : Subgroup G}

theorem card_im_of_sylow (D : PiData L) (hSN : S ≤ normalizer (L : Set G))
    (hsyl : IsSylowTwoOf S (L ⊔ S))
    (hsurj : Function.Surjective
      (D.π.comp (Subgroup.inclusion (sup_le Subgroup.le_normalizer hSN :
        L ⊔ S ≤ normalizer (L : Set G))))) :
    Nat.card (D.im S) = 8 := by
  have hHN : L ⊔ S ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSN
  have hS' : IsPGroup 2 (S.subgroupOf (L ⊔ S)) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  let P : Sylow 2 ↥(L ⊔ S) := hS'.toSylow hsyl.2.2
  have h1 := sylow_card_perm_five (P.mapSurjective hsurj)
  have h2 : ((P.mapSurjective hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) =
      (S.subgroupOf (L ⊔ S)).map (D.π.comp (Subgroup.inclusion hHN)) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : (S.subgroupOf (L ⊔ S)).map (D.π.comp (Subgroup.inclusion hHN)) = D.im S := by
    ext g
    rw [D.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hHN x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hsyl.1 hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [← h3, ← h2]
  exact h1

theorem exists_mem_thompsonJ_pi_ne_one_of (hL : IsShort2 L) (hSN : S ≤ normalizer (L : Set G))
    (hJ : ⁅L, thompsonJ S⁆ = L) (D : PiData L) (hLQ : ¬ L ≤ blockQ L) :
    ∃ y : ↥(normalizer (L : Set G)), (y : G) ∈ thompsonJ S ∧ D.π y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hLQ
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hLQ' : L ⊓ centralizer (blockU L : Set G) = pCoreOf 2 L :=
    C1.inf_centralizer_blockU_eq hL le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)
  calc L = ⁅L, thompsonJ S⁆ := hJ.symm
    _ ≤ blockQ L := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ y hy
      have hyN : y ∈ normalizer (L : Set G) := hSN (hJS hy)
      have hyL : y * ℓ⁻¹ * y⁻¹ ∈ L := (mem_normalizer_iff.mp hyN _).mp (inv_mem hℓ)
      have hcom : ⁅ℓ, y⁆ = ℓ * (y * ℓ⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have hcL : ⁅ℓ, y⁆ ∈ L := by rw [hcom]; exact mul_mem hℓ hyL
      have hπ : D.π (⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
          ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        have hy1 := hcon ⟨y, hyN⟩ hy
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        simp
      have hc := (D.hker _).1 hπ
      have hcC : ⁅ℓ, y⁆ ∈ centralizer (blockU L : Set G) := by
        rw [mem_centralizer_iff]
        intro u hu
        have h1 := hc u hu
        have h2 : (((⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
            ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹ :
              ↥(normalizer (L : Set G))) : ↥(normalizer (L : Set G))) : G) =
            ⁅ℓ, y⁆ := by
          simp [commutatorElement_def]
        rw [h2] at h1
        calc u * ⁅ℓ, y⁆ = (⁅ℓ, y⁆ * u * ⁅ℓ, y⁆⁻¹) * ⁅ℓ, y⁆ := by rw [h1]
          _ = ⁅ℓ, y⁆ * u := by group
      have h3 : ⁅ℓ, y⁆ ∈ L ⊓ centralizer (blockU L : Set G) := ⟨hcL, hcC⟩
      rw [hLQ'] at h3
      exact h3

theorem swapGen_imJ_of (hL : IsShort2 L) (hSN : S ≤ normalizer (L : Set G))
    (hUS : blockU L ≤ S) (D : PiData L) :
    ∀ g ∈ D.im (thompsonJ S),
      g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} := by
  have hU := isElemAbelian_blockU hL
  set Cl := Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} with hCl
  have hW : thompsonJ S ≤ (Cl.comap D.π).map (normalizer (L : Set G)).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    have haN : a ∈ normalizer (L : Set G) := hSN (hA.1 ha)
    refine Subgroup.mem_map.2 ⟨⟨a, haN⟩, ?_, rfl⟩
    show D.π ⟨a, haN⟩ ∈ Cl
    have hmem : D.π ⟨a, haN⟩ ∈ D.im A := D.pi_mem_im ha
    have := D.swapGen_im hU hUS hSN hA _ hmem
    refine Subgroup.closure_mono ?_ this
    intro s hs
    exact ⟨D.im_mono (GammaExtra.le_thompsonJ hA) hs.1, hs.2⟩
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.1 (hW hy)
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact hy'

theorem a5_core_single (hL : IsShort2 L) (hSN : S ≤ normalizer (L : Set G))
    (hUS : blockU L ≤ S) (hsyl : IsSylowTwoOf S (L ⊔ S)) (hJ : ⁅L, thompsonJ S⁆ = L)
    (P : A5Pi L) :
    ∃ τ₁ τ₂ : Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      P.im (thompsonJ S) = Subgroup.closure {τ₁, τ₂} ∧
      P.im (baum S) = Subgroup.closure {τ₁, τ₂} ∧ Nat.card (P.im S) = 8 ∧
      (∀ d ∈ P.im S, ∀ j ∈ P.im (thompsonJ S), d * j * d⁻¹ ∈ P.im (thompsonJ S)) := by
  classical
  have hHN : L ⊔ S ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSN
  have hU := isElemAbelian_blockU hL
  have hBS : baum S ≤ S := inf_le_left
  have hJB : thompsonJ S ≤ baum S := C5.thompsonJ_le_baum' S
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hXN : L ⊔ baum S ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (hBS.trans hSN)
  have hXH : L ⊔ baum S ≤ L ⊔ S := sup_le_sup_left hBS L
  let D : PiData L := P.toPiData
  let β := D.β
  let π := D.π
  have hcomp := D.hcomp
  have hα := P.hα
  have hαk := P.hαk
  have hπα := P.hπα
  have hLQ : ¬ L ≤ blockQ L := by
    intro hle
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [A5.Delta5.a5_card]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨ℓ, rfl⟩ := hα a
    apply ha
    have h1 : ℓ ∈ P.α.ker := by
      rw [hαk, mem_pCore_iff_mem_blockQ]
      exact hle ℓ.2
    exact h1
  obtain ⟨y₀, hy₀J, hy₀⟩ := exists_mem_thompsonJ_pi_ne_one_of hL hSN hJ D hLQ
  have hJ1 : ∃ j ∈ D.im (thompsonJ S), j ≠ 1 := ⟨D.π y₀, D.pi_mem_im hy₀J, hy₀⟩
  have hJsw := swapGen_imJ_of hL hSN hUS D
  obtain ⟨t, htJ, htsw⟩ := exists_swap_of_swapGen _ hJ1 hJsw
  have hπX : ∀ σ : Perm (Fin 5), ∃ x : ↥(L ⊔ baum S), π ⟨x, hXN x.2⟩ = σ := by
    intro σ
    by_cases hs : Equiv.Perm.sign σ = 1
    · obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩, ?_⟩
      have := hπα ℓ ℓ.2
      rw [hℓ] at this
      exact this
    · obtain ⟨y, hyJ, hyt⟩ := (D.mem_im).1 htJ
      have hsg : Equiv.Perm.sign (σ * t⁻¹) = 1 := by
        obtain ⟨a, b, hab, rfl⟩ := htsw
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · rw [h]; decide
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ * t⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hsg⟩
      have hyB : (y : G) ∈ baum S := hJB hyJ
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩ * ⟨y, Subgroup.mem_sup_right hyB⟩, ?_⟩
      have h1 := hπα ℓ ℓ.2
      rw [hℓ] at h1
      have h2 : π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) =
          π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * π y := by
        rw [← map_mul]
      show π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) = σ
      rw [h2, hyt]
      have h3 : π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ = σ * t⁻¹ := h1
      rw [h3]
      exact inv_mul_cancel_right σ t
  have hfsurj : Function.Surjective (D.π.comp (Subgroup.inclusion hHN)) := by
    intro σ
    obtain ⟨x, hx⟩ := hπX σ
    exact ⟨⟨x, hXH x.2⟩, hx⟩
  have hD8 : Nat.card (D.im S) = 8 := card_im_of_sylow D hSN hsyl hfsurj
  have hJn : ∀ d ∈ D.im S, ∀ j ∈ D.im (thompsonJ S), d * j * d⁻¹ ∈ D.im (thompsonJ S) := by
    intro d hd j hj'
    obtain ⟨s, hs, rfl⟩ := (D.mem_im).1 hd
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hj'
    have h1 : (s : G) * y * (s : G)⁻¹ ∈ thompsonJ S := thompsonJ_conj_mem hs hy
    have : D.π s * D.π y * (D.π s)⁻¹ = D.π (s * y * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact D.pi_mem_im (K := thompsonJ S) (y := s * y * s⁻¹) (by simpa using h1)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, -, hfix⟩ :=
    swap_core (D.im S) (D.im (thompsonJ S)) hD8 (D.im_mono hJS) hJn hJ1 hJsw
  have hBJ : D.im (baum S) ≤ D.im (thompsonJ S) := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := (D.mem_im).1 hg
    apply hfix
    intro w hw
    set u : ↥(blockU L) := β.symm (Multiplicative.ofAdd w) with hu
    have hwu : Multiplicative.toAdd (β u) = w := by simp [hu]
    have hcJ : ∀ y ∈ thompsonJ S, (y : G) * u = u * y := by
      intro y hy
      have hyN : y ∈ normalizer (L : Set G) := hSN (hJS hy)
      have hmem : y * (u : G) * y⁻¹ ∈ blockU L :=
        (mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hyN) u).mp u.2
      have h := hcomp ⟨y, hyN⟩ u ⟨_, hmem⟩ rfl
      have hfy : vact (π ⟨y, hyN⟩) w = w := hw _ (D.pi_mem_im (K := thompsonJ S) hy)
      rw [hwu, hfy] at h
      have h' : Multiplicative.toAdd (β ⟨y * (u : G) * y⁻¹, hmem⟩) =
          Multiplicative.toAdd (β u) := by rw [h, hwu]
      have h2 : (⟨_, hmem⟩ : ↥(blockU L)) = u := β.injective (Multiplicative.toAdd.injective h')
      have h3 : y * (u : G) * y⁻¹ = u := congrArg Subtype.val h2
      calc (y : G) * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h3]
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
    have huA : (u : G) ∈ A :=
      inf_centralizer_le_of_isMaxElemAbelian hU hUS hA
        ⟨u.2, mem_centralizer_iff.2 fun a ha => hcJ a (GammaExtra.le_thompsonJ hA ha)⟩
    have huJ : (u : G) ∈ thompsonJ S := GammaExtra.le_thompsonJ hA huA
    have huΩ : (u : G) ∈ omegaOneCenterOf (thompsonJ S) :=
      Subgroup.subset_closure ⟨⟨huJ, mem_centralizer_iff.2 fun y hy => hcJ y hy⟩,
        C1.blockU_sq hL u u.2⟩
    have hbc : (u : G) * b = b * u := mem_centralizer_iff.1 hb.2 u huΩ
    have h := hcomp b u u (by
      show (u : G) = (b : G) * (u : G) * (b : G)⁻¹
      rw [← hbc]; group)
    rw [hwu] at h
    exact h.symm
  have hBeq : D.im (baum S) = D.im (thompsonJ S) := le_antisymm hBJ (D.im_mono hJB)
  exact ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq.trans hJeq, hD8, hJn⟩

theorem exists_a5Pi_std (hL : IsShort2 L) (hSN : S ≤ normalizer (L : Set G))
    (hUS : blockU L ≤ S) (hsyl : IsSylowTwoOf S (L ⊔ S)) (hJ : ⁅L, thompsonJ S⁆ = L)
    (P : A5Pi L) :
    ∃ P' : A5Pi L, P'.im (thompsonJ S) = Estd ∧ P'.im (baum S) = Estd ∧ P'.im S = Dstd := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq, hD8, hJn⟩ := a5_core_single hL hSN hUS hsyl hJ P
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Perm (Fin 5)))).map (MulAut.conj ρ).toMonoidHom =
      Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  have hJ' : (P.conj ρ).im (thompsonJ S) = Estd := by rw [A5Pi.im_conj, hJeq, hcl]
  have hB' : (P.conj ρ).im (baum S) = Estd := by rw [A5Pi.im_conj, hBeq, hcl]
  have hnorm' : ∀ d ∈ (P.conj ρ).im S, ∀ j ∈ (P.conj ρ).im (thompsonJ S),
      d * j * d⁻¹ ∈ (P.conj ρ).im (thompsonJ S) := by
    intro d hd j hj'
    rw [A5Pi.im_conj] at hd hj' ⊢
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hj'
    refine Subgroup.mem_map.2 ⟨d₀ * j₀ * d₀⁻¹, hJn d₀ hd₀ j₀ hj₀, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : (P.conj ρ).im S ≤ Dstd := by
    intro d hd
    rw [mem_Dstd, mem_Dset]
    intro x hx
    have := hnorm' d hd x (by rw [hJ']; exact hx)
    rwa [hJ'] at this
  have hcard : Nat.card ((P.conj ρ).im S) = 8 := by
    rw [A5Pi.im_conj, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hD8]
  exact ⟨P.conj ρ, hJ', hB', Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])⟩

theorem blockU_le_pCoreOf_sup (hL : IsShort2 L) (hSN : S ≤ normalizer (L : Set G)) :
    blockU L ≤ pCoreOf 2 (L ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (C1.blockU_le_blockQ hL).trans ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact (sup_le Subgroup.le_normalizer hSN).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem sup_inf_centralizer_eq (hL : IsShort2 L) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (L : Set G)) :
    (L ⊔ S) ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ S) :=
  C1.inf_centralizer_blockU_eq hL le_sup_left (sup_le Subgroup.le_normalizer hSN)
    (fun _ hg => C1.exists_pow_mem_of_mem_sup hS2 hSN hg)

theorem a5_blockU_le_baum (hL : IsShort2 L) (h5 : IsAltType L 5) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (L : Set G)) (hsyl : IsSylowTwoOf S (L ⊔ S)) :
    blockU L ≤ baum S := by
  obtain ⟨P⟩ := nonempty_a5pi hL h5
  have hU := isElemAbelian_blockU hL
  have hQ := sup_inf_centralizer_eq hL hS2 hSN
  have hUQ := blockU_le_pCoreOf_sup hL hSN
  have hQS : pCoreOf 2 (L ⊔ S) ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hUS : blockU L ≤ S := hUQ.trans hQS
  have hQU : ∀ q ∈ pCoreOf 2 (L ⊔ S), ∀ u ∈ blockU L, q * u = u * q := by
    intro q hq u hu
    have hq' : q ∈ (L ⊔ S) ⊓ centralizer (blockU L : Set G) := by rw [hQ]; exact hq
    exact (mem_centralizer_iff.1 hq'.2 u hu).symm
  have haU : ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ S →
      IsElemAbelian 2 (aU L A) ∧ Nat.card A ≤ Nat.card ↥(aU L A) ∧
        aU L A ≤ pCoreOf 2 (L ⊔ S) := by
    intro A hA hAS
    have hAN : A ≤ normalizer (L : Set G) := hAS.trans hSN
    set K := A ⊓ centralizer (blockU L : Set G) with hK
    have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA
    have hcomm : ∀ k ∈ K, ∀ u ∈ blockU L, k * u = u * k := fun k hk u hu =>
      (mem_centralizer_iff.1 hk.2 u hu).symm
    have hB1e := B2F.isElemAbelian_sup_of_commute hKe hU hcomm
    have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
    have h3 : Nat.card ↥(K ⊓ blockU L) ≤
        Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) := by
      refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, mem_centralizer_iff.2 fun a ha => ?_⟩
      exact B2F.isElemAbelian_comm hA ha hx.1.1
    have h4 := P.card_im_mul hAN
    have h5' := P.card_fix hAN
    have h6 := P.card_blockU
    have h7 := card_mul_fix_le (P.im A) (P.im_elemAbelian hA).1 (P.im_elemAbelian hA).2
    have hbpos : 0 < Nat.card ↥(K ⊓ blockU L) := Nat.card_pos
    rw [h5'] at h3
    set p := Nat.card (P.im A)
    set f := Nat.card (FixΔ (P.im A))
    set b := Nat.card ↥(K ⊓ blockU L)
    set a := Nat.card ↥(K ⊔ blockU L)
    set k := Nat.card ↥K
    have h8 : Nat.card A ≤ a := by
      rw [← h4]
      have hab : a * b = k * 16 := by rw [h2, h6]
      have h9 : (k * p) * b ≤ a * b := by
        calc (k * p) * b ≤ (k * p) * f := Nat.mul_le_mul_left _ h3
          _ = k * (p * f) := by ring
          _ ≤ k * 16 := Nat.mul_le_mul_left _ h7
          _ = a * b := hab.symm
      have := Nat.le_of_mul_le_mul_right h9 hbpos
      nlinarith
    refine ⟨hB1e, h8, sup_le ?_ hUQ⟩
    intro x hx
    rw [← hQ]
    exact ⟨le_sup_right (a := L) (hAS hx.1), hx.2⟩
  have hΩ : omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 (L ⊔ S) := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    obtain ⟨he, hcard, hle⟩ := haU A₀ hA₀.2.1 hA₀.1
    have hmax : IsMaxElemAbelian S (aU L A₀) :=
      ⟨sup_le (inf_le_left.trans hA₀.1) hUS, he,
        fun B hBS hBe => (hA₀.2.2 B hBS hBe).trans hcard⟩
    rw [(omegaOne_centralizer_thompsonJ S).2]
    exact (iInf₂_le (aU L A₀) hmax).trans hle
  refine le_inf hUS ?_
  intro u hu
  rw [mem_centralizer_iff]
  intro z hz
  exact hQU z (hΩ hz) u hu

theorem a5_baum_inf_centralizer (hL : IsShort2 L) (h5 : IsAltType L 5) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (L : Set G)) (hsyl : IsSylowTwoOf S (L ⊔ S)) :
    baum S ⊓ centralizer (blockU L : Set G) =
      blockU L ⊔ (baum S ⊓ centralizer (L : Set G)) := by
  obtain ⟨P⟩ := nonempty_a5pi hL h5
  have hUB := a5_blockU_le_baum hL h5 hS2 hSN hsyl
  have hQ := sup_inf_centralizer_eq hL hS2 hSN
  have hBS : baum S ≤ S := inf_le_left
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
  refine le_antisymm (fun q hq => ?_) (sup_le (le_inf hUB ?_) (inf_le_inf_left _ ?_))
  · have hqP : q ∈ pCoreOf 2 (L ⊔ S) := by
      rw [← hQ]; exact ⟨le_sup_right (a := L) (hBS hq.1), hq.2⟩
    have hbb : ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU L :=
      C1.commutator_mem_blockU_of_mem_blockQ hL (fun l hl =>
        C1.commutator_mem_blockQ_of_mem_pCoreOf le_sup_left
          (sup_le Subgroup.le_normalizer hSN) hqP hl)
    have hqC : ∀ u ∈ blockU L, q * u = u * q := fun u hu =>
      (mem_centralizer_iff.1 hq.2 u hu).symm
    obtain ⟨u, hu, hc⟩ := AppCS2.exists_split_abs hL h5 P hbb hqC
    have huq : u * q ∈ baum S ⊓ centralizer (L : Set G) :=
      ⟨mul_mem (hUB hu) hq.1, mem_centralizer_iff.2 fun γ hγ => hc γ hγ⟩
    have e : q = u⁻¹ * (u * q) := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem hu)) (mem_sup_right huq)
  · intro u hu
    rw [mem_centralizer_iff]
    intro v hv
    exact C1.blockU_comm hL v hv u (C1.blockU_le_blockQ hL hu)
  · exact Subgroup.centralizer_le hUL

end A5

theorem baum_le_normalizer_of_central {L R : Subgroup G} (hL : IsShort2 L)
    (hperm : ∀ g ∈ R, g ∉ normalizer (L : Set G) →
      ∀ a ∈ L, ∀ b ∈ conjSubgroup L g, a * b = b * a)
    {e : G} (heU : e ∈ blockU L) (heZ : e ∉ blockZ L) (heR : e ∈ R)
    (hec : ∀ y ∈ thompsonJ R, y * e = e * y) :
    baum R ≤ normalizer (L : Set G) := by
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
  have hVe : IsElemAbelian 2 (blockU L ⊓ R) :=
    B2F.isElemAbelian_mono inf_le_left (isElemAbelian_blockU hL)
  have heA : ∀ A : Subgroup G, IsMaxElemAbelian R A → e ∈ A := fun A hA =>
    inf_centralizer_le_of_isMaxElemAbelian hVe inf_le_right hA
      ⟨⟨heU, heR⟩, mem_centralizer_iff.2 fun a ha => hec a (GammaExtra.le_thompsonJ hA ha)⟩
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
  have heJ : e ∈ thompsonJ R := GammaExtra.le_thompsonJ hA₀ (heA A₀ hA₀)
  have heΩ : e ∈ omegaOneCenterOf (thompsonJ R) :=
    Subgroup.subset_closure ⟨⟨heJ, mem_centralizer_iff.2 fun y hy => hec y hy⟩,
      C1.blockU_sq hL e heU⟩
  intro b hb
  by_contra hbN
  have hbe : e * b = b * e := mem_centralizer_iff.1 hb.2 e heΩ
  have heLb : e ∈ conjSubgroup L b := by
    rw [mem_conjSubgroup_iff]
    have : b * e * b⁻¹ = e := by rw [← hbe]; group
    rw [this]; exact hUL heU
  exact heZ ⟨heU, mem_centralizer_iff.2 fun a ha => (hperm b hb.1 hbN a ha e heLb)⟩

end CFSG.Quasithin.C58NS
