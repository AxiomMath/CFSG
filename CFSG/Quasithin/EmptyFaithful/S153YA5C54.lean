module

public import CFSG.Quasithin.EmptyFaithful.S153YGSet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.YG.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

theorem sylow_card_perm_five (P : Sylow 2 (Equiv.Perm (Fin 5))) : Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Fintype.card_perm]
  have h120 : (Nat.factorial (Fintype.card (Fin 5))) = 2 ^ 3 * 15 := by
    rw [Fintype.card_fin]; decide
  rw [h120, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

theorem card_im_S (hcs : WGen H S L) (hj : conjJoin S L = L) (D : PiData L)
    (hsurj : Function.Surjective
      (D.π.comp (Subgroup.inclusion (C56.H_le_normalizer hcs hj)))) :
    Nat.card (D.im S) = 8 := by
  have hHN := C56.H_le_normalizer hcs hj
  have hS := hcs.sylow
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have h1 := sylow_card_perm_five (P.mapSurjective hsurj)
  have h2 : ((P.mapSurjective hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) =
      (S.subgroupOf H).map (D.π.comp (Subgroup.inclusion hHN)) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : (S.subgroupOf H).map (D.π.comp (Subgroup.inclusion hHN)) = D.im S := by
    ext g
    rw [D.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hHN x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hS.1 hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [← h3, ← h2]
  exact h1

omit [Finite G] in
theorem thompsonJ_conj_mem {s y : G} (hs : s ∈ S) (hy : y ∈ thompsonJ S) :
    s * y * s⁻¹ ∈ thompsonJ S := by
  have h := cjSub_thompsonJ (S := S) (g := s⁻¹) (Subgroup.le_normalizer (inv_mem hs))
  have h2 : y ∈ cjSub s⁻¹ (thompsonJ S) := by rw [h]; exact hy
  rw [mem_cjSub] at h2
  simpa using h2

theorem exists_mem_thompsonJ_pi_ne_one (hcs : WGen H S L)
    (hj : conjJoin S L = L) (D : PiData L) (hLQ : ¬ L ≤ blockQ L) :
    ∃ y : ↥(Subgroup.normalizer (L : Set G)), (y : G) ∈ thompsonJ S ∧ D.π y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hLQ
  have hL : IsShort2 L := C56.isShort hcs
  have hSN := C56.S_le_normalizer hj
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hLQ' : L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L :=
    C1.inf_centralizer_blockU_eq hL le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)
  calc L = ⁅L, thompsonJ S⁆ := hcs.thompson.symm
    _ ≤ blockQ L := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ y hy
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hSN (hJS hy)
      have hyL : y * ℓ⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hℓ)
      have hcom : ⁅ℓ, y⁆ = ℓ * (y * ℓ⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have hcL : ⁅ℓ, y⁆ ∈ L := by rw [hcom]; exact mul_mem hℓ hyL
      have hπ : D.π (⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
          ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        have hy1 := hcon ⟨y, hyN⟩ hy
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        simp
      have hc := (D.hker _).1 hπ
      have hcC : ⁅ℓ, y⁆ ∈ Subgroup.centralizer (blockU L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := hc u hu
        have h2 : (((⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
            ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹ :
              ↥(Subgroup.normalizer (L : Set G))) : ↥(Subgroup.normalizer (L : Set G))) : G) =
            ⁅ℓ, y⁆ := by
          simp [commutatorElement_def]
        rw [h2] at h1
        calc u * ⁅ℓ, y⁆ = (⁅ℓ, y⁆ * u * ⁅ℓ, y⁆⁻¹) * ⁅ℓ, y⁆ := by rw [h1]
          _ = ⁅ℓ, y⁆ * u := by group
      have h3 : ⁅ℓ, y⁆ ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hcL, hcC⟩
      rw [hLQ'] at h3
      exact h3

theorem swapGen_imJ (hcs : WGen H S L) (hj : conjJoin S L = L)
    (D : PiData L) :
    ∀ g ∈ D.im (thompsonJ S),
      g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} := by
  have hL := C56.isShort hcs
  have hSN := C56.S_le_normalizer hj
  have hUS : blockU L ≤ S := (C56.blockU_le_pCoreOf hcs hj).trans (C56.pCoreOf_le_S hcs)
  have hU := isElemAbelian_blockU hL
  set Cl := Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ S) ∧ s.IsSwap} with hCl
  have hW : thompsonJ S ≤ (Cl.comap D.π).map (Subgroup.normalizer (L : Set G)).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hSN (hA.1 ha)
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

theorem a5_core {H S L : Subgroup G} (hcs : WGen H S L)
    (hj : conjJoin S L = L) (P : A5Pi L) :
    ∃ τ₁ τ₂ : Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      P.im (thompsonJ S) = Subgroup.closure {τ₁, τ₂} ∧
      P.im (baum S) = Subgroup.closure {τ₁, τ₂} ∧ Nat.card (P.im S) = 8 ∧
      (∃ d ∈ P.im S, d * τ₁ * d⁻¹ = τ₂) ∧ P.im (L ⊔ baum S) = ⊤ ∧
      (∀ d ∈ P.im S, ∀ j ∈ P.im (thompsonJ S), d * j * d⁻¹ ∈ P.im (thompsonJ S)) ∧
      ∀ g : Perm (Fin 5), (∀ w ∈ FixΔ (P.im (thompsonJ S)), vact g w = w) →
        g ∈ P.im (thompsonJ S) := by
  classical
  have hL : IsShort2 L := C56.isShort hcs
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := C56.S_le_normalizer hj
  have hHN := C56.H_le_normalizer hcs hj
  have hHeq : H = L ⊔ S := C56.H_eq hcs hj
  have hUS : blockU L ≤ S := (C56.blockU_le_pCoreOf hcs hj).trans (C56.pCoreOf_le_S hcs)
  have hU := isElemAbelian_blockU hL
  have hBS : baum S ≤ S := inf_le_left
  have hJB : thompsonJ S ≤ baum S := C5.thompsonJ_le_baum' S
  have hJS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hXN : L ⊔ baum S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (hBS.trans hSN)
  have hXH : L ⊔ baum S ≤ H := by rw [hHeq]; exact sup_le_sup_left hBS L
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
  obtain ⟨y₀, hy₀J, hy₀⟩ := exists_mem_thompsonJ_pi_ne_one hcs hj D hLQ
  have hJ1 : ∃ j ∈ D.im (thompsonJ S), j ≠ 1 := ⟨D.π y₀, D.pi_mem_im hy₀J, hy₀⟩
  have hJsw := swapGen_imJ hcs hj D
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
  have hD8 : Nat.card (D.im S) = 8 := card_im_S hcs hj D hfsurj
  have hJn : ∀ d ∈ D.im S, ∀ j ∈ D.im (thompsonJ S), d * j * d⁻¹ ∈ D.im (thompsonJ S) := by
    intro d hd j hj'
    obtain ⟨s, hs, rfl⟩ := (D.mem_im).1 hd
    obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hj'
    have h1 : (s : G) * y * (s : G)⁻¹ ∈ thompsonJ S := thompsonJ_conj_mem hs hy
    have : D.π s * D.π y * (D.π s)⁻¹ = D.π (s * y * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact D.pi_mem_im (K := thompsonJ S) (y := s * y * s⁻¹) (by simpa using h1)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hswap, hfix⟩ :=
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
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hSN (hJS hy)
      have hmem : y * (u : G) * y⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hyN) u).mp u.2
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
        ⟨u.2, Subgroup.mem_centralizer_iff.2 fun a ha => hcJ a (GammaExtra.le_thompsonJ hA ha)⟩
    have huJ : (u : G) ∈ thompsonJ S := GammaExtra.le_thompsonJ hA huA
    have huΩ : (u : G) ∈ omegaOneCenterOf (thompsonJ S) :=
      Subgroup.subset_closure ⟨⟨huJ, Subgroup.mem_centralizer_iff.2 fun y hy => hcJ y hy⟩,
        C1.blockU_sq hL u u.2⟩
    have hbc : (u : G) * b = b * u := Subgroup.mem_centralizer_iff.1 hb.2 u huΩ
    have h := hcomp b u u (by
      show (u : G) = (b : G) * (u : G) * (b : G)⁻¹
      rw [← hbc]; group)
    rw [hwu] at h
    exact h.symm
  have hBeq : D.im (baum S) = D.im (thompsonJ S) := le_antisymm hBJ (D.im_mono hJB)
  refine ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq.trans hJeq, hD8, hswap, ?_, hJn, hfix⟩
  refine eq_top_iff.2 fun σ _ => ?_
  obtain ⟨x, hx⟩ := hπX σ
  exact (D.mem_im).2 ⟨⟨x, hXN x.2⟩, x.2, hx⟩

end CFSG.Quasithin.YG.AppC
