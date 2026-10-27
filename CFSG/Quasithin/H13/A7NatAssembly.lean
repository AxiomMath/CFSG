module

public import CFSG.Quasithin.H13.A7NatPre
public import CFSG.Quasithin.H13.A7NatSchur
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

theorem toAdd_allOnes_zpow_seven (k : ℤ) (i : Fin 7) :
    Multiplicative.toAdd (G6.allOnes 7 ^ k) i = (k : ZMod 2) := by
  rw [toAdd_zpow]
  simp [G6.allOnes]

theorem altDn_seven_ker_eq_bot : (FFModel.altDn 7).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 = ⊥
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  have hx2 : G6.allOnes 7 ^ k ∈ G6.coreMod 7 := hx2
  rw [G6.mem_coreMod] at hx2
  simp only [toAdd_allOnes_zpow_seven, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hx2
  have hk : (k : ZMod 2) = 0 := by
    have h7 : (7 : ZMod 2) = 1 := by decide
    rwa [nsmul_eq_mul, Nat.cast_ofNat, h7, one_mul] at hx2
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_allOnes_zpow_seven, hk]
  rfl

theorem altDn_seven_mk_injective :
    Function.Injective (QuotientGroup.mk : ↥(FFModel.altDn 7).sec →
      ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) := by
  intro a b h
  rw [QuotientGroup.eq, mem_subgroupOf, altDn_seven_ker_eq_bot, Subgroup.mem_bot] at h
  have h' : a⁻¹ * b = 1 := Subtype.ext h
  rw [inv_mul_eq_one] at h'
  exact h'

@[expose] def coreModSevenEquiv : ↥(G6.coreMod 7) ≃* Multiplicative (evenWeight 7) where
  toFun m := Multiplicative.ofAdd ⟨Multiplicative.toAdd (m : G6.PermMod 7), m.2⟩
  invFun x := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd x : evenWeight 7) :
    Fin 7 → ZMod 2), (Multiplicative.toAdd x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

section Coord

variable {G : Type} [Group G]

theorem exists_coord_of_alternatingNatural {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ normalizer (V : Set G))
    (hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 7)
    (hCV : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ := by
  classical
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, hβk, mem_subgroupOf] at hu
    rw [Subgroup.mem_bot]
    have h1 : ((u : V) : G) ∈ V ⊓ centralizer (L : Set G) := ⟨(u : V).2, hu⟩
    rw [hCV, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  set Q7 := ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec
  let e2 : (⊤ : Subgroup V) ≃* Q7 := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  let e3 : Q7 ≃* ↥(FFModel.altDn 7).sec :=
    (MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨altDn_seven_mk_injective, QuotientGroup.mk_surjective⟩).symm
  let ψ : V ≃* Multiplicative (evenWeight 7) :=
    Subgroup.topEquiv.symm.trans (e2.trans (e3.trans coreModSevenEquiv))
  have hmk : ∀ u : V, (QuotientGroup.mk (e3 (β ⟨u, mem_top u⟩)) : Q7) = β ⟨u, mem_top u⟩ :=
    fun u => e3.symm_apply_apply (β ⟨u, mem_top u⟩)
  have hvec : ∀ u : V, vec ψ u =
      Multiplicative.toAdd ((e3 (β ⟨u, mem_top u⟩)).1 : G6.PermMod 7) :=
    fun u => rfl
  have hequi : ∀ (γ : alternatingGroup (Fin 7)) (u : V),
      vec ψ (((π γ : autOn L V) : MulAut V) u) = permAct7 γ (vec ψ u) := by
    intro γ u
    set m := e3 (β ⟨u, mem_top u⟩) with hm
    have hm' : G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7) ∈ G6.coreMod 7 :=
      G6.permAct_mem_coreMod _ m.2
    have h1 := hβe γ ⟨u, mem_top u⟩ m (mem_top _) hm' (hmk u).symm
    have h2 : e3 (β ⟨((π γ : autOn L V) : MulAut V) u, mem_top _⟩) =
        ⟨G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7), hm'⟩ := by
      rw [h1]
      exact e3.apply_symm_apply _
    rw [hvec, h2, hvec, ← hm]
    rfl
  have hconj : ∀ (l : G) (hl : l ∈ L), ∃ γ : alternatingGroup (Fin 7),
      ∀ x : V, ((((π γ : autOn L V) : MulAut V) x : V) : G) = l * x * l⁻¹ := by
    intro l hl
    have hmem : conjAct V ⟨l, hLV hl⟩ ∈ autOn L V :=
      Subgroup.mem_map_of_mem _ (show (⟨l, hLV hl⟩ : normalizer (V : Set G)) ∈
        L.subgroupOf (normalizer (V : Set G)) from hl)
    obtain ⟨γ, hγ⟩ := hπs ⟨_, hmem⟩
    refine ⟨γ, fun x => ?_⟩
    rw [hγ]
    rfl
  refine ⟨ψ, fun l hl => ?_, fun σ hσ => ?_⟩
  · obtain ⟨γ, hγ⟩ := hconj l hl
    refine ⟨γ, γ.2, fun x y hxy => ?_⟩
    have : y = ((π γ : autOn L V) : MulAut V) x := Subtype.ext (by rw [hxy, hγ])
    rw [this, hequi]
  · obtain ⟨⟨a, ha⟩, ha'⟩ : ∃ a, a = π ⟨σ, hσ⟩ := ⟨_, rfl⟩
    obtain ⟨⟨l, hlN⟩, hlL, hla⟩ := Subgroup.mem_map.1 ha
    have hlL' : l ∈ L := hlL
    refine ⟨l, hlL', fun x y hxy => ?_⟩
    have h1 : ((π ⟨σ, hσ⟩ : autOn L V) : MulAut V) = conjAct V ⟨l, hlN⟩ := by
      rw [← ha']
      exact hla.symm
    have : y = ((π ⟨σ, hσ⟩ : autOn L V) : MulAut V) x := Subtype.ext (by rw [hxy, h1]; rfl)
    rw [this, hequi]

theorem nact_of_lact {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hNM : normalizer (V : Set G) ≤ normalizer (L : Set G)) :
    ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct ψ n σ := by
  classical
  intro n hn
  let c : V → V := fun x => ⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn x).1 x.2⟩
  have hcmul : ∀ x y : V, c (x * y) = c x * c y := fun x y => Subtype.ext (by
    show n * (x * y : G) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹)
    group)
  let f : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2 := fun e =>
    if he : e ∈ evenWeight 7 then vec ψ (c (ψ.symm (Multiplicative.ofAdd ⟨e, he⟩))) else 0
  have hsymm : ∀ x : V, ψ.symm (Multiplicative.ofAdd ⟨vec ψ x, vec_mem ψ x⟩) = x := by
    intro x
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hf : ∀ x : V, f (vec ψ x) = vec ψ (c x) := by
    intro x
    simp only [f, vec_mem ψ x, ↓reduceDIte, hsymm]
  have hcoord : ∀ x y : V, (y : G) = n * x * n⁻¹ → f (vec ψ x) = vec ψ y := by
    intro x y hxy
    rw [hf]
    congr 1
    exact Subtype.ext hxy.symm
  obtain ⟨τ, hτ⟩ := exists_perm_of_normalizes_alternating (f := f)
    (fun e he => by
      obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
      rw [hf]
      exact vec_mem ψ _)
    (fun e he e' he' => by
      obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
      obtain ⟨y, rfl⟩ := exists_vec_eq ψ he'
      rw [← vec_mul, hf, hf, hf, hcmul, vec_mul])
    (fun e he h => by
      obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
      rw [hf, vec_eq_zero_iff] at h
      have hx : x = 1 := by
        have h1 : (n * x * n⁻¹ : G) = 1 := congrArg Subtype.val h
        have h2 : (x : G) = 1 := by
          calc (x : G) = n⁻¹ * (n * x * n⁻¹) * n := by group
            _ = 1 := by rw [h1]; group
        exact Subtype.ext h2
      rw [hx, vec_one])
    (fun e he => by
      obtain ⟨y, rfl⟩ := exists_vec_eq ψ he
      let x : V := ⟨n⁻¹ * y * n, by
        have := (mem_normalizer_iff.1 (inv_mem hn) y).1 y.2
        rwa [inv_inv] at this⟩
      refine ⟨vec ψ x, vec_mem ψ x, ?_⟩
      apply hcoord
      show (y : G) = n * (n⁻¹ * y * n) * n⁻¹
      group)
    (fun σ hσ => by
      obtain ⟨l, hl, hlσ⟩ := hLonto σ hσ
      have hnl : n * l * n⁻¹ ∈ L := (mem_normalizer_iff.1 (hNM hn) l).1 hl
      obtain ⟨σ', hσ', hσ'act⟩ := hLact _ hnl
      refine ⟨σ', hσ', fun e he => ?_⟩
      obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
      let y : V := ⟨l * x * l⁻¹, (mem_normalizer_iff.1 (hLV hl) x).1 x.2⟩
      have hy : vec ψ y = permAct7 σ (vec ψ x) := hlσ x y rfl
      rw [← hy, hf, hf]
      refine hσ'act (c x) (c y) ?_
      show n * (l * x * l⁻¹) * n⁻¹ = n * l * n⁻¹ * (n * x * n⁻¹) * (n * l * n⁻¹)⁻¹
      group)
  exact ⟨τ, fun x y hxy => by rw [← hcoord x y hxy, hτ _ (vec_mem ψ x)]⟩

end Coord

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_hyp1223 (h331 : Stmt3_3_1) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  obtain ⟨M', hM', hVM'⟩ := exists_maxTwoLocal_ge (L := normalizer (V : Set G)) ⟨V, hV1, hV2, rfl⟩
  have hLT : L ⊔ T ≤ M' := (sup_le hyp.irrPlus.2.2.1 hTV).trans hVM'
  rw [← huniq M' hM' hLT]
  exact hVM'

theorem exists_A7NatPre (h331 : Stmt3_3_1) {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hTI : ∀ m ∈ normalizer (L : Set G),
      CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥)
    [IsMulCommutative ↥V]
    (hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 7)
    (hCV : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ ψ : V ≃* Multiplicative (evenWeight 7), A7NatPre T L V ψ := by
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  obtain ⟨ψ, hLact, hLonto⟩ := exists_coord_of_alternatingNatural hLV hnat hCV
  have hNM := normalizer_le_of_hyp1223 h331 hyp hVT hTV
  exact ⟨ψ, ⟨hVT, hLV, hTV, hLact, hLonto, nact_of_lact hLV hLact hLonto hNM, hNM, hTI⟩⟩

end Assembly

end CFSG.Quasithin.H13.A7
