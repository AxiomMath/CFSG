module

public import CFSG.Quasithin.H13.A7NatAssembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.H13.A7
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_coord_bot {K V : Subgroup G} [IsMulCommutative ↥V]
    (hKV : K ≤ normalizer (V : Set G))
    (hnat : AlternatingNatural (V := ↥V) (autOn K V) ⊤ ⊥ 7) :
    ∃ ψ : V ≃* Multiplicative (evenWeight 7),
      (∀ k ∈ K, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ k σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ k ∈ K, IsCoordAct ψ k σ := by
  classical
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, hβk] at hu
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hu))
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
      vec ψ (((π γ : autOn K V) : MulAut V) u) = permAct7 γ (vec ψ u) := by
    intro γ u
    set m := e3 (β ⟨u, mem_top u⟩) with hm
    have hm' : G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7) ∈ G6.coreMod 7 :=
      G6.permAct_mem_coreMod _ m.2
    have h1 := hβe γ ⟨u, mem_top u⟩ m (mem_top _) hm' (hmk u).symm
    have h2 : e3 (β ⟨((π γ : autOn K V) : MulAut V) u, mem_top _⟩) =
        ⟨G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7), hm'⟩ := by
      rw [h1]
      exact e3.apply_symm_apply _
    rw [hvec, h2, hvec, ← hm]
    rfl
  have hconj : ∀ (k : G) (hk : k ∈ K), ∃ γ : alternatingGroup (Fin 7),
      ∀ x : V, ((((π γ : autOn K V) : MulAut V) x : V) : G) = k * x * k⁻¹ := by
    intro k hk
    have hmem : conjAct V ⟨k, hKV hk⟩ ∈ autOn K V :=
      Subgroup.mem_map_of_mem _ (show (⟨k, hKV hk⟩ : normalizer (V : Set G)) ∈
        K.subgroupOf (normalizer (V : Set G)) from hk)
    obtain ⟨γ, hγ⟩ := hπs ⟨_, hmem⟩
    refine ⟨γ, fun x => ?_⟩
    rw [hγ]
    rfl
  refine ⟨ψ, fun k hk => ?_, fun σ hσ => ?_⟩
  · obtain ⟨γ, hγ⟩ := hconj k hk
    refine ⟨γ, γ.2, fun x y hxy => ?_⟩
    have : y = ((π γ : autOn K V) : MulAut V) x := Subtype.ext (by rw [hxy, hγ])
    rw [this, hequi]
  · obtain ⟨⟨a, ha⟩, ha'⟩ : ∃ a, a = π ⟨σ, hσ⟩ := ⟨_, rfl⟩
    obtain ⟨⟨k, hkN⟩, hkK, hka⟩ := Subgroup.mem_map.1 ha
    have hkK' : k ∈ K := hkK
    refine ⟨k, hkK', fun x y hxy => ?_⟩
    have h1 : ((π ⟨σ, hσ⟩ : autOn K V) : MulAut V) = conjAct V ⟨k, hkN⟩ := by
      rw [← ha']
      exact hka.symm
    have : y = ((π ⟨σ, hσ⟩ : autOn K V) : MulAut V) x := Subtype.ext (by rw [hxy, h1]; rfl)
    rw [this, hequi]

theorem exists_coordAct {K V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hKV : K ≤ normalizer (V : Set G))
    (hKact : ∀ k ∈ K, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ k σ)
    (hKonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ k ∈ K, IsCoordAct ψ k σ) {n : G}
    (hn : n ∈ normalizer (V : Set G)) (hnK : n ∈ normalizer (K : Set G)) :
    ∃ σ, IsCoordAct ψ n σ := by
  classical
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
      obtain ⟨k, hk, hkσ⟩ := hKonto σ hσ
      have hnk : n * k * n⁻¹ ∈ K := (mem_normalizer_iff.1 hnK k).1 hk
      obtain ⟨σ', hσ', hσ'act⟩ := hKact _ hnk
      refine ⟨σ', hσ', fun e he => ?_⟩
      obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
      let y : V := ⟨k * x * k⁻¹, (mem_normalizer_iff.1 (hKV hk) x).1 x.2⟩
      have hy : vec ψ y = permAct7 σ (vec ψ x) := hkσ x y rfl
      rw [← hy, hf, hf]
      refine hσ'act (c x) (c y) ?_
      show n * (k * x * k⁻¹) * n⁻¹ = n * k * n⁻¹ * (n * x * n⁻¹) * (n * k * n⁻¹)⁻¹
      group)
  exact ⟨τ, fun x y hxy => by rw [← hcoord x y hxy, hτ _ (vec_mem ψ x)]⟩

end CFSG.Quasithin.Vol2.Ch11.O10
