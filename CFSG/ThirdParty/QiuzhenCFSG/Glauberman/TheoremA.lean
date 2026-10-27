module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem4_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman Theorem A (the ZJ-theorem)

Proof of Theorem A of George Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canadian Journal of Mathematics 20 (1968), 1101–1135 — reference [6] of the
dihedral-Sylow project — following the validated transcription in
`refs/glauberman-p-stable.tex` (Theorem A at L301–L306, proof at L974–L989).

The target statement is exactly the wrapper's `Glauberman.theoremA`; it is declared
here in the module namespace `Glauberman.TheoremA` (so that callers can use
it into the wrapper without a name clash), as `Glauberman.TheoremA.theoremA`.

Proof outline (tex L974–L989): let `P = O_p(G)` and `Z = Z(J(S))`.
1. `Z` is Abelian, `Z ≤ S` and `Z ⊴ S` (local copies of the Chapter8_2 lemmas,
   which are module-private there).
2. `[P,Z,Z] = 1` via `commutator_commutator_eq_bot_of_abelian_normalizer`
   (`Glauberman.pStability`).
3. `Z ⊆ P`: for `z ∈ Z`, the p-stability hypothesis applied to `P` and `z` gives the
   coset of `z` modulo `C_G(P)` in `O_p(G/C_G(P))`; the plumbing lemma
   `pCore_quotient_centralizer_le_of_centralizer_le_core` (hypothesis `C_G(P) ⊆ P`)
   puts that coset in `P·C_G(P)/C_G(P)`, and `C_G(P) ⊆ P` pulls `z` back into `P`.
4. Theorem 4.3 (`Glauberman.theorem4_3`) with `B = P` gives `Z ∩ P ⊴ G`; since
   `Z ⊆ P`, this is `Z ⊴ G`.
5. Characteristic: for `φ : G ≃* G`, `S.map φ` is a Sylow `p`-subgroup, hence
   `S^g = S.map φ` for some `g` (Sylow conjugacy); `thompsonCenter_map_mulEquiv`
   transports `Z(J(-))` across `φ` and across `conj g`; `Z ⊴ G` gives
   `Z^g = Z`, so `Z^φ = Z`.

The non-public helpers of `FeitThompson/Gorenstein/Chapter8_2.lean` and
`Glauberman/Theorem5_1.lean` used below are reproduced as local copies (module-private
declarations are not importable across modules in this repo).
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local copies of non-public Chapter8_2 / Theorem5_1 helpers -/

/-- `J(P) ≤ P`.  Local copy of the module-private `thompsonSubgroup_le` of
`FeitThompson/Gorenstein/Chapter8_2.lean`. -/
theorem thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

/-- `Z(J(P)) ≤ P`.  Local copy of the module-private `thompsonCenter_le` of
`FeitThompson/Gorenstein/Chapter8_2.lean`. -/
theorem thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := thompsonSubgroup_le (G := G) P

/-- `Z(J(P)) ⊴ P` for a Sylow `p`-subgroup `P`.  Local copy of the module-private
`thompsonCenter_normal_subgroupOf_sylow` of `FeitThompson/Gorenstein/Chapter8_2.lean`. -/
theorem thompsonCenter_normal_subgroupOf_sylow
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    ((thompsonCenter (G := G) (P : Subgroup G)).subgroupOf (P : Subgroup G)).Normal := by
  classical
  let S : Subgroup G := (P : Subgroup G)
  let J : Subgroup G := thompsonSubgroup (G := G) S
  have hJ_map_eq :
      ∀ g ∈ S, J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    let e : G ≃* G := MulAut.conj g
    have himage :
        (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S =
          thompsonAbelianSubgroups (G := G) S := by
      ext B
      constructor
      · rintro ⟨A, hA, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · change A.map (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) ≤ S
          exact Subgroup.conj_smul_le_of_le hA.1 ⟨g, hg⟩
        · let : IsMulCommutative A := hA.2.1
          exact Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.symm.toMonoidHom ≤ S := by
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            simpa [e] using S.mul_mem (S.mul_mem (S.inv_mem hg) (hC hy)) hg
          have hCpre_comm : IsMulCommutative (C.map e.symm.toMonoidHom) := by
            infer_instance
          have hAmax := hA.2.2 (C.map e.symm.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.symm.injective
            _ ≤ Nat.card A := hAmax
            _ = Nat.card (A.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := A) e.injective
      · intro hB
        refine ⟨B.map e.symm.toMonoidHom, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            simpa [e] using S.mul_mem (S.mul_mem (S.inv_mem hg) (hB.1 hy)) hg
          · let : IsMulCommutative B := hB.2.1
            exact Subgroup.map_isMulCommutative (H := B) e.symm.toMonoidHom
          · intro C hC hCcomm
            have hCpre_le : C.map e.toMonoidHom ≤ S := by
              change C.map (MulDistribMulAction.toMonoidHom G (MulAut.conj g)) ≤ S
              exact Subgroup.conj_smul_le_of_le hC ⟨g, hg⟩
            have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
              infer_instance
            have hBmax := hB.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
            calc
              Nat.card C = Nat.card (C.map e.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := C) e.injective
              _ ≤ Nat.card B := hBmax
              _ = Nat.card (B.map e.symm.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := B) e.symm.injective
        · ext x
          simp
    calc
      J.map (MulAut.conj g).toMonoidHom
          = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) S)) := rfl
      _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S) := by
        simp
      _ = J := by simpa [J, thompsonSubgroup] using congrArg sSup himage
  refine (Subgroup.normal_subgroupOf_iff (thompsonCenter_le (G := G) S)).2 ?_
  intro z g hz hg
  refine ⟨?_, ?_⟩
  · have hzJ : z ∈ J := by
      simpa [thompsonCenter, centerIn, J] using hz.1
    have hzmap :
        g * z * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzJ
    rwa [hJ_map_eq g hg] at hzmap
  · exact Subgroup.mem_centralizer_iff.mpr <| by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ J := by
        have hymap :
            g⁻¹ * y * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom := by
          simpa [J] using
            (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy)
        rwa [hJ_map_eq g⁻¹ (S.inv_mem hg)] at hymap
      have hzcent :
          z ∈ Subgroup.centralizer (J : Set G) := by
        simpa [thompsonCenter, centerIn, J] using hz.2
      have hzcent' := Subgroup.mem_centralizer_iff.mp hzcent
      have hcomm : z * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z := (hzcent' _ hy').symm
      have hcomm' := congrArg (fun x : G => g * x * g⁻¹) hcomm.symm
      simpa [mul_assoc] using hcomm'

/-- The Thompson subgroup commutes with the subgroup map.  Local copy of the
module-private `thompsonSubgroup_top_map_subtype` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonSubgroup_top_map_subtype (S : Subgroup G) :
    (thompsonSubgroup (G := S) (⊤ : Subgroup S)).map S.subtype = thompsonSubgroup (G := G) S := by
  classical
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    exact (Subgroup.map_le_iff_le_comap).mp <| le_sSup <| by
      refine ⟨?_, ?_, ?_⟩
      · simpa using (Subgroup.map_subtype_le (H := S) (K := A))
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) S.subtype
      · intro B hB hBcomm
        let B' : Subgroup S := B.subgroupOf S
        have hAmax := hA.2.2 B' (by simp) (by
          let : IsMulCommutative B := hBcomm
          infer_instance)
        calc
          Nat.card B = Nat.card B' := by
            simpa [B', Subgroup.map_subgroupOf_eq_of_le hB] using
              (Subgroup.card_subtype S B')
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map S.subtype) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) S.subtype_injective
  · refine sSup_le ?_
    intro A hA
    have hAin :
        A.subgroupOf S ∈ thompsonAbelianSubgroups (G := S) (⊤ : Subgroup S) := by
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative A := hA.2.1
        infer_instance
      · intro B hB hBcomm
        have hAmax := hA.2.2 (B.map S.subtype) (by
          simpa using (Subgroup.map_subtype_le (H := S) (K := B))) (by
            exact Subgroup.map_isMulCommutative (H := B) S.subtype)
        calc
          Nat.card B = Nat.card (B.map S.subtype) := by
            symm
            exact Subgroup.card_subtype S B
      _ ≤ Nat.card A := hAmax
      _ = Nat.card (A.subgroupOf S) := by
            simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
              (Subgroup.card_subtype S (A.subgroupOf S))
    calc
      A = (A.subgroupOf S).map S.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA.1]
      _ ≤ (thompsonSubgroup (G := S) (⊤ : Subgroup S)).map S.subtype := by
        exact Subgroup.map_mono (le_sSup hAin)

/-- `centerIn` commutes with the subgroup map.  Local copy of the module-private
`centerIn_top_map_subtype` of `Glauberman/Theorem5_1.lean`. -/
private theorem centerIn_top_map_subtype (S : Subgroup G) (H : Subgroup S) :
    (centerIn (G := S) H).map S.subtype = centerIn (G := G) (H.map S.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyH : y ∈ H := hy.1
    have hyC : y ∈ Subgroup.centralizer (H : Set S) := hy.2
    refine ⟨Subgroup.mem_map_of_mem S.subtype hyH, ?_⟩
    show ∀ h ∈ (H.map S.subtype : Set G), h * S.subtype y = S.subtype y * h
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact congrArg S.subtype ((Subgroup.mem_centralizer_iff.mp hyC) _ hw)
  · intro hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨y, ⟨hy, ?_⟩, rfl⟩
    have hxC : S.subtype y ∈ Subgroup.centralizer (H.map S.subtype : Set G) := hx.2
    show ∀ h ∈ (H : Set S), h * y = y * h
    intro z hz
    have hzmap : S.subtype z ∈ H.map S.subtype := Subgroup.mem_map_of_mem S.subtype hz
    exact S.subtype_injective <| by
      simpa using (Subgroup.mem_centralizer_iff.mp hxC) _ hzmap

/-- `Z(J(⊤))` inside a subgroup maps to `Z(J(S))` in the ambient group.  Local copy of
the module-private `thompsonCenter_top_map_subtype` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonCenter_top_map_subtype (S : Subgroup G) :
    (thompsonCenter (G := S) (⊤ : Subgroup S)).map S.subtype = thompsonCenter (G := G) S := by
  calc
    (thompsonCenter (G := S) (⊤ : Subgroup S)).map S.subtype
        = (centerIn (G := S) (thompsonSubgroup (G := S) (⊤ : Subgroup S))).map S.subtype := rfl
    _ = centerIn (G := G) ((thompsonSubgroup (G := S) (⊤ : Subgroup S)).map S.subtype) :=
      centerIn_top_map_subtype S (thompsonSubgroup (G := S) (⊤ : Subgroup S))
    _ = thompsonCenter (G := G) S := by
      rw [thompsonSubgroup_top_map_subtype]
      rfl

/-- `centerIn` commutes with an isomorphism between groups.  Local copy of the
module-private `centerIn_map_mulEquiv` of `Glauberman/Theorem5_1.lean`. -/
private theorem centerIn_map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (J : Subgroup G) :
    (centerIn (G := G) J).map e.toMonoidHom = centerIn (G := H) (J.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem e.toMonoidHom hy.1, ?_⟩
    show ∀ h ∈ (J.map e.toMonoidHom : Set H), h * e y = e y * h
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    simpa [map_mul] using congrArg e ((Subgroup.mem_centralizer_iff.mp hy.2) _ hw)
  · intro hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨y, ⟨hy, ?_⟩, rfl⟩
    show ∀ h ∈ (J : Set G), h * y = y * h
    intro z hz
    have hzmap : e z ∈ J.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hz
    exact e.injective <| by
      simpa [map_mul] using (Subgroup.mem_centralizer_iff.mp hx.2) _ hzmap

/-- The Thompson subgroup commutes with an isomorphism between groups.  Local copy of
the module-private `thompsonSubgroup_top_map_mulEquiv` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonSubgroup_top_map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    (thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonSubgroup (G := H) (⊤ : Subgroup H) := by
  classical
  have himage :
      (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G) =
        thompsonAbelianSubgroups (G := H) (⊤ : Subgroup H) := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative B := hB.2.1
        exact Subgroup.map_isMulCommutative (H := B) e.toMonoidHom
      · intro C _ hCcomm
        have hBmax := hB.2.2 (C.map e.symm.toMonoidHom) (by simp) (by
          let : IsMulCommutative C := hCcomm
          exact Subgroup.map_isMulCommutative (H := C) e.symm.toMonoidHom)
        calc
          Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := C) e.symm.injective
          _ ≤ Nat.card B := hBmax
          _ = Nat.card (B.map e.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := B) e.injective
    · intro hA
      refine ⟨A.map e.symm.toMonoidHom, ?_, ?_⟩
      · refine ⟨by simp, ?_, ?_⟩
        · let : IsMulCommutative A := hA.2.1
          exact Subgroup.map_isMulCommutative (H := A) e.symm.toMonoidHom
        · intro C _ hCcomm
          have hAmax := hA.2.2 (C.map e.toMonoidHom) (by simp) (by
            let : IsMulCommutative C := hCcomm
            exact Subgroup.map_isMulCommutative (H := C) e.toMonoidHom)
          calc
            Nat.card C = Nat.card (C.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.injective
            _ ≤ Nat.card A := hAmax
            _ = Nat.card (A.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := A) e.symm.injective
      · ext x
        simp
  calc
    (thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom
        = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G))) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) (⊤ : Subgroup G)) := by
      simp
    _ = thompsonSubgroup (G := H) (⊤ : Subgroup H) := by
      simpa [thompsonSubgroup] using congrArg sSup himage

/-- `Z(J(⊤))` commutes with an isomorphism between groups.  Local copy of the
module-private `thompsonCenter_top_map_mulEquiv` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonCenter_top_map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    (thompsonCenter (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonCenter (G := H) (⊤ : Subgroup H) := by
  calc
    (thompsonCenter (G := G) (⊤ : Subgroup G)).map e.toMonoidHom
        = centerIn (G := H) ((thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom) := by
          exact centerIn_map_mulEquiv e (thompsonSubgroup (G := G) (⊤ : Subgroup G))
    _ = thompsonCenter (G := H) (⊤ : Subgroup H) := by
          rw [thompsonSubgroup_top_map_mulEquiv]
          rfl

/-- The Thompson subgroup of the image of a subgroup under an automorphism.  Local copy
of the module-private `thompsonSubgroup_map_mulEquiv` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonSubgroup_map_mulEquiv (e : G ≃* G) (P : Subgroup G) :
    thompsonSubgroup (P.map e.toMonoidHom) = (thompsonSubgroup P).map e.toMonoidHom := by
  classical
  let φ : ↥P ≃* ↥(P.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have h1 : thompsonSubgroup (P.map e.toMonoidHom) =
      Subgroup.map (P.map e.toMonoidHom).subtype
        (thompsonSubgroup (⊤ : Subgroup ↥(P.map e.toMonoidHom))) := by
    simpa using (thompsonSubgroup_top_map_subtype (G := G) (S := P.map e.toMonoidHom)).symm
  have h2 : thompsonSubgroup (⊤ : Subgroup ↥(P.map e.toMonoidHom)) =
      (thompsonSubgroup (⊤ : Subgroup ↥P)).map φ.toMonoidHom := by
    exact (thompsonSubgroup_top_map_mulEquiv (G := ↥P) (H := ↥(P.map e.toMonoidHom)) φ).symm
  have h3 : Subgroup.map (P.map e.toMonoidHom).subtype
        ((thompsonSubgroup (⊤ : Subgroup ↥P)).map φ.toMonoidHom) =
      (thompsonSubgroup (⊤ : Subgroup ↥P)).map
        ((P.map e.toMonoidHom).subtype.comp φ.toMonoidHom) := by
    rw [Subgroup.map_map]
  have h4 : (thompsonSubgroup (⊤ : Subgroup ↥P)).map
        ((P.map e.toMonoidHom).subtype.comp φ.toMonoidHom) =
      (thompsonSubgroup (⊤ : Subgroup ↥P)).map (e.toMonoidHom.comp P.subtype) := by
    rfl
  rw [h1, h2, h3, h4]
  rw [← Subgroup.map_map]
  rw [thompsonSubgroup_top_map_subtype]

/-- `Z(J(P))` commutes with an automorphism of the ambient group.  Local copy of the
module-private `thompsonCenter_map_mulEquiv` of `Glauberman/Theorem5_1.lean`. -/
private theorem thompsonCenter_map_mulEquiv (e : G ≃* G) (P : Subgroup G) :
    thompsonCenter (P.map e.toMonoidHom) = (thompsonCenter P).map e.toMonoidHom := by
  classical
  let φ : ↥P ≃* ↥(P.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have h1 : thompsonCenter (P.map e.toMonoidHom) =
      Subgroup.map (P.map e.toMonoidHom).subtype
        (thompsonCenter (⊤ : Subgroup ↥(P.map e.toMonoidHom))) := by
    simpa using (thompsonCenter_top_map_subtype (G := G) (S := P.map e.toMonoidHom)).symm
  have h2 : thompsonCenter (⊤ : Subgroup ↥(P.map e.toMonoidHom)) =
      (thompsonCenter (⊤ : Subgroup ↥P)).map φ.toMonoidHom := by
    exact (thompsonCenter_top_map_mulEquiv (G := ↥P) (H := ↥(P.map e.toMonoidHom)) φ).symm
  have h3 : Subgroup.map (P.map e.toMonoidHom).subtype
        ((thompsonCenter (⊤ : Subgroup ↥P)).map φ.toMonoidHom) =
      (thompsonCenter (⊤ : Subgroup ↥P)).map
        ((P.map e.toMonoidHom).subtype.comp φ.toMonoidHom) := by
    rw [Subgroup.map_map]
  have h4 : (thompsonCenter (⊤ : Subgroup ↥P)).map
        ((P.map e.toMonoidHom).subtype.comp φ.toMonoidHom) =
      (thompsonCenter (⊤ : Subgroup ↥P)).map (e.toMonoidHom.comp P.subtype) := by
    rfl
  rw [h1, h2, h3, h4]
  rw [← Subgroup.map_map]
  rw [thompsonCenter_top_map_subtype]

/-! ## Theorem A -/

namespace TheoremA

variable {p : ℕ} [Fact p.Prime]

/-- Glauberman's Theorem A (the ZJ-theorem), matching the wrapper statement
`Glauberman.theoremA` exactly (see `refs/glauberman-p-stable.tex` L301–L306; proof
L974–L989). -/
public theorem theoremA (hpodd : p ≠ 2) {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) :
    pStable p G → Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G →
      (ZJ (G := G) S.toSubgroup).Characteristic := by
  intro hstab hC
  let P : Subgroup G := pCore p G
  let Z : Subgroup G := ZJ (G := G) (S : Subgroup G)
  have : P.Normal := by simpa [P] using (pCore_normal (p := p) (G := G))
  have hP_p : IsPGroup p P := by simpa [P] using (pCore_isPGroup (p := p) (G := G))
  -- `Z ≤ S`, `Z` Abelian, `Z ⊴ S`
  have hZleS : Z ≤ (S : Subgroup G) := by
    change thompsonCenter (G := G) (S : Subgroup G) ≤ (S : Subgroup G)
    exact thompsonCenter_le (G := G) (S : Subgroup G)
  have hZcomm : IsMulCommutative Z := by
    change IsMulCommutative (thompsonCenter (G := G) (S : Subgroup G))
    exact thompsonCenter_isMulCommutative (G := G) (S : Subgroup G)
  have hZS : (Z.subgroupOf (S : Subgroup G)).Normal := by
    simpa [Z, ZJ] using (thompsonCenter_normal_subgroupOf_sylow (G := G) (p := p) S)
  have hPleS : P ≤ (S : Subgroup G) :=
    IsPGroup.le_sylow_of_normal (N := P) hP_p S
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_normal_subgroupOf_of_le (P := P) (Z := Z) (S := (S : Subgroup G)) hZleS hZS hPleS
  have hPZZ : ⁅⁅P, Z⁆, Z⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_abelian_normalizer (P := P) (Z := Z) hPZ hZcomm
  by_cases hPbot : P = ⊥
  · -- `C_G(1) ⊆ 1` forces `G = 1`, hence `Z = 1` is characteristic.
    have hC1 : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := by simpa using hy
        simp [hy1]
    have hCbot : (⊤ : Subgroup G) ≤ (⊥ : Subgroup G) := by
      have hC' : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ P := hC
      rw [hPbot] at hC'
      rwa [hC1] at hC'
    have hGbot : (⊤ : Subgroup G) = ⊥ := le_antisymm hCbot bot_le
    have hZlebot : Z ≤ (⊥ : Subgroup G) := by
      calc
        Z ≤ (S : Subgroup G) := hZleS
        _ ≤ (⊤ : Subgroup G) := le_top
        _ ≤ (⊥ : Subgroup G) := by simp [hGbot]
    have hZbot : Z = ⊥ := le_bot_iff.mp hZlebot
    have hZchar : (Z : Subgroup G).Characteristic := by
      rw [hZbot]
      infer_instance
    simpa [Z, ZJ] using hZchar
  · -- main case: `P ≠ ⊥`; show `Z ⊆ P`
    have hZleP : Z ≤ P := by
      intro z hz
      have hcomm : ⁅⁅P, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥ :=
        commutator_zpowers_le_of_mem (P := P) (Z := Z) hPZZ hz
      let C : Subgroup G := Subgroup.centralizer (P : Set G)
      have : C.Normal := Subgroup.normal_centralizer (H := P)
      let mk : G →* G ⧸ C := QuotientGroup.mk' C
      have hcos0 : QuotientGroup.mk' (Subgroup.centralizer (P : Set G)) z ∈
          pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
        exact pStableLocal_apply_of_core_normal (G := G) (p := p) hstab (by simpa [P] using hPbot) z hcomm
      have hcos : mk z ∈ pCore p (G ⧸ C) := by
        simpa [C, mk] using hcos0
      have hcore0 : pCore p (G ⧸ Subgroup.centralizer (P : Set G)) ≤
          (pCore p G).map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) := by
        exact pCore_quotient_centralizer_le_of_centralizer_le_core (G := G) (p := p) hC
      have hcore : pCore p (G ⧸ C) ≤ P.map mk := by
        simpa [C, mk, P] using hcore0
      have hmk : mk z ∈ P.map mk := hcore hcos
      rcases (Subgroup.mem_map.mp hmk) with ⟨p0, hp0P, hpmk⟩
      have hker : z⁻¹ * p0 ∈ C := by
        have hk : mk (z⁻¹ * p0) = 1 := by
          rw [map_mul, map_inv, hpmk]
          simp
        exact (QuotientGroup.ker_mk' (N := C) ▸ (MonoidHom.mem_ker (f := mk)).mp hk)
      have hp0z : p0⁻¹ * z ∈ P := by
        have hzpinv : (z⁻¹ * p0)⁻¹ ∈ P := P.inv_mem (hC hker)
        have hzpinv' : p0⁻¹ * z = (z⁻¹ * p0)⁻¹ := by group
        rw [hzpinv']
        exact hzpinv
      have hzP' : p0 * (p0⁻¹ * z) ∈ P := P.mul_mem hp0P hp0z
      have hz_eq : z = p0 * (p0⁻¹ * z) := by group
      rw [hz_eq]
      exact hzP'
    -- Theorem 4.3 with `B = P` gives `Z ∩ P ⊴ G`, hence `Z ⊴ G`
    have hZinP_normal : (Z ⊓ P : Subgroup G).Normal := by
      simpa [Z] using (theorem4_3 (p := p) hpodd S (B := P) (by simpa [P] using (pCore_normal (p := p) (G := G))) hP_p hstab)
    have hZ_normal : Z.Normal := by
      have hZinf : Z ⊓ P = Z := by
        apply le_antisymm
        · exact inf_le_left
        · exact le_inf le_rfl hZleP
      rwa [hZinf] at hZinP_normal
    -- characteristic: transport through automorphisms and Sylow conjugacy
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    change (thompsonCenter (G := G) (S : Subgroup G)).map φ.toMonoidHom =
      thompsonCenter (G := G) (S : Subgroup G)
    let T : Sylow p G := S.mapSurjective (f := φ.toMonoidHom) (by simpa using φ.surjective)
    have hTφ : (T : Subgroup G) = (S : Subgroup G).map φ.toMonoidHom := rfl
    obtain ⟨g, hg⟩ : ∃ g : G, g • S = T := MulAction.exists_smul_eq G S T
    have hTg : (T : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← congrArg (fun Q : Sylow p G => (Q : Subgroup G)) hg]
      exact sylow_smul_subgroup_eq_map_conj (m := g) (P := S)
    have h1 : thompsonCenter (G := G) (T : Subgroup G) =
        (thompsonCenter (G := G) (S : Subgroup G)).map φ.toMonoidHom := by
      rw [hTφ]
      exact thompsonCenter_map_mulEquiv φ (S : Subgroup G)
    have h2 : thompsonCenter (G := G) (T : Subgroup G) =
        (thompsonCenter (G := G) (S : Subgroup G)).map (MulAut.conj g).toMonoidHom := by
      rw [hTg]
      exact thompsonCenter_map_mulEquiv (MulAut.conj g) (S : Subgroup G)
    have hgN : g ∈ Subgroup.normalizer ((Z : Subgroup G) : Set G) := by
      exact (Subgroup.normalizer_eq_top_iff.mpr hZ_normal) ▸ trivial
    have hZg : (Z : Subgroup G).map (MulAut.conj g).toMonoidHom = Z :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
    calc
      (thompsonCenter (G := G) (S : Subgroup G)).map φ.toMonoidHom
          = thompsonCenter (G := G) (T : Subgroup G) := h1.symm
      _ = (thompsonCenter (G := G) (S : Subgroup G)).map (MulAut.conj g).toMonoidHom := h2
      _ = Z := by simpa [Z, ZJ] using hZg

end TheoremA

end CFSG.Glauberman
