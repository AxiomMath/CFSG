module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem4_1

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — §4, Theorem 4.2

Statement and proof of Theorem 4.2 of George Glauberman, *A Characteristic Subgroup of a
p-Stable Group*, Canadian Journal of Mathematics 20 (1968), 1101–1135 — reference [6] of
the dihedral-Sylow project — following the validated transcription in
`refs/glauberman-p-stable.tex` (Theorem 4.2 at L934–L948).

* Theorem 4.2 (tex L934–L948): `p` odd, `S ∈ Syl_p G`, `B ⊴ G` a normal `p`-subgroup of
  nilpotence class at most two with `[B,B] ⊆ Z(J(S))`, `G` `p`-stable
  ⟹ `Z(J(S)) ∩ B ⊴ G`.

The paper says: "By substituting Corollary 4.1 for Corollary 3.1 in the proof of Theorem
3.2, we obtain the following theorem."  Accordingly, the proof below is a verbatim port
of the proof of `theorem3_2` (`Glauberman/Theorem3_2.lean`), with the single change that
Corollary 3.1 (which required `B` Abelian) is replaced by Corollary 4.1
(`Glauberman/Theorem4_1.lean`), whose hypothesis `[B,B] ⊆ Z(B) ∩ Z(J(S))` is supplied by
the class-≤-2 hypothesis (`[B,B] ⊆ Z(B)` via `commutator_le_centerIn_of_commutator_commutator_eq_bot`)
and by the hypothesis `[B,B] ⊆ Z(J(S))`; Corollary 4.1 supplies `A₀ ∈ A(S)` with
`commChain B A₀ 2 = ⊥` (as `p` is odd), i.e. exactly the `[B,A₀,A₀] = 1` that
Corollary 3.1 supplied for Abelian `B`, and the rest of the proof (the `(3.5)` plumbing
`h35`, the Frattini argument, `V = ⟨C^G⟩`, the Replacement Theorem contradiction) ports
unchanged.

The module-private helpers of `Glauberman/Theorem3_2.lean` used by the proof are copied
here verbatim (different module, same convention as documented there); the public
`lemma3_5` and `pStableLocal_apply_of_normal_pSubgroup` are imported from that module.

No `axiom`/`opaque`/unregistered `sorry` is used.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local infrastructure (module-private copies of Theorem3_2 helpers) -/

/-- `J(P) ≤ P`. -/
private lemma thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

/-- `Z(J(P)) ≤ P`. -/
private lemma thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := thompsonSubgroup_le (G := G) P

/-- `Z(J(P))` is Abelian. -/
public lemma thompsonCenter_isMulCommutative (P : Subgroup G) :
    IsMulCommutative (thompsonCenter (G := G) P) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := thompsonCenter (G := G) P)).1 ?_
  have hle_left : thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
    exact inf_le_left
  have hle_right :
      thompsonCenter (G := G) P ≤
        Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  exact hle_right.trans <|
    Subgroup.centralizer_le
      (show (thompsonCenter (G := G) P : Set G) ⊆ (thompsonSubgroup (G := G) P : Set G) from
        hle_left)

/-- Conjugation by a normalizer element preserves `A(P)`: if `g ∈ N_G(P)`, then the map
`A ↦ A^g` is a bijection of `A(P)` onto itself. -/
private lemma thompsonSubgroup_map_conj_of_normalizer (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P := by
  classical
  let e : G ≃* G := MulAut.conj g
  let e' : G ≃* G := MulAut.conj (g⁻¹ : G)
  have hg' : (P : Subgroup G).map e.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hg'inv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  have hg'inv' : (P : Subgroup G).map e'.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg'inv
  have himage :
      (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P =
        thompsonAbelianSubgroups (G := G) P := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · change A.map e.toMonoidHom ≤ P
        exact (Subgroup.map_mono hA.1).trans hg'.le
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
      · intro C hC hCcomm
        have hCpre_le : C.map e'.toMonoidHom ≤ P :=
          (Subgroup.map_mono hC).trans hg'inv'.le
        have hCpre_comm : IsMulCommutative (C.map e'.toMonoidHom) := by
          infer_instance
        have hAmax := hA.2.2 (C.map e'.toMonoidHom) hCpre_le hCpre_comm
        calc
          Nat.card C = Nat.card (C.map e'.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := C) e'.injective
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map e.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) e.injective
    · intro hB
      refine ⟨B.map e'.toMonoidHom, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · exact (Subgroup.map_mono hB.1).trans hg'inv'.le
        · let : IsMulCommutative B := hB.2.1
          exact Subgroup.map_isMulCommutative (H := B) e'.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.toMonoidHom ≤ P :=
            (Subgroup.map_mono hC).trans hg'.le
          have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
            infer_instance
          have hBmax := hB.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.injective
            _ ≤ Nat.card B := hBmax
            _ = Nat.card (B.map e'.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := B) e'.injective
      · ext x
        simp [e, e', mul_assoc]
  calc
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom
        = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) P)) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P) := by
      simp
    _ = thompsonSubgroup (G := G) P := by
      simpa [thompsonSubgroup] using congrArg sSup himage

/-- If `P` is a subgroup of `G`, then `N_G(P) ≤ N_G(J(P))`: `J(P)` is characteristic in `P`. -/
public lemma normalizer_le_normalizer_of_thompsonSubgroup (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 (thompsonSubgroup_map_conj_of_normalizer P hg)

/-- If `P` is a subgroup of `G`, then `N_G(J(P)) ≤ N_G(Z(J(P)))`: `Z(J(P))` is
characteristic in `J(P)`. -/
public lemma normalizer_le_normalizer_of_thompsonCenter (P : Subgroup G) :
    Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thompsonCenter (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hJ : (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hcen : (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    rw [map_centralizer_eq_of_equiv (G := G) (G' := G) (e := MulAut.conj g)
      (P := thompsonSubgroup (G := G) P), hJ]
  calc
    (thompsonCenter (G := G) P).map (MulAut.conj g).toMonoidHom
        = ((thompsonSubgroup (G := G) P ⊓
            Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)) : Subgroup G).map
            (MulAut.conj g).toMonoidHom := rfl
    _ = (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom ⊓
        (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
          (MulAut.conj g).toMonoidHom := by
          exact Subgroup.map_inf (thompsonSubgroup (G := G) P)
            (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    _ = thompsonCenter (G := G) P := by
      rw [hJ, hcen]
      rfl

/-! ## Lemma 3.5(a) for arbitrary subgroups -/

/-- If `A ∈ A(P)` then `Z(J(P)) ≤ A`. -/
private lemma lemma3_5a [Finite G] {P A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    thompsonCenter (G := G) P ≤ A := by
  classical
  let Z := thompsonCenter (G := G) P
  have hZ_le_P : Z ≤ P := thompsonCenter_le (G := G) P
  have hZ_cent_J : Z ≤ Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  have hA_le_J : A ≤ thompsonSubgroup (G := G) P := by
    exact le_sSup hA
  have hZA_comm : IsMulCommutative ((Z ⊔ A : Subgroup G)) := by
    rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative Z := thompsonCenter_isMulCommutative (G := G) P
    let : IsMulCommutative A := hA.2.1
    refine Subgroup.isMulCommutative_closure (k := ((Z : Subgroup G) : Set G) ∪ ((A : Subgroup G) : Set G)) (Set.Pairwise.of_forall₂ ?_)
    intro y hy z hz
    show y * z = z * y
    rcases hy with hyZ | hyA
    · rcases hz with hzZ | hzA
      · exact setLike_mul_comm (s := Z) hyZ hzZ
      · exact (Subgroup.mem_centralizer_iff.mp (hZ_cent_J hyZ) z (hA_le_J hzA)).symm
    · rcases hz with hzZ | hzA
      · exact Subgroup.mem_centralizer_iff.mp (hZ_cent_J hzZ) y (hA_le_J hyA)
      · exact setLike_mul_comm (s := A) hyA hzA
  have hZA_le_P : Z ⊔ A ≤ P := sup_le hZ_le_P hA.1
  have hcard : Nat.card (Z ⊔ A : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (Z ⊔ A : Subgroup G) hZA_le_P hZA_comm
  have hA_le_ZA : A ≤ Z ⊔ A := le_sup_right
  have hZA_eq_A : A = Z ⊔ A := Subgroup.eq_of_le_of_card_ge hA_le_ZA hcard
  exact hZA_eq_A ▸ le_sup_left

/-! ## Sylow subgroups of normal subgroups and the Frattini argument -/

/-- If `N ⊴ G` and `S ∈ Syl_p G`, then `S ∩ N` (viewed as a subgroup of `N`) is a Sylow
`p`-subgroup of `N`: the standard "Sylow ∩ normal = Sylow of normal". -/
private lemma sylow_subgroupOf_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ P : Sylow p (↥N), (P : Subgroup (↥N)).map N.subtype = (S : Subgroup G) ⊓ N := by
  classical
  let T : Subgroup (↥N) := (S : Subgroup G).subgroupOf N
  have hT_map : T.map N.subtype = (S : Subgroup G) ⊓ N := by
    simp [T, Subgroup.subgroupOf_map_subtype]
  have hT_p : IsPGroup p T := by
    intro x
    let xs : ↥(S : Subgroup G) := ⟨x.1.1, x.2⟩
    rcases (S.isPGroup' xs) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hn
  have hT_max : ∀ {Q : Subgroup (↥N)}, IsPGroup p Q → T ≤ Q → Q = T := by
    intro Q hQ hTQ
    let QG : Subgroup G := Q.map N.subtype
    have hQG_p : IsPGroup p QG := IsPGroup.map hQ N.subtype
    obtain ⟨T', hQ_le_T'⟩ := IsPGroup.exists_le_sylow hQG_p
    obtain ⟨x, hx⟩ : ∃ x : G, x • S = T' := MulAction.exists_smul_eq G S T'
    have hQG_le_xS : QG ≤ ((x • S : Sylow p G) : Subgroup G) := by
      simpa [hx] using hQ_le_T'
    have hQGx_le_S : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ (S : Subgroup G) := by
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ ((x • S : Sylow p G) : Subgroup G).map (MulAut.conj (x⁻¹ : G)).toMonoidHom :=
              Subgroup.map_mono hQG_le_xS
        _ = (S : Subgroup G) := by
          rw [sylow_smul_subgroup_eq_map_conj x S]
          calc
            ((S : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom).map
                (MulAut.conj (x⁻¹ : G)).toMonoidHom
                = (S : Subgroup G).map
                    ((MulAut.conj (x⁻¹ : G)).toMonoidHom.comp (MulAut.conj (x : G)).toMonoidHom) := by
                      rw [Subgroup.map_map]
            _ = (S : Subgroup G) := by
              ext g
              simp [MulAut.conj_apply, mul_assoc]
    have hQGx_le_N : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ N := by
      have hNinv : N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom = N := by
        have hxN : x⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
          (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)) ▸ trivial
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hxN
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom := by
              exact Subgroup.map_mono (by
                intro y hy
                rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
                exact n.2)
        _ = N := hNinv
    have hQGx_le_T : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ T.map N.subtype := by
      rw [hT_map]
      exact le_inf hQGx_le_S hQGx_le_N
    have hcard_Q_le_T : Nat.card Q ≤ Nat.card T := by
      calc
        Nat.card Q = Nat.card QG := by
          symm
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ = Nat.card (QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom) := by
          symm
          exact Subgroup.card_map_of_injective (K := QG) (f := (MulAut.conj (x⁻¹ : G)).toMonoidHom)
            (MulAut.conj (x⁻¹ : G)).injective
        _ ≤ Nat.card (T.map N.subtype) := Subgroup.card_le_of_le hQGx_le_T
        _ = Nat.card T := by
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_le : T.map N.subtype ≤ QG := Subgroup.map_mono hTQ
    have hcard_QT : Nat.card QG ≤ Nat.card (T.map N.subtype) := by
      calc
        Nat.card QG = Nat.card Q := by
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ ≤ Nat.card T := hcard_Q_le_T
        _ = Nat.card (T.map N.subtype) := by
          symm
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_eq : T.map N.subtype = QG := Subgroup.eq_of_le_of_card_ge hTQ_map_le hcard_QT
    apply (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
    simpa [QG] using hTQ_map_eq.symm
  refine ⟨⟨T, hT_p, hT_max⟩, hT_map⟩

/-- The Frattini argument: if `L ⊴ G` and `S ∈ Syl_p G`, then `G = L·N_G(L ∩ S)`;
here `L ∩ S` is the Sylow `p`-subgroup of `L` supplied by `sylow_subgroupOf_normal`.
This is Lemma 3.6 of the paper (`refs/glauberman-p-stable.tex` L595–L604), stated in the
ambient group `G`. -/
private lemma frattini_sup_eq_top {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (L : Subgroup G) [L.Normal] :
    Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ := by
  classical
  obtain ⟨P, hP_map⟩ := sylow_subgroupOf_normal S L
  have hfr := Sylow.normalizer_sup_eq_top (N := L) (P := P)
  simpa [hP_map] using hfr

/-! ## Theorem 4.2 (tex L934–L948) -/

/-- A subgroup of nilpotence class at most two satisfies `[B,B] ⊆ Z(B)`: from
`⁅⁅B,B⁆,B⁆ = ⊥` we get `[B,B] ≤ C_G(B)` (via `Subgroup.commutator_eq_bot_iff_le_centralizer`)
and `[B,B] ≤ B` (a subgroup contains its own commutators, `commutator_le_left_of_normalizer`). -/
public lemma commutator_le_centerIn_of_commutator_commutator_eq_bot (B : Subgroup G)
    (hB_class2 : ⁅⁅B, B⁆, B⁆ = ⊥) : ⁅B, B⁆ ≤ centerIn B := by
  exact le_inf
    (commutator_le_left_of_normalizer (H := B) (K := B) Subgroup.le_normalizer)
    ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅B, B⁆) (H₂ := B)).1 hB_class2)

/-- Theorem 4.2 ([6], §4, Theorem 4.2, p. 1111; `refs/glauberman-p-stable.tex` L934–L948):
let `p` be an odd prime and `S` a Sylow `p`-subgroup of a finite group `G`.  Suppose that
`B` is a normal `p`-subgroup of `G` of nilpotence class at most two (i.e.
`⁅⁅B,B⁆,B⁆ = ⊥`) and that `[B,B] ⊆ Z(J(S))`.  If `G` is `p`-stable, then
`Z(J(S)) ∩ B` is a normal subgroup of `G`.

Proof (port of the proof of `theorem3_2` with Corollary 4.1 in place of Corollary 3.1,
as the paper prescribes): `L` is the normal core of `N_G(C)` (`C = Z(J(S)) ∩ B`); the
Frattini argument gives `G = L·N(L∩S)` and `X = Z(J(L∩S))`; `(3.5)` (an `A ∈ A(S)` with
`[C₁,A,A] = 1` for a normal `p`-subgroup `C₁ ⊇ C` lies in `L`) is derived from the
`p`-stability hypothesis via `pStableLocal_apply_of_normal_pSubgroup`; Corollary 4.1
applied to `B ⊆ S` (using `[B,B] ⊆ Z(B) ∩ Z(J(S))`) supplies `A₀ ∈ A(S)` with
`[B,A₀,A₀] = 1` (`commChain B A₀ 2 = ⊥`, `p` odd), so `A₀ ⊆ L` by `(3.5)` and
`C ⊆ Z(J(S)) ⊆ Z(J(L∩S)) = X` ("(3.6)"); by Frattini, `G = L·N(X)` ("(3.7)"); the normal
closure `V = ⟨C^G⟩` satisfies `V ⊆ X` ("(3.8)").  Choosing `A ∈ A(S)`, `A ⊄ L`, with
`A ∩ V` maximal, `(3.5)` applied to `C₁ := V` gives `[V,A,A] ≠ 1` ("(3.9)"); the
Replacement Theorem (theorem3_1b) applied to `(V,A)` yields `A* ∈ A(S)` with
`A ∩ V < A* ∩ V` and `[A*,A,A] = 1`; maximality forces `A* ⊆ L∩S`, so `X ⊆ A*` by
Lemma 3.5(a) and `[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`, contradicting `(3.9)`. -/
public theorem theorem4_2 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) {B : Subgroup G} (hB_norm : B.Normal)
    (hB_p : IsPGroup p B) (hB_class2 : ⁅⁅B, B⁆, B⁆ = ⊥)
    (hBB_le_ZJ : ⁅B, B⁆ ≤ thompsonCenter (G := G) (S : Subgroup G))
    (hstab : pStable p G) :
    ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G).Normal) := by
  classical
  let C : Subgroup G := ZJ (G := G) (S : Subgroup G) ⊓ B
  let L : Subgroup G := (Subgroup.normalizer (C : Set G)).normalCore
  have hL_normal : L.Normal := Subgroup.normalCore_normal _
  have : L.Normal := hL_normal
  have hL_le_NC : L ≤ Subgroup.normalizer (C : Set G) := Subgroup.normalCore_le _
  by_cases hB1 : B = ⊥
  · have hC_bot : C = ⊥ := by
      simp [C, hB1]
    simp [C, hC_bot]
  -- `B ≠ ⊥`, so `O_p(G) ≠ ⊥` (and `⊤ ∈ M_p(G)` below)
  have hOpne : pCore p G ≠ ⊥ := by
    have hB_le_core : B ≤ pCore p G := le_sSup ⟨hB_norm, hB_p⟩
    intro hbot
    apply hB1
    apply le_antisymm
    · intro b hb
      have hb' : b ∈ pCore p G := hB_le_core hb
      rw [hbot] at hb'
      exact Subgroup.mem_bot.mp hb'
    · exact bot_le
  -- `B ≤ S` (`B` is a normal `p`-subgroup)
  have hB_le_S : B ≤ (S : Subgroup G) := IsPGroup.le_sylow_of_normal (N := B) hB_p S
  -- `S` normalizes `Z(J(S))`, `B`, hence `C`
  have hS_le_NZJ : S ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
    calc
      S ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := Subgroup.le_normalizer
      _ ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonSubgroup (S : Subgroup G)
      _ ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonCenter (S : Subgroup G)
  have hS_le_NC : S ≤ Subgroup.normalizer (C : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      C.map (MulAut.conj s).toMonoidHom
          = ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G)).map (MulAut.conj s).toMonoidHom := rfl
      _ = (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj s).toMonoidHom ⊓
          B.map (MulAut.conj s).toMonoidHom := by
            exact Subgroup.map_inf (ZJ (G := G) (S : Subgroup G)) B (MulAut.conj s).toMonoidHom
              (MulAut.conj s).injective
      _ = ZJ (G := G) (S : Subgroup G) ⊓ B := by
        have hZJ : (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj s).toMonoidHom =
            ZJ (G := G) (S : Subgroup G) :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hS_le_NZJ hs))
        have hB : B.map (MulAut.conj s).toMonoidHom = B :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer_eq_top_iff.mpr hB_norm) ▸ trivial))
        rw [hZJ, hB]
  -- the Frattini argument: `G = L·N(L∩S)`
  have hfrattini : Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ :=
    frattini_sup_eq_top S L
  -- `N(L∩S) ≤ N(J(L∩S)) ≤ N(Z(J(L∩S)))`
  have hNL_le_NJL : Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_of_thompsonSubgroup ((S : Subgroup G) ⊓ L)
  have hNJL_le_NZL : Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((ZJ (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_of_thompsonCenter ((S : Subgroup G) ⊓ L)
  let X : Subgroup G := ZJ (G := G) ((S : Subgroup G) ⊓ L)
  have hX_le_LS : X ≤ (S : Subgroup G) ⊓ L := thompsonCenter_le (G := G) ((S : Subgroup G) ⊓ L)
  -- `(3.5)`: `A ∈ A(S)`, `C ≤ C₁ ⊴ G` a `p`-subgroup, `[C₁,A,A] = 1` ⟹ `A ≤ L`
  have h35 : ∀ (A C1 : Subgroup G),
      A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) → C ≤ C1 → C1.Normal →
      IsPGroup p C1 → ⁅⁅C1, A⁆, A⁆ = ⊥ → A ≤ L := by
    intro A C1 hA hC_le_C1 hC1_norm hC1_p hC1AA
    have : C1.Normal := hC1_norm
    let C1cen : Subgroup G := Subgroup.centralizer (C1 : Set G)
    have : C1cen.Normal := Subgroup.normal_centralizer (H := C1)
    let q : G →* G ⧸ C1cen := QuotientGroup.mk' C1cen
    let M : Subgroup G := (pCore p (G ⧸ C1cen)).comap q
    have hM_normal : M.Normal := Subgroup.Normal.comap (pCore_normal (G := G ⧸ C1cen)) q
    have : M.Normal := hM_normal
    -- `C(C₁) ≤ N(C)`: `C ⊆ C₁`, so centralizing `C₁` centralizes `C`
    have hC1cen_le_NC : C1cen ≤ Subgroup.normalizer (C : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hx_eq : c * x * c⁻¹ = x := by
          calc
            c * x * c⁻¹ = x * c * c⁻¹ := by
              rw [Subgroup.mem_centralizer_iff.mp hc x (hC_le_C1 hx)]
            _ = x := by group
        rw [hx_eq]
        exact hx
      · intro hx'
        have hyC1 : c * x * c⁻¹ ∈ C1 := hC_le_C1 hx'
        have hcinv_x : c⁻¹ * (c * x * c⁻¹) = (c * x * c⁻¹) * c⁻¹ :=
          (Subgroup.mem_centralizer_iff.mp (C1cen.inv_mem hc) (c * x * c⁻¹) hyC1).symm
        have hx_eq : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        have hx'C : c⁻¹ * (c * x * c⁻¹) * c ∈ C := by
          have h1 : c⁻¹ * (c * x * c⁻¹) * c = c * x * c⁻¹ := by
            calc
              c⁻¹ * (c * x * c⁻¹) * c = (c * x * c⁻¹) * (c⁻¹ * c) := by
                rw [hcinv_x]
                group
              _ = c * x * c⁻¹ := by group
          rw [h1]
          exact hx'
        rw [← hx_eq] at hx'C
        exact hx'C
    -- `M ≤ N(C)`: `M = C(C₁)·(M∩S)` (the image of `M` in `G/C(C₁)` is `O_p`, which lies
    -- in the image of `S`), and both `C(C₁)` and `S` lie in `N(C)`
    have hM_le_NC : M ≤ Subgroup.normalizer (C : Set G) := by
      let Sbar : Sylow p (G ⧸ C1cen) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective C1cen)
      have hSbar : (Sbar : Subgroup (G ⧸ C1cen)) = (S : Subgroup G).map q := by
        simp [Sbar]
      have hO_le_Sbar : pCore p (G ⧸ C1cen) ≤ (Sbar : Subgroup (G ⧸ C1cen)) :=
        IsPGroup.le_sylow_of_normal (N := pCore p (G ⧸ C1cen)) (pCore_isPGroup (G := G ⧸ C1cen)) Sbar
      have hM_le_C1cenS : M ≤ C1cen ⊔ (S : Subgroup G) := by
        intro m hm
        have hqm : q m ∈ (S : Subgroup G).map q := by
          exact hO_le_Sbar (by simpa [hSbar] using (Subgroup.mem_comap.mp hm))
        rcases Subgroup.mem_map.mp hqm with ⟨s, hs, hqs⟩
        have hms : s⁻¹ * m ∈ C1cen := (QuotientGroup.eq.mp hqs)
        have hm_mem : s * (s⁻¹ * m) ∈ C1cen ⊔ (S : Subgroup G) := by
          rw [← sup_comm (S : Subgroup G) C1cen]
          exact Subgroup.mul_mem_sup hs hms
        rw [show m = s * (s⁻¹ * m) by group]
        exact hm_mem
      intro m hm
      have hm' : m ∈ (S : Subgroup G) ⊔ C1cen := by
        rw [sup_comm]
        exact hM_le_C1cenS hm
      rcases (Subgroup.mem_sup_of_normal_right (s := (S : Subgroup G)) (t := C1cen) (x := m)).1 hm'
        with ⟨s, hs, c, hc, hms⟩
      -- `m = s·c`, `s ∈ S ⊆ N(C)`, `c ∈ C(C₁) ⊆ N(C)`
      have hs_NC : s ∈ Subgroup.normalizer (C : Set G) := hS_le_NC hs
      have hc_NC : c ∈ Subgroup.normalizer (C : Set G) := hC1cen_le_NC hc
      have hm_mem : s * c ∈ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normalizer (C : Set G)).mul_mem hs_NC hc_NC
      rw [show m = s * c by exact hms.symm]
      exact hm_mem
    -- `(3.4)`: `O_p(G/C(C₁)) ⊆ L/C(C₁)`
    have h34 : pCore p (G ⧸ C1cen) ≤ L.map q := by
      calc
        pCore p (G ⧸ C1cen) = M.map q := by
          exact (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C1cen)
            (pCore p (G ⧸ C1cen))).symm
        _ ≤ L.map q := Subgroup.map_mono (Subgroup.normal_le_normalCore.mpr hM_le_NC)
    -- for `x ∈ A`: `[C₁,x,x] = 1`, so the `p`-stability plumbing applies
    intro x hxA
    have hx_comm : ⁅⁅C1, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ :=
      commutator_zpowers_le_of_mem hC1AA hxA
    have hx_core : QuotientGroup.mk' C1cen x ∈ pCore p (G ⧸ C1cen) :=
      pStableLocal_apply_of_normal_pSubgroup (p := p) hstab hOpne hC1_p hC1_norm x hx_comm
    have hx_Lmap : QuotientGroup.mk' C1cen x ∈ L.map q := h34 hx_core
    rcases Subgroup.mem_map.mp hx_Lmap with ⟨l, hl, hxl⟩
    have hxl_inv : l⁻¹ * x ∈ C1cen := (QuotientGroup.eq.mp hxl)
    have hC1cen_le_L : C1cen ≤ L := (Subgroup.normal_le_normalCore.mpr hC1cen_le_NC)
    rw [show x = l * (l⁻¹ * x) by group]
    exact L.mul_mem hl (hC1cen_le_L hxl_inv)
  -- Corollary 4.1 applied to `B ⊆ S`: `∃ A₀ ∈ A(S)` with `[B,A₀,A₀] = 1`
  -- (the hypothesis `[B,B] ⊆ Z(B) ∩ Z(J(S))` combines the class-≤-2 hypothesis with
  -- `hBB_le_ZJ`; as `p` is odd, Corollary 4.1 gives `commChain B A₀ 2 = ⊥`)
  have hBB_le_ZB : ⁅B, B⁆ ≤ centerIn B :=
    commutator_le_centerIn_of_commutator_commutator_eq_bot B hB_class2
  obtain ⟨A0, hA0_AS, _hA0_chain3, hA0_chain2⟩ := corollary4_1 (P := (S : Subgroup G)) S.isPGroup' (B := B)
    hB_le_S (Subgroup.Normal.subgroupOf hB_norm (S : Subgroup G)) hBB_le_ZB hBB_le_ZJ
  have hA0_BAA : ⁅⁅B, A0⁆, A0⁆ = ⊥ := by
    simpa [commChain] using hA0_chain2 hpodd
  -- `(3.5)` with `C₁ := B`: `A₀ ≤ L`
  have hC_le_B : C ≤ B := inf_le_right
  have hA0_le_L : A0 ≤ L := h35 A0 B hA0_AS hC_le_B hB_norm hB_p hA0_BAA
  -- `(3.6)`: `Z(J(S)) ⊆ Z(J(L∩S)) = X`
  have hA0_le_LS : A0 ≤ (S : Subgroup G) ⊓ L := le_inf hA0_AS.1 hA0_le_L
  have hZS_le_X : ZJ (G := G) (S : Subgroup G) ≤ X := by
    exact (lemma3_5 S).2.1 hA0_AS hA0_le_LS (inf_le_left : (S : Subgroup G) ⊓ L ≤ (S : Subgroup G))
  have hC_le_X : C ≤ X := (inf_le_left : C ≤ ZJ (G := G) (S : Subgroup G)).trans hZS_le_X
  -- `(3.7)`: `G = L·N(X)` (Frattini again, since `X` is characteristic in `L∩S`)
  have hG_eq_LNX : Subgroup.normalizer (X : Set G) ⊔ L = ⊤ := by
    apply le_antisymm
    · exact le_top
    · calc
        (⊤ : Subgroup G) = Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L := hfrattini.symm
        _ ≤ Subgroup.normalizer (X : Set G) ⊔ L := by
          exact sup_le_sup (hNL_le_NJL.trans hNJL_le_NZL) le_rfl
  -- `V = ⟨C^G⟩` (the normal closure of `C`)
  let V : Subgroup G := Subgroup.normalClosure (C : Set G)
  have hV_normal : V.Normal := Subgroup.normalClosure_normal
  have : V.Normal := hV_normal
  have hC_le_V : C ≤ V := Subgroup.le_normalClosure
  -- `(3.8)`: `V ⊆ X`
  have hV_le_X : V ≤ X := by
    dsimp [V, Subgroup.normalClosure]
    refine (Subgroup.closure_le (K := X)).2 ?_
    intro y hy
    rcases (Group.mem_conjugatesOfSet_iff).1 hy with ⟨a, ha, hconj⟩
    rcases isConj_iff.1 hconj with ⟨c, hy_eq⟩
    have hc_mem : c ∈ Subgroup.normalizer (X : Set G) ⊔ L := by
      rw [hG_eq_LNX]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (X : Set G)) (t := L)
      (x := c)).1 hc_mem with ⟨n, hn, l, hl, hcl⟩
    have hla : l * a * l⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hL_le_NC hl) a).1 ha
    have hnal : n * (l * a * l⁻¹) * n⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hn (l * a * l⁻¹)).1 (hC_le_X hla)
    have hcalc : y = n * (l * a * l⁻¹) * n⁻¹ := by
      calc
        y = c * a * c⁻¹ := hy_eq.symm
        _ = (n * l) * a * (n * l)⁻¹ := by rw [hcl]
        _ = n * (l * a * l⁻¹) * n⁻¹ := by group
    rw [hcalc]
    exact hnal
  -- `V` is a `p`-subgroup (it lies in `X ≤ L∩S ≤ S`)
  have hV_p : IsPGroup p V := by
    have hV_le_S : V ≤ (S : Subgroup G) := (hV_le_X.trans hX_le_LS).trans inf_le_left
    exact IsPGroup.to_le S.isPGroup' hV_le_S
  have hV_comm : IsMulCommutative V := by
    let : IsMulCommutative X := thompsonCenter_isMulCommutative (G := G) ((S : Subgroup G) ⊓ L)
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact setLike_mul_comm (s := X) (hV_le_X a.2) (hV_le_X b.2)
  -- `V ≤ S` (for the Replacement Theorem)
  have hV_le_S : V ≤ (S : Subgroup G) := (hV_le_X.trans hX_le_LS).trans inf_le_left
  have hA_le_NV (A : Subgroup G) : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hV_normal]
    exact le_top
  -- split on `J(S) ⊆ L∩S`
  by_cases hJS_le_LS : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (S : Subgroup G) ⊓ L
  · -- `J(S) ⊆ L∩S`: `J(S) = J(L∩S)` by Lemma 3.5(b), so `G = L·N(J(S)) ⊆ N(C)`
    have hJS_eq : thompsonSubgroup (G := G) (S : Subgroup G) =
        thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) :=
      (lemma3_5 S).2.2
        (IsPGroup.to_le S.isPGroup' (inf_le_left : (S : Subgroup G) ⊓ L ≤ (S : Subgroup G))) hJS_le_LS
    have hG_le_NC : (⊤ : Subgroup G) ≤ Subgroup.normalizer (C : Set G) := by
      calc
        (⊤ : Subgroup G) = Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L := hfrattini.symm
        _ ≤ Subgroup.normalizer (C : Set G) := by
          refine sup_le ?_ ?_
          · calc
              Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G)
                  ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
                    hNL_le_NJL
              _ = Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
                    rw [hJS_eq]
              _ ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
                    normalizer_le_normalizer_of_thompsonCenter (S : Subgroup G)
              _ ≤ Subgroup.normalizer (C : Set G) := by
                intro n hn
                rw [Subgroup.mem_normalizer_iff_map_conj_eq]
                calc
                  C.map (MulAut.conj n).toMonoidHom
                      = ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G)).map (MulAut.conj n).toMonoidHom := rfl
                  _ = (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj n).toMonoidHom ⊓
                      B.map (MulAut.conj n).toMonoidHom := by
                        exact Subgroup.map_inf (ZJ (G := G) (S : Subgroup G)) B (MulAut.conj n).toMonoidHom
                          (MulAut.conj n).injective
                  _ = ZJ (G := G) (S : Subgroup G) ⊓ B := by
                    have hZJ : (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj n).toMonoidHom =
                        ZJ (G := G) (S : Subgroup G) :=
                      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
                    have hB : B.map (MulAut.conj n).toMonoidHom = B :=
                      (Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer_eq_top_iff.mpr hB_norm) ▸ trivial))
                    rw [hZJ, hB]
          · exact hL_le_NC
    have hNC_top : Subgroup.normalizer (C : Set G) = ⊤ := top_le_iff.mp hG_le_NC
    have hC_normal : C.Normal := (Subgroup.normalizer_eq_top_iff.mp hNC_top)
    simpa [C] using hC_normal
  · -- `(3.3)`: `J(S) ⊄ L∩S`; the long argument
    -- there is `A ∈ A(S)` with `A ⊄ L`
    have h_exists_A_notL : ∃ A : Subgroup G,
        A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) ∧ ¬ A ≤ L := by
      by_contra hnone
      have hJS_le_LS' : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (S : Subgroup G) ⊓ L := by
        refine le_inf (thompsonSubgroup_le (G := G) (S : Subgroup G)) ?_
        refine sSup_le ?_
        intro A hA
        by_contra hAL
        exact hnone ⟨A, hA, hAL⟩
      exact hJS_le_LS hJS_le_LS'
    -- choose `A` with `A ∩ V` maximal among the `A ∈ A(S)` with `A ⊄ L`
    let t : Set (Subgroup G) := {A' : Subgroup G |
      A' ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) ∧ ¬ A' ≤ L}
    have ht_fin : t.Finite := Set.toFinite t
    have ht_ne : t.Nonempty := by
      rcases h_exists_A_notL with ⟨A', hA', hA'_notL⟩
      exact ⟨A', hA', hA'_notL⟩
    obtain ⟨A, hA_t, hA_max⟩ :=
      Set.exists_max_image t (fun A' : Subgroup G => Nat.card ((A' ⊓ V : Subgroup G))) ht_fin ht_ne
    have hA_AS : A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) := hA_t.1
    have hA_notL : ¬ A ≤ L := hA_t.2
    -- `(3.9)`: `[V,A,A] ≠ 1` by `(3.5)` with `C₁ := V`
    have hVAA_ne : ⁅⁅V, A⁆, A⁆ ≠ ⊥ := by
      intro hVAA
      exact hA_notL (h35 A V hA_AS hC_le_V hV_normal hV_p hVAA)
    -- the Replacement Theorem applied to `(V, A)`
    obtain ⟨Astar, hAstar_AS, hlt, hAstarAA⟩ := theorem3_1b (P := (S : Subgroup G)) S.isPGroup'
      hA_AS hV_le_S hV_comm (hA_le_NV A) hVAA_ne
    -- maximality of `A ∩ V` forces `A* ⊆ L ∩ S`
    have hAstar_le_LS : Astar ≤ (S : Subgroup G) ⊓ L := by
      have hAstar_le_L : Astar ≤ L := by
        by_contra hnot
        have hcard : Nat.card ((A ⊓ V : Subgroup G)) < Nat.card ((Astar ⊓ V : Subgroup G)) := by
          have hle : Nat.card ((A ⊓ V : Subgroup G)) ≤ Nat.card ((Astar ⊓ V : Subgroup G)) :=
            Subgroup.card_le_of_le hlt.le
          refine lt_of_le_of_ne hle ?_
          intro hEq
          have hEq' : A ⊓ V = Astar ⊓ V := Subgroup.eq_of_le_of_card_ge hlt.le (Nat.le_of_eq hEq.symm)
          exact hlt.ne hEq'
        exact (not_lt_of_ge (hA_max Astar ⟨hAstar_AS, hnot⟩)) hcard
      exact le_inf hAstar_AS.1 hAstar_le_L
    -- `X ≤ A*` (Lemma 3.5(a) with `P := L∩S`)
    have hAstar_in_ALS : Astar ∈ thompsonAbelianSubgroups (G := G) ((S : Subgroup G) ⊓ L) := by
      refine ⟨hAstar_le_LS, hAstar_AS.2.1, ?_⟩
      intro B' hB' hB'comm
      exact hAstar_AS.2.2 B' (le_trans hB' inf_le_left) hB'comm
    have hX_le_Astar : X ≤ Astar := lemma3_5a hAstar_in_ALS
    -- `[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`, contradicting `(3.9)`
    have hVX_le : ⁅⁅V, A⁆, A⁆ ≤ ⁅⁅X, A⁆, A⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hV_le_X le_rfl) le_rfl
    have hXA_le : ⁅⁅X, A⁆, A⁆ ≤ ⁅⁅Astar, A⁆, A⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hX_le_Astar le_rfl) le_rfl
    have hVAA_le : ⁅⁅V, A⁆, A⁆ ≤ ⁅⁅Astar, A⁆, A⁆ := hVX_le.trans hXA_le
    have hVAA_bot : ⁅⁅V, A⁆, A⁆ = ⊥ := by
      refine le_bot_iff.mp (hVAA_le.trans (le_of_eq hAstarAA))
    exfalso
    exact hVAA_ne hVAA_bot

end CFSG.Glauberman
