module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

set_option maxHeartbeats 800000

/-!
# Lemma 5.2 of Glauberman, "A Characteristic Subgroup of a p-Stable Group" ([6], §5)

Let `p` be a prime, `S` a Sylow `p`-subgroup of a finite group `G`, and put
`P = S ∩ O_{p',p}(G)`.  If the centralizer of `P` in `S` is contained in `P`
(`C_S(P) ⊆ P`), then, in `G/O_{p'}(G)`, the centralizer of `O_p(G/O_{p'}(G))`
is contained in `O_p(G/O_{p'}(G))`:

\[
  C_{\overline G}(O_p(\overline G)) \subseteq O_p(\overline G),\qquad
  \overline G = G/O_{p'}(G).
\]

The proof follows the paper ([6], Lemma 5.2, refs/glauberman-p-stable.tex
L1418–1458):

1.  With `C = C_G(P)`: since `P ⊴ S`, `C_S(P) = S ∩ C` is a Sylow `p`-subgroup
    of `C` (second-isomorphism counting inside `N_G(C)`).  The hypothesis gives
    `S ∩ C = Z(P) ⊆ Z(C)`, so Burnside's normal-p-complement criterion applies
    to `C`, and `C = O_{p',p}(C) = O_{p'}(C) · Z(P)`.
2.  `O_{p'}(C) ⊆ O_{p'}(G)`: with `M = O_{p'}(G)`, the Frattini argument gives
    `G = M · N_G(P)`; since `O_{p'}(C)` is characteristic in `C` and
    `N_G(P) ≤ N_G(C)`, the subgroup `O_{p'}(C) · M` is a normal `p'`-subgroup of
    `G`, hence lies in `M`.
3.  Hence `C ⊆ L := O_{p',p}(G)`.
4.  In `G/M`, the image of `L` is `O_p(G/M)` and is contained in the image of
    `S`, so `L = M · P`; `P` is a Sylow `p`-subgroup of `L`, and the Frattini
    argument yields `G = M · N_G(P)`.
5.  For `x̄ ∈ C_{G/M}(O_p(G/M))`, choose `x ∈ N_G(P)` in the coset; then
    `[x, P] ⊆ M ∩ P = 1`, so `x ∈ C = C_G(P) ⊆ L`, hence `x̄ ∈ L/M = O_p(G/M)`.

All auxiliary statements needed below are proved in this file; nothing outside
this module is modified.
-/

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-- Second isomorphism theorem (cardinality form): if `H` normalizes `K`, then the index
of `K` in `H ⊔ K` equals the index of `H ∩ K` in `H`:

\[
  |HK : K| = |H : H ∩ K|.
  \]

This is proved by running the usual tower-of-`relIndex` chain inside the normalizer of
`K`, where `K` is normal.  No normality of `K` in `G` is required. -/
private lemma relIndex_sup_eq_relIndex_inf {H K : Subgroup G} [Finite G]
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    let NG : Subgroup G := Subgroup.normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := Subgroup.le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    let : (K.subgroupOf NG).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKleNG).2 le_rfl
    calc
      K.relIndex (H ⊔ K)
          = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) := by
            exact (Subgroup.relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
            rw [Subgroup.subgroupOf_sup (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
            calc
              (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG))
                  = (K.subgroupOf NG).relIndex (H.subgroupOf NG) := by
                    exact Subgroup.relIndex_sup_right (H := H.subgroupOf NG) (K := K.subgroupOf NG)
              _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
                    symm
                    exact Subgroup.inf_relIndex_left (H := H.subgroupOf NG) (K := K.subgroupOf NG)
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
            rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
              ext x
              simp [Subgroup.mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := by
            exact Subgroup.relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hHleNG
  have hmul :
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := by
        exact Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K)
          inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) := by
        symm
        exact Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K)
          inf_le_right le_sup_right
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
        rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := by
    have hne : (H ⊓ K).relIndex H ≠ 0 := by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H)
    exact Nat.pos_of_ne_zero hne
  have hmul' : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex H * (H ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

set_option backward.isDefEq.respectTransparency false in
/-- If `N` is characteristic in `C` and `n` normalizes `C`, then `n` normalizes the image
of `N` in `G`. -/
private lemma conj_mem_pPrimeCore_map_subtype_of_normalizer
    {C : Subgroup G} (N : Subgroup (↥C)) [N.Characteristic] {n x : G}
    (hn : n ∈ Subgroup.normalizer (C : Set G)) (hx : x ∈ (N.map C.subtype : Subgroup G)) :
    n * x * n⁻¹ ∈ (N.map C.subtype : Subgroup G) := by
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hconj : C.map (MulAut.conj n).toMonoidHom = C := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨c, hc, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hn c).1 hc
    · intro c hc
      have hn' : n⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normalizer (C : Set G)).inv_mem hn
      rw [Subgroup.mem_normalizer_iff] at hn'
      have hc' : n⁻¹ * (c : G) * n ∈ C := by
        simpa using (hn' (c : G)).1 hc
      have hstep : n * (n⁻¹ * (c : G) * n) * n⁻¹ = c := by group
      have hmul : (MulAut.conj n).toMonoidHom (n⁻¹ * (c : G) * n) = c := by
        simpa [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe] using hstep
      exact Subgroup.mem_map.mpr ⟨n⁻¹ * (c : G) * n, hc', hmul⟩
  let e : C ≃* C :=
    ((MulEquiv.subgroupMap (MulAut.conj n) C).trans (MulEquiv.subgroupCongr hconj))
  have he_apply : ((e y : ↥C) : G) = n * ((y : ↥C) : G) * n⁻¹ := by
    simp [e, MulAut.conj_apply, mul_assoc]
  have hyN : e y ∈ N := by
    have hmap : N.map e.toMonoidHom = N :=
      Subgroup.characteristic_iff_map_eq.1 (by infer_instance : N.Characteristic) e
    exact hmap ▸ Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr ⟨e y, hyN, he_apply⟩

/-- If `n` normalizes `P`, then `n` normalizes the centralizer of `P`. -/
private lemma conj_mem_centralizer_of_normalizer {P : Subgroup G} {n x : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G))
    (hx : x ∈ Subgroup.centralizer (P : Set G)) :
    n * x * n⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hn' : n⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hn
  have hp' : n⁻¹ * p * n ∈ P := by
    simpa using (Subgroup.mem_normalizer_iff.mp hn' p).1 hp
  have hx' : (n⁻¹ * p * n) * x = x * (n⁻¹ * p * n) :=
    Subgroup.mem_centralizer_iff.mp hx (n⁻¹ * p * n) hp'
  have hstep : p * (n * x * n⁻¹) = n * ((n⁻¹ * p * n) * x) * n⁻¹ := by group
  have hstep2 : n * ((n⁻¹ * p * n) * x) * n⁻¹ = n * (x * (n⁻¹ * p * n)) * n⁻¹ := by
    rw [hx']
  have hstep3 : n * (x * (n⁻¹ * p * n)) * n⁻¹ = (n * x * n⁻¹) * p := by group
  exact hstep.trans (hstep2.trans hstep3)

/-- The intersection of a Sylow `p`-subgroup with a subgroup is a `p`-group. -/
private lemma isPGroup_inf_sylow (p : ℕ) [Fact p.Prime] (S : Sylow p G) (H : Subgroup G) :
    IsPGroup p ((S : Subgroup G) ⊓ H : Subgroup G) := by
  intro x
  let xs : ↥(S : Subgroup G) := ⟨(x : G), x.2.1⟩
  rcases (S.isPGroup' xs) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa [Subgroup.coe_pow] using congrArg Subtype.val hn

/-- `P = S ∩ L` is normal in `S` when `L ⊴ G`. -/
private lemma lemma5_2_P_normal_in_S (p : ℕ) [Fact p.Prime] (S : Sylow p G) (L : Subgroup G)
    [L.Normal] :
    ∀ {s : G} (_hs : s ∈ (S : Subgroup G)),
      ∀ p ∈ (S : Subgroup G) ⊓ L, s * p * s⁻¹ ∈ (S : Subgroup G) ⊓ L := by
  intro s hs p hp
  exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hp.1) ((S : Subgroup G).inv_mem hs),
    (inferInstance : L.Normal).conj_mem p hp.2 s⟩

/-- Glauberman's Lemma 5.2 ([6], §5; refs/glauberman-p-stable.tex L1418–1458):
if `P = S ∩ O_{p',p}(G)` and `C_S(P) ⊆ P`, then
`C_{G/O_{p'}(G)}(O_p(G/O_{p'}(G))) ⊆ O_p(G/O_{p'}(G))`. -/
public theorem lemma5_2 (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G)
    (hCS : (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ Op_p'p p G) : Set G) ≤
      (S : Subgroup G) ⊓ Op_p'p p G) :
    Subgroup.centralizer
        ((pCore p (G ⧸ pPrimeCore p G) : Subgroup (G ⧸ pPrimeCore p G)) : Set (G ⧸ pPrimeCore p G)) ≤
      pCore p (G ⧸ pPrimeCore p G) := by
  classical
  let L : Subgroup G := Op_p'p p G
  let M : Subgroup G := pPrimeCore p G
  let P : Subgroup G := (S : Subgroup G) ⊓ L
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have : M.Normal := pPrimeCore_normal (G := G) (p := p)
  have : L.Normal := Op_p'p_normal p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let O : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
  have hP_le_L : P ≤ L := inf_le_right
  have hP_le_S : P ≤ (S : Subgroup G) := inf_le_left
  have hM_le_L : M ≤ L := by
    intro m hm
    have hqm : q m = 1 := (QuotientGroup.eq_one_iff (N := M) (x := m)).2 hm
    have hqmO : q m ∈ O := by simp [hqm]
    simpa [L, q, M, O, Op_p'p] using Subgroup.mem_comap.mpr hqmO
  have hmap_op : L.map q = O := by
    simpa [L, q, M, O, Op_p'p] using
      (Subgroup.map_comap_eq_self_of_surjective (f := q)
        (QuotientGroup.mk'_surjective M) O)
  have hLbar_le_Sbar : L.map q ≤ (S : Subgroup G).map q := by
    let Sbar : Sylow p (G ⧸ M) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
    have hSbar : (Sbar : Subgroup (G ⧸ M)) = (S : Subgroup G).map q := by
      simp [Sbar]
    have hO_p : IsPGroup p O := pCore_isPGroup (G := G ⧸ M) (p := p)
    have hO_le_Sbar : O ≤ (Sbar : Subgroup (G ⧸ M)) :=
      IsPGroup.le_sylow_of_normal (N := O) hO_p Sbar
    simpa [hSbar, hmap_op] using hO_le_Sbar
  have hL_le_comap : L ≤ Subgroup.comap q ((S : Subgroup G).map q) := by
    intro l hl
    exact Subgroup.mem_comap.mpr (hLbar_le_Sbar (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩))
  have hL_le_SM : L ≤ (S : Subgroup G) ⊔ M := by
    intro l hl
    have hcomap : Subgroup.comap q ((S : Subgroup G).map q) = (S : Subgroup G) ⊔ M := by
      have hker : q.ker = M := QuotientGroup.ker_mk' M
      simpa [q, M, hker] using (Subgroup.comap_map_eq q (S : Subgroup G))
    exact hcomap ▸ hL_le_comap hl
  have hL_eq_MP : L = M ⊔ P := by
    apply le_antisymm
    · intro l hl
      rcases (Subgroup.mem_sup_of_normal_right (s := (S : Subgroup G)) (t := M) (x := l)).1
        (hL_le_SM hl) with ⟨s, hs, m, hm, hsm⟩
      have hsL : s ∈ L := by
        have hlm : l * m⁻¹ ∈ L := L.mul_mem hl (L.inv_mem (hM_le_L hm))
        have hsm' : l * m⁻¹ = s := by
          calc
            l * m⁻¹ = (s * m) * m⁻¹ := by rw [hsm]
            _ = s := by group
        exact hsm' ▸ hlm
      rw [← hsm]
      simpa [P, sup_comm] using
        (Subgroup.mul_mem_sup (S := (S : Subgroup G) ⊓ L) (T := M) (x := s) (y := m)
          (show s ∈ (S : Subgroup G) ⊓ L from ⟨hs, hsL⟩) hm)
    · exact sup_le hM_le_L hP_le_L
  have hP_norm_S : ∀ {s : G} (hs : s ∈ (S : Subgroup G)),
      ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
    intro s hs x hx
    exact lemma5_2_P_normal_in_S (G := G) p S L hs x hx
  have hS_le_NP : (S : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      exact hP_norm_S hs p hp
    · intro hp
      have hs' : s⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hs
      have hp' : s⁻¹ * (s * p * s⁻¹) * (s⁻¹)⁻¹ ∈ P := hP_norm_S hs' (s * p * s⁻¹) hp
      simpa [mul_assoc] using hp'
  have hNC : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_centralizer_of_normalizer (P := P) hn hx
    · intro hx
      have hn' : n⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hn
      have hx' : n⁻¹ * (n * x * n⁻¹) * n ∈ C := by
        simpa [mul_assoc] using conj_mem_centralizer_of_normalizer (P := P) hn' hx
      simpa [mul_assoc] using hx'
  have hS_le_NC : (S : Subgroup G) ≤ Subgroup.normalizer (C : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact conj_mem_centralizer_of_normalizer (P := P) (hS_le_NP hs) hc
    · intro hc
      have hs' : s⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hs
      have hc' : s⁻¹ * (s * c * s⁻¹) * s ∈ C := by
        simpa [mul_assoc] using conj_mem_centralizer_of_normalizer (P := P) (hS_le_NP hs') hc
      simpa [mul_assoc] using hc'
  let Psub : Subgroup (↥L) := (S : Subgroup G).subgroupOf L
  have hPsub_p : IsPGroup p Psub := by
    have hS_inf_L_p : IsPGroup p (((S : Subgroup G) ⊓ L) : Subgroup G) := isPGroup_inf_sylow (G := G) p S L
    have hsub : ((S : Subgroup G) ⊓ L).subgroupOf L = Psub := by
      ext x
      simp [Psub]
    exact hS_inf_L_p.of_equiv
      ((Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup G) ⊓ L) (K := L) inf_le_right).symm.trans
        (MulEquiv.subgroupCongr hsub))
  have hS_le_NL : (S : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact (inferInstance : L.Normal).conj_mem l hl s
    · intro hl
      have h' : s⁻¹ * (s * l * s⁻¹) * s ∈ L := by
        simpa [mul_assoc] using (inferInstance : L.Normal).conj_mem (s * l * s⁻¹) hl s⁻¹
      simpa [mul_assoc] using h'
  have hrel : S.relIndex (S ⊔ L) = ((S : Subgroup G) ⊓ L).relIndex L :=
    relIndex_sup_eq_relIndex_inf (H := (S : Subgroup G)) (K := L) hS_le_NL
  have hdvd : Psub.index ∣ S.index := by
    have hsub2 : Psub = ((S : Subgroup G) ⊓ L).subgroupOf L := by
      ext x
      simp [Psub]
    rw [hsub2]
    change ((S : Subgroup G) ⊓ L).relIndex L ∣ S.index
    rw [← hrel]
    exact Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup G)) (K := (S : Subgroup G) ⊔ L) le_sup_left
  have hnot : ¬ p ∣ Psub.index := by
    intro hp
    exact S.not_dvd_index (hp.trans hdvd)
  let : Finite (Sylow p (↥L)) := by
    have : Finite (Sylow p G) := Sylow.finite_of_finiteIndex (G := G) (p := p) S
    infer_instance
  let PS : Sylow p (↥L) := IsPGroup.toSylow (p := p) hPsub_p hnot
  have hPS : (PS : Subgroup (↥L)) = Psub := by
    simp [PS]
  have hFrattini : Subgroup.normalizer (P : Set G) ⊔ L = ⊤ := by
    have hnorm : Subgroup.normalizer ((PS : Subgroup (↥L)).map L.subtype : Subgroup G) ⊔ L = ⊤ :=
      Sylow.normalizer_sup_eq_top (G := G) (N := L) PS
    have hPS_map : (PS : Subgroup (↥L)).map L.subtype = P := by
      rw [hPS]
      simp [Psub, P, Subgroup.subgroupOf_map_subtype]
    simpa [hPS_map] using hnorm
  have hG_eq_MN : M ⊔ Subgroup.normalizer (P : Set G) = ⊤ := by
    calc
      M ⊔ Subgroup.normalizer (P : Set G)
          = (M ⊔ P) ⊔ Subgroup.normalizer (P : Set G) := by
            rw [sup_assoc, sup_eq_right.mpr (Subgroup.le_normalizer : P ≤ Subgroup.normalizer (P : Set G))]
      _ = L ⊔ Subgroup.normalizer (P : Set G) := by rw [hL_eq_MP]
      _ = ⊤ := by simpa [sup_comm] using hFrattini
  let Z : Subgroup (↥C) := (S : Subgroup G).subgroupOf C
  have hZp : IsPGroup p Z := by
    have hS_inf_C_p : IsPGroup p (((S : Subgroup G) ⊓ C) : Subgroup G) := isPGroup_inf_sylow (G := G) p S C
    have hsubC : ((S : Subgroup G) ⊓ C).subgroupOf C = Z := by
      ext x
      simp [Z]
    exact hS_inf_C_p.of_equiv
      ((Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup G) ⊓ C) (K := C) inf_le_right).symm.trans
        (MulEquiv.subgroupCongr hsubC))
  have hrel_C : S.relIndex (S ⊔ C) = ((S : Subgroup G) ⊓ C).relIndex C :=
    relIndex_sup_eq_relIndex_inf (H := (S : Subgroup G)) (K := C) hS_le_NC
  have hnotIdx : ¬ p ∣ Z.index := by
    intro hp
    have hdvd : ((S : Subgroup G) ⊓ C).relIndex C ∣ S.index := by
      rw [← hrel_C]
      exact Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup G)) (K := (S : Subgroup G) ⊔ C) le_sup_left
    have hpS : p ∣ S.index := by
      have hz : Z.index = ((S : Subgroup G) ⊓ C).relIndex C := by
        have hsubC' : Z = ((S : Subgroup G) ⊓ C).subgroupOf C := by
          ext x
          simp [Z]
        rw [hsubC', Subgroup.relIndex]
      exact (hp.trans (hz ▸ hdvd))
    exact S.not_dvd_index hpS
  let ZP : Sylow p (↥C) := IsPGroup.toSylow (p := p) hZp hnotIdx
  have hZP : (ZP : Subgroup (↥C)) = Z := by
    simp [ZP]
  have hZ_mem_P {z : ↥C} (hz : z ∈ Z) : (z : G) ∈ P := by
    have hzS : ((z : ↥C) : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.mp hz
    exact hCS ⟨hzS, (z : ↥C).property⟩
  have hZ_le_center : Z ≤ centerIn (G := ↥C) (Subgroup.normalizer (Z : Subgroup (↥C))) := by
    intro z hz
    rw [centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · exact (Subgroup.le_normalizer : Z ≤ Subgroup.normalizer (Z : Set (↥C))) hz
    · intro n hn
      apply Subtype.ext
      have hnC : ((n : ↥C) : G) ∈ C := (n : ↥C).property
      have hzP : ((z : ↥C) : G) ∈ P := hZ_mem_P hz
      exact (Subgroup.mem_centralizer_iff.mp hnC ((z : ↥C) : G) hzP).symm
  have hcomp : HasNormalPComplement p (↥C) :=
    hasNormalPComplement_of_sylow_le_center_normalizer (G := ↥C) p ZP (by simpa [hZP] using hZ_le_center)
  have hCquot_p : IsPGroup p (C ⧸ pPrimeCore p (↥C)) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement p (↥C) hcomp
  have hC_eq_KZ : pPrimeCore p (↥C) ⊔ Z = ⊤ := by
    have h := section10_sylow_sup_normal_of_p_quotient_eq_top (H := C)
      (N := pPrimeCore p (↥C)) hCquot_p ZP
    simpa [hZP, sup_comm] using h
  let K : Subgroup G := (pPrimeCore p (↥C)).map C.subtype
  have hK_le_C : K ≤ C := Subgroup.map_subtype_le (H := C) (pPrimeCore p (↥C))
  have hK_norm_NC : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_pPrimeCore_map_subtype_of_normalizer (C := C) (N := pPrimeCore p (↥C)) hn hx
    · intro hx
      have hn' : n⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normalizer (C : Set G)).inv_mem hn
      have hx' : n⁻¹ * (n * x * n⁻¹) * n ∈ K := by
        simpa [K, mul_assoc] using conj_mem_pPrimeCore_map_subtype_of_normalizer (C := C) (N := pPrimeCore p (↥C)) hn' hx
      simpa [mul_assoc] using hx'
  have hK_norm_NP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hNC.trans hK_norm_NC
  have conj_mem_sup_of_mem : ∀ (x : G) (m : G), m ∈ M → x ∈ M ⊔ K → m * x * m⁻¹ ∈ M ⊔ K := by
    intro x m hm hx
    rcases (Subgroup.mem_sup_of_normal_left (s := M) (t := K) (x := x)).1 hx with
      ⟨m', hm', k, hk, hmk⟩
    have hmk1 : m * k * m⁻¹ ∈ M ⊔ K := by
      exact (M ⊔ K).mul_mem
        ((M ⊔ K).mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hk))
        ((M ⊔ K).inv_mem (Subgroup.mem_sup_left hm))
    have hm1 : m * m' * m⁻¹ ∈ M := (inferInstance : M.Normal).conj_mem m' hm' m
    have hstep : m * x * m⁻¹ = (m * m' * m⁻¹) * (m * k * m⁻¹) := by
      rw [← hmk]
      group
    rw [hstep]
    exact (M ⊔ K).mul_mem (Subgroup.mem_sup_left hm1) hmk1
  have hM_norm_MK : M ≤ Subgroup.normalizer ((M ⊔ K : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_sup_of_mem x m hm hx
    · intro hx
      have hm' : m⁻¹ ∈ M := M.inv_mem hm
      have h1 : m⁻¹ * (m * x * m⁻¹) * m ∈ M ⊔ K := by
        simpa [inv_inv] using conj_mem_sup_of_mem (m * x * m⁻¹) m⁻¹ hm' hx
      have hx_eq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [hx_eq]
      exact h1
  have hNP_norm_MK : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((M ⊔ K : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases (Subgroup.mem_sup_of_normal_left (s := M) (t := K) (x := x)).1 hx with
        ⟨m, hm, k, hk, hmk⟩
      have hn1 : n * m * n⁻¹ ∈ M := (inferInstance : M.Normal).conj_mem m hm n
      have hn2 : n * k * n⁻¹ ∈ K := by
        exact (Subgroup.mem_normalizer_iff.mp (hK_norm_NP hn) k).1 hk
      have hstep : n * x * n⁻¹ = (n * m * n⁻¹) * (n * k * n⁻¹) := by
        rw [← hmk]
        group
      rw [hstep]
      exact (M ⊔ K).mul_mem (Subgroup.mem_sup_left hn1) (Subgroup.mem_sup_right hn2)
    · intro hx
      have hn' : n⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hn
      have h1 : n⁻¹ * (n * x * n⁻¹) * n ∈ M ⊔ K := by
        rcases (Subgroup.mem_sup_of_normal_left (s := M) (t := K) (x := n * x * n⁻¹)).1 hx with
          ⟨m, hm, k, hk, hmk⟩
        have hn1 : n⁻¹ * m * (n⁻¹)⁻¹ ∈ M := (inferInstance : M.Normal).conj_mem m hm n⁻¹
        have hn2 : n⁻¹ * k * (n⁻¹)⁻¹ ∈ K := by
          exact (Subgroup.mem_normalizer_iff.mp (hK_norm_NP hn') k).1 hk
        have hstep : n⁻¹ * (n * x * n⁻¹) * n = (n⁻¹ * m * (n⁻¹)⁻¹) * (n⁻¹ * k * (n⁻¹)⁻¹) := by
          rw [← hmk]
          group
        rw [hstep]
        exact (M ⊔ K).mul_mem (Subgroup.mem_sup_left hn1) (Subgroup.mem_sup_right hn2)
      have hx_eq : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [hx_eq]
      simpa [inv_inv] using h1
  have hMK_norm : (M ⊔ K).Normal := by
    have htop : M ⊔ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((M ⊔ K : Subgroup G) : Set G) :=
      sup_le hM_norm_MK hNP_norm_MK
    have hnorm_top : Subgroup.normalizer ((M ⊔ K : Subgroup G) : Set G) = ⊤ := by
      apply le_antisymm le_top
      simpa [hG_eq_MN] using htop
    exact Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hK_cop : Nat.Coprime p (Nat.card K) := by
    have hcard : Nat.card K = Nat.card (pPrimeCore p (↥C)) := by
      simpa [K] using (Subgroup.card_map_of_injective (K := pPrimeCore p (↥C))
        (f := C.subtype) C.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := ↥C) (p := p)
  have hMK_card : Nat.card (M ⊔ K : Subgroup G) = Nat.card M * ((M ⊓ K : Subgroup G)).relIndex K := by
    let MK : Subgroup G := M ⊔ K
    have h1 : Nat.card MK = Nat.card M * M.relIndex MK := by
      have h3 := Subgroup.card_mul_index (G := ↥MK) (H := M.subgroupOf MK)
      have hcard : Nat.card (M.subgroupOf MK) = Nat.card M := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := M) (K := MK) le_sup_left).toEquiv
      simpa [Subgroup.relIndex, hcard] using h3.symm
    have hrel : M.relIndex MK = (M ⊓ K).relIndex K := by
      calc
        M.relIndex MK = M.relIndex K := by
          exact Subgroup.relIndex_sup_left (H := K) (K := M)
        _ = (M ⊓ K).relIndex K := by
          symm
          exact Subgroup.inf_relIndex_right (H := M) (K := K)
    simpa [MK] using (h1.trans (by rw [hrel]))
  have hMK_cop : Nat.Coprime p (Nat.card (M ⊔ K : Subgroup G)) := by
    rw [hMK_card]
    have hMcop : Nat.Coprime p (Nat.card M) := pPrimeCore_coprime_card (G := G) (p := p)
    have hrel_dvd : ((M ⊓ K : Subgroup G)).relIndex K ∣ Nat.card K :=
      Subgroup.relIndex_dvd_card ((M ⊓ K : Subgroup G)) K
    have hrelcop : Nat.Coprime p ((M ⊓ K).relIndex K) :=
      (Nat.Coprime.coprime_dvd_left hrel_dvd hK_cop.symm).symm
    exact hMcop.mul_right hrelcop
  have hMK_le_M : M ⊔ K ≤ M := by
    exact le_sSup ⟨hMK_norm, hMK_cop⟩
  have hK_le_M : K ≤ M :=
    le_trans le_sup_right hMK_le_M
  have hC_le_L : C ≤ L := by
    intro c hc
    let cC : ↥C := ⟨c, hc⟩
    have hcC : cC ∈ (⊤ : Subgroup (↥C)) := Subgroup.mem_top cC
    have hcKZ : cC ∈ pPrimeCore p (↥C) ⊔ Z := hC_eq_KZ.symm ▸ hcC
    rcases (Subgroup.mem_sup_of_normal_left (s := pPrimeCore p (↥C)) (t := Z) (x := cC)).1 hcKZ with
      ⟨k, hk, z, hz, hkz⟩
    have hkL : ((k : ↥C) : G) ∈ L := by
      have hkm : ((k : ↥C) : G) ∈ (pPrimeCore p (↥C)).map C.subtype :=
        Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      have hkM : ((k : ↥C) : G) ∈ M := hK_le_M hkm
      exact hM_le_L hkM
    have hzL : ((z : ↥C) : G) ∈ L := by
      have hzS : ((z : ↥C) : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.mp hz
      exact hP_le_L (hCS ⟨hzS, (z : ↥C).property⟩)
    have hc_eq : (c : G) = ((k : ↥C) : G) * ((z : ↥C) : G) := by
      simpa using (congrArg Subtype.val hkz).symm
    simpa [hc_eq] using L.mul_mem hkL hzL
  have hM_inf_P : M ⊓ P = ⊥ := by
    have hP_p : IsPGroup p P := by simpa [P] using (isPGroup_inf_sylow (G := G) p S L)
    rcases hP_p.exists_card_eq with ⟨n, hcardP⟩
    have hcop : Nat.Coprime (Nat.card M) (Nat.card P) := by
      rw [hcardP]
      exact Nat.Coprime.pow_right n ((pPrimeCore_coprime_card (G := G) (p := p)).symm)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  intro xbar hxbar
  rcases QuotientGroup.mk'_surjective M xbar with ⟨x, rfl⟩
  have hxMN : x ∈ M ⊔ Subgroup.normalizer (P : Set G) := by
    simp [hG_eq_MN]
  rcases (Subgroup.mem_sup_of_normal_left (s := M) (t := Subgroup.normalizer (P : Set G))
    (x := x)).1 hxMN with ⟨m, hm, n, hn, hmn⟩
  have hqx_eq : q x = q n := by
    rw [← hmn, map_mul]
    have hqm : q m = 1 := (QuotientGroup.eq_one_iff (N := M) (x := m)).2 hm
    simp [hqm]
  have hcomm_n : ∀ p ∈ P, q n * q p = q p * q n := by
    intro p hp
    have hqpO : q p ∈ O := by
      have hmem : q p ∈ L.map q := Subgroup.mem_map.mpr ⟨p, hP_le_L hp, rfl⟩
      simpa [hmap_op] using hmem
    have hx : q p * q x = q x * q p := hxbar (q p) hqpO
    simpa [hqx_eq] using hx.symm
  have hnpM : ∀ p ∈ P, n * p * n⁻¹ * p⁻¹ ∈ M := by
    intro p hp
    rw [← QuotientGroup.eq_one_iff]
    calc
      q (n * p * n⁻¹ * p⁻¹) = q n * q p * (q n)⁻¹ * (q p)⁻¹ := by
        simp [q, map_mul]
      _ = 1 := by
        rw [hcomm_n p hp]
        simp
  have hnpP : ∀ p ∈ P, n * p * n⁻¹ * p⁻¹ ∈ P := by
    intro p hp
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hn p).1 hp) (P.inv_mem hp)
  have hn_comm : ∀ p ∈ P, n * p = p * n := by
    intro p hp
    have hmem : n * p * n⁻¹ * p⁻¹ ∈ M ⊓ P := ⟨hnpM p hp, hnpP p hp⟩
    have h1 : n * p * n⁻¹ * p⁻¹ = 1 := by
      simpa [hM_inf_P] using hmem
    have hstep : n * p * n⁻¹ = p := by
      calc
        n * p * n⁻¹ = (n * p * n⁻¹ * p⁻¹) * p := by group
        _ = p := by rw [h1]; simp
    calc
      n * p = (n * p * n⁻¹) * n := by group
      _ = p * n := by rw [hstep]
  have hnC : n ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hn_comm p hp).symm
  have hnL : n ∈ L := hC_le_L hnC
  have hqnO : q n ∈ O := by
    have hmem : q n ∈ L.map q := Subgroup.mem_map.mpr ⟨n, hnL, rfl⟩
    simpa [hmap_op] using hmem
  rw [hqx_eq]
  exact hqnO

end CFSG.Glauberman
